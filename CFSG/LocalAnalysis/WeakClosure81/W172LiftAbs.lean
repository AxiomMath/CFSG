module

public import CFSG.LocalAnalysis.WeakClosure81.W172Plift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Walter.Cited.HuppertBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

private theorem w172_mem_pCore_of_mem_normal_nilpotent {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) {N : Subgroup K} (hN : N.Normal)
    (hNnil : Group.IsNilpotent N) {x : K} (hxN : x ∈ N) {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ∈ CFSG.pCore p K := by
  have : Fact p.Prime := ⟨hp⟩
  have hxp : IsPGroup p (Subgroup.zpowers (⟨x, hxN⟩ : N)) := by
    have hdvd : Nat.card (Subgroup.zpowers (⟨x, hxN⟩ : N)) ∣ p ^ k := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact IsPGroup.of_card hj
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  have h1 : (⟨x, hxN⟩ : N) ∈ (S : Subgroup N) := hS (Subgroup.mem_zpowers _)
  exact Sylow.map_le_pCore hN hNnil p S ⟨⟨x, hxN⟩, h1, rfl⟩

private theorem w172_exists_acting_prime_group {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hO2 : CFSG.pCore 2 G = ⊥) {d : G}
    (hd : d * d = 1) (hd1 : d ≠ 1) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ x ∈ CFSG.pCore q G,
      d * x * d⁻¹ * x⁻¹ ∉ (⁅CFSG.pCore q G, CFSG.pCore q G⁆ : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdF : d ∉ fittingSubgroup G := by
    intro hmem
    have hmem2 : d ∈ CFSG.pCore 2 G :=
      w172_mem_pCore_of_mem_normal_nilpotent Nat.prime_two (fittingSubgroup_normal (G := G))
        (fittingSubgroup_nilpotent (G := G)) hmem (k := 1)
        (by show d ^ 2 = 1; rw [pow_two]; exact hd)
    rw [hO2, Subgroup.mem_bot] at hmem2
    exact hd1 hmem2
  have hdcent : d ∉ Subgroup.centralizer (fittingSubgroup G : Set G) :=
    fun hc => hdF (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hc)
  have hnotall : ¬ ∀ p : (Nat.card G).primeFactors,
      d ∈ Subgroup.centralizer (CFSG.pCore (p : ℕ) G : Set G) := by
    intro hall
    apply hdcent
    have h := subgroup_le_centralizer_fitting_of_le_centralizer_pCores
      (G := G) (P := Subgroup.zpowers d) (fun q => Subgroup.zpowers_le.mpr (hall q.1))
    exact h (Subgroup.mem_zpowers d)
  obtain ⟨q, hq⟩ := not_forall.mp hnotall
  have hqprime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    intro h
    apply hq
    rw [h, hO2, Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy]
    simp
  have hq' : ¬ ∀ y : G, y ∈ CFSG.pCore q G → y * d = d * y :=
    fun h => hq (Subgroup.mem_centralizer_iff.mpr h)
  obtain ⟨x, hx⟩ := not_forall.mp hq'
  have hxP : x ∈ CFSG.pCore q G := (not_imp.mp hx).1
  have hxd : x * d ≠ d * x := (not_imp.mp hx).2
  refine ⟨(q : ℕ), hqprime, hq2, ?_⟩
  by_contra hcon
  have hall : ∀ y ∈ CFSG.pCore q G,
      d * y * d⁻¹ * y⁻¹ ∈ (⁅CFSG.pCore q G, CFSG.pCore q G⁆ : Subgroup G) := by
    intro y hy
    by_contra hy'
    exact hcon ⟨y, hy, hy'⟩
  haveI : Fact (q : ℕ).Prime := ⟨hqprime⟩
  let P : Subgroup G := CFSG.pCore q G
  haveI hPnorm : P.Normal := by dsimp [P]; infer_instance
  have hPp : IsPGroup q ↥P := by dsimp [P]; exact pCore_isPGroup
  haveI : Fact (IsPGroup q ↥P) := ⟨hPp⟩
  let τ : MulAut ↥P := MulAut.conjNormal d
  have htop : (⊤ : Subgroup ↥P).map P.subtype = P := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hy
      exact x.2
    · intro hy
      exact ⟨⟨y, hy⟩, trivial, rfl⟩
  have hτ2 : τ ^ 2 = 1 := by
    show MulAut.conjNormal d ^ 2 = 1
    rw [← map_pow, show d ^ 2 = 1 by rw [pow_two]; exact hd, map_one]
  have hcop : Nat.Coprime q (orderOf τ) :=
    ((Nat.coprime_primes hqprime Nat.prime_two).mpr hq2).coprime_dvd_right
      ((orderOf_dvd_iff_pow_eq_one).mpr hτ2)
  have hPPleΦ : (⁅P, P⁆ : Subgroup G) ≤ (frattini ↥P).map P.subtype := by
    have hc := CFSG.commutator_le_frattini_of_isPGroup (R := ↥P) (p := q)
    have hmap : ((_root_.commutator ↥P : Subgroup ↥P).map P.subtype) ≤
        (frattini ↥P).map P.subtype := Subgroup.map_mono hc
    rw [show (_root_.commutator ↥P : Subgroup ↥P) = ⁅(⊤ : Subgroup ↥P), ⊤⁆ from rfl,
      Subgroup.map_commutator, htop] at hmap
    exact hmap
  have hgen : ∀ g : ↥P, g⁻¹ * τ g ∈ frattini ↥P := by
    intro g
    refine (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective P)).mp ?_
    have hmem : d * (g : G) * d⁻¹ * (g : G)⁻¹ ∈ (⁅P, P⁆ : Subgroup G) := hall (g : G) g.2
    have hconj : (g : G)⁻¹ * (d * (g : G) * d⁻¹ * (g : G)⁻¹) * (g : G) ∈
        (⁅P, P⁆ : Subgroup G) := by
      simpa using (inferInstance : (⁅P, P⁆ : Subgroup G).Normal).conj_mem _ hmem (g : G)⁻¹
    have heq : (g : G)⁻¹ * (d * (g : G) * d⁻¹ * (g : G)⁻¹) * (g : G) =
        (g : G)⁻¹ * d * (g : G) * d⁻¹ := by group
    rw [heq] at hconj
    have hcoe : P.subtype (g⁻¹ * τ g) = (g : G)⁻¹ * d * (g : G) * d⁻¹ := by
      show ((g⁻¹ * τ g : ↥P) : G) = (g : G)⁻¹ * d * (g : G) * d⁻¹
      simp only [τ, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      group
    rw [hcoe]
    exact hPPleΦ hconj
  have hτker : CFSG.Walter.Huppert.frattiniAut ↥P τ = 1 := by
    ext y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [CFSG.Walter.Huppert.frattiniAut_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem]
    rw [div_eq_mul_inv, show (τ g : ↥P) * g⁻¹ = g * (g⁻¹ * τ g) * g⁻¹ from by group]
    exact (inferInstance : (frattini ↥P).Normal).conj_mem _ (hgen g) g
  have hτ1 : τ = 1 :=
    CFSG.Walter.Huppert.eq_one_of_frattiniAut_eq_one hPp hcop hτker
  have h2 : d * x = x * d := by
    have h1 := congrArg (fun σ : MulAut ↥P => ((σ ⟨x, hxP⟩ : ↥P) : G)) hτ1
    simp only [τ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul).mp h1
  exact hxd h2.symm

theorem w172_exists_acting_prime {L : Subgroup Γ} (hsolv : Group.IsSolvable ↥L)
    (hO2 : pCoreOf 2 L = ⊥) {d : Γ} (hdL : d ∈ L) (hd : d * d = 1) (hd1 : d ≠ 1) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ x ∈ pCoreOf q L,
      d * x * d⁻¹ * x⁻¹ ∉ (⁅pCoreOf q L, pCoreOf q L⁆ : Subgroup Γ) := by
  classical
  have hO2' : CFSG.pCore 2 ↥L = ⊥ := by
    have h := hO2
    rw [CFSG.Open.pCoreOf] at h
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥L) (f := L.subtype)
      (Subgroup.subtype_injective L)).mp h
  let d' : ↥L := ⟨d, hdL⟩
  have hd' : d' * d' = 1 := Subtype.ext (by simpa [d'] using hd)
  have hd1' : d' ≠ 1 := fun h => hd1 (by simpa [d'] using congrArg Subtype.val h)
  obtain ⟨q, hqprime, hq2, x, hxP, hxnot⟩ :=
    w172_exists_acting_prime_group hsolv hO2' hd' hd1'
  refine ⟨q, hqprime, hq2, (x : Γ), ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem L.subtype hxP
  · intro hmem
    have hmem' : d * (x : Γ) * d⁻¹ * (x : Γ)⁻¹ ∈
        (⁅CFSG.pCore q ↥L, CFSG.pCore q ↥L⁆ : Subgroup ↥L).map L.subtype := by
      rw [Subgroup.map_commutator]
      simpa only [CFSG.Open.pCoreOf] using hmem
    have hmem'' : L.subtype (d' * x * d'⁻¹ * x⁻¹) ∈
        (⁅CFSG.pCore q ↥L, CFSG.pCore q ↥L⁆ : Subgroup ↥L).map L.subtype := hmem'
    exact hxnot ((Subgroup.mem_map_iff_mem (Subgroup.subtype_injective L)).mp hmem'')


private theorem w172_pCoreOf_top (p : ℕ) :
    pCoreOf p (⊤ : Subgroup Γ) = CFSG.pCore p Γ := by
  unfold CFSG.Open.pCoreOf
  rw [show (⊤ : Subgroup Γ).subtype = (Subgroup.topEquiv (G := Γ)).toMonoidHom from rfl]
  exact CFSG.pCore_map_iso p (Subgroup.topEquiv (G := Γ))

theorem w172_lift_abstract {S : Subgroup Γ} {d₀ : Γ} (hsolv : Group.IsSolvable Γ)
    (hO2 : CFSG.pCore 2 Γ = ⊥) (hd₀ : d₀ * d₀ = 1) (hd₀1 : d₀ ≠ 1)
    (hcomm : ∀ s ∈ S, d₀ * (s * d₀ * s⁻¹) = (s * d₀ * s⁻¹) * d₀)
    (hno : ∀ s ∈ S, s * d₀ * s⁻¹ ≠ d₀ → ∀ u : Γ, Odd (orderOf u) → d₀ * u * d₀⁻¹ = u⁻¹ →
      (s * d₀ * s⁻¹) * u * (s * d₀ * s⁻¹)⁻¹ = u⁻¹ → u = 1) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (∃ B : Subgroup Γ, IsElemAbelian p B ∧
        Nat.card B = p ^ (Subgroup.centralizer ({d₀} : Set Γ)).relIndex S) ∧
      ∃ B : Subgroup Γ, B ≤ Subgroup.centralizer ({d₀} : Set Γ) ∧ IsElemAbelian p B ∧
        Nat.card B = p ^ ((Subgroup.centralizer ({d₀} : Set Γ)).relIndex S - 1) := by
  classical
  haveI : Fintype ↥S := Fintype.ofFinite ↥S
  have hsolvTop : Group.IsSolvable ↥(⊤ : Subgroup Γ) := by
    haveI : IsSolvable Γ := hsolv
    exact solvable_of_surjective (f := (Subgroup.topEquiv (G := Γ)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := Γ)).symm.surjective
  have hO2top : pCoreOf 2 (⊤ : Subgroup Γ) = ⊥ := by
    rw [w172_pCoreOf_top, hO2]
  obtain ⟨p, hpprime, hp2, x₀, hx₀P, hx₀not⟩ :=
    w172_exists_acting_prime (L := ⊤) hsolvTop hO2top (d := d₀) trivial hd₀ hd₀1
  haveI : Fact p.Prime := ⟨hpprime⟩
  let P : Subgroup Γ := pCoreOf p ⊤
  let N : Subgroup Γ := ⁅P, P⁆
  have hPdef : P = CFSG.pCore p Γ := by
    dsimp [P]
    exact w172_pCoreOf_top p
  haveI hPnorm : P.Normal := by rw [hPdef]; infer_instance
  have hPp : IsPGroup p ↥P := by rw [hPdef]; exact pCore_isPGroup
  haveI hNnorm : N.Normal := by dsimp [N]; infer_instance
  let C : Subgroup Γ := Subgroup.centralizer ({d₀} : Set Γ)
  let D : Finset Γ := Finset.univ.image (fun s : ↥S => (s : Γ) * d₀ * (s : Γ)⁻¹)
  have hD_card : D.card = C.relIndex S := by
    let act : ↥S →* MulAut Γ := MulAut.conj.comp S.subtype
    letI : MulAction ↥S Γ := MulAction.compHom Γ act
    have horbit : MulAction.orbit ↥S d₀ = (D : Set Γ) := by
      ext y
      constructor
      · intro hy
        obtain ⟨s, rfl⟩ := MulAction.mem_orbit_iff.mp hy
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, ?_⟩)
        show (s : Γ) * d₀ * (s : Γ)⁻¹ = s • d₀
        rfl
      · intro hy
        obtain ⟨s, -, hs⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        exact MulAction.mem_orbit_iff.mpr ⟨s, by rw [← hs]; rfl⟩
    have hstab : MulAction.stabilizer ↥S d₀ = C.subgroupOf S := by
      ext s
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff]
      show (s : Γ) * d₀ * (s : Γ)⁻¹ = d₀ ↔ (s : Γ) * d₀ = d₀ * (s : Γ)
      rw [mul_inv_eq_iff_eq_mul]
    show D.card = (C.subgroupOf S).index
    rw [← hstab, MulAction.index_stabilizer, horbit, Set.ncard_coe_finset]
  have hDd₀ : d₀ ∈ D := by
    dsimp [D]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, by simp⟩
  have hsetup : W172PliftSetup p P N D :=
    { prime := hpprime
      odd := hp2
      pgroup := hPp
      le := by dsimp [N]; exact Subgroup.commutator_le_left P P
      n_norm := fun x _ n hn => hNnorm.conj_mem n hn x
      abelian := fun x hx y hy => by
        have h := Subgroup.commutator_mem_commutator hx hy
        dsimp [N]
        simpa only [commutatorElement_def] using h
      sq := by
        intro e he
        obtain ⟨s, -, hs⟩ := Finset.mem_image.mp (by simpa only [D] using he)
        rw [← hs]
        calc ((s : Γ) * d₀ * (s : Γ)⁻¹) * ((s : Γ) * d₀ * (s : Γ)⁻¹)
            = (s : Γ) * (d₀ * d₀) * (s : Γ)⁻¹ := by group
          _ = 1 := by rw [hd₀]; group
      comm := by
        intro e he f hf
        obtain ⟨s, -, hs⟩ := Finset.mem_image.mp (by simpa only [D] using he)
        obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (by simpa only [D] using hf)
        rw [← hs, ← ht]
        have hmem : (s : Γ)⁻¹ * (t : Γ) ∈ S := S.mul_mem (S.inv_mem s.2) t.2
        have hc : Commute d₀ ((s : Γ)⁻¹ * ((t : Γ) * d₀ * (t : Γ)⁻¹) * (s : Γ)) := by
          have h := hcomm ((s : Γ)⁻¹ * (t : Γ)) hmem
          rw [show (s : Γ)⁻¹ * (t : Γ) * d₀ * ((s : Γ)⁻¹ * (t : Γ))⁻¹ =
              (s : Γ)⁻¹ * ((t : Γ) * d₀ * (t : Γ)⁻¹) * (s : Γ) from by group] at h
          exact h
        have hc2 := hc.conj (s : Γ)
        have h2 : (s : Γ) * ((s : Γ)⁻¹ * ((t : Γ) * d₀ * (t : Γ)⁻¹) * (s : Γ)) *
            (s : Γ)⁻¹ = (t : Γ) * d₀ * (t : Γ)⁻¹ := by group
        rw [h2] at hc2
        exact hc2
      norm_p := fun e _ x hx => hPnorm.conj_mem x hx e
      norm_n := fun e _ n hn => hNnorm.conj_mem n hn e
      acts := by
        intro e he
        obtain ⟨s, -, hs⟩ := Finset.mem_image.mp (by simpa only [D] using he)
        refine ⟨(s : Γ) * x₀ * (s : Γ)⁻¹, hPnorm.conj_mem x₀ hx₀P s, ?_⟩
        rw [← hs]
        intro hmem
        apply hx₀not
        have hconj : (s : Γ)⁻¹ * (((s : Γ) * d₀ * (s : Γ)⁻¹) *
            ((s : Γ) * x₀ * (s : Γ)⁻¹) * ((s : Γ) * d₀ * (s : Γ)⁻¹)⁻¹ *
            ((s : Γ) * x₀ * (s : Γ)⁻¹)⁻¹) * (s : Γ) ∈ N := by
          simpa using hNnorm.conj_mem _ hmem (s : Γ)⁻¹
        convert hconj using 1 <;> group
      no_two_inverted := by
        intro e he f hf hef u huP heu hfu
        obtain ⟨s, -, hs⟩ := Finset.mem_image.mp (by simpa only [D] using he)
        obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (by simpa only [D] using hf)
        have hmem : (s : Γ)⁻¹ * (t : Γ) ∈ S := S.mul_mem (S.inv_mem s.2) t.2
        let u₁ : Γ := (s : Γ)⁻¹ * u * (s : Γ)
        have hodd : Odd (orderOf u₁) := by
          have hord : orderOf u₁ = orderOf u := by
            dsimp [u₁]
            exact SemiconjBy.orderOf_eq (s : Γ) (by simp [SemiconjBy, mul_assoc])
          rw [hord]
          obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow hPp ⟨u, huP⟩
          rw [Subgroup.orderOf_mk] at hk
          rw [hk]
          exact (hpprime.odd_of_ne_two hp2).pow
        have hd₀inv : d₀ * u₁ * d₀⁻¹ = u₁⁻¹ := by
          have h := heu
          rw [← hs] at h
          dsimp [u₁]
          calc d₀ * ((s : Γ)⁻¹ * u * (s : Γ)) * d₀⁻¹
              = (s : Γ)⁻¹ * (((s : Γ) * d₀ * (s : Γ)⁻¹) * u *
                  ((s : Γ) * d₀ * (s : Γ)⁻¹)⁻¹) * (s : Γ) := by group
            _ = (s : Γ)⁻¹ * u⁻¹ * (s : Γ) := by rw [h]
            _ = ((s : Γ)⁻¹ * u * (s : Γ))⁻¹ := by group
        have hconjinv : ((s : Γ)⁻¹ * (t : Γ) * d₀ * ((s : Γ)⁻¹ * (t : Γ))⁻¹) * u₁ *
            ((s : Γ)⁻¹ * (t : Γ) * d₀ * ((s : Γ)⁻¹ * (t : Γ))⁻¹)⁻¹ = u₁⁻¹ := by
          have h := hfu
          rw [← ht] at h
          dsimp [u₁]
          calc ((s : Γ)⁻¹ * (t : Γ) * d₀ * ((s : Γ)⁻¹ * (t : Γ))⁻¹) *
                ((s : Γ)⁻¹ * u * (s : Γ)) *
                ((s : Γ)⁻¹ * (t : Γ) * d₀ * ((s : Γ)⁻¹ * (t : Γ))⁻¹)⁻¹
              = (s : Γ)⁻¹ * (((t : Γ) * d₀ * (t : Γ)⁻¹) * u *
                  ((t : Γ) * d₀ * (t : Γ)⁻¹)⁻¹) * (s : Γ) := by group
            _ = (s : Γ)⁻¹ * u⁻¹ * (s : Γ) := by rw [h]
            _ = ((s : Γ)⁻¹ * u * (s : Γ))⁻¹ := by group
        have hne : (s : Γ)⁻¹ * (t : Γ) * d₀ * ((s : Γ)⁻¹ * (t : Γ))⁻¹ ≠ d₀ := by
          intro h
          apply hef
          rw [← hs, ← ht]
          calc (s : Γ) * d₀ * (s : Γ)⁻¹
              = (s : Γ) * ((s : Γ)⁻¹ * (t : Γ) * d₀ * ((s : Γ)⁻¹ * (t : Γ))⁻¹) *
                  (s : Γ)⁻¹ := by conv_lhs => rw [← h]
            _ = (t : Γ) * d₀ * (t : Γ)⁻¹ := by group
        have hu₁1 : u₁ = 1 := hno ((s : Γ)⁻¹ * (t : Γ)) hmem hne u₁ hodd hd₀inv hconjinv
        have : u = 1 := by
          have h := congrArg (fun x => (s : Γ) * x * (s : Γ)⁻¹) hu₁1
          dsimp [u₁] at h
          simpa [mul_assoc] using h
        exact this }
  obtain ⟨⟨B₁, -, hB₁ea, hB₁card⟩, hsecond⟩ := w172_plift hsetup
  refine ⟨p, hpprime, hp2, ⟨B₁, hB₁ea, ?_⟩, ?_⟩
  · rw [hB₁card, hD_card]
  · obtain ⟨B₂, hB₂le, hB₂ea, hB₂card⟩ := hsecond d₀ hDd₀
    exact ⟨B₂, fun x hx => (hB₂le hx).2, hB₂ea, by rw [hB₂card, hD_card]⟩

end CFSG.LocalAnalysis.WeakClosure81

end
