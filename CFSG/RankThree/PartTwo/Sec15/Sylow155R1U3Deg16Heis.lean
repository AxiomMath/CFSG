module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofHeis
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
open Module
open scoped TensorProduct commutatorElement

theorem pow_le_sixteen_or_lt_4080 {s m n : ℕ} (hs : 2 ≤ s) (hm : 1 ≤ m) (hsm : s ^ m ≤ 6)
    (hn : s ^ n ≤ s ^ m * s ^ m) : s ^ n ≤ 16 ∨ (s ^ n) ^ n < 4080 := by
  have hm2 : m ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ s ^ m :=
      le_trans (Nat.pow_le_pow_left hs 3) (Nat.pow_le_pow_right (by omega) h)
    omega
  have hs6 : s ≤ 6 := le_trans (Nat.le_self_pow (by omega) s) hsm
  have hn2 : n ≤ 2 * m := by
    rw [← pow_add, ← two_mul] at hn
    exact (Nat.pow_le_pow_iff_right (by omega)).mp hn
  interval_cases m
  · interval_cases s <;> interval_cases n <;> norm_num
  · interval_cases s <;> norm_num at hsm
    interval_cases n <;> norm_num

theorem index_dvd_factorial_of_center {Y : Type*} [Group Y] [Finite Y] {R : Subgroup Y}
    [R.Normal] (hZR : Subgroup.center Y ≤ R) (C : Subgroup Y)
    (hC : ∀ c : Y, (∀ x ∈ R, c * x * c⁻¹ * x⁻¹ ∈ Subgroup.center Y) → c ∈ C) :
    C.index ∣ ((Subgroup.center Y).relIndex R).factorial := by
  classical
  have _ := hZR
  set Z := Subgroup.center Y with hZ
  set Rb : Subgroup (Y ⧸ Z) := R.map (QuotientGroup.mk' Z) with hRb
  have hRbn : Rb.Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  let ψ : Y →* Equiv.Perm Rb :=
    (MulAut.toPerm Rb).comp (MulAut.conjNormal.comp (QuotientGroup.mk' Z))
  have hker : ψ.ker ≤ C := by
    intro c hc
    apply hC c
    intro x hx
    have h1 : ψ c = 1 := hc
    have h2 : ((ψ c ⟨(x : Y ⧸ Z), x, hx, rfl⟩ : Rb) : Y ⧸ Z) = (x : Y ⧸ Z) := by
      rw [h1]; rfl
    have h3 : (c : Y ⧸ Z) * (x : Y ⧸ Z) * (c : Y ⧸ Z)⁻¹ = (x : Y ⧸ Z) := h2
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h3, mul_inv_cancel]
  have hcard : Nat.card Rb = Z.relIndex R := by
    rw [hRb, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have hdvd1 : C.index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hker
  have hdvd2 : ψ.ker.index ∣ (Nat.card Rb).factorial := by
    rw [Subgroup.index_ker, ← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  rw [hcard] at hdvd2
  exact hdvd1.trans hdvd2

section Irreducible

variable {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
  {ρ : Y →* (V →ₗ[ZMod p] V)}

theorem false_of_noncentral_normal_four (hρ : Function.Injective ρ) (hirr : IsIrreducibleRep ρ)
    [Nontrivial V] (hdim : Module.finrank (ZMod p) V ≤ 6)
    (hsmall : ∀ J : Subgroup Y, J.Normal → J ≠ ⊤ → 4080 ∣ J.index)
    (R : Subgroup Y) [R.Normal] (hZR : Subgroup.center Y ≤ R) (hRZ : ¬ R ≤ Subgroup.center Y)
    (hRR : ⁅R, R⁆ ≤ Subgroup.center Y) {s : ℕ} (hs : s.Prime)
    (hpow : ∀ x ∈ R, x ^ s ∈ Subgroup.center Y)
    (hact : ∃ y : Y, ∃ x ∈ R, y * x * y⁻¹ * x⁻¹ ∉ Subgroup.center Y) : False := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  set Z := Subgroup.center Y with hZ
  have hsmall720 : ∀ J : Subgroup Y, J.Normal → J.index ≤ 720 → J = ⊤ := by
    intro J hJ h
    by_contra hJne
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (hsmall J hJ hJne)
    omega
  have hRnc : ¬ ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun hc =>
    hRZ (le_center_of_comm_of_normal hρ hirr hdim hsmall720 R hc)
  have hZRc : ∀ a ∈ R, (∀ x ∈ R, a * x = x * a) → a ∈ Z := by
    intro a haR ha
    set CR := Subgroup.centralizer (R : Set Y) ⊓ R with hCR
    have : CR.Normal := inferInstance
    have hCRc : ∀ u ∈ CR, ∀ w ∈ CR, u * w = w * u := fun u hu w hw =>
      (Subgroup.mem_centralizer_iff.mp hu.1 w hw.2).symm
    refine le_center_of_comm_of_normal hρ hirr hdim hsmall720 CR hCRc
      (Subgroup.mem_inf.mpr ⟨?_, haR⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (ha x hx).symm
  have hZc : Z ≤ Subgroup.centralizer (Z : Set Y) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w _
    exact Subgroup.mem_center_iff.mp hz w
  obtain ⟨A, hZA, hAR, hAc, hAmax⟩ := exists_maximal_abelian Z R hZR hZc
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAc hb) a ha)
  have hRRA : ⁅R, R⁆ ≤ A := hRR.trans hZA
  have hAnorm : ∀ x ∈ R, ∀ a ∈ A, x⁻¹ * a * x ∈ A := by
    intro x hx a ha
    have h1 : ⁅x⁻¹, a⁆ ∈ A := hRRA (Subgroup.commutator_mem_commutator (R.inv_mem hx) (hAR ha))
    have e : x⁻¹ * a * x = ⁅x⁻¹, a⁆ * a := by rw [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem h1 ha
  set L := AlgebraicClosure (ZMod p)
  set σ : Y →* Module.End L (L ⊗[ZMod p] V) := CFSG.Theory.Representation.extendScalars L ρ
    with hσdef
  have hdimL : Module.finrank L (L ⊗[ZMod p] V) ≤ 6 := by
    rw [finrank_baseChange_eq]; exact hdim
  have hcomm : ∀ c d : A, Commute (σ c) (σ d) := fun c d => by
    change σ c * σ d = σ d * σ c
    rw [← map_mul, ← map_mul, hAcomm c c.2 d d.2]
  have hW : (⊤ : Submodule L (L ⊗[ZMod p] V)) ≠ ⊥ := by
    have : Nontrivial (L ⊗[ZMod p] V) := by
      rw [← Module.finrank_pos_iff (R := L), finrank_baseChange_eq]
      exact Module.finrank_pos
    exact top_ne_bot
  obtain ⟨v, -, hv0, χ, hχ⟩ := exists_common_eigenvector_of_isAlgClosed
    (fun c : A => σ c) hcomm ⊤ (fun _ _ _ => Submodule.mem_top) hW
  set χY : Y → L := fun g => if h : g ∈ A then χ ⟨g, h⟩ else 0 with hχY
  have hv : ∀ a ∈ A, σ a v = χY a • v := by
    intro a ha
    rw [hχY]
    simp only [ha, ↓reduceDIte]
    exact hχ ⟨a, ha⟩
  have hZw : ∀ z ∈ Z, χY z = 1 → z = 1 := by
    intro z hz h1
    by_contra hz1
    have hk := ker_sub_one_eq_bot_of_mem_center hρ hirr hz hz1
    have hkL : LinearMap.ker (σ z - 1) = ⊥ := by
      have e : σ z - 1 = (ρ z - 1).baseChange L := by
        rw [baseChange_sub_one]; rfl
      rw [e]
      exact ker_baseChange_eq_bot hk
    have hvk : v ∈ LinearMap.ker (σ z - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hv z (hZA hz), h1,
        one_smul, sub_self]
    rw [hkL, Submodule.mem_bot] at hvk
    exact hv0 hvk
  have hRA : A.relIndex R ≤ 6 := by
    have h := card_le_finrank_of_weights σ A hAcomm (ι := R ⧸ A.subgroupOf R)
      (fun q => ((Quotient.out q : R) : Y)) (fun q a ha => hAnorm _ (Quotient.out q).2 a ha)
      hv0 hv (fun q₁ q₂ h => by
        set x₁ := ((Quotient.out q₁ : R) : Y)
        set x₂ := ((Quotient.out q₂ : R) : Y)
        have hx₁ : x₁ ∈ R := (Quotient.out q₁).2
        have hx₂ : x₂ ∈ R := (Quotient.out q₂).2
        set g := x₁⁻¹ * x₂ with hg
        have hgR : g ∈ R := R.mul_mem (R.inv_mem hx₁) hx₂
        have hgA : g ∈ A := by
          refine hAmax g hgR fun a ha => ?_
          have ha' : x₁ * a * x₁⁻¹ ∈ A := by
            have := hAnorm x₁⁻¹ (R.inv_mem hx₁) a ha
            rwa [inv_inv] at this
          have h1 := h _ ha'
          have e1 : x₁⁻¹ * (x₁ * a * x₁⁻¹) * x₁ = a := by group
          have e2 : x₂⁻¹ * (x₁ * a * x₁⁻¹) * x₂ = g⁻¹ * a * g := by rw [hg]; group
          rw [e1, e2] at h1
          have hgag : g⁻¹ * a * g ∈ A := hAnorm g hgR a ha
          have hd : ⁅g⁻¹, a⁆ ∈ Z :=
            hRR (Subgroup.commutator_mem_commutator (R.inv_mem hgR) (hAR ha))
          have hdw : χY ⁅g⁻¹, a⁆ = 1 := by
            have e3 : ⁅g⁻¹, a⁆ = (g⁻¹ * a * g) * a⁻¹ := by
              rw [commutatorElement_def, inv_inv]
            rw [e3, weight_mul σ hv0 hv hgag (A.inv_mem ha), ← h1,
              ← weight_mul σ hv0 hv ha (A.inv_mem ha), mul_inv_cancel, weight_one σ hv0 hv]
          have h2 := hZw _ hd hdw
          rw [commutatorElement_eq_one_iff_mul_comm] at h2
          calc g * a = g * (g⁻¹ * a) * g := by rw [h2]; group
            _ = a * g := by group
        rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
        change ((Quotient.out q₁ : R) : R ⧸ A.subgroupOf R) = ((Quotient.out q₂ : R) : _)
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [x₁, x₂, g] using hgA)
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact h.trans hdimL
  have hRZp : IsPGroup s (R ⧸ Z.subgroupOf R) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hpow x x.2
  obtain ⟨n, hn⟩ := hRZp.exists_card_eq
  have hn' : Z.relIndex R = s ^ n := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]; exact hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hs).mp
    (hn' ▸ Subgroup.relIndex_dvd_of_le_left R hZA)
  have hm1 : 1 ≤ m := by
    by_contra h0
    push Not at h0
    have : m = 0 := by omega
    rw [this, pow_zero, Subgroup.relIndex_eq_one] at hm
    exact hRnc fun a ha b hb => hAcomm a (hm ha) b (hm hb)
  have hexp := pow_eq_one_of_mem_commutator hRR hpow
  have hR' : Nat.card (⁅R, R⁆ : Subgroup Y) ≤ s := by
    have hwpow : ∀ a ∈ A, ∀ k : ℕ, χY (a ^ k) = χY a ^ k := by
      intro a ha k
      induction k with
      | zero => rw [pow_zero, pow_zero, weight_one σ hv0 hv]
      | succ k ih =>
        rw [pow_succ, weight_mul σ hv0 hv (A.pow_mem ha k) ha, ih, pow_succ]
    let f : (⁅R, R⁆ : Subgroup Y) → Polynomial.nthRootsFinset s (1 : L) := fun c =>
      ⟨χY c, by
        rw [Polynomial.mem_nthRootsFinset hs.pos, ← hwpow _ (hRRA c.2), hexp c c.2,
          weight_one σ hv0 hv]⟩
    have hf : Function.Injective f := by
      intro c d hcd
      have h1 : χY (c : Y) = χY (d : Y) := congrArg Subtype.val hcd
      apply Subtype.ext
      have hdinv : χY ((d : Y)⁻¹) * χY (d : Y) = 1 := by
        rw [← weight_mul σ hv0 hv (A.inv_mem (hRRA d.2)) (hRRA d.2), inv_mul_cancel,
          weight_one σ hv0 hv]
      have h2 : χY ((d : Y)⁻¹ * c) = 1 := by
        rw [weight_mul σ hv0 hv (A.inv_mem (hRRA d.2)) (hRRA c.2), h1, hdinv]
      have h3 := hZw _ (hRR ((⁅R, R⁆ : Subgroup Y).mul_mem (Subgroup.inv_mem _ d.2) c.2)) h2
      exact (inv_mul_eq_one.mp h3).symm
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_finsetCard] at h1
    refine h1.trans ?_
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots s 1)
  have hAZ := relIndex_le_of_commutator hAR hAc hRR
    (fun a ha hax => hZRc a (hAR ha) hax) hs hm hR'
  have hn2 : s ^ n ≤ s ^ m * s ^ m := by
    rw [← hn', ← Subgroup.relIndex_mul_relIndex Z A R hZA hAR, hm]
    exact Nat.mul_le_mul_right _ hAZ
  let C : Subgroup Y :=
    { carrier := {c | ∀ x ∈ R, c * x * c⁻¹ * x⁻¹ ∈ Z}
      one_mem' := fun x _ => by simp
      mul_mem' := fun {c c'} hc hc' x hx => by
        have hu := hc' x hx
        have hu' := Subgroup.mem_center_iff.mp hu
        have e : c * c' * x * (c * c')⁻¹ * x⁻¹ =
            (c' * x * c'⁻¹ * x⁻¹) * (c * x * c⁻¹ * x⁻¹) := by
          calc c * c' * x * (c * c')⁻¹ * x⁻¹
              = c * ((c' * x * c'⁻¹ * x⁻¹) * x) * c⁻¹ * x⁻¹ := by group
            _ = (c' * x * c'⁻¹ * x⁻¹) * (c * x * c⁻¹ * x⁻¹) := by
                rw [← mul_assoc c, hu' c]; group
        change c * c' * x * (c * c')⁻¹ * x⁻¹ ∈ Z
        rw [e]
        exact Z.mul_mem hu (hc x hx)
      inv_mem' := fun {c} hc x hx => by
        have h1 := hc (c⁻¹ * x * c) (by
          have := (inferInstance : R.Normal).conj_mem x hx c⁻¹
          rwa [inv_inv] at this)
        have e : c⁻¹ * x * c⁻¹⁻¹ * x⁻¹ = (c * (c⁻¹ * x * c) * c⁻¹ * (c⁻¹ * x * c)⁻¹)⁻¹ := by
          group
        change c⁻¹ * x * c⁻¹⁻¹ * x⁻¹ ∈ Z
        rw [e]
        exact Z.inv_mem h1 }
  have hCn : C.Normal := ⟨fun c hc g x hx => by
    have h1 := hc (g⁻¹ * x * g) (by
      have := (inferInstance : R.Normal).conj_mem x hx g⁻¹
      rwa [inv_inv] at this)
    have h2 := (inferInstance : Z.Normal).conj_mem _ h1 g
    have e : g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ * x⁻¹ =
        g * (c * (g⁻¹ * x * g) * c⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2⟩
  have hCidx := index_le_of_generators C (fun c hc => hc) hs hn'
  have hlt := pow_le_sixteen_or_lt_4080 hs.two_le hm1 (hm ▸ hRA) hn2
  have hCtop : C = ⊤ := by
    by_contra hCne
    have h4080 := hsmall C hCn hCne
    have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rcases hlt with h16 | hlt
    · have hdvd : C.index ∣ (s ^ n).factorial := by
        have := index_dvd_factorial_of_center hZR C (fun c hc => hc)
        rwa [hn'] at this
      have h17 : 17 ∣ (s ^ n).factorial :=
        (show 17 ∣ 4080 by norm_num).trans (h4080.trans hdvd)
      have h18 := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 17)).mp h17
      omega
    · have h1 : C.index < 4080 := lt_of_le_of_lt hCidx hlt
      have h2 := Nat.le_of_dvd hpos h4080
      omega
  obtain ⟨y, x, hx, hyx⟩ := hact
  have hyC : y ∈ C := by rw [hCtop]; exact Subgroup.mem_top y
  exact hyx (hyC x hx)

end Irreducible

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
