module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open scoped IsMulCommutative

theorem exists_fixed_in_coset_uc6 {Mg : Type*} [Group Mg] [Finite Mg] {p : ℕ} [Fact p.Prime]
    (X F : Subgroup Mg) (hX : IsPGroup p X) (hF : ¬ p ∣ Nat.card F)
    (hFX : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F) (q : Mg)
    (hq : ∀ x ∈ X, q⁻¹ * (x * q * x⁻¹) ∈ F) :
    ∃ n : Mg, q⁻¹ * n ∈ F ∧ ∀ x ∈ X, x * n * x⁻¹ = n := by
  have hmem : ∀ x ∈ X, ∀ z : Mg, q⁻¹ * z ∈ F → q⁻¹ * (x * z * x⁻¹) ∈ F := by
    intro x hx z hz
    have e : q⁻¹ * (x * z * x⁻¹) = (q⁻¹ * (x * q * x⁻¹)) * (x * (q⁻¹ * z) * x⁻¹) := by group
    rw [e]
    exact F.mul_mem (hq x hx) (hFX x hx _ hz)
  letI : MulAction ↥X {z : Mg // q⁻¹ * z ∈ F} :=
    { smul := fun x z => ⟨(x : Mg) * z.1 * (x : Mg)⁻¹, hmem x x.2 z.1 z.2⟩
      one_smul := fun z => Subtype.ext (by
        show ((1 : ↥X) : Mg) * z.1 * ((1 : ↥X) : Mg)⁻¹ = z.1
        simp)
      mul_smul := fun x y z => Subtype.ext (by
        show ((x * y : ↥X) : Mg) * z.1 * ((x * y : ↥X) : Mg)⁻¹ =
          (x : Mg) * ((y : Mg) * z.1 * (y : Mg)⁻¹) * (x : Mg)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card {z : Mg // q⁻¹ * z ∈ F} = Nat.card F :=
    Nat.card_congr
      { toFun := fun z => ⟨q⁻¹ * z.1, z.2⟩
        invFun := fun f => ⟨q * f.1, by simp⟩
        left_inv := fun z => Subtype.ext (by simp)
        right_inv := fun f => Subtype.ext (by simp) }
  obtain ⟨z, hz⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card
    {z : Mg // q⁻¹ * z ∈ F} (by rw [hcard]; exact hF)
  refine ⟨z.1, z.2, fun x hx => ?_⟩
  have := MulAction.mem_fixedPoints.1 hz ⟨x, hx⟩
  exact congrArg Subtype.val this

section Rep

variable {Mg : Type} [Group Mg] [Finite Mg] (Q₀ : Subgroup Mg) [Q₀.Normal]

@[expose] noncomputable def frattiniAct : Mg →* MulAut (↥Q₀ ⧸ frattini ↥Q₀) :=
  (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Q₀)).comp
    MulAut.conjNormal

theorem frattiniAct_mk (g : Mg) (q : ↥Q₀) :
    frattiniAct Q₀ g (q : ↥Q₀ ⧸ frattini ↥Q₀) =
      ((MulAut.conjNormal g q : ↥Q₀) : ↥Q₀ ⧸ frattini ↥Q₀) :=
  CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply (frattini ↥Q₀)
    (MulAut.conjNormal g) q

@[expose, instance_reducible] noncomputable def frattiniMDMA : MulDistribMulAction Mg (↥Q₀ ⧸ frattini ↥Q₀) :=
  MulDistribMulAction.compHom _ (frattiniAct Q₀)

variable [IsElementaryAbelian 2 (↥Q₀ ⧸ frattini ↥Q₀)]

@[expose] noncomputable def frattiniRep :
    Representation (ZMod 2) Mg (Additive (↥Q₀ ⧸ frattini ↥Q₀)) :=
  letI := frattiniMDMA Q₀
  CFSG.Theory.Representation.ofElementaryAbelianAction (A := Mg)
    (G := ↥Q₀ ⧸ frattini ↥Q₀) (p := 2)

theorem frattiniRep_apply_mk (g : Mg) (q : ↥Q₀) :
    frattiniRep Q₀ g (Additive.ofMul (q : ↥Q₀ ⧸ frattini ↥Q₀)) =
      Additive.ofMul ((MulAut.conjNormal g q : ↥Q₀) : ↥Q₀ ⧸ frattini ↥Q₀) := by
  letI := frattiniMDMA Q₀
  unfold frattiniRep
  rw [CFSG.Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
  exact congrArg Additive.ofMul (frattiniAct_mk Q₀ g q)

end Rep

section Kernel

variable {Mg : Type} [Group Mg] [Finite Mg] (Q₀ : Subgroup Mg) [Q₀.Normal]

theorem eq_one_of_odd_orderOf_of_fix_uc6 (hQ : IsPGroup 2 Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {x : Mg} (hx : Odd (orderOf x))
    (hfix : ∀ q : ↥Q₀, ((MulAut.conjNormal x q : ↥Q₀) : ↥Q₀ ⧸ frattini ↥Q₀) =
      (q : ↥Q₀ ⧸ frattini ↥Q₀)) : x = 1 := by
  have hker := (CFSG.GroupTheory.frattini_automorphism_kernel hQ).2
  have hg : (MulAut.conjNormal x : MulAut ↥Q₀) ∈
      (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Q₀)).ker :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel
      (frattini ↥Q₀) _).2 (fun q => hfix q)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hker ⟨_, hg⟩
  have hord1 : orderOf (MulAut.conjNormal x : MulAut ↥Q₀) = 2 ^ k := by
    rw [← hk]; exact (Subgroup.orderOf_mk _ _).symm
  have hdvd : orderOf (MulAut.conjNormal x : MulAut ↥Q₀) ∣ orderOf x := orderOf_map_dvd _ x
  rw [hord1] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf x := (dvd_pow_self 2 hne).trans hdvd
    exact (Nat.not_even_iff_odd.2 hx) (even_iff_two_dvd.2 h2)
  have hg1 : (MulAut.conjNormal x : MulAut ↥Q₀) = 1 :=
    orderOf_eq_one_iff.1 (by rw [hord1, hk0]; rfl)
  have hxQ : x ∈ Q₀ := by
    apply hchar
    rw [mem_centralizer_iff]
    intro h hh
    have h1 := congrArg Subtype.val (MulEquiv.congr_fun hg1 (⟨h, hh⟩ : ↥Q₀))
    rw [MulAut.conjNormal_apply] at h1
    have h2 : x * h * x⁻¹ = h := h1
    calc h * x = (x * h * x⁻¹) * x := by rw [h2]
      _ = x * h := by group
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hQ ⟨x, hxQ⟩
  rw [Subgroup.orderOf_mk] at hm
  have hm0 : m = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf x := by rw [hm]; exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hx) (even_iff_two_dvd.2 h2)
  exact orderOf_eq_one_iff.1 (by rw [hm, hm0]; rfl)

end Kernel

section Fixed

open scoped IsMulCommutative
open CFSG.RankThree.FFModules (fixSub)

variable {Mg : Type} [Group Mg] [Finite Mg] (Q₀ : Subgroup Mg) [Q₀.Normal]
  [IsElementaryAbelian 2 (↥Q₀ ⧸ frattini ↥Q₀)]

theorem finrank_fixSub_le_uc6 (hQ : IsPGroup 2 Q₀) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (X : Subgroup Mg) (hX : IsPGroup p X)
    (hfix : Nat.card ↥(Q₀ ⊓ centralizer (X : Set Mg)) ≤ 2) :
    Module.finrank (ZMod 2) (fixSub (frattiniRep Q₀) X) ≤ 1 := by
  set F : Subgroup Mg := (frattini ↥Q₀).map Q₀.subtype with hF
  have hFQ : F ≤ Q₀ := Subgroup.map_subtype_le _
  have hFcard : ¬ p ∣ Nat.card F := by
    intro hdvd
    have h1 : Nat.card F ∣ Nat.card Q₀ := Subgroup.card_dvd_of_le hFQ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have : p ∣ 2 ^ n := by rw [← hn]; exact hdvd.trans h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1
      (Fact.out (p := p.Prime) |>.dvd_of_dvd_pow this))
  have hFX : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F := by
    intro x _ f hf
    obtain ⟨φ, hφ, rfl⟩ := hf
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (frattini ↥Q₀).Characteristic) (MulAut.conjNormal x)
    have : (MulAut.conjNormal x φ : ↥Q₀) ∈ frattini ↥Q₀ := by
      rw [← hmap]; exact ⟨φ, hφ, rfl⟩
    refine ⟨_, this, ?_⟩
    simp [MulAut.conjNormal_apply]
  have hsurj : ∀ v : Additive (↥Q₀ ⧸ frattini ↥Q₀), ∃ q : ↥Q₀,
      v = Additive.ofMul (q : ↥Q₀ ⧸ frattini ↥Q₀) := by
    intro v
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨q, by rw [hq]; rfl⟩
  have key : ∀ v ∈ fixSub (frattiniRep Q₀) X, ∃ n : ↥(Q₀ ⊓ centralizer (X : Set Mg)),
      v = Additive.ofMul ((⟨n.1, n.2.1⟩ : ↥Q₀) : ↥Q₀ ⧸ frattini ↥Q₀) := by
    intro v hv
    obtain ⟨q, rfl⟩ := hsurj v
    have hq : ∀ x ∈ X, (q : Mg)⁻¹ * (x * q * x⁻¹) ∈ F := by
      intro x hx
      have h1 := hv x hx
      rw [frattiniRep_apply_mk] at h1
      have h2 : ((MulAut.conjNormal x q : ↥Q₀) : ↥Q₀ ⧸ frattini ↥Q₀) =
          (q : ↥Q₀ ⧸ frattini ↥Q₀) := Additive.ofMul.injective h1
      have h3 := QuotientGroup.eq.1 h2.symm
      refine ⟨_, h3, ?_⟩
      simp [MulAut.conjNormal_apply]
    obtain ⟨n, hn1, hn2⟩ := exists_fixed_in_coset_uc6 X F hX hFcard hFX (q : Mg) hq
    have hnQ : n ∈ Q₀ := by
      have : (q : Mg)⁻¹ * n ∈ Q₀ := hFQ hn1
      have h2 := Q₀.mul_mem q.2 this
      simpa using h2
    have hnC : n ∈ centralizer (X : Set Mg) := by
      rw [mem_centralizer_iff]
      intro h hh
      have := hn2 h hh
      calc h * n = (h * n * h⁻¹) * h := by group
        _ = n * h := by rw [this]
    refine ⟨⟨n, hnQ, hnC⟩, ?_⟩
    congr 1
    apply QuotientGroup.eq.2
    obtain ⟨φ, hφ, hφn⟩ := hn1
    have : φ = ((⟨q, q.2⟩ : ↥Q₀))⁻¹ * ⟨n, hnQ⟩ := Subtype.ext (by simpa using hφn)
    rw [← this]; exact hφ
  classical
  choose s hs using key
  have hinj : Function.Injective
      (fun v : ↥(fixSub (frattiniRep Q₀) X) => s v.1 v.2) := by
    intro v w hvw
    have e : s v.1 v.2 = s w.1 w.2 := hvw
    apply Subtype.ext
    calc v.1 = Additive.ofMul ((⟨(s v.1 v.2).1, (s v.1 v.2).2.1⟩ : ↥Q₀) :
          ↥Q₀ ⧸ frattini ↥Q₀) := hs v.1 v.2
      _ = Additive.ofMul ((⟨(s w.1 w.2).1, (s w.1 w.2).2.1⟩ : ↥Q₀) :
          ↥Q₀ ⧸ frattini ↥Q₀) := by rw [e]
      _ = w.1 := (hs w.1 w.2).symm
  have hcard1 : Nat.card ↥(fixSub (frattiniRep Q₀) X) ≤ 2 :=
    (Nat.card_le_card_of_injective _ hinj).trans hfix
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard1
  by_contra hne
  push Not at hne
  have : 2 ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) ↥(fixSub (frattiniRep Q₀) X) :=
    Nat.pow_le_pow_right (by norm_num) hne
  omega

end Fixed

section Transport

open scoped IsMulCommutative
open CFSG.RankThree.FFModules (fixSub)

variable {Mg : Type} [Group Mg] [Finite Mg]

theorem odd_orderOf_of_mem_pGroup_uc6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup Mg}
    (hP : IsPGroup p P) {z : Mg} (hz : z ∈ P) : Odd (orderOf z) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP ⟨z, hz⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

variable (Q₀ : Subgroup Mg) [Q₀.Normal] [IsElementaryAbelian 2 (↥Q₀ ⧸ frattini ↥Q₀)]

theorem eq_one_of_odd_of_rep_eq_one_uc6 (hQ : IsPGroup 2 Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {x : Mg} (hx : Odd (orderOf x))
    (h : frattiniRep Q₀ x = 1) : x = 1 :=
  eq_one_of_odd_orderOf_of_fix_uc6 Q₀ hQ hchar hx (fun q => by
    have := congrArg (fun f => f (Additive.ofMul (q : ↥Q₀ ⧸ frattini ↥Q₀))) h
    simp only [frattiniRep_apply_mk, Module.End.one_apply] at this
    exact Additive.ofMul.injective this)

theorem k47_transport_uc6 (hK : UCK.K47) (hMg : CFSG.Open.IsKGroup Mg)
    (Q₀ : Subgroup Mg) [Q₀.Normal] (hQ : IsPGroup 2 Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (X : Subgroup Mg) (hXcard : Nat.card X = p)
    (hfix : Nat.card ↥(Q₀ ⊓ centralizer (X : Set Mg)) ≤ 2)
    (P : Subgroup Mg) (hP : IsPGroup p P) (hXP : X ≤ P) (y : Mg) (hy : y ∈ P)
    (hyc : ∀ x ∈ X, ∀ w ∈ P, (y * x * y⁻¹ * x⁻¹) * w = w * (y * x * y⁻¹ * x⁻¹)) :
    ∀ x ∈ X, y * x = x * y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsElementaryAbelian 2 (↥Q₀ ⧸ frattini ↥Q₀) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hQ).2.2.2.1
  set ρ := frattiniRep Q₀ with hρ
  set N : Subgroup Mg := ρ.ker with hN
  haveI hNn : N.Normal := MonoidHom.normal_ker ρ
  have hGK : CFSG.Open.IsKGroup (Mg ⧸ N) := hMg.quotient N
  set ρ' : Representation (ZMod 2) (Mg ⧸ N) (Additive (↥Q₀ ⧸ frattini ↥Q₀)) :=
    QuotientGroup.lift N ρ (fun x hx => hx) with hρ'
  have hρ'mk : ∀ g : Mg, ρ' (QuotientGroup.mk' N g) = ρ g := fun g => rfl
  have hinj : Function.Injective ρ' := by
    intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N b
    rw [hρ'mk, hρ'mk] at hab
    apply QuotientGroup.eq.2
    show a⁻¹ * b ∈ ρ.ker
    rw [MonoidHom.mem_ker, map_mul, ← hab, ← map_mul, inv_mul_cancel, map_one]
  have hXp : IsPGroup p X := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hXcard)
  have hPodd : ∀ z ∈ P, Odd (orderOf z) := fun z hz =>
    odd_orderOf_of_mem_pGroup_uc6 hp hp2 hP hz
  have hPN : ∀ z ∈ P, z ∈ N → z = 1 := fun z hz hzN =>
    eq_one_of_odd_of_rep_eq_one_uc6 Q₀ hQ hchar (hPodd z hz) hzN
  set D : Subgroup (Mg ⧸ N) := X.map (QuotientGroup.mk' N) with hD
  have hDcard : Nat.card D = p := by
    have hdvd : Nat.card D ∣ Nat.card X := Subgroup.card_map_dvd X _
    rw [hXcard] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exfalso
      have hDbot : D = ⊥ := Subgroup.card_eq_one.1 h1
      obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : Nat.card X = 1 := Subgroup.card_eq_one.2 (eq_bot_iff.2 fun x hx => by
          rw [Subgroup.mem_bot]; exact hcon x hx)
        rw [hXcard] at this
        exact hp.ne_one this
      have hmem : (QuotientGroup.mk' N x) ∈ D := ⟨x, hxX, rfl⟩
      rw [hDbot, Subgroup.mem_bot] at hmem
      exact hx1 (hPN x (hXP hxX) ((QuotientGroup.eq_one_iff x).1 hmem))
    · exact h1
  have hfD : Module.finrank (ZMod 2) (fixSub ρ' D) ≤ 1 := by
    have h1 := finrank_fixSub_le_uc6 Q₀ hQ hp2 X hXp hfix
    have heq : fixSub ρ' D = fixSub ρ X := by
      ext v
      constructor
      · intro hv x hx
        have := hv (QuotientGroup.mk' N x) ⟨x, hx, rfl⟩
        rw [hρ'mk] at this
        exact this
      · intro hv d hd
        obtain ⟨x, hx, rfl⟩ := hd
        have := hv x hx
        rw [hρ'mk]
        exact this
    rw [heq]; exact h1
  obtain ⟨q', hq'pr, hq'2, hq'p⟩ : ∃ q' : ℕ, q'.Prime ∧ q' ≠ 2 ∧ q' ≠ p := by
    obtain ⟨q', hge, hpr⟩ := Nat.exists_infinite_primes (p + 3)
    exact ⟨q', hpr, by omega, by omega⟩
  have hk := (hK (Mg ⧸ N) hGK (Additive (↥Q₀ ⧸ frattini ↥Q₀)) ρ' hinj
    q' p hq'pr hp hq'2 hp2 hq'p D hDcard hfD).1
  set R : Subgroup (Mg ⧸ N) := P.map (QuotientGroup.mk' N) with hR
  have hRp : IsPGroup p R := hP.map _
  have hDR : D ≤ R := Subgroup.map_mono hXP
  have hcR : (QuotientGroup.mk' N y) ∈ R := ⟨y, hy, rfl⟩
  have hcomm : ∀ d ∈ D, (QuotientGroup.mk' N y) * d * (QuotientGroup.mk' N y)⁻¹ * d⁻¹ ∈
      (Subgroup.center ↥R).map R.subtype := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := hd
    have hcP : y * x * y⁻¹ * x⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hy (hXP hx)) (P.inv_mem hy)) (P.inv_mem (hXP hx))
    have hRz : (QuotientGroup.mk' N (y * x * y⁻¹ * x⁻¹)) ∈ R := ⟨_, hcP, rfl⟩
    refine ⟨⟨QuotientGroup.mk' N (y * x * y⁻¹ * x⁻¹), hRz⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, hwP, hw⟩ := g.2
      apply Subtype.ext
      show (g : Mg ⧸ N) * QuotientGroup.mk' N (y * x * y⁻¹ * x⁻¹) =
        QuotientGroup.mk' N (y * x * y⁻¹ * x⁻¹) * (g : Mg ⧸ N)
      rw [← hw, ← map_mul, ← map_mul]
      congr 1
      exact (hyc x hx w hwP).symm
    · show QuotientGroup.mk' N (y * x * y⁻¹ * x⁻¹) = _
      simp
  intro x hx
  have h1 := hk R hRp hDR _ hcR hcomm (QuotientGroup.mk' N x) ⟨x, hx, rfl⟩
  have h2 : QuotientGroup.mk' N (y * x) = QuotientGroup.mk' N (x * y) := by
    simpa using h1
  have h3 : (y * x)⁻¹ * (x * y) ∈ N := QuotientGroup.eq.1 h2
  have h4 : (y * x)⁻¹ * (x * y) ∈ P :=
    P.mul_mem (P.inv_mem (P.mul_mem hy (hXP hx))) (P.mul_mem (hXP hx) hy)
  have h5 := hPN _ h4 h3
  exact inv_mul_eq_one.1 h5 |>.symm |>.symm ▸ (inv_mul_eq_one.1 h5).symm

end Transport

end CFSG.LocalAnalysis.UniquenessCase.UC6
