module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transfer

variable {G : Type} [Group G] [Finite G]

section TransferHelpers

theorem ggTorusTBGroup_of_marking {p r : ℕ} (hp : p.Prime) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range) :
    GGTorusTBGroup p r R I X (ggQuotHom θ) (ggGamma X hBsN).range := by
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 (b : G) b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p (ggGamma X hBsN).range :=
    isElemAbelian_range hBc hBp (ggGamma X hBsN)
  have hAI : ∀ a ∈ (ggGamma X hBsN).range, ∃ φ ∈ I, ∀ l : X,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, hBsI b b.2, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  exact ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hX, hA, hAI, hr, h3,
    ggTorusSelfCent_ggGamma hBsN hSC⟩

theorem ggReflection_overGamma_of_induced {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {t : MulAut ↥Bs} (ht : t ∈ ggInduced X Bs)
    (htr : GGIsReflection p t) :
    ∃ (n : X) (hn : MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma X hBsN).range : Set (MulAut ↥X))),
      GGOverGamma hBsN t (ggConjAut (ggGamma X hBsN).range hn) ∧
        GGIsReflection p (ggConjAut (ggGamma X hBsN).range hn) ∧
        ggConjAut (ggGamma X hBsN).range hn ∈
          ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hBsN).range := by
  classical
  obtain ⟨g, hgX, hg, htg⟩ := ht
  have ht_eq : t = ggConjAut Bs hg := MulEquiv.ext fun b => Subtype.ext (htg b)
  have hn := conj_mem_normalizer_range_ggGamma hBsN hgX hg
  have hov : GGOverGamma hBsN t (ggConjAut (ggGamma X hBsN).range hn) := by
    rw [ht_eq]
    exact ggOverGamma_conjAut hgX hg
  refine ⟨⟨g, hgX⟩, hn, hov, ?_, ?_⟩
  · rcases isReflection_or_eq_one_of_overGamma hp hp2 hBs hBsN hov htr with h | h
    · exact h
    · exfalso
      have ht2 : ∀ x : ↥Bs, t (t x) = x := by
        intro x
        have := congrArg (fun φ : MulAut ↥Bs => φ x) htr.1
        simpa [pow_two, MulAut.mul_apply] using this
      have hfix : ∀ b : ↥Bs, t b = b := by
        intro b
        have hbγ : ggGamma X hBsN (t b) = ggGamma X hBsN b := by
          have h1 := congrArg Subtype.val (hov b)
          rw [h, MulAut.one_apply] at h1
          simpa using h1
        set u : ↥Bs := t b * b⁻¹ with hu
        have huγ : ggGamma X hBsN u = 1 := by
          rw [hu, map_mul, map_inv, hbγ, mul_inv_cancel]
        have huC : (u : G) ∈ Subgroup.centralizer (X : Set G) :=
          (ggGamma_eq_one_iff X hBsN u).mp huγ
        have htu : t u = u⁻¹ := by
          rw [hu, map_mul, map_inv, ht2]
          group
        have hufix : t u = u := by
          apply Subtype.ext
          rw [ht_eq, ggConjAut_apply, Subgroup.mem_centralizer_iff.mp huC g hgX,
            mul_inv_cancel_right]
        have huu : u = u⁻¹ := hufix.symm.trans htu
        have hu2 : u ^ 2 = 1 := by
          rw [pow_two]
          nth_rewrite 2 [huu]
          exact mul_inv_cancel u
        have hup : u ^ p = 1 := Subtype.ext (by simpa using hBs.2 (u : G) u.2)
        have hcop : Nat.Coprime 2 p :=
          (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
        have hord : orderOf u = 1 := by
          have h2 := orderOf_dvd_of_pow_eq_one hu2
          have hp' := orderOf_dvd_of_pow_eq_one hup
          have h := Nat.dvd_gcd h2 hp'
          rw [Nat.Coprime.gcd_eq_one hcop] at h
          exact Nat.dvd_one.mp h
        have hu1' : u = 1 := orderOf_eq_one_iff.mp hord
        rw [hu] at hu1'
        exact mul_inv_eq_one.mp hu1'
      have ht_one : t = 1 := MulEquiv.ext hfix
      have hcardBs : Nat.card {b : ↥Bs // t b = b} = Nat.card ↥Bs :=
        Nat.card_congr (Equiv.subtypeUnivEquiv fun b => by rw [ht_one, MulAut.one_apply])
      have hcard : Nat.card ↥Bs * p = Nat.card ↥Bs := by
        calc Nat.card ↥Bs * p = Nat.card {b : ↥Bs // t b = b} * p := by rw [hcardBs]
          _ = Nat.card ↥Bs := htr.2
      have hp1 : p = 1 :=
        Nat.mul_left_cancel (Nat.card_pos (α := ↥Bs)) (by simpa using hcard)
      exact (ne_of_gt hp.one_lt) hp1
  · exact ggConjAut_mem_ggAutomizer
      (H := (MulAut.conj : ↥X →* MulAut ↥X).range) ⟨⟨g, hgX⟩, rfl⟩ hn

private theorem exists_lift_pi {p : ℕ} (hp : p.Prime) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {m : ℕ}
    (π₀ : (Fin m → ℤ) →+ Additive ↥(ggGamma X hBsN).range) :
    ∃ π : (Fin m → ℤ) →+ Additive ↥Bs, ∀ y : Fin m → ℤ,
      (ggGamma X hBsN).rangeRestrict (Additive.toMul (π y)) = Additive.toMul (π₀ y) := by
  classical
  let γ := ggGamma X hBsN
  letI : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with
      mul_comm := fun a b => Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2) }
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b => mul_comm a b
  have hBp : ∀ a : ↥Bs, a ^ p = 1 := fun a => Subtype.ext (by simpa using hBs.2 (a : G) a.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  letI : CommGroup ↥γ.range :=
    { (inferInstance : Group ↥γ.range) with
      mul_comm := fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2) }
  have hγsurj : Function.Surjective γ.rangeRestrict := MonoidHom.rangeRestrict_surjective γ
  let addγ : Additive ↥Bs →+ Additive ↥γ.range :=
    { toFun := fun x => Additive.ofMul (γ.rangeRestrict (Additive.toMul x))
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [toMul_add, map_mul]
        rfl }
  have hsurj : Function.Surjective addγ := by
    intro w
    obtain ⟨b, hb⟩ := hγsurj (Additive.toMul w)
    refine ⟨Additive.ofMul b, ?_⟩
    show Additive.ofMul (γ.rangeRestrict (Additive.toMul (Additive.ofMul b))) = w
    rw [toMul_ofMul, hb, ofMul_toMul]
  haveI : Module.Free ℤ (Fin m → ℤ) := Module.Free.of_basis (Pi.basisFun ℤ (Fin m))
  haveI : Module.Projective ℤ (Fin m → ℤ) := Module.Projective.of_free
  obtain ⟨h, hh⟩ := Module.projective_lifting_property addγ.toIntLinearMap π₀.toIntLinearMap hsurj
  refine ⟨h.toAddMonoidHom, fun y => ?_⟩
  have hy := congrArg (fun f : (Fin m → ℤ) →ₗ[ℤ] Additive ↥γ.range => f y) hh
  simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap] at hy
  simpa [addγ] using congrArg Additive.toMul hy

end TransferHelpers

theorem ggAutLattice_of_marking {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range) (hT : GGTorusLattice p r R I) :
    GGAutLattice p Bs X := by
  classical
  obtain ⟨m, Q, π₀, hQ, hsurj₀, hrefl₀⟩ :=
    hT X (ggQuotHom θ) (ggGamma X hBsN).range
      (ggTorusTBGroup_of_marking hp hBs hSC hX θ hBsN hBsI hr h3)
  obtain ⟨π, hπ⟩ := exists_lift_pi hp hBs hBsN π₀
  refine ⟨m, Q, π, hQ, ?_, ?_⟩
  · intro b
    obtain ⟨y, hy⟩ := hsurj₀ (Additive.ofMul ((ggGamma X hBsN).rangeRestrict b))
    refine ⟨y, ?_⟩
    have h1 : (ggGamma X hBsN).rangeRestrict (Additive.toMul (π y)) =
        (ggGamma X hBsN).rangeRestrict b := by
      rw [hπ y, hy, toMul_ofMul]
    have h2 : ggGamma X hBsN (Additive.toMul (π y)) = ggGamma X hBsN b := by
      simpa using congrArg Subtype.val h1
    have h3 : ggGamma X hBsN ((Additive.toMul (π y))⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have h4 := (ggGamma_eq_one_iff X hBsN ((Additive.toMul (π y))⁻¹ * b)).mp h3
    simpa using h4
  · intro t ht htr
    obtain ⟨n, hn, hov, hrefl, hmem⟩ :=
      ggReflection_overGamma_of_induced hp hp2 hBs hBsN ht htr
    obtain ⟨w, hw, hφ⟩ := hrefl₀ (ggConjAut (ggGamma X hBsN).range hn) hmem hrefl
    refine ⟨w, hw, fun y => ?_⟩
    have h1 : ggGamma X hBsN (t (Additive.toMul (π y))) =
        ggGamma X hBsN (Additive.toMul (π (ggLatRefl Q w y))) := by
      have h2 := hov (Additive.toMul (π y))
      rw [hπ y, hφ y, ← hπ (ggLatRefl Q w y)] at h2
      simpa using congrArg Subtype.val h2
    have h3 : ggGamma X hBsN
        ((t (Additive.toMul (π y)))⁻¹ * Additive.toMul (π (ggLatRefl Q w y))) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h4 := (ggGamma_eq_one_iff X hBsN _).mp h3
    simpa using h4

theorem ggNoRefl_of_marking {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range) (hT : GGTorusNoRefl p r R I) :
    ∀ t ∈ ggInduced X Bs, ¬ GGIsReflection p t := by
  classical
  intro t ht htr
  obtain ⟨n, hn, -, hrefl, hmem⟩ :=
    ggReflection_overGamma_of_induced hp hp2 hBs hBsN ht htr
  exact hT X (ggQuotHom θ) (ggGamma X hBsN).range
    (ggTorusTBGroup_of_marking hp hBs hSC hX θ hBsN hBsI hr h3)
    (ggConjAut (ggGamma X hBsN).range hn) hmem hrefl

end Transfer

end CFSG.StandardType
