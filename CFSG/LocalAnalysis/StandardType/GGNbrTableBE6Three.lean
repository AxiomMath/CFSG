module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelData
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBWeylOn
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrderRestOn
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc.E6Three

namespace CFSG.StandardType

private def hypE6Wit (i : Fin Tag.E6.rank) : Fin Tag.E6.rank → ZMod 3 :=
  ![![1, 0, 0, 0, 2, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 2],
    ![0, 0, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![0, 0, 2, 0, 0, 1]] i

private lemma hypE6Wit_mem (i : Fin Tag.E6.rank) :
    hypE6Wit i ∈ CFSG.StandardType.NoOffRest.hypE6 := by
  rw [CFSG.StandardType.NoOffRest.mem_hypE6]
  fin_cases i <;> decide

private lemma hypE6Wit_self (i : Fin Tag.E6.rank) : hypE6Wit i i = 1 := by
  fin_cases i <;> decide

theorem adRefl_eq_self_iff (i : Fin Tag.E6.rank) (v : Fin Tag.E6.rank → ZMod 3) :
    adRefl .E6 3 i v = v ↔ v i = 0 := by
  constructor
  · intro h
    have hi := congrFun h i
    simp only [adRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [show ((Tag.E6.cartan i i : ℤ) : ZMod 3) = 2 by
      rw [cartan_diag]; norm_num] at hi
    have h2' : v i * 2 = 0 := sub_eq_self.mp hi
    have h2 : (2 : ZMod 3) * v i = 0 := by rwa [mul_comm] at h2'
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  · intro h
    funext j
    simp [adRefl, h]

theorem card_fix_adRefl_mul_three (G : AddSubgroup (Fin Tag.E6.rank → ZMod 3))
    (hG : G = ⊤ ∨ G = CFSG.StandardType.NoOffRest.hypE6) (i : Fin Tag.E6.rank) :
    Nat.card {v : G // adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) = v} * 3 = Nat.card G := by
  classical
  let f : G →+ ZMod 3 :=
    { toFun := fun v => (v : Fin Tag.E6.rank → ZMod 3) i
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hker : Nat.card {v : G // adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) = v} =
      Nat.card f.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    show adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) = v ↔ f v = 0
    rw [adRefl_eq_self_iff]
    rfl
  have hrange : f.range = ⊤ := by
    have h1 : (1 : ZMod 3) ∈ f.range := by
      rcases hG with htop | hhyp
      · refine ⟨⟨hypE6Wit i, ?_⟩, ?_⟩
        · rw [htop]; exact AddSubgroup.mem_top _
        · simp [f, hypE6Wit_self i]
      · refine ⟨⟨hypE6Wit i, ?_⟩, ?_⟩
        · rw [hhyp]; exact hypE6Wit_mem i
        · simp [f, hypE6Wit_self i]
    haveI : Fact (Nat.Prime (Nat.card (ZMod 3))) :=
      ⟨by rw [Nat.card_zmod]; exact Nat.prime_three⟩
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card f.range with hbot | htop
    · rw [hbot] at h1
      exfalso
      have h10 : (1 : ZMod 3) = 0 := by simpa using h1
      exact absurd h10 (by decide)
    · exact htop
  have hfcard : Nat.card f.range = 3 := by
    rw [hrange, AddSubgroup.card_top, Nat.card_zmod]
  have hcard := AddSubgroup.card_ker_mul_card_range f
  rw [hfcard] at hcard
  rw [hker]
  exact hcard

section PerExtension

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

namespace GGE6ThreeActData

theorem conj_w_mem_normalizer (h : GGE6ThreeActData A Φ w)
    (i : Fin Tag.E6.rank) :
    MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  refine mem_normalizer_of_conj_mem (A := A) (f := MulAut.conj (w i)) fun a ha => ?_
  obtain ⟨b, hb, -⟩ := h.act i ⟨a, ha⟩
  rw [hb]
  exact b.2

@[expose] noncomputable def conjAut (h : GGE6ThreeActData A Φ w)
    (i : Fin Tag.E6.rank) : MulAut ↥A :=
  ggConjAut A (h.conj_w_mem_normalizer i)

theorem conjAut_apply_toAdd (h : GGE6ThreeActData A Φ w)
    (i : Fin Tag.E6.rank) (a : A) :
    Multiplicative.toAdd (Φ (h.conjAut i a)) =
      adRefl .E6 3 i (Multiplicative.toAdd (Φ a)) := by
  obtain ⟨b, hb, hbΦ⟩ := h.act i a
  have hba : h.conjAut i a = b := by
    apply Subtype.ext
    show MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ = (b : MulAut L')
    exact hb
  rw [hba]
  exact hbΦ

theorem conjAut_sq (h : GGE6ThreeActData A Φ w) (i : Fin Tag.E6.rank) :
    h.conjAut i ^ 2 = 1 := by
  apply MulEquiv.ext
  intro a
  rw [pow_two, MulAut.mul_apply]
  apply h.injective
  apply Multiplicative.toAdd.injective
  exact (h.conjAut_apply_toAdd i (h.conjAut i a)).trans
    ((congrArg (adRefl .E6 3 i) (h.conjAut_apply_toAdd i a)).trans
      ((adRefl_adRefl i (Multiplicative.toAdd (Φ a))).trans rfl))

theorem card_fix_conjAut_top (h : GGE6ThreeActData A Φ w) (i : Fin Tag.E6.rank)
    (hsurj : ∀ v : Fin 6 → ZMod 3, ∃ a : A, Φ a = Multiplicative.ofAdd v) :
    Nat.card {a : A // h.conjAut i a = a} * 3 = Nat.card A := by
  classical
  let φ : Additive ↥A →+ (Fin 6 → ZMod 3) :=
    { toFun := fun a => Multiplicative.toAdd (Φ (Additive.toMul a))
      map_zero' := by
        change Multiplicative.toAdd (Φ 1) = 0
        rw [map_one, toAdd_one]
      map_add' := by
        intro a b
        change Multiplicative.toAdd (Φ (Additive.toMul (a + b))) =
          Multiplicative.toAdd (Φ (Additive.toMul a)) + Multiplicative.toAdd (Φ (Additive.toMul b))
        rw [toMul_add, map_mul, toAdd_mul] }
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Additive.ofMul.injective
    apply h.injective
    apply Multiplicative.toAdd.injective
    exact hab
  have hsurjφ : Function.Surjective φ := by
    intro v
    obtain ⟨a, ha⟩ := hsurj v
    exact ⟨Additive.ofMul a, ha⟩
  let e : Additive ↥A ≃+ (Fin 6 → ZMod 3) := AddEquiv.ofBijective φ ⟨hinj, hsurjφ⟩
  let ee : Additive ↥A ≃ (Fin 6 → ZMod 3) := e.toEquiv
  have hact : ∀ a : A, ee (Additive.ofMul (h.conjAut i a)) =
      adRefl .E6 3 i (ee (Additive.ofMul a)) := by
    intro a
    exact h.conjAut_apply_toAdd i a
  have hiff : ∀ a : A, h.conjAut i a = a ↔
      adRefl .E6 3 i (ee (Additive.ofMul a)) = ee (Additive.ofMul a) := by
    intro a
    constructor
    · intro hh
      rw [← hact a, hh]
    · intro hh
      apply h.injective
      apply Multiplicative.toAdd.injective
      exact (h.conjAut_apply_toAdd i a).trans hh
  have hcard : Nat.card {a : A // h.conjAut i a = a} =
      Nat.card {v : Fin Tag.E6.rank → ZMod 3 // adRefl .E6 3 i v = v} := by
    let e' : A ≃ (Fin Tag.E6.rank → ZMod 3) := Additive.ofMul.trans ee
    refine Nat.card_congr (Equiv.subtypeEquiv e' ?_)
    intro a
    change h.conjAut i a = a ↔
      adRefl .E6 3 i (ee (Additive.ofMul a)) = ee (Additive.ofMul a)
    exact hiff a
  have hcount := card_fix_adRefl_mul_three (⊤ : AddSubgroup (Fin Tag.E6.rank → ZMod 3))
    (Or.inl rfl) i
  have htop : Nat.card {v : Fin Tag.E6.rank → ZMod 3 //
      adRefl .E6 3 i v = v} * 3 = 3 ^ 6 := by
    have h := hcount
    have e1 : Nat.card {v : (⊤ : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) //
        adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) = v} =
        Nat.card {v : Fin Tag.E6.rank → ZMod 3 // adRefl .E6 3 i v = v} :=
      Nat.card_congr (Equiv.subtypeEquiv (AddSubgroup.topEquiv).toEquiv (fun v => Iff.rfl))
    rw [e1, Nat.card_congr (AddSubgroup.topEquiv).toEquiv, card_top] at h
    exact h
  rcases h.card_cases with ⟨hA, -⟩ | ⟨hA5, -⟩
  · rw [hcard, htop, hA]
  · exfalso
    have hcardΦ : Nat.card Φ.range = Nat.card A :=
      Nat.card_congr (MonoidHom.ofInjective h.injective).symm.toEquiv
    have hrange_top : Φ.range = ⊤ := by
      rw [eq_top_iff]
      intro v _
      obtain ⟨a, ha⟩ := hsurj (Multiplicative.toAdd v)
      exact MonoidHom.mem_range.mpr ⟨a, by simpa using ha⟩
    have h6 : Nat.card A = 3 ^ 6 := by
      rw [← hcardΦ, hrange_top, Subgroup.card_top]
      rw [Nat.card_congr Multiplicative.toAdd]
      exact card_top
    rw [hA5] at h6
    norm_num at h6

theorem card_fix_conjAut_hyp (h : GGE6ThreeActData A Φ w) (i : Fin Tag.E6.rank)
    (hc5 : Nat.card A = 3 ^ 5)
    (hmem : ∀ a : A, Multiplicative.toAdd (Φ a) ∈ NoOffRest.hypE6) :
    Nat.card {a : A // h.conjAut i a = a} * 3 = Nat.card A := by
  classical
  let φ : Additive ↥A →+ NoOffRest.hypE6 :=
    { toFun := fun a => ⟨Multiplicative.toAdd (Φ (Additive.toMul a)),
        hmem (Additive.toMul a)⟩
      map_zero' := by
        apply Subtype.ext
        change Multiplicative.toAdd (Φ 1) = 0
        rw [map_one, toAdd_one]
      map_add' := by
        intro a b
        apply Subtype.ext
        change Multiplicative.toAdd (Φ (Additive.toMul (a + b))) =
          Multiplicative.toAdd (Φ (Additive.toMul a)) +
            Multiplicative.toAdd (Φ (Additive.toMul b))
        rw [toMul_add, map_mul, toAdd_mul] }
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : Multiplicative.toAdd (Φ (Additive.toMul a)) =
        Multiplicative.toAdd (Φ (Additive.toMul b)) := congrArg Subtype.val hab
    apply Additive.ofMul.injective
    apply h.injective
    apply Multiplicative.toAdd.injective
    exact h1
  have hle : Nat.card NoOffRest.hypE6 ≤ Nat.card (Additive ↥A) := by
    rw [NoOffRest.card_hypE6, ← Nat.card_congr Additive.ofMul, hc5]
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le hle
  let e : Additive ↥A ≃+ NoOffRest.hypE6 := AddEquiv.ofBijective φ hbij
  let T : NoOffRest.hypE6 → NoOffRest.hypE6 :=
    fun v => ⟨adRefl .E6 3 i v, E6ThreeModel.adRefl_mem_hypE6 v.2 i⟩
  have hT : ∀ v : NoOffRest.hypE6, T v = v ↔ adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) = v :=
    fun v => Subtype.ext_iff
  have hact : ∀ a : A, e (Additive.ofMul (h.conjAut i a)) = T (e (Additive.ofMul a)) := by
    intro a
    apply Subtype.ext
    exact h.conjAut_apply_toAdd i a
  have hiff : ∀ a : A, h.conjAut i a = a ↔ T (e (Additive.ofMul a)) = e (Additive.ofMul a) := by
    intro a
    constructor
    · intro hh
      rw [← hact a, hh]
    · intro hh
      apply h.injective
      apply Multiplicative.toAdd.injective
      have h1 : Multiplicative.toAdd (Φ (h.conjAut i a)) =
          (T (e (Additive.ofMul a)) : Fin Tag.E6.rank → ZMod 3) := by
        rw [← hact a]
        rfl
      exact h1.trans (congrArg Subtype.val hh)
  have hcard : Nat.card {a : A // h.conjAut i a = a} =
      Nat.card {v : NoOffRest.hypE6 // T v = v} := by
    let ee : A ≃ NoOffRest.hypE6 := Additive.ofMul.trans e.toEquiv
    refine Nat.card_congr (Equiv.subtypeEquiv ee ?_)
    intro a
    change h.conjAut i a = a ↔ T (e (Additive.ofMul a)) = e (Additive.ofMul a)
    exact hiff a
  have hcount := card_fix_adRefl_mul_three NoOffRest.hypE6 (Or.inr rfl) i
  have hfixT : Nat.card {v : NoOffRest.hypE6 // T v = v} =
      Nat.card {v : NoOffRest.hypE6 // adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight (p := fun v : NoOffRest.hypE6 => T v = v)
      (q := fun v : NoOffRest.hypE6 =>
        adRefl .E6 3 i (v : Fin Tag.E6.rank → ZMod 3) = v) hT)
  have hA : Nat.card A = Nat.card NoOffRest.hypE6 :=
    (Nat.card_congr Additive.ofMul).trans (Nat.card_congr e.toEquiv)
  rw [hcard, hfixT]
  rw [hcount, hA]

theorem card_fix_conjAut (h : GGE6ThreeActData A Φ w) (i : Fin Tag.E6.rank) :
    Nat.card {a : A // h.conjAut i a = a} * 3 = Nat.card A := by
  rcases h.card_cases with ⟨hc6, hsurj⟩ | ⟨hc5, hmem⟩
  · exact card_fix_conjAut_top h i hsurj
  · exact card_fix_conjAut_hyp h i hc5 hmem

theorem conjAut_isReflection (h : GGE6ThreeActData A Φ w) (i : Fin Tag.E6.rank) :
    GGIsReflection 3 (h.conjAut i) :=
  ⟨h.conjAut_sq i, card_fix_conjAut h i⟩

theorem conjAut_mem_automizer (h : GGE6ThreeActData A Φ w) (i : Fin Tag.E6.rank) :
    h.conjAut i ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
  Subgroup.subset_closure
    (ggConjAut_mem_ggInduced (H := (MulAut.conj : L' →* MulAut L').range)
      (MonoidHom.mem_range.mpr ⟨w i, rfl⟩) (h.conj_w_mem_normalizer i))

theorem reflGen_le_automizer (h : GGE6ThreeActData A Φ w) :
    Subgroup.closure (Set.range h.conjAut) ≤
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
  refine (Subgroup.closure_le _).mpr ?_
  rw [Set.range_subset_iff]
  exact fun i => h.conjAut_mem_automizer i

theorem exists_reflGen_act (h : GGE6ThreeActData A Φ w) (u : WeylGroup .E6) :
    ∃ ψ ∈ Subgroup.closure (Set.range h.conjAut),
      ∀ a : A, Multiplicative.toAdd (Φ (ψ a)) = adAct .E6 3 u (Multiplicative.toAdd (Φ a)) := by
  classical
  refine weyl_induction (P := fun u => ∃ ψ ∈ Subgroup.closure (Set.range h.conjAut),
      ∀ a : A,
        Multiplicative.toAdd (Φ (ψ a)) = adAct .E6 3 u (Multiplicative.toAdd (Φ a))) ?_ ?_ u
  · refine ⟨1, Subgroup.one_mem _, fun a => ?_⟩
    exact (adAct_one (τ := .E6) (p := 3) (Multiplicative.toAdd (Φ a))).symm
  · rintro i v ⟨ψ, hψ, hact⟩
    refine ⟨h.conjAut i * ψ,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hψ, fun a => ?_⟩
    change Multiplicative.toAdd (Φ (h.conjAut i (ψ a))) =
      adAct .E6 3 (simple .E6 i * v) (Multiplicative.toAdd (Φ a))
    have h1 : Multiplicative.toAdd (Φ (h.conjAut i (ψ a))) =
        adRefl .E6 3 i (Multiplicative.toAdd (Φ (ψ a))) :=
      h.conjAut_apply_toAdd i (ψ a)
    have h2 : adRefl .E6 3 i (Multiplicative.toAdd (Φ (ψ a))) =
        adRefl .E6 3 i (adAct .E6 3 v (Multiplicative.toAdd (Φ a))) :=
      congrArg (adRefl .E6 3 i) (hact a)
    have h3 : adRefl .E6 3 i (adAct .E6 3 v (Multiplicative.toAdd (Φ a))) =
        adAct .E6 3 (simple .E6 i) (adAct .E6 3 v (Multiplicative.toAdd (Φ a))) :=
      (adAct_simple (τ := .E6) (p := 3) i _).symm
    have h4 : adAct .E6 3 (simple .E6 i) (adAct .E6 3 v (Multiplicative.toAdd (Φ a))) =
        adAct .E6 3 (simple .E6 i * v) (Multiplicative.toAdd (Φ a)) :=
      (adAct_mul (τ := .E6) (p := 3) (simple .E6 i) v _).symm
    exact h1.trans (h2.trans (h3.trans h4))

@[expose] noncomputable def weylAut (h : GGE6ThreeActData A Φ w) (u : WeylGroup .E6) : MulAut ↥A :=
  (h.exists_reflGen_act u).choose

theorem weylAut_mem (h : GGE6ThreeActData A Φ w) (u : WeylGroup .E6) :
    h.weylAut u ∈ Subgroup.closure (Set.range h.conjAut) :=
  (h.exists_reflGen_act u).choose_spec.1

theorem weylAut_act (h : GGE6ThreeActData A Φ w) (u : WeylGroup .E6) (a : A) :
    Multiplicative.toAdd (Φ (h.weylAut u a)) =
      adAct .E6 3 u (Multiplicative.toAdd (Φ a)) :=
  (h.exists_reflGen_act u).choose_spec.2 a

theorem weylAut_one (h : GGE6ThreeActData A Φ w) : h.weylAut 1 = 1 := by
  apply MulEquiv.ext
  intro a
  apply h.injective
  apply Multiplicative.toAdd.injective
  exact (h.weylAut_act 1 a).trans (adAct_one (τ := .E6) (p := 3) (Multiplicative.toAdd (Φ a)))

theorem weylAut_mul (h : GGE6ThreeActData A Φ w) (u v : WeylGroup .E6) :
    h.weylAut (u * v) = h.weylAut u * h.weylAut v := by
  apply MulEquiv.ext
  intro a
  apply h.injective
  apply Multiplicative.toAdd.injective
  exact (h.weylAut_act (u * v) a).trans
    ((adAct_mul (τ := .E6) (p := 3) u v (Multiplicative.toAdd (Φ a))).trans
      ((congrArg (adAct .E6 3 u) (h.weylAut_act v a).symm).trans
        ((h.weylAut_act u (h.weylAut v a)).symm)))

theorem weylAut_inv (h : GGE6ThreeActData A Φ w) (u : WeylGroup .E6) :
    h.weylAut u⁻¹ = (h.weylAut u)⁻¹ := by
  apply MulEquiv.ext
  intro a
  apply h.injective
  apply Multiplicative.toAdd.injective
  have h1 := h.weylAut_act u ((h.weylAut u)⁻¹ a)
  have h2 : h.weylAut u ((h.weylAut u)⁻¹ a) = a := MulAut.apply_inv_self _ _ _
  rw [h2] at h1
  have h3 := congrArg (adAct .E6 3 u⁻¹) h1
  rw [← adAct_mul, inv_mul_cancel, adAct_one] at h3
  exact (h.weylAut_act u⁻¹ a).trans h3

theorem weylAut_simple (h : GGE6ThreeActData A Φ w) (i : Fin Tag.E6.rank) :
    h.weylAut (simple .E6 i) = h.conjAut i := by
  apply MulEquiv.ext
  intro a
  apply h.injective
  apply Multiplicative.toAdd.injective
  exact (h.weylAut_act (simple .E6 i) a).trans
    (((adAct_simple (τ := .E6) (p := 3) i (Multiplicative.toAdd (Φ a)))).trans
      (h.conjAut_apply_toAdd i a).symm)

theorem weylAut_injective
    (h : GGE6ThreeActData A Φ w) : Function.Injective h.weylAut := by
  intro u v huv
  have hact : ∀ x ∈ NoOffRest.hypE6, adAct .E6 3 u x = adAct .E6 3 v x := by
    intro x hx
    let x6 : Fin 6 → ZMod 3 := x
    have hxT : (x6 : Fin Tag.E6.rank → ZMod 3) = x := rfl
    have hx6 : x6 ∈ NoOffRest.hypE6 := by
      rw [show x6 ∈ NoOffRest.hypE6 ↔ (x : Fin Tag.E6.rank → ZMod 3) ∈ NoOffRest.hypE6
        from Iff.rfl]
      exact hx
    have hxr : Multiplicative.ofAdd x6 ∈ Φ.range := by
      rcases h.range with hr | hr
      · rw [hr]; exact Subgroup.mem_top _
      · exact (hr x6).mpr hx6
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxr
    have hx' : Multiplicative.toAdd (Φ a) = x6 := by rw [ha, toAdd_ofAdd]
    let va : Fin 6 → ZMod 3 := Multiplicative.toAdd (Φ a)
    have hva : va = x6 := hx'
    have hvaT : (va : Fin Tag.E6.rank → ZMod 3) =
        (x6 : Fin Tag.E6.rank → ZMod 3) := by rw [hva]
    have h2 : adAct .E6 3 u x = adAct .E6 3 u (x6 : Fin Tag.E6.rank → ZMod 3) := by
      rw [hxT]
    have h2' : adAct .E6 3 u (x6 : Fin Tag.E6.rank → ZMod 3) =
        adAct .E6 3 u (va : Fin Tag.E6.rank → ZMod 3) := by rw [hvaT]
    have h3 : adAct .E6 3 u (va : Fin Tag.E6.rank → ZMod 3) =
        Multiplicative.toAdd (Φ (h.weylAut u a)) := (h.weylAut_act u a).symm
    have h4 : Multiplicative.toAdd (Φ (h.weylAut u a)) =
        Multiplicative.toAdd (Φ (h.weylAut v a)) := by rw [huv]
    have h5 : Multiplicative.toAdd (Φ (h.weylAut v a)) =
        adAct .E6 3 v (va : Fin Tag.E6.rank → ZMod 3) := h.weylAut_act v a
    have h5' : adAct .E6 3 v (va : Fin Tag.E6.rank → ZMod 3) =
        adAct .E6 3 v (x6 : Fin Tag.E6.rank → ZMod 3) := by rw [hvaT]
    have h6 : adAct .E6 3 v (x6 : Fin Tag.E6.rank → ZMod 3) = adAct .E6 3 v x := by
      rw [hxT]
    exact h2.trans (h2'.trans (h3.trans (h4.trans (h5.trans (h5'.trans h6)))))
  have hz : u⁻¹ * v = 1 := by
    apply eq_one_of_adAct_eq_on_hypE6
    intro x hx
    rw [adAct_mul, ← hact x hx, ← adAct_mul, inv_mul_cancel, adAct_one]
  have hvu : v = u := by
    have h := congrArg (fun z => u * z) hz
    simpa using h
  exact hvu.symm

@[expose] noncomputable def weylAutHom (h : GGE6ThreeActData A Φ w) :
    WeylGroup .E6 →* MulAut ↥A where
  toFun := h.weylAut
  map_one' := h.weylAut_one
  map_mul' := h.weylAut_mul

theorem weylAutHom_range_eq_closure (h : GGE6ThreeActData A Φ w) :
    h.weylAutHom.range = Subgroup.closure (Set.range h.conjAut) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    exact h.weylAut_mem u
  · refine (Subgroup.closure_le _).mpr ?_
    rw [Set.range_subset_iff]
    intro i
    exact ⟨simple .E6 i, h.weylAut_simple i⟩

theorem automizer_eq_reflGen_of_card_le
    (h : GGE6ThreeActData A Φ w)
    (hcard : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≤
      Nat.card (WeylGroup .E6)) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range h.conjAut) := by
  haveI := h.finite
  have hcardH : Nat.card (Subgroup.closure (Set.range h.conjAut)) = Nat.card (WeylGroup .E6) := by
    have hcard_eq := Nat.card_congr
      (MonoidHom.ofInjective (f := h.weylAutHom) h.weylAut_injective).toEquiv
    rw [weylAutHom_range_eq_closure h] at hcard_eq
    exact hcard_eq.symm
  exact (Subgroup.eq_of_le_of_card_ge h.reflGen_le_automizer (by rw [hcardH]; exact hcard)).symm

noncomputable def automizerEquivWeylOfCardLe
    (h : GGE6ThreeActData A Φ w)
    (hcard : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≤
      Nat.card (WeylGroup .E6)) :
    WeylGroup .E6 ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
  (MonoidHom.ofInjective (f := h.weylAutHom) h.weylAut_injective).trans
    (MulEquiv.subgroupCongr (h.weylAutHom_range_eq_closure.trans
      (h.automizer_eq_reflGen_of_card_le hcard).symm))

theorem automizerEquivWeylOfCardLe_simple
    (h : GGE6ThreeActData A Φ w)
    (hcard : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≤
      Nat.card (WeylGroup .E6)) (i : Fin Tag.E6.rank) :
    (h.automizerEquivWeylOfCardLe hcard (simple .E6 i) : MulAut ↥A) = h.conjAut i :=
  h.weylAut_simple i

end GGE6ThreeActData

namespace GGE6ThreeData

theorem conj_w_mem_normalizer (h : GGE6ThreeData Z A Φ T w)
    (i : Fin Tag.E6.rank) :
    MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
  h.toActData.conj_w_mem_normalizer i

@[expose] noncomputable def conjAut (h : GGE6ThreeData Z A Φ T w)
    (i : Fin Tag.E6.rank) : MulAut ↥A :=
  h.toActData.conjAut i

theorem conjAut_apply_toAdd (h : GGE6ThreeData Z A Φ T w)
    (i : Fin Tag.E6.rank) (a : A) :
    Multiplicative.toAdd (Φ (h.conjAut i a)) =
      adRefl .E6 3 i (Multiplicative.toAdd (Φ a)) :=
  h.toActData.conjAut_apply_toAdd i a

theorem conjAut_isReflection (h : GGE6ThreeData Z A Φ T w) (i : Fin Tag.E6.rank) :
    GGIsReflection 3 (h.conjAut i) :=
  h.toActData.conjAut_isReflection i

theorem conjAut_mem_automizer (h : GGE6ThreeData Z A Φ T w) (i : Fin Tag.E6.rank) :
    h.conjAut i ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
  h.toActData.conjAut_mem_automizer i

theorem reflGen_le_automizer (h : GGE6ThreeData Z A Φ T w) :
    Subgroup.closure (Set.range h.conjAut) ≤
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
  h.toActData.reflGen_le_automizer

theorem exists_reflGen_act (h : GGE6ThreeData Z A Φ T w) (u : WeylGroup .E6) :
    ∃ ψ ∈ Subgroup.closure (Set.range h.conjAut),
      ∀ a : A, Multiplicative.toAdd (Φ (ψ a)) = adAct .E6 3 u (Multiplicative.toAdd (Φ a)) :=
  h.toActData.exists_reflGen_act u

@[expose] noncomputable def weylAut (h : GGE6ThreeData Z A Φ T w) (u : WeylGroup .E6) : MulAut ↥A :=
  h.toActData.weylAut u

theorem weylAut_mem (h : GGE6ThreeData Z A Φ T w) (u : WeylGroup .E6) :
    h.weylAut u ∈ Subgroup.closure (Set.range h.conjAut) :=
  h.toActData.weylAut_mem u

theorem weylAut_act (h : GGE6ThreeData Z A Φ T w) (u : WeylGroup .E6) (a : A) :
    Multiplicative.toAdd (Φ (h.weylAut u a)) =
      adAct .E6 3 u (Multiplicative.toAdd (Φ a)) :=
  h.toActData.weylAut_act u a

theorem weylAut_one (h : GGE6ThreeData Z A Φ T w) : h.weylAut 1 = 1 :=
  h.toActData.weylAut_one

theorem weylAut_mul (h : GGE6ThreeData Z A Φ T w) (u v : WeylGroup .E6) :
    h.weylAut (u * v) = h.weylAut u * h.weylAut v :=
  h.toActData.weylAut_mul u v

theorem weylAut_inv (h : GGE6ThreeData Z A Φ T w) (u : WeylGroup .E6) :
    h.weylAut u⁻¹ = (h.weylAut u)⁻¹ :=
  h.toActData.weylAut_inv u

theorem weylAut_simple (h : GGE6ThreeData Z A Φ T w) (i : Fin Tag.E6.rank) :
    h.weylAut (simple .E6 i) = h.conjAut i :=
  h.toActData.weylAut_simple i

theorem weylAut_injective
    (h : GGE6ThreeData Z A Φ T w) : Function.Injective h.weylAut :=
  h.toActData.weylAut_injective

@[expose] noncomputable def weylAutHom (h : GGE6ThreeData Z A Φ T w) :
    WeylGroup .E6 →* MulAut ↥A :=
  h.toActData.weylAutHom

theorem torusWeylElt_w (h : GGE6ThreeData Z A Φ T w) (i : Fin 6) :
    GGTorusWeylElt 3 A (w i) := by
  intro a ha
  obtain ⟨hT, hcube⟩ := h.coboundary i a ha
  exact ⟨hcube, fun a' ha' => h.fixed a' ha' _ hT⟩

theorem conjAut_mem_ggTorusReflSet (h : GGE6ThreeData Z A Φ T w) (i : Fin Tag.E6.rank) :
    h.conjAut i ∈ ggTorusReflSet 3 A :=
  ⟨w i, h.conj_w_mem_normalizer i, h.torusWeylElt_w i, rfl, h.conjAut_isReflection i⟩

theorem automizer_le_reflGen (h : GGE6ThreeData Z A Φ T w) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
      Subgroup.closure (Set.range h.conjAut) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro φ ⟨g, hgH, hgN, hφ⟩
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hgH
  have hφeq : φ = ggConjAut A hgN := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [hφ a, ggConjAut_apply]
  obtain ⟨u, hu⟩ := h.inner m hgN
  obtain ⟨ψu, hψu, hact⟩ := h.exists_reflGen_act u
  have hφψ : φ = ψu := by
    rw [hφeq]
    apply MulEquiv.ext
    intro a
    apply h.injective
    apply Multiplicative.toAdd.injective
    exact (hu a (ggConjAut A hgN a) (ggConjAut_apply A hgN a)).trans (hact a).symm
  rw [hφψ]
  exact hψu

theorem automizer_eq_reflGen (h : GGE6ThreeData Z A Φ T w) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range h.conjAut) :=
  le_antisymm h.automizer_le_reflGen h.reflGen_le_automizer

theorem weylAutHom_range (h : GGE6ThreeData Z A Φ T w) :
    h.weylAutHom.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
  rw [h.automizer_eq_reflGen]
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨u, rfl⟩
    exact h.weylAut_mem u
  · rintro _ ⟨i, rfl⟩
    exact ⟨simple .E6 i, h.weylAut_simple i⟩

@[expose] noncomputable def automizerEquivWeyl
    (h : GGE6ThreeData Z A Φ T w) :
    WeylGroup .E6 ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
  (MonoidHom.ofInjective h.weylAut_injective).trans
    (MulEquiv.subgroupCongr h.weylAutHom_range)

theorem automizerEquivWeyl_simple
    (h : GGE6ThreeData Z A Φ T w) (i : Fin Tag.E6.rank) :
    (h.automizerEquivWeyl (simple .E6 i) : MulAut ↥A) = h.conjAut i :=
  h.weylAut_simple i

end GGE6ThreeData

end PerExtension

end CFSG.StandardType

namespace CFSG.StandardType

theorem ggTorusReflGenW_of_e6ThreeModel {R : Type} [Group R] {I : Set (MulAut R)}
    (hM : GGE6ThreeModelSCr R I) : GGTorusReflGenW 3 5 R I := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨Φ, T, w, h⟩ := (hM L' ψ hψ hker hperf A hAe hAI hr hsc).exists_data
  exact h.automizer_le_reflGen.trans
    (Subgroup.closure_mono (Set.range_subset_iff.mpr h.conjAut_mem_ggTorusReflSet))

theorem ggTorusAutCardDvdSCr_of_e6ThreeModel
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hM : GGE6ThreeModelSCr R I) : GGTorusAutCardDvdSCr 3 5 R I 51840 := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨Φ, T, w, h⟩ := (hM L' ψ hψ hker hperf A hAe hAI hr hsc).exists_data
  let S : Subgroup (MulAut ↥A) := Subgroup.closure (Set.range h.conjAut)
  have hSA : S ≤ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    h.reflGen_le_automizer
  have hS_range : ∀ x ∈ S, ∃ u : WeylGroup .E6, h.weylAut u = x := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ∃ u : WeylGroup .E6, h.weylAut u = x) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨i, rfl⟩
      exact ⟨simple .E6 i, h.weylAut_simple i⟩
    · exact ⟨1, h.weylAut_one⟩
    · rintro x y _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
      exact ⟨u * v, h.weylAut_mul u v⟩
    · rintro x _ ⟨u, rfl⟩
      exact ⟨u⁻¹, h.weylAut_inv u⟩
  have hcardS : Nat.card S = 51840 := by
    have hbij : Function.Bijective
        (fun u : WeylGroup .E6 => (⟨h.weylAut u, h.weylAut_mem u⟩ : S)) := by
      constructor
      · intro u v huv
        exact h.weylAut_injective (congrArg Subtype.val huv)
      · rintro ⟨x, hx⟩
        obtain ⟨u, hu⟩ := hS_range x hx
        exact ⟨u, Subtype.ext hu⟩
    have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [NoOffExc.card_weyl_E6] at hcard
    exact hcard.symm
  have hdvd := Subgroup.card_dvd_of_le hSA
  rwa [hcardS] at hdvd

end CFSG.StandardType

section CertificatesE6

namespace CFSG.StandardType

theorem ggNbrTableBWeylInputOn_e6Three_holds :
    GGNbrTableBWeylInputOn fun p lab => lab.tag = .E6 ∧ p = 3 := by
  intro p hp hp2 lab hlab hS hhs hsp
  obtain ⟨htag, rfl⟩ := hS
  intro Q hQ
  have h3 : 3 ∣ 2 ^ lab.n - 1 := hsp.2.2
  have h := largeEvenLabelAll_e6Div_of (P := fun R _ I => GGTorusReflGenW 3 5 R I)
    htag hlab h3 (fun K _ _ n hn hK h3' =>
      ggTorusReflGenW_of_e6ThreeModel (E6ThreeModel.e6ThreeModel_holds.1 K n hn hK h3'))
  exact largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, 5, hh.2.1, hh.2.2⟩) (h Q hQ)

theorem ggNbrTableBOrderRestInputOn_e6Three_holds :
    GGNbrTableBOrderRestInputOn fun p lab => lab.tag = .E6 ∧ p = 3 := by
  intro p hp hp2 lab N hlab hS hsp hN
  obtain ⟨htag, rfl⟩ := hS
  have hN5 : N = 51840 := by
    rcases hN with ⟨hC, -⟩ | ⟨hD, -⟩ | ⟨-, hE6⟩ | ⟨hE7, -⟩ | ⟨hE8, -⟩
    · rw [htag] at hC; cases hC
    · rw [htag] at hD; cases hD
    · exact hE6
    · rw [htag] at hE7; cases hE7
    · rw [htag] at hE8; cases hE8
  rw [hN5]
  intro Q hQ
  have h3 : 3 ∣ 2 ^ lab.n - 1 := hsp.2.2
  have h := largeEvenLabelAll_e6Div_of (P := fun R _ I => GGTorusAutCardDvdSCr 3 5 R I 51840)
    htag hlab h3 (fun K _ _ n hn hK h3' =>
      ggTorusAutCardDvdSCr_of_e6ThreeModel (E6ThreeModel.e6ThreeModel_holds.1 K n hn hK h3'))
  exact largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, 5, hh.2.1, hh.2.2⟩) (h Q hQ)

theorem ggTwE6ThreeNbrWeylInput_holds : GGTwE6ThreeNbrWeylInput := by
  intro lab hlab hbad
  have h := largeEvenLabelAll_twE6Three_of (p := 3)
    (P := fun R _ I => GGTorusReflGenW 3 5 R I) hlab hbad
    (fun K _ _ n hn hK h3 =>
      ggTorusReflGenW_of_e6ThreeModel (E6ThreeModel.e6ThreeModel_holds.2 K n hn hK h3))
  intro Q hQ
  exact largeEvenRawDatum_mono (fun R _ I F hh => ⟨hh.1, hh.2.2⟩) (h Q hQ)

end CFSG.StandardType

end CertificatesE6

end
