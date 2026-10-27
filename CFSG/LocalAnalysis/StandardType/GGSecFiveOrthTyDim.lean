module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthPolar
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyGram
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge

public section

namespace CFSG.StandardType.OrthF3


open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private lemma ct_tyc_root
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] [Finite V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : PolarNondeg3 Q)
    [Fact (Nat.Prime 3)] {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs} (hφ : GGIsReflection 3 φ)
    (hiso : ggLin (p := 3) ι φ ∈ QuadraticMap.orthogonalGroup Q) :
    ∃ v : V, Q v ≠ 0 ∧
      ∀ w, ggLin (p := 3) ι φ w = w - (QuadraticMap.polar Q v w / Q v) • v := by
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hrefl : GGLinRefl (ggLin (p := 3) ι φ) :=
    (ggIsReflection_iff_ggLinRefl (p := 3) hp2 ι φ).mp hφ
  have hcond : ggLin (p := 3) ι φ * ggLin (p := 3) ι φ = 1 ∧
      Module.finrank (ZMod 3)
        (LinearMap.range ((ggLin (p := 3) ι φ).toLinearMap - LinearMap.id)) = 1 := by
    unfold GGLinRefl ggLinMove at hrefl
    exact hrefl
  obtain ⟨c, hc, v, hinv, hQv, hgv⟩ := (linRefl_iff_orthRefl hQ hiso).mp hcond
  refine ⟨v, ?_, ?_⟩
  · rw [hQv]; exact hc
  · intro w
    have h_eq : ggLin (p := 3) ι φ =
        @QuadraticMap.reflection (ZMod 3) V _ _ _ Q v hinv := by
      rw [← hgv]
      exact @QuadraticMap.coe_reflectionOrthogonal (ZMod 3) V _ _ _ Q v hinv
    rw [h_eq]
    exact @QuadraticMap.reflection_apply_eq_sub_div (ZMod 3) V _ _ _ Q v hinv w

private lemma ct_tyc_orth_span_le
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {s : Set V} {w0 : V}
    (hs : ∀ x ∈ s, QuadraticMap.polar Q x w0 = 0) {w : V}
    (hw : w ∈ Submodule.span K {w0}) :
    ∀ u ∈ Submodule.span K s, QuadraticMap.polar Q u w = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  have hzero : ∀ u ∈ Submodule.span K s, QuadraticMap.polar Q u w0 = 0 := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · intro x hx; exact hs x hx
    · exact QuadraticMap.polar_zero_left Q w0
    · intro p q hp hq ihp ihq
      rw [QuadraticMap.polar_add_left, ihp, ihq, add_zero]
    · intro c p hp ihp
      rw [QuadraticMap.polar_smul_left, ihp, smul_eq_mul, mul_zero]
  intro u hu
  rw [← hc, QuadraticMap.polar_smul_right, hzero u hu, smul_eq_mul, mul_zero]

private lemma ct_tyc_finrank_eq
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (U W : Submodule K V) (hW : ∀ w, w ∈ W ↔ ∀ u ∈ U, QuadraticMap.polar Q u w = 0)
    (hWfin : Module.finrank K W = 1) :
    Module.finrank K U + 1 = Module.finrank K V := by
  have horth : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) U = W := by
    ext w
    rw [LinearMap.BilinForm.mem_orthogonal_iff, hW w]
    simp [QuadraticMap.polarBilin_apply_apply]
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := QuadraticMap.polarBilin Q) U
  rw [LinearMap.BilinForm.Nondegenerate.ker_eq_bot hQ, inf_bot_eq, finrank_bot, add_zero,
    horth, hWfin] at h
  exact h


private theorem ct_tyc_exists_roots
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] [Finite V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : PolarNondeg3 Q)
    {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {κ : Type} (a : κ → MulAut ↥Bs) (hε : ∀ i, GGIsReflection 3 (a i))
    (horth : ∀ i, ggLin (p := 3) ι (a i) ∈ QuadraticMap.orthogonalGroup Q) :
    ∃ v : κ → V, (∀ i, Q (v i) ≠ 0) ∧
      ∀ i w, ggLin (p := 3) ι (a i) w =
        w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i := by
  have hroot : ∀ i, ∃ v : V, Q v ≠ 0 ∧
      ∀ w, ggLin (p := 3) ι (a i) w =
        w - (QuadraticMap.polar Q v w / Q v) • v :=
    fun i => ct_tyc_root hQ ι (hε i) (horth i)
  refine ⟨fun i => Classical.choose (hroot i), ?_, ?_⟩
  · intro i; exact (Classical.choose_spec (hroot i)).1
  · intro i; exact (Classical.choose_spec (hroot i)).2

private lemma ct_tyc_closure_eq
    {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    {κ : Type} (M : CoxeterMatrix κ) (ε : M.Group ≃* ↥A) :
    Subgroup.closure (Set.range (fun i : κ => ((ε (M.simple i) : ↥A) : MulAut ↥Bs))) = A := by
  have htop : (⊤ : Subgroup ↥A) =
      Subgroup.closure (Set.range (fun i : κ => ε (M.simple i))) := by
    rw [← Subgroup.map_top_of_surjective (ε : M.Group →* ↥A) ε.surjective,
      ← M.toCoxeterSystem.subgroup_closure_range_simple, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
  have hmap_top : Subgroup.map A.subtype (⊤ : Subgroup ↥A) = A := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨z, rfl⟩; exact z.property
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  have h1 : Subgroup.map A.subtype
        (Subgroup.closure (Set.range (fun i : κ => ε (M.simple i)))) =
      Subgroup.closure
        (Set.range (fun i : κ => ((ε (M.simple i) : ↥A) : MulAut ↥Bs))) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, hzy⟩; exact ⟨i, hzy⟩
    · rintro ⟨i, rfl⟩; exact ⟨ε (M.simple i), ⟨i, rfl⟩, rfl⟩
  rw [← h1, ← htop, hmap_top]

private lemma ct_tyc_fix_iff_orth
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V}
    {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {κ : Type} {A : Subgroup (MulAut ↥Bs)} (a : κ → MulAut ↥Bs)
    (hgen : Subgroup.closure (Set.range a) = A)
    (v : κ → V) (hv_norm : ∀ i, Q (v i) ≠ 0)
    (hv_formula : ∀ i w, ggLin (p := 3) ι (a i) w =
      w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i) :
    ∀ w, (∀ φ ∈ A, ggLin (p := 3) ι φ w = w) ↔
      ∀ i, QuadraticMap.polar Q (v i) w = 0 := by
  intro w
  constructor
  · intro hw i
    have hmem : a i ∈ A := by
      rw [← hgen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hform := hv_formula i w
    have hwi : ggLin (p := 3) ι (a i) w = w := hw (a i) hmem
    rw [hwi] at hform
    have hc : (QuadraticMap.polar Q (v i) w / Q (v i)) • v i = 0 :=
      (sub_eq_self).mp hform.symm
    have hvi : v i ≠ 0 := fun h0 => hv_norm i (by rw [h0, map_zero])
    have hc0 : QuadraticMap.polar Q (v i) w / Q (v i) = 0 := by
      rcases smul_eq_zero.mp hc with h | h
      · exact h
      · exact absurd h hvi
    rcases div_eq_zero_iff.mp hc0 with h | h
    · exact h
    · exact absurd h (hv_norm i)
  · intro horth φ hφ
    have hmem : φ ∈ Subgroup.closure (Set.range a) := by rwa [hgen]
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hmem
    · intro ψ hψ
      obtain ⟨i, rfl⟩ := hψ
      rw [hv_formula i, horth i]
      simp
    · simp
    · intro ψ χ hψ hχ ihψ ihχ
      rw [map_mul, LinearEquiv.mul_apply, ihχ, ihψ]
    · intro ψ hψ ih
      have h := congrArg (ggLin (p := 3) ι ψ⁻¹) ih
      simpa [← LinearEquiv.mul_apply, ← map_mul] using h.symm

private lemma ct_tyc_images_ne
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {κ : Type} (M : CoxeterMatrix κ) {A : Subgroup (MulAut ↥Bs)}
    (ε : M.Group ≃* ↥A) (a : κ → MulAut ↥Bs)
    (ha : ∀ i, a i = ((ε (M.simple i) : ↥A) : MulAut ↥Bs))
    (g : κ → V ≃ₗ[ZMod 3] V) (hg : ∀ i, g i = ggLin (p := 3) ι (a i)) :
    ∀ i j, i ≠ j → g i ≠ g j := by
  intro i j hij h
  have hsimple_ne : M.simple i ≠ M.simple j :=
    fun hs => hij (M.toCoxeterSystem.simple_injective hs)
  have ha_ne : a i ≠ a j := by
    intro hab
    apply hsimple_ne
    apply ε.injective
    apply Subtype.ext
    rw [← ha i, ← ha j]
    exact hab
  exact ha_ne (ggLin_injective (p := 3) ι (by rw [← hg i, ← hg j]; exact h))

private lemma ct_tyc_polar_zero_of_label_two
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {κ : Type} (M : CoxeterMatrix κ) {A : Subgroup (MulAut ↥Bs)}
    (ε : M.Group ≃* ↥A) (a : κ → MulAut ↥Bs)
    (ha : ∀ i, a i = ((ε (M.simple i) : ↥A) : MulAut ↥Bs))
    (g : κ → V ≃ₗ[ZMod 3] V) (hg : ∀ i, g i = ggLin (p := 3) ι (a i))
    (hg_ne : ∀ i j, i ≠ j → g i ≠ g j)
    (v : κ → V) (hv_norm : ∀ i, Q (v i) ≠ 0)
    (hv_formula : ∀ i w, g i w =
      w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i) :
    ∀ i j, i ≠ j → M.M i j = 2 → QuadraticMap.polar Q (v i) (v j) = 0 := by
  intro i j hij hij2
  have hrel := ggOrthGram_relations (V := V) Q (g := g i) (h := g j)
    (u := v i) (v := v j) (hv_norm i) (hv_norm j) (hv_formula i) (hv_formula j)
  have hsi : M.simple i * M.simple i = 1 := M.toCoxeterSystem.simple_mul_simple_self i
  have hsj : M.simple j * M.simple j = 1 := M.toCoxeterSystem.simple_mul_simple_self j
  have hord : orderOf (M.simple i * M.simple j) = M.M i j := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      M.toCoxeterSystem.orderOf_simple_mul_simple i j
  have hord2 : orderOf (M.simple i * M.simple j) = 2 := hord.trans hij2
  have hsij2 : (M.simple i * M.simple j) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (M.simple i * M.simple j)
    rwa [hord2] at h
  have hsimple_comm : M.simple i * M.simple j = M.simple j * M.simple i := by
    have h2 := hsij2
    rw [pow_two] at h2
    have h1 : (M.simple i * M.simple j)⁻¹ = M.simple i * M.simple j :=
      inv_eq_of_mul_eq_one_left h2
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hsi,
      inv_eq_of_mul_eq_one_right hsj] at h1
    exact h1.symm
  have hab : a i * a j = a j * a i := by
    rw [ha i, ha j]
    exact congrArg (fun x : ↥A => (x : MulAut ↥Bs)) (by
      calc ε (M.simple i) * ε (M.simple j)
          = ε (M.simple i * M.simple j) := (map_mul ε _ _).symm
        _ = ε (M.simple j * M.simple i) := by rw [hsimple_comm]
        _ = ε (M.simple j) * ε (M.simple i) := map_mul ε _ _)
  have hcomm : g i * g j = g j * g i := by
    rw [hg i, hg j, ← map_mul, ← map_mul, hab]
  exact (hrel.1 (hg_ne i j hij)).mp hcomm

private lemma ct_tyc_order_three_of_label_three
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {κ : Type} (M : CoxeterMatrix κ) {A : Subgroup (MulAut ↥Bs)}
    (ε : M.Group ≃* ↥A) (a : κ → MulAut ↥Bs)
    (ha : ∀ i, a i = ((ε (M.simple i) : ↥A) : MulAut ↥Bs))
    (g : κ → V ≃ₗ[ZMod 3] V) (hg : ∀ i, g i = ggLin (p := 3) ι (a i))
    (hg_ne : ∀ i j, i ≠ j → g i ≠ g j) :
    ∀ i j, i ≠ j → M.M i j = 3 →
      (g i * g j) ^ 3 = 1 ∧ g i * g j ≠ g j * g i := by
  intro i j hij hij3
  have hsi : M.simple i * M.simple i = 1 := M.toCoxeterSystem.simple_mul_simple_self i
  have hsj : M.simple j * M.simple j = 1 := M.toCoxeterSystem.simple_mul_simple_self j
  have hai : a i * a i = 1 := by
    rw [ha i, ← Subgroup.coe_mul, ← map_mul, hsi, map_one, Subgroup.coe_one]
  have haj : a j * a j = 1 := by
    rw [ha j, ← Subgroup.coe_mul, ← map_mul, hsj, map_one, Subgroup.coe_one]
  have hgi : g i * g i = 1 := by rw [hg i, ← map_mul, hai, map_one]
  have hgj : g j * g j = 1 := by rw [hg j, ← map_mul, haj, map_one]
  have hord : orderOf (M.simple i * M.simple j) = M.M i j := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      M.toCoxeterSystem.orderOf_simple_mul_simple i j
  have hord3 : orderOf (M.simple i * M.simple j) = 3 := hord.trans hij3
  have hsij3 : (M.simple i * M.simple j) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (M.simple i * M.simple j)
    rwa [hord3] at h
  have hab : a i * a j = ((ε (M.simple i * M.simple j) : ↥A) : MulAut ↥Bs) := by
    rw [ha i, ha j, ← Subgroup.coe_mul, ← map_mul]
  have hp : (a i * a j) ^ 3 = 1 := by
    rw [hab, ← Subgroup.coe_pow, ← map_pow, hsij3, map_one, Subgroup.coe_one]
  have hpow : (g i * g j) ^ 3 = 1 := by
    rw [hg i, hg j, ← map_mul, ← map_pow, hp, map_one]
  have hne : g i * g j ≠ g j * g i := by
    intro hcomm
    have h2 : (g i * g j) ^ 2 = 1 := by
      calc (g i * g j) ^ 2 = (g i * g j) * (g i * g j) := pow_two _
        _ = g i * (g j * g i) * g j := by group
        _ = g i * (g i * g j) * g j := by rw [← hcomm]
        _ = (g i * g i) * (g j * g j) := by group
        _ = 1 := by rw [hgi, hgj, one_mul]
    have hx : g i * g j = 1 := by
      have h : g i * g j = (g i * g j) ^ 3 * ((g i * g j) ^ 2)⁻¹ := by group
      rw [hpow, h2] at h
      simpa using h
    have hge : g i = g j := by
      calc g i = (g i * g j) * g j := by rw [mul_assoc, hgj, mul_one]
        _ = 1 * g j := by rw [hx]
        _ = g j := one_mul _
    exact hg_ne i j hij hge
  exact ⟨hpow, hne⟩

private lemma ct_tyc_gram_of_label_three
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {κ : Type} (M : CoxeterMatrix κ) {A : Subgroup (MulAut ↥Bs)}
    (ε : M.Group ≃* ↥A) (a : κ → MulAut ↥Bs)
    (ha : ∀ i, a i = ((ε (M.simple i) : ↥A) : MulAut ↥Bs))
    (g : κ → V ≃ₗ[ZMod 3] V) (hg : ∀ i, g i = ggLin (p := 3) ι (a i))
    (hg_ne : ∀ i j, i ≠ j → g i ≠ g j)
    (v : κ → V) (hv_norm : ∀ i, Q (v i) ≠ 0)
    (hv_formula : ∀ i w, g i w =
      w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i) :
    ∀ i j, i ≠ j → M.M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0 := by
  have h3 := ct_tyc_order_three_of_label_three ι M ε a ha g hg hg_ne
  intro i j hij hij3
  have hpow := (h3 i j hij hij3).1
  have hne := (h3 i j hij hij3).2
  have hrel := (ggOrthGram_relations Q (hv_norm i) (hv_norm j)
    (hv_formula i) (hv_formula j)).2 hpow hne
  refine ⟨hrel, ?_⟩
  intro hp
  have hzero : QuadraticMap.polar Q (v i) (v j) ^ 2 = 0 := by rw [hp]; ring
  exact (mul_ne_zero (hv_norm i) (hv_norm j)) (hrel.symm.trans hzero)

private theorem ct_tyc_roots_and_fix
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] [Finite V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : PolarNondeg3 Q)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (ι : Additive ↥Bs ≃+ V)
    (horthQ : ∀ g : V ≃ₗ[ZMod 3] V,
      (∃ a ∈ ggAInf 3 B Bs x L D J, ggLin (p := 3) ι a = g) ↔ ∀ v, Q (g v) = Q v)
    {κ : Type} (M : CoxeterMatrix κ) (A : Subgroup (MulAut ↥Bs))
    (ε : M.Group ≃* ↥A)
    (hεA : ∀ i, GGIsReflection 3 (((ε (M.simple i) : ↥A) : MulAut ↥Bs)))
    (hAle : A ≤ ggAInf 3 B Bs x L D J) :
    ∃ v : κ → V,
      (∀ i, Q (v i) ≠ 0) ∧
      (∀ i w, ggLin (p := 3) ι (((ε (M.simple i) : ↥A) : MulAut ↥Bs)) w =
        w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i) ∧
      (∀ w, (∀ φ ∈ A, ggLin (p := 3) ι (φ : MulAut ↥Bs) w = w) ↔
        ∀ i, QuadraticMap.polar Q (v i) w = 0) := by
  have horth : ∀ i, ggLin (p := 3) ι (((ε (M.simple i) : ↥A) : MulAut ↥Bs)) ∈
      QuadraticMap.orthogonalGroup Q := by
    intro i
    refine QuadraticMap.mem_orthogonalGroup_iff.mpr ?_
    exact (horthQ _).mp ⟨_, hAle (ε (M.simple i)).property, rfl⟩
  obtain ⟨v, hv_norm, hv_formula⟩ :=
    ct_tyc_exists_roots hQ ι (fun i => ((ε (M.simple i) : ↥A) : MulAut ↥Bs)) hεA horth
  have hgen : Subgroup.closure
      (Set.range (fun i => ((ε (M.simple i) : ↥A) : MulAut ↥Bs))) = A :=
    ct_tyc_closure_eq M ε
  exact ⟨v, hv_norm, hv_formula,
    ct_tyc_fix_iff_orth (Q := Q) ι _ hgen v hv_norm hv_formula⟩

private lemma ct_tyc_fixes_x
    {G : Type} [Group G] {Bs : Subgroup G} {x : G} {L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hxBs : x ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    ∀ φ ∈ ggAutomizer L Bs,
      ggLin (p := 3) ι (φ : MulAut ↥Bs) (ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) =
        ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
  have hfix_gen : ∀ φ ∈ ggInduced L Bs, φ (⟨x, hxBs⟩ : ↥Bs) = ⟨x, hxBs⟩ := by
    rintro φ ⟨d, hdL, _hdN, hdφ⟩
    have hxfix : d * x * d⁻¹ = x := by
      rw [((hLx hdL) x (Set.mem_singleton x)).symm]
      group
    apply Subtype.ext
    rw [hdφ (⟨x, hxBs⟩ : ↥Bs)]
    change d * x * d⁻¹ = x
    exact hxfix
  intro φ hφ
  change φ ∈ Subgroup.closure (ggInduced L Bs) at hφ
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hφ
  · intro ψ hψ
    exact (ggLin_fix_iff (p := 3) ι ψ (⟨x, hxBs⟩ : ↥Bs)).mp (hfix_gen ψ hψ)
  · simp
  · intro ψ χ hψ hχ ihψ ihχ
    rw [map_mul, LinearEquiv.mul_apply, ihχ, ihψ]
  · intro ψ hψ ih
    have h := congrArg (ggLin (p := 3) ι ψ⁻¹) ih
    simpa [← LinearEquiv.mul_apply, ← map_mul] using h.symm

private lemma ct_tyc_fixed_le_span
    {G : Type} [Group G] {Bs : Subgroup G} {x : G} {A : Subgroup (MulAut ↥Bs)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hxBs : x ∈ Bs)
    (hfixz : ∀ b : ↥Bs, (∀ φ ∈ A, φ b = b) → (b : G) ∈ Subgroup.zpowers x) :
    ∀ w, (∀ φ ∈ A, ggLin (p := 3) ι (φ : MulAut ↥Bs) w = w) →
      w ∈ Submodule.span (ZMod 3)
        {ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))} := by
  intro w hw
  let w0 : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  change w ∈ Submodule.span (ZMod 3) {w0}
  let b : ↥Bs := Additive.toMul (ι.symm w)
  have hbw : ι (Additive.ofMul b) = w := by simp [b]
  have hb_fix : ∀ φ ∈ A, φ b = b := by
    intro φ hφ
    rw [ggLin_fix_iff (p := 3) ι φ b, hbw]
    exact hw φ hφ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hfixz b hb_fix)
  have hb_eq : b = (⟨x, hxBs⟩ : ↥Bs) ^ n := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hn.symm
  have hw' : w = n • w0 := by
    rw [← hbw, hb_eq]
    simp [map_zsmul]
    rfl
  rw [Submodule.mem_span_singleton]
  refine ⟨(n : ZMod 3), ?_⟩
  rw [hw']
  exact Int.cast_smul_eq_zsmul (ZMod 3) n w0

private theorem ct_tyc_finrank_span_codim_one
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : PolarNondeg3 Q)
    {G : Type} [Group G] {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {A : Subgroup (MulAut ↥Bs)} {κ : Type} (v : κ → V) {w0 : V}
    (hw0_ne : w0 ≠ 0)
    (hfix : ∀ w, (∀ φ ∈ A, ggLin (p := 3) ι (φ : MulAut ↥Bs) w = w) ↔
      ∀ i, QuadraticMap.polar Q (v i) w = 0)
    (hfixed_le : ∀ w, (∀ φ ∈ A, ggLin (p := 3) ι (φ : MulAut ↥Bs) w = w) →
      w ∈ Submodule.span (ZMod 3) {w0})
    (horth_w0 : ∀ i, QuadraticMap.polar Q (v i) w0 = 0) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range v)) + 1 =
      Module.finrank (ZMod 3) V := by
  refine ct_tyc_finrank_eq (K := ZMod 3) Q hQ
    (Submodule.span (ZMod 3) (Set.range v)) (Submodule.span (ZMod 3) {w0}) ?_
    (finrank_span_singleton hw0_ne)
  intro w
  constructor
  · intro hw
    exact ct_tyc_orth_span_le Q (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact horth_w0 i) hw
  · intro horth
    exact hfixed_le w ((hfix w).mpr
      (fun i => horth (v i) (Submodule.subset_span ⟨i, rfl⟩)))

private lemma ct_tyc_w0_ne
    {G : Type} [Group G] {Bs : Subgroup G} {x : G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hxBs : x ∈ Bs) (hxNe : x ≠ 1) :
    ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 := by
  intro h
  have h0 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
    apply ι.injective
    simpa using h
  have hx_sub_ne : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := fun hx1 => hxNe (Subtype.ext_iff.mp hx1)
  exact hx_sub_ne (Additive.ofMul.injective (by simpa using h0))

theorem ggOrthTy_roots
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hFix : GGSecFiveFixInput)
    {κ : Type} [Fintype κ] [DecidableEq κ] (M : CoxeterMatrix κ)
    (ε : M.Group ≃* ↥(ggAutomizer L Bs))
    (hε : ∀ i, GGIsReflection 3 ((ε (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) :
    ∃ v : κ → V, (∀ i, Q (v i) ≠ 0) ∧
      (∀ i w, ggLin (p := 3) ι ((ε (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) w =
        w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i) ∧
      (∀ i j, i ≠ j → M.M i j = 2 → QuadraticMap.polar Q (v i) (v j) = 0) ∧
      (∀ i j, i ≠ j → M.M i j = 3 →
        QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0) ∧
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range v)) + 1 =
        Module.finrank (ZMod 3) V ∧
      ∃ hx : x ∈ Bs, ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 ∧
        ∀ i, QuadraticMap.polar Q (v i) (ι (Additive.ofMul ⟨x, hx⟩)) = 0 := by
  classical
  have : Finite ↥Bs := by infer_instance
  have : Finite V := Finite.of_injective (⇑ι.symm) ι.symm.injective
  have : FiniteDimensional (ZMod 3) V :=
    (Module.finite_iff_finite (R := ZMod 3) (M := V)).mpr inferInstance
  have hxBs : x ∈ Bs := S.cfg.1.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := S.cfg.1.1.tableB_facts.2.2.2.1
  have hxNe : x ≠ 1 := (S.cfg.1.1.1.2.2.2.2.2.2.1).2.2.1
  let A_L : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs
  let a : κ → A_L := fun i => ε (M.simple i)
  let g : κ → V ≃ₗ[ZMod 3] V := fun i => ggLin (p := 3) ι ((a i : A_L) : MulAut ↥Bs)
  obtain ⟨v, hv_norm, hv_formula, hfix⟩ :=
    ct_tyc_roots_and_fix S.nondeg ι S.orth M A_L ε hε le_sup_left
  have hg_ne : ∀ i j, i ≠ j → g i ≠ g j :=
    ct_tyc_images_ne ι M ε (fun i => ((a i : A_L) : MulAut ↥Bs)) (fun i => rfl) g
      (fun i => rfl)
  have h2rel : ∀ i j, i ≠ j → M.M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0 :=
    ct_tyc_polar_zero_of_label_two Q ι M ε (fun i => ((a i : A_L) : MulAut ↥Bs))
      (fun i => rfl) g (fun i => rfl) hg_ne v hv_norm hv_formula
  have h3rel : ∀ i j, i ≠ j → M.M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0 :=
    ct_tyc_gram_of_label_three Q ι M ε (fun i => ((a i : A_L) : MulAut ↥Bs))
      (fun i => rfl) g (fun i => rfl) hg_ne v hv_norm hv_formula
  let w0 : V := ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hw0_ne : w0 ≠ 0 := by
    simpa [w0] using ct_tyc_w0_ne ι hxBs hxNe
  have hfixz : ∀ b : ↥Bs, (∀ φ ∈ A_L, φ b = b) → (b : G) ∈ Subgroup.zpowers x := by
    intro b hb
    exact hFix G 3 B Bs x L D J 𝒦 S.cfg S.split b hb
  have hfixed_le : ∀ w, (∀ φ ∈ A_L, ggLin (p := 3) ι (φ : MulAut ↥Bs) w = w) →
      w ∈ Submodule.span (ZMod 3) {w0} := by
    intro w hw
    exact ct_tyc_fixed_le_span ι hxBs hfixz w hw
  have hfix_x : ∀ φ ∈ A_L, ggLin (p := 3) ι (φ : MulAut ↥Bs) w0 = w0 := by
    simpa [w0, A_L] using ct_tyc_fixes_x ι hxBs hLx
  have horth_w0 : ∀ i, QuadraticMap.polar Q (v i) w0 = 0 := (hfix w0).mp hfix_x
  have hdim : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range v)) + 1 =
      Module.finrank (ZMod 3) V :=
    ct_tyc_finrank_span_codim_one S.nondeg ι v hw0_ne hfix hfixed_le horth_w0
  refine ⟨v, hv_norm, hv_formula, h2rel, h3rel, hdim, hxBs, ?_, ?_⟩
  · intro h
    exact hw0_ne h
  · simpa [w0] using horth_w0

end CFSG.StandardType.OrthF3

end
