module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearWitness
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvdBlock
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace SLRep

noncomputable abbrev slConj (n : ℕ) (F : Type) [Field F] (A : GL (Fin n) F) :
    MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
  ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A

variable {G : Type} [Group G] {n : ℕ} {F : Type} [Field F]

theorem mem_scalars_of_ker_le_center {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : φ g = 1) : g ∈ scalars n F := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hg)
  rw [Fintype.card_fin] at hr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, by simp, ?_⟩
    ext i
    exact i.elim0
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hr
    exact zero_ne_one hr
  exact ⟨Units.mk0 r hr0, by ext; simpa using hr, by rw [← hrg]; rfl⟩

theorem range_inf_centralizer_eq_map {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) {b : G}
    {D : GL (Fin n) F} {t : Fin n → F} (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) {T : Finset (Fin n)}
    (htc : ∀ i j, i ∉ T → j ∉ T → t i = t j) (hT : T.card < Tᶜ.card) :
    φ.range ⊓ Subgroup.centralizer {b} = (ggFix (slConj n F D)).map φ := by
  ext g
  constructor
  · rintro ⟨⟨s, rfl⟩, hc⟩
    refine ⟨s, TypeA.mem_fix_of_apply_eq (fun g hg => mem_scalars_of_ker_le_center hker hg)
      hD htc hT ?_, rfl⟩
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [← hb s, ← hc', mul_inv_cancel_right]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : b * φ s * b⁻¹ = φ s := by rw [hb s, mem_ggFix.mp hs]
    calc φ s * b = b * φ s * b⁻¹ * b := by rw [h1]
      _ = b * φ s := by group

theorem compIndicator_comm_of_mem_fix {D : GL (Fin n) F} {t : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t) {S : Finset (Fin n)} {μ : F}
    (hS : ∀ i ∈ S, t i = μ) (hSc : ∀ i ∉ S, t i ≠ μ) {c : Matrix.SpecialLinearGroup (Fin n) F}
    (hc : c ∈ ggFix (slConj n F D)) :
    compIndicator F S * (c : Matrix (Fin n) (Fin n) F) =
      (c : Matrix (Fin n) (Fin n) F) * compIndicator F S := by
  have h0 := (TypeA.mem_ggFix_slConjugation_iff hD).mp hc
  ext i j
  rw [compIndicator_mul_apply, compIndicator, Matrix.mul_diagonal]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp [hi, hj]
  · rw [ite_eq_left hi, ite_eq_right hj, mul_one, h0 i j (by rw [hS i hi]; exact (hSc j hj).symm)]
  · rw [ite_eq_right hi, ite_eq_left hj, mul_zero, h0 i j (by rw [hS j hj]; exact hSc i hi)]
  · simp [hi, hj]

theorem isComponentOf_map_coordBlockSL [Finite F] (h4 : 4 ≤ Nat.card F)
    {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) {b : G}
    {D : GL (Fin n) F} {t : Fin n → F} (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) {S : Finset (Fin n)} {μ : F}
    (hS : ∀ i ∈ S, t i = μ) (hSc : ∀ i ∉ S, t i ≠ μ) (hcard : Sᶜ.card < S.card)
    (hS2 : 2 ≤ S.card) {i₀ : Fin n} (hi₀ : i₀ ∉ S) :
    IsComponentOf ((coordBlockSL F S).map φ) (φ.range ⊓ Subgroup.centralizer {b}) := by
  have htc : ∀ i j, i ∉ Sᶜ → j ∉ Sᶜ → t i = t j := fun i j hi hj => by
    rw [hS i (by simpa using hi), hS j (by simpa using hj)]
  rw [range_inf_centralizer_eq_map hker hD hb htc (by rwa [compl_compl])]
  set C := ggFix (slConj n F D) with hC
  set J₀ := coordBlockSL F S with hJ₀
  have hJ₀C : J₀ ≤ C := by
    have := TypeA.coordBlockSL_le_fix (T := Sᶜ) hD htc
    rwa [compl_compl] at this
  have hJn : ∀ c ∈ C, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀ := fun c hc j hj =>
    conj_mem_coordBlockSL (compIndicator_comm_of_mem_fix hD hS hSc hc) hj
  have hinj : ∀ j ∈ J₀, φ j = 1 → j = 1 := fun j hj h1 => by
    have hj' : j ∈ coordBlockSL F Sᶜᶜ := by rwa [compl_compl]
    exact TypeA.coordBlockSL_compl_inf_scalars (T := Sᶜ) (by simpa using hi₀) hj'
      (mem_scalars_of_ker_le_center hker h1)
  have hq : CFSG.IsQuasisimple J₀ := isQuasisimple_coordBlockSL hS2 h4
  have hinj' : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (φ.comp J₀.subtype).range = J₀.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple (J₀.map φ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange)) hq
  have hJF : J₀.map φ ≤ C.map φ := Subgroup.map_mono hJ₀C
  have hJn' : ((J₀.map φ).subgroupOf (C.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ f ⟨j, hj, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * j * c⁻¹, hJn c hc j hj, by rw [map_mul, map_mul, map_inv]⟩
  exact ⟨hJF, IsSubnormal.step hJF hJn' (IsSubnormal.refl _),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJq⟩

theorem diagonal_GL_comm {D D' : GL (Fin n) F} {t t' : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hD' : (D' : Matrix (Fin n) (Fin n) F) = diagonal t') : D * D' = D' * D := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD, hD', diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem slConj_eq_self_of_diagonal {D : GL (Fin n) F} {t : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t) {d : Matrix.SpecialLinearGroup (Fin n) F}
    {δ : Fin n → F} (hd : (d : Matrix (Fin n) (Fin n) F) = diagonal δ) : slConj n F D d = d :=
  mem_ggFix.mp ((TypeA.mem_ggFix_slConjugation_iff hD).mpr fun i j hij => by
    rw [hd, diagonal_apply_ne _ (by rintro rfl; exact hij rfl)])

@[expose] def GGFrameDiag (φ : Matrix.SpecialLinearGroup (Fin n) F →* G) (b : G) : Prop :=
  ∃ (D : GL (Fin n) F) (t : Fin n → F), (D : Matrix (Fin n) (Fin n) F) = diagonal t ∧
    ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)

theorem mem_of_frame_diagonal_inner {p : ℕ} {B Bs : Subgroup G} (hBs : GGBstar p B Bs)
    {φ : Matrix.SpecialLinearGroup (Fin n) F →* G} (hframe : ∀ b ∈ Bs, GGFrameDiag φ b)
    {d : Matrix.SpecialLinearGroup (Fin n) F} {δ : Fin n → F}
    (hd : (d : Matrix (Fin n) (Fin n) F) = diagonal δ) (hdp : d ^ p = 1) : φ d ∈ Bs := by
  refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    (by rw [← map_pow, hdp, map_one])
  obtain ⟨D, t, hD, hbD⟩ := hframe b hb
  have h1 : b * φ d * b⁻¹ = φ d := by rw [hbD, slConj_eq_self_of_diagonal hD hd]
  calc b * φ d = b * φ d * b⁻¹ * b := by group
    _ = φ d * b := by rw [h1]

theorem commute_of_frame {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {g b : G} {D D' : GL (Fin n) F}
    (hDD : D * D' = D' * D) (hg : ∀ s, g * φ s * g⁻¹ = φ (slConj n F D s))
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D' s)) : g * b = b * g := by
  have hact : ∀ s, (g * b) * φ s * (g * b)⁻¹ = (b * g) * φ s * (b * g)⁻¹ := by
    intro s
    have hm : ∀ A A' : GL (Fin n) F, slConj n F (A * A') = slConj n F A * slConj n F A' :=
      fun A A' => map_mul _ A A'
    have e1 : (g * b) * φ s * (g * b)⁻¹ = φ (slConj n F (D * D') s) := by
      rw [hm, MulAut.mul_apply, ← hg, ← hb]
      group
    have e2 : (b * g) * φ s * (b * g)⁻¹ = φ (slConj n F (D' * D) s) := by
      rw [hm, MulAut.mul_apply, ← hb, ← hg]
      group
    rw [e1, e2, hDD]
  have hc : (b * g)⁻¹ * (g * b) ∈ Subgroup.centralizer (φ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    have h := hact s
    calc φ s * ((b * g)⁻¹ * (g * b)) =
        (b * g)⁻¹ * ((b * g) * φ s * (b * g)⁻¹) * (g * b) := by group
      _ = (b * g)⁻¹ * ((g * b) * φ s * (g * b)⁻¹) * (g * b) := by rw [h]
      _ = (b * g)⁻¹ * (g * b) * φ s := by group
  rw [hcent, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem mem_of_frame_diagonal {p : ℕ} {B Bs : Subgroup G} (hBs : GGBstar p B Bs)
    {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) (hframe : ∀ b ∈ Bs, GGFrameDiag φ b)
    {g : G} (hg : GGFrameDiag φ g) (hgp : g ^ p = 1) : g ∈ Bs := by
  refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) hgp
  obtain ⟨D, t, hD, hgD⟩ := hg
  obtain ⟨D', t', hD', hbD⟩ := hframe b hb
  exact commute_of_frame hcent (diagonal_GL_comm hD' hD) hbD hgD

theorem ne_zero_of_diagonal {D : GL (Fin n) F} {t : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t) (k : Fin n) : t k ≠ 0 := by
  intro hk
  have h1 := D.isUnit.map (Matrix.detMonoidHom (n := Fin n) (R := F))
  rw [Matrix.coe_detMonoidHom, hD, det_diagonal,
    Finset.prod_eq_zero (Finset.mem_univ k) hk] at h1
  exact not_isUnit_zero h1

theorem eq_of_map_transvection_eq {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) {i j : Fin n}
    (hij : i ≠ j) {a c : F}
    (h : φ (Matrix.SpecialLinearGroup.transvection hij a) =
      φ (Matrix.SpecialLinearGroup.transvection hij c)) : a = c := by
  have hmem : Matrix.SpecialLinearGroup.transvection hij (-a + c) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, Matrix.SpecialLinearGroup.transvection_add,
      ← Matrix.SpecialLinearGroup.transvection_inv, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hker hmem)
  have h1 := congrFun (congrFun hr i) j
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij, Matrix.add_apply, Matrix.one_apply_ne hij,
    Matrix.single_apply_same, zero_add] at h1
  linear_combination h1

theorem slConj_transvection {D : GL (Fin n) F} {t : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t) {i j : Fin n} (hij : i ≠ j) (c : F) :
    slConj n F D (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij (t i * c * (t j)⁻¹) := by
  have ht0 := ne_zero_of_diagonal hD
  apply Subtype.ext
  rw [ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hD,
    TypeA.coe_inv_of_diagonal hD, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  rw [TypeA.diagonal_conj_apply, Matrix.add_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have hne : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [hne, ht0 a]
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab]
    · simp [hab, h]

theorem coe_pow_of_diagonal {D : GL (Fin n) F} {t : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t) (k : ℕ) :
    ((D ^ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal (t ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ih, hD, diagonal_mul_diagonal, pow_succ]
    rfl

theorem pow_act {φ : Matrix.SpecialLinearGroup (Fin n) F →* G} {b : G} {D : GL (Fin n) F}
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) (k : ℕ)
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    b ^ k * φ s * (b ^ k)⁻¹ = φ (slConj n F (D ^ k) s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have hm : slConj n F (D ^ k * D) = slConj n F (D ^ k) * slConj n F D := map_mul _ _ _
    rw [pow_succ, pow_succ, hm, MulAut.mul_apply, ← ih, ← hb]
    group

theorem pow_eq_pow_of_frame {p : ℕ} {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) {b : G}
    (hbp : b ^ p = 1) {D : GL (Fin n) F} {t : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) (i j : Fin n) : t i ^ p = t j ^ p := by
  by_cases hij : i = j
  · rw [hij]
  have h := pow_act hb p (Matrix.SpecialLinearGroup.transvection hij 1)
  rw [hbp, one_mul, inv_one, mul_one, slConj_transvection (coe_pow_of_diagonal hD p) hij] at h
  have h1 := eq_of_map_transvection_eq hker hij h
  have hj0 : t j ^ p ≠ 0 := pow_ne_zero _ (ne_zero_of_diagonal hD j)
  simp only [Pi.pow_apply, mul_one] at h1
  field_simp at h1
  exact h1.symm

theorem eq_of_act_eq {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {x y : G}
    (h : ∀ s, x * φ s * x⁻¹ = y * φ s * y⁻¹) : x = y := by
  have hc : y⁻¹ * x ∈ Subgroup.centralizer (φ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    calc φ s * (y⁻¹ * x) = y⁻¹ * (y * φ s * y⁻¹) * x := by group
      _ = y⁻¹ * (x * φ s * x⁻¹) * x := by rw [h]
      _ = y⁻¹ * x * φ s := by group
  rw [hcent, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem card_le_of_frame [Finite F] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1)
    {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (hcent : Subgroup.centralizer (φ.range : Set G) = ⊥) {X : Subgroup G}
    (hXp : ∀ b ∈ X, b ^ p = 1) (hframe : ∀ b ∈ X, GGFrameDiag φ b) {S : Finset (Fin n)}
    {i₀ : Fin n}
    (hXS : ∀ b ∈ X, ∀ (D : GL (Fin n) F) (t : Fin n → F),
      (D : Matrix (Fin n) (Fin n) F) = diagonal t → (∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) →
        ∀ i ∈ S, t i = t i₀) :
    Nat.card X ≤ p ^ Sᶜ.card := by
  classical
  choose D t hD hb using fun x : X => hframe x.1 x.2
  have ht0 : ∀ x k, t x k ≠ 0 := fun x k => ne_zero_of_diagonal (hD x) k
  let r : X → (↥Sᶜ → rootsOfUnity p F) := fun x j =>
    ⟨Units.mk0 (t x j / t x i₀) (div_ne_zero (ht0 x j) (ht0 x i₀)), by
      rw [mem_rootsOfUnity]
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, div_pow,
        pow_eq_pow_of_frame hker (hXp x.1 x.2) (hD x) (hb x) j i₀,
        div_self (pow_ne_zero _ (ht0 x i₀)), Units.val_one]⟩
  have hr : Function.Injective r := by
    intro x y hxy
    have hk : ∀ k, t x k / t x i₀ = t y k / t y i₀ := by
      intro k
      by_cases hkS : k ∈ S
      · rw [hXS x.1 x.2 _ _ (hD x) (hb x) k hkS, hXS y.1 y.2 _ _ (hD y) (hb y) k hkS,
          div_self (ht0 x i₀), div_self (ht0 y i₀)]
      · have h1 := congrArg (fun g => (((g ⟨k, by simpa using hkS⟩ : rootsOfUnity p F) : Fˣ) : F))
          hxy
        simpa [r] using h1
    have he : ∀ a c, t x a * (t x c)⁻¹ = t y a * (t y c)⁻¹ := by
      intro a c
      have hx0 := ht0 x i₀
      have hy0 := ht0 y i₀
      have hxc := ht0 x c
      have hyc := ht0 y c
      calc t x a * (t x c)⁻¹ = (t x a / t x i₀) / (t x c / t x i₀) := by field_simp
        _ = (t y a / t y i₀) / (t y c / t y i₀) := by rw [hk a, hk c]
        _ = t y a * (t y c)⁻¹ := by field_simp
    have hconj : ∀ s, slConj n F (D x) s = slConj n F (D y) s := by
      intro s
      apply Subtype.ext
      rw [ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
        ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hD x, hD y,
        TypeA.coe_inv_of_diagonal (hD x), TypeA.coe_inv_of_diagonal (hD y)]
      ext a c
      rw [TypeA.diagonal_conj_apply, TypeA.diagonal_conj_apply]
      calc t x a * (s : Matrix (Fin n) (Fin n) F) a c * (t x c)⁻¹ =
          (t x a * (t x c)⁻¹) * (s : Matrix (Fin n) (Fin n) F) a c := by ring
        _ = (t y a * (t y c)⁻¹) * (s : Matrix (Fin n) (Fin n) F) a c := by rw [he a c]
        _ = _ := by ring
    exact Subtype.ext (eq_of_act_eq hcent fun s => by rw [hb x, hb y, hconj])
  calc Nat.card X ≤ Nat.card (↥Sᶜ → rootsOfUnity p F) := Nat.card_le_card_of_injective r hr
    _ = p ^ Sᶜ.card := by
      rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpF, Nat.card_eq_fintype_card,
        Fintype.card_coe]

end SLRep

end CFSG.StandardType
