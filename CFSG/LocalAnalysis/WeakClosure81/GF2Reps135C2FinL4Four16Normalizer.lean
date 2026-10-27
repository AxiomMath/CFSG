module

public import CFSG.LieType.SpecialLinear.BorelStd
import CFSG.LieType.SpecialLinear.FieldActor.AutomorphismForm
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.BorelForm
import CFSG.LieType.SpecialLinear.NormalizerLift.IndexBounds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_conj_mem_range_or_borelStd_or_stdAut_zero {K : Type} [Field K] [Fintype K]
    [CharP K 2] {n : ℕ} (hn : 3 ≤ n) {H : Type*} [Group H]
    (π : Matrix.SpecialLinearGroup (Fin n) K →* H) (hπ : Function.Injective π)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    {g : H} (hgN : g ∈ Subgroup.normalizer (π.range : Set H)) (hg2 : g * g = 1) :
    ∃ x : Matrix.SpecialLinearGroup (Fin n) K,
      (π x)⁻¹ * g * π x ∈ π.range ∨
        (∃ B : Matrix.GeneralLinearGroup (Fin n) K, IsUpperGL B ∧ ∃ τ : K ≃+* K,
          ∀ y : Matrix.SpecialLinearGroup (Fin n) K,
            ((π x)⁻¹ * g * π x) * π y = π (borelStd n K B τ 1 y) * ((π x)⁻¹ * g * π x)) ∨
        (∃ (B : Matrix.GeneralLinearGroup (Fin n) K) (τ : K ≃+* K), τ ≠ RingEquiv.refl K ∧
          ∀ y : Matrix.SpecialLinearGroup (Fin n) K,
            ((π x)⁻¹ * g * π x) * π y =
              π (CFSG.QuasithinUnique.K1.stdAut B τ 0 y) * ((π x)⁻¹ * g * π x)) := by
  classical
  have hker : π.ker ≤ scalars n K := by
    rw [(MonoidHom.ker_eq_bot_iff π).mpr hπ]
    exact bot_le
  have hgfin : IsOfFinOrder g := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [pow_two]; exact hg2⟩
  let E : Subgroup H := Subgroup.zpowers g
  have hE : E ≤ rangeNormalizer π := Subgroup.zpowers_le.mpr hgN
  let P : Subgroup H := π.range ⊔ E
  have hNfin : (π.range : Set H).Finite := by
    rw [MonoidHom.coe_range]
    exact Set.finite_range π
  have hEfin : (E : Set H).Finite := hgfin.finite_zpowers
  have hPfin : (P : Set H).Finite := by
    change (↑(π.range ⊔ E) : Set H).Finite
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (π.range) E hE]
    exact hNfin.mul hEfin
  haveI : Fintype P := hPfin.fintype
  have hgP : g ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  let gP : P := ⟨g, hgP⟩
  let πP : Matrix.SpecialLinearGroup (Fin n) K →* P :=
    { toFun x := ⟨π x, Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' x y := Subtype.ext (map_mul π x y) }
  have hπP : Function.Injective πP := fun a b h => hπ (Subtype.ext_iff.mp h)
  have hgP2 : gP ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hg2
  have hgPinv : gP⁻¹ = gP := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hgP2
  have hfwd : ∀ y : Matrix.SpecialLinearGroup (Fin n) K,
      gP * πP y * gP⁻¹ ∈ πP.range := by
    intro y
    have hmem : g * π y * g⁻¹ ∈ π.range :=
      (Subgroup.mem_normalizer_iff.mp hgN (π y)).mp (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    obtain ⟨y', hy'⟩ := MonoidHom.mem_range.mp hmem
    refine MonoidHom.mem_range.mpr ⟨y', ?_⟩
    apply Subtype.ext
    change π y' = (gP : H) * (πP y : H) * (gP : H)⁻¹
    rw [hy']
    rfl
  have hgPnorm : gP ∈ Subgroup.normalizer (πP.range : Set P) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · rintro ⟨y, rfl⟩
      exact hfwd y
    · intro hu
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hu
      have heq : gP * πP y * gP⁻¹ = u := by
        rw [hy, hgPinv]
        calc gP * (gP * u * gP) * gP = (gP * gP) * u * (gP * gP) := by group
          _ = u := by rw [← pow_two, hgP2]; group
      have h := hfwd y
      rw [heq] at h
      exact h
  have hE'le : Subgroup.zpowers gP ≤ rangeNormalizer πP := Subgroup.zpowers_le.mpr hgPnorm
  have hE'2 : IsPGroup 2 (Subgroup.zpowers gP) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    simpa using (orderOf_dvd_iff_pow_eq_one.mpr hgP2 : orderOf gP ∣ 2)
  obtain ⟨x, hx⟩ :=
    CFSG.LieType.SpecialLinear.exists_conj_normalizes_unitriangular (π := πP) (hn := hn)
      (Subgroup.zpowers gP) hE'le hE'2
  refine ⟨x, ?_⟩
  set g'' : H := (π x)⁻¹ * g * π x with hg''
  have hg''2 : g'' * g'' = 1 := by
    rw [hg'']
    calc (π x)⁻¹ * g * π x * ((π x)⁻¹ * g * π x)
        = (π x)⁻¹ * (g * g) * π x := by group
      _ = 1 := by rw [hg2]; group
  have hg''N : g'' ∈ rangeNormalizer π := by
    have hxN : π x ∈ rangeNormalizer π := (π.range).le_normalizer ⟨x, rfl⟩
    rw [hg'']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hgN) hxN
  have hg''U : g'' ∈ Subgroup.normalizer ((unitriangular n K).map π : Set H) := by
    let mP : P := (πP x)⁻¹ * gP * πP x
    have hmP : mP ∈ Subgroup.normalizer ((unitriangular n K).map πP : Set P) :=
      hx gP (Subgroup.mem_zpowers gP)
    have hconj : ∀ t, t ∈ unitriangular n K →
        (mP : H) * π t * (mP : H)⁻¹ ∈ (unitriangular n K).map π := by
      intro t ht
      have h2 := (Subgroup.mem_normalizer_iff.mp hmP (πP t)).mp (Subgroup.mem_map_of_mem πP ht)
      obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.mp h2
      refine Subgroup.mem_map.mpr ⟨s, hs, ?_⟩
      have hval := congrArg Subtype.val hseq
      simpa [πP] using hval
    have hconj_inv : ∀ t, t ∈ unitriangular n K →
        (mP : H)⁻¹ * π t * (mP : H) ∈ (unitriangular n K).map π := by
      intro t ht
      have hmPinv : mP⁻¹ ∈ Subgroup.normalizer ((unitriangular n K).map πP : Set P) :=
        Subgroup.inv_mem _ hmP
      have h2 := (Subgroup.mem_normalizer_iff.mp hmPinv (πP t)).mp
        (Subgroup.mem_map_of_mem πP ht)
      obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.mp h2
      refine Subgroup.mem_map.mpr ⟨s, hs, ?_⟩
      have hval := congrArg Subtype.val hseq
      simpa [πP] using hval
    have hmPH : (mP : H) ∈ Subgroup.normalizer ((unitriangular n K).map π : Set H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
        exact hconj t ht
      · intro hu
        obtain ⟨t, ht, htu⟩ := Subgroup.mem_map.mp hu
        have heq : u = (mP : H)⁻¹ * π t * (mP : H) := by
          calc u = (mP : H)⁻¹ * ((mP : H) * u * (mP : H)⁻¹) * (mP : H) := by group
            _ = (mP : H)⁻¹ * π t * (mP : H) := by rw [← htu]
        rw [heq]
        exact hconj_inv t ht
    rw [hg'']
    convert hmPH using 1
  obtain ⟨B, hB, τ, ε, hε, hlift⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.liftAut_eq_borelStd_of_normalizes
      (π := π) hker hn ⟨g'', hg''N⟩ hg''U
  rcases (show ε = 0 ∨ ε = 1 by omega) with hε0 | hε1
  · rcases eq_or_ne τ (RingEquiv.refl K) with hτ | hτ
    · left
      have hstd : CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn ⟨g'', hg''N⟩).1
          (stdData π hker hn ⟨g'', hg''N⟩).2.1
          (stdData π hker hn ⟨g'', hg''N⟩).2.2 =
          CFSG.QuasithinUnique.K1.stdAut B τ 0 := by
        rw [← liftAut_eq_stdAut, hlift, hε0, borelStd_zero]
      have hfg := stdAut_field_graph_unique hn (stdData_eps_le_one π hker hn ⟨g'', hg''N⟩)
        (by norm_num : (0 : ℕ) ≤ 1) (hstd.trans (by rw [hτ]))
      have hfield : fieldPart π hker hn ⟨g'', hg''N⟩ = 1 := hfg.1
      have hgraph : graphPart π hker hn ⟨g'', hg''N⟩ = 1 := by
        change Multiplicative.ofAdd ((stdData π hker hn ⟨g'', hg''N⟩).2.2 : ZMod 2) = 1
        rw [hfg.2]
        rfl
      exact mem_range_of_fieldPart_graphPart_eq_one (π := π) hker hn hodd hg''N hg''2
        hfield hgraph
    · right
      right
      refine ⟨B, τ, hτ, fun y => ?_⟩
      have hspec := liftAut_spec (π := π) hker hn (⟨g'', hg''N⟩ : rangeNormalizer π) y
      rw [hlift, hε0, borelStd_zero] at hspec
      change ((⟨g'', hg''N⟩ : rangeNormalizer π) : H) * π y =
        π (CFSG.QuasithinUnique.K1.stdAut B τ 0 y) *
          ((⟨g'', hg''N⟩ : rangeNormalizer π) : H)
      rw [hspec]
      group
  · right
    left
    refine ⟨B, hB, τ, ?_⟩
    intro y
    have hspec := liftAut_spec (π := π) hker hn (⟨g'', hg''N⟩ : rangeNormalizer π) y
    rw [hlift, hε1] at hspec
    rw [hspec]
    group

theorem exists_conj_eq_fieldAut_of_stdAut_zero {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 4) {H : Type*} [Group H]
    (π : Matrix.SpecialLinearGroup (Fin 4) K →* H) (hπ : Function.Injective π)
    {g : H} (hg2 : g * g = 1) {B : Matrix.GeneralLinearGroup (Fin 4) K} {τ : K ≃+* K}
    (hτ : τ ≠ RingEquiv.refl K)
    (hg : ∀ y : Matrix.SpecialLinearGroup (Fin 4) K,
      g * π y = π (CFSG.QuasithinUnique.K1.stdAut B τ 0 y) * g) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 4) K, ∀ y : Matrix.SpecialLinearGroup (Fin 4) K,
      ((π x)⁻¹ * g * π x) * π y =
        π (Matrix.SpecialLinearGroup.map τ.toRingHom y) * ((π x)⁻¹ * g * π x) := by
  classical
  set φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) K) :=
    CFSG.QuasithinUnique.K1.stdAut B τ 0 with hφdef
  have hgφ : ∀ y : Matrix.SpecialLinearGroup (Fin 4) K,
      g * π y = π (φ y) * g := by
    intro y
    rw [hφdef]
    exact hg y
  have hφφ : φ * φ = 1 := by
    apply MulEquiv.ext
    intro y
    simp only [MulAut.mul_apply, MulAut.one_apply]
    apply hπ
    have hcy : g * π y * g⁻¹ = π (φ y) := by
      rw [hgφ y]
      group
    have hcφy : g * π (φ y) * g⁻¹ = π (φ (φ y)) := by
      rw [hgφ (φ y)]
      group
    calc π (φ (φ y)) = g * π (φ y) * g⁻¹ := hcφy.symm
      _ = g * (g * π y * g⁻¹) * g⁻¹ := by rw [hcy]
      _ = π y := by
          have hg' : g⁻¹ * g⁻¹ = 1 := by
            rw [← mul_inv_rev, hg2, inv_one]
          rw [show g * (g * π y * g⁻¹) * g⁻¹ = (g * g) * π y * (g⁻¹ * g⁻¹) by group,
            hg2, hg']
          group
  have hττ : τ * τ = 1 := by
    obtain ⟨C, hC⟩ := exists_stdAut_mul (n := 4) (F := K) (by norm_num : 3 ≤ 4) B τ 0 B τ 0
      (by norm_num : (0 : ℕ) ≤ 1) (by norm_num : (0 : ℕ) ≤ 1)
    have h1 : CFSG.QuasithinUnique.K1.stdAut C (τ * τ) ((0 + 0) % 2) =
        CFSG.QuasithinUnique.K1.stdAut (1 : Matrix.GeneralLinearGroup (Fin 4) K)
          (1 : K ≃+* K) 0 := by
      rw [← hC, ← hφdef, hφφ]
      simp [CFSG.QuasithinUnique.K1.stdAut]
    exact (stdAut_field_graph_unique (n := 4) (F := K) (by norm_num : 3 ≤ 4)
      (by norm_num : (0 + 0) % 2 ≤ 1) (by norm_num : (0 : ℕ) ≤ 1) h1).1
  have hτ2 : τ.trans τ = RingEquiv.refl K := by
    have h : τ * τ = 1 := hττ
    rw [RingAut.one_eq_refl] at h
    rw [← h]
    apply RingEquiv.ext
    intro z
    simp [RingEquiv.trans_apply, RingAut.mul_apply]
  have hff : CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) K τ *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) K τ = 1 := by
    rw [← map_mul, hττ, map_one]
  have hmul : φ * φ = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K
      (B * Matrix.GeneralLinearGroup.map τ.toRingHom B) := by
    have hφeq : φ = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K B *
        CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) K τ := by
      rw [hφdef]
      simp [CFSG.QuasithinUnique.K1.stdAut]
    rw [hφeq]
    set cB : MulAut (Matrix.SpecialLinearGroup (Fin 4) K) :=
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K B with hcB
    set fτ : MulAut (Matrix.SpecialLinearGroup (Fin 4) K) :=
      CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 4) K τ with hfτ
    have hcomm : fτ * cB = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        4 K (Matrix.GeneralLinearGroup.map τ.toRingHom B) * fτ := by
      rw [hfτ, hcB]
      have h := slFieldAut_mul_slConjugation (n := 4) (F := K) τ B
      rw [show CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin 4) τ B =
        Matrix.GeneralLinearGroup.map τ.toRingHom B from rfl] at h
      exact h
    have hff' : fτ * fτ = 1 := by
      rw [hfτ]
      exact hff
    calc cB * fτ * (cB * fτ)
        = cB * (fτ * cB) * fτ := by group
      _ = cB * (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K
            (Matrix.GeneralLinearGroup.map τ.toRingHom B) * fτ) * fτ := by rw [hcomm]
      _ = (cB * CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K
            (Matrix.GeneralLinearGroup.map τ.toRingHom B)) * (fτ * fτ) := by group
      _ = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K
            (B * Matrix.GeneralLinearGroup.map τ.toRingHom B) * (fτ * fτ) := by
          rw [hcB, ← map_mul]
      _ = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K
            (B * Matrix.GeneralLinearGroup.map τ.toRingHom B) * 1 := by rw [hff']
      _ = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K
            (B * Matrix.GeneralLinearGroup.map τ.toRingHom B) := by rw [mul_one]
  have hcenter : B * Matrix.GeneralLinearGroup.map τ.toRingHom B ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 4) K) := by
    rw [← CFSG.LinearGroups.ker_slConjugation 4 K, MonoidHom.mem_ker]
    exact hmul ▸ hφφ
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨lam, hlam⟩ := MonoidHom.mem_range.mp hcenter
  have hb : B * Matrix.GeneralLinearGroup.map τ.toRingHom B =
      Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 (lam : K) lam.ne_zero) := by
    rw [← hlam]
    congr 1
    exact Units.ext rfl
  obtain ⟨P, hP⟩ := exists_stdAut_eq_conj (n := 4) (F := K) (σ := τ) (b := B) (lam := (lam : K))
    hτ2 hτ (by norm_num : 3 ≤ 4) lam.ne_zero hb
  set c : Kˣ := P.det with hc
  have hc3 : c ^ 3 = 1 := by
    have hcard : Fintype.card Kˣ = 3 := by
      rw [Fintype.card_units, hK]
    rw [← hcard]
    exact pow_card_eq_one
  set P₀ : Matrix.GeneralLinearGroup (Fin 4) K :=
    Matrix.GeneralLinearGroup.scalar (Fin 4) c⁻¹ * P with hP₀
  have hP₀det : P₀.det = 1 := by
    rw [hP₀, map_mul, Matrix.GeneralLinearGroup.det_scalar, ← hc]
    simp only [Fintype.card_fin]
    rw [show (c⁻¹) ^ 4 * c = (c ^ 3)⁻¹ by group, hc3, inv_one]
  have hP₀det' : (P₀ : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    simpa using congrArg Units.val hP₀det
  let x : Matrix.SpecialLinearGroup (Fin 4) K :=
    ⟨(P₀ : Matrix (Fin 4) (Fin 4) K), hP₀det'⟩
  have hxP₀ : (Matrix.SpecialLinearGroup.toGL x : Matrix.GeneralLinearGroup (Fin 4) K) = P₀ :=
    Units.ext rfl
  have hstdA : ∀ A : Matrix.GeneralLinearGroup (Fin 4) K,
      CFSG.QuasithinUnique.K1.stdAut A (RingEquiv.refl K) 0 =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K A := by
    intro A
    simp only [CFSG.QuasithinUnique.K1.stdAut, ← RingAut.one_eq_refl, map_one, pow_zero, mul_one]
  have hstd_x : CFSG.QuasithinUnique.K1.stdAut (Matrix.SpecialLinearGroup.toGL x)
      (RingEquiv.refl K) 0 = CFSG.QuasithinUnique.K1.stdAut P (RingEquiv.refl K) 0 := by
    rw [hstdA (Matrix.SpecialLinearGroup.toGL x), hstdA P, hxP₀, hP₀]
    rw [map_mul, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar,
      one_mul]
  have hconj_x : CFSG.QuasithinUnique.K1.stdAut P (RingEquiv.refl K) 0 = MulAut.conj x := by
    rw [← hstd_x]
    exact stdAut_toGL_one x
  have hconj_xinv : CFSG.QuasithinUnique.K1.stdAut P⁻¹ (RingEquiv.refl K) 0 =
      MulAut.conj x⁻¹ := by
    have hstdinv : CFSG.QuasithinUnique.K1.stdAut P⁻¹ (RingEquiv.refl K) 0 =
        (CFSG.QuasithinUnique.K1.stdAut P (RingEquiv.refl K) 0)⁻¹ := by
      simp only [CFSG.QuasithinUnique.K1.stdAut, RingAut.one_eq_refl, map_one, pow_zero, mul_one]
      exact map_inv (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 K) P
    rw [hstdinv, hconj_x]
    exact (map_inv (MulAut.conj (G := Matrix.SpecialLinearGroup (Fin 4) K)) x).symm
  have hφ : ∀ z : Matrix.SpecialLinearGroup (Fin 4) K,
      φ z = x * (CFSG.QuasithinUnique.K1.stdAut 1 τ 0) (x⁻¹ * z * x) * x⁻¹ := by
    intro z
    rw [hφdef, hP z, hconj_x, hconj_xinv]
    simp only [MulAut.conj_apply]
    group
  have hfτ : ∀ y : Matrix.SpecialLinearGroup (Fin 4) K,
      (CFSG.QuasithinUnique.K1.stdAut 1 τ 0) y =
        Matrix.SpecialLinearGroup.map τ.toRingHom y := by
    intro y
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    simp
  refine ⟨x, fun y => ?_⟩
  set d : H := (π x)⁻¹ * g * π x with hd
  have hconj : d * π y * d⁻¹ = π (Matrix.SpecialLinearGroup.map τ.toRingHom y) := by
    rw [hd]
    have hφz : φ (x * y * x⁻¹) =
        x * (CFSG.QuasithinUnique.K1.stdAut 1 τ 0) y * x⁻¹ := by
      have h := hφ (x * y * x⁻¹)
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h
    have hπxy : π (x * y * x⁻¹) = π x * π y * (π x)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have hφπ : π (φ (x * y * x⁻¹)) =
        π x * π ((CFSG.QuasithinUnique.K1.stdAut 1 τ 0) y) * (π x)⁻¹ := by
      rw [hφz, map_mul, map_mul, map_inv]
    calc (π x)⁻¹ * g * π x * π y * ((π x)⁻¹ * g * π x)⁻¹
        = (π x)⁻¹ * (g * (π x * π y * (π x)⁻¹) * g⁻¹) * π x := by group
      _ = (π x)⁻¹ * (g * π (x * y * x⁻¹) * g⁻¹) * π x := by rw [hπxy]
      _ = (π x)⁻¹ * π (φ (x * y * x⁻¹)) * π x := by
            rw [hg (x * y * x⁻¹)]
            group
      _ = (π x)⁻¹ * (π x * π ((CFSG.QuasithinUnique.K1.stdAut 1 τ 0) y) * (π x)⁻¹) * π x := by
            rw [hφπ]
      _ = π (Matrix.SpecialLinearGroup.map τ.toRingHom y) := by
            rw [hfτ y]
            group
  rw [← hconj]
  group

theorem exists_conj_mem_range_or_borelStd_or_fieldAut {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : Fintype.card K = 4) {H : Type*} [Group H]
    (π : Matrix.SpecialLinearGroup (Fin 4) K →* H) (hπ : Function.Injective π)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    {g : H} (hgN : g ∈ Subgroup.normalizer (π.range : Set H)) (hg2 : g * g = 1) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 4) K,
      (π x)⁻¹ * g * π x ∈ π.range ∨
        (∃ B : Matrix.GeneralLinearGroup (Fin 4) K, IsUpperGL B ∧ ∃ τ : K ≃+* K,
          ∀ y : Matrix.SpecialLinearGroup (Fin 4) K,
            ((π x)⁻¹ * g * π x) * π y = π (borelStd 4 K B τ 1 y) * ((π x)⁻¹ * g * π x)) ∨
        (∃ τ : K ≃+* K, τ ≠ RingEquiv.refl K ∧
          ∀ y : Matrix.SpecialLinearGroup (Fin 4) K,
            ((π x)⁻¹ * g * π x) * π y =
              π (Matrix.SpecialLinearGroup.map τ.toRingHom y) * ((π x)⁻¹ * g * π x)) := by
  obtain ⟨x, hx⟩ := exists_conj_mem_range_or_borelStd_or_stdAut_zero (by norm_num : 3 ≤ 4) π hπ
    hodd hgN hg2
  rcases hx with h | h | ⟨B, τ, hτ, hB⟩
  · exact ⟨x, Or.inl h⟩
  · exact ⟨x, Or.inr (Or.inl h)⟩
  · have hg'2 : ((π x)⁻¹ * g * π x) * ((π x)⁻¹ * g * π x) = 1 := by
      calc ((π x)⁻¹ * g * π x) * ((π x)⁻¹ * g * π x) = (π x)⁻¹ * (g * g) * π x := by group
        _ = 1 := by rw [hg2]; group
    obtain ⟨x₂, hx₂⟩ := exists_conj_eq_fieldAut_of_stdAut_zero hK π hπ hg'2 hτ hB
    refine ⟨x * x₂, Or.inr (Or.inr ⟨τ, hτ, fun y => ?_⟩)⟩
    have hconj : (π (x * x₂))⁻¹ * g * π (x * x₂) = (π x₂)⁻¹ * ((π x)⁻¹ * g * π x) * π x₂ := by
      rw [map_mul]
      group
    rw [hconj]
    exact hx₂ y

end CFSG.LocalAnalysis.WeakClosure81
