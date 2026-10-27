module

public import CFSG.LieType.SpecialLinear.BorelStd
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.BorelForm
import CFSG.LieType.SpecialLinear.NormalizerLift.IndexBounds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.SpecialLinear
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_conj_mem_range_or_borelStd_one {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {n : ℕ} (hn : 3 ≤ n) {H : Type*} [Group H]
    (π : Matrix.SpecialLinearGroup (Fin n) K →* H) (hπ : Function.Injective π)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    {g : H} (hgN : g ∈ Subgroup.normalizer (π.range : Set H)) (hg2 : g * g = 1) :
    ∃ x : Matrix.SpecialLinearGroup (Fin n) K,
      (π x)⁻¹ * g * π x ∈ π.range ∨
        ∃ B : Matrix.GeneralLinearGroup (Fin n) K, IsUpperGL B ∧ ∃ τ : K ≃+* K,
          ∀ y : Matrix.SpecialLinearGroup (Fin n) K,
            ((π x)⁻¹ * g * π x) * π y = π (borelStd n K B τ 1 y) * ((π x)⁻¹ * g * π x) := by
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
  haveI : Subsingleton (K ≃+* K) := by
    constructor
    intro f f' 
    ext x
    have hcard : Nat.card K = 2 := by
      rw [Nat.card_eq_fintype_card, hK]
    obtain ⟨y, hy0, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hcard
    have hxy : x = 0 ∨ x = y := by
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr (hyuniq x hx0)
    rcases hxy with hx0 | hxy
    · rw [hx0]; simp
    · rw [hxy]
      have hfy : f y = y := by
        have hne : f y ≠ 0 := by
          intro hfy0
          exact hy0 (f.injective (hfy0.trans (map_zero f).symm))
        exact hyuniq (f y) hne
      have hf'y : f' y = y := by
        have hne : f' y ≠ 0 := by
          intro hfy0
          exact hy0 (f'.injective (hfy0.trans (map_zero f').symm))
        exact hyuniq (f' y) hne
      rw [hfy, hf'y]
  rcases (show ε = 0 ∨ ε = 1 by omega) with hε0 | hε1
  · left
    have hfield : fieldPart π hker hn ⟨g'', hg''N⟩ = 1 := Subsingleton.elim _ _
    have hstd : CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn ⟨g'', hg''N⟩).1
        (stdData π hker hn ⟨g'', hg''N⟩).2.1
        (stdData π hker hn ⟨g'', hg''N⟩).2.2 =
        CFSG.QuasithinUnique.K1.stdAut B τ 0 := by
      rw [← liftAut_eq_stdAut, hlift, hε0, borelStd_zero]
    have hδ : (stdData π hker hn ⟨g'', hg''N⟩).2.2 = 0 :=
      (stdAut_field_graph_unique hn (stdData_eps_le_one π hker hn ⟨g'', hg''N⟩)
        (by norm_num : (0 : ℕ) ≤ 1) hstd).2
    have hgraph : graphPart π hker hn ⟨g'', hg''N⟩ = 1 := by
      change Multiplicative.ofAdd ((stdData π hker hn ⟨g'', hg''N⟩).2.2 : ZMod 2) = 1
      rw [hδ]
      rfl
    exact mem_range_of_fieldPart_graphPart_eq_one (π := π) hker hn hodd hg''N hg''2
      hfield hgraph
  · right
    refine ⟨B, hB, τ, ?_⟩
    intro y
    have hspec := liftAut_spec (π := π) hker hn (⟨g'', hg''N⟩ : rangeNormalizer π) y
    rw [hlift, hε1] at hspec
    rw [hspec]
    group

end CFSG.LocalAnalysis.WeakClosure81
