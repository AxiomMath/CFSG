module

public import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
public import CFSG.RankThree.CentralCover.SteinbergBNEvenLinearSplitTorus
public import CFSG.RankThree.Classical.SteinbergBJRectangularUnipotent
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical

theorem exists_projectiveSL_of_statedClassicalModel_PSL {T : Type} [Group T] {n ℓ f : ℕ}
    (h : StatedClassicalModel T .PSL n ℓ f) :
    ℓ.Prime ∧ 1 ≤ f ∧ 2 ≤ n ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = ℓ ^ f ∧
        Nonempty (T ≃* LinearFlag.projectiveSL n K) := by
  obtain ⟨⟨hℓ, hf, hn, -, -⟩, K, hK, hfin, hcard, ⟨e⟩⟩ := h
  exact ⟨hℓ, hf, hn, K, hK, hfin, hcard, ⟨(e.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩

theorem isElementaryAbelian_of_le {p : ℕ} {G : Type*} [Group G] {U E : Subgroup G}
    (hUE : U ≤ E) [IsElementaryAbelian p E] : IsElementaryAbelian p U :=
  CFSG.IsElementaryAbelian.of_le inferInstance hUE

theorem exists_elementaryAbelian_two_pow_five_projectiveSL {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    ∃ U : Subgroup (LinearFlag.projectiveSL 5 K), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Finset (Fin 5) := {0, 1} with hI
  set J : Finset (Fin 5) := {2, 3, 4} with hJ
  have hIJ : Disjoint I J := by decide
  set R : Finset (Fin 5 × Fin 5) := I ×ˢ J with hRdef
  have hR : R ⊆ I ×ˢ J := Finset.Subset.refl _
  set ρ := (LinearFlag.proj 5 K).comp (rectHom K hIJ hR) with hρ
  have hinj : Function.Injective ρ := proj_comp_rectHom_injective hIJ hR
  have hsq : ∀ c : Multiplicative (R → K), c ^ 2 = 1 := by
    intro c
    apply Multiplicative.toAdd.injective
    funext α
    simp [pow_two, CharTwo.add_self_eq_zero]
  have hEel : IsElementaryAbelian 2 ρ.range := by
    refine
      { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
        exponent_dvd_p := ?_ }
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      apply Subtype.ext
      change ρ c * ρ d = ρ d * ρ c
      rw [← map_mul, ← map_mul, mul_comm]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
      obtain ⟨g, c, rfl⟩ := g
      apply Subtype.ext
      change ρ c ^ 2 = 1
      rw [← map_pow, hsq c, map_one]
  have hEcard : Nat.card ρ.range = 2 ^ (6 * f) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hK, Nat.card_eq_fintype_card,
      Fintype.card_coe, ← pow_mul]
    have : R.card = 6 := by decide
    rw [this, mul_comm]
  have h2 : 2 ^ 5 ∣ Nat.card ρ.range := by
    rw [hEcard]; exact pow_dvd_pow 2 (by omega)
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 2 h2
  refine ⟨K'.map ρ.range.subtype, ?_, ?_⟩
  · have hle : K'.map ρ.range.subtype ≤ ρ.range := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have := hEel
    exact isElementaryAbelian_of_le hle
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK']


theorem isSimpleGroup_projectiveSL_five {K : Type} [Field K] :
    IsSimpleGroup (LinearFlag.projectiveSL 5 K) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 5) (by omega)
    (Or.inl (by omega))).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 K).symm.isSimpleGroup

theorem even_square_field_linear_five_rank_ge_four {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : 1 ≤ f) (hfe : Even f) {T : Type} [Group T]
    (hT : StatedClassicalModel T .PSL 5 2 f) (H : Subgroup G) (π : H →* T)
    (hπ : Function.Surjective π) : 4 ≤ evenRank G := by
  classical
  by_contra hlt
  have hle : evenRank G ≤ 3 := by omega
  have he : twoLocalOddRank G ≤ 3 := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]; exact hle
  obtain ⟨-, -, -, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_projectiveSL_of_statedClassicalModel_PSL hT
  obtain ⟨U, hUel, hUcard⟩ := exists_elementaryAbelian_two_pow_five_projectiveSL hf hKcard
  have hsimpP : IsSimpleGroup (LinearFlag.projectiveSL 5 K) := isSimpleGroup_projectiveSL_five
  have : Finite (LinearFlag.projectiveSL 5 K) := inferInstance
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have := hsimpP
  have hS : IsSimpleGroup T := e.isSimpleGroup
  have := hS
  have hU' : ∃ V : Subgroup T, IsElementaryAbelian 2 V ∧ Nat.card V = 2 ^ (3 + 2) := by
    refine ⟨U.map e.symm.toMonoidHom, ?_, ?_⟩
    · have := hUel
      have := (IsElementaryAbelian.map (p := 2) (A := U) e.symm.toMonoidHom)
      exact this
    · rw [Subgroup.card_map_of_injective e.symm.injective, hUcard]
  have hnab : ∃ a b : T, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    let _ : CommGroup T := { (inferInstance : Group T) with mul_comm := hcomm }
    have hprime := IsSimpleGroup.prime_card (α := T)
    obtain ⟨V, -, hV⟩ := hU'
    have hdvd : 2 ^ (3 + 2) ∣ Nat.card T := hV ▸ Subgroup.card_subgroup_dvd_card V
    have h2 := (Nat.Prime.eq_one_or_self_of_dvd hprime 2 (dvd_trans (by norm_num) hdvd))
    have h32 := (Nat.Prime.eq_one_or_self_of_dvd hprime (2 ^ (3 + 2)) hdvd)
    omega
  obtain ⟨Y, _, _, hYp, φ, hφ, hker, hY3⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.high_two_rank_simple_section_small_rank_central_cover
      3 he hS hnab hU' H π hπ
  have hP := LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 K
  set φ' : Y →* Matrix.ProjectiveSpecialLinearGroup (Fin 5) K :=
    (hP.symm.toMonoidHom.comp (e.toMonoidHom.comp φ)) with hφ'
  have hφ'surj : Function.Surjective φ' := fun x => by
    obtain ⟨y, hy⟩ := hφ (e.symm (hP x))
    exact ⟨y, by simp [hφ', hy]⟩
  have hker' : φ'.ker ≤ Subgroup.center Y := by
    intro y hy
    apply hker
    have : φ' y = 1 := hy
    simp only [hφ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at this
    simpa using this
  have : Fintype K := Fintype.ofFinite K
  have hcharK : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [← Nat.card_eq_fintype_card, hKcard])
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hKcard' : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hKcard]
  have h3q : 3 ∣ Fintype.card K - 1 := by
    obtain ⟨k, rfl⟩ := hfe
    rw [hKcard', ← two_mul, pow_mul]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 k
    simpa using this
  obtain ⟨R, -, -, V, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.even_linear_split_torus_central_cover_two_local_normalizer_rank
      hf (by norm_num : 3 ≤ 5) hring hKcard' Nat.prime_three (by norm_num) h3q φ' hφ'surj hker'
  have h35 : ¬ (3 ∣ 5) := by decide
  simp only [h35, ite_false] at hrank
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 Y := by simpa using hrank
  have hlr := CFSG.RankThree.OddKernel.localRank_le_evenRank (G := Y) Nat.prime_three (by norm_num)
  rw [← CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank] at hlr
  omega


theorem even_of_five_dvd_two_pow_sub_one {f : ℕ} (h : 5 ∣ 2 ^ f - 1) : Even f := by
  have h1 : 2 ^ f % 5 = 1 := by
    have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  have key : 2 ^ f % 5 = 2 ^ (f % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod f 4, pow_add, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  have hlt : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hr : f % 4 = 0 := by
    interval_cases hr : f % 4 <;> simp_all
  exact ⟨f / 2, by omega⟩

theorem not_five_dvd_of_component {G : Type} [Group G] [Finite G]
    (hmain : ∀ {f : ℕ} {T : Type} [Group T], 1 ≤ f → Even f → StatedClassicalModel T .PSL 5 2 f →
      ∀ (H : Subgroup G) (π : H →* T), Function.Surjective π → 4 ≤ evenRank G)
    (he : evenRank G ≤ 3) (N : Subgroup G) [N.Normal] (L : Subgroup (G ⧸ N)) {f : ℕ} (hf : 1 ≤ f)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 5 2 f) : ¬ 5 ∣ 2 ^ f - 1 := by
  intro h5
  have hfe := even_of_five_dvd_two_pow_sub_one h5
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let π0 : L.comap q →* L := (q.comp (L.comap q).subtype).codRestrict L fun x => x.2
  let π : L.comap q →* L ⧸ Subgroup.center L := (QuotientGroup.mk' (Subgroup.center L)).comp π0
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (l : G ⧸ N)
    have hmem : g ∈ L.comap q := by
      show q g ∈ L
      rw [show q g = (l : G ⧸ N) from hg]
      exact l.2
    refine ⟨⟨g, hmem⟩, ?_⟩
    have h1 : π0 ⟨g, hmem⟩ = l := Subtype.ext hg
    show QuotientGroup.mk' (Subgroup.center L) (π0 ⟨g, hmem⟩) = QuotientGroup.mk l
    rw [h1]
    rfl
  have := hmain hf hfe hmod (L.comap q) π hπ
  omega

theorem even_square_field_linear_five_sections_force_two_local_rank_four {G : Type} [Group G]
    [Finite G] :
    (∀ {f : ℕ} {T : Type} [Group T], 1 ≤ f → Even f → StatedClassicalModel T .PSL 5 2 f →
      ∀ (H : Subgroup G) (π : H →* T), Function.Surjective π → 4 ≤ evenRank G) ∧
    (evenRank G ≤ 3 → ∀ (N : Subgroup G) [N.Normal] (L : Subgroup (G ⧸ N)) {f : ℕ}, 1 ≤ f →
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 5 2 f → ¬ 5 ∣ 2 ^ f - 1) := by
  have hmain : ∀ {f : ℕ} {T : Type} [Group T], 1 ≤ f → Even f →
      StatedClassicalModel T .PSL 5 2 f → ∀ (H : Subgroup G) (π : H →* T),
        Function.Surjective π → 4 ≤ evenRank G :=
    fun hf hfe hT H π hπ => even_square_field_linear_five_rank_ge_four hf hfe hT H π hπ
  exact ⟨hmain, fun he N _ L _ hf hmod => not_five_dvd_of_component hmain he N L hf hmod⟩

end CFSG.RankThree.PartOne
