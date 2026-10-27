module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsSumZeroCompare
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open CFSG.GroupTheory Matrix

theorem le_pRank_centralizer_image_mk {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    {p m : ℕ} (hp : p.Prime) (hN : ¬ p ∣ Nat.card N) (T : Set H)
    (hm : m ≤ CFSG.Open.pRank p (Subgroup.centralizer T)) :
    m ≤ CFSG.Open.pRank p (Subgroup.centralizer (QuotientGroup.mk' N '' T)) := by
  have hp1 : 1 < p := hp.one_lt
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hE_le, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank hp1 (Subgroup.centralizer T)
  have hmap : E.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer (QuotientGroup.mk' N '' T) :=
    (Subgroup.map_mono hE_le).trans (Subgroup.map_centralizer_le_centralizer_image T _)
  have hcard' : Nat.card (E.map (QuotientGroup.mk' N)) =
      p ^ CFSG.Open.pRank p (Subgroup.centralizer T) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Coords.card_map_mk' N hN
      hE.isPGroup, hcard]
  exact hm.trans (CFSG.SectionRank.le_pRank hp1 hmap (hE.map _) hcard')

theorem centralizer_image_eq_map_of_bijective {G G' : Type*} [Group G] [Group G'] (φ : G →* G')
    (hφ : Function.Bijective φ) (T : Set G) :
    Subgroup.centralizer (φ '' T) = (Subgroup.centralizer T).map φ := by
  refine le_antisymm ?_ (Subgroup.map_centralizer_le_centralizer_image T φ)
  intro y hy
  obtain ⟨x, rfl⟩ := hφ.2 y
  rw [Subgroup.mem_map]
  refine ⟨x, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 := (Subgroup.mem_centralizer_iff.mp hy) (φ t) ⟨t, ht, rfl⟩
  exact hφ.1 (by rw [map_mul, map_mul, h1])

theorem le_pRank_centralizer_of_bijective_image {G G' : Type} [Group G] [Finite G] [Group G']
    [Finite G'] (φ : G →* G') (hφ : Function.Bijective φ) (T : Set G) {p m : ℕ} (hp : 1 < p)
    (hm : m ≤ CFSG.Open.pRank p (Subgroup.centralizer (φ '' T))) :
    m ≤ CFSG.Open.pRank p (Subgroup.centralizer T) := by
  let ψ : G ≃* G' := MulEquiv.ofBijective φ hφ
  have hcent := centralizer_image_eq_map_of_bijective φ hφ T
  have hmap : (Subgroup.centralizer (φ '' T)).map ψ.symm.toMonoidHom =
      Subgroup.centralizer T := by
    rw [hcent, Subgroup.map_map]
    have hcomp : ψ.symm.toMonoidHom.comp φ = MonoidHom.id G := by
      ext x
      exact ψ.symm_apply_apply x
    rw [hcomp, Subgroup.map_id]
  have hle := CFSG.SectionRank.pRank_le_map hp ψ.symm.toMonoidHom ψ.symm.injective
    (Subgroup.centralizer (φ '' T))
  rw [hmap] at hle
  exact hm.trans hle

namespace IsSumZeroCoords

theorem le_pRank_centralizer_of_model_bot {H Y : Type} [Group H] [Finite H] [Group Y] [Finite Y]
    {A₀ : Subgroup H} {c₀ : Multiplicative (Fin 4 → ZMod 3) →* H} (h₀ : IsSumZeroCoords A₀ c₀)
    (N : Subgroup H) [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) (hU : UniqueElemSylow 3 3 (H ⧸ N))
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* H ⧸ N)
    {A : Subgroup Y} {c : Multiplicative (Fin 4 → ZMod 3) →* Y} (h : IsSumZeroCoords A c)
    (S : Set (Multiplicative (Fin 4 → ZMod 3))) {p m : ℕ} (hp : p.Prime)
    (hNp : ¬ p ∣ Nat.card N)
    (hm : m ≤ CFSG.Open.pRank p (Subgroup.centralizer (c₀ '' S))) :
    m ≤ CFSG.Open.pRank p (Subgroup.centralizer (c '' S)) := by
  have hN3' : ¬ 3 ∣ Nat.card Z := by rw [hZ, Subgroup.card_bot]; norm_num
  have h1 : m ≤ CFSG.Open.pRank p (Subgroup.centralizer
      ((fun v => QuotientGroup.mk' N (c₀ v)) '' S)) := by
    simpa only [Set.image_image] using
      le_pRank_centralizer_image_mk N hp hNp (c₀ '' S) hm
  have h2 := IsSumZeroCoords.le_pRank_centralizer_image_of_model h₀ N hN3 hU Z hN3' e h S
    hp.one_lt h1
  have hinj : Function.Injective (QuotientGroup.mk' Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  refine le_pRank_centralizer_of_bijective_image
    (e.toMonoidHom.comp (QuotientGroup.mk' Z))
    (e.bijective.comp ⟨hinj, QuotientGroup.mk'_surjective Z⟩) (c '' S) hp.one_lt ?_
  simpa only [Set.image_image, Function.comp_apply, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom] using h2

theorem le_pRank_centralizer_of_stdDiagHomH {K : Type} [Field K] [Finite K] {Y : Type} [Group Y]
    [Finite Y] {H : Subgroup (GL (Fin 4) K)}
    (hscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ H → c ^ 4 = 1)
    {ζ : CubeRoot K} (hD : D₀ ζ ≤ H) {A₀ : Subgroup H}
    (h₀ : IsSumZeroCoords A₀ (stdDiagHomH ζ hD)) (hU : UniqueElemSylow 3 3 (StatedProj H))
    (Z : Subgroup Y) [Z.Normal] (hZ : Z = ⊥) (e : Y ⧸ Z ≃* StatedProj H)
    {A : Subgroup Y} {c : Multiplicative (Fin 4 → ZMod 3) →* Y} (h : IsSumZeroCoords A c)
    (S : Set (Multiplicative (Fin 4 → ZMod 3))) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : m ≤ CFSG.Open.pRank p (Subgroup.centralizer (stdDiagHomH ζ hD '' S))) :
    m ≤ CFSG.Open.pRank p (Subgroup.centralizer (c '' S)) := by
  have hN3 : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 4) K).subgroupOf H) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf H Nat.prime_three (by norm_num) hscal
  have hp4 : ¬ p ∣ 4 := by
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (by
      rwa [show (4 : ℕ) = 2 ^ 2 from by norm_num] at h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hNp : ¬ p ∣ Nat.card ((StatedScalars (Fin 4) K).subgroupOf H) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf H hp hp4 hscal
  exact IsSumZeroCoords.le_pRank_centralizer_of_model_bot h₀
    ((StatedScalars (Fin 4) K).subgroupOf H) hN3 hU Z hZ e h S hp hNp hm

end IsSumZeroCoords

theorem commute_diagonal_of_support {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι K} {d : ι → K} (hM : ∀ a b, M a b ≠ 0 → d a = d b) :
    Matrix.diagonal d * M = M * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M a b = 0
  · rw [h, mul_zero, zero_mul]
  · rw [hM a b h, mul_comm]

theorem le_pRank_centralizer_of_diag_commuting {K : Type} [Field K] [Finite K]
    {H : Subgroup (GL (Fin 4) K)} {p k : ℕ} (hp : 1 < p) {A : Type} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (hA : Nat.card A = p ^ k)
    (φ : A →* H) (hφ : Function.Injective φ) (P : (Fin 4 → K) → Prop)
    (hφd : ∀ (a : A) (d : Fin 4 → K), P d →
      Matrix.diagonal d * ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal d)
    (T : Set H) (hT : ∀ t ∈ T, ∃ d : Fin 4 → K, P d ∧
      ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d) :
    k ≤ CFSG.Open.pRank p (Subgroup.centralizer T) := by
  refine CFSG.SectionRank.le_pRank_of_injective hp hcomm hpow hA φ hφ ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨d, hPd, htd⟩ := hT t ht
  apply Subtype.ext
  apply Units.ext
  simpa only [Subgroup.coe_mul, Units.val_mul, htd] using hφd a d hPd

theorem exists_units_orderOf_eq_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) : ∃ a : Kˣ, orderOf a = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_units] at hpK
  exact exists_prime_orderOf_dvd_card' p hpK

theorem exists_diagTorus_hom {K : Type} [Field K] {H : Subgroup (GL (Fin 4) K)} {a : Kˣ}
    (hH : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers a,
      diagUnit (K := K) ![x, x⁻¹, y, y⁻¹] ∈ H) :
    ∃ φ : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers a) →* H, Function.Injective φ ∧
      ∀ g, ((φ g : GL (Fin 4) K)) =
        diagUnit (K := K) ![(g.1 : Kˣ), (g.1 : Kˣ)⁻¹, (g.2 : Kˣ), (g.2 : Kˣ)⁻¹] := by
  let χ : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers a) →* (Fin 4 → Kˣ) :=
    { toFun := fun g => ![(g.1 : Kˣ), (g.1 : Kˣ)⁻¹, (g.2 : Kˣ), (g.2 : Kˣ)⁻¹]
      map_one' := by
        funext i
        fin_cases i <;> simp
      map_mul' := fun g h => by
        funext i
        fin_cases i <;> simp [Pi.mul_apply] <;> ac_rfl }
  let φ₀ : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers a) →* GL (Fin 4) K :=
    { toFun := fun g => diagUnit (χ g)
      map_one' := by rw [map_one, diagUnit_one]
      map_mul' := fun g h => by rw [map_mul, diagUnit_mul] }
  have hχinj : Function.Injective χ := by
    intro g h hgh
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa [χ] using congrFun hgh 0
    · simpa [χ] using congrFun hgh 2
  have hmem : ∀ g, φ₀ g ∈ H := by
    intro g
    change diagUnit ![(g.1 : Kˣ), (g.1 : Kˣ)⁻¹, (g.2 : Kˣ), (g.2 : Kˣ)⁻¹] ∈ H
    exact hH _ g.1.2 _ g.2.2
  refine ⟨φ₀.codRestrict H hmem, ?_, ?_⟩
  · intro g h hgh
    refine hχinj (card_D₀_diagUnit_injective ?_)
    exact congrArg Subtype.val hgh
  · intro g
    rfl

theorem two_le_pRank_centralizer_of_diagTorus {K : Type} [Field K] [Finite K]
    {H : Subgroup (GL (Fin 4) K)} {p : ℕ} (hp : p.Prime) {a : Kˣ} (ha : orderOf a = p)
    (hH : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers a,
      diagUnit (K := K) ![x, x⁻¹, y, y⁻¹] ∈ H)
    (T : Set H) (hT : ∀ t ∈ T, ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer T) := by
  obtain ⟨φ, hφinj, hφspec⟩ := exists_diagTorus_hom (K := K) hH
  have hcomm : ∀ x y : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers a), x * y = y * x :=
    fun x y => mul_comm x y
  have hpow : ∀ x : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers a), x ^ p = 1 := by
    intro x
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using (orderOf_dvd_iff_pow_eq_one).mp
        (by rw [← ha]; exact orderOf_dvd_of_mem_zpowers x.1.2)
    · simpa using (orderOf_dvd_iff_pow_eq_one).mp
        (by rw [← ha]; exact orderOf_dvd_of_mem_zpowers x.2.2)
  have hA : Nat.card (↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers a)) = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, ha]
    exact (pow_two p).symm
  have hφd : ∀ (x : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers a)) (d : Fin 4 → K),
      True → Matrix.diagonal d * ((φ x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((φ x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal d := by
    intro x d _
    rw [hφspec x]
    show Matrix.diagonal d *
        (Matrix.diagonal fun i => (((![(x.1 : Kˣ), (x.1 : Kˣ)⁻¹, (x.2 : Kˣ),
          (x.2 : Kˣ)⁻¹] : Fin 4 → Kˣ) i : Kˣ) : K)) =
      (Matrix.diagonal fun i => (((![(x.1 : Kˣ), (x.1 : Kˣ)⁻¹, (x.2 : Kˣ),
          (x.2 : Kˣ)⁻¹] : Fin 4 → Kˣ) i : Kˣ) : K)) * Matrix.diagonal d
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hT' : ∀ t ∈ T, ∃ d : Fin 4 → K, True ∧
      ((t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal d :=
    fun t ht => ⟨_, trivial, (hT t ht).diagonal_diag.symm⟩
  exact le_pRank_centralizer_of_diag_commuting hp.one_lt hcomm hpow hA φ hφinj
    (fun _ => True) hφd T hT'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
