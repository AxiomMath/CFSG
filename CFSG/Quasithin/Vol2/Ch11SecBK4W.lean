module

public import CFSG.Quasithin.Vol2.Ch11SecBK4V
public import CFSG.Quasithin.Vol2.Ch11SecBK4C
public import CFSG.Quasithin.Vol2.Ch11SecBK4U

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open CFSG.Open (IsElemAbelian)
open scoped IsMulCommutative Pointwise

namespace BK4

theorem hstep_map {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (Φ Ψ : M →ₗ[K] M)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ x, Φ (Ψ x) = x) {m : ℕ} {F : ℕ → Submodule K M}
    (hstep : ∀ i < m, ∃ e ∈ F (i + 1), e ∉ F i ∧ ∀ y ∈ F (i + 1), ∃ c : K, y - c • e ∈ F i) :
    ∀ i < m, ∃ e ∈ (F (i + 1)).map Φ, e ∉ (F i).map Φ ∧
      ∀ y ∈ (F (i + 1)).map Φ, ∃ c : K, y - c • e ∈ (F i).map Φ := by
  have hmem : ∀ (S : Submodule K M) (y : M), y ∈ S.map Φ ↔ Ψ y ∈ S := by
    intro S y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [hΨΦ]
    · intro h
      exact ⟨Ψ y, h, hΦΨ y⟩
  intro i hi
  obtain ⟨e, he, he', hdec⟩ := hstep i hi
  refine ⟨Φ e, (hmem _ _).mpr (by rwa [hΨΦ]), fun h => he' (by rwa [hmem, hΨΦ] at h),
    fun y hy => ?_⟩
  obtain ⟨c, hc⟩ := hdec _ ((hmem _ _).mp hy)
  refine ⟨c, (hmem _ _).mpr ?_⟩
  rwa [map_sub, map_smul, hΨΦ]

variable {G : Type} [Group G] {L V : Subgroup G}

theorem autOn_mono' {Y₁ Y₂ : Subgroup G} (h : Y₁ ≤ Y₂) : autOn Y₁ V ≤ autOn Y₂ V :=
  Subgroup.map_mono fun _ hx => h hx

theorem mem_normalizer_inf {T : Subgroup G} {t : G} (ht : t ∈ T)
    (htL : t ∈ Subgroup.normalizer (L : Set G)) :
    t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht), (Subgroup.mem_normalizer_iff.mp htL x).mp h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htL x).mpr h2⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht
    rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this

theorem cartanPower_of_flag [Finite G] [IsMulCommutative ↥V] {Dm : FFModel} {K M : Type}
    [Field K] [Finite K] [CharP K 2] [AddCommGroup M] [Module K M] [Finite M]
    {LM : KGNat.LinModel Dm K M} {π : Dm.Gam →* ↥(autOn L V)} {f : ↥V → M}
    (hf : KGNat.IsCoord LM (autOn L V) ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hcomm : ∀ T : M →+ M, (∀ (γ : Dm.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x) {x₀ : M} (hx₀ : x₀ ≠ 0)
    (hrig : ∀ x (hxV : x ∈ Subgroup.normalizer (V : Set G)),
      x ∈ Subgroup.normalizer (L : Set G) → (∀ w, f (SecA.conjV V x hxV w) = f w) →
        x ∈ Subgroup.centralizer (V : Set G))
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (F : ℕ → Submodule K M)
    (hF0 : F 0 = ⊥) (hFtop : ∀ i, m ≤ i → F i = ⊤)
    (hstep : ∀ i < m, ∃ e ∈ F (i + 1), e ∉ F i ∧ ∀ y ∈ F (i + 1), ∃ c : K, y - c • e ∈ F i)
    (hflag : ∀ i, 0 < i → i < m → SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (Nat.card K) i (hf.pre (F i).toAddSubgroup))
    (huniq : ∀ i, 0 < i → i < m → ∀ U, SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (Nat.card K) i U →
        U = hf.pre (F i).toAddSubgroup)
    (hover : ∀ A : Subgroup (MulAut ↥V), A ≤ autOn L V → autOn (T ⊓ L) V ≤ A →
      Group.IsSolvable A → ∀ a ∈ A, ∀ i, ∀ w, f w ∈ F i → f (a w) ∈ F i)
    {D : Subgroup G} (hDL : D ≤ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : IsElemAbelian p D) (hDT : (D : Set G) * T = T * D) {t : G} (ht : t ∈ T)
    (htD : t ∈ Subgroup.normalizer (D : Set G)) :
    ∃ r : ℕ, ∀ d ∈ D, t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have htV := hTV ht
  have htL := hTL ht
  have htT := mem_normalizer_inf ht htL
  have hDp : IsPGroup p D := fun g => ⟨1, Subtype.ext (by simpa using hD.2 g g.2)⟩
  have hYs : Group.IsSolvable ↥((D ⊔ T) ⊓ L) := by
    have := isSolvable_sup hp hp2 hDp hT2 hDT
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : (D ⊔ T) ⊓ L ≤ D ⊔ T))
  have hA := isSolvable_autOn V hYs
  have hAH : autOn ((D ⊔ T) ⊓ L) V ≤ autOn L V := autOn_mono' inf_le_right
  have hPA : autOn (T ⊓ L) V ≤ autOn ((D ⊔ T) ⊓ L) V :=
    autOn_mono' (inf_le_inf_right L le_sup_right)
  have hDF : ∀ d (hd : d ∈ D), ∀ i, ∀ w : ↥V, f w ∈ F i →
      f (SecA.conjV V d (hLV (hDL hd)) w) ∈ F i := fun d hd i w hw =>
    hover _ hAH hPA hA _ (SecA.conjV_mem_autOn (L := (D ⊔ T) ⊓ L)
      (Subgroup.mem_inf.mpr ⟨le_sup_left (b := T) hd, hDL hd⟩) _) i w hw
  obtain ⟨T', σ, hσ, hT'⟩ := exists_semilinear_conjV hf hcomm hx₀ htV htL
  have hTF : ∀ i, ∀ y ∈ F i, T' y ∈ F i := by
    intro i y hy
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hF0, Submodule.mem_bot] at hy ⊢
      rw [hy, map_zero]
    by_cases him : m ≤ i
    · rw [hFtop i him]
      exact Submodule.mem_top
    exact mapsTo_of_isFlagW hf htV htL htT hT' (hflag i hi0 (by omega))
      (huniq i hi0 (by omega)) y hy
  have := hD.1
  exact exists_pow_of_flag hf hLV hDL hp hp2 hD.2 htV htL htD F hF0 (hFtop m le_rfl) hstep hDF hσ
    hT' hTF hrig

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
