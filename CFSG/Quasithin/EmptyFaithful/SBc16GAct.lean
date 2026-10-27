module

public import CFSG.Quasithin.EmptyFaithful.S14117Star
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc16

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def actHom (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (OTwoQuot K) :=
  haveI : (CFSG.Open.pCore 2 ↥K).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
  SteinbergBS.conjQuotientHom K (CFSG.Open.pCore 2 ↥K)

theorem mem_pCore_iff_coe (K : Subgroup G) (x : ↥K) :
    x ∈ CFSG.Open.pCore 2 ↥K ↔ (x : G) ∈ pCoreOf 2 K :=
  (Subgroup.mem_map_iff_mem K.subtype_injective).symm

theorem actHom_mk (K : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {k : G}
    (hk : k ∈ K) :
    actHom K ⟨g, hg⟩ (QuotientGroup.mk ⟨k, hk⟩) =
      QuotientGroup.mk ⟨g * k * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg k).mp hk⟩ := by
  unfold actHom
  change (QuotientGroup.mk (Subgroup.normalizerMonoidHom K ⟨g, hg⟩ ⟨k, hk⟩ : ↥K) :
    OTwoQuot K) = _
  exact congrArg QuotientGroup.mk
    (Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨g, hg⟩ ⟨k, hk⟩))

theorem actHom_eq_one_iff (K : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    actHom K ⟨g, hg⟩ = 1 ↔ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  constructor
  · intro h k hk
    have h1 := DFunLike.congr_fun h (QuotientGroup.mk ⟨k, hk⟩ : OTwoQuot K)
    rw [actHom_mk, MulAut.one_apply, QuotientGroup.eq, mem_pCore_iff_coe] at h1
    have h2 : (g * k * g⁻¹)⁻¹ * k ∈ pCoreOf 2 K := h1
    have h3 := (Subgroup.mem_normalizer_iff.mp (hKO hk) _).mp ((pCoreOf 2 K).inv_mem h2)
    have e : g * k * g⁻¹ * k⁻¹ = k * ((g * k * g⁻¹)⁻¹ * k)⁻¹ * k⁻¹ := by group
    rw [e]
    exact h3
  · intro h
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨k, hk⟩ := x
    rw [actHom_mk, MulAut.one_apply, QuotientGroup.eq, mem_pCore_iff_coe]
    have h3 := (Subgroup.mem_normalizer_iff.mp (hKO (K.inv_mem hk)) _).mp
      ((pCoreOf 2 K).inv_mem (h k hk))
    have e : (g * k * g⁻¹)⁻¹ * k = k⁻¹ * (g * k * g⁻¹ * k⁻¹)⁻¹ * k⁻¹⁻¹ := by group
    show (g * k * g⁻¹)⁻¹ * k ∈ pCoreOf 2 K
    rw [e]
    exact h3

theorem map_actHom_imageOTwoQuot (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {X : Subgroup G} (hX : X ≤ K) :
    (imageOTwoQuot K X).map (actHom K ⟨g, hg⟩).toMonoidHom = imageOTwoQuot K (conjSub g X) := by
  ext v
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hxK, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    refine mem_imageOTwoQuot_iff.mpr
      ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hxK, ?_, (actHom_mk K hg hxK).symm⟩
    rw [mem_conjSub]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]
    exact hxX
  · intro hv
    obtain ⟨y, hyK, hyX, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    have hx : g⁻¹ * y * g ∈ X := mem_conjSub.mp hyX
    refine ⟨QuotientGroup.mk ⟨g⁻¹ * y * g, hX hx⟩,
      mem_imageOTwoQuot_iff.mpr ⟨g⁻¹ * y * g, hX hx, hx, rfl⟩, ?_⟩
    refine (actHom_mk K hg (hX hx)).trans (congrArg QuotientGroup.mk (Subtype.ext ?_))
    show g * (g⁻¹ * y * g) * g⁻¹ = y
    group

end Action

section Counting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_card_range_mul_card_ker {X N : Type} [Group X] [Group N] (ψ : X →* N) :
    Nat.card X = Nat.card ψ.range * Nat.card ψ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]

theorem not_sixteen_dvd_card_range {X T Q : Subgroup G} {N : Type} [Group N] (ψ : ↥X →* N)
    (hT : IsSylowTwoOf T X) (hQX : Q ≤ X) (hker : ∀ q : ↥X, (q : G) ∈ Q → ψ q = 1)
    (hcard : Nat.card T = 8 * Nat.card Q) : ¬ 16 ∣ Nat.card ψ.range := by
  intro h16
  have h1 := card_eq_card_range_mul_card_ker ψ
  have hle : Q.subgroupOf X ≤ ψ.ker := fun q hq =>
    MonoidHom.mem_ker.mpr (hker q (Subgroup.mem_subgroupOf.mp hq))
  have hQ : Nat.card Q ∣ Nat.card ψ.ker := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  have h2 := Subgroup.index_mul_card (T.subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv, hcard] at h2
  obtain ⟨a, ha⟩ := h16
  obtain ⟨c, hc⟩ := hQ
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h3 : (T.subgroupOf X).index * (8 * Nat.card Q) = (2 * a * c) * (8 * Nat.card Q) := by
    rw [h2, h1, ha, hc]
    ring
  have h4 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < 8 * Nat.card Q) h3
  exact hT.2.2 ⟨a * c, by rw [h4]; ring⟩

end Counting

end SBc16

end CFSG.Quasithin
