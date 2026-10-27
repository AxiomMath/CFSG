module

import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.WeakClosure81.FiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.FiveKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem kerQuotMk_surjective (M H : Subgroup G) : Function.Surjective (kerQuotMk M H) := by
  unfold kerQuotMk
  exact QuotientGroup.mk'_surjective _

theorem ker_kerQuotMk (M H : Subgroup G) :
    (kerQuotMk M H).ker = (kerMOf M H).subgroupOf H := by
  unfold kerQuotMk
  rw [QuotientGroup.ker_mk', subgroupOf_kerMOf]

theorem kerQuotImg_mono {M H X Y : Subgroup G} (h : X ≤ Y) :
    kerQuotImg M H X ≤ kerQuotImg M H Y := by
  unfold kerQuotImg
  exact Subgroup.map_mono (Subgroup.comap_mono h)

theorem kerQuotImg_eq_bot_iff {M H A : Subgroup G} (hAH : A ≤ H) :
    kerQuotImg M H A = ⊥ ↔ A ≤ kerMOf M H := by
  unfold kerQuotImg
  rw [Subgroup.map_eq_bot_iff, ker_kerQuotMk]
  constructor
  · intro h x hx
    exact (Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_subgroupOf.2 hx) : (⟨x, hAH hx⟩ : H) ∈
      (kerMOf M H).subgroupOf H))
  · intro h y hy
    exact Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hy))

theorem isElemAbelian_kerQuotImg {M H A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (kerQuotImg M H A) :=
  (hA.subgroupOf H).map (kerQuotMk M H)

theorem relIndex_kerQuotImg (M H : Subgroup G) :
    (kerQuotImg M H M).relIndex ⊤ = M.relIndex H := by
  rw [Subgroup.relIndex_top_right]
  unfold kerQuotImg
  have hker : (kerQuotMk M H).ker ≤ M.subgroupOf H := by
    unfold kerQuotMk
    rw [QuotientGroup.ker_mk']
    exact Subgroup.normalCore_le _
  exact Subgroup.index_map_eq (M.subgroupOf H) (kerQuotMk_surjective M H) hker

theorem b5_FiveNineQuot_comap_kerQuotImg_self (M H : Subgroup G) :
    (kerQuotImg M H M).comap (kerQuotMk M H) = M.subgroupOf H := by
  unfold kerQuotImg
  apply Subgroup.comap_map_eq_self
  unfold kerQuotMk
  rw [QuotientGroup.ker_mk']
  exact Subgroup.normalCore_le _

theorem kerMOf_kerQuotImg (M H : Subgroup G) :
    kerMOf (kerQuotImg M H M) (⊤ : Subgroup (KerQuot M H)) = ⊥ := by
  set Z := kerMOf (kerQuotImg M H M) (⊤ : Subgroup (KerQuot M H)) with hZ
  haveI hZn : Z.Normal := ⟨fun n hn g => conj_mem_kerMOf (Subgroup.mem_top g) hn⟩
  have hZM : Z ≤ kerQuotImg M H M := kerMOf_le_left _ _
  have hD : Z.comap (kerQuotMk M H) ≤ M.subgroupOf H := by
    exact (Subgroup.comap_mono hZM).trans (b5_FiveNineQuot_comap_kerQuotImg_self M H).le
  haveI : (Z.comap (kerQuotMk M H)).Normal := Subgroup.normal_comap _
  have hDcore : Z.comap (kerQuotMk M H) ≤ (M.subgroupOf H).normalCore :=
    Subgroup.normal_le_normalCore.2 hD
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, rfl⟩ := kerQuotMk_surjective M H z
  have hy : y ∈ Z.comap (kerQuotMk M H) := hz
  have hy1 : kerQuotMk M H y = 1 := by
    unfold kerQuotMk
    exact (QuotientGroup.eq_one_iff _).2 (hDcore hy)
  exact Subgroup.mem_bot.2 hy1

theorem card_kerQuotImg {M H A : Subgroup G} (hAH : A ≤ H) :
    Nat.card ↥(kerQuotImg M H A) = (A ⊓ kerMOf M H).relIndex A := by
  let φ : ↥A →* KerQuot M H := (kerQuotMk M H).comp (Subgroup.inclusion hAH)
  have hrange : φ.range = kerQuotImg M H A := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a, hAH a.2⟩, a.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : φ.ker = (A ⊓ kerMOf M H).subgroupOf A := by
    ext a
    have h1 : a ∈ φ.ker ↔ (Subgroup.inclusion hAH a) ∈ (kerQuotMk M H).ker := by
      simp [φ, MonoidHom.mem_ker]
    rw [h1, ker_kerQuotMk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    simp [Subgroup.inclusion, a.2]
  rw [← hrange]
  have e := QuotientGroup.quotientKerEquivRange φ
  rw [← Nat.card_congr e.toEquiv, ← Subgroup.index_eq_card, hker]
  rfl

theorem sec5Hyp_kerQuot {H M A : Subgroup G} (h : Sec5Hyp H M A) :
    Sec5Hyp (⊤ : Subgroup (KerQuot M H)) (kerQuotImg M H M) (kerQuotImg M H A) where
  isElemAbelian := isElemAbelian_kerQuotImg h.isElemAbelian
  le_group := le_top
  le_M := kerQuotImg_mono h.le_M
  not_le := by
    intro htop
    apply h.not_le
    intro x hxH
    have hmem : kerQuotMk M H ⟨x, hxH⟩ ∈ kerQuotImg M H M := htop (Subgroup.mem_top _)
    have : (⟨x, hxH⟩ : ↥H) ∈ (kerQuotImg M H M).comap (kerQuotMk M H) := hmem
    rw [b5_FiveNineQuot_comap_kerQuotImg_self] at this
    exact this
  odd_relIndex := by
    rw [relIndex_kerQuotImg]
    exact h.odd_relIndex

end CFSG.LocalAnalysis.WeakClosure81
