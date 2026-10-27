module

public import CFSG.Open.UniquenessExclusionRankFourMilestoneDefs
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem mem_uniqueFourConj_iff {H : Subgroup G} {g x : G} :
    x ∈ uniqueFourConj g H ↔ g * x * g⁻¹ ∈ H := by
  unfold uniqueFourConj
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem uniqueFourConj_eq_self_iff {H : Subgroup G} {g : G} :
    uniqueFourConj g H = H ↔ g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h x
    rw [← mem_uniqueFourConj_iff, h]
  · intro h
    ext x
    rw [mem_uniqueFourConj_iff]
    exact (h x).symm

theorem normalizer_eq_of_isMaxTwoLocal {M : Subgroup G} (hM : IsMaxTwoLocalSubgroup M) :
    normalizer (M : Set G) = M := by
  obtain ⟨⟨P, hP1, hP2, hPM⟩, hmax⟩ := hM
  set Q : Subgroup G := pCoreOf 2 M with hQdef
  have hQM : Q ≤ M := CFSG.openPCoreOf_le 2 M
  have hQsub : Q.subgroupOf M = CFSG.pCore 2 M := CFSG.openPCoreOf_subgroupOf 2 M
  have hQnormal : (Q.subgroupOf M).Normal := by
    rw [hQsub]
    exact CFSG.pCore_normal
  have hQp : IsPGroup 2 Q := by
    rw [hQdef, pCoreOf]
    exact CFSG.pCore_isPGroup.map M.subtype
  have hKQ : ∀ K : Subgroup G, K ≤ M → (K.subgroupOf M).Normal → IsPGroup 2 K → K ≤ Q := by
    intro K hKM hKn hKp x hx
    have hxK : (⟨x, hKM hx⟩ : M) ∈ CFSG.pCore 2 M := by
      have h1 : K.subgroupOf M ≤ CFSG.pCore 2 M :=
        le_sSup (show K.subgroupOf M ∈ {K : Subgroup M | K.Normal ∧ IsPGroup 2 K} from
          ⟨hKn, hKp.comap_subtype⟩)
      exact h1 hx
    exact (CFSG.mem_openPCoreOf_iff ⟨x, hKM hx⟩).2 hxK
  have hPM' : P ≤ M := hPM ▸ Subgroup.le_normalizer
  have hPn : (P.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM').2 (le_of_eq hPM)
  have hPQ : P ≤ Q := hKQ P hPM' hPn hP2
  have hQ1 : Q ≠ ⊥ := fun h => hP1 (le_bot_iff.1 (h ▸ hPQ))
  have hMQ : M ≤ normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).1 hQnormal
  have hNQ : normalizer (Q : Set G) = M := hmax _ ⟨Q, hQ1, hQp, rfl⟩ hMQ
  have hconj : ∀ h : G, h ∈ normalizer (M : Set G) → ∀ x ∈ Q, h * x * h⁻¹ ∈ Q := by
    intro h hh x hx
    have hhi : h⁻¹ ∈ normalizer (M : Set G) := inv_mem hh
    have hKM : Q.map (MulAut.conj h).toMonoidHom ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hh y).1 (hQM hy)
    have hKp : IsPGroup 2 (Q.map (MulAut.conj h).toMonoidHom) := hQp.map _
    have hKn : ((Q.map (MulAut.conj h).toMonoidHom).subgroupOf M).Normal := by
      refine ⟨fun k hk m => ?_⟩
      obtain ⟨y, hy, hyk⟩ : (k : G) ∈ Q.map (MulAut.conj h).toMonoidHom := hk
      have hzM : h⁻¹ * (m : G) * h ∈ M := by
        simpa using (mem_normalizer_iff.1 hhi m).1 m.2
      have hyQ : (⟨y, hQM hy⟩ : M) ∈ Q.subgroupOf M := hy
      have h1 := hQnormal.conj_mem _ hyQ ⟨h⁻¹ * (m : G) * h, hzM⟩
      have hk' : (k : G) = h * y * h⁻¹ := by
        simpa [MulAut.conj_apply] using hyk.symm
      refine Subgroup.mem_map.2 ⟨h⁻¹ * (m : G) * h * y * (h⁻¹ * (m : G) * h)⁻¹, h1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      change h * (h⁻¹ * (m : G) * h * y * (h⁻¹ * (m : G) * h)⁻¹) * h⁻¹ =
        (m : G) * (k : G) * (m : G)⁻¹
      rw [hk']
      group
    exact hKQ _ hKM hKn hKp ⟨x, hx, rfl⟩
  apply le_antisymm _ Subgroup.le_normalizer
  intro g hg
  have hgQ : g ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hconj g hg x hx
    · intro hx
      have := hconj g⁻¹ (inv_mem hg) _ hx
      simpa [mul_assoc] using this
  rwa [hNQ] at hgQ

@[expose] def InU (M X : Subgroup G) : Prop :=
  X ≤ M ∧ ∀ g : G, X ≤ uniqueFourConj g M → uniqueFourConj g M = M

theorem inU_iff_not_le {M : Subgroup G} (hM : normalizer (M : Set G) = M) {X : Subgroup G} :
    InU M X ↔ X ≤ M ∧ ∀ g : G, g ∉ M → ¬ X ≤ uniqueFourConj g M := by
  unfold InU
  refine and_congr_right fun _ => ?_
  constructor
  · intro h g hg hle
    apply hg
    have := uniqueFourConj_eq_self_iff.1 (h g hle)
    rwa [hM] at this
  · intro h g hle
    by_contra hne
    have hg : g ∉ M := by
      intro hgM
      apply hne
      apply uniqueFourConj_eq_self_iff.2
      rwa [hM]
    exact h g hg hle

theorem inU_iff_fixed {M : Subgroup G} (hM : normalizer (M : Set G) = M) {X : Subgroup G} :
    InU M X ↔ X ≤ M ∧ ∀ g : G, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M := by
  rw [inU_iff_not_le hM]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h g hg
    by_contra hgM
    refine h g⁻¹ (fun h' => hgM (by simpa using h')) fun x hx => ?_
    rw [mem_uniqueFourConj_iff]
    simpa using hg x hx
  · intro h g hg hle
    apply hg
    have := h g⁻¹ fun x hx => by
      have := (mem_uniqueFourConj_iff.1 (hle hx))
      simpa using this
    simpa using this

theorem InU.normalizer_le {M X : Subgroup G} (hM : normalizer (M : Set G) = M) (h : InU M X) :
    normalizer (X : Set G) ≤ M := by
  intro n hn
  by_contra hnM
  have hle : X ≤ uniqueFourConj n M := by
    intro x hx
    rw [mem_uniqueFourConj_iff]
    exact h.1 ((mem_normalizer_iff.1 hn x).1 hx)
  exact ((inU_iff_not_le hM).1 h).2 n hnM hle

theorem inU_of_normalizer_le_of_fusion {M X : Subgroup G} (hM : normalizer (M : Set G) = M)
    (hXM : X ≤ M) (hN : normalizer (X : Set G) ≤ M)
    (hfus : ∀ g : G, uniqueFourConj g X ≤ M → ∃ m ∈ M, uniqueFourConj g X = uniqueFourConj m X) :
    InU M X := by
  rw [inU_iff_not_le hM]
  refine ⟨hXM, fun g hgM hle => hgM ?_⟩
  have hle' : uniqueFourConj g⁻¹ X ≤ M := by
    intro x hx
    rw [mem_uniqueFourConj_iff] at hx
    have := hle hx
    rw [mem_uniqueFourConj_iff] at this
    simpa [mul_assoc] using this
  obtain ⟨m, hmM, hm⟩ := hfus g⁻¹ hle'
  have hmg : m * g ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have h1 : g * y * g⁻¹ ∈ uniqueFourConj g⁻¹ X ↔ g * y * g⁻¹ ∈ uniqueFourConj m X := by
      rw [hm]
    rw [mem_uniqueFourConj_iff, mem_uniqueFourConj_iff] at h1
    have e1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    have e2 : m * (g * y * g⁻¹) * m⁻¹ = m * g * y * (m * g)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1.symm.symm
  have hmgM := hN hmg
  simpa using M.mul_mem (M.inv_mem hmM) hmgM

theorem inU_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {M T : Subgroup G}
    (hM : normalizer (M : Set G) = M) (hTM : CFSG.ABGLocalTools.IsSylowOf p T M)
    (hN : normalizer (T : Set G) ≤ M) : InU M T := by
  refine inU_of_normalizer_le_of_fusion hM hTM.le hN fun g hg => ?_
  have hcard : Nat.card (uniqueFourConj g T) = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hTg : CFSG.ABGLocalTools.IsSylowOf p (uniqueFourConj g T) M :=
    CFSG.ABGLocalTools.isSylowOf_of_card hg (by rw [hcard, hTM.card_eq])
  obtain ⟨k, hkM, hk⟩ := hTM.exists_mem_conj hTg
  refine ⟨k⁻¹, inv_mem hkM, ?_⟩
  ext x
  rw [mem_uniqueFourConj_iff (g := k⁻¹)]
  simpa using hk x

theorem InU.of_subnormal {M X Y : Subgroup G} (hM : normalizer (M : Set G) = M)
    (hXY : IsSubnormal X Y) (hX : InU M X) : InU M Y := by
  revert hX
  induction hXY with
  | refl H => exact id
  | step hHM' hnorm _ ih =>
    intro hH
    refine ih ⟨?_, fun g hg => hH.2 g (hHM'.trans hg)⟩
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM').1 hnorm).trans
      (hH.normalizer_le hM)

end CFSG.LocalAnalysis.UniquenessCase.UC6
