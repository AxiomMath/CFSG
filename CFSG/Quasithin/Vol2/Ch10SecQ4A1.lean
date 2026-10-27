module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1 CFSG.QuasithinUnique.C5

variable {G : Type*} [Group G] [Finite G] {K J : Subgroup G}

omit [Finite G] in
theorem commutator_mem_blockQ_of_pCoreOf (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) {q : G} (hq : q ∈ pCoreOf 2 J)
    {k : G} (hk : k ∈ K) : q * k * q⁻¹ * k⁻¹ ∈ blockQ K := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  have hP2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
  have h1 : q * k * q⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQK hq) k).mp hk) (K.inv_mem hk)
  have h2 : q * k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 J := by
    have h3 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 J :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm (hKJ hk)) q⁻¹).mp (Subgroup.inv_mem _ hq)
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hq h3
  have hKP : K ⊓ pCoreOf 2 J ≤ blockQ K := by
    refine le_pCoreOf_of_normalized inf_le_left ?_ (hP2.to_le inf_le_right)
    intro g hg
    exact mem_normalizer_inf (Subgroup.le_normalizer hg) (hPnorm (hKJ hg))
  exact hKP ⟨h1, h2⟩

theorem commutator_mem_blockU_of_pCoreOf (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) {q : G} (hq : q ∈ pCoreOf 2 J)
    {k : G} (hk : k ∈ K) : q * k * q⁻¹ * k⁻¹ ∈ blockU K :=
  commutator_mem_blockU_of_mem_blockQ hK
    (fun _ hl => commutator_mem_blockQ_of_pCoreOf hKJ hQK hq hl) k hk

theorem commute_blockU_of_pCoreOf (hK : IsShort2 K) (hKJ : K ≤ J)
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) {q : G} (hq : q ∈ pCoreOf 2 J) :
    ∀ u ∈ blockU K, u * q = q * u := by
  have hP2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J
  obtain ⟨n, hn⟩ := hP2 ⟨q, hq⟩
  refine commute_blockU_of_mem hK (hQK hq) ⟨n, by simpa using congrArg Subtype.val hn⟩
    (fun _ hl => commutator_mem_blockQ_of_pCoreOf hKJ hQK hq hl)

theorem blockU_inf_pCoreOf (hK : IsShort2 K) (hZ : blockZ K = ⊥) (hKJ : K ≤ J) :
    blockU K ⊓ pCoreOf 2 J = ⊥ ∨ blockU K ≤ pCoreOf 2 J := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  rcases hK.2.2.2.2.2 (blockU K ⊓ pCoreOf 2 J) (by rw [hZ]; exact bot_le) inf_le_left
      (fun g hg => mem_normalizer_inf (le_normalizer_blockU K hg) (hPnorm (hKJ hg))) with h | h
  · left
    rw [h, hZ]
  · right
    rw [← h]
    exact inf_le_right

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
