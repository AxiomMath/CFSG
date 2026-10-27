module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem eq_of_normal_of_ne_Q {Y Q K : Subgroup G} {q : ℕ} (h4 : 4 ≤ q)
    (hq2 : ∃ s : ℕ, q = 2 ^ s) (h : QuotSat Y Q (IsSLModel 2 q)) (hQK : Q ≤ K) (hKY : K ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hne : ¬ K ≤ Q) : K = Y := by
  obtain ⟨hn, hmod⟩ := h
  haveI := hn
  obtain ⟨-, hsimple⟩ := isSLModel_two_data h4 hq2 hmod
  haveI := hsimple
  let K' : Subgroup ↥Y := K.subgroupOf Y
  haveI hK'n : K'.Normal := ⟨fun k hk y => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hnorm y y.2 k hk⟩
  haveI hmapn : (K'.map (QuotientGroup.mk' (Q.subgroupOf Y))).Normal :=
    Subgroup.Normal.map hK'n _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (K'.map (QuotientGroup.mk' (Q.subgroupOf Y))) with hbot | htop
  · exfalso
    apply hne
    intro k hk
    have hkY : k ∈ Y := hKY hk
    have hmem : (QuotientGroup.mk' (Q.subgroupOf Y)) ⟨k, hkY⟩ ∈
        K'.map (QuotientGroup.mk' (Q.subgroupOf Y)) :=
      Subgroup.mem_map.mpr ⟨⟨k, hkY⟩, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · refine le_antisymm hKY (fun y hy => ?_)
    have hmem : (QuotientGroup.mk' (Q.subgroupOf Y)) ⟨y, hy⟩ ∈
        K'.map (QuotientGroup.mk' (Q.subgroupOf Y)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkmk⟩ := Subgroup.mem_map.mp hmem
    have hq : k⁻¹ * ⟨y, hy⟩ ∈ Q.subgroupOf Y := QuotientGroup.eq.mp hkmk
    have e : (y : G) = (k : G) * ((k : G)⁻¹ * y) := by group
    rw [e]
    exact K.mul_mem hk (hQK (Subgroup.mem_subgroupOf.mp hq))

theorem one_part_a (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {e : G}
    (heL : e ∈ LB M Q B) (heX : e ∈ X) : (LB M Q B ⊓ X) ⊔ Y ≤ Rt M (LB M Q B) e := by
  classical
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (hc.Rt_le_M t)
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e', -, he', -⟩ := hc.hyp.cp
    exact ⟨e', he'⟩
  set L := LB M Q B with hL
  refine sup_le (le_trans inf_le_left (le_Rt _ heL)) ?_
  let N₀ : Subgroup G := ⨆ (y : G) (_ : y ∈ Y), conjSubgroup y (L ⊓ Y)
  have hconj : ∀ y ∈ Y, conjSubgroup y L ≤ Rt M L e := by
    intro y hy
    have heconj : e ∈ conjSubgroup y L := by
      rw [mem_conjSubgroup]
      have e1 : y⁻¹ * e * y = e * ⁅e⁻¹, y⁻¹⁆ := by simp only [commutatorElement_def]; group
      rw [e1]
      exact L.mul_mem heL (sec39_Q_le_LB (hcomm e⁻¹ (X.inv_mem heX) y⁻¹ (Y.inv_mem hy)))
    exact le_iSup₂_of_le y (hYM hy) (le_iSup_of_le heconj le_rfl)
  have hN₀R : N₀ ≤ Rt M L e := iSup_le fun y => iSup_le fun hy =>
    (Subgroup.map_mono inf_le_left).trans (hconj y hy)
  have hN₀Y : N₀ ≤ Y := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    intro z hz
    rw [mem_conjSubgroup] at hz
    have hz' := (Subgroup.mem_inf.mp hz).2
    have e2 : z = y * (y⁻¹ * z * y) * y⁻¹ := by group
    rw [e2]
    exact Y.mul_mem (Y.mul_mem hy hz') (Y.inv_mem hy)
  have hLYN₀ : L ⊓ Y ≤ N₀ := by
    have h1 : conjSubgroup (1 : G) (L ⊓ Y) ≤ N₀ := le_iSup₂_of_le (1 : G) Y.one_mem le_rfl
    rwa [conjSubgroup_one] at h1
  have hQN₀ : Q ≤ N₀ := (le_inf sec39_Q_le_LB hQY).trans hLYN₀
  have hN₀n : ∀ y ∈ Y, ∀ k ∈ N₀, y * k * y⁻¹ ∈ N₀ := by
    intro y hy k hk
    have hle : N₀ ≤ N₀.comap (MulAut.conj y).toMonoidHom := by
      refine iSup_le fun y' => iSup_le fun hy' => ?_
      intro z hz
      show y * z * y⁻¹ ∈ N₀
      have h1 : conjSubgroup (y * y') (L ⊓ Y) ≤ N₀ :=
        le_iSup₂_of_le (y * y') (Y.mul_mem hy hy') le_rfl
      refine h1 ?_
      rw [mem_conjSubgroup] at hz ⊢
      have e3 : (y * y')⁻¹ * (y * z * y⁻¹) * (y * y') = y'⁻¹ * z * y' := by group
      rw [e3]
      exact hz
    exact hle hk
  have hne : ¬ N₀ ≤ Q := by
    intro hle
    have h1 : L ⊓ Y ≤ Q := hLYN₀.trans hle
    have h2 : Q.relIndex (L ⊓ Y) = 1 := Subgroup.relIndex_eq_one.mpr h1
    rw [h4.2.1] at h2
    omega
  have hNY : N₀ = Y := eq_of_normal_of_ne_Q hq4 hq2 hYsl hQN₀ hN₀Y hN₀n hne
  exact hNY ▸ hN₀R

end HS9

end CFSG.RankThree.GF2n.Stroth80
