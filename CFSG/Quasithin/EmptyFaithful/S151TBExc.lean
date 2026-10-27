module

public import CFSG.Quasithin.EmptyFaithful.S151TBZ
public import CFSG.Quasithin.EmptyFaithful.S151TBCtx
public import CFSG.Quasithin.EmptyFaithful.S151TBMax

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem relIndex_le_blockN (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (hsh : IsShort2 L) (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G)) :
    (mZ1516 Mc Z₁).relIndex L ≤ Nat.card (BlockN L) - 1 := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hB : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := sylow_inf hc
  have hS2 : IsPGroup 2 ↥(s1516 T Z₁) := hc.h18.four.2.1
  obtain ⟨W, hWb, hWfix, -, hWz⟩ :=
    exists_zU hsh.2.1 hperf hS2 hSN hB (omegaOneCenter_le hc)
  have hnot := not_le_centralizer hc hLG
  obtain ⟨l₀, hl₀L, hl₀⟩ : ∃ l ∈ L, l ∉ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G) := by
    by_contra h
    push Not at h
    exact hnot h
  rw [Subgroup.mem_centralizer_iff] at hl₀
  push Not at hl₀
  obtain ⟨z, hz, hl₀z⟩ := hl₀
  obtain ⟨w, hw, hwiff⟩ := hWz z hz
  have hl₀w : ¬ l₀ * w = w * l₀ := fun h => hl₀z ((hwiff l₀ hl₀L).2 h).symm
  have hwU : w ∈ blockU L := hWb hw
  have hwZ : w ∉ blockZ L := by
    intro hZw
    apply hl₀w
    have h := s151v_blockZ_comm hZw hl₀L
    calc l₀ * w = (l₀ * w * l₀⁻¹) * l₀ := by group
      _ = w * l₀ := by rw [h]
  have hz1 : z ≠ 1 := by
    intro h
    apply hl₀z
    rw [h]
    simp
  have hidx := index_centralizer_le hsh hB hwU hwZ (hWfix w hw)
  have hle : L ⊓ Subgroup.centralizer ({w} : Set G) ≤ mZ1516 Mc Z₁ := by
    intro x hx
    have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    exact centralizer_le_mZ hc hz hz1 (hLG hx.1) ((hwiff x hx.1).2 hxw)
  have hdvd := Subgroup.relIndex_dvd_of_le_left L hle
  have hpos : 0 < (L ⊓ Subgroup.centralizer ({w} : Set G)).relIndex L :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  exact (Nat.le_of_dvd hpos hdvd).trans hidx

theorem not_excA7_index (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G)) (hexc : IsExcA7Block L)
    (hidx : (mZ1516 Mc Z₁).relIndex L = 35) : False := by
  have h := relIndex_le_blockN hc hcomp hexc.1 hSN
  have hn : Nat.card (BlockN L) = 16 := by
    have := hexc.2.2
    show ((blockZ L).subgroupOf (blockU L)).index = 16
    rw [this]
    norm_num
  rw [hidx, hn] at h
  omega

end CFSG.Quasithin.S151TB
