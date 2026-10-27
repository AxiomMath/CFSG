module

public import CFSG.Quasithin.EmptyFaithful.S151TBZ
public import CFSG.Quasithin.EmptyFaithful.S151TBCtx
public import CFSG.Quasithin.EmptyFaithful.S151TBNum
public import CFSG.Quasithin.EmptyFaithful.S151TBMax
public import CFSG.Quasithin.EmptyFaithful.S151U6

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem three_of_block
    (h37 : A37ForSQTK)
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (htype : IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) :
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
      IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L) := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hB : IsSylowTwoOf (S ⊓ L) L := sylow_inf hc
  obtain ⟨hN, hlat⟩ := input15122Rank2Lat_holds G L (S ⊓ L) htype hB
  have hmax3 := s151u_hmax3_of_lat hlat
  obtain ⟨hsh, hcard, hbig⟩ := numerics_of_type htype hB
  have hLc : CharTwo L := hsh.2.1
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hZS := omegaOneCenter_le hc
  have hZN : ∀ z ∈ quasithinOmegaOneCenter T, z ∈ Subgroup.normalizer (L : Set G) := by
    intro z hz
    have hz' := mem_quasithinOmegaOneCenter_iff.1 (hZS hz)
    refine s151u_mem_normalizer_of_comm hq.qtke hq.simple hq.nonabelian h37
      (hSet.pCore_g1_ne_bot hq hMf) hcomp hB hN (s1516_le_g1 T Z₁ hz'.1) fun c hcB => ?_
    have h1 : c * z = z * c := Subgroup.mem_centralizer_iff.1 hz'.2.1 c hcB.1
    rw [Subgroup.mem_centralizer_iff]
    intro l _
    have : ⁅z, c⁆ = 1 := by
      rw [commutatorElement_def, ← h1]
      group
    rw [this]
    simp
  set SH := S ⊓ Subgroup.normalizer (L : Set G) with hSH
  have hSHL : SH ⊓ L = S ⊓ L := s151u_inf_normalizer_inf S L
  have hSHN : SH ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hSH2 : IsPGroup 2 ↥SH := hS2.to_le inf_le_left
  have hBSH : IsSylowTwoOf (SH ⊓ L) L := by
    rw [hSHL]
    exact hB
  have hZSH : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter SH := by
    intro z hz
    have hz' := mem_quasithinOmegaOneCenter_iff.1 (hZS hz)
    refine mem_quasithinOmegaOneCenter_iff.2 ⟨⟨hz'.1, hZN z hz⟩, ?_, hz'.2.2⟩
    exact Subgroup.centralizer_le inf_le_left hz'.2.1
  obtain ⟨W, hWb, hWfix, hWcent, -⟩ := exists_zU hLc hperf hSH2 hSHN hBSH hZSH
  have hWB : ∀ w ∈ W, ∀ s ∈ S ⊓ L, s * w * s⁻¹ = w := by
    intro w hw s hs
    exact hWfix w hw s (by rw [hSHL]; exact hs)
  have hnot : ¬ L ≤ Subgroup.centralizer (W : Set G) := fun h =>
    not_le_centralizer hc hLG fun l hl => (hWcent l hl).2 (h hl)
  obtain ⟨hBP, hPmax⟩ := rank2_centralizer_max hsh hB hN hmax3 hcard hbig hWb hWB hnot
  have hPZ : L ⊓ Subgroup.centralizer (W : Set G) =
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact and_congr_right fun hx => (hWcent x hx).symm
  have hPle : L ⊓ Subgroup.centralizer (W : Set G) ≤ mZ1516 Mc Z₁ ⊓ L := by
    rw [hPZ]
    intro x hx
    exact ⟨centralizerZ_le_mZ hc (hLG hx.1) hx.2, hx.1⟩
  have hMLeq : mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (W : Set G) := by
    by_contra hne
    have hlt : L ⊓ Subgroup.centralizer (W : Set G) < mZ1516 Mc Z₁ ⊓ L :=
      lt_of_le_of_ne hPle (Ne.symm hne)
    exact hc.hL.not_le ((hPmax.2 _ hlt inf_le_right).symm.le.trans inf_le_left)
  refine ⟨hMLeq.trans hPZ, ?_⟩
  rw [hMLeq]
  refine ⟨⟨inf_le_left, S ⊓ L, hB, fun x hx => hBP (hN hx)⟩, hPmax.1.ne, ?_⟩
  · intro Q hQ hQL hPQ
    by_contra hne
    exact hQL (hPmax.2 Q (lt_of_le_of_ne hPQ (Ne.symm hne)) hQ.1)

end CFSG.Quasithin.S151TB
