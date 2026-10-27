module

public import CFSG.Quasithin.EmptyFaithful.S151ZG
public import CFSG.Quasithin.EmptyFaithful.S151ZR

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem SMin.isMinParabolic' [Finite G] {L S P : Subgroup G} (h : SMin L S P) (hS2 : IsPGroup 2 ↥S)
    (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hnn : ¬ P ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    IsMinParabolicOf (P ⊔ S) (P ⊔ S) := by
  have hBP : IsSylowTwoOf (S ⊓ L) P := ya7_isSylowTwoOf_restrict hsyl h.sl h.le
  have e5 : S.relIndex (P ⊔ S) = (S ⊓ L).relIndex P := smin_relIndex_S h
  have hSH : IsSylowTwoOf S (P ⊔ S) := by
    refine ⟨le_sup_right, hS2, ?_⟩
    have h3 : (S.subgroupOf (P ⊔ S)).index = (S ⊓ L).relIndex P := e5
    rw [h3]
    exact hBP.2.2
  refine zb_isMinParabolic_of hSH ?_ fun K hSK hKH => h.S_maximal hSK hKH
  intro hH
  apply hnn
  exact fun x hx => zb_mem_normalizer_inf (hH (Subgroup.mem_sup_left hx))
    (Subgroup.le_normalizer (h.le hx))

theorem s1516_normalizer_le_M [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L) : Subgroup.normalizer (s1516 T Z₁ : Set G) ≤ M := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hS0 : S ≠ ⊥ := ne_bot_of_le_ne_bot (hSet.pCore_g1_ne_bot hq hMf) hc.h18.four.pCoreOf_le
  have hb0 : baum S ≠ ⊥ := C1GN.baum_ne_bot hS2 hS0
  intro g hg
  have hmap : (baum S).map (MulAut.conj g).toMonoidHom = baum S := by
    rw [baum_map_mulEquiv, map_conj_eq_of_mem_normalizer hg]
  have hgb : g ∈ Subgroup.normalizer ((baum S : Subgroup G) : Set G) := by
    have key : ∀ x : G, x ∈ baum S ↔ g⁻¹ * x * g ∈ baum S := by
      intro x
      have h1 : x ∈ (baum S).map (MulAut.conj g).toMonoidHom ↔
          (MulAut.conj g).symm x ∈ baum S := Subgroup.mem_map_equiv
      rw [hmap] at h1
      rw [h1]
      simp only [MulAut.conj_symm_apply]
    have hg' : g⁻¹ ∈ Subgroup.normalizer ((baum S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simpa using key x
    exact inv_mem_iff.mp hg'
  exact hc.h17.cgs (normalizer_le_cgs hb0 hgb)

@[expose] def Input15122ThreeCLoc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G),
    (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) → IsPGroup 2 ↥S →
    S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
      L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
        Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
      IsMaxSubgroupIn L (L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G)) ∧
      ∃ P : Subgroup G, SMin L S P ∧
        ¬ P ≤ L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
        ¬ P ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
        IsMaxSubgroupIn L (P ⊔ (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))) ∧
        CharTwo P ∧ ¬ C126Third (P ⊔ S) S ∧ oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P

theorem input15122ThreeC_of' (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kN : RankTwoSimpleNotA38) (hloc : Input15122ThreeCLoc)
    (hzl : Input15122ThreeCZL2) : Input15122ThreeC := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h3C
  have h3C' := h3C
  obtain ⟨htype, hMLeq⟩ := h3C
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L htype)
  obtain ⟨hNS, hNC, hMLmax0, P, hP, hPnotML, hPnn, hPstar, hchP, hno, hoP⟩ :=
    hloc G L S htype hS2 hSN hsyl
  have hMLmax : IsMaxSubgroupIn L (mZ1516 Mc Z₁ ⊓ L) := by
    rw [hMLeq]
    exact hMLmax0
  have hSMZ : S ≤ mZ1516 Mc Z₁ := fun x hx => ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hPnot : ¬ P ≤ mZ1516 Mc Z₁ := by
    intro hPM
    apply hPnotML
    rw [← hMLeq]
    exact le_inf hPM hP.le
  have hchH : CharTwo (P ⊔ S) := zb_charTwo_sup hP.sP hS2 hchP
  have hmin : IsMinParabolicOf (P ⊔ S) (P ⊔ S) := hP.isMinParabolic' hS2 hsyl hPnn
  have hPM : P ≤ M := (bang_of_good h118 h126 hc hP.le hchH hmin hno).resolve_right hPnot
  set N : Subgroup G := L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) with hNdef
  have hNM : N ≤ M := fun n hn => s1516_normalizer_le_M hc (hNS hn)
  have hMLP : M ⊓ L = P ⊔ N := by
    have h1 : P ⊔ N ≤ M ⊓ L := sup_le (le_inf hPM hP.le) fun n hn => ⟨hNM hn, hn.1⟩
    have h2 : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
    rcases lt_or_eq_of_le h1 with hlt | heq
    · exact absurd (hPstar.2 _ hlt inf_le_right) h2
    · exact heq.symm
  have hNML : N ≤ mZ1516 Mc Z₁ ⊓ L := by
    rw [hMLeq]
    exact le_inf inf_le_left hNC
  have hMLpar : IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L) := by
    refine ⟨⟨inf_le_right, S ⊓ L, hsyl, hNML⟩, hMLmax.1.ne, fun Q hQ hQne hMQ => ?_⟩
    rcases lt_or_eq_of_le hMQ with hlt | heq
    · exact absurd (hMLmax.2 _ hlt hQ.1) hQne
    · exact heq.symm
  refine ⟨htype, hMLeq, hMLpar, ?_, ?_, ?_⟩
  · rw [hMLP]
    refine ⟨⟨sup_le hP.le inf_le_left, S ⊓ L, hsyl, le_sup_right⟩, hPstar.1.ne, fun Q hQ hQne hPQ => ?_⟩
    rcases lt_or_eq_of_le hPQ with hlt | heq
    · exact absurd (hPstar.2 _ hlt hQ.1) hQne
    · exact heq.symm
  · rw [hMLP]
    intro h
    exact hPnot ((le_sup_left.trans h.ge).trans inf_le_left)
  · exact centS15122_of hc hSN (hzl G T Mc M Z₁ Z₂ V₁ V₂ L hc h3C') (le_inf hPM hP.le) hPnot hoP

end CFSG.Quasithin
