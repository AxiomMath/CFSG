module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenCommon
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenFund
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fun_case_hyps {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h1 : ¬ P17_12_1 r q L) (h2 : ¬ P17_12_2 q L) {x : G}
    (hxM : x ∈ D.M) {Lx : Subgroup G} (hLx : Lx = L.map (MulAut.conj x).toMonoidHom) :
    (∃ (t : CFSG.Open.StatedLieTag) (n f : ℕ), CFSG.Open.StatedLieAdmissible t n r f ∧
        q = r ^ f ∧ LieModel (Bar2 Lx ⧸ Subgroup.center (Bar2 Lx)) t n r f) ∧
      CFSG.Open.IsQuasisimple (Bar2 Lx) ∧ Odd (Nat.card (Subgroup.center (Bar2 Lx))) ∧
      ¬ IsL2Over17 (Bar2 Lx ⧸ Subgroup.center (Bar2 Lx)) q ∧
      ¬ IsL3EpsOdd17 (Bar2 Lx ⧸ Subgroup.center (Bar2 Lx)) r ∧ ¬ IsReeOver17 (Bar2 Lx) q := by
  subst hLx
  obtain ⟨hr, hr2, t, n, f, hadm, hq, hmodel⟩ := hC.lie
  have hMx : D.M.map (MulAut.conj x).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer hxM)
  have hLxC : L.map (MulAut.conj x).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M (MulAut.conj x) hMx hC.memL
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hC.memL
  obtain ⟨e2⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hLxC
  let eB : Bar2 L ≃* Bar2 (L.map (MulAut.conj x).toMonoidHom) :=
    UC6S846.bar2Equiv (Subgroup.equivMapOfInjective L (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective)
  let eC : (Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      (Bar2 (L.map (MulAut.conj x).toMonoidHom) ⧸
        Subgroup.center (Bar2 (L.map (MulAut.conj x).toMonoidHom))) :=
    QuotientGroup.congr (Subgroup.center (Bar2 L))
      (Subgroup.center (Bar2 (L.map (MulAut.conj x).toMonoidHom))) eB
      (Subgroup.map_center_eq eB)
  refine ⟨⟨t, n, f, hadm, hq, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact LieModel.of_mulEquiv eC (LieModel.of_mulEquiv e1 hmodel)
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv eB.symm hC.memL.2.2
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2
      ↥(L.map (MulAut.conj x).toMonoidHom)
  · intro hL2
    rw [P17_12_1] at h1
    exact h1 (Or.inl (isL2Over17_of_mulEquiv e1 (isL2Over17_of_mulEquiv eC hL2)))
  · intro hL3
    rw [P17_12_1] at h1
    refine h1 (Or.inr ?_)
    rcases hL3 with h | h
    · exact Or.inl (LieModel.of_mulEquiv e1.symm (LieModel.of_mulEquiv eC.symm h))
    · exact Or.inr (LieModel.of_mulEquiv e1.symm (LieModel.of_mulEquiv eC.symm h))
  · intro hRee
    rw [P17_12_2] at h2
    obtain ⟨n', hqn, hLie⟩ := hRee
    exact h2 ⟨n', hqn, LieModel.of_mulEquiv eB.symm hLie⟩


theorem fun_case_dichotomy (hFunComm : K_FunCommute) {D : Data G} {V₀ V L : Subgroup G}
    {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) (h9 : R17_9At D V₀ V L r q hC)
    (h1 : ¬ P17_12_1 r q L) (h2 : ¬ P17_12_2 q L)
    {x : G} (hxM : x ∈ D.M) {Lx X : Subgroup G} (hLx : Lx = L.map (MulAut.conj x).toMonoidHom)
    (hXLx : X ≤ Lx) (hO2 : CFSG.Open.pCoreOf 2 Lx ≤ X)
    (hKb : (X.subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) ∈
      FunSet (fundPred q) (Bar2 Lx)
        (((NTL17 D L ⊓ Lx).subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))))
    {t : G} (ht : t ∈ D.T) :
    X.map (MulAut.conj t).toMonoidHom = X ∨
      ⁅X, X.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.Open.pCoreOf 2 D.M := by
  classical
  have hMx : D.M.map (MulAut.conj x).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer hxM)
  have hLxC : Lx ∈ calC D.M := by
    rw [hLx]
    exact UC6S846.calC_map D.M (MulAut.conj x) hMx hC.memL
  by_cases htN : t ∈ Subgroup.normalizer (Lx : Set G)
  · have hLxt : Lx.map (MulAut.conj t).toMonoidHom = Lx :=
      UC6S846.mem_normalizer_iff_map_conj.mp htN
    have hO2map : CFSG.Open.pCoreOf 2 Lx ≤ X.map (MulAut.conj t).toMonoidHom := by
      have h1 : CFSG.Open.pCoreOf 2 (Lx.map (MulAut.conj t).toMonoidHom) =
          (CFSG.Open.pCoreOf 2 Lx).map (MulAut.conj t).toMonoidHom :=
        CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 (MulAut.conj t).toMonoidHom
          (MulAut.conj t).injective Lx
      rw [hLxt] at h1
      rw [h1]
      exact Subgroup.map_mono hO2
    have hSS' : ((NTL17 D L ⊓ Lx).subgroupOf Lx) ≤
        ((NTL17 D Lx ⊓ Lx).subgroupOf Lx) := by
      have hEq : NTL17 D Lx ⊓ Lx = D.T ⊓ Lx := by
        ext y
        constructor
        · rintro ⟨⟨hyT, -⟩, hyL⟩
          exact ⟨hyT, hyL⟩
        · rintro ⟨hyT, hyL⟩
          exact ⟨⟨hyT, Subgroup.le_normalizer hyL⟩, hyL⟩
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rw [hEq]
      exact ⟨(Subgroup.mem_inf.mp hy).1.1, (Subgroup.mem_inf.mp hy).2⟩
    have hSyl2 : IsPGroup 2 (Syl2Bar D Lx) := by
      obtain ⟨P, hP⟩ := exists_sylow_syl2Bar D Lx hLxC.1
      exact hP ▸ P.isPGroup'
    have hKbSyl : (X.subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) ∈
        FunSet (fundPred q) (Bar2 Lx) (Syl2Bar D Lx) :=
      funSet_mono_of_le (Subgroup.map_mono hSS') hSyl2 hKb
    set Kb : Subgroup (Bar2 Lx) :=
      (X.subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) with hKbdef
    let M0 : Subgroup G := NTL17 D Lx
    have hM0N : M0 ≤ Subgroup.normalizer (Lx : Set G) := fun m hm => (Subgroup.mem_inf.mp hm).2
    have htM0 : t ∈ M0 := ⟨ht, htN⟩
    let m0 : ↥M0 := ⟨t, htM0⟩
    let eα : Bar2 Lx ≃* Bar2 Lx := CFSG.GroupTheory.conjModPCore 2 Lx M0 hM0N m0
    have heα : eα = CFSG.GroupTheory.conjModPCore 2 Lx M0 hM0N m0 := rfl
    have hmk : ∀ (u : ↥M0) (y : ↥Lx),
        (CFSG.GroupTheory.conjModPCore 2 Lx M0 hM0N u).toMonoidHom
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx) y) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥Lx) ⟨(u : G) * (y : G) * (u : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hM0N u.2) (y : G)).1 y.2⟩ := by
      intro u y
      exact CFSG.GroupTheory.conjModPCore_mk 2 Lx M0 hM0N u y
    have hgen : ∀ u : ↥M0, (Syl2Bar D Lx).map
        (CFSG.GroupTheory.conjModPCore 2 Lx M0 hM0N u).toMonoidHom ≤ Syl2Bar D Lx := by
      intro u z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
      have hyG : (y : G) ∈ NTL17 D Lx ⊓ Lx := Subgroup.mem_subgroupOf.mp hy
      have hyT : (y : G) ∈ D.T := (Subgroup.mem_inf.mp hyG).1.1
      have hyL : (y : G) ∈ Lx := (Subgroup.mem_inf.mp hyG).2
      have hmem : (⟨(u : G) * (y : G) * (u : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hM0N u.2) (y : G)).1 hyL⟩ : ↥Lx) ∈
          (NTL17 D Lx ⊓ Lx).subgroupOf Lx := by
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.mpr ⟨⟨?_, ?_⟩, ?_⟩
        · have huT : (u : G) ∈ D.T := (Subgroup.mem_inf.mp u.2).1
          exact D.T.mul_mem (D.T.mul_mem huT hyT) (D.T.inv_mem huT)
        · have huN : (u : G) ∈ Subgroup.normalizer (Lx : Set G) := (Subgroup.mem_inf.mp u.2).2
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huN (Subgroup.mem_inf.mp hyG).1.2)
            (Subgroup.inv_mem _ huN)
        · exact (Subgroup.mem_normalizer_iff.mp (hM0N u.2) (y : G)).1 hyL
      rw [hmk u y]
      exact Subgroup.mem_map_of_mem _ hmem
    have hαS : (Syl2Bar D Lx).map eα.toMonoidHom = Syl2Bar D Lx := by
      refine le_antisymm (hgen m0) ?_
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have hyG : (y : G) ∈ NTL17 D Lx ⊓ Lx := Subgroup.mem_subgroupOf.mp hy
      have hyT : (y : G) ∈ D.T := (Subgroup.mem_inf.mp hyG).1.1
      have hyL : (y : G) ∈ Lx := (Subgroup.mem_inf.mp hyG).2
      have hinvN : t⁻¹ ∈ Subgroup.normalizer (Lx : Set G) := Subgroup.inv_mem _ htN
      have hinvL : t⁻¹ * (y : G) * t ∈ Lx := by
        simpa using (Subgroup.mem_normalizer_iff.mp hinvN (y : G)).1 hyL
      have hmem : (⟨t⁻¹ * (y : G) * t, hinvL⟩ : ↥Lx) ∈
          (NTL17 D Lx ⊓ Lx).subgroupOf Lx := by
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.mpr ⟨⟨?_, ?_⟩, ?_⟩
        · exact D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) hyT) ht
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htN)
            (Subgroup.mem_inf.mp hyG).1.2) htN
        · exact hinvL
      refine Subgroup.mem_map.mpr
        ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Lx) ⟨t⁻¹ * (y : G) * t, hinvL⟩,
          Subgroup.mem_map_of_mem _ hmem, ?_⟩
      rw [heα, hmk m0]
      apply congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))
      apply Subtype.ext
      show t * (t⁻¹ * (y : G) * t) * t⁻¹ = (y : G)
      group
    have hKbα : Kb.map eα.toMonoidHom ∈ FunSet (fundPred q) (Bar2 Lx) (Syl2Bar D Lx) := by
      have h := funSet_map_mulEquiv eα hKbSyl
      rwa [hαS] at h
    obtain ⟨P, hPcoe⟩ := exists_sylow_syl2Bar D Lx hLxC.1
    by_cases hfix : Kb.map eα.toMonoidHom = Kb
    · left
      obtain ⟨⟨t', n', f', hadm', hq', hmodel'⟩, hqs, hodd, hnotL2, hnotL3, hnotRee⟩ :=
        fun_case_hyps hC h1 h2 hxM hLx
      have hkerX : (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)).ker ≤ X.subgroupOf Lx := by
        rw [QuotientGroup.ker_mk']
        intro v hv
        exact Subgroup.mem_subgroupOf.mpr (hO2 (Subgroup.mem_map_of_mem Lx.subtype hv))
      have hkerY : (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)).ker ≤
          (X.map (MulAut.conj t).toMonoidHom).subgroupOf Lx := by
        rw [QuotientGroup.ker_mk']
        intro v hv
        exact Subgroup.mem_subgroupOf.mpr (hO2map (Subgroup.mem_map_of_mem Lx.subtype hv))
      have hYmap : ((X.map (MulAut.conj t).toMonoidHom).subgroupOf Lx).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) = Kb.map eα.toMonoidHom := by
        apply le_antisymm
        · intro z hz
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
          obtain ⟨v, hvX, hvy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
          have hvL : v ∈ Lx := hXLx hvX
          refine Subgroup.mem_map.mpr
            ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Lx) ⟨v, hvL⟩, ?_, ?_⟩
          · rw [hKbdef]
            exact Subgroup.mem_map.mpr ⟨⟨v, hvL⟩, Subgroup.mem_subgroupOf.mpr hvX, rfl⟩
          · have hvy' : (MulAut.conj t) v = (y : G) := hvy
            refine (hmk m0 ⟨v, hvL⟩).trans (congrArg
              (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) (Subtype.ext ?_))
            rw [MulAut.conj_apply] at hvy'
            exact hvy'
        · intro z hz
          obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
          obtain ⟨v, hvXb, rfl⟩ := Subgroup.mem_map.mp hk
          have hvX : ((v : ↥Lx) : G) ∈ X := Subgroup.mem_subgroupOf.mp hvXb
          have hvL : ((v : ↥Lx) : G) ∈ Lx := v.2
          have htL : (MulAut.conj t) ((v : ↥Lx) : G) ∈ Lx :=
            (Subgroup.mem_normalizer_iff.mp htN ((v : ↥Lx) : G)).1 v.2
          refine Subgroup.mem_map.mpr
            ⟨⟨(MulAut.conj t) ((v : ↥Lx) : G), htL⟩, ?_, ?_⟩
          · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hvX)
          · refine (congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))
              (Subtype.ext ?_)).trans (hmk m0 v).symm
            show (MulAut.conj t) (v : G) = t * (v : G) * t⁻¹
            rw [MulAut.conj_apply]
      have hYeq : (X.map (MulAut.conj t).toMonoidHom).subgroupOf Lx = X.subgroupOf Lx := by
        have hXb : Kb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) = X.subgroupOf Lx := by
          rw [hKbdef]
          exact Subgroup.comap_map_eq_self hkerX
        calc (X.map (MulAut.conj t).toMonoidHom).subgroupOf Lx
            = (((X.map (MulAut.conj t).toMonoidHom).subgroupOf Lx).map
                (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))).comap
                (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) :=
              (Subgroup.comap_map_eq_self hkerY).symm
          _ = (Kb.map eα.toMonoidHom).comap
                (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) := by rw [hYmap]
          _ = Kb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) := by rw [hfix]
          _ = X.subgroupOf Lx := hXb
      have hYle : X.map (MulAut.conj t).toMonoidHom ≤ Lx := by
        rw [← hLxt]
        exact Subgroup.map_mono hXLx
      calc X.map (MulAut.conj t).toMonoidHom
          = ((X.map (MulAut.conj t).toMonoidHom).subgroupOf Lx).map Lx.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hYle).symm
        _ = (X.subgroupOf Lx).map Lx.subtype := by rw [hYeq]
        _ = X := Subgroup.map_subgroupOf_eq_of_le hXLx
    · right
      obtain ⟨⟨t', n', f', hadm', hq', hmodel'⟩, hqs, hodd, hnotL2, hnotL3, hnotRee⟩ :=
        fun_case_hyps hC h1 h2 hxM hLx
      have hcomm : ⁅Kb, Kb.map eα.toMonoidHom⁆ = ⊥ :=
        hFunComm (Bar2 Lx) r q (hC.lie.1) (hC.lie.2.1) ⟨t', n', f', hadm', hq', hmodel'⟩ hqs
          hodd hnotL2 hnotL3 hnotRee h9 P Kb (hPcoe.symm ▸ hKbSyl)
          (Kb.map eα.toMonoidHom) (hPcoe.symm ▸ hKbα) (fun h => hfix h.symm)
      have hO2LxM : CFSG.Open.pCoreOf 2 Lx ≤ CFSG.Open.pCoreOf 2 D.M :=
        CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hLxC.1
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨xb, hxb, rfl⟩ := Subgroup.mem_map.mp hb
      have haL : a ∈ Lx := hXLx ha
      have hbL : (MulAut.conj t) xb ∈ Lx := by
        rw [← hLxt]
        exact Subgroup.mem_map_of_mem _ (hXLx hxb)
      have hKbL : (QuotientGroup.mk (⟨a, haL⟩ : ↥Lx) : Bar2 Lx) ∈ Kb := by
        rw [hKbdef]
        exact Subgroup.mem_map.mpr ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have hKbR : (QuotientGroup.mk (⟨(MulAut.conj t) xb, hbL⟩ : ↥Lx) : Bar2 Lx) ∈
          Kb.map eα.toMonoidHom := by
        refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk (⟨xb, hXLx hxb⟩ : ↥Lx), ?_, ?_⟩
        · rw [hKbdef]
          exact Subgroup.mem_map.mpr ⟨⟨xb, hXLx hxb⟩, Subgroup.mem_subgroupOf.mpr hxb, rfl⟩
        · have h1 := CFSG.GroupTheory.conjModPCore_mk 2 Lx M0 hM0N m0
            (⟨xb, hXLx hxb⟩ : ↥Lx)
          rw [heα]
          refine h1.trans (congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))
            (Subtype.ext ?_))
          show t * (xb : G) * t⁻¹ = (MulAut.conj t) (xb : G)
          rw [MulAut.conj_apply]
      have hbot : ⁅(QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) (⟨a, haL⟩ : ↥Lx),
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)) (⟨(MulAut.conj t) xb, hbL⟩ : ↥Lx)⁆ = 1 := by
        have hb1 := Subgroup.commutator_mem_commutator hKbL hKbR
        rw [hcomm] at hb1
        simpa using hb1
      have hone : (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))
          (⁅(⟨a, haL⟩ : ↥Lx), (⟨(MulAut.conj t) xb, hbL⟩ : ↥Lx)⁆) = 1 := by
        rw [map_commutatorElement]
        exact hbot
      have hmemP : (↑(⁅(⟨a, haL⟩ : ↥Lx), (⟨(MulAut.conj t) xb, hbL⟩ : ↥Lx)⁆) : G) ∈
          CFSG.Open.pCoreOf 2 Lx :=
        Subgroup.mem_map_of_mem Lx.subtype ((QuotientGroup.eq_one_iff _).mp hone)
      exact hO2LxM (by simpa [commutatorElement_def] using hmemP)
  · exact Or.inr (comm_conj_of_not_mem_normalizer hLxC hXLx ht htN)

theorem delta17_12_case_fun_triple (hFunComm : K_FunCommute) {D : Data G}
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC) {H : Subgroup G}
    (hH : H ∈ Delta17_12 D (fundPred q) r q L) (h1 : ¬ P17_12_1 r q L)
    (h2 : ¬ P17_12_2 q L) :
    ∃ K : Subgroup (Bar2 H), CFSG.IsComponent K ∧
      orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
        CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤ ∧
      OddComponentShapeCore q (↥K ⧸ Subgroup.center ↥K) := by
  classical
  rw [Delta17_12, dif_neg h1, dif_neg h2] at hH
  obtain ⟨x, hxM, X, hX⟩ := hH
  dsimp only at hX
  obtain ⟨hXLx, hO2, rfl, hKb⟩ := hX
  set Lx : Subgroup G := L.map (MulAut.conj x).toMonoidHom with hLx
  set H' : Subgroup G := D.T ⊔ X with hH'
  have hMx : D.M.map (MulAut.conj x).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer hxM)
  have hLxC : Lx ∈ calC D.M := by
    rw [hLx]
    exact UC6S846.calC_map D.M (MulAut.conj x) hMx hC.memL
  have hXDM : X ≤ D.M := hXLx.trans hLxC.1.le
  have hXH : X ≤ H' := by rw [hH']; exact le_sup_right
  have hO2LxM : CFSG.Open.pCoreOf 2 Lx ≤ CFSG.Open.pCoreOf 2 D.M :=
    CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hLxC.1
  have hO2MH : CFSG.Open.pCoreOf 2 D.M ≤ CFSG.Open.pCoreOf 2 H' := by
    rw [hH']
    exact pCoreOf_M_le_of_T_le le_sup_left (sup_le D.sylowM.le hXDM)
  have hO2LH : CFSG.Open.pCoreOf 2 Lx ≤ CFSG.Open.pCoreOf 2 H' := hO2LxM.trans hO2MH
  let πL : ↥Lx →* Bar2 Lx := QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)
  let Kb : Subgroup (Bar2 Lx) := (X.subgroupOf Lx).map πL
  let πH : ↥H' →* Bar2 H' := QuotientGroup.mk' (CFSG.pCore 2 ↥H')
  let Xbar : Subgroup (Bar2 H') := (X.subgroupOf H').map πH
  have hKbFund : IsFundamentalOver q Kb := hKb.1
  obtain ⟨hKb_qs, q', hL2Kb, hq', hq'3⟩ := isFundamentalOver_quasisimple_shape h9 hKbFund
  let f₀ : ↥X →* Bar2 Lx := πL.comp (Subgroup.inclusion hXLx)
  have hf₀ : ∀ xx : ↥X, f₀ xx ∈ Kb := fun xx =>
    Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr xx.2)
  let f : ↥X →* ↥Kb := MonoidHom.codRestrict f₀ Kb hf₀
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp (show (z : Bar2 Lx) ∈ Kb from z.2)
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext ?_⟩
    exact hyz
  let g₀ : ↥X →* Bar2 H' := πH.comp (Subgroup.inclusion hXH)
  have hg₀ : ∀ xx : ↥X, g₀ xx ∈ Xbar := fun xx =>
    Subgroup.mem_map_of_mem πH (Subgroup.mem_subgroupOf.mpr xx.2)
  let g : ↥X →* ↥Xbar := MonoidHom.codRestrict g₀ Xbar hg₀
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp (show (z : Bar2 H') ∈ Xbar from z.2)
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext ?_⟩
    exact hyz
  have hker : f.ker ≤ g.ker := by
    intro xx hxx
    rw [MonoidHom.mem_ker] at hxx ⊢
    have hxx' : f₀ xx = 1 := by
      have h := congrArg Subtype.val hxx
      rw [show ((f xx : ↥Kb) : Bar2 Lx) = f₀ xx from rfl] at h
      simpa using h
    have h1 : (xx : G) ∈ CFSG.Open.pCoreOf 2 Lx := by
      have h2 : (⟨(xx : G), hXLx xx.2⟩ : ↥Lx) ∈ CFSG.pCore 2 ↥Lx :=
        (QuotientGroup.eq_one_iff _).mp hxx'
      exact Subgroup.mem_map_of_mem Lx.subtype h2
    have h3 : (xx : G) ∈ CFSG.Open.pCoreOf 2 H' := hO2LH h1
    have h4 : (⟨(xx : G), hXH xx.2⟩ : ↥H') ∈ CFSG.pCore 2 ↥H' := by
      rw [← CFSG.openPCoreOf_subgroupOf]
      exact Subgroup.mem_subgroupOf.mpr h3
    have h5 : g₀ xx = 1 := (QuotientGroup.eq_one_iff _).mpr h4
    exact Subtype.ext h5
  have hXbar_ne : Xbar ≠ ⊥ := by
    intro hbot
    have hle : X ≤ CFSG.Open.pCoreOf 2 H' := by
      intro xx hxx
      have h2 : πH (⟨xx, hXH hxx⟩ : ↥H') ∈ (X.subgroupOf H').map πH :=
        Subgroup.mem_map_of_mem πH (Subgroup.mem_subgroupOf.mpr hxx)
      rw [show (X.subgroupOf H').map πH = ⊥ from hbot, Subgroup.mem_bot] at h2
      have h3 : (⟨xx, hXH hxx⟩ : ↥H') ∈ CFSG.pCore 2 ↥H' :=
        (QuotientGroup.eq_one_iff _).mp h2
      exact Subgroup.mem_map_of_mem H'.subtype h3
    have hX2 : IsPGroup 2 ↥X :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H').to_le hle
    have hKb2 : IsPGroup 2 ↥Kb := IsPGroup.of_surjective hX2 f hf
    have : IsSimpleGroup (↥Kb ⧸ Subgroup.center ↥Kb) := hKb_qs.2.1
    have : Nontrivial ↥Kb := (QuotientGroup.mk'_surjective (Subgroup.center ↥Kb)).nontrivial
    have : Group.IsPerfect ↥Kb := hKb_qs.1
    exact Group.IsPerfect.not_isNilpotent ↥Kb hKb2.isNilpotent
  have : Nontrivial ↥Xbar := (Subgroup.nontrivial_iff_ne_bot Xbar).mpr hXbar_ne
  obtain ⟨hXbar_qs, ⟨eZ⟩⟩ :=
    CFSG.GroupTheory.quasisimple_and_centralQuotient_of_ker_le hKb_qs f hf g hg hker
  have hcore : OddComponentShapeCore q (↥Xbar ⧸ Subgroup.center ↥Xbar) :=
    Or.inl ⟨q', isL2Over17_of_mulEquiv eZ.symm hL2Kb, hq', hq'3⟩
  have htop : Xbar ⊔ CFSG.LocalAnalysis.WeakClosure81.barImage H' D.T = ⊤ :=
    barImage_sup_barImage_eq_top hH' hXH
  have hconj : ∀ t ∈ CFSG.LocalAnalysis.WeakClosure81.barImage H' D.T,
      Xbar.map (MulAut.conj t).toMonoidHom = Xbar ∨
        ⁅Xbar, Xbar.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ht
    have hyT : (y : G) ∈ D.T := Subgroup.mem_subgroupOf.mp hy
    have hconj_mk : ∀ u v : ↥H',
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H') u)).toMonoidHom
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H') v) =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H')) (MulAut.conj u v) := by
      intro u v
      simp [MulAut.conj_apply]
    have hval : ∀ u v : ↥H', ((MulAut.conj u v : ↥H') : G) = MulAut.conj (u : G) (v : G) := by
      intro u v
      simp [MulAut.conj_apply]
    rcases fun_case_dichotomy hFunComm hC h9 h1 h2 hxM hLx hXLx hO2 hKb hyT with hfix | hcomm
    · have hmain : Xbar.map
          (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H') y)).toMonoidHom = Xbar := by
        apply le_antisymm
        · intro z hz
          obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
          obtain ⟨xx, hxxb, rfl⟩ := Subgroup.mem_map.mp hw
          have hstep := hconj_mk y xx
          rw [hstep]
          refine Subgroup.mem_map.mpr ⟨MulAut.conj y xx, ?_, rfl⟩
          rw [Subgroup.mem_subgroupOf, hval y xx, ← hfix]
          exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hxxb)
        · intro z hz
          obtain ⟨xx, hxxb, rfl⟩ := Subgroup.mem_map.mp hz
          have hxxX : (xx : G) ∈ X := Subgroup.mem_subgroupOf.mp hxxb
          have hmem : (xx : G) ∈ X.map (MulAut.conj (y : G)).toMonoidHom := by
            rw [hfix]
            exact hxxX
          obtain ⟨w, hwX, hwx⟩ := Subgroup.mem_map.mp hmem
          have hwH : w ∈ H' := hXH hwX
          refine Subgroup.mem_map.mpr
            ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H') ⟨w, hwH⟩, ?_, ?_⟩
          · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hwX)
          · rw [hconj_mk y ⟨w, hwH⟩]
            exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥H')) (by
              apply Subtype.ext
              rw [hval y ⟨w, hwH⟩]
              exact hwx)
      exact Or.inl hmain
    · have hmain : ⁅Xbar, Xbar.map
          (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H') y)).toMonoidHom⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_bot]
        obtain ⟨xa, hxa, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
        obtain ⟨xb, hxb, rfl⟩ := Subgroup.mem_map.mp hb'
        have hxaX : (xa : G) ∈ X := Subgroup.mem_subgroupOf.mp hxa
        have hxbX : (xb : G) ∈ X := Subgroup.mem_subgroupOf.mp hxb
        have hcm : ⁅(xa : G), MulAut.conj (y : G) (xb : G)⁆ ∈ CFSG.Open.pCoreOf 2 H' :=
          hO2MH ((Subgroup.commutator_le.mp hcomm) (xa : G) hxaX
            (MulAut.conj (y : G) (xb : G)) (Subgroup.mem_map_of_mem _ hxbX))
        have hcoe : ((⁅xa, MulAut.conj y xb⁆ : ↥H') : G) =
            ⁅(xa : G), MulAut.conj (y : G) (xb : G)⁆ := by
          simp [commutatorElement_def, hval y xb]
        have hone : (QuotientGroup.mk' (CFSG.pCore 2 ↥H'))
            (⁅xa, MulAut.conj y xb⁆) = 1 := by
          refine (QuotientGroup.eq_one_iff (⁅xa, MulAut.conj y xb⁆)).mpr ?_
          rw [← CFSG.openPCoreOf_subgroupOf]
          refine Subgroup.mem_subgroupOf.mpr ?_
          rw [hcoe]
          exact hcm
        rw [hconj_mk y xb, ← map_commutatorElement]
        exact hone
      exact Or.inr hmain
  obtain ⟨hKcomp, hKtop⟩ :=
    CFSG.GroupTheory.isComponent_of_conj_dichotomy hXbar_qs hconj htop
  exact ⟨Xbar, hKcomp, hKtop, hcore⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
