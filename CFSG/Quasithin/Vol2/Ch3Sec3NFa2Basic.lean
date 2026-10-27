module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321NF

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

namespace A2Cfg

variable (c : A2Cfg G T M L D H K q)
include c

theorem TL : T ≤ Subgroup.normalizer (L : Set G) := c.site.1

theorem Heq : H = (L ⊔ T) ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨-, -, -, -, -, h⟩ := c.site
  exact h

theorem mPlus_eq : mPlus L T = L := by
  refine le_antisymm (conjClosure_le fun t ht l hl => ?_) (le_conjClosure L T)
  exact (Subgroup.mem_normalizer_iff.mp (c.TL ht) l).mp hl

theorem hH : H = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T := by
  have hTZ := CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  rw [c.Heq]
  exact (CFSG.Quasithin.H13.sup_inf_eq_inf_sup_of_le_normalizer hTZ c.TL).symm

theorem rD_eq : L3321.rD T L = pCoreOf 2 H := by
  rw [c.hH]

theorem sylow_H : IsSylowTwoOf T H :=
  isSylowTwoOf_of_quasithinIsSylowTwo c.nf.hyp.sylow c.nf.inH.1

theorem H_le_G2 : H ≤ conjClosure K T ⊔ T := by
  rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow c.sylow_H]
  exact sup_le_sup_right c.nf.YK T

theorem TC_le_R : pCoreOf 2 (conjClosure K T ⊔ T) ≤ pCoreOf 2 H := by
  have hTsylK : IsSylowTwoOf T (conjClosure K T ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo c.nf.hyp.sylow le_sup_right
  have hTCT : pCoreOf 2 (conjClosure K T ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsylK
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hTCT.trans c.nf.inH.1)
    (c.H_le_G2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure K T ⊔ T)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure K T ⊔ T))

theorem N0_le_TC : pCoreOf 2 (conjClosure K T) ≤ pCoreOf 2 (conjClosure K T ⊔ T) := by
  have hN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure K T))
  exact (le_trans hN (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjClosure K T)))

theorem Q_le_R : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 H := by
  obtain ⟨-, -, -, -, hOR, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  rw [← c.rD_eq]
  exact hOR

theorem V_le_Q : vPlus L T ≤ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨-, -, -, hVO, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  exact hVO

theorem V_le_R : vPlus L T ≤ pCoreOf 2 H := c.V_le_Q.trans c.Q_le_R

theorem V_elemAbelian : IsElemAbelian 2 (vPlus L T) := by
  obtain ⟨hVe, -, -, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  exact hVe

theorem V_ne_bot : vPlus L T ≠ ⊥ := by
  intro h
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (quasithinOmegaOneCenter_ne_bot c.nf.hyp.sylow.1 c.nf.hyp.toSetup331.T_ne_bot)
  have hzV : (z : G) ∈ vPlus L T := le_conjClosure _ _ z.2
  rw [h] at hzV
  exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hzV))

theorem not_K0_le_M (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : ¬ conjClosure K T ≤ M := by
  intro hK0
  have hKT : K ⊔ T ≤ M := sup_le ((le_conjClosure K T).trans hK0) c.nf.hyp.TM
  have hMK : M = Subgroup.normalizer (conjClosure K T : Set G) :=
    (c.nf.uniqueM h128 h37 h38 h39).2 M ⟨c.nf.hyp.maxM, hKT⟩
  exact Hyp331.not_D_le c.nf.hyp (hMK ▸ le_sup_right.trans (c.nf.H₀_le_normalizer h37 h38))

theorem o2_G0 (h5 : Stmt3_3_5) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    pCoreOf 2 ((L ⊔ T) ⊔ (conjClosure K T ⊔ T)) = ⊥ := by
  by_contra hne
  have hX2 : IsPGroup 2 (pCoreOf 2 ((L ⊔ T) ⊔ (conjClosure K T ⊔ T))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hN : (L ⊔ T) ⊔ (conjClosure K T ⊔ T) ≤
      Subgroup.normalizer (pCoreOf 2 ((L ⊔ T) ⊔ (conjClosure K T ⊔ T)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hloc : IsTwoLocal
      (Subgroup.normalizer (pCoreOf 2 ((L ⊔ T) ⊔ (conjClosure K T ⊔ T)) : Set G)) :=
    ⟨_, hne, hX2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hU := (h5 G T M L c.nf.hyp.toSetup331).2.1
  rw [c.mPlus_eq] at hU
  have hLT : L ⊔ T ≤ M' := fun g hg => hle (hN (Subgroup.mem_sup_left hg))
  have hM'M : M' = M := hU.2 M' ⟨hM', hLT⟩
  apply c.not_K0_le_M h128 h37 h38 h39
  intro g hg
  have hg' : g ∈ M' := hle (hN (Subgroup.mem_sup_right (Subgroup.mem_sup_left hg)))
  rwa [hM'M] at hg'

theorem amalgamHypV (h5 : Stmt3_3_5) (h7 : Stmt3_3_7)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    AmalgamHypV ((L ⊔ T) ⊔ (conjClosure K T ⊔ T)) (L ⊔ T) (conjClosure K T ⊔ T) T (vPlus L T) := by
  have hyp := c.nf.hyp
  have hred := Hyp331.vPlus_reduced hyp.toSetup331
  have h7' := h7 G T M L D hyp
  rw [c.mPlus_eq] at h7'
  refine ⟨⟨rfl, charTwo_of_inH' hyp.qtke hyp.sylow ⟨le_sup_right, hyp.toSetup331.pCoreOf_ne_bot⟩,
    hyp.toSetup331.isSylowTwoOf, isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right,
    c.o2_G0 h5 h128 h37 h38 h39⟩, hred.2.2, ?_⟩
  have hCT : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = pCoreOf 2 (L ⊔ T) := h7'.1.2
  have hVN : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hCN : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G) : Subgroup G) : Set G) :=
    F7.le_normalizer_inf Subgroup.le_normalizer
      (hVN.trans (F7.normalizer_le_normalizer_centralizer _))
  have hQV : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (vPlus L T : Set G) := by
    rw [← hCT]; exact inf_le_right
  apply le_antisymm
  · rw [hCT]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hQV)
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · rw [hCT]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
      (hCN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem normalizer_le_M (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) :
    Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.nf.hyp
  obtain ⟨hTL, ⟨e⟩, hc, hmodE, -, -⟩ := c.site
  have hmod : Mod3321 T L := ⟨hc, Or.inl hmodE⟩
  obtain ⟨hVe, -, -, hVO, hOR, hRT, -⟩ := L3321.setting_facts hyp c.TL
  have hJC : thompsonJ (L3321.rD T L) ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    iSup₂_le fun A hA =>
      L3321.le_centralizer_of_isMaxElemAbelian h9 hyp c.mPlus_eq c.TL e hmod hA
  have h7' := (h7 G T M L D hyp).1.2
  rw [c.mPlus_eq] at h7'
  have hJO : thompsonJ (L3321.rD T L) ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← h7']
    exact le_inf ((thompsonJ_le_self _).trans hRT) hJC
  have hJeq : thompsonJ (L3321.rD T L) = thompsonJ (pCoreOf 2 (L ⊔ T)) :=
    thompsonJ_eq_of_le hJO hOR
  intro g hg
  rw [← c.rD_eq] at hg
  have hgJ : g ∈ Subgroup.normalizer (thompsonJ (L3321.rD T L) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (cjSub_thompsonJ hg)
  rw [hJeq] at hgJ
  refine L3322.normalizer_le_M h5 hyp c.mPlus_eq ?_ ?_ ?_ hgJ
  · obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L ⊔ T))
    have hAJ : A ≤ thompsonJ (pCoreOf 2 (L ⊔ T)) := le_iSup₂_of_le A hA le_rfl
    intro hbot
    rw [hbot, le_bot_iff] at hAJ
    have hVA := hA.2.2 (vPlus L T) hVO hVe
    rw [hAJ, Subgroup.card_bot] at hVA
    have hsubV : Subsingleton ↥(vPlus L T) := Finite.card_le_one_iff_subsingleton.1 hVA
    have hsub : Subsingleton (MulAut ↥(vPlus L T)) :=
      ⟨fun a b => MulEquiv.ext fun v => Subsingleton.elim _ _⟩
    have h1 : Nat.card ↥(autOn L (vPlus L T)) ≤ 1 := by
      have : Subsingleton ↥(autOn L (vPlus L T)) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim (a : MulAut ↥(vPlus L T)) b)⟩
      exact Finite.card_le_one_iff_subsingleton.2 this
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)] at h1
    norm_num at h1
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le (thompsonJ_le_self _)
  · intro x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (cjSub_thompsonJ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) hx))

end A2Cfg

end CFSG.Quasithin.H13.NFa2
