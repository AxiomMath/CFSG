module

public import CFSG.Quasithin.Vol2.Ch10SecKRTa
public import CFSG.Quasithin.Vol2.Ch10SecD211B
public import CFSG.Quasithin.Background.C1PackS15212A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

structure FFSet (T K M₁ H₀ V : Subgroup G) : Prop where
  sylow : IsSylowTwoOf T H₀
  le : H₀ ≤ M₁
  o2 : pCoreOf 2 M₁ ≤ pCoreOf 2 H₀
  charTwo : CharTwo H₀
  sqtk : SQTKGroup ↥H₀
  elem : IsElemAbelian 2 V
  red : IsTwoReducedIn H₀ V
  thompson : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  K_not : ¬ K ≤ Subgroup.centralizer (V : Set G)

theorem sylow_of_le (cfg : B0KConfig G T L I H K M₁ J n m) {X : Subgroup G} (hTX : T ≤ X) :
    IsSylowTwoOf T X :=
  ⟨hTX, cfg.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le cfg.hyp.fsu.sylow hTX⟩

theorem H_le_of (cfg : B0KConfig G T L I H K M₁ J n m) {H₀ : Subgroup G} (hT : T ≤ H₀)
    (hK : conjClosure K T ≤ H₀) : H ≤ H₀ := by
  rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow (sylow_of_le cfg cfg.hH.1.1), cfg.hHK]
  exact sup_le hK hT

omit [Finite G] in
theorem T_le_centralizer_Z (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  exact (Subgroup.closure_le _).mpr fun _ hz => hz.1.2

theorem not_K_le_centralizer_Z (cfg : B0KConfig G T L I H K M₁ J n m) :
    ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro hK
  apply cfg.hZH
  have hTZ := T_le_centralizer_Z T
  have hKT : conjClosure K T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    refine conjClosure_le fun t ht k hk => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTZ ht) (hK hk)) (Subgroup.inv_mem _ (hTZ ht))
  have hH : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [← C1Pack12.oTwoUpper_sup_eq_of_sylow (sylow_of_le cfg cfg.hH.1.1), cfg.hHK]
    exact sup_le hKT hTZ
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  exact hH

theorem ffSet (h1022 : Stmt10_2_2) (cfg : B0KConfig G T L I H K M₁ J n m) {H₀ : Subgroup G}
    (hTH₀ : T ≤ H₀) (hH₀ : H₀ ≤ M₁) (hHH₀ : H ≤ H₀) :
    FFSet T K M₁ H₀ (conjClosure (quasithinOmegaOneCenter T) H₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := sylow_of_le cfg hTH₀
  have hQT : pCoreOf 2 M₁ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf (sylow cfg)
  have ho2 : pCoreOf 2 M₁ ≤ pCoreOf 2 H₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans hTH₀)
      (hH₀.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
  have hO : pCoreOf 2 H₀ ≠ ⊥ := fun h => pCoreOf_ne_bot cfg (le_bot_iff.mp (h ▸ ho2))
  have hchar : CharTwo H₀ := SecD.charTwo_of_le cfg.hyp.fsu.qtke cfg.hyp.fsu.sylow hTH₀ hO
  have hZ : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter T := le_rfl
  have hel := (conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hchar hZ).2
  have hred := isTwoReducedIn_conjClosure_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hchar hZ
  have hVZ : VZ T H ≤ conjClosure (quasithinOmegaOneCenter T) H₀ := conjClosure_mono le_rfl hHH₀
  have hJ := ((h1022 G T L I cfg.hyp H cfg.hH cfg.hZH).2 (Or.inl ⟨n, cfg.case1⟩)).1.2.1
  refine ⟨hsyl, hH₀, ho2, hchar, InternalSec.sqtkGroup_of_localSQTK (localSQTK cfg) hO, hel,
    hred, fun h => hJ (h.trans (Subgroup.centralizer_le hVZ)), fun h => ?_⟩
  exact not_K_le_centralizer_Z cfg (h.trans (Subgroup.centralizer_le (le_conjClosure _ _)))

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
