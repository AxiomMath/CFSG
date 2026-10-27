module

public import CFSG.Quasithin.Vol2.Ch12Sec6L11f
public import CFSG.Quasithin.Vol2.Ch12Sec6L11g
public import CFSG.Quasithin.H13.A7Nat1238YSetup
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Vol2.Ch12Sec6L12a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126L11h

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem autOn_Lv_equiv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {W : Subgroup G}
    (hLW : Lv L v ≤ Subgroup.normalizer (W : Set G))
    (hO2 : pCoreOf 2 (Lv L v) ≤ Subgroup.centralizer (W : Set G))
    (hnc : ¬ Lv L v ≤ Subgroup.centralizer (W : Set G)) :
    Nonempty (↥(autOn (Lv L v) W) ≃* ↥A6s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_A6s
  obtain ⟨f, hf, hk, -⟩ := exists_psiLv h1222 F hH hv hβ
  set φ := InternalSec.autOnHom hLW with hφ
  have hP : f.ker ≤ φ.ker := by
    have hle : f.ker ≤ CFSG.pCore 2 ↥(Lv L v) := le_sSup ⟨f.normal_ker, hk⟩
    intro x hx
    refine (InternalSec.mem_ker_autOnHom hLW x).2 (hO2 ?_)
    rw [A7.pCoreOf_eq_map_cfsgPCore]
    exact ⟨x, hle hx, rfl⟩
  have hker : φ.ker = f.ker := by
    refine le_antisymm ?_ hP
    have hN : (φ.ker.map f).Normal := φ.normal_ker.map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map f) with h1 | h1
    · intro x hx
      have hmem : f x ∈ φ.ker.map f := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply hnc
      intro k hk'
      have hmem : f ⟨k, hk'⟩ ∈ φ.ker.map f := by
        rw [h1]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hxk⟩ := hmem
      have h2 : x⁻¹ * ⟨k, hk'⟩ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxk, inv_mul_cancel]
      have h3 : (⟨k, hk'⟩ : ↥(Lv L v)) ∈ φ.ker := by
        have := φ.ker.mul_mem hx (hP h2)
        rwa [mul_inv_cancel_left] at this
      exact (InternalSec.mem_ker_autOnHom hLW _).1 h3
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ
    (InternalSec.autOnHom_surjective hLW)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end S126L11h

theorem stmt12_6_11_f_of (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (hD3 : Lemma12_6_6_9)
    (h56 : AsB56) : Stmt12_6_11_f := by
  intro G _ _ T L V _ F v Kv S hC hLK hJ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hyp := hH.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hST : S = Tv T v := S126L11f.S_eq_Tv h1222 h1261 hD3 hC hLK hJ
  obtain ⟨-, hLJ⟩ := (hD3 G T L V F v Kv S hC).2.2.2.2 hJ
  have hGL : Gv v ≤ Subgroup.normalizer (Lv L v : Set G) := hLK ▸ hC.normal
  have hLG : Lv L v ≤ Gv v := Lv_le_Gv L v
  have hO2 : pCoreOf 2 (Lv L v) ≤ pCoreOf 2 (Gv v) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hLG)
      (hGL.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  obtain ⟨u, huΔ, huZ⟩ := exists_mem_Delta_central h1222 hH hv hβ
  have hZO : Subgroup.zpowers u ≤ pCoreOf 2 (Gv v) :=
    (Subgroup.zpowers_le).2 (hO2 (Vv_le_pCoreOf h1222 hH hv huΔ.2.1))
  have hZT : Subgroup.zpowers u ≤ quasithinOmegaOneCenter S := by
    rw [hST]
    exact (Subgroup.zpowers_le).2 huZ
  set W := conjClosure (Subgroup.zpowers u) (Gv v) with hW
  obtain ⟨-, hred⟩ := isTwoReducedIn_conjClosure_of_isSylowTwoOf hC.sylow hZO hZT
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have : IsMulCommutative ↥W := hWe.1
  have hΔW : ∀ u' ∈ Delta F v, u' ∈ W := by
    intro u' hu'
    obtain ⟨l, hl, hlu⟩ := exists_Lv_conj_eq h1222 hH hv hβ huΔ hu'
    exact Subgroup.subset_closure ⟨l, hLG hl, u, Subgroup.mem_zpowers u, hlu⟩
  have hVW : Vv L V v ≤ W :=
    (Vv_le_closure_Delta h1222 hH hv hβ).trans ((Subgroup.closure_le _).2 hΔW)
  have hGW : Gv v ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  have hLW : Lv L v ≤ Subgroup.normalizer (W : Set G) := hLG.trans hGW
  have hO2W : pCoreOf 2 (Lv L v) ≤ Subgroup.centralizer (W : Set G) :=
    A7.pCoreOf_le_centralizer_of_isTwoReducedIn hred hLG hGL
  have hncV : ¬ Lv L v ≤ Subgroup.centralizer (Vv L V v : Set G) := by
    intro hc
    have hbot : ⁅Vv L V v, Lv L v⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.1 hc
    have hu1 : u = 1 := by
      have := Vv_le_comm h1222 hH hv huΔ.2.1
      rwa [hbot, Subgroup.mem_bot] at this
    obtain ⟨-, huD⟩ := (mem_Delta_iff h1222 hH hv hβ).1 huΔ
    rw [hu1, coordV_one h1222 hH hv hβ] at huD
    exact absurd huD (by decide)
  have hnc : ¬ Lv L v ≤ Subgroup.centralizer (W : Set G) := fun hc => hncV fun l hl =>
    Subgroup.mem_centralizer_iff.2 fun y hy => Subgroup.mem_centralizer_iff.1 (hc hl) y (hVW hy)
  set K := autOn (Lv L v) W with hK
  obtain ⟨eK⟩ := S126L11h.autOn_Lv_equiv h1222 F hH hv hβ hLW hO2W hnc
  have hKs : IsSimpleGroup ↥K := by
    have := isSimpleGroup_A6s
    exact eK.isSimpleGroup
  have h360 : Nat.card ↥K = 360 := by
    rw [Nat.card_congr eK.toEquiv, card_A6s]
  have hKq : CFSG.IsQuasisimple ↥K := by
    refine A7.isQuasisimple_of_simple ⟨eK.symm ⟨cy 2 3 4, cy_mem (by decide) (by decide)
      (by decide) (by decide) (by decide)⟩, eK.symm ⟨cy 3 4 5, cy_mem (by decide) (by decide)
      (by decide) (by decide) (by decide)⟩, fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    have h1 := congrArg Subtype.val (eK.symm.injective h)
    exact absurd h1 (by decide)
  have hTv : CFSG.QuasithinUnique.IsSylowTwoOf (Tv T v) (Gv v) := hST ▸ hC.sylow
  have hTL : Tv T v ≤ Subgroup.normalizer (Lv L v : Set G) :=
    hC.tv_le.trans (hC.sylow.1.trans hGL)
  obtain ⟨A, -, hA, hLA⟩ := A7.exists_offender_moving hTv hTL hred hLW hKs hLJ
  have hH2 : pCoreOf 2 (Gv v) ≠ ⊥ := pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥(Gv v) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2
  obtain ⟨hKJ, hn, -, -, hcases⟩ := InternalSec.b56Cases_ffJ_autOn h56 hred.2.2.1.2 hGW hLG hGL
    hSQ (Setup.pCoreOf_autOn_eq_bot hred) hA hLA
  set P : Subgroup ↥W := (Vv L V v).subgroupOf W with hP
  have hmap : ⁅W, Lv L v⁆ ≤ (commV K).map W.subtype := A7.commutator_le_map_commV hLW
  have hVc : Vv L V v ≤ ⁅W, Lv L v⁆ :=
    (Vv_le_comm h1222 hH hv).trans (Subgroup.commutator_mono hVW le_rfl)
  have hPX : P ≤ commV K := by
    intro p hp
    obtain ⟨w, hw, hwp⟩ := hmap (hVc (Subgroup.mem_subgroupOf.1 hp))
    have hwp' : w = p := Subtype.ext hwp
    rw [← hwp']
    exact hw
  have hPinv : ∀ x ∈ K, ∀ p ∈ P, x p ∈ P := by
    intro x hx p hp
    obtain ⟨g, hgK, rfl⟩ := Setup.mem_autOn_iff.1 hx
    rw [Subgroup.mem_subgroupOf, Setup.coe_conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v hgK) _).1
      (Subgroup.mem_subgroupOf.1 hp)
  have hPf : ¬ P ≤ fixV K := by
    intro hfix
    apply hncV
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (hfix (show (⟨y, hVW hy⟩ : ↥W) ∈ P from hy)
      (conjAct W ⟨l, hLW hl⟩) (InternalSec.conjAct_mem_autOn hLW hl))
    rw [Setup.coe_conjAct_apply] at h1
    calc y * l = l * y * l⁻¹ * l := by rw [h1]
      _ = l * y := by group
  have hP32 : Nat.card ↥P = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv, card_Vv h1222 hH hv hβ]
  have hCV := S126L11g.commV_eq_of_b56_A6 hKJ hn h360 hKq hPX hPinv hPf hP32 hcases
  have hWL : ⁅W, Lv L v⁆ = Vv L V v := by
    refine le_antisymm ?_ hVc
    calc ⁅W, Lv L v⁆ ≤ (commV K).map W.subtype := hmap
      _ = P.map W.subtype := by rw [hCV]
      _ = Vv L V v := Subgroup.map_subgroupOf_eq_of_le hVW
  intro g hg
  rw [← hWL]
  exact A7.mem_normalizer_commutator (hGW hg) (hGL hg)

end CFSG.Quasithin.H13
