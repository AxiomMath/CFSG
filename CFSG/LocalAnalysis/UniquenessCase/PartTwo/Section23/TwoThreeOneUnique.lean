module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneBasic
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerTV
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

namespace S231

omit [Finite G] in
private theorem le_normalizer_closure_twoElems_S03 {S K : Subgroup G}
    (hKn : S ≤ Subgroup.normalizer (K : Set G)) :
    S ≤ Subgroup.normalizer
      ((Subgroup.closure {x : G | x ∈ K ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} : Subgroup G) : Set G) := by
  classical
  let T : Set G := {x : G | x ∈ K ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1}
  have hmemT : ∀ g ∈ S, ∀ x ∈ T, MulAut.conj g x ∈ T := by
    intro g hg x hx
    obtain ⟨hxK, n, hxn⟩ := hx
    have hgxK : MulAut.conj g x ∈ K := by
      have h1 : MulAut.conj g x ∈ K.map (MulAut.conj g) := ⟨x, hxK, rfl⟩
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKn hg)] at h1
    exact ⟨hgxK, n, by rw [MulAut.conj_apply, conj_pow, hxn, mul_one, mul_inv_cancel]⟩
  have hnormT : S ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hmemT g hg x hx
    · intro y hy
      refine ⟨MulAut.conj (g⁻¹) y, hmemT (g⁻¹) (S.inv_mem hg) y hy, ?_⟩
      show MulAut.conj g (MulAut.conj (g⁻¹) y) = y
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
  exact hnormT.trans (Subgroup.normalizer_le_normalizer_closure T)

theorem inf_centralizer_le_pCoreOf {L X : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hX : L ⊔ D.T ≤ normalizer (X : Set G)) (hCM : centralizer (X : Set G) ≤ D.M) :
    D.T ⊓ centralizer (X : Set G) ≤ CFSG.Open.pCoreOf 2 (L ⊔ D.T) := by
  let K : Subgroup G := (L ⊔ D.T) ⊓ centralizer (X : Set G)
  let R : Subgroup G := Subgroup.closure {x : G | x ∈ K ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1}
  have hKn : L ⊔ D.T ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hX)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRn : L ⊔ D.T ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_closure_twoElems_S03 (S := L ⊔ D.T) (K := K) hKn
  have hRK : R ≤ K := (Subgroup.closure_le K).2 fun x hx => hx.1
  have hpin : R ≤ CFSG.Open.pCoreOf 2 (L ⊔ D.T) :=
    S231.le_pCoreOf_of_normal hL (hRK.trans inf_le_left) hRn
      (hRK.trans (inf_le_right.trans hCM)) ⟨{x : G | x ∈ K ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1},
        fun x hx => hx.2, rfl⟩
  intro t ht
  have ht2 : ∃ n : ℕ, t ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := D.sylowM.isPGroup ⟨t, ht.1⟩
    exact ⟨n, by simpa using congrArg (fun x : ↥D.T => (x : G)) hn⟩
  exact hpin (Subgroup.subset_closure
    (show t ∈ {x : G | x ∈ K ∧ ∃ n : ℕ, x ^ (2 ^ n) = 1} from
      ⟨⟨(le_sup_right : D.T ≤ L ⊔ D.T) ht.1, ht.2⟩, ht2⟩))

theorem le_normalizer_inf_centralizer {L X : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hX : L ⊔ D.T ≤ normalizer (X : Set G)) (hCM : centralizer (X : Set G) ≤ D.M) :
    L ⊔ D.T ≤ normalizer ((D.T ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  have hO2 : CFSG.Open.pCoreOf 2 (L ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (TwelveShort.isSylowIn_of_le D (le_sup_right : D.T ≤ L ⊔ D.T))
  have h1 : (D.T ⊓ centralizer (X : Set G) : Subgroup G) =
      (CFSG.Open.pCoreOf 2 (L ⊔ D.T) ⊓ centralizer (X : Set G) : Subgroup G) := by
    refine le_antisymm ?_ ?_
    · exact le_inf (inf_centralizer_le_pCoreOf hL hX hCM) inf_le_right
    · exact le_inf (inf_le_left.trans hO2) inf_le_right
  rw [h1]
  exact (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ D.T))
    (B2F.le_normalizer_centralizer hX)).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem setting11 (c : Ctx23L D Ch) {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVle : V ≤ c.V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥) :
    CFSG.LocalAnalysis.WeakClosure81.Setting11 c.N V (D.T ⊓ centralizer (V : Set G)) := by
  have hNmax : rankThreeIsMaxTwoLocal c.N := (Ctx23L.N_mem_calMOf_T c).1
  have hTleN : D.T ≤ c.N := (Ctx23L.N_mem_calMOf_T c).2
  have hNnormV : c.N ≤ normalizer (V : Set G) := S231.N_le_normalizer_V c hVeq
  have hX : c.L ⊔ D.T ≤ normalizer (V : Set G) := (Ctx23L.sup_le_N D Ch c).trans hNnormV
  have hCM : centralizer (V : Set G) ≤ D.M := S231.centralizer_le_M c hVeq hVne inf_le_left
  refine ⟨D.standing.charTwo, hNmax, hV, S231.V_le_N c hVle, hNnormV, hVne, ?_, ?_⟩
  · have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 D.T c.N := D.sylowG.of_le hTleN le_top
    have hNnorm : c.N ≤ Subgroup.normalizer
        ((c.N ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hNnormV)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hsyl := hSylN.inf_of_le_normalizer (N := c.N ⊓ centralizer (V : Set G))
      inf_le_left hNnorm
    have hset : D.T ⊓ (c.N ⊓ centralizer (V : Set G)) = D.T ⊓ centralizer (V : Set G) := by
      rw [← inf_assoc, inf_eq_left.2 hTleN]
    rw [hset] at hsyl
    exact (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)
      (P := D.T ⊓ centralizer (V : Set G))
      (K := c.N ⊓ centralizer (V : Set G))).1 hsyl
  · refine Set.ext fun K => ?_
    rw [Set.mem_singleton_iff]
    constructor
    · intro hK
      have hLT : c.L ⊔ D.T ≤
          Subgroup.normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ⊓ c.N :=
        le_inf (le_normalizer_inf_centralizer c.hL.1 hX hCM) (Ctx23L.sup_le_N D Ch c)
      have hmem : K ∈ calMOf (c.L ⊔ D.T) := ⟨hK.1, hLT.trans hK.2⟩
      rw [c.hN] at hmem
      exact Set.mem_singleton_iff.mp hmem
    · rintro rfl
      exact ⟨hNmax, inf_le_right⟩

theorem mBar_eq_mParam (c : Ctx23L D Ch) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVle : V ≤ c.V) (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥) :
    mBar c.N ⊥ V hV = E3.mParam (autI hV ⊤) := by
  have hMbar : Mbar c.N ⊥ V hV =
      (autI hV ⊤).map (MulAut.congr (TwelveShort.mkTilEquiv V hV)).toMonoidHom :=
    TwelveShort.barSub_bot_eq_map_congr c.N V hV (S231.normalizer_V_eq c hVle hVeq hVne).symm
  rw [mBar, hMbar, E3.mParam_map_congr (TwelveShort.mkTilEquiv V hV) (autI hV ⊤)]

theorem lt_sParam (c : Ctx23L D Ch) (h111 : W3Thm111 G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVle : V ≤ c.V) (hVeq : V = conjClosure c.N (V ⊓ D.Z))
    (hVne : V ≠ ⊥) (h2 : 2 < mBar c.N ⊥ V hV) {k : ℕ} (hk : k < mBar c.N ⊥ V hV) :
    k < E3.sParam hV := by
  have hNnorm : c.N ≤ normalizer (V : Set G) := S231.N_le_normalizer_V c hVeq
  have hN0 : c.N ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hm2 : MBarGT c.N ⊥ V 2 :=
    (mBarGT_iff_lt_mBar c.N ⊥ V hV bot_le hNnorm hN0 2).2 h2
  have hmk : MBarGT c.N ⊥ V k :=
    (mBarGT_iff_lt_mBar c.N ⊥ V hV bot_le hNnorm hN0 k).2 hk
  have hr : (k : ℕ∞) < E3.rParam V := by
    have h := h111 c.N V (D.T ⊓ centralizer (V : Set G)) (setting11 c hV hVle hVeq hVne) hm2 k hmk
    rwa [rMV_eq_rParam (S231.normalizer_V_eq c hVle hVeq hVne)] at h
  have hm : k < E3.mParam (autI hV ⊤) := by
    rwa [S231.mBar_eq_mParam c hV hVle hVeq hVne] at hk
  exact E3.lt_sParam_of_lt hV hr hm

theorem two_lt_rk (c : Ctx23L D Ch) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (h2 : 2 < mBar c.N ⊥ V hV) :
    2 < rk ↥V := by
  have hNnorm : c.N ≤ normalizer (V : Set G) := S231.N_le_normalizer_V c hVeq
  have hN0 : c.N ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hm2 : MBarGT c.N ⊥ V 2 :=
    (mBarGT_iff_lt_mBar c.N ⊥ V hV bot_le hNnorm hN0 2).2 h2
  have hcard : 2 ^ 3 ≤ Nat.card V := by simpa using uc22p22ta_card_le hm2
  have hpow : Nat.card V = 2 ^ rk ↥V :=
    card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)
  rw [hpow] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

end S231

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
