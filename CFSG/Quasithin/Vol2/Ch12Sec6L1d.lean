module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2J
public import CFSG.Quasithin.Vol2.Ch11SecCB51Core
public import CFSG.Quasithin.Vol2.Ch11SecCB213
public import CFSG.Quasithin.Vol2.Ch12Sec4A5Data
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Vocab

public section

namespace CFSG.Quasithin.H13

namespace S126L1d

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_offender {T L Y W : Subgroup G} [IsMulCommutative ↥W]
    (hred : IsTwoReducedIn Y W) (hTsyl : IsSylowTwoOf T Y) (hLY : L ≤ Y)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hq : CFSG.IsQuasisimple ↥(autOn L W))
    (hnc : ¬ L ≤ Subgroup.centralizer (W : Set G)) (hJ : L = ⁅L, thompsonJ T⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W := by
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := hTsyl.1.trans hred.2.1
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := hLY.trans hred.2.1
  have hnorm : ∀ A : Subgroup G, A ≤ T →
      autOn A W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := by
    intro A hAT x hx
    have hc := autOn_normal_of (U := W) (hAT.trans hTN)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A W).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ⁅autOn L W, autOn A W⁆ = autOn L W
  · obtain ⟨A, hA, hLA⟩ := hex
    have hAC : ¬ A ≤ Subgroup.centralizer (W : Set G) := by
      intro hAC
      have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, Subgroup.commutator_bot_right] at hLA
      refine not_commute_of_isQuasisimple hq fun a ha b hb => ?_
      rw [← hLA, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hTsyl hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe hred.1 hred.2.1 ⟨A, hoff, rfl⟩, hLA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian T A →
        autOn A W ≤ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) := by
      intro A hA
      rcases Vol2.Ch11.SecC.B51.commutator_eq_or_eq_bot hq (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S : Subgroup G :=
      ((Subgroup.centralizer (autOn L W : Set (MulAut ↥W))).comap (conjAct W)).map
        (Subgroup.normalizer (W : Set G)).subtype with hS
    have hJS : thompsonJ T ≤ S := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ Subgroup.normalizer (W : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    apply hnc
    rw [hJ, Subgroup.commutator_le]
    intro l hl j hj
    obtain ⟨g, hg, rfl⟩ := hJS hj
    set lN : ↥(Subgroup.normalizer (W : Set G)) := ⟨l, hLW hl⟩
    have hlK : conjAct W lN ∈ autOn L W := conjAct_mem_autOn hLW hl
    have hcomm : conjAct W ⁅lN, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hg _ hlK)
    exact (convI_eq_one_iff hWe ⁅lN, g⁆).1 hcomm

omit [Finite G] in
theorem exists_two_pow_mem {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {c : G} (hc : c ∈ L ⊔ T) :
    ∃ k : ℕ, c ^ 2 ^ k ∈ L := by
  have hc' : c ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
    exact hc
  obtain ⟨l, hl, t, ht, rfl⟩ := hc'
  have key : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', h⟩ := ih
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), mul_mem hl' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hTL (pow_mem ht m)) l).1 hl
      · rw [pow_succ, h]
        group
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', h⟩ := key (2 ^ k)
  exact ⟨k, by rw [h, htk, mul_one]; exact hl'⟩

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem isTwoReducedIn_R2 (L T : Subgroup G) :
    IsTwoReducedIn (L ⊔ T) (reducedAggregate (L ⊔ T)) := by
  have h := A4.isTwoReducedIn_twoReducedJoin (L ⊔ T)
  rwa [← primeReducedAggregate_map_subtype_eq_twoReducedJoin] at h

omit [IsMulCommutative ↥V] in
theorem commutator_le (h51 : AsB51) (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
    (hJ : L = ⁅L, thompsonJ T⁆) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have := hyp.simple
  set W := reducedAggregate (L ⊔ T) with hWdef
  have hred : IsTwoReducedIn (L ⊔ T) W := isTwoReducedIn_R2 L T
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have : IsMulCommutative ↥W := hWe.1
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hWe.2 w w.2)
  have hVW : V ≤ W := hyp.irrPlus.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hred.2.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hncV : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hyp.irrPlus.2.1
    rw [← hVL, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h
  have hnc : ¬ L ≤ Subgroup.centralizer (W : Set G) := fun h =>
    hncV (h.trans (Subgroup.centralizer_le hVW))
  have hO2Y : pCoreOf 2 (autOn (L ⊔ T) W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2L : pCoreOf 2 (autOn L W) = ⊥ := by
    have hn : ((autOn L W).subgroupOf (autOn (L ⊔ T) W)).Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact autOn_normal_of (sup_le Subgroup.le_normalizer hTN) _ x.2 _ hk
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
      (autOn_le_autOn_of_le le_sup_left) hn
    rw [hO2Y] at this
    exact le_bot_iff.1 this
  have hq : CFSG.IsQuasisimple ↥(autOn L W) := isQuasisimple_autOn hLW hyp.quasisimple hO2L hnc
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hQne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h =>
    hyp.irrPlus.2.1 (le_bot_iff.1 (h ▸ hVW.trans (reducedAggregate_le_pCoreOf _)))
  have hSL : SQTKGroup ↥L := sqtkGroup_mono (sqtkGroup_of_localSQTK hloc hQne) le_sup_left
  have hSQ : SQTKGroup ↥(autOn L W) := sqtkGroup_autOn hLW hSL
    ((S126T2.isPGroup_CL h1222 hH).to_le (inf_le_inf_left L (Subgroup.centralizer_le hVW)))
  obtain ⟨A, -, hA, hLA⟩ := exists_offender hred hTsyl le_sup_left hTN hq hnc hJ
  have h2 : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (W : Set G) :=
    fun y hy => (exists_two_pow_mem hTsyl.2.1 hTN hy).imp fun _ he =>
      (le_sup_left : L ≤ L ⊔ Subgroup.centralizer (W : Set G)) he
  have hb51 := (b51Hyp_ffJ_autOn hred.2.1 le_sup_left (sup_le Subgroup.le_normalizer hTN) h2
    hO2Y hq hSQ hA hLA).1
  have hconc := h51 ↥W hW2 _ _ hb51
  set K := autOn L W with hKdef
  set U := commV K with hUdef
  have hFix : fixV K = (Subgroup.centralizer (L : Set G)).subgroupOf W := fixV_autOn_eq hLW
  have hUmap : U.map W.subtype = ⁅W, L⁆ := map_commV_autOn hLW
  have hVU : V.subgroupOf W ≤ U := by
    intro v hv
    have h1 : (v : G) ∈ U.map W.subtype := by
      rw [hUmap]
      have h2 : (v : G) ∈ V := hv
      rw [← hVL] at h2
      exact Subgroup.commutator_mono hVW le_rfl h2
    obtain ⟨u, hu, hue⟩ := h1
    rwa [show u = v from Subtype.ext hue] at hu
  obtain ⟨⟨z, hzV, hzL⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hzW : z ∈ W := hVW hzV
  have hzF : (⟨z, hzW⟩ : ↥W) ∈ fixV K := by
    rw [hFix]
    exact hzL
  have hzU : (⟨z, hzW⟩ : ↥W) ∈ U := hVU hzV
  have hz1' : (⟨z, hzW⟩ : ↥W) ≠ 1 := fun h =>
    hz1 (Subtype.ext (show z = 1 from congrArg (fun w : ↥W => (w : G)) h))
  have hnotDir : ¬ IsIntDirect U (fixV K) ⊤ := fun h => by
    have h1 : (⟨z, hzW⟩ : ↥W) ∈ U ⊓ fixV K := ⟨hzU, hzF⟩
    rw [h.2, Subgroup.mem_bot] at h1
    exact hz1' h1
  obtain ⟨-, -, hcommU, hirrSec⟩ := (hconc.2.1.2 hnotDir).1
  have hVinv : ∀ a : ↥K, ∀ v ∈ V.subgroupOf W, (a : MulAut ↥W) v ∈ V.subgroupOf W := by
    intro a v hv
    obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.1 a.2
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_subgroupOf]
    show (((a : MulAut ↥W) v : ↥W) : G) ∈ V
    rw [← hga, A5Mod.conjAct_apply_coe]
    exact (Subgroup.mem_normalizer_iff.1 (hLV hg) v).1 hv
  have hUle : U ≤ V.subgroupOf W ⊔ fixV K := by
    set F := XMod.fixed (↥K) U with hFdef
    have hFK : F ≤ fixV K := fun f hf' a ha => hf'.2 ⟨a, ha⟩
    have hJinv : XMod.IsInv (↥K) (V.subgroupOf W ⊔ F) := by
      intro a x hx
      have hle : (V.subgroupOf W ⊔ F) ≤ (V.subgroupOf W ⊔ F).comap
          ((a : MulAut ↥W) : ↥W →* ↥W) := by
        refine sup_le (fun v hv => ?_) (fun f hf' => ?_)
        · exact Subgroup.mem_comap.2 (le_sup_left (a := V.subgroupOf W) (hVinv a v hv))
        · refine Subgroup.mem_comap.2 (le_sup_right (b := F) ?_)
          show (a : MulAut ↥W) f ∈ F
          have h1 : (a : MulAut ↥W) f = f := hf'.2 a
          rw [h1]
          exact hf'
      exact hle hx
    rcases hirrSec.2 _ hJinv le_sup_right (sup_le hVU hirrSec.1.le) with h | h
    · exfalso
      obtain ⟨v, hvV, hvL⟩ : ∃ v ∈ V, v ∉ Subgroup.centralizer (L : Set G) := by
        by_contra hall
        push Not at hall
        apply hncV
        intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact (Subgroup.mem_centralizer_iff.1 (hall w hw) l hl).symm
      have h1 : (⟨v, hVW hvV⟩ : ↥W) ∈ F := h ▸ le_sup_left (a := V.subgroupOf W) hvV
      have h2 := hFK h1
      rw [hFix] at h2
      exact hvL h2
    · exact (le_of_eq h.symm).trans (sup_le_sup_left hFK _)
  have hUV : U ≤ V.subgroupOf W := by
    show commV K ≤ V.subgroupOf W
    rw [← hcommU]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, u, hu, rfl⟩
    obtain ⟨v, hv, f, hf, rfl⟩ := Subgroup.mem_sup.1 (hUle hu)
    have hfa : a • f = f := hf a a.2
    have hva : a • v ∈ V.subgroupOf W := hVinv a v hv
    show a • (v * f) * (v * f)⁻¹ ∈ V.subgroupOf W
    rw [smul_mul', hfa, show a • v * f * (v * f)⁻¹ = a • v * v⁻¹ by group]
    exact (V.subgroupOf W).mul_mem hva ((V.subgroupOf W).inv_mem hv)
  rw [← hUmap]
  rintro _ ⟨u, hu, rfl⟩
  exact hUV hu

omit [IsMulCommutative ↥V] in
theorem part6 (h51 : AsB51) (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
    (hJ : L = ⁅L, thompsonJ T⁆) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  set Z := quasithinOmegaOneCenter T with hZdef
  set X := L ⊔ T with hXdef
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hTsyl : IsSylowTwoOf T X := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hZT : Z ≤ T := (Subgroup.closure_le _).mpr fun _ hx => hx.1.1
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := (Subgroup.closure_le _).mpr fun _ hx => hx.1.2
  have hVT : V ≤ T := hyp.irrPlus.1.trans ((reducedAggregate_le_pCoreOf X).trans
    (pCoreOf_two_le_of_isSylowTwoOf hTsyl))
  have hZO : Z ≤ pCoreOf 2 X := by
    have hQ : S126T2.Qv T V ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
        (S126T2.LT_le_normalizer_Qv h1222 hH) (hyp.sylow.1.to_le inf_le_left)
    refine le_trans (fun z hz => ?_) hQ
    exact ⟨hZT hz, Subgroup.mem_centralizer_iff.2 fun v hv =>
      Subgroup.mem_centralizer_iff.1 (hZC hz) v (hVT hv)⟩
  obtain ⟨-, hUred⟩ := isTwoReducedIn_conjClosure_of_isSylowTwoOf hTsyl hZO le_rfl
  set UZ := conjClosure Z X with hUZ
  have hUX : UZ ≤ X := hUred.1
  have hUW : UZ ≤ reducedAggregate X := by
    show UZ ≤ (primeReducedAggregate ↥X 2).map X.subtype
    rw [primeReducedAggregate_map_subtype_eq_twoReducedJoin]
    exact A4.le_twoReducedJoin hUred
  have hcomm := commutator_le h51 h1222 hH hJ hZ
  have hLU : ∀ l ∈ L, ∀ w ∈ UZ, l * w * l⁻¹ * w⁻¹ ∈ V := by
    intro l hl w hw
    have h1 := Subgroup.commutator_mem_commutator (hUW hw) hl
    have h2 : l * w * l⁻¹ * w⁻¹ = (⁅w, l⁆)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact V.inv_mem (hcomm h1)
  have hTU : ∀ t ∈ T, ∀ w ∈ UZ, t * w * t⁻¹ * w⁻¹ ∈ V := by
    intro t ht w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      obtain ⟨l, hl, s, hs, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hTN hh
      have hsz : s * z * s⁻¹ = z := by
        rw [Subgroup.mem_centralizer_iff.1 (hZC hz) s hs]
        group
      have htz : t * z * t⁻¹ = z := by
        rw [Subgroup.mem_centralizer_iff.1 (hZC hz) t ht]
        group
      have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTN ht) l).1 hl
      have hzU : z ∈ UZ := le_conjClosure Z X hz
      have e : t * (l * s * z * (l * s)⁻¹) * t⁻¹ * (l * s * z * (l * s)⁻¹)⁻¹ =
          ((t * l * t⁻¹) * z * (t * l * t⁻¹)⁻¹ * z⁻¹) * (l * z * l⁻¹ * z⁻¹)⁻¹ := by
        have e1 : l * s * z * (l * s)⁻¹ = l * z * l⁻¹ := by
          rw [show l * s * z * (l * s)⁻¹ = l * (s * z * s⁻¹) * l⁻¹ by group, hsz]
        rw [e1]
        calc t * (l * z * l⁻¹) * t⁻¹ * (l * z * l⁻¹)⁻¹
            = (t * l * t⁻¹) * (t * z * t⁻¹) * (t * l * t⁻¹)⁻¹ * (l * z * l⁻¹)⁻¹ := by group
          _ = _ := by rw [htz]; group
      rw [e]
      exact V.mul_mem (hLU _ hl' z hzU) (V.inv_mem (hLU l hl z hzU))
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : t * (x * y) * t⁻¹ * (x * y)⁻¹ =
          (t * x * t⁻¹ * x⁻¹) * (x * (t * y * t⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e]
      exact V.mul_mem ihx ((Subgroup.mem_normalizer_iff.1 (hXV (hUX hx)) _).1 ihy)
    | inv x hx ihx =>
      have e : t * x⁻¹ * t⁻¹ * x⁻¹⁻¹ = x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hXV (hUX (UZ.inv_mem hx))) _).1 (V.inv_mem ihx)
  have hXU : ∀ x ∈ X, ∀ w ∈ UZ, x * w * x⁻¹ * w⁻¹ ∈ V := by
    intro x hx w hw
    obtain ⟨l, hl, t, ht, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hTN hx
    have e : l * t * w * (l * t)⁻¹ * w⁻¹ =
        l * (t * w * t⁻¹ * w⁻¹) * l⁻¹ * (l * w * l⁻¹ * w⁻¹) := by group
    rw [e]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 (hLV hl) _).1 (hTU t ht w hw))
      (hLU l hl w hw)
  have hUe : IsElemAbelian 2 UZ := hUred.2.2.1
  have hUc : ∀ a ∈ UZ, ∀ b ∈ UZ, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcX : ⁅UZ, X⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    have h1 := hXU x hx w⁻¹ (UZ.inv_mem hw)
    have hxw : x * w⁻¹ * x⁻¹ ∈ UZ :=
      (Subgroup.mem_normalizer_iff.1 (hUred.2.1 hx) _).1 (UZ.inv_mem hw)
    rw [commutatorElement_def]
    have e : w * x * w⁻¹ * x⁻¹ = x * w⁻¹ * x⁻¹ * w⁻¹⁻¹ := by
      calc w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
        _ = x * w⁻¹ * x⁻¹ * w := hUc w hw _ hxw
        _ = x * w⁻¹ * x⁻¹ * w⁻¹⁻¹ := by rw [inv_inv]
    rw [e]
    exact h1
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZC
  have hdec := Vol2.Ch11.SecC.conjClosure_eq_commutator_sup (X := X) hTsyl.2.2 hUe hTZ
  have hcU : ⁅UZ, X⁆ ≤ UZ := Subgroup.le_normalizer_iff_commutator_le_left.mp hUred.2.1
  have hBN : UZ ⊓ Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer ((⁅UZ, X⁆ : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [hUc b hb.1 a (hcU ha), mul_assoc, mul_inv_cancel, mul_one]
      exact ha
    · intro ha
      have hab : b * a * b⁻¹ ∈ UZ := by
        have := hcU ha
        exact this
      have h1 : a = b⁻¹ * (b * a * b⁻¹) * b := by group
      have hau : a ∈ UZ := by
        rw [h1]
        exact UZ.mul_mem (UZ.mul_mem (UZ.inv_mem hb.1) hab) hb.1
      rw [hUc b hb.1 a hau, mul_assoc, mul_inv_cancel, mul_one] at ha
      exact ha
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzU : z ∈ conjClosure Z X := le_conjClosure Z X hz
  rw [hdec] at hzU
  obtain ⟨c, hc, d, hd, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hBN hzU
  have hcV : c ∈ V := hcX hc
  have hdT : ∀ t ∈ T, t * d = d * t := fun t ht =>
    (Subgroup.mem_centralizer_iff.1 hd.2 t ((le_sup_right : T ≤ X) ht))
  have hcT : c ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
    refine ⟨hcV, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    have hzt : t * (c * d) = c * d * t := Subgroup.mem_centralizer_iff.1 (hZC hz) t ht
    have h1 : t * c * d = c * t * d := by
      calc t * c * d = t * (c * d) := by group
        _ = c * d * t := hzt
        _ = c * (d * t) := by group
        _ = c * (t * d) := by rw [hdT t ht]
        _ = c * t * d := by group
    exact mul_right_cancel h1
  rw [← (S126L1c.part2 h1222 hH hZ).2] at hcT
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.1 hcT.2 l hl
  have hdl : l * d = d * l := Subgroup.mem_centralizer_iff.1 hd.2 l ((le_sup_left : L ≤ X) hl)
  calc c * d * l = c * (d * l) := by group
    _ = c * (l * d) := by rw [hdl]
    _ = (c * l) * d := by group
    _ = (l * c) * d := by rw [hcl]
    _ = l * (c * d) := by group

end S126L1d

end CFSG.Quasithin.H13
