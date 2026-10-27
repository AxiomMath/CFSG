module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Cut
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5C
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QJ
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Cases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mem_of_odd_of_mem_sup_ch615 {T N : Subgroup G} (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ T)
    (hodd : Odd (orderOf x)) : x ∈ N := by
  have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N T hTN] at hx'
  obtain ⟨k, hk, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨e, he⟩ := hT ⟨t, ht⟩
  have ht2 : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  obtain ⟨y', hy', hpow⟩ := pow_mul_mem_of_mem_normalizer hk (hTN ht) (2 ^ e)
  rw [ht2, mul_one] at hpow
  refine B6.mem_of_pow_mem_of_coprime (k := 2 ^ e) (hpow ▸ hy') ?_
  exact Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hodd)

omit [Finite G] in
theorem le_normalizer_of_le_centralizer_ch615 {X Z : Subgroup G}
    (h : X ≤ Subgroup.centralizer (Z : Set G)) : X ≤ Subgroup.normalizer (Z : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have e : g * z * g⁻¹ = z ∨ z ∉ Z := by
    by_cases hz : z ∈ Z
    · left
      rw [← Subgroup.mem_centralizer_iff.mp (h hg) z hz, mul_inv_cancel_right]
    · right; exact hz
  constructor
  · intro hz
    rcases e with e | e
    · rw [e]; exact hz
    · exact absurd hz e
  · intro hz
    have hz' : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ ∈ Z := by
      rw [← Subgroup.mem_centralizer_iff.mp (h (Subgroup.inv_mem _ hg)) _ hz,
        mul_inv_cancel_right]
      exact hz
    simpa [mul_assoc] using hz'

namespace Cx615B

theorem le_pCoreOf_of_le_commutator_ch615 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (c : Cx615B G T M L V H n)
    (hF : H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤
      ⁅H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G), thompsonJ T⁆ ⊔ pCoreOf 2 H) :
    H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤ pCoreOf 2 H := by
  classical
  by_contra hC
  have h := c.hyp
  set Z := quasithinOmegaOneCenter T with hZdef
  set C := H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) with hCdef
  set W := ⁅Z, L⁆ with hWdef
  set KW := Subgroup.centralizer (W : Set G) with hKWdef
  have hTH : T ≤ H := c.hH.1.1
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hsylH : IsSylowTwoOf T H := c.toCx615.isSylowTwoOf
  have hMP := c.toCx615.minParabolic h331
  have hZU : Z ≤ Cx615.UH T H := le_conjClosure _ _
  have hCZ : C ≤ Subgroup.centralizer (Z : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZU))
  have hCJ : C ≤ kerIn (H ⊓ M) H :=
    hMP.inf_centralizer_le_kerIn c.toCx615.UH_red.2 c.toCx615.not_le_centralizer_UH
  have hCM : C ≤ M := hCJ.trans (kerIn_le.trans inf_le_right)
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := hCM.trans h.normal
  have hCTL : C ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    refine le_trans (le_inf hCM ?_) c.CMZ
    exact hCZ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have hCW : C ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator_ch6 (le_normalizer_of_le_centralizer_ch615 hCZ) hCL
  have hCKW : C ≤ Subgroup.normalizer (KW : Set G) := le_normalizer_centralizer_ch6 hCW
  have hZT : Z ≤ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.2
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZT
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTW : T ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator_ch6 (le_normalizer_of_le_centralizer_ch615 hTZ) hTL
  have hTKW : T ≤ Subgroup.normalizer (KW : Set G) := le_normalizer_centralizer_ch6 hTW
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_right Z L
  have hLKW : L ≤ Subgroup.normalizer (KW : Set G) := le_normalizer_centralizer_ch6 hLW
  have hWL : ⁅W, L⁆ ≠ ⊥ := by
    intro hWL
    apply c.ZL
    have h1 : ⁅⁅L, Z⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L Z]; exact hWL
    have h3 : ⁅⁅L, L⁆, Z⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 hWL
    rw [h.toHyp5_0_1.commutator_eq, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    exact fun x hx => Subgroup.le_centralizer_iff.mp h3 hx.1
  have hLO : L ⊓ KW ≤ pCoreOf 2 L := h.toHyp5_0_1.inf_centralizer_le hLW hWL
  have hOLT : pCoreOf 2 L ≤ T :=
    (F7.isSylowTwoOf_pCoreOf_le c.toCx615.isSylowTwoOf_inf).trans inf_le_left
  have hTLB : T ⊓ L ≤ borelL T L := le_inf inf_le_right fun x hx => Subgroup.le_normalizer hx
  have hsylB : IsSylowTwoOf (T ⊓ L) (borelL T L) :=
    A4.isSylowTwoOf_mono c.toCx615.isSylowTwoOf_inf hTLB inf_le_left
  obtain ⟨D, hD⟩ := Lin2.exists_hall_of_normal_sylow hsylB inf_le_right
  have hS := h.toHyp5_0_1.setting516 hD h.module
  obtain ⟨F, _, _, _, -, ψ, Yc, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hVR : V ≤ reducedAggregate (L ⊔ T) := c.V_eq.le
  have hWV : W ≤ V :=
    (Subgroup.commutator_mono c.ZV le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans c.V_facts.2.1))
  have hJ : thompsonJ T ≤ (T ⊓ L) ⊔ KW := by
    refine GammaExtra.thompsonJ_le fun A hA a ha => ?_
    obtain ⟨s, hs, has⟩ := hS.exists_mul_of_isMaxElemAbelian hVR c.V_facts.2.1 hc hA ha
    have has' : a * s⁻¹ ∈ KW :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hWV.trans hVR)) has
    have e : a = a * s⁻¹ * s := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right has') (Subgroup.mem_sup_left hs)
  have hCN : C ≤ Subgroup.normalizer (((T ⊓ L) ⊔ KW : Subgroup G) : Set G) := by
    intro g hg
    have h1 := hCTL hg
    have h2 := hCKW hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have hCJT : ⁅C, thompsonJ T⁆ ≤ (T ⊓ L) ⊔ KW := by
    rw [Subgroup.commutator_le]
    intro g hg j hj
    have hj' := hJ hj
    have hgj : g * j * g⁻¹ ∈ (T ⊓ L) ⊔ KW := (Subgroup.mem_normalizer_iff.mp (hCN hg) j).mp hj'
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hgj (Subgroup.inv_mem _ hj')
  have hO2T : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hsylH
  have hCKT : C ≤ KW ⊔ T :=
    hF.trans (sup_le (hCJT.trans (sup_le (inf_le_left.trans le_sup_right) le_sup_left))
      (hO2T.trans le_sup_right))
  set Y := oTwoUpper C with hYdef
  have hoddKW : ∀ y ∈ C, Odd (orderOf y) → y ∈ KW := fun y hy hyo =>
    mem_of_odd_of_mem_sup_ch615 hT2 hTKW (hCKT hy) hyo
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, le_normalizer_centralizer_ch6 (le_normalizer_conjClosure _ _) hg⟩
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    hHC.trans (normalizer_le_normalizer_oTwoUpper C)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := hTH.trans hHC
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    have hgen : ∀ y ∈ C, Odd (orderOf y) → l * y * l⁻¹ ∈ Y := by
      intro y hyC hyo
      have hyKW := hoddKW y hyC hyo
      have hc1 : l * y * l⁻¹ * y⁻¹ ∈ L ⊓ KW := by
        refine ⟨?_, ?_⟩
        · have h1 : y * l⁻¹ * y⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp (hCL hyC) _).mp (L.inv_mem hl)
          have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
          rw [e]
          exact L.mul_mem hl h1
        · have h1 : l * y * l⁻¹ ∈ KW := (Subgroup.mem_normalizer_iff.mp (hLKW hl) y).mp hyKW
          exact KW.mul_mem h1 (KW.inv_mem hyKW)
      have hc2 : l * y * l⁻¹ * y⁻¹ ∈ T := hOLT (hLO hc1)
      have hmem : l * y * l⁻¹ ∈ C ⊔ T := by
        have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc2) (Subgroup.mem_sup_left hyC)
      have hodd' : Odd (orderOf (l * y * l⁻¹)) := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hyo
      exact mem_oTwoUpper_of_odd (mem_of_odd_of_mem_sup_ch615 hT2 hTC hmem hodd') hodd'
    apply mem_normalizer_of_conj_mem_ch6
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx.1 hx.2
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using Y.mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using Y.inv_mem ih
  have hYne : Y ≠ ⊥ := by
    intro hY
    apply hC
    refine le_pCoreOf_of_le_normalizer inf_le_left hHC ?_
    intro x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper C x.2
    rw [← hYdef, hY, Subgroup.mem_bot] at hk
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hYH : Y ≤ H := (oTwoUpper_le C).trans inf_le_left
  have hOY : pCoreOf 2 Y ≠ ⊥ := by
    intro hOY
    apply hYne
    have hYO : Y ⊓ pCoreOf 2 H ≤ pCoreOf 2 Y := by
      refine le_pCoreOf_of_le_normalizer inf_le_left ?_
        ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 H (hYH hg)⟩
    rw [hOY] at hYO
    have hcomm : ⁅Y, pCoreOf 2 H⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (le_inf ?_ ?_) hYO)
      · exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((pCoreOf_le 2 H).trans hHY)
      · exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          (hYH.trans (le_normalizer_pCoreOf 2 H))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    have hYO2 : Y ≤ pCoreOf 2 H := (le_inf hYH hcomm).trans c.toCx615.charTwo
    have hY2 : IsPGroup 2 Y := (pCoreOf_isPGroup 2 H).to_le hYO2
    have hYY : Y ≤ pCoreOf 2 Y := le_pCoreOf_of_le_normalizer le_rfl Subgroup.le_normalizer hY2
    rw [hOY] at hYY
    exact le_bot_iff.mp hYY
  have hNY : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Y
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
    ⟨pCoreOf 2 Y, hOY, pCoreOf_isPGroup 2 Y, rfl⟩
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    (sup_le hLY (hTH.trans hHY)).trans hNY
  exact c.hH.2.1 ((hHY.trans hNY).trans
    (le_of_isUniqueM_of_le_twoLocal (h.isUniqueM h432) hLT hloc))

end Cx615B

end CFSG.Quasithin.H13
