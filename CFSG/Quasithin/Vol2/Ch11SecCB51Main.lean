module

public import CFSG.Quasithin.Vol2.Ch11SecCB51Cases
public import CFSG.Quasithin.Background.InternalSecB56B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
open CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace B51

variable {T L I : Subgroup G} {n : ℕ} {Y W : Subgroup G}

theorem ffModule_structure_of_b51Hyp (h51 : AsB51) (h1102 : Stmt11_0_2)
    (hKF : KindModuleFacts) (h : BridgeHyp T L I n Y W) [IsMulCommutative ↥W]
    {J : Subgroup (MulAut ↥W)} (hB : B51Hyp J (autOn L W)) {U : Subgroup G}
    (hU : ⁅W, L⁆ = U) :
    ∃ _ : IsMulCommutative ↥U,
      (KindSL3 L (fsuV T I) n ∧ BinaryNaturalSL (V := ↥U) (autOn L U) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf U) 3 n) ∨
      (KindSp4 L (fsuV T I) n ∧ BinaryNaturalSp4 (V := ↥U) (autOn L U) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf U) n) ∨
      (KindG2 L (fsuV T I) n ∧ G2Natural (V := ↥U) (autOn L U) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf U) n) ∨
      (KindSL3 L (fsuV T I) n ∧ U ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        SumTwoNatural L U n) := by
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using h.isElemAbelian.2 w w.2)
  obtain ⟨-, hcases⟩ := (h51 ↥W hW2 J (autOn L W) hB).1
  rcases hcases with hi | hii | ⟨m, hiii⟩ | hiv
  · obtain ⟨hc, hd⟩ := natural_of_case1i h1102 hKF h hi hU
    exact ⟨hc, hd.imp_right fun hd => hd.imp_right Or.inl⟩
  · obtain ⟨hk, hC, hS⟩ := sumTwoNatural_of_case1ii h1102 hKF h hii hU
    have hUW : U ≤ W := by
      rw [← hU, ← map_commV_autOn h.le_normW]
      exact Subgroup.map_subtype_le _
    exact ⟨isMulCommutative_of_le hUW, Or.inr (Or.inr (Or.inr ⟨hk, hC, hS⟩))⟩
  · exact (not_case1iii h1102 hKF.2.2.2 h hiii).elim
  · exact (not_case1iv h1102 hKF.2.2.2 h hiv).elim

theorem fsuV_ne_bot (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder)
    (hyp : Hyp11 G T L I n) : fsuV T I ≠ ⊥ := by
  intro hV
  have hall : autOn L (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro σ _
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun v => Subtype.ext ?_
    have h1 : (v : G) ∈ (⊥ : Subgroup G) := by rw [← hV]; exact v.2
    have h2 : ((σ v : ↥(fsuV T I)) : G) ∈ (⊥ : Subgroup G) := by rw [← hV]; exact (σ v).2
    rw [Subgroup.mem_bot] at h1 h2
    rw [MulAut.one_apply, h2, h1]
  have hc : Nat.card ↥(autOn L (fsuV T I)) = 1 := by rw [hall]; exact Subgroup.card_bot
  have hn : 2 ≤ n := hyp.one_lt
  have hlt : ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, 2 ^ k * m = 1 → False := by
    intro k hk m hm
    have h2 : 2 ^ k ∣ 1 := hm ▸ Dvd.intro _ rfl
    have := Nat.le_of_dvd one_pos h2
    have := Nat.one_lt_two_pow (n := k) (by omega)
    omega
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n hyp
  rcases hk with ⟨F, _, _, hF, ⟨e⟩, -⟩ | ⟨F, _, _, hF, ⟨e⟩, -⟩ | ⟨F, _, _, hF, ⟨e⟩, -⟩
  · rw [Nat.card_congr e.toEquiv, card_SL3_eq_pow hF] at hc
    exact hlt _ (by omega) _ hc
  · rw [Nat.card_congr e.toEquiv, card_Sp4_eq_pow hF] at hc
    exact hlt _ (by omega) _ hc
  · rw [Nat.card_congr e.toEquiv, card_G2_eq_pow hG2 hn hF] at hc
    exact hlt _ (by omega) _ hc

theorem commutator_fsuV_eq' (hyp : Hyp11 G T L I n) :
    ⁅fsuV T I, L⁆ = fsuV T I := by
  have hL := SecA.L_le_normalizer_fsuV hyp
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    have h1 : l * v⁻¹ * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (hL hl) v⁻¹).mp ((fsuV T I).inv_mem hv)
    rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact (fsuV T I).mul_mem hv h1
  · have hI : ⁅I, L⁆ = I := by
      have := hyp.fsu.irrPlus.2.2.2.1
      rwa [SecA.conjClosure_eq_self hyp] at this
    refine conjClosure_le fun t ht z hz => ?_
    have htL : t ∈ Subgroup.normalizer (L : Set G) := hyp.normal ht
    have h1 : (⁅I, L⁆).map (MulAut.conj t).toMonoidHom ≤ ⁅fsuV T I, L⁆ := by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer htL]
      refine Subgroup.commutator_mono (Subgroup.map_le_iff_le_comap.mpr fun i hi => ?_) le_rfl
      show t * i * t⁻¹ ∈ fsuV T I
      exact mem_conjClosure ht hi
    rw [hI] at h1
    exact h1 ⟨z, hz, by simp⟩

theorem commutator_VM_eq (hyp : Hyp11 G T L I n) : ⁅VM T L I, L⁆ = VM T L I := by
  have hV := commutator_fsuV_eq' hyp
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    have hlN : l ∈ Subgroup.normalizer ((VM T L I : Subgroup G) : Set G) :=
      le_normalizer_conjClosure _ _ (Subgroup.le_normalizer hl)
    have h1 : l * v⁻¹ * l⁻¹ ∈ VM T L I :=
      (Subgroup.mem_normalizer_iff.mp hlN v⁻¹).mp ((VM T L I).inv_mem hv)
    rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact (VM T L I).mul_mem hv h1
  · refine conjClosure_le fun m hm z hz => ?_
    have h1 : (⁅fsuV T I, L⁆).map (MulAut.conj m).toMonoidHom ≤ ⁅VM T L I, L⁆ := by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hm]
      refine Subgroup.commutator_mono (Subgroup.map_le_iff_le_comap.mpr fun i hi => ?_) le_rfl
      show m * i * m⁻¹ ∈ VM T L I
      exact mem_conjClosure hm hi
    rw [hV] at h1
    exact h1 ⟨z, hz, by simp⟩

namespace BridgeHyp

variable (h : BridgeHyp T L I n Y W)
include h

theorem b51Hyp_of_b56 [IsMulCommutative ↥W] (h56 : AsB56) (h1102 : Stmt11_0_2)
    (hJ : L = ⁅L, thompsonJ T⁆) (hWL : ⁅W, L⁆ = W) :
    B51Hyp (ffJ (autOn Y W)) (autOn L W) := by
  have hW1 : W ≠ ⊥ := hWL ▸ h.comm_ne
  have := h.hyp.fsu.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.hyp.fsu.nonabelian h.hyp.fsu.qtke).1
  have hWn : (W.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.red.1).2 h.normW
  have hWO : W ≤ pCoreOf 2 Y :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 W Y h.red.1 hWn
      (B6.isPGroup_of_isElemAbelian h.isElemAbelian)
  have hSY : SQTKGroup ↥Y :=
    sqtkGroup_of_localSQTK hloc fun h0 => hW1 (le_bot_iff.mp (h0 ▸ hWO))
  obtain ⟨A, -, hA, hLA⟩ := h.exists_offender hJ
  exact (b51Hyp_ffJ_autOn_of_b56_of_commutator h56 h.isElemAbelian.2 h.normW h.le_Y h.normL hSY
    h.pCoreOf_autOn_Y h.isQuasisimple (h.sqtkGroup h1102) hA hLA hWL).1

theorem eq_of_case1i [IsMulCommutative ↥W] (h1102 : Stmt11_0_2) (hG2 : SecA.FactG2DerivedOrder)
    {J : Subgroup (MulAut ↥W)} (hi : B51Case1i J (autOn L W)) (hWL : ⁅W, L⁆ = W) :
    fsuV T I = W := by
  have hLW := h.le_normW
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h.hyp
  have hV := commutator_fsuV_eq' h.hyp
  have hV1 := fsuV_ne_bot h1102 hG2 h.hyp
  have hirr := hi.1.2.2.2
  have hcomm : commV (autOn L W) = ⊤ := by
    rw [commV_autOn hLW, hWL, Subgroup.subgroupOf_self]
  rw [hcomm] at hirr
  set Vs : Subgroup ↥W := (fsuV T I).subgroupOf W with hVs
  set C : Subgroup ↥W := XMod.fixed ↥(autOn L W) (⊤ : Subgroup ↥W) with hC
  have hinv : XMod.IsInv ↥(autOn L W) (Vs ⊔ C) := by
    intro a x hx
    have hle : Vs ⊔ C ≤ (Vs ⊔ C).comap (a : MulAut ↥W).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · apply Subgroup.mem_sup_left
        obtain ⟨g, hgL, hg⟩ := Setup.mem_autOn_iff.1 a.2
        show (a : MulAut ↥W) y ∈ Vs
        rw [← hg, Subgroup.mem_subgroupOf, coe_conjAct_apply]
        exact (Subgroup.mem_normalizer_iff.mp (hLV hgL) y).mp hy
      · apply Subgroup.mem_sup_right
        show (a : MulAut ↥W) y ∈ C
        have hya : a • y = y := hy.2 a
        rw [show (a : MulAut ↥W) y = a • y from rfl, hya]
        exact hy
    exact hle hx
  have hfix : ∀ x : ↥W, x ∈ C → ∀ l ∈ L, l * (x : G) = (x : G) * l := by
    intro x hx l hl
    have h2 : ((conjAct W ⟨l, hLW hl⟩ x : ↥W) : G) = x :=
      congrArg Subtype.val (hx.2 ⟨conjAct W ⟨l, hLW hl⟩, conjAct_mem_autOn hLW hl⟩)
    rw [coe_conjAct_apply] at h2
    change l * (x : G) * l⁻¹ = x at h2
    calc l * (x : G) = l * x * l⁻¹ * l := by group
      _ = x * l := by rw [h2]
  rcases hirr.2 (Vs ⊔ C) hinv le_sup_right le_top with h1 | h1
  · exfalso
    apply hV1
    rw [← hV, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l hl
    have hvC : (⟨v, h.fsuV_le hv⟩ : ↥W) ∈ C :=
      h1 ▸ Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hv)
    have hc := hfix _ hvC l hl
    rw [Subgroup.mem_bot, commutatorElement_def]
    change v * l * v⁻¹ * l⁻¹ = 1
    rw [← hc]
    group
  · refine le_antisymm h.fsuV_le ?_
    rw [← hWL, Subgroup.commutator_le]
    intro w hw l hl
    have hw' : (⟨w, hw⟩ : ↥W) ∈ Vs ⊔ C := h1 ▸ Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hw'
    have hzl := hfix z hz l hl
    have hwyz : w = (y : G) * z := congrArg Subtype.val hyz.symm
    have hyV : (y : G) ∈ fsuV T I := hy
    rw [hwyz, commutatorElement_def]
    have e : (y : G) * z * l * ((y : G) * z)⁻¹ * l⁻¹ = (y : G) * (l * (y : G)⁻¹ * l⁻¹) := by
      rw [mul_inv_rev, mul_assoc (y : G) z l, ← hzl]
      group
    rw [e]
    exact (fsuV T I).mul_mem hyV
      ((Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp ((fsuV T I).inv_mem hyV))

end BridgeHyp

end B51

end CFSG.Quasithin.Vol2.Ch11.SecC
