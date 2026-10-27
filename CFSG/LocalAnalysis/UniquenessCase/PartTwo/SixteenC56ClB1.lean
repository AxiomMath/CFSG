module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Fix
public import CFSG.LocalAnalysis.WeakClosure81.SixTwo
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveA
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G]

structure C33Hyp (M V : Subgroup G) (g : G) : Prop where
  mQuot_le : E3.mQuot (conjSubgroup V g) (BOf M V g) ≤ 2
  not_le : ¬ BOf M V g ≤ Subgroup.centralizer (V : Set G)

structure C33Core (M V : Subgroup G) (g : G) : Prop where
  not_conjV_le_M : ¬ conjSubgroup V g ≤ M
  mQuot_U : E3.mQuot V (conjSubgroup M g) ≤ 2
  comm_ne : ¬ UOf M V g ≤ Subgroup.centralizer (conjSubgroup V g : Set G)

@[expose] def c33Pull {V : Subgroup G} (hV : IsElemAbelian 2 V) (X : Subgroup G) :
    Subgroup (IntMod V hV) where
  carrier := {w | w.val ∈ X}
  one_mem' := X.one_mem
  mul_mem' := fun {_ _} ha hb => X.mul_mem ha hb
  inv_mem' := fun {_} ha => X.inv_mem ha

theorem mem_c33Pull {V : Subgroup G} {hV : IsElemAbelian 2 V} {X : Subgroup G}
    {w : IntMod V hV} : w ∈ c33Pull hV X ↔ w.val ∈ X := Iff.rfl

@[expose] def c33Sub {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* V where
  toFun w := ⟨w.val, w.val_mem⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem c33Sub_surjective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Surjective (c33Sub hV) := fun v => ⟨IntMod.mk hV v, rfl⟩

theorem index_c33Pull {V : Subgroup G} (hV : IsElemAbelian 2 V) (X : Subgroup G) :
    (c33Pull hV X).index = X.relIndex V := by
  have h : c33Pull hV X = (X.subgroupOf V).comap (c33Sub hV) := rfl
  rw [h, Subgroup.index_comap_of_surjective _ (c33Sub_surjective hV)]
  rfl

theorem mQuot_le_two_of_index_le {V : Subgroup G} [Finite G] (hV : IsElemAbelian 2 V)
    {X : Subgroup G} (h : (c33Pull hV X).index ≤ 4) : E3.mQuot V X ≤ 2 := by
  have h1 := E3.relIndex_eq_two_pow (CFSG.Open.IsElemAbelian.isPGroup hV) X
  rw [index_c33Pull, h1] at h
  by_contra hlt
  push Not at hlt
  have h8 : 2 ^ 3 ≤ 2 ^ E3.mQuot V X := Nat.pow_le_pow_right (by norm_num) hlt
  omega

section Core

variable [Finite G] {M V : Subgroup G} {g : G}

theorem c33_BOf_le_normalizer (hS : C33Setting M V) :
    BOf M V g ≤ Subgroup.normalizer (V : Set G) := by
  rw [hS.normalizer_eq]
  exact inf_le_right

theorem c33_mQuot_eq_two (hS : C33Setting M V) (hh : C33Hyp M V g) :
    E3.mQuot (conjSubgroup V g) (BOf M V g) = 2 := by
  by_contra hne
  have hle : E3.mQuot (conjSubgroup V g) (BOf M V g) ≤ 1 := by
    have := hh.mQuot_le
    omega
  have hmem : BOf M V g ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) (BOf M V g)) M :=
    ⟨inf_le_right, g, inf_le_left, rfl⟩
  exact hh.not_le (hS.gamma_le _ hle _ hmem)

theorem c33_B_mem_gammaSet (hS : C33Setting M V) (hh : C33Hyp M V g) :
    BOf M V g ∈ E3.gammaSet V 2 M :=
  ⟨inf_le_right, g, inf_le_left, c33_mQuot_eq_two hS hh⟩

theorem c33_E_mem_aSet (hS : C33Setting M V) (hh : C33Hyp M V g) :
    autI hS.elemAbelian (BOf M V g) ∈ E3.aSet 2 (autI hS.elemAbelian ⊤) :=
  hS.aSet_two _ (c33_B_mem_gammaSet hS hh) hh.not_le

theorem c33_dichotomy (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    E3.gammaCheck 2 (autI hS.elemAbelian (BOf M V g)) = ⊤ ∨
      SingLineShape (autI hS.elemAbelian (BOf M V g)) := by
  obtain ⟨S, hSK, hSN⟩ := hS.orth
  exact hgeo S hSK hSN (c33_E_mem_aSet hS hh)

theorem c33_fixV_le_gammaCheck {W : Type} [CommGroup W] [Finite W] (E : Subgroup (MulAut W))
    (k : ℕ) : fixV E ≤ E3.gammaCheck k E :=
  le_iSup_of_le E (le_iSup_of_le le_rfl (le_iSup_of_le (by rw [E3.mQuot_self]; exact Nat.zero_le _)
    le_rfl))

theorem c33_gammaCheck_le (hS : C33Setting M V) (hm : E3.mQuot (conjSubgroup V g) (BOf M V g) ≤ 2) :
    E3.gammaCheck 2 (autI hS.elemAbelian (BOf M V g)) ≤
      c33Pull hS.elemAbelian (conjSubgroup M g) := by
  have hV := hS.elemAbelian
  have hBN : BOf M V g ≤ Subgroup.normalizer (V : Set G) := c33_BOf_le_normalizer hS
  unfold E3.gammaCheck
  refine iSup_le fun D => iSup_le fun hD => iSup_le fun hDm => ?_
  intro w hw
  rw [mem_c33Pull]
  have hD'B : preI hV (BOf M V g) hBN D ≤ BOf M V g := preI_le hV
  have hautD : autI hV (preI hV (BOf M V g) hBN D) = D := autI_preI hV hD
  have hm1 : E3.mQuot (BOf M V g) (preI hV (BOf M V g) hBN D) ≤ 2 := by
    rw [← E3.mQuot_autI_preI hV hBN hD]
    exact hDm
  have hBV : BOf M V g ≤ conjSubgroup V g := inf_le_left
  have hD'V : preI hV (BOf M V g) hBN D ≤ conjSubgroup V g := hD'B.trans hBV
  have hadd := E3.mQuot_add hD'B hBV
  have hlt : (E3.mQuot (conjSubgroup V g) (preI hV (BOf M V g) hBN D) : ℕ∞) <
      rMV (conjSubgroup M g) (conjSubgroup V g) := by
    rw [rMV_conj hS.normalizer_eq g]
    refine lt_of_le_of_lt ?_ hS.lt_rMV
    exact_mod_cast (by omega : E3.mQuot (conjSubgroup V g) (preI hV (BOf M V g) hBN D) ≤ 4)
  have hC := centralizer_le_of_mQuot_lt_rMV hD'V hlt
  have hw' : w.val ∈ Subgroup.centralizer ((preI hV (BOf M V g) hBN D : Subgroup G) : Set G) := by
    rw [← mem_fixV_autI hV (hD'B.trans hBN), hautD]
    exact hw
  exact hC hw'

theorem c33_mQuot_U (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    E3.mQuot V (conjSubgroup M g) ≤ 2 := by
  have hV := hS.elemAbelian
  have hT1 := c33_gammaCheck_le hS hh.mQuot_le
  have hidx : (E3.gammaCheck 2 (autI hV (BOf M V g))).index ≤ 4 := by
    rcases c33_dichotomy hgeo hS hh with h | h
    · rw [h, Subgroup.index_top]
      norm_num
    · exact h.index_le
  have h1 : (c33Pull hV (conjSubgroup M g)).index ∣
      (E3.gammaCheck 2 (autI hV (BOf M V g))).index := Subgroup.index_dvd_of_le hT1
  exact mQuot_le_two_of_index_le hV
    (le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1) hidx)

theorem c33_comm_ne (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    ¬ UOf M V g ≤ Subgroup.centralizer (conjSubgroup V g : Set G) := by
  intro hU
  have hV := hS.elemAbelian
  have hBN : BOf M V g ≤ Subgroup.normalizer (V : Set G) := c33_BOf_le_normalizer hS
  have hT1 := c33_gammaCheck_le hS hh.mQuot_le
  have hle : E3.gammaCheck 2 (autI hV (BOf M V g)) ≤ fixV (autI hV (BOf M V g)) := by
    intro w hw
    rw [mem_fixV_autI hV hBN]
    have hwU : w.val ∈ UOf M V g := Subgroup.mem_inf.2 ⟨w.val_mem, hT1 hw⟩
    exact Subgroup.centralizer_le (fun x hx => (inf_le_left : BOf M V g ≤ conjSubgroup V g) hx)
      (hU hwU)
  have heq : E3.gammaCheck 2 (autI hV (BOf M V g)) = fixV (autI hV (BOf M V g)) :=
    le_antisymm hle (c33_fixV_le_gammaCheck _ 2)
  have hne : autI hV (BOf M V g) ≠ ⊥ := (c33_E_mem_aSet hS hh).2.1
  rcases c33_dichotomy hgeo hS hh with htop | hshape
  · rw [heq] at htop
    exact fixV_ne_top hne htop
  · apply hshape.fix_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    obtain ⟨e, he, u, hu, rfl⟩ := hshape.fix_le_comm f hf
    rw [heq] at hu
    rw [mem_fixV.1 hu e he, mul_inv_cancel]

theorem c33_core (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g) :
    C33Core M V g where
  not_conjV_le_M := fun h => by
    have h2 := c33_mQuot_eq_two hS hh
    have : BOf M V g = conjSubgroup V g := inf_eq_left.2 h
    rw [this, E3.mQuot_self] at h2
    omega
  mQuot_U := c33_mQuot_U hgeo hS hh
  comm_ne := c33_comm_ne hgeo hS hh

end Core

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
