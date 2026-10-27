module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLeBasic
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIPushUp3
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIbGen
public import CFSG.GroupTheory.SteinbergBWAbelianProduct

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open CFSG.Quasithin.F53.Stellmacher.S43.Even
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_notLe_linear
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hU3 : VU3Big L1) (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hZ : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S) :
    ∃ g ∈ u3H L1 L2 S,
      Z1 L1 L2 S ⊔ conjSubgroup (Z1 L1 L2 S) g ⊔ Q2 L1 L2 S = u3H L1 L2 S ∧
      (2 ^ m) ^ 2 ≤ (Z1 L1 L2 S ⊓ conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S).relIndex
        ((Z1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ (conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S)) := by
  classical
  set Z : Subgroup G := Z1 L1 L2 S with hZdef
  set Q : Subgroup G := Q2 L1 L2 S with hQdef
  set H : Subgroup G := u3H L1 L2 S with hHdef
  have hm2 : 2 ≤ m := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q ≤ S := by
    rw [hQdef]
    exact F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hZS : Z ≤ S := (A4.omegaOneCenterOf_le (Q1 L1 L2 S)).trans hQ1S
  have hSbigB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hSP1 : S ≤ P1 L1 L2 S := hSbigB.trans hBP1
  have hSP2 : S ≤ P2 L1 L2 S := hSbigB.trans hBP2
  have hZP1 : Z ≤ P1 L1 L2 S := hZS.trans hSP1
  have hZP2 : Z ≤ P2 L1 L2 S := hZS.trans hSP2
  have hQP1 : Q ≤ P1 L1 L2 S := hQ2S.trans hSP1
  have hP1NZ : P1 L1 L2 S ≤ Subgroup.normalizer (Z : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))
  have hP2NQ : P2 L1 L2 S ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hQNZ : Q ≤ Subgroup.normalizer (Z : Set G) := hQP1.trans hP1NZ
  have hZNQ : Z ≤ Subgroup.normalizer (Q : Set G) := hZP2.trans hP2NQ
  have hHleP2 : H ≤ P2 L1 L2 S := by
    rw [hHdef]
    exact u3H_le_p2 L1 L2 S
  have hHNQ : H ≤ Subgroup.normalizer (Q : Set G) := hHleP2.trans hP2NQ
  have hZea : IsElemAbelian 2 Z := by
    rw [hZdef]
    exact SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  obtain ⟨-, hZrel⟩ := str86_z1_sup_q2_of_not_le hF hSB hB2 hm hZ
  obtain ⟨g, hgH, hgen⟩ := str86_caseIIb_generation hF.toW hSB hm2 hm hZS hZea hZrel
  refine ⟨g, hgH, hgen, ?_⟩
  set Zg : Subgroup G := conjSubgroup Z g with hZgdef
  set X : Subgroup G := Z ⊓ Q with hXdef
  set Xg : Subgroup G := Zg ⊓ Q with hXgdef
  set Y : Subgroup G := X ⊓ Xg with hYdef
  set W : Subgroup G := X ⊔ Xg with hWdef
  have hYleX : Y ≤ X := inf_le_left
  have hYleXg : Y ≤ Xg := inf_le_right
  have hXleW : X ≤ W := le_sup_left
  have hXgleW : Xg ≤ W := le_sup_right
  have hYleW : Y ≤ W := hYleX.trans hXleW
  have hXleQ : X ≤ Q := inf_le_right
  have hXgleQ : Xg ≤ Q := inf_le_right
  have hWleQ : W ≤ Q := sup_le hXleQ hXgleQ
  have hXleZ : X ≤ Z := inf_le_left
  have hXgleZg : Xg ≤ Zg := inf_le_left
  have hYleZ : Y ≤ Z := hYleX.trans hXleZ
  have hYleZg : Y ≤ Zg := hYleXg.trans hXgleZg
  have hXea : IsElemAbelian 2 X := hZea.mono hXleZ
  have hZgea : IsElemAbelian 2 Zg := by
    rw [hZgdef]
    exact hZea.map (MulAut.conj g⁻¹).toMonoidHom
  have hXgea : IsElemAbelian 2 Xg := hZgea.mono hXgleZg
  have hQNZg : Q ≤ Subgroup.normalizer (Zg : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq x' hx'
    have hq1 : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHNQ hgH) q).mp hq
    have hz : g * x' * g⁻¹ ∈ Z := (mem_conjSubgroup_iff).mp hx'
    have hconj : g * q * g⁻¹ * (g * x' * g⁻¹) * (g * q * g⁻¹)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hQNZ hq1) (g * x' * g⁻¹)).mp hz
    refine (mem_conjSubgroup_iff).mpr ?_
    rw [show g * (q * x' * q⁻¹) * g⁻¹ =
      (g * q * g⁻¹) * (g * x' * g⁻¹) * (g * q * g⁻¹)⁻¹ by group]
    exact hconj
  have hXgZX : ⁅Xg, Z⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x' hx' e he
    rw [commutatorElement_def]
    have hx'Q : x' ∈ Q := (Subgroup.mem_inf.mp hx').2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hP1NZ (hQP1 hx'Q)) e).mp he)
        (Z.inv_mem he)
    · have hconj : e * x'⁻¹ * e⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hZNQ he) x'⁻¹).mp (Q.inv_mem hx'Q)
      simpa [mul_assoc] using Q.mul_mem hx'Q hconj
  have hXZgXg : ⁅X, Zg⁆ ≤ Xg := by
    rw [Subgroup.commutator_le]
    intro x hx e' he'
    rw [commutatorElement_def]
    have hxQ : x ∈ Q := hXleQ hx
    have hz : g * e' * g⁻¹ ∈ Z := (mem_conjSubgroup_iff).mp he'
    have hgxg : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHNQ hgH) x).mp hxQ
    have h1 : ⁅g * x * g⁻¹, g * e' * g⁻¹⁆ ∈ Z := by
      rw [commutatorElement_def]
      exact Z.mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hP1NZ (hQP1 hgxg)) (g * e' * g⁻¹)).mp hz)
        (Z.inv_mem hz)
    have h2 : ⁅g * x * g⁻¹, g * e' * g⁻¹⁆ ∈ Q := by
      rw [commutatorElement_def]
      have hconj : g * e' * g⁻¹ * (g * x * g⁻¹)⁻¹ * (g * e' * g⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hZNQ hz) (g * x * g⁻¹)⁻¹).mp
          (Q.inv_mem hgxg)
      simpa [mul_assoc] using Q.mul_mem hgxg hconj
    have hcomm : x * e' * x⁻¹ * e'⁻¹ = g⁻¹ * ⁅g * x * g⁻¹, g * e' * g⁻¹⁆ * g := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_conjSubgroup_iff).mpr (by simpa [mul_assoc] using h1)
    · have hgQ : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hHNQ (H.inv_mem hgH)
      simpa using (Subgroup.mem_normalizer_iff.mp hgQ _).mp h2
  have hXXgY : ⁅X, Xg⁆ ≤ Y := by
    have h1 : ⁅X, Xg⁆ ≤ Xg := (Subgroup.commutator_mono le_rfl hXgleZg).trans hXZgXg
    have h2 : ⁅X, Xg⁆ ≤ X := by
      refine (Subgroup.commutator_mono hXleZ le_rfl).trans ?_
      rw [Subgroup.commutator_comm]
      exact hXgZX
    exact le_inf h2 h1
  have hXNXg : X ≤ Subgroup.normalizer (Xg : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (hXXgY.trans hYleXg)
  have hXgNX : Xg ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hXXgY.trans hYleX)
  obtain ⟨-, hWWY, -⟩ :=
    CFSG.GroupTheory.ZJ.mutually_normalizing_abelian_product (A := X) (D := Xg)
      hXea.1 hXgea.1 hXNXg hXgNX
  have hXXgY' : ∀ a ∈ X, ∀ b ∈ Xg, ⁅b, a⁆ ∈ Y := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ Y := Subgroup.commutator_le.mp hXXgY a ha b hb
    rw [← commutatorElement_inv]
    exact Y.inv_mem h1
  have hsqW : ∀ x ∈ W, x ^ 2 ∈ Y := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hXgNX).mp (show x ∈ X ⊔ Xg from hx)
    have hba : b * a = ⁅b, a⁆ * (a * b) := by
      rw [commutatorElement_def]
      group
    have hca : a * ⁅b, a⁆ = ⁅b, a⁆ * a :=
      CFSG.Open.IsElemAbelian.comm hZea (hXleZ ha) (hYleZ (hXXgY' a ha b hb))
    have h1 : (a * b) ^ 2 = ⁅b, a⁆ := by
      rw [pow_two]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (⁅b, a⁆ * (a * b)) * b := by rw [hba]
        _ = (a * ⁅b, a⁆ * a) * (b * b) := by group
        _ = (⁅b, a⁆ * (a * a)) * (b * b) := by rw [hca]; group
        _ = ⁅b, a⁆ := by
              rw [CFSG.Open.IsElemAbelian.mul_self_eq_one hXea ha,
                CFSG.Open.IsElemAbelian.mul_self_eq_one hXgea hb, mul_one, mul_one]
    rw [h1]
    exact hXXgY' a ha b hb
  have hQNX : Q ≤ Subgroup.normalizer (X : Set G) := by
    intro q hq
    exact A4.mem_normalizer_inf (hQNZ hq) (Subgroup.le_normalizer hq)
  have hQNXg : Q ≤ Subgroup.normalizer (Xg : Set G) := by
    intro q hq
    exact A4.mem_normalizer_inf (hQNZg hq) (Subgroup.le_normalizer hq)
  have hQNY : Q ≤ Subgroup.normalizer (Y : Set G) := by
    intro q hq
    exact A4.mem_normalizer_inf (hQNX hq) (hQNXg hq)
  have hZNW : Z ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz w hw
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hXgNX).mp (show w ∈ X ⊔ Xg from hw)
    have hza : z * a * z⁻¹ = a := by
      rw [CFSG.Open.IsElemAbelian.comm hZea hz (hXleZ ha), mul_inv_cancel_right]
    have hzb : z * b * z⁻¹ = ⁅z, b⁆ * b := by
      rw [commutatorElement_def]
      group
    have hcomm : ⁅z, b⁆ ∈ X := by
      have h1 : ⁅b, z⁆ ∈ X := Subgroup.commutator_le.mp hXgZX b hb z hz
      rw [← commutatorElement_inv]
      exact X.inv_mem h1
    rw [show z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) by group, hza, hzb]
    exact W.mul_mem (hXleW ha) (W.mul_mem (hXleW hcomm) (hXgleW hb))
  have hZgNW : Zg ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro z' hz' w hw
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hXgNX).mp (show w ∈ X ⊔ Xg from hw)
    have hz'a : z' * a * z'⁻¹ = ⁅z', a⁆ * a := by
      rw [commutatorElement_def]
      group
    have hz'b : z' * b * z'⁻¹ = b := by
      rw [CFSG.Open.IsElemAbelian.comm hZgea hz' (hXgleZg hb), mul_inv_cancel_right]
    have hcomm : ⁅z', a⁆ ∈ Xg := by
      have h1 : ⁅a, z'⁆ ∈ Xg := Subgroup.commutator_le.mp hXZgXg a ha z' hz'
      rw [← commutatorElement_inv]
      exact Xg.inv_mem h1
    rw [show z' * (a * b) * z'⁻¹ = (z' * a * z'⁻¹) * (z' * b * z'⁻¹) by group, hz'a, hz'b]
    exact W.mul_mem (W.mul_mem (hXgleW hcomm) (hXleW ha)) (hXgleW hb)
  have hQNW : Q ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq w hw
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hXgNX).mp (show w ∈ X ⊔ Xg from hw)
    have hqa : q * a * q⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hQNX hq) a).mp ha
    have hqb : q * b * q⁻¹ ∈ Xg := (Subgroup.mem_normalizer_iff.mp (hQNXg hq) b).mp hb
    rw [show q * (a * b) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) by group]
    exact W.mul_mem (hXleW hqa) (hXgleW hqb)
  have hHNW : H ≤ Subgroup.normalizer (W : Set G) := by
    have hH : H = Z ⊔ Zg ⊔ Q := hgen.symm
    rw [hH]
    exact sup_le (sup_le hZNW hZgNW) hQNW
  have hZNY : Z ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz y hy
    rw [CFSG.Open.IsElemAbelian.comm hZea hz (hYleZ hy), mul_inv_cancel_right]
    exact hy
  have hZgNY : Zg ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro z' hz' y hy
    rw [CFSG.Open.IsElemAbelian.comm hZgea hz' (hYleZg hy), mul_inv_cancel_right]
    exact hy
  have hHNY : H ≤ Subgroup.normalizer (Y : Set G) := by
    have hH : H = Z ⊔ Zg ⊔ Q := hgen.symm
    rw [hH]
    exact sup_le (sup_le hZNY hZgNY) hQNY
  have hW2 : IsPGroup 2 W := (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le hWleQ
  have hsec : CFSG.Quasithin.F53Mod.IsSec H Y W :=
    { le := hYleW
      normN := hHNW
      normL := hHNY
      comm := fun x hx y hy => by
        simpa [commutatorElement_def, hYdef] using
          Subgroup.commutator_le.mp hWWY x hx y hy
      sq := hsqW }
  have hCY : oTwoUpper H ≤ Subgroup.centralizer (Y : Set G) := by
    refine CFSG.Quasithin.Vol2.Ch11.SecD.oTwoUpper_le_of_le_sup' (X := H)
      (Y := Subgroup.centralizer (Y : Set G)) (T := Q) ?_
      (pCoreOf_isPGroup 2 (P2 L1 L2 S)) ?_
    · have hH : H = Z ⊔ Zg ⊔ Q := hgen.symm
      rw [hH]
      refine sup_le (sup_le ?_ ?_) le_sup_right
      · refine le_sup_of_le_left ?_
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact CFSG.Open.IsElemAbelian.comm hZea (hYleZ hy) hz
      · refine le_sup_of_le_left ?_
        intro z' hz'
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact CFSG.Open.IsElemAbelian.comm hZgea (hYleZg hy) hz'
    · exact hQNY.trans (F7.normalizer_le_normalizer_centralizer Y)
  have hnot : ¬ ⁅W, oTwoRes H⁆ ≤ Y := by
    intro hle
    have hle' : ⁅W, oTwoUpper H⁆ ≤ Y := by
      rwa [CFSG.Quasithin.oTwoRes_eq_oTwoUpper] at hle
    have hbot : ⁅oTwoUpper H, W⁆ = ⊥ := by
      have h := A4.commutator_le_of_oTwoUpper (A := oTwoUpper H) (N := ⊥) (B := Y) (D := W)
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        hYleW
        (fun d hd => by
          obtain ⟨j, hj⟩ := hW2 ⟨d, hd⟩
          exact ⟨j, by rw [Subgroup.mem_bot]; simpa using congrArg Subtype.val hj⟩)
        (by rw [Subgroup.commutator_comm]; exact hle')
        (by rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hCY)
      rw [A4.oTwoUpper_oTwoUpper] at h
      exact le_bot_iff.mp h
    have hO2NX : oTwoUpper H ≤ Subgroup.normalizer (X : Set G) := by
      refine Subgroup.le_normalizer_iff_commutator_le_right.mpr ?_
      calc ⁅oTwoUpper H, X⁆ ≤ ⁅oTwoUpper H, W⁆ := Subgroup.commutator_mono le_rfl hXleW
        _ = ⊥ := hbot
        _ ≤ X := bot_le
    have hBNX : bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G) := by
      intro b hb
      exact A4.mem_normalizer_inf (hP1NZ (hBP1 hb)) (hP2NQ (hBP2 hb))
    have hL2NX : L2 ≤ Subgroup.normalizer (X : Set G) := by
      have hLH : L2 ≤ H := by rw [hHdef]; exact le_sup_left
      have hsup : H = oTwoUpper H ⊔ Q := by
        rw [hHdef, hQdef]
        exact str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hm2 hm
      rw [hsup] at hLH
      exact hLH.trans (sup_le hO2NX hQNX)
    have hP2NX : P2 L1 L2 S ≤ Subgroup.normalizer (X : Set G) :=
      sup_le hL2NX hBNX
    exact str86_false_of_pushUp hF.toW hSB (Or.inr hU3) hB2 ⟨m, hm⟩ (P := Z)
      hZea.isPGroup hZP1 hP1NZ hZ hP2NX
  obtain ⟨L', N', hLL', hN'W, hstep, hnc⟩ :=
    exists_noncentral_of_not_le (X := H) (U := Q) (L := Y) (N := W) hsec hWleQ hnot
  have hbound : (2 ^ m) ^ 2 ≤ L'.relIndex N' :=
    str86_card_chiefStep_ge hF.toW hm2 hm hstep hnc
  have hidx1 : L'.relIndex N' ≤ L'.relIndex W :=
    Subgroup.relIndex_le_of_le_right hN'W (D15Proof.relIndex_ne_zero L' W)
  have hidx2 : L'.relIndex W ≤ Y.relIndex W :=
    Subgroup.relIndex_le_of_le_left hLL' (D15Proof.relIndex_ne_zero Y W)
  have hfinal : (2 ^ m) ^ 2 ≤ Y.relIndex W := hbound.trans (hidx1.trans hidx2)
  have hYgoal : Y = Z ⊓ Zg ⊓ Q := by
    rw [hYdef, hXdef, hXgdef]
    ac_rfl
  rw [hYgoal] at hfinal
  exact hfinal

end CFSG.Quasithin.Stroth

end
