module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedLemma11

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def Str86YCommBridge (L1 L2 S : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ S → E ⊔ Q2 L1 L2 S = S →
    ⁅u3Y L1 L2 S, E⁆ = Z1 L1 L2 S

private theorem q1_commutes_z1 {L1 L2 S : Subgroup G} :
    Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : z ∈ centerOf (Q1 L1 L2 S) := A4.omegaOneCenterOf_le_centerOf (Q1 L1 L2 S) hz
  have hzc : z ∈ Subgroup.centralizer (Q1 L1 L2 S : Set G) := (Subgroup.mem_inf.mp hz').2
  exact ((Subgroup.mem_centralizer_iff.mp hzc) q hq).symm

private theorem y_commutative {L1 L2 S : Subgroup G} :
    ∀ a ∈ u3Y L1 L2 S, ∀ b ∈ u3Y L1 L2 S, a * b = b * a := by
  intro a ha b hb
  have haZ : a ∈ Z2 L1 L2 S := (Subgroup.mem_inf.mp ha).1
  have hbZ : b ∈ Z2 L1 L2 S := (Subgroup.mem_inf.mp hb).1
  have hbQ : b ∈ Q2 L1 L2 S := (omegaOneCenterOf_le (Q2 L1 L2 S)) hbZ
  have haz : a ∈ centerOf (Q2 L1 L2 S) := A4.omegaOneCenterOf_le_centerOf (Q2 L1 L2 S) haZ
  have hac : a ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) := (Subgroup.mem_inf.mp haz).2
  exact ((Subgroup.mem_centralizer_iff.mp hac) b hbQ).symm

private theorem l1_commutes_z1 {L1 L2 S : Subgroup G}
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    L1 ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
  le_sup_left.trans hZI

private theorem x1_generator_commutes_q1
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hbridge : Str86YCommBridge L1 L2 S)
    (hQ1sup : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {h y : G} (hh : h ∈ L1) (hy : y ∈ u3Y L1 L2 S) (q : G) (hq : q ∈ Q1 L1 L2 S) :
    ⁅h * y * h⁻¹, q⁆ ∈ Z1 L1 L2 S := by
  have hP1 : h ∈ P1 L1 L2 S := (le_sup_left : L1 ≤ P1 L1 L2 S) hh
  have hN : h ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hP1
  have hNin : h⁻¹ ∈ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    (Subgroup.normalizer (Q1 L1 L2 S : Set G)).inv_mem hN
  have hq' : h⁻¹ * q * h ∈ Q1 L1 L2 S := by
    simpa using (Subgroup.mem_normalizer_iff.mp hNin q).mp hq
  have hYQ : ⁅u3Y L1 L2 S, Q1 L1 L2 S⁆ = Z1 L1 L2 S :=
    hbridge (Q1 L1 L2 S)
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)) hQ1sup
  have hmem : ⁅y, h⁻¹ * q * h⁆ ∈ Z1 L1 L2 S := by
    rw [← hYQ]
    exact Subgroup.commutator_mem_commutator hy hq'
  have hconj : h * ⁅y, h⁻¹ * q * h⁆ * h⁻¹ = ⁅y, h⁻¹ * q * h⁆ := by
    have hc : h ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      (l1_commutes_z1 hZI) hh
    have hc' : h * ⁅y, h⁻¹ * q * h⁆ = ⁅y, h⁻¹ * q * h⁆ * h :=
      ((Subgroup.mem_centralizer_iff.mp hc) _ hmem).symm
    rw [hc', mul_assoc, mul_inv_cancel, mul_one]
  rw [show ⁅h * y * h⁻¹, q⁆ = h * ⁅y, h⁻¹ * q * h⁆ * h⁻¹ by
    simp only [commutatorElement_def]; group]
  rw [hconj]
  exact hmem

private theorem x1_generators_commute
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hbridge : Str86YCommBridge L1 L2 S)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {h1 h2 y1 y2 : G} (hh1 : h1 ∈ L1) (hh2 : h2 ∈ L1)
    (hy1 : y1 ∈ u3Y L1 L2 S) (hy2 : y2 ∈ u3Y L1 L2 S) :
    ⁅h1 * y1 * h1⁻¹, h2 * y2 * h2⁻¹⁆ ∈ Z1 L1 L2 S := by
  let g : G := h1⁻¹ * h2
  have hgL : g ∈ L1 := L1.mul_mem (L1.inv_mem hh1) hh2
  have hgS : g ∈ L1 ⊔ S := (le_sup_left : L1 ≤ L1 ⊔ S) hgL
  have hcomm_eq : ⁅h1 * y1 * h1⁻¹, h2 * y2 * h2⁻¹⁆ =
      h1 * ⁅y1, g * y2 * g⁻¹⁆ * h1⁻¹ := by
    simp only [commutatorElement_def]
    dsimp only [g]
    group
  by_cases hgB : g ∈ bigB L1 L2 S
  ·
    have hgy : g * y2 * g⁻¹ ∈ u3Y L1 L2 S := by
      have hN : g ∈ Subgroup.normalizer (u3Y L1 L2 S : Set G) :=
        bigB_le_normalizer_u3Y (L1 := L1) (L2 := L2) (S := S) hgB
      exact (Subgroup.mem_normalizer_iff.mp hN y2).mp hy2
    have hone : ⁅y1, g * y2 * g⁻¹⁆ = 1 := by
      have hc := y_commutative y1 hy1 (g * y2 * g⁻¹) hgy
      rw [commutatorElement_def, hc]
      group
    rw [hcomm_eq, hone, mul_one, mul_inv_cancel]
    exact (Z1 L1 L2 S).one_mem
  ·
    let Yg : Subgroup G := MulAut.conj g • u3Y L1 L2 S
    have hYgS : Yg ≤ S :=
      (str86_u3Y_conj_le_q1 (L1 := L1) (L2 := L2) (S := S) hgS).trans
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW))
    have hYgSup : Yg ⊔ Q2 L1 L2 S = S :=
      str86_u3Y_conj_sup_q2 hF hSB hk hFc hU3 hn hL2 hZQ hgS hgB
    have hYgComm : ⁅u3Y L1 L2 S, Yg⁆ = Z1 L1 L2 S := hbridge Yg hYgS hYgSup
    have hgy : g * y2 * g⁻¹ ∈ Yg := by
      change g * y2 * g⁻¹ ∈ (u3Y L1 L2 S).map (MulAut.conj g).toMonoidHom
      refine Subgroup.mem_map.mpr ⟨y2, hy2, ?_⟩
      exact (MulAut.conj_apply g y2).symm
    have hinner : ⁅y1, g * y2 * g⁻¹⁆ ∈ Z1 L1 L2 S := by
      rw [← hYgComm]
      exact Subgroup.commutator_mem_commutator hy1 hgy
    have hconj : h1 * ⁅y1, g * y2 * g⁻¹⁆ * h1⁻¹ = ⁅y1, g * y2 * g⁻¹⁆ := by
      have hc : h1 ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        (l1_commutes_z1 hZI) hh1
      have hc' : h1 * ⁅y1, g * y2 * g⁻¹⁆ = ⁅y1, g * y2 * g⁻¹⁆ * h1 :=
        ((Subgroup.mem_centralizer_iff.mp hc) _ hinner).symm
      rw [hc', mul_assoc, mul_inv_cancel, mul_one]
    rw [hcomm_eq, hconj]
    exact hinner

private theorem q1_sup_q2_eq_s
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    Q1 L1 L2 S ⊔ Q2 L1 L2 S = S := by
  obtain ⟨c, hser⟩ := exists_isChiefSeriesFrom_u3X1 (L1 := L1) (L2 := L2) (S := S) hF
  have hX1Q2 : u3X1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_u3X1_sup_q2 hF hSB hk hFc hU3 hn hL2 hZQ hser
  refine le_antisymm
    (sup_le
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW))
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW))) ?_
  calc S = u3X1 L1 L2 S ⊔ Q2 L1 L2 S := hX1Q2.symm
    _ ≤ Q1 L1 L2 S ⊔ Q2 L1 L2 S :=
        sup_le (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S) |>.trans le_sup_left) le_sup_right

private theorem str86_X1_Q1_le_z1_of_bridge
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hbridge : Str86YCommBridge L1 L2 S) :
    ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
  let Gens : Set G := {x | ∃ h ∈ L1, ∃ y ∈ u3Y L1 L2 S, h * y * h⁻¹ = x}
  have hXeq : u3X1 L1 L2 S = Subgroup.closure Gens := rfl
  have hQ1sup : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
    q1_sup_q2_eq_s hF hSB hk hFc hU3 hn hL2 hZQ
  have hXK : Subgroup.closure Gens ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
    rw [← hXeq]
    exact u3X1_le_q1.trans (q1_commutes_z1 (L1 := L1) (L2 := L2) (S := S))
  rw [hXeq, ← Subgroup.closure_eq (Q1 L1 L2 S)]
  refine TauCeti.commutator_closure_closure_le
    (hXK.trans (Subgroup.centralizer_le_normalizer (s := (Z1 L1 L2 S : Set G))))
    (by
      rw [Subgroup.closure_eq]
      exact (q1_commutes_z1 (L1 := L1) (L2 := L2) (S := S)).trans
        (Subgroup.centralizer_le_normalizer (s := (Z1 L1 L2 S : Set G)))) ?_
  intro a ha q hq
  obtain ⟨h, hh, y, hy, rfl⟩ := ha
  exact x1_generator_commutes_q1 hF hbridge hQ1sup hZI hh hy q hq

private theorem str86_X1_derived_le_z1_of_bridge
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hbridge : Str86YCommBridge L1 L2 S) :
    ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
  let Gens : Set G := {x | ∃ h ∈ L1, ∃ y ∈ u3Y L1 L2 S, h * y * h⁻¹ = x}
  have hXeq : u3X1 L1 L2 S = Subgroup.closure Gens := rfl
  have hXK : Subgroup.closure Gens ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
    rw [← hXeq]
    exact u3X1_le_q1.trans (q1_commutes_z1 (L1 := L1) (L2 := L2) (S := S))
  rw [hXeq]
  have hXN := hXK.trans (Subgroup.centralizer_le_normalizer (s := (Z1 L1 L2 S : Set G)))
  refine TauCeti.commutator_closure_closure_le hXN hXN ?_
  intro a ha b hb
  obtain ⟨h1, hh1, y1, hy1, rfl⟩ := ha
  obtain ⟨h2, hh2, y2, hy2, rfl⟩ := hb
  exact x1_generators_commute hF hSB hk hFc hU3 hn hL2 hZQ hbridge hZI hh1 hh2 hy1 hy2

private theorem str86_Z1_le_X1_derived_of_bridge
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hbridge : Str86YCommBridge L1 L2 S) :
    Z1 L1 L2 S ≤ ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨g, hgL1, hgborel⟩ := SetLike.exists_of_lt (F1.lt_borelOf hR)
  have hgB : g ∉ bigB L1 L2 S := by
    intro h
    apply hgborel
    have hmem : g ∈ L1 ⊓ bigB L1 L2 S := Subgroup.mem_inf.mpr ⟨hgL1, h⟩
    rwa [F1.inf_bigB_eq_borelOf hR] at hmem
  let Yg : Subgroup G := MulAut.conj g • u3Y L1 L2 S
  have hgS : g ∈ L1 ⊔ S := (le_sup_left : L1 ≤ L1 ⊔ S) hgL1
  have hYgS : Yg ≤ S :=
    (str86_u3Y_conj_le_q1 (L1 := L1) (L2 := L2) (S := S) hgS).trans
      (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW))
  have hYgSup : Yg ⊔ Q2 L1 L2 S = S :=
    str86_u3Y_conj_sup_q2 hF hSB hk hFc hU3 hn hL2 hZQ hgS hgB
  have hYgComm : ⁅u3Y L1 L2 S, Yg⁆ = Z1 L1 L2 S := hbridge Yg hYgS hYgSup
  have hYle : u3Y L1 L2 S ≤ u3X1 L1 L2 S := by
    rw [u3X1, u3Y]
    exact le_conjClosure _ _
  have hYgle : Yg ≤ u3X1 L1 L2 S := by
    intro z hz
    change z ∈ (u3Y L1 L2 S).map (MulAut.conj g).toMonoidHom at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact mem_conjClosure (Z := u3Y L1 L2 S) (H := L1) hgL1 hy
  rw [← hYgComm]
  exact Subgroup.commutator_mono hYle hYgle

theorem str86X1Comm_of_bridge
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hbridge : Str86YCommBridge L1 L2 S) :
    ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S ∧
      ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S :=
  ⟨le_antisymm
      (str86_X1_derived_le_z1_of_bridge hF hSB hk hFc hU3 hn hL2 hZI hZQ hbridge)
      (str86_Z1_le_X1_derived_of_bridge hF hSB hk hFc hU3 hn hL2 hZQ hbridge),
    str86_X1_Q1_le_z1_of_bridge hF hSB hk hFc hU3 hn hL2 hZI hZQ hbridge⟩

end CFSG.Quasithin.Stroth

end
