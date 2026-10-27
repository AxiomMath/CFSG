module

public import CFSG.Quasithin.Recognition.St84.TransferA5A5
public import CFSG.GroupTheory.FixedPointFreeCommutator
public import CFSG.GroupTheory.AlternatingFive.TwoCoreQuotient
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Borel
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.RankThree.PartOne.KE.CommutatorFactor

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

open CFSG.GroupTheory (card_inf_centralizer_eq_one_or_four_or_sixteen
  le_normalizer_inf_centralizer_of_commutator_mem relIndex_sup_eq_three_of_not_le
  exists_mem_of_card_eq_nine_of_four_lines mem_of_commutator_mem_of_fixedPointFree
  exists_orderOf_eq_three_of_not_le_of_relIndex_nine mem_normalizer_of_conjugator_mod
  fixedPointFree_of_inf_centralizer_eq_bot)
open CFSG.GroupTheory.AlternatingFive (monoidHom_eq_one_of_isL2Quot_of_card_lt_sixty
  exists_orderOf_eq_three_of_isL2Quot mem_pCoreOf_of_forall_commutator_mem
  exists_conjugator_mod_pCore)

section Generic

variable {G : Type} [Group G]

private theorem fixedPointFree_of_natSec {L Q : Subgroup G} (hnat : NatSec L ⊥ Q)
    {x : G} (hxL : x ∈ L) (hx3 : orderOf x = 3) :
    ∀ q ∈ Q, x * q * x⁻¹ = q → q = 1 := by
  intro q hq hfix
  have hcomm : q * x = x * q := by
    calc q * x = (x * q * x⁻¹) * x := by rw [hfix]
      _ = x * q := by group
  have hcomm' : ⁅q, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hmem := hnat x hxL hx3 q hq (by simpa using hcomm')
  simpa using hmem

private theorem commutator_eq_of_natSec_bot {L Q : Subgroup G} [Finite ↥Q]
    (hQN : L ≤ Subgroup.normalizer (Q : Set G)) (hQab : IsMulCommutative ↥Q)
    (hL3 : ∃ x ∈ L, orderOf x = 3) (hnat : NatSec L ⊥ Q) : ⁅Q, L⁆ = Q := by
  obtain ⟨x, hxL, hx3⟩ := hL3
  have hxN : x ∈ Subgroup.normalizer (Q : Set G) := hQN hxL
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hfree := fixedPointFree_of_natSec hnat hxL hx3
  have hQx : ⁅Q, Subgroup.zpowers x⁆ = Q :=
    CFSG.commutator_zpowers_eq_of_fixedPointFree Q x hQcomm hxN hfree
  refine le_antisymm ?_ ?_
  · exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hQN
  · calc Q = ⁅Q, Subgroup.zpowers x⁆ := hQx.symm
      _ ≤ ⁅Q, L⁆ := Subgroup.commutator_mono_right (Subgroup.zpowers_le.mpr hxL)

private theorem inf_centralizer_eq_bot_of_natSec_bot {L Q : Subgroup G}
    (hL3 : ∃ x ∈ L, orderOf x = 3) (hnat : NatSec L ⊥ Q) :
    Q ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨x, hxL, hx3⟩ := hL3
  refine le_antisymm ?_ bot_le
  intro q hq
  obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
  have hqx : ⁅q, x⁆ = 1 := by
    have hxq : ⁅x, q⁆ = 1 :=
      Subgroup.mem_centralizer_iff_commutator_eq_one.mp hqC x hxL
    have hinv := commutatorElement_inv (g₁ := q) (g₂ := x)
    rw [hxq] at hinv
    exact inv_eq_one.mp hinv
  have hmem := hnat x hxL hx3 q hqQ (by simpa using hqx)
  simpa using hmem

end Generic

section GenericCentralizer

variable {G : Type} [Group G]

private theorem inf_centralizer_eq_bot_of_centralizes_mod [Finite G] {L Q E : Subgroup G}
    (hQN : L ≤ Subgroup.normalizer (Q : Set G))
    (hQab : IsMulCommutative ↥Q) (hcardQ : Nat.card Q = 16)
    (hquot : IsL2Quot 2 (oTwoQuot ↥L)) (hnat : NatSec L ⊥ Q)
    (hQp : Q = pCoreOf 2 L)
    {c : G} (hcE : c ∈ E) (hcNQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hc3 : orderOf c = 3) (hcC : ∀ l ∈ L, ⁅c, l⁆ ∈ Q)
    (hEchar : CharTwo E) (hQeq : Q = pCoreOf 2 E) :
    Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
  classical
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({c} : Set G)
  have hCcard := card_inf_centralizer_eq_one_or_four_or_sixteen (Q := Q) hcardQ hcNQ hc3
  change Nat.card ↥C = 1 ∨ Nat.card ↥C = 4 ∨ Nat.card ↥C = 16 at hCcard
  rcases hCcard with h1 | h4 | h16
  · exact Subgroup.eq_bot_of_card_eq C h1
  ·
    have hLC : L ≤ Subgroup.normalizer (C : Set G) :=
      le_normalizer_inf_centralizer_of_commutator_mem hQab hQN hcC
    let φ : ↥L →* MulAut C :=
      (Subgroup.normalizerMonoidHom C).comp (Subgroup.inclusion hLC)
    have hQker : CFSG.pCore 2 ↥L ≤ φ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      have hxQ : (x : G) ∈ Q := by
        rw [hQp]
        exact Subgroup.mem_map_of_mem L.subtype hx
      have hyQ : (y : G) ∈ Q := (Subgroup.mem_inf.mp y.2).1
      have hcomm : (x : G) * (y : G) = (y : G) * (x : G) := by
        exact congrArg Subtype.val (hQab.is_comm.comm
          ⟨(x : G), hxQ⟩ ⟨(y : G), hyQ⟩)
      change (((Subgroup.normalizerMonoidHom C) ((Subgroup.inclusion hLC) x)) y : G) = (y : G)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      show (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
      rw [hcomm]
      group
    have hMulAutCard : Nat.card (MulAut C) < 60 := by
      have hinj : Function.Injective (fun f : MulAut C => (f : Equiv.Perm C)) := by
        intro f g h
        have h' : (f : C → C) = (g : C → C) :=
          congrArg (fun e : Equiv.Perm C => (e : C → C)) h
        exact MulEquiv.ext (fun x => congrFun h' x)
      have hle : Nat.card (MulAut C) ≤ Nat.card (Equiv.Perm C) :=
        Nat.card_le_card_of_injective _ hinj
      have hperm : Nat.card (Equiv.Perm C) = Nat.factorial (Nat.card C) := Nat.card_perm
      rw [hperm, h4] at hle
      norm_num at hle ⊢
      omega
    have hφ1 : φ = 1 :=
      monoidHom_eq_one_of_isL2Quot_of_card_lt_sixty hquot φ hMulAutCard hQker
    obtain ⟨x, hxL, hx3⟩ := exists_orderOf_eq_three_of_isL2Quot hquot
    have hx_act : ∀ y ∈ C, x * y * x⁻¹ = y := by
      intro y hy
      have hval := congrArg (fun g : ↥L →* MulAut C => g ⟨x, hxL⟩) hφ1
      have h2 := congrArg (fun f : MulAut C => f ⟨y, hy⟩) hval
      have h2' : ((φ ⟨x, hxL⟩) ⟨y, hy⟩ : C) = ⟨y, hy⟩ := by simpa using h2
      change ((Subgroup.normalizerMonoidHom C)
        ((Subgroup.inclusion hLC) ⟨x, hxL⟩)) ⟨y, hy⟩ = ⟨y, hy⟩ at h2'
      have h2'' := congrArg Subtype.val h2'
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2''
      simpa [Subgroup.coe_inclusion] using h2''
    have hCbot : C = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyQ : y ∈ Q := (Subgroup.mem_inf.mp hy).1
      have hxy : x * y = y * x := by
        calc x * y = (x * y * x⁻¹) * x := by group
          _ = y * x := by rw [hx_act y hy]
      have hcomm : ⁅y, x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hxy.symm
      have hmem := hnat x hxL hx3 y hyQ (by simpa using hcomm)
      simpa using hmem
    rw [hCbot, Subgroup.card_bot] at h4
    norm_num at h4
  ·
    have hCeq : C = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, hcardQ])
    have hcent : c ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqC : q ∈ C := by rw [hCeq]; exact hq
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hqC).2
    have hcCE : c ∈ E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set G) :=
      ⟨hcE, by simpa [hQeq] using hcent⟩
    have hcQ : c ∈ Q := by simpa [hQeq] using hEchar hcCE
    have hdvd := _root_.orderOf_dvd_natCard (⟨c, hcQ⟩ : ↥Q)
    rw [Subgroup.orderOf_mk, hc3, hcardQ] at hdvd
    norm_num at hdvd

end GenericCentralizer

variable {H : Type} [Group H] [Finite H]

structure L34VertexData (E : Subgroup H) : Prop where
  quot : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime E))
  elem : IsElemAbelian 2 (pCoreOf 2 E)
  card : Nat.card (pCoreOf 2 E) = 16
  nat : NatSec (oTwoPrime E) ⊥ (pCoreOf 2 E)

theorem transferVertexData_of_l34VertexData {E : Subgroup H} (h : L34VertexData E) :
    TransferVertexData E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hQfin : Finite ↥(pCoreOf 2 E) :=
    Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  have hL3 : ∃ x ∈ oTwoPrime E, orderOf x = 3 :=
    exists_orderOf_eq_three_of_isL2Quot h.quot
  have hQL : pCoreOf 2 E ≤ oTwoPrime E :=
    CFSG.Quasithin.le_oTwoPrime_of_isPGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 E)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 E)
  have hLN : oTwoPrime E ≤ Subgroup.normalizer (pCoreOf 2 E : Set H) :=
    (oTwoPrime_le E).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E)
  have hcent := inf_centralizer_eq_bot_of_natSec_bot (L := oTwoPrime E)
    (Q := pCoreOf 2 E) hL3 h.nat
  refine ⟨h.quot, h.elem.1, ?_, ?_, ?_⟩
  · rw [hcent, Subgroup.relIndex_bot_left, h.card]
  · simpa [hcent] using h.nat
  · exact commutator_eq_of_natSec_bot hLN h.elem.1 hL3 h.nat

section Vertex

variable {L1 L2 S : Subgroup H}

theorem f112saX1_eq_inf_borelOf (hF : F112HypW L1 L2 S) :
    f112saX1 L1 L2 S = oTwoRes L1 ⊓ borelOf L1 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hB : bigB L1 L2 S ⊓ L1 = borelOf L1 S := by
    rw [inf_comm]
    exact F1.inf_bigB_eq_borelOf hR
  rw [f112saX1, ← hB]
  show oTwoRes L1 ⊓ bigB L1 L2 S = oTwoRes L1 ⊓ (bigB L1 L2 S ⊓ L1)
  rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans (oTwoRes_le L1))]

theorem f112sa_exists_cartan_X1 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) :
    ∃ D : Subgroup H, D ≤ f112saX1 L1 L2 S ∧ Nat.card D = 3 ∧
      D ⊓ (S ⊓ L1) = ⊥ ∧ f112saX1 L1 L2 S = (f112saX1 L1 L2 S ⊓ S) ⊔ D := by
  classical
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  obtain ⟨D, hDB, hD3, hDP, hPD⟩ :=
    CFSG.Quasithin.FA5.exists_cartan_three (L := L1) (S := S) hF.1.h1.sylow (e1.trans e2)
  have hX1 : f112saX1 L1 L2 S = oTwoRes L1 ⊓ borelOf L1 S := f112saX1_eq_inf_borelOf hF
  have hDB1 : D ≤ borelOf L1 S := hDB
  have hDL1 : D ≤ L1 := hDB1.trans (F1.borelOf_le L1 S)
  have hDo2 : D ≤ oTwoRes L1 := by
    intro d hd
    have hd3 : d ^ 3 = 1 := by
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      have h := _root_.orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
      rw [Subgroup.orderOf_mk, hD3] at h
      exact h
    exact Subgroup.subset_closure ⟨hDL1 hd, 3, by norm_num, hd3⟩
  have hDX1 : D ≤ f112saX1 L1 L2 S := by
    rw [hX1]; exact le_inf hDo2 hDB1
  have hX1B1 : f112saX1 L1 L2 S ≤ borelOf L1 S := by
    rw [hX1]; exact inf_le_right
  have hDnormP : D ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup H) : Set H) :=
    hDB1.trans (F1.borelOf_le_normalizer L1 S)
  refine ⟨D, hDX1, hD3, hDP, ?_⟩
  refine le_antisymm ?_ (sup_le inf_le_left hDX1)
  intro x hx
  have hxB1 : x ∈ (S ⊓ L1) ⊔ D := by rw [hPD]; exact hX1B1 hx
  obtain ⟨p, hp, d, hd, hpd⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (H := S ⊓ L1) (K := D) hDnormP).mp hxB1
  have hpX : p ∈ f112saX1 L1 L2 S := by
    have hdX : d ∈ f112saX1 L1 L2 S := hDX1 hd
    have hp_eq : p = x * d⁻¹ := by
      calc p = (p * d) * d⁻¹ := by group
        _ = x * d⁻¹ := by rw [← hpd]
    rw [hp_eq]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hdX)
  rw [hpd]
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hpX, hp.1⟩) hd

theorem f112sa_exists_cartan_X2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) :
    ∃ D : Subgroup H, D ≤ f112saX2 L1 L2 S ∧ Nat.card D = 3 ∧
      D ⊓ (S ⊓ L2) = ⊥ ∧ f112saX2 L1 L2 S = (f112saX2 L1 L2 S ⊓ S) ⊔ D := by
  have hX : f112saX2 L1 L2 S = f112saX1 L2 L1 S := by
    rw [f112saX1, f112saX2, bigB_comm]
  rw [hX]
  exact f112sa_exists_cartan_X1 hF.symm h2

end Vertex

private theorem sup_eq_sup_of_eq_sup_inf {A B S D1 D2 K T : Subgroup H}
    (hK : K = A ⊔ B) (hT : T = S ⊓ K) (hA : A = (A ⊓ S) ⊔ D1)
    (hB : B = (B ⊓ S) ⊔ D2) (hAT : A ⊓ S ≤ T) (hBT : B ⊓ S ≤ T)
    (hD1 : D1 ≤ A) (hD2 : D2 ≤ B) : K = (T ⊔ D1) ⊔ D2 := by
  rw [hK]
  refine le_antisymm ?_ ?_
  · have h1 : A ≤ (T ⊔ D1) ⊔ D2 := by
      calc A = (A ⊓ S) ⊔ D1 := hA
        _ ≤ T ⊔ D1 := sup_le (hAT.trans le_sup_left) le_sup_right
        _ ≤ (T ⊔ D1) ⊔ D2 := le_sup_left
    have h2 : B ≤ (T ⊔ D1) ⊔ D2 := by
      calc B = (B ⊓ S) ⊔ D2 := hB
        _ ≤ T ⊔ D2 := sup_le (hBT.trans le_sup_left) le_sup_right
        _ ≤ (T ⊔ D1) ⊔ D2 := sup_le_sup le_sup_left le_rfl
    exact sup_le h1 h2
  · refine sup_le (sup_le ?_ (hD1.trans le_sup_left)) ?_
    · exact hT.le.trans (inf_le_right.trans hK.le)
    · exact hD2.trans le_sup_right

theorem f112saX1_inf_S_le_T (L1 L2 S : Subgroup H) :
    f112saX1 L1 L2 S ⊓ S ≤ S ⊓ f112saK L1 L2 S :=
  le_inf inf_le_right (inf_le_left.trans (le_sup_left : f112saX1 L1 L2 S ≤ f112saK L1 L2 S))

theorem f112saX2_inf_S_le_T (L1 L2 S : Subgroup H) :
    f112saX2 L1 L2 S ⊓ S ≤ S ⊓ f112saK L1 L2 S :=
  le_inf inf_le_right (inf_le_left.trans (le_sup_right : f112saX2 L1 L2 S ≤ f112saK L1 L2 S))

private theorem sup_eq_sup_of_eq_sup_of_le {A X Y D L E : Subgroup H}
    (hE : E = A ⊔ X) (hX : X = Y ⊔ D) (hA : A ≤ L) (hY : Y ≤ L)
    (hD : D ≤ E) (hL : L ≤ E) : E = L ⊔ D := by
  refine le_antisymm ?_ (sup_le hL hD)
  rw [hE, hX]
  calc A ⊔ (Y ⊔ D) = (A ⊔ Y) ⊔ D := (sup_assoc _ _ _).symm
    _ ≤ L ⊔ D := sup_le_sup (sup_le hA hY) le_rfl

theorem f112saP1'_eq_oTwoPrime_sup_cartan
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) {D2 : Subgroup H}
    (hD2X : D2 ≤ f112saX2 L1 L2 S)
    (hX2eq : f112saX2 L1 L2 S = (f112saX2 L1 L2 S ⊓ S) ⊔ D2) :
    f112saP1' L1 L2 S = oTwoPrime (f112saP1' L1 L2 S) ⊔ D2 := by
  exact sup_eq_sup_of_eq_sup_of_le rfl hX2eq
    (f112sa_oTwoRes_le_oTwoPrime_P1' hF h1)
    ((f112saX2_inf_S_le_T L1 L2 S).trans (f112sa_T_le_oTwoPrime_P1' hF))
    (hD2X.trans le_sup_right) (oTwoPrime_le _)

theorem f112saP2'_eq_oTwoPrime_sup_cartan
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h2 : VA5 L2) {D1 : Subgroup H}
    (hD1X : D1 ≤ f112saX1 L1 L2 S)
    (hX1eq : f112saX1 L1 L2 S = (f112saX1 L1 L2 S ⊓ S) ⊔ D1) :
    f112saP2' L1 L2 S = oTwoPrime (f112saP2' L1 L2 S) ⊔ D1 := by
  exact sup_eq_sup_of_eq_sup_of_le rfl hX1eq
    (f112sa_oTwoRes_le_oTwoPrime_P2' hF h2)
    ((f112saX1_inf_S_le_T L1 L2 S).trans (f112sa_T_le_oTwoPrime_P2' hF))
    (hD1X.trans le_sup_right) (oTwoPrime_le _)

theorem f112saK_eq_T_sup_cartan {L1 L2 S D1 D2 : Subgroup H}
    (hD1X : D1 ≤ f112saX1 L1 L2 S) (hD2X : D2 ≤ f112saX2 L1 L2 S)
    (hX1eq : f112saX1 L1 L2 S = (f112saX1 L1 L2 S ⊓ S) ⊔ D1)
    (hX2eq : f112saX2 L1 L2 S = (f112saX2 L1 L2 S ⊓ S) ⊔ D2) :
    f112saK L1 L2 S = (S ⊓ f112saK L1 L2 S) ⊔ D1 ⊔ D2 :=
  sup_eq_sup_of_eq_sup_inf (A := f112saX1 L1 L2 S) (B := f112saX2 L1 L2 S)
    (S := S) (D1 := D1) (D2 := D2) (K := f112saK L1 L2 S)
    (T := S ⊓ f112saK L1 L2 S) rfl rfl hX1eq hX2eq
    (f112saX1_inf_S_le_T L1 L2 S) (f112saX2_inf_S_le_T L1 L2 S) hD1X hD2X

theorem f112sa_T_normal_K {L1 L2 S : Subgroup H}
    (hT : S ⊓ f112saK L1 L2 S =
      pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S)) :
    ((S ⊓ f112saK L1 L2 S).subgroupOf (f112saK L1 L2 S)).Normal := by
  have hK1 : f112saK L1 L2 S ≤ f112saP1' L1 L2 S := f112saK_le_P1' L1 L2 S
  have hK2 : f112saK L1 L2 S ≤ f112saP2' L1 L2 S := f112saK_le_P2' L1 L2 S
  have hα : f112saK L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
    hK1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP1' L1 L2 S))
  have hβ : f112saK L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (f112saP2' L1 L2 S) : Set H) :=
    hK2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP2' L1 L2 S))
  have hN : f112saK L1 L2 S ≤
      Subgroup.normalizer ((S ⊓ f112saK L1 L2 S) : Set H) := by
    change f112saK L1 L2 S ≤
      Subgroup.normalizer (((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H))
    rw [show ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H) =
      ((pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S) :
        Subgroup H) : Set H) by rw [hT]]
    exact (le_inf hα hβ).trans
      (Subgroup.inf_normalizer_le_normalizer_sup
        (pCoreOf 2 (f112saP1' L1 L2 S)) (pCoreOf 2 (f112saP2' L1 L2 S)))
  exact Subgroup.normal_subgroupOf_of_le_normalizer hN

theorem f112sa_exists_cartan_decomposition
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∃ D1 D2 : Subgroup H,
      D1 ≤ f112saX1 L1 L2 S ∧ D2 ≤ f112saX2 L1 L2 S ∧
      Nat.card D1 = 3 ∧ Nat.card D2 = 3 ∧
      D1 ⊓ (S ⊓ L1) = ⊥ ∧ D2 ⊓ (S ⊓ L2) = ⊥ ∧
      f112saX1 L1 L2 S = (f112saX1 L1 L2 S ⊓ S) ⊔ D1 ∧
      f112saX2 L1 L2 S = (f112saX2 L1 L2 S ⊓ S) ⊔ D2 ∧
      f112saP1' L1 L2 S = oTwoPrime (f112saP1' L1 L2 S) ⊔ D2 ∧
      f112saP2' L1 L2 S = oTwoPrime (f112saP2' L1 L2 S) ⊔ D1 ∧
      f112saK L1 L2 S = (S ⊓ f112saK L1 L2 S) ⊔ D1 ⊔ D2 := by
  obtain ⟨D1, hD1X, hD13, hD1P, hX1eq⟩ := f112sa_exists_cartan_X1 hF h1
  obtain ⟨D2, hD2X, hD23, hD2P, hX2eq⟩ := f112sa_exists_cartan_X2 hF h2
  exact ⟨D1, D2, hD1X, hD2X, hD13, hD23, hD1P, hD2P, hX1eq, hX2eq,
    f112saP1'_eq_oTwoPrime_sup_cartan hF h1 hD2X hX2eq,
    f112saP2'_eq_oTwoPrime_sup_cartan hF h2 hD1X hX1eq,
    f112saK_eq_T_sup_cartan hD1X hD2X hX1eq hX2eq⟩

theorem f112sa_S_le_centralizer_A1 {L1 L2 S : Subgroup H}
    (hD1 : L34VertexData (f112saP1' L1 L2 S))
    (hD2 : L34VertexData (f112saP2' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S = pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S))
    (hS : S ≤ f112saK L1 L2 S) :
    S ≤ Subgroup.centralizer
      (↑(pCoreOf 2 (f112saP1' L1 L2 S) ⊓ pCoreOf 2 (f112saP2' L1 L2 S)) : Set H) := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  let A1 := Qα ⊓ Qβ
  have hT' : S = Qα ⊔ Qβ := by
    have h := hT
    rw [show S ⊓ f112saK L1 L2 S = S from inf_eq_left.mpr hS] at h
    exact h
  have hQαC : Qα ≤ Subgroup.centralizer (A1 : Set H) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haQ : a ∈ Qα := (Subgroup.mem_inf.mp ha).1
    exact congrArg Subtype.val (hD1.elem.1.is_comm.comm ⟨a, haQ⟩ ⟨q, hq⟩)
  have hQβC : Qβ ≤ Subgroup.centralizer (A1 : Set H) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haQ : a ∈ Qβ := (Subgroup.mem_inf.mp ha).2
    exact congrArg Subtype.val (hD2.elem.1.is_comm.comm ⟨a, haQ⟩ ⟨q, hq⟩)
  change S ≤ Subgroup.centralizer (A1 : Set H)
  rw [hT']
  exact sup_le hQαC hQβC

theorem f112sa_K_le_normalizer_A1 (L1 L2 S : Subgroup H) :
    f112saK L1 L2 S ≤
      Subgroup.normalizer
        (↑(pCoreOf 2 (f112saP1' L1 L2 S) ⊓ pCoreOf 2 (f112saP2' L1 L2 S)) : Set H) :=
  (le_inf ((f112saK_le_P1' L1 L2 S).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    ((f112saK_le_P2' L1 L2 S).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))).trans
    Subgroup.inf_normalizer_le_normalizer_inf
theorem f112sa_relIndex_S_K_eq_nine_of_not_le {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hV1 : TransferVertexData (f112saP1' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S =
      pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S))
    (hS : S ≤ f112saK L1 L2 S)
    {D1 D2 : Subgroup H}
    (hD1X : D1 ≤ f112saX1 L1 L2 S) (hD2X : D2 ≤ f112saX2 L1 L2 S)
    (hD13 : Nat.card D1 = 3) (hD23 : Nat.card D2 = 3)
    (hD1S : D1 ⊓ (S ⊓ L1) = ⊥)
    (hKeq : f112saK L1 L2 S = (S ⊓ f112saK L1 L2 S) ⊔ D1 ⊔ D2)
    (hD2notL1 : ¬ D2 ≤ L1) :
    S.relIndex (f112saK L1 L2 S) = 9 := by
  classical
  let K := f112saK L1 L2 S
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  have hA1 := f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData hF h1 hS hV1
  have hS1 : S ≤ L1 := hA1.1
  have hL1eq : L1 = oTwoPrime Eα := hA1.2.1
  have hNormSub : ((S ⊓ K).subgroupOf K).Normal := by
    change ((S ⊓ f112saK L1 L2 S).subgroupOf (f112saK L1 L2 S)).Normal
    exact f112sa_T_normal_K hT
  rw [show S ⊓ K = S from inf_eq_left.mpr hS] at hNormSub
  have hKN : K ≤ Subgroup.normalizer (S : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS).mp hNormSub
  have hKeq' : K = S ⊔ D1 ⊔ D2 := by
    change f112saK L1 L2 S = S ⊔ D1 ⊔ D2
    rw [hKeq, show S ⊓ f112saK L1 L2 S = S from inf_eq_left.mpr hS]
  have hD1Sbot : D1 ⊓ S = ⊥ := by
    have h := hD1S
    rwa [inf_eq_left.mpr hS1] at h
  have hD1L1 : D1 ≤ L1 :=
    hD1X.trans ((inf_le_left : f112saX1 L1 L2 S ≤ oTwoRes L1).trans (oTwoRes_le L1))
  have hB1leL1 : S ⊔ D1 ≤ L1 := sup_le hS1 hD1L1
  have hD1K : D1 ≤ K := hD1X.trans (le_sup_left : f112saX1 L1 L2 S ≤ K)
  have hD2K : D2 ≤ K := hD2X.trans (le_sup_right : f112saX2 L1 L2 S ≤ K)
  have hD1N : D1 ≤ Subgroup.normalizer (S : Set H) := hD1K.trans hKN
  have hD2N_S : D2 ≤ Subgroup.normalizer (S : Set H) := hD2K.trans hKN
  have hD1notS : ¬ D1 ≤ S := by
    intro hle
    have hbot : D1 = ⊥ := by
      rw [← hD1Sbot, inf_comm, inf_eq_right.mpr hle]
    have hcard1 : Nat.card D1 = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hrelSB1 : S.relIndex (S ⊔ D1) = 3 :=
    relIndex_sup_eq_three_of_not_le hD13 hD1N hD1notS
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  have hB1eq : S ⊔ D1 = borelOf L1 S :=
    FA5.borelOf_eq_sup_cartan_of_le hF.1.h1.sylow (e1.trans e2) hS1 hD1L1 hD1N hD13
      hD1notS
  have hKleEα : K ≤ Eα := f112saK_le_P1' L1 L2 S
  have hEN : Eα ≤ Subgroup.normalizer (L1 : Set H) := by
    rw [show L1 = oTwoPrime Eα from hL1eq]
    exact le_normalizer_oTwoPrime Eα
  have hD2N_L1 : D2 ≤ Subgroup.normalizer (L1 : Set H) := hD2K.trans (hKleEα.trans hEN)
  have hD2N_B1 : D2 ≤ Subgroup.normalizer ((S ⊔ D1 : Subgroup H) : Set H) := by
    rw [hB1eq, borelOf, inf_eq_left.mpr hS1]
    exact (le_inf hD2N_L1 (hD2N_S.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hD2notB1 : ¬ D2 ≤ S ⊔ D1 := fun hle => hD2notL1 (hle.trans hB1leL1)
  have hB1K3 : (S ⊔ D1).relIndex K = 3 := by
    have h := relIndex_sup_eq_three_of_not_le (A := S ⊔ D1) (B := D2)
      hD23 hD2N_B1 hD2notB1
    rwa [← hKeq'] at h
  have hB1K : S ⊔ D1 ≤ K := by
    rw [hKeq']
    exact le_sup_left
  have hrel := Subgroup.relIndex_mul_relIndex (H := S) (K := S ⊔ D1) (L := K)
    le_sup_left hB1K
  change S.relIndex K = 9
  rw [hrelSB1, hB1K3] at hrel
  norm_num at hrel
  exact hrel.symm

theorem f112sa_card_S_eq_sixtyfour {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD1 : L34VertexData (f112saP1' L1 L2 S))
    (hS : S ≤ f112saK L1 L2 S) :
    Nat.card S = 64 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Eα := f112saP1' L1 L2 S
  have hV1' : TransferVertexData Eα := transferVertexData_of_l34VertexData hD1
  have hA1 := f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData hF h1 hS hV1'
  have hS1 : S ≤ L1 := hA1.1
  have hL1 : L1 = oTwoPrime Eα := hA1.2.1
  have hQ1 : pCoreOf 2 L1 = pCoreOf 2 Eα := hA1.2.2
  have hquotL1 : IsL2Quot 2 (oTwoQuot ↥L1) := by
    rw [hL1]
    exact hD1.quot
  have h60 : Nat.card (oTwoQuot ↥L1) = 60 := by
    rw [CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) hquotL1]
    norm_num
  have hQcard : Nat.card ↥(pCoreOf 2 L1) = 16 := by
    rw [hQ1, hD1.card]
  have hQcorecard : Nat.card ↥(pCore 2 ↥L1) = 16 := by
    rw [← hQcard]
    exact (Subgroup.card_map_of_injective L1.subtype_injective).symm
  have hL1card : Nat.card ↥L1 = 960 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L1)
    rw [h60, hQcorecard] at h
    omega
  have hsyl : IsSylowTwoOf S L1 := by
    have h := hF.1.h1.sylow
    rwa [inf_eq_left.mpr hS1] at h
  obtain ⟨n, hn⟩ := hsyl.2.1.exists_card_eq
  have hrel : S.relIndex L1 * Nat.card S = 960 := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := L1)
    rw [show S ⊓ L1 = S from inf_eq_left.mpr hS1, hL1card] at h
    exact h
  have hrel' : S.relIndex L1 * 2 ^ n = 960 := by rw [← hn]; exact hrel
  have hodd : ¬ 2 ∣ S.relIndex L1 := hsyl.2.2
  have hfac : n = 6 := by
    have hmul := congrArg (fun x : ℕ => x.factorization 2) hrel'
    rw [Nat.factorization_mul (Nat.ne_of_gt (Nat.pos_of_ne_zero (by
        intro h; rw [h] at hrel'; norm_num at hrel')))
      (Nat.ne_of_gt (Nat.pos_of_ne_zero (by
        intro h; rw [h] at hrel'; norm_num at hrel')))] at hmul
    have hodd0 : (S.relIndex L1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hodd
    have hfac960 : (Nat.factorization 960) 2 = 6 := by norm_num [Nat.factorization]
    rw [Nat.Prime.factorization_pow Nat.prime_two] at hmul
    simp [hodd0, hfac960] at hmul
    omega
  rw [hn, hfac]
  norm_num

theorem f112sa_card_inf_pCoreOf_eq_four {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD1 : L34VertexData (f112saP1' L1 L2 S))
    (hD2 : L34VertexData (f112saP2' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S = pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S))
    (hS : S ≤ f112saK L1 L2 S) :
    Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S) ⊓ pCoreOf 2 (f112saP2' L1 L2 S)) = 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  have hcardS : Nat.card S = 64 := f112sa_card_S_eq_sixtyfour hF h1 hD1 hS
  have hT' : S = Qα ⊔ Qβ := by
    have h := hT
    rw [show S ⊓ f112saK L1 L2 S = S from inf_eq_left.mpr hS] at h
    exact h
  have hcardSup : Nat.card ↥(Qα ⊔ Qβ) = 64 := by rw [← hT', hcardS]
  have hcardQα : Nat.card ↥Qα = 16 := by dsimp [Qα, Eα]; exact hD1.card
  have hcardQβ : Nat.card ↥Qβ = 16 := by dsimp [Qβ, Eβ]; exact hD2.card
  have hKleEα : f112saK L1 L2 S ≤ Eα := f112saK_le_P1' L1 L2 S
  have hQαN : f112saK L1 L2 S ≤ Subgroup.normalizer (Qα : Set H) := by
    dsimp [Qα, Eα]
    exact hKleEα.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP1' L1 L2 S))
  have hQβS : Qβ ≤ S := by
    rw [hT']
    exact le_sup_right
  have hQβK : Qβ ≤ f112saK L1 L2 S := hQβS.trans hS
  have hQβN : Qβ ≤ Subgroup.normalizer (Qα : Set H) := hQβK.trans hQαN
  have hformula :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Qβ) (K := Qα) hQβN
  rw [sup_comm Qβ Qα, inf_comm Qβ Qα] at hformula
  rw [hcardSup, hcardQα, hcardQβ] at hformula
  change Nat.card ↥(Qα ⊓ Qβ) = 4
  omega

theorem f112sa_bigB_le_inf_of_no_extra_torus
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hV1 : TransferVertexData (f112saP1' L1 L2 S))
    (hV2 : TransferVertexData (f112saP2' L1 L2 S))
    (hS : S ≤ f112saK L1 L2 S)
    (hL1 : oTwoPrime (f112saP1' L1 L2 S) = f112saP1' L1 L2 S)
    (hL2 : oTwoPrime (f112saP2' L1 L2 S) = f112saP2' L1 L2 S) :
    bigB L1 L2 S ≤ L1 ⊓ L2 ∧
      f112P1 L1 L2 S = L1 ∧ f112P2 L1 L2 S = L2 := by
  obtain ⟨-, hL1eq, -⟩ :=
    f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData hF h1 hS hV1
  obtain ⟨-, hL2eq, -⟩ :=
    f112sa_S_le_L2_and_eq_oTwoPrime_of_transferVertexData hF h2 hS hV2
  have hP1 : f112P1 L1 L2 S = f112saP1' L1 L2 S := f112saP1_eq_of_S_le_K hF hS
  have hP2 : f112P2 L1 L2 S = f112saP2' L1 L2 S := f112saP2_eq_of_S_le_K hF hS
  have hKle1 : f112saK L1 L2 S ≤ L1 := by
    conv_rhs => rw [hL1eq, hL1]
    exact f112saK_le_P1' L1 L2 S
  have hKle2 : f112saK L1 L2 S ≤ L2 := by
    conv_rhs => rw [hL2eq, hL2]
    exact f112saK_le_P2' L1 L2 S
  have hBig : bigB L1 L2 S = f112saK L1 L2 S := by
    rw [f112sa_bigB_eq_S_sup_K hF, sup_eq_right.mpr hS]
  refine ⟨?_, ?_, ?_⟩
  · rw [hBig]
    exact le_inf hKle1 hKle2
  · conv_lhs => rw [hP1]
    conv_rhs => rw [hL1eq, hL1]
  · conv_lhs => rw [hP2]
    conv_rhs => rw [hL2eq, hL2]

private theorem exists_orderThree_fixedFree_of_commutatorKernel
    {K S L Q E : Subgroup H}
    (hrel : S.relIndex K = 9) (hSnorm : (S.subgroupOf K).Normal)
    (hS2 : IsPGroup 2 S)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set H))
    (hKE : K ≤ E) (hLQ : L ≤ Subgroup.normalizer (Q : Set H))
    (hQeq : Q = pCoreOf 2 L) (hquot : oTwoQuot L ≃* alternatingGroup (Fin 5))
    (hQab : IsMulCommutative ↥Q) (hcardQ : Nat.card Q = 16)
    (hnat : NatSec L ⊥ Q) (hEchar : CharTwo E) (hQeqE : Q = pCoreOf 2 E)
    {x g : H} (hxK : x ∈ K) (hgL : g ∈ L) (hgK : g ∈ K)
    (hconj : ∀ l ∈ L, x * l * x⁻¹ * (g * l * g⁻¹)⁻¹ ∈ Q)
    (hx0NotS : g⁻¹ * x ∉ S) :
    ∃ r : H, r ∈ K ∧ orderOf r = 3 ∧ r ∉ S ∧
      (∀ l ∈ L, ⁅r, l⁆ ∈ Q) ∧ Q ⊓ Subgroup.centralizer ({r} : Set H) = ⊥ := by
  classical
  let R : Subgroup H := dsCentMod K L Q
  have hRmem : ∀ y, y ∈ R ↔ y ∈ K ∧ ∀ l ∈ L, ⁅y, l⁆ ∈ Q := fun y =>
    (show y ∈ R ↔ y ∈ K ∧ y ∈ Subgroup.normalizer (Q : Set H) ∧ ∀ l ∈ L, ⁅y, l⁆ ∈ Q
      from Iff.rfl).trans ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hKQ h.1, h.2⟩⟩
  have hRK : R ≤ K := fun y hy => ((hRmem y).mp hy).1
  let x0 : H := g⁻¹ * x
  have hx0K : x0 ∈ K := K.mul_mem (K.inv_mem hgK) hxK
  have hx0R : x0 ∈ R := by
    rw [hRmem]
    refine ⟨hx0K, ?_⟩
    intro l hl
    have hqQ : x * l * x⁻¹ * (g * l * g⁻¹)⁻¹ ∈ Q := hconj l hl
    have hxl : x0 * l * x0⁻¹ = g⁻¹ *
        (x * l * x⁻¹ * (g * l * g⁻¹)⁻¹) * g * l := by
      dsimp [x0]
      rw [show x * l * x⁻¹ =
        (x * l * x⁻¹ * (g * l * g⁻¹)⁻¹) * (g * l * g⁻¹) from by group]
      group
    have hcomm : ⁅x0, l⁆ = g⁻¹ * (x * l * x⁻¹ * (g * l * g⁻¹)⁻¹) * g := by
      rw [commutatorElement_def, hxl]
      group
    rw [hcomm]
    simpa using (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem hgL)) _).mp hqQ
  obtain ⟨r, hrR, hr3, hrNotS⟩ :=
    exists_orderOf_eq_three_of_not_le_of_relIndex_nine (K := K) (S := S) (R := R)
      hrel hSnorm hRK (fun hle => hx0NotS (hle hx0R)) hS2
  have hrK : r ∈ K := hRK hrR
  have hrCent : ∀ l ∈ L, ⁅r, l⁆ ∈ Q := ((hRmem r).mp hrR).2
  have hrNQ : r ∈ Subgroup.normalizer (Q : Set H) := hKQ hrK
  have hquotL : IsL2Quot 2 (oTwoQuot ↥L) := by
    obtain ⟨ep⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
    exact ⟨hquot.trans ep.symm⟩
  have hr_cent_bot : Q ⊓ Subgroup.centralizer ({r} : Set H) = ⊥ :=
    inf_centralizer_eq_bot_of_centralizes_mod (L := L) (Q := Q) (E := E)
      hLQ hQab hcardQ hquotL hnat hQeq (hKE hrK) hrNQ hr3 hrCent hEchar hQeqE
  exact ⟨r, hrK, hr3, hrNotS, hrCent, hr_cent_bot⟩

private structure L34Setup (H : Type) [Group H] [Finite H] where
  L1 : Subgroup H
  L2 : Subgroup H
  S : Subgroup H
  D1 : Subgroup H
  D2 : Subgroup H
  K : Subgroup H
  Eα : Subgroup H
  Eβ : Subgroup H
  Qα : Subgroup H
  Qβ : Subgroup H
  A1 : Subgroup H
  hS1 : S ≤ L1
  hS2 : S ≤ L2
  hSK : S ≤ K
  hrelK : S.relIndex K = 9
  hSnormK : (S.subgroupOf K).Normal
  hS2p : IsPGroup 2 S
  hKN : K ≤ Subgroup.normalizer (S : Set H)
  hKQα : K ≤ Subgroup.normalizer (Qα : Set H)
  hKQβ : K ≤ Subgroup.normalizer (Qβ : Set H)
  hKleEα : K ≤ Eα
  hKleEβ : K ≤ Eβ
  hQαS : Qα ≤ S
  hQβS : Qβ ≤ S
  hQβL2 : Qβ ≤ L2
  hL1NQα : L1 ≤ Subgroup.normalizer (Qα : Set H)
  hL2NQβ : L2 ≤ Subgroup.normalizer (Qβ : Set H)
  hQ1eq : pCoreOf 2 L1 = Qα
  hQ2eq : pCoreOf 2 L2 = Qβ
  hQαE : Qα = pCoreOf 2 Eα
  hQβE : Qβ = pCoreOf 2 Eβ
  hQαab : IsMulCommutative ↥Qα
  hQβab : IsMulCommutative ↥Qβ
  hQαexp : ∀ q ∈ Qα, q * q = 1
  hQβexp : ∀ q ∈ Qβ, q * q = 1
  hcardQα : Nat.card Qα = 16
  hcardQβ : Nat.card Qβ = 16
  hnat1 : NatSec L1 ⊥ Qα
  hnat2 : NatSec L2 ⊥ Qβ
  hcharP1 : CharTwo Eα
  hcharP2 : CharTwo Eβ
  hquotL1 : oTwoQuot L1 ≃* alternatingGroup (Fin 5)
  hquotL2 : oTwoQuot L2 ≃* alternatingGroup (Fin 5)
  hD1L1 : D1 ≤ L1
  hD2L2 : D2 ≤ L2
  hD1K : D1 ≤ K
  hD2K : D2 ≤ K
  hD1Eβ : D1 ≤ Eβ
  hD2Eα : D2 ≤ Eα
  hD13 : Nat.card D1 = 3
  hD23 : Nat.card D2 = 3
  hD1N : D1 ≤ Subgroup.normalizer (S : Set H)
  hD2N : D2 ≤ Subgroup.normalizer (S : Set H)
  hD1notS : ¬ D1 ≤ S
  hD2notS : ¬ D2 ≤ S
  hB1eq : S ⊔ D1 = borelOf L1 S
  hB2eq : S ⊔ D2 = borelOf L2 S
  hB1leL1 : S ⊔ D1 ≤ L1
  hEαNL1 : Eα ≤ Subgroup.normalizer (L1 : Set H)
  hEβNL2 : Eβ ≤ Subgroup.normalizer (L2 : Set H)
  hnot : ¬ D2 ≤ L1
  hA1eq : A1 = Qα ⊓ Qβ
  hA1card : Nat.card A1 = 4
  hScentralA1 : S ≤ Subgroup.centralizer (A1 : Set H)
  hKnormalA1 : K ≤ Subgroup.normalizer (A1 : Set H)
  hcommSQα : ∀ s ∈ S, ∀ q ∈ S, ⁅s, q⁆ ∈ Qα

private structure FourLines {H : Type} [Group H] [Finite H] (c : L34Setup H) where
  k1 : H
  k2 : H
  rα : H
  rβ : H
  hk1D1 : k1 ∈ c.D1
  hk1K : k1 ∈ c.K
  hk13 : orderOf k1 = 3
  hk1notS : k1 ∉ c.S
  hfree_k1 : ∀ q ∈ c.A1, k1 * q * k1⁻¹ = q → q = 1
  hk2D2 : k2 ∈ c.D2
  hk2K : k2 ∈ c.K
  hk23 : orderOf k2 = 3
  hk2notS : k2 ∉ c.S
  hfree_k2 : ∀ q ∈ c.A1, k2 * q * k2⁻¹ = q → q = 1
  hrαK : rα ∈ c.K
  hrα3 : orderOf rα = 3
  hrαnotS : rα ∉ c.S
  hfree_rα : ∀ q ∈ c.A1, rα * q * rα⁻¹ = q → q = 1
  hrαcent : ∀ l ∈ c.L1, ⁅rα, l⁆ ∈ c.Qα
  hrβK : rβ ∈ c.K
  hrβ3 : orderOf rβ = 3
  hrβnotS : rβ ∉ c.S
  hfree_rβ : ∀ q ∈ c.A1, rβ * q * rβ⁻¹ = q → q = 1
  hrβcent : ∀ l ∈ c.L2, ⁅rβ, l⁆ ∈ c.Qβ

private structure RalphaData (c : L34Setup H) where
  rα : H
  hrαK : rα ∈ c.K
  hrα3 : orderOf rα = 3
  hrαnotS : rα ∉ c.S
  hfree : ∀ q ∈ c.A1, rα * q * rα⁻¹ = q → q = 1
  hrαcent : ∀ l ∈ c.L1, ⁅rα, l⁆ ∈ c.Qα

private structure RbetaData (c : L34Setup H) where
  rβ : H
  hrβK : rβ ∈ c.K
  hrβ3 : orderOf rβ = 3
  hrβnotS : rβ ∉ c.S
  hfree : ∀ q ∈ c.A1, rβ * q * rβ⁻¹ = q → q = 1
  hrβcent : ∀ l ∈ c.L2, ⁅rβ, l⁆ ∈ c.Qβ

private theorem sup_S_D1_eq_sup_S_D2_of_le {S D1 D2 : Subgroup H}
    (hD13 : Nat.card D1 = 3) (hD23 : Nat.card D2 = 3)
    (hD1N : D1 ≤ Subgroup.normalizer (S : Set H))
    (hD2N : D2 ≤ Subgroup.normalizer (S : Set H))
    (hD1notS : ¬ D1 ≤ S) (hD2notS : ¬ D2 ≤ S)
    (hle : S ⊔ D1 ≤ S ⊔ D2) : S ⊔ D1 = S ⊔ D2 := by
  have hrel1 : S.relIndex (S ⊔ D1) = 3 :=
    relIndex_sup_eq_three_of_not_le hD13 hD1N hD1notS
  have hrel2 : S.relIndex (S ⊔ D2) = 3 :=
    relIndex_sup_eq_three_of_not_le hD23 hD2N hD2notS
  have hcard1 : Nat.card ↥(S ⊔ D1) = 3 * Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := S ⊔ D1)
    rw [show S ⊓ (S ⊔ D1) = S from inf_eq_left.mpr le_sup_left, hrel1] at h
    exact h.symm
  have hcard2 : Nat.card ↥(S ⊔ D2) = 3 * Nat.card ↥S := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := S ⊔ D2)
    rw [show S ⊓ (S ⊔ D2) = S from inf_eq_left.mpr le_sup_left, hrel2] at h
    exact h.symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hcard1])

private theorem mem_sup_of_quotient_mem_zpowers {K S : Subgroup H}
    [(S.subgroupOf K).Normal] {x : H} {y : ↥K}
    (hxK : x ∈ K)
    (hmem : QuotientGroup.mk' (S.subgroupOf K) ⟨x, hxK⟩ ∈
      Subgroup.zpowers (QuotientGroup.mk' (S.subgroupOf K) y)) :
    x ∈ S ⊔ Subgroup.zpowers (y : H) := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hclass : QuotientGroup.mk' (S.subgroupOf K) ⟨x, hxK⟩ =
      QuotientGroup.mk' (S.subgroupOf K) (y ^ j) := by
    rw [map_zpow]
    exact hj.symm
  have hdiv : (⟨x, hxK⟩ / (y ^ j)) ∈ S.subgroupOf K :=
    (QuotientGroup.eq_iff_div_mem (N := S.subgroupOf K)).mp hclass
  have hs : x * ((y : H) ^ j)⁻¹ ∈ S := by
    have h := Subgroup.mem_subgroupOf.mp hdiv
    simpa [div_eq_mul_inv] using h
  have hxeq : x = (x * ((y : H) ^ j)⁻¹) * (y : H) ^ j := by group
  rw [hxeq]
  exact (S ⊔ Subgroup.zpowers (y : H)).mul_mem (Subgroup.mem_sup_left hs)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers (y : H) j))

private noncomputable def ralphaData (c : L34Setup H) :
    RalphaData c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let k2D : ↥c.D2 :=
    Classical.choose (exists_prime_orderOf_dvd_card' (G := ↥c.D2) 3 (by simpa [c.hD23]))
  have hk2ordD : orderOf k2D = 3 :=
    Classical.choose_spec (exists_prime_orderOf_dvd_card' (G := ↥c.D2) 3 (by simpa [c.hD23]))
  let k2 : H := (k2D : H)
  have hk2D2 : k2 ∈ c.D2 := k2D.2
  have hk23 : orderOf k2 = 3 := by
    have h := hk2ordD
    rwa [Subgroup.orderOf_mk] at h
  have hk2zp : Subgroup.zpowers k2 = c.D2 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk2D2) ?_
    rw [Nat.card_zpowers, hk23, c.hD23]
  have hk2K : k2 ∈ c.K := c.hD2K hk2D2
  have hex : ∃ g ∈ c.L1, ∀ l ∈ c.L1, k2 * l * k2⁻¹ * (g * l * g⁻¹)⁻¹ ∈ c.Qα := by
    simpa only [c.hQ1eq] using exists_conjugator_mod_pCore (L := c.L1) c.hquotL1
      (c.hEαNL1 (c.hD2Eα hk2D2)) hk23
  let gα : H := Classical.choose hex
  have hgαspec := Classical.choose_spec hex
  obtain ⟨hgαL1, hconjα⟩ := hgαspec
  have hgαN : gα ∈ Subgroup.normalizer (c.S : Set H) :=
    mem_normalizer_of_conjugator_mod (K := c.K) (L := c.L1) (Q := c.Qα) (S := c.S)
      c.hS1 c.hKN c.hQαS hk2K hconjα
  have hgαB1 : gα ∈ c.S ⊔ c.D1 := by
    have h : gα ∈ borelOf c.L1 c.S := by
      rw [borelOf, inf_eq_left.mpr c.hS1]
      exact ⟨hgαL1, hgαN⟩
    rwa [← c.hB1eq] at h
  have hgαK : gα ∈ c.K := (sup_le c.hSK c.hD1K) hgαB1
  have hx0αNotS : gα⁻¹ * k2 ∉ c.S := by
    intro hx0S
    have hk2L1 : k2 ∈ c.L1 := by
      have h : k2 = gα * (gα⁻¹ * k2) := by group
      rw [h]
      exact c.L1.mul_mem (c.hB1leL1 hgαB1) (c.hS1 hx0S)
    exact c.hnot (by rw [← hk2zp]; exact Subgroup.zpowers_le.mpr hk2L1)
  let rα : H := Classical.choose (exists_orderThree_fixedFree_of_commutatorKernel
    (K := c.K) (S := c.S) (L := c.L1) (Q := c.Qα) (E := c.Eα)
    c.hrelK c.hSnormK c.hS2p c.hKQα c.hKleEα c.hL1NQα
    c.hQ1eq.symm c.hquotL1 c.hQαab c.hcardQα c.hnat1 c.hcharP1 c.hQαE
    hk2K hgαL1 hgαK hconjα hx0αNotS)
  have hrαspec := Classical.choose_spec (exists_orderThree_fixedFree_of_commutatorKernel
    (K := c.K) (S := c.S) (L := c.L1) (Q := c.Qα) (E := c.Eα)
    c.hrelK c.hSnormK c.hS2p c.hKQα c.hKleEα c.hL1NQα
    c.hQ1eq.symm c.hquotL1 c.hQαab c.hcardQα c.hnat1 c.hcharP1 c.hQαE
    hk2K hgαL1 hgαK hconjα hx0αNotS)
  obtain ⟨hrαK, hrα3, hrαnotS, hrαcent, hrαbot⟩ := hrαspec
  have hfreeQ : ∀ q ∈ c.Qα, rα * q * rα⁻¹ = q → q = 1 :=
    fixedPointFree_of_inf_centralizer_eq_bot hrαbot
  exact
    { rα := rα, hrαK := hrαK, hrα3 := hrα3, hrαnotS := hrαnotS,
      hfree := fun q hq => hfreeQ q (by
        have h := hq
        rw [c.hA1eq] at h
        exact h.1), hrαcent := hrαcent }

private noncomputable def rbetaData (c : L34Setup H) :
    RbetaData c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let k1D : ↥c.D1 :=
    Classical.choose (exists_prime_orderOf_dvd_card' (G := ↥c.D1) 3 (by simpa [c.hD13]))
  have hk1ordD : orderOf k1D = 3 :=
    Classical.choose_spec (exists_prime_orderOf_dvd_card' (G := ↥c.D1) 3 (by simpa [c.hD13]))
  let k1 : H := (k1D : H)
  have hk1D1 : k1 ∈ c.D1 := k1D.2
  have hk13 : orderOf k1 = 3 := by
    have h := hk1ordD
    rwa [Subgroup.orderOf_mk] at h
  have hk1zp : Subgroup.zpowers k1 = c.D1 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk1D1) ?_
    rw [Nat.card_zpowers, hk13, c.hD13]
  have hk1K : k1 ∈ c.K := c.hD1K hk1D1
  have hex : ∃ g ∈ c.L2, ∀ l ∈ c.L2, k1 * l * k1⁻¹ * (g * l * g⁻¹)⁻¹ ∈ c.Qβ := by
    simpa only [c.hQ2eq] using exists_conjugator_mod_pCore (L := c.L2) c.hquotL2
      (c.hEβNL2 (c.hD1Eβ hk1D1)) hk13
  let gβ : H := Classical.choose hex
  have hgβspec := Classical.choose_spec hex
  obtain ⟨hgβL2, hconjβ⟩ := hgβspec
  have hgβN : gβ ∈ Subgroup.normalizer (c.S : Set H) :=
    mem_normalizer_of_conjugator_mod (K := c.K) (L := c.L2) (Q := c.Qβ) (S := c.S)
      c.hS2 c.hKN c.hQβS hk1K hconjβ
  have hgβB2 : gβ ∈ c.S ⊔ c.D2 := by
    have h : gβ ∈ borelOf c.L2 c.S := by
      rw [borelOf, inf_eq_left.mpr c.hS2]
      exact ⟨hgβL2, hgβN⟩
    rwa [← c.hB2eq] at h
  have hgβK : gβ ∈ c.K := (sup_le c.hSK c.hD2K) hgβB2
  have hx0βNotS : gβ⁻¹ * k1 ∉ c.S := by
    intro hx0S
    have hk1B2 : k1 ∈ c.S ⊔ c.D2 := by
      have h : k1 = gβ * (gβ⁻¹ * k1) := by group
      rw [h]
      exact (c.S ⊔ c.D2).mul_mem hgβB2 (Subgroup.mem_sup_left hx0S)
    have hD1leB2 : c.D1 ≤ c.S ⊔ c.D2 := by
      calc c.D1 = Subgroup.zpowers k1 := hk1zp.symm
        _ ≤ c.S ⊔ c.D2 := Subgroup.zpowers_le.mpr hk1B2
    have hle : c.S ⊔ c.D1 ≤ c.S ⊔ c.D2 := by
      apply sup_le
      · exact (le_sup_left : c.S ≤ c.S ⊔ c.D2)
      · exact hD1leB2
    have heq : c.S ⊔ c.D1 = c.S ⊔ c.D2 :=
      sup_S_D1_eq_sup_S_D2_of_le (S := c.S) (D1 := c.D1) (D2 := c.D2)
        c.hD13 c.hD23 c.hD1N c.hD2N c.hD1notS c.hD2notS hle
    have hD2leB1 : c.D2 ≤ c.S ⊔ c.D1 := by
      calc c.D2 ≤ c.S ⊔ c.D2 := le_sup_right
        _ = c.S ⊔ c.D1 := heq.symm
    exact c.hnot (hD2leB1.trans (sup_le c.hS1 c.hD1L1))
  let rβ : H := Classical.choose (exists_orderThree_fixedFree_of_commutatorKernel
    (K := c.K) (S := c.S) (L := c.L2) (Q := c.Qβ) (E := c.Eβ)
    c.hrelK c.hSnormK c.hS2p c.hKQβ c.hKleEβ c.hL2NQβ
    c.hQ2eq.symm c.hquotL2 c.hQβab c.hcardQβ c.hnat2 c.hcharP2 c.hQβE
    hk1K hgβL2 hgβK hconjβ hx0βNotS)
  have hrβspec := Classical.choose_spec (exists_orderThree_fixedFree_of_commutatorKernel
    (K := c.K) (S := c.S) (L := c.L2) (Q := c.Qβ) (E := c.Eβ)
    c.hrelK c.hSnormK c.hS2p c.hKQβ c.hKleEβ c.hL2NQβ
    c.hQ2eq.symm c.hquotL2 c.hQβab c.hcardQβ c.hnat2 c.hcharP2 c.hQβE
    hk1K hgβL2 hgβK hconjβ hx0βNotS)
  obtain ⟨hrβK, hrβ3, hrβnotS, hrβcent, hrβbot⟩ := hrβspec
  have hfreeQ : ∀ q ∈ c.Qβ, rβ * q * rβ⁻¹ = q → q = 1 :=
    fixedPointFree_of_inf_centralizer_eq_bot hrβbot
  exact
    { rβ := rβ, hrβK := hrβK, hrβ3 := hrβ3, hrβnotS := hrβnotS,
      hfree := fun q hq => hfreeQ q (by
        have h := hq
        rw [c.hA1eq] at h
        exact h.2), hrβcent := hrβcent }

private noncomputable def setup_of_l34Data
    {L1 L2 S D1 D2 : Subgroup H} (hF : F112HypW L1 L2 S)
    (hVA1 : VA5 L1) (hVA2 : VA5 L2)
    (hD1 : L34VertexData (f112saP1' L1 L2 S))
    (hD2 : L34VertexData (f112saP2' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S =
      pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S))
    (hD1X : D1 ≤ f112saX1 L1 L2 S) (hD2X : D2 ≤ f112saX2 L1 L2 S)
    (hD13 : Nat.card D1 = 3) (hD23 : Nat.card D2 = 3)
    (hD1S : D1 ⊓ (S ⊓ L1) = ⊥) (hD2S : D2 ⊓ (S ⊓ L2) = ⊥)
    (hEαeq : f112saP1' L1 L2 S = oTwoPrime (f112saP1' L1 L2 S) ⊔ D2)
    (hEβeq : f112saP2' L1 L2 S = oTwoPrime (f112saP2' L1 L2 S) ⊔ D1)
    (hKeq : f112saK L1 L2 S = (S ⊓ f112saK L1 L2 S) ⊔ D1 ⊔ D2)
    (hnot : ¬ D2 ≤ L1) :
    L34Setup H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let Qα := pCoreOf 2 Eα
  let Qβ := pCoreOf 2 Eβ
  let K := f112saK L1 L2 S
  let A1 := Qα ⊓ Qβ
  have hV1 : TransferVertexData Eα := transferVertexData_of_l34VertexData hD1
  have hV2 : TransferVertexData Eβ := transferVertexData_of_l34VertexData hD2
  have hSK : S ≤ K := f112sa_le_K_of_transfer hF hVA1 hVA2 hV1 hV2 hT
  have hSL1 := f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData hF hVA1 hSK hV1
  have hSL2 := f112sa_S_le_L2_and_eq_oTwoPrime_of_transferVertexData hF hVA2 hSK hV2
  have hS1 : S ≤ L1 := hSL1.1
  have hS2 : S ≤ L2 := hSL2.1
  have hL1eq : L1 = oTwoPrime Eα := hSL1.2.1
  have hL2eq : L2 = oTwoPrime Eβ := hSL2.2.1
  have hQ1eq : pCoreOf 2 L1 = Qα := hSL1.2.2
  have hQ2eq : pCoreOf 2 L2 = Qβ := hSL2.2.2
  have hT' : S = Qα ⊔ Qβ := by
    have h := hT
    rw [show S ⊓ K = S from inf_eq_left.mpr hSK] at h
    exact h
  have hQαS : Qα ≤ S := by rw [hT']; exact le_sup_left
  have hQβS : Qβ ≤ S := by rw [hT']; exact le_sup_right
  have hQαK : Qα ≤ K := hQαS.trans hSK
  have hQβK : Qβ ≤ K := hQβS.trans hSK
  have hKleEα : K ≤ Eα := f112saK_le_P1' L1 L2 S
  have hKleEβ : K ≤ Eβ := f112saK_le_P2' L1 L2 S
  have hKQα : K ≤ Subgroup.normalizer (Qα : Set H) :=
    hKleEα.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Eα)
  have hKQβ : K ≤ Subgroup.normalizer (Qβ : Set H) :=
    hKleEβ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Eβ)
  have hL1NQα : L1 ≤ Subgroup.normalizer (Qα : Set H) := by
    rw [← hQ1eq]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L1
  have hL2NQβ : L2 ≤ Subgroup.normalizer (Qβ : Set H) := by
    rw [← hQ2eq]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L2
  have hQβL2 : Qβ ≤ L2 := by
    rw [← hQ2eq]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 L2
  have hD1L1 : D1 ≤ L1 :=
    hD1X.trans ((inf_le_left : f112saX1 L1 L2 S ≤ oTwoRes L1).trans (oTwoRes_le L1))
  have hD2L2 : D2 ≤ L2 :=
    hD2X.trans ((inf_le_left : f112saX2 L1 L2 S ≤ oTwoRes L2).trans (oTwoRes_le L2))
  have hD1K : D1 ≤ K := hD1X.trans (le_sup_left : f112saX1 L1 L2 S ≤ K)
  have hD2K : D2 ≤ K := hD2X.trans (le_sup_right : f112saX2 L1 L2 S ≤ K)
  have hD2Eα : D2 ≤ Eα := by
    dsimp only [Eα]
    rw [hEαeq]
    exact le_sup_right
  have hD1Eβ : D1 ≤ Eβ := by
    dsimp only [Eβ]
    rw [hEβeq]
    exact le_sup_right
  have hSnormK : (S.subgroupOf K).Normal := by
    have h := f112sa_T_normal_K hT
    rwa [show S ⊓ K = S from inf_eq_left.mpr hSK] at h
  have hKN : K ≤ Subgroup.normalizer (S : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).mp hSnormK
  have hD1N : D1 ≤ Subgroup.normalizer (S : Set H) := hD1K.trans hKN
  have hD2N : D2 ≤ Subgroup.normalizer (S : Set H) := hD2K.trans hKN
  have hD1Sbot : D1 ⊓ S = ⊥ := by
    have h := hD1S
    rwa [inf_eq_left.mpr hS1] at h
  have hD2Sbot : D2 ⊓ S = ⊥ := by
    have h := hD2S
    rwa [inf_eq_left.mpr hS2] at h
  have hD1notS : ¬ D1 ≤ S := by
    intro hle
    have hbot : D1 = ⊥ := by rw [← hD1Sbot, inf_comm, inf_eq_right.mpr hle]
    have hcard1 : Nat.card D1 = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hD2notS : ¬ D2 ≤ S := by
    intro hle
    have hbot : D2 = ⊥ := by rw [← hD2Sbot, inf_comm, inf_eq_right.mpr hle]
    have hcard1 : Nat.card D2 = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  let e1 := Classical.choice hVA1
  let e1b := Classical.choice CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  let e2 := Classical.choice hVA2
  let e2b := Classical.choice CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  have hB1eq : S ⊔ D1 = borelOf L1 S :=
    FA5.borelOf_eq_sup_cartan_of_le (L := L1) (S := S) (D := D1)
      hF.1.h1.sylow (e1.trans e1b) hS1 hD1L1 hD1N hD13 hD1notS
  have hB2eq : S ⊔ D2 = borelOf L2 S :=
    FA5.borelOf_eq_sup_cartan_of_le (L := L2) (S := S) (D := D2)
      hF.1.h2.sylow (e2.trans e2b) hS2 hD2L2 hD2N hD23 hD2notS
  have hB1leL1 : S ⊔ D1 ≤ L1 := sup_le hS1 hD1L1
  have hEαNL1 : Eα ≤ Subgroup.normalizer (L1 : Set H) := by
    rw [hL1eq]
    exact le_normalizer_oTwoPrime Eα
  have hEβNL2 : Eβ ≤ Subgroup.normalizer (L2 : Set H) := by
    rw [hL2eq]
    exact le_normalizer_oTwoPrime Eβ
  have hcommSQα : ∀ s ∈ S, ∀ q ∈ S, ⁅s, q⁆ ∈ Qα :=
    fun s hs q hq => CFSG.RankThree.PartOne.KE.commutator_mem_of_mem_sup_normalizer
      (hQβK.trans hKQα)
      (fun a ha b hb => congrArg Subtype.val (hD2.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      (by rw [sup_comm, ← hT']; exact hs) (by rw [sup_comm, ← hT']; exact hq)
  have hrelK : S.relIndex K = 9 :=
    f112sa_relIndex_S_K_eq_nine_of_not_le hF hVA1 hV1 hT hSK
      hD1X hD2X hD13 hD23 hD1S hKeq hnot
  have hA1card : Nat.card A1 = 4 :=
    f112sa_card_inf_pCoreOf_eq_four hF hVA1 hD1 hD2 hT hSK
  have hScentralA1 : S ≤ Subgroup.centralizer (A1 : Set H) :=
    f112sa_S_le_centralizer_A1 hD1 hD2 hT hSK
  have hKnormalA1 : K ≤ Subgroup.normalizer (A1 : Set H) :=
    f112sa_K_le_normalizer_A1 L1 L2 S
  exact
    { L1 := L1, L2 := L2, S := S, D1 := D1, D2 := D2, K := K,
      Eα := Eα, Eβ := Eβ, Qα := Qα, Qβ := Qβ, A1 := A1,
      hS1 := hS1, hS2 := hS2, hSK := hSK, hrelK := hrelK,
      hSnormK := hSnormK, hS2p := hF.1.h1.pgroup,
      hKN := hKN, hKQα := hKQα, hKQβ := hKQβ,
      hKleEα := hKleEα, hKleEβ := hKleEβ,
      hQαS := hQαS, hQβS := hQβS, hQβL2 := hQβL2,
      hL1NQα := hL1NQα, hL2NQβ := hL2NQβ,
      hQ1eq := hQ1eq, hQ2eq := hQ2eq, hQαE := rfl, hQβE := rfl,
      hQαab := hD1.elem.1, hQβab := hD2.elem.1,
      hQαexp := fun q hq => by
        have h := hD1.elem.2 q hq
        simpa [pow_two] using h,
      hQβexp := fun q hq => by
        have h := hD2.elem.2 q hq
        simpa [pow_two] using h,
      hcardQα := hD1.card, hcardQβ := hD2.card,
      hnat1 := hL1eq ▸ hD1.nat, hnat2 := hL2eq ▸ hD2.nat,
      hcharP1 := f112sa_charTwo_P1' hF, hcharP2 := f112sa_charTwo_P2' hF,
      hquotL1 := e1.trans e1b, hquotL2 := e2.trans e2b,
      hD1L1 := hD1L1, hD2L2 := hD2L2, hD1K := hD1K, hD2K := hD2K,
      hD1Eβ := hD1Eβ, hD2Eα := hD2Eα,
      hD13 := hD13, hD23 := hD23, hD1N := hD1N, hD2N := hD2N,
      hD1notS := hD1notS, hD2notS := hD2notS,
      hB1eq := hB1eq, hB2eq := hB2eq, hB1leL1 := hB1leL1,
      hEαNL1 := hEαNL1, hEβNL2 := hEβNL2, hnot := hnot,
      hA1eq := rfl, hA1card := hA1card,
      hScentralA1 := hScentralA1, hKnormalA1 := hKnormalA1,
      hcommSQα := hcommSQα }

private noncomputable def fourLines (c : L34Setup H) :
    FourLines c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let k1D : ↥c.D1 :=
    Classical.choose (exists_prime_orderOf_dvd_card' (G := ↥c.D1) 3 (by simpa [c.hD13]))
  have hk1ordD : orderOf k1D = 3 :=
    Classical.choose_spec (exists_prime_orderOf_dvd_card' (G := ↥c.D1) 3 (by simpa [c.hD13]))
  let k1 : H := (k1D : H)
  have hk1D1 : k1 ∈ c.D1 := k1D.2
  have hk13 : orderOf k1 = 3 := by
    have h := hk1ordD
    rwa [Subgroup.orderOf_mk] at h
  have hk1zp : Subgroup.zpowers k1 = c.D1 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk1D1) ?_
    rw [Nat.card_zpowers, hk13, c.hD13]
  have hk1K : k1 ∈ c.K := c.hD1K hk1D1
  have hk1notS : k1 ∉ c.S := by
    intro hle
    exact c.hD1notS (by rw [← hk1zp]; exact Subgroup.zpowers_le.mpr hle)
  have hk1L1 : k1 ∈ c.L1 := c.hD1L1 hk1D1
  have hfree_k1 : ∀ q ∈ c.A1, k1 * q * k1⁻¹ = q → q = 1 := by
    intro q hq hfix
    have hqQ : q ∈ c.Qα := by
      have h := hq
      rw [c.hA1eq] at h
      exact h.1
    exact fixedPointFree_of_natSec c.hnat1 hk1L1 hk13 q hqQ hfix
  let k2D : ↥c.D2 :=
    Classical.choose (exists_prime_orderOf_dvd_card' (G := ↥c.D2) 3 (by simpa [c.hD23]))
  have hk2ordD : orderOf k2D = 3 :=
    Classical.choose_spec (exists_prime_orderOf_dvd_card' (G := ↥c.D2) 3 (by simpa [c.hD23]))
  let k2 : H := (k2D : H)
  have hk2D2 : k2 ∈ c.D2 := k2D.2
  have hk23 : orderOf k2 = 3 := by
    have h := hk2ordD
    rwa [Subgroup.orderOf_mk] at h
  have hk2zp : Subgroup.zpowers k2 = c.D2 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk2D2) ?_
    rw [Nat.card_zpowers, hk23, c.hD23]
  have hk2K : k2 ∈ c.K := c.hD2K hk2D2
  have hk2notS : k2 ∉ c.S := by
    intro hle
    exact c.hD2notS (by rw [← hk2zp]; exact Subgroup.zpowers_le.mpr hle)
  have hk2L2 : k2 ∈ c.L2 := c.hD2L2 hk2D2
  have hfree_k2 : ∀ q ∈ c.A1, k2 * q * k2⁻¹ = q → q = 1 := by
    intro q hq hfix
    have hqQ : q ∈ c.Qβ := by
      have h := hq
      rw [c.hA1eq] at h
      exact h.2
    exact fixedPointFree_of_natSec c.hnat2 hk2L2 hk23 q hqQ hfix
  let rαd := ralphaData c
  let rβd := rbetaData c
  exact
    { k1 := k1, k2 := k2, rα := rαd.rα, rβ := rβd.rβ,
      hk1D1 := hk1D1, hk1K := hk1K, hk13 := hk13, hk1notS := hk1notS,
      hfree_k1 := hfree_k1,
      hk2D2 := hk2D2, hk2K := hk2K, hk23 := hk23, hk2notS := hk2notS,
      hfree_k2 := hfree_k2,
      hrαK := rαd.hrαK, hrα3 := rαd.hrα3, hrαnotS := rαd.hrαnotS,
      hfree_rα := rαd.hfree, hrαcent := rαd.hrαcent,
      hrβK := rβd.hrβK, hrβ3 := rβd.hrβ3, hrβnotS := rβd.hrβnotS,
      hfree_rβ := rβd.hfree, hrβcent := rβd.hrβcent }

private theorem false_of_fourLines (c : L34Setup H) (f : FourLines c) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := c.S.subgroupOf c.K
  haveI : N.Normal := c.hSnormK
  let Qk := ↥c.K ⧸ N
  let πK : ↥c.K →* Qk := QuotientGroup.mk' N
  let a1 : Qk := πK ⟨f.k1, f.hk1K⟩
  let a2 : Qk := πK ⟨f.k2, f.hk2K⟩
  let a3 : Qk := πK ⟨f.rα, f.hrαK⟩
  let a4 : Qk := πK ⟨f.rβ, f.hrβK⟩
  let H1 : Subgroup Qk := Subgroup.zpowers a1
  let H2 : Subgroup Qk := Subgroup.zpowers a2
  let H3 : Subgroup Qk := Subgroup.zpowers a3
  let H4 : Subgroup Qk := Subgroup.zpowers a4
  have hk1zp : Subgroup.zpowers f.k1 = c.D1 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr f.hk1D1) ?_
    rw [Nat.card_zpowers, f.hk13, c.hD13]
  have hk2zp : Subgroup.zpowers f.k2 = c.D2 := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr f.hk2D2) ?_
    rw [Nat.card_zpowers, f.hk23, c.hD23]
  have order3_of_class : ∀ {x : H} (hxK : x ∈ c.K), orderOf x = 3 → x ∉ c.S →
      orderOf (πK ⟨x, hxK⟩) = 3 := by
    intro x hxK hx3 hxnot
    apply orderOf_eq_prime
    · rw [← map_pow]
      have h : (⟨x, hxK⟩ : ↥c.K) ^ 3 = 1 := by
        apply Subtype.ext
        show x ^ 3 = 1
        rw [← hx3]
        exact pow_orderOf_eq_one x
      rw [h, map_one]
    · intro h1
      have hmem : (⟨x, hxK⟩ : ↥c.K) ∈ c.S.subgroupOf c.K := by
        simpa [πK, N, QuotientGroup.mk'_apply] using
          ((QuotientGroup.eq_one_iff (N := c.S.subgroupOf c.K) ⟨x, hxK⟩).mp h1)
      exact hxnot (Subgroup.mem_subgroupOf.mp hmem)
  have ha1 : orderOf a1 = 3 := order3_of_class f.hk1K f.hk13 f.hk1notS
  have ha2 : orderOf a2 = 3 := order3_of_class f.hk2K f.hk23 f.hk2notS
  have ha3 : orderOf a3 = 3 := order3_of_class f.hrαK f.hrα3 f.hrαnotS
  have ha4 : orderOf a4 = 3 := order3_of_class f.hrβK f.hrβ3 f.hrβnotS
  have hH1card : Nat.card H1 = 3 := by
    rw [show H1 = Subgroup.zpowers a1 from rfl, Nat.card_zpowers, ha1]
  have hH2card : Nat.card H2 = 3 := by
    rw [show H2 = Subgroup.zpowers a2 from rfl, Nat.card_zpowers, ha2]
  have hH3card : Nat.card H3 = 3 := by
    rw [show H3 = Subgroup.zpowers a3 from rfl, Nat.card_zpowers, ha3]
  have hH4card : Nat.card H4 = 3 := by
    rw [show H4 = Subgroup.zpowers a4 from rfl, Nat.card_zpowers, ha4]
  have hquotL1 : IsL2Quot 2 (oTwoQuot ↥c.L1) := by
    obtain ⟨ep⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
    exact ⟨c.hquotL1.trans ep.symm⟩
  have hquotL2 : IsL2Quot 2 (oTwoQuot ↥c.L2) := by
    obtain ⟨ep⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
    exact ⟨c.hquotL2.trans ep.symm⟩
  have hA1leQα : c.A1 ≤ c.Qα := by rw [c.hA1eq]; exact inf_le_left
  have hA1leQβ : c.A1 ≤ c.Qβ := by rw [c.hA1eq]; exact inf_le_right
  have h12 : H1 ≠ H2 := by
    intro heq
    have hmem : a2 ∈ H1 := by rw [heq]; exact Subgroup.mem_zpowers a2
    have hsup : f.k2 ∈ c.S ⊔ Subgroup.zpowers f.k1 :=
      mem_sup_of_quotient_mem_zpowers (K := c.K) (S := c.S) (x := f.k2) (y := ⟨f.k1, f.hk1K⟩)
        f.hk2K (by
          change (πK ⟨f.k2, f.hk2K⟩ : Qk) ∈ Subgroup.zpowers (πK ⟨f.k1, f.hk1K⟩)
          exact hmem)
    have hle : c.S ⊔ Subgroup.zpowers f.k1 ≤ c.L1 :=
      sup_le c.hS1 ((Subgroup.zpowers_le.mpr f.hk1D1).trans c.hD1L1)
    have hk2L1 : f.k2 ∈ c.L1 := hle hsup
    exact c.hnot (by rw [← hk2zp]; exact Subgroup.zpowers_le.mpr hk2L1)
  have h13 : H1 ≠ H3 := by
    intro heq
    have hmem : a3 ∈ H1 := by rw [heq]; exact Subgroup.mem_zpowers a3
    have hsup : f.rα ∈ c.S ⊔ Subgroup.zpowers f.k1 :=
      mem_sup_of_quotient_mem_zpowers (K := c.K) (S := c.S) (x := f.rα) (y := ⟨f.k1, f.hk1K⟩)
        f.hrαK (by
          change (πK ⟨f.rα, f.hrαK⟩ : Qk) ∈ Subgroup.zpowers (πK ⟨f.k1, f.hk1K⟩)
          exact hmem)
    have hle : c.S ⊔ Subgroup.zpowers f.k1 ≤ c.L1 :=
      sup_le c.hS1 ((Subgroup.zpowers_le.mpr f.hk1D1).trans c.hD1L1)
    have hrαL1 : f.rα ∈ c.L1 := hle hsup
    have hrαcore : f.rα ∈ pCoreOf 2 c.L1 :=
      mem_pCoreOf_of_forall_commutator_mem hquotL1 hrαL1 (fun l hl => by
        rw [c.hQ1eq]
        exact f.hrαcent l hl)
    have hrαQ : f.rα ∈ c.Qα := by
      rw [c.hQ1eq] at hrαcore
      exact hrαcore
    have hdvd : 3 ∣ Nat.card c.Qα := by
      have h := orderOf_dvd_natCard (⟨f.rα, hrαQ⟩ : ↥c.Qα)
      rw [Subgroup.orderOf_mk, f.hrα3, c.hcardQα] at h
      simpa [c.hcardQα] using h
    rw [c.hcardQα] at hdvd
    norm_num at hdvd
  have h14 : H1 ≠ H4 := by
    intro heq
    have hmem : a4 ∈ H1 := by rw [heq]; exact Subgroup.mem_zpowers a4
    have hsup : f.rβ ∈ c.S ⊔ Subgroup.zpowers f.k1 :=
      mem_sup_of_quotient_mem_zpowers (K := c.K) (S := c.S) (x := f.rβ) (y := ⟨f.k1, f.hk1K⟩)
        f.hrβK (by
          change (πK ⟨f.rβ, f.hrβK⟩ : Qk) ∈ Subgroup.zpowers (πK ⟨f.k1, f.hk1K⟩)
          exact hmem)
    have hle : c.S ⊔ Subgroup.zpowers f.k1 ≤ c.L1 :=
      sup_le c.hS1 ((Subgroup.zpowers_le.mpr f.hk1D1).trans c.hD1L1)
    have hrβL1 : f.rβ ∈ c.L1 := hle hsup
    have hfreeβQα : ∀ q ∈ c.Qα, f.rβ * q * f.rβ⁻¹ = q → q = 1 :=
      fixedPointFree_of_natSec c.hnat1 hrβL1 f.hrβ3
    have hcop : ∀ q ∈ c.Qα, q ∈ c.A1 := by
      intro q hq
      have hqL2 : q ∈ c.L2 := (c.hQαS.trans c.hS2) hq
      have hcommQβ : ⁅f.rβ, q⁆ ∈ c.Qβ := f.hrβcent q hqL2
      have hcommQα : ⁅f.rβ, q⁆ ∈ c.Qα := by
        have hqN : f.rβ * q * f.rβ⁻¹ ∈ c.Qα :=
          (Subgroup.mem_normalizer_iff.mp (c.hL1NQα hrβL1) q).mp hq
        rw [commutatorElement_def]
        exact c.Qα.mul_mem hqN (c.Qα.inv_mem hq)
      have hcommA : ⁅f.rβ, q⁆ ∈ c.A1 := by
        rw [c.hA1eq]
        exact ⟨hcommQα, hcommQβ⟩
      exact mem_of_commutator_mem_of_fixedPointFree c.hQαab c.hQαexp
        (c.hL1NQα hrβL1) f.hrβ3 hfreeβQα hA1leQα
        (c.hKnormalA1 f.hrβK) hq hcommA
    have hleQA : c.Qα ≤ c.A1 := hcop
    have hcardle : Nat.card c.Qα ≤ Nat.card c.A1 := Subgroup.card_le_of_le hleQA
    rw [c.hcardQα, c.hA1card] at hcardle
    norm_num at hcardle
  have h23 : H2 ≠ H3 := by
    intro heq
    have hmem : a3 ∈ H2 := by rw [heq]; exact Subgroup.mem_zpowers a3
    have hsup : f.rα ∈ c.S ⊔ Subgroup.zpowers f.k2 :=
      mem_sup_of_quotient_mem_zpowers (K := c.K) (S := c.S) (x := f.rα) (y := ⟨f.k2, f.hk2K⟩)
        f.hrαK (by
          change (πK ⟨f.rα, f.hrαK⟩ : Qk) ∈ Subgroup.zpowers (πK ⟨f.k2, f.hk2K⟩)
          exact hmem)
    have hle : c.S ⊔ Subgroup.zpowers f.k2 ≤ c.L2 :=
      sup_le c.hS2 ((Subgroup.zpowers_le.mpr f.hk2D2).trans c.hD2L2)
    have hrαL2 : f.rα ∈ c.L2 := hle hsup
    have hfreeαQβ : ∀ q ∈ c.Qβ, f.rα * q * f.rα⁻¹ = q → q = 1 :=
      fixedPointFree_of_natSec c.hnat2 hrαL2 f.hrα3
    have hcop : ∀ q ∈ c.Qβ, q ∈ c.A1 := by
      intro q hq
      have hqL1 : q ∈ c.L1 := (c.hQβS.trans c.hS1) hq
      have hcommQα : ⁅f.rα, q⁆ ∈ c.Qα := f.hrαcent q hqL1
      have hcommQβ : ⁅f.rα, q⁆ ∈ c.Qβ := by
        have hqN : f.rα * q * f.rα⁻¹ ∈ c.Qβ :=
          (Subgroup.mem_normalizer_iff.mp (c.hL2NQβ hrαL2) q).mp hq
        rw [commutatorElement_def]
        exact c.Qβ.mul_mem hqN (c.Qβ.inv_mem hq)
      have hcommA : ⁅f.rα, q⁆ ∈ c.A1 := by
        rw [c.hA1eq]
        exact ⟨hcommQα, hcommQβ⟩
      exact mem_of_commutator_mem_of_fixedPointFree c.hQβab c.hQβexp
        (c.hL2NQβ hrαL2) f.hrα3 hfreeαQβ hA1leQβ
        (c.hKnormalA1 f.hrαK) hq hcommA
    have hleQA : c.Qβ ≤ c.A1 := hcop
    have hcardle : Nat.card c.Qβ ≤ Nat.card c.A1 := Subgroup.card_le_of_le hleQA
    rw [c.hcardQβ, c.hA1card] at hcardle
    norm_num at hcardle
  have h24 : H2 ≠ H4 := by
    intro heq
    have hmem : a4 ∈ H2 := by rw [heq]; exact Subgroup.mem_zpowers a4
    have hsup : f.rβ ∈ c.S ⊔ Subgroup.zpowers f.k2 :=
      mem_sup_of_quotient_mem_zpowers (K := c.K) (S := c.S) (x := f.rβ) (y := ⟨f.k2, f.hk2K⟩)
        f.hrβK (by
          change (πK ⟨f.rβ, f.hrβK⟩ : Qk) ∈ Subgroup.zpowers (πK ⟨f.k2, f.hk2K⟩)
          exact hmem)
    have hle : c.S ⊔ Subgroup.zpowers f.k2 ≤ c.L2 :=
      sup_le c.hS2 ((Subgroup.zpowers_le.mpr f.hk2D2).trans c.hD2L2)
    have hrβL2 : f.rβ ∈ c.L2 := hle hsup
    have hrβcore : f.rβ ∈ pCoreOf 2 c.L2 :=
      mem_pCoreOf_of_forall_commutator_mem hquotL2 hrβL2 (fun l hl => by
        rw [c.hQ2eq]
        exact f.hrβcent l hl)
    have hrβQ : f.rβ ∈ c.Qβ := by
      rw [c.hQ2eq] at hrβcore
      exact hrβcore
    have hdvd : 3 ∣ Nat.card c.Qβ := by
      have h := orderOf_dvd_natCard (⟨f.rβ, hrβQ⟩ : ↥c.Qβ)
      rw [Subgroup.orderOf_mk, f.hrβ3, c.hcardQβ] at h
      simpa [c.hcardQβ] using h
    rw [c.hcardQβ] at hdvd
    norm_num at hdvd
  have h34 : H3 ≠ H4 := by
    intro heq
    have hmem : a4 ∈ H3 := by rw [heq]; exact Subgroup.mem_zpowers a4
    have hsup : f.rβ ∈ c.S ⊔ Subgroup.zpowers f.rα :=
      mem_sup_of_quotient_mem_zpowers (K := c.K) (S := c.S) (x := f.rβ) (y := ⟨f.rα, f.hrαK⟩)
        f.hrβK (by
          change (πK ⟨f.rβ, f.hrβK⟩ : Qk) ∈ Subgroup.zpowers (πK ⟨f.rα, f.hrαK⟩)
          exact hmem)
    obtain ⟨s, hs, w, hw, hsw⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes
        ((Subgroup.zpowers_le.mpr f.hrαK).trans c.hKN)).mp hsup
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hwcent : ∀ l ∈ c.L1, ⁅w, l⁆ ∈ c.Qα := by
      have hrα : f.rα ∈ dsCentMod c.K c.L1 c.Qα := ⟨f.hrαK, c.hKQα f.hrαK, f.hrαcent⟩
      have h : w ∈ dsCentMod c.K c.L1 c.Qα := by
        rw [← hi]; exact Subgroup.zpow_mem _ hrα i
      exact h.2.2
    have hcop : ∀ q ∈ c.Qβ, q ∈ c.A1 := by
      intro q hq
      have hqL1 : q ∈ c.L1 := (c.hQβS.trans c.hS1) hq
      have hwq : ⁅w, q⁆ ∈ c.Qα := hwcent q hqL1
      have hsq : ⁅s, q⁆ ∈ c.Qα := c.hcommSQα s hs q (c.hQβS hq)
      have hsN : s ∈ Subgroup.normalizer (c.Qα : Set H) := c.hL1NQα (c.hS1 hs)
      have hconj : s * ⁅w, q⁆ * s⁻¹ ∈ c.Qα :=
        (Subgroup.mem_normalizer_iff.mp hsN _).mp hwq
      have hcommQα : ⁅f.rβ, q⁆ ∈ c.Qα := by
        rw [hsw, commutatorElement_mul_left_eq_conj_mul]
        exact c.Qα.mul_mem hconj hsq
      have hcommQβ : ⁅f.rβ, q⁆ ∈ c.Qβ := f.hrβcent q (c.hQβL2 hq)
      have hcommA : ⁅f.rβ, q⁆ ∈ c.A1 := by
        rw [c.hA1eq]
        exact ⟨hcommQα, hcommQβ⟩
      have hcentbot : c.Qβ ⊓ Subgroup.centralizer ({f.rβ} : Set H) = ⊥ :=
        inf_centralizer_eq_bot_of_centralizes_mod
          (L := c.L2) (Q := c.Qβ) (E := c.Eβ) c.hL2NQβ c.hQβab c.hcardQβ
          hquotL2 c.hnat2 c.hQ2eq.symm (c.hKleEβ f.hrβK) (c.hKQβ f.hrβK)
          f.hrβ3 f.hrβcent c.hcharP2 c.hQβE
      have hfreeQβ : ∀ q ∈ c.Qβ, f.rβ * q * f.rβ⁻¹ = q → q = 1 :=
        fixedPointFree_of_inf_centralizer_eq_bot hcentbot
      exact mem_of_commutator_mem_of_fixedPointFree c.hQβab c.hQβexp
        (c.hKQβ f.hrβK) f.hrβ3 hfreeQβ hA1leQβ
        (c.hKnormalA1 f.hrβK) hq hcommA
    have hleQA : c.Qβ ≤ c.A1 := hcop
    have hcardle : Nat.card c.Qβ ≤ Nat.card c.A1 := Subgroup.card_le_of_le hleQA
    rw [c.hcardQβ, c.hA1card] at hcardle
    norm_num at hcardle
  have hdist : H1 ≠ H2 ∧ H1 ≠ H3 ∧ H1 ≠ H4 ∧ H2 ≠ H3 ∧ H2 ≠ H4 ∧ H3 ≠ H4 :=
    ⟨h12, h13, h14, h23, h24, h34⟩
  let φ : ↥c.K →* MulAut ↥c.A1 :=
    (Subgroup.normalizerMonoidHom c.A1).comp (Subgroup.inclusion c.hKnormalA1)
  have action_triv : ∀ {x : H} (hxK : x ∈ c.K), φ ⟨x, hxK⟩ = 1 →
      ∀ a : ↥c.A1, x * (a : H) * x⁻¹ = (a : H) := by
    intro x hxK hphi a
    have h := congrArg (fun g : MulAut ↥c.A1 => g a) hphi
    have h' : ((φ ⟨x, hxK⟩) a : ↥c.A1) = a := by simpa using h
    change ((Subgroup.normalizerMonoidHom c.A1)
      ((Subgroup.inclusion c.hKnormalA1) ⟨x, hxK⟩)) a = a at h'
    have h'' := congrArg Subtype.val h'
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] at h''
    simpa using h''
  have hSker : c.S.subgroupOf c.K ≤ φ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    have hsS : (s : H) ∈ c.S := Subgroup.mem_subgroupOf.mp hs
    have hcent := c.hScentralA1 hsS
    have hcomm : (s : H) * (a : H) = (a : H) * (s : H) :=
      (Subgroup.mem_centralizer_iff.mp hcent (a : H) a.2).symm
    dsimp only [φ, MonoidHom.comp_apply]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
    show (s : H) * (a : H) * (s : H)⁻¹ = (a : H)
    rw [hcomm]
    group
  have hker_ne : φ.ker ≠ c.S.subgroupOf c.K := by
    intro hker
    have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have hleft : Nat.card (↥c.K ⧸ φ.ker) = 9 := by
      rw [hker]
      exact c.hrelK
    have hrange : Nat.card φ.range ≤ Nat.card (MulAut ↥c.A1) :=
      Subgroup.card_le_card_group (H := φ.range)
    have haut : Nat.card (MulAut ↥c.A1) ≤ 6 := card_mulAut_le_of_card_four c.hA1card
    rw [← hcard, hleft] at hrange
    omega
  have hnotle : ¬ φ.ker ≤ c.S.subgroupOf c.K :=
    fun hle => hker_ne (le_antisymm hle hSker)
  obtain ⟨y, hyker, hyS⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hyK : (y : H) ∈ c.K := y.2
  have hyNotS : (y : H) ∉ c.S := fun h => hyS (Subgroup.mem_subgroupOf.mpr h)
  have hyTriv : φ y = 1 := MonoidHom.mem_ker.mp hyker
  have hyact : ∀ a : ↥c.A1, (y : H) * (a : H) * (y : H)⁻¹ = (a : H) :=
    action_triv hyK hyTriv
  haveI : Finite ↥c.A1 := Nat.finite_of_card_ne_zero (by rw [c.hA1card]; norm_num)
  haveI : Nontrivial ↥c.A1 :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [c.hA1card]; norm_num)
  have contradiction_of_triv : ∀ {x : H} (hxK : x ∈ c.K)
      (hfree : ∀ q ∈ c.A1, x * q * x⁻¹ = q → q = 1), φ ⟨x, hxK⟩ = 1 → False := by
    intro x hxK hfree hphi
    obtain ⟨a, ha1⟩ := exists_ne (1 : ↥c.A1)
    have hact := action_triv hxK hphi a
    have hq1 : x * (a : H) * x⁻¹ = (a : H) := hact
    exact ha1 (Subtype.ext (hfree (a : H) a.2 hq1))
  let ay : Qk := πK y
  have hay_ne : ay ≠ 1 := by
    intro h1
    have hmem : y ∈ c.S.subgroupOf c.K := by
      simpa [ay, πK, QuotientGroup.mk'_apply] using
        ((QuotientGroup.eq_one_iff (N := c.S.subgroupOf c.K) y).mp h1)
    exact hyS hmem
  have line_eq : ∀ {L : Subgroup Qk} (hL : Nat.card L = 3) {z : Qk},
      z ∈ L → z ≠ 1 → Subgroup.zpowers z = L := by
    intro L hL z hz hz1
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    have hz3 : orderOf z = 3 := by
      have hdvd : orderOf z ∣ 3 := by
        have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥L)
        rwa [Subgroup.orderOf_mk, hL] at h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h3
    rw [Nat.card_zpowers, hz3, hL]
  have hcover := exists_mem_of_card_eq_nine_of_four_lines
    (G := Qk) (by show Nat.card Qk = 9; dsimp [Qk, N]; exact c.hrelK)
    hH1card hH2card hH3card hH4card hdist ay
  have finish : ∀ {x : H} (hxK : x ∈ c.K)
      (hfree : ∀ q ∈ c.A1, x * q * x⁻¹ = q → q = 1)
      (hmem : πK ⟨x, hxK⟩ ∈ Subgroup.zpowers ay), False := by
    intro x hxK hfree hmem
    have hmem' : QuotientGroup.mk' (c.S.subgroupOf c.K) ⟨x, hxK⟩ ∈
        Subgroup.zpowers (QuotientGroup.mk' (c.S.subgroupOf c.K) y) := by
      change (πK ⟨x, hxK⟩ : Qk) ∈ Subgroup.zpowers (πK y)
      exact hmem
    have hxsup : x ∈ c.S ⊔ Subgroup.zpowers (y : H) :=
      mem_sup_of_quotient_mem_zpowers (K := c.K) (S := c.S) (x := x) (y := y)
        hxK hmem'
    obtain ⟨s, hs, w, hw, hsw⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes
        ((Subgroup.zpowers_le.mpr hyK).trans c.hKN)).mp hxsup
    have hsker : (⟨s, c.hSK hs⟩ : ↥c.K) ∈ φ.ker :=
      hSker (Subgroup.mem_subgroupOf.mpr hs)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hwker : (⟨w, (Subgroup.zpowers_le.mpr hyK) hw⟩ : ↥c.K) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hsub : (⟨w, (Subgroup.zpowers_le.mpr hyK) hw⟩ : ↥c.K) =
          y ^ i := Subtype.ext hi.symm
      rw [hsub, map_zpow, hyTriv, one_zpow]
    have hxker : φ ⟨x, hxK⟩ = 1 := by
      have hsub : (⟨x, hxK⟩ : ↥c.K) =
          ⟨s, c.hSK hs⟩ * ⟨w, (Subgroup.zpowers_le.mpr hyK) hw⟩ := Subtype.ext hsw
      rw [hsub, map_mul, MonoidHom.mem_ker.mp hsker, MonoidHom.mem_ker.mp hwker, one_mul]
    exact contradiction_of_triv hxK hfree hxker
  rcases hcover with h1 | h2 | h3 | h4
  · have hline : Subgroup.zpowers ay = H1 := line_eq hH1card h1 hay_ne
    have ha1mem : a1 ∈ Subgroup.zpowers ay := by rw [hline]; exact Subgroup.mem_zpowers a1
    exact finish f.hk1K f.hfree_k1 (by simpa [a1, πK] using ha1mem)
  · have hline : Subgroup.zpowers ay = H2 := line_eq hH2card h2 hay_ne
    have ha2mem : a2 ∈ Subgroup.zpowers ay := by rw [hline]; exact Subgroup.mem_zpowers a2
    exact finish f.hk2K f.hfree_k2 (by simpa [a2, πK] using ha2mem)
  · have hline : Subgroup.zpowers ay = H3 := line_eq hH3card h3 hay_ne
    have ha3mem : a3 ∈ Subgroup.zpowers ay := by rw [hline]; exact Subgroup.mem_zpowers a3
    exact finish f.hrαK f.hfree_rα (by simpa [a3, πK] using ha3mem)
  · have hline : Subgroup.zpowers ay = H4 := line_eq hH4card h4 hay_ne
    have ha4mem : a4 ∈ Subgroup.zpowers ay := by rw [hline]; exact Subgroup.mem_zpowers a4
    exact finish f.hrβK f.hfree_rβ (by simpa [a4, πK] using ha4mem)

private theorem f112sa_oTwoPrime_P1'_eq_of_l34Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (hVA1 : VA5 L1) (hVA2 : VA5 L2)
    (hD1 : L34VertexData (f112saP1' L1 L2 S))
    (hD2 : L34VertexData (f112saP2' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S =
      pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S)) :
    oTwoPrime (f112saP1' L1 L2 S) = f112saP1' L1 L2 S := by
  classical
  let Eα := f112saP1' L1 L2 S
  let Eβ := f112saP2' L1 L2 S
  let K := f112saK L1 L2 S
  have hV1 : TransferVertexData Eα := transferVertexData_of_l34VertexData hD1
  have hV2 : TransferVertexData Eβ := transferVertexData_of_l34VertexData hD2
  have hSK : S ≤ K := f112sa_le_K_of_transfer hF hVA1 hVA2 hV1 hV2 hT
  have hL1eq : L1 = oTwoPrime Eα :=
    (f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData hF hVA1 hSK hV1).2.1
  obtain ⟨D1, D2, hD1X, hD2X, hD13, hD23, hD1S, hD2S, hX1eq, hX2eq,
    hEαeq, hEβeq, hKeq⟩ := f112sa_exists_cartan_decomposition hF hVA1 hVA2
  have hD2le : D2 ≤ L1 := by
    by_contra hnot
    let c := setup_of_l34Data hF hVA1 hVA2 hD1 hD2 hT hD1X hD2X hD13 hD23
      hD1S hD2S hEαeq hEβeq hKeq hnot
    exact false_of_fourLines c (fourLines c)
  have hEαeq' : Eα = L1 ⊔ D2 := by
    dsimp only [Eα]
    rw [hEαeq, ← hL1eq]
  calc oTwoPrime Eα = L1 := hL1eq.symm
    _ = L1 ⊔ D2 := (sup_eq_left.mpr hD2le).symm
    _ = Eα := hEαeq'.symm

theorem f112sa_oTwoPrime_eq_of_l34Data {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD1 : L34VertexData (f112saP1' L1 L2 S)) (hD2 : L34VertexData (f112saP2' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S = pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S)) :
    oTwoPrime (f112saP1' L1 L2 S) = f112saP1' L1 L2 S ∧
      oTwoPrime (f112saP2' L1 L2 S) = f112saP2' L1 L2 S := by
  constructor
  · exact f112sa_oTwoPrime_P1'_eq_of_l34Data hF h1 h2 hD1 hD2 hT
  · have hD1' : L34VertexData (f112saP1' L2 L1 S) := by
      simpa [f112saP2'_eq_P1'_swap L1 L2 S] using hD2
    have hD2' : L34VertexData (f112saP2' L2 L1 S) := by
      simpa [f112saP1'_eq_P2'_swap L1 L2 S] using hD1
    have hTswap : S ⊓ f112saK L2 L1 S =
        pCoreOf 2 (f112saP1' L2 L1 S) ⊔ pCoreOf 2 (f112saP2' L2 L1 S) := by
      rw [f112saK_comm L1 L2 S, ← f112saP2'_eq_P1'_swap L1 L2 S,
        f112saP2'_eq_P1'_swap L2 L1 S, sup_comm]
      exact hT
    have h := f112sa_oTwoPrime_P1'_eq_of_l34Data hF.symm h2 h1 hD1' hD2' hTswap
    simpa [f112saP2'_eq_P1'_swap L1 L2 S] using h

theorem f112sa_bigB_le_inf_of_l34Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD1 : L34VertexData (f112saP1' L1 L2 S))
    (hD2 : L34VertexData (f112saP2' L1 L2 S))
    (hT : S ⊓ f112saK L1 L2 S =
      pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S)) :
    bigB L1 L2 S ≤ L1 ⊓ L2 ∧
      f112P1 L1 L2 S = L1 ∧ f112P2 L1 L2 S = L2 := by
  have hV1 : TransferVertexData (f112saP1' L1 L2 S) :=
    transferVertexData_of_l34VertexData hD1
  have hV2 : TransferVertexData (f112saP2' L1 L2 S) :=
    transferVertexData_of_l34VertexData hD2
  have hS : S ≤ f112saK L1 L2 S := f112sa_le_K_of_transfer hF h1 h2 hV1 hV2 hT
  have hNE := f112sa_oTwoPrime_eq_of_l34Data hF h1 h2 hD1 hD2 hT
  exact f112sa_bigB_le_inf_of_no_extra_torus hF h1 h2 hV1 hV2 hS hNE.1 hNE.2

end CFSG.Quasithin.F112R.St84
