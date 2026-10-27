module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46D4qDefs

import CFSG.Quasithin.Recognition.St84.Gen.L2SecFinite
import CFSG.Quasithin.Recognition.St84.Gen.NatSecCoord
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSec
import CFSG.CGT.Timmesfeld75.NodeAux
public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Sec7Setup

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open CFSG.Quasithin CFSG.Quasithin.F112R.St84
open scoped Pointwise commutatorElement MatrixGroups

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

private theorem s46d4q_pCoreOf_L (X : Setup Γ G) (i : ℤ) : pCoreOf 2 (X.L i) = X.Q i :=
  (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq

private theorem s46d4q_quot (X : Setup Γ G) (i : ℤ) : IsL2Quot (X.n i) (oTwoQuot ↥(X.L i)) :=
  (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot

private theorem s46d4q_finite (X : Setup Γ G) (i : ℤ) : Finite ↥(X.L i) :=
  finite_of_le_stabilizer X.hyp (H := X.L i) (X.L_le_Gi i)

private theorem s46d4q_Q_le_L (X : Setup Γ G) (i : ℤ) : X.Q i ≤ X.L i := by
  rw [← s46d4q_pCoreOf_L X i]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 (X.L i)

private theorem s46d4q_Gi_le_normalizer_Q (X : Setup Γ G) (i : ℤ) :
    X.Gi i ≤ Subgroup.normalizer (X.Q i : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i)

private theorem s46d4q_Gi_le_normalizer_Z (X : Setup Γ G) (i : ℤ) :
    X.Gi i ≤ Subgroup.normalizer (X.Z i : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact X.Z_normal i g hg

private theorem s46d4q_exists_not_mem (A : X.CaseAGen) {W : Subgroup G} (hWQ : W ≤ X.Q 0)
    (hne : W ≠ X.Q 0) : ∃ l ∈ X.L 0, ∃ v ∈ X.Q 0, ⁅l, v⁆ ∉ W := by
  by_contra hcon
  push Not at hcon
  apply hne
  refine le_antisymm hWQ ?_
  rw [← A.indec_Q0, Subgroup.commutator_le]
  intro x hx y hy
  have h := hcon y (oTwoRes_le (X.L 0) hy) x hx
  rw [← commutatorElement_inv]
  exact W.inv_mem h

private theorem s46d4q_relIndex_Z0 (A : X.CaseAGen) :
    (X.Z 0).relIndex (X.Q 0) = 2 ^ (2 * X.n 0 + 2 * X.n 1) := by
  have h := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Q 0)
  rw [inf_eq_left.mpr A.sec_Q0.1, A.card_Z0, A.card_Q0,
    show 2 * X.n 0 + 3 * X.n 1 = (2 * X.n 0 + 2 * X.n 1) + X.n 1 by ring, pow_add] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem CaseAGen.irred_Q0 (A : X.CaseAGen) (hn : X.n 1 < X.n 0) :
    ∀ W : Subgroup G, X.Z 0 ≤ W → W ≤ X.Q 0 → X.L 0 ≤ Subgroup.normalizer (W : Set G) →
      W = X.Z 0 ∨ W = X.Q 0 := by
  intro W hZW hWQ hLW
  by_contra hne
  push Not at hne
  obtain ⟨hWZ, hWQ'⟩ := hne
  haveI := s46d4q_finite X 0
  have hquot := s46d4q_quot X 0
  have hm : 1 ≤ X.n 0 := by have := A.two_le_n1; omega
  have hQL := s46d4q_Q_le_L X 0
  have hNQ : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (s46d4q_Gi_le_normalizer_Q X 0)
  have hNZ : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    (X.L_le_Gi 0).trans (s46d4q_Gi_le_normalizer_Z X 0)
  have hcore : ∀ p ∈ pCoreOf 2 (X.L 0), ∀ v ∈ X.Q 0, ⁅p, v⁆ ∈ X.Z 0 := by
    rw [s46d4q_pCoreOf_L X 0]
    intro p hp v hv
    exact Subgroup.commutator_le.mp A.sec_Q0.2.1 p hp v hv
  have hsecW : IsElemSec (X.Z 0) W :=
    ⟨hZW, (Subgroup.commutator_mono hWQ hWQ).trans A.sec_Q0.2.1,
      fun e he => A.sec_Q0.2.2 e (hWQ he)⟩
  have hsecQ : IsElemSec W (X.Q 0) :=
    ⟨hWQ, A.sec_Q0.2.1.trans hZW, fun e he => hZW (A.sec_Q0.2.2 e he)⟩
  have hnt1 : ∃ l ∈ X.L 0, ∃ v ∈ W, ⁅l, v⁆ ∉ X.Z 0 := by
    by_contra hcon
    push Not at hcon
    apply hWZ
    refine le_antisymm ?_ hZW
    have hLW' : ⁅X.L 0, W⁆ ≤ X.Z 0 := Subgroup.commutator_le.mpr hcon
    have hZc : ⁅X.Z 0, X.L 0⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, A.Z0_eq]
      exact inf_le_right
    have h1 : ⁅⁅X.L 0, W⁆, X.L 0⁆ = ⊥ :=
      le_bot_iff.mp (hZc ▸ Subgroup.commutator_mono hLW' le_rfl)
    have h2 : ⁅⁅W, X.L 0⁆, X.L 0⁆ = ⊥ := by
      rw [Subgroup.commutator_comm W]
      exact h1
    have h3 : ⁅⁅X.L 0, X.L 0⁆, W⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [A.perfect_L0, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    rw [A.Z0_eq]
    exact le_inf (hWQ.trans hQL) h3
  have h1 := two_pow_le_relIndex_of_nontrivial_of_le hm hquot (hWQ.trans hQL) hsecW
    (le_inf hLW hNZ) (fun p hp v hv => hcore p hp v (hWQ hv)) hnt1
  have h2 := two_pow_le_relIndex_of_nontrivial_of_le hm hquot hQL hsecQ (le_inf hNQ hLW)
    (fun p hp v hv => hZW (hcore p hp v hv)) (s46d4q_exists_not_mem A hWQ hWQ')
  have hmul := Subgroup.relIndex_mul_relIndex (X.Z 0) W (X.Q 0) hZW hWQ
  rw [s46d4q_relIndex_Z0 A] at hmul
  have h4 : 2 ^ (2 * X.n 0) * 2 ^ (2 * X.n 0) ≤ 2 ^ (2 * X.n 0 + 2 * X.n 1) := by
    rw [← hmul]
    exact Nat.mul_le_mul h1 h2
  rw [← pow_add] at h4
  have h5 : 2 ^ (2 * X.n 0 + 2 * X.n 1) < 2 ^ (2 * X.n 0 + 2 * X.n 0) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem CaseAGen.n0_eq (A : X.CaseAGen) (hn : X.n 1 ≠ X.n 0) : X.n 0 = 3 * X.n 1 := by
  have hlt : X.n 1 < X.n 0 := lt_of_le_of_ne A.n1_le_n0 hn
  haveI := s46d4q_finite X 0
  have hNQ : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (s46d4q_Gi_le_normalizer_Q X 0)
  have hNZ : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    (X.L_le_Gi 0).trans (s46d4q_Gi_le_normalizer_Z X 0)
  have hZQ : X.Z 0 ≠ X.Q 0 := by
    intro h
    have hc := s46d4q_relIndex_Z0 A
    rw [h, Subgroup.relIndex_self] at hc
    have : 1 < 2 ^ (2 * X.n 0 + 2 * X.n 1) := Nat.one_lt_two_pow (by omega)
    omega
  have h1 : 0 < X.n 1 := by have := A.two_le_n1; omega
  exact eq_three_mul_of_irreducible_of_relIndex_of_le h1 hlt (s46d4q_quot X 0)
    (s46d4q_Q_le_L X 0) A.sec_Q0.1 A.sec_Q0 (le_inf hNQ hNZ) (A.irred_Q0 hlt)
    (s46d4q_exists_not_mem A A.sec_Q0.1 hZQ) (s46d4q_relIndex_Z0 A)

theorem CaseAGen.center_Q1 (A : X.CaseAGen) : centerOf (X.Q 1) = X.Z 1 := by
  refine le_antisymm ?_ (X.Z_le_center 1)
  set C := centerOf (X.Q 1) with hCdef
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hZleC : X.Z 1 ≤ C := X.Z_le_center 1
  have hCQ : C ≤ X.Q 1 := inf_le_left
  have hCcent : ∀ c ∈ C, ∀ q ∈ X.Q 1, c * q = q * c := fun c hc q hq =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) q hq).symm
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  have hGC : X.Gi 1 ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centerOf_of_le_normalizer (s46d4q_Gi_le_normalizer_Q X 1)
  have hGsup : X.Gi 1 ≤ Subgroup.normalizer ((C ⊔ (X.Q 0 ⊓ X.Q 2) : Subgroup G) : Set G) :=
    (le_inf hGC A.normal_A1).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hcommQQ : X.Z 1 ≤ ⁅X.Q 1, X.Q 1⁆ := by
    rw [← A.comm_D]
    exact Subgroup.commutator_mono inf_le_left le_rfl
  have hZ1ne : X.Z 1 ≠ ⊥ := by
    intro hbot
    have hidx := A.natZ1.index
    rw [hbot, Subgroup.relIndex_self] at hidx
    have : 1 < 2 ^ (2 * X.n 1) := Nat.one_lt_two_pow (by have := A.two_le_n1; omega)
    omega
  have hCmem : C ≤ X.Q 0 ⊓ X.Q 2 := by
    rcases A.irred_W1 (C ⊔ (X.Q 0 ⊓ X.Q 2)) le_sup_right (sup_le hCQ A.sec_W1.1) hGsup with
      h | h
    · rw [← h]
      exact le_sup_left
    · exfalso
      have hCcomm : IsMulCommutative ↥C :=
        IsMulCommutative.of_comm (fun a b => Subtype.ext (hCcent (a : G) a.2 (b : G) (hCQ b.2)))
      have habel : IsMulCommutative ↥(X.Q 1) := by
        rw [← h]
        have hunion : C ⊔ (X.Q 0 ⊓ X.Q 2) =
            Subgroup.closure ((C : Set G) ∪ ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G)) := by
          rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
        rw [hunion]
        refine Subgroup.isMulCommutative_closure ?_
        intro x hx y hy _
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact congrArg Subtype.val (hCcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        · exact hCcent x hx y (A.sec_W1.1 hy)
        · exact (hCcent y hy x (A.sec_W1.1 hx)).symm
        · exact congrArg Subtype.val (A.elem_A1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      have hbot : ⁅X.Q 1, X.Q 1⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr habel
      exact hZ1ne (le_bot_iff.mp (hbot ▸ hcommQQ))
  have hCD : C ⊓ D = ⊥ := by
    refine le_bot_iff.mp ?_
    calc C ⊓ D ≤ Subgroup.centralizer (X.Q 1 : Set G) ⊓ D :=
          inf_le_inf_right _ (show C ≤ Subgroup.centralizer (X.Q 1 : Set G) from inf_le_right)
      _ = ⊥ := by rw [inf_comm]; exact A.D_cent
  have hCZ : C ⊓ (D ⊔ X.Z 1) ≤ X.Z 1 := by
    intro x hx
    obtain ⟨hxC, hxsup⟩ := Subgroup.mem_inf.mp hx
    have hDA : D ≤ X.Q 0 ⊓ X.Q 2 := by
      rw [A.A1_eq]
      exact le_sup_left
    have hDZnorm : D ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (X.Z 1 : Set G))
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact CFSG.CGT.Timmesfeld75.commute_of_isElemAbelian A.elem_A1 (hZA hz) (hDA hd)
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right D (X.Z 1) hDZnorm
    have hxmul : x ∈ (D : Set G) * (X.Z 1 : Set G) := by
      rw [← hcoe]
      exact hxsup
    obtain ⟨d, hd, z, hz, hdz⟩ := hxmul
    have hzC : z ∈ C := hZleC hz
    have hdC : d ∈ C := by
      have he : d = x * z⁻¹ := by rw [← hdz]; group
      rw [he]
      exact C.mul_mem hxC (C.inv_mem hzC)
    have hdbot : d ∈ (⊥ : Subgroup G) := by
      rw [← hCD]
      exact Subgroup.mem_inf.mpr ⟨hdC, hd⟩
    rw [Subgroup.mem_bot.mp hdbot] at hdz
    simp only [one_mul] at hdz
    rwa [← hdz]
  calc C = C ⊓ (X.Q 0 ⊓ X.Q 2) := (inf_eq_left.mpr hCmem).symm
    _ = C ⊓ (D ⊔ X.Z 1) := by rw [A.A1_eq]
    _ ≤ X.Z 1 := hCZ

private theorem s46d4q_pCoreOf_subgroupOf (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  exact CFSG.mem_openPCoreOf_iff x

theorem CaseAGen.nat_right (A : X.CaseAGen) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ X.n 1 ∧
      ∃ α : ↥(X.L 1) →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥(X.L 1) ∧
        IsNatSecOf (X.L 1) (centerOf (pCoreOf 2 (X.L 1))) ⊥ α := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := s46d4q_finite X 1
  have hn := A.two_le_n1
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  have hZQ : X.Z 1 ≤ X.Q 1 := (X.Z_le_center 1).trans inf_le_left
  have hZL : X.Z 1 ≤ X.L 1 := hZQ.trans (s46d4q_Q_le_L X 1)
  haveI : Finite ↥(X.Z 1) :=
    Finite.of_injective (Subgroup.inclusion hZL) (Subgroup.inclusion_injective hZL)
  have hT : IsSylowTwoOf X.S (X.L 1) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L_succ 0
  have hsec : IsElemSec ⊥ (X.Z 1) := by
    refine ⟨bot_le, ?_, fun e he => ?_⟩
    · have hbot : ⁅X.Q 0 ⊓ X.Q 2, X.Q 0 ⊓ X.Q 2⁆ = ⊥ :=
        Subgroup.commutator_self_eq_bot_iff.mpr A.elem_A1.1
      exact hbot ▸ Subgroup.commutator_mono hZA hZA
    · rw [A.elem_A1.2 e (hZA he)]
      exact one_mem _
  have hcore : ∀ x ∈ pCoreOf 2 (X.L 1), ∀ e ∈ X.Z 1, ⁅x, e⁆ ∈ (⊥ : Subgroup G) := by
    rw [s46d4q_pCoreOf_L X 1]
    intro x hx e he
    have hc : x * e = e * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 1 he)).2 x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, hc]
  have hEZ : X.Z 1 ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g _ =>
    Subgroup.mem_normalizer_iff.mpr fun x => by
      simp only [SetLike.mem_coe, Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro h
        simpa using h
  have hnt : ∃ l ∈ X.L 1, ∃ e ∈ X.Z 1, ⁅l, e⁆ ∉ (⊥ : Subgroup G) := by
    by_contra hcon
    push Not at hcon
    have hrel : relCent (X.Z 1) ⊥ X.S = X.Z 1 := by
      refine le_antisymm (fun _ h => h.1) fun e he => (mem_relCent hEZ).mpr ⟨he, ?_⟩
      intro a ha
      have h := hcon a (hT.1 ha) e he
      rw [Subgroup.mem_bot] at h ⊢
      rw [← commutatorElement_inv, h, inv_one]
    have hline := A.natZ1.line X.S hT
    rw [hrel, A.natZ1.index] at hline
    have : X.n 1 = 2 * X.n 1 := Nat.pow_right_injective le_rfl hline.symm
    omega
  obtain ⟨α, hα, hker, hnat⟩ := exists_isNatSecOf_of_two_pow_le (L := X.L 1) (E := X.Z 1)
    (Z := ⊥) (T := X.S) hn (s46d4q_quot X 1) hsec A.natZ1.normal hcore A.natZ1.index hnt hT
    (A.natZ1.line X.S hT).ge
  letI : Fintype (GaloisField 2 (X.n 1)) := Fintype.ofFinite _
  refine ⟨GaloisField 2 (X.n 1), inferInstance, inferInstance, ?_, α, hα, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (X.n 1) (by omega)
  · rw [hker]
    exact s46d4q_pCoreOf_subgroupOf (X.L 1)
  · rw [s46d4q_pCoreOf_L X 1, A.center_Q1]
    exact hnat

private theorem s46d4q_card_sup {D Z : Subgroup G} [Finite ↥D] [Finite ↥Z]
    (hDZ : D ≤ Subgroup.normalizer (Z : Set G)) (hinf : D ⊓ Z = ⊥) :
    Nat.card ↥(D ⊔ Z) = Nat.card ↥D * Nat.card ↥Z := by
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right D Z hDZ
  let φ : ↥D × ↥Z → ↥(D ⊔ Z) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have h : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val hpq
      have hmem : (q.1 : G)⁻¹ * (p.1 : G) ∈ D ⊓ Z := by
        refine Subgroup.mem_inf.mpr ⟨D.mul_mem (D.inv_mem q.1.2) p.1.2, ?_⟩
        have he : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
        rw [he]
        exact Z.mul_mem q.2.2 (Z.inv_mem p.2.2)
      rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have h2 : (p.2 : G) = (q.2 : G) := by
        rw [← hmem] at h
        exact mul_left_cancel h
      exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext h2)
    · have hx : (x : G) ∈ (D : Set G) * (Z : Set G) := by
        rw [← hcoe]
        exact x.2
      obtain ⟨d, hd, z, hz, hdz⟩ := hx
      exact ⟨(⟨d, hd⟩, ⟨z, hz⟩), Subtype.ext hdz⟩
  rw [← Nat.card_prod]
  exact (Nat.card_eq_of_bijective φ hbij).symm

private theorem s46d4q_mid_right (A : X.CaseAGen) (h3 : X.n 0 = 3 * X.n 1) :
    ∃ W : Subgroup G, centerOf (pCoreOf 2 (X.L 1)) ≤ W ∧ W ≤ pCoreOf 2 (X.L 1) ∧
      Nat.card W = 2 ^ (5 * X.n 1) ∧ ⁅W, X.L 1⁆ ≤ centerOf (pCoreOf 2 (X.L 1)) := by
  rw [s46d4q_pCoreOf_L X 1, A.center_Q1]
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_right
  have hDA : X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [A.A1_eq]
    exact le_sup_left
  have hQfin : Finite ↥(X.Q 1) := finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  haveI : Finite ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  haveI : Finite ↥(X.Z 1) :=
    Finite.of_injective (Subgroup.inclusion (hZA.trans A.sec_W1.1))
      (Subgroup.inclusion_injective _)
  have hDZ : X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) ≤
      Subgroup.normalizer (X.Z 1 : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (X.Z 1 : Set G))
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact CFSG.CGT.Timmesfeld75.commute_of_isElemAbelian A.elem_A1 (hZA hz) (hDA hd)
  have hcardZ : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
    rw [← Subgroup.relIndex_bot_left, A.natZ1.index]
  refine ⟨X.Q 0 ⊓ X.Q 2, hZA, A.sec_W1.1, ?_, A.comm_A1⟩
  rw [A.A1_eq, s46d4q_card_sup hDZ A.D_inf, A.card_D, hcardZ, h3, ← pow_add]
  ring_nf

theorem caseA_d4q (X : Setup Γ G) (A : X.CaseAGen) (hn : X.n 1 ≠ X.n 0) :
    X.n 0 = 3 * X.n 1 ∧ D4qLocalData (X.L 0) (X.L 1) X.S (X.n 1) ∧
      ∀ k ∈ X.L 1, Odd (orderOf k) → k ≠ 1 →
        pCoreOf 2 (X.L 1) ⊓ Subgroup.centralizer ({k} : Set G) ≤ pCoreOf 2 (X.L 0) := by
  have h3 := A.n0_eq hn
  have hlt : X.n 1 < X.n 0 := lt_of_le_of_ne A.n1_le_n0 hn
  refine ⟨h3, ?_, ?_⟩
  · refine
      { card_S := ?_
        special_left := ?_
        center_left := ?_
        irred_left := ?_
        card_right := ?_
        nat_right := A.nat_right
        mid_right := s46d4q_mid_right A h3 }
    · rw [A.card_S, h3]
      ring_nf
    · rw [s46d4q_pCoreOf_L X 0]
      refine ⟨A.special_Q0, ?_, ?_⟩
      · rw [A.card_Q0, h3, ← pow_mul]
        ring_nf
      · have hmapc : (Subgroup.center ↥(X.Q 0)).map (X.Q 0).subtype = centerOf (X.Q 0) := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hy) ⟨z, hz⟩)
          · rintro ⟨hxP, hxC⟩
            refine Subgroup.mem_map_of_mem (X.Q 0).subtype (x := ⟨x, hxP⟩) ?_
            rw [Subgroup.mem_center_iff]
            intro z
            exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC z.1 z.2)
        rw [← Subgroup.card_map_of_injective (X.Q 0).subtype_injective, hmapc, A.center_Q0,
          A.card_Z0]
    · rw [s46d4q_pCoreOf_L X 0, A.center_Q0, A.Z0_eq]
    · rw [s46d4q_pCoreOf_L X 0, A.center_Q0]
      exact A.irred_Q0 hlt
    · rw [s46d4q_pCoreOf_L X 1, A.card_Q1, h3]
      ring_nf
  · intro k hk hodd hk1 x hx
    rw [s46d4q_pCoreOf_L X 1] at hx
    rw [s46d4q_pCoreOf_L X 0]
    obtain ⟨hxQ, hxk⟩ := Subgroup.mem_inf.mp hx
    have hc : k * x = x * k :=
      Subgroup.mem_centralizer_iff.mp hxk k (Set.mem_singleton k)
    have hcomm : ⁅x, k⁆ ∈ X.Q 0 ⊓ X.Q 2 := by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc.symm]
      exact one_mem _
    exact (Subgroup.mem_inf.mp (A.fpf_W1 k hk hodd hk1 x hxQ hcomm)).1

end Setup

end CFSG.Quasithin.St84

end
