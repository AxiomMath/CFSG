module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W7NineFourSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFiveCent
public import CFSG.CGT.Foote82.EF1Steps
public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.GroupTheory.DedekindNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement
open CFSG.CGT.Foote82

variable {G : Type} [Group G] [Finite G]

theorem w7_9_map_conj_pCoreOf {H : Subgroup G} {g : G} (hg : g ∈ H) :
    (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = pCoreOf 2 H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H) hg)

theorem w7_9_map_conj_iSup {Y P : Subgroup G} {g : G} (hg : g ∈ Y) :
    (⨆ y : ↥Y, P.map (MulAut.conj (y : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      ⨆ y : ↥Y, P.map (MulAut.conj (y : G)).toMonoidHom := by
  rw [Subgroup.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun y => ?_
    rw [← map_conj_mul_eq P g (y : G)]
    exact le_iSup (fun z : ↥Y => P.map (MulAut.conj (z : G)).toMonoidHom)
      ⟨g * (y : G), Y.mul_mem hg y.2⟩
  · refine iSup_le fun z => ?_
    have hgz : g⁻¹ * (z : G) ∈ Y := Y.mul_mem (Y.inv_mem hg) z.2
    have h := le_iSup (fun y : ↥Y =>
      (P.map (MulAut.conj (y : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom)
      ⟨g⁻¹ * (z : G), hgz⟩
    rw [← map_conj_mul_eq P g (g⁻¹ * (z : G))] at h
    rwa [show g * (g⁻¹ * (z : G)) = (z : G) by group] at h

theorem w7_9_le_normalizer_of_commutator_le_pCore {H L S : Subgroup G}
    (hL : IsTwoPrimeComponent H L) (hSH : S ≤ H) (hSL : ⁅S, L⁆ ≤ pCoreOf 2 H) :
    S ≤ Subgroup.normalizer (L : Set G) := by
  have hpc : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H := by
    rw [CFSG.Open.pCoreOf, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hbot : ⁅barM H S, barM H L⁆ = ⊥ := by
    rw [barM, barM, ← Subgroup.map_commutator,
      CFSG.GroupTheory.commutator_subgroupOf_eq hSH hL.le, Subgroup.map_eq_bot_iff]
    calc (⁅S, L⁆).subgroupOf H ≤ (pCoreOf 2 H).subgroupOf H :=
          Subgroup.subgroupOf_mono H hSL
      _ = CFSG.pCore 2 ↥H := hpc
      _ = (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker := (QuotientGroup.ker_mk' _).symm
  refine hL.le_normalizer ?_ hSH
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
    (Subgroup.centralizer_le_normalizer _)

theorem le_oUpperTwo_sup_of_isSylowTwoOf {X R Y A Q : Subgroup G} (hY : Y = X ⊔ R)
    (hRY : Y ≤ normalizer (R : Set G)) (hR : IsPGroup 2 R) (hAY : A ≤ Y)
    (hOA : S17.oUpperTwo X ≤ A) (hQ : IsSylowTwoOf Q A) : A ≤ S17.oUpperTwo X ⊔ Q := by
  classical
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := by
    rw [hY] at hRY
    exact le_sup_left.trans hRY
  have hpow : ∀ a ∈ A, ∃ k : ℕ, a ^ (2 ^ k) ∈ S17.oUpperTwo X ⊔ R := by
    intro a ha
    have ha' : a ∈ (X ⊔ R : Subgroup G) := hY ▸ hAY ha
    have hamul : a ∈ (↑(X ⊔ R) : Set G) := ha'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X R hXR] at hamul
    obtain ⟨x, hx, r, hr, rfl⟩ := hamul
    obtain ⟨k, hk⟩ := CFSG.GroupTheory.pow_two_pow_mem_oddOrderClosure X hx
    have hkO : x ^ 2 ^ k ∈ S17.oUpperTwo X := by
      rw [S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
      exact hk
    have hc : (x ^ 2 ^ k)⁻¹ * (x * r) ^ (2 ^ k) ∈ R :=
      CFSG.AGLEmbedding.AscEightFive.pow_mul_mem_of_normalizes (hXR hx) hr (2 ^ k)
    have hmul : (x * r) ^ (2 ^ k) =
        x ^ 2 ^ k * ((x ^ 2 ^ k)⁻¹ * (x * r) ^ (2 ^ k)) := by group
    refine ⟨k, ?_⟩
    rw [hmul]
    exact Subgroup.mul_mem_sup hkO hc
  have hclos : CFSG.GroupTheory.oddOrderClosure A ≤ S17.oUpperTwo X ⊔ R := by
    rw [CFSG.GroupTheory.oddOrderClosure_le_iff]
    rintro g ⟨hgA, hgold⟩
    obtain ⟨k, hk⟩ := hpow g hgA
    have hcop : Nat.Coprime (2 ^ k) (orderOf g) := by
      cases k with
      | zero => simp
      | succ k =>
          rw [Nat.coprime_pow_left_iff (Nat.succ_pos k)]
          simpa using hgold
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 2 ^ k) (x := g) hcop
    rw [← hm]
    exact Subgroup.pow_mem _ hk m
  have hA : A = CFSG.GroupTheory.oddOrderClosure A ⊔ Q :=
    (CFSG.GroupTheory.sup_sylow_eq A hQ.1 hQ.2.1 hQ.2.2).symm
  have hN1 : A ⊓ (S17.oUpperTwo X ⊔ R) = S17.oUpperTwo X ⊔ (A ⊓ R) :=
    CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hOA
      ((S17.oUpperTwo_le X).trans hXR)
  have hRQ : A ⊓ R ≤ Q :=
    le_of_isSylowTwoOf_of_le_normalizer hQ inf_le_left (hR.to_inf_right (H := A))
      ((le_inf Subgroup.le_normalizer (hAY.trans hRY)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := A) (K := R)))
  have hN1Q : A ⊓ (S17.oUpperTwo X ⊔ R) ≤ S17.oUpperTwo X ⊔ Q := by
    rw [hN1]
    exact sup_le le_sup_left (hRQ.trans le_sup_right)
  calc A = CFSG.GroupTheory.oddOrderClosure A ⊔ Q := hA
    _ ≤ (A ⊓ (S17.oUpperTwo X ⊔ R)) ⊔ Q :=
        sup_le_sup (le_inf (CFSG.GroupTheory.oddOrderClosure_le A) hclos) le_rfl
    _ ≤ (S17.oUpperTwo X ⊔ Q) ⊔ Q := sup_le_sup hN1Q le_rfl
    _ = S17.oUpperTwo X ⊔ Q := by rw [sup_assoc, sup_idem]

theorem w7_9_exists_sylow_fixed {M X Y H L : Subgroup G} (hYM : Y ≤ M)
    (hY : Y = X ⊔ pCoreOf 2 Y) (hYH : Y ≤ H) (hL : IsTwoPrimeComponent H L)
    (hcomm : ⁅Opp 2 (M ⊓ L), S17.oUpperTwo X⁆ ≤ pCoreOf 2 (Opp 2 (M ⊓ L))) :
    ∃ P₁ : Subgroup G, IsSylowTwoOf P₁ (M ⊓ L) ∧ P₁ ≤ L ∧
      Y ⊓ normalizer (L : Set G) ≤ normalizer (P₁ : Set G) := by
  classical
  have hXY : X ≤ Y := by
    rw [hY]
    exact le_sup_left
  by_cases hK : Opp 2 (M ⊓ L) ≤ pCoreOf 2 H
  · refine ⟨Opp 2 (M ⊓ L), ?_, ?_, ?_⟩
    · exact isSylowTwoOf_opp_of_isPGroup
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hK)
    · exact (s13_Thirteen2_pElementSubgroup_le 2 (M ⊓ L)).trans inf_le_right
    · refine ((le_inf ?_ inf_le_right).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := M) (K := L))).trans
        (normalizer_le_normalizer_opp (M ⊓ L))
      exact inf_le_left.trans (hYM.trans Subgroup.le_normalizer)
  · have hKL : Opp 2 (M ⊓ L) ≤ L :=
      (s13_Thirteen2_pElementSubgroup_le 2 (M ⊓ L)).trans inf_le_right
    obtain ⟨P, hP⟩ := exists_isSylowTwoOf (Opp 2 (M ⊓ L))
    have hOK : S17.oUpperTwo X ≤ Subgroup.normalizer (Opp 2 (M ⊓ L) : Set G) :=
      (le_normalizer_of_commutator_opp_le (A := M ⊓ L) (B := S17.oUpperTwo X) (P := P)
        hcomm hP).2
    have hOL : S17.oUpperTwo X ≤ Subgroup.normalizer (L : Set G) := by
      intro x hx
      have hxX : x ∈ X := S17.oUpperTwo_le X hx
      have hxH : x ∈ H := hYH (hXY hxX)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      by_contra hne
      have hKx : Opp 2 (M ⊓ L) ≤ L.map (MulAut.conj x).toMonoidHom := by
        rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp (hOK hx)]
        exact Subgroup.map_mono hKL
      have hle := opp_le_pCoreOf_of_le_conj hL hxH hne hKL hKx
      rw [opp_opp] at hle
      exact hK hle
    obtain ⟨Q, hQ⟩ := exists_isSylowTwoOf (Y ⊓ Subgroup.normalizer (L : Set G))
    have hQN : Q ≤ Subgroup.normalizer (Opp 2 (M ⊓ L) : Set G) := by
      have hQM : Q ≤ Subgroup.normalizer (M : Set G) :=
        (hQ.1.trans inf_le_left).trans (hYM.trans Subgroup.le_normalizer)
      have hQL : Q ≤ Subgroup.normalizer (L : Set G) := hQ.1.trans inf_le_right
      exact (le_inf hQM hQL).trans
        ((Subgroup.inf_normalizer_le_normalizer_inf (H := M) (K := L)).trans
          (normalizer_le_normalizer_opp (M ⊓ L)))
    obtain ⟨P₁, hP₁, hQP₁⟩ := exists_isSylowTwoOf_normalized hQ.2.1 hQN
    have hOP₁ : S17.oUpperTwo X ≤ Subgroup.normalizer (P₁ : Set G) :=
      (le_normalizer_of_commutator_opp_le (A := M ⊓ L) (B := S17.oUpperTwo X) (P := P₁)
        hcomm hP₁).1
    have hstep : Y ⊓ Subgroup.normalizer (L : Set G) ≤ S17.oUpperTwo X ⊔ Q :=
      le_oUpperTwo_sup_of_isSylowTwoOf (X := X) (R := pCoreOf 2 Y) (Y := Y)
        (A := Y ⊓ Subgroup.normalizer (L : Set G)) (Q := Q) hY
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) Y)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) inf_le_left
        (le_inf ((S17.oUpperTwo_le X).trans hXY) hOL) hQ
    refine ⟨P₁, isSylowTwoOf_of_isSylowTwoOf_opp hP₁, ?_,
      hstep.trans (sup_le hOP₁ hQP₁)⟩
    exact hP₁.1.trans hKL

theorem w7_9_conj_le_normalizer_of_isTwoPrimeComponent {H L Y P₁ : Subgroup G}
    (hL : IsTwoPrimeComponent H L) (hYH : Y ≤ H) (hPL : P₁ ≤ L) {y : G} (hy : y ∈ Y) :
    P₁.map (MulAut.conj y).toMonoidHom ≤ Subgroup.normalizer (L : Set G) := by
  by_cases hEq : L.map (MulAut.conj y).toMonoidHom = L
  · calc P₁.map (MulAut.conj y).toMonoidHom ≤ L.map (MulAut.conj y).toMonoidHom :=
        Subgroup.map_mono hPL
      _ = L := hEq
      _ ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  · refine w7_9_le_normalizer_of_commutator_le_pCore hL ?_ ?_
    · exact (Subgroup.map_mono hPL).trans (by
        intro z hz
        obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
        change MulAut.conj y l ∈ H
        rw [MulAut.conj_apply]
        exact H.mul_mem (H.mul_mem (hYH hy) (hL.le hl)) (H.inv_mem (hYH hy)))
    · refine (Subgroup.commutator_mono (Subgroup.map_mono hPL) le_rfl).trans ?_
      exact (hL.map_conj (hYH hy)).commutator_le hL hEq

theorem w7_9_conj_le_normalizer_iSup_conj_sup_pCoreOf {H L Y P₁ : Subgroup G}
    (hL : IsTwoPrimeComponent H L) (hYH : Y ≤ H) (hPL : P₁ ≤ L)
    (hst : Y ⊓ normalizer (L : Set G) ≤ normalizer (P₁ : Set G)) {a : G} (ha : a ∈ Y)
    (s : Finset ↥Y) :
    P₁.map (MulAut.conj a).toMonoidHom ≤
      Subgroup.normalizer (((⨆ y ∈ s, P₁.map (MulAut.conj (y : G)).toMonoidHom) ⊔
        pCoreOf 2 H : Subgroup G) : Set G) := by
  classical
  let A : ↥Y → Subgroup G := fun y => P₁.map (MulAut.conj (y : G)).toMonoidHom
  have hAHa : P₁.map (MulAut.conj a).toMonoidHom ≤ H := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
    change MulAut.conj a p ∈ H
    rw [MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem (hYH ha) (hL.le (hPL hp))) (H.inv_mem (hYH ha))
  refine le_normalizer_of_forall_map_conj_le ?_
  intro z hz
  have hzH : z ∈ H := hAHa hz
  simp only [Subgroup.map_sup, Subgroup.map_iSup]
  refine sup_le ?_ ?_
  · refine iSup_le fun y => iSup_le fun hy => ?_
    by_cases hEq : L.map (MulAut.conj (y : G)).toMonoidHom =
        L.map (MulAut.conj a).toMonoidHom
    · have hPA : A y = P₁.map (MulAut.conj a).toMonoidHom :=
        map_conj_eq_of_map_conj_eq hst y.2 ha hEq
      have hzA : z ∈ A y := hPA ▸ hz
      have hfix : (A y).map (MulAut.conj z).toMonoidHom = A y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hzA)
      rw [hfix]
      exact le_sup_of_le_left (le_iSup_of_le y (le_iSup_of_le hy le_rfl))
    · intro x hx
      obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hx
      have hcomm : ⁅P₁.map (MulAut.conj a).toMonoidHom, A y⁆ ≤ pCoreOf 2 H := by
        refine (Subgroup.commutator_mono (Subgroup.map_mono hPL)
          (Subgroup.map_mono hPL)).trans ?_
        exact (hL.map_conj (hYH ha)).commutator_le (hL.map_conj (hYH y.2))
          (fun h => hEq h.symm)
      have hconj : (MulAut.conj z).toMonoidHom t = z * t * z⁻¹ := MulAut.conj_apply z t
      rw [← htx, hconj,
        show z * t * z⁻¹ = ⁅z, t⁆ * t by rw [commutatorElement_def]; group,
        ← sup_comm (pCoreOf 2 H) (⨆ y ∈ s, A y)]
      exact Subgroup.mul_mem_sup (hcomm (Subgroup.commutator_mem_commutator hz ht))
        (Subgroup.mem_iSup_of_mem y (Subgroup.mem_iSup_of_mem hy ht))
  · rw [w7_9_map_conj_pCoreOf hzH]
    exact le_sup_right

theorem w7_9_isPGroup_iSup_conj_sup_pCoreOf {H L Y P₁ : Subgroup G}
    (hL : IsTwoPrimeComponent H L) (hYH : Y ≤ H) (hP : IsPGroup 2 P₁) (hPL : P₁ ≤ L)
    (hst : Y ⊓ normalizer (L : Set G) ≤ normalizer (P₁ : Set G)) :
    IsPGroup 2 (((⨆ y : ↥Y, P₁.map (MulAut.conj (y : G)).toMonoidHom) ⊔ pCoreOf 2 H :
      Subgroup G)) := by
  classical
  haveI : Fintype ↥Y := Fintype.ofFinite ↥Y
  let A : ↥Y → Subgroup G := fun y => P₁.map (MulAut.conj (y : G)).toMonoidHom
  let T : Finset ↥Y → Subgroup G := fun s => (⨆ y ∈ s, A y) ⊔ pCoreOf 2 H
  have hA2 : ∀ y : ↥Y, IsPGroup 2 (A y) := fun y => hP.map _
  have key : ∀ s : Finset ↥Y, IsPGroup 2 (T s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have h0 : T ∅ = pCoreOf 2 H := by simp [T]
        rw [h0]
        exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    | insert a s ha ih =>
        have hstep : T (insert a s) = T s ⊔ A a := by
          simp only [T, Finset.iSup_insert]
          ac_rfl
        rw [hstep]
        exact IsPGroup.to_sup_of_normal_left' ih (hA2 a)
          (w7_9_conj_le_normalizer_iSup_conj_sup_pCoreOf hL hYH hPL hst a.2 s)
  have hfin : T Finset.univ = (⨆ y : ↥Y, P₁.map (MulAut.conj (y : G)).toMonoidHom) ⊔
      pCoreOf 2 H := by simp [T, A]
  rw [← hfin]
  exact key Finset.univ

theorem w7_9_exists_orbit_pGroup {H L Y P₁ : Subgroup G} (hL : IsTwoPrimeComponent H L)
    (hYH : Y ≤ H) (hP : IsPGroup 2 P₁) (hPL : P₁ ≤ L)
    (hst : Y ⊓ normalizer (L : Set G) ≤ normalizer (P₁ : Set G)) :
    ∃ W : Subgroup G, P₁ ≤ W ∧ pCoreOf 2 H ≤ W ∧ IsPGroup 2 W ∧ W ≤ H ∧
      Y ≤ normalizer (W : Set G) ∧ W ≤ normalizer (L : Set G) := by
  classical
  haveI : Fintype ↥Y := Fintype.ofFinite ↥Y
  let A : ↥Y → Subgroup G := fun y => P₁.map (MulAut.conj (y : G)).toMonoidHom
  let W : Subgroup G := (⨆ y : ↥Y, A y) ⊔ pCoreOf 2 H
  have hAH : ∀ y : ↥Y, A y ≤ H := by
    intro y x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    change MulAut.conj (y : G) p ∈ H
    rw [MulAut.conj_apply]
    exact H.mul_mem (H.mul_mem (hYH y.2) (hL.le (hPL hp))) (H.inv_mem (hYH y.2))
  have hPLcomm : ⁅pCoreOf 2 H, L⁆ ≤ pCoreOf 2 H :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := pCoreOf 2 H)).mp
      (hL.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H))
  have hP_NL : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) :=
    w7_9_le_normalizer_of_commutator_le_pCore hL (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
      hPLcomm
  have hA_NL : ∀ y : ↥Y, A y ≤ Subgroup.normalizer (L : Set G) := fun y =>
    w7_9_conj_le_normalizer_of_isTwoPrimeComponent hL hYH hPL y.2
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_forall_map_conj_le ?_
    intro g hg
    have h1 := w7_9_map_conj_iSup (Y := Y) (P := P₁) hg
    have h2 := w7_9_map_conj_pCoreOf (H := H) (hYH hg)
    change ((⨆ y : ↥Y, A y) ⊔ pCoreOf 2 H).map (MulAut.conj g).toMonoidHom ≤
      (⨆ y : ↥Y, A y) ⊔ pCoreOf 2 H
    rw [Subgroup.map_sup, h1, h2]
  have hW2 : IsPGroup 2 W := w7_9_isPGroup_iSup_conj_sup_pCoreOf hL hYH hP hPL hst
  have hWNL : W ≤ Subgroup.normalizer (L : Set G) := sup_le (iSup_le hA_NL) hP_NL
  have hA1 : A (1 : ↥Y) = P₁ := by
    simp only [A]
    rw [show ((1 : ↥Y) : G) = 1 from rfl,
      show MulAut.conj (1 : G) = 1 from map_one (MulAut.conj),
      show (1 : MulAut G).toMonoidHom = MonoidHom.id G from rfl]
    exact Subgroup.map_id P₁
  have hP₁W : P₁ ≤ W := by
    rw [← hA1]
    exact (le_sup_of_le_left (le_iSup (fun y : ↥Y => A y) (1 : ↥Y)) :
      A (1 : ↥Y) ≤ (⨆ y : ↥Y, A y) ⊔ pCoreOf 2 H)
  exact ⟨W, hP₁W, le_sup_right, hW2,
    sup_le (iSup_le hAH) (CFSG.LieType.BorelTits.pCoreOf_le 2 H), hYW, hWNL⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
