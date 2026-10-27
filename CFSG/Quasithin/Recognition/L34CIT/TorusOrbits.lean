module

public import CFSG.Quasithin.Recognition.L34CIT.OppositeInvolutions
public import CFSG.Quasithin.Recognition.L34CIT.FixedSylows
public import CFSG.Quasithin.Recognition.L34CIT.OrderThree

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise
open CFSG.GroupTheory.WielandtProduct (mem_conj_smul_iff)

variable {A : Type} [Group A]

namespace Config

private abbrev B (C : Config A) : Subgroup A := normalizer (C.T : Set A)

private abbrev K (k : A) : Subgroup A := Subgroup.zpowers k

private abbrev KP (C : Config A) (P : Sylow 2 A) : Subgroup A :=
  normalizer (C.T : Set A) ⊓ normalizer (P : Set A)

private def oppSet (C : Config A) : Set (Sylow 2 A) :=
  {P | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥}

private def jSet (C : Config A) (k : A) : Set (Sylow 2 A) :=
  {P | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥ ∧ k • P = P}

private def fixSet (C : Config A) (k : A) : Set (Sylow 2 A) := {P | k • P = P}

private theorem card_K {k : A} (hk : orderOf k = 3) : Nat.card (K k) = 3 := by
  rw [Nat.card_zpowers, hk]

private theorem card_B (C : Config A) [Finite A] : Nat.card (C.B) = 192 :=
  C.card_normalizer_T

private noncomputable def sylowThreeOfSubgroup (C : Config A) [Finite A] (H : Subgroup A)
    (hH : H ≤ C.B) (hcard : Nat.card ↥H = 3) : Sylow 3 C.B := by
  classical
  have hcard' : Nat.card ↥(H.subgroupOf C.B) = 3 := by
    rw [show Nat.card ↥(H.subgroupOf C.B) = Nat.card ↥H from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hcard]
  have hH3 : IsPGroup 3 (H.subgroupOf C.B) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [hcard']; norm_num)
  have hidx : ¬ 3 ∣ (H.subgroupOf C.B).index := by
    have hmul := Subgroup.index_mul_card (H.subgroupOf C.B)
    rw [hcard', C.card_B] at hmul
    have : (H.subgroupOf C.B).index = 64 := by omega
    rw [this]
    norm_num
  exact hH3.toSylow hidx

private theorem coe_sylowThreeOfSubgroup (C : Config A) [Finite A] (H : Subgroup A)
    (hH : H ≤ C.B) (hcard : Nat.card ↥H = 3) :
    ((C.sylowThreeOfSubgroup H hH hcard : Sylow 3 C.B) : Subgroup C.B) = H.subgroupOf C.B := by
  unfold sylowThreeOfSubgroup
  rfl

private theorem exists_conj_eq_of_card_three (C : Config A) [Finite A] {H K' : Subgroup A}
    (hH : H ≤ C.B) (hHcard : Nat.card ↥H = 3)
    (hK : K' ≤ C.B) (hKcard : Nat.card ↥K' = 3) :
    ∃ b : C.B, MulAut.conj (b : A) • H = K' := by
  let P : Sylow 3 C.B := C.sylowThreeOfSubgroup H hH hHcard
  have hP : (P : Subgroup C.B) = H.subgroupOf C.B :=
    C.coe_sylowThreeOfSubgroup H hH hHcard
  let Q : Sylow 3 C.B := C.sylowThreeOfSubgroup K' hK hKcard
  have hQ : (Q : Subgroup C.B) = K'.subgroupOf C.B :=
    C.coe_sylowThreeOfSubgroup K' hK hKcard
  haveI : Finite (Sylow 3 C.B) := Sylow.finite_of_finiteIndex P
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq C.B P Q
  refine ⟨b, ?_⟩
  have hcoe : (MulAut.conj (b : A) • H).subgroupOf C.B = K'.subgroupOf C.B := by
    rw [← Subgroup.conj_smul_subgroupOf hH b, ← hP, ← Sylow.coe_subgroup_smul, hb, hQ]
  have hconjle : MulAut.conj (b : A) • H ≤ C.B := Subgroup.conj_smul_le_of_le hH b
  have hinf := Subgroup.subgroupOf_inj.mp hcoe
  rwa [inf_eq_left.mpr hconjle, inf_eq_left.mpr hK] at hinf

private theorem smul_mem_oppSet (C : Config A) [Finite A] {P : Sylow 2 A}
    (hP : P ∈ C.oppSet) (b : C.B) : b • P ∈ C.oppSet := by
  rw [oppSet, Set.mem_setOf_eq] at hP ⊢
  have hbT : MulAut.conj (b : A) • (C.T : Subgroup A) = (C.T : Subgroup A) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp b.2
  calc (C.T : Subgroup A) ⊓ ((b • P : Sylow 2 A) : Subgroup A)
      = (C.T : Subgroup A) ⊓ MulAut.conj (b : A) • (P : Subgroup A) := rfl
    _ = (MulAut.conj (b : A) • (C.T : Subgroup A)) ⊓
        MulAut.conj (b : A) • (P : Subgroup A) := by rw [hbT]
    _ = MulAut.conj (b : A) • ((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
        rw [Subgroup.smul_inf]
    _ = ⊥ := by rw [hP, Subgroup.smul_bot]

private theorem KP_eq_K_of_mem_jSet (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) {P : Sylow 2 A} (hP : P ∈ C.jSet k) :
    C.KP P = K k := by
  obtain ⟨hOpp, hFix⟩ := hP
  have hKPcard : Nat.card ↥(C.KP P) = 3 := C.card_normalizer_inf_normalizer P hOpp
  have hle : K k ≤ C.KP P := by
    rw [Subgroup.zpowers_le]
    exact ⟨hkB, (Sylow.smul_eq_iff_mem_normalizer).mp hFix⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hKPcard, card_K hk])).symm

private theorem eq_of_smul_eq_of_mem_jSet (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) {P P' : Sylow 2 A}
    (hP : P ∈ C.jSet k) (hP' : P' ∈ C.jSet k) {b : C.B} (hb : b • P' = P) : P' = P := by
  have hkP : k • P = P := hP.2
  have hkP' : k • P' = P' := hP'.2
  have hKP : C.KP P' = K k := C.KP_eq_K_of_mem_jSet hkB hk hP'
  have hbA : (b : A) • P' = P := hb
  have hxP' : ((b : A)⁻¹ * k * (b : A)) • P' = P' := by
    calc ((b : A)⁻¹ * k * (b : A)) • P'
        = (b : A)⁻¹ • (k • ((b : A) • P')) := by rw [mul_smul, mul_smul]
      _ = (b : A)⁻¹ • (k • P) := by rw [hbA]
      _ = (b : A)⁻¹ • P := by rw [hkP]
      _ = P' := by rw [← hbA, inv_smul_smul]
  have hxP'mem : (b : A)⁻¹ * k * (b : A) ∈ normalizer (P' : Set A) :=
    (Sylow.smul_eq_iff_mem_normalizer).mp hxP'
  have hxT : (b : A)⁻¹ * k * (b : A) ∈ C.B :=
    C.B.mul_mem (C.B.mul_mem (C.B.inv_mem b.2) hkB) b.2
  have hxKP : (b : A)⁻¹ * k * (b : A) ∈ C.KP P' := ⟨hxT, hxP'mem⟩
  rw [hKP] at hxKP
  have hconjK : MulAut.conj ((b : A)⁻¹) • K k = Subgroup.zpowers ((b : A)⁻¹ * k * (b : A)) := by
    rw [show MulAut.conj ((b : A)⁻¹) • K k =
        (K k).map (MulAut.conj ((b : A)⁻¹)).toMonoidHom from rfl, MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply]
  have hconjle : MulAut.conj ((b : A)⁻¹) • K k ≤ K k := by
    rw [hconjK]
    exact Subgroup.zpowers_le.mpr hxKP
  have hcardconj : Nat.card ↥(MulAut.conj ((b : A)⁻¹) • K k) = Nat.card (K k) :=
    card_conj ((b : A)⁻¹) (K k)
  have hconj_eq : MulAut.conj ((b : A)⁻¹) • K k = K k :=
    Subgroup.eq_of_le_of_card_ge hconjle (by rw [hcardconj])
  have hb_inv_norm : (b : A)⁻¹ ∈ normalizer (K k : Set A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change MulAut.conj ((b : A)⁻¹) • K k = K k
    exact hconj_eq
  have hb_norm : (b : A) ∈ normalizer (K k : Set A) := by
    simpa using (Subgroup.inv_mem (normalizer (K k : Set A)) hb_inv_norm)
  have hbK : (b : A) ∈ K k := by
    have hbB : (b : A) ∈ C.B := b.2
    have hbN : (b : A) ∈ normalizer (K k : Set A) ⊓ C.B := ⟨hb_norm, hbB⟩
    rwa [C.normalizer_zpowers_inf_normalizer_T hkB hk] at hbN
  have hKle : K k ≤ MulAction.stabilizer A P := by
    rw [Subgroup.zpowers_le]
    exact (MulAction.mem_stabilizer_iff).mpr hkP
  have hbP : (b : A) • P = P := MulAction.mem_stabilizer_iff.mp (hKle hbK)
  have hbb : (b : A) • P' = (b : A) • P := by rw [hbA, hbP]
  exact smul_left_cancel (b : A) hbb

private theorem smul_eq_self_iff_mem_Ksub (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) {P : Sylow 2 A} (hP : P ∈ C.jSet k) (b : C.B) :
    b • P = P ↔ b ∈ (K k).subgroupOf C.B := by
  have hKP : C.KP P = K k := C.KP_eq_K_of_mem_jSet hkB hk hP
  constructor
  · intro hb
    have hbN : (b : A) ∈ normalizer (P : Set A) :=
      (Sylow.smul_eq_iff_mem_normalizer).mp hb
    have hbKP : (b : A) ∈ C.KP P := ⟨b.2, hbN⟩
    rw [hKP] at hbKP
    exact hbKP
  · intro hb
    have hbKP : (b : A) ∈ C.KP P := by
      rw [hKP]
      exact hb
    exact (Sylow.smul_eq_iff_mem_normalizer).mpr hbKP.2

private theorem exists_mem_jSet_smul_eq (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) {Q : Sylow 2 A} (hQ : Q ∈ C.oppSet) :
    ∃ P : Sylow 2 A, P ∈ C.jSet k ∧ ∃ b : C.B, b • P = Q := by
  have hKle : K k ≤ C.B := Subgroup.zpowers_le.mpr hkB
  have hKcard : Nat.card (K k) = 3 := card_K hk
  have hHle : C.KP Q ≤ C.B := inf_le_left
  have hHcard : Nat.card ↥(C.KP Q) = 3 := C.card_normalizer_inf_normalizer Q hQ
  obtain ⟨b, hb⟩ := C.exists_conj_eq_of_card_three hHle hHcard hKle hKcard
  have hk_in : k ∈ MulAut.conj (b : A) • C.KP Q := by
    rw [hb]
    exact Subgroup.mem_zpowers k
  have hxKP : b⁻¹ * k * b ∈ C.KP Q := mem_conj_smul_iff.mp hk_in
  have hxNQ : b⁻¹ * k * b ∈ normalizer (Q : Set A) := hxKP.2
  refine ⟨b • Q, ⟨C.smul_mem_oppSet hQ b, ?_⟩, b⁻¹, by simp⟩
  have hxQ : ((b : A)⁻¹ * k * (b : A)) • Q = Q :=
    (Sylow.smul_eq_iff_mem_normalizer).mpr hxNQ
  calc k • (b • Q) = k • ((b : A) • Q) := rfl
    _ = (k * (b : A)) • Q := smul_smul k (b : A) Q
    _ = ((b : A) * ((b : A)⁻¹ * k * (b : A))) • Q := by
          congr 1
          group
    _ = (b : A) • (((b : A)⁻¹ * k * (b : A)) • Q) := mul_smul (b : A) _ Q
    _ = (b : A) • Q := by rw [hxQ]

private noncomputable def actionMap (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) :
    {P : Sylow 2 A // P ∈ C.jSet k} × C.B → {Q : Sylow 2 A // Q ∈ C.oppSet} :=
  fun x => ⟨x.2 • x.1.1, C.smul_mem_oppSet x.1.2.1 x.2⟩

@[simp] private theorem actionMap_val (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (x : {P : Sylow 2 A // P ∈ C.jSet k} × C.B) :
    (C.actionMap hkB x : Sylow 2 A) = x.2 • x.1.1 := rfl

private theorem ncard_fiber_actionMap (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3)
    (Q : {Q : Sylow 2 A // Q ∈ C.oppSet}) :
    Nat.card {x : {P : Sylow 2 A // P ∈ C.jSet k} × C.B // C.actionMap hkB x = Q} = 3 := by
  classical
  obtain ⟨P₀, hP₀J, b₀, hb₀⟩ := C.exists_mem_jSet_smul_eq hkB hk Q.2
  have huniq : ∀ (P : {P : Sylow 2 A // P ∈ C.jSet k}) (b : C.B),
      b • P.1 = Q.1 → P.1 = P₀ := by
    intro P b hb
    have hbA : (b : A) • P.1 = Q.1 := hb
    let b₁ : C.B := b₀⁻¹ * b
    have hb₁ : b₁ • P.1 = P₀ := by
      change ((b₀ : A)⁻¹ * (b : A)) • P.1 = P₀
      calc ((b₀ : A)⁻¹ * (b : A)) • P.1
          = (b₀ : A)⁻¹ • ((b : A) • P.1) := mul_smul (b₀ : A)⁻¹ (b : A) P.1
        _ = (b₀ : A)⁻¹ • Q.1 := by rw [hbA]
        _ = P₀ := by
              rw [← show (b₀ : A) • P₀ = Q.1 from hb₀]
              exact inv_smul_smul (b₀ : A) P₀
    exact C.eq_of_smul_eq_of_mem_jSet hkB hk hP₀J P.2 hb₁
  have hfib_eq : ({x : {P : Sylow 2 A // P ∈ C.jSet k} × C.B |
        C.actionMap hkB x = Q} : Set ({P : Sylow 2 A // P ∈ C.jSet k} × C.B)) =
        {x : {P : Sylow 2 A // P ∈ C.jSet k} × C.B |
          x.1 = ⟨P₀, hP₀J⟩ ∧ x.2 • P₀ = Q.1} := by
    ext x
    constructor
    · intro hx
      have hxval : x.2 • x.1.1 = Q.1 := by
        simpa using congrArg Subtype.val hx
      have hxP : x.1.1 = P₀ := huniq x.1 x.2 hxval
      refine ⟨Subtype.ext hxP, ?_⟩
      rw [← hxP]
      exact hxval
    · rintro ⟨hx1, hx2⟩
      apply Subtype.ext
      show x.2 • x.1.1 = Q.1
      rw [hx1]
      exact hx2
  change Nat.card ↥({x : {P : Sylow 2 A // P ∈ C.jSet k} × C.B |
      C.actionMap hkB x = Q}) = 3
  rw [hfib_eq]
  change Nat.card {x : {P : Sylow 2 A // P ∈ C.jSet k} × C.B //
      x.1 = ⟨P₀, hP₀J⟩ ∧ x.2 • P₀ = Q.1} = 3
  have hS_card :
      Nat.card {x : {P : Sylow 2 A // P ∈ C.jSet k} × C.B //
          x.1 = ⟨P₀, hP₀J⟩ ∧ x.2 • P₀ = Q.1} =
        Nat.card {b : C.B // b • P₀ = Q.1} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨x.1.2, x.2.2⟩
        invFun := fun b => ⟨(⟨P₀, hP₀J⟩, b.1), ⟨rfl, b.2⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      apply Subtype.ext
      apply Prod.ext
      · exact x.2.1.symm
      · rfl
    · intro b
      rfl
  rw [hS_card]
  have hKsubcard : Nat.card ↥((K k).subgroupOf C.B) = 3 := by
    rw [show Nat.card ↥((K k).subgroupOf C.B) = Nat.card (K k) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hkB)).toEquiv,
      card_K hk]
  refine (Nat.card_congr ?_).trans hKsubcard
  refine
    { toFun := fun b => ⟨b₀⁻¹ * b.1, ?_⟩
      invFun := fun s => ⟨b₀ * s.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hbP : (b₀⁻¹ * b.1) • P₀ = P₀ := by
      change ((b₀ : A)⁻¹ * (b.1 : A)) • P₀ = P₀
      calc ((b₀ : A)⁻¹ * (b.1 : A)) • P₀
          = (b₀ : A)⁻¹ • ((b.1 : A) • P₀) := mul_smul (b₀ : A)⁻¹ (b.1 : A) P₀
        _ = (b₀ : A)⁻¹ • Q.1 := by
              rw [show (b.1 : A) • P₀ = Q.1 from b.2]
        _ = P₀ := by
              rw [← show (b₀ : A) • P₀ = Q.1 from hb₀]
              exact inv_smul_smul (b₀ : A) P₀
    exact (C.smul_eq_self_iff_mem_Ksub hkB hk hP₀J (b₀⁻¹ * b.1)).mp hbP
  · have hsfix : (s.1 : A) • P₀ = P₀ :=
      (C.smul_eq_self_iff_mem_Ksub hkB hk hP₀J s.1).mpr s.2
    have hs : (b₀ * s.1) • P₀ = Q.1 := by
      change ((b₀ : A) * (s.1 : A)) • P₀ = Q.1
      calc ((b₀ : A) * (s.1 : A)) • P₀
          = (b₀ : A) • ((s.1 : A) • P₀) := mul_smul (b₀ : A) (s.1 : A) P₀
        _ = (b₀ : A) • P₀ := by rw [hsfix]
        _ = Q.1 := hb₀
    exact hs
  · intro b
    apply Subtype.ext
    change b₀ * (b₀⁻¹ * b.1) = b.1
    group
  · intro s
    apply Subtype.ext
    change b₀⁻¹ * (b₀ * s.1) = s.1
    group

theorem ncard_opposite_eq_mul (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ normalizer (C.T : Set A)) (hk : orderOf k = 3) :
    {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥}.ncard =
      64 * {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥ ∧ k • P = P}.ncard := by
  classical
  let Jt : Type := {P : Sylow 2 A // P ∈ C.jSet k}
  let Ot : Type := {Q : Sylow 2 A // Q ∈ C.oppSet}
  let f : Jt × C.B → Ot := C.actionMap hkB
  haveI : Fintype Jt := Fintype.ofFinite _
  haveI : Fintype Ot := Fintype.ofFinite _
  haveI : Fintype C.B := Fintype.ofFinite _
  have hsum : Fintype.card (Jt × C.B) =
      ∑ Q : Ot, Fintype.card {x : Jt × C.B // f x = Q} := by
    let s : Finset (Jt × C.B) := Finset.univ
    let t : Finset Ot := Finset.univ
    have H : (s : Set (Jt × C.B)).MapsTo f t := by
      intro x _
      exact Finset.mem_univ (f x)
    have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := t) H
    simpa [s, t, Fintype.card_subtype] using h
  have hfiber : ∀ Q : Ot, Fintype.card {x : Jt × C.B // f x = Q} = 3 := by
    intro Q
    rw [← Nat.card_eq_fintype_card]
    exact C.ncard_fiber_actionMap hkB hk Q
  have hsum3 : (∑ Q : Ot, Fintype.card {x : Jt × C.B // f x = Q}) = 3 * Fintype.card Ot := by
    rw [Finset.sum_congr rfl (fun Q _ => hfiber Q)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hBcard : Fintype.card C.B = 192 := by
    rw [← Nat.card_eq_fintype_card, C.card_B]
  have hprod : Fintype.card (Jt × C.B) = Fintype.card Jt * 192 := by
    calc Fintype.card (Jt × C.B) = Fintype.card Jt * Fintype.card C.B :=
          Fintype.card_prod Jt C.B
      _ = Fintype.card Jt * 192 := by rw [hBcard]
  have hrel : Fintype.card Jt * 192 = 3 * Fintype.card Ot := by
    rw [← hprod, hsum, hsum3]
  have hcard : Fintype.card Ot = 64 * Fintype.card Jt := by omega
  have hfinal : Nat.card Ot = 64 * Nat.card Jt := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hcard
  change (C.oppSet).ncard = 64 * (C.jSet k).ncard
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hfinal

private abbrev Nrm (k : A) : Subgroup A := normalizer (K k : Set A)

private def invN (C : Config A) (k : A) : Set A :=
  {u | u ∈ Nrm k ∧ u * u = 1 ∧ u ≠ 1}

private theorem eq_k_or_inv_of_mem_K_of_order_three {k x : A} (hk : orderOf k = 3)
    (hxK : x ∈ K k) (hx3 : orderOf x = 3) : x = k ∨ x = k⁻¹ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxK
  have hk3 : k ^ 3 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
  have hm : k ^ m = k ^ (m % ((3:ℕ):ℤ)) := by
    rw [← zpow_mod_orderOf k m, hk]
  rw [hm] at hx3 ⊢
  have h0 : 0 ≤ m % ((3:ℕ):ℤ) := Int.emod_nonneg _ (by norm_num)
  have hlt : m % ((3:ℕ):ℤ) < ((3:ℕ):ℤ) := Int.emod_lt_of_pos _ (by norm_num)
  have hcases : m % ((3:ℕ):ℤ) = 0 ∨ m % ((3:ℕ):ℤ) = 1 ∨ m % ((3:ℕ):ℤ) = 2 := by
    omega
  rcases hcases with h | h | h
  · exfalso
    rw [h] at hx3
    norm_num at hx3
  · left
    rw [h]
    norm_num
  · right
    rw [h]
    have hk2 : k ^ (2 : ℤ) = k ^ 2 := by norm_num
    rw [hk2]
    have hmul : k ^ 2 * k = 1 := by
      calc k ^ 2 * k = k ^ 3 := by group
        _ = 1 := hk3
    exact eq_inv_of_mul_eq_one_left hmul

private theorem ncard_fixSet_le (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) :
    (C.fixSet k).ncard ≤ 5 + (C.jSet k).ncard := by
  classical
  haveI : Finite (Sylow 2 A) :=
    Finite.of_surjective (fun a : A => a • C.T) fun P => MulAction.exists_smul_eq A C.T P
  let A1 : Set (Sylow 2 A) :=
    {P | (C.T : Subgroup A) ⊓ (P : Subgroup A) ≠ ⊥ ∧ k • P = P}
  have hsub : C.fixSet k ⊆ A1 ∪ C.jSet k := by
    intro P hP
    by_cases h : (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥
    · right
      exact ⟨h, hP⟩
    · left
      exact ⟨h, hP⟩
  have h1 : A1.ncard ≤ 5 := C.ncard_nonopposite_fixed_le hkB hk
  have h2 : (A1 ∪ C.jSet k).ncard ≤ A1.ncard + (C.jSet k).ncard :=
    Set.ncard_union_le _ _
  calc (C.fixSet k).ncard ≤ (A1 ∪ C.jSet k).ncard := Set.ncard_le_ncard hsub
    _ ≤ 5 + (C.jSet k).ncard := by omega

private theorem smul_mem_fixSet (C : Config A) [Finite A] {k : A} (n : Nrm k)
    {P : Sylow 2 A} (hP : P ∈ C.fixSet k) : n • P ∈ C.fixSet k := by
  rw [fixSet, Set.mem_setOf_eq] at hP ⊢
  have hnk : ((n : A)⁻¹ * k * (n : A)) ∈ K k := by
    exact (Subgroup.mem_normalizer_iff''.mp n.2 k).mp (Subgroup.mem_zpowers k)
  have hfixK : ((n : A)⁻¹ * k * (n : A)) • P = P := by
    have hzle : K k ≤ MulAction.stabilizer A P := by
      rw [Subgroup.zpowers_le]
      exact (MulAction.mem_stabilizer_iff).mpr hP
    exact MulAction.mem_stabilizer_iff.mp (hzle hnk)
  calc k • (n • P) = k • ((n : A) • P) := rfl
    _ = (k * (n : A)) • P := smul_smul k (n : A) P
    _ = ((n : A) * ((n : A)⁻¹ * k * (n : A))) • P := by
          congr 1
          group
    _ = (n : A) • (((n : A)⁻¹ * k * (n : A)) • P) := mul_smul (n : A) _ P
    _ = (n : A) • P := by rw [hfixK]

private noncomputable def fixMap (C : Config A) [Finite A] {k : A} (hkB : k ∈ C.B) :
    Nrm k → C.fixSet k :=
  fun n => ⟨n • C.T, C.smul_mem_fixSet n (by
    rw [fixSet, Set.mem_setOf_eq]
    exact (Sylow.smul_eq_iff_mem_normalizer).mpr hkB)⟩

private theorem ncard_fiber_fixMap_le (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) (P : C.fixSet k) :
    Nat.card {n : Nrm k // C.fixMap hkB n = P} ≤ 3 := by
  classical
  by_cases hne : Nonempty {n : Nrm k // C.fixMap hkB n = P}
  · obtain ⟨n₀, hn₀⟩ := hne
    have hn₀T : n₀ • C.T = P.1 := congrArg Subtype.val hn₀
    have hKsubcard : Nat.card ↥((K k).subgroupOf (Nrm k)) = 3 := by
      rw [show Nat.card ↥((K k).subgroupOf (Nrm k)) = Nat.card (K k) from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv,
        card_K hk]
    refine (Nat.card_congr ?_).trans_le (le_of_eq hKsubcard)
    refine
      { toFun := fun n => ⟨n₀⁻¹ * n.1, ?_⟩
        invFun := fun s => ⟨n₀ * s.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    ·
      have hTfix : ((n₀ : A)⁻¹ * (n.1 : A)) • C.T = C.T := by
        calc ((n₀ : A)⁻¹ * (n.1 : A)) • C.T
            = (n₀ : A)⁻¹ • ((n.1 : A) • C.T) := mul_smul (n₀ : A)⁻¹ (n.1 : A) C.T
          _ = (n₀ : A)⁻¹ • P.1 := by
                rw [show (n.1 : A) • C.T = P.1 from congrArg Subtype.val n.2]
          _ = C.T := by
                rw [← hn₀T]
                exact inv_smul_smul (n₀ : A) C.T
      have hnorm : ((n₀ : A)⁻¹ * (n.1 : A)) ∈ normalizer ((C.T : Subgroup A) : Set A) :=
        (Sylow.smul_eq_iff_mem_normalizer).mp hTfix
      have hmem : ((n₀ : A)⁻¹ * (n.1 : A)) ∈ Nrm k ⊓ C.B :=
        ⟨(Nrm k).mul_mem ((Nrm k).inv_mem n₀.2) n.1.2, hnorm⟩
      rw [C.normalizer_zpowers_inf_normalizer_T hkB hk] at hmem
      exact hmem
    ·
      have hfixT : (s.1 : A) • C.T = C.T := by
        have hzle : K k ≤ MulAction.stabilizer A C.T := by
          rw [Subgroup.zpowers_le]
          exact (MulAction.mem_stabilizer_iff).mpr ((Sylow.smul_eq_iff_mem_normalizer).mpr hkB)
        exact MulAction.mem_stabilizer_iff.mp (hzle s.2)
      apply Subtype.ext
      change ((n₀ : A) * (s.1 : A)) • C.T = P.1
      calc ((n₀ : A) * (s.1 : A)) • C.T
          = (n₀ : A) • ((s.1 : A) • C.T) := mul_smul (n₀ : A) (s.1 : A) C.T
        _ = (n₀ : A) • C.T := by rw [hfixT]
        _ = P.1 := hn₀T
    · intro n
      apply Subtype.ext
      change (n₀ : Nrm k) * ((n₀ : Nrm k)⁻¹ * n.1) = n.1
      group
    · intro s
      apply Subtype.ext
      change (n₀ : Nrm k)⁻¹ * ((n₀ : Nrm k) * s.1) = s.1
      group
  · haveI : IsEmpty {n : Nrm k // C.fixMap hkB n = P} := not_nonempty_iff.mp hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le 3

private theorem ncard_Nrm_le (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) :
    Nat.card (Nrm k) ≤ 3 * (C.fixSet k).ncard := by
  classical
  haveI : Fintype (Nrm k) := Fintype.ofFinite _
  haveI : Fintype (C.fixSet k) := Fintype.ofFinite _
  let f : Nrm k → C.fixSet k := C.fixMap hkB
  have hsum : Fintype.card (Nrm k) =
      ∑ P : C.fixSet k, Fintype.card {n : Nrm k // f n = P} := by
    let s : Finset (Nrm k) := Finset.univ
    let t : Finset (C.fixSet k) := Finset.univ
    have H : (s : Set (Nrm k)).MapsTo f t := by
      intro n _
      exact Finset.mem_univ (f n)
    have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := t) H
    simpa [s, t, Fintype.card_subtype] using h
  have hle : ∀ P : C.fixSet k, Fintype.card {n : Nrm k // f n = P} ≤ 3 := by
    intro P
    rw [← Nat.card_eq_fintype_card]
    exact C.ncard_fiber_fixMap_le hkB hk P
  have hsumle : (∑ P : C.fixSet k, Fintype.card {n : Nrm k // f n = P}) ≤
      3 * Fintype.card (C.fixSet k) := by
    calc (∑ P : C.fixSet k, Fintype.card {n : Nrm k // f n = P})
        ≤ ∑ _ : C.fixSet k, 3 := Finset.sum_le_sum (fun P _ => hle P)
      _ = 3 * Fintype.card (C.fixSet k) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
            omega
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card (Nrm k)
      = ∑ P : C.fixSet k, Fintype.card {n : Nrm k // f n = P} := hsum
    _ ≤ 3 * Fintype.card (C.fixSet k) := hsumle
    _ = 3 * (C.fixSet k).ncard := by rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

private theorem three_mul_jSet_le_invN (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) :
    3 * (C.jSet k).ncard ≤ (C.invN k).ncard := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype (Sylow 2 A) := Fintype.ofFinite _
  have hfin : (C.jSet k).Finite := Set.toFinite _
  set S : Finset (Sylow 2 A) := hfin.toFinset with hS
  have hSmem : ∀ P : Sylow 2 A, P ∈ S ↔ P ∈ C.jSet k := fun P =>
    Set.Finite.mem_toFinset hfin
  have hScard : S.card = (C.jSet k).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
  have hfib : ∀ P : Sylow 2 A, (C.fibre P).Finite := fun P => Set.toFinite _
  have hdisj : (S : Set (Sylow 2 A)).PairwiseDisjoint (fun P => (hfib P).toFinset) := by
    intro P hP Q hQ hne
    change Disjoint ((hfib P).toFinset) ((hfib Q).toFinset)
    rw [Finset.disjoint_left]
    intro u huP huQ
    rw [Set.Finite.mem_toFinset] at huP huQ
    exact hne (huP.2.2.symm.trans huQ.2.2)
  have hcardfib : ∀ P ∈ S, ((hfib P).toFinset).card = 3 := by
    intro P hP
    rw [← Set.ncard_eq_toFinset_card _ (hfib P)]
    have hPJ := (hSmem P).1 hP
    exact C.ncard_fibre_eq_three P hPJ.1
  have hsubset : (↑(S.biUnion fun P => (hfib P).toFinset) : Set A) ⊆ C.invN k := by
    intro u hu
    rw [Finset.mem_coe, Finset.mem_biUnion] at hu
    obtain ⟨P, hP, huP⟩ := hu
    rw [Set.Finite.mem_toFinset] at huP
    have hPJ := (hSmem P).1 hP
    have huN : u ∈ Nrm k := by
      have hmem := C.mem_normalizer_of_mem_fibre huP
      change u ∈ normalizer (C.KP P : Set A) at hmem
      rw [show C.KP P = K k from C.KP_eq_K_of_mem_jSet hkB hk hPJ] at hmem
      exact hmem
    exact ⟨huN, huP.1, huP.2.1⟩
  have hunion_card : (S.biUnion fun P => (hfib P).toFinset).card = 3 * S.card := by
    rw [Finset.card_biUnion hdisj]
    calc (∑ P ∈ S, ((hfib P).toFinset).card) = ∑ P ∈ S, 3 :=
          Finset.sum_congr rfl (fun P hP => hcardfib P hP)
      _ = 3 * S.card := by
            rw [Finset.sum_const, smul_eq_mul]
            omega
  have hle : (S.biUnion fun P => (hfib P).toFinset).card ≤ (C.invN k).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsubset
  calc 3 * (C.jSet k).ncard = 3 * S.card := by rw [hScard]
    _ = (S.biUnion fun P => (hfib P).toFinset).card := hunion_card.symm
    _ ≤ (C.invN k).ncard := hle

private noncomputable def invNEquiv (C : Config A) (k : A) :
    {u : Nrm k // (u : A) * u = 1 ∧ (u : A) ≠ 1} ≃ ↥(C.invN k) where
  toFun u := ⟨u.1.1, u.1.2, u.2.1, u.2.2⟩
  invFun u := ⟨⟨u.1, u.2.1⟩, u.2.2.1, u.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem two_mul_invN_le_Nrm (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ C.B) (hk : orderOf k = 3) :
    2 * (C.invN k).ncard ≤ Nat.card (Nrm k) := by
  classical
  haveI : Fintype (Nrm k) := Fintype.ofFinite _
  let X : Set (Nrm k) := {n | (n : A) * k * (n : A)⁻¹ = k⁻¹}
  let Y : Set (Nrm k) := {n | (n : A) * k * (n : A)⁻¹ = k}
  have hxK : ∀ n : Nrm k, ((n : A) * k * (n : A)⁻¹) ∈ K k := by
    intro n
    exact (Subgroup.mem_normalizer_iff.mp n.2 k).mp (Subgroup.mem_zpowers k)
  have hx3 : ∀ n : Nrm k, orderOf ((n : A) * k * (n : A)⁻¹) = 3 := by
    intro n
    have hk3 : k ^ 3 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
    have hpow : ((n : A) * k * (n : A)⁻¹) ^ 3 = 1 := by
      calc ((n : A) * k * (n : A)⁻¹) ^ 3
          = MulAut.conj (n : A) (k ^ 3) := by
              rw [map_pow, MulAut.conj_apply]
        _ = 1 := by rw [hk3, map_one]
    have hne : ((n : A) * k * (n : A)⁻¹) ≠ 1 := by
      intro h
      have hk1 : k = 1 := by
        have := congrArg (fun x => (n : A)⁻¹ * x * (n : A)) h
        simpa [mul_assoc] using this
      rw [hk1, orderOf_one] at hk
      norm_num at hk
    exact orderOf_eq_prime hpow hne
  have hdisj : Disjoint X Y := by
    rw [Set.disjoint_left]
    intro n hx hy
    have hk_eq : k⁻¹ = k := hx.symm.trans hy
    have hk2 : k * k = 1 := by
      have := congrArg (fun x => x * k) hk_eq
      simpa [mul_assoc] using this.symm
    have hdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hk2)
    rw [hk] at hdvd
    norm_num at hdvd
  have hcover : X ∪ Y = Set.univ := by
    ext n
    constructor
    · intro _
      exact Set.mem_univ n
    · intro _
      rcases eq_k_or_inv_of_mem_K_of_order_three hk (hxK n) (hx3 n) with h | h
      · right
        exact h
      · left
        exact h
  have hInvX : ∀ u : Nrm k, (u : A) * u = 1 → (u : A) ≠ 1 → u ∈ X := by
    intro u hu2 hu1
    rcases eq_k_or_inv_of_mem_K_of_order_three hk (hxK u) (hx3 u) with h | h
    · exfalso
      have hcomm : (u : A) * k = k * (u : A) := by
        have := congrArg (fun x => x * (u : A)) h
        simpa [mul_assoc] using this
      have hu1' : (u : A) = 1 :=
        C.eq_one_of_commute_of_orderOf_eq_three hk (n := 1)
          (by simpa [pow_two] using hu2) hcomm
      exact hu1 hu1'
    · exact h
  have hNcard : Nat.card (Nrm k) = Nat.card X + Nat.card Y := by
    have hunion := Set.ncard_union_eq hdisj
    rw [hcover, Set.ncard_univ] at hunion
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hunion
    exact hunion
  have hInv_le_X : Nat.card {u : Nrm k // (u : A) * u = 1 ∧ (u : A) ≠ 1} ≤
      Nat.card X := by
    refine Nat.card_le_card_of_injective
      (f := fun u : {u : Nrm k // (u : A) * u = 1 ∧ (u : A) ≠ 1} =>
        (⟨u.1, hInvX u.1 u.2.1 u.2.2⟩ : X)) ?_
    intro u v h
    apply Subtype.ext
    exact congrArg (fun x : X => x.1) h
  by_cases hne : Nonempty {u : Nrm k // (u : A) * u = 1 ∧ (u : A) ≠ 1}
  · obtain ⟨u₀, hu₀⟩ := hne
    have hu₀X : u₀ ∈ X := hInvX u₀ hu₀.1 hu₀.2
    have hXY : Nat.card X = Nat.card Y := by
      apply le_antisymm
      · refine Nat.card_le_card_of_injective
          (f := fun x : X => (⟨(u₀ : Nrm k) * x.1, ?_⟩ : Y)) ?_
        · have hx : (x.1 : A) * k * (x.1 : A)⁻¹ = k⁻¹ := x.2
          have hu₀x : (u₀ : A) * k * (u₀ : A)⁻¹ = k⁻¹ := hu₀X
          change ((u₀ : A) * (x.1 : A)) * k * ((u₀ : A) * (x.1 : A))⁻¹ = k
          calc ((u₀ : A) * (x.1 : A)) * k * ((u₀ : A) * (x.1 : A))⁻¹
              = (u₀.1 : A) * ((x.1 : A) * k * (x.1 : A)⁻¹) * (u₀.1 : A)⁻¹ := by group
            _ = (u₀.1 : A) * k⁻¹ * (u₀.1 : A)⁻¹ := by rw [hx]
            _ = ((u₀ : A) * k * (u₀ : A)⁻¹)⁻¹ := by group
            _ = (k⁻¹)⁻¹ := by rw [hu₀x]
            _ = k := by group
        · intro x y h
          apply Subtype.ext
          have h' : ((u₀ : Nrm k) * x.1 : Nrm k) =
              ((u₀ : Nrm k) * y.1 : Nrm k) := congrArg Subtype.val h
          exact mul_left_cancel h'
      · refine Nat.card_le_card_of_injective
          (f := fun y : Y => (⟨(u₀ : Nrm k) * y.1, ?_⟩ : X)) ?_
        · have hy : (y.1 : A) * k * (y.1 : A)⁻¹ = k := y.2
          have hu₀x : (u₀ : A) * k * (u₀ : A)⁻¹ = k⁻¹ := hu₀X
          change ((u₀ : A) * (y.1 : A)) * k * ((u₀ : A) * (y.1 : A))⁻¹ = k⁻¹
          calc ((u₀ : A) * (y.1 : A)) * k * ((u₀ : A) * (y.1 : A))⁻¹
              = (u₀.1 : A) * ((y.1 : A) * k * (y.1 : A)⁻¹) * (u₀.1 : A)⁻¹ := by group
            _ = (u₀ : A) * k * (u₀ : A)⁻¹ := by rw [hy]
            _ = k⁻¹ := hu₀x
        · intro x y h
          apply Subtype.ext
          have h' : ((u₀ : Nrm k) * x.1 : Nrm k) =
              ((u₀ : Nrm k) * y.1 : Nrm k) := congrArg Subtype.val h
          exact mul_left_cancel h'
    have hN2 : Nat.card (Nrm k) = 2 * Nat.card X := by
      rw [hNcard, hXY]
      omega
    calc 2 * (C.invN k).ncard
        = 2 * Nat.card ↥(C.invN k) := by rw [Nat.card_coe_set_eq]
      _ = 2 * Nat.card {u : Nrm k // (u : A) * u = 1 ∧ (u : A) ≠ 1} := by
            rw [← Nat.card_congr (C.invNEquiv k)]
      _ ≤ 2 * Nat.card X := by omega
      _ = Nat.card (Nrm k) := hN2.symm
  · haveI : IsEmpty {u : Nrm k // (u : A) * u = 1 ∧ (u : A) ≠ 1} :=
      not_nonempty_iff.mp hne
    have hzero : (C.invN k).ncard = 0 := by
      rw [← Nat.card_coe_set_eq]
      rw [← Nat.card_congr (C.invNEquiv k)]
      exact Nat.card_of_isEmpty
    rw [hzero]
    omega

theorem ncard_opposite_fixed_le (C : Config A) [Finite A] {k : A}
    (hkB : k ∈ normalizer (C.T : Set A)) (hk : orderOf k = 3) :
    {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥ ∧ k • P = P}.ncard ≤ 5 := by
  have hfix := C.ncard_fixSet_le hkB hk
  have hN := C.ncard_Nrm_le hkB hk
  have h3j := C.three_mul_jSet_le_invN hkB hk
  have h2 := C.two_mul_invN_le_Nrm hkB hk
  have hJ : 6 * (C.jSet k).ncard ≤ Nat.card (Nrm k) := by omega
  have hFix : Nat.card (Nrm k) ≤ 15 + 3 * (C.jSet k).ncard := by omega
  change (C.jSet k).ncard ≤ 5
  omega

end Config

end CFSG.Quasithin.L34CIT
