module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Cases
public import CFSG.Quasithin.Vol2.Ch3Sec3FactAutL3Red
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313He
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312

public section

namespace CFSG.Quasithin.H13.InspA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def SporSimple (s : TauCeti.SporadicName) : Prop :=
  IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s) ∧
    ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier s, a * b ≠ b * a

structure KGInputs : Prop where
  l42 : FactAutSylowL42
  l52 : FactAutSylowL52
  a7 : FactAutSylowA7
  l2sq : FactAutSylowL2Sq
  l3eps : FactAutL3Eps
  m11 : FactAutSylowM11
  m22 : FactAutSylowM22
  m23 : FactAutSylowM23
  m24 : FactAutSylowM24
  j4 : FactAutSylowJ4
  hs : FactAutSylowHS
  ru : FactAutSylowRu
  he : FactAutHeSylow
  sM11 : SporSimple .M11
  sM22 : SporSimple .M22
  sM23 : SporSimple .M23
  sM24 : SporSimple .M24
  sJ4 : SporSimple .J4
  sHS : SporSimple .HS
  sHe : SporSimple .He
  sRu : SporSimple .Ru

@[expose] def RadQuotAutOddNormCent {Q : Type} [Group Q] (L : Subgroup Q) : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (f : ↥L →* W), Function.Surjective f →
    f.ker = (solvRad L).subgroupOf L → AutOddNormCent W

section Generic

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {P : ∀ (W : Type) [Group W], Prop}

theorem radQuot_of_simple (hinv : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A)
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W → P W → AutOddNormCent W)
    [IsSimpleGroup ↥L] (hnc : ∃ a b : ↥L, a * b ≠ b * a) (hL : P ↥L) :
    RadQuotAutOddNormCent L := by
  intro W _ _ f hf hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_simple f hf hker hnc
  exact hP W e.isSimpleGroup (hinv e hL)

theorem radQuot_of_quasisimple (hinv : ∀ {A B : Type} [Group A] [Group B], (A ≃* B) → P B → P A)
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W → P W → AutOddNormCent W)
    (hq : CFSG.IsQuasisimple ↥L) (hL : P (↥L ⧸ Subgroup.center ↥L)) :
    RadQuotAutOddNormCent L := by
  intro W _ _ f hf hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_quasisimple f hf hker hq
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  exact hP W e.isSimpleGroup (hinv e hL)

end Generic

section Types

theorem exists_noncomm_of_four_le {X : Type} [Group X] [IsSimpleGroup X]
    (h4 : 4 ≤ ordProj[2] (Nat.card X)) : ∃ a b : X, a * b ≠ b * a := by
  have hc : Nat.card X ≠ 0 := by
    intro h0
    rw [h0] at h4
    simp at h4
  have : Finite X := Nat.finite_of_card_ne_zero hc
  refine CFSG.Quasithin.A314.exists_noncomm_of_simple inferInstance fun hp => ?_
  have hk : 2 ≤ (Nat.card X).factorization 2 := by
    by_contra hk
    have : 2 ^ (Nat.card X).factorization 2 ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4d : 4 ∣ Nat.card X :=
    dvd_trans (by simpa using Nat.pow_dvd_pow 2 hk) (Nat.ordProj_dvd (Nat.card X) 2)
  have h2 := hp.eq_one_or_self_of_dvd 2 (dvd_trans (by norm_num) h4d)
  have h4le : 4 ≤ Nat.card X := Nat.le_of_dvd (Nat.pos_of_ne_zero hc) h4d
  omega

variable {X : Type} [Group X] {n p e : ℕ}

theorem isSimpleGroup_of_isPSL (h : IsPSL n p e X) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity X n p e h).2

theorem exists_noncomm_of_isPSL (h : IsPSL n p e X) : ∃ a b : X, a * b ≠ b * a := by
  have := isSimpleGroup_of_isPSL h
  exact exists_noncomm_of_four_le
    (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound X n p e h).2.1

theorem isSimpleGroup_of_isPSU (h : IsPSU n p e X) : IsSimpleGroup X :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X n p e h).2

theorem exists_noncomm_of_isPSU (h : IsPSU n p e X) : ∃ a b : X, a * b ≠ b * a := by
  have := isSimpleGroup_of_isPSU h
  exact exists_noncomm_of_four_le
    (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound X n p e h).2.2.2.1

theorem isPSL_of_mulEquiv {A B : Type} [Group A] [Group B] (f : A ≃* B) (h : IsPSL n p e B) :
    IsPSL n p e A :=
  CFSG.SectionRank.statedClassicalModel_of_mulEquiv f h

theorem isPSU_of_mulEquiv {A B : Type} [Group A] [Group B] (f : A ≃* B) (h : IsPSU n p e B) :
    IsPSU n p e A :=
  CFSG.SectionRank.statedClassicalModel_of_mulEquiv f h

theorem isAlt_of_mulEquiv {A B : Type} [Group A] [Group B] (f : A ≃* B) (h : IsAlt n B) :
    IsAlt n A := by
  obtain ⟨g⟩ := h
  exact ⟨f.trans g⟩

theorem isSporadic_of_mulEquiv {s : TauCeti.SporadicName} {A B : Type} [Group A] [Group B]
    (f : A ≃* B) (h : IsSporadic s B) : IsSporadic s A := by
  obtain ⟨g⟩ := h
  exact ⟨f.trans g⟩

end Types

section LTypes

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}

theorem radQuot_of_isPSL {n p e : ℕ}
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W → IsPSL n p e W → AutOddNormCent W)
    (hL : IsPSL n p e ↥L) : RadQuotAutOddNormCent L := by
  have := isSimpleGroup_of_isPSL hL
  exact radQuot_of_simple (P := fun W _ => IsPSL n p e W) (fun f h => isPSL_of_mulEquiv f h) hP
    (exists_noncomm_of_isPSL hL) hL

theorem radQuot_of_isPSU {n p e : ℕ}
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W → IsPSU n p e W → AutOddNormCent W)
    (hL : IsPSU n p e ↥L) : RadQuotAutOddNormCent L := by
  have := isSimpleGroup_of_isPSU hL
  exact radQuot_of_simple (P := fun W _ => IsPSU n p e W) (fun f h => isPSU_of_mulEquiv f h) hP
    (exists_noncomm_of_isPSU hL) hL

theorem radQuot_of_isSL3 {p : ℕ} (hp : p.Prime)
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W → IsPSL 3 p 1 W → AutOddNormCent W)
    (hL : IsSL3 p ↥L) : RadQuotAutOddNormCent L := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  have hq := Gold14610.Struct.isQuasisimple_statedSL_three hp K hK
  have hs := Gold14610.Struct.isSimpleGroup_statedProj_statedSL_three hp K hK
  obtain ⟨hqL, ⟨g⟩⟩ := F6.InspRest.isQuasisimple_and_quotientCenter (StatedSL 3 K) hq hs
    (Or.inl ⟨e⟩)
  refine radQuot_of_quasisimple (P := fun W _ => IsPSL 3 p 1 W)
    (fun f h => isPSL_of_mulEquiv f h) hP hqL ?_
  exact ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance,
    by rw [pow_one, hK], ⟨g⟩⟩

theorem radQuot_of_isSU3 {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W → IsPSU 3 p 1 W → AutOddNormCent W)
    (hL : IsSU3 p ↥L) : RadQuotAutOddNormCent L := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  have hq := Gold14610.Struct.isQuasisimple_statedSU_three hp hp3 K hK
  have hs := Gold14610.Struct.isSimpleGroup_statedProj_statedSU_three hp hp3 K hK
  obtain ⟨hqL, ⟨g⟩⟩ := F6.InspRest.isQuasisimple_and_quotientCenter (StatedSU 3 p K) hq hs
    (Or.inl ⟨e⟩)
  refine radQuot_of_quasisimple (P := fun W _ => IsPSU 3 p 1 W)
    (fun f h => isPSU_of_mulEquiv f h) hP hqL ?_
  refine ⟨⟨hp, le_rfl, le_rfl, ?_⟩, K, inferInstance, inferInstance, by rw [pow_one, hK],
    ⟨g.trans (L3Eps.statedProjSUCongr (pow_one p).symm)⟩⟩
  simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
  omega

theorem radQuot_of_isAlt7 (hA7 : FactAutSylowA7) (hL : IsAlt 7 ↥L) : RadQuotAutOddNormCent L := by
  obtain ⟨e⟩ := hL
  have := F6.InspRest.isSimpleGroup_alt_seven
  have : IsSimpleGroup ↥L := e.isSimpleGroup
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := F6.InspRest.exists_noncomm_alt_seven
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  exact radQuot_of_simple (P := fun W _ => IsAlt 7 W) (fun f h => isAlt_of_mulEquiv f h)
    (fun W _ _ _ h => (hA7 W h).autOddNormCent) hnc ⟨e⟩

theorem radQuot_of_isHat_alt7 (hA7 : FactAutSylowA7) (hL : IsHat ↥L ↥(alternatingGroup (Fin 7))) :
    RadQuotAutOddNormCent L :=
  radQuot_of_quasisimple (P := fun W _ => IsAlt 7 W) (fun f h => isAlt_of_mulEquiv f h)
    (fun W _ _ _ h => (hA7 W h).autOddNormCent) hL.1 hL.2.2

theorem radQuot_of_isSporadic {s : TauCeti.SporadicName} (hss : SporSimple s)
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSporadic s W → AutOddNormCent W)
    (hL : IsSporadic s ↥L) : RadQuotAutOddNormCent L := by
  obtain ⟨e⟩ := hL
  obtain ⟨hs, a, b, hab⟩ := hss
  have : IsSimpleGroup ↥L := e.isSimpleGroup
  exact radQuot_of_simple (P := fun W _ => IsSporadic s W)
    (fun f h => isSporadic_of_mulEquiv f h) (fun W _ _ _ h => hP W h)
    ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩ ⟨e⟩

theorem radQuot_of_isHat_sporadic {s : TauCeti.SporadicName}
    (hP : ∀ (W : Type) [Group W] [Finite W], IsSporadic s W → AutOddNormCent W)
    (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier s)) : RadQuotAutOddNormCent L :=
  radQuot_of_quasisimple (P := fun W _ => IsSporadic s W) (fun f h => isSporadic_of_mulEquiv f h)
    (fun W _ _ _ h => hP W h) hL.1 hL.2.2

end LTypes

section Cases

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} (hK : KGInputs)
include hK

theorem autOddNormCent_of_isPSL_three {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (W : Type) [Group W]
    [Finite W] (hs : IsSimpleGroup W) (h : IsPSL 3 p 1 W) : AutOddNormCent W :=
  hK.l3eps W hs (Or.inr ⟨true, p, hp, hp2, h⟩)

theorem autOddNormCent_of_isPSU_three {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (W : Type) [Group W]
    [Finite W] (hs : IsSimpleGroup W) (h : IsPSU 3 p 1 W) : AutOddNormCent W :=
  hK.l3eps W hs (Or.inr ⟨false, p, hp, hp2, h⟩)

theorem radQuot_of_c4 (h : A312C4 B L) : RadQuotAutOddNormCent L := by
  obtain ⟨-, hL | hL, -⟩ := h
  · exact radQuot_of_isPSL (fun W _ _ _ h => (hK.l42 W h).autOddNormCent) hL
  · exact radQuot_of_isPSL (fun W _ _ _ h => (hK.l52 W h).autOddNormCent) hL

theorem radQuot_of_c5 (h : A312C5 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isPSL (fun W _ _ _ h => (hK.l52 W h).autOddNormCent) h.2.1

theorem radQuot_of_c6 (h : A312C6 B L) : RadQuotAutOddNormCent L := by
  rcases h.2 with hL | hL
  · exact radQuot_of_isAlt7 hK.a7 hL
  · exact radQuot_of_isHat_alt7 hK.a7 hL

theorem radQuot_of_c7 (h : A312C7 B L) : RadQuotAutOddNormCent L := by
  rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
  · exact radQuot_of_isAlt7 hK.a7 hL
  · exact radQuot_of_isHat_alt7 hK.a7 hL

theorem radQuot_of_c8_left {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hL : IsPSL 2 p 2 ↥L) :
    RadQuotAutOddNormCent L :=
  radQuot_of_isPSL (fun W _ _ _ h => (hK.l2sq p hp hp3 W h).autOddNormCent) hL

theorem radQuot_of_c9 (h : A312C9 B L) : RadQuotAutOddNormCent L := by
  rcases h with ⟨s, p, hp, hp3, -, hL⟩ | ⟨-, hL⟩ | ⟨-, hL⟩
  · cases s
    · rcases hL with hL | hL
      · exact radQuot_of_isPSU (autOddNormCent_of_isPSU_three hK hp (by omega)) hL
      · exact radQuot_of_isSU3 hp (by omega) (autOddNormCent_of_isPSU_three hK hp (by omega)) hL
    · rcases hL with hL | hL
      · exact radQuot_of_isPSL (autOddNormCent_of_isPSL_three hK hp (by omega)) hL
      · exact radQuot_of_isSL3 hp (autOddNormCent_of_isPSL_three hK hp (by omega)) hL
  · exact radQuot_of_isPSU (autOddNormCent_of_isPSU_three hK (by norm_num) (by norm_num)) hL
  · exact radQuot_of_isSU3 (by norm_num) (by norm_num)
      (autOddNormCent_of_isPSU_three hK (by norm_num) (by norm_num)) hL

theorem radQuot_of_c10 (h : A312C10 B L) : RadQuotAutOddNormCent L := by
  obtain ⟨p, hp, hp3, -, hL | hL⟩ := h
  · exact radQuot_of_isPSL (autOddNormCent_of_isPSL_three hK hp (by omega)) hL
  · exact radQuot_of_isSL3 hp (autOddNormCent_of_isPSL_three hK hp (by omega)) hL

theorem radQuot_of_c11 (h : A312C11 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isSporadic hK.sM11 (fun W _ _ h => (hK.m11 W h).autOddNormCent) h.2

theorem radQuot_of_c12 (h : A312C12 B L) : RadQuotAutOddNormCent L := by
  rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
  · exact radQuot_of_isSporadic hK.sM22 (fun W _ _ h => (hK.m22 W h).autOddNormCent) hL
  · exact radQuot_of_isHat_sporadic (fun W _ _ h => (hK.m22 W h).autOddNormCent) hL

theorem radQuot_of_c13 (h : A312C13 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isSporadic hK.sM23 (fun W _ _ h => (hK.m23 W h).autOddNormCent) h.2

theorem radQuot_of_c14 (h : A312C14 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isSporadic hK.sM24 (fun W _ _ h => (hK.m24 W h).autOddNormCent) h.2

theorem radQuot_of_c17 (h : A312C17 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isSporadic hK.sJ4 (fun W _ _ h => (hK.j4 W h).autOddNormCent) h.1

theorem radQuot_of_c18 (h : A312C18 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isSporadic hK.sHS (fun W _ _ h => (hK.hs W h).autOddNormCent) h.2

theorem radQuot_of_c19 (h : A312C19 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isSporadic hK.sHe
    (fun W _ _ h => AutSylowSelfNorm.autOddNormCent (hK.he W h)) h.2

theorem radQuot_of_c20 (h : A312C20 B L) : RadQuotAutOddNormCent L :=
  radQuot_of_isSporadic hK.sRu (fun W _ _ h => (hK.ru W h).autOddNormCent) h.2.2

end Cases

end CFSG.Quasithin.H13.InspA312
