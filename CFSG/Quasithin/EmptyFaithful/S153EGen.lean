module

public import CFSG.Quasithin.Background.A1cTransfer
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin

namespace S153E

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_not_mem_of_lt [Finite G] {p : ℕ} [Fact p.Prime] {A P : Subgroup G}
    (hP : IsPGroup p P) (hAP : A < P) : ∃ x ∈ P, x ∈ Subgroup.normalizer (A : Set G) ∧ x ∉ A := by
  classical
  let IP : Subgroup P := A.subgroupOf P
  have hne : IP ≠ ⊤ := by
    intro htop
    obtain ⟨y, hyP, hyA⟩ := IsConcreteLE.exists_of_lt hAP
    have : (⟨y, hyP⟩ : P) ∈ IP := by rw [htop]; trivial
    exact hyA (Subgroup.mem_subgroupOf.mp this)
  have hlt : IP < ⊤ := lt_of_le_of_ne le_top hne
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  have h := hnc IP hlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt h
  refine ⟨x, x.2, ?_, fun hxA => hxnot (Subgroup.mem_subgroupOf.mpr hxA)⟩
  have hxsub : x ∈ (Subgroup.normalizer (A : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hAP.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

noncomputable def toSylow153 [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : P ≤ K ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex K) : Sylow p ↥K :=
  IsPGroup.toSylow (P := P.subgroupOf K) (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm)
    (by simpa [Subgroup.relIndex] using hP.2.2)

theorem map_toSylow153 [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : P ≤ K ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex K) :
    ((toSylow153 hP : Sylow p ↥K) : Subgroup ↥K).map K.subtype = P := by
  change (P.subgroupOf K).map K.subtype = P
  exact Subgroup.map_subgroupOf_eq_of_le hP.1

theorem exists_sylow_ge [Finite G] {p : ℕ} [Fact p.Prime] {Q K : Subgroup G}
    (hQp : IsPGroup p Q) (hQK : Q ≤ K) :
    ∃ R : Subgroup G, Q ≤ R ∧ R ≤ K ∧ IsPGroup p R ∧ ¬ p ∣ R.relIndex K := by
  have hQ' : IsPGroup p (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup ↥K).map K.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hQK hx⟩, hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · exact (S.isPGroup').map K.subtype
  · have : ((S : Subgroup ↥K).map K.subtype).subgroupOf K = (S : Subgroup ↥K) :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [Subgroup.relIndex, this]
    exact S.not_dvd_index

theorem exists_conj_of_isSylow [Finite G] {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : P ≤ K ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex K) (hQp : IsPGroup p Q) (hQK : Q ≤ K) :
    ∃ k ∈ K, Q ≤ conjSubgroup P k := by
  have hQ' : IsPGroup p (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K (toSylow153 hP) S
  refine ⟨((k⁻¹ : ↥K) : G), (k⁻¹).2, ?_⟩
  intro x hx
  have hxK : x ∈ K := hQK hx
  have h1 : (⟨x, hxK⟩ : ↥K) ∈ ((k • toSylow153 hP : Sylow p ↥K) : Subgroup ↥K) := by
    rw [hk]
    exact hS (Subgroup.mem_subgroupOf.mpr hx)
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
  have h1' : (⟨x, hxK⟩ : ↥K) ∈
      ((toSylow153 hP : Sylow p ↥K) : Subgroup ↥K).map (MulAut.conj k).toMonoidHom := h1
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1'
  have hyP : (y : G) ∈ P := by
    rw [← map_toSylow153 hP]
    exact ⟨y, hy, rfl⟩
  have hyx' : (k : G) * (y : G) * (k : G)⁻¹ = x := by
    have := congrArg Subtype.val hyx
    simpa using this
  rw [mem_conjSubgroup_iff]
  have e : ((k⁻¹ : ↥K) : G) * x * ((k⁻¹ : ↥K) : G)⁻¹ = (y : G) := by
    rw [← hyx']
    simp [mul_assoc]
  rw [e]
  exact hyP

theorem isPGroup_conjSubgroup153 {p : ℕ} {R : Subgroup G} (hR : IsPGroup p R) (g : G) :
    IsPGroup p (conjSubgroup R g) :=
  hR.of_equiv (Subgroup.equivMapOfInjective R (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective)

theorem card_conjSubgroup153 (R : Subgroup G) (g : G) : Nat.card (conjSubgroup R g) = Nat.card R :=
  (Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem card_eq_of_isSylow [Finite G] {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : P ≤ K ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex K)
    (hQ : Q ≤ K ∧ IsPGroup p Q ∧ ¬ p ∣ Q.relIndex K) : Nat.card P = Nat.card Q := by
  obtain ⟨k, -, hk⟩ := exists_conj_of_isSylow hP hQ.2.1 hQ.1
  obtain ⟨k', -, hk'⟩ := exists_conj_of_isSylow hQ hP.2.1 hP.1
  have e1 : Nat.card (conjSubgroup P k) = Nat.card P := card_conjSubgroup153 P k
  have e2 : Nat.card (conjSubgroup Q k') = Nat.card Q := card_conjSubgroup153 Q k'
  have h1 : Nat.card Q ≤ Nat.card P := e1 ▸ Subgroup.card_le_of_le hk
  have h2 : Nat.card P ≤ Nat.card Q := e2 ▸ Subgroup.card_le_of_le hk'
  omega

end S153E

end CFSG.Quasithin
