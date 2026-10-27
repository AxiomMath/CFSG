module

public import CFSG.RankThree.PartOne.S11d.FourSeedAux
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
public import CFSG.RankThree.PartOne.S11d.ThetaCalc
public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore

public section

namespace CFSG.RankThree.PartOne.FourSeed

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G]

theorem not_dvd_card_of_isPGroup_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V : Subgroup G} (hV : IsPGroup 2 V) : ¬ p ∣ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem mem_normalizer_inf' {X Y : Subgroup G} {g : G} (hX : g ∈ normalizer (X : Set G))
    (hY : g ∈ normalizer (Y : Set G)) : g ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hX, hY⟩

theorem exists_two_core_commutator_ne_bot_of_normalizes [Finite G]
    (hG : IsCharacteristicPType G 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B R K : Subgroup G}
    (hB : IsElementaryAbelian p B) (hBcard : p ^ 2 ≤ Nat.card B) (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) (hBR : B ≤ normalizer (R : Set G)) (hKR : K ≤ normalizer (R : Set G))
    (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    ∃ a ∈ B, a ≠ 1 ∧
      ⁅inSubgroup (pCore 2) (normalizer (R : Set G)) ⊓ Subgroup.centralizer ({a} : Set G),
        K⁆ ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := normalizer (R : Set G) with hJ
  set T₂ := inSubgroup (pCore 2) J with hT₂
  have hT₂2 : IsPGroup 2 T₂ := (CFSG.pCore_isPGroup (p := 2) (G := J)).map J.subtype
  have hJT₂ : J ≤ normalizer (T₂ : Set G) :=
    SteinbergBM.le_normalizer_inSubgroup_pCore 2 J
  by_contra hcon
  push Not at hcon
  have hT₂K : T₂ ≤ Subgroup.centralizer (K : Set G) :=
    SteinbergBM.le_of_forall_inf_centralizer_le hB hBcard (not_dvd_card_of_isPGroup_two hp hp2 hT₂2)
      (hBR.trans hJT₂) fun a ha ha1 =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon a ha ha1)
  have hKT₂c : K ≤ Subgroup.centralizer (T₂ : Set G) := Subgroup.le_centralizer_iff.mp hT₂K
  have hKT₂ : K ≤ T₂ := fun x hx =>
    SteinbergBM.mem_inSubgroup_pCore_of_isCharacteristicPType hG hR2 hR1 (hKR hx)
      fun s hs => Subgroup.mem_centralizer_iff.mp (hKT₂c hx) s hs
  have hK2 : IsPGroup 2 K := hT₂2.to_le hKT₂
  have : Group.IsNilpotent K := hK2.isNilpotent
  have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem exists_stable_two_subgroup [Finite G] (hG : IsCharacteristicPType G 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A B R E : Subgroup G}
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hBA : B ≤ A) (hB : IsElementaryAbelian p B)
    (hBcard : p ^ 2 ≤ Nat.card B) (hBE : B ≤ centralizer (E : Set G)) (hE : ⁅E, E⁆ = E)
    (hE1 : E ≠ ⊥) (hAE : A ≤ normalizer (E : Set G)) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hAR : A ≤ normalizer (R : Set G)) (hER : E ≤ normalizer (R : Set G)) :
    ∃ b ∈ B, b ≠ 1 ∧ ∃ S : Subgroup G, S ≤ centralizer ({b} : Set G) ∧ IsPGroup 2 S ∧
      S ≠ ⊥ ∧ E ≤ normalizer (S : Set G) ∧ A ≤ normalizer (S : Set G) ∧ ⁅S, E⁆ = S := by
  obtain ⟨b, hbB, hb1, hne⟩ := exists_two_core_commutator_ne_bot_of_normalizes hG hp hp2 hB hBcard
    hR2 hR1 (hBA.trans hAR) hER hE hE1
  refine ⟨b, hbB, hb1, ?_⟩
  set J := normalizer (R : Set G) with hJ
  set T₂ := inSubgroup (pCore 2) J with hT₂
  have hT₂2 : IsPGroup 2 T₂ := (CFSG.pCore_isPGroup (p := 2) (G := J)).map J.subtype
  have hJT₂ : J ≤ normalizer (T₂ : Set G) := SteinbergBM.le_normalizer_inSubgroup_pCore 2 J
  set Y := T₂ ⊓ centralizer ({b} : Set G) with hY
  have hbA : b ∈ A := hBA hbB
  have hEb : E ≤ centralizer ({b} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hBE hbB) e he)
  have hAb : A ≤ centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm x hx b hbA)
  have hEY : E ≤ normalizer (Y : Set G) := fun e he =>
    mem_normalizer_inf' (hJT₂ (hER he)) (Subgroup.le_normalizer (hEb he))
  have hAY : A ≤ normalizer (Y : Set G) := fun x hx =>
    mem_normalizer_inf' (hJT₂ (hAR hx)) (Subgroup.le_normalizer (hAb hx))
  obtain ⟨S, hSY, hS1, hES, hAS, hSE⟩ := exists_stable_commutator hE hAE Y hEY hAY hne
  exact ⟨S, hSY.trans inf_le_right, (hT₂2.to_le (hSY.trans inf_le_left)), hS1, hES, hAS, hSE⟩


open CFSG.Assembly (evenRank) in
theorem commutator_le_thetaComponent [Finite G] (he : evenRank G ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {x : G} {I E S : Subgroup G} (hI : I ∈ thetaComponentsAt p x) (hEI : E ≤ I)
    (hgen : ∀ e ∈ E, e ∈ Subgroup.closure {y : G | y ∈ E ∧ ∃ k : ℕ, orderOf y = p ^ k})
    (hSx : S ≤ centralizer ({x} : Set G)) (hSE : S ≤ ⁅S, E⁆) : S ≤ I := by
  have hIC : I ≤ centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.mp hI).1
  have hEx : E ≤ centralizer ({x} : Set G) := hEI.trans hIC
  set N := normalizer (I : Set G) with hN
  have h1 : ∀ s ∈ S, ∀ y ∈ E, (∃ k : ℕ, orderOf y = p ^ k) → ⁅s, y⁆ ∈ N := by
    intro s hs y hy hyp
    have hsC := hSx hs
    have hyC := hEx hy
    have h2 : s * y * s⁻¹ ∈ N := by
      refine pElement_normalizes_thetaComponentsAt he hp hp3
        (mul_mem (mul_mem hsC hyC) (inv_mem hsC)) ?_ hI
      obtain ⟨k, hk⟩ := hyp
      exact ⟨k, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hk]⟩
    rw [commutatorElement_def]
    exact mul_mem h2 (inv_mem (Subgroup.le_normalizer (hEI hy)))
  have h2 : ∀ e ∈ Subgroup.closure {y : G | y ∈ E ∧ ∃ k : ℕ, orderOf y = p ^ k},
      e ∈ E ∧ ∀ s ∈ S, ⁅s, e⁆ ∈ N := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem y hy => exact ⟨hy.1, fun s hs => h1 s hs y hy.1 hy.2⟩
    | one => exact ⟨E.one_mem, fun s _ => by simp⟩
    | mul e₁ e₂ _ _ ih₁ ih₂ =>
      refine ⟨E.mul_mem ih₁.1 ih₂.1, fun s hs => ?_⟩
      have : ⁅s, e₁ * e₂⁆ = ⁅s, e₁⁆ * (e₁ * ⁅s, e₂⁆ * e₁⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      have h3 : e₁ ∈ N := Subgroup.le_normalizer (hEI ih₁.1)
      exact mul_mem (ih₁.2 s hs) (mul_mem (mul_mem h3 (ih₂.2 s hs)) (inv_mem h3))
    | inv e _ ih =>
      refine ⟨E.inv_mem ih.1, fun s hs => ?_⟩
      have : ⁅s, e⁻¹⁆ = e⁻¹ * (⁅s, e⁆)⁻¹ * e := by
        simp only [commutatorElement_def]
        group
      rw [this]
      have h3 : e ∈ N := Subgroup.le_normalizer (hEI ih.1)
      exact mul_mem (mul_mem (inv_mem h3) (inv_mem (ih.2 s hs))) h3
  have hSN : ⁅S, E⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro s hs e he
    exact (h2 e (hgen e he)).2 s hs
  have hSI : ⁅S, E⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro s hs e he
    have hsN : s ∈ N := hSN (hSE hs)
    have hse : s * e * s⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp hsN e).mp (hEI he)
    rw [commutatorElement_def]
    exact mul_mem hse (inv_mem (hEI he))
  exact hSE.trans hSI


theorem le_closure_pElements_of_quasisimple {p : ℕ} {E : Subgroup G}
    (hE : CFSG.IsQuasisimple ↥E) {d : G} (hdE : d ∈ E) (hdp : ∃ k : ℕ, orderOf d = p ^ k)
    (hdc : ∃ e ∈ E, d * e ≠ e * d) :
    ∀ e ∈ E, e ∈ Subgroup.closure {y : G | y ∈ E ∧ ∃ k : ℕ, orderOf y = p ^ k} := by
  set T : Set ↥E := {y | ∃ k : ℕ, orderOf y = p ^ k} with hT
  set N : Subgroup ↥E := Subgroup.closure T with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ?_
      obtain ⟨k, hk⟩ := hy
      exact ⟨k, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hk]⟩
    | one => simp [one_mem]
    | mul x y _ _ ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact mul_mem ihx ihy
    | inv x _ ihx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ihx
  have hd : (⟨d, hdE⟩ : ↥E) ∈ N := by
    refine Subgroup.subset_closure ?_
    obtain ⟨k, hk⟩ := hdp
    exact ⟨k, by rw [Subgroup.orderOf_mk, hk]⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hE hNn with htop | hcen
  · intro e he
    have h1 : (⟨e, he⟩ : ↥E) ∈ N := htop ▸ Subgroup.mem_top _
    have h2 : e ∈ N.map E.subtype := ⟨⟨e, he⟩, h1, rfl⟩
    rw [hN, MonoidHom.map_closure] at h2
    refine (Subgroup.closure_mono ?_) h2
    rintro _ ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [← Subgroup.orderOf_coe] at hk; exact hk⟩
  · exfalso
    obtain ⟨e, he, hne⟩ := hdc
    have := Subgroup.mem_center_iff.mp (hcen hd) ⟨e, he⟩
    exact hne (congrArg Subtype.val this).symm

open CFSG.RankThree.PartOne (sectionTenSetup_prime sectionTenSetup_vanishing) in
theorem commutator_centralized_of_le_theta [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt p b) {U : Subgroup G}
    (hU : U ≤ inSubgroup (aschbacherSolvableCore p) K) (hU2 : IsPGroup 2 U)
    (hUA : A ≤ normalizer (U : Set G)) : ⁅U, A⁆ = ⊥ := by
  have hp := sectionTenSetup_prime h
  have hθ := theta_eq_inf_of_mem_thetaComponentsAt hp hK
  have hUC : U ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) := by
    have := hU
    rw [hθ] at this
    exact this.trans inf_le_right
  exact vanishing_centralizes_invariant_two_subgroups hp (sectionTenSetup_vanishing h)
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 hbA hb1 hUC hU2 hUA

open CFSG in
theorem commutator_double_eq_self_of_coprime_solvable [Finite G] (P K : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card (↥K))) (hsolv : Group.IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ :=
  GL83.commutator_double_eq_self P K hPK hcop hsolv

theorem commutator_zpowers_self [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : G}
    (hcp : orderOf c = p) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hcS : c ∈ normalizer (S : Set G)) :
    ⁅⁅S, Subgroup.zpowers c⁆, Subgroup.zpowers c⁆ = ⁅S, Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card S) := by
    rw [Nat.card_zpowers, hcp]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_card_of_isPGroup_two hp hp2 hS2)
  have : Group.IsNilpotent S := hS2.isNilpotent
  exact commutator_double_eq_self_of_coprime_solvable
    (Subgroup.zpowers c) S (Subgroup.zpowers_le.mpr hcS) hcop inferInstance

end CFSG.RankThree.PartOne.FourSeed
