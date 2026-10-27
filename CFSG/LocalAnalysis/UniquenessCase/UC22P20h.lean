module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.Adapters.LieModelOrders
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Frattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

theorem uc22p20h_prime_dvd_pow_eq {ℓ p k : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (h : ℓ ∣ p ^ k) :
    ℓ = p :=
  (Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow h)

theorem uc22p20h_not_pow_five_dvd_glTwelve (ℓ : ℕ) (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) :
    ¬ ℓ ^ 5 ∣ 2 ^ 28 * 3 ^ 66 * 5 ^ 3 * 7 ^ 2 * 11 ^ 4 * 13 ^ 4 * 23 * 41 * 61 * 73 * 757 * 1093 *
      3851 := by
  intro h
  have hd : ℓ ∣ 2 ^ 28 * 3 ^ 66 * 5 ^ 3 * 7 ^ 2 * 11 ^ 4 * 13 ^ 4 * 23 * 41 * 61 * 73 * 757 * 1093 *
      3851 := (dvd_pow_self ℓ (by norm_num)).trans h
  have p2 : Nat.Prime 2 := by norm_num
  have p3 : Nat.Prime 3 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  have p11 : Nat.Prime 11 := by norm_num
  have p13 : Nat.Prime 13 := by norm_num
  have p23 : Nat.Prime 23 := by norm_num
  have p41 : Nat.Prime 41 := by norm_num
  have p61 : Nat.Prime 61 := by norm_num
  have p73 : Nat.Prime 73 := by norm_num
  have p757 : Nat.Prime 757 := by norm_num
  have p1093 : Nat.Prime 1093 := by norm_num
  have p3851 : Nat.Prime 3851 := by norm_num
  simp only [hℓ.dvd_mul] at hd
  rcases hd with ((((((((((((hd | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd)
  · exact absurd (uc22p20h_prime_dvd_pow_eq hℓ p2 hd) (by omega)
  · exact absurd (uc22p20h_prime_dvd_pow_eq hℓ p3 hd) (by omega)
  · have := uc22p20h_prime_dvd_pow_eq hℓ p5 hd
    subst this
    revert h
    decide +kernel
  · have := uc22p20h_prime_dvd_pow_eq hℓ p7 hd
    subst this
    revert h
    decide +kernel
  · have := uc22p20h_prime_dvd_pow_eq hℓ p11 hd
    subst this
    revert h
    decide +kernel
  · have := uc22p20h_prime_dvd_pow_eq hℓ p13 hd
    subst this
    revert h
    decide +kernel
  · have := (Nat.prime_dvd_prime_iff_eq hℓ p23).1 hd
    subst this
    revert h
    decide +kernel
  · have := (Nat.prime_dvd_prime_iff_eq hℓ p41).1 hd
    subst this
    revert h
    decide +kernel
  · have := (Nat.prime_dvd_prime_iff_eq hℓ p61).1 hd
    subst this
    revert h
    decide +kernel
  · have := (Nat.prime_dvd_prime_iff_eq hℓ p73).1 hd
    subst this
    revert h
    decide +kernel
  · have := (Nat.prime_dvd_prime_iff_eq hℓ p757).1 hd
    subst this
    revert h
    decide +kernel
  · have := (Nat.prime_dvd_prime_iff_eq hℓ p1093).1 hd
    subst this
    revert h
    decide +kernel
  · have := (Nat.prime_dvd_prime_iff_eq hℓ p3851).1 hd
    subst this
    revert h
    decide +kernel

theorem uc22p20h_glTwelve_eq :
    (∏ i : Fin 12, (3 ^ 12 - 3 ^ (i : ℕ))) =
      2 ^ 28 * 3 ^ 66 * 5 ^ 3 * 7 ^ 2 * 11 ^ 4 * 13 ^ 4 * 23 * 41 * 61 * 73 * 757 * 1093 * 3851 := by
  decide +kernel

theorem uc22p20h_gl_dvd (e : ℕ) (he : e ≤ 12) :
    (∏ i : Fin e, (3 ^ e - 3 ^ (i : ℕ))) ∣ ∏ i : Fin 12, (3 ^ 12 - 3 ^ (i : ℕ)) := by
  interval_cases e <;> decide +kernel

theorem uc22p20h_not_pow_five_dvd_gl (ℓ : ℕ) (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {e : ℕ} (he : e ≤ 12) :
    ¬ ℓ ^ 5 ∣ ∏ i : Fin e, (3 ^ e - 3 ^ (i : ℕ)) := fun h =>
  uc22p20h_not_pow_five_dvd_glTwelve ℓ hℓ h5 (uc22p20h_glTwelve_eq ▸ h.trans (uc22p20h_gl_dvd e he))

theorem uc22p20h_card_closure_insert {A : Type*} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hexp : ∀ a : A, a ^ 3 = 1) (S : Set A) (x : A) (hx : x ∉ Subgroup.closure S) :
    Nat.card (Subgroup.closure (insert x S)) = 3 * Nat.card (Subgroup.closure S) := by
  have hx1 : x ≠ 1 := fun h => hx (h ▸ one_mem _)
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.closure S) :=
    uc22p20d_disjoint_zpowers 3 Nat.prime_three x (hexp x) hx1 _ hx
  have hsup : Subgroup.closure (insert x S) = Subgroup.zpowers x ⊔ Subgroup.closure S := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  rw [hsup, uc22p20d_card_sup _ _ (fun a _ b _ => hcomm a b) hdisj,
    uc22p20d_card_zpowers 3 Nat.prime_three x (hexp x) hx1]

theorem uc22p20h_exists_gen {A : Type*} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hexp : ∀ a : A, a ^ 3 = 1) (hcard : Nat.card A ≤ 27) :
    ∃ S : Finset A, S.card ≤ 3 ∧ Subgroup.closure (S : Set A) = ⊤ := by
  classical
  have key : ∀ k : ℕ, ∃ S : Finset A, S.card ≤ k ∧
      (Subgroup.closure (S : Set A) = ⊤ ∨ 3 ^ k ≤ Nat.card (Subgroup.closure (S : Set A))) := by
    intro k
    induction k with
    | zero =>
      refine ⟨∅, by simp, ?_⟩
      right
      simp [Nat.card_pos]
    | succ k ih =>
      obtain ⟨S, hS, h⟩ := ih
      rcases h with h | h
      · exact ⟨S, hS.trans (Nat.le_succ k), Or.inl h⟩
      · by_cases htop : Subgroup.closure (S : Set A) = ⊤
        · exact ⟨S, hS.trans (Nat.le_succ k), Or.inl htop⟩
        · obtain ⟨x, hx⟩ : ∃ x : A, x ∉ Subgroup.closure (S : Set A) := by
            by_contra hcon
            push Not at hcon
            exact htop (eq_top_iff.2 fun x _ => hcon x)
          refine ⟨insert x S, ?_, Or.inr ?_⟩
          · exact (Finset.card_insert_le x S).trans (Nat.succ_le_succ hS)
          · rw [Finset.coe_insert, uc22p20h_card_closure_insert hcomm hexp _ x hx, pow_succ]
            omega
  obtain ⟨S, hS, h⟩ := key 3
  refine ⟨S, hS, ?_⟩
  rcases h with h | h
  · exact h
  · apply Subgroup.eq_top_of_card_eq
    have h1 : Nat.card (Subgroup.closure (S : Set A)) ≤ Nat.card A := Subgroup.card_le_card_group _
    omega

theorem uc22p20h_card_le {D : Type*} [Group D] [Finite D] (hexp : ∀ x : D, x ^ 3 = 1)
    (hcl : ∀ x y z : D, ⁅x, y⁆ * z = z * ⁅x, y⁆)
    (hrk : ∀ (E : Subgroup D) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 3) :
    Nat.card D ≤ 3 ^ 12 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hab : ∀ E : Subgroup D, IsMulCommutative E → Nat.card E ≤ 27 := by
    intro E hE
    have hP : IsPGroup 3 E := fun x => ⟨1, by
      apply Subtype.ext
      simpa using hexp (x : D)⟩
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have := hrk E k ⟨hE, fun x _ => hexp x⟩ hk
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
      _ = 27 := by norm_num
  have hcentral : ∀ x y : D, ⁅x, y⁆ ∈ Subgroup.center D := fun x y =>
    Subgroup.mem_center_iff.2 fun z => (hcl x y z).symm
  obtain ⟨A, -, hA⟩ := Finite.exists_le_maximal (p := fun A : Subgroup D => IsMulCommutative A)
    (a := ⊥) (inferInstance : IsMulCommutative (⊥ : Subgroup D))
  have hAab : IsMulCommutative A := hA.1
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hCA : ∀ d : D, (∀ a ∈ A, d * a = a * d) → d ∈ A := by
    intro d hd
    have hpair : ((A : Set D) ∪ {d}).Pairwise Commute := by
      intro x hx y hy _
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hcommA x hx y hy
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hd x hx).symm
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hd y hy
      · rw [Set.mem_singleton_iff] at hx hy
        subst hx; subst hy
        rfl
    haveI := Subgroup.isMulCommutative_closure hpair
    have hle : A ≤ Subgroup.closure ((A : Set D) ∪ {d}) := fun a ha => Subgroup.subset_closure (Or.inl ha)
    have := hA.2 (y := Subgroup.closure ((A : Set D) ∪ {d})) inferInstance hle
    exact this (Subgroup.subset_closure (Or.inr rfl))
  have hZcard : Nat.card (Subgroup.center D) ≤ 27 := hab _ inferInstance
  obtain ⟨S, hS3, hSgen⟩ : ∃ S : Finset A, S.card ≤ 3 ∧ Subgroup.closure (S : Set A) = ⊤ := by
    refine uc22p20h_exists_gen (fun a b => Subtype.ext (hcommA a a.2 b b.2)) (fun a => ?_) (hab A hAab)
    exact Subtype.ext (by simpa using hexp (a : D))
  let S' : Finset D := S.image A.subtype
  have hS'card : S'.card ≤ 3 := Finset.card_image_le.trans hS3
  have hcl' : Subgroup.closure ((S' : Finset D) : Set D) = A := by
    show Subgroup.closure ((S.image A.subtype : Finset D) : Set D) = A
    rw [Finset.coe_image, ← MonoidHom.map_closure, hSgen, Subgroup.map_top, Subgroup.range_subtype]
  have hS'gen : ∀ d : D, (∀ s ∈ S', d * s = s * d) → ∀ a ∈ A, d * a = a * d := by
    intro d hd a ha
    rw [← hcl'] at ha
    have hle : Subgroup.closure ((S' : Finset D) : Set D) ≤ Subgroup.centralizer ({d} : Set D) := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hd s hs
    have := (Subgroup.mem_centralizer_iff.1 (hle ha)) d rfl
    exact this
  let θs : ∀ s : D, D →* ↥(Subgroup.center D) := fun s =>
    { toFun := fun d => ⟨⁅d, s⁆, hcentral d s⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro d e
        apply Subtype.ext
        show ⁅d * e, s⁆ = ⁅d, s⁆ * ⁅e, s⁆
        have h1 : ⁅d * e, s⁆ = d * ⁅e, s⁆ * d⁻¹ * ⁅d, s⁆ := by
          simp only [commutatorElement_def]; group
        have h2 : d * ⁅e, s⁆ * d⁻¹ = ⁅e, s⁆ := by
          have := hcl e s d
          calc d * ⁅e, s⁆ * d⁻¹ = (d * ⁅e, s⁆) * d⁻¹ := rfl
            _ = (⁅e, s⁆ * d) * d⁻¹ := by rw [← this]
            _ = ⁅e, s⁆ := by simp
        rw [h1, h2]
        exact (hcl d s ⁅e, s⁆).symm }
  let θ : D →* (S' → ↥(Subgroup.center D)) := Pi.monoidHom (fun s : S' => θs (s : D))
  have hker : θ.ker ≤ A := by
    intro d hd
    apply hCA
    intro a ha
    apply hS'gen d _ a ha
    intro s hs
    have h1 : θ d = 1 := hd
    have h2 : θs s d = 1 := congrFun h1 ⟨s, hs⟩
    have h3 : ⁅d, s⁆ = 1 := congrArg Subtype.val h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have hcard1 : Nat.card D = Nat.card (D ⧸ θ.ker) * Nat.card θ.ker := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  have hcard2 : Nat.card (D ⧸ θ.ker) = Nat.card θ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
  have hcard3 : Nat.card θ.range ≤ Nat.card (S' → ↥(Subgroup.center D)) :=
    Subgroup.card_le_card_group _
  have hcard4 : Nat.card (S' → ↥(Subgroup.center D)) = Nat.card (Subgroup.center D) ^ S'.card := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := S'), Fintype.card_coe]
  have hcard5 : Nat.card θ.ker ≤ 27 :=
    (Subgroup.card_le_of_le hker).trans (hab A hAab)
  have hcard6 : Nat.card (Subgroup.center D) ^ S'.card ≤ 27 ^ 3 := by
    calc Nat.card (Subgroup.center D) ^ S'.card ≤ 27 ^ S'.card :=
          Nat.pow_le_pow_left hZcard _
      _ ≤ 27 ^ 3 := Nat.pow_le_pow_right (by norm_num) hS'card
  calc Nat.card D = Nat.card (D ⧸ θ.ker) * Nat.card θ.ker := hcard1
    _ ≤ 27 ^ 3 * 27 := by
        rw [hcard2]
        exact Nat.mul_le_mul (hcard3.trans (hcard4 ▸ hcard6)) hcard5
    _ = 3 ^ 12 := by norm_num

theorem uc22p20h_perfect_le_ker {A B : Type*} [Group A] [Group B] (f : A →* B) {K : Subgroup A}
    (hK : ⁅K, K⁆ = K) {M : Subgroup B} (hM : Group.IsSolvable M) (hKM : K.map f ≤ M) :
    K ≤ f.ker := by
  intro k hk
  by_contra hk1
  have hperf : ⁅K.map f, K.map f⁆ = K.map f := by rw [← Subgroup.map_commutator, hK]
  haveI : Group.IsSolvable ↥(K.map f) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKM)
      (Subgroup.inclusion_injective hKM)
  haveI : Group.IsPerfect ↥(K.map f) := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial ↥(K.map f) :=
    ⟨⟨⟨f k, Subgroup.mem_map_of_mem f hk⟩, 1, fun h => hk1 (by
      have := congrArg Subtype.val h
      simpa using this)⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥(K.map f) inferInstance

theorem uc22p20h_perfect_le_ker_of_pGroup {A B : Type*} [Group A] [Group B] [Finite B] (f : A →* B)
    {K : Subgroup A} (hK : ⁅K, K⁆ = K) {p : ℕ} [Fact p.Prime] {N : Subgroup B}
    (hN : IsPGroup p N) (hKN : K.map f ≤ N) : K ≤ f.ker := by
  haveI : Group.IsNilpotent N := hN.isNilpotent
  exact uc22p20h_perfect_le_ker f hK inferInstance hKN

open CFSG.SectionRank.Ccomm in
theorem uc22p20h_isPGroup_ker_frattiniAction {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (D : Subgroup P) [D.Characteristic]
    (hD : IsPGroup 3 (fixingSubgroup (MulAut P) (D : Set P))) :
    IsPGroup 3 (frattiniAction D).ker := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply isPGroup_of_forall_prime_orderOf
  intro a q hq hord
  by_contra hne
  have ha : (a : MulAut P) ∈ (frattiniAction D).ker := a.2
  set aD : MulAut D := MulAut.characteristic D (a : MulAut P) with haD
  have haDker : aD ∈ (autQuotient (frattini D)).ker := ha
  have hDp : IsPGroup 3 D := hP.to_subgroup D
  have hker3 := isPGroup_ker_autQuotient_frattini hDp
  have hordA : orderOf (a : MulAut P) = q := by rw [Subgroup.orderOf_coe]; exact hord
  have hdvd : orderOf aD ∣ q := by
    have := orderOf_map_dvd (MulAut.characteristic D) (a : MulAut P)
    rw [hordA] at this
    exact this
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hker3 ⟨aD, haDker⟩
  have hk' : orderOf aD = 3 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hone : orderOf aD = 1 := by
    rw [hk'] at hdvd ⊢
    rcases (Nat.dvd_prime hq).1 hdvd with h | h
    · exact h
    · exfalso
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp at h
        exact hq.one_lt.ne' h.symm
      · have h3 : 3 ∣ q := by rw [← h]; exact dvd_pow_self 3 hkpos.ne'
        exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h3).symm
  have haD1 : aD = 1 := orderOf_eq_one_iff.1 hone
  have hfix : (a : MulAut P) ∈ fixingSubgroup (MulAut P) (D : Set P) := by
    rw [mem_fixingSubgroup_iff (MulAut P)]
    intro y hy
    have := congrArg (fun β : MulAut D => ((β ⟨y, hy⟩ : D) : P)) haD1
    simpa [haD] using this
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hD ⟨(a : MulAut P), hfix⟩
  have hm' : q = 3 ^ m := by rw [← hordA, ← hm, Subgroup.orderOf_mk]
  have h3 : 3 ∣ q := by
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp at hm'
      exact absurd hm' hq.one_lt.ne'
    · rw [hm']; exact dvd_pow_self 3 hmpos.ne'
  exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h3).symm

theorem uc22p20h_elemAbelian_map_card {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {p : ℕ} {E : Subgroup A} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) ∧ Nat.card (E.map f) = Nat.card E :=
  ⟨uc22p20d_isElemAbelian_map f hf hE, Subgroup.card_map_of_injective hf⟩

open CFSG.SectionRank.Ccomm in
theorem uc22p20h_caseB {X : Type} [Group X] [Finite X] (Q R : Subgroup X) [Q.Normal] [R.Normal]
    (hQ : IsPGroup 3 Q) (hR : Group.IsSolvable R)
    (hrk : ∀ (E : Subgroup X) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 3)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (K W : Fin 5 → Subgroup X) [hWn : ∀ i, ((W i).subgroupOf (K i)).Normal]
    (hKperf : ∀ i, ⁅K i, K i⁆ = K i)
    (hWR : ∀ i, W i ≤ R)
    (hsimple : ∀ i, IsSimpleGroup (↥(K i) ⧸ (W i).subgroupOf (K i)))
    (hnonab : ∀ i, ∃ a b : ↥(K i) ⧸ (W i).subgroupOf (K i), a * b ≠ b * a)
    (hℓd : ∀ i, ℓ ∣ Nat.card (↥(K i) ⧸ (W i).subgroupOf (K i)))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, ⁅a, b⁆ ∈ R)
    (hnc : ∀ i, ¬ K i ≤ Subgroup.centralizer (Q : Set X)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial ↥Q := by
    obtain ⟨x, -, hx⟩ := Set.not_subset.1 (hnc 0)
    obtain ⟨q, hq, hqx⟩ : ∃ q ∈ (Q : Set X), ¬ q * x = x * q := by
      simpa [Subgroup.mem_centralizer_iff] using hx
    refine ⟨⟨⟨q, hq⟩, 1, fun h => hqx ?_⟩⟩
    have : q = 1 := congrArg Subtype.val h
    subst this
    simp
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ := odd_critical_exponent_subgroup (p := 3) (P := ↥Q)
    (by norm_num) hQ
  haveI := hDchar
  have hDp : IsPGroup 3 D := hQ.to_subgroup D
  have hDcard : Nat.card D ≤ 3 ^ 12 := by
    refine uc22p20h_card_le (D := ↥D) (fun x => Subtype.ext (by simpa using hDexp x x.2)) ?_ ?_
    · intro x y z
      have h1 : ⁅(x : ↥Q), (y : ↥Q)⁆ ∈ ⁅D, (⊤ : Subgroup ↥Q)⁆ :=
        Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
      have h2 := (Subgroup.mem_inf.1 (hDcomm h1)).2
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.1 h2 (z : ↥Q) z.2
      exact this.symm
    · intro E k hE hk
      have h1 := uc22p20h_elemAbelian_map_card D.subtype D.subtype_injective hE
      have h2 := uc22p20h_elemAbelian_map_card Q.subtype Q.subtype_injective h1.1
      exact hrk _ k h2.1 (by rw [h2.2, h1.2, hk])
  haveI hVcomm : IsMulCommutative (↥D ⧸ frattini ↥D) :=
    CFSG.PreuniquenessRankFour.Helpers.pGroup_frattini_quotient_isMulCommutative 3 hDp
  have hVpow : ∀ v : ↥D ⧸ frattini ↥D, v ^ 3 = 1 :=
    CFSG.PreuniquenessRankFour.Helpers.pGroup_frattini_quotient_pow_eq_one 3 hDp
  have hVp : IsPGroup 3 (↥D ⧸ frattini ↥D) := hDp.to_quotient _
  obtain ⟨e, he⟩ := hVp.exists_card_eq
  have he12 : e ≤ 12 := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) ≤ Nat.card D := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥D)]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    rw [he] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans hDcard)
  obtain ⟨φV⟩ := nonempty_mulEquiv_of_elementary (p := 3) (fun a b => hVcomm.is_comm.comm a b) hVpow he
  let ρ : X →* MulAut ↥Q := MulAut.conjNormal
  let ψ : X →* MulAut (↥D ⧸ frattini ↥D) := (frattiniAction D).comp ρ
  have hker3 : IsPGroup 3 (frattiniAction D).ker := uc22p20h_isPGroup_ker_frattiniAction hQ D hDfix
  have hKJ : ∀ i, ¬ K i ≤ ψ.ker := by
    intro i hi
    have h1 : (K i).map ρ ≤ (frattiniAction D).ker := by
      rintro _ ⟨k, hk, rfl⟩
      exact hi hk
    have h2 := uc22p20h_perfect_le_ker_of_pGroup ρ (hKperf i) hker3 h1
    apply hnc i
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h3 := congrArg (fun β : MulAut ↥Q => ((β ⟨q, hq⟩ : ↥Q) : X)) (MonoidHom.mem_ker.1 (h2 hk))
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hKL : ∀ i, ¬ K i ≤ R ⊔ ψ.ker := by
    intro i hi
    haveI hRsolv : Group.IsSolvable ↥(R.map ψ) :=
      Group.isSolvable_of_surjective (f := ψ.subgroupMap R) (ψ.subgroupMap_surjective R)
    have h1 : (K i).map ψ ≤ R.map ψ := by
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨r, hr, j, hj, hrj⟩ := Subgroup.mem_sup_of_normal_right.1 (hi hk)
      refine ⟨r, hr, ?_⟩
      rw [← hrj, map_mul, MonoidHom.mem_ker.1 hj, mul_one]
    exact hKJ i (uc22p20h_perfect_le_ker ψ (hKperf i) hRsolv h1)
  set L : Subgroup X := R ⊔ ψ.ker with hLdef
  let π : X →* X ⧸ L := QuotientGroup.mk' L
  let φ : ∀ i, (↥(K i) ⧸ (W i).subgroupOf (K i)) →* X ⧸ L := fun i =>
    QuotientGroup.lift ((W i).subgroupOf (K i)) (π.comp (K i).subtype) (by
      intro x hx
      show π (x : X) = 1
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left (hWR i (Subgroup.mem_subgroupOf.1 hx))))
  have hφmk : ∀ i (k : ↥(K i)), φ i (QuotientGroup.mk k) = π (k : X) := fun i k => rfl
  have hφinj : ∀ i, Function.Injective (φ i) := by
    intro i
    haveI := hsimple i
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ i).ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).1 h
    · exfalso
      apply hKL i
      intro k hk
      have h1 : (QuotientGroup.mk ⟨k, hk⟩ : ↥(K i) ⧸ (W i).subgroupOf (K i)) ∈ (φ i).ker := by
        rw [h]; trivial
      have h2 : φ i (QuotientGroup.mk ⟨k, hk⟩) = 1 := h1
      rw [hφmk] at h2
      exact (QuotientGroup.eq_one_iff k).1 h2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hs : ∀ i, ∃ s : ↥(K i) ⧸ (W i).subgroupOf (K i), orderOf s = ℓ := fun i =>
    exists_prime_orderOf_dvd_card' ℓ (hℓd i)
  choose s hs using hs
  let y : Fin 5 → X ⧸ L := fun i => φ i (s i)
  have hyo : ∀ i, orderOf (y i) = ℓ := fun i => by
    rw [orderOf_injective (φ i) (hφinj i) (s i)]; exact hs i
  let A : Fin 5 → Subgroup (X ⧸ L) := fun i => (φ i).range
  have hcomm' : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := by
    intro i j hij a ha b hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    obtain ⟨a'', rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
    rw [hφmk, hφmk]
    have h1 : π ⁅(a'' : X), (b'' : X)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left (hcomm i j hij _ a''.2 _ b''.2))
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hxz : ∀ i, ∃ a ∈ A i, a * y i ≠ y i * a := by
    intro i
    haveI := hsimple i
    have hcen : Subgroup.center (↥(K i) ⧸ (W i).subgroupOf (K i)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (↥(K i) ⧸ (W i).subgroupOf (K i))) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab i
        apply hab
        have : a ∈ Subgroup.center (↥(K i) ⧸ (W i).subgroupOf (K i)) := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.1 this b).symm
    have hs1 : s i ∉ Subgroup.center (↥(K i) ⧸ (W i).subgroupOf (K i)) := by
      rw [hcen, Subgroup.mem_bot]
      intro h
      have := hs i
      rw [h, orderOf_one] at this
      exact hℓ.one_lt.ne this
    rw [Subgroup.mem_center_iff] at hs1
    push Not at hs1
    obtain ⟨t, ht⟩ := hs1
    refine ⟨φ i t, ⟨t, rfl⟩, fun h => ht (hφinj i ?_)⟩
    simpa [y, map_mul] using h
  obtain ⟨E, -, hE, hEc⟩ := uc22p20d_elemAbelian_of_commuting (X := X ⧸ L) ℓ 5 hℓ A y hcomm'
    (fun i => ⟨s i, rfl⟩) (fun i => by rw [← hyo i]; exact pow_orderOf_eq_one _) hxz
  have hdvd1 : ℓ ^ 5 ∣ Nat.card (X ⧸ L) := hEc ▸ Subgroup.card_subgroup_dvd_card E
  have hdvd2 : Nat.card (X ⧸ L) ∣ Nat.card (X ⧸ ψ.ker) :=
    Subgroup.index_dvd_of_le (le_sup_right : ψ.ker ≤ R ⊔ ψ.ker)
  have hdvd3 : Nat.card (X ⧸ ψ.ker) ∣ Nat.card (MulAut (↥D ⧸ frattini ↥D)) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have hcardAut : Nat.card (MulAut (↥D ⧸ frattini ↥D)) = ∏ i : Fin e, (3 ^ e - 3 ^ (i : ℕ)) := by
    rw [card_mulAut_eq_card_GL φV, card_GL_zmod]
  exact uc22p20h_not_pow_five_dvd_gl ℓ hℓ hℓ5 he12
    (hcardAut ▸ hdvd1.trans (hdvd2.trans hdvd3))

theorem uc22p20h_caseA {X : Type} [Group X] [Finite X] (hKG : CFSG.Open.IsKGroup X)
    (h3 : ThreeNoncentralFact)
    (hrk : ∀ (E : Subgroup X) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 3)
    (Q R : Subgroup X) [Q.Normal] [R.Normal] (hR : Group.IsSolvable R)
    (hCR : ∀ x ∈ R, (∀ q ∈ Q, q * x = x * q) → x ∈ Q)
    (K W : Fin 5 → Subgroup X) [hKn : ∀ i, (K i).Normal]
    [hWn : ∀ i, ((W i).subgroupOf (K i)).Normal]
    (hKperf : ∀ i, ⁅K i, K i⁆ = K i)
    (hWK : ∀ i, W i ≤ K i) (hWR : ∀ i, W i ≤ R)
    (hsimple : ∀ i, IsSimpleGroup (↥(K i) ⧸ (W i).subgroupOf (K i)))
    (hnonab : ∀ i, ∃ a b : ↥(K i) ⧸ (W i).subgroupOf (K i), a * b ≠ b * a)
    (h3d : ∀ i, 3 ∣ Nat.card (↥(K i) ⧸ (W i).subgroupOf (K i)))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, ⁅a, b⁆ ∈ R)
    (hcent : ∀ i, K i ≤ Subgroup.centralizer (Q : Set X)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWc : ∀ i, ∀ w ∈ W i, ∀ k ∈ K i, k * w = w * k := by
    intro i w hw k hk
    have hwQ : w ∈ Q := hCR w (hWR i hw) (fun q hq => Subgroup.mem_centralizer_iff.1 (hcent i (hWK i hw)) q hq)
    exact ((Subgroup.mem_centralizer_iff.1 (hcent i hk) w hwQ)).symm
  have hperf : ∀ i, Group.IsPerfect ↥(K i) := fun i => Subgroup.isPerfect_iff.2 (hKperf i)
  have hNon : ∀ i, ¬ ∀ a b : ↥(K i), a * b = b * a := by
    intro i h
    obtain ⟨a, b, hab⟩ := hnonab i
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])
  let f : ∀ i, (↥(K i) ⧸ (W i).subgroupOf (K i)) →* (↥(K i) ⧸ Subgroup.center ↥(K i)) := fun i =>
    QuotientGroup.lift ((W i).subgroupOf (K i)) (QuotientGroup.mk' (Subgroup.center ↥(K i))) (by
      intro x hx
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hWc i x (Subgroup.mem_subgroupOf.1 hx) g g.2))
  have hfsurj : ∀ i, Function.Surjective (f i) := by
    intro i t
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hTnt : ∀ i, Nontrivial (↥(K i) ⧸ Subgroup.center ↥(K i)) := by
    intro i
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hNon i
    intro a b
    have h2 : a ∈ Subgroup.center ↥(K i) := by
      have h3 : (QuotientGroup.mk a : ↥(K i) ⧸ Subgroup.center ↥(K i)) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥(K i)) a).1 h3
    exact (Subgroup.mem_center_iff.1 h2 b).symm
  have hTsimple : ∀ i, IsSimpleGroup (↥(K i) ⧸ Subgroup.center ↥(K i)) := by
    intro i
    haveI := hsimple i
    haveI := hTnt i
    exact IsSimpleGroup.isSimpleGroup_of_surjective (f i) (hfsurj i)
  have hq : ∀ i, CFSG.Open.IsQuasisimple ↥(K i) := fun i => ⟨(hperf i).commutator_eq_top, hTsimple i⟩
  have hfinj : ∀ i, Function.Injective (f i) := by
    intro i
    haveI := hsimple i
    haveI := hTnt i
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f i).ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).1 h
    · exfalso
      obtain ⟨t, ht⟩ := exists_ne (1 : ↥(K i) ⧸ Subgroup.center ↥(K i))
      obtain ⟨s, rfl⟩ := hfsurj i t
      apply ht
      have : s ∈ (f i).ker := by rw [h]; trivial
      exact this
  have hcomp : ∀ i, CFSG.IsComponent (K i) := fun i =>
    ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.2 (hq i), Subgroup.Normal.isSubnormal inferInstance⟩
  have hne : ∀ i j, i ≠ j → K i ≠ K j := by
    intro i j hij h
    have h1 : ⁅K i, K i⁆ ≤ R := by
      have := Subgroup.commutator_le.2 (hcomm i j hij)
      rwa [← h] at this
    rw [hKperf i] at h1
    have h2 : K i ≤ (MonoidHom.id X).ker :=
      uc22p20h_perfect_le_ker (MonoidHom.id X) (hKperf i) hR (by simpa using h1)
    apply hNon i
    intro a b
    have ha : (a : X) = 1 := by simpa using h2 a.2
    have hb : (b : X) = 1 := by simpa using h2 b.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb])
  have hcomm2 : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a := by
    intro i j hij a ha b hb
    rcases CFSG.LocalCores.distinct_components_commute (hcomp i) (hcomp j) with h | h
    · exact absurd h (hne i j hij)
    · exact (Subgroup.mem_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) ha)
        b hb).symm
  have hcat : ∀ i, CFSG.Assembly.InCatalog (↥(K i) ⧸ Subgroup.center ↥(K i)) := by
    intro i
    haveI := hTsimple i
    have hKK : CFSG.Open.IsKGroup ↥(K i) := hKG.subgroup (K i)
    have hnab :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥(K i) (hq i)
    exact hKK.isCatalogGroup_of_surjective ⊤ hnab
      ((QuotientGroup.mk' (Subgroup.center ↥(K i))).comp
        (Subgroup.topEquiv (G := ↥(K i))).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := ↥(K i))).surjective)
  have h3div : ∀ i, 3 ∣ Nat.card (↥(K i) ⧸ Subgroup.center ↥(K i)) := fun i => by
    rw [← Nat.card_congr (Equiv.ofBijective (f i) ⟨hfinj i, hfsurj i⟩)]
    exact h3d i
  choose x hx using fun i => h3 ↥(K i) (hq i) (hcat i) (h3div i)
  obtain ⟨E, -, hE, hEc⟩ := uc22p20d_elemAbelian_of_commuting (X := X) 3 5 Nat.prime_three K
    (fun i => ((x i : ↥(K i)) : X)) hcomm2 (fun i => (x i).2)
    (fun i => by
      have h : (x i) ^ 3 = 1 := by rw [← (hx i).1]; exact pow_orderOf_eq_one _
      exact congrArg Subtype.val h)
    (fun i => by
      have hnc := (hx i).2
      rw [Subgroup.mem_center_iff] at hnc
      push Not at hnc
      obtain ⟨a, ha⟩ := hnc
      exact ⟨(a : X), a.2, fun h => ha (Subtype.ext h)⟩)
  exact absurd (hrk E 5 hE hEc) (by norm_num)

theorem uc22p20h_normal_map_of_char {X : Type*} [Group X] (R : Subgroup X) [R.Normal] (C : Subgroup ↥R)
    [C.Characteristic] : (C.map R.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hn
  refine ⟨MulAut.conjNormal g c, ?_, ?_⟩
  · exact Subgroup.characteristic_iff_le_comap.mp inferInstance (MulAut.conjNormal g) hc
  · simp [MulAut.conjNormal_apply]

theorem uc22p20h_centralizer_le_pCore {X : Type} [Group X] [Finite X] (hP : CFSG.pPrimeCore 3 X = ⊥) :
    ∀ x ∈ CFSG.solvableRadical X, (∀ q ∈ CFSG.pCore 3 X, q * x = x * q) → x ∈ CFSG.pCore 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hxR hxc
  set R := CFSG.solvableRadical X with hRdef
  haveI hRn : R.Normal := CFSG.Quasithin.A3.instNormalSolvableRadical X
  have hRs : Group.IsSolvable R := CFSG.Quasithin.A3.solvableRadical_isSolvable
  have hPR : CFSG.pPrimeCore 3 ↥R = ⊥ := by
    haveI := uc22p20h_normal_map_of_char R (CFSG.pPrimeCore 3 ↥R)
    have hcop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 ↥R).map R.subtype)) := by
      rw [Subgroup.card_map_of_injective R.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle : (CFSG.pPrimeCore 3 ↥R).map R.subtype ≤ CFSG.pPrimeCore 3 X :=
      le_sSup ⟨inferInstance, hcop⟩
    rw [hP, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective).1 hle
  have hF : CFSG.fittingSubgroup ↥R = CFSG.pCore 3 ↥R := CFSG.Fitting_eq_pcore ↥R 3 hPR
  have hcen := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hRs
  haveI := uc22p20h_normal_map_of_char R (CFSG.pCore 3 ↥R)
  have hle : (CFSG.pCore 3 ↥R).map R.subtype ≤ CFSG.pCore 3 X :=
    le_sSup ⟨inferInstance, (CFSG.pCore_isPGroup (p := 3) (G := ↥R)).map R.subtype⟩
  have hx : (⟨x, hxR⟩ : ↥R) ∈ CFSG.fittingSubgroup ↥R := by
    apply hcen
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    rw [hF] at hf
    apply Subtype.ext
    exact hxc (f : X) (hle ⟨f, hf, rfl⟩)
  rw [hF] at hx
  exact hle ⟨⟨x, hxR⟩, hx, rfl⟩

theorem uc22p20h_main_abstract {X : Type} [Group X] [Finite X] (hKG : CFSG.Open.IsKGroup X)
    (h3 : ThreeNoncentralFact) (hP : CFSG.pPrimeCore 3 X = ⊥)
    (hrk : ∀ (E : Subgroup X) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 3)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (K W : Fin 5 → Subgroup X) [hKn : ∀ i, (K i).Normal]
    [hWn : ∀ i, ((W i).subgroupOf (K i)).Normal]
    (hKperf : ∀ i, ⁅K i, K i⁆ = K i)
    (hWK : ∀ i, W i ≤ K i) (hWR : ∀ i, W i ≤ CFSG.solvableRadical X)
    (hsimple : ∀ i, IsSimpleGroup (↥(K i) ⧸ (W i).subgroupOf (K i)))
    (hnonab : ∀ i, ∃ a b : ↥(K i) ⧸ (W i).subgroupOf (K i), a * b ≠ b * a)
    (h3d : ∀ i, 3 ∣ Nat.card (↥(K i) ⧸ (W i).subgroupOf (K i)))
    (hℓd : ∀ i, ℓ ∣ Nat.card (↥(K i) ⧸ (W i).subgroupOf (K i)))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, ⁅a, b⁆ ∈ CFSG.solvableRadical X)
    (hsymm : ∀ i, ∃ σ : MulAut X, (K 0).map σ.toMonoidHom = K i) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hRn : (CFSG.solvableRadical X).Normal := CFSG.Quasithin.A3.instNormalSolvableRadical X
  have hRs : Group.IsSolvable (CFSG.solvableRadical X) :=
    CFSG.Quasithin.A3.solvableRadical_isSolvable
  haveI : (CFSG.pCore 3 X).Normal := inferInstance
  have hQp : IsPGroup 3 (CFSG.pCore 3 X) := CFSG.pCore_isPGroup
  have hCR := uc22p20h_centralizer_le_pCore hP
  have hcentiff : ∀ i, K i ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X) ↔
      K 0 ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X) := by
    intro i
    obtain ⟨σ, hσ⟩ := hsymm i
    have hσQ : ∀ q, σ q ∈ CFSG.pCore 3 X ↔ q ∈ CFSG.pCore 3 X := fun q => by
      have := Subgroup.ext_iff.1
        (Subgroup.characteristic_iff_comap_eq.1 (inferInstance : (CFSG.pCore 3 X).Characteristic) σ) q
      simpa using this
    constructor
    · intro h x hx
      have hσx : σ x ∈ K i := hσ ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hx
      have h1 := Subgroup.mem_centralizer_iff.1 (h hσx)
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h2 := h1 (σ q) ((hσQ q).2 hq)
      exact σ.injective (by simpa using h2)
    · intro h y hy
      rw [← hσ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : σ.symm q ∈ CFSG.pCore 3 X := (hσQ _).1 (by simpa using hq)
      have h2 := Subgroup.mem_centralizer_iff.1 (h hx) (σ.symm q) hq'
      have h3' := congrArg σ h2
      simpa using h3'
  by_cases hA : K 0 ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X)
  · exact uc22p20h_caseA hKG h3 hrk (CFSG.pCore 3 X) (CFSG.solvableRadical X) hRs hCR K W hKperf hWK hWR
      hsimple hnonab h3d hcomm (fun i => (hcentiff i).2 hA)
  · exact uc22p20h_caseB (CFSG.pCore 3 X) (CFSG.solvableRadical X) hQp hRs hrk ℓ hℓ hℓ5 K W hKperf hWR
      hsimple hnonab hℓd hcomm (fun i h => hA ((hcentiff i).1 h))

theorem uc22p20h_lift_elemAbelian_coprime {A : Type*} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card N)) (B : Subgroup A)
    (E₀ : Subgroup (A ⧸ N)) (hE₀ : IsElemAbelian p E₀) {n : ℕ} (hn : Nat.card E₀ = p ^ n)
    (hle : E₀ ≤ B.map (QuotientGroup.mk' N)) :
    ∃ E : Subgroup A, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ n := by
  set f : A →* A ⧸ N := QuotientGroup.mk' N with hf
  have hmap : (B ⊓ E₀.comap f).map f = E₀ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := hle hy
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
  have hdvd : p ^ n ∣ Nat.card (B ⊓ E₀.comap f : Subgroup A) := by
    rw [← hn]
    conv_lhs => rw [← hmap]
    exact Subgroup.card_map_dvd _ f
  obtain ⟨S, hScard, -, hSB'⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp (H := ⊥) (L := B ⊓ E₀.comap f)
      (by simp) hdvd bot_le
  have hSB : S ≤ B := hSB'.trans inf_le_left
  have hSE : ∀ x ∈ S, f x ∈ E₀ := fun x hx => (hSB' hx).2
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card N) := by
    rw [hScard]
    exact Nat.Coprime.pow_left _ hcop
  have hdisj : Disjoint S N := Subgroup.disjoint_of_coprime_natCard hcop'
  have hinj : ∀ x ∈ S, f x = 1 → x = 1 := by
    intro x hxS hx1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 hx1
    simpa using hdisj.le_bot ⟨hxS, hxN⟩
  have hinjOn : Set.InjOn f (S : Set A) := (Set.injOn_iff_map_eq_one f S).2 hinj
  refine ⟨S, hSB, ⟨?_, ?_⟩, hScard⟩
  · refine IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_
    refine hinjOn (S.mul_mem hx hy) (S.mul_mem hy hx) ?_
    rw [map_mul, map_mul]
    haveI : IsMulCommutative E₀ := hE₀.1
    exact setLike_mul_comm (hSE x hx) (hSE y hy)
  · intro x hx
    refine hinj _ (S.pow_mem hx p) ?_
    rw [map_pow]
    exact hE₀.2 _ (hSE x hx)

theorem uc22p20h_subgroupOf_le_solvableRadical {Y : Type} [Group Y] [Finite Y] (K N : Subgroup Y)
    [N.Normal] (hs : IsSimpleGroup (↥K ⧸ CFSG.solvableRadical ↥K))
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.solvableRadical ↥K)) (hN : Nat.Coprime 3 (Nat.card N)) :
    N.subgroupOf K ≤ CFSG.solvableRadical ↥K := by
  intro y hy
  let ρ : ↥K →* ↥K ⧸ CFSG.solvableRadical ↥K := QuotientGroup.mk' _
  haveI : (N.subgroupOf K).Normal := Subgroup.Normal.subgroupOf inferInstance K
  haveI : ((N.subgroupOf K).map ρ).Normal := Subgroup.Normal.map inferInstance ρ
    (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf K).map ρ) with h | h
  · have : ρ y ∈ (N.subgroupOf K).map ρ := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff y).1 this
  · exfalso
    have h1 : Nat.card (↥K ⧸ CFSG.solvableRadical ↥K) ∣ Nat.card (N.subgroupOf K) := by
      have := Subgroup.card_map_dvd (H := N.subgroupOf K) ρ
      rwa [h, Subgroup.card_top] at this
    have h2 : Nat.card (N.subgroupOf K) ∣ Nat.card N := by
      have e1 : Nat.card ((N.subgroupOf K).map K.subtype) = Nat.card (N.subgroupOf K) :=
        Subgroup.card_map_of_injective K.subtype_injective
      rw [← e1, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact absurd (Nat.Coprime.eq_one_of_dvd hN (h3.trans (h1.trans h2))) (by norm_num)

theorem uc22p20h_bar_equiv {Y : Type} [Group Y] [Finite Y] (N K : Subgroup Y) [N.Normal]
    [hW : (((CFSG.solvableRadical ↥K).map K.subtype).map (QuotientGroup.mk' N)).Normal]
    (hs : IsSimpleGroup (↥K ⧸ CFSG.solvableRadical ↥K))
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.solvableRadical ↥K)) (hN : Nat.Coprime 3 (Nat.card N)) :
    Nonempty ((↥K ⧸ CFSG.solvableRadical ↥K) ≃*
      (↥(K.map (QuotientGroup.mk' N)) ⧸
        (((CFSG.solvableRadical ↥K).map K.subtype).map (QuotientGroup.mk' N)).subgroupOf
          (K.map (QuotientGroup.mk' N)))) := by
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  let S : Subgroup Y := (CFSG.solvableRadical ↥K).map K.subtype
  haveI : ((S.map π).subgroupOf (K.map π)).Normal := Subgroup.Normal.subgroupOf hW _
  let ξ : ↥K →* ↥(K.map π) ⧸ (S.map π).subgroupOf (K.map π) :=
    (QuotientGroup.mk' ((S.map π).subgroupOf (K.map π))).comp (π.subgroupMap K)
  have hξ : Function.Surjective ξ :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective _ _)
  have hker : ξ.ker = CFSG.solvableRadical ↥K := by
    ext k
    constructor
    · intro hk
      have h1 : π.subgroupMap K k ∈ (S.map π).subgroupOf (K.map π) :=
        (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hk)
      have h2 : π (k : Y) ∈ S.map π := h1
      obtain ⟨_, ⟨t, ht, rfl⟩, hsk⟩ := h2
      have hyN : (k : Y)⁻¹ * (t : Y) ∈ N := (QuotientGroup.eq).1 hsk.symm
      have hyS : k⁻¹ * t ∈ CFSG.solvableRadical ↥K :=
        uc22p20h_subgroupOf_le_solvableRadical K N hs h3 hN (Subgroup.mem_subgroupOf.2 hyN)
      have : k = t * (k⁻¹ * t)⁻¹ := by group
      rw [this]
      exact mul_mem ht (inv_mem hyS)
    · intro hk
      rw [MonoidHom.mem_ker]
      apply (QuotientGroup.eq_one_iff _).2
      show π (k : Y) ∈ S.map π
      exact ⟨k, ⟨k, hk, rfl⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ξ hξ)⟩

theorem uc22p20h_main_abstract2 {Y : Type} [Group Y] [Finite Y] (hKG : CFSG.Open.IsKGroup Y)
    (h3 : ThreeNoncentralFact)
    (hrk : ∀ (E : Subgroup Y) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 3)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (K : Fin 5 → Subgroup Y) [hKn : ∀ i, (K i).Normal]
    (hKperf : ∀ i, ⁅K i, K i⁆ = K i)
    (hsimple : ∀ i, IsSimpleGroup (↥(K i) ⧸ CFSG.solvableRadical ↥(K i)))
    (hnonab : ∀ i, ∃ a b : ↥(K i) ⧸ CFSG.solvableRadical ↥(K i), a * b ≠ b * a)
    (h3d : ∀ i, 3 ∣ Nat.card (↥(K i) ⧸ CFSG.solvableRadical ↥(K i)))
    (hℓd : ∀ i, ℓ ∣ Nat.card (↥(K i) ⧸ CFSG.solvableRadical ↥(K i)))
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, ⁅a, b⁆ ∈ CFSG.solvableRadical Y)
    (hsymm : ∀ i, ∃ σ : MulAut Y, (K 0).map σ.toMonoidHom = K i) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup Y, N = CFSG.pPrimeCore 3 Y := ⟨_, rfl⟩
  haveI hNn : N.Normal := hNdef ▸ CFSG.pPrimeCore_normal
  have hNcop : Nat.Coprime 3 (Nat.card N) := hNdef ▸ CFSG.pPrimeCore_coprime_card
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  obtain ⟨S, hSdef⟩ : ∃ S : Fin 5 → Subgroup Y,
      ∀ i, S i = (CFSG.solvableRadical ↥(K i)).map (K i).subtype := ⟨_, fun _ => rfl⟩
  have hSK : ∀ i, S i ≤ K i := fun i => by rw [hSdef]; exact Subgroup.map_subtype_le _
  haveI hSn : ∀ i, (S i).Normal := fun i => by
    rw [hSdef]; exact uc22p20h_normal_map_of_char (K i) _
  have hSsolv : ∀ i, Group.IsSolvable (S i) := fun i => by
    rw [hSdef]
    haveI : Group.IsSolvable ↥(CFSG.solvableRadical ↥(K i)) :=
      CFSG.Quasithin.A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective (f := (K i).subtype.subgroupMap _)
      (MonoidHom.subgroupMap_surjective _ _)
  obtain ⟨Kt, hKtdef⟩ : ∃ Kt : Fin 5 → Subgroup (Y ⧸ N), ∀ i, Kt i = (K i).map π :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Wt, hWtdef⟩ : ∃ Wt : Fin 5 → Subgroup (Y ⧸ N), ∀ i, Wt i = (S i).map π :=
    ⟨_, fun _ => rfl⟩
  haveI hKtn : ∀ i, (Kt i).Normal := fun i => by
    rw [hKtdef]; exact Subgroup.Normal.map (hKn i) π hπ
  haveI hWtn : ∀ i, (Wt i).Normal := fun i => by
    rw [hWtdef]; exact Subgroup.Normal.map (hSn i) π hπ
  haveI hWtn' : ∀ i, ((Wt i).subgroupOf (Kt i)).Normal := fun i =>
    Subgroup.Normal.subgroupOf (hWtn i) (Kt i)
  have hKtperf : ∀ i, ⁅Kt i, Kt i⁆ = Kt i := fun i => by
    rw [hKtdef, ← Subgroup.map_commutator, hKperf i]
  have hWtK : ∀ i, Wt i ≤ Kt i := fun i => by
    rw [hWtdef, hKtdef]; exact Subgroup.map_mono (hSK i)
  have hRY : (CFSG.solvableRadical Y).map π ≤ CFSG.solvableRadical (Y ⧸ N) := by
    refine CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (Subgroup.Normal.map inferInstance π hπ) ?_
    haveI : Group.IsSolvable ↥(CFSG.solvableRadical Y) :=
      CFSG.Quasithin.A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective (f := π.subgroupMap _)
      (MonoidHom.subgroupMap_surjective _ _)
  have hWtR : ∀ i, Wt i ≤ CFSG.solvableRadical (Y ⧸ N) := fun i => by
    rw [hWtdef]
    refine CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (Subgroup.Normal.map (hSn i) π hπ) ?_
    haveI := hSsolv i
    exact Group.isSolvable_of_surjective (f := π.subgroupMap _)
      (MonoidHom.subgroupMap_surjective _ _)
  have hcommt : ∀ i j, i ≠ j → ∀ a ∈ Kt i, ∀ b ∈ Kt j, ⁅a, b⁆ ∈ CFSG.solvableRadical (Y ⧸ N) := by
    intro i j hij a ha b hb
    rw [hKtdef] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_commutatorElement]
    exact hRY ⟨_, hcomm i j hij a' ha' b' hb', rfl⟩
  have hsymmt : ∀ i, ∃ σ : MulAut (Y ⧸ N), (Kt 0).map σ.toMonoidHom = Kt i := by
    intro i
    obtain ⟨σ, hσ⟩ := hsymm i
    have hσN : N.map σ.toMonoidHom = N := hNdef ▸ CFSG.pPrimeCore_map_iso 3 σ
    refine ⟨QuotientGroup.congr N N σ hσN, ?_⟩
    have hcomp : (QuotientGroup.congr N N σ hσN).toMonoidHom.comp π = π.comp σ.toMonoidHom := by
      ext y; rfl
    rw [hKtdef, hKtdef, Subgroup.map_map, hcomp, ← Subgroup.map_map, hσ]
  have hrkt : ∀ (E : Subgroup (Y ⧸ N)) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 3 := by
    intro E₀ k hE₀ hk
    obtain ⟨E, -, hE, hEc⟩ := uc22p20h_lift_elemAbelian_coprime N Nat.prime_three hNcop ⊤ E₀ hE₀ hk
      (by rw [Subgroup.map_top_of_surjective _ hπ]; exact le_top)
    exact hrk E k hE hEc
  have hKGt : CFSG.Open.IsKGroup (Y ⧸ N) := hKG.quotient N
  have hP : CFSG.pPrimeCore 3 (Y ⧸ N) = ⊥ := by
    subst hNdef; exact CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hbar : ∀ i, Nonempty ((↥(K i) ⧸ CFSG.solvableRadical ↥(K i)) ≃*
      (↥(Kt i) ⧸ (Wt i).subgroupOf (Kt i))) := by
    intro i
    have hKtfun : Kt = fun i => (K i).map π := funext hKtdef
    have hSfun : S = fun i => (CFSG.solvableRadical ↥(K i)).map (K i).subtype := funext hSdef
    have hWtfun : Wt = fun i => (S i).map π := funext hWtdef
    have hWtn2 := hWtn i
    subst hWtfun hKtfun
    subst hSfun
    exact uc22p20h_bar_equiv N (K i) (hsimple i) (h3d i) hNcop (hW := hWtn2)
  let e : ∀ i, (↥(K i) ⧸ CFSG.solvableRadical ↥(K i)) ≃* (↥(Kt i) ⧸ (Wt i).subgroupOf (Kt i)) :=
    fun i => (hbar i).some
  have hsimplet : ∀ i, IsSimpleGroup (↥(Kt i) ⧸ (Wt i).subgroupOf (Kt i)) := fun i => by
    haveI := hsimple i
    exact (e i).symm.isSimpleGroup
  have hnonabt : ∀ i, ∃ a b : ↥(Kt i) ⧸ (Wt i).subgroupOf (Kt i), a * b ≠ b * a := by
    intro i
    obtain ⟨a, b, hab⟩ := hnonab i
    exact ⟨e i a, e i b, fun h => hab ((e i).injective (by rw [map_mul, map_mul]; exact h))⟩
  have h3dt : ∀ i, 3 ∣ Nat.card (↥(Kt i) ⧸ (Wt i).subgroupOf (Kt i)) := fun i => by
    rw [← Nat.card_congr (e i).toEquiv]; exact h3d i
  have hℓdt : ∀ i, ℓ ∣ Nat.card (↥(Kt i) ⧸ (Wt i).subgroupOf (Kt i)) := fun i => by
    rw [← Nat.card_congr (e i).toEquiv]; exact hℓd i
  exact uc22p20h_main_abstract hKGt h3 hP hrkt ℓ hℓ hℓ5 Kt Wt hKtperf hWtK hWtR hsimplet hnonabt h3dt hℓdt
    hcommt hsymmt

theorem uc22p20h_sq_sub_one_eq (r : ℕ) (hr : 1 ≤ r) : r ^ 2 - 1 = (r - 1) * (r + 1) := by
  zify [hr, Nat.one_le_pow 2 r hr]
  ring

theorem uc22p20h_ordA_one_dvd {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    3 ∣ CFSG.Open.ordA 1 r ∧ r ∣ CFSG.Open.ordA 1 r := by
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have h3r : ¬ 3 ∣ r := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h).symm
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hg : Nat.gcd 2 (r - 1) = 2 := by
    apply Nat.gcd_eq_left
    obtain ⟨k, rfl⟩ := hodd
    omega
  have hunfold : CFSG.Open.ordA 1 r = (r * (r ^ 2 - 1)) / 2 := by
    simp [CFSG.Open.ordA, hg]
  have h2 : 2 ∣ r ^ 2 - 1 := by
    rw [uc22p20h_sq_sub_one_eq r hr1]
    obtain ⟨k, rfl⟩ := hodd
    exact ⟨(k) * (2 * k + 2), by simp only [Nat.add_sub_cancel]; ring⟩
  obtain ⟨m, hm⟩ := h2
  have hm' : (r * (r ^ 2 - 1)) / 2 = r * m := by
    rw [hm, ← mul_assoc, mul_comm r 2, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hunfold, hm']
  refine ⟨?_, dvd_mul_right r m⟩
  have h3 : 3 ∣ r ^ 2 - 1 := by
    rw [uc22p20h_sq_sub_one_eq r hr1]
    rcases (by omega : 3 ∣ r - 1 ∨ 3 ∣ r + 1) with h | h
    · exact Dvd.dvd.mul_right h _
    · exact Dvd.dvd.mul_left h _
  rw [hm] at h3
  exact Dvd.dvd.mul_left ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)) r

theorem uc22p20h_ordA_two_dvd_three {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : 3 ∣ CFSG.Open.ordA 2 r := by
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hunfold : CFSG.Open.ordA 2 r =
      (r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1))) / Nat.gcd 3 (r - 1) := by
    simp [CFSG.Open.ordA, Finset.prod_Icc_succ_top, mul_assoc]
  rw [hunfold]
  have hgpos : 0 < Nat.gcd 3 (r - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have key : 3 * Nat.gcd 3 (r - 1) ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
    by_cases h3 : 3 ∣ r
    · have hg : Nat.gcd 3 (r - 1) = 1 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
      rw [hg, mul_one]
      exact Dvd.dvd.mul_right (dvd_pow h3 (by norm_num)) _
    · by_cases h31 : 3 ∣ r - 1
      · have hg : Nat.gcd 3 (r - 1) = 3 := Nat.gcd_eq_left h31
        rw [hg]
        have h2 : 3 ∣ r ^ 2 - 1 := h31.trans (by simpa using Nat.sub_dvd_pow_sub_pow r 1 2)
        have h3' : 3 ∣ r ^ 3 - 1 := h31.trans (by simpa using Nat.sub_dvd_pow_sub_pow r 1 3)
        exact Dvd.dvd.mul_left (mul_dvd_mul h2 h3') _
      · have hg : Nat.gcd 3 (r - 1) = 1 :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h31
        rw [hg, mul_one]
        have h4 : 3 ∣ r + 1 := by omega
        have h2 : 3 ∣ r ^ 2 - 1 := by
          rw [uc22p20h_sq_sub_one_eq r hr1]; exact Dvd.dvd.mul_left h4 _
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 _) _
  obtain ⟨c, hc⟩ := key
  rw [hc, show 3 * Nat.gcd 3 (r - 1) * c = Nat.gcd 3 (r - 1) * (3 * c) by ring,
    Nat.mul_div_cancel_left _ hgpos]
  exact dvd_mul_right 3 c

theorem uc22p20h_ordA_two_three_dvd : 13 ∣ CFSG.Open.ordA 2 3 := by
  decide +kernel

theorem uc22p20h_shape_L2 {B : Type} [Group B] {r : ℕ} (h : IsL2Odd B r) (hr : r.Prime) (hr2 : r ≠ 2) :
    r ≠ 3 ∧ 3 ∣ Nat.card B ∧ r ∣ Nat.card B := by
  have hadm := CFSG.Blueprint.LieModel.admissible h
  have hr3 : r ≠ 3 := by
    intro h3
    subst h3
    obtain ⟨-, -, -, -, h23⟩ := hadm
    exact h23 (by simp)
  have hcard : Nat.card B = CFSG.Open.ordA 1 r := by
    have := CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : 2 ≠ 0) h
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using this
  rw [hcard]
  exact ⟨hr3, (uc22p20h_ordA_one_dvd hr hr2 hr3).1, (uc22p20h_ordA_one_dvd hr hr2 hr3).2⟩

theorem uc22p20h_shape_L3 {B : Type} [Group B] {r : ℕ} (h : IsL3Odd B r) (hr : r.Prime) (hr2 : r ≠ 2) :
    3 ∣ Nat.card B ∧ r ∣ Nat.card B ∧ (r = 3 → 13 ∣ Nat.card B) := by
  have hcard : Nat.card B = CFSG.Open.ordA 2 r := by
    have := CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : 3 ≠ 0) h
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using this
  have hdvd := CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd
    (t := .PSL) (n := 3) (by simp [CFSG.EvenSmallLie.CatalogOrders.lieMin]) r
  have hexp : CFSG.EvenSmallLie.CatalogOrders.lieExp .PSL 3 = 3 := by
    simp [CFSG.EvenSmallLie.CatalogOrders.lieExp]
  rw [hexp] at hdvd
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]; exact uc22p20h_ordA_two_dvd_three hr hr2
  · rw [hcard]
    exact (dvd_pow_self r (by norm_num)).trans (hdvd.trans (by
      simp [CFSG.EvenSmallLie.CatalogOrders.lieOrd]))
  · rintro rfl
    rw [hcard]; exact uc22p20h_ordA_two_three_dvd

theorem uc22p20h_shape_alt {B : Type} [Group B] {n : ℕ} (h : IsAlt B n) (hn : n = 6 ∨ n = 7) :
    3 ∣ Nat.card B ∧ 5 ∣ Nat.card B := by
  obtain ⟨e⟩ := h
  rcases hn with rfl | rfl <;>
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide

theorem uc22p20h_commutator_le_solvRad {G : Type} [Group G] [Finite G] {X C K' : Subgroup G}
    (hC : C ∈ CFSG.Quasithin.cComp X) (hK' : K' ∈ CFSG.Quasithin.cComp X) (hne : C ≠ K') :
    ⁅C, K'⁆ ≤ CFSG.Quasithin.solvRad X := by
  have hnormK' : CFSG.Quasithin.cCompSpan X ≤ normalizer (K' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.Quasithin.cComp_normal_span_of_le hK').1).1
      (CFSG.Quasithin.cComp_normal_span_of_le hK').2
  rcases CFSG.Quasithin.cComp_commutator_dichotomy_of_le hC
      (CFSG.Quasithin.le_of_mem_cComp hK') with ⟨h1, -⟩ | h2
  · exact h1
  · exfalso
    have hle : ⁅C, K'⁆ ≤ K' := by
      refine Subgroup.commutator_le.mpr fun c' hc' k' hk' => ?_
      have hc'N := hnormK' (CFSG.Quasithin.le_cCompSpan hC hc')
      have : c' * k' * c'⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.1 hc'N k').1 hk'
      exact K'.mul_mem this (K'.inv_mem hk')
    have hCle' : C ≤ K' := (CFSG.Quasithin.le_conjClosure C K').trans (h2 ▸ hle)
    rcases eq_or_lt_of_le hCle' with heq | hlt
    · exact hne heq
    · exact CFSG.Quasithin.not_subnormal_of_mem_cComp hK'  hlt
        (CFSG.Quasithin.ne_bot_of_mem_cComp hC) (CFSG.Quasithin.perfect_of_mem_cComp hC)
        (CFSG.Quasithin.subnormal_of_mem_cComp hC)

theorem uc22p20h_barInf_equiv_subgroupOf {G : Type} [Group G] [Finite G] {C Yg : Subgroup G} (hle : C ≤ Yg) :
    Nonempty (BarInf C ≃* (↥(C.subgroupOf Yg) ⧸ CFSG.solvableRadical ↥(C.subgroupOf Yg))) := by
  let e : ↥(C.subgroupOf Yg) ≃* ↥C := Subgroup.subgroupOfEquivOfLe hle
  have hker : Group.IsSolvable ↥e.toMonoidHom.ker := by
    have hbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
    rw [hbot]
    infer_instance
  exact ⟨(CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.solQuotEquiv
    (ρ := e.toMonoidHom) e.surjective hker).symm⟩

theorem uc22p20h_shape_of_alt {G : Type} [Group G] [Finite G] {Yg : Subgroup G} (h : S20_2Alt Yg) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ∀ C ∈ CFSG.Quasithin.cComp Yg,
      3 ∣ Nat.card (BarInf C) ∧ ℓ ∣ Nat.card (BarInf C) := by
  rcases h.1 with ⟨r, hr, hr2, hC⟩ | hC
  · by_cases hr3 : r = 3
    · subst hr3
      refine ⟨13, by norm_num, by norm_num, fun C hCm => ?_⟩
      rcases hC C hCm with h2 | h3
      · exact absurd (uc22p20h_shape_L2 h2 hr hr2).1 (by norm_num)
      · exact ⟨(uc22p20h_shape_L3 h3 hr hr2).1, (uc22p20h_shape_L3 h3 hr hr2).2.2 rfl⟩
    · have hr5 : 5 ≤ r := by
        have h2 := hr.two_le
        have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
        omega
      refine ⟨r, hr, hr5, fun C hCm => ?_⟩
      rcases hC C hCm with h2 | h3
      · exact ⟨(uc22p20h_shape_L2 h2 hr hr2).2.1, (uc22p20h_shape_L2 h2 hr hr2).2.2⟩
      · exact ⟨(uc22p20h_shape_L3 h3 hr hr2).1, (uc22p20h_shape_L3 h3 hr hr2).2.1⟩
  · refine ⟨5, by norm_num, le_rfl, fun C hCm => ?_⟩
    rcases hC C hCm with h6 | h7
    · exact uc22p20h_shape_alt h6 (Or.inl rfl)
    · exact uc22p20h_shape_alt h7 (Or.inr rfl)

variable {G : Type} [Group G] [Finite G]

theorem uc22p20h_five (D : Data G) (h3 : ThreeNoncentralFact) : FiveConjugatesNotAlt D := by
  intro H hH hrk3 K hK g hg hinj hAlt
  have hHtop : H ≠ ⊤ := by
    haveI := D.standing.simple
    obtain ⟨N, hN, hHN⟩ := uc22p20a_exists_mem_calMOf D hH
    intro htop
    have hNtop : N = ⊤ := top_le_iff.mp (htop ▸ hHN)
    exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1 hNtop
  set Yg : Subgroup G := uc22p20bOrb H K with hYdef
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp hK
  have hYH : Yg ≤ H := uc22p20b_orb_le le_rfl hKH
  have hHn : H ≤ normalizer (Yg : Set G) := uc22p20b_le_normalizer_orb H K
  have hspan : sSup (CFSG.Quasithin.cComp Yg) = Yg := uc22p20b_sSup_cComp_orb hK le_rfl
  have hcC : CFSG.Quasithin.cComp Yg = Set.range (fun t : H => uc22p20bCj (t : G) K) :=
    uc22p20b_cComp_orb hK le_rfl
  obtain ⟨Ki, hKidef⟩ : ∃ Ki : Fin 5 → Subgroup G, ∀ i, Ki i = uc22p20bCj (g i) K :=
    ⟨_, fun _ => rfl⟩
  have hKi : ∀ i, Ki i ∈ CFSG.Quasithin.cComp Yg := fun i => by
    rw [hKidef, hcC]; exact ⟨⟨g i, hg i⟩, rfl⟩
  have hKiY : ∀ i, Ki i ≤ Yg := fun i => CFSG.Quasithin.le_of_mem_cComp (hKi i)
  have hne : ∀ i j, i ≠ j → Ki i ≠ Ki j := fun i j h h' => h (hinj (by
    show uc22p20bCj (g i) K = uc22p20bCj (g j) K
    rw [← hKidef i, ← hKidef j]; exact h'))
  have hYtop : Yg ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hYH))
  have hKGY : CFSG.Open.IsKGroup ↥Yg := D.standing.kProper.isKGroup Yg hYtop
  obtain ⟨ℓ, hℓ, hℓ5, hshape⟩ := uc22p20h_shape_of_alt hAlt
  have hnormG : ∀ i, Yg ≤ normalizer (Ki i : Set G) := fun i => by
    have h := CFSG.Quasithin.cComp_normal_span_of_le (hKi i)
    have h2 := (Subgroup.normal_subgroupOf_iff_le_normalizer h.1).1 h.2
    rwa [show CFSG.Quasithin.cCompSpan Yg = Yg from hspan] at h2
  obtain ⟨K'', hK''def⟩ : ∃ K'' : Fin 5 → Subgroup ↥Yg, ∀ i, K'' i = (Ki i).subgroupOf Yg :=
    ⟨_, fun _ => rfl⟩
  haveI hK''n : ∀ i, (K'' i).Normal := fun i => by
    rw [hK''def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hKiY i)).2 (hnormG i)
  have hK''perf : ∀ i, ⁅K'' i, K'' i⁆ = K'' i := fun i => by
    rw [hK''def]
    exact CFSG.Quasithin.perfect_of_mem_cComp (CFSG.Quasithin.subgroupOf_mem_cComp (hKi i))
  have hbar : ∀ i, Nonempty (BarInf (Ki i) ≃*
      (↥(K'' i) ⧸ CFSG.solvableRadical ↥(K'' i))) := fun i => by
    rw [hK''def]; exact uc22p20h_barInf_equiv_subgroupOf (hKiY i)
  let e := fun i => (hbar i).some
  have hsimple'' : ∀ i, IsSimpleGroup (↥(K'' i) ⧸ CFSG.solvableRadical ↥(K'' i)) := fun i => by
    haveI := (uc22p20c_barInf_simple (hKi i)).1
    exact (e i).symm.isSimpleGroup
  have hnonab'' : ∀ i, ∃ a b : ↥(K'' i) ⧸ CFSG.solvableRadical ↥(K'' i), a * b ≠ b * a := by
    intro i
    obtain ⟨a, b, hab⟩ := (uc22p20c_barInf_simple (hKi i)).2
    exact ⟨e i a, e i b, fun h => hab ((e i).injective (by rw [map_mul, map_mul]; exact h))⟩
  have h3d'' : ∀ i, 3 ∣ Nat.card (↥(K'' i) ⧸ CFSG.solvableRadical ↥(K'' i)) := fun i => by
    rw [← Nat.card_congr (e i).toEquiv]; exact (hshape _ (hKi i)).1
  have hℓd'' : ∀ i, ℓ ∣ Nat.card (↥(K'' i) ⧸ CFSG.solvableRadical ↥(K'' i)) := fun i => by
    rw [← Nat.card_congr (e i).toEquiv]; exact (hshape _ (hKi i)).2
  have hcomm'' : ∀ i j, i ≠ j → ∀ a ∈ K'' i, ∀ b ∈ K'' j,
      ⁅a, b⁆ ∈ CFSG.solvableRadical ↥Yg := by
    intro i j hij a ha b hb
    rw [hK''def] at ha hb
    have h1 : ⁅(a : G), (b : G)⁆ ∈ CFSG.Quasithin.solvRad Yg :=
      uc22p20h_commutator_le_solvRad (hKi i) (hKi j) (hne i j hij)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 ha)
          (Subgroup.mem_subgroupOf.1 hb))
    rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have : z = ⁅a, b⁆ := Subtype.ext hzeq
    rw [← this]
    exact hz
  have hsymm'' : ∀ i, ∃ σ : MulAut ↥Yg, (K'' 0).map σ.toMonoidHom = K'' i := by
    intro i
    obtain ⟨t, htdef⟩ : ∃ t : G, t = g i * (g 0)⁻¹ := ⟨_, rfl⟩
    have htH : t ∈ H := htdef ▸ H.mul_mem (hg i) (H.inv_mem (hg 0))
    have htn : t ∈ normalizer (Yg : Set G) := hHn htH
    have hmap : Yg.map (MulAut.conj t).toMonoidHom = Yg :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 htn
    let σ : ↥Yg ≃* ↥Yg :=
      (MulEquiv.subgroupMap (MulAut.conj t) Yg).trans (MulEquiv.subgroupCongr hmap)
    have hσ : ∀ y : ↥Yg, ((σ y : ↥Yg) : G) = t * y * t⁻¹ := fun y => rfl
    have hKt : Ki i = uc22p20bCj t (Ki 0) := by
      rw [hKidef, hKidef, uc22p20b_cj_cj, htdef, inv_mul_cancel_right]
    refine ⟨σ, ?_⟩
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hK''def] at hy ⊢
      show ((σ y : ↥Yg) : G) ∈ Ki i
      rw [hσ, hKt]
      exact uc22p20b_mem_cj.2 ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
    · intro hz
      rw [hK''def] at hz
      have hzK : (z : G) ∈ Ki i := Subgroup.mem_subgroupOf.1 hz
      rw [hKt] at hzK
      obtain ⟨y', hy', hyz⟩ := uc22p20b_mem_cj.1 hzK
      have hy'Y : y' ∈ Yg := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htn) (z : G)).1 z.2
        have h2 : t⁻¹ * (z : G) * t⁻¹⁻¹ = y' := by
          rw [← hyz]; group
        rw [← h2]; exact h1
      refine ⟨⟨y', hy'Y⟩, ?_, ?_⟩
      · rw [hK''def]; exact Subgroup.mem_subgroupOf.2 hy'
      · refine Subtype.ext ?_
        show ((σ ⟨y', hy'Y⟩ : ↥Yg) : G) = (z : G)
        rw [hσ]; exact hyz
  have hrk'' : ∀ (E : Subgroup ↥Yg) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → k ≤ 3 := by
    intro E k hE hk
    have h1 := uc22p20h_elemAbelian_map_card Yg.subtype Yg.subtype_injective hE
    have hEH : E.map Yg.subtype ≤ H := (Subgroup.map_subtype_le E).trans hYH
    exact (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEH h1.1
      (by rw [h1.2, hk])).trans hrk3
  exact uc22p20h_main_abstract2 hKGY h3 hrk'' ℓ hℓ hℓ5 K'' hK''perf hsimple'' hnonab'' h3d'' hℓd''
    hcomm'' hsymm''

end CFSG.LocalAnalysis.UniquenessCase.UC22
