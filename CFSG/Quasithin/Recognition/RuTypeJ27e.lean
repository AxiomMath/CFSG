module

public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import Certificates.Certificate17010
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6


public section

namespace CFSG.Quasithin.RuType

open CFSG.QuasithinUnique

section Sylow

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem comm_of_isCyclic [IsCyclic X] (a b : X) : a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  exact (Commute.zpow_zpow_self g m n).eq

theorem sylow_normal_of_index {p : ℕ} [Fact p.Prime] (P : Sylow p X)
    (h : ∀ n, n ∣ P.index → n % p = 1 % p → n = 1) : (P : Subgroup X).Normal := by
  have hc := card_sylow_modEq_one p X
  have hd := Sylow.card_dvd_index P
  have h1 : Nat.card (Sylow p X) = 1 := h _ hd hc
  have : Subsingleton (Sylow p X) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Sylow.normal_of_subsingleton P

omit [Finite X] in
theorem eq_one_of_mem_coprime {P R : Subgroup X} (hcop : Nat.Coprime (Nat.card P) (Nat.card R))
    {x : X} (hP : x ∈ P) (hR : x ∈ R) : x = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (Subgroup.orderOf_dvd_natCard P hP)
    (Subgroup.orderOf_dvd_natCard R hR))

theorem comm_of_normal_coprime (P R : Subgroup X) (hPn : P.Normal) (hRn : R.Normal)
    (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hR : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card R)) (hcard : Nat.card P * Nat.card R = Nat.card X) :
    ∀ x y : X, x * y = y * x := by
  classical
  have hdis : Disjoint P R := by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    exact eq_one_of_mem_coprime hcop hx hy
  have hcomm : ∀ a ∈ P, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    (Subgroup.commute_of_normal_of_disjoint P R hPn hRn hdis a b ha hb).eq
  let F : P × R → X := fun q => (q.1 : X) * q.2
  have hF : Function.Injective F := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : X) * b = a' * b' := h
    have h2 : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ := by
      calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
        _ = (a' : X)⁻¹ * (a' * b') * (b : X)⁻¹ := by rw [h1]
        _ = b' * (b : X)⁻¹ := by group
    have h3 := eq_one_of_mem_coprime hcop (mul_mem (inv_mem a'.2) a.2)
      (h2 ▸ mul_mem b'.2 (inv_mem b.2))
    have haa : (a : X) = a' := by
      calc (a : X) = a' * ((a' : X)⁻¹ * a) := by group
        _ = a' := by rw [h3, mul_one]
    have hbb : (b : X) = b' := by
      rw [haa] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext haa) (Subtype.ext hbb)
  have hbij : Function.Bijective F :=
    hF.bijective_of_nat_card_le (le_of_eq (by rw [Nat.card_prod, hcard]))
  intro x y
  obtain ⟨⟨a, b⟩, rfl⟩ := hbij.2 x
  obtain ⟨⟨a', b'⟩, rfl⟩ := hbij.2 y
  show (a : X) * b * (a' * b') = a' * b' * (a * b)
  have e1 := hcomm _ a'.2 _ b.2
  have e2 := hcomm _ a.2 _ b'.2
  calc (a : X) * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [e1]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [hP _ a.2 _ a'.2, hR _ b.2 _ b'.2]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [e2]
    _ = a' * b' * (a * b) := by group

theorem card_sylow_of_sq_not_dvd {p : ℕ} [hp : Fact p.Prime] (P : Sylow p X)
    (h1 : p ∣ Nat.card X) (h2 : ¬ p ^ 2 ∣ Nat.card X) : Nat.card P = p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : Nat.card P ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd ⊢
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k
    · exfalso
      apply P.ne_bot_of_dvd_card h1
      rw [← Subgroup.card_eq_one, hk, pow_zero]
    · rw [pow_one]
  · exact absurd ((pow_dvd_pow p h).trans hdvd) h2

theorem card_sylow_of_cube_not_dvd {p : ℕ} [hp : Fact p.Prime] (P : Sylow p X)
    (h1 : p ^ 2 ∣ Nat.card X) (h2 : ¬ p ^ 3 ∣ Nat.card X) : Nat.card P = p ^ 2 := by
  have hc := P.card_eq_multiplicity
  have hle : (Nat.card X).factorization p ≤ 2 := by
    by_contra hlt
    push Not at hlt
    apply h2
    exact (pow_dvd_pow p hlt).trans (Nat.ordProj_dvd _ _)
  have hge : 2 ≤ (Nat.card X).factorization p :=
    (hp.out.pow_dvd_iff_le_factorization (Nat.card_pos (α := X)).ne').mp h1
  rw [hc, show (Nat.card X).factorization p = 2 by omega]

theorem comm_of_card_fifteen (h15 : Nat.card X = 15) : ∀ x y : X, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P3⟩ := (inferInstance : Nonempty (Sylow 3 X))
  obtain ⟨P5⟩ := (inferInstance : Nonempty (Sylow 5 X))
  have h3 := card_sylow_of_sq_not_dvd P3 (by rw [h15]; norm_num) (by rw [h15]; norm_num)
  have h5 := card_sylow_of_sq_not_dvd P5 (by rw [h15]; norm_num) (by rw [h15]; norm_num)
  have hi3 : (P3 : Subgroup X).index = 5 := by
    have := (P3 : Subgroup X).card_mul_index
    rw [h3, h15] at this
    omega
  have hi5 : (P5 : Subgroup X).index = 3 := by
    have := (P5 : Subgroup X).card_mul_index
    rw [h5, h15] at this
    omega
  have hn3 := sylow_normal_of_index P3 (by
    intro n hn hmod
    rw [hi3] at hn
    have : n ≤ 5 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> simp_all)
  have hn5 := sylow_normal_of_index P5 (by
    intro n hn hmod
    rw [hi5] at hn
    have : n ≤ 3 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> simp_all)
  have hab : ∀ (P : Subgroup X) (q : ℕ) [Fact q.Prime], Nat.card P = q →
      ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro P q _ hq a ha b hb
    have : IsCyclic P := isCyclic_of_prime_card hq
    exact congrArg Subtype.val (comm_of_isCyclic (⟨a, ha⟩ : P) ⟨b, hb⟩)
  exact comm_of_normal_coprime P3 P5 hn3 hn5 (hab P3 3 h3) (hab P5 5 h5)
    (by rw [h3, h5]; norm_num) (by rw [h3, h5, h15])

theorem comm_of_card_fortyfive (h45 : Nat.card X = 45) : ∀ x y : X, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P3⟩ := (inferInstance : Nonempty (Sylow 3 X))
  obtain ⟨P5⟩ := (inferInstance : Nonempty (Sylow 5 X))
  have h3 := card_sylow_of_cube_not_dvd P3 (by rw [h45]; norm_num) (by rw [h45]; norm_num)
  have h5 := card_sylow_of_sq_not_dvd P5 (by rw [h45]; norm_num) (by rw [h45]; norm_num)
  have hi3 : (P3 : Subgroup X).index = 5 := by
    have := (P3 : Subgroup X).card_mul_index
    rw [h3, h45] at this
    omega
  have hi5 : (P5 : Subgroup X).index = 9 := by
    have := (P5 : Subgroup X).card_mul_index
    rw [h5, h45] at this
    omega
  have hn3 := sylow_normal_of_index P3 (by
    intro n hn hmod
    rw [hi3] at hn
    have : n ≤ 5 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> simp_all)
  have hn5 := sylow_normal_of_index P5 (by
    intro n hn hmod
    rw [hi5] at hn
    have : n ≤ 9 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> simp_all)
  have hab3 : ∀ a ∈ (P3 : Subgroup X), ∀ b ∈ (P3 : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P3) (by rw [h3])
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hab5 : ∀ a ∈ (P5 : Subgroup X), ∀ b ∈ (P5 : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have : IsCyclic P5 := isCyclic_of_prime_card h5
    exact congrArg Subtype.val (comm_of_isCyclic (⟨a, ha⟩ : P5) ⟨b, hb⟩)
  exact comm_of_normal_coprime P3 P5 hn3 hn5 hab3 hab5
    (by rw [h3, h5]; norm_num) (by rw [h3, h5, h45]; norm_num)

end Sylow

section Four

variable {G : Type*} [Group G]

@[expose] def fourSub (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  mul_mem' {x y} hx hy := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have h3 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_ofPred_eq, one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, ← hab,
        true_or, or_true]
  one_mem' := Or.inl rfl
  inv_mem' {x} hx := by
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have habi : (a * b)⁻¹ = a * b := by rw [mul_inv_rev, hai, hbi, hab]
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl hai)
    · exact Or.inr (Or.inr (Or.inl hbi))
    · exact Or.inr (Or.inr (Or.inr habi))

theorem mem_fourSub {a b : G} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : G} :
    x ∈ fourSub a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  unfold fourSub
  rfl

theorem isKleinFour_fourSub {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : IsKleinFour (fourSub a b ha hb hab) := by
  classical
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hb])
  refine CFSG.LinearGroups.isKleinFour_of_card_eq_four ?_ ?_
  · let g : Fin 4 → G := ![1, a, b, a * b]
    have hgmem : ∀ i, g i ∈ fourSub a b ha hb hab := by
      intro i
      rw [mem_fourSub]
      fin_cases i <;> simp [g]
    have hginj : Function.Injective g := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp only [g] at h ⊢ <;>
        first
        | rfl
        | (exfalso; simp at h; first
            | exact ha1 h | exact ha1 h.symm | exact hb1 h | exact hb1 h.symm
            | exact hne h | exact hne h.symm | exact hab1 h | exact hab1 h.symm)
    let f : Fin 4 → fourSub a b ha hb hab := fun i => ⟨g i, hgmem i⟩
    have hf : Function.Bijective f := by
      refine ⟨fun i j hij => hginj (congrArg Subtype.val hij), ?_⟩
      rintro ⟨x, hx⟩
      rcases mem_fourSub.mp hx with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    simp only [OneMemClass.coe_one, pow_two, Subgroup.coe_mul]
    rcases mem_fourSub.mp hx with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ha
    · exact hb
    · rw [← mul_assoc, mul_assoc a b a, ← hab, ← mul_assoc, ha, one_mul, hb]

end Four

theorem oddCore_map {X : Type*} [Group X] [Finite X] (α : X ≃* X) {x : X}
    (hx : x ∈ CFSG.oddCore X) : α x ∈ CFSG.oddCore X := by
  have hodd : Odd (Nat.card (CFSG.oddCore X)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := X)
  have hn : ((CFSG.oddCore X).map α.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ α.surjective
  have ho : Odd (Nat.card ((CFSG.oddCore X).map α.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective α.injective]
  have hle : (CFSG.oddCore X).map α.toMonoidHom ≤ CFSG.oddCore X := le_sSup ⟨hn, ho⟩
  exact hle ⟨x, hx, rfl⟩

namespace Sigma

theorem no_order_fifteen : ∀ g : SigmaL2F4, g ^ 15 = 1 → g ^ 3 = 1 ∨ g ^ 5 = 1 :=
  Certificates.certificate17010.1

end Sigma

theorem code_pow (x : Equiv.Perm (Fin 10)) (n : ℕ) :
    A6Facts.code (x ^ n) = cpow (A6Facts.code x) n := by
  induction n with
  | zero => rw [pow_zero, A6Facts.code_one]; rfl
  | succ n ih => rw [pow_succ, A6Facts.code_mul, ih]; rfl

theorem m10_check : ∀ c ∈ A6Facts.Core.pslLit, ∀ r ∈ [A6Facts.code 1,
    A6Facts.code A6Models.tMulFrob],
    cpow (A6Facts.Core.cmul c r) 15 = A6Facts.Core.cid →
      cpow (A6Facts.Core.cmul c r) 3 = A6Facts.Core.cid ∨
        cpow (A6Facts.Core.cmul c r) 5 = A6Facts.Core.cid :=
  Certificates.certificate17010.2.1

theorem m10_pow_fifteen
    {x : Equiv.Perm (Fin 10)} (hx : x ∈ A6Models.m10) (h15 : x ^ 15 = 1) :
    x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  obtain ⟨r, hr, hxr⟩ := (Out21.A6.mem_m10_iff x).1 hx
  have hc : A6Facts.code (x * r⁻¹) ∈ A6Facts.Core.pslLit := (A6Facts.mem_psl29_iff _).1 hxr
  have hr' : A6Facts.code r ∈ [A6Facts.code 1, A6Facts.code A6Models.tMulFrob] := by
    simp only [Out21.A6.m10Reps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  have hcx : A6Facts.Core.cmul (A6Facts.code (x * r⁻¹)) (A6Facts.code r) = A6Facts.code x := by
    rw [← A6Facts.code_mul, inv_mul_cancel_right]
  have h := m10_check _ hc _ hr'
  rw [hcx, ← code_pow, ← code_pow, ← code_pow, h15, A6Facts.code_one] at h
  rcases h rfl with h | h
  · exact Or.inl (A6Facts.code_injective (by rw [h, A6Facts.code_one]))
  · exact Or.inr (A6Facts.code_injective (by rw [h, A6Facts.code_one]))

theorem x5_mem_m10 : x5 ∈ A6Models.m10 :=
  mul_mem (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    (Subgroup.subset_closure (by simp))

theorem x5_pow_five : x5 ^ 5 = 1 :=
  Certificates.certificate17010.2.2.1

theorem x5_ne_one : x5 ≠ 1 :=
  Certificates.certificate17010.2.2.2

end CFSG.Quasithin.RuType
