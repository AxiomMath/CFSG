module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Equiv Equiv.Perm Subgroup

theorem u1_two_part {M : Type*} [Group M] [Finite M] (y : M) :
    ∃ o : ℕ, Odd o ∧ ∃ e : ℕ, (y ^ o) ^ 2 ^ e = 1 := by
  obtain ⟨e, o, ho, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨o, ho, e, ?_⟩
  rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]

theorem u1_isPGroup_closure {B : Type*} [Group B] (S : Set B) (h2 : ∀ x ∈ S, x * x = 1)
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : IsPGroup 2 (Subgroup.closure S) := by
  have hSC : S ⊆ (Subgroup.centralizer S : Set B) := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun h hh => hc h hh x hx
  have hcl : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).mpr hSC
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hx' := Subgroup.closure_le_centralizer_centralizer S hx
    rw [Subgroup.mem_centralizer_iff] at hx'
    exact (hx' y (hcl hy)).symm
  have hsq : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h2 x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hyx : Commute y x := (hcomm x hx y hy).symm
      calc (x * y) * (x * y) = (x * x) * (y * y) := hyx.mul_mul_mul_comm x y
        _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  have hg := hsq (g : B) g.2
  simpa [pow_two] using hg

theorem u1_eq_one_of_odd {N : Type*} [Group N] (R : Subgroup N) (hR : Odd (Nat.card R)) {g : N}
    (hg : g ∈ R) (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hg2
  have hcop : Nat.Coprime (2 ^ k) (Nat.card R) :=
    Nat.Coprime.pow_left k ((Nat.prime_two.coprime_iff_not_dvd).mpr hR.not_two_dvd_nat)
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (Subgroup.orderOf_dvd_natCard R hg)
  rw [Nat.Coprime.gcd_eq_one hcop] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem u1_sylow_lift {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ} [Fact p.Prime]
    (f : A →* B) (E : Subgroup B) (hE : IsPGroup p E) (hEf : E ≤ f.range) :
    ∃ T : Subgroup A, IsPGroup p T ∧ T.map f = E := by
  obtain ⟨g, hg_apply⟩ : ∃ g : E.comap f →* E, ∀ x, ((g x : E) : B) = f x :=
    ⟨(f.comp (E.comap f).subtype).codRestrict E (fun x => Subgroup.mem_comap.mp x.2),
      fun x => rfl⟩
  have hgs : Function.Surjective g := by
    intro e
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hEf e.2)
    have ha' : a ∈ E.comap f := by
      rw [Subgroup.mem_comap, ha]
      exact e.2
    refine ⟨⟨a, ha'⟩, Subtype.ext ?_⟩
    rw [hg_apply]
    exact ha
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p (E.comap f)))
  have htop : IsPGroup p (⊤ : Subgroup E) := by
    intro x
    obtain ⟨k, hk⟩ := hE x.1
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hmap : P.toSubgroup.map g = ⊤ := ((P.mapSurjective hgs).is_maximal' htop le_top).symm
  refine ⟨P.toSubgroup.map (E.comap f).subtype, P.isPGroup'.map (E.comap f).subtype, ?_⟩
  ext b
  constructor
  · intro hb
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp ht
    exact Subgroup.mem_comap.mp y.2
  · intro hb
    have hbtop : (⟨b, hb⟩ : E) ∈ P.toSubgroup.map g := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.mp hbtop
    refine Subgroup.mem_map.mpr
      ⟨(E.comap f).subtype y, Subgroup.mem_map_of_mem (E.comap f).subtype hy, ?_⟩
    have h1 : ((g y : E) : B) = b := congrArg Subtype.val hgy
    rw [hg_apply] at h1
    exact h1

theorem u1a2_comm {T : Type*} [Group T] (z : T) (hz2 : z * z = 1) (hz1 : z ≠ 1) (x y : T)
    (hxx : x * x = z) (hyy : y * y = z) (hxy : (x * y) * (x * y) = z)
    (h : x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z) : y * x = z * (x * y) := by
  rcases h with h | h
  · exfalso
    have hxy' : x * y = y * x := by
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = 1 * (y * x) := by rw [h]
        _ = y * x := one_mul _
    apply hz1
    calc z = (x * y) * (x * y) := hxy.symm
      _ = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hxy']
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = z * z := by rw [hxx, hyy]
      _ = 1 := hz2
  · have h1 : x * y = z * (y * x) := by
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = z * (y * x) := by rw [h]
    calc y * x = z * (z * (y * x)) := by rw [← mul_assoc, hz2, one_mul]
      _ = z * (x * y) := by rw [h1]

theorem u1_alg {T : Type*} [Group T] (z : T) (hz2 : z * z = 1) (hzc : ∀ m : T, m * z = z * m)
    (a b c : T)
    (ha : a * a = 1 ∨ a * a = z) (hb : b * b = 1 ∨ b * b = z) (hc : c * c = 1 ∨ c * c = z)
    (hab : (a * b) * (a * b) = 1 ∨ (a * b) * (a * b) = z)
    (hac : (a * c) * (a * c) = 1 ∨ (a * c) * (a * c) = z)
    (hbc : (b * c) * (b * c) = 1 ∨ (b * c) * (b * c) = z)
    (cab : a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = z)
    (cac : a * c * a⁻¹ * c⁻¹ = 1 ∨ a * c * a⁻¹ * c⁻¹ = z)
    (cbc : b * c * b⁻¹ * c⁻¹ = 1 ∨ b * c * b⁻¹ * c⁻¹ = z) :
    a * a = 1 ∨ b * b = 1 ∨ c * c = 1 ∨ (a * b) * (a * b) = 1 ∨ (a * c) * (a * c) = 1 ∨
      (b * c) * (b * c) = 1 ∨ (a * b * c) * (a * b * c) = 1 := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hA1, hB1, hC1, hAB1, hAC1, hBC1, hABC1⟩ := hne
  have hA : a * a = z := ha.resolve_left hA1
  have hB : b * b = z := hb.resolve_left hB1
  have hC : c * c = z := hc.resolve_left hC1
  have hAB : (a * b) * (a * b) = z := hab.resolve_left hAB1
  have hAC : (a * c) * (a * c) = z := hac.resolve_left hAC1
  have hBC : (b * c) * (b * c) = z := hbc.resolve_left hBC1
  have hz1 : z ≠ 1 := fun h => hA1 (hA.trans h)
  have R2 : b * a = z * (a * b) := u1a2_comm z hz2 hz1 a b hA hB hAB cab
  have R1 : c * a = z * (a * c) := u1a2_comm z hz2 hz1 a c hA hC hAC cac
  have hzl : ∀ m n : T, m * (z * n) = z * (m * n) := by
    intro m n
    rw [← mul_assoc, hzc m, mul_assoc]
  have key : (a * b * c) * (a * b * c) = 1 := by
    calc (a * b * c) * (a * b * c)
        = a * (b * ((c * a) * (b * c))) := by simp only [mul_assoc]
      _ = a * (b * ((z * (a * c)) * (b * c))) := by rw [R1]
      _ = a * (b * (z * ((a * c) * (b * c)))) := by rw [mul_assoc z]
      _ = a * (z * (b * ((a * c) * (b * c)))) := by rw [hzl b]
      _ = z * (a * (b * ((a * c) * (b * c)))) := by rw [hzl a]
      _ = z * (a * ((b * a) * (c * (b * c)))) := by simp only [mul_assoc]
      _ = z * (a * ((z * (a * b)) * (c * (b * c)))) := by rw [R2]
      _ = z * (a * (z * ((a * b) * (c * (b * c))))) := by rw [mul_assoc z]
      _ = z * (z * (a * ((a * b) * (c * (b * c))))) := by rw [hzl a]
      _ = z * (z * ((a * a) * (b * (c * (b * c))))) := by simp only [mul_assoc]
      _ = z * (z * (z * (b * (c * (b * c))))) := by rw [hA]
      _ = z * (z * (z * ((b * c) * (b * c)))) := by simp only [mul_assoc]
      _ = z * (z * (z * z)) := by rw [hBC]
      _ = 1 := by rw [hz2, mul_one, hz2]
  exact hABC1 key

theorem u1a3_sq_mem : ∀ x ∈ ({Equiv.swap (0 : Fin 7) 1, Equiv.swap (2 : Fin 7) 3,
    Equiv.swap (4 : Fin 7) 5} : Set (Equiv.Perm (Fin 7))), x * x = 1 := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> decide

theorem u1a3_comm_mem : ∀ x ∈ ({Equiv.swap (0 : Fin 7) 1, Equiv.swap (2 : Fin 7) 3,
    Equiv.swap (4 : Fin 7) 5} : Set (Equiv.Perm (Fin 7))),
    ∀ y ∈ ({Equiv.swap (0 : Fin 7) 1, Equiv.swap (2 : Fin 7) 3,
    Equiv.swap (4 : Fin 7) 5} : Set (Equiv.Perm (Fin 7))), x * y = y * x := by
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> decide

theorem u1_O {M : Type*} [Group M] [Finite M] (φ : M →* Equiv.Perm (Fin 7)) (z : M)
    (hz2 : z * z = 1) (hzc : ∀ m : M, m * z = z * m)
    (hker : ∀ g : M, (∃ k : ℕ, g ^ 2 ^ k = 1) → φ g = 1 → g = 1 ∨ g = z)
    (ha : Equiv.swap (0 : Fin 7) 1 ∈ φ.range) (hb : Equiv.swap (2 : Fin 7) 3 ∈ φ.range)
    (hc : Equiv.swap (4 : Fin 7) 5 ∈ φ.range) :
    ∃ u : M, u * u = 1 ∧ φ u ≠ 1 := by
  have hsub : ({Equiv.swap (0 : Fin 7) 1, Equiv.swap (2 : Fin 7) 3,
      Equiv.swap (4 : Fin 7) 5} : Set (Equiv.Perm (Fin 7))) ⊆
      (φ.range : Set (Equiv.Perm (Fin 7))) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  obtain ⟨T, hT, hTE⟩ := u1_sylow_lift φ
    (Subgroup.closure ({Equiv.swap (0 : Fin 7) 1, Equiv.swap (2 : Fin 7) 3,
      Equiv.swap (4 : Fin 7) 5} : Set (Equiv.Perm (Fin 7))))
    (u1_isPGroup_closure _ u1a3_sq_mem u1a3_comm_mem) ((Subgroup.closure_le _).mpr hsub)
  have hmem : ∀ x ∈ ({Equiv.swap (0 : Fin 7) 1, Equiv.swap (2 : Fin 7) 3,
      Equiv.swap (4 : Fin 7) 5} : Set (Equiv.Perm (Fin 7))), ∃ t ∈ T, φ t = x := by
    intro x hx
    have hxE : x ∈ T.map φ := by
      rw [hTE]
      exact Subgroup.subset_closure hx
    exact Subgroup.mem_map.mp hxE
  obtain ⟨a, haT, hfa⟩ := hmem (Equiv.swap (0 : Fin 7) 1) (by simp)
  obtain ⟨b, hbT, hfb⟩ := hmem (Equiv.swap (2 : Fin 7) 3) (by simp)
  obtain ⟨c, hcT, hfc⟩ := hmem (Equiv.swap (4 : Fin 7) 5) (by simp)
  have h2T : ∀ g ∈ T, ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hT ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hT1 : ∀ g ∈ T, φ g = 1 → g = 1 ∨ g = z :=
    fun g hg hφ => hker g (h2T g hg) hφ
  have hsqa : a * a ∈ T := T.mul_mem haT haT
  have hsqb : b * b ∈ T := T.mul_mem hbT hbT
  have hsqc : c * c ∈ T := T.mul_mem hcT hcT
  have hpab : (a * b) * (a * b) ∈ T := T.mul_mem (T.mul_mem haT hbT) (T.mul_mem haT hbT)
  have hpac : (a * c) * (a * c) ∈ T := T.mul_mem (T.mul_mem haT hcT) (T.mul_mem haT hcT)
  have hpbc : (b * c) * (b * c) ∈ T := T.mul_mem (T.mul_mem hbT hcT) (T.mul_mem hbT hcT)
  have hkab : a * b * a⁻¹ * b⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem haT hbT) (T.inv_mem haT)) (T.inv_mem hbT)
  have hkac : a * c * a⁻¹ * c⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem haT hcT) (T.inv_mem haT)) (T.inv_mem hcT)
  have hkbc : b * c * b⁻¹ * c⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem hbT hcT) (T.inv_mem hbT)) (T.inv_mem hcT)
  have hφsqa : φ (a * a) = 1 := by
    simp only [map_mul, hfa]
    decide
  have hφsqb : φ (b * b) = 1 := by
    simp only [map_mul, hfb]
    decide
  have hφsqc : φ (c * c) = 1 := by
    simp only [map_mul, hfc]
    decide
  have hφpab : φ ((a * b) * (a * b)) = 1 := by
    simp only [map_mul, hfa, hfb]
    decide
  have hφpac : φ ((a * c) * (a * c)) = 1 := by
    simp only [map_mul, hfa, hfc]
    decide
  have hφpbc : φ ((b * c) * (b * c)) = 1 := by
    simp only [map_mul, hfb, hfc]
    decide
  have hφkab : φ (a * b * a⁻¹ * b⁻¹) = 1 := by
    simp only [map_mul, map_inv, hfa, hfb]
    decide
  have hφkac : φ (a * c * a⁻¹ * c⁻¹) = 1 := by
    simp only [map_mul, map_inv, hfa, hfc]
    decide
  have hφkbc : φ (b * c * b⁻¹ * c⁻¹) = 1 := by
    simp only [map_mul, map_inv, hfb, hfc]
    decide
  rcases u1_alg z hz2 hzc a b c (hT1 _ hsqa hφsqa) (hT1 _ hsqb hφsqb) (hT1 _ hsqc hφsqc)
    (hT1 _ hpab hφpab) (hT1 _ hpac hφpac) (hT1 _ hpbc hφpbc)
    (hT1 _ hkab hφkab) (hT1 _ hkac hφkac) (hT1 _ hkbc hφkbc) with
    h | h | h | h | h | h | h
  · exact ⟨a, h, by rw [hfa]; decide⟩
  · exact ⟨b, h, by rw [hfb]; decide⟩
  · exact ⟨c, h, by rw [hfc]; decide⟩
  · exact ⟨a * b, h, by simp only [map_mul, hfa, hfb]; decide⟩
  · exact ⟨a * c, h, by simp only [map_mul, hfa, hfc]; decide⟩
  · exact ⟨b * c, h, by simp only [map_mul, hfb, hfc]; decide⟩
  · exact ⟨a * b * c, h, by simp only [map_mul, hfa, hfb, hfc]; decide⟩

theorem u1a4_pow_two_pow_eq_one {N : Type*} [Group N] (T : Subgroup N) (hT : IsPGroup 2 T)
    {g : N} (hg : g ∈ T) : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hT ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem u1a4_eq_one_of_mem {N : Type*} [Group N] (R T : Subgroup N) (hR : Odd (Nat.card R))
    (hT : IsPGroup 2 T) {g : N} (hgT : g ∈ T) (hgR : g ∈ R) : g = 1 :=
  u1_eq_one_of_odd R hR hgR (u1a4_pow_two_pow_eq_one T hT hgT)

theorem u1_lift {N : Type*} [Group N] [Finite N] (R : Subgroup N) [R.Normal]
    (hR : Odd (Nat.card R)) {a b : N ⧸ R} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    ∃ x y : N, x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧ (x : N ⧸ R) = a ∧ (y : N ⧸ R) = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ∀ z ∈ ({a, b} : Set (N ⧸ R)), z * z = 1 := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · rw [h]; exact ha
    · rw [h]; exact hb
  have hc : ∀ z ∈ ({a, b} : Set (N ⧸ R)), ∀ w ∈ ({a, b} : Set (N ⧸ R)), z * w = w * z := by
    intro z hz w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hw
    rcases hz with h | h <;> rcases hw with h' | h'
    · rw [h, h']
    · rw [h, h']; exact hab
    · rw [h, h']; exact hab.symm
    · rw [h, h']
  have hE : IsPGroup 2 (Subgroup.closure ({a, b} : Set (N ⧸ R))) :=
    u1_isPGroup_closure ({a, b} : Set (N ⧸ R)) h2 hc
  have hEf : Subgroup.closure ({a, b} : Set (N ⧸ R)) ≤ (QuotientGroup.mk' R).range := by
    intro g _
    exact MonoidHom.mem_range.mpr (QuotientGroup.mk'_surjective R g)
  obtain ⟨T, hT, hTE⟩ := u1_sylow_lift (QuotientGroup.mk' R) _ hE hEf
  have ha_mem : a ∈ T.map (QuotientGroup.mk' R) := by
    rw [hTE]; exact Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ T.map (QuotientGroup.mk' R) := by
    rw [hTE]; exact Subgroup.subset_closure (by simp)
  obtain ⟨x, hxT, hxa⟩ := Subgroup.mem_map.mp ha_mem
  obtain ⟨y, hyT, hyb⟩ := Subgroup.mem_map.mp hb_mem
  have hxx : x * x = 1 := by
    have himg : QuotientGroup.mk' R (x * x) = 1 := by
      rw [map_mul, hxa]; exact ha
    have hmem : x * x ∈ R := by
      rw [QuotientGroup.mk'_apply] at himg
      exact (QuotientGroup.eq_one_iff _).mp himg
    exact u1a4_eq_one_of_mem R T hR hT (T.mul_mem hxT hxT) hmem
  have hyy : y * y = 1 := by
    have himg : QuotientGroup.mk' R (y * y) = 1 := by
      rw [map_mul, hyb]; exact hb
    have hmem : y * y ∈ R := by
      rw [QuotientGroup.mk'_apply] at himg
      exact (QuotientGroup.eq_one_iff _).mp himg
    exact u1a4_eq_one_of_mem R T hR hT (T.mul_mem hyT hyT) hmem
  have hcomm : x * y * x⁻¹ * y⁻¹ = 1 := by
    have himg : QuotientGroup.mk' R (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxa, hyb, hab]
      simp
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ R := by
      rw [QuotientGroup.mk'_apply] at himg
      exact (QuotientGroup.eq_one_iff _).mp himg
    have hTmem : x * y * x⁻¹ * y⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem (T.mul_mem hxT hyT) (T.inv_mem hxT)) (T.inv_mem hyT)
    exact u1a4_eq_one_of_mem R T hR hT hTmem hmem
  refine ⟨x, y, hxx, hyy, ?_, hxa, hyb⟩
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hcomm, one_mul]

end CFSG.RankThree.PartTwo.Sec13.F135Last
