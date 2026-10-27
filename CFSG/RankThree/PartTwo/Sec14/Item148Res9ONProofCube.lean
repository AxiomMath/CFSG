module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res9ON

theorem mul_pow_three_of_central' {X : Type*} [Group X] {x y c : X}
    (hc : c ∈ Subgroup.center X) (hyx : y * x = c * (x * y)) (hc3 : c ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hcz : ∀ g : X, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hc g
  have hmove : ∀ a b : X, a * (c * b) = c * (a * b) := fun a b => by
    rw [← mul_assoc, hcz a, mul_assoc]
  have key : (x * y) ^ 3 = c * (c * (c * (x * (x * (x * (y * (y * y))))))) := by
    calc (x * y) ^ 3 = x * ((y * x) * ((y * x) * y)) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = x * ((c * (x * y)) * ((c * (x * y)) * y)) := by rw [hyx]
      _ = c * (c * (x * (x * ((y * x) * (y * y))))) := by
          simp only [mul_assoc]
          rw [hmove x, hmove y, hmove x, hmove x]
      _ = c * (c * (x * (x * ((c * (x * y)) * (y * y))))) := by rw [hyx]
      _ = c * (c * (c * (x * (x * (x * (y * (y * y))))))) := by
          simp only [mul_assoc]
          rw [hmove x, hmove x]
  rw [key]
  have h3 : c * (c * (c * (x * (x * (x * (y * (y * y))))))) = c ^ 3 * (x ^ 3 * y ^ 3) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h3, hc3, one_mul]

theorem mul_pow_three_of_central {X : Type*} [Group X] {x y : X}
    (hc : y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center X) (hc3 : (y * x * y⁻¹ * x⁻¹) ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 :=
  mul_pow_three_of_central' hc (by group) hc3

theorem card_eq_card_ker_mul_card_range {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

theorem isMulCommutative_of_card_dvd_nine {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H ∣ 3 ^ 2) : IsMulCommutative H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hH
  interval_cases k
  · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp (by simpa using hcard)).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : IsCyclic H := isCyclic_of_prime_card (p := 3) (by simpa using hcard)
    exact IsCyclic.isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard

theorem closure_pair_eq {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP27 : Nat.card P = 27) {g₁ g₂ : X} (h₁ : g₁ ∈ P) (h₂ : g₂ ∈ P) (h12 : g₁ * g₂ ≠ g₂ * g₁) :
    Subgroup.closure {g₁, g₂} = P := by
  set H := Subgroup.closure ({g₁, g₂} : Set X) with hHdef
  have hHP : H ≤ P := (Subgroup.closure_le P).mpr (by
    rintro x (rfl | rfl)
    · exact h₁
    · exact h₂)
  have hdvd : Nat.card H ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hP27]
    exact Subgroup.card_dvd_of_le hHP
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk3 : k = 3 := by
    by_contra hk3
    have hk2 : k ≤ 2 := by omega
    have hc : IsMulCommutative H := isMulCommutative_of_card_dvd_nine (by
      rw [hcard]
      exact pow_dvd_pow 3 hk2)
    apply h12
    have h1 : g₁ ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
    have h2 : g₂ ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact congrArg Subtype.val (hc.is_comm.comm ⟨g₁, h1⟩ ⟨g₂, h2⟩)
  subst hk3
  exact Subgroup.eq_of_le_of_card_ge hHP (by rw [hcard, hP27]; norm_num)

theorem card_center_eq_three {P : Type*} [Group P] [Finite P] (hP27 : Nat.card P = 27)
    (hPna : ¬ IsMulCommutative P) {Z : Subgroup P} (hZ : Z ≤ Subgroup.center P)
    (hZ3 : Nat.card Z = 3) : Nat.card (Subgroup.center P) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card (Subgroup.center P) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hP27]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h3 : 3 ∣ Nat.card (Subgroup.center P) := hZ3 ▸ Subgroup.card_dvd_of_le hZ
  have hidx := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
  interval_cases k
  · rw [hcard] at h3
    norm_num at h3
  · simpa using hcard
  · exfalso
    rw [hcard, hP27] at hidx
    have hq : Nat.card (P ⧸ Subgroup.center P) = 3 := by omega
    have : IsCyclic (P ⧸ Subgroup.center P) := isCyclic_of_prime_card (p := 3) hq
    exact hPna (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center P)) (by rw [QuotientGroup.ker_mk']))
  · exfalso
    apply hPna
    have htop : Subgroup.center P = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [hcard, hP27]
      norm_num
    exact ⟨⟨fun a b => Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a⟩⟩

@[expose] def commHom {X : Type*} [Group X] {Z S : Subgroup X} (hZc : Z ≤ Subgroup.center X)
    (g : X) (hcomm : ∀ s ∈ S, s * g * s⁻¹ * g⁻¹ ∈ Z) : ↥S →* ↥Z where
  toFun s := ⟨s * g * s⁻¹ * g⁻¹, hcomm s s.2⟩
  map_one' := by ext; simp
  map_mul' s t := by
    ext
    have hw : (t : X) * g * (t : X)⁻¹ * g⁻¹ ∈ Subgroup.center X := hZc (hcomm t t.2)
    have hsw : (s : X) * ((t : X) * g * (t : X)⁻¹ * g⁻¹) =
        ((t : X) * g * (t : X)⁻¹ * g⁻¹) * s := Subgroup.mem_center_iff.mp hw (s : X)
    show (s : X) * t * g * ((s : X) * t)⁻¹ * g⁻¹ =
      ((s : X) * g * (s : X)⁻¹ * g⁻¹) * ((t : X) * g * (t : X)⁻¹ * g⁻¹)
    calc (s : X) * t * g * ((s : X) * t)⁻¹ * g⁻¹ =
        (s : X) * ((t : X) * g * (t : X)⁻¹ * g⁻¹) * g * (s : X)⁻¹ * g⁻¹ := by group
      _ = ((t : X) * g * (t : X)⁻¹ * g⁻¹) * s * g * (s : X)⁻¹ * g⁻¹ := by rw [hsw]
      _ = ((t : X) * g * (t : X)⁻¹ * g⁻¹) * ((s : X) * g * (s : X)⁻¹ * g⁻¹) := by group
      _ = ((s : X) * g * (s : X)⁻¹ * g⁻¹) * ((t : X) * g * (t : X)⁻¹ * g⁻¹) :=
        (Subgroup.mem_center_iff.mp hw _).symm

theorem mem_ker_commHom {X : Type*} [Group X] {Z S : Subgroup X} (hZc : Z ≤ Subgroup.center X)
    {g : X} (hcomm : ∀ s ∈ S, s * g * s⁻¹ * g⁻¹ ∈ Z) (s : ↥S) :
    s ∈ (commHom hZc g hcomm).ker ↔ (s : X) * g = g * s := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (s : X) * g * (s : X)⁻¹ * g⁻¹ = 1 := congrArg Subtype.val h
    calc (s : X) * g = ((s : X) * g * (s : X)⁻¹ * g⁻¹) * g * s := by group
      _ = g * s := by rw [h1, one_mul]
  · intro h
    apply Subtype.ext
    show (s : X) * g * (s : X)⁻¹ * g⁻¹ = 1
    rw [h]
    group

theorem exists_pow_three_eq_one_centralizes {X : Type*} [Group X] [Finite X]
    {Z P S : Subgroup X} (hZc : Z ≤ Subgroup.center X) (hZ3 : Nat.card Z = 3) (hZP : Z ≤ P)
    (hP27 : Nat.card P = 27) {g₁ g₂ : X} (h₁ : g₁ ∈ P) (h₂ : g₂ ∈ P) (h12 : g₁ * g₂ ≠ g₂ * g₁)
    (hPS : P ≤ S) (hS : Nat.card S = 243)
    (hScomm : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Z) (hS3 : ∀ s ∈ S, s ^ 3 ∈ Z) :
    ∃ r ∈ S, r ^ 3 = 1 ∧ r ∉ P ∧ ∀ g ∈ P, g * r = r * g := by
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  set ρ₁ := commHom hZc g₁ (fun s hs => hScomm s hs g₁ (hPS h₁)) with hρ₁
  set ρ₂ := commHom hZc g₂ (fun s hs => hScomm s hs g₂ (hPS h₂)) with hρ₂
  set χ := ρ₁.prod ρ₂ with hχ
  have hχker : ∀ s : ↥S, s ∈ χ.ker ↔ (s : X) * g₁ = g₁ * s ∧ (s : X) * g₂ = g₂ * s := by
    intro s
    rw [MonoidHom.mem_ker, hχ, MonoidHom.prod_apply, Prod.mk_eq_one, ← MonoidHom.mem_ker,
      ← MonoidHom.mem_ker, mem_ker_commHom, mem_ker_commHom]
  have hχcard : 27 ≤ Nat.card χ.ker := by
    have h1 := card_eq_card_ker_mul_card_range χ
    have h2 : Nat.card χ.range ≤ 9 := by
      calc Nat.card χ.range ≤ Nat.card (↥Z × ↥Z) := Subgroup.card_le_card_group _
        _ = 9 := by rw [Nat.card_prod, hZ3]
    rw [hS] at h1
    have h3 : 243 ≤ Nat.card χ.ker * 9 := h1 ▸ Nat.mul_le_mul_left _ h2
    omega
  have hcube : ∀ c d : ↥χ.ker, (((c * d : ↥χ.ker) : ↥S) : X) ^ 3 =
      (((c : ↥S) : X)) ^ 3 * (((d : ↥S) : X)) ^ 3 := by
    intro c d
    have hdc := hScomm _ (d : ↥S).2 _ (c : ↥S).2
    exact mul_pow_three_of_central (hZc hdc) (hz3 _ hdc)
  let ω : ↥χ.ker →* ↥Z :=
    { toFun := fun c => ⟨((c : ↥S) : X) ^ 3, hS3 _ (c : ↥S).2⟩
      map_one' := by ext; simp
      map_mul' := fun c d => Subtype.ext (hcube c d) }
  have hωcard : 9 ≤ Nat.card ω.ker := by
    have h1 := card_eq_card_ker_mul_card_range ω
    have h2 : Nat.card ω.range ≤ 3 := hZ3 ▸ Subgroup.card_le_card_group _
    have h3 : Nat.card χ.ker ≤ Nat.card ω.ker * 3 := h1 ▸ Nat.mul_le_mul_left _ h2
    omega
  have hcl := closure_pair_eq hP27 h₁ h₂ h12
  have hcentP : ∀ r : X, r * g₁ = g₁ * r → r * g₂ = g₂ * r → ∀ g ∈ P, g * r = r * g := by
    intro r hr₁ hr₂ g hg
    have hrC : r ∈ Subgroup.centralizer (Subgroup.closure ({g₁, g₂} : Set X) : Set X) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      rintro h (rfl | rfl)
      · exact hr₁.symm
      · exact hr₂.symm
    rw [hcl] at hrC
    exact Subgroup.mem_centralizer_iff.mp hrC g hg
  have hPna : ¬ IsMulCommutative ↥P := fun hc =>
    h12 (congrArg Subtype.val (hc.is_comm.comm ⟨g₁, h₁⟩ ⟨g₂, h₂⟩))
  have hZPc : Z.subgroupOf P ≤ Subgroup.center ↥P := fun z hz =>
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext ((Subgroup.mem_center_iff.mp (hZc hz) y))
  have hZP3 : Nat.card (Z.subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ3]
  have hcenter := card_center_eq_three (P := ↥P) hP27 hPna hZPc hZP3
  by_contra hno
  push Not at hno
  have hmem : ∀ c : ↥ω.ker, (((c : ↥χ.ker) : ↥S) : X) ∈ P ∧
      ∀ g ∈ P, g * (((c : ↥χ.ker) : ↥S) : X) = (((c : ↥χ.ker) : ↥S) : X) * g := by
    intro c
    have hr3 : (((c : ↥χ.ker) : ↥S) : X) ^ 3 = 1 := congrArg Subtype.val c.2
    obtain ⟨hr₁, hr₂⟩ := (hχker _).mp (c : ↥χ.ker).2
    have hc := hcentP _ hr₁ hr₂
    refine ⟨?_, hc⟩
    by_contra hnP
    obtain ⟨g, hg, hne⟩ := hno _ ((c : ↥χ.ker) : ↥S).2 hr3 hnP
    exact hne (hc g hg)
  let ι : ↥ω.ker → ↥(Subgroup.center ↥P) := fun c =>
    ⟨⟨_, (hmem c).1⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ((hmem c).2 y y.2)⟩
  have hinj : Function.Injective ι := by
    intro c d h
    have h1 : (((c : ↥χ.ker) : ↥S) : X) = (((d : ↥χ.ker) : ↥S) : X) :=
      congrArg (fun w : ↥(Subgroup.center ↥P) => ((w : ↥P) : X)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  have := Nat.card_le_card_of_injective ι hinj
  rw [hcenter] at this
  omega

end CFSG.RankThree.PartTwo.Sec14.Res9ON
