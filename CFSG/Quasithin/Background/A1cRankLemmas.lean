module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace A1c

variable {G : Type*} [Group G]

theorem exists_isElemAbelian_card_sq [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B : Subgroup G} (hB : IsPGroup p B) (hnc : ¬ IsCyclic B) :
    ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact (IsPGroup p B) := ⟨hB⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hS : IsElemAbelian p S :=
    ⟨hSel.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  refine ⟨S.map B.subtype, Subgroup.map_subtype_le S, CFSG.SectionRank.isElemAbelian_map hS _, ?_⟩
  rw [Subgroup.card_map_of_injective B.subtype_injective, hScard]

theorem le_total_of_isCyclic_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {C U V : Subgroup G}
    [IsCyclic C] (hC : IsPGroup p C) (hU : U ≤ C) (hV : V ≤ C) : U ≤ V ∨ V ≤ U := by
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).1 (hC.to_le hU)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hC.to_le hV)
  have key : ∀ {U V : Subgroup G}, U ≤ C → V ≤ C → Nat.card U ∣ Nat.card V → U ≤ V := by
    intro U V hU hV hd
    have hcU : Nat.card (U.subgroupOf C) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
    have hcV : Nat.card (V.subgroupOf C) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv
    have h1 : U.subgroupOf C ≤ V.subgroupOf C :=
      (IsCyclic.subgroup_le_iff_card_dvd).2 (by rw [hcU, hcV]; exact hd)
    intro x hx
    have hxC : x ∈ C := hU hx
    have : (⟨x, hxC⟩ : C) ∈ U.subgroupOf C := Subgroup.mem_subgroupOf.2 hx
    exact Subgroup.mem_subgroupOf.1 (h1 this)
  rcases le_total i j with h | h
  · exact Or.inl (key hU hV (by rw [hi, hj]; exact pow_dvd_pow p h))
  · exact Or.inr (key hV hU (by rw [hi, hj]; exact pow_dvd_pow p h))

theorem fixedPointSubgroup_le_of_le {A P : Type*} [Group A] [Group P] [MulDistribMulAction A P]
    {B B' : Subgroup A} (h : B ≤ B') :
    CFSG.fixedPointSubgroup B' P ≤ CFSG.fixedPointSubgroup B P := by
  intro x hx b
  exact hx ⟨b, h b.2⟩

theorem exists_not_isCyclic_fixedPoints {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    {A : Type*} [Group A] [Finite A] [CFSG.IsElementaryAbelian 2 A] [MulDistribMulAction A P]
    (hcard : 8 ≤ Nat.card A) (hfaith : ∀ a : A, (∀ x : P, a • x = x) → a = 1) :
    ∃ a : A, a ≠ 1 ∧ ¬ IsCyclic ↥(CFSG.fixedPointSubgroup (Subgroup.zpowers a) P) := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := CFSG.IsElementaryAbelian.isPGroup 2 A
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 this).symm
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := P) hodd
  obtain ⟨B₁, hB₁⟩ := CFSG.SolvableHall.exists_index_eq_prime hA2
  let ι := {B : Subgroup A // B.index = 2}
  let F : ι → Subgroup P := fun B => CFSG.fixedPointSubgroup B.1 P
  have hι : Nonempty ι := ⟨⟨B₁, hB₁⟩⟩
  have hcomp : ∀ i j : ι, F i ≤ F j ∨ F j ≤ F i := by
    intro i j
    have h1 : 2 ≤ Nat.card ↥(i.1 ⊓ j.1) := by
      have h2 := Subgroup.card_mul_index (i.1 ⊓ j.1)
      have h3 : (i.1 ⊓ j.1).index ≤ 4 := by
        have := Subgroup.index_inf_le (H := i.1) (K := j.1)
        rw [i.2, j.2] at this
        omega
      by_contra hlt
      push Not at hlt
      have : Nat.card ↥(i.1 ⊓ j.1) * (i.1 ⊓ j.1).index ≤ 1 * 4 :=
        Nat.mul_le_mul (by omega) h3
      omega
    have : Nontrivial ↥(i.1 ⊓ j.1) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : ↥(i.1 ⊓ j.1))
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hzi : Subgroup.zpowers a ≤ i.1 := Subgroup.zpowers_le.2 ha.1
    have hzj : Subgroup.zpowers a ≤ j.1 := Subgroup.zpowers_le.2 ha.2
    have hC : IsCyclic ↥(CFSG.fixedPointSubgroup (Subgroup.zpowers a) P) := hcon a ha1'
    exact le_total_of_isCyclic_isPGroup (p := p) (hP.to_subgroup _)
      (fixedPointSubgroup_le_of_le hzi) (fixedPointSubgroup_le_of_le hzj)
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i : ι => Nat.card (F i))
  have hmax : ∀ i, F i ≤ F i₀ := by
    intro i
    rcases hcomp i i₀ with h | h
    · exact h
    · exact (Subgroup.eq_of_le_of_card_ge h (hi₀ i)).symm ▸ le_rfl
  have htop : F i₀ = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup₂_le fun B hB => ?_
    exact hmax ⟨B, hB⟩
  have hall : ∀ b : i₀.1, ∀ x : P, b • x = x := by
    intro b x
    have : x ∈ F i₀ := htop ▸ Subgroup.mem_top x
    exact this b
  have hB0 : i₀.1 = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    exact (Subgroup.mem_bot).2 (hfaith b (fun x => hall ⟨b, hb⟩ x))
  have h2 := i₀.2
  rw [hB0, Subgroup.index_bot] at h2
  omega

section Lift

variable {Q : Type*} [Group Q] {p : ℕ} [Fact p.Prime]

theorem exists_involution_lift {φ : G →* Q} (hφ : Function.Surjective φ)
    (hker : IsPGroup p φ.ker) (hp2 : p ≠ 2) {q : Q} (hq : orderOf q = 2) :
    ∃ t : G, orderOf t = 2 ∧ φ t = q := by
  obtain ⟨t₀, ht₀⟩ := hφ q
  have hq2 : q ^ 2 = 1 := hq ▸ pow_orderOf_eq_one q
  have hmem : t₀ ^ 2 ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, ht₀, hq2]
  obtain ⟨m, hm⟩ := hker ⟨t₀ ^ 2, hmem⟩
  have hm' : (t₀ ^ 2) ^ p ^ m = 1 := congrArg Subtype.val hm
  have hodd : Odd (p ^ m) := Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp2)
  obtain ⟨k, hk⟩ := hodd
  have ht2 : (t₀ ^ p ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hm']
  have hφt : φ (t₀ ^ p ^ m) = q := by
    rw [map_pow, ht₀, hk, pow_succ, pow_mul, hq2, one_pow, one_mul]
  have hne : t₀ ^ p ^ m ≠ 1 := by
    intro h
    rw [h, map_one] at hφt
    have : q = 1 := hφt.symm
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)
  exact ⟨t₀ ^ p ^ m, orderOf_eq_prime ht2 hne, hφt⟩

theorem exists_lift_fixed [Finite G] {φ : G →* Q} (hker : IsPGroup p φ.ker) (hp2 : p ≠ 2)
    {t : G} (ht : t ^ 2 = 1) {x : G} (hx : φ t * φ x = φ x * φ t) :
    ∃ w : G, φ w = φ x ∧ t * w = w * t := by
  classical
  let S := {w : G // φ w = φ x}
  have ht' : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ht]
  have hmem : ∀ w : G, φ w = φ x → φ (t * w * t⁻¹) = φ x := by
    intro w hw
    rw [map_mul, map_mul, map_inv, hw, hx, mul_assoc, mul_inv_cancel, mul_one]
  let σ : Equiv.Perm S :=
    { toFun := fun w => ⟨t * w.1 * t⁻¹, hmem w.1 w.2⟩
      invFun := fun w => ⟨t * w.1 * t⁻¹, hmem w.1 w.2⟩
      left_inv := fun w => Subtype.ext (by
        show t * (t * w.1 * t⁻¹) * t⁻¹ = w.1
        rw [ht']
        calc t * (t * w.1 * t) * t = (t * t) * w.1 * (t * t) := by group
          _ = w.1 := by rw [← sq, ht]; simp)
      right_inv := fun w => Subtype.ext (by
        show t * (t * w.1 * t⁻¹) * t⁻¹ = w.1
        rw [ht']
        calc t * (t * w.1 * t) * t = (t * t) * w.1 * (t * t) := by group
          _ = w.1 := by rw [← sq, ht]; simp) }
  have hσ : σ ^ 2 = 1 := by
    ext w
    show t * (t * w.1 * t⁻¹) * t⁻¹ = w.1
    rw [ht']
    calc t * (t * w.1 * t) * t = (t * t) * w.1 * (t * t) := by group
      _ = w.1 := by rw [← sq, ht]; simp
  have : Fintype S := Fintype.ofFinite S
  have hcard : Nat.card S = Nat.card φ.ker := by
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective (fun k : φ.ker => (⟨x * k.1, ?_⟩ : S))
      ⟨?_, ?_⟩))
    · rw [map_mul, MonoidHom.mem_ker.1 k.2, mul_one]
    · intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      exact mul_left_cancel this
    · intro w
      refine ⟨⟨x⁻¹ * w.1, ?_⟩, Subtype.ext (by simp)⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, w.2, inv_mul_cancel]
  have hodd : Odd (Fintype.card S) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hker
    rw [hk]
    exact Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hsupp : σ.support ≠ Finset.univ := by
    intro h
    have h2 := Equiv.Perm.two_dvd_card_support hσ
    rw [h, Finset.card_univ] at h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  obtain ⟨w, hw⟩ : ∃ w : S, w ∉ σ.support := by
    by_contra hcon
    push Not at hcon
    exact hsupp (Finset.eq_univ_iff_forall.2 hcon)
  rw [Equiv.Perm.notMem_support] at hw
  refine ⟨w.1, w.2, ?_⟩
  have h1 : t * w.1 * t⁻¹ = w.1 := congrArg Subtype.val hw
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

end Lift

end A1c

end CFSG.Quasithin
