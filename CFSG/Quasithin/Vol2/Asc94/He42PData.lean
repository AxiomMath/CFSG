module

public import CFSG.Quasithin.Vol2.Asc94.He42PDef
public import CFSG.Quasithin.Vol2.Asc94.He42FinA
public import CFSG.Quasithin.Vol2.Asc94.He42FinB
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN1

public section

namespace CFSG.Quasithin.A94.He42PD

open Equiv Subgroup

variable {Δ : Type*} [Group Δ]

private lemma he42pd_trans (i : Fin 5) : ∃ σ ∈ alternatingGroup (Fin 5), σ 0 = i := by
  have h : ∀ i : Fin 5, ∃ σ : Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ 0 = i := by
    decide +kernel
  obtain ⟨σ, hσ, hσ0⟩ := h i
  exact ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ, hσ0⟩

private lemma he42pd_fixed_of_cube {α : Type*} [Finite α] (T : α → α) (hinj : Function.Injective T)
    (h3 : ∀ x, T (T (T x)) = x) (hcard : ¬ 3 ∣ Nat.card α) : ∃ x, T x = x := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let e : Equiv.Perm α := Equiv.ofBijective T ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have he : ∀ x, e x = T x := fun x => rfl
  have he3 : e ^ (3 ^ 1) = 1 := by
    ext x
    show (e ^ 3) x = x
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, he]
    exact h3 x
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard) he3
  exact ⟨x, (he x).symm.trans hx⟩

namespace PData

variable {L K A J : Subgroup Δ} {ψ : ↥L →* Perm (Fin 5)} (hP : PData L K A J ψ)

include hP

theorem he42pd_ker_iff (k : ↥L) : ψ k = 1 ↔ (k : Δ) ∈ A := by
  rw [← MonoidHom.mem_ker, hP.ker, Subgroup.mem_subgroupOf]

theorem he42pd_fix_iff (l l' : ↥L) : ψ l 0 = ψ l' 0 ↔ (l : Δ)⁻¹ * (l' : Δ) ∈ K := by
  have h1 : ((l⁻¹ * l' : ↥L) : Δ) = (l : Δ)⁻¹ * (l' : Δ) := by simp
  rw [← h1, ← hP.stab (l⁻¹ * l'), map_mul, map_inv, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_eq_iff_eq]
  exact eq_comm

theorem he42pd_orderOf {Y : ↥L} {y₀ : Δ} (hY : (Y : Δ) = y₀) (hy₀A : y₀ ∉ A)
    (hy₀3 : orderOf y₀ = 3) : orderOf (ψ Y) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hy3 : y₀ ^ 3 = 1 := by rw [← hy₀3]; exact pow_orderOf_eq_one y₀
  have hY3 : Y ^ 3 = 1 := Subtype.ext (by simp [hY, hy3])
  have h3 : ψ Y ^ 3 = 1 := by rw [← map_pow, hY3, map_one]
  have h1 : ψ Y ≠ 1 := fun h => hy₀A (by rw [← hY]; exact (he42pd_ker_iff hP Y).mp h)
  exact orderOf_eq_prime h3 h1

theorem comm_of_klein {y : Δ} (hyL : y ∈ normalizer (L : Set Δ)) (hyK : y ∈ normalizer (K : Set Δ))
    (hy3 : y ^ 3 = 1) (hyJ : ∀ j ∈ J, y * j * y⁻¹ * j⁻¹ ∈ A) :
    ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ A := by
  have hLc : ∀ x : Δ, x ∈ L → y * x * y⁻¹ ∈ L := fun x hx => (mem_normalizer_iff.mp hyL x).mp hx
  have hKc : ∀ x : Δ, x ∈ K ↔ y * x * y⁻¹ ∈ K := fun x => mem_normalizer_iff.mp hyK x
  obtain ⟨cL, hcL⟩ : ∃ cL : ↥L → ↥L, ∀ k : ↥L, (cL k : Δ) = y * (k : Δ) * y⁻¹ :=
    ⟨fun k => ⟨y * k * y⁻¹, hLc k k.2⟩, fun k => rfl⟩
  have hcL_mul : ∀ a b : ↥L, cL (a * b) = cL a * cL b := by
    intro a b
    apply Subtype.ext
    simp only [hcL, Subgroup.coe_mul]
    group
  have hcL_one : cL 1 = 1 := by
    apply Subtype.ext
    rw [hcL]
    simp
  have hy3' : y * y * y = 1 := (pow_three' y).symm.trans hy3
  have hcL_cube : ∀ k : ↥L, cL (cL (cL k)) = k := by
    intro k
    apply Subtype.ext
    simp only [hcL]
    have e : y * (y * (y * (k : Δ) * y⁻¹) * y⁻¹) * y⁻¹ =
        (y * y * y) * (k : Δ) * (y * y * y)⁻¹ := by
      group
    rw [e, hy3']
    simp
  have hcK : ∀ k k' : ↥L, (k : Δ)⁻¹ * (k' : Δ) ∈ K ↔ (cL k : Δ)⁻¹ * (cL k' : Δ) ∈ K := by
    intro k k'
    rw [hcL, hcL]
    have e : (y * (k : Δ) * y⁻¹)⁻¹ * (y * (k' : Δ) * y⁻¹) =
        y * ((k : Δ)⁻¹ * (k' : Δ)) * y⁻¹ := by
      group
    rw [e]
    exact hKc _
  have hpresv : ∀ k k' : ↥L, ψ k 0 = ψ k' 0 ↔ ψ (cL k) 0 = ψ (cL k') 0 := fun k k' =>
    (he42pd_fix_iff hP k k').trans ((hcK k k').trans (he42pd_fix_iff hP (cL k) (cL k')).symm)
  have htrans : ∀ i : Fin 5, ∃ k : ↥L, ψ k 0 = i := by
    intro i
    obtain ⟨σ, hσ, hσ0⟩ := he42pd_trans i
    have hσr : σ ∈ ψ.range := by rw [hP.range]; exact hσ
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hσr
    exact ⟨k, by rw [hk, hσ0]⟩
  choose g hg using htrans
  obtain ⟨pif, hpif⟩ : ∃ pif : Fin 5 → Fin 5, ∀ k : ↥L, pif (ψ k 0) = ψ (cL k) 0 :=
    ⟨fun i => ψ (cL (g i)) 0, fun k => (hpresv (g (ψ k 0)) k).mp (hg (ψ k 0))⟩
  have hpifg : ∀ i : Fin 5, pif i = ψ (cL (g i)) 0 := by
    intro i
    have h1 := hpif (g i)
    rw [hg i] at h1
    exact h1
  have hpifinj : Function.Injective pif := by
    intro i i' h
    rw [hpifg, hpifg] at h
    have h2 := (hpresv (g i) (g i')).mpr h
    rw [hg, hg] at h2
    exact h2
  have hpifsurj : Function.Surjective pif := Finite.injective_iff_surjective.mp hpifinj
  obtain ⟨p, hp⟩ : ∃ p : Perm (Fin 5), ∀ i, p i = pif i :=
    ⟨Equiv.ofBijective pif ⟨hpifinj, hpifsurj⟩, fun i => rfl⟩
  have hp0 : p 0 = 0 := by
    have h1 := hpif 1
    simp only [map_one, hcL_one, Equiv.Perm.one_apply] at h1
    rw [hp]
    exact h1
  have hpk : ∀ k : ↥L, p (ψ k 0) = ψ (cL k) 0 := fun k => by rw [hp, hpif]
  have hpeq_aux : ∀ k k' : ↥L, p (ψ k (ψ k' 0)) = ψ (cL k) (p (ψ k' 0)) := by
    intro k k'
    have e1 : ψ k (ψ k' 0) = ψ (k * k') 0 := by rw [map_mul, Equiv.Perm.mul_apply]
    have e2 : ψ (cL k) (ψ (cL k') 0) = ψ (cL (k * k')) 0 := by
      rw [hcL_mul, map_mul, Equiv.Perm.mul_apply]
    rw [e1, hp, hp, hpif, hpif, e2]
  have hpeq : ∀ k : ↥L, ∀ i : Fin 5, p (ψ k i) = ψ (cL k) (p i) := by
    intro k i
    have h1 := hpeq_aux k (g i)
    rw [hg i] at h1
    exact h1
  have hp3 : p ^ 3 = 1 := by
    refine Equiv.ext fun i => ?_
    rw [Equiv.Perm.one_apply]
    have h1 : ∀ k : ↥L, (p ^ 3) (ψ k 0) = ψ k 0 := by
      intro k
      have e : (p ^ 3) (ψ k 0) = p (p (p (ψ k 0))) := by
        simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply]
      rw [e, hpk, hpk, hpk, hcL_cube]
    have h2 := h1 (g i)
    rw [hg i] at h2
    exact h2
  have hJL : ∀ j : ↥L, (j : Δ) ∈ J → ψ (cL j) = ψ j := by
    intro j hj
    have e : ((cL j * j⁻¹ : ↥L) : Δ) = y * (j : Δ) * y⁻¹ * (j : Δ)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcL]
    have h1 : ψ (cL j * j⁻¹) = 1 := (he42pd_ker_iff hP _).mpr (by rw [e]; exact hyJ _ hj)
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hHA : (J.subgroupOf L).map ψ ≤ alternatingGroup (Fin 5) := by
    intro h hh
    obtain ⟨j, -, rfl⟩ := Subgroup.mem_map.mp hh
    rw [← hP.range]
    exact MonoidHom.mem_range.mpr ⟨j, rfl⟩
  have hH0 : ∀ h ∈ (J.subgroupOf L).map ψ, h 0 = 0 := by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hh
    exact (hP.stab j).mpr (hP.JK (Subgroup.mem_subgroupOf.mp hj))
  have hcomm : ∀ h ∈ (J.subgroupOf L).map ψ, p * h = h * p := by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hh
    refine Equiv.ext fun i => ?_
    simp only [Equiv.Perm.mul_apply]
    rw [hpeq j i, hJL j (Subgroup.mem_subgroupOf.mp hj)]
  have hp1 : p = 1 :=
    CFSG.Quasithin.A94.He42Fin.eq_one_of_commute_klein _ hHA hH0 hP.Jcard p hp0 hp3 hcomm
  intro l hl
  obtain ⟨l', hl'⟩ : ∃ l' : ↥L, (l' : Δ) = l := ⟨⟨l, hl⟩, rfl⟩
  have h1 : ψ (cL l') = ψ l' := by
    refine Equiv.ext fun i => ?_
    have h2 := hpeq l' i
    rw [hp1] at h2
    simpa using h2.symm
  have h2 : ψ (cL l' * l'⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := (he42pd_ker_iff hP _).mp h2
  have e : ((cL l' * l'⁻¹ : ↥L) : Δ) = y * l * y⁻¹ * l⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcL, hl']
  rwa [e] at h3

theorem exists_mul_centralizer [Finite Δ] {y : Δ} (hyL : y ∈ normalizer (L : Set Δ))
    (hy3 : y ^ 3 = 1) (hyc : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ A) (h3 : ¬ 3 ∣ Nat.card A) :
    ∀ l ∈ L, ∃ a ∈ A, ∃ c ∈ L ⊓ centralizer ({y} : Set Δ), l = a * c := by
  intro l hl
  have hAL : A ≤ L := fun a ha => hP.KL (hP.JK (hP.AJ ha))
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := by
    intro a ha
    have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact A.mul_mem (hyc a (hAL ha)) ha
  have hcoset : ∀ x : Δ, (∃ a ∈ A, x = l * a) → ∃ a ∈ A, y * x * y⁻¹ = l * a := by
    rintro x ⟨a, ha, rfl⟩
    have hd : l⁻¹ * (y * l * y⁻¹ * l⁻¹) * l⁻¹⁻¹ ∈ A :=
      hP.A_normal l⁻¹ (L.inv_mem hl) _ (hyc l hl)
    rw [inv_inv] at hd
    exact ⟨(l⁻¹ * (y * l * y⁻¹ * l⁻¹) * l) * (y * a * y⁻¹), A.mul_mem hd (hyA a ha), by group⟩
  obtain ⟨T, hT⟩ : ∃ T : {x : Δ // ∃ a ∈ A, x = l * a} → {x : Δ // ∃ a ∈ A, x = l * a},
      ∀ x, (T x : Δ) = y * x.1 * y⁻¹ :=
    ⟨fun x => ⟨y * x.1 * y⁻¹, hcoset x.1 x.2⟩, fun x => rfl⟩
  have hTinj : Function.Injective T := by
    intro x x' h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [hT, hT] at h'
    exact mul_left_cancel (mul_right_cancel h')
  have hy3' : y * y * y = 1 := (pow_three' y).symm.trans hy3
  have hT3 : ∀ x, T (T (T x)) = x := by
    intro x
    apply Subtype.ext
    rw [hT, hT, hT]
    have e : y * (y * (y * x.1 * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * x.1 * (y * y * y)⁻¹ := by
      group
    rw [e, hy3']
    simp
  have hcardX : Nat.card {x : Δ // ∃ a ∈ A, x = l * a} = Nat.card A := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun a : A => (⟨l * a.1, a.1, a.2, rfl⟩ : {x : Δ // ∃ a ∈ A, x = l * a})) ⟨?_, ?_⟩)).symm
    · intro a b hab
      have h' : l * a.1 = l * b.1 := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel h')
    · rintro ⟨x, a, ha, hxa⟩
      exact ⟨⟨a, ha⟩, Subtype.ext hxa.symm⟩
  have hcard : ¬ 3 ∣ Nat.card {x : Δ // ∃ a ∈ A, x = l * a} := by
    rw [hcardX]
    exact h3
  obtain ⟨⟨c, hcX⟩, hfix⟩ := he42pd_fixed_of_cube T hTinj hT3 hcard
  have hfix' : y * c * y⁻¹ = c := by
    have h' := congrArg Subtype.val hfix
    rw [hT] at h'
    exact h'
  obtain ⟨a, ha, hca⟩ := hcX
  have hcL : c ∈ L := by
    rw [hca]
    exact L.mul_mem hl (hAL ha)
  have hcC : c ∈ centralizer ({y} : Set Δ) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    calc y * c = y * c * y⁻¹ * y := by group
      _ = c * y := by rw [hfix']
  refine ⟨c * a⁻¹ * c⁻¹, hP.A_normal c hcL a⁻¹ (A.inv_mem ha), c,
    Subgroup.mem_inf.mpr ⟨hcL, hcC⟩, ?_⟩
  rw [hca]
  group

theorem exists_inverting {y y₀ : Δ}
    (hcompl : ∀ l ∈ L, ∃ a ∈ A, ∃ c ∈ L ⊓ centralizer ({y} : Set Δ), l = a * c)
    (hAy : A ⊓ centralizer ({y} : Set Δ) = ⊥) (hy₀ : y₀ ∈ L ⊓ centralizer ({y} : Set Δ))
    (hy₀K : y₀ ∈ K) (hy₀A : y₀ ∉ A) (hy₀3 : orderOf y₀ = 3) :
    ∃ l ∈ L ⊓ centralizer ({y} : Set Δ), l * l = 1 ∧ l ∉ K ∧ l * y₀ * l⁻¹ = y₀⁻¹ := by
  have hAL : A ≤ L := fun a ha => hP.KL (hP.JK (hP.AJ ha))
  obtain ⟨hy₀L, hy₀C⟩ := Subgroup.mem_inf.mp hy₀
  obtain ⟨Y, hY⟩ : ∃ Y : ↥L, (Y : Δ) = y₀ := ⟨⟨y₀, hy₀L⟩, rfl⟩
  have hg0 : ψ Y 0 = 0 := (hP.stab Y).mpr (by rw [hY]; exact hy₀K)
  have hgA : ψ Y ∈ alternatingGroup (Fin 5) := by
    rw [← hP.range]
    exact MonoidHom.mem_range.mpr ⟨Y, rfl⟩
  have hord := he42pd_orderOf hP hY hy₀A hy₀3
  obtain ⟨τ, hτA, hτ2, hτinv, hτ0⟩ :=
    CFSG.Quasithin.A94.He42Fin.exists_inverting_involution (ψ Y) hgA hg0 hord
  have hτr : τ ∈ ψ.range := by
    rw [hP.range]
    exact hτA
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hτr
  obtain ⟨a, ha, c, hc, hxac⟩ := hcompl (x : Δ) x.2
  obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨C', hC'⟩ : ∃ C' : ↥L, (C' : Δ) = c := ⟨⟨c, hcL⟩, rfl⟩
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ↥L, (Aa : Δ) = a := ⟨⟨a, hAL ha⟩, rfl⟩
  have hAa1 : ψ Aa = 1 := (he42pd_ker_iff hP Aa).mpr (by rw [hAa]; exact ha)
  have hψc : ψ C' = τ := by
    rw [← hx]
    have hxe : x = Aa * C' := Subtype.ext (by rw [Subgroup.coe_mul, hAa, hC']; exact hxac)
    rw [hxe, map_mul, hAa1, one_mul]
  refine ⟨c, hc, ?_, ?_, ?_⟩
  ·
    have hcc : ψ (C' * C') = 1 := by rw [map_mul, hψc, hτ2]
    have hcA : c * c ∈ A := by
      have h1 := (he42pd_ker_iff hP (C' * C')).mp hcc
      rwa [Subgroup.coe_mul, hC'] at h1
    have hmem : c * c ∈ A ⊓ centralizer ({y} : Set Δ) :=
      Subgroup.mem_inf.mpr ⟨hcA, Subgroup.mul_mem _ hcC hcC⟩
    rw [hAy] at hmem
    exact Subgroup.mem_bot.mp hmem
  ·
    intro hcK
    have h0 : ψ C' 0 = 0 := (hP.stab C').mpr (by rw [hC']; exact hcK)
    rw [hψc] at h0
    exact hτ0 h0
  ·
    obtain ⟨Z, hZ⟩ : ∃ Z : ↥L, Z = C' * Y * C'⁻¹ * Y := ⟨_, rfl⟩
    have hZ1 : ψ Z = 1 := by
      rw [hZ, map_mul, map_mul, map_mul, map_inv, hψc, hτinv, inv_mul_cancel]
    have hZA : (Z : Δ) ∈ A := (he42pd_ker_iff hP Z).mp hZ1
    have hZC : (Z : Δ) ∈ centralizer ({y} : Set Δ) := by
      rw [hZ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hC', hY]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hy₀C)
        (Subgroup.inv_mem _ hcC)) hy₀C
    have hZ0 : (Z : Δ) = 1 := by
      have hm : (Z : Δ) ∈ A ⊓ centralizer ({y} : Set Δ) := Subgroup.mem_inf.mpr ⟨hZA, hZC⟩
      rw [hAy] at hm
      exact Subgroup.mem_bot.mp hm
    rw [hZ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hC', hY]
      at hZ0
    exact eq_inv_of_mul_eq_one_left hZ0

theorem mem_zpowers_of_commute {y y₀ : Δ}
    (hcompl : ∀ l ∈ L, ∃ a ∈ A, ∃ c ∈ L ⊓ centralizer ({y} : Set Δ), l = a * c)
    (hAy : A ⊓ centralizer ({y} : Set Δ) = ⊥) (hy₀ : y₀ ∈ L ⊓ centralizer ({y} : Set Δ))
    (hy₀K : y₀ ∈ K) (hy₀A : y₀ ∉ A) (hy₀3 : orderOf y₀ = 3) :
    ∀ c ∈ L ⊓ centralizer ({y} : Set Δ), c * y₀ = y₀ * c → c ∈ zpowers y₀ := by
  intro c hc hcy
  obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨hy₀L, hy₀C⟩ := Subgroup.mem_inf.mp hy₀
  obtain ⟨Y, hY⟩ : ∃ Y : ↥L, (Y : Δ) = y₀ := ⟨⟨y₀, hy₀L⟩, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : ↥L, (C' : Δ) = c := ⟨⟨c, hcL⟩, rfl⟩
  have hgA : ψ Y ∈ alternatingGroup (Fin 5) := by
    rw [← hP.range]
    exact MonoidHom.mem_range.mpr ⟨Y, rfl⟩
  have hτA : ψ C' ∈ alternatingGroup (Fin 5) := by
    rw [← hP.range]
    exact MonoidHom.mem_range.mpr ⟨C', rfl⟩
  have hord := he42pd_orderOf hP hY hy₀A hy₀3
  have hYC : C' * Y = Y * C' :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hC', hY]; exact hcy)
  have hcomm : ψ C' * ψ Y = ψ Y * ψ C' := by rw [← map_mul, ← map_mul, hYC]
  have hmem := CFSG.Quasithin.A94.He42Fin.mem_zpowers_of_commute_order_three (ψ Y) (ψ C')
    hgA hτA hord hcomm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : ψ (Y ^ k) = ψ C' := by rw [map_zpow, hk]
  have hZ1 : ψ (C' * (Y ^ k)⁻¹) = 1 := by rw [map_mul, map_inv, hk', mul_inv_cancel]
  have hZA : c * (y₀ ^ k)⁻¹ ∈ A := by
    have h1 := (he42pd_ker_iff hP _).mp hZ1
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, hC', Subgroup.coe_zpow, hY] at h1
  have hZC : c * (y₀ ^ k)⁻¹ ∈ centralizer ({y} : Set Δ) :=
    Subgroup.mul_mem _ hcC (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hy₀C k))
  have hm : c * (y₀ ^ k)⁻¹ ∈ A ⊓ centralizer ({y} : Set Δ) := Subgroup.mem_inf.mpr ⟨hZA, hZC⟩
  rw [hAy] at hm
  have hceq : c = y₀ ^ k := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hm)
  rw [hceq]
  exact Subgroup.zpow_mem_zpowers y₀ k

theorem exists_rankOne {R : Subgroup Δ} (hRJ : R ≤ J)
    (hRcard : Nat.card ((R.subgroupOf L).map ψ) = 4) {l : Δ} (hlL : l ∈ L) (hlK : l ∉ K)
    (hl2 : l * l = 1) :
    ∃ U : List Δ, (∀ u ∈ U, u ∈ R) ∧ CFSG.Quasithin.H13.F431.U42Aut.RankOne K L l U := by
  classical
  have hHA : (R.subgroupOf L).map ψ ≤ alternatingGroup (Fin 5) := by
    intro h hh
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hh
    rw [← hP.range]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hH0 : ∀ h ∈ (R.subgroupOf L).map ψ, h 0 = 0 := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    exact (hP.stab x).mpr (hP.JK (hRJ (Subgroup.mem_subgroupOf.mp hx)))
  have hpre : ∀ s : ↥((R.subgroupOf L).map ψ),
      ∃ x : ↥L, (x : Δ) ∈ R ∧ ψ x = (s : Perm (Fin 5)) := by
    rintro ⟨s, hs⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hs
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  choose px hpxR hpxψ using hpre
  haveI : Fintype ↥((R.subgroupOf L).map ψ) := Fintype.ofFinite _
  refine ⟨((Finset.univ : Finset ↥((R.subgroupOf L).map ψ)).toList).map (fun s => (px s : Δ)),
    ?_, ?_⟩
  · intro u hu
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hu
    exact hpxR s
  refine ⟨hP.KL, hlL, hl2, hlK, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hu
    exact hP.JK (hRJ (hpxR s))
  · intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · right
      have hx0 : ψ ⟨x, hx⟩ 0 ≠ 0 := fun h => hxK ((hP.stab ⟨x, hx⟩).mp h)
      have hl0 : ψ ⟨l, hlL⟩ 0 ≠ 0 := fun h => hlK ((hP.stab ⟨l, hlL⟩).mp h)
      obtain ⟨h, hhH, hh⟩ := CFSG.Quasithin.A94.He42Fin.exists_mem_klein_apply _ hHA hH0 hRcard
        (ψ ⟨x, hx⟩ 0) (ψ ⟨l, hlL⟩ 0) hx0 hl0
      obtain ⟨s, hs⟩ : ∃ s : ↥((R.subgroupOf L).map ψ), (s : Perm (Fin 5)) = h :=
        ⟨⟨h, hhH⟩, rfl⟩
      have hw0 : ψ ((⟨l, hlL⟩ : ↥L)⁻¹ * (px s * ⟨x, hx⟩)) 0 = 0 := by
        rw [map_mul, map_inv, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hpxψ s, hs, hh]
        exact (Equiv.Perm.inv_eq_iff_eq).mpr rfl
      refine ⟨(px s : Δ), List.mem_map.mpr ⟨s, Finset.mem_toList.mpr (Finset.mem_univ s), rfl⟩,
        (((⟨l, hlL⟩ : ↥L)⁻¹ * (px s * ⟨x, hx⟩) : ↥L) : Δ), (hP.stab _).mp hw0, ?_⟩
      show (px s : Δ) * x = l * (l⁻¹ * ((px s : Δ) * x))
      exact (mul_inv_cancel_left l _).symm

end PData

end CFSG.Quasithin.A94.He42PD
