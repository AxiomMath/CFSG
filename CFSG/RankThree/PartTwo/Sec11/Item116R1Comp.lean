module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem compJ1_eq_one_of_pow_three {Y : Type*} [Group Y] {Q : Subgroup Y}
    (hQ : IsPGroup 2 Q) {e : Y} (he : e ∈ Q) (h3 : e ^ 3 = 1) : e = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨e, he⟩
  have hk' : e ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h4 : orderOf e ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one hcop] at h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

theorem compJ1_le_normalizer_inSubgroup_pCore {X : Type*} [Group X] (p : ℕ) (C : Subgroup X) :
    C ≤ Subgroup.normalizer ((CFSG.inSubgroup (CFSG.pCore p) C : Subgroup X) : Set X) := by
  have key : ∀ h ∈ C, ∀ y ∈ CFSG.inSubgroup (CFSG.pCore p) C,
      h * y * h⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore p) C := by
    intro h hh y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥C) * z * (⟨h, hh⟩ : ↥C)⁻¹,
      (CFSG.pCore_normal (p := p) (G := ↥C)).conj_mem z hz _, ?_⟩
    simp
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro hy
    have h' := key g⁻¹ (C.inv_mem hg) _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h'

theorem compJ1_main {X : Type*} [Group X] [Finite X]
    {K₁ : Subgroup X} (h1 : CFSG.IsComponent K₁) (hZ1 : Subgroup.center K₁ = ⊥)
    {P : Subgroup X} (hPp : IsPGroup 2 P)
    (hPnorm : ∀ g ∈ K₁, ∀ y : X, y ∈ P ↔ g * y * g⁻¹ ∈ P)
    {d : X} (hd : d ∈ K₁) (hd3 : orderOf d = 3) :
    ∀ x ∈ P, x ∈ Subgroup.centralizer (K₁ : Set X) := by
  have hd3pow : d ^ 3 = 1 := by
    have := pow_orderOf_eq_one d
    rwa [hd3] at this
  have hA : ∀ x ∈ P, ∀ k ∈ K₁, x * k * x⁻¹ ∈ K₁ := by
    intro x hx k hk
    set K' : Subgroup X := K₁.map (MulAut.conj x : X ≃* X).toMonoidHom with hK'def
    have hK' : CFSG.IsComponent K' :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x : X ≃* X) h1
    rcases CFSG.LocalCores.distinct_components_commute h1 hK' with heq | hcomm
    · have hmem : x * k * x⁻¹ ∈ K' :=
        Subgroup.mem_map_of_mem (MulAut.conj x : X ≃* X).toMonoidHom hk
      rw [← heq] at hmem
      exact hmem
    · exfalso
      have hK1C' : K₁ ≤ Subgroup.centralizer (K' : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hinf : ∀ z : X, z ∈ K₁ → z ∈ K' → z = 1 := by
        intro z hz hzK'
        have hzc : (⟨z, hz⟩ : K₁) ∈ Subgroup.center K₁ := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          exact (Subgroup.mem_centralizer_iff.mp (hK1C' g.2) z hzK').symm
        rw [hZ1, Subgroup.mem_bot] at hzc
        exact congrArg Subtype.val hzc
      have hd' : x * d * x⁻¹ ∈ K' :=
        Subgroup.mem_map_of_mem (MulAut.conj x : X ≃* X).toMonoidHom hd
      have hC : Commute (x * d * x⁻¹) d := Subgroup.mem_centralizer_iff.mp (hK1C' hd) _ hd'
      have hdne : x * d * x⁻¹ ≠ d := by
        intro h
        have hd1 : d = 1 := hinf d hd (by rw [h] at hd'; exact hd')
        rw [hd1, orderOf_one] at hd3
        norm_num at hd3
      have hd'3 : (x * d * x⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hd3pow, mul_one, mul_inv_cancel]
      have hC' : Commute (x * d * x⁻¹) d⁻¹ := hC.inv_right
      have he3 : (x * d * x⁻¹ * d⁻¹) ^ 3 = 1 := by
        rw [hC'.mul_pow, hd'3, inv_pow, hd3pow, inv_one, one_mul]
      have he_P : x * d * x⁻¹ * d⁻¹ ∈ P := by
        have h1' : d * x⁻¹ * d⁻¹ ∈ P := (hPnorm d hd x⁻¹).mp (P.inv_mem hx)
        have heq' : x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) := by simp only [mul_assoc]
        rw [heq']
        exact P.mul_mem hx h1'
      have he1 : x * d * x⁻¹ * d⁻¹ = 1 :=
        compJ1_eq_one_of_pow_three hPp he_P he3
      exact hdne (mul_inv_eq_one.mp he1)
  have hMnorm : (P.subgroupOf K₁).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgn := (hPnorm (g : X) g.2 (n : X)).mp hn
    simpa using hgn
  rcases CFSG.LocalCores.quasisimple_normal_subgroups h1.1 hMnorm with htop | hle
  ·
    exfalso
    have hdP : d ∈ P := by
      have hmem : (⟨d, hd⟩ : K₁) ∈ P.subgroupOf K₁ := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hd1 : d = 1 := compJ1_eq_one_of_pow_three hPp hdP hd3pow
    rw [hd1, orderOf_one] at hd3
    norm_num at hd3
  ·
    rw [hZ1] at hle
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hxK : x * k * x⁻¹ ∈ K₁ := hA x hx k hk
    have hcK : x * k * x⁻¹ * k⁻¹ ∈ K₁ := K₁.mul_mem hxK (K₁.inv_mem hk)
    have hcP : x * k * x⁻¹ * k⁻¹ ∈ P := by
      have h1' : k * x⁻¹ * k⁻¹ ∈ P := (hPnorm k hk x⁻¹).mp (P.inv_mem hx)
      have heq' : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by simp only [mul_assoc]
      rw [heq']
      exact P.mul_mem hx h1'
    have hmemM : (⟨x * k * x⁻¹ * k⁻¹, hcK⟩ : K₁) ∈ P.subgroupOf K₁ :=
      Subgroup.mem_subgroupOf.mpr hcP
    have hone : (⟨x * k * x⁻¹ * k⁻¹, hcK⟩ : K₁) = 1 := Subgroup.mem_bot.mp (hle hmemM)
    have hval : x * k * x⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hone
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hval)).symm

theorem pCore_two_centralizer_le_centralizer_of_component {X : Type*} [Group X] [Finite X]
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) {c d : X} (hd : d ∈ K₁) (hc : c ∈ K₂) (hd3 : orderOf d = 3) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X)) ≤
      Subgroup.centralizer (K₁ : Set X) := by
  have hK1C : K₁ ≤ Subgroup.centralizer ({c} : Set X) := by
    have hcomm : K₁ ≤ Subgroup.centralizer (K₂ : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((CFSG.LocalCores.distinct_components_commute h1 h2).resolve_left hne)
    exact hcomm.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc))
  have hPp : IsPGroup 2 (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X))) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.centralizer ({c} : Set X)))).map
      (Subgroup.centralizer ({c} : Set X)).subtype
  have hPnorm : ∀ g ∈ K₁, ∀ y : X,
      y ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X)) ↔
        g * y * g⁻¹ ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X)) := by
    intro g hg y
    exact Subgroup.mem_normalizer_iff.mp
      (compJ1_le_normalizer_inSubgroup_pCore 2 _ (hK1C hg)) y
  intro x hx
  exact compJ1_main h1 hZ1 hPp hPnorm hd hd3 x hx

end CFSG.RankThree.PartTwo.Sec11

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem compJ3_inf_eq_bot {X : Type*} [Group X] [Finite X] {K K' : Subgroup X}
    (hK : CFSG.IsComponent K) (hK' : CFSG.IsComponent K') (hne : K ≠ K')
    (hZ : Subgroup.center K = ⊥) : K ⊓ K' = ⊥ := by
  have hc : K' ≤ Subgroup.centralizer (K : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hK' hK).resolve_left (Ne.symm hne))
  rw [eq_bot_iff]
  intro z hz
  have hzK : z ∈ K := (Subgroup.mem_inf.mp hz).1
  have hzK' : z ∈ K' := (Subgroup.mem_inf.mp hz).2
  have hzc : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp (hc hzK') g.1 g.2
    simpa using this
  rw [hZ, Subgroup.mem_bot] at hzc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hzc)

theorem compJ3_conj_mem {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.IsComponent K) (hZ : Subgroup.center K = ⊥) {y x : X} (hy : y ∈ K)
    (hy3 : orderOf y = 3) (h2 : ∃ k : ℕ, (x * y * x⁻¹ * y⁻¹) ^ (2 ^ k) = 1) :
    x * y * x⁻¹ ∈ K := by
  have hK' : CFSG.IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK
  have hy' : x * y * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom := ⟨y, hy, rfl⟩
  by_contra hyK
  have hKK' : K ≠ K.map (MulAut.conj x).toMonoidHom := by
    intro h
    apply hyK
    rw [h]
    exact hy'
  have hbot : ⁅K, K.map (MulAut.conj x).toMonoidHom⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left hKK'
  have hcomm : Commute (x * y * x⁻¹) y :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hy) (x * y * x⁻¹) hy'
  have hy3pow : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  have hyne : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy3
    omega
  have hyy' : x * y * x⁻¹ ≠ y := by
    intro h
    have hyI : y ∈ K ⊓ K.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_inf.mpr ⟨hy, by rw [← h]; exact hy'⟩
    rw [compJ3_inf_eq_bot hK hK' hKK' hZ, Subgroup.mem_bot] at hyI
    exact hyne hyI
  have he1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := fun h => hyy' (mul_inv_eq_one.mp h)
  have hy3' : (x * y * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3pow, mul_one, mul_inv_cancel]
  have he3 : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1 := by
    rw [hcomm.inv_right.mul_pow 3, hy3', inv_pow, hy3pow, inv_one, one_mul]
  obtain ⟨k, hk⟩ := h2
  have hcop : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
  have hgcd := pow_gcd_eq_one.mpr ⟨he3, hk⟩
  rw [hcop, pow_one] at hgcd
  exact absurd hgcd he1

theorem compJ3_fix_of_mem {X : Type*} [Group X] [Finite X]
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥) {c d : X} (hd : d ∈ K₁)
    (hc : c ∈ K₂) (hd3 : orderOf d = 3) (hc3 : orderOf c = 3) (P : Subgroup X)
    (hP2 : ∀ y ∈ P, ∃ k : ℕ, y ^ (2 ^ k) = 1)
    (hPc : ∀ y ∈ P, c * y * c⁻¹ ∈ P) (hPd : ∀ y ∈ P, d * y * d⁻¹ ∈ P)
    {x : X} (hx : x ∈ P) (hxcd : x * (c * d) = c * d * x) :
    x ∈ Subgroup.centralizer ({c} : Set X) ⊓ Subgroup.centralizer ({d} : Set X) := by
  have hmd : x * d * x⁻¹ * d⁻¹ ∈ P := by
    rw [show x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) by simp only [mul_assoc]]
    exact P.mul_mem hx (hPd x⁻¹ (P.inv_mem hx))
  have hmc : x * c * x⁻¹ * c⁻¹ ∈ P := by
    rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by simp only [mul_assoc]]
    exact P.mul_mem hx (hPc x⁻¹ (P.inv_mem hx))
  have hdx : x * d * x⁻¹ ∈ K₁ := compJ3_conj_mem h1 hZ1 hd hd3 (hP2 _ hmd)
  have hcx : x * c * x⁻¹ ∈ K₂ := compJ3_conj_mem h2 hZ2 hc hc3 (hP2 _ hmc)
  have hmul : (x * c * x⁻¹) * (x * d * x⁻¹) = c * d := by
    calc (x * c * x⁻¹) * (x * d * x⁻¹) = x * (c * d) * x⁻¹ := by group
      _ = c * d * x * x⁻¹ := by rw [hxcd]
      _ = c * d := by group
  have hu : (x * c * x⁻¹)⁻¹ * c = (x * d * x⁻¹) * d⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hmul, mul_inv_cancel_right]
  have hu1 : (x * c * x⁻¹)⁻¹ * c ∈ K₂ := K₂.mul_mem (K₂.inv_mem hcx) hc
  have hu2 : (x * c * x⁻¹)⁻¹ * c ∈ K₁ := by
    rw [hu]
    exact K₁.mul_mem hdx (K₁.inv_mem hd)
  have hu0 : (x * c * x⁻¹)⁻¹ * c ∈ K₁ ⊓ K₂ := Subgroup.mem_inf.mpr ⟨hu2, hu1⟩
  rw [compJ3_inf_eq_bot h1 h2 hne hZ1, Subgroup.mem_bot] at hu0
  have hcfix : x * c * x⁻¹ = c := inv_mul_eq_one.mp hu0
  have hdfix : x * d * x⁻¹ = d := mul_inv_eq_one.mp (hu.symm.trans hu0)
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  · calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [hcfix]
  · calc x * d = x * d * x⁻¹ * x := by group
      _ = d * x := by rw [hdfix]

theorem compJ3_normal_of_mem {X : Type*} [Group X] {C : Subgroup X} {g : X} (hg : g ∈ C)
    {y : X} (hy : y ∈ CFSG.inSubgroup (CFSG.pCore 2) C) :
    g * y * g⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore 2) C :=
  (Subgroup.mem_normalizer_iff.mp
    (CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 C hg) y).mp hy

theorem compJ3_pow_two {X : Type*} [Group X] (C : Subgroup X) {y : X}
    (hy : y ∈ CFSG.inSubgroup (CFSG.pCore 2) C) : ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 C ⟨y, hy⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem pCore_two_centralizer_mul_le {X : Type*} [Group X] [Finite X]
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥) {c d : X} (hd : d ∈ K₁)
    (hc : c ∈ K₂) (hd3 : orderOf d = 3) (hc3 : orderOf c = 3) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c * d} : Set X)) ≤
      Subgroup.centralizer ({c} : Set X) ⊓ Subgroup.centralizer ({d} : Set X) := by
  have hbot : ⁅K₁, K₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute h1 h2).resolve_left hne
  have hcd : c * d = d * c :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hd) c hc
  have hdC : d ∈ Subgroup.centralizer ({c * d} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← mul_assoc, ← hcd])
  have hcC : c ∈ Subgroup.centralizer ({c * d} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [mul_assoc, ← hcd])
  intro x hx
  exact compJ3_fix_of_mem h1 h2 hne hZ1 hZ2 hd hc hd3 hc3
    (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c * d} : Set X)))
    (fun y hy => compJ3_pow_two _ hy)
    (fun y hy => compJ3_normal_of_mem hcC hy)
    (fun y hy => compJ3_normal_of_mem hdC hy)
    hx
    (Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2
        (Subgroup.centralizer ({c * d} : Set X)) hx))

end CFSG.RankThree.PartTwo.Sec11

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem compT_conj_mem_inSubgroup_pCore {X : Type*} [Group X] (p : ℕ) {H : Subgroup X} {g : X}
    (hg : g ∈ H) {x : X} (hx : x ∈ inSubgroup (CFSG.pCore p) H) :
    g * x * g⁻¹ ∈ inSubgroup (CFSG.pCore p) H := by
  unfold inSubgroup at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : H) * y * (⟨g, hg⟩ : H)⁻¹,
    (CFSG.pCore_normal (p := p) (G := H)).conj_mem y hy _, ?_⟩
  simp

theorem compT_pow_eq_one_of_mem_inSubgroup {X : Type*} [Group X] (p : ℕ) {H : Subgroup X}
    {x : X} (hx : x ∈ inSubgroup (CFSG.pCore p) H) : ∃ k : ℕ, x ^ p ^ k = 1 := by
  unfold inSubgroup at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := H)) ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have h3 : y ^ p ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h4 : H.subtype (y ^ p ^ k) = H.subtype y ^ p ^ k := map_pow H.subtype y (p ^ k)
  rw [← h4, h3, map_one]

theorem compT_pow_eq_one_of_mem_pCore {X : Type*} [Group X] (p : ℕ) {x : X}
    (hx : x ∈ CFSG.pCore p X) : ∃ k : ℕ, x ^ p ^ k = 1 := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := X)) ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem compT_inf_eq_bot_of_pow {X : Type*} [Group X] {A B : Subgroup X}
    (hA : ∀ x ∈ A, ∃ k : ℕ, x ^ 2 ^ k = 1) (hB : ∀ x ∈ B, ∃ k : ℕ, x ^ 3 ^ k = 1) :
    A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxB⟩
  obtain ⟨k, hk⟩ := hA x hxA
  obtain ⟨m, hm⟩ := hB x hxB
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm
  have hcop : Nat.Coprime (2 ^ k) (3 ^ m) := Nat.Coprime.pow k m (by norm_num)
  have h1' : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp h1'

theorem compT_pCore_eq_bot_of_theta {X : Type*} [Group X] [Finite X]
    (hθ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X = ⊥) {r : ℕ} (hr : r.Prime)
    (hr3 : r ≠ 3) : CFSG.pCore r X = ⊥ := by
  have key := (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
    (H := X) Nat.prime_three).2.2.2.2.2.2 r hr hr3
  exact eq_bot_iff.mpr (key.trans hθ.le)

theorem compT_fitting_le_pCore_three {X : Type*} [Group X] [Finite X]
    (hθ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X = ⊥) :
    CFSG.fittingSubgroup X ≤ CFSG.pCore 3 X := by
  rw [CFSG.fitting_eq_sup_pCore X]
  refine iSup_le fun p => ?_
  by_cases h3 : p.1.1 = 3
  · exact (congrArg (fun n => CFSG.pCore n X) h3).le
  · have hp : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
    rw [compT_pCore_eq_bot_of_theta hθ hp h3]
    exact bot_le

def CompTTwoCentral {X : Type*} [Group X] (M : Subgroup X) (x : X) : Prop :=
  x ∈ M ∧ (∀ m ∈ M, m * x = x * m) ∧ ∃ k : ℕ, x ^ 2 ^ k = 1

theorem compT_twoCentral_one {X : Type*} [Group X] (M : Subgroup X) :
    CompTTwoCentral M 1 :=
  ⟨M.one_mem, fun m _ => by rw [mul_one, one_mul], 0, by rw [one_pow]⟩

theorem compT_twoCentral_mul {X : Type*} [Group X] {M : Subgroup X} {x y : X}
    (hx : CompTTwoCentral M x) (hy : CompTTwoCentral M y) :
    CompTTwoCentral M (x * y) := by
  obtain ⟨hxM, hxc, k, hk⟩ := hx
  obtain ⟨hyM, hyc, l, hl⟩ := hy
  have hxy : Commute x y := (hxc y hyM).symm
  refine ⟨M.mul_mem hxM hyM, fun m hm => ?_, k + l, ?_⟩
  · calc m * (x * y) = (m * x) * y := (mul_assoc _ _ _).symm
      _ = (x * m) * y := by rw [hxc m hm]
      _ = x * (m * y) := mul_assoc _ _ _
      _ = x * (y * m) := by rw [hyc m hm]
      _ = x * y * m := (mul_assoc _ _ _).symm
  · have e1 : x ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    have e2 : y ^ 2 ^ (k + l) = 1 := by rw [add_comm, pow_add, pow_mul, hl, one_pow]
    rw [hxy.mul_pow, e1, e2, one_mul]

theorem compT_twoCentral_inv {X : Type*} [Group X] {M : Subgroup X} {x : X}
    (hx : CompTTwoCentral M x) : CompTTwoCentral M x⁻¹ := by
  obtain ⟨hxM, hxc, k, hk⟩ := hx
  refine ⟨M.inv_mem hxM, fun m hm => ?_, k, ?_⟩
  · exact Commute.inv_right (show Commute m x from hxc m hm)
  · rw [inv_pow, hk, inv_one]

def compTTwoCentralPart {X : Type*} [Group X] (M : Subgroup X) : Subgroup X where
  carrier := {x | CompTTwoCentral M x}
  one_mem' := compT_twoCentral_one M
  mul_mem' := fun hx hy => compT_twoCentral_mul hx hy
  inv_mem' := fun hx => compT_twoCentral_inv hx

theorem mem_compTTwoCentralPart {X : Type*} [Group X] {M : Subgroup X} {x : X} :
    x ∈ compTTwoCentralPart M ↔ CompTTwoCentral M x := Iff.rfl

theorem compT_eq_bot_of_two_central {X : Type*} [Group X] {M I : Subgroup X} (hM : M.Normal)
    (hIM : I ≤ M) (hIc : ∀ i ∈ I, ∀ m ∈ M, m * i = i * m)
    (hI2 : ∀ i ∈ I, ∃ k : ℕ, i ^ 2 ^ k = 1) (h2 : CFSG.pCore 2 X = ⊥) : I = ⊥ := by
  have hTn : (compTTwoCentralPart M).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxM, hxc, k, hk⟩ := (mem_compTTwoCentralPart).mp hx
    refine (mem_compTTwoCentralPart).mpr ⟨hM.conj_mem x hxM g, fun m hm => ?_, k, ?_⟩
    · have hm' : g⁻¹ * m * g ∈ M := by
        have h := hM.conj_mem m hm g⁻¹
        rwa [inv_inv] at h
      have hc := hxc _ hm'
      calc m * (g * x * g⁻¹) = g * (g⁻¹ * m * g) * x * g⁻¹ := by group
        _ = g * ((g⁻¹ * m * g) * x) * g⁻¹ := by simp only [mul_assoc]
        _ = g * (x * (g⁻¹ * m * g)) * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * m := by group
    · rw [conj_pow, hk]
      simp
  have hTle : compTTwoCentralPart M ≤ CFSG.pCore 2 X := by
    have hTp : IsPGroup 2 (compTTwoCentralPart M) := by
      intro t
      obtain ⟨-, -, k, hk⟩ := (mem_compTTwoCentralPart).mp t.2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    exact le_sSup (show compTTwoCentralPart M ∈ {K : Subgroup X | K.Normal ∧ IsPGroup 2 K} from
      ⟨hTn, hTp⟩)
  rw [eq_bot_iff]
  intro i hi
  have hT : i ∈ compTTwoCentralPart M :=
    (mem_compTTwoCentralPart).mpr ⟨hIM hi, hIc i hi, hI2 i hi⟩
  have hT' := hTle hT
  rw [h2] at hT'
  exact hT'

theorem compT_map_conj_eq_self {X : Type*} [Group X] {K : Subgroup X} {g : X}
    (h : ∀ k ∈ K, g * k = k * g) : K.map (MulAut.conj g).toMonoidHom = K := by
  have e : ∀ y ∈ K, (MulAut.conj g).toMonoidHom y = y := by
    intro y hy
    show g * y * g⁻¹ = y
    rw [h y hy, mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [e y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, e x hx⟩

theorem compT_main {X : Type*} [Group X] [Finite X]
    (hO2 : CFSG.pCore 2 X = ⊥) (hF : CFSG.fittingSubgroup X ≤ CFSG.pCore 3 X)
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    {c d : X} (hd : d ∈ K₁) (hc : c ∈ K₂)
    {Pc Pd : Subgroup X}
    (hPc2 : ∀ x ∈ Pc, ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hPcn : ∀ g ∈ Subgroup.centralizer ({c} : Set X), ∀ x ∈ Pc, g * x * g⁻¹ ∈ Pc)
    (hPdn : ∀ g ∈ Subgroup.centralizer ({d} : Set X), ∀ x ∈ Pd, g * x * g⁻¹ ∈ Pd)
    (hPc1 : Pc ≤ Subgroup.centralizer (K₁ : Set X))
    (hPd2 : Pd ≤ Subgroup.centralizer (K₂ : Set X)) :
    Pc ⊓ Pd = ⊥ := by
  obtain ⟨I, hIdef⟩ : ∃ I : Subgroup X, I = Pc ⊓ Pd := ⟨_, rfl⟩
  have hI_mem : ∀ x, x ∈ I ↔ x ∈ Pc ∧ x ∈ Pd := fun x => by
    rw [hIdef]
    exact Subgroup.mem_inf
  rw [← hIdef]
  have hIPc : I ≤ Pc := fun x hx => ((hI_mem x).mp hx).1
  have hIPd : I ≤ Pd := fun x hx => ((hI_mem x).mp hx).2
  have hI2 : ∀ i ∈ I, ∃ k : ℕ, i ^ 2 ^ k = 1 := fun i hi => hPc2 i (hIPc hi)
  have hI1 : I ≤ Subgroup.centralizer (K₁ : Set X) := hIPc.trans hPc1
  have hI2' : I ≤ Subgroup.centralizer (K₂ : Set X) := hIPd.trans hPd2
  have hcentI1 : ∀ i ∈ I, ∀ k ∈ K₁, i * k = k * i := fun i hi k hk =>
    ((Subgroup.mem_centralizer_iff.mp (hI1 hi)) k hk).symm
  have hcentI2 : ∀ i ∈ I, ∀ k ∈ K₂, i * k = k * i := fun i hi k hk =>
    ((Subgroup.mem_centralizer_iff.mp (hI2' hi)) k hk).symm
  obtain ⟨E2, hE2def⟩ : ∃ E : Subgroup X,
      E = sSup {J : Subgroup X | CFSG.IsComponent J ∧ J ≠ K₁ ∧ J ≠ K₂} := ⟨_, rfl⟩
  have hJE2 : ∀ J : Subgroup X, CFSG.IsComponent J → J ≠ K₁ → J ≠ K₂ → J ≤ E2 := by
    intro J hJc hJ1 hJ2
    rw [hE2def]
    exact le_sSup ⟨hJc, hJ1, hJ2⟩
  have hE2_le : ∀ T : Subgroup X,
      (∀ J : Subgroup X, CFSG.IsComponent J → J ≠ K₁ → J ≠ K₂ → J ≤ T) → E2 ≤ T := by
    intro T hT
    rw [hE2def]
    refine sSup_le fun J hJ => ?_
    obtain ⟨hJc, hJ1, hJ2⟩ := hJ
    exact hT J hJc hJ1 hJ2
  have hE2_layer : E2 ≤ CFSG.layer X :=
    hE2_le _ fun J hJ _ _ => CFSG.LocalCores.component_le_layer hJ
  have hcomp_c : ∀ J : Subgroup X, CFSG.IsComponent J → J ≠ K₂ →
      J ≤ Subgroup.centralizer ({c} : Set X) := by
    intro J hJ hJ2
    rcases CFSG.LocalCores.distinct_components_commute hJ h2 with h | h
    · exact absurd h hJ2
    · intro j hj
      have hjK : j ∈ Subgroup.centralizer (K₂ : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hj
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact (Subgroup.mem_centralizer_iff.mp hjK) c hc
  have hcomp_d : ∀ J : Subgroup X, CFSG.IsComponent J → J ≠ K₁ →
      J ≤ Subgroup.centralizer ({d} : Set X) := by
    intro J hJ hJ1
    rcases CFSG.LocalCores.distinct_components_commute hJ h1 with h | h
    · exact absurd h hJ1
    · intro j hj
      have hjK : j ∈ Subgroup.centralizer (K₁ : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hj
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact (Subgroup.mem_centralizer_iff.mp hjK) d hd
  have hE2_cc : E2 ≤ Subgroup.centralizer ({c} : Set X) :=
    hE2_le _ fun J hJ _ hJ2 => hcomp_c J hJ hJ2
  have hE2_cd : E2 ≤ Subgroup.centralizer ({d} : Set X) :=
    hE2_le _ fun J hJ hJ1 _ => hcomp_d J hJ hJ1
  have hconjE2 : ∀ g : X, (∀ k ∈ K₁, g * k = k * g) → (∀ k ∈ K₂, g * k = k * g) →
      ∀ e ∈ E2, g * e * g⁻¹ ∈ E2 := by
    intro g hg1 hg2 e he
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    have key : E2 ≤ E2.comap (MulAut.conj g).toMonoidHom := by
      rw [hE2def]
      refine sSup_le fun J hJ => ?_
      obtain ⟨hJc, hJ1, hJ2⟩ := hJ
      intro j hj
      rw [Subgroup.mem_comap]
      have hne1 : J.map (MulAut.conj g).toMonoidHom ≠ K₁ := fun h =>
        hJ1 (Subgroup.map_injective hinj (h.trans (compT_map_conj_eq_self hg1).symm))
      have hne2 : J.map (MulAut.conj g).toMonoidHom ≠ K₂ := fun h =>
        hJ2 (Subgroup.map_injective hinj (h.trans (compT_map_conj_eq_self hg2).symm))
      have hJ' : CFSG.IsComponent (J.map (MulAut.conj g).toMonoidHom) :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJc
      exact le_sSup (show J.map (MulAut.conj g).toMonoidHom ∈
          {J : Subgroup X | CFSG.IsComponent J ∧ J ≠ K₁ ∧ J ≠ K₂} from ⟨hJ', hne1, hne2⟩)
        (Subgroup.mem_map_of_mem _ hj)
    have h' : (MulAut.conj g).toMonoidHom e ∈ E2 := key he
    exact h'
  have hE2_I : ∀ e ∈ E2, ∀ i ∈ I, e * i * e⁻¹ ∈ I := by
    intro e he i hi
    rw [hI_mem]
    exact ⟨hPcn e (hE2_cc he) i (hIPc hi), hPdn e (hE2_cd he) i (hIPd hi)⟩
  have hE2_I' : ∀ e ∈ E2, ∀ i ∈ I, e⁻¹ * i * e ∈ I := by
    intro e he i hi
    have h := hE2_I e⁻¹ (E2.inv_mem he) i hi
    rwa [inv_inv] at h
  have hI_E2 : ∀ i ∈ I, ∀ e ∈ E2, i * e * i⁻¹ ∈ E2 := fun i hi e he =>
    hconjE2 i (hcentI1 i hi) (hcentI2 i hi) e he
  have hI_E2' : ∀ i ∈ I, ∀ e ∈ E2, i⁻¹ * e * i ∈ E2 := by
    intro i hi e he
    have h := hI_E2 i⁻¹ (I.inv_mem hi) e he
    rwa [inv_inv] at h
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup X, N = I ⊓ E2 := ⟨_, rfl⟩
  have hN_mem : ∀ x, x ∈ N ↔ x ∈ I ∧ x ∈ E2 := fun x => by
    rw [hNdef]
    exact Subgroup.mem_inf
  have hE2_N : ∀ e ∈ E2, ∀ n ∈ N, e * n * e⁻¹ ∈ N := by
    intro e he n hn
    obtain ⟨hnI, hnE⟩ := (hN_mem n).mp hn
    rw [hN_mem]
    exact ⟨hE2_I e he n hnI, E2.mul_mem (E2.mul_mem he hnE) (E2.inv_mem he)⟩
  have hE2_N' : ∀ e ∈ E2, ∀ n ∈ N, e⁻¹ * n * e ∈ N := by
    intro e he n hn
    have h := hE2_N e⁻¹ (E2.inv_mem he) n hn
    rwa [inv_inv] at h
  have hJN : ∀ J : Subgroup X, CFSG.IsComponent J → J ≠ K₁ → J ≠ K₂ → ⁅J, N⁆ = ⊥ := by
    intro J hJ hJ1 hJ2
    have hJE : J ≤ E2 := hJE2 J hJ hJ1 hJ2
    have hnorm : ∀ n ∈ E2, ∀ j ∈ J, n * j * n⁻¹ ∈ J := by
      intro n hn j hj
      have hn' : n ∈ Subgroup.normalizer (J : Set X) :=
        CFSG.LocalCores.layer_le_normalizer hJ (hE2_layer hn)
      exact (Subgroup.mem_normalizer_iff.mp hn' j).mp hj
    have hcomm : ⁅J, N⁆ ≤ J ⊓ N := by
      rw [Subgroup.commutator_le]
      intro j hj n hn
      obtain ⟨-, hnE⟩ := (hN_mem n).mp hn
      rw [commutatorElement_def, Subgroup.mem_inf]
      constructor
      · have h1' : n * j⁻¹ * n⁻¹ ∈ J := hnorm n hnE j⁻¹ (J.inv_mem hj)
        rw [show j * n * j⁻¹ * n⁻¹ = j * (n * j⁻¹ * n⁻¹) by simp only [mul_assoc]]
        exact J.mul_mem hj h1'
      · exact N.mul_mem (hE2_N j (hJE hj) n hn) (N.inv_mem hn)
    have hNJ_norm : ((J ⊓ N).subgroupOf J).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
      have e : ((g * x * g⁻¹ : ↥J) : X) = (g : X) * (x : X) * (g : X)⁻¹ := by simp
      rw [Subgroup.mem_subgroupOf, e, Subgroup.mem_inf]
      exact ⟨J.mul_mem (J.mul_mem g.2 hx.1) (J.inv_mem g.2),
        hE2_N (g : X) (hJE g.2) (x : X) hx.2⟩
    have hcases := CFSG.LocalCores.quasisimple_normal_subgroups hJ.1 hNJ_norm
    have hJ_not_top : (J ⊓ N).subgroupOf J ≠ ⊤ := by
      intro htop
      have hJ2' : IsPGroup 2 ↥J := by
        intro g
        have hgmem : g ∈ (J ⊓ N).subgroupOf J := by
          rw [htop]
          exact Subgroup.mem_top g
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hgmem
        obtain ⟨k, hk⟩ := hI2 (g : X) ((hN_mem _).mp hgmem.2).1
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      haveI : Group.IsNilpotent ↥J := IsPGroup.isNilpotent hJ2'
      haveI : Group.IsSolvable ↥J := inferInstance
      haveI : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
      haveI : Group.IsPerfect ↥J := hJ.1.1
      exact (Group.IsPerfect.not_isSolvable ↥J) inferInstance
    have hcentJ : ∀ x ∈ J ⊓ N, ∀ j ∈ J, j * x = x * j := by
      intro x hx j hj
      have hxmem : (⟨x, hx.1⟩ : ↥J) ∈ (J ⊓ N).subgroupOf J := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      have hz := Subgroup.mem_center_iff.mp
        ((hcases.resolve_left hJ_not_top) hxmem) ⟨j, hj⟩
      have hz' := congrArg Subtype.val hz
      simpa using hz'
    have hdc : ⁅⁅J, N⁆, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact hcentJ y (hcomm hy) j hj
    exact CFSG.LocalCores.perfect_double_commutator hJ.1.1 hdc
  have hJI : ∀ J : Subgroup X, CFSG.IsComponent J → J ≠ K₁ → J ≠ K₂ → ⁅J, I⁆ = ⊥ := by
    intro J hJ hJ1 hJ2
    have hJN_eq := hJN J hJ hJ1 hJ2
    have hJI_le : ⁅J, I⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro j hj i hi
      have hjE : j ∈ E2 := hJE2 J hJ hJ1 hJ2 hj
      rw [commutatorElement_def, hN_mem]
      constructor
      · exact I.mul_mem (hE2_I j hjE i hi) (I.inv_mem hi)
      · rw [show j * i * j⁻¹ * i⁻¹ = j * (i * j⁻¹ * i⁻¹) by simp only [mul_assoc]]
        exact E2.mul_mem hjE (hI_E2 i hi j⁻¹ (E2.inv_mem hjE))
    have hdc2 : ⁅⁅J, I⁆, J⁆ = ⊥ := by
      have h1' : ⁅⁅J, I⁆, J⁆ ≤ ⁅N, J⁆ := Subgroup.commutator_mono_left hJI_le
      have h2' : ⁅N, J⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hJN_eq
      exact le_bot_iff.mp (h1'.trans h2'.le)
    exact CFSG.LocalCores.perfect_double_commutator hJ.1.1 hdc2
  have hcentall : ∀ J : Subgroup X, CFSG.IsComponent J → J ≤ Subgroup.centralizer (I : Set X) := by
    intro J hJ
    by_cases hJ1 : J = K₁
    · rw [hJ1]
      exact Subgroup.le_centralizer_iff.mp hI1
    · by_cases hJ2 : J = K₂
      · rw [hJ2]
        exact Subgroup.le_centralizer_iff.mp hI2'
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hJI J hJ hJ1 hJ2)
  have hFcent : CFSG.fittingSubgroup X ≤ Subgroup.centralizer (CFSG.layer X : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := X))
  have hcL1 : c ∈ CFSG.layer X := CFSG.LocalCores.component_le_layer h2 hc
  have hcL2 : d ∈ CFSG.layer X := CFSG.LocalCores.component_le_layer h1 hd
  have hFCc : ∀ f ∈ CFSG.fittingSubgroup X, f ∈ Subgroup.centralizer ({c} : Set X) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact Subgroup.mem_centralizer_iff.mp (hFcent hf) c hcL1
  have hFCd : ∀ f ∈ CFSG.fittingSubgroup X, f ∈ Subgroup.centralizer ({d} : Set X) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact Subgroup.mem_centralizer_iff.mp (hFcent hf) d hcL2
  have hF_I : ∀ f ∈ CFSG.fittingSubgroup X, ∀ x ∈ I, f * x * f⁻¹ ∈ I := by
    intro f hf x hx
    rw [hI_mem] at hx ⊢
    exact ⟨hPcn f (hFCc f hf) x hx.1, hPdn f (hFCd f hf) x hx.2⟩
  have hIF_inf : I ⊓ CFSG.fittingSubgroup X = ⊥ :=
    compT_inf_eq_bot_of_pow hI2 (fun x hx => compT_pow_eq_one_of_mem_pCore 3 (hF hx))
  have hIF : ∀ i ∈ I, ∀ f ∈ CFSG.fittingSubgroup X, i * f = f * i := by
    intro i hi f hf
    have hz1 : i * f * i⁻¹ * f⁻¹ ∈ CFSG.fittingSubgroup X := by
      have h := (inferInstance : (CFSG.fittingSubgroup X).Normal).conj_mem f hf i
      exact (CFSG.fittingSubgroup X).mul_mem h ((CFSG.fittingSubgroup X).inv_mem hf)
    have hz2 : i * f * i⁻¹ * f⁻¹ ∈ I := by
      rw [show i * f * i⁻¹ * f⁻¹ = i * (f * i⁻¹ * f⁻¹) by simp only [mul_assoc]]
      exact I.mul_mem hi (hF_I f hf i⁻¹ (I.inv_mem hi))
    have hz : i * f * i⁻¹ * f⁻¹ ∈ I ⊓ CFSG.fittingSubgroup X :=
      Subgroup.mem_inf.mpr ⟨hz2, hz1⟩
    rw [hIF_inf, Subgroup.mem_bot] at hz
    have hcomm1 : ⁅i, f⁆ = 1 := by
      rw [commutatorElement_def]
      exact hz
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm1
  have hI_cent_F : I ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (hIF i hi f hf).symm
  have hF_cent_I : CFSG.fittingSubgroup X ≤ Subgroup.centralizer (I : Set X) :=
    Subgroup.le_centralizer_iff.mp hI_cent_F
  have hL_cent_I : CFSG.layer X ≤ Subgroup.centralizer (I : Set X) := by
    rw [CFSG.layer.eq_sSup X]
    exact sSup_le fun J hJ => hcentall J hJ
  have hM_cent_I : CFSG.generalizedFitting X ≤ Subgroup.centralizer (I : Set X) := by
    rw [CFSG.generalizedFitting.eq_sup X]
    exact sup_le hF_cent_I hL_cent_I
  have hI_cent_M : I ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) :=
    Subgroup.le_centralizer_iff.mpr hM_cent_I
  have hIM : I ≤ CFSG.generalizedFitting X :=
    hI_cent_M.trans (CFSG.centralizer_generalizedFitting_le X)
  exact compT_eq_bot_of_two_central (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
    hIM (fun i hi m hm => Subgroup.mem_centralizer_iff.mp (hI_cent_M hi) m hm) hI2 hO2

theorem pCore_two_centralizers_inf_eq_bot {X : Type*} [Group X] [Finite X]
    (hθ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X = ⊥)
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥) {c d : X} (hd : d ∈ K₁)
    (hc : c ∈ K₂) (hd3 : orderOf d = 3) (hc3 : orderOf c = 3) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X)) ⊓
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({d} : Set X)) = ⊥ := by
  have hO2 : CFSG.pCore 2 X = ⊥ := compT_pCore_eq_bot_of_theta hθ Nat.prime_two (by norm_num)
  have hF : CFSG.fittingSubgroup X ≤ CFSG.pCore 3 X := compT_fitting_le_pCore_three hθ
  have hPc1 := pCore_two_centralizer_le_centralizer_of_component h1 h2 hne hZ1 hd hc hd3
  have hPd2 := pCore_two_centralizer_le_centralizer_of_component h2 h1 hne.symm hZ2 hc hd hc3
  exact compT_main hO2 hF h1 h2 hne hd hc
    (fun x hx => compT_pow_eq_one_of_mem_inSubgroup 2 hx)
    (fun g hg x hx => compT_conj_mem_inSubgroup_pCore 2 hg hx)
    (fun g hg x hx => compT_conj_mem_inSubgroup_pCore 2 hg hx)
    hPc1 hPd2

end CFSG.RankThree.PartTwo.Sec11

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem pairJ_orderOf_zpow {X : Type*} [Group X] {x : X} (hx : orderOf x = 3) {j : ℤ}
    (hj : ¬ (3 : ℤ) ∣ j) : orderOf (x ^ j) = 3 := by
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have h3 : (x ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  apply orderOf_eq_prime h3
  intro h1
  apply hj
  have hd : (orderOf x : ℤ) ∣ j := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hx] at hd
  exact_mod_cast hd

theorem pairJ_centralizer_zpow_le {X : Type*} [Group X] {x : X} (hx : orderOf x = 3) {j : ℤ}
    (hj : ¬ (3 : ℤ) ∣ j) :
    Subgroup.centralizer ({x ^ j} : Set X) ≤ Subgroup.centralizer ({x} : Set X) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (j * m) % 3 = 1 := by
    rcases (by omega : j % 3 = 1 ∨ j % 3 = 2) with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  have hxm : (x ^ j) ^ m = x := by
    have h1 : (j * m) % (orderOf x : ℤ) = 1 := by
      rw [hx]
      exact hm
    have h := zpow_mod_orderOf x (j * m)
    rw [h1, zpow_one] at h
    rw [← zpow_mul]
    exact h.symm
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  have hc2 : Commute g ((x ^ j) ^ m) :=
    Commute.zpow_right (show Commute g (x ^ j) from hg) m
  rw [hxm] at hc2
  exact hc2.eq

theorem pairJ_closure_pair {X : Type*} [Group X] {c d : X} (hcd : Commute c d) {b : X}
    (hb : b ∈ Subgroup.closure ({c, d} : Set X)) : ∃ j k : ℤ, b = c ^ j * d ^ k := by
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨j₁, k₁, rfl⟩ := ihx
    obtain ⟨j₂, k₂, rfl⟩ := ihy
    refine ⟨j₁ + j₂, k₁ + k₂, ?_⟩
    have hc : Commute (c ^ j₂) (d ^ k₁) := hcd.zpow_zpow j₂ k₁
    calc c ^ j₁ * d ^ k₁ * (c ^ j₂ * d ^ k₂)
        = c ^ j₁ * (d ^ k₁ * c ^ j₂) * d ^ k₂ := by simp only [mul_assoc]
      _ = c ^ j₁ * (c ^ j₂ * d ^ k₁) * d ^ k₂ := by rw [hc.eq]
      _ = c ^ (j₁ + j₂) * d ^ (k₁ + k₂) := by
          rw [zpow_add, zpow_add]
          simp only [mul_assoc]
  | inv x _ ih =>
    obtain ⟨j, k, rfl⟩ := ih
    refine ⟨-j, -k, ?_⟩
    have hc : Commute (c ^ (-j)) (d ^ (-k)) := hcd.zpow_zpow (-j) (-k)
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact hc.eq.symm

theorem pCore_two_centralizer_le_pair {X : Type*} [Group X] [Finite X]
    {K₁ K₂ : Subgroup X} (h1 : CFSG.IsComponent K₁) (h2 : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center K₁ = ⊥) (hZ2 : Subgroup.center K₂ = ⊥) {c d : X} (hd : d ∈ K₁)
    (hc : c ∈ K₂) (hd3 : orderOf d = 3) (hc3 : orderOf c = 3) {b : X}
    (hb : b ∈ Subgroup.closure ({c, d} : Set X)) (hb1 : b ≠ 1) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X)) ≤
      Subgroup.centralizer ({c} : Set X) ⊓ Subgroup.centralizer ({d} : Set X) := by
  have hbot : ⁅K₁, K₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute h1 h2).resolve_left hne
  have hcd : c * d = d * c :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hd) c hc
  have hcomm : Commute c d := hcd
  obtain ⟨j, k, rfl⟩ := pairJ_closure_pair hcomm hb
  have hcj1 : (3 : ℤ) ∣ j → c ^ j = 1 := fun h => by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hc3]
    exact_mod_cast h
  have hdk1 : (3 : ℤ) ∣ k → d ^ k = 1 := fun h => by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hd3]
    exact_mod_cast h
  have hcjK : c ^ j ∈ K₂ := K₂.zpow_mem hc j
  have hdkK : d ^ k ∈ K₁ := K₁.zpow_mem hd k
  by_cases hj : (3 : ℤ) ∣ j
  · by_cases hk : (3 : ℤ) ∣ k
    · exfalso
      apply hb1
      rw [hcj1 hj, hdk1 hk, one_mul]
    ·
      rw [hcj1 hj, one_mul]
      have hA := pCore_two_centralizer_le_centralizer_of_component h2 h1 hne.symm hZ2 hc hdkK hc3
      refine le_inf (hA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc))) ?_
      exact (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2
        (Subgroup.centralizer ({d ^ k} : Set X))).trans (pairJ_centralizer_zpow_le hd3 hk)
  · by_cases hk : (3 : ℤ) ∣ k
    ·
      rw [hdk1 hk, mul_one]
      have hA := pCore_two_centralizer_le_centralizer_of_component h1 h2 hne hZ1 hd hcjK hd3
      refine le_inf ?_ (hA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd)))
      exact (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2
        (Subgroup.centralizer ({c ^ j} : Set X))).trans (pairJ_centralizer_zpow_le hc3 hj)
    ·
      have hcj3 : orderOf (c ^ j) = 3 := pairJ_orderOf_zpow hc3 hj
      have hdk3 : orderOf (d ^ k) = 3 := pairJ_orderOf_zpow hd3 hk
      have hM := pCore_two_centralizer_mul_le h1 h2 hne hZ1 hZ2 hdkK hcjK hdk3 hcj3
      have hL : Subgroup.centralizer ({c ^ j} : Set X) ≤ Subgroup.centralizer ({c} : Set X) :=
        pairJ_centralizer_zpow_le hc3 hj
      have hR : Subgroup.centralizer ({d ^ k} : Set X) ≤ Subgroup.centralizer ({d} : Set X) :=
        pairJ_centralizer_zpow_le hd3 hk
      exact hM.trans (le_inf (inf_le_left.trans hL) (inf_le_right.trans hR))

end CFSG.RankThree.PartTwo.Sec11
