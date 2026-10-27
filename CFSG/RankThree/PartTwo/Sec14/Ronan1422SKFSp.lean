module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerChev2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)

theorem kf1422_mem_mul_of_sup {G : Type*} [Group G] {A C : Subgroup G}
    (hAC : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A) {g : G} (hg : g ∈ A ⊔ C) :
    ∃ a ∈ A, ∃ c ∈ C, g = a * c := by
  let T : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ c ∈ C, g = a * c}
      mul_mem' := by
        rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
        exact ⟨a * (c * a' * c⁻¹), A.mul_mem ha (hAC c hc a' ha'), c * c',
          C.mul_mem hc hc', by group⟩
      one_mem' := ⟨1, A.one_mem, 1, C.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        exact ⟨c⁻¹ * a⁻¹ * c⁻¹⁻¹, hAC c⁻¹ (C.inv_mem hc) a⁻¹ (A.inv_mem ha), c⁻¹,
          C.inv_mem hc, by group⟩ }
  have hAT : A ≤ T := fun a ha => ⟨a, ha, 1, C.one_mem, by group⟩
  have hCT : C ≤ T := fun c hc => ⟨1, A.one_mem, c, hc, by group⟩
  obtain ⟨a, ha, c, hc, h⟩ := sup_le hAT hCT hg
  exact ⟨a, ha, c, hc, h⟩

theorem kf1422_conj_mem_inf {Y : Type} [Group Y] {J P : Subgroup Y} (hJ : J.Normal) {g n : Y}
    (hg : g ∈ P) (hn : n ∈ P ⊓ J) : g * n * g⁻¹ ∈ P ⊓ J :=
  Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem hg (Subgroup.mem_inf.1 hn).1) (P.inv_mem hg),
    hJ.conj_mem n (Subgroup.mem_inf.1 hn).2 g⟩

theorem kf1422_cube_mem_inf {Y : Type} [Group Y] {J E P : Subgroup Y}
    (hN9 : ∀ x ∈ P ⊓ J, x ^ 9 = 1) (hNΩ : ∀ x ∈ P ⊓ J, x ^ 3 = 1 → x ∈ E) {n : Y}
    (hn : n ∈ P ⊓ J) : n ^ 3 ∈ E ⊓ J := by
  have h3 : n ^ 3 ∈ P ⊓ J := (P ⊓ J).pow_mem hn 3
  have h9 : (n ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    exact hN9 n hn
  exact Subgroup.mem_inf.2 ⟨hNΩ _ h3 h9, (Subgroup.mem_inf.1 h3).2⟩

theorem kf1422_conj_div_mem {Y : Type} [Group Y] {J E P : Subgroup Y} (hJ : J.Normal)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEe : ∀ a ∈ E, a ^ 3 = 1) (hEP : E ≤ P)
    (hNc : ∀ x ∈ P ⊓ J, ∀ y ∈ P ⊓ J, x * y = y * x)
    (hN9 : ∀ x ∈ P ⊓ J, x ^ 9 = 1) (hNΩ : ∀ x ∈ P ⊓ J, x ^ 3 = 1 → x ∈ E) {f n : Y}
    (hf : f ∈ E) (hn : n ∈ P ⊓ J) : f * n * f⁻¹ * n⁻¹ ∈ E ⊓ J := by
  have hu : f * n * f⁻¹ ∈ P ⊓ J := kf1422_conj_mem_inf hJ (hEP hf) hn
  have hv : n⁻¹ ∈ P ⊓ J := (P ⊓ J).inv_mem hn
  have hcomm : Commute (f * n * f⁻¹) n⁻¹ := hNc _ hu _ hv
  have hn3 : n ^ 3 ∈ E := (Subgroup.mem_inf.1 (kf1422_cube_mem_inf hN9 hNΩ hn)).1
  have hfn3 : f * n ^ 3 * f⁻¹ = n ^ 3 := by
    rw [hEc f hf _ hn3]
    group
  have ha3 : (f * n * f⁻¹ * n⁻¹) ^ 3 = 1 := by
    rw [hcomm.mul_pow, conj_pow, hfn3, inv_pow, mul_inv_cancel]
  have haP : f * n * f⁻¹ * n⁻¹ ∈ P ⊓ J := (P ⊓ J).mul_mem hu hv
  exact Subgroup.mem_inf.2 ⟨hNΩ _ haP ha3, (Subgroup.mem_inf.1 haP).2⟩

theorem kf1422_cube_formula {G : Type*} [Group G] {a n : G} (hc : Commute a n) :
    n * (a * n) * (a * a * n) = n * n * n * (a * a * a) := by
  have hc2 : Commute (a * a) n := hc.mul_left hc
  calc n * (a * n) * (a * a * n) = n * (n * a) * (n * (a * a)) := by
        rw [hc.eq, hc2.eq]
    _ = n * (n * (a * (n * (a * a)))) := by simp only [mul_assoc]
    _ = n * (n * (n * (a * (a * a)))) := by rw [hc.left_comm]
    _ = n * n * n * (a * a * a) := by simp only [mul_assoc]

theorem kf1422_sup_eq_of_card {Y : Type} [Group Y] [Finite Y] {J E P : Subgroup Y}
    (hE27 : Nat.card E = 27) (hEJ : Nat.card (E ⊓ J : Subgroup Y) = 9) (hEP : E ≤ P)
    (hP : Nat.card P = 243) (hN81 : Nat.card (P ⊓ J : Subgroup Y) = 81) :
    (P ⊓ J) ⊔ E = P := by
  have hle : (P ⊓ J) ⊔ E ≤ P := sup_le inf_le_left hEP
  have hd1 : Nat.card ((P ⊓ J) ⊔ E : Subgroup Y) ∣ 243 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hP] at h
  have hd2 : 81 ∣ Nat.card ((P ⊓ J) ⊔ E : Subgroup Y) := by
    have h := Subgroup.card_dvd_of_le (le_sup_left : P ⊓ J ≤ (P ⊓ J) ⊔ E)
    rwa [hN81] at h
  have hne : Nat.card ((P ⊓ J) ⊔ E : Subgroup Y) ≠ 81 := by
    intro h81
    have heq : P ⊓ J = (P ⊓ J) ⊔ E :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : P ⊓ J ≤ (P ⊓ J) ⊔ E) (by omega)
    have hEN : E ≤ P ⊓ J := by
      rw [heq]
      exact le_sup_right
    have hEJ' : E ⊓ J = E := inf_eq_left.2 (fun y hy => (Subgroup.mem_inf.1 (hEN hy)).2)
    rw [hEJ'] at hEJ
    omega
  have hle243 : Nat.card ((P ⊓ J) ⊔ E : Subgroup Y) ≤ 243 := Nat.le_of_dvd (by norm_num) hd1
  have h243 : Nat.card ((P ⊓ J) ⊔ E : Subgroup Y) = 243 := by
    obtain ⟨t, ht⟩ := hd2
    have ht3 : t ≤ 3 := by omega
    interval_cases t <;> first | omega | (rw [ht] at hd1; norm_num at hd1)
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem kf1422_covering {Y : Type} [Group Y] [Finite Y] {J E : Subgroup Y}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEe : ∀ a ∈ E, a ^ 3 = 1)
    (hE27 : Nat.card E = 27) (hEJ : Nat.card (E ⊓ J : Subgroup Y) = 9) {x : Y} (hx : x ∈ E)
    (hxJ : x ∉ J) {y : Y} (hy : y ∈ E) (hyJ : y ∉ J) :
    (∃ b ∈ E ⊓ J, y = b * x) ∨ (∃ b ∈ E ⊓ J, y⁻¹ = b * x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxB : x ∉ E ⊓ J := fun h => hxJ (Subgroup.mem_inf.1 h).2
  have hzE : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.2 hx
  have hHE : (E ⊓ J) ⊔ Subgroup.zpowers x ≤ E := sup_le inf_le_left hzE
  have hdvd : Nat.card ((E ⊓ J) ⊔ Subgroup.zpowers x : Subgroup Y) ∣ 27 := by
    have h := Subgroup.card_dvd_of_le hHE
    rwa [hE27] at h
  have hne : Nat.card ((E ⊓ J) ⊔ Subgroup.zpowers x : Subgroup Y) ≠ 9 := by
    intro h9
    have heq : E ⊓ J = (E ⊓ J) ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : E ⊓ J ≤ (E ⊓ J) ⊔ Subgroup.zpowers x)
        (by omega)
    apply hxB
    rw [heq]
    exact (le_sup_right : Subgroup.zpowers x ≤ (E ⊓ J) ⊔ Subgroup.zpowers x)
      (Subgroup.mem_zpowers x)
  have hle9 : 9 ≤ Nat.card ((E ⊓ J) ⊔ Subgroup.zpowers x : Subgroup Y) := by
    have h := Subgroup.card_le_of_le (le_sup_left : E ⊓ J ≤ (E ⊓ J) ⊔ Subgroup.zpowers x)
    omega
  have h27 : Nat.card ((E ⊓ J) ⊔ Subgroup.zpowers x : Subgroup Y) = 27 := by
    generalize Nat.card ((E ⊓ J) ⊔ Subgroup.zpowers x : Subgroup Y) = c at hdvd hle9 hne ⊢
    have hc27 : c ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases c <;> omega
  have hH : (E ⊓ J) ⊔ Subgroup.zpowers x = E :=
    Subgroup.eq_of_le_of_card_ge hHE (by omega)
  have hnorm : ∀ c ∈ Subgroup.zpowers x, ∀ a ∈ E ⊓ J, c * a * c⁻¹ ∈ E ⊓ J := by
    intro c hc a ha
    have hcE : c ∈ E := hzE hc
    have hcomm : c * a = a * c := hEc c hcE a (Subgroup.mem_inf.1 ha).1
    have hca : c * a * c⁻¹ = a := by
      rw [hcomm]
      group
    rw [hca]
    exact ha
  have hyH : y ∈ (E ⊓ J) ⊔ Subgroup.zpowers x := by
    rw [hH]
    exact hy
  obtain ⟨b, hb, c, hc, rfl⟩ := kf1422_mem_mul_of_sup hnorm hyH
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hx1 : x ≠ 1 := fun h => hxJ (by rw [h]; exact J.one_mem)
  have hord : orderOf x = 3 := orderOf_eq_prime (hEe x hx) hx1
  have hm : x ^ m = x ^ (m % 3) := by
    have h := zpow_mod_orderOf x m
    rw [hord] at h
    simpa using h.symm
  have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · exfalso
    apply hyJ
    have hxm : x ^ m = 1 := by rw [hm, h0, zpow_zero]
    rw [hxm, mul_one]
    exact (Subgroup.mem_inf.1 hb).2
  · left
    refine ⟨b, hb, ?_⟩
    rw [hm, h1, zpow_one]
  · right
    refine ⟨b⁻¹, (E ⊓ J).inv_mem hb, ?_⟩
    have hxm : x ^ m = x ^ (2 : ℤ) := by rw [hm, h2]
    have h3 : x * x * x = 1 := by
      rw [← pow_three']
      exact hEe x hx
    have hx2 : (x * x)⁻¹ = x := inv_eq_of_mul_eq_one_right h3
    rw [hxm, zpow_two, mul_inv_rev, hx2]
    exact hEc x hx b⁻¹ (E.inv_mem (Subgroup.mem_inf.1 hb).1)

theorem kf1422_orbit_surj {Y : Type} [Group Y] [Finite Y] {J E P : Subgroup Y} (hJ : J.Normal)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEe : ∀ a ∈ E, a ^ 3 = 1) (hEP : E ≤ P)
    (hEJ : Nat.card (E ⊓ J : Subgroup Y) = 9) (hN81 : Nat.card (P ⊓ J : Subgroup Y) = 81)
    (hNc : ∀ x ∈ P ⊓ J, ∀ y ∈ P ⊓ J, x * y = y * x)
    (hN9 : ∀ x ∈ P ⊓ J, x ^ 9 = 1) (hNΩ : ∀ x ∈ P ⊓ J, x ^ 3 = 1 → x ∈ E)
    (hC : ∀ f ∈ E, f ∉ J → ∀ x ∈ P ⊓ J, f * x = x * f → x ∈ E) {x : Y} (hx : x ∈ E)
    (hxJ : x ∉ J) : ∀ b ∈ E ⊓ J, ∃ n ∈ P ⊓ J, x * n * x⁻¹ * n⁻¹ = b := by
  have hdiv : ∀ n ∈ P ⊓ J, x * n * x⁻¹ * n⁻¹ ∈ E ⊓ J :=
    fun n hn => kf1422_conj_div_mem hJ hEc hEe hEP hNc hN9 hNΩ hx hn
  have hEJP : E ⊓ J ≤ P ⊓ J := inf_le_inf_right J hEP
  let d : (P ⊓ J : Subgroup Y) →* (E ⊓ J : Subgroup Y) :=
    MonoidHom.mk' (fun n => ⟨x * n.1 * x⁻¹ * n.1⁻¹, hdiv n.1 n.2⟩) (by
      intro m n
      apply Subtype.ext
      have hcm : (x * n.1 * x⁻¹ * n.1⁻¹) * m.1⁻¹ = m.1⁻¹ * (x * n.1 * x⁻¹ * n.1⁻¹) :=
        hNc _ (hEJP (hdiv n.1 n.2)) _ ((P ⊓ J).inv_mem m.2)
      show x * (m.1 * n.1) * x⁻¹ * (m.1 * n.1)⁻¹ =
        (x * m.1 * x⁻¹ * m.1⁻¹) * (x * n.1 * x⁻¹ * n.1⁻¹)
      calc x * (m.1 * n.1) * x⁻¹ * (m.1 * n.1)⁻¹
          = (x * m.1 * x⁻¹) * ((x * n.1 * x⁻¹ * n.1⁻¹) * m.1⁻¹) := by group
        _ = (x * m.1 * x⁻¹) * (m.1⁻¹ * (x * n.1 * x⁻¹ * n.1⁻¹)) := by rw [hcm]
        _ = (x * m.1 * x⁻¹ * m.1⁻¹) * (x * n.1 * x⁻¹ * n.1⁻¹) := by group)
  have hker_eq : d.ker.map (P ⊓ J).subtype = E ⊓ J := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      have h1 : x * n.1 * x⁻¹ * n.1⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hn)
      have h2 : x * n.1 * x⁻¹ = n.1 := mul_inv_eq_one.1 h1
      have h3 : x * n.1 = n.1 * x := by
        calc x * n.1 = (x * n.1 * x⁻¹) * x := by group
          _ = n.1 * x := by rw [h2]
      have hnE : n.1 ∈ E := hC x hx hxJ n.1 n.2 h3
      exact Subgroup.mem_inf.2 ⟨hnE, (Subgroup.mem_inf.1 n.2).2⟩
    · intro hy
      have hyN : y ∈ P ⊓ J := hEJP hy
      refine ⟨⟨y, hyN⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      apply Subtype.ext
      show x * y * x⁻¹ * y⁻¹ = 1
      rw [hEc x hx y (Subgroup.mem_inf.1 hy).1]
      group
  have hker : Nat.card d.ker = 9 := by
    have h := Subgroup.card_map_of_injective (K := d.ker) (f := (P ⊓ J).subtype)
      Subtype.val_injective
    rw [hker_eq, hEJ] at h
    omega
  have hcard := Subgroup.card_ker_mul_card_range d
  rw [hker, hN81] at hcard
  have htop : d.range = ⊤ := Subgroup.eq_top_of_card_eq d.range (by rw [hEJ]; omega)
  have hsurj : Function.Surjective d := MonoidHom.range_eq_top.1 htop
  intro b hb
  obtain ⟨n, hn⟩ := hsurj ⟨b, hb⟩
  refine ⟨n.1, n.2, ?_⟩
  exact congrArg Subtype.val hn

theorem sylow_facts_of_homocyclic {Y : Type} [Group Y] [Finite Y] {J E P : Subgroup Y}
    (hJ : J.Normal)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEJ : Nat.card (E ⊓ J : Subgroup Y) = 9) (hEP : E ≤ P) (hP : Nat.card P = 243)
    (hN81 : Nat.card (P ⊓ J : Subgroup Y) = 81)
    (hNc : ∀ x ∈ P ⊓ J, ∀ y ∈ P ⊓ J, x * y = y * x)
    (hN9 : ∀ x ∈ P ⊓ J, x ^ 9 = 1)
    (hNΩ : ∀ x ∈ P ⊓ J, x ^ 3 = 1 → x ∈ E)
    (hC : ∀ f ∈ E, f ∉ J → ∀ x ∈ P ⊓ J, f * x = x * f → x ∈ E) :
    (∀ x ∈ P, x ^ 3 = 1 → x ∈ E) ∧
      ∀ x ∈ E, x ∉ J → ∀ y ∈ E, y ∉ J →
        ∃ p ∈ P ⊓ J, Subgroup.zpowers (p * x * p⁻¹) = Subgroup.zpowers y := by
  obtain ⟨hEc0, hEe⟩ := hE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEc0.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnorm : ∀ c ∈ E, ∀ a ∈ P ⊓ J, c * a * c⁻¹ ∈ P ⊓ J :=
    fun c hc a ha => kf1422_conj_mem_inf hJ (hEP hc) ha
  have hPNE : (P ⊓ J) ⊔ E = P := kf1422_sup_eq_of_card hE27 hEJ hEP hP hN81
  refine ⟨fun x hx hx3 => ?_, fun x hx hxJ y hy hyJ => ?_⟩
  ·
    have hxNE : x ∈ (P ⊓ J) ⊔ E := by
      rw [hPNE]
      exact hx
    obtain ⟨n, hn, f, hf, rfl⟩ := kf1422_mem_mul_of_sup hnorm hxNE
    obtain ⟨a, ha⟩ : ∃ a, f * n * f⁻¹ * n⁻¹ = a := ⟨_, rfl⟩
    have haB : a ∈ E ⊓ J := ha ▸ kf1422_conj_div_mem hJ hEc hEe hEP hNc hN9 hNΩ hf hn
    have haE : a ∈ E := (Subgroup.mem_inf.1 haB).1
    have haN : a ∈ P ⊓ J := inf_le_inf_right J hEP haB
    have ha3 : a * a * a = 1 := by
      rw [← pow_three']
      exact hEe a haE
    have hfn : f * n * f⁻¹ = a * n := by
      rw [← ha]
      group
    have hfa : f * a * f⁻¹ = a := by
      rw [hEc f hf a haE]
      group
    have hf2n : f * f * n * (f * f)⁻¹ = a * a * n := by
      calc f * f * n * (f * f)⁻¹ = f * (f * n * f⁻¹) * f⁻¹ := by group
        _ = f * (a * n) * f⁻¹ := by rw [hfn]
        _ = (f * a * f⁻¹) * (f * n * f⁻¹) := by group
        _ = a * (a * n) := by rw [hfa, hfn]
        _ = a * a * n := by rw [mul_assoc]
    have hf3 : f * f * f = 1 := by
      rw [← pow_three']
      exact hEe f hf
    have hcube : n * f * (n * f) * (n * f) = n * n * n * (a * a * a) := by
      calc n * f * (n * f) * (n * f)
          = n * (f * n * f⁻¹) * (f * f * n * (f * f)⁻¹) * (f * f * f) := by group
        _ = n * (a * n) * (a * a * n) * (f * f * f) := by rw [hfn, hf2n]
        _ = n * (a * n) * (a * a * n) := by rw [hf3, mul_one]
        _ = n * n * n * (a * a * a) := kf1422_cube_formula (hNc a haN n hn)
    have hn3 : n * n * n = 1 := by
      rw [pow_three', hcube, ha3, mul_one] at hx3
      exact hx3
    exact E.mul_mem (hNΩ n hn (by rw [pow_three']; exact hn3)) hf
  · have hcov := kf1422_covering hEc hEe hE27 hEJ hx hxJ hy hyJ
    have hsurj := kf1422_orbit_surj hJ hEc hEe hEP hEJ hN81 hNc hN9 hNΩ hC hx hxJ
    have key : ∀ b ∈ E ⊓ J, ∃ p ∈ P ⊓ J, p * x * p⁻¹ = b * x := by
      intro b hb
      obtain ⟨n, hn, hnb⟩ := hsurj b hb
      refine ⟨n⁻¹, (P ⊓ J).inv_mem hn, ?_⟩
      have hu : x * n * x⁻¹ ∈ P ⊓ J := kf1422_conj_mem_inf hJ (hEP hx) hn
      have hcomm : (x * n * x⁻¹) * n⁻¹ = n⁻¹ * (x * n * x⁻¹) :=
        hNc _ hu _ ((P ⊓ J).inv_mem hn)
      rw [inv_inv, ← hnb, hcomm]
      group
    rcases hcov with ⟨b, hb, rfl⟩ | ⟨b, hb, hyb⟩
    · obtain ⟨p, hp, hpx⟩ := key b hb
      exact ⟨p, hp, by rw [hpx]⟩
    · obtain ⟨p, hp, hpx⟩ := key b hb
      refine ⟨p, hp, ?_⟩
      rw [hpx, ← hyb, Subgroup.zpowers_inv]

theorem kf1422Sp48_noE27 : ∀ (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* projSp 2 (GaloisField 2 3)) → ∀ E : Subgroup S,
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27 := by
  intro S _ _ hS E hE hcard
  obtain ⟨e⟩ := hS
  have hno : CFSG.RankThree.PartTwo.Sec4.RonanK429.NoE27 S :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429.NoE27.of_mulEquiv e
      (CFSG.RankThree.PartTwo.Sec18.Item185Proof.noE27_projSp_two_two (n := 3))
  exact hno E (by unfold CFSG.RankThree.PartTwo.Late.IsE27; exact ⟨hE, hcard⟩)

theorem kf1422Sp48_center : ∀ (S : Type) [Group S] [Finite S],
    Nonempty (S ≃* projSp 2 (GaloisField 2 3)) → ∀ α β : MulAut S, α ^ 3 = 1 →
      (∀ s : S, α ≠ MulAut.conj s) → β * α * β⁻¹ = α⁻¹ → False := by
  intro S _ _ hS α β hα3 hαc hβ
  obtain ⟨e⟩ := hS
  have hK : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  haveI : CharP (GaloisField 2 3) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num) hK
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (by norm_num) hFr hord hzp
  have hcomm : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (StatedProj (StatedSp 2 (GaloisField 2 3))), a * b = b * a := by
    intro a b
    haveI := hcyc
    exact IsCyclic.commutative.is_comm.comm a b
  set e' := e.trans (CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 2 (GaloisField 2 3))
    with he'
  set q := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (StatedProj (StatedSp 2 (GaloisField 2 3)))) with hq
  have h3 : (MulAut.congr e' α) ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have hq3 : q (MulAut.congr e' α) ^ 3 = 1 := by
    rw [← map_pow, h3, map_one]
  have hg : (q (MulAut.congr e' α))⁻¹ = q (MulAut.congr e' α) := by
    have h1 := congrArg (fun γ => q (MulAut.congr e' γ)) hβ
    simp only [map_mul, map_inv] at h1
    have h2 : q (MulAut.congr e' β) * q (MulAut.congr e' α) * (q (MulAut.congr e' β))⁻¹ =
        q (MulAut.congr e' α) := by
      rw [hcomm (q (MulAut.congr e' β)) (q (MulAut.congr e' α))]
      group
    exact h1.symm.trans h2
  have hg2 : q (MulAut.congr e' α) * q (MulAut.congr e' α) = 1 :=
    mul_eq_one_iff_eq_inv.2 hg.symm
  have hg2' : q (MulAut.congr e' α) ^ 2 = 1 := by
    rw [pow_two]
    exact hg2
  have hg1 : q (MulAut.congr e' α) = 1 := by
    calc q (MulAut.congr e' α)
        = q (MulAut.congr e' α) ^ 3 * (q (MulAut.congr e' α) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hq3, hg2', inv_one, mul_one]
  have hin : MulAut.congr e' α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 (GaloisField 2 3))) := by
    rw [hq, QuotientGroup.mk'_apply] at hg1
    exact (QuotientGroup.eq_one_iff _).1 hg1
  obtain ⟨s, hs⟩ := (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e' α).1 hin
  exact hαc s hs.symm

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
