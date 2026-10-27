module

public import CFSG.Quasithin.EmptyFaithful.S143RB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

section Abstract

variable {C : Type*} [CommGroup C]

theorem zpow_two_mul_eq {d z : C} (hd : d * d = z) (m : ℤ) : d ^ (2 * m) = z ^ m := by
  rw [zpow_mul, zpow_two, hd]

theorem zpow_two_mul_add_one_eq {d z : C} (hd : d * d = z) (m : ℤ) : d ^ (2 * m + 1) = z ^ m * d := by
  rw [zpow_add_one, zpow_two_mul_eq hd]

theorem zpow_sq_eq_one {z : C} (hz : z * z = 1) (m : ℤ) : (z ^ m) * (z ^ m) = 1 := by
  rw [← mul_zpow, hz, one_zpow]

theorem invol_cases_of_comm {d d₁ d₂ z a : C} (hd : d * d = z) (hd₁ : d₁ * d₁ = a)
    (hd₂ : d₂ * d₂ = z * a) (hz : z * z = 1) (ha : a * a = 1) (hz1 : z ≠ 1) (ha1 : a ≠ 1)
    (hza : z ≠ a) (i j k : ℤ)
    (h : (d ^ i * d₁ ^ j * d₂ ^ k) * (d ^ i * d₁ ^ j * d₂ ^ k) = 1) :
    ∃ p q : ℤ, (d ^ i * d₁ ^ j * d₂ ^ k = z ^ p * a ^ q) ∨
      (d ^ i * d₁ ^ j * d₂ ^ k = d * d₁ * d₂ * (z ^ p * a ^ q)) := by
  have hza1 : z * a ≠ 1 := by
    intro h1
    apply hza
    have : z = a⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (inv_eq_of_mul_eq_one_right ha)
  have hsq : ∀ m : ℤ, (z ^ m) * (z ^ m) = 1 := zpow_sq_eq_one hz
  have hsq' : ∀ m : ℤ, (a ^ m) * (a ^ m) = 1 := zpow_sq_eq_one ha
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' i <;> obtain ⟨n, hn | hn⟩ := Int.even_or_odd' j <;>
    obtain ⟨r, hr | hr⟩ := Int.even_or_odd' k
  ·
    subst hm hn hr
    refine ⟨m + r, n + r, Or.inl ?_⟩
    rw [zpow_two_mul_eq hd, zpow_two_mul_eq hd₁, zpow_mul d₂ 2 r, zpow_two, hd₂, mul_zpow,
      zpow_add, zpow_add]
    simp only [mul_assoc, mul_left_comm]
  ·
    exfalso
    subst hm hn hr
    rw [zpow_two_mul_eq hd, zpow_two_mul_eq hd₁, zpow_two_mul_add_one_eq hd₂] at h
    have e : (z ^ m * a ^ n * ((z * a) ^ r * d₂)) * (z ^ m * a ^ n * ((z * a) ^ r * d₂)) =
        ((z ^ m) * (z ^ m)) * ((a ^ n) * (a ^ n)) * (((z * a) ^ r) * ((z * a) ^ r)) * (d₂ * d₂) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [e, hsq, hsq', hd₂] at h
    have hsq2 : ((z * a) ^ r) * ((z * a) ^ r) = 1 := by
      rw [← mul_zpow, mul_mul_mul_comm, hz, ha, one_mul, one_zpow]
    rw [hsq2] at h
    simp at h
    exact hza1 h
  ·
    exfalso
    subst hm hn hr
    rw [zpow_two_mul_eq hd, zpow_two_mul_add_one_eq hd₁, zpow_two_mul_eq hd₂] at h
    have e : (z ^ m * (a ^ n * d₁) * (z * a) ^ r) * (z ^ m * (a ^ n * d₁) * (z * a) ^ r) =
        ((z ^ m) * (z ^ m)) * ((a ^ n) * (a ^ n)) * (((z * a) ^ r) * ((z * a) ^ r)) * (d₁ * d₁) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hsq2 : ((z * a) ^ r) * ((z * a) ^ r) = 1 := by
      rw [← mul_zpow, mul_mul_mul_comm, hz, ha, one_mul, one_zpow]
    rw [e, hsq, hsq', hsq2, hd₁] at h
    simp at h
    exact ha1 h
  ·
    exfalso
    subst hm hn hr
    rw [zpow_two_mul_eq hd, zpow_two_mul_add_one_eq hd₁, zpow_two_mul_add_one_eq hd₂] at h
    have e : (z ^ m * (a ^ n * d₁) * ((z * a) ^ r * d₂)) * (z ^ m * (a ^ n * d₁) * ((z * a) ^ r * d₂)) =
        ((z ^ m) * (z ^ m)) * ((a ^ n) * (a ^ n)) * (((z * a) ^ r) * ((z * a) ^ r)) *
          ((d₁ * d₁) * (d₂ * d₂)) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hsq2 : ((z * a) ^ r) * ((z * a) ^ r) = 1 := by
      rw [← mul_zpow, mul_mul_mul_comm, hz, ha, one_mul, one_zpow]
    rw [e, hsq, hsq', hsq2, hd₁, hd₂] at h
    have : a * (z * a) = z := by
      calc a * (z * a) = z * (a * a) := by simp only [mul_left_comm]
        _ = z := by rw [ha, mul_one]
    simp [this] at h
    exact hz1 h
  ·
    exfalso
    subst hm hn hr
    rw [zpow_two_mul_add_one_eq hd, zpow_two_mul_eq hd₁, zpow_two_mul_eq hd₂] at h
    have e : (z ^ m * d * a ^ n * (z * a) ^ r) * (z ^ m * d * a ^ n * (z * a) ^ r) =
        ((z ^ m) * (z ^ m)) * ((a ^ n) * (a ^ n)) * (((z * a) ^ r) * ((z * a) ^ r)) * (d * d) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hsq2 : ((z * a) ^ r) * ((z * a) ^ r) = 1 := by
      rw [← mul_zpow, mul_mul_mul_comm, hz, ha, one_mul, one_zpow]
    rw [e, hsq, hsq', hsq2, hd] at h
    simp at h
    exact hz1 h
  ·
    exfalso
    subst hm hn hr
    rw [zpow_two_mul_add_one_eq hd, zpow_two_mul_eq hd₁, zpow_two_mul_add_one_eq hd₂] at h
    have e : (z ^ m * d * a ^ n * ((z * a) ^ r * d₂)) * (z ^ m * d * a ^ n * ((z * a) ^ r * d₂)) =
        ((z ^ m) * (z ^ m)) * ((a ^ n) * (a ^ n)) * (((z * a) ^ r) * ((z * a) ^ r)) *
          ((d * d) * (d₂ * d₂)) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hsq2 : ((z * a) ^ r) * ((z * a) ^ r) = 1 := by
      rw [← mul_zpow, mul_mul_mul_comm, hz, ha, one_mul, one_zpow]
    rw [e, hsq, hsq', hsq2, hd, hd₂] at h
    have : z * (z * a) = a := by
      calc z * (z * a) = (z * z) * a := by simp only [mul_assoc]
        _ = a := by rw [hz, one_mul]
    simp [this] at h
    exact ha1 h
  ·
    exfalso
    subst hm hn hr
    rw [zpow_two_mul_add_one_eq hd, zpow_two_mul_add_one_eq hd₁, zpow_two_mul_eq hd₂] at h
    have e : (z ^ m * d * (a ^ n * d₁) * (z * a) ^ r) * (z ^ m * d * (a ^ n * d₁) * (z * a) ^ r) =
        ((z ^ m) * (z ^ m)) * ((a ^ n) * (a ^ n)) * (((z * a) ^ r) * ((z * a) ^ r)) *
          ((d * d) * (d₁ * d₁)) := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hsq2 : ((z * a) ^ r) * ((z * a) ^ r) = 1 := by
      rw [← mul_zpow, mul_mul_mul_comm, hz, ha, one_mul, one_zpow]
    rw [e, hsq, hsq', hsq2, hd, hd₁] at h
    simp at h
    exact hza1 h
  ·
    subst hm hn hr
    refine ⟨m + r, n + r, Or.inr ?_⟩
    rw [zpow_two_mul_add_one_eq hd, zpow_two_mul_add_one_eq hd₁, zpow_two_mul_add_one_eq hd₂,
      mul_zpow, zpow_add, zpow_add]
    simp only [mul_assoc, mul_comm, mul_left_comm]

end Abstract

section Gen

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_of_commute {a b : G} (h : a * b = b * a) {ξ : G}
    (hξ : ξ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : ∃ i j : ℤ, ξ = a ^ i * b ^ j := by
  have hb : b ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (show Commute a b from h) k).eq)
  have hN : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    (Subgroup.zpowers_le.mpr hb).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨n, hn, y, hy, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hN).1 hξ
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨i, j, rfl⟩

theorem zpowers_le_normalizer_sup_of_commute {a b c : G} (hac : a * c = c * a) (hbc : b * c = c * b) :
    Subgroup.zpowers c ≤
      Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  have hN : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh; subst hh; exact hac.symm
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh; subst hh; exact hbc.symm
  have hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun n hn => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hN hn) c rfl).symm
  exact (Subgroup.zpowers_le.mpr hc).trans (Subgroup.centralizer_le_normalizer _)

end Gen

section XStruct

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {d : G} (hD : dOf T M = Subgroup.zpowers d) (hd4 : orderOf d = 4)
  {x : G} (hxL : x ∈ yOfL22 T M) (hx3 : orderOf x = 3)

include c hD hd4 hxL hx3 in
theorem delta_cases_x {R : Subgroup G} (hR : R ∈ Delta ⊤ (dOf T M) T) :
    R = dOf T M ∨ R = conjSubgroup (dOf T M) x⁻¹ ∨ R = conjSubgroup (dOf T M) (x⁻¹ * x⁻¹) := by
  obtain ⟨l, hlL, rfl⟩ := delta_eq_conj c hD hd4 hR
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hz1 : d * d ≠ 1 := (dd_facts hd4).2
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hnorm : ∀ y : G, y * (d * d) * y⁻¹ = d * d → conjSubgroup (dOf T M) y = dOf T M := by
    intro y hy
    rw [hD]
    exact conjugate_eq_iff_mem_normalizer.mpr (mem_normalizer_zpowers_of_comm c hD hd4 hy)
  have hlV : l⁻¹ * (d * d) * l ∈ VZ T M := by
    have hl' : l⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      c.h1281.LT_le_normalizer_VZ (Subgroup.mem_sup_left ((yOfL22 T M).inv_mem hlL))
    have := (Subgroup.mem_normalizer_iff.mp hl' (d * d)).mp
      (Hyp1281Two.omegaOneCenter_le_VZ T M hzZ)
    simpa using this
  rcases hall _ hlV with h1 | h1 | h1 | h1
  · exfalso
    apply hz1
    calc d * d = l * (l⁻¹ * (d * d) * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · left
    exact hnorm l (by
      calc l * (d * d) * l⁻¹ = l * (l⁻¹ * (d * d) * l) * l⁻¹ := by rw [h1]
        _ = d * d := by group)
  · right; left
    have hy : (l * x) * (d * d) * (l * x)⁻¹ = d * d := by
      calc (l * x) * (d * d) * (l * x)⁻¹ = l * (x * (d * d) * x⁻¹) * l⁻¹ := by group
        _ = l * a * l⁻¹ := by rw [← ha]
        _ = l * (l⁻¹ * (d * d) * l) * l⁻¹ := by rw [h1]
        _ = d * d := by group
    have hl_eq : l = (l * x) * x⁻¹ := by group
    calc conjSubgroup (dOf T M) l = conjSubgroup (dOf T M) ((l * x) * x⁻¹) := by rw [← hl_eq]
      _ = conjSubgroup (conjSubgroup (dOf T M) (l * x)) x⁻¹ := (conjugate_conjugate _ _ _).symm
      _ = conjSubgroup (dOf T M) x⁻¹ := by rw [hnorm _ hy]
  · right; right
    have hy : (l * x * x) * (d * d) * (l * x * x)⁻¹ = d * d := by
      calc (l * x * x) * (d * d) * (l * x * x)⁻¹
          = l * (x * (x * (d * d) * x⁻¹) * x⁻¹) * l⁻¹ := by group
        _ = l * (x * a * x⁻¹) * l⁻¹ := by rw [← ha]
        _ = l * ((d * d) * a) * l⁻¹ := by rw [hxa]
        _ = l * (l⁻¹ * (d * d) * l) * l⁻¹ := by rw [h1]
        _ = d * d := by group
    have hl_eq : l = (l * x * x) * (x⁻¹ * x⁻¹) := by group
    calc conjSubgroup (dOf T M) l = conjSubgroup (dOf T M) ((l * x * x) * (x⁻¹ * x⁻¹)) := by
          rw [← hl_eq]
      _ = conjSubgroup (conjSubgroup (dOf T M) (l * x * x)) (x⁻¹ * x⁻¹) :=
          (conjugate_conjugate _ _ _).symm
      _ = conjSubgroup (dOf T M) (x⁻¹ * x⁻¹) := by rw [hnorm _ hy]

include c hD hd4 hxL hx3 in
theorem Xgen_le_sup : Xgen T M ≤ Subgroup.zpowers d ⊔ Subgroup.zpowers (x * d * x⁻¹) ⊔
    Subgroup.zpowers (x * (x * d * x⁻¹) * x⁻¹) := by
  apply Wgen_le_of_le
  intro R hR
  rcases delta_cases_x c hD hd4 hxL hx3 hR with rfl | rfl | rfl
  · rw [hD]; exact le_sup_left.trans le_sup_left
  · intro w hw
    have h1 : x⁻¹ * w * x⁻¹⁻¹ ∈ dOf T M := mem_conjSubgroup_iff.mp hw
    rw [hD] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hw' : w = (x * d * x⁻¹) ^ k := by rw [conj_zpow, hk]; group
    rw [hw']
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k))
  · intro w hw
    have h1 : (x⁻¹ * x⁻¹) * w * (x⁻¹ * x⁻¹)⁻¹ ∈ dOf T M := mem_conjSubgroup_iff.mp hw
    rw [hD] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hw' : w = (x * (x * d * x⁻¹) * x⁻¹) ^ k := by
      rw [conj_zpow, conj_zpow, hk]; group
    rw [hw']
    exact Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k)

include c hD hd4 hxL hx3 in
theorem mem_Xgen_prod {ξ : G} (hξ : ξ ∈ Xgen T M) :
    ∃ i j k : ℤ, ξ = d ^ i * (x * d * x⁻¹) ^ j * (x * (x * d * x⁻¹) * x⁻¹) ^ k := by
  have hξ' := Xgen_le_sup c hD hd4 hxL hx3 hξ
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hc := Xgen_comm c hD hd4
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  have h1 := d1_mem_Xgen c hxL hd
  have h2 := d2_mem_Xgen c hxL hd
  have hN := zpowers_le_normalizer_sup_of_commute (hc _ h0 _ h2) (hc _ h1 _ h2)
  obtain ⟨n, hn, y, hy, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hN).1 hξ'
  obtain ⟨i, j, rfl⟩ := mem_sup_zpowers_of_commute (hc _ h0 _ h1) hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨i, j, k, rfl⟩

include c hD hd4 hxL hx3 in
theorem Xgen_invol {ξ : G} (hξ : ξ ∈ Xgen T M) (h2 : ξ * ξ = 1) :
    ξ ∈ VZ T M ∨ ∃ v ∈ VZ T M, ξ = wOfX d x * v := by
  obtain ⟨i, j, k, rfl⟩ := mem_Xgen_prod c hD hd4 hxL hx3 hξ
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x c hD hd4 hxL hx3
  have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
  have hc := Xgen_comm c hD hd4
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta c) hd
  have h1 := d1_mem_Xgen c hxL hd
  have h2' := d2_mem_Xgen c hxL hd
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hzV : d * d ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hzZ
  have hzX : d * d ∈ Xgen T M := (Xgen T M).mul_mem h0 h0
  have haX : a ∈ Xgen T M := VZ_le_Xgen c haV
  let _ : CommGroup ↥(Xgen T M) :=
    { (inferInstance : Group ↥(Xgen T M)) with
      mul_comm := fun u v => Subtype.ext (Xgen_comm c hD hd4 u u.2 v v.2) }
  have e1 : (x * d * x⁻¹) * (x * d * x⁻¹) = a := by rw [ha]; group
  have e2 : (x * (x * d * x⁻¹) * x⁻¹) * (x * (x * d * x⁻¹) * x⁻¹) = (d * d) * a := by
    rw [← hxa, ← e1]; group
  obtain ⟨p, q, hpq⟩ := invol_cases_of_comm
    (d := (⟨d, h0⟩ : ↥(Xgen T M))) (d₁ := ⟨x * d * x⁻¹, h1⟩) (d₂ := ⟨x * (x * d * x⁻¹) * x⁻¹, h2'⟩)
    (z := ⟨d * d, hzX⟩) (a := ⟨a, haX⟩)
    (Subtype.ext rfl) (Subtype.ext e1) (Subtype.ext e2)
    (Subtype.ext (dd_facts hd4).1) (Subtype.ext haa)
    (fun h => (dd_facts hd4).2 (congrArg Subtype.val h))
    (fun h => haZ (by
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      rw [this]; exact (quasithinOmegaOneCenter T).one_mem))
    (fun h => haZ (by
      have := congrArg Subtype.val h
      simp only at this
      rw [← this]; exact hzZ))
    i j k (Subtype.ext (by simpa using h2))
  have hv : ∀ P Q : ℤ, (d * d) ^ P * a ^ Q ∈ VZ T M := fun P Q =>
    (VZ T M).mul_mem (Subgroup.zpow_mem _ hzV P) (Subgroup.zpow_mem _ haV Q)
  rcases hpq with h | h
  · left
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow] at this
    rw [this]; exact hv p q
  · right
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow] at this
    exact ⟨_, hv p q, by rw [this]; rfl⟩

end XStruct

end S143

end CFSG.Quasithin
