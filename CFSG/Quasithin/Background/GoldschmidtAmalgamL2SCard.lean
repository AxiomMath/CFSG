module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SGens

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL2S

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem comm_of_card_le_two_mul [Finite D] {C K : Subgroup D} (hCK : C ≤ K)
    (hC : ∀ c ∈ C, ∀ k ∈ K, c * k = k * c) (hcard : Nat.card K ≤ 2 * Nat.card C) {p q : D}
    (hp : p ∈ K) (hq : q ∈ K) : p * q = q * p := by
  by_cases hpC : p ∈ C
  · exact hC p hpC q hq
  · have hCL : C ≤ C ⊔ Subgroup.zpowers p := le_sup_left
    have hLK : C ⊔ Subgroup.zpowers p ≤ K :=
      sup_le hCK (Subgroup.zpowers_le.mpr hp)
    have hne : C ≠ C ⊔ Subgroup.zpowers p := fun e =>
      hpC (e ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers p))
    have hlt : Nat.card C < Nat.card ↥(C ⊔ Subgroup.zpowers p) := by
      by_contra hcon
      push Not at hcon
      exact hne (Subgroup.eq_of_le_of_card_ge hCL hcon)
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hCL
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hm2 : 2 ≤ m := by
      by_contra hcon
      push Not at hcon
      interval_cases m <;> omega
    have hge : 2 * Nat.card C ≤ Nat.card ↥(C ⊔ Subgroup.zpowers p) := by
      rw [hm]; nlinarith
    have hKL : K ≤ C ⊔ Subgroup.zpowers p := by
      refine le_of_eq ?_
      exact (Subgroup.eq_of_le_of_card_ge hLK (by omega)).symm
    have hqL := hKL hq
    have hcen : C ⊔ Subgroup.zpowers p ≤ Subgroup.centralizer ({p} : Set D) := by
      refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (hC c hc y hp).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rfl
    exact (Subgroup.mem_centralizer_iff.mp (hcen hqL) p rfl)

section Centre

variable {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.z_mul_z : z * z = 1 := by
  have := g.hyp.natural.z_sq
  rwa [pow_two] at this

omit g in
theorem conj_of_comm_eq {p q : D} (h : p * q * p⁻¹ * q⁻¹ = z) : p * q * p⁻¹ = z * q := by
  calc p * q * p⁻¹ = (p * q * p⁻¹ * q⁻¹) * q := by group
    _ = z * q := by rw [h]

theorem Gen.comm_symm {p q : D} (h : p * q * p⁻¹ * q⁻¹ = z) : q * p * q⁻¹ * p⁻¹ = z := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right g.z_mul_z
  calc q * p * q⁻¹ * p⁻¹ = (p * q * p⁻¹ * q⁻¹)⁻¹ := by group
    _ = z := by rw [h, hz]

variable [Finite D] in
theorem Gen.c_comm_a : a * a₁ * a₂ * a = a * (a * a₁ * a₂) := by
  have e1 : a * a₁ * a⁻¹ = z * a₁ := conj_of_comm_eq g.comm01_eq
  have e2 : a * a₂ * a⁻¹ = z * a₂ := conj_of_comm_eq (g.comm_symm g.comm20_eq)
  have e3 : a * (a * a₁ * a₂) * a⁻¹ = a * a₁ * a₂ := by
    calc a * (a * a₁ * a₂) * a⁻¹ = (a * a * a⁻¹) * (a * a₁ * a⁻¹) * (a * a₂ * a⁻¹) := by group
      _ = a * (z * a₁) * (z * a₂) := by rw [e1, e2]; group
      _ = a * (z * a₁ * z) * a₂ := by group
      _ = a * (a₁ * z * z) * a₂ := by rw [g.z_comm_a₁]
      _ = a * a₁ * (z * z) * a₂ := by group
      _ = a * a₁ * a₂ := by rw [g.z_mul_z]; group
  calc a * a₁ * a₂ * a = (a * (a * a₁ * a₂) * a⁻¹) * a := by rw [e3]
    _ = a * (a * a₁ * a₂) := by group


variable [Finite D] in
theorem Gen.c_comm_a₁ : a * a₁ * a₂ * a₁ = a₁ * (a * a₁ * a₂) := by
  have e1 : a₁ * a * a₁⁻¹ = z * a := conj_of_comm_eq (g.comm_symm g.comm01_eq)
  have e2 : a₁ * a₂ * a₁⁻¹ = z * a₂ := conj_of_comm_eq g.comm12_eq
  have e3 : a₁ * (a * a₁ * a₂) * a₁⁻¹ = a * a₁ * a₂ := by
    calc a₁ * (a * a₁ * a₂) * a₁⁻¹
        = (a₁ * a * a₁⁻¹) * (a₁ * a₁ * a₁⁻¹) * (a₁ * a₂ * a₁⁻¹) := by group
      _ = (z * a) * a₁ * (z * a₂) := by rw [e1, e2]; group
      _ = z * (a * a₁) * (z * a₂) := by group
      _ = (a * a₁) * z * (z * a₂) := by
          have hc : Commute z (a * a₁) :=
            (show Commute z a from g.z_comm_a).mul_right (show Commute z a₁ from g.z_comm_a₁)
          rw [hc.eq]
      _ = a * a₁ * (z * z) * a₂ := by group
      _ = a * a₁ * a₂ := by rw [g.z_mul_z]; group
  calc a * a₁ * a₂ * a₁ = (a₁ * (a * a₁ * a₂) * a₁⁻¹) * a₁ := by rw [e3]
    _ = a₁ * (a * a₁ * a₂) := by group

variable [Finite D] in
theorem Gen.c_comm_a₂ : a * a₁ * a₂ * a₂ = a₂ * (a * a₁ * a₂) := by
  have e1 : a₂ * a * a₂⁻¹ = z * a := conj_of_comm_eq g.comm20_eq
  have e2 : a₂ * a₁ * a₂⁻¹ = z * a₁ := conj_of_comm_eq (g.comm_symm g.comm12_eq)
  have e3 : a₂ * (a * a₁ * a₂) * a₂⁻¹ = a * a₁ * a₂ := by
    calc a₂ * (a * a₁ * a₂) * a₂⁻¹
        = (a₂ * a * a₂⁻¹) * (a₂ * a₁ * a₂⁻¹) * (a₂ * a₂ * a₂⁻¹) := by group
      _ = (z * a) * (z * a₁) * a₂ := by rw [e1, e2]; group
      _ = z * (a * z) * a₁ * a₂ := by group
      _ = z * (z * a) * a₁ * a₂ := by rw [← g.z_comm_a]
      _ = (z * z) * a * a₁ * a₂ := by group
      _ = a * a₁ * a₂ := by rw [g.z_mul_z]; group
  calc a * a₁ * a₂ * a₂ = (a₂ * (a * a₁ * a₂) * a₂⁻¹) * a₂ := by rw [e3]
    _ = a₂ * (a * a₁ * a₂) := by group

theorem Gen.c_comm_z : a * a₁ * a₂ * z = z * (a * a₁ * a₂) := by
  calc a * a₁ * a₂ * z = a * a₁ * (a₂ * z) := by group
    _ = a * a₁ * (z * a₂) := by rw [g.z_comm_a₂]
    _ = a * (a₁ * z) * a₂ := by group
    _ = a * (z * a₁) * a₂ := by rw [g.z_comm_a₁]
    _ = (a * z) * a₁ * a₂ := by group
    _ = (z * a) * a₁ * a₂ := by rw [g.z_comm_a]
    _ = z * (a * a₁ * a₂) := by group

variable [Finite D] in
theorem Gen.c_central : ∀ u ∈ conjClosure V B, (a * a₁ * a₂) * u = u * (a * a₁ * a₂) := by
  intro u hu
  have hle : conjClosure V B ≤ Subgroup.centralizer ({a * a₁ * a₂} : Set D) := by
    rw [g.U_eq_closure, Subgroup.closure_le]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact g.c_comm_a
    · exact g.c_comm_z
    · exact g.c_comm_a₁
    · exact g.c_comm_a₂
  exact (Subgroup.mem_centralizer_iff.mp (hle hu) _ rfl)

theorem Gen.c_mem_U : a * a₁ * a₂ ∈ conjClosure V B :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ g.a_mem_U g.a₁_mem_U) g.a₂_mem_U

variable [Finite D] in
theorem Gen.c_not_mem : a * a₁ * a₂ ∉ Subgroup.zpowers z := by
  intro hc
  have hcc : (a * a₁ * a₂) * (a * a₁ * a₂) = 1 := by
    rcases g.hyp.mem_zpowers hc with e | e
    · rw [e, mul_one]
    · rw [e]; exact g.z_mul_z
  have hca : (a * a₁ * a₂) * a = a * (a * a₁ * a₂) := g.c_comm_a
  have hca₁ : (a * a₁ * a₂) * a₁ = a₁ * (a * a₁ * a₂) := g.c_comm_a₁
  have ha := g.a_sq
  have ha1 := g.a₁_sq
  have ha₂ : a₂ = a₁ * a * (a * a₁ * a₂) := by
    calc a₂ = (a₁ * a₁) * a₂ := by rw [ha1, one_mul]
      _ = a₁ * (a * a) * a₁ * a₂ := by rw [ha]; group
      _ = a₁ * a * (a * a₁ * a₂) := by group
  have hcom : (a * a₁ * a₂) * (a₁ * a) = (a₁ * a) * (a * a₁ * a₂) := by
    calc (a * a₁ * a₂) * (a₁ * a) = ((a * a₁ * a₂) * a₁) * a := by group
      _ = a₁ * ((a * a₁ * a₂) * a) := by rw [hca₁]; group
      _ = a₁ * (a * (a * a₁ * a₂)) := by rw [hca]
      _ = (a₁ * a) * (a * a₁ * a₂) := by group
  have hsq : (a₁ * a) * (a₁ * a) = 1 := by
    have h1 : a₂ * a₂ = (a₁ * a) * (a₁ * a) * ((a * a₁ * a₂) * (a * a₁ * a₂)) := by
      calc a₂ * a₂ = (a₁ * a * (a * a₁ * a₂)) * (a₁ * a * (a * a₁ * a₂)) := by
            rw [← ha₂]
        _ = (a₁ * a) * ((a * a₁ * a₂) * (a₁ * a)) * (a * a₁ * a₂) := by group
        _ = (a₁ * a) * ((a₁ * a) * (a * a₁ * a₂)) * (a * a₁ * a₂) := by rw [hcom]
        _ = (a₁ * a) * (a₁ * a) * ((a * a₁ * a₂) * (a * a₁ * a₂)) := by group
    rw [g.a₂_sq, hcc, mul_one] at h1
    exact h1.symm
  have hcomm : a * a₁ = a₁ * a := by
    calc a * a₁ = a * a₁ * ((a₁ * a) * (a₁ * a)) := by rw [hsq, mul_one]
      _ = (a * (a₁ * a₁)) * a * a₁ * a := by group
      _ = a₁ * a := by rw [ha1]; calc a * 1 * a * a₁ * a = (a * a) * a₁ * a := by group
                                                         _ = a₁ * a := by rw [ha]; group
  exact g.comm01_ne_one (by rw [hcomm]; group)

variable [Finite D] in
theorem Gen.c_mem_center : a * a₁ * a₂ ∈ centerOf (conjClosure V B) := by
  refine ⟨g.c_mem_U, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  exact (g.c_central u hu).symm

variable [Finite D] in
theorem Gen.z_mem_center : z ∈ centerOf (conjClosure V B) := by
  refine ⟨g.hyp.z_mem_U, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  exact g.hyp.z_comm (g.hyp.QB_le_T (g.hyp.U_le hu)).2


theorem Gen.not_comm01 [Finite D] : a * a₁ ≠ a₁ * a := fun h =>
  g.comm01_ne_one (by rw [h]; group)

variable [Finite D] in
theorem Gen.V_comm_a₁ {v : D} (hv : v ∈ V) (hc : v * a₁ = a₁ * v) :
    v ∈ Subgroup.zpowers z := by
  have hz1 : z * a₁ = a₁ * z := g.z_comm_a₁
  have hnc := g.not_comm01
  rcases (g.mem_V_iff).mp hv with e | e | e | e
  · rw [e]; exact Subgroup.one_mem _
  · rw [e]; exact Subgroup.mem_zpowers _
  · rw [e] at hc; exact absurd hc hnc
  · exfalso
    rw [e] at hc
    apply hnc
    have : z * (a * a₁) = z * (a₁ * a) := by
      calc z * (a * a₁) = (z * a) * a₁ := by group
        _ = a₁ * (z * a) := hc
        _ = (a₁ * z) * a := by group
        _ = (z * a₁) * a := by rw [← hz1]
        _ = z * (a₁ * a) := by group
    exact mul_left_cancel this

end Centre

theorem card_lt_of_lt' [Finite D] {H K : Subgroup D} (h : H < K) : Nat.card H < Nat.card K := by
  by_contra hcon
  push Not at hcon
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hcon)

theorem two_pow_succ_le [Finite D] {H K : Subgroup D} (hK : IsPGroup 2 ↥K) (hlt : H < K) {j : ℕ}
    (hH : Nat.card H = 2 ^ j) : 2 ^ (j + 1) ≤ Nat.card K := by
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  have h1 := card_lt_of_lt' hlt
  rw [hH, hk] at h1
  have h2 : j < k := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) h2

section Order

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.card_ge_sixteen : 16 ≤ Nat.card (conjClosure V B) := by
  have hT := g.hyp.isPGroup_T
  have hVU : V ≤ conjClosure V B := le_conjClosure V B
  have hcU : a * a₁ * a₂ ∈ conjClosure V B := g.c_mem_U
  have hU₀ : V ⊔ Subgroup.zpowers (a * a₁ * a₂) ≤ conjClosure V B :=
    sup_le hVU (Subgroup.zpowers_le.mpr hcU)
  have hU₁ : V ⊔ Subgroup.zpowers (a * a₁ * a₂) ⊔ Subgroup.zpowers a₁ ≤ conjClosure V B :=
    sup_le hU₀ (Subgroup.zpowers_le.mpr g.a₁_mem_U)
  have hcV : a * a₁ * a₂ ∉ V := fun hcV =>
    g.c_not_mem (g.V_comm_a₁ hcV g.c_comm_a₁)
  have hlt₀ : V < V ⊔ Subgroup.zpowers (a * a₁ * a₂) := by
    refine lt_of_le_of_ne le_sup_left fun e => hcV ?_
    have : a * a₁ * a₂ ∈ V ⊔ Subgroup.zpowers (a * a₁ * a₂) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [← e] at this
  have hcen : V ⊔ Subgroup.zpowers (a * a₁ * a₂) ≤ Subgroup.centralizer ({a} : Set D) := by
    refine sup_le (fun v hv => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact g.hyp.natural.comm_of_mem g.a_mem hv
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact g.c_comm_a.symm
  have hlt₁ : V ⊔ Subgroup.zpowers (a * a₁ * a₂) <
      V ⊔ Subgroup.zpowers (a * a₁ * a₂) ⊔ Subgroup.zpowers a₁ := by
    refine lt_of_le_of_ne le_sup_left fun e => g.not_comm01 ?_
    have : a₁ ∈ V ⊔ Subgroup.zpowers (a * a₁ * a₂) ⊔ Subgroup.zpowers a₁ :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [← e] at this
    exact Subgroup.mem_centralizer_iff.mp (hcen this) a rfl
  have hp₀ : IsPGroup 2 ↥(V ⊔ Subgroup.zpowers (a * a₁ * a₂)) :=
    hT.to_le (hU₀.trans g.hyp.U_le_T)
  have hp₁ : IsPGroup 2 ↥(V ⊔ Subgroup.zpowers (a * a₁ * a₂) ⊔ Subgroup.zpowers a₁) :=
    hT.to_le (hU₁.trans g.hyp.U_le_T)
  have hV4 : Nat.card V = 2 ^ 2 := by rw [g.hyp.natural.card_eq]; norm_num
  have h1 := two_pow_succ_le hp₀ hlt₀ hV4
  obtain ⟨j, hj⟩ := hp₀.exists_card_eq
  have h2 : 2 ^ (j + 1) ≤ Nat.card ↥(V ⊔ Subgroup.zpowers (a * a₁ * a₂) ⊔ Subgroup.zpowers a₁) :=
    two_pow_succ_le hp₁ hlt₁ hj
  rw [hj] at h1
  have h3 : 3 ≤ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h1)
  have h4 : 2 ^ 4 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 := Subgroup.card_le_of_le hU₁
  omega

theorem Gen.card_U : Nat.card (conjClosure V B) = 16 :=
  le_antisymm g.card_le_sixteen g.card_ge_sixteen

end Order

section Center

variable [Finite D] {x a a₁ a₂ : D} (g : Gen A B z V x a a₁ a₂)

include g

theorem Gen.card_center_U : Nat.card (centerOf (conjClosure V B)) = 4 := by
  have hT := g.hyp.isPGroup_T
  have hZU : centerOf (conjClosure V B) ≤ conjClosure V B := inf_le_left
  have hp : IsPGroup 2 ↥(centerOf (conjClosure V B)) :=
    hT.to_le (hZU.trans g.hyp.U_le_T)
  have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂) ≤ centerOf (conjClosure V B) :=
    sup_le (Subgroup.zpowers_le.mpr g.z_mem_center) (Subgroup.zpowers_le.mpr g.c_mem_center)
  have hlt : Subgroup.zpowers z < Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂) := by
    refine lt_of_le_of_ne le_sup_left fun e => g.c_not_mem ?_
    have : a * a₁ * a₂ ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [← e] at this
  have hp' : IsPGroup 2 ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂)) :=
    hT.to_le ((hle.trans hZU).trans g.hyp.U_le_T)
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by rw [g.hyp.card_zpowers]; norm_num
  have h1 := two_pow_succ_le hp' hlt hz2
  have h2 := Subgroup.card_le_of_le hle
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcomm : Nat.card (centerOf (conjClosure V B)) < 8 := by
    by_contra hcon
    push Not at hcon
    apply g.not_comm01
    refine comm_of_card_le_two_mul (C := centerOf (conjClosure V B)) (K := conjClosure V B)
      hZU (fun c hc k hk => ?_) ?_ g.a_mem_U g.a₁_mem_U
    · exact (Subgroup.mem_centralizer_iff.mp hc.2 k hk).symm
    · rw [g.card_U]; omega
  have h3 : 4 ≤ Nat.card (centerOf (conjClosure V B)) := by
    have := h1.trans h2
    simpa using this
  rw [hk] at h3 hcomm ⊢
  have hk2 : k < 3 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  have hk2' : 2 ≤ k := by
    by_contra hcon
    push Not at hcon
    interval_cases k <;> omega
  have : k = 2 := by omega
  subst this
  norm_num

theorem Gen.V_inf_center : V ⊓ centerOf (conjClosure V B) = Subgroup.zpowers z := by
  apply le_antisymm
  · intro v hv
    refine g.V_comm_a₁ hv.1 ?_
    exact (Subgroup.mem_centralizer_iff.mp hv.2.2 a₁ g.a₁_mem_U).symm
  · refine le_inf (Subgroup.zpowers_le.mpr g.hyp.natural.z_mem_V)
      (Subgroup.zpowers_le.mpr g.z_mem_center)


theorem Gen.center_U_eq :
    centerOf (conjClosure V B) = Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂) ∧
      (a * a₁ * a₂) * (a * a₁ * a₂) ∈ Subgroup.zpowers z := by
  have hT := g.hyp.isPGroup_T
  have hZU : centerOf (conjClosure V B) ≤ conjClosure V B := inf_le_left
  have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂) ≤ centerOf (conjClosure V B) :=
    sup_le (Subgroup.zpowers_le.mpr g.z_mem_center) (Subgroup.zpowers_le.mpr g.c_mem_center)
  have hlt : Subgroup.zpowers z < Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂) := by
    refine lt_of_le_of_ne le_sup_left fun e => g.c_not_mem ?_
    have : a * a₁ * a₂ ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [← e] at this
  have hp' : IsPGroup 2 ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers (a * a₁ * a₂)) :=
    hT.to_le ((hle.trans hZU).trans g.hyp.U_le_T)
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by rw [g.hyp.card_zpowers]; norm_num
  have h1 := two_pow_succ_le hp' hlt hz2
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle ?_).symm, g.hyp.sq_U _ g.c_mem_U⟩
  rw [g.card_center_U]
  simpa using h1

end Center

section Hyp

variable [Finite D] (h : Hyp2 A B z V)

include h

theorem Hyp2.not_mem_normalizer {x : D} (hxB : x ∈ B) (hxT : x ∉ A ⊓ B) :
    x ∉ Subgroup.normalizer (V : Set D) := by
  intro hxN
  have hTC : A ⊓ B ≤ B ⊓ Subgroup.normalizer (V : Set D) := fun t ht =>
    ⟨ht.2, h.natural.reduced.2.1 ht.1⟩
  have hBC : B ≤ B ⊓ Subgroup.normalizer (V : Set D) :=
    h.gold.vertex_right.le_of_not_mem hTC inf_le_left ⟨hxB, hxN⟩ hxT
  have hVT : V ≤ A ⊓ B := h.natural.le_pCoreOf.trans h.gold.pCoreOf_left_le
  exact h.natural.natural.ne_bot
    (h.gold.eq_bot_of_normalizes h.natural.reduced.2.1 (fun b hb => (hBC hb).2) hVT)

theorem Hyp2.card_U : Nat.card (conjClosure V B) = 16 := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  exact g.card_U

theorem Hyp2.card_center_U : Nat.card (centerOf (conjClosure V B)) = 4 := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  exact g.card_center_U

theorem Hyp2.V_inf_center : V ⊓ centerOf (conjClosure V B) = Subgroup.zpowers z := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  exact g.V_inf_center

theorem Hyp2.three_conjugates : ∃ x ∈ B, x ∉ A ⊓ B ∧ conjSub x V ≠ V ∧ conjSub (x * x) V ≠ V ∧
    conjSub x V ≠ conjSub (x * x) V ∧
    ∀ b ∈ B, conjSub b V = V ∨ conjSub b V = conjSub x V ∨ conjSub b V = conjSub (x * x) V := by
  obtain ⟨x, a, a₁, a₂, g⟩ := h.exists_gen
  have h1 : conjSub x V ≠ V := fun e =>
    h.not_mem_normalizer g.x_mem g.x_not (mem_normalizer_of_conjSub_eq e)
  have h2 : conjSub (x * x) V ≠ V := fun e =>
    h.not_mem_normalizer g.x2_mem g.x2_not (mem_normalizer_of_conjSub_eq e)
  refine ⟨x, g.x_mem, g.x_not, h1, h2, fun e => h1 ?_, fun b hb => ?_⟩
  · have e' : conjSub x V = conjSub x (conjSub x V) := by rw [← conjSub_mul]; exact e
    have := congrArg (conjSub x⁻¹) e'
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
    exact this.symm
  · rcases coset_decomp h.gold.relIndex_right g.x_mem g.x_not g.x2_not hb with hbT | ⟨t, htT, rfl⟩ |
        ⟨t, htT, rfl⟩
    · exact Or.inl (conjSub_eq_of_mem_normalizer (h.natural.reduced.2.1 hbT.1))
    · right; left
      rw [conjSub_mul, conjSub_eq_of_mem_normalizer (h.natural.reduced.2.1 htT.1)]
    · right; right
      rw [conjSub_mul, conjSub_eq_of_mem_normalizer (h.natural.reduced.2.1 htT.1)]

end Hyp

end GoldAmL2S

end F6

end CFSG.Quasithin
