module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R9
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R8

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem TfG_sq_ne_F (c : AutCtx G M₁ M₂ z) {t : G} (ht : t ∈ TfG c) :
    t * t ≠ c.iso.toG fhB := by
  intro h
  obtain ⟨b, hb, rfl⟩ := c.iso.mem_imgG.1 ht.1
  have h1 : b * b = fhB := c.iso.toG_injective (by rw [AutIso.toG_mul]; exact h)
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff (b : Ah)).1 hb
  have h2 : ((b : Ah) : P45) * ((b : Ah) : P45) = (fhatA : P45) :=
    congrArg (fun x : ↥Bh => ((x : Ah) : P45)) h1
  have h3 : RepL (comp l l) (fhatA : P45) := by rw [← h2]; exact repL_mul hrep hrep
  exact Thl_sq_ne_f l hl (repL_unique h3 repL_fhat)

structure RhoCtx (c : AutCtx G M₁ M₂ z) (R : Subgroup G) (ρ : G) : Prop where
  mem : ρ ∈ C1G c R
  sq : ρ * ρ = c.iso.toG fhB

@[expose] def Erho (R : Subgroup G) (ρ : G) : Subgroup G :=
  R ⊓ Subgroup.centralizer ({ρ} : Set G)

section Rho

variable {c : AutCtx G M₁ M₂ z} {R : Subgroup G} {ρ : G}

theorem RhoCtx.not_mem_Tf (hr : RhoCtx c R ρ) : ρ ∉ TfG c := fun ht => TfG_sq_ne_F c ht hr.sq

theorem RhoCtx.conj_z (h : F55Ctx c R) (hr : RhoCtx c R ρ) :
    ρ * z * ρ⁻¹ = c.iso.toG fhB * z :=
  conj_z_of_not_mem c h.h5 h.h6 h.ht0 h.hR h.hTR h.hR64 hr.mem.1 hr.not_mem_Tf

theorem RhoCtx.orderOf (hr : RhoCtx c R ρ) : orderOf ρ = 4 := by
  have hF2 : c.iso.toG fhB * c.iso.toG fhB = 1 := F_sq c.iso
  have h2 : ρ ^ 2 ≠ 1 := by
    rw [pow_two, hr.sq]
    exact F_ne_one c.iso
  have h4 : ρ ^ 4 = 1 := by
    calc ρ ^ 4 = (ρ * ρ) * (ρ * ρ) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [hr.sq]; exact hF2
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ρ) (by simpa using h2) (by simpa using h4)
  simpa using this

theorem RhoCtx.comm_UG (h : F55Ctx c R) (hr : RhoCtx c R ρ) {u : G} (hu : u ∈ UG c) :
    ρ * u = u * ρ := C1G_comm_UG c h hr.mem hu

theorem RhoCtx.zpowers_inf_UG (hr : RhoCtx c R ρ) {x : G} (hx : x ∈ Subgroup.zpowers ρ)
    (hu : x ∈ UG c) : x = 1 :=
  C1G_inf_UG c hu (Subgroup.zpowers_le.2 hr.mem hx)

theorem RhoCtx.UG_le_Erho (h : F55Ctx c R) (hr : RhoCtx c R ρ) : UG c ≤ Erho R ρ := fun _ hu =>
  ⟨UG_le_R c h hu, Subgroup.mem_centralizer_singleton_iff.2 (hr.comm_UG h hu).symm⟩

theorem RhoCtx.zpowers_le_Erho (hr : RhoCtx c R ρ) : Subgroup.zpowers ρ ≤ Erho R ρ :=
  Subgroup.zpowers_le.2 ⟨hr.mem.1, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem RhoCtx.card_Erho_ge (h : F55Ctx c R) (hr : RhoCtx c R ρ) : 32 ≤ Nat.card ↥(Erho R ρ) := by
  have h1 := card_mul_le_of_inf_bot hr.zpowers_le_Erho (hr.UG_le_Erho h)
    (fun x hx hu => hr.zpowers_inf_UG hx hu)
  rw [Nat.card_zpowers, hr.orderOf, card_UG c] at h1
  omega

theorem RhoCtx.z_not_mem_Erho (h : F55Ctx c R) (hr : RhoCtx c R ρ) : z ∉ Erho R ρ := by
  intro hz
  have h1 : z * ρ = ρ * z := Subgroup.mem_centralizer_singleton_iff.1 hz.2
  have h2 := hr.conj_z h
  apply F_ne_one c.iso
  have : c.iso.toG fhB * z = z := by
    rw [← h2]
    calc ρ * z * ρ⁻¹ = (ρ * z) * ρ⁻¹ := rfl
      _ = (z * ρ) * ρ⁻¹ := by rw [h1]
      _ = z := by group
  calc c.iso.toG fhB = (c.iso.toG fhB * z) * z⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem RhoCtx.card_Erho (h : F55Ctx c R) (hr : RhoCtx c R ρ) : Nat.card ↥(Erho R ρ) = 32 ∧
    (Erho R ρ).relIndex R = 2 := by
  have h64 := h.hR64
  have hle : Erho R ρ ≤ R := inf_le_left
  have hcard := Subgroup.card_mul_index ((Erho R ρ).subgroupOf R)
  have h4 : Nat.card ↥((Erho R ρ).subgroupOf R) = Nat.card ↥(Erho R ρ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h5 : ((Erho R ρ).subgroupOf R).index = (Erho R ρ).relIndex R := rfl
  rw [h4, h5, h64] at hcard
  have hge := hr.card_Erho_ge h
  have hne : (Erho R ρ).relIndex R ≠ 1 := by
    intro h1
    have h2 : (Erho R ρ).subgroupOf R = ⊤ := Subgroup.index_eq_one.1 h1
    have hz : (⟨z, z_mem_R c h⟩ : ↥R) ∈ (Erho R ρ).subgroupOf R := by rw [h2]; trivial
    exact hr.z_not_mem_Erho h hz
  have hpos : 0 < (Erho R ρ).relIndex R := by
    by_contra hz
    have : (Erho R ρ).relIndex R = 0 := by omega
    rw [this] at hcard
    omega
  have hidx : (Erho R ρ).relIndex R = 2 := by
    have : (Erho R ρ).relIndex R ≤ 2 := by
      by_contra hgt
      have : 3 ≤ (Erho R ρ).relIndex R := by omega
      have := Nat.mul_le_mul hge this
      omega
    omega
  refine ⟨?_, hidx⟩
  rw [hidx] at hcard
  norm_num at hcard
  omega

theorem RhoCtx.mem_Erho_decomp (h : F55Ctx c R) (hr : RhoCtx c R ρ) :
    ∀ y ∈ Erho R ρ, ∃ a ∈ Subgroup.zpowers ρ, ∃ u ∈ UG c, y = a * u := by
  refine exists_mul_of_card_eq hr.zpowers_le_Erho (hr.UG_le_Erho h)
    (fun x hx hu => hr.zpowers_inf_UG hx hu) ?_
  rw [Nat.card_zpowers, hr.orderOf, card_UG c, (hr.card_Erho h).1]

theorem RhoCtx.zpowers_cases (hr : RhoCtx c R ρ) :
    ∀ a ∈ Subgroup.zpowers ρ, a = 1 ∨ a = ρ ∨ a = c.iso.toG fhB ∨ a = ρ * c.iso.toG fhB := by
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hk := zpow_mod_orderOf ρ k
  rw [hr.orderOf] at hk
  rw [← hk]
  have h4 : (k % ((4 : ℕ) : ℤ)) = 0 ∨ (k % ((4 : ℕ) : ℤ)) = 1 ∨ (k % ((4 : ℕ) : ℤ)) = 2 ∨
      (k % ((4 : ℕ) : ℤ)) = 3 := by omega
  rcases h4 with h4 | h4 | h4 | h4 <;> rw [h4]
  · left; simp
  · right; left; simp
  · right; right; left
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hr.sq]
  · right; right; right
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    calc ρ ^ 3 = (ρ * ρ) * ρ := by simp [pow_succ]
      _ = ρ * (ρ * ρ) := by group
      _ = ρ * c.iso.toG fhB := by rw [hr.sq]

theorem RhoCtx.E_invol (h : F55Ctx c R) (hr : RhoCtx c R ρ) {y : G} (hy : y ∈ Erho R ρ)
    (hy2 : y * y = 1) :
    ∃ u ∈ UG c, u * u = 1 ∧ (y = u ∨ y = c.iso.toG fhB * u) := by
  obtain ⟨a, ha, u, hu, rfl⟩ := hr.mem_Erho_decomp h y hy
  set F := c.iso.toG fhB with hF
  have hF2 : F * F = 1 := F_sq c.iso
  have hFc : ∀ x : G, x ∈ R → F * x = x * F := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hx)).symm
  have hcomm : a * u = u * a := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (hr.comm_UG h hu : Commute ρ u) k).eq
  have hnF : F ∉ UG c := F_not_mem_UG c
  have hsq : a * a * (u * u) = 1 := by
    calc a * a * (u * u) = a * (a * u) * u := by group
      _ = a * (u * a) * u := by rw [hcomm]
      _ = (a * u) * (a * u) := by group
      _ = 1 := hy2
  rcases hr.zpowers_cases a ha with rfl | rfl | rfl | rfl
  · refine ⟨u, hu, by simpa using hsq, Or.inl (by simp)⟩
  · exfalso
    apply hnF
    have : F = (u * u)⁻¹ := by
      rw [hr.sq] at hsq
      exact eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact (UG c).inv_mem ((UG c).mul_mem hu hu)
  · have : u * u = 1 := by
      have := hsq
      rw [hF2, one_mul] at this
      exact this
    exact ⟨u, hu, this, Or.inr rfl⟩
  · exfalso
    apply hnF
    have hFρ : F * ρ = ρ * F := hFc ρ hr.mem.1
    have h1 : (ρ * F) * (ρ * F) = F := by
      calc (ρ * F) * (ρ * F) = ρ * (F * ρ) * F := by group
        _ = ρ * (ρ * F) * F := by rw [hFρ]
        _ = (ρ * ρ) * (F * F) := by group
        _ = F := by rw [hr.sq, hF2, mul_one]
    rw [h1] at hsq
    have : F = (u * u)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact (UG c).inv_mem ((UG c).mul_mem hu hu)

end Rho

end CFSG.Quasithin.H13.F431.U42Aut
