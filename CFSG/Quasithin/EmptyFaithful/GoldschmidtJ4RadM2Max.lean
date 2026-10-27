module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadPrim
public import CFSG.Quasithin.Vol2.GoldschmidtF134J4EOrbit
public import CFSG.Sporadic.J4.QT2LocCntProof

public section

namespace CFSG.Quasithin.J4Rad

theorem orbit_ncard_mod_four {Γ : Type*} [Group Γ] [Finite Γ] (H E D : Subgroup Γ)
    (hE : IsPGroup 2 ↥E) (hEH : E ≤ H) (hED : E ≤ D)
    (h4 : ∀ g : Γ, g • ((1 : Γ) : Γ ⧸ H) ≠ ((1 : Γ) : Γ ⧸ H) →
      4 ≤ {w : Γ ⧸ H | ∃ e ∈ E, e • (g • ((1 : Γ) : Γ ⧸ H)) = w}.ncard) :
    {w : Γ ⧸ H | ∃ d ∈ D, d • ((1 : Γ) : Γ ⧸ H) = w}.ncard % 4 = 1 := by
  set x₀ : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H) with hx₀
  have hsmul : ∀ g : Γ, g • x₀ = ((g : Γ) : Γ ⧸ H) := fun g => by
    show ((g * 1 : Γ) : Γ ⧸ H) = _
    rw [mul_one]
  have hfixiff : ∀ g : Γ, g • x₀ = x₀ ↔ g ∈ H := fun g => by
    rw [hsmul, hx₀, QuotientGroup.eq, mul_one, inv_mem_iff]
  refine ncard_mod_four_eq_one E hE x₀ (fun e he => (hfixiff e).mpr (hEH he)) ?_ _
    (Set.toFinite _) ?_ ⟨1, D.one_mem, one_smul _ _⟩
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g • x₀ = ((g : Γ) : Γ ⧸ H) := hsmul g
    rw [← hg] at hx ⊢
    exact h4 g hx
  · rintro e he _ ⟨d, hd, rfl⟩
    exact ⟨e * d, D.mul_mem (hED he) hd, by rw [mul_smul]⟩

theorem maximal_of_orbits {Γ : Type*} [Group Γ] [Finite Γ] (H E M : Subgroup Γ)
    (hE : IsPGroup 2 ↥E) (hEH : E ≤ H) (hEM : E ≤ M)
    (h4 : ∀ g : Γ, g • ((1 : Γ) : Γ ⧸ H) ≠ ((1 : Γ) : Γ ⧸ H) →
      4 ≤ {w : Γ ⧸ H | ∃ e ∈ E, e • (g • ((1 : Γ) : Γ ⧸ H)) = w}.ncard)
    (hcard : Nat.card ↥M = 77 * Nat.card ↥(M ⊓ H)) :
    ∀ D : Subgroup Γ, M ⊓ H ≤ D → D ≤ M → D = M ⊓ H ∨ D = M := by
  intro D hCD hDM
  set x₀ : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H) with hx₀
  have hsmul : ∀ g : Γ, g • x₀ = ((g : Γ) : Γ ⧸ H) := fun g => by
    show ((g * 1 : Γ) : Γ ⧸ H) = _
    rw [mul_one]
  have hfixiff : ∀ g : Γ, g • x₀ = x₀ ↔ g ∈ H := fun g => by
    rw [hsmul, hx₀, QuotientGroup.eq, mul_one, inv_mem_iff]
  have hEC : E ≤ M ⊓ H := le_inf hEM hEH
  have hED : E ≤ D := hEC.trans hCD
  have hDH : D ⊓ H = M ⊓ H :=
    le_antisymm (inf_le_inf_right H hDM) (le_inf hCD inf_le_right)
  have hcardD : Nat.card ↥D = Nat.card (MulAction.orbit ↥D x₀) * Nat.card ↥(M ⊓ H) := by
    rw [← hDH]
    exact CFSG.Sporadic.J4.QT2.card_eq_orbit_mul_inf D H x₀ hfixiff
  set S : Set (Γ ⧸ H) := {w | ∃ d ∈ D, d • x₀ = w} with hS
  have hSorb : MulAction.orbit ↥D x₀ = S := by
    ext w
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  have hSn : Nat.card (MulAction.orbit ↥D x₀) = S.ncard := by
    rw [hSorb, Nat.card_coe_set_eq]
  have hmod : S.ncard % 4 = 1 := orbit_ncard_mod_four H E D hE hEH hED h4
  have hdvd : Nat.card ↥D ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hDM
  have hCpos : 0 < Nat.card ↥(M ⊓ H) := Nat.card_pos
  rw [hcardD, hSn, hcard] at hdvd
  have h77 : S.ncard ∣ 77 := Nat.dvd_of_mul_dvd_mul_right hCpos hdvd
  have hcases : S.ncard = 1 ∨ S.ncard = 77 := by
    have hle : S.ncard ≤ 77 := Nat.le_of_dvd (by norm_num) h77
    interval_cases h : S.ncard <;> omega
  rcases hcases with h1 | h77'
  · left
    refine (Subgroup.eq_of_le_of_card_ge hCD ?_).symm
    rw [hcardD, hSn, h1]
    simp
  · right
    refine Subgroup.eq_of_le_of_card_ge hDM ?_
    rw [hcardD, hSn, h77', hcard, mul_comm]

section J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.F134.J4E9

theorem card_inf_Hj_of_mem_Zl
    (hF : J4Facts) {z : J} (hz : z ∈ Zl) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set J) ⊓ Hj) = 283115520 := by
  have hM := hF.mat
  have h := card_eq_card_mul_centralizer Hj z Zl hz (fun h hh x hx => (Zl_conj hM h hh).1 x hx)
    (fun x hx => Zl_trans hM z hz x hx)
  rw [card_Hj hF, card_Zl hM] at h
  omega

theorem card_centralizer_eq
    (hF : J4Facts) {z : J}
    (hz : z ∈ Zl) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set J)) =
      77 * Nat.card ↥(Subgroup.centralizer ({z} : Set J) ⊓ Hj) := by
  rw [card_centralizer_of_mem_Zl hF hz, card_inf_Hj_of_mem_Zl hF hz]

theorem Eg_le_centralizer
    (hF : J4Facts) {z : J} (hz : z ∈ Zl) :
    Eg uJ 11 ≤ Subgroup.centralizer ({z} : Set J) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Eg_comm (elem_uJ hF.mat) hx (mem_Eg_of_mem_Zl hz)

theorem orbit_ncard_mod_four_J
    (hF : J4Facts)
    (D : Subgroup J) (hED : Eg uJ 11 ≤ D) :
    {w : J ⧸ Hj | ∃ d ∈ D, d • basePt = w}.ncard % 4 = 1 :=
  orbit_ncard_mod_four Hj (Eg uJ 11) D (isPGroup_Eg (elem_uJ hF.mat)) Eg_le_Hj hED
    (fun _ hg => four_le_ncard_orbit hg)

theorem centralizer_maximal
    (hF : J4Facts) {z : J} (hz : z ∈ Zl) :
    ∀ D : Subgroup J, Subgroup.centralizer ({z} : Set J) ⊓ Hj ≤ D →
      D ≤ Subgroup.centralizer ({z} : Set J) →
      D = Subgroup.centralizer ({z} : Set J) ⊓ Hj ∨ D = Subgroup.centralizer ({z} : Set J) := by
  refine maximal_of_orbits Hj (Eg uJ 11) (Subgroup.centralizer ({z} : Set J))
    (isPGroup_Eg (elem_uJ hF.mat)) Eg_le_Hj (Eg_le_centralizer hF hz) ?_
    (card_centralizer_eq hF hz)
  intro g hg
  exact four_le_ncard_orbit hg

@[expose] def Opt (z : J) : Set (J ⧸ Hj) :=
  {w | ∃ g : J, ((g : J) : J ⧸ Hj) = w ∧ g⁻¹ * z * g ∈ Eg uJ 11}

@[expose] noncomputable def rowOf (hM : MatFacts) : J ⧸ Hj → Row :=
  Quotient.lift (fun g : J => g • w₀) (fun a b hab => by
    have h1 : a⁻¹ * b ∈ Hj := QuotientGroup.leftRel_apply.mp hab
    have h := smul_root_of_mem_Hj hM h1
    calc a • w₀ = a • ((a⁻¹ * b) • w₀) := by rw [h]
      _ = b • w₀ := by rw [smul_smul, mul_inv_cancel_left])

theorem rowOf_mk (hM : MatFacts) (g : J) : rowOf hM ((g : J) : J ⧸ Hj) = g • w₀ := rfl

theorem rowOf_injective (hF : J4Facts) : Function.Injective (rowOf hF.mat) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with
  | _ g₁ =>
  induction b using QuotientGroup.induction_on with
  | _ g₂ =>
  rw [rowOf_mk, rowOf_mk] at hab
  rw [QuotientGroup.eq]
  refine mem_Hj_of_smul_root hF ?_
  rw [← smul_smul]
  rw [← hab, inv_smul_smul]

theorem ncard_Opt_le
    (hF : J4Facts) {z : J} (hz : z ∈ Zl) :
    (Opt z).ncard ≤ 77 := by
  have himg : rowOf hF.mat '' Opt z = Omega z := by
    ext v
    constructor
    · rintro ⟨w, ⟨g, rfl, hg⟩, rfl⟩
      exact ⟨g, rfl, hg⟩
    · rintro ⟨g, rfl, hg⟩
      exact ⟨((g : J) : J ⧸ Hj), ⟨g, rfl, hg⟩, rfl⟩
  rw [← Set.ncard_image_of_injective _ (rowOf_injective hF), himg]
  exact card_Omega_le hF hz

theorem smul_basePt_eq_mk (g : J) : g • basePt = ((g : J) : J ⧸ Hj) := by
  rw [basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

theorem orbit_subset_Opt {z : J} (hz : z ∈ Eg uJ 11) :
    {w : J ⧸ Hj | ∃ q ∈ Subgroup.centralizer ({z} : Set J), q • basePt = w} ⊆ Opt z := by
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨q, (smul_basePt_eq_mk q).symm, ?_⟩
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hq
  have : q⁻¹ * z * q = z := by
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [this]
  exact hz

theorem ncard_orbit_centralizer
    (hF : J4Facts) {z : J}
    (hz : z ∈ Zl) :
    {w : J ⧸ Hj | ∃ q ∈ Subgroup.centralizer ({z} : Set J), q • basePt = w}.ncard = 77 := by
  have hfix : ∀ g : J, g • basePt = basePt ↔ g ∈ Hj := fun g => smul_basePt_eq_self_iff
  have h := CFSG.Sporadic.J4.QT2.card_eq_orbit_mul_inf (Subgroup.centralizer ({z} : Set J)) Hj
    basePt hfix
  rw [card_centralizer_eq hF hz] at h
  have hCpos : 0 < Nat.card ↥(Subgroup.centralizer ({z} : Set J) ⊓ Hj) := Nat.card_pos
  have h77 : Nat.card (MulAction.orbit ↥(Subgroup.centralizer ({z} : Set J)) basePt) = 77 :=
    (Nat.eq_of_mul_eq_mul_right hCpos h).symm
  have hS : MulAction.orbit ↥(Subgroup.centralizer ({z} : Set J)) basePt =
      {w : J ⧸ Hj | ∃ q ∈ Subgroup.centralizer ({z} : Set J), q • basePt = w} := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  rw [← hS, ← Nat.card_coe_set_eq, h77]

theorem exists_mem_centralizer_of_mem_Opt
    (hF : J4Facts) {z : J} (hz : z ∈ Zl) {w : J ⧸ Hj} (hw : w ∈ Opt z) :
    ∃ q ∈ Subgroup.centralizer ({z} : Set J), q • basePt = w := by
  have hsub := orbit_subset_Opt (mem_Eg_of_mem_Zl hz)
  have heq := Set.eq_of_subset_of_ncard_le hsub
    ((ncard_Opt_le hF hz).trans (ncard_orbit_centralizer hF hz).ge)
  rw [← heq] at hw
  exact hw

end J4

end CFSG.Quasithin.J4Rad
