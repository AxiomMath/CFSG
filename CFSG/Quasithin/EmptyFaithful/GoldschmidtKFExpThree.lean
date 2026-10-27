module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFAutThree
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFHyp

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

theorem KFHyp.pow_three_of_pow (h113 : StageLemma14113)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {g : G} (hg : g ∈ I)
    (hn : ∃ n : ℕ, g ^ 3 ^ n = 1) : g ^ 3 = 1 := by
  classical
  obtain ⟨K, _, _, _, ρ, φ, Φ, hK4, -, hker, hφ, hΦ, -⟩ := h.r.exists_outer_action h113
  obtain ⟨n, hn⟩ := hn
  set g' : ↥I := ⟨g, hg⟩ with hg'
  have h1 : Φ g' ^ 3 ^ n = 1 := by
    rw [← map_pow]
    have : g' ^ 3 ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [this, map_one]
  have h3 : Φ g' ^ 3 = 1 := pow_three_eq_one_of_mulAut hK4 ⟨n, h1⟩
  have hg3 : Φ (g' ^ 3) = 1 := by rw [map_pow]; exact h3
  have hperf : Group.IsPerfect ↥L := h.r.ctx.c33.quasisimple.1
  have hφ1 : φ (g' ^ 3) = 1 := by
    apply SBd14.eq_one_of_central_perfect hperf
    intro x
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← hΦ, hg3, MulAut.one_apply, mul_inv_cancel]
  have hcL : g ^ 3 ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := congrArg (fun e : MulAut ↥L => ((e ⟨y, hy⟩ : ↥L) : G)) hφ1
    simp only [hφ, MulAut.one_apply] at h2
    have h4 : ((g' ^ 3 : ↥I) : G) = g ^ 3 := by simp [hg']
    rw [h4] at h2
    calc y * g ^ 3 = (g ^ 3 * y * (g ^ 3)⁻¹) * g ^ 3 := by rw [h2]
      _ = g ^ 3 * y := by group
  have hV : g ^ 3 ∈ V₁ := by
    rw [← h.hCIL]
    exact ⟨I.pow_mem hg 3, hcL⟩
  have hsq : g ^ 3 * g ^ 3 = 1 := h.r.V_sq _ (h.r.ctx.hyp.decomp.le₁ hV)
  have hd2 : orderOf (g ^ 3) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hd3 : orderOf (g ^ 3) ∣ 3 ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hn, one_pow])
  have hcop : Nat.Coprime (3 ^ n) 2 := Nat.Coprime.pow_left n (by norm_num)
  have hone : orderOf (g ^ 3) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd3 hd2
  exact orderOf_eq_one_iff.mp hone

theorem KFHyp.commutator_sigma_mem (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {g : G} (hg : g ∈ I) :
    (g * (τ * f) * g⁻¹) * (τ * f) ∈ L := by
  have hσI : τ * f ∈ I := h.sigma_mem_I
  have hσN : τ * f ∈ Subgroup.normalizer (L : Set G) := h.r.hNL hσI
  have hgN : g ∈ Subgroup.normalizer (V₁ : Set G) := h.hI ▸ hg
  have hmem : g * (τ * f) * g⁻¹ ∈ Subgroup.centralizer (V₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
      simpa using this
    have h1 := h.hcent _ hv'
    calc v * (g * (τ * f) * g⁻¹)
        = g * ((g⁻¹ * v * g) * (τ * f)) * g⁻¹ := by group
      _ = g * ((τ * f) * (g⁻¹ * v * g)) * g⁻¹ := by rw [← h1]
      _ = (g * (τ * f) * g⁻¹) * v := by group
  rw [h.hcl'] at hmem
  rcases SBd18.mem_sup_zpowers_cases h.sigma_ne_one h.sigma_sq hσN hmem with h1 | h1
  · exfalso
    apply h.hσL
    have := (Subgroup.mem_normalizer_iff.mp (h.r.hNL (I.inv_mem hg)) _).mp h1
    simpa [mul_assoc] using this
  · exact h1

end CFSG.Quasithin.SBd19F
