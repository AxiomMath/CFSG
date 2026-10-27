module

public import CFSG.RankThree.GF2n.Smith81.Sec1Local

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem smith_1_14 (H : StrothHyp M Q Z) {a : G} (haQ : a ∈ Q) (haZ : a ∉ Z) {r : G}
    (hrM : r ∈ M) (hr : ∀ c ∈ Q ⊓ Subgroup.centralizer ({a} : Set G), r * c = c * r) :
    r ∈ Q := by
  have hcen := (smith_1_14_analysis H haQ haZ hrM hr).1
  have hrZ : ∀ z ∈ Z, r * z * r⁻¹ = z := by
    intro z hz
    have hzC : z ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨H.Z_normal.1 hz, Subgroup.mem_centralizer_singleton_iff.mpr (Z_central H hz haQ)⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact hr z hzC
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨T, hTπ, hTQ, hTB⟩ := hD.linear_of_centralizes hrM hrZ
  set e₀ := M₀.π a with he₀
  have he₀0 : e₀ ≠ 0 := fun h => haZ ((M₀.π_ker a haQ).mp h)
  have hfix : ∀ e, M₀.B e e₀ = 0 → T e = e := by
    intro e he
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    have hya : ⁅y, a⁆ = 1 := (GM.comm_eq_one_iff hD hyQ haQ).mpr he
    have hyC : y ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp hya)⟩
    have h1 := hr y hyC
    rw [← hTπ y hyQ]
    congr 1
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  obtain ⟨e₁, he₁⟩ : ∃ e₁, M₀.B e₁ e₀ = 1 := by
    obtain ⟨f, hf⟩ : ∃ f, M₀.B f e₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact he₀0 (M₀.nondeg e₀ fun f => by rw [Tim79.QuadModel.B_comm e₀ f, hcon f, neg_zero])
    refine ⟨(M₀.B f e₀)⁻¹ • f, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
  have hdecomp : ∀ e, e - M₀.B e e₀ • e₁ ∈ {h : M₀.E | M₀.B h e₀ = 0} := by
    intro e
    show M₀.B (e - M₀.B e e₀ • e₁) e₀ = 0
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, he₁, mul_one,
      sub_self]
  have hTe : ∀ e, T e = e + M₀.B e e₀ • (T e₁ - e₁) := by
    intro e
    have h1 := hfix _ (hdecomp e)
    rw [map_sub, map_smul] at h1
    have h2 : T e = (T e - M₀.B e e₀ • T e₁) + M₀.B e e₀ • T e₁ := (sub_add_cancel _ _).symm
    rw [h2, h1, smul_sub]
    abel
  have hw : ∀ h, M₀.B h e₀ = 0 → M₀.B (T e₁ - e₁) h = 0 := by
    intro h hh
    rw [map_sub, LinearMap.sub_apply, ← hfix h hh, hTB e₁ h, hfix h hh, sub_self]
  have hBw : ∀ e, M₀.B (T e₁ - e₁) e = M₀.B e e₀ * M₀.B (T e₁ - e₁) e₁ := by
    intro e
    have h1 := hw _ (hdecomp e)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c : K, T e₁ - e₁ = c • e₀ := by
    refine ⟨-M₀.B (T e₁ - e₁) e₁, ?_⟩
    have h0 : T e₁ - e₁ + M₀.B (T e₁ - e₁) e₁ • e₀ = 0 := by
      refine M₀.nondeg _ fun f => ?_
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hBw f,
        Tim79.QuadModel.B_comm e₀ f]
      ring
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h0
  have hTform : ∀ e, T e = e + (c * M₀.B e e₀) • e₀ := by
    intro e
    rw [hTe e, hc, smul_smul, mul_comm]
  have hcq : c * (c * M₀.Qf e₀ + 1) = 0 := by
    have h1 := hTQ e₁
    rw [hTform e₁, he₁, mul_one] at h1
    have h2 := M₀.Qf_add e₁ (c • e₀)
    rw [M₀.Qf_smul, map_smul, smul_eq_mul, he₁] at h2
    rw [h2] at h1
    linear_combination h1
  have hTT : ∀ e, T (T e) = e := by
    intro e
    have hB : M₀.B (T e) e₀ = M₀.B e e₀ := by
      rw [hTform e, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, M₀.alt,
        smul_eq_mul, mul_zero, add_zero]
    rw [hTform (T e), hB, hTform e, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul,
      add_zero]
  by_cases hc0 : c = 0
  · refine H.centralizer_Qt r hrM fun y hy => ?_
    have e : ⁅r, y⁆ = (r * y * r⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    have hryQ : ⁅r, y⁆ ∈ Q := by
      rw [e]; exact Q.mul_mem (conj_mem_Q H hrM hy) (Q.inv_mem hy)
    refine (M₀.π_ker _ hryQ).mp ?_
    rw [e, M₀.π_mul _ (conj_mem_Q H hrM hy) _ (Q.inv_mem hy), Tim79.QuadModel.pi_inv M₀ hy,
      hTπ y hy, hTform, hc0]
    simp
  exfalso
  have hQf : c * M₀.Qf e₀ + 1 = 0 := (mul_eq_zero.mp hcq).resolve_left hc0
  have hsM : r * r ∈ M := M.mul_mem hrM hrM
  have hconj_s : ∀ y ∈ Q, M₀.π ((r * r) * y * (r * r)⁻¹) = M₀.π y := by
    intro y hy
    have : (r * r) * y * (r * r)⁻¹ = r * (r * y * r⁻¹) * r⁻¹ := by group
    rw [this, hTπ _ (conj_mem_Q H hrM hy), hTπ y hy, hTT]
  have hsQ : r * r ∈ Q := by
    refine H.centralizer_Qt _ hsM fun y hy => ?_
    have e : ⁅r * r, y⁆ = ((r * r) * y * (r * r)⁻¹) * y⁻¹ := by
      simp only [commutatorElement_def]
    have hsy : (r * r) * y * (r * r)⁻¹ ∈ Q := conj_mem_Q H hsM hy
    rw [e]
    refine (M₀.π_ker _ (Q.mul_mem hsy (Q.inv_mem hy))).mp ?_
    rw [M₀.π_mul _ hsy _ (Q.inv_mem hy), Tim79.QuadModel.pi_inv M₀ hy, hconj_s y hy, add_neg_cancel]
  have hkey : ∀ y ∈ Q, M₀.B (M₀.π (r * r)) (M₀.π y) = c ^ 2 * M₀.Qf e₀ * M₀.B (M₀.π y) e₀ ^ 2 := by
    intro y hy
    obtain ⟨u, hu_def⟩ : ∃ u, u = ⁅r, y⁆ := ⟨_, rfl⟩
    have hu_eq : u = (r * y * r⁻¹) * y⁻¹ := by rw [hu_def, commutatorElement_def]
    have hryQ := conj_mem_Q H hrM hy
    have huQ : u ∈ Q := by rw [hu_eq]; exact Q.mul_mem hryQ (Q.inv_mem hy)
    have hπu : M₀.π u = (c * M₀.B (M₀.π y) e₀) • e₀ := by
      rw [hu_eq, M₀.π_mul _ hryQ _ (Q.inv_mem hy), Tim79.QuadModel.pi_inv M₀ hy, hTπ y hy, hTform]
      abel
    have hyinv : y⁻¹ ∈ Q := Q.inv_mem hy
    have hu' : ⁅y⁻¹, r⁆ ∈ centreCQ Q a := hcen _ hyinv
    have hru : r * u = u * r := by
      have hmem : u ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) := by
        refine ⟨huQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        refine commutatorElement_eq_one_iff_mul_comm.mp ?_
        refine (GM.comm_eq_one_iff hD huQ haQ).mpr ?_
        rw [hπu, map_smul, LinearMap.smul_apply, M₀.alt, smul_eq_mul, mul_zero]
      exact hr u hmem
    have hsy : ⁅r * r, y⁆ = u ^ 2 := by
      have h1 : r * y * r⁻¹ = u * y := by rw [hu_eq]; group
      have h2 : r * u * r⁻¹ = u := by rw [hru]; group
      simp only [commutatorElement_def]
      calc r * r * y * (r * r)⁻¹ * y⁻¹ = r * (r * y * r⁻¹) * r⁻¹ * y⁻¹ := by group
        _ = r * (u * y) * r⁻¹ * y⁻¹ := by rw [h1]
        _ = (r * u * r⁻¹) * (r * y * r⁻¹) * y⁻¹ := by group
        _ = u ^ 2 := by rw [h2, h1, pow_two]; group
    have h1 := M₀.comm_eq _ hsQ y hy
    rw [hsy, M₀.sq_eq u huQ, hπu, M₀.Qf_smul] at h1
    rw [← h1]
    ring
  have hκ : c ^ 2 * M₀.Qf e₀ ≠ 0 := by
    intro h
    apply hc0
    have : c * (c * M₀.Qf e₀) = 0 := by rw [← mul_assoc, ← pow_two]; exact h
    rw [eq_neg_of_add_eq_zero_left hQf, mul_neg, mul_one, neg_eq_zero] at this
    exact this
  have hlin : ∀ t : K, t * M₀.B (M₀.π (r * r)) e₁ = t ^ 2 * (c ^ 2 * M₀.Qf e₀) := by
    intro t
    obtain ⟨y, hy, hyπ⟩ := M₀.π_surj (t • e₁)
    have h := hkey y hy
    simp only [hyπ, map_smul, LinearMap.smul_apply, smul_eq_mul, he₁, mul_one] at h
    rw [h]
    ring
  have hidem : ∀ t : K, t ^ 2 = t := by
    intro t
    have h1 := hlin t
    have h0 := hlin 1
    rw [one_mul, one_pow, one_mul] at h0
    rw [h0] at h1
    exact (mul_right_cancel₀ hκ h1).symm
  have hK : Nat.card K ≤ 2 := by
    classical
    have h01 : ∀ t : K, t = 0 ∨ t = 1 := by
      intro t
      have := hidem t
      have h : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, this, sub_self]
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    let f : K → Fin 2 := fun t => if t = 0 then 0 else 1
    have hf : Function.Injective f := by
      intro s t hst
      rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
      · rfl
      · simp [f] at hst
      · simp [f] at hst
      · rfl
    simpa using Nat.card_le_card_of_injective f hf
  have := H.q4
  rw [← hD.card] at this
  omega

end CFSG.RankThree.GF2n.Smith81
