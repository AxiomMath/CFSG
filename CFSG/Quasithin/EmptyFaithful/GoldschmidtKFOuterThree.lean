module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFExpThree
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFComp

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

theorem KFHyp.Yp_le_I (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) : Yp ≤ I := by
  rw [h.hIsup]
  exact le_sup_of_le_left le_sup_right

theorem KFHyp.X_comm (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {a b : G} (ha : a ∈ X) (hb : b ∈ X) :
    a * b = b * a := by
  have h1 := h.hinv (a * b) (X.mul_mem ha hb)
  have h2 : f * (a * b) * f⁻¹ = (f * a * f⁻¹) * (f * b * f⁻¹) := by group
  rw [h2, h.hinv a ha, h.hinv b hb, mul_inv_rev] at h1
  have h3 := congrArg (fun w : G => w⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at h3
  exact h3.symm

theorem KFHyp.exists_mem_X_not_mem_L (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) :
    ∃ x ∈ X, x ∉ L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyY, hy3, hyL, -⟩ := h.r.hy
  by_contra hcon
  push Not at hcon
  have hXs : IsPGroup 3 ↥(X.subgroupOf Yp) :=
    h.hX3.of_equiv (Subgroup.subgroupOfEquivOfLe h.hXY).symm
  let Xs : Sylow 3 ↥Yp := hXs.toSylow h.hXidx
  have hcard : Nat.card (X.subgroupOf Yp) = 3 ^ (Nat.card ↥Yp).factorization 3 := by
    have h1 := Sylow.card_eq_multiplicity Xs
    have h2 : (Xs : Subgroup ↥Yp) = X.subgroupOf Yp := IsPGroup.toSylow_coe hXs h.hXidx
    rwa [h2] at h1
  have hy3' : (⟨y, hyY⟩ : ↥Yp) ^ 3 = 1 := Subtype.ext (by simp [← hy3])
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hcard
    (isPGroup_zpowers_of_cube hy3')
  have hyX : ((MulAut.conj g) (⟨y, hyY⟩ : ↥Yp) : ↥Yp) ∈ X.subgroupOf Yp :=
    hg ⟨_, Subgroup.mem_zpowers _, rfl⟩
  have hyX' : (g : G) * y * (g : G)⁻¹ ∈ X := hyX
  have hgI : (g : G) ∈ I := h.Yp_le_I g.2
  have hL' : (g : G) * y * (g : G)⁻¹ ∈ L := hcon _ hyX'
  have hyL' : y ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (h.r.hNL (I.inv_mem hgI)) _).mp hL'
    simpa [mul_assoc] using this
  exact hyL (Subgroup.mem_sup_left hyL')

theorem KFHyp.exists_mem_X_centralizes_sigma (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) :
    ∃ y ∈ X, y ∉ L ∧ (τ * f) * y = y * (τ * f) := by
  classical
  obtain ⟨x₀, hx₀X, hx₀L⟩ := h.exists_mem_X_not_mem_L
  have hσ2 := h.sigma_sq
  have hσinv : (τ * f)⁻¹ = τ * f := inv_eq_of_mul_eq_one_right hσ2
  have hσN : τ * f ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem h.hτN h.hfN
  have hx₁X : (τ * f) * x₀ * (τ * f)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hσN x₀).mp hx₀X
  set x₁ : G := (τ * f) * x₀ * (τ * f)⁻¹ with hx₁
  obtain ⟨a, ha⟩ := h.hX3.exists_card_eq
  have hodd : Odd (Nat.card ↥X) := by rw [ha]; exact Odd.pow (by decide)
  set m := Nat.card ↥X with hm
  set e := (m + 1) / 2 with he
  have h2e : 2 * e = m + 1 := Nat.two_mul_div_two_of_even hodd.add_one
  have hpowm : ∀ z ∈ X, z ^ m = 1 := fun z hz => by
    have h1 : (⟨z, hz⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2
  obtain ⟨lam, hlam⟩ : ∃ lam : G, lam = x₁ * x₀⁻¹ := ⟨_, rfl⟩
  have hlamX : lam ∈ X := hlam ▸ X.mul_mem hx₁X (X.inv_mem hx₀X)
  have hlamL : lam ∈ L := by
    have hk := h.commutator_sigma_mem (h.Yp_le_I (h.hXY hx₀X))
    have key : ∀ s x : G, s⁻¹ = s → s * x * s⁻¹ * x⁻¹ = ((x * s * x⁻¹) * s)⁻¹ := by
      intro s x hs
      simp only [mul_inv_rev, inv_inv, hs, mul_assoc]
    rw [hlam, hx₁, key _ _ hσinv]
    exact L.inv_mem hk
  have hx₁eq : x₁ = lam * x₀ := by rw [hlam]; group
  have hcomm : x₀ * x₁ = x₁ * x₀ := h.X_comm hx₀X hx₁X
  have hlx : lam * x₀ = x₀ * lam := h.X_comm hlamX hx₀X
  set c : G := (x₀ * x₁) ^ e with hc
  have hcX : c ∈ X := X.pow_mem (X.mul_mem hx₀X hx₁X) e
  have hcσ : (τ * f) * c = c * (τ * f) := by
    have h1 : (τ * f) * (x₀ * x₁) * (τ * f)⁻¹ = x₀ * x₁ := by
      have h2 : (τ * f) * x₁ * (τ * f)⁻¹ = x₀ := by
        rw [hx₁]
        calc (τ * f) * ((τ * f) * x₀ * (τ * f)⁻¹) * (τ * f)⁻¹
            = ((τ * f) * (τ * f)) * x₀ * ((τ * f)⁻¹ * (τ * f)⁻¹) := by group
          _ = x₀ := by rw [hσ2, hσinv, hσ2]; group
      calc (τ * f) * (x₀ * x₁) * (τ * f)⁻¹
          = ((τ * f) * x₀ * (τ * f)⁻¹) * ((τ * f) * x₁ * (τ * f)⁻¹) := by group
        _ = x₁ * x₀ := by rw [← hx₁, h2]
        _ = x₀ * x₁ := hcomm.symm
    have h3 : (τ * f) * c * (τ * f)⁻¹ = c := by
      have : (τ * f) * (x₀ * x₁) ^ e * (τ * f)⁻¹ = ((τ * f) * (x₀ * x₁) * (τ * f)⁻¹) ^ e := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
      rw [hc, this, h1]
    calc (τ * f) * c = (τ * f) * c * (τ * f)⁻¹ * (τ * f) := by group
      _ = c * (τ * f) := by rw [h3]
  have hcL : c ∉ L := by
    intro hcL
    have h1 : x₀ * x₁ = lam * x₀ ^ 2 := by
      calc x₀ * x₁ = x₀ * (lam * x₀) := by rw [hx₁eq]
        _ = (x₀ * lam) * x₀ := by rw [mul_assoc]
        _ = (lam * x₀) * x₀ := by rw [hlx]
        _ = lam * x₀ ^ 2 := by rw [mul_assoc, pow_two]
    have hcomm' : Commute lam (x₀ ^ 2) := Commute.pow_right hlx 2
    have h2 : c = lam ^ e * x₀ := by
      rw [hc, h1, hcomm'.mul_pow, ← pow_mul, h2e, pow_succ, hpowm x₀ hx₀X, one_mul]
    have h3 : x₀ = (lam ^ e)⁻¹ * c := by rw [h2]; group
    exact hx₀L (h3 ▸ L.mul_mem (L.inv_mem (L.pow_mem hlamL e)) hcL)
  exact ⟨c, hcX, hcL, hcσ⟩

end CFSG.Quasithin.SBd19F
