module

public import CFSG.Quasithin.EmptyFaithful.S152Y16
public import CFSG.Quasithin.EmptyFaithful.S152Y09
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.EmptyFaithful.S152Y13

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G]

section Basic

open Data

variable {T Mc M : Subgroup G}

theorem Rcs_le_Ls (T Mc M : Subgroup G) : Rcs Mc M ≤ Ls T Mc M :=
  imageOTwoQuot_mono (le_conjClosure _ _)

theorem pRank_Mstar_le_two (h : Data T Mc M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (OTwoQuot M)) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥M := CFSG.Open.pCore 2 ↥M with hN
  have hnd : ¬ p ∣ Nat.card N := by
    intro hd
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2).exists_card_eq
    rw [hk] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have h1 := CFSG.SectionRank.pRank_quotient_eq (p := p) N hnd
  have h2 := pRank_top_subtype (p := p) M
  have h3 := pRank_le_two_of_isTwoLocal h.qtfe.qtke h.inM.1.1 hp hp2
  calc CFSG.Open.pRank p (⊤ : Subgroup (OTwoQuot M)) = CFSG.Open.pRank p (⊤ : Subgroup ↥M) := h1
    _ = CFSG.Open.pRank p M := h2
    _ ≤ 2 := h3

theorem K_central_Ys (h : Data T Mc M) :
    ∀ k ∈ Ys T Mc M ⊓ (piStar h).ker, ∀ x ∈ Ys T Mc M, x * k = k * x :=
  fun k hk x hx => K_central h k hk x (Ys_le_Ls h hx)

theorem Rcs_comm_K (h : Data T Mc M) :
    ∀ r ∈ Rcs Mc M, ∀ k ∈ Ys T Mc M ⊓ (piStar h).ker, r * k = k * r :=
  fun r hr k hk => Rcs_centralizes h r hr k ⟨Ys_le_Y0s h hk.1, hk.2⟩

theorem Ys_abelian_of_cyclic (h : Data T Mc M) (hcyc : IsCyclic ↥(autOn (yOf152 T Mc M) (V154 T Mc M))) :
    ∀ a ∈ Ys T Mc M, ∀ b ∈ Ys T Mc M, a * b = b * a := by
  let f : ↥(Ys T Mc M) →* ↥(autOn (yOf152 T Mc M) (V154 T Mc M)) :=
    MonoidHom.codRestrict ((piStar h).comp (Ys T Mc M).subtype) (autOn (yOf152 T Mc M) (V154 T Mc M))
      (fun u => by rw [← map_Ys h]; exact Subgroup.mem_map_of_mem _ u.2)
  have hf : f.ker ≤ Subgroup.center ↥(Ys T Mc M) := by
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro g
    have hu1 : piStar h (u : OTwoQuot M) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
      simpa [f] using this
    have hmem : (u : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := ⟨u.2, hu1⟩
    exact Subtype.ext (K_central_Ys h _ hmem (g : OTwoQuot M) g.2)
  intro a ha b hb
  have : IsMulCommutative ↥(Ys T Mc M) := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hf
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(Ys T Mc M)) ⟨b, hb⟩)

theorem Ys_abelian_of_eigen (h : Data T Mc M)
    (hYE : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M))
    (hEab : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∀ b ∈ oTwoUpper (mBar0 T Mc M), a * b = b * a)
    {ρ e₁ e₂ : MulAut (V154 T Mc M)} (hρ : ρ ∈ autOn (rcOf Mc M) (V154 T Mc M))
    (he₁ : e₁ ∈ oTwoUpper (mBar0 T Mc M)) (he₂ : e₂ ∈ oTwoUpper (mBar0 T Mc M))
    (hgen : ∀ a ∈ oTwoUpper (mBar0 T Mc M), ∃ i j : ℕ, a = e₁ ^ i * e₂ ^ j)
    (h₁ : ρ * e₁ * ρ⁻¹ = e₁) (h₂ : ρ * e₂ * ρ⁻¹ = e₂⁻¹) :
    ∀ a ∈ Ys T Mc M, ∀ b ∈ Ys T Mc M, a * b = b * a := by
  obtain ⟨r, hrR, hrρ⟩ := h.exists_Rcs_of_mem_autOn hρ
  have hrN : r ∈ Subgroup.normalizer (Ys T Mc M : Set (OTwoQuot M)) :=
    Ls_le_normalizer_Ys h (Rcs_le_Ls T Mc M hrR)
  have hKc := K_central_Ys h
  have hrK := Rcs_comm_K h r hrR
  have hmapY : (Ys T Mc M).map (piStar h) = oTwoUpper (mBar0 T Mc M) := by
    rw [map_Ys h, hYE]
  obtain ⟨y₁, hy₁, hπ₁⟩ := Subgroup.mem_map.mp (hmapY ▸ he₁)
  obtain ⟨y₂, hy₂, hπ₂⟩ := Subgroup.mem_map.mp (hmapY ▸ he₂)
  have hconj : ∀ y ∈ Ys T Mc M, r * y * r⁻¹ ∈ Ys T Mc M := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hrN y).mp hy
  have hk₁ : y₁⁻¹ * (r * y₁ * r⁻¹) ∈ Ys T Mc M ⊓ (piStar h).ker := by
    refine ⟨(Ys T Mc M).mul_mem ((Ys T Mc M).inv_mem hy₁) (hconj y₁ hy₁), ?_⟩
    refine MonoidHom.mem_ker.mpr ?_
    simp only [map_mul, map_inv, hπ₁, hrρ, h₁, inv_mul_cancel]
  have hk₂ : y₂ * (r * y₂ * r⁻¹) ∈ Ys T Mc M ⊓ (piStar h).ker := by
    refine ⟨(Ys T Mc M).mul_mem hy₂ (hconj y₂ hy₂), ?_⟩
    refine MonoidHom.mem_ker.mpr ?_
    simp only [map_mul, map_inv, hπ₂, hrρ, h₂, mul_inv_cancel]
  set k₁ := y₁⁻¹ * (r * y₁ * r⁻¹) with hk₁def
  set k₂ := y₂ * (r * y₂ * r⁻¹) with hk₂def
  have e₁' : r * y₁ * r⁻¹ = y₁ * k₁ := by rw [hk₁def]; group
  have e₂' : r * y₂ * r⁻¹ = y₂⁻¹ * k₂ := by rw [hk₂def]; group
  have hcY : ⁅y₁, y₂⁆ ∈ Ys T Mc M :=
    (Ys T Mc M).mul_mem ((Ys T Mc M).mul_mem ((Ys T Mc M).mul_mem hy₁ hy₂)
      ((Ys T Mc M).inv_mem hy₁)) ((Ys T Mc M).inv_mem hy₂)
  have hcK : ⁅y₁, y₂⁆ ∈ Ys T Mc M ⊓ (piStar h).ker := by
    refine ⟨hcY, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_commutatorElement, hπ₁, hπ₂]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hEab _ he₁ _ he₂)
  have hrc : r * ⁅y₁, y₂⁆ * r⁻¹ = ⁅y₁, y₂⁆ := by
    rw [hrK _ hcK]; group
  have hconjc : r * ⁅y₁, y₂⁆ * r⁻¹ = ⁅r * y₁ * r⁻¹, r * y₂ * r⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have hy₁k₁ : y₁ * k₁ ∈ Ys T Mc M := (Ys T Mc M).mul_mem hy₁ hk₁.1
  have hstep : ⁅r * y₁ * r⁻¹, r * y₂ * r⁻¹⁆ = ⁅y₁, y₂⁻¹⁆ := by
    rw [e₁', e₂', commutator_mul_central_right (hKc k₂ hk₂ _ hy₁k₁).symm,
      commutator_mul_central_left (hKc k₁ hk₁ _ ((Ys T Mc M).inv_mem hy₂)).symm]
  have hinvc : ⁅y₁, y₂⁻¹⁆ = ⁅y₁, y₂⁆⁻¹ := by
    have e : ⁅y₁, y₂⁻¹⁆ = y₂⁻¹ * ⁅y₁, y₂⁆⁻¹ * y₂ := by
      simp only [commutatorElement_def]; group
    have hcy : y₂⁻¹ * ⁅y₁, y₂⁆ * y₂ = ⁅y₁, y₂⁆ := by
      rw [mul_assoc, ← hKc _ hcK y₂ hy₂, inv_mul_cancel_left]
    have : y₂⁻¹ * ⁅y₁, y₂⁆⁻¹ * y₂ = (y₂⁻¹ * ⁅y₁, y₂⁆ * y₂)⁻¹ := by group
    rw [e, this, hcy]
  have hcc : ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆⁻¹ := hrc.symm.trans (hconjc.trans (hstep.trans hinvc))
  have hc2 : ⁅y₁, y₂⁆ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    calc ⁅y₁, y₂⁆ * ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆ * ⁅y₁, y₂⁆⁻¹ := by rw [← hcc]
      _ = 1 := mul_inv_cancel _
  have hc1 : ⁅y₁, y₂⁆ = 1 :=
    eq_one_of_odd_of_two_power (Ys_inf_ker_odd h _ hcK) hc2
  have hcomm12 : Commute y₁ y₂ := commutatorElement_eq_one_iff_mul_comm.mp hc1
  have hdecomp : ∀ a ∈ Ys T Mc M, ∃ k ∈ Ys T Mc M ⊓ (piStar h).ker, ∃ i j : ℕ,
      a = k * (y₁ ^ i * y₂ ^ j) := by
    intro a ha
    obtain ⟨i, j, hij⟩ := hgen _ (piStar_mem_of_mem_Ys h ha)
    refine ⟨a * (y₁ ^ i * y₂ ^ j)⁻¹, ⟨(Ys T Mc M).mul_mem ha
      ((Ys T Mc M).inv_mem ((Ys T Mc M).mul_mem ((Ys T Mc M).pow_mem hy₁ i)
        ((Ys T Mc M).pow_mem hy₂ j))), ?_⟩, i, j, (inv_mul_cancel_right a _).symm⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [map_mul, map_inv, map_mul, map_pow, map_pow, hπ₁, hπ₂, ← hij, mul_inv_cancel]
  intro a ha b hb
  obtain ⟨ka, hka, i, j, rfl⟩ := hdecomp a ha
  obtain ⟨kb, hkb, i', j', rfl⟩ := hdecomp b hb
  have hpow : ∀ i j : ℕ, y₁ ^ i * y₂ ^ j ∈ Ys T Mc M := fun i j =>
    (Ys T Mc M).mul_mem ((Ys T Mc M).pow_mem hy₁ i) ((Ys T Mc M).pow_mem hy₂ j)
  have h5 : Commute (y₁ ^ i * y₂ ^ j) (y₁ ^ i' * y₂ ^ j') :=
    Commute.mul_left
      (Commute.mul_right ((Commute.refl y₁).pow_pow i i') (hcomm12.pow_pow i j'))
      (Commute.mul_right (hcomm12.symm.pow_pow j i') ((Commute.refl y₂).pow_pow j j'))
  have hkab : ka * kb = kb * ka := hKc kb hkb ka hka.1
  have hkb' : (y₁ ^ i * y₂ ^ j) * kb = kb * (y₁ ^ i * y₂ ^ j) := hKc kb hkb _ (hpow i j)
  have hka' : (y₁ ^ i' * y₂ ^ j') * ka = ka * (y₁ ^ i' * y₂ ^ j') := hKc ka hka _ (hpow i' j')
  generalize y₁ ^ i * y₂ ^ j = A at h5 hkb' ⊢
  generalize y₁ ^ i' * y₂ ^ j' = B at h5 hka' ⊢
  calc ka * A * (kb * B) = ka * (A * kb) * B := by group
    _ = ka * (kb * A) * B := by rw [hkb']
    _ = (ka * kb) * (A * B) := by group
    _ = (kb * ka) * (B * A) := by rw [hkab, h5.eq]
    _ = kb * (ka * B) * A := by group
    _ = kb * (B * ka) * A := by rw [hka']
    _ = kb * B * (ka * A) := by group

end Basic

end S152Y

end CFSG.Quasithin
