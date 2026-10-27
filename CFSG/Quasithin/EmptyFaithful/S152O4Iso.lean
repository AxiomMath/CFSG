module

public import CFSG.Quasithin.EmptyFaithful.S152O4Kappa
public import CFSG.Quasithin.EmptyFaithful.S152O4FBasic

public section

namespace CFSG.Quasithin

namespace S152O4

open CFSG.Open CFSG.QuasithinUnique

section Iso

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def conjBack (c : V ≃* Vec) (f : MulAut Vec) : MulAut V := c.trans (f.trans c.symm)

omit [Finite V] in
theorem conjBack_apply (c : V ≃* Vec) (f : MulAut Vec) (v : V) :
    c (conjBack c f v) = f (c v) := by
  simp [conjBack]

omit [Finite V] in
theorem conjBack_mul (c : V ≃* Vec) (f g : MulAut Vec) :
    conjBack c (f * g) = conjBack c f * conjBack c g := by
  ext v
  apply c.injective
  simp [conjBack_apply]

omit [Finite V] in
theorem conjBack_one (c : V ≃* Vec) : conjBack c 1 = 1 := by
  ext v
  apply c.injective
  simp [conjBack_apply]

@[expose] def rhoV (c : V ≃* Vec) : Gam →* MulAut V where
  toFun g := conjBack c (rho g)
  map_one' := by rw [map_one, conjBack_one]
  map_mul' g h := by rw [map_mul, conjBack_mul]

omit [Finite V] in
theorem rhoV_apply (c : V ≃* Vec) (g : Gam) (v : V) : c (rhoV c g v) = act g (c v) :=
  conjBack_apply c (rho g) v

omit [Finite V] in
theorem rhoV_injective (c : V ≃* Vec) : Function.Injective (rhoV c) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply rho_ker g
  intro m
  have h1 := rhoV_apply c g (c.symm m)
  rw [hg] at h1
  simpa using h1.symm

omit [Finite V] in
theorem card_fixV_conjBack (c : V ≃* Vec) (f : MulAut Vec) :
    Nat.card ↥(fixV (Subgroup.zpowers (conjBack c f))) = Nat.card {m : Vec // f m = m} := by
  refine Nat.card_congr (Equiv.subtypeEquiv c.toEquiv fun v => ?_)
  rw [mem_fixV_zpowers_iff]
  constructor
  · intro h
    have := conjBack_apply c f v
    rw [h] at this
    exact this.symm
  · intro h
    apply c.injective
    rw [conjBack_apply]
    exact h

theorem nat_card_fix (g : Gam) : Nat.card {v : Vec // act g v = v} = 1 ∨
    Nat.card {v : Vec // act g v = v} = 4 ∨ Nat.card {v : Vec // act g v = v} = 16 := by
  simp only [Nat.card_eq_fintype_card]
  exact fixCount g

omit [Finite V] in
theorem rk_V_eq_four (hcard : Nat.card V = 16) : rk V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [hcard, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]

theorem even_rk_comm_of_card (hexp : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16) (g : MulAut V)
    (h : Nat.card ↥(fixV (Subgroup.zpowers g)) = 1 ∨ Nat.card ↥(fixV (Subgroup.zpowers g)) = 4 ∨
      Nat.card ↥(fixV (Subgroup.zpowers g)) = 16) :
    Even (rk (commV (Subgroup.zpowers g))) := by
  have hsum := rk_commV_add_rk_fixV g
  rw [rk_V_eq_four hcard] at hsum
  rw [Nat.even_iff]
  rcases h with h | h | h
  · have := S152O.rk_eq_of_card_eq hexp (n := 0) (by simpa using h)
    omega
  · have := S152O.rk_eq_of_card_eq hexp (n := 2) (by simpa using h)
    omega
  · have := S152O.rk_eq_of_card_eq hexp (n := 4) (by simpa using h)
    omega

theorem not_even_rk_comm_of_card (hexp : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (g : MulAut V) (h : Nat.card ↥(fixV (Subgroup.zpowers g)) = 8) :
    ¬ Even (rk (commV (Subgroup.zpowers g))) := by
  have hsum := rk_commV_add_rk_fixV g
  rw [rk_V_eq_four hcard] at hsum
  rw [Nat.even_iff]
  have := S152O.rk_eq_of_card_eq hexp (n := 3) (by simpa using h)
  omega

theorem om4_model {X : Subgroup (MulAut V)} (hX : IsOmegaFourPlus X) :
    ∃ (c : V ≃* Vec), (rhoV c).range = X := by
  obtain ⟨hcard, q, hq1, hq2, hq3, hXq⟩ := hX
  have hexp : ∀ w : V, w * w = 1 := S152O.sq_eq_one_of_nondeg hq1 hq2
  have hexp' : ∀ w : V, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hqe⟩ :=
    S153.exists_decomposition_of_plusType hexp hcard hq1 hq2 hq3
  let c : V ≃* Vec := (S1417.coordEquiv hinf hsup φ₁ φ₂).trans kappa
  have hqc : ∀ v, q v = detQ (c v) := by
    intro v
    rw [hqe v, quadOf_eq_qFloc hinf hsup φ₁ φ₂ v]
    exact qFloc_eq_detQ _
  refine ⟨c, ?_⟩
  have hOq : ∀ g : Gam, rhoV c g ∈ X := by
    intro g
    refine (hXq _).mpr ⟨?_, ?_⟩
    · intro v
      rw [hqc, hqc, rhoV_apply, detQ_act]
    · apply even_rk_comm_of_card hexp' hcard
      have := card_fixV_conjBack c (rho g)
      change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho g)))) = _ at this
      change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho g)))) = 1 ∨
        Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho g)))) = 4 ∨
        Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho g)))) = 16
      rw [this]
      exact nat_card_fix g
  have hle : (rhoV c).range ≤ X := by
    rintro _ ⟨g, rfl⟩
    exact hOq g
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
  have hO72 : Nat.card (orthogonalGroupOf q) = 72 := hS.card_X
  have hXO : X ≤ orthogonalGroupOf q := fun g hg => ((hXq g).mp hg).1
  set g₀ : MulAut V := conjBack c transV with hg₀
  have hg₀O : g₀ ∈ orthogonalGroupOf q := by
    intro v
    rw [hqc, hqc, hg₀, conjBack_apply, detQ_trans]
  have hg₀X : g₀ ∉ X := by
    intro hg
    refine not_even_rk_comm_of_card hexp' hcard g₀ ?_ ((hXq g₀).mp hg).2
    rw [hg₀, card_fixV_conjBack c transV]
    simp only [Nat.card_eq_fintype_card]
    exact transCount
  have hR36 : Nat.card (rhoV c).range = 36 := by
    rw [← card_Gam]
    exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective c)).toEquiv).symm
  have hX72 : Nat.card X ∣ 72 := by
    rw [← hO72]
    exact Subgroup.card_dvd_of_le hXO
  have hXge : 36 ≤ Nat.card X := by
    rw [← hR36]
    exact Subgroup.card_le_of_le hle
  have hR_dvd : 36 ∣ Nat.card X := by
    rw [← hR36]
    exact Subgroup.card_dvd_of_le hle
  have hXne : Nat.card X ≠ 72 := by
    intro h72
    have heq : X = orthogonalGroupOf q :=
      Subgroup.eq_of_le_of_card_ge hXO (by rw [hO72, h72])
    exact hg₀X (heq ▸ hg₀O)
  have hXle : Nat.card X ≤ 72 := Nat.le_of_dvd (by norm_num) hX72
  obtain ⟨k, hk⟩ := hR_dvd
  have hX36 : Nat.card X = 36 := by omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hX36, hR36])

end Iso

end S152O4

end CFSG.Quasithin
