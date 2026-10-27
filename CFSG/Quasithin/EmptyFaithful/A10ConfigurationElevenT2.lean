module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenSyl

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def HH : Subgroup G := oTwoUpper E.CE

@[expose] def H₁ : Subgroup G := H1m.map E.ι

@[expose] def tz : G := E.ι t0'

theorem HH_le_CE : E.HH ≤ E.CE := oTwoUpper_le _

theorem T₂_isPGroup : IsPGroup 2 E.T₂ := IsPGroup.of_card (n := 3) (by rw [E.card_T₂]; norm_num)

theorem tz_mem_T₂ : E.tz ∈ E.T₂ := ⟨t0', t0'_mem_T2h, rfl⟩

theorem T₂_comm_tz {y : G} (hy : y ∈ E.T₂) : y * E.tz = E.tz * y := by
  obtain ⟨w, hw, rfl⟩ := hy
  show E.ι w * E.ι t0' = E.ι t0' * E.ι w
  rw [← map_mul, ← map_mul, T2h_comm_t0' w hw]

theorem tz_sq : E.tz * E.tz = 1 := by
  show E.ι t0' * E.ι t0' = 1
  rw [← map_mul, t0'_sq, map_one]

theorem tz_ne_one : E.tz ≠ 1 := fun h => t0'_ne_one (E.injective (by rw [map_one]; exact h))

theorem tz_eq_pt (ℓ : Bool) : E.tz = E.pt ℓ 3 * E.pt ℓ 4 := by
  show E.ι t0' = E.ι (ptm ℓ 3) * E.ι (ptm ℓ 4)
  rw [← map_mul, ptm_three_four]

theorem t_mul_tz : E.t * E.tz = E.z := by
  show E.ι t0 * E.ι t0' = E.ι z0
  rw [← map_mul, t0_mul_t0'_eq]

theorem mem_HH_of_pow_three {x : G} (hx : x ∈ E.CE) (h3 : x ^ 3 = 1) : x ∈ E.HH := by
  refine mem_oTwoUpper_of_odd hx ?_
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)

theorem H₁_le_HH : E.H₁ ≤ E.HH := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨a, ha, b, hb, ha3, hb3, rfl⟩ := H1m_odd y hy
  rw [map_mul]
  have hodd : ∀ x ∈ H1m, x ^ 3 = 1 → E.ι x ∈ E.HH := fun x hx hx3 => by
    refine E.mem_HH_of_pow_three ?_ ?_
    · rw [E.mem_CE]
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_mul, ← map_mul, H1m_comm_E0 u hu x hx]
    · rw [← map_pow, hx3, map_one]
  exact E.HH.mul_mem (hodd a ha ha3) (hodd b hb hb3)

theorem W_mem_HH {ℓ : Bool} {c : G} (hcs : E.Acts ℓ c s3) (hc3 : c ^ 3 = 1)
    (hEc : ∀ x ∈ E.E₀, x * c = c * x) (hEW : ∀ x ∈ E.E₀, ∀ w ∈ E.W ℓ, x * w = w * x) {w : G}
    (hw : w ∈ E.W ℓ) : w ∈ E.HH := by
  have hcC : c ∈ E.CE := E.mem_CE.2 hEc
  have hcH : c ∈ E.HH := E.mem_HH_of_pow_three hcC hc3
  have hwC : w ∈ E.CE := E.mem_CE.2 fun x hx => hEW x hx w hw
  have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have key : (w * c) ^ 3 = 1 → w ∈ E.HH := fun h3 => by
    have h1 : w * c ∈ E.HH := E.mem_HH_of_pow_three (E.CE.mul_mem hwC hcC) h3
    have := E.HH.mul_mem h1 (E.HH.inv_mem hcH)
    simpa using this
  have hpair : ∀ i j : Fin 5, ((i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 3 ∧ j = 4)) →
      (E.pt ℓ i * E.pt ℓ j * c) ^ 3 = 1 := by
    intro i j hij
    have hk1 := E.acts_conj_pair hcs i j
    have hk2 := E.acts_conj_pair hcs (s3 i) (s3 j)
    rw [pow_three']
    calc (E.pt ℓ i * E.pt ℓ j * c) * (E.pt ℓ i * E.pt ℓ j * c) * (E.pt ℓ i * E.pt ℓ j * c)
        = (E.pt ℓ i * E.pt ℓ j) * (c * (E.pt ℓ i * E.pt ℓ j) * c⁻¹) *
            (c * (c * (E.pt ℓ i * E.pt ℓ j) * c⁻¹) * c⁻¹) * (c * c * c) := by group
      _ = 1 := by
        rw [hk1, hk2, hc3', mul_one]
        have h := congrArg E.ι (W_norm ℓ i j hij)
        simp only [map_mul, map_one] at h
        exact h
  rcases E.mem_W_iff.1 hw with rfl | rfl | rfl | rfl
  · exact E.HH.one_mem
  · exact key (hpair 3 4 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · exact key (hpair 0 3 (Or.inl ⟨rfl, rfl⟩))
  · exact key (hpair 0 4 (Or.inr (Or.inl ⟨rfl, rfl⟩)))

theorem T₂_le_HH {c : G} (hcs : E.Acts false c s3) (hc3 : c ^ 3 = 1)
    (hEc : ∀ x ∈ E.E₀, x * c = c * x) (hEW : ∀ x ∈ E.E₀, ∀ w ∈ E.W false, x * w = w * x) :
    E.T₂ ≤ E.HH := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨v, hv, w, hw, rfl⟩ := T2h_decomp y hy
  rw [map_mul]
  refine E.HH.mul_mem ?_ ?_
  · exact E.H₁_le_HH ⟨v, V2_le_H1m hv, rfl⟩
  · exact E.W_mem_HH hcs hc3 hEc hEW ⟨w, hw, rfl⟩

theorem card_le_8 [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPH : P ≤ E.HH) : Nat.card P ≤ 8 := by
  classical
  have hPC : P ≤ E.CE := hPH.trans E.HH_le_CE
  have hcomm : ∀ (p : P) (q : E.E₀), Commute (P.subtype p) (E.E₀.subtype q) := fun p q => by
    show (p : G) * (q : G) = (q : G) * (p : G)
    exact (E.mem_CE.1 (hPC p.2) q q.2).symm
  let φ : ↥P × ↥E.E₀ →* G := MonoidHom.noncommCoprod P.subtype E.E₀.subtype hcomm
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨p, q⟩ hpq
    have h1 : (p : G) * (q : G) = 1 := by
      simpa [φ, MonoidHom.noncommCoprod_apply] using hpq
    have hpq' : (p : G) = ((q : G))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hpE : (p : G) ∈ E.E₀ := by
      rw [hpq']
      exact E.E₀.inv_mem q.2
    have hp1 : (p : G) = 1 := E.E₀_inf_H hT hM hpE (hPH p.2)
    have hq1 : (q : G) = 1 := by
      rw [hp1, one_mul] at h1
      exact h1
    have hp : p = 1 := Subtype.ext hp1
    have hq : q = 1 := Subtype.ext hq1
    rw [hp, hq]
    exact Subgroup.one_mem _
  have hRC : φ.range ≤ E.CE := by
    rintro _ ⟨⟨p, q⟩, rfl⟩
    simp only [φ, MonoidHom.noncommCoprod_apply]
    exact E.CE.mul_mem (hPC p.2) (E.E₀_le_CE q.2)
  have hcardR : Nat.card φ.range = Nat.card P * 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, E.card_E₀]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  have hRp : IsPGroup 2 φ.range := IsPGroup.of_card (n := a + 2) (by
    rw [hcardR, ha]
    ring)
  have h32 := E.card_le_32 hT hM hRp hRC
  rw [hcardR] at h32
  omega

theorem mem_T₂_of_centralizes_tz [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) (hT₂H : E.T₂ ≤ E.HH) {y : G}
    (hy : y ∈ E.HH) (hyt : y * E.tz = E.tz * y) : y ∈ E.T₂ := by
  have hD : E.T₂ ≤ E.HH ⊓ Subgroup.centralizer ({E.tz} : Set G) := fun x hx =>
    ⟨hT₂H hx, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (E.T₂_comm_tz hx).symm⟩
  have hDJ : E.HH ⊓ Subgroup.centralizer ({E.tz} : Set G) ≤ E.J := by
    rintro x ⟨hxH, hxt⟩
    have hxC := E.HH_le_CE hxH
    have hxt0 : E.t * x = x * E.t := E.mem_CE.1 hxC E.t E.t_mem_E₀
    have hxtz : E.tz * x = x * E.tz := Subgroup.mem_centralizer_iff.1 hxt E.tz rfl
    have hxz : E.z * x = x * E.z := by
      rw [← E.t_mul_tz]
      calc E.t * E.tz * x = E.t * (E.tz * x) := by group
        _ = E.t * (x * E.tz) := by rw [hxtz]
        _ = (E.t * x) * E.tz := by group
        _ = (x * E.t) * E.tz := by rw [hxt0]
        _ = x * (E.t * E.tz) := by group
    rw [← E.lemma_13_9_7 hEven hT hM, Subgroup.mem_centralizer_iff]
    rintro h (rfl | rfl)
    · exact hxz
    · exact hxt0
  have hDp : IsPGroup 2 ↥(E.HH ⊓ Subgroup.centralizer ({E.tz} : Set G)) :=
    E.J_isPGroup.to_le hDJ
  have hcard := E.card_le_8 hT hM hDp inf_le_left
  have heq : E.T₂ = E.HH ⊓ Subgroup.centralizer ({E.tz} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hD (by rw [E.card_T₂]; exact hcard)
  rw [heq]
  exact ⟨hy, Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hyt.symm⟩

end Emb

end CFSG.Quasithin.A10
