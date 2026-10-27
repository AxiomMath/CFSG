module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTD
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTS

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5tf_inner_fixed {R : Subgroup (MulAut (hypPSU hK 2 1))} (hRP : R ≤ Pi hK)
    (hR : IsPGroup 2 R)
    (hRf : ∀ ρ ∈ R, ρ * fieldP hK (bar5 hK) = fieldP hK (bar5 hK) * ρ) :
    Nat.card R ≤ (2 ^ f) ^ 4 := by
  have inj := conj_injective (u5_center_eq_bot hK)
  set R₀ : Subgroup (hypPSU hK 2 1) :=
    R.comap (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)) with hR₀
  have h2 : IsPGroup 2 R₀ := hR.comap_of_injective _ inj
  have hmap : R₀.map (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)) = R := by
    rw [hR₀, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hRP
  have hfix : ∀ x ∈ R₀, fieldP hK (bar5 hK) x = x := by
    intro x hx
    have h1 := hRf (MulAut.conj x) hx
    have h3 := aut5_mul_cj5_mul_inv hK (fieldP hK (bar5 hK)) x
    apply inj
    have h4 : fieldP hK (bar5 hK) * MulAut.conj x * (fieldP hK (bar5 hK))⁻¹ =
        MulAut.conj x := by
      rw [← h1]
      group
    exact h3.symm.trans h4
  have h4 := un5_card_le_of_fixed_Y hK h2 hfix
  have h5 : Nat.card R = Nat.card R₀ := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective inj
  rwa [h5]

theorem un5tf_isPGroup_Uh : IsPGroup 2 ↥(Uh hK) :=
  CFSG.ABGLocalTools.IsSylowOf.isPGroup (isSylow_Uh (u5_center_eq_bot hK))

theorem un5tf_card_Cf : Nat.card ↥(Uh hK ⊓ Subgroup.centralizer
    ({fieldP hK (bar5 hK)} : Set (MulAut (hypPSU hK 2 1)))) = (2 ^ f) ^ 4 := by
  refine le_antisymm (un5tf_inner_fixed hK (inf_le_left.trans Uh_le_Pi)
    ((un5tf_isPGroup_Uh hK).to_le inf_le_left) fun ρ hρ => ?_) (un5_card_fixUh_ge hK)
  exact Subgroup.mem_centralizer_singleton_iff.1 hρ.2

@[expose] def un5tfFp (T : Subgroup (MulAut (hypPSU hK 2 1))) : Subgroup (K ≃+* K) :=
  T.comap (fieldP hK)

theorem un5tf_decomp {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) {τ : MulAut (hypPSU hK 2 1)}
    (hτ : τ ∈ T) : ∃ u ∈ Uh hK, ∃ σ ∈ un5tfFp hK T, τ = u * fieldP hK σ := by
  obtain ⟨u, hu, σ, rfl⟩ := hT τ hτ
  refine ⟨u, hu, σ, ?_, rfl⟩
  have := T.mul_mem (T.inv_mem (hU hu)) hτ
  rwa [inv_mul_cancel_left] at this

theorem un5tf_card_T {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) :
    Nat.card T = Nat.card (Uh hK) * Nat.card (un5tfFp hK T) := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : Uh hK × un5tfFp hK T => (⟨(p.1 : MulAut (hypPSU hK 2 1)) * fieldP hK p.2,
      T.mul_mem (hU p.1.2) p.2.2⟩ : T)) ⟨?_, ?_⟩)
  · rintro ⟨u, σ⟩ ⟨u', σ'⟩ e
    obtain ⟨h1, h2⟩ := un5t_decomp_unique hK u.2 u'.2 (congrArg Subtype.val e)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨τ, hτ⟩
    obtain ⟨u, hu, σ, hσ, rfl⟩ := un5tf_decomp hK hU hT hτ
    exact ⟨(⟨u, hu⟩, ⟨σ, hσ⟩), rfl⟩

theorem un5tf_comm_bar (σ : K ≃+* K) :
    fieldP hK σ * fieldP hK (bar5 hK) = fieldP hK (bar5 hK) * fieldP hK σ := by
  rw [← map_mul, ← map_mul, fld5_comm hK σ (bar5 hK)]

theorem un5tf_mul_comm_iff (u : MulAut (hypPSU hK 2 1)) (σ : K ≃+* K) :
    Commute (u * fieldP hK σ) (fieldP hK (bar5 hK)) ↔ Commute u (fieldP hK (bar5 hK)) := by
  have hc : Commute (fieldP hK σ) (fieldP hK (bar5 hK)) := un5tf_comm_bar hK σ
  constructor
  · intro h
    have := h.mul_left hc.inv_left
    simpa [mul_assoc] using this
  · intro h
    exact h.mul_left hc

theorem un5tf_card_Tf {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) :
    Nat.card (spTf T (fieldP hK (bar5 hK))) = (2 ^ f) ^ 4 * Nat.card (un5tfFp hK T) := by
  rw [← un5tf_card_Cf hK, ← Nat.card_prod]
  symm
  have hmem : ∀ (u : MulAut (hypPSU hK 2 1)) (σ : K ≃+* K), u ∈ Uh hK → σ ∈ un5tfFp hK T →
      Commute u (fieldP hK (bar5 hK)) →
      u * fieldP hK σ ∈ spTf T (fieldP hK (bar5 hK)) := fun u σ hu hσ hc =>
    Subgroup.mem_inf.2 ⟨T.mul_mem (hU hu) hσ, Subgroup.mem_centralizer_singleton_iff.2
      ((un5tf_mul_comm_iff hK u σ).2 hc).eq⟩
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : ↥(Uh hK ⊓ Subgroup.centralizer ({fieldP hK (bar5 hK)} :
        Set (MulAut (hypPSU hK 2 1)))) × un5tfFp hK T =>
      (⟨(p.1 : MulAut (hypPSU hK 2 1)) * fieldP hK p.2,
        hmem _ _ p.1.2.1 p.2.2 (Subgroup.mem_centralizer_singleton_iff.1 p.1.2.2 : _)⟩ :
          spTf T (fieldP hK (bar5 hK)))) ⟨?_, ?_⟩)
  · rintro ⟨u, σ⟩ ⟨u', σ'⟩ e
    obtain ⟨h1, h2⟩ := un5t_decomp_unique hK u.2.1 u'.2.1 (congrArg Subtype.val e)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro ⟨τ, hτ⟩
    obtain ⟨u, hu, σ, hσ, rfl⟩ := un5tf_decomp hK hU hT hτ.1
    have hc := (un5tf_mul_comm_iff hK u σ).1 (Subgroup.mem_centralizer_singleton_iff.1 hτ.2)
    exact ⟨(⟨u, hu, Subgroup.mem_centralizer_singleton_iff.2 hc.eq⟩, ⟨σ, hσ⟩), rfl⟩

end CFSG.Quasithin.H13.F431.Un.OL5
