module

public import CFSG.Quasithin.Background.F918Z3A1Irr

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace Z3A1

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

omit [Finite V] in
theorem isA2_of_le {H K B : Subgroup (MulAut V)} (hB : IsA2 H B) (hHK : H ≤ K) : IsA2 K B :=
  ⟨hB.1.trans hHK, hB.2⟩

theorem QhatStar_of_le {G H A : Subgroup (MulAut V)} (hHG : H ≤ G) (hAH : A ≤ H)
    (hA : A ∈ QhatStar G) : qhatOf H = qhatOf G ∧ A ∈ QhatStar H := by
  obtain ⟨r, hr, hr2, hAr, hmin⟩ := QhatStar_spec hA
  have hA2G : IsA2 G A := hAr.1.1
  have hA2H : IsA2 H A := ⟨hAH, hA2G.2.1, hA2G.2.2⟩
  have hk : commSeries A 3 = ⊥ := hAr.2
  have hrAV : rAV A = r := hAr.1.2
  have hHr : qhatOf H = (r : WithTop ℚ) := by
    refine le_antisymm (kq_le_iff.mpr ⟨A, hA2H, hk, hrAV.le⟩) ?_
    refine le_kq_iff.mpr fun B hB hBk => ?_
    exact le_kq_iff.mp hr.ge B (isA2_of_le hB hHG) hBk
  refine ⟨hHr.trans hr.symm, r, hHr, hr2, ⟨⟨hA2H, hrAV.le⟩, hk⟩, fun B hB hBA => ?_⟩
  exact hmin B ⟨⟨isA2_of_le hB.1.1 hHG, hB.1.2⟩, hB.2⟩ hBA

omit [Finite V] in
theorem le_stabSub_of_inv {A : Subgroup (MulAut V)} {I : Subgroup V}
    (hIA : ∀ a ∈ A, ∀ v ∈ I, a v ∈ I) : A ≤ stabSub I := by
  intro a ha u
  refine ⟨fun hu => ?_, hIA a ha u⟩
  have := hIA a⁻¹ (A.inv_mem ha) _ hu
  simpa using this

theorem commSub_ne_bot (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} {I : Subgroup V}
    (hI : I ≠ ⊥) (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D)
    (hnc : ∃ a ∈ A, ∃ y ∈ D, a * y ≠ y * a) : commSub I A ≠ ⊥ := by
  intro h
  rw [commSub_eq_bot_iff] at h
  obtain ⟨a, ha, y, hy, hne⟩ := hnc
  apply hne
  have hc : a * y * a⁻¹ * y⁻¹ ∈ D := D.mul_mem (hAD a ha y hy) (D.inv_mem hy)
  have h1 : a * y * a⁻¹ * y⁻¹ = 1 := by
    refine faithful hZ hI hID _ hc fun v hv => ?_
    have hv1 : y⁻¹ v ∈ I := hID _ (D.inv_mem hy) v hv
    have hv2 : a⁻¹ (y⁻¹ v) = y⁻¹ v := h hv1 a⁻¹ (A.inv_mem ha)
    have hv3 : a v = v := h hv a ha
    show a (y (a⁻¹ (y⁻¹ v))) = v
    have hv4 : y (y⁻¹ v) = v := by simp
    rw [hv2, hv4, hv3]
  have h2 : a * y * a⁻¹ = y := mul_inv_eq_one.mp h1
  exact mul_inv_eq_iff_eq_mul.mp h2

omit [Finite V] in
theorem mul_comm_of_inf_eq_bot {D : Subgroup (MulAut V)} {I J : Subgroup V}
    (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I) (hJD : ∀ y ∈ D, ∀ v ∈ J, y v ∈ J)
    (hJf : ∀ y ∈ D, (∀ v ∈ J, y v = v) → y = 1) (hIJ : J ⊓ I = ⊥)
    {a : MulAut V} (ha : ∀ u : V, a u * u⁻¹ ∈ I) {y : MulAut V} (hy : y ∈ D)
    (hy' : a * y * a⁻¹ ∈ D) : a * y = y * a := by
  obtain ⟨y', hy'e⟩ : ∃ y' : MulAut V, y' = a * y * a⁻¹ := ⟨_, rfl⟩
  rw [← hy'e] at hy'
  have key : ∀ v ∈ J, y' v = y v := by
    intro v hv
    have e1 : y' (a v) = a (y v) := by rw [hy'e]; simp
    have h1 : y' (a v) = y' (a v * v⁻¹) * y' v := by
      rw [← map_mul]
      congr 1
      group
    have hi1 : y' (a v * v⁻¹) ∈ I := hID y' hy' _ (ha v)
    have hi2 : a (y v) * (y v)⁻¹ ∈ I := ha (y v)
    have hmem : y' v * (y v)⁻¹ ∈ I := by
      have : y' v * (y v)⁻¹ = (y' (a v * v⁻¹))⁻¹ * (a (y v) * (y v)⁻¹) := by
        rw [← e1, h1]
        group
      rw [this]
      exact I.mul_mem (I.inv_mem hi1) hi2
    have hmemJ : y' v * (y v)⁻¹ ∈ J := J.mul_mem (hJD y' hy' v hv) (J.inv_mem (hJD y hy v hv))
    have hboth : y' v * (y v)⁻¹ ∈ J ⊓ I := ⟨hmemJ, hmem⟩
    rw [hIJ, Subgroup.mem_bot, mul_inv_eq_one] at hboth
    exact hboth
  have h2 : y'⁻¹ * y = 1 := hJf _ (D.mul_mem (D.inv_mem hy') hy) fun v hv => by
    have := key v hv
    simp [← this]
  have h3 : y' = y := inv_mul_eq_one.mp h2
  rw [hy'e] at h3
  exact mul_inv_eq_iff_eq_mul.mp h3

theorem false_of_sup_eq_top (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} {I : Subgroup V}
    (hI : XMod.IsIrr ↥D I) (hIA : ∀ a ∈ A, ∀ v ∈ I, a v ∈ I)
    (hnc : ∃ a ∈ A, ∃ y ∈ D, a * y ≠ y * a) (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D)
    (hsup : I ⊔ fixV A = ⊤) : False := by
  have hcomm : ∀ a ∈ A, ∀ u : V, a u * u⁻¹ ∈ I := by
    intro a ha u
    have hu : u ∈ I ⊔ fixV A := by rw [hsup]; trivial
    obtain ⟨i, hi, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    have : a (i * c) * (i * c)⁻¹ = a i * i⁻¹ := by
      rw [map_mul, hc a ha]
      group
    rw [this]
    exact I.mul_mem (hIA a ha i hi) (I.inv_mem hi)
  obtain ⟨hIne, hID, hImin⟩ := isIrr_iff.mp hI
  obtain ⟨t, ht⟩ : ∃ t : ↥X, ¬ (t • I ≤ I) := by
    by_contra hcon
    push Not at hcon
    have h1 : (⨆ t : ↥X, t • I) ≤ I := iSup_le hcon
    rw [iSup_smul_eq_top hZ hI] at h1
    have hItop : I = ⊤ := top_le_iff.mp h1
    refine not_irr_top hZ fun U hU => ?_
    have := hImin U (hItop ▸ le_top) hU
    rwa [hItop] at this
  have hN := normalizes_of_comm hZ.comm
  obtain ⟨hJne, hJD, hJmin⟩ := isIrr_iff.mp (isIrr_smul hN t hI)
  have hIJ : (t • I) ⊓ I = ⊥ := by
    rcases hJmin ((t • I) ⊓ I) inf_le_left
      (fun y hy v hv => ⟨hJD y hy v hv.1, hID y hy v hv.2⟩) with h | h
    · exact h
    · exact absurd (inf_eq_left.mp h) ht
  obtain ⟨a, ha, y, hy, hne⟩ := hnc
  exact hne (mul_comm_of_inf_eq_bot hID hJD (faithful hZ hJne hJD) hIJ (hcomm a ha) hy
    (hAD a ha y hy))

end Z3A1

end CFSG.Quasithin
