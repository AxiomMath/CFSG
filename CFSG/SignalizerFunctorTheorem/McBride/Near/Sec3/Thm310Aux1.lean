module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux6
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm34Quot

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm310

section Rank

variable {G : Type*} [Group G] [Finite G]

theorem exists_card_sq_le {p : ℕ} (hp : p.Prime) {A C : Subgroup G} (hA : IsElemAbelian p A)
    (hrank : p ^ 3 ≤ Nat.card ↥A) (hCA : C ≤ A) (hcyc : CyclicMod A C) :
    ∃ E : Subgroup G, E ≤ C ∧ Nat.card ↥E = p ^ 2 := by
  have := Fact.mk hp
  have h1 : Nat.card ↥A ≤ p * Nat.card ↥C := Thm36.card_le_mul_of_cyclicMod hp hA hCA hcyc
  have hAp : IsPGroup p ↥A := fun g => ⟨1, by
    have := hA.2 g g.2
    simpa using Subtype.ext this⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hCd : Nat.card ↥C ∣ Nat.card ↥A := Subgroup.card_dvd_of_le hCA
  rw [hm] at hCd
  obtain ⟨j, -, hjC⟩ := (Nat.dvd_prime_pow hp).mp hCd
  have hp2 : p ^ 2 ≤ Nat.card ↥C := by
    have h3 : p * p ^ 2 ≤ p * Nat.card ↥C := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card ↥A := hrank
        _ ≤ p * Nat.card ↥C := h1
    exact Nat.le_of_mul_le_mul_left h3 hp.pos
  rw [hjC] at hp2
  have hj2 : 2 ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).mp hp2
  obtain ⟨K, hK, -, hKC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G) (H := ⊥)
    (L := C) (n := 2) hp (by simp) (by rw [hjC]; exact pow_dvd_pow p hj2) bot_le
  exact ⟨K, hKC, hK⟩

end Rank

section Pairs

variable {Γ : Type*} [Group Γ]

theorem mem_iPairsY_of_le {A X₀ X₁ Y : Subgroup Γ} {P : Subgroup Γ × Subgroup Γ}
    (hcen : cenIn X₁ (A : Set Γ) = cenIn X₀ (A : Set Γ)) (hP : P ∈ iPairsY A X₀ Y)
    (h1 : P.1 ≤ X₁) (h2 : P.2 ≤ X₁) : P ∈ iPairsY A X₁ Y := by
  obtain ⟨⟨⟨_, hadm1⟩, ⟨_, hadm2⟩, hch, hsec⟩, hinf⟩ := hP
  rw [← hcen] at hadm1 hadm2 hch hsec hinf
  exact ⟨⟨⟨h1, hadm1⟩, ⟨h2, hadm2⟩, hch, hsec⟩, hinf⟩

variable [Finite Γ]

theorem hypA6_of_iPairsY
    {p : ℕ} {A X D Y : Subgroup Γ} (h : NearAsolvAction p A X)
    (hD : cenIn X (A : Set Γ) = D) [(Y.subgroupOf D).Normal]
    (hpair : (iPairsY A X Y).Nonempty) : HypA6 X A D (fittingPre D Y) Y := by
  subst hD
  intro N L R hN hL hR hNd hLd hRd hLR hch hc hRD hDN hdp
  have hRn : IsNormalIn R (R ⊔ cenIn X (A : Set Γ) ⊔ A) :=
    ⟨le_sup_left.trans le_sup_left, sup_le (sup_le Subgroup.le_normalizer
      (le_sup_left.trans hRd)) (le_sup_right.trans hRd)⟩
  obtain ⟨B, hBR, hBn, hBD, hRB⟩ := iThm35 h hpair hN hL hR ⟨hch.1, hch.2.1, hRn⟩
    ⟨hch, hLR⟩ hc ⟨hRD, hDN, hdp⟩
  exact ⟨B, hBR, hBn.2, hBD, hRB⟩

end Pairs

section Quotient

variable {Γ : Type u} [Group Γ]

theorem comm_mem_of_qmap_comm {R : Subgroup Γ} {x y : Γ} (hx : x ∈ AChief.nrm R)
    (hy : y ∈ AChief.nrm R)
    (h : AChief.qmap R ⟨x, hx⟩ * AChief.qmap R ⟨y, hy⟩ =
      AChief.qmap R ⟨y, hy⟩ * AChief.qmap R ⟨x, hx⟩) : ⁅x, y⁆ ∈ R := by
  have h1 : AChief.qmap R (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using h2

theorem qmap_comm_of_comm_mem {R : Subgroup Γ} {x y : Γ} (hx : x ∈ AChief.nrm R)
    (hy : y ∈ AChief.nrm R) (h : ⁅x, y⁆ ∈ R) :
    AChief.qmap R ⟨x, hx⟩ * AChief.qmap R ⟨y, hy⟩ =
      AChief.qmap R ⟨y, hy⟩ * AChief.qmap R ⟨x, hx⟩ := by
  have h1 : (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : ↥(AChief.nrm R)) ∈
      R.subgroupOf (AChief.nrm R) := by
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using h
  have h2 : AChief.qmap R (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)

theorem qimg_le_centralizer_of_comm {R E F : Subgroup Γ}
    (h : ∀ e ∈ E, ∀ f ∈ F, ⁅e, f⁆ ∈ R) :
    AChief.qimg R E ≤
      Subgroup.centralizer ((AChief.qimg R F : Subgroup (AChief.QG R)) : Set (AChief.QG R)) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff R E z).mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, hx, rfl⟩ := (AChief.mem_qimg_iff R F w).mp hw
  exact (qmap_comm_of_comm_mem y.2 x.2 (h _ hy _ hx)).symm

variable [Finite Γ]

omit [Finite Γ] in
theorem comm_of_chief {H L N : Subgroup Γ} (hH : Group.IsSolvable ↥H)
    (hch : IsChiefFactorOf H L N) : ∀ x ∈ L, ∀ y ∈ L, ⁅x, y⁆ ∈ N := by
  have hHn : H ≤ AChief.nrm N := hch.1.2
  have hN : N ≤ H := hch.1.1
  have hq : IsChiefFactorOf (AChief.qimg N H) (AChief.qimg N L) ⊥ :=
    Thm34.isChiefFactorOf_qimg_inf hHn (by rwa [inf_eq_right.mpr hN])
  have hHs : Group.IsSolvable ↥(AChief.qimg N H) :=
    Group.isSolvable_of_surjective (SolQuot.qres_surjective hHn)
  have hcomm : ∀ x ∈ AChief.qimg N L, ∀ y ∈ AChief.qimg N L, x * y = y * x := by
    by_contra hnc
    push Not at hnc
    exact Thm32.not_isSolvable_of_chief_bot hq hnc (Thm211.isSolvable_of_le hq.2.1.1 hHs)
  intro x hx y hy
  have hLH : L ≤ H := hch.2.1.1
  refine comm_mem_of_qmap_comm (hHn (hLH hx)) (hHn (hLH hy)) (hcomm _ ?_ _ ?_)
  · exact (AChief.mem_qimg_iff N L _).mpr ⟨⟨x, hHn (hLH hx)⟩, hx, rfl⟩
  · exact (AChief.mem_qimg_iff N L _).mpr ⟨⟨y, hHn (hLH hy)⟩, hy, rfl⟩

theorem secCenIn_fittingPre {D D₂ : Subgroup Γ} [(D₂.subgroupOf D).Normal]
    (hD : Group.IsSolvable ↥D) (hch : IsChiefFactorOf D (fittingPre D D₂) D₂) :
    secCenIn D (fittingPre D D₂) D₂ = fittingPre D D₂ := by
  have hD₂D : D₂ ≤ D := hch.1.1
  have hDn : D ≤ AChief.nrm D₂ := hch.1.2
  have hD₁D : fittingPre D D₂ ≤ D := hch.2.1.1
  have hDn₁ : D ≤ Subgroup.normalizer (fittingPre D D₂ : Set Γ) := hch.2.1.2
  have hinf : D ⊓ D₂ = D₂ := inf_eq_right.mpr hD₂D
  have e1 : fittingPre D D₂ =
      D ⊓ SolQuot.qpre D₂ (CFSG.fittingSubgroupOf (AChief.qimg D₂ D)) :=
    Thm34.fittingPre_eq_inf_qpre hDn hinf
  have hFeq : AChief.qimg D₂ (fittingPre D D₂) =
      CFSG.fittingSubgroupOf (AChief.qimg D₂ D) := by
    rw [e1, SolQuot.qimg_inf_of_le (SolQuot.qpre_le_nrm _) (SolQuot.le_qpre _),
      SolQuot.qimg_qpre]
    exact inf_eq_right.mpr (Subgroup.map_subtype_le _)
  have hDs : Group.IsSolvable ↥(AChief.qimg D₂ D) :=
    Group.isSolvable_of_surjective (SolQuot.qres_surjective hDn)
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨hxD, hxs⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨-, -, hxc⟩ := mem_sectionCentralizer_iff.mp hxs
    rw [e1]
    refine Subgroup.mem_inf.mpr ⟨hxD, SolQuot.mem_qpre_iff.mpr ⟨hDn hxD, ?_⟩⟩
    have hxbar : AChief.qmap D₂ ⟨x, hDn hxD⟩ ∈ AChief.qimg D₂ D :=
      (AChief.mem_qimg_iff D₂ D _).mpr ⟨⟨x, hDn hxD⟩, hxD, rfl⟩
    have hcent : (⟨AChief.qmap D₂ ⟨x, hDn hxD⟩, hxbar⟩ : ↥(AChief.qimg D₂ D)) ∈
        Subgroup.centralizer (CFSG.fittingSubgroup ↥(AChief.qimg D₂ D) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : (z : AChief.QG D₂) ∈ AChief.qimg D₂ (fittingPre D D₂) := by
        rw [hFeq]
        exact ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyz⟩ := (AChief.mem_qimg_iff D₂ _ _).mp hz'
      have hcomm := qmap_comm_of_comm_mem (hDn hxD) y.2 (hxc y hy)
      apply Subtype.ext
      change (z : AChief.QG D₂) * AChief.qmap D₂ ⟨x, hDn hxD⟩ =
        AChief.qmap D₂ ⟨x, hDn hxD⟩ * z
      rw [← hyz]
      exact hcomm.symm
    have hmem := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hDs hcent
    exact ⟨_, hmem, rfl⟩
  · have hxD : x ∈ D := hD₁D hx
    refine Subgroup.mem_inf.mpr ⟨hxD, mem_sectionCentralizer_iff.mpr ⟨hDn hxD, hDn₁ hxD, ?_⟩⟩
    exact fun y hy => comm_of_chief hD hch x hx y hy

end Quotient

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm310
