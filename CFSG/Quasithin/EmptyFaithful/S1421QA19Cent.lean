module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Split
public import CFSG.Quasithin.EmptyFaithful.S1421QA19Tr
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentJ2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDA6
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocRu
public import CFSG.LargeExtraspecial.S63CD4AData
public import CFSG.LargeExtraspecial.S63CD4Iso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace QA19

theorem card_centralizer_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (t : X) :
    Nat.card (Subgroup.centralizer ({t} : Set X)) =
      Nat.card (Subgroup.centralizer ({φ t} : Set Y)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨φ x, Subgroup.mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2])⟩
      invFun := fun y => ⟨φ.symm y, Subgroup.mem_centralizer_singleton_iff.mpr (by
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_centralizer_singleton_iff.mp y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

theorem card_centralizer_conj {Y : Type*} [Group Y] (c a : Y) :
    Nat.card (Subgroup.centralizer ({c * a * c⁻¹} : Set Y)) =
      Nat.card (Subgroup.centralizer ({a} : Set Y)) := by
  have := card_centralizer_mulEquiv (MulAut.conj c) a
  rw [MulAut.conj_apply] at this
  exact this.symm

@[expose] def centA (N : ℕ) : ℕ :=
  if N = 604800 then 1920 else if N = 44352000 then 7680 else
  if N = 145926144000 then 245760 else if N = 211341312 then 258048 else N

@[expose] def smallOrder (N : ℕ) : Prop :=
  N = 604800 ∨ N = 44352000 ∨ N = 145926144000 ∨ N = 211341312 ∨ N = 86775571046077562880

@[expose] def CentData (X : Type) [Group X] [Finite X] (N : ℕ) : Prop :=
  Nat.card X = N ∧ ∀ t : X, orderOf t = 2 →
    (∃ P : Subgroup X, IsSylowTwoOf P ⊤ ∧ P ≤ Subgroup.centralizer ({t} : Set X)) →
      Nat.card (Subgroup.centralizer ({t} : Set X)) ∣ centA N

theorem two_pow_dvd_card_centralizer {X : Type} [Group X] [Finite X] {e m : ℕ}
    (hX : Nat.card X = 2 ^ e * m) {t : X}
    (h : ∃ P : Subgroup X, IsSylowTwoOf P ⊤ ∧ P ≤ Subgroup.centralizer ({t} : Set X)) :
    2 ^ e ∣ Nat.card (Subgroup.centralizer ({t} : Set X)) := by
  obtain ⟨P, hP, hle⟩ := h
  exact (two_pow_dvd_card_of_isSylowTwoOf hP hX).trans (Subgroup.card_dvd_of_le hle)

theorem centData_j2
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.J2) : CentData X 604800 := by
  have hN : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine ⟨hN, fun t ht h => ?_⟩
  have h2 := two_pow_dvd_card_centralizer (e := 7) (m := 4725) (by rw [hN]; norm_num) h
  have hc := card_centralizer_mulEquiv (e.trans ComponentClassification.J2Cover.nativeEquivP) t
  have ho : orderOf ((e.trans ComponentClassification.J2Cover.nativeEquivP) t) = 2 := by
    rw [MulEquiv.orderOf_eq, ht]
  have h3 := QuasithinUnique.Id2519.Tab.card_centralizer_involution_P ho
  rw [← hc] at h3
  have : Nat.card (Subgroup.centralizer ({t} : Set X)) = 1920 := by
    rcases h3 with h3 | h3
    · rw [h3] at h2
      norm_num at h2
    · exact h3
  rw [this]
  simp [centA]

theorem centData_hs
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.HS) : CentData X 44352000 := by
  have hN : Nat.card X = 44352000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  refine ⟨hN, fun t ht h => ?_⟩
  have h2 := two_pow_dvd_card_centralizer (e := 9) (m := 86625) (by rw [hN]; norm_num) h
  have h3 := CFSG.ComponentClassification.HSFLit.card_centralizer_of_HS e ht
  have : Nat.card (Subgroup.centralizer ({t} : Set X)) = 7680 := by
    rcases h3 with h3 | h3
    · exact h3
    · rw [h3] at h2
      norm_num at h2
  rw [this]
  simp [centA]

theorem centData_ru
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .Ru) :
    CentData X 145926144000 := by
  have hN : Nat.card X = 145926144000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru
  refine ⟨hN, fun t ht h => ?_⟩
  have h2 := two_pow_dvd_card_centralizer (e := 14) (m := 8906625) (by rw [hN]; norm_num) h
  have h3 := CFSG.Quasithin.HSRuLoc.Mod.ru_cent_card e ht
  have : Nat.card (Subgroup.centralizer ({t} : Set X)) = 245760 := by
    rcases h3 with h3 | h3
    · exact h3
    · rw [h3] at h2
      norm_num at h2
  rw [this]
  simp [centA]

theorem centData_j4
    {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.Carrier .J4) :
    CentData X 86775571046077562880 := by
  have hN : Nat.card X = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  refine ⟨hN, fun t _ _ => ?_⟩
  have : centA 86775571046077562880 = 86775571046077562880 := by simp [centA]
  rw [this, ← hN]
  exact Subgroup.card_subgroup_dvd_card _

open CFSG.LargeExtraspecial.S63 in
theorem card_centralizer_d4z_eq :
    Nat.card (Subgroup.centralizer ({d4z} : Set trialityGroup8)) = 258048 := by
  classical
  have : Finite trialityGroup8 :=
    Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)
  refine le_antisymm card_centralizer_d4z_le ?_
  let f : d4Q × d4L → trialityGroup8 := fun p => (p.1 : trialityGroup8) * p.2
  have hf : Function.Injective f := by
    rintro ⟨q₁, l₁⟩ ⟨q₂, l₂⟩ h
    have h' : (q₁ : trialityGroup8) * l₁ = q₂ * l₂ := h
    have h1 : (q₂ : trialityGroup8)⁻¹ * q₁ = (l₂ : trialityGroup8) * (l₁ : trialityGroup8)⁻¹ := by
      calc (q₂ : trialityGroup8)⁻¹ * q₁
          = (q₂ : trialityGroup8)⁻¹ * (q₁ * l₁) * (l₁ : trialityGroup8)⁻¹ := by group
        _ = (q₂ : trialityGroup8)⁻¹ * (q₂ * l₂) * (l₁ : trialityGroup8)⁻¹ := by rw [h']
        _ = (l₂ : trialityGroup8) * (l₁ : trialityGroup8)⁻¹ := by group
    have h2 := eq_one_of_mem_d4Q_d4L (d4Q.mul_mem (d4Q.inv_mem q₂.2) q₁.2)
      (h1 ▸ d4L.mul_mem l₂.2 (d4L.inv_mem l₁.2))
    have hq : q₁ = q₂ := Subtype.ext (inv_mul_eq_one.1 h2).symm
    have hl : l₁ = l₂ := by
      subst hq
      exact Subtype.ext (mul_left_cancel h')
    rw [hq, hl]
  have hsub : Set.range f ⊆
      (Subgroup.centralizer ({d4z} : Set trialityGroup8) : Set trialityGroup8) := by
    rintro _ ⟨⟨q, l⟩, rfl⟩
    exact Subgroup.mul_mem _ (d4Q_le_centralizer q.2) (d4L_le_centralizer l.2)
  have hcard : Nat.card (Set.range f) = 258048 := by
    rw [Nat.card_range_of_injective hf, Nat.card_prod, card_d4Q, card_d4L]
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, hcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h2
  exact h2

open CFSG.LargeExtraspecial.S63 in
theorem centData_d4
    {X : Type} [Group X] [Finite X] (h : Is3D4 2 1 X) : CentData X 211341312 := by
  have hN : Nat.card X = 211341312 := threeD4TwoOrder1522 X h
  refine ⟨hN, fun t ht hP => ?_⟩
  have h2 := two_pow_dvd_card_centralizer (e := 12) (m := 51597) (by rw [hN]; norm_num) hP
  have hL : LieModel X .trialityD4 0 2 1 := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  obtain ⟨φ⟩ := nonempty_equiv_trialityGroup8 X hL
  have hc := card_centralizer_mulEquiv φ t
  have ho : orderOf (φ t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  obtain ⟨c, hcl⟩ := exists_conj_of_orderOf_eq_two ho
  rw [hc]
  rw [hc] at h2
  rcases hcl with hcl | hcl
  · rw [hcl, card_centralizer_conj, card_centralizer_d4z_eq]
    simp [centA]
  · exfalso
    rw [hcl, card_centralizer_conj] at h2
    have hfin : Finite trialityGroup8 :=
      Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)
    have h3 : 2 ^ 12 ≤ Nat.card (Subgroup.centralizer ({d4t} : Set trialityGroup8)) :=
      Nat.le_of_dvd Nat.card_pos h2
    have h4 := card_centralizer_d4t_le
    omega


@[expose] def Core3CentData : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Core3IsSmall X →
    ∃ N, smallOrder N ∧ CentData X N ∧ (N = 86775571046077562880 → IsSporadic .J4 X)

theorem core3CentData_holds :
    Core3CentData := by
  intro X _ _ hX
  rcases hX with h | ⟨s, hs, ⟨e⟩⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), centData_d4 h,
      fun h' => absurd h' (by norm_num)⟩
  · rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, centData_j2 e, fun h' => absurd h' (by norm_num)⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr rfl))), centData_j4 e, fun _ => ⟨e⟩⟩
    · exact ⟨_, Or.inr (Or.inl rfl), centData_hs e, fun h' => absurd h' (by norm_num)⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), centData_ru e, fun h' => absurd h' (by norm_num)⟩

end QA19

end CFSG.Quasithin
