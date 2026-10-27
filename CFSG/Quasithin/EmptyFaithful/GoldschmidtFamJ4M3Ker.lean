module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3Str
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4PermFive

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad

noncomputable abbrev OrbM3 : Set (J ⧸ Hj) := MulAction.orbit ↥M3 (basePt : J ⧸ Hj)

noncomputable def basePtOrb : ↥OrbM3 := ⟨basePt, MulAction.mem_orbit_self _⟩

section Ker


theorem natCard_OrbM3 (hF : J4Facts) : Nat.card ↥OrbM3 = 5 := by
  have h : OrbM3 = X5 := orbit_M3_eq
  rw [Nat.card_coe_set_eq, h, ncard_X5 hF]

noncomputable def eOrb (hF : J4Facts) : ↥OrbM3 ≃ Fin 5 :=
  (Finite.equivFinOfCardEq (natCard_OrbM3 hF)).trans
    (Equiv.swap (Finite.equivFinOfCardEq (natCard_OrbM3 hF) basePtOrb) 4)

theorem eOrb_base (hF : J4Facts) : eOrb hF basePtOrb = 4 := by
  simp [eOrb]

noncomputable def rho3 (hF : J4Facts) : ↥M3 →* Equiv.Perm (Fin 5) :=
  (Equiv.permCongrHom (eOrb hF)).toMonoidHom.comp (MulAction.toPermHom ↥M3 ↥OrbM3)

theorem rho3_apply (hF : J4Facts) (m : ↥M3) (x : ↥OrbM3) :
    rho3 hF m (eOrb hF x) = eOrb hF (m • x) := by
  simp [rho3, Equiv.permCongrHom]

noncomputable abbrev Dm : Subgroup ↥M3 := (Subgroup.centralizer (V0 : Set J)).subgroupOf M3

theorem card_Dm (hF : J4Facts) : Nat.card ↥Dm = 3932160 := by
  have hfix : ∀ g : J, g • (basePt : J ⧸ Hj) = basePt ↔ g ∈ Hj := fun g => smul_basePt_eq_self_iff
  have h := card_eq_orbit_mul_inf (Subgroup.centralizer (V0 : Set J)) Hj basePt hfix
  have hS : MulAction.orbit ↥(Subgroup.centralizer (V0 : Set J)) (basePt : J ⧸ Hj) = D5 := by
    ext w
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  rw [hS, Nat.card_coe_set_eq, D5_eq_X5 hF, ncard_X5 hF] at h
  have hDH : Subgroup.centralizer (V0 : Set J) ⊓ Hj = CV := inf_comm _ _
  rw [hDH, card_CV hF] at h
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D_le_M3).toEquiv, h]

theorem smul_basePtOrb_of_mem_Eg (m : ↥M3) (hm : (m : J) ∈ Eg uJ 11) :
    m • basePtOrb = basePtOrb := by
  apply Subtype.ext
  show (m : J) • (basePt : J ⧸ Hj) = basePt
  exact smul_basePt_eq_self_iff.mpr (Eg_le_Hj hm)

theorem sixty_dvd_card_rho3 (hF : J4Facts) :
    60 ∣ Nat.card ((rho3 hF).comp Dm.subtype).range := by
  have hM := hF.mat
  have hEM : ∀ m : ↥M3, (m : J) ∈ Eg uJ 11 → m ∈ Dm := fun m hm =>
    Subgroup.mem_subgroupOf.mpr (Eg_le_D hM hm)
  let V : Subgroup (Equiv.Perm (Fin 5)) := ((Eg uJ 11).subgroupOf M3).map (rho3 hF)
  have hVG : V ≤ ((rho3 hF).comp Dm.subtype).range := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨⟨m, hEM m hm⟩, rfl⟩
  have hfix4 : ∀ m : ↥M3, (m : J) ∈ Eg uJ 11 → rho3 hF m 4 = 4 := by
    intro m hm
    have h1 := rho3_apply hF m basePtOrb
    rw [eOrb_base, smul_basePtOrb_of_mem_Eg m hm, eOrb_base] at h1
    exact h1
  have ha : ∀ v ∈ V, v 4 = 4 := by
    rintro _ ⟨m, hm, rfl⟩
    exact hfix4 m hm
  have hb : ∀ v ∈ V, v * v = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (Eg_sq (elem_uJ hM) hm)
    rw [this, map_one]
  have hc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
    rw [← map_mul, ← map_mul]
    have : m * m' = m' * m := Subtype.ext (Eg_comm (elem_uJ hM) hm hm')
    rw [this]
  have hd : ∀ i : Fin 5, i ≠ 4 → ∃ v ∈ V, v 0 = i := by
    intro i hi
    have hne : ∀ j : Fin 5, j ≠ 4 → ((eOrb hF).symm j : ↥OrbM3) ≠ basePtOrb := by
      intro j hj h
      apply hj
      have := congrArg (eOrb hF) h
      rw [Equiv.apply_symm_apply, eOrb_base] at this
      exact this
    have hmem : ∀ j : Fin 5, ((eOrb hF).symm j : J ⧸ Hj) ∈ X5 := fun j => by
      have h : OrbM3 = X5 := orbit_M3_eq
      rw [← h]
      exact ((eOrb hF).symm j).2
    have hnebase : ∀ j : Fin 5, j ≠ 4 → ((eOrb hF).symm j : J ⧸ Hj) ≠ basePt := by
      intro j hj h
      exact hne j hj (Subtype.ext h)
    obtain ⟨e, he, hex⟩ := E_transitive_X5 hF (hmem 0) (hnebase 0 (by decide)) (hmem i)
      (hnebase i hi)
    have hm : e ∈ M3 := D_le_M3 (Eg_le_D hM he)
    refine ⟨rho3 hF ⟨e, hm⟩, ⟨⟨e, hm⟩, he, rfl⟩, ?_⟩
    have h1 := rho3_apply hF ⟨e, hm⟩ ((eOrb hF).symm 0)
    rw [Equiv.apply_symm_apply] at h1
    rw [h1]
    have h2 : (⟨e, hm⟩ : ↥M3) • ((eOrb hF).symm 0 : ↥OrbM3) = (eOrb hF).symm i :=
      Subtype.ext hex
    rw [h2, Equiv.apply_symm_apply]
  have he : ∃ g ∈ ((rho3 hF).comp Dm.subtype).range, g 4 ≠ 4 := by
    have hcard : (X5 \ {basePt}).ncard = 4 := by
      rw [Set.ncard_sdiff_singleton_of_mem basePt_mem_X5, ncard_X5 hF]
    obtain ⟨w, hwX, hwb⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcard]; norm_num)
    have hwD : w ∈ D5 := by rw [D5_eq_X5 hF]; exact hwX
    obtain ⟨d, hd, hdw⟩ := hwD
    have hdm : (⟨d, D_le_M3 hd⟩ : ↥M3) ∈ Dm := Subgroup.mem_subgroupOf.mpr hd
    refine ⟨rho3 hF ⟨d, D_le_M3 hd⟩, ⟨⟨_, hdm⟩, rfl⟩, ?_⟩
    have h1 := rho3_apply hF ⟨d, D_le_M3 hd⟩ basePtOrb
    rw [eOrb_base] at h1
    rw [h1]
    intro h
    have h2 : (⟨d, D_le_M3 hd⟩ : ↥M3) • basePtOrb = basePtOrb := by
      apply (eOrb hF).injective
      rw [h, eOrb_base]
    apply hwb
    rw [← hdw]
    exact congrArg Subtype.val h2
  exact sixty_dvd_card_of_klein hVG ha hb hc hd he

theorem isPGroup_ker_rho3_Dm (hF : J4Facts) : IsPGroup 2 ((rho3 hF).comp Dm.subtype).ker := by
  have h60 := sixty_dvd_card_rho3 hF
  have hdvd : Nat.card ((rho3 hF).comp Dm.subtype).range ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card ((rho3 hF).comp Dm.subtype).range
    rwa [Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 from rfl] at this
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ((rho3 hF).comp Dm.subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ((rho3 hF).comp Dm.subtype)).toEquiv,
    card_Dm hF] at hcard
  generalize Nat.card ↥((rho3 hF).comp Dm.subtype).range = g at h60 hdvd hcard
  obtain ⟨t, rfl⟩ := h60
  have ht : t ∣ 2 := by
    have : 60 * t ∣ 60 * 2 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have ht' : t = 1 ∨ t = 2 := by
    have := Nat.le_of_dvd (by norm_num) ht
    interval_cases t <;> simp_all
  rcases ht' with rfl | rfl
  · refine IsPGroup.of_card (n := 16) ?_
    have h : Nat.card ↥((rho3 hF).comp Dm.subtype).ker = 65536 := by omega
    rw [h]
    norm_num
  · refine IsPGroup.of_card (n := 15) ?_
    have h : Nat.card ↥((rho3 hF).comp Dm.subtype).ker = 32768 := by omega
    rw [h]
    norm_num

end Ker

end CFSG.Quasithin.J4Fam
