module

public import CFSG.RankThree.GF2n.Stroth80.Sec53cFix
public import CFSG.RankThree.GF2n.Stroth80.Sec53FromFix
public import CFSG.RankThree.GF2n.Stroth80.Sec53aVoneNe

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec53c_card_vone_eq (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r s : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hsR : s ∈ Rt M (LB M Q B) t) (hplanes : HypPlane Q Z B (conjSubgroup s B) t) :
    Nat.card ↥(Sec8V1 M Q Z B t s) = Nat.card ↥(Sec8V1 M Q Z B t r) := by
  classical
  have hs8 : Sec8Hyp hc n t := by
    obtain ⟨K, fK, finK, hK, m, hm, hrep⟩ := hsp
    exact ⟨hs, m, hm, K, fK, finK, hK, hrep⟩
  obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hsp
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  obtain ⟨u, hu0, hBiff, -, hrIff⟩ := hc.sp_points_core h34 hRoot hs hK hm φ hφ hker ψ hψ
  let rR : ↥(Rt M (LB M Q B) t) := ⟨r, hr⟩
  let sR : ↥(Rt M (LB M Q B) t) := ⟨s, hsR⟩
  have hru : spForm m K u ((φ rR : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 :=
    (hrIff rR).1.mp hplane
  have hsu : spForm m K u
      ((φ (1⁻¹ * sR) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 := by
    rw [inv_one, one_mul]
    exact (hrIff sR).1.mp hplanes
  obtain ⟨h, c, -, hv₁, hv₂⟩ := sec8_witt_pair (h₁ := 1) (h₂ := sR) (r := rR) φ hφ hru hsu
  have hp₁ : conjSubgroup (h : G) B ⊔ Z =
      conjSubgroup ((1 : ↥(Rt M (LB M Q B) t)) : G) B ⊔ Z :=
    sec8_point_of_vec hs8 hu0 ψ hBiff hψ (c := 1) (by rw [one_smul]; exact hv₁)
  have hp₂ : conjSubgroup ((h * rR : ↥(Rt M (LB M Q B) t)) : G) B ⊔ Z =
      conjSubgroup (sR : G) B ⊔ Z :=
    sec8_point_of_vec hs8 hu0 ψ hBiff hψ hv₂
  have hhM : (h : G) ∈ M := hc.Rt_le_M t h.2
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hVh : conjSubgroup (h : G) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem h.2)
  have h1B : conjSubgroup ((1 : ↥(Rt M (LB M Q B) t)) : G) B = B := conjSubgroup_one B
  have e1 : Q ⊓ QB (conjSubgroup (h : G) B) = Q ⊓ QB B :=
    sec8_inf_QB_eq_of_sup_eq (hc.conj_of_mem hhM) hc (by rw [hp₁, h1B])
  have e2 : Q ⊓ QB (conjSubgroup ((h : G) * r) B) = Q ⊓ QB (conjSubgroup s B) :=
    sec8_inf_QB_eq_of_sup_eq (hc.conj_of_mem (M.mul_mem hhM hrM)) (hc.conj_of_mem hsM) hp₂
  have hconj : conjSubgroup (h : G) (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t s := by
    show conjSubgroup (h : G) (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) =
      Vone Q B (conjSubgroup s B) (Vt M (LB M Q B) B Z t)
    rw [sec8_conj_Vone (hc.conj_Q_eq hhM) hVh, ← conjSubgroup_mul]
    simp only [Vone, e1, e2]
  rw [← hconj, card_conjSubgroup]

theorem sec53c_prod_of_vone_ne (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (hsp : SpNat hc t) (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hne : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t) :
    ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  obtain ⟨K₀, iF₀, iFin₀, hK₀, m, hm, hrep₀⟩ := hsp
  have hV : SpMNat hc t m := ⟨K₀, iF₀, iFin₀, hK₀, hrep₀⟩
  obtain ⟨K, iF, iFin, iCh, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := iF
  letI := iFin
  letI := iCh
  let T : Submodule K M₀.E := imgSub M₀ (Vt M (LB M Q B) B Z t) (hc.smul_mem_img_Vt hD t)
  have hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun e => mem_imgSub
  have hBC := (Ctx.hBC_iff_vone_ne h34 hRoot h51 hc hs hm hV hr hplane hD T hTmem).mpr hne
  have hspan := Ctx.le_sup_imgQInfQB_sp_of_hplane h34 hRoot hc hs hm hV hr hplane hD T hTmem
  have hcard := Ctx.card_vone_sp_of_hBC h34 hRoot hc hs hm hV hr hD T hTmem hBC hspan
  have hcommB : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcommC : ∀ x ∈ Q ⊓ QB (conjSubgroup r B), ∀ y ∈ Q ⊓ QB (conjSubgroup r B),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hcC).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAD : QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) := fun a ha =>
    mem_Wt_of_le_sup ha.2
      (fun s hs' => hcommB s hs' a ⟨(inf_le_left : Wt Q _ ≤ Q) ha.2, ha.1⟩) inf_le_left
  have hCD : QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ≤
      Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) := fun a ha =>
    mem_Wt_of_le_sup ha.2
      (fun s hs' => hcommC s hs' a ⟨(inf_le_left : Wt Q _ ≤ Q) ha.2, ha.1⟩) inf_le_right
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hQ : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have hDc : Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
      Nat.card Z ^ (2 * m) = Nat.card Z ^ (2 * n) := by
    have h := hc.card_Wt_mul_card_vone hs hcC hnoC
    rw [hcard, SpMNat.card_V hV, hQ] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hq 2) ?_
    calc Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
          Nat.card Z ^ (2 * m) * Nat.card Z ^ 2
        = Nat.card ↥(Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))) *
          (Nat.card Z ^ (2 * m + 1) * Nat.card Z) := by ring
      _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z := h
      _ = Nat.card Z ^ (2 * n) * Nat.card Z ^ 2 := by ring
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := sec53b_prod_of_model_count h34 hRoot hc hs hm hV hr hD hBC
    hAD hCD hDc x hx
  exact ⟨a, ⟨ha.1, hAD ha⟩, b, ⟨hb.1, hCD hb⟩, hab⟩

theorem sec53c_prod_pair (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    (hsp : SpNat hc t) (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b := by
  by_cases hE : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t
  · obtain ⟨K₀, iF₀, iFin₀, hK₀, m, hm, hrep₀⟩ := hsp
    have hW : Sec8W1 M Q Z B t r = Wt Q (Vt M (LB M Q B) B Z t) := by
      show Wt Q (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) = _
      rw [hE]
    rw [hW]
    exact sec53b_prod_of_vone_eq h34 hRoot hc hs hm ⟨K₀, iF₀, iFin₀, hK₀, hrep₀⟩ hr hplane hE
  · exact sec53c_prod_of_vone_ne h34 hRoot h51 hc hs hsp hr hplane hE

theorem sec53c_hfixB_of_inputs' (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  exact sec53c_fixB h34 hRoot hc hs hsp hr hplane
    (fun s hsR hps => le_of_eq (sec53c_card_vone_eq h34 hRoot hc hs hsp hr hplane hsR hps))
    (sec53c_prod_pair h34 hRoot h51 hc hs hsp hr hplane)
    (stroth53VW_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)
    (fun s hsR hps => stroth53Inf_holds G M Q Z B hc n t hs hsp s hsR hps)

theorem sec53c_hfixC_of_inputs' (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  exact sec53c_fixC h34 hRoot hc hs hsp hr hplane
    (fun s hsR hps => le_of_eq (sec53c_card_vone_eq h34 hRoot hc hs hsp hr hplane hsR hps))
    (sec53c_prod_pair h34 hRoot h51 hc hs hsp hr hplane)
    (stroth53VW_holds h34 hRoot h51 G M Q Z B hc n t hs hsp r hr hplane)
    (fun s hsR hps => stroth53Inf_holds G M Q Z B hc n t hs hsp s hsR hps)

theorem stroth53FixB_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53FixBStatement :=
  sec53c_hfixB_of_inputs' h34 hRoot h51

theorem stroth53FixC_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) : Stroth53FixCStatement :=
  sec53c_hfixC_of_inputs' h34 hRoot h51

end CFSG.RankThree.GF2n.Stroth80
