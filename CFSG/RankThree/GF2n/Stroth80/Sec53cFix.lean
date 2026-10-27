module

public import CFSG.RankThree.GF2n.Stroth80.Sec52bProof
public import CFSG.RankThree.GF2n.Stroth80.Sec8CanonPts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem conjSubgroup_Wt {g : G} (hQ : conjSubgroup g Q = Q) (X : Subgroup G) :
    conjSubgroup g (Wt Q X) = Wt Q (conjSubgroup g X) := by
  ext x
  rw [mem_conjSubgroup]
  simp only [Wt, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hxQ, hxC⟩
    refine ⟨?_, fun v hv => ?_⟩
    · have hx : x ∈ conjSubgroup g Q := mem_conjSubgroup.mpr hxQ
      rwa [hQ] at hx
    · have h := hxC _ (mem_conjSubgroup.mp hv)
      calc v * x = g * ((g⁻¹ * v * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
        _ = x * v := by group
  · rintro ⟨hxQ, hxC⟩
    refine ⟨?_, fun v hv => ?_⟩
    · have hx : x ∈ conjSubgroup g Q := by rw [hQ]; exact hxQ
      exact mem_conjSubgroup.mp hx
    · have hv' : g * v * g⁻¹ ∈ conjSubgroup g X := by
        rw [mem_conjSubgroup, show g⁻¹ * (g * v * g⁻¹) * g = v by group]
        exact hv
      have h := hxC _ hv'
      calc v * (g⁻¹ * x * g) = g⁻¹ * ((g * v * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * v * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * x * g * v := by group

theorem sec53c_c2_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    ∃ y ∈ LB M Q B, ∃ r' ∈ Rt M (LB M Q B) t, ∃ z ∈ LB M Q (conjSubgroup r B),
      HypPlane Q Z B (conjSubgroup r' B) t ∧
      conjSubgroup r (conjSubgroup r' B) = conjSubgroup y (conjSubgroup r B) ∧
      HypPlane Q Z B (conjSubgroup z B) t := by
  classical
  obtain ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩ := hsp
  obtain ⟨u, -, hL, hrIff⟩ := hc.sp_points h34 hRoot hs hK hm φ hφ hker hact
  let R : Subgroup G := Rt M (LB M Q B) t
  let rR : ↥R := ⟨r, hr⟩
  let g : GL (Fin m ⊕ Fin m) K := φ rR
  have hg : g ∈ StatedSp m K := hφ ▸ MonoidHom.mem_range.mpr ⟨rR, rfl⟩
  let c : Fin m ⊕ Fin m → K := (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u
  have huc : spForm m K u c ≠ 0 := (hrIff rR).1.mp hplane
  have hcu : spForm m K c u ≠ 0 := by
    intro h0
    apply huc
    have h1 := (spForm_isAlt (m := m) (K := K)).neg_eq u c
    rw [h0, neg_eq_zero] at h1
    exact h1
  obtain ⟨A, hA, hAx⟩ := exists_transvection_LspGL (m := m) (K := K) u
  have hAmem : A ∈ ((LB M Q B).subgroupOf R).map φ := by
    rw [hL]
    exact hA
  obtain ⟨yR, hyR, hyφ⟩ := Subgroup.mem_map.mp hAmem
  have hyL : (yR : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hyR
  let r' : G := r⁻¹ * (yR : G) * r
  have hr'R : r' ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hr) yR.2) hr
  have hr'φ : φ ⟨r', hr'R⟩ = g⁻¹ * A * g := by
    have hdecomp : (⟨r', hr'R⟩ : ↥R) = rR⁻¹ * yR * rR := Subtype.ext rfl
    rw [hdecomp, map_mul, map_mul, map_inv, hyφ]
  have hpol' : spForm m K u
      ((φ ⟨r', hr'R⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 := by
    rw [hr'φ, spForm_conj_mulVec hg u, hAx, map_add, map_smul, spForm_self, zero_add,
      smul_eq_mul]
    exact mul_ne_zero hcu hcu
  obtain ⟨A', hA', hA'x⟩ := exists_transvection_LspGL (m := m) (K := K) c
  have hLC : ((LB M Q (conjSubgroup r B)).subgroupOf R).map φ = LspGL m K c := by
    rw [hc.LB_conj (hc.Rt_le_M t hr)]
    exact (hrIff rR).2
  have hA'mem : A' ∈ ((LB M Q (conjSubgroup r B)).subgroupOf R).map φ := by
    rw [hLC]
    exact hA'
  obtain ⟨zR, hzR, hzφ⟩ := Subgroup.mem_map.mp hA'mem
  have hzL : (zR : G) ∈ LB M Q (conjSubgroup r B) := Subgroup.mem_subgroupOf.mp hzR
  have hpolz : spForm m K u ((φ zR : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 := by
    rw [hzφ, hA'x, map_add, map_smul, spForm_self, zero_add, smul_eq_mul]
    exact mul_ne_zero huc huc
  refine ⟨(yR : G), hyL, r', hr'R, (zR : G), hzL, (hrIff ⟨r', hr'R⟩).1.mpr hpol', ?_,
    (hrIff zR).1.mpr hpolz⟩
  rw [← conjSubgroup_mul, ← conjSubgroup_mul]
  congr 1
  show r * (r⁻¹ * (yR : G) * r) = (yR : G) * r
  group

theorem sec53c_fix_of_partner (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t)
    {L X X' : Subgroup G} {y g s : G} (hyL : y ∈ L)
    (hyV₁ : y ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G))
    (hyM : y ∈ M) (hyR : y ∈ Rt M (LB M Q B) t) (hgM : g ∈ M) (hgR : g ∈ Rt M (LB M Q B) t)
    (hgB : conjSubgroup g B = X')
    (hgs : conjSubgroup g (conjSubgroup s B) = conjSubgroup y X')
    (hV₁X' : Sec8V1 M Q Z B t r ≤ (Q ⊓ QB X') ⊔ Vt M (LB M Q B) B Z t)
    (hVW : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hcommA : ⁅L, (QB X ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r⁆ ≤ Sec8V1 M Q Z B t r)
    (hfac : ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ (QB X ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r,
      ∃ b ∈ (QB X' ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r, x = a * b)
    (hcardle : Nat.card ↥(Sec8V1 M Q Z B t s) ≤ Nat.card ↥(Sec8V1 M Q Z B t r))
    (hinf' : ((QB B ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s) ⊓
        ((QB (conjSubgroup s B) ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s) ≤
        Sec8V1 M Q Z B t s) :
    ∀ x ∈ Sec8W1 M Q Z B t r, (∀ l ∈ L, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
      x ∈ (QB X ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := by
  have hyQ : conjSubgroup y Q = Q := hc.conj_Q_eq hyM
  have hyV : conjSubgroup y (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hyR)
  have hgQ : conjSubgroup g Q = Q := hc.conj_Q_eq hgM
  have hgV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hgR)
  have hyV₁' : conjSubgroup y (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t r :=
    conjSubgroup_eq_self_iff.mpr hyV₁
  have hyW₁ : conjSubgroup y (Sec8W1 M Q Z B t r) = Sec8W1 M Q Z B t r := by
    show conjSubgroup y (Wt Q (Sec8V1 M Q Z B t r)) = Wt Q (Sec8V1 M Q Z B t r)
    rw [conjSubgroup_Wt hyQ, hyV₁']
  have hconjV : conjSubgroup g (Sec8V1 M Q Z B t s) =
      Vone Q X' (conjSubgroup y X') (Vt M (LB M Q B) B Z t) := by
    show conjSubgroup g (Vone Q B (conjSubgroup s B) (Vt M (LB M Q B) B Z t)) = _
    rw [sec8_conj_Vone hgQ hgV, hgB, hgs]
  have hle : Sec8V1 M Q Z B t r ≤ conjSubgroup g (Sec8V1 M Q Z B t s) := by
    rw [hconjV]
    refine le_inf hV₁X' ?_
    have h1 : conjSubgroup y (Sec8V1 M Q Z B t r) ≤
        conjSubgroup y ((Q ⊓ QB X') ⊔ Vt M (LB M Q B) B Z t) := fun x hx =>
      mem_conjSubgroup.mpr (hV₁X' (mem_conjSubgroup.mp hx))
    rwa [hyV₁', conjSubgroup_sup', conjSubgroup_inf, ← QB_conj, hyQ, hyV] at h1
  have hEq : Sec8V1 M Q Z B t r = conjSubgroup g (Sec8V1 M Q Z B t s) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup]; exact hcardle)
  have hWEq : conjSubgroup g (Sec8W1 M Q Z B t s) = Sec8W1 M Q Z B t r := by
    show conjSubgroup g (Wt Q (Sec8V1 M Q Z B t s)) = Wt Q (Sec8V1 M Q Z B t r)
    rw [conjSubgroup_Wt hgQ, ← hEq]
  have hD : ((QB X' ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊓
      ((QB (conjSubgroup y X') ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ≤
      Sec8V1 M Q Z B t r := by
    have h1 : conjSubgroup g (((QB B ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s) ⊓
        ((QB (conjSubgroup s B) ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s)) ≤
        conjSubgroup g (Sec8V1 M Q Z B t s) := fun x hx =>
      mem_conjSubgroup.mpr (hinf' (mem_conjSubgroup.mp hx))
    rwa [conjSubgroup_inf, conjSubgroup_sup', conjSubgroup_sup', conjSubgroup_inf,
      conjSubgroup_inf, ← QB_conj, ← QB_conj, hgB, hgs, hWEq, ← hEq] at h1
  have hmap : conjSubgroup y ((QB X' ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) =
      (QB (conjSubgroup y X') ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := by
    rw [conjSubgroup_sup', conjSubgroup_inf, ← QB_conj, hyW₁, hyV₁']
  have hQV : Sec8W1 M Q Z B t r ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    (inf_le_left : Sec8W1 M Q Z B t r ≤ Q).trans (hc.Q_le_normalizer_vone t)
  exact sec52b_fixed_of_map hQV (sup_le inf_le_right hVW) (sup_le inf_le_right hVW) hfac
    (le_antisymm hD (le_inf le_sup_right le_sup_right)) hmap hcommA hyL le_sup_right
    le_sup_right

theorem sec53c_fixB (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hcardle : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      Nat.card ↥(Sec8V1 M Q Z B t s) ≤ Nat.card ↥(Sec8V1 M Q Z B t r))
    (hprod : ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b)
    (hVW : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hinf : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      ((QB B ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s) ⊓
        ((QB (conjSubgroup s B) ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s) ≤
        Sec8V1 M Q Z B t s) :
    ∀ x ∈ Sec8W1 M Q Z B t r, (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
      x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := by
  obtain ⟨y, hyL, r', hr'R, _z, _hzL, hplane', hEq, _hplanez⟩ :=
    sec53c_c2_sp h34 hRoot hc hs hsp hr hplane
  have hLN : LB M Q B ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sup_le (hc.Q_le_normalizer_vone t) (hc.QB_inf_M_le_normalizer_vone hs)
  refine sec53c_fix_of_partner hc hs (X' := conjSubgroup r B) hyL (hLN hyL) (hc.LB_le_M hyL)
    (le_Rt (M := M) (LB M Q B) hs.mem hyL) (hc.Rt_le_M t hr) hr rfl hEq inf_le_right hVW
    (hc.comm_LB_A1_le_vone hs) ?_ (hcardle r' hr'R hplane') (hinf r' hr'R hplane')
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
  exact ⟨a, Subgroup.mem_sup_left ha, b, Subgroup.mem_sup_left hb, rfl⟩

theorem sec53c_fixC (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hsp : SpNat hc t)
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hcardle : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      Nat.card ↥(Sec8V1 M Q Z B t s) ≤ Nat.card ↥(Sec8V1 M Q Z B t r))
    (hprod : ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b)
    (hVW : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r)
    (hinf : ∀ s ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup s B) t →
      ((QB B ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s) ⊓
        ((QB (conjSubgroup s B) ⊓ Sec8W1 M Q Z B t s) ⊔ Sec8V1 M Q Z B t s) ≤
        Sec8V1 M Q Z B t s) :
    ∀ x ∈ Sec8W1 M Q Z B t r,
      (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
      x ∈ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r := by
  obtain ⟨_y, _hyL, _r', _hr'R, z, hzL, _hplane', _hEq, hplanez⟩ :=
    sec53c_c2_sp h34 hRoot hc hs hsp hr hplane
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hzR : z ∈ Rt M (LB M Q B) t := hc.LB_conj_le_Rt_of_mem hs.mem hr hzL
  have hLN : LB M Q (conjSubgroup r B) ≤
      Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sup_le (hc.Q_le_normalizer_vone t) (hc.QBC_inf_M_le_normalizer_vone hs hr)
  have hWQ : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  refine sec53c_fix_of_partner hc hs (X' := B) (g := 1) (s := z) hzL (hLN hzL)
    ((hc.conj_of_mem hrM).LB_le_M hzL) hzR M.one_mem (Rt M (LB M Q B) t).one_mem
    (conjSubgroup_one B) (conjSubgroup_one _) inf_le_left hVW (hc.comm_LBC_A2_le_vone hs hr) ?_
    (hcardle z hzR hplanez) (hinf z hzR hplanez)
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
  have hz : ⁅a⁻¹, b⁻¹⁆ ∈ Sec8V1 M Q Z B t r :=
    Z_le_vone (hc.hyp.toHyp79.comm_mem_V (Q.inv_mem (hWQ ha.2)) (Q.inv_mem (hWQ hb.2)))
  refine ⟨b, Subgroup.mem_sup_left hb, a * ⁅a⁻¹, b⁻¹⁆,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hz), ?_⟩
  rw [commutatorElement_def]
  group

end CFSG.RankThree.GF2n.Stroth80
