module

public import CFSG.Quasithin.H13.NQCatLieThompsonCore
public import CFSG.Quasithin.H13.NQCatLieThompsonSp4U
public import CFSG.Quasithin.H13.NQCatCartanSp4

public section

namespace CFSG.Quasithin.H13.NQCat.LieThompson.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (radical radical_le_unipotent tau_comm
  tau_sq card_radical)
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauAut tauAut_proj tauSp_tauSp tauSp_bijective frobAut
  projEquiv)
open CFSG.GH74.Uniqueness.Bender (autFixed)
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin.H13.NQCat.LieThompson (isElemAbelian_of_forall isElemAbelian_map
  mem_normalizer_of_map_eq ThompsonModel)

variable {F : Type} [Field F] [CharP F 2]

theorem tauSp_mem_unipotent {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) :
    tauSp u ∈ unipotent 2 F := by
  obtain ⟨x, c₀, c₁, c₂, h⟩ := exists_uMat hu
  exact mem_unipotent_of_uMat (spMat_tauSp h)

variable [Finite F]

theorem tauSp_iterate_two_mul (i : ℕ) (g : StatedSp 2 F) :
    tauSp^[2 * i] g = fieldSp 2 F (frobAut F ^ i) g := by
  induction i generalizing g with
  | zero => simp
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, Function.iterate_add_apply, ih, pow_succ,
      map_mul, MulAut.mul_apply]
    congr 1
    exact tauSp_tauSp g

theorem tauAut_pow_proj (m : ℕ) (g : StatedSp 2 F) :
    (tauAut ^ m) (proj 2 F g) = proj 2 F (tauSp^[m] g) := by
  induction m generalizing g with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, tauAut_proj, ih, Function.iterate_succ_apply]

theorem exists_conj_tauSp_iterate (α : MulAut (StatedSp 2 F)) :
    ∃ (x : StatedSp 2 F) (m : ℕ), ∀ g, α g = x * tauSp^[m] g * x⁻¹ := by
  obtain ⟨x', m, hx⟩ := F134.Sp4.exists_eq_conj_mul_tauAut_pow (MulAut.congr (projEquiv F) α)
  obtain ⟨x, rfl⟩ := proj_surjective x'
  refine ⟨x, m, fun g => (projEquiv F).injective ?_⟩
  have h1 := congrArg (fun β : MulAut (StatedProj (StatedSp 2 F)) => β (projEquiv F g)) hx
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.mul_apply, MulAut.conj_apply] at h1
  rw [h1]
  change proj 2 F x * (tauAut ^ m) (proj 2 F g) * (proj 2 F x)⁻¹ =
    proj 2 F (x * tauSp^[m] g * x⁻¹)
  rw [tauAut_pow_proj, map_mul, map_mul, map_inv]

theorem isCyclic_outer_projSp : IsCyclic (Outer (StatedProj (StatedSp 2 F))) := by
  refine ⟨⟨QuotientGroup.mk tauAut, fun q => ?_⟩⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨x, m, rfl⟩ := F134.Sp4.exists_eq_conj_mul_tauAut_pow α
  refine ⟨m, ?_⟩
  have hx : (QuotientGroup.mk (MulAut.conj x) : Outer (StatedProj (StatedSp 2 F))) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  simp only [zpow_natCast]
  rw [QuotientGroup.mk_mul, hx, one_mul, QuotientGroup.mk_pow]

omit [Finite F] in
theorem torus_conj_coord (t : Fin 2 → Fˣ) {w : StatedSp 2 F} (hw : w ∈ unipotent 2 F) :
    torusHom t * w * (torusHom t)⁻¹ ∈ unipotent 2 F ∧
      piA (torusHom t * w * (torusHom t)⁻¹) = (t 0 : F) * (t 1 : F)⁻¹ * piA w ∧
      piB (torusHom t * w * (torusHom t)⁻¹) = (t 1 : F) ^ 2 * piB w := by
  obtain ⟨x, c₀, c₁, c₂, h⟩ := exists_uMat hw
  have h' := spMat_torus_conj t h
  exact ⟨mem_unipotent_of_uMat h', by rw [piA_of h', piA_of h], by rw [piB_of h', piB_of h]⟩

omit [Finite F] in
theorem torus_conj_coordZ (t : Fin 2 → Fˣ) {z : StatedSp 2 F} (hz : z ∈ unipotent 2 F)
    (hA : piA z = 0) (hB : piB z = 0) :
    piA (torusHom t * z * (torusHom t)⁻¹) = 0 ∧ piB (torusHom t * z * (torusHom t)⁻¹) = 0 ∧
      zC (torusHom t * z * (torusHom t)⁻¹) = (t 0 : F) ^ 2 * zC z ∧
      zD (torusHom t * z * (torusHom t)⁻¹) = (t 0 : F) * (t 1 : F) * zD z := by
  have h' := spMat_torus_conj t (spMat_eq_of_piA_eq_zero hz hA hB)
  refine ⟨by rw [piA_of h']; ring, by rw [piB_of h']; ring, by rw [zC_of h']; ring,
    by rw [zD_of h']; ring⟩

theorem card_fix_le_mul {α : MulAut (StatedSp 2 F)} {v : StatedSp 2 F} {t : Fin 2 → Fˣ}
    {Φ : StatedSp 2 F → StatedSp 2 F} (fπ fζ : F × F → F × F) (hv : v ∈ unipotent 2 F)
    (hα : ∀ g, α g = v * torusHom t * Φ g * (v * torusHom t)⁻¹)
    (hΦU : ∀ u ∈ unipotent 2 F, Φ u ∈ unipotent 2 F)
    (hπ : ∀ u ∈ unipotent 2 F, (piA (Φ u), piB (Φ u)) = fπ (piA u, piB u))
    (hζ : ∀ z ∈ unipotent 2 F, piA z = 0 → piB z = 0 →
      piA (Φ z) = 0 ∧ piB (Φ z) = 0 ∧ (zC (Φ z), zD (Φ z)) = fζ (zC z, zD z)) :
    Nat.card ↥(unipotent 2 F ⊓ autFixed α) ≤
      Nat.card {p : F × F //
        p = ((t 0 : F) * (t 1 : F)⁻¹ * (fπ p).1, (t 1 : F) ^ 2 * (fπ p).2)} *
      Nat.card {p : F × F //
        p = ((t 0 : F) ^ 2 * (fζ p).1, (t 0 : F) * (t 1 : F) * (fζ p).2)} := by
  have hαv : ∀ g, α g = v * (torusHom t * Φ g * (torusHom t)⁻¹) * v⁻¹ := fun g => by
    rw [hα g]
    group
  have hrelπ : ∀ y ∈ unipotent 2 F, α y = y →
      (piA y, piB y) = ((t 0 : F) * (t 1 : F)⁻¹ * (fπ (piA y, piB y)).1,
        (t 1 : F) ^ 2 * (fπ (piA y, piB y)).2) := by
    intro y hy hfix
    obtain ⟨hTU, hTA, hTB⟩ := torus_conj_coord t (hΦU y hy)
    have hA := piA_conj hv hTU
    have hB := piB_conj hv hTU
    rw [← hαv, hfix, hTA] at hA
    rw [← hαv, hfix, hTB] at hB
    rw [← hπ y hy, hA, hB]
  have hrelζ : ∀ z ∈ unipotent 2 F, piA z = 0 → piB z = 0 → α z = z →
      (zC z, zD z) = ((t 0 : F) ^ 2 * (fζ (zC z, zD z)).1,
        (t 0 : F) * (t 1 : F) * (fζ (zC z, zD z)).2) := by
    intro z hz hA hB hfix
    obtain ⟨hΦA, hΦB, hΦζ⟩ := hζ z hz hA hB
    obtain ⟨hTU, -, -⟩ := torus_conj_coord t (hΦU z hz)
    obtain ⟨hTA, hTB, hTC, hTD⟩ := torus_conj_coordZ t (hΦU z hz) hΦA hΦB
    have hc : v * (torusHom t * Φ z * (torusHom t)⁻¹) * v⁻¹ =
        torusHom t * Φ z * (torusHom t)⁻¹ := by
      rw [mul_comm_of_piA_eq_zero hv hTU hTA hTB, mul_inv_cancel_right]
    rw [← hαv, hfix] at hc
    have e1 : (zC z, zD z) = (zC (torusHom t * Φ z * (torusHom t)⁻¹),
        zD (torusHom t * Φ z * (torusHom t)⁻¹)) := by
      rw [← hc]
    refine e1.trans ?_
    rw [hTC, hTD, ← hΦζ]
  let πY : ↥(unipotent 2 F ⊓ autFixed α) →* Multiplicative (F × F) :=
    { toFun := fun y => Multiplicative.ofAdd (piA (y : StatedSp 2 F), piB (y : StatedSp 2 F))
      map_one' := by
        simp only [OneMemClass.coe_one, piA_one, piB_one, Prod.mk_zero_zero, ofAdd_zero]
      map_mul' := fun y y' => by
        rw [← ofAdd_add, Prod.mk_add_mk, Subgroup.coe_mul, piA_mul y.2.1 y'.2.1,
          piB_mul y.2.1 y'.2.1] }
  have hπY : ∀ y, πY y = Multiplicative.ofAdd (piA (y : StatedSp 2 F), piB (y : StatedSp 2 F)) :=
    fun _ => rfl
  have h1 := Subgroup.card_mul_index πY.ker
  rw [Subgroup.index_ker] at h1
  have hrange : Nat.card πY.range ≤ Nat.card {p : F × F //
      p = ((t 0 : F) * (t 1 : F)⁻¹ * (fπ p).1, (t 1 : F) ^ 2 * (fπ p).2)} := by
    refine Nat.card_le_card_of_injective (fun p =>
      ⟨Multiplicative.toAdd (p : Multiplicative (F × F)), by
        obtain ⟨y, hy⟩ := p.2
        rw [← hy, hπY, toAdd_ofAdd]
        exact hrelπ y y.2.1 y.2.2⟩) fun p p' hpp => ?_
    have h2 := congrArg Subtype.val hpp
    simp only at h2
    exact Subtype.ext (Multiplicative.toAdd.injective h2)
  have hker : Nat.card πY.ker ≤ Nat.card {p : F × F //
      p = ((t 0 : F) ^ 2 * (fζ p).1, (t 0 : F) * (t 1 : F) * (fζ p).2)} := by
    have hk : ∀ y : πY.ker, piA ((y : ↥(unipotent 2 F ⊓ autFixed α)) : StatedSp 2 F) = 0 ∧
        piB ((y : ↥(unipotent 2 F ⊓ autFixed α)) : StatedSp 2 F) = 0 := by
      intro y
      have h2 := y.2
      rw [MonoidHom.mem_ker, hπY, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
        ← Prod.mk_zero_zero, Prod.mk.injEq] at h2
      exact h2
    refine Nat.card_le_card_of_injective (fun y => ⟨(zC (((y : ↥(unipotent 2 F ⊓ autFixed α)) :
      StatedSp 2 F)), zD (((y : ↥(unipotent 2 F ⊓ autFixed α)) : StatedSp 2 F))),
      hrelζ _ (y : ↥(unipotent 2 F ⊓ autFixed α)).2.1 (hk y).1 (hk y).2
        (y : ↥(unipotent 2 F ⊓ autFixed α)).2.2⟩) fun y y' hyy => ?_
    have h2 := congrArg Subtype.val hyy
    simp only [Prod.mk.injEq] at h2
    apply Subtype.ext
    apply Subtype.ext
    exact eq_of_zC_eq (y : ↥(unipotent 2 F ⊓ autFixed α)).2.1
      (y' : ↥(unipotent 2 F ⊓ autFixed α)).2.1 (hk y).1 (hk y).2 (hk y').1 (hk y').2 h2.1 h2.2
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul hrange hker

omit [CharP F 2] in
theorem card_fix_sq_le {σ : F ≃+* F} (hσ : σ ≠ 1) (l : F) :
    Nat.card {c : F // c = l * σ c} ^ 2 ≤ Nat.card F := by
  obtain ⟨e, he⟩ : ∃ e : F, σ e ≠ e := by
    by_contra hcon
    push Not at hcon
    exact hσ (RingEquiv.ext hcon)
  have hFσ : Nat.card {c : F // σ c = c} ^ 2 ≤ Nat.card F := by
    rw [sq, ← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun p => (p.1 : F) + e * p.2) fun p p' hpp => ?_
    simp only at hpp
    by_cases hb : (p.2 : F) = p'.2
    · have ha : (p.1 : F) = p'.1 := by rw [hb] at hpp; exact add_right_cancel hpp
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · exfalso
      have hb' : (p.2 : F) - p'.2 ≠ 0 := sub_ne_zero.2 hb
      have he' : e = ((p'.1 : F) - p.1) / ((p.2 : F) - p'.2) := by
        rw [eq_div_iff hb']
        linear_combination hpp
      apply he
      rw [he', map_div₀, map_sub, map_sub, p.1.2, p.2.2, p'.1.2, p'.2.2]
  have hV : Nat.card {c : F // c = l * σ c} ≤ Nat.card {c : F // σ c = c} := by
    by_cases h0 : ∃ d : F, d ≠ 0 ∧ d = l * σ d
    · obtain ⟨d, hd0, hd⟩ := h0
      have hl : l ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hd
        exact hd0 hd
      refine Nat.card_le_card_of_injective (fun c => ⟨(c : F) / d, ?_⟩) fun c c' hcc => ?_
      · rw [map_div₀]
        have hσd : σ d = d / l := by rw [eq_div_iff hl, mul_comm]; exact hd.symm
        have hσc : σ c = c / l := by rw [eq_div_iff hl, mul_comm]; exact c.2.symm
        rw [hσc, hσd]
        field_simp
      · have h1 := congrArg Subtype.val hcc
        simp only at h1
        exact Subtype.ext ((div_left_inj' hd0).1 h1)
    · push Not at h0
      have : Subsingleton {c : F // c = l * σ c} := ⟨fun c c' => Subtype.ext (by
        rw [show (c : F) = 0 from by_contra fun hc => h0 c hc c.2,
          show (c' : F) = 0 from by_contra fun hc => h0 c' hc c'.2])⟩
      have h1 : Nat.card {c : F // c = l * σ c} ≤ 1 := Finite.card_le_one_iff_subsingleton.2 this
      have h2 : 1 ≤ Nat.card {c : F // σ c = c} :=
        Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨⟨⟨1, map_one σ⟩⟩, inferInstance⟩)
      omega
  calc Nat.card {c : F // c = l * σ c} ^ 2 ≤ Nat.card {c : F // σ c = c} ^ 2 :=
        Nat.pow_le_pow_left hV 2
    _ ≤ Nat.card F := hFσ

omit [CharP F 2] in
theorem card_pair_field_le {σ : F ≃+* F} (hσ : σ ≠ 1) (l₁ l₂ : F) :
    Nat.card {p : F × F // p = (l₁ * σ p.1, l₂ * σ p.2)} ≤ Nat.card F := by
  have h1 : Nat.card {p : F × F // p = (l₁ * σ p.1, l₂ * σ p.2)} ≤
      Nat.card {c : F // c = l₁ * σ c} * Nat.card {c : F // c = l₂ * σ c} := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun p => (⟨p.1.1, congrArg Prod.fst p.2⟩,
      ⟨p.1.2, congrArg Prod.snd p.2⟩)) fun p p' hpp => ?_
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hpp
    exact Subtype.ext (Prod.ext hpp.1 hpp.2)
  have h2 := card_fix_sq_le hσ l₁
  have h3 := card_fix_sq_le hσ l₂
  have h4 : (Nat.card {c : F // c = l₁ * σ c} * Nat.card {c : F // c = l₂ * σ c}) ^ 2 ≤
      Nat.card F ^ 2 := by
    rw [mul_pow, sq (Nat.card F)]
    exact Nat.mul_le_mul h2 h3
  exact h1.trans ((Nat.pow_le_pow_iff_left two_ne_zero).1 h4)

omit [Field F] [CharP F 2] in
theorem card_pair_snd_le {f : F → F} :
    Nat.card {p : F × F // p.1 = f p.2} ≤ Nat.card F :=
  Nat.card_le_card_of_injective (fun p => p.1.2) fun p p' hpp => by
    simp only at hpp
    exact Subtype.ext (Prod.ext (by rw [p.2, p'.2, hpp]) hpp)

omit [Finite F] in
theorem iterate_mem_unipotent (m : ℕ) {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) :
    tauSp^[m] u ∈ unipotent 2 F := by
  induction m generalizing u with
  | zero => exact hu
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (tauSp_mem_unipotent hu)

theorem card_fix_le {α : MulAut (StatedSp 2 F)}
    (hαU : (unipotent 2 F).map α.toMonoidHom = unipotent 2 F)
    (hα : α ∉ OuterAutomorphisms.inner (StatedSp 2 F)) :
    Nat.card ↥(unipotent 2 F ⊓ autFixed α) ≤ Nat.card F ^ 2 := by
  obtain ⟨x, m, hxm⟩ := exists_conj_tauSp_iterate α
  have hΦU : ∀ u ∈ unipotent 2 F, tauSp^[m] u ∈ unipotent 2 F :=
    fun u hu => iterate_mem_unipotent m hu
  have hxN : x ∈ Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) := by
    have hinj : Function.Injective (fun u : unipotent 2 F =>
        (⟨tauSp^[m] u, hΦU u u.2⟩ : unipotent 2 F)) := fun u u' h =>
      Subtype.ext ((tauSp_bijective (F := F)).1.iterate m (congrArg Subtype.val h))
    have hsurj := Finite.surjective_of_injective hinj
    have hle : (unipotent 2 F).map (MulAut.conj x).toMonoidHom ≤ unipotent 2 F := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
      have hu' : tauSp^[m] (u : StatedSp 2 F) = w := congrArg Subtype.val hu
      have h1 : α u = x * w * x⁻¹ := by rw [hxm u, hu']
      rw [← hαU]
      exact ⟨u, u.2, h1⟩
    exact mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge)
  rw [normalizer_unipotent] at hxN
  set t := diagHom 2 F ⟨x, hxN⟩ with ht
  have hv : x * (torusHom t)⁻¹ ∈ unipotent 2 F := by
    have hb : (⟨x, hxN⟩ * (⟨torusHom t, torus_le_borelSubgroup ⟨t, rfl⟩⟩ :
        borelSubgroup 2 F)⁻¹ : borelSubgroup 2 F) ∈ (diagHom 2 F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, CartanSp4.diagHom_torusHom, mul_inv_cancel]
    rw [ker_diagHom, Subgroup.mem_subgroupOf] at hb
    exact hb
  have hα' : ∀ g, α g = x * (torusHom t)⁻¹ * torusHom t * tauSp^[m] g *
      (x * (torusHom t)⁻¹ * torusHom t)⁻¹ := fun g => by
    rw [hxm g]
    group
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
  ·
    have hσ : frobAut F ^ i ≠ 1 := by
      intro h1
      apply hα
      refine ⟨x, MulEquiv.ext fun g => ?_⟩
      rw [hxm g, tauSp_iterate_two_mul, h1, map_one]
      rfl
    refine (card_fix_le_mul (fun p => ((frobAut F ^ i) p.1, (frobAut F ^ i) p.2))
      (fun p => ((frobAut F ^ i) p.1, (frobAut F ^ i) p.2)) hv hα' hΦU ?_ ?_).trans ?_
    · intro u hu
      obtain ⟨y, c₀, c₁, c₂, h⟩ := exists_uMat hu
      have h' := spMat_fieldSp (frobAut F ^ i) h
      rw [tauSp_iterate_two_mul, piA_of h', piB_of h', piA_of h, piB_of h]
    · intro z hz hA hB
      have h' := spMat_fieldSp (frobAut F ^ i) (spMat_eq_of_piA_eq_zero hz hA hB)
      rw [tauSp_iterate_two_mul, piA_of h', piB_of h', zC_of h', zD_of h']
      simp
    · calc _ ≤ Nat.card F * Nat.card F :=
            Nat.mul_le_mul (card_pair_field_le hσ _ _) (card_pair_field_le hσ _ _)
        _ = Nat.card F ^ 2 := (sq _).symm
  ·
    have hΦ : ∀ g, tauSp^[2 * i + 1] g = fieldSp 2 F (frobAut F ^ i) (tauSp g) := fun g => by
      rw [Function.iterate_succ_apply, tauSp_iterate_two_mul]
    refine (card_fix_le_mul (fun p => ((frobAut F ^ i) p.2, (frobAut F ^ i) p.1 ^ 2))
      (fun p => ((frobAut F ^ i) p.2 ^ 2, (frobAut F ^ i) p.1)) hv hα' hΦU ?_ ?_).trans ?_
    · intro u hu
      obtain ⟨y, c₀, c₁, c₂, h⟩ := exists_uMat hu
      have h' := spMat_fieldSp (frobAut F ^ i) (spMat_tauSp h)
      rw [hΦ, piA_of h', piB_of h', piA_of h, piB_of h, map_pow]
    · intro z hz hA hB
      have h' := spMat_fieldSp (frobAut F ^ i) (spMat_tauSp (spMat_eq_of_piA_eq_zero hz hA hB))
      rw [hΦ, piA_of h', piB_of h', zC_of h', zD_of h']
      simp
    · refine Nat.mul_le_mul ?_ ?_ |>.trans (sq _).symm.le
      · refine le_trans (Nat.card_le_card_of_injective
          (fun p => (⟨p.1, congrArg Prod.fst p.2⟩ : {p : F × F // p.1 =
            (t 0 : F) * (t 1 : F)⁻¹ * (frobAut F ^ i) p.2})) fun p p' hpp => ?_)
          (card_pair_snd_le (f := fun b => (t 0 : F) * (t 1 : F)⁻¹ * (frobAut F ^ i) b))
        have h2 := congrArg Subtype.val hpp
        simp only at h2
        exact Subtype.ext h2
      · refine le_trans (Nat.card_le_card_of_injective
          (fun p => (⟨p.1, congrArg Prod.fst p.2⟩ : {p : F × F // p.1 =
            (t 0 : F) ^ 2 * (frobAut F ^ i) p.2 ^ 2})) fun p p' hpp => ?_)
          (card_pair_snd_le (f := fun b => (t 0 : F) ^ 2 * (frobAut F ^ i) b ^ 2))
        have h2 := congrArg Subtype.val hpp
        simp only at h2
        exact Subtype.ext h2

omit [Finite F] in
theorem isElemAbelian_radical : CFSG.Open.IsElemAbelian 2 (radical F) := by
  refine isElemAbelian_of_forall ?_ ?_
  · rintro _ ⟨C, hC, rfl⟩ _ ⟨E, hE, rfl⟩
    exact tau_comm hC hE
  · rintro _ ⟨C, hC, rfl⟩
    rw [← sq]
    exact tau_sq hC

theorem thompsonModel_sp4 (hF : 4 ≤ Nat.card F) : ThompsonModel (StatedSp 2 F) := by
  refine ⟨?_, fun P hP _ α _ hα hαP => ?_⟩
  · have := isCyclic_outer_projSp (F := F)
    exact isCyclic_of_surjective (OuterAutomorphisms.equivalence (projEquiv F)).symm.toMonoidHom
      (OuterAutomorphisms.equivalence (projEquiv F)).symm.surjective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := F) 2 2
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent 2 F) ⊤ :=
    hQ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Q
  obtain ⟨g, -, hg⟩ := hU.exists_conj hP
  set β : MulAut (StatedSp 2 F) := (MulAut.conj g)⁻¹ * α * MulAut.conj g with hβ
  have hβU : (unipotent 2 F).map β.toMonoidHom = unipotent 2 F := by
    rw [hβ, NQCat.map_mul_toMonoidHom, NQCat.map_mul_toMonoidHom, ← hg, hαP, hg,
      ← NQCat.map_mul_toMonoidHom, inv_mul_cancel]
    ext y
    simp
  have hβout : β ∉ OuterAutomorphisms.inner (StatedSp 2 F) := by
    rintro ⟨y, hy⟩
    apply hα
    refine ⟨g * y * g⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hy, hβ]
    group
  have hβapp : ∀ u, β u = g⁻¹ * α (g * u * g⁻¹) * g := fun u => by
    rw [hβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, ← map_inv MulAut.conj g,
      MulAut.conj_apply, inv_inv]
  have hcard : Nat.card ↥(P ⊓ autFixed α) = Nat.card ↥(unipotent 2 F ⊓ autFixed β) := by
    have hmap : (unipotent 2 F ⊓ autFixed β).map (MulAut.conj g).toMonoidHom =
        P ⊓ autFixed α := by
      ext y
      constructor
      · rintro ⟨u, ⟨hu, hufix⟩, rfl⟩
        have h1 : β u = u := hufix
        rw [hβapp] at h1
        refine ⟨by rw [hg]; exact ⟨u, hu, rfl⟩, ?_⟩
        change α (g * u * g⁻¹) = g * u * g⁻¹
        calc α (g * u * g⁻¹) = g * (g⁻¹ * α (g * u * g⁻¹) * g) * g⁻¹ := by group
          _ = g * u * g⁻¹ := by rw [h1]
      · rintro ⟨hyP, hyfix⟩
        rw [hg] at hyP
        obtain ⟨u, hu, rfl⟩ := hyP
        refine ⟨u, ⟨hu, ?_⟩, rfl⟩
        change β u = u
        have h1 : α (g * u * g⁻¹) = g * u * g⁻¹ := hyfix
        rw [hβapp, h1]
        group
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  refine ⟨(radical F).map (MulAut.conj g).toMonoidHom, ?_,
    isElemAbelian_map _ isElemAbelian_radical, ?_⟩
  · rw [hg]
    exact Subgroup.map_mono radical_le_unipotent
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_radical, hcard]
    have h1 := card_fix_le hβU hβout
    have h2 : 0 < Nat.card F ^ 2 := by positivity
    nlinarith

theorem thompsonModel_projSp4 (hF : 4 ≤ Nat.card F) :
    ThompsonModel (StatedProj (StatedSp 2 F)) :=
  ThompsonModel.of_mulEquiv (projEquiv F).symm (thompsonModel_sp4 hF)

end CFSG.Quasithin.H13.NQCat.LieThompson.Sp4
