module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154DeltaComm
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem s16h_bl_isElemAbelian {X : Type*} [Group X] {L : Subgroup X} {p r : ℕ}
    (h : IsElemAbelianOfRank p r ↥L) : IsElemAbelian p L :=
  ⟨⟨⟨fun a b => Subtype.ext (congrArg Subtype.val (s16h_dc_comm_of_elem h a b))⟩⟩,
    fun x hx => by
      simpa using congrArg Subtype.val (s16h_dc_pow_eq_one_of_elem h ⟨x, hx⟩)⟩

theorem s16h_bl_le_pRank {X : Type*} [Group X] [Finite X] {L : Subgroup X} {p r : ℕ} (hp : 1 < p)
    (h : IsElemAbelianOfRank p r ↥L) : r ≤ CFSG.Open.pRank p L :=
  CFSG.SectionRank.le_pRank hp le_rfl (s16h_bl_isElemAbelian h) (s16h_dc_card_of_elem h)

section Conc

variable {W : Type} [CommGroup W]

theorem s16h_bl_eq_one_of_fixes {A L : Subgroup (MulAut W)} {t : MulAut W}
    (h : Conc4_136W A t L) {l : MulAut W} (hl : l ∈ L)
    (hfix : ∀ u ∈ commSub (⊤ : Subgroup W) L, l u = u) : l = 1 := by
  obtain ⟨hgen, h2, -⟩ := h
  have hF : fixV (Subgroup.zpowers l) = ⊤ := by
    rw [← top_le_iff, ← hgen]
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    obtain ⟨a, ha, rfl⟩ := hX
    intro u hu
    rw [mem_fixV_zpowers_iff_apply]
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
    by_cases haN : a ∈ normalizer (L : Set (MulAut W))
    · have haw : a w ∈ commSub (⊤ : Subgroup W) L :=
        commSub_top_map151b (X := L) (Y := L) (g := a)
          (fun x hx => (Subgroup.mem_normalizer_iff.mp haN x).mp hx) w hw
      exact hfix (a w) haw
    · have hainvN : a⁻¹ ∉ normalizer (L : Set (MulAut W)) := by
        intro hcon
        exact haN ((normalizer (L : Set (MulAut W))).inv_mem hcon)
      have hle := commSub_eq_bot_iff.mp (h2 a⁻¹ (A.inv_mem ha) hainvN).2
      have hy : (MulAut.conj a⁻¹).toMonoidHom l ∈ L.map (MulAut.conj a⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj a⁻¹).toMonoidHom hl
      have hfixy : (a⁻¹ * l * a) w = w := (mem_fixV.mp (hle hw)) _ hy
      have h1 : a⁻¹ (l (a w)) = w := by simpa [MulAut.mul_apply] using hfixy
      have h2' := congrArg (fun z => a z) h1
      rwa [MulAut.apply_inv_self] at h2'
  ext v
  have hv : v ∈ fixV (Subgroup.zpowers l) := by rw [hF]; trivial
  simpa using (mem_fixV_zpowers_iff_apply.mp hv)

theorem s16h_bl_mem_normalizer_of_stab {A L : Subgroup (MulAut W)} {t : MulAut W}
    (h : Conc4_136W A t L) {g : MulAut W} (hgA : g ∈ A)
    (hgs : g ∈ stabSub (commSub (⊤ : Subgroup W) L)) : g ∈ normalizer (L : Set (MulAut W)) := by
  by_contra hn
  have hle := commSub_eq_bot_iff.mp (h.2.1 g hgA hn).2
  have hL1 : L = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall L).2 fun l hl => ?_
    refine s16h_bl_eq_one_of_fixes h hl fun u hu => ?_
    have hgu : g u ∈ commSub (⊤ : Subgroup W) L := (mem_stabSub.1 hgs u).2 hu
    have hx : (MulAut.conj g).toMonoidHom l ∈ L.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hl
    have h1 : (g * l * g⁻¹) (g u) = g u := (mem_fixV.mp (hle hgu)) _ hx
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h1
    exact g.injective h1
  apply hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp [hL1, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_one_iff_eq_inv]

private def s16h_bl_commHom (t : MulAut W) : W →* W where
  toFun y := t y * y⁻¹
  map_one' := by simp
  map_mul' y y' := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

theorem s16h_bl_rk_le_of_inf_eq_bot [Finite W] {U : Subgroup W} {t : MulAut W}
    (h : U ⊓ U.map t.toMonoidHom = ⊥) :
    rk ↥U ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
  let φ : U →* W := (s16h_bl_commHom t).comp U.subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hty : t (y : W) = y := mul_inv_eq_one.mp hy
    have hmem : (y : W) ∈ U ⊓ U.map t.toMonoidHom :=
      ⟨y.2, ⟨y, y.2, hty⟩⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcard : Nat.card ↥U = Nat.card ↥φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hle : φ.range ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers t) := by
    rintro _ ⟨y, rfl⟩
    exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, (y : W), Subgroup.mem_top _, rfl⟩
  calc rk ↥U = rk ↥φ.range := by unfold rk; rw [hcard]
    _ ≤ _ := rk_mono hle

theorem s16h_bl_rk_le_of_not_normalizes [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (h : Conc4_136W A t L) (hind : sSupIndep (conjSubs A (commSub (⊤ : Subgroup W) L)))
    (htA : t ∈ A) (htn : t ∉ normalizer (L : Set (MulAut W))) :
    rk ↥(commSub (⊤ : Subgroup W) L) ≤
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
  set U := commSub (⊤ : Subgroup W) L with hU
  have hne : U.map t.toMonoidHom ≠ U := by
    intro heq
    refine htn (s16h_bl_mem_normalizer_of_stab h htA (mem_stabSub.2 fun u => ?_))
    constructor
    · intro hu
      have hu' : t u ∈ U := hu
      rw [← heq] at hu'
      obtain ⟨u', hu'', hu'e⟩ := Subgroup.mem_map.1 hu'
      exact (t.injective hu'e) ▸ hu''
    · intro hu
      have hu' : u ∈ U := hu
      have : t u ∈ U.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hu'
      rwa [heq] at this
  have h1 : U ∈ conjSubs A U := ⟨1, A.one_mem, by ext; simp⟩
  have h2 : U.map t.toMonoidHom ∈ conjSubs A U := ⟨t, htA, rfl⟩
  have hdis := hind.pairwiseDisjoint h1 h2 (Ne.symm hne)
  exact s16h_bl_rk_le_of_inf_eq_bot (disjoint_iff.mp hdis)

theorem s16h_bl_mem_normalizer_or_rk [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (h : Conc4_136W A t L) (hind : sSupIndep (conjSubs A (commSub (⊤ : Subgroup W) L)))
    (htA : t ∈ A) (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3) :
    t ∈ normalizer (L : Set (MulAut W)) ∨ rk ↥(commSub (⊤ : Subgroup W) L) ≤ 3 :=
  (em _).imp_right fun htn => (s16h_bl_rk_le_of_not_normalizes h hind htA htn).trans htr

theorem s16h_bl_le_commutator_of_inverted {X : Type*} [Group X] {A L : Subgroup X} {t : X}
    (htA : t ∈ A) (hLA : L ≤ A) (hL3 : ∀ x ∈ L, x ^ 3 = 1)
    (hinv : ∀ x ∈ L, t * x * t⁻¹ = x⁻¹) : L ≤ ⁅A, A⁆ := by
  intro x hx
  have hc : ⁅x, t⁆ ∈ ⁅A, A⁆ := Subgroup.commutator_mem_commutator (hLA hx) htA
  have hxt : ⁅x, t⁆ = x ^ 2 := by
    have h1 := congrArg (fun y => y⁻¹) (hinv x hx)
    have h' : t * x⁻¹ * t⁻¹ = x := by simpa [mul_assoc] using h1
    calc ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
      _ = x * x := by rw [h']
      _ = x ^ 2 := (sq x).symm
  have hx2 : x = (x ^ 2) ^ 2 := by
    have h3 := hL3 x hx
    calc x = x * x ^ 3 := by rw [h3, mul_one]
      _ = (x ^ 2) ^ 2 := by group
  rw [hx2, ← hxt]
  exact (⁅A, A⁆).pow_mem hc 2

theorem s16h_bl_le_commutator_of_deltaSym [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hconc : Conc4_136W A t L) (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3) {p r m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : (p = 3 ∧ m = 2) ∨ (p = 7 ∧ m = 3)) (hr : 2 ≤ r)
    (hpr : ¬ (p = 3 ∧ r = 2)) (hLA : L ≤ A) (hE : IsElemAbelianOfRank p r ↥L)
    (hLt : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥)
    (hD : DeltaSym A t (commSub (⊤ : Subgroup W) L) r m) : L ≤ ⁅A, A⁆ :=
  s16h_dc_le_commutator hW ht2 htr hp hp2 hm hr hpr hLA
    (fun g hg => (Subgroup.mem_normalizer_iff_map_conj_eq.1
      (s16h_bl_mem_normalizer_of_stab hconc hg.1 hg.2)))
    (fun l hl hfix => s16h_bl_eq_one_of_fixes hconc hl hfix) hE hLt hD

end Conc

section Central

variable {X : Type*} [Group X]

theorem s16h_der_exists_central_of_abelian {A L : Subgroup X} {t : X} {p r : ℕ}
    (htA : t ∈ A) (hLA : L ≤ A) (htn : t ∈ normalizer (L : Set X))
    (hE : IsElemAbelianOfRank p r ↥L) (hLt : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ B : Subgroup X, B ≤ L ∧ B ≠ ⊥ ∧ IsElemAbelian p B ∧
      (∀ b ∈ B, ∀ l ∈ L, b * l = l * b) ∧ B ≤ ⁅A, A⁆ := by
  have hB : ⁅L, Subgroup.zpowers t⁆ ≤ L :=
    (Subgroup.le_normalizer_iff_commutator_le_left
      (H := Subgroup.zpowers t) (K := L)).1 (Subgroup.zpowers_le.2 htn)
  refine ⟨⁅L, Subgroup.zpowers t⁆, hB, hLt, ?_, ?_, ?_⟩
  · exact (s16h_bl_isElemAbelian hE).mono hB
  · intro b hb l hl
    exact congrArg Subtype.val (s16h_dc_comm_of_elem hE ⟨b, hB hb⟩ ⟨l, hl⟩)
  · exact Subgroup.commutator_mono hLA (Subgroup.zpowers_le.2 htA)

theorem s16h_der_exists_central_of_extraspecial {A L : Subgroup X} {p : ℕ} (hp : p.Prime)
    (hLA : L ≤ A) (hL : IsPOnePlusTwo p ↥L) :
    ∃ B : Subgroup X, B ≤ L ∧ B ≠ ⊥ ∧ IsElemAbelian p B ∧
      (∀ b ∈ B, ∀ l ∈ L, b * l = l * b) ∧ B ≤ ⁅A, A⁆ := by
  obtain ⟨hext, hcard, hexp⟩ := hL
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsExtraspecial p ↥L := hext
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero 3 hp.ne_zero)
  let B : Subgroup X := (Subgroup.center ↥L).map L.subtype
  have hBcard : Nat.card B = p := by
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      IsExtraspecial.center_order_p p ↥L]
  have hBne : B ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card B = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hBcard] at h1
    exact hp.ne_one h1
  have hZel : IsElemAbelian p (Subgroup.center ↥L) :=
    ⟨Subgroup.center.isMulCommutative (G := ↥L), fun z _ => hexp z⟩
  have hBel : IsElemAbelian p B := hZel.map L.subtype
  have hcomm_le : commutator ↥L ≤ Subgroup.center ↥L := by
    haveI : IsMulCommutative (↥L ⧸ Subgroup.center ↥L) :=
      (IsExtraspecial.quotient_elementary_abelian p ↥L).toIsMulCommutative
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Subgroup.center ↥L)).mp inferInstance
  have hCne : commutator ↥L ≠ ⊥ := by
    intro hC
    have hcomm : IsMulCommutative ↥L := (commutator_eq_bot_iff (G := ↥L)).1 hC
    letI : IsMulCommutative ↥L := hcomm
    have htop : Subgroup.center ↥L = ⊤ := Subgroup.center_eq_top
    have hsub : Subsingleton (↥L ⧸ Subgroup.center ↥L) :=
      (QuotientGroup.subsingleton_iff (N := Subgroup.center ↥L)).2 htop
    exact not_nontrivial_iff_subsingleton.mpr hsub hext.quotient_nontrivial
  have hCcard_ne_one : Nat.card (commutator ↥L) ≠ 1 := by
    intro h1
    exact hCne ((Subgroup.eq_bot_iff_card (H := commutator ↥L)).2 h1)
  have hCcard_dvd : Nat.card (commutator ↥L) ∣ p := by
    have h := Subgroup.card_subgroup_dvd_card
      ((commutator ↥L).subgroupOf (Subgroup.center ↥L))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcomm_le).toEquiv,
      IsExtraspecial.center_order_p p ↥L] at h
  have hCcard : Nat.card (commutator ↥L) = p := by
    rcases (Nat.dvd_prime hp).1 hCcard_dvd with h1 | h1
    · exact absurd h1 hCcard_ne_one
    · exact h1
  have hcenter_le : Subgroup.center ↥L ≤ commutator ↥L := by
    rw [Subgroup.eq_of_le_of_card_ge hcomm_le]
    rw [hCcard, IsExtraspecial.center_order_p p ↥L]
  refine ⟨B, Subgroup.map_subtype_le _, hBne, hBel, ?_, ?_⟩
  · intro b hb l hl
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hb
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩)).symm
  · calc B ≤ (commutator ↥L).map L.subtype := Subgroup.map_mono hcenter_le
      _ = ⁅L, L⁆ := by
        change (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆).map L.subtype = ⁅L, L⁆
        rw [Subgroup.map_commutator]
        simp only [Subgroup.map_top, Subgroup.range_subtype]
      _ ≤ ⁅A, A⁆ := Subgroup.commutator_mono hLA hLA

end Central

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
