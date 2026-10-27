module

public import CFSG.Quasithin.H13.U4ParRecog
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528UKG

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem map_le_centralizer_map {G Y : Type} [Group G] [Group Y] (ψ : G →* Y) {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    A.map ψ ≤ Subgroup.centralizer ((B.map ψ : Subgroup Y) : Set Y) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hAB ha) b hb]

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

@[expose] noncomputable def slUt (t : h.fixedField) :
    Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![1, t; 0, 1], by simp [det_fin_two]⟩

@[expose] noncomputable def slLt (t : h.fixedField) :
    Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![1, 0; t, 1], by simp [det_fin_two]⟩

@[expose] noncomputable def slW : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  ⟨!![0, 1; 1, 0], by
    have := charP_fixedField h
    simp [det_fin_two, CharTwo.neg_eq]⟩

theorem coe_conj_levHom {g : hypSU h 2 0} {x y c : K}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    (((levHom h A * g * (levHom h A)⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h (slMat h A 0 0 * x + slMat h A 0 1 * y) (slMat h A 1 0 * x + slMat h A 1 1 * y)
        c := by
  rw [coe_mul_hypSU, coe_mul_hypSU, coe_levHom, hg, coe_levHom_inv, levMat_conj_sMat]

variable {h}

theorem sAdm_of_mem_radQ {g : hypSU h 2 0} (hg : g ∈ radQ h) {x y c : K}
    (hG : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) : SAdm h x y c := by
  obtain ⟨x', y', c', hc', hg'⟩ := hg
  rw [hg'] at hG
  obtain ⟨rfl, rfl, rfl⟩ := sMat_injective h hG
  exact hc'

theorem coe_inv_of_sMat {g : hypSU h 2 0} {x y c : K} (hc : SAdm h x y c)
    (hG : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) :
    (((g⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = sMat h x y (h.bar c) := by
  rw [Subgroup.coe_inv]
  have h1 : ((g : GL Ix K) : Matrix Ix Ix K) * sMat h x y (h.bar c) = 1 := by
    rw [hG, sMat_mul_bar h hc]
  exact Units.inv_eq_of_mul_eq_one_right h1

theorem coe_eq_sMat_coord {g : hypSU h 2 0} (hg : g ∈ radQ h) :
    ((g : GL Ix K) : Matrix Ix Ix K) = sMat h (((g : GL Ix K) : Matrix Ix Ix K) ie2 if1)
      (((g : GL Ix K) : Matrix Ix Ix K) if2 if1) (((g : GL Ix K) : Matrix Ix Ix K) ie1 if1) := by
  obtain ⟨x, y, c, -, hG⟩ := hg
  rw [hG, sMat_ie2_if1, sMat_if2_if1, sMat_ie1_if1]

variable (h) in
@[expose] def RImg (R : Subgroup (hypSU h 2 0)) (x y : K) : Prop :=
  ∃ g ∈ R, ∃ c : K, ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c

section RImg

variable {R : Subgroup (hypSU h 2 0)}
  (hN : (levHom h).range ≤ Subgroup.normalizer (R : Set (hypSU h 2 0)))
include hN

omit hN in
theorem rimg_zero : RImg h R 0 0 :=
  ⟨1, R.one_mem, 0, by ext i j; simp [sMat_apply]⟩

omit hN in
theorem RImg.mul {x y x' y' : K} (h1 : RImg h R x y) (h2 : RImg h R x' y') :
    RImg h R (x + x') (y + y') := by
  obtain ⟨g, hg, c, hgc⟩ := h1
  obtain ⟨g', hg', c', hgc'⟩ := h2
  exact ⟨g * g', R.mul_mem hg hg', _, by rw [coe_mul_hypSU, hgc, hgc', sMat_mul]⟩

omit hN in
theorem RImg.congr {x y x' y' : K} (h1 : RImg h R x y) (hx : x = x') (hy : y = y') :
    RImg h R x' y' := hx ▸ hy ▸ h1

theorem RImg.conj {x y : K} (h1 : RImg h R x y)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    RImg h R (slMat h A 0 0 * x + slMat h A 0 1 * y) (slMat h A 1 0 * x + slMat h A 1 1 * y) := by
  obtain ⟨g, hg, c, hgc⟩ := h1
  refine ⟨levHom h A * g * (levHom h A)⁻¹, ?_, c, coe_conj_levHom h hgc A⟩
  exact (Subgroup.mem_normalizer_iff.mp (hN ⟨A, rfl⟩) g).mp hg

theorem RImg.lower {x y : K} (h1 : RImg h R x y) (t : h.fixedField) :
    RImg h R x ((t : K) * x + y) :=
  (RImg.conj hN h1 (slLt h t)).congr (by simp [slMat, slLt]) (by simp [slMat, slLt])

theorem RImg.swap {x y : K} (h1 : RImg h R x y) : RImg h R y x :=
  (RImg.conj hN h1 (slW h)).congr (by simp [slMat, slW]) (by simp [slMat, slW])

theorem RImg.fst {x y : K} (h1 : RImg h R x y) : RImg h R x 0 := by
  have := h.charP
  have h2 := (RImg.lower hN h1 1).mul h1
  have h3 : RImg h R 0 x := h2.congr (CharTwo.add_self_eq_zero x)
    (by simp [add_assoc, CharTwo.add_self_eq_zero])
  exact RImg.swap hN h3

theorem RImg.snd {x y : K} (h1 : RImg h R x y) : RImg h R y 0 :=
  RImg.fst hN (RImg.swap hN h1)

theorem RImg.of_fst_snd {x y : K} (hx : RImg h R x 0) (hy : RImg h R y 0) : RImg h R x y :=
  (hx.mul (RImg.swap hN hy)).congr (add_zero x) (zero_add y)

end RImg

@[expose] noncomputable def lineL (R : Subgroup (hypSU h 2 0))
    (hN : (levHom h).range ≤ Subgroup.normalizer (R : Set (hypSU h 2 0))) :
    Submodule h.fixedField K where
  carrier := {x | RImg h R x 0}
  add_mem' hx hy := (RImg.mul hx hy).congr rfl (add_zero 0)
  zero_mem' := rimg_zero
  smul_mem' t x hx := (RImg.snd hN (RImg.lower hN hx t)).congr (by rw [add_zero]; rfl) rfl

theorem mem_lineL {R : Subgroup (hypSU h 2 0)}
    {hN : (levHom h).range ≤ Subgroup.normalizer (R : Set (hypSU h 2 0))} {x : K} :
    x ∈ lineL R hN ↔ RImg h R x 0 :=
  Iff.rfl

variable (h) in
@[expose] noncomputable def radS (L : Submodule h.fixedField K) : Subgroup (hypSU h 2 0) where
  carrier := {g | g ∈ radQ h ∧ ((g : GL Ix K) : Matrix Ix Ix K) ie2 if1 ∈ L ∧
    ((g : GL Ix K) : Matrix Ix Ix K) if2 if1 ∈ L}
  mul_mem' := by
    rintro g g' ⟨hg, hx, hy⟩ ⟨hg', hx', hy'⟩
    refine ⟨(radQ h).mul_mem hg hg', ?_, ?_⟩
    · rw [coe_mul_hypSU, coe_eq_sMat_coord hg, coe_eq_sMat_coord hg', sMat_mul, sMat_ie2_if1]
      exact L.add_mem hx hx'
    · rw [coe_mul_hypSU, coe_eq_sMat_coord hg, coe_eq_sMat_coord hg', sMat_mul, sMat_if2_if1]
      exact L.add_mem hy hy'
  one_mem' := ⟨(radQ h).one_mem, by simp, by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hx, hy⟩
    have hc := sAdm_of_mem_radQ hg (coe_eq_sMat_coord hg)
    refine ⟨(radQ h).inv_mem hg, ?_, ?_⟩
    · rw [coe_inv_of_sMat hc (coe_eq_sMat_coord hg), sMat_ie2_if1]
      exact hx
    · rw [coe_inv_of_sMat hc (coe_eq_sMat_coord hg), sMat_if2_if1]
      exact hy

theorem mem_radS {L : Submodule h.fixedField K} {g : hypSU h 2 0} :
    g ∈ radS h L ↔ g ∈ radQ h ∧ ((g : GL Ix K) : Matrix Ix Ix K) ie2 if1 ∈ L ∧
      ((g : GL Ix K) : Matrix Ix Ix K) if2 if1 ∈ L :=
  Iff.rfl

variable (h) in
theorem card_radS (L : Submodule h.fixedField K) :
    Nat.card (radS h L) = Nat.card L * Nat.card L * 2 ^ m := by
  have := h.charP
  have hF : ∀ {x y c : K}, SAdm h x y c → c + h.bar x * y ∈ h.fixedField := by
    intro x y c hc
    rw [h.mem_fixedField, map_add, map_mul, h.bar_bar]
    unfold SAdm at hc
    grind
  have hF' : ∀ (x y : K) (z : h.fixedField), SAdm h x y ((z : K) + h.bar x * y) := by
    intro x y z
    have hz : h.bar (z : K) = z := (h.mem_fixedField).mp z.2
    unfold SAdm
    rw [map_add, map_mul, h.bar_bar, hz]
    grind
  let e : radS h L ≃ (L × L) × h.fixedField :=
    { toFun := fun g => ((⟨_, (mem_radS.mp g.2).2.1⟩, ⟨_, (mem_radS.mp g.2).2.2⟩),
        ⟨_, hF (sAdm_of_mem_radQ (mem_radS.mp g.2).1 (coe_eq_sMat_coord (mem_radS.mp g.2).1))⟩)
      invFun := fun p => ⟨sElt h (hF' p.1.1 p.1.2 p.2), mem_radS.mpr ⟨sElt_mem_radQ h _,
        by rw [coe_sElt, sMat_ie2_if1]; exact p.1.1.2,
        by rw [coe_sElt, sMat_if2_if1]; exact p.1.2.2⟩⟩
      left_inv := by
        rintro ⟨g, hg⟩
        apply Subtype.ext
        apply hypSU_ext
        show sMat h (((g : GL Ix K) : Matrix Ix Ix K) ie2 if1)
          (((g : GL Ix K) : Matrix Ix Ix K) if2 if1)
          (((g : GL Ix K) : Matrix Ix Ix K) ie1 if1 +
            h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie2 if1) *
              ((g : GL Ix K) : Matrix Ix Ix K) if2 if1 +
            h.bar (((g : GL Ix K) : Matrix Ix Ix K) ie2 if1) *
              ((g : GL Ix K) : Matrix Ix Ix K) if2 if1) = ((g : GL Ix K) : Matrix Ix Ix K)
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, ← coe_eq_sMat_coord (mem_radS.mp hg).1]
      right_inv := by
        rintro ⟨⟨a, b⟩, z⟩
        ext <;> simp [coe_sElt, sMat_ie2_if1, sMat_if2_if1, sMat_ie1_if1, add_assoc,
          CharTwo.add_self_eq_zero] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, h.card_fixedField]

variable (h) in
theorem card_submodule_eq {L : Submodule h.fixedField K} (h0 : L ≠ ⊥) (htop : L ≠ ⊤) :
    Nat.card L = 2 ^ m := by
  have := h.finite
  have hK : Nat.card K = (2 ^ m) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hKd := Module.natCard_eq_pow_finrank (K := h.fixedField) (V := K)
  have hLd := Module.natCard_eq_pow_finrank (K := h.fixedField) (V := L)
  rw [h.card_fixedField] at hKd hLd
  have h2m : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.one_le
  have hdK : Module.finrank h.fixedField K = 2 := by
    rw [hK] at hKd
    exact (Nat.pow_right_injective h2m hKd).symm
  have hle := Submodule.finrank_le L
  have h1 : Module.finrank h.fixedField L ≠ 0 := fun e => h0 (Submodule.finrank_eq_zero.mp e)
  have h2 : Module.finrank h.fixedField L ≠ 2 := fun e =>
    htop (Submodule.eq_top_of_finrank_eq (e.trans hdK.symm))
  have h3 : Module.finrank h.fixedField L = 1 := by omega
  rw [hLd, h3, pow_one]

theorem sup_eq_radS {R : Subgroup (hypSU h 2 0)} (hRQ : R ≤ radQ h)
    (hN : (levHom h).range ≤ Subgroup.normalizer (R : Set (hypSU h 2 0))) :
    R ⊔ zRad h = radS h (lineL R hN) := by
  have := h.charP
  apply le_antisymm
  · refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · have hgQ := hRQ hg
      have hI : RImg h R _ _ := ⟨g, hg, _, coe_eq_sMat_coord hgQ⟩
      exact mem_radS.mpr ⟨hgQ, mem_lineL.mpr (RImg.fst hN hI), mem_lineL.mpr (RImg.snd hN hI)⟩
    · obtain ⟨c, hc, hG⟩ := hg
      refine mem_radS.mpr ⟨zRad_le_radQ h ⟨c, hc, hG⟩, ?_, ?_⟩
      · rw [hG, sMat_ie2_if1]
        exact (lineL R hN).zero_mem
      · rw [hG, sMat_if2_if1]
        exact (lineL R hN).zero_mem
  · intro g hg
    obtain ⟨hgQ, hx, hy⟩ := mem_radS.mp hg
    obtain ⟨x, y, c, hc, hG⟩ := hgQ
    rw [hG, sMat_ie2_if1] at hx
    rw [hG, sMat_if2_if1] at hy
    obtain ⟨r, hr, c', hr'⟩ := RImg.of_fst_snd hN (mem_lineL.mp hx) (mem_lineL.mp hy)
    have hrQ := hRQ hr
    have hc' := sAdm_of_mem_radQ hrQ hr'
    have hz : g * r⁻¹ ∈ zRad h := by
      have hmem : g * r⁻¹ ∈ radQ h := (radQ h).mul_mem ⟨x, y, c, hc, hG⟩ ((radQ h).inv_mem hrQ)
      have hGz : (((g * r⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
          sMat h 0 0 (c + h.bar c' + (h.bar y * x + h.bar x * y)) := by
        rw [coe_mul_hypSU, coe_inv_of_sMat hc' hr', hG, sMat_mul, CharTwo.add_self_eq_zero,
          CharTwo.add_self_eq_zero]
      exact ⟨_, (sAdm_zero_zero_iff h).mp (sAdm_of_mem_radQ hmem hGz), hGz⟩
    have e : g = (g * r⁻¹) * r := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hr)

theorem zRad_le_commutator_of_mem {R : Subgroup (hypSU h 2 0)} {g : hypSU h 2 0} (hgR : g ∈ R)
    (hgQ : g ∈ radQ h) (hgZ : g ∉ zRad h) : zRad h ≤ ⁅R, radQ h⁆ := by
  have := h.charP
  obtain ⟨x, y, c, hc, hG⟩ := hgQ
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · subst hx hy
        exact (hgZ ⟨c, (sAdm_zero_zero_iff h).mp hc, hG⟩).elim
      · exact Or.inr hy
    · exact Or.inl hx
  rintro z ⟨a, ha, hz⟩
  obtain ⟨t, ht⟩ := h.traceLin_surjective ⟨a, (h.mem_fixedField).mpr ha⟩
  have ht' : h.trace t = a := congrArg Subtype.val ht
  obtain ⟨x', y', hadm', htr⟩ : ∃ x' y' : K, SAdm h x' y' 0 ∧
      h.bar y * x' + h.bar x * y' = t := by
    rcases hxy with hx | hy
    · have hbx : h.bar x ≠ 0 := fun e => hx (by rw [← h.bar_bar x, e, map_zero])
      refine ⟨0, (h.bar x)⁻¹ * t, sAdm_zero_y h _, ?_⟩
      rw [mul_zero, zero_add, ← mul_assoc, mul_inv_cancel₀ hbx, one_mul]
    · have hby : h.bar y ≠ 0 := fun e => hy (by rw [← h.bar_bar y, e, map_zero])
      refine ⟨(h.bar y)⁻¹ * t, 0, sAdm_x_zero h _, ?_⟩
      rw [mul_zero, add_zero, ← mul_assoc, mul_inv_cancel₀ hby, one_mul]
  have hcomm : z = g * sElt h hadm' * g⁻¹ * (sElt h hadm')⁻¹ := by
    apply hypSU_ext
    rw [coe_mul_hypSU, coe_mul_hypSU, coe_mul_hypSU, coe_inv_of_sMat hc hG, coe_sElt_inv,
      coe_sElt, hG, commutator_sMat h hc hadm', hz, htr, ht']
  rw [hcomm, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hgR (sElt_mem_radQ h hadm')

theorem module_radQ {R : Subgroup (hypSU h 2 0)} (hRQ : R ≤ radQ h)
    (hN : (levHom h).range ≤ Subgroup.normalizer (R : Set (hypSU h 2 0)))
    (hRZ : ¬ R ≤ zRad h) (hRZQ : R ⊔ zRad h ≠ radQ h) :
    ⁅R, radQ h⁆ = zRad h ∧ Nat.card ↥(R ⊔ zRad h) = (2 ^ m) ^ 3 := by
  have := h.charP
  obtain ⟨g, hgR, hgZ⟩ : ∃ g ∈ R, g ∉ zRad h := by
    by_contra hcon
    exact hRZ fun g hg => by_contra fun hgZ => hcon ⟨g, hg, hgZ⟩
  refine ⟨le_antisymm ?_ (zRad_le_commutator_of_mem hgR (hRQ hgR) hgZ), ?_⟩
  · rw [← commutator_radQ h]
    exact Subgroup.commutator_mono hRQ le_rfl
  · have hL0 : lineL R hN ≠ ⊥ := by
      intro hbot
      have hgQ := hRQ hgR
      have hI : RImg h R _ _ := ⟨g, hgR, _, coe_eq_sMat_coord hgQ⟩
      have hx : ((g : GL Ix K) : Matrix Ix Ix K) ie2 if1 ∈ lineL R hN :=
        mem_lineL.mpr (RImg.fst hN hI)
      have hy : ((g : GL Ix K) : Matrix Ix Ix K) if2 if1 ∈ lineL R hN :=
        mem_lineL.mpr (RImg.snd hN hI)
      rw [hbot, Submodule.mem_bot] at hx hy
      have hG := coe_eq_sMat_coord hgQ
      rw [hx, hy] at hG
      exact hgZ ⟨_, (sAdm_zero_zero_iff h).mp (sAdm_of_mem_radQ hgQ hG), hG⟩
    have hLtop : lineL R hN ≠ ⊤ := by
      intro htop
      apply hRZQ
      rw [sup_eq_radS hRQ hN, htop]
      apply le_antisymm (fun g hg => (mem_radS.mp hg).1)
      intro g hg
      exact mem_radS.mpr ⟨hg, Submodule.mem_top, Submodule.mem_top⟩
    rw [sup_eq_radS hRQ hN, card_radS h, card_submodule_eq h hL0 hLtop]
    ring

theorem factU4ParabolicModule_holds : FactU4ParabolicModule := by
  intro Y _ m T M₁ M hm hY hpair hsp
  obtain ⟨-, K, _, h, ψ, hψ, -, -, -, hcore, hO⟩ := recog_of hm hY hpair hsp
  have hZ : centerOf (pCoreOf 2 (perfectCore M)) = (zRad h).map ψ := by
    rw [hO, centerOf_map_of_inj hψ, centerOf_radQ]
  rw [hZ, hO, hcore]
  refine ⟨map_le_centralizer_map ψ (perfectCore_parP_le_centralizer h), ?_, ?_⟩
  · rw [← Subgroup.map_commutator, commutator_radQ_perfectCore h hm]
  · intro R hRQ hRN hRZ hRZQ
    have hR : (R.comap ψ).map ψ = R :=
      Subgroup.map_comap_eq_self (hRQ.trans (Subgroup.map_le_range ψ _))
    have hR₀Q : R.comap ψ ≤ radQ h := fun g hg =>
      (Subgroup.mem_map_iff_mem hψ).mp (hRQ hg)
    have hR₀N : (levHom h).range ≤ Subgroup.normalizer ((R.comap ψ : Subgroup _) : Set _) := by
      rintro _ ⟨A, rfl⟩
      have hA : ψ (levHom h A) ∈ Subgroup.normalizer (R : Set Y) :=
        hRN (Subgroup.mem_map_of_mem ψ (levHom_range_le_perfectCore h hm ⟨A, rfl⟩))
      rw [Subgroup.mem_normalizer_iff] at hA ⊢
      intro g
      have := hA (ψ g)
      simpa [Subgroup.mem_comap, map_mul, map_inv] using this
    have hR₀Z : ¬ R.comap ψ ≤ zRad h := fun hle => hRZ (by
      rw [← hR]
      exact Subgroup.map_mono hle)
    have hR₀ZQ : R.comap ψ ⊔ zRad h ≠ radQ h := fun e => hRZQ (by
      rw [← hR, ← Subgroup.map_sup, e])
    obtain ⟨hc, hcard⟩ := module_radQ hR₀Q hR₀N hR₀Z hR₀ZQ
    refine ⟨?_, ?_⟩
    · rw [← hR, ← Subgroup.map_commutator, hc]
    · rw [← hR, ← Subgroup.map_sup, Subgroup.card_map_of_injective hψ, hcard]

end CFSG.Quasithin.H13.U4Par
