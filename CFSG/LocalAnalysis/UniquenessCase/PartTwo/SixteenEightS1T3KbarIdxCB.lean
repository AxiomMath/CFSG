module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxCA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_toMonoidHom_one : (1 : MulAut W).toMonoidHom = MonoidHom.id W := rfl

theorem s16t3_map_mem_irrSet (h : ThreeNat A L T) {a : MulAut W}
    (ha : a ∈ Subgroup.normalizer (L : Set (MulAut W))) {J : Subgroup W}
    (hJ : J ∈ irrSet L) : J.map a.toMonoidHom ∈ irrSet L := by
  have hfixmap : (fixV L).map a.toMonoidHom = fixV L := s16t3_inv_map_fixV_normalizer ha
  have hLmap : L.map (MulAut.conj a).toMonoidHom = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact conj_mem_of_mem_normalizer ha hy
    · intro hx
      exact ⟨a⁻¹ * x * a, inv_conj_mem_of_mem_normalizer ha hx, by
        change (MulAut.conj a) (a⁻¹ * x * a) = x
        simp only [MulAut.conj_apply]
        group⟩
  refine ⟨?_, ?_⟩
  · have h1 : commSub (J.map a.toMonoidHom) (L.map (MulAut.conj a).toMonoidHom) =
        (commSub J L).map a.toMonoidHom := s16t3_commSub_map_conj a
    rw [hLmap, hJ.1] at h1
    exact h1
  · have hnat : SumOfNatShape L J (J ⊓ fixV L) 1 := h.natural_of_mem_irrSet hJ
    have hfixinf : (J ⊓ fixV L).map a.toMonoidHom = J.map a.toMonoidHom ⊓ fixV L := by
      rw [Subgroup.map_inf _ _ _ a.injective, hfixmap]
    have hsum := SumOfNatShape.map_of_mem_normalizer ha hnat
    rw [hfixinf] at hsum
    exact SumOfNatShape.isIrrOn h.quasi hsum

section Fixed

variable (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
  {J₀ : Subgroup W} (hJ₀ : J₀ ∈ irrSet L)

noncomputable def s16t3_phi (a : ↥A) :
    ↥(J₀.map (a : MulAut W).toMonoidHom) ≃* ↥J₀ :=
  Classical.choose (ThreeNat.exists_iso_of_mem_irrSet h h7
    (s16t3_map_mem_irrSet h (h.normal a.2) hJ₀) hJ₀)

theorem s16t3_phi_pres (a : ↥A) :
    s16t3_PreservesFix L (s16t3_phi h h7 hJ₀ a) :=
  (Classical.choose_spec (ThreeNat.exists_iso_of_mem_irrSet h h7
    (s16t3_map_mem_irrSet h (h.normal a.2) hJ₀) hJ₀)).1

theorem s16t3_phi_equiv (a : ↥A) :
    s16t3_IsEquivariant L (s16t3_phi h h7 hJ₀ a) :=
  (Classical.choose_spec (ThreeNat.exists_iso_of_mem_irrSet h h7
    (s16t3_map_mem_irrSet h (h.normal a.2) hJ₀) hJ₀)).2

noncomputable def s16t3_sectionAut (a : ↥A) : MulAut (s16t3_U L J₀) :=
  (s16t3_transport L (fun w => s16t3_mem_map_fixV_iff (L := L) (h.normal a.2) w) J₀).trans
    (s16t3_quotOfEquiv L (s16t3_phi h h7 hJ₀ a) (s16t3_phi_pres h h7 hJ₀ a))

theorem s16t3_sectionAut_mk (a : ↥A) (u : ↥J₀) :
    s16t3_sectionAut h h7 hJ₀ a (QuotientGroup.mk u) =
      QuotientGroup.mk (s16t3_phi h h7 hJ₀ a
        ⟨(a : MulAut W) (u : W), Subgroup.mem_map_of_mem (a : MulAut W).toMonoidHom u.2⟩) := by
  simp only [s16t3_sectionAut, MulEquiv.trans_apply, s16t3_transport_mk, s16t3_quotOfEquiv_mk]

theorem s16t3_sectionAut_one : s16t3_sectionAut h h7 hJ₀ (1 : ↥A) = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [s16t3_sectionAut_mk, MulAut.one_apply]
    have hmap1 : J₀.map (1 : MulAut W).toMonoidHom = J₀ := by
      rw [s16t3_toMonoidHom_one, Subgroup.map_id]
    have hJ1 : J₀.map (1 : MulAut W).toMonoidHom ∈ irrSet L :=
      s16t3_map_mem_irrSet h (h.normal (1 : ↥A).2) hJ₀
    have hrel := s16t3_eq_mod_fixV_of_isEquivariant h hJ1 hJ₀
      (s16t3_phi_pres h h7 hJ₀ 1) (s16t3_phi_equiv h h7 hJ₀ 1)
      (s16t3_subgroupCongr_pres hmap1) (s16t3_subgroupCongr_equiv hmap1)
    have hv := hrel ⟨(1 : MulAut W) u, Subgroup.mem_map_of_mem _ u.2⟩
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [div_eq_mul_inv]
    refine ⟨J₀.mul_mem (s16t3_phi h h7 hJ₀ 1
      ⟨(1 : MulAut W) u, Subgroup.mem_map_of_mem _ u.2⟩).2 (J₀.inv_mem u.2), ?_⟩
    change (((s16t3_phi h h7 hJ₀ 1)
        ⟨(1 : MulAut W) u, Subgroup.mem_map_of_mem _ u.2⟩ : ↥J₀) : W) *
        ((1 : MulAut W) u)⁻¹ ∈ fixV L
    exact hv

theorem s16t3_sectionAut_mul (a b : ↥A) :
    s16t3_sectionAut h h7 hJ₀ (a * b) =
      s16t3_sectionAut h h7 hJ₀ a * s16t3_sectionAut h h7 hJ₀ b := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H u =>
    let bMap : ↥J₀ ≃* ↥(J₀.map (b : MulAut W).toMonoidHom) :=
      Subgroup.equivMapOfInjective J₀ (b : MulAut W).toMonoidHom
        (s16t3_injective_toMonoidHom (b : MulAut W))
    let aMap : ↥J₀ ≃* ↥(J₀.map (a : MulAut W).toMonoidHom) :=
      Subgroup.equivMapOfInjective J₀ (a : MulAut W).toMonoidHom
        (s16t3_injective_toMonoidHom (a : MulAut W))
    let abMap : ↥J₀ ≃* ↥(J₀.map ((a * b : ↥A) : MulAut W).toMonoidHom) :=
      Subgroup.equivMapOfInjective J₀ ((a * b : ↥A) : MulAut W).toMonoidHom
        (s16t3_injective_toMonoidHom ((a * b : ↥A) : MulAut W))
    let G : ↥J₀ ≃* ↥J₀ := abMap.trans (s16t3_phi h h7 hJ₀ (a * b))
    let H : ↥J₀ ≃* ↥J₀ :=
      (bMap.trans (s16t3_phi h h7 hJ₀ b)).trans (aMap.trans (s16t3_phi h h7 hJ₀ a))
    let R : ↥J₀ ≃* ↥J₀ := H.symm.trans G
    have hstableJ₀ : StableUnder L J₀ := hJ₀.2.2.1
    have hstableb : StableUnder L (J₀.map (b : MulAut W).toMonoidHom) :=
      s16t3_stableUnder_map hstableJ₀ (h.normal b.2)
    have hstablea : StableUnder L (J₀.map (a : MulAut W).toMonoidHom) :=
      s16t3_stableUnder_map hstableJ₀ (h.normal a.2)
    have hstableab : StableUnder L (J₀.map ((a * b : ↥A) : MulAut W).toMonoidHom) :=
      s16t3_stableUnder_map hstableJ₀ (h.normal (a * b).2)
    have hZb : s16t3_PreservesFix L bMap :=
      s16t3_equivMapOfInjective_pres (s16t3_mem_map_fixV_iff (h.normal b.2)) J₀
    have hZa : s16t3_PreservesFix L aMap :=
      s16t3_equivMapOfInjective_pres (s16t3_mem_map_fixV_iff (h.normal a.2)) J₀
    have hZab : s16t3_PreservesFix L abMap :=
      s16t3_equivMapOfInjective_pres (s16t3_mem_map_fixV_iff (h.normal (a * b).2)) J₀
    have hZG : s16t3_PreservesFix L G :=
      s16t3_PreservesFix.trans hZab (s16t3_phi_pres h h7 hJ₀ (a * b))
    have hZH : s16t3_PreservesFix L H :=
      s16t3_PreservesFix.trans
        (s16t3_PreservesFix.trans hZb (s16t3_phi_pres h h7 hJ₀ b))
        (s16t3_PreservesFix.trans hZa (s16t3_phi_pres h h7 hJ₀ a))
    have hZR : s16t3_PreservesFix L R :=
      s16t3_PreservesFix.trans (s16t3_PreservesFix.symm hZH) hZG
    have hSb : s16t3_IsSemiConj L (b : MulAut W) bMap :=
      s16t3_equivMapOfInjective_semiConj (b : MulAut W) J₀
    have hSa : s16t3_IsSemiConj L (a : MulAut W) aMap :=
      s16t3_equivMapOfInjective_semiConj (a : MulAut W) J₀
    have hSab : s16t3_IsSemiConj L ((a * b : ↥A) : MulAut W) abMap :=
      s16t3_equivMapOfInjective_semiConj ((a * b : ↥A) : MulAut W) J₀
    have hSφb : s16t3_IsSemiConj L 1 (s16t3_phi h h7 hJ₀ b) := by
      simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using s16t3_phi_equiv h h7 hJ₀ b
    have hSφa : s16t3_IsSemiConj L 1 (s16t3_phi h h7 hJ₀ a) := by
      simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using s16t3_phi_equiv h h7 hJ₀ a
    have hSφab : s16t3_IsSemiConj L 1 (s16t3_phi h h7 hJ₀ (a * b)) := by
      simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using s16t3_phi_equiv h h7 hJ₀ (a * b)
    have hZHb : s16t3_PreservesFix L (bMap.trans (s16t3_phi h h7 hJ₀ b)) :=
      s16t3_PreservesFix.trans hZb (s16t3_phi_pres h h7 hJ₀ b)
    have hZHa : s16t3_PreservesFix L (aMap.trans (s16t3_phi h h7 hJ₀ a)) :=
      s16t3_PreservesFix.trans hZa (s16t3_phi_pres h h7 hJ₀ a)
    have hH_semi : s16t3_IsSemiConj L ((a * b : ↥A) : MulAut W) H := by
      have h1 : s16t3_IsSemiConj L (1 * (b : MulAut W))
          (bMap.trans (s16t3_phi h h7 hJ₀ b)) :=
        s16t3_IsSemiConj.trans (h.normal b.2) (one_mem _) hstableb hZb
          (s16t3_phi_pres h h7 hJ₀ b) hSb hSφb
      have h2 : s16t3_IsSemiConj L (1 * (a : MulAut W))
          (aMap.trans (s16t3_phi h h7 hJ₀ a)) :=
        s16t3_IsSemiConj.trans (h.normal a.2) (one_mem _) hstablea hZa
          (s16t3_phi_pres h h7 hJ₀ a) hSa hSφa
      have h3 : s16t3_IsSemiConj L ((a : MulAut W) * (b : MulAut W))
          ((bMap.trans (s16t3_phi h h7 hJ₀ b)).trans
            (aMap.trans (s16t3_phi h h7 hJ₀ a))) :=
        s16t3_IsSemiConj.trans (h.normal b.2) (h.normal a.2) hstableJ₀ hZHb hZHa h1 h2
      simpa [H, Subgroup.coe_mul] using h3
    have hG_semi : s16t3_IsSemiConj L ((a * b : ↥A) : MulAut W) G := by
      have h1 : s16t3_IsSemiConj L (1 * ((a * b : ↥A) : MulAut W))
          (abMap.trans (s16t3_phi h h7 hJ₀ (a * b))) :=
        s16t3_IsSemiConj.trans (h.normal (a * b).2) (one_mem _) hstableab hZab
          (s16t3_phi_pres h h7 hJ₀ (a * b)) hSab hSφab
      simpa [G] using h1
    have hHinv_semi : s16t3_IsSemiConj L (((a * b : ↥A) : MulAut W))⁻¹ H.symm :=
      s16t3_IsSemiConj.symm (h.normal (a * b).2) hstableJ₀ hZH hH_semi
    have hR_semi : s16t3_IsSemiConj L 1 R := by
      have h1 := s16t3_IsSemiConj.trans (L := L)
        (α := (((a * b : ↥A) : MulAut W))⁻¹) (β := ((a * b : ↥A) : MulAut W))
        (φ := H.symm) (ψ := G)
        (Subgroup.inv_mem _ (h.normal (a * b).2)) (h.normal (a * b).2)
        hstableJ₀ (s16t3_PreservesFix.symm hZH) hZG hHinv_semi hG_semi
      simpa [R, mul_inv_cancel] using h1
    have hR : s16t3_IsEquivariant L R := by
      simpa [s16t3_IsEquivariant, s16t3_IsSemiConj] using hR_semi
    have hZR' : ∀ v : ↥J₀, ((R v : ↥J₀) : W) ∈ J₀ ⊓ fixV L ↔ (v : W) ∈ J₀ ⊓ fixV L := by
      intro v
      rw [Subgroup.mem_inf, Subgroup.mem_inf, and_iff_right (R v).2, and_iff_right v.2]
      exact hZR v
    have hφR : ∀ l ∈ L, ∀ v : ↥J₀, ∀ hv : l (v : W) ∈ J₀,
        ((R ⟨l (v : W), hv⟩ : ↥J₀) : W) * (l ((R v : ↥J₀) : W))⁻¹ ∈ J₀ ⊓ fixV L := by
      intro l hl v hv
      refine ⟨J₀.mul_mem (R _).2 (J₀.inv_mem ?_), hR l hl v hv⟩
      exact hstableJ₀ l hl (R v) (R v).2
    have hconcl := SumOfNatShape.eq_of_equivariant h.quasi (h.natural_of_mem_irrSet hJ₀) R
      hZR' hφR
    rw [s16t3_sectionAut_mk, MulAut.mul_apply, s16t3_sectionAut_mk, s16t3_sectionAut_mk]
    change QuotientGroup.mk (G u) = QuotientGroup.mk (H u)
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [div_eq_mul_inv]
    refine ⟨J₀.mul_mem (G u).2 (J₀.inv_mem (H u).2), ?_⟩
    have hmem := (Subgroup.mem_inf.mp (hconcl (H u))).2
    have hRH : R (H u) = G u := by
      simp only [R, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hRH] at hmem
    simpa using hmem

noncomputable def s16t3_sectionHom : ↥A →* MulAut (s16t3_U L J₀) where
  toFun := s16t3_sectionAut h h7 hJ₀
  map_one' := s16t3_sectionAut_one h h7 hJ₀
  map_mul' := s16t3_sectionAut_mul h h7 hJ₀

theorem s16t3_sectionHom_mk (a : ↥A) (u : ↥J₀) :
    s16t3_sectionHom h h7 hJ₀ a (QuotientGroup.mk u) =
      QuotientGroup.mk (s16t3_phi h h7 hJ₀ a
        ⟨(a : MulAut W) (u : W), Subgroup.mem_map_of_mem (a : MulAut W).toMonoidHom u.2⟩) :=
  s16t3_sectionAut_mk h h7 hJ₀ a u

theorem s16t3_sectionHom_l {l : ↥A} (hl : (l : MulAut W) ∈ L) (u : ↥J₀)
    (hu : (l : MulAut W) (u : W) ∈ J₀) :
    s16t3_sectionHom h h7 hJ₀ l (QuotientGroup.mk u) =
      QuotientGroup.mk (⟨(l : MulAut W) (u : W), hu⟩ : ↥J₀) := by
  have hstableJ₀ : StableUnder L J₀ := hJ₀.2.2.1
  have hmapl : J₀.map (l : MulAut W).toMonoidHom = J₀ := by
    apply le_antisymm
    · rintro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact hstableJ₀ _ hl y hy
    · intro x hx
      exact Subgroup.mem_map.mpr
        ⟨(l : MulAut W)⁻¹ x, hstableJ₀ _ (L.inv_mem hl) x hx, by simp⟩
  have hJ1 : J₀.map (l : MulAut W).toMonoidHom ∈ irrSet L :=
    s16t3_map_mem_irrSet h (h.normal l.2) hJ₀
  have hrel := s16t3_eq_mod_fixV_of_isEquivariant h hJ1 hJ₀
    (s16t3_phi_pres h h7 hJ₀ l) (s16t3_phi_equiv h h7 hJ₀ l)
    (s16t3_subgroupCongr_pres hmapl) (s16t3_subgroupCongr_equiv hmapl)
  rw [s16t3_sectionHom_mk]
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [div_eq_mul_inv]
  refine ⟨J₀.mul_mem (s16t3_phi h h7 hJ₀ l
    ⟨(l : MulAut W) (u : W), Subgroup.mem_map_of_mem _ u.2⟩).2 (J₀.inv_mem hu), ?_⟩
  have hv := hrel ⟨(l : MulAut W) (u : W), Subgroup.mem_map_of_mem _ u.2⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.subgroupCongr_apply] using hv

theorem s16t3_sectionHom_ker :
    (s16t3_sectionHom h h7 hJ₀).ker = (s1t3KBar A L).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, s1t3KBar, Subgroup.mem_inf]
  constructor
  · intro ha
    refine ⟨a.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    let lA : ↥A := ⟨l, h.le hl⟩
    let c : ↥A := a * lA * a⁻¹
    have hcmem : (c : MulAut W) ∈ L := by
      change (a : MulAut W) * l * (a : MulAut W)⁻¹ ∈ L
      exact conj_mem_of_mem_normalizer (h.normal a.2) hl
    have hc_eq : s16t3_sectionHom h h7 hJ₀ c = s16t3_sectionHom h h7 hJ₀ lA := by
      change s16t3_sectionHom h h7 hJ₀ (a * lA * a⁻¹) = s16t3_sectionHom h h7 hJ₀ lA
      simp only [map_mul, map_inv, ha, one_mul, inv_one, mul_one]
    let k : ↥A := c⁻¹ * lA
    have hkmem : (k : MulAut W) ∈ L := by
      change ((a : MulAut W) * l * (a : MulAut W)⁻¹)⁻¹ * l ∈ L
      exact L.mul_mem (L.inv_mem hcmem) hl
    have hk1 : s16t3_sectionHom h h7 hJ₀ k = 1 := by
      change s16t3_sectionHom h h7 hJ₀ (c⁻¹ * lA) = 1
      rw [map_mul, map_inv, hc_eq, inv_mul_cancel]
    have hktriv : ∀ u ∈ J₀, (k : MulAut W) u * u⁻¹ ∈ J₀ ⊓ fixV L := by
      intro u hu
      have hku : (k : MulAut W) u ∈ J₀ := hJ₀.2.2.1 _ hkmem u hu
      have h1 := s16t3_sectionHom_l h h7 hJ₀ (l := k) hkmem ⟨u, hu⟩ hku
      have h2 : (QuotientGroup.mk (⟨(k : MulAut W) u, hku⟩ : ↥J₀) : s16t3_U L J₀) =
          (QuotientGroup.mk (⟨u, hu⟩ : ↥J₀) : s16t3_U L J₀) := by
        rw [← h1, hk1, MulAut.one_apply]
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        div_eq_mul_inv] at h2
      exact h2
    have hk_eq : (k : MulAut W) = 1 :=
      SumOfNatShape.eq_one_of_trivial h.quasi (h.natural_of_mem_irrSet hJ₀) hkmem hktriv
    have hcl : (c : MulAut W) = l := by
      have h : (c : MulAut W)⁻¹ * l = 1 := by
        have := hk_eq
        change (c : MulAut W)⁻¹ * l = 1 at this
        exact this
      exact inv_mul_eq_one.mp h
    have hgoal : l * (a : MulAut W) = (a : MulAut W) * l := by
      have h := hcl
      change (a : MulAut W) * l * (a : MulAut W)⁻¹ = l at h
      have h2 := congrArg (fun m : MulAut W => m * (a : MulAut W)) h
      simpa [mul_assoc] using h2.symm
    exact hgoal
  · intro ha
    obtain ⟨_, ha2⟩ := ha
    change s16t3_sectionAut h h7 hJ₀ a = 1
    ext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [s16t3_sectionAut_mk, MulAut.one_apply]
      let aMap : ↥J₀ ≃* ↥(J₀.map (a : MulAut W).toMonoidHom) :=
        Subgroup.equivMapOfInjective J₀ (a : MulAut W).toMonoidHom
          (s16t3_injective_toMonoidHom (a : MulAut W))
      have hstableJ₀ : StableUnder L J₀ := hJ₀.2.2.1
      have hZaMap : s16t3_PreservesFix L aMap :=
        s16t3_equivMapOfInjective_pres (s16t3_mem_map_fixV_iff (h.normal a.2)) J₀
      have hEaMap : s16t3_IsEquivariant L aMap := by
        intro l hl v hv
        change (a : MulAut W) (l (v : W)) * (l ((a : MulAut W) (v : W)))⁻¹ ∈ fixV L
        have hcomm := Subgroup.mem_centralizer_iff.mp ha2 l hl
        have hthis : (a : MulAut W) (l (v : W)) = l ((a : MulAut W) (v : W)) := by
          have := congrArg (fun m : MulAut W => m (v : W)) hcomm
          simpa [MulAut.mul_apply] using this.symm
        rw [hthis, mul_inv_cancel]
        exact Subgroup.one_mem _
      have hJ1 : J₀.map (a : MulAut W).toMonoidHom ∈ irrSet L :=
        s16t3_map_mem_irrSet h (h.normal a.2) hJ₀
      have hrel := s16t3_eq_mod_fixV_of_isEquivariant h hJ1 hJ₀
        (s16t3_phi_pres h h7 hJ₀ a) (s16t3_phi_equiv h h7 hJ₀ a)
        (s16t3_PreservesFix.symm hZaMap)
        (s16t3_IsEquivariant.symm hstableJ₀ hZaMap hEaMap)
      have hv := hrel (aMap u)
      have hsymm : aMap.symm (aMap u) = u := MulEquiv.symm_apply_apply aMap u
      rw [hsymm] at hv
      rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      rw [div_eq_mul_inv]
      refine ⟨J₀.mul_mem (s16t3_phi h h7 hJ₀ a
        ⟨(a : MulAut W) (u : W), Subgroup.mem_map_of_mem (a : MulAut W).toMonoidHom u.2⟩).2
        (J₀.inv_mem u.2), ?_⟩
      have hval : aMap u = ⟨(a : MulAut W) (u : W),
          Subgroup.mem_map_of_mem (a : MulAut W).toMonoidHom u.2⟩ := Subtype.ext rfl
      rw [hval] at hv
      exact hv

theorem s16t3_exists_section_hom_of_mem (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) {J₀ : Subgroup W} (hJ₀ : J₀ ∈ irrSet L) :
    ∃ g : ↥A →* MulAut (s16t3_U L J₀),
      g.ker = (s1t3KBar A L).subgroupOf A ∧
      ∀ l : ↥A, (l : MulAut W) ∈ L → ∀ u : ↥J₀, ∀ hu : (l : MulAut W) (u : W) ∈ J₀,
        g l (QuotientGroup.mk u) = QuotientGroup.mk ⟨(l : MulAut W) (u : W), hu⟩ :=
  ⟨s16t3_sectionHom h h7 hJ₀, s16t3_sectionHom_ker h h7 hJ₀,
    fun l hl u hu => s16t3_sectionHom_l h h7 hJ₀ hl u hu⟩

end Fixed

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
