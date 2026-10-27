module

public import CFSG.Quasithin.MS93.S46I466aQLin

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.Quasithin.MS93 Matrix

variable {F : Type} [Field F]

theorem exists_lnStab_conj_uniTri {b c τ : F} (hbc : b ≠ 0 ∨ c ≠ 0) (hτ : τ ≠ 0) :
    ∃ σ : SL3 F, ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
        σ * uniTri 0 τ 0 * σ⁻¹ = uniTri 0 b c := by
  by_cases hb : b ≠ 0
  · let σ : SL3 F := ⟨!![b / τ, 0, 0; c / τ, τ / b, 0; 0, 0, 1], by
      simp [Matrix.det_fin_three]; field_simp⟩
    refine ⟨σ, rfl, rfl, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change (σ : Matrix (Fin 3) (Fin 3) F) * ((uniTri 0 τ 0 : SL3 F) : Matrix _ _ F) =
      ((uniTri 0 b c : SL3 F) : Matrix _ _ F) * (σ : Matrix (Fin 3) (Fin 3) F)
    rw [coe_uniTri, coe_uniTri]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [σ, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  · push Not at hb
    subst hb
    have hc : c ≠ 0 := hbc.resolve_left (fun h => h rfl)
    let σ : SL3 F := ⟨!![0, -(τ / c), 0; c / τ, 0, 0; 0, 0, 1], by
      simp [Matrix.det_fin_three]; field_simp⟩
    refine ⟨σ, rfl, rfl, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    change (σ : Matrix (Fin 3) (Fin 3) F) * ((uniTri 0 τ 0 : SL3 F) : Matrix _ _ F) =
      ((uniTri 0 0 c : SL3 F) : Matrix _ _ F) * (σ : Matrix (Fin 3) (Fin 3) F)
    rw [coe_uniTri, coe_uniTri]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [σ, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp

@[expose] def rotE12 : SL3 F := ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem rotE12_conj_rootElt01 (c : F) :
    rotE12 * rootElt 0 1 c * rotE12⁻¹ = rootElt 0 2 c := by
  rw [rootElt01_eq_uniTri, rootElt02_eq_uniTri, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change ((rotE12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((uniTri c 0 0 : SL3 F) : Matrix _ _ F) =
    ((uniTri 0 c 0 : SL3 F) : Matrix _ _ F) * ((rotE12 : SL3 F) : Matrix (Fin 3) (Fin 3) F)
  rw [coe_uniTri, coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotE12, Matrix.mul_apply, Fin.sum_univ_three]

theorem fixN_apply_two_of_le {E : Subgroup (SL3 F)}
    (hE : (rootGroup 0 2 : Subgroup (SL3 F)) ≤ E) : ∀ v ∈ fixN E, v 2 = 0 := by
  intro v hv
  have h1 : v ∈ fixN (rootGroup 0 2 : Subgroup (SL3 F)) := fun g hg => hv g (hE hg)
  rw [S46.fixN_rootGroup_zero_two] at h1
  exact h1

theorem exists_coords [Finite F] [CharP F 2] {E : Subgroup (SL3 F)}
    (h2 : ∀ g ∈ E, g * g = 1) (hc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g) (hE : E ≠ ⊥)
    (hcard : Nat.card E = Nat.card F ^ (3 - Module.finrank F (fixN E))) :
    ∃ s : SL3 F, (∀ v ∈ fixN (E.map (MulAut.conj s).toMonoidHom), v 2 = 0) ∧
      (((rootGroup 0 2 : Subgroup (SL3 F)) ≤ E.map (MulAut.conj s).toMonoidHom ∧
          Module.finrank F (commN E) = 1) ∨
        ((∀ t ∈ (rootGroup 0 2 : Subgroup (SL3 F)), ∃ σ : SL3 F,
            ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
            ((σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
            σ * t * σ⁻¹ ∈ E.map (MulAut.conj s).toMonoidHom) ∧
          Module.finrank F (commN E) = 2)) := by
  have hP : IsPGroup 2 E := fun g => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (by simpa using h2 g g.2)⟩
  have hf1 := S46.finrank_fixN_pos hP
  have hfix : fixN E ≠ ⊤ := by
    intro htop
    apply hE
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine eq_one_of_mulVec_eq_self fun x => ?_
    have hx : x ∈ fixN E := by rw [htop]; trivial
    exact hx g hg
  have hf3 : Module.finrank F (fixN E) < 3 := by
    have := Submodule.finrank_lt hfix
    rwa [Module.finrank_fin_fun] at this
  have hd0 : 0 < Module.finrank F (commN E) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact commN_ne_bot hE
  have hdf := finrank_commN_le_finrank_fixN_of_elemAb h2 hc
  by_cases hroot : Module.finrank F (commN E) = 1 ∧ Module.finrank F (fixN E) = 2
  ·
    obtain ⟨hd1, hf2⟩ := hroot
    obtain ⟨⟨r, hr⟩, hr0, hspan⟩ := finrank_eq_one_iff'.mp hd1
    have hr0' : r ≠ 0 := fun h => hr0 (Subtype.ext h)
    have hrP : r ∈ fixN E := commN_le_fixN_of_elemAb h2 hc hr
    have hcomm : ∀ g ∈ E, ∀ v, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ F ∙ r := by
      intro g hg v
      obtain ⟨c, hc'⟩ := hspan ⟨_, sub_mem_commN hg v⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨c, congrArg Subtype.val hc'⟩
    have hcardq : Nat.card E = Nat.card F := by rw [hcard, hf2, pow_one]
    obtain ⟨y, hy⟩ := S46.exists_conj_eq_rootGroup hf2 hrP hr0' (fun g hg p hp => hp g hg)
      hcomm hcardq
    have hX : (rootGroup 0 2 : Subgroup (SL3 F)) ≤
        E.map (MulAut.conj (rotE12 * y)).toMonoidHom := by
      intro t ht
      obtain ⟨τ, rfl⟩ := mem_rootGroup.mp ht
      have h1 : rootElt 0 1 τ ∈ E.map (MulAut.conj y).toMonoidHom :=
        hy ▸ mem_rootGroup.mpr ⟨τ, rfl⟩
      obtain ⟨g, hg, hge⟩ := h1
      refine ⟨g, hg, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hge ⊢
      rw [← rotE12_conj_rootElt01, ← hge]
      group
    exact ⟨rotE12 * y, fixN_apply_two_of_le hX, Or.inl ⟨hX, hd1⟩⟩
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hP
  have h2₁ : ∀ g ∈ E.map (MulAut.conj x).toMonoidHom, g * g = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, h2 g hg, map_one]
  have hfE₁ := finrank_fixN_map_conj x E
  have hdE₁ := finrank_commN_map_conj x E
  rcases le_qPt_or_le_qLn_of_mul_self_eq_one hx h2₁ with hPt | hLn
  ·
    have hcommPt : commN (E.map (MulAut.conj x).toMonoidHom) ≤ pt0 := by
      rw [commN, Submodule.span_le]
      rintro _ ⟨g, hg, v, rfl⟩
      obtain ⟨a, b, rfl⟩ := mem_qPt_iff_uniTri.mp (hPt hg)
      rw [SetLike.mem_coe, mem_pt0, uniTri_mulVec]
      simp
    have hd1 : Module.finrank F (commN E) = 1 := by
      have := Submodule.finrank_mono hcommPt
      rw [finrank_pt0, hdE₁] at this
      omega
    have hf1' : Module.finrank F (fixN E) = 1 := by
      by_contra hne
      exact hroot ⟨hd1, by omega⟩
    have hcard₁ : Nat.card ↥(E.map (MulAut.conj x).toMonoidHom) = Nat.card F ^ 2 := by
      rw [Nat.card_congr (E.equivMapOfInjective _ (MulAut.conj x).injective).toEquiv.symm, hcard,
        hf1']
    have heq : E.map (MulAut.conj x).toMonoidHom = qPt :=
      Subgroup.eq_of_le_of_card_ge hPt (by rw [card_qPt, hcard₁])
    have hX : (rootGroup 0 2 : Subgroup (SL3 F)) ≤ E.map (MulAut.conj x).toMonoidHom :=
      heq ▸ le_sup_right
    exact ⟨x, fixN_apply_two_of_le hX, Or.inl ⟨hX, hd1⟩⟩
  ·
    have hln : ln01 ≤ fixN (E.map (MulAut.conj x).toMonoidHom) := by
      intro v hv g hg
      obtain ⟨b, c, rfl⟩ := mem_qLn_iff_uniTri.mp (hLn hg)
      rw [uniTri_mulVec]
      have hv2 : v 2 = 0 := hv
      ext i
      fin_cases i <;> simp [hv2]
    have hf2 : Module.finrank F (fixN E) = 2 := by
      have := Submodule.finrank_mono hln
      rw [finrank_ln01, hfE₁] at this
      omega
    have hd2 : Module.finrank F (commN E) = 2 := by
      have := S46.finrank_commN_le_two_of_pGroup hP
      by_contra hne
      exact hroot ⟨by omega, hf2⟩
    have hE₁ne : E.map (MulAut.conj x).toMonoidHom ≠ ⊥ := by
      intro h0
      apply hE
      rw [eq_bot_iff]
      intro g hg
      have h1 : (MulAut.conj x).toMonoidHom g ∈ E.map (MulAut.conj x).toMonoidHom := ⟨g, hg, rfl⟩
      rw [h0, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact (MulAut.conj x).injective (h1.trans (map_one _).symm)
    obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE₁ne
    obtain ⟨b, c, hbc⟩ := mem_qLn_iff_uniTri.mp (hLn g.2)
    have hbc0 : b ≠ 0 ∨ c ≠ 0 := by
      by_contra h0
      push Not at h0
      obtain ⟨rfl, rfl⟩ := h0
      apply hg1
      apply Subtype.ext
      rw [← hbc, uniTri_zero]
      rfl
    have hax : ∀ v ∈ fixN (E.map (MulAut.conj x).toMonoidHom), v 2 = 0 := by
      intro v hv
      have h1 := hv _ g.2
      rw [← hbc, uniTri_mulVec] at h1
      have h10 := congrFun h1 0
      have h11 := congrFun h1 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_eq_left, zero_mul,
        add_zero] at h10 h11
      rcases hbc0 with hb | hc'
      · exact (mul_eq_zero.mp (by simpa using h10)).resolve_left hb
      · exact (mul_eq_zero.mp (by simpa using h11)).resolve_left hc'
    refine ⟨x, hax, Or.inr ⟨fun t ht => ?_, hd2⟩⟩
    obtain ⟨τ, rfl⟩ := mem_rootGroup.mp ht
    by_cases hτ : τ = 0
    · refine ⟨1, by simp, by simp, ?_⟩
      rw [hτ, rootElt_zero, mul_one, inv_one, mul_one]
      exact Subgroup.one_mem _
    · obtain ⟨σ, h0, h1, hσ⟩ := exists_lnStab_conj_uniTri hbc0 hτ
      refine ⟨σ, h0, h1, ?_⟩
      rw [rootElt02_eq_uniTri, hσ, hbc]
      exact g.2

end CFSG.Quasithin.MS93.S4A.C441
