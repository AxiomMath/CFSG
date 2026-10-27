module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

abbrev Sp4 (F : Type) [Field F] : Type := ↥(StatedSp 2 F)

abbrev V4 (F : Type) : Type := Fin 2 ⊕ Fin 2 → F

abbrev mat (g : Sp4 F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

theorem mat_mul (g h : Sp4 F) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : Sp4 F) = 1 := rfl

theorem mat_mul_mulVec (g h : Sp4 F) (v : V4 F) :
    mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
  rw [mat_mul, mulVec_mulVec]

theorem mat_inv_mulVec (g : Sp4 F) (v : V4 F) : mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
  rw [← mat_mul_mulVec, inv_mul_cancel, mat_one, one_mulVec]

theorem mat_mulVec_inv (g : Sp4 F) (v : V4 F) : mat g *ᵥ (mat g⁻¹ *ᵥ v) = v := by
  rw [← mat_mul_mulVec, mul_inv_cancel, mat_one, one_mulVec]

theorem mat_injective : Function.Injective (mat (F := F)) := fun _ _ h =>
  SymplecticTorusWeyl.statedSp_ext h

theorem mulVec_mat_injective (g : Sp4 F) : Function.Injective (mat g *ᵥ · : V4 F → V4 F) :=
  fun u v h => by rw [← mat_inv_mulVec g u, ← mat_inv_mulVec g v]; exact congrArg _ h

theorem ext_mulVec {g h : Sp4 F} (H : ∀ v : V4 F, mat g *ᵥ v = mat h *ᵥ v) : g = h :=
  mat_injective (Matrix.ext_of_mulVec_single fun _ => H _)

abbrev form (F : Type) [Field F] : LinearMap.BilinForm F (V4 F) := pairedSympForm F 2

theorem form_mat (g : Sp4 F) (u v : V4 F) : form F (mat g *ᵥ u) (mat g *ᵥ v) = form F u v :=
  SymplecticHigher.pairedSympForm_mulVec g u v

theorem form_self (u : V4 F) : form F u u = 0 := pairedSympForm_self u

theorem form_swap (u v : V4 F) : form F v u = -form F u v :=
  (LinearMap.BilinForm.IsAlt.neg_eq SymplecticFlag.pairedSympForm_isAlt u v).symm

theorem form_apply (u v : V4 F) :
    form F u v = u (.inl 0) * v (.inr 0) + u (.inl 1) * v (.inr 1) -
      (u (.inr 0) * v (.inl 0) + u (.inr 1) * v (.inl 1)) := by
  rw [pairedSympForm_apply]
  simp [dotProduct, Fin.sum_univ_two]

theorem form_nondegenerate : (form F).Nondegenerate := SymplecticFlag.pairedSympForm_nondegenerate

abbrev perp (W : Submodule F (V4 F)) : Submodule F (V4 F) := (form F).orthogonal W

theorem mem_perp {W : Submodule F (V4 F)} {v : V4 F} : v ∈ perp W ↔ ∀ w ∈ W, form F w v = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem perp_antitone {W W' : Submodule F (V4 F)} (h : W ≤ W') : perp W' ≤ perp W :=
  fun _ hv => mem_perp.2 fun w hw => mem_perp.1 hv w (h hw)

theorem finrank_perp (W : Submodule F (V4 F)) :
    Module.finrank F (perp W) + Module.finrank F W = 4 := by
  have h4 : Module.finrank F (V4 F) = 4 := by simp
  have h : Module.finrank F (perp W) = 4 - Module.finrank F W := by
    rw [← h4]
    exact LinearMap.BilinForm.finrank_orthogonal form_nondegenerate W
  have hle := Submodule.finrank_le W
  omega

theorem perp_perp (W : Submodule F (V4 F)) : perp (perp W) = W := by
  refine (Submodule.eq_of_le_of_finrank_eq (fun w hw => mem_perp.2 fun v hv => ?_) ?_).symm
  · rw [form_swap, mem_perp.1 hv w hw, neg_zero]
  · have h1 := finrank_perp W
    have h2 := finrank_perp (perp W)
    omega

@[expose] def IsPoint (p : Submodule F (V4 F)) : Prop := Module.finrank F p = 1

@[expose] def IsLine (l : Submodule F (V4 F)) : Prop :=
  Module.finrank F l = 2 ∧ IsTotallyIsotropic (form F) l

theorem IsLine.le_perp {l : Submodule F (V4 F)} (hl : IsLine l) : l ≤ perp l :=
  fun v hv => mem_perp.2 fun w hw => hl.2 w hw v hv

theorem IsLine.perp_eq {l : Submodule F (V4 F)} (hl : IsLine l) : perp l = l := by
  refine (Submodule.eq_of_le_of_finrank_eq hl.le_perp ?_).symm
  have h := finrank_perp l
  rw [hl.1] at h ⊢
  omega

@[expose] def fixSp (A : Subgroup (Sp4 F)) : Submodule F (V4 F) where
  carrier := {v | ∀ a ∈ A, mat a *ᵥ v = v}
  add_mem' {u v} hu hv a ha := by rw [mulVec_add, hu a ha, hv a ha]
  zero_mem' a _ := mulVec_zero _
  smul_mem' c v hv a ha := by rw [mulVec_smul, hv a ha]

theorem mem_fixSp {A : Subgroup (Sp4 F)} {v : V4 F} : v ∈ fixSp A ↔ ∀ a ∈ A, mat a *ᵥ v = v :=
  Iff.rfl

theorem fixSp_antitone {A A' : Subgroup (Sp4 F)} (h : A ≤ A') : fixSp A' ≤ fixSp A :=
  fun _ hv a ha => hv a (h ha)

@[expose] def commSp (A : Subgroup (Sp4 F)) : Submodule F (V4 F) :=
  Submodule.span F {w | ∃ a ∈ A, ∃ v : V4 F, w = mat a *ᵥ v - v}

theorem sub_mem_commSp {A : Subgroup (Sp4 F)} {a : Sp4 F} (ha : a ∈ A) (v : V4 F) :
    mat a *ᵥ v - v ∈ commSp A :=
  Submodule.subset_span ⟨a, ha, v, rfl⟩

theorem commSp_le_iff {A : Subgroup (Sp4 F)} {W : Submodule F (V4 F)} :
    commSp A ≤ W ↔ ∀ a ∈ A, ∀ v : V4 F, mat a *ᵥ v - v ∈ W := by
  refine ⟨fun h a ha v => h (sub_mem_commSp ha v), fun h => Submodule.span_le.2 ?_⟩
  rintro _ ⟨a, ha, v, rfl⟩
  exact h a ha v

theorem commSp_mono {A A' : Subgroup (Sp4 F)} (h : A ≤ A') : commSp A ≤ commSp A' :=
  commSp_le_iff.2 fun _ ha v => sub_mem_commSp (h ha) v

@[expose] def fixer (W : Submodule F (V4 F)) : Subgroup (Sp4 F) where
  carrier := {g | ∀ v ∈ W, mat g *ᵥ v = v}
  one_mem' v _ := by rw [mat_one, one_mulVec]
  mul_mem' {g h} hg hh v hv := by rw [mat_mul_mulVec, hh v hv, hg v hv]
  inv_mem' {g} hg v hv := by
    conv_lhs => rw [← hg v hv]
    exact mat_inv_mulVec g v

theorem mem_fixer {W : Submodule F (V4 F)} {g : Sp4 F} : g ∈ fixer W ↔ ∀ v ∈ W, mat g *ᵥ v = v :=
  Iff.rfl

theorem le_fixer_iff {A : Subgroup (Sp4 F)} {W : Submodule F (V4 F)} :
    A ≤ fixer W ↔ W ≤ fixSp A :=
  ⟨fun h _ hv _ ha => h ha _ hv, fun h _ ha _ hv => h hv _ ha⟩

theorem fixer_antitone {W W' : Submodule F (V4 F)} (h : W ≤ W') : fixer W' ≤ fixer W :=
  fun _ hg v hv => hg v (h hv)

abbrev stab (W : Submodule F (V4 F)) : Subgroup (Sp4 F) := stabilizer 2 F W

theorem mem_stab_iff {W : Submodule F (V4 F)} {g : Sp4 F} :
    g ∈ stab W ↔ W.map (mulVecLin (mat g)) = W :=
  Iff.rfl

theorem mem_stab_of_le {W : Submodule F (V4 F)} {g : Sp4 F}
    (h : ∀ v ∈ W, mat g *ᵥ v ∈ W) : g ∈ stab W := by
  have hle : W.map (mulVecLin (mat g)) ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact (Submodule.equivMapOfInjective (mulVecLin (mat g)) (mulVec_mat_injective g)
    W).finrank_eq.symm

theorem mulVec_mem_of_mem_stab {W : Submodule F (V4 F)} {g : Sp4 F} (hg : g ∈ stab W)
    {v : V4 F} (hv : v ∈ W) : mat g *ᵥ v ∈ W := by
  rw [← mem_stab_iff.1 hg]
  exact ⟨v, hv, rfl⟩

theorem fixer_le_stab (W : Submodule F (V4 F)) : fixer W ≤ stab W :=
  fun g hg => mem_stab_of_le fun v hv => by rw [hg v hv]; exact hv

theorem stab_le_stab_perp (W : Submodule F (V4 F)) : stab W ≤ stab (perp W) := by
  intro g hg
  refine mem_stab_of_le fun v hv => mem_perp.2 fun w hw => ?_
  have hw' : mat g⁻¹ *ᵥ w ∈ W := mulVec_mem_of_mem_stab (inv_mem hg) hw
  rw [← mat_mulVec_inv g w, form_mat]
  exact mem_perp.1 hv _ hw'

theorem stab_perp (W : Submodule F (V4 F)) : stab (perp W) = stab W := by
  refine le_antisymm ?_ (stab_le_stab_perp W)
  have h := stab_le_stab_perp (perp W)
  rwa [perp_perp] at h

@[expose] def qPoint (p : Submodule F (V4 F)) : Subgroup (Sp4 F) where
  carrier := {g | (∀ v ∈ p, mat g *ᵥ v = v) ∧ ∀ v ∈ perp p, mat g *ᵥ v - v ∈ p}
  one_mem' := ⟨fun v _ => by rw [mat_one, one_mulVec], fun v _ => by
    rw [mat_one, one_mulVec, sub_self]; exact zero_mem _⟩
  mul_mem' {g h} hg hh := by
    refine ⟨fun v hv => by rw [mat_mul_mulVec, hh.1 v hv, hg.1 v hv], fun v hv => ?_⟩
    have h1 := hh.2 v hv
    have h2 : mat g *ᵥ (mat h *ᵥ v - v) = mat h *ᵥ v - v := hg.1 _ h1
    have h3 := hg.2 v hv
    rw [mulVec_sub] at h2
    have : mat (g * h) *ᵥ v - v = (mat h *ᵥ v - v) + (mat g *ᵥ v - v) := by
      rw [mat_mul_mulVec]
      rw [sub_eq_iff_eq_add] at h2
      rw [h2]
      abel
    rw [this]
    exact add_mem h1 h3
  inv_mem' {g} hg := by
    have hfix : ∀ v ∈ p, mat g⁻¹ *ᵥ v = v := fun v hv => by
      conv_lhs => rw [← hg.1 v hv]
      exact mat_inv_mulVec g v
    refine ⟨hfix, fun v hv => ?_⟩
    have hw : mat g⁻¹ *ᵥ v ∈ perp p := mem_perp.2 fun x hx => by
      rw [← form_mat g, hg.1 x hx, mat_mulVec_inv]
      exact mem_perp.1 hv x hx
    have h := hg.2 _ hw
    rw [mat_mulVec_inv] at h
    have : mat g⁻¹ *ᵥ v - v = -(v - mat g⁻¹ *ᵥ v) := by abel
    rw [this]
    exact neg_mem h

theorem mem_qPoint {p : Submodule F (V4 F)} {g : Sp4 F} :
    g ∈ qPoint p ↔ (∀ v ∈ p, mat g *ᵥ v = v) ∧ ∀ v ∈ perp p, mat g *ᵥ v - v ∈ p :=
  Iff.rfl

abbrev qLine (l : Submodule F (V4 F)) : Subgroup (Sp4 F) := fixer l

abbrev xPoint (p : Submodule F (V4 F)) : Subgroup (Sp4 F) := fixer (perp p)

abbrev pt₀ (F : Type) [Field F] : Submodule F (V4 F) := flag 2 F 1

abbrev ln₀ (F : Type) [Field F] : Submodule F (V4 F) := flag 2 F 2

abbrev sylS (F : Type) [Field F] : Subgroup (Sp4 F) := unipotent 2 F

abbrev borel (F : Type) [Field F] : Subgroup (Sp4 F) := borelSubgroup 2 F

abbrev P₁ (F : Type) [Field F] : Subgroup (Sp4 F) := stab (ln₀ F)

abbrev P₂ (F : Type) [Field F] : Subgroup (Sp4 F) := stab (pt₀ F)

abbrev Q₁ (F : Type) [Field F] : Subgroup (Sp4 F) := qLine (ln₀ F)

abbrev Q₂ (F : Type) [Field F] : Subgroup (Sp4 F) := qPoint (pt₀ F)

abbrev X₂ (F : Type) [Field F] : Subgroup (Sp4 F) := xPoint (pt₀ F)

theorem mem_pt₀ {v : V4 F} :
    v ∈ pt₀ F ↔ v (.inl 1) = 0 ∧ v (.inr 0) = 0 ∧ v (.inr 1) = 0 := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2 1 (by simp), h1 0, h1 1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact h2
      · exact h3
    · fin_cases j
      · simp at hj
      · exact h1

theorem mem_ln₀ {v : V4 F} : v ∈ ln₀ F ↔ v (.inr 0) = 0 ∧ v (.inr 1) = 0 := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0, h1 1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact h1
      · exact h2
    · have := j.2
      omega

theorem pt₀_eq_isoFlag : pt₀ F = isoFlag 2 F 1 :=
  Submodule.ext fun _ => mem_flag_of_le (by norm_num)

theorem mem_perp_pt₀ {v : V4 F} : v ∈ perp (pt₀ F) ↔ v (.inr 0) = 0 := by
  change v ∈ (pairedSympForm F 2).orthogonal (pt₀ F) ↔ _
  rw [pt₀_eq_isoFlag, mem_orthogonal_isoFlag]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h j hj
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    rw [hj0]
    exact h

theorem pt₀_le_ln₀ : pt₀ F ≤ ln₀ F := fun _ hv => by
  obtain ⟨-, h2, h3⟩ := mem_pt₀.1 hv
  exact mem_ln₀.2 ⟨h2, h3⟩

theorem ln₀_le_perp_pt₀ : ln₀ F ≤ perp (pt₀ F) := fun _ hv => mem_perp_pt₀.2 (mem_ln₀.1 hv).1

theorem sub_mem_perp_of_mem_fixer {W : Submodule F (V4 F)} {g : Sp4 F} (hg : g ∈ fixer W)
    (v : V4 F) : mat g *ᵥ v - v ∈ perp W :=
  mem_perp.2 fun w hw => by
    rw [map_sub, ← form_mat g w v, hg w hw, sub_self]

theorem sub_mem_of_mem_fixer_perp {W : Submodule F (V4 F)} {g : Sp4 F} (hg : g ∈ fixer (perp W))
    (v : V4 F) : mat g *ᵥ v - v ∈ W := by
  rw [← perp_perp W]
  exact sub_mem_perp_of_mem_fixer hg v

theorem commSp_fixer_perp_le (W : Submodule F (V4 F)) : commSp (fixer (perp W)) ≤ W :=
  commSp_le_iff.2 fun _ hg v => sub_mem_of_mem_fixer_perp hg v

theorem commSp_qLine_le {l : Submodule F (V4 F)} (hl : IsLine l) : commSp (qLine l) ≤ l := by
  refine commSp_le_iff.2 fun _ hg v => ?_
  rw [← hl.perp_eq]
  exact sub_mem_perp_of_mem_fixer hg v

theorem qPoint_le_fixer (p : Submodule F (V4 F)) : qPoint p ≤ fixer p := fun _ hg => hg.1

theorem mem_map_conj {A : Subgroup (Sp4 F)} {g h : Sp4 F} :
    h ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * h * g ∈ A := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_map_mulVecLin {W : Submodule F (V4 F)} {g : Sp4 F} {v : V4 F} :
    v ∈ W.map (mulVecLin (mat g)) ↔ mat g⁻¹ *ᵥ v ∈ W := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mulVecLin_apply, mat_inv_mulVec]
    exact hw
  · intro hv
    exact ⟨_, hv, by rw [mulVecLin_apply, mat_mulVec_inv]⟩

theorem mulVec_mem_map {W : Submodule F (V4 F)} (g : Sp4 F) {v : V4 F} (hv : v ∈ W) :
    mat g *ᵥ v ∈ W.map (mulVecLin (mat g)) :=
  ⟨v, hv, rfl⟩

theorem perp_map (g : Sp4 F) (W : Submodule F (V4 F)) :
    perp (W.map (mulVecLin (mat g))) = (perp W).map (mulVecLin (mat g)) := by
  ext v
  rw [mem_map_mulVecLin, mem_perp, mem_perp]
  constructor
  · intro h w hw
    rw [← form_mat g, mat_mulVec_inv]
    exact h _ (mulVec_mem_map g hw)
  · intro h w hw
    rw [mem_map_mulVecLin] at hw
    have := h _ hw
    rwa [← form_mat g, mat_mulVec_inv, mat_mulVec_inv] at this

theorem fixer_map_conj (g : Sp4 F) (W : Submodule F (V4 F)) :
    (fixer W).map (MulAut.conj g).toMonoidHom = fixer (W.map (mulVecLin (mat g))) := by
  ext h
  rw [mem_map_conj, mem_fixer, mem_fixer]
  constructor
  · intro H v hv
    rw [mem_map_mulVecLin] at hv
    have := H _ hv
    rw [mat_mul_mulVec, mat_mul_mulVec, mat_mulVec_inv] at this
    exact mulVec_mat_injective g⁻¹ this
  · intro H v hv
    rw [mat_mul_mulVec, mat_mul_mulVec, H _ (mulVec_mem_map g hv), mat_inv_mulVec]

theorem qPoint_map_conj (g : Sp4 F) (p : Submodule F (V4 F)) :
    (qPoint p).map (MulAut.conj g).toMonoidHom = qPoint (p.map (mulVecLin (mat g))) := by
  ext h
  rw [mem_map_conj, mem_qPoint, mem_qPoint, perp_map]
  have key : ∀ v, mat (g⁻¹ * h * g) *ᵥ v = mat g⁻¹ *ᵥ (mat h *ᵥ (mat g *ᵥ v)) := fun v => by
    rw [mat_mul_mulVec, mat_mul_mulVec]
  constructor
  · rintro ⟨H1, H2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [mem_map_mulVecLin] at hv
      have := H1 _ hv
      rw [key, mat_mulVec_inv] at this
      rw [← mat_mulVec_inv g (mat h *ᵥ v), this, mat_mulVec_inv]
    · rw [mem_map_mulVecLin] at hv ⊢
      have := H2 _ hv
      rwa [key, mat_mulVec_inv, ← mulVec_sub] at this
  · rintro ⟨H1, H2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [key, H1 _ (mulVec_mem_map g hv), mat_inv_mulVec]
    · have := H2 _ (mulVec_mem_map g hv)
      rw [mem_map_mulVecLin, mulVec_sub, mat_inv_mulVec] at this
      rwa [key]

theorem stab_map_conj (g : Sp4 F) (W : Submodule F (V4 F)) :
    (stab W).map (MulAut.conj g).toMonoidHom = stab (W.map (mulVecLin (mat g))) :=
  (SymplecticHigher.stabilizer_map_spAct g W).symm

theorem fixSp_map_conj (g : Sp4 F) (A : Subgroup (Sp4 F)) :
    fixSp (A.map (MulAut.conj g).toMonoidHom) = (fixSp A).map (mulVecLin (mat g)) := by
  ext v
  rw [mem_map_mulVecLin, mem_fixSp, mem_fixSp]
  constructor
  · intro H a ha
    have := H _ (Subgroup.mem_map_of_mem _ ha)
    change mat (g * a * g⁻¹) *ᵥ v = v at this
    rw [mat_mul_mulVec, mat_mul_mulVec] at this
    calc mat a *ᵥ (mat g⁻¹ *ᵥ v)
        = mat g⁻¹ *ᵥ (mat g *ᵥ (mat a *ᵥ (mat g⁻¹ *ᵥ v))) := (mat_inv_mulVec _ _).symm
      _ = mat g⁻¹ *ᵥ v := by rw [this]
  · intro H b hb
    rw [mem_map_conj] at hb
    have := H _ hb
    rw [mat_mul_mulVec, mat_mul_mulVec, mat_mulVec_inv] at this
    rw [← mat_mulVec_inv g (mat b *ᵥ v), this, mat_mulVec_inv]

theorem map_conj_map_conj {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem mem_normalizer_iff_map_conj {A : Subgroup (Sp4 F)} {g : Sp4 F} :
    g ∈ Subgroup.normalizer (A : Set (Sp4 F)) ↔ A.map (MulAut.conj g).toMonoidHom = A :=
  Subgroup.mem_normalizer_iff_map_conj_eq

theorem stab_le_normalizer_fixer (W : Submodule F (V4 F)) :
    stab W ≤ Subgroup.normalizer (fixer W : Set (Sp4 F)) := fun g hg => by
  rw [mem_normalizer_iff_map_conj, fixer_map_conj, mem_stab_iff.1 hg]

theorem stab_le_normalizer_qPoint (p : Submodule F (V4 F)) :
    stab p ≤ Subgroup.normalizer (qPoint p : Set (Sp4 F)) := fun g hg => by
  rw [mem_normalizer_iff_map_conj, qPoint_map_conj, mem_stab_iff.1 hg]

theorem stab_le_normalizer_xPoint (p : Submodule F (V4 F)) :
    stab p ≤ Subgroup.normalizer (xPoint p : Set (Sp4 F)) := fun _ hg =>
  stab_le_normalizer_fixer (perp p) (stab_le_stab_perp p hg)

theorem mat_ext_mulVec {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : ∀ v : V4 F, M *ᵥ v = N *ᵥ v) : M = N :=
  Matrix.ext_of_mulVec_single fun _ => h _

theorem toBilin'_transpose_mul_mul (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (u v : V4 F) :
    Matrix.toBilin' (Mᵀ * fromBlocks 0 1 (-1) 0 * M) u v = form F (M *ᵥ u) (M *ᵥ v) := by
  change _ = Matrix.toBilin' (fromBlocks 0 1 (-1) 0) (M *ᵥ u) (M *ᵥ v)
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]

theorem mem_statedSp_of_isom {g : GL (Fin 2 ⊕ Fin 2) F}
    (h : ∀ u v : V4 F, form F ((g : Matrix _ _ F) *ᵥ u) ((g : Matrix _ _ F) *ᵥ v) = form F u v) :
    g ∈ StatedSp 2 F := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  refine Matrix.toBilin'.injective (LinearMap.ext fun u => LinearMap.ext fun v => ?_)
  rw [toBilin'_transpose_mul_mul, h]
  rfl

@[expose] def ofMat (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hMN : M * N = 1)
    (hNM : N * M = 1) (hM : ∀ u v : V4 F, form F (M *ᵥ u) (M *ᵥ v) = form F u v) : Sp4 F :=
  ⟨⟨M, N, hMN, hNM⟩, mem_statedSp_of_isom hM⟩

theorem mat_ofMat (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hMN : M * N = 1)
    (hNM : N * M = 1) (hM : ∀ u v : V4 F, form F (M *ᵥ u) (M *ᵥ v) = form F u v) :
    mat (ofMat M N hMN hNM hM) = M :=
  rfl

@[expose] def transvMat (x : V4 F) (c : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  LinearMap.toMatrix' (LinearMap.id + c • (form F x).smulRight x)

theorem transvMat_mulVec (x : V4 F) (c : F) (v : V4 F) :
    transvMat x c *ᵥ v = v + (c * form F x v) • x := by
  rw [transvMat, LinearMap.toMatrix'_mulVec]
  simp [smul_smul]

theorem transvMat_mul (x : V4 F) (c d : F) :
    transvMat x c * transvMat x d = transvMat x (c + d) := by
  refine mat_ext_mulVec fun v => ?_
  rw [← mulVec_mulVec, transvMat_mulVec, transvMat_mulVec, transvMat_mulVec, map_add, map_smul,
    form_self, smul_eq_mul, mul_zero, add_zero, add_assoc, ← add_smul]
  congr 2
  ring

theorem transvMat_zero (x : V4 F) : transvMat x 0 = 1 :=
  mat_ext_mulVec fun v => by rw [transvMat_mulVec, zero_mul, zero_smul, add_zero, one_mulVec]

theorem transvMat_isom (x : V4 F) (c : F) (u v : V4 F) :
    form F (transvMat x c *ᵥ u) (transvMat x c *ᵥ v) = form F u v := by
  rw [transvMat_mulVec, transvMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, form_self,
    form_swap u x]
  ring

@[expose] def transv (x : V4 F) (c : F) : Sp4 F :=
  ofMat (transvMat x c) (transvMat x (-c)) (by rw [transvMat_mul, add_neg_cancel, transvMat_zero])
    (by rw [transvMat_mul, neg_add_cancel, transvMat_zero]) (transvMat_isom x c)

theorem transv_mulVec (x : V4 F) (c : F) (v : V4 F) :
    mat (transv x c) *ᵥ v = v + (c * form F x v) • x :=
  transvMat_mulVec x c v

theorem transv_mul (x : V4 F) (c d : F) : transv x c * transv x d = transv x (c + d) :=
  mat_injective (transvMat_mul x c d)

theorem transv_zero (x : V4 F) : transv x 0 = 1 :=
  mat_injective (transvMat_zero x)

theorem transv_inv (x : V4 F) (c : F) : (transv x c)⁻¹ = transv x (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [transv_mul, add_neg_cancel, transv_zero]

theorem transv_conj (g : Sp4 F) (x : V4 F) (c : F) :
    g * transv x c * g⁻¹ = transv (mat g *ᵥ x) c := by
  refine ext_mulVec fun v => ?_
  rw [mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, mulVec_add, mulVec_smul,
    mat_mulVec_inv, ← form_mat g x, mat_mulVec_inv]

theorem transv_smul_vec (l : F) (x : V4 F) (c : F) : transv (l • x) c = transv x (l ^ 2 * c) := by
  refine ext_mulVec fun v => ?_
  rw [transv_mulVec, transv_mulVec, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 2
  ring

theorem mem_perp_span {x v : V4 F} : v ∈ perp (F ∙ x) ↔ form F x v = 0 := by
  rw [mem_perp]
  refine ⟨fun h => h x (Submodule.mem_span_singleton_self x), fun h w hw => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [map_smul, LinearMap.smul_apply, h, smul_zero]

theorem transv_mem_xPoint (x : V4 F) (c : F) : transv x c ∈ xPoint (F ∙ x) := fun v hv => by
  rw [transv_mulVec, mem_perp_span.1 hv, mul_zero, zero_smul, add_zero]

theorem exists_form_eq_one {x : V4 F} (hx : x ≠ 0) : ∃ y : V4 F, form F x y = 1 := by
  by_contra h
  refine hx (form_nondegenerate.1 x fun n => ?_)
  by_contra hn
  exact h ⟨(form F x n)⁻¹ • n, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hn]⟩

theorem mem_xPoint_span {x : V4 F} (hx : x ≠ 0) {g : Sp4 F} :
    g ∈ xPoint (F ∙ x) ↔ ∃ c : F, transv x c = g := by
  refine ⟨fun hg => ?_, fun ⟨c, hc⟩ => hc ▸ transv_mem_xPoint x c⟩
  obtain ⟨y, hy⟩ := exists_form_eq_one hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (sub_mem_of_mem_fixer_perp hg y)
  refine ⟨c, ext_mulVec fun v => ?_⟩
  have hv' : v - form F x v • y ∈ perp (F ∙ x) := by
    rw [mem_perp_span, map_sub, map_smul, hy, smul_eq_mul, mul_one, sub_self]
  have h1 := hg _ hv'
  rw [mulVec_sub, mulVec_smul] at h1
  have h2 : mat g *ᵥ y = y + c • x := by rw [hc]; abel
  have h3 : mat g *ᵥ v = v - form F x v • y + form F x v • (mat g *ᵥ y) := by
    rw [← h1]
    abel
  rw [transv_mulVec, h3, h2, smul_add, smul_smul]
  abel_nf
  rw [mul_comm]

theorem transv_injective {x : V4 F} (hx : x ≠ 0) : Function.Injective (transv x) := by
  intro c d h
  obtain ⟨y, hy⟩ := exists_form_eq_one hx
  have := congrArg (fun g : Sp4 F => mat g *ᵥ y) h
  simp only [transv_mulVec, hy, mul_one, add_right_inj] at this
  by_contra hcd
  refine hx ?_
  have h' : (c - d) • x = 0 := by rw [sub_smul, this, sub_self]
  exact (smul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hcd)

end CFSG.Quasithin.MS93.MSP
