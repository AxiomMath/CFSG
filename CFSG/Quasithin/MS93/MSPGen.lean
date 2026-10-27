module

public import CFSG.Quasithin.MS93.MSPRad
public import CFSG.Quasithin.Background.JonesParshallSp4
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F]

theorem coe_transv_smul (x : V4 F) (c : F) (v : V4 F) :
    ((transv x c : Sp4 F) : GL (Fin 2 ⊕ Fin 2) F) • v = v + (c * form F x v) • x :=
  transv_mulVec x c v

theorem isTotallyIsotropic_span (x : V4 F) :
    SymplecticFlag.IsTotallyIsotropic (form F) (F ∙ x) := by
  intro u hu v hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hv
  simp [form_self]

theorem exists_map_pt₀_eq {p : Submodule F (V4 F)} (hp : IsPoint p) :
    ∃ g : Sp4 F, (pt₀ F).map (mulVecLin (mat g)) = p := by
  obtain ⟨x, -, rfl⟩ := exists_eq_span_of_isPoint hp
  rw [pt₀_eq_span]
  exact SymplecticFlag.exists_statedSp_map_eq (isTotallyIsotropic_span _)
    (isTotallyIsotropic_span _) (by rw [← pt₀_eq_span]; exact isPoint_pt₀.trans hp.symm)

theorem X₂_map_conj (g : Sp4 F) :
    (X₂ F).map (MulAut.conj g).toMonoidHom = xPoint ((pt₀ F).map (mulVecLin (mat g))) :=
  xPoint_map_conj g _

section CharTwo

variable [CharP F 2]

theorem spX_eq (a b d : F) : (spX a b d : GL Ix F) =
    ((transv (e₁ F) (a - b) * transv (e₂ F) (d - b) * transv (e₁ F + e₂ F) b : Sp4 F) :
      GL (Fin 2 ⊕ Fin 2) F) := by
  refine gl_ext_vec4 fun x y z w => ?_
  rw [spX_smul, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, coe_transv_smul,
    coe_transv_smul, coe_transv_smul]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, vec4] <;> grind

theorem spY_eq (a b d : F) : (spY a b d : GL Ix F) =
    ((transv (f₁ F) (a - b) * transv (f₂ F) (d - b) * transv (f₁ F + f₂ F) b : Sp4 F) :
      GL (Fin 2 ⊕ Fin 2) F) := by
  refine gl_ext_vec4 fun x y z w => ?_
  rw [spY_smul, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, coe_transv_smul,
    coe_transv_smul, coe_transv_smul]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, vec4] <;> grind

theorem spZ_eq (t : F) : (spZ t : GL Ix F) =
    ((transv (e₁ F + f₂ F) t * transv (e₁ F) t * transv (f₂ F) t : Sp4 F) :
      GL (Fin 2 ⊕ Fin 2) F) := by
  refine gl_ext_vec4 fun x y z w => ?_
  rw [spZ_smul, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, coe_transv_smul,
    coe_transv_smul, coe_transv_smul]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, vec4] <;> grind

theorem spZ'_eq (t : F) : (spZ' t : GL Ix F) =
    ((transv (f₁ F + e₂ F) t * transv (f₁ F) t * transv (e₂ F) t : Sp4 F) :
      GL (Fin 2 ⊕ Fin 2) F) := by
  refine gl_ext_vec4 fun x y z w => ?_
  rw [spZ'_smul, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, coe_transv_smul,
    coe_transv_smul, coe_transv_smul]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply, vec4] <;> grind

theorem eq_top_of_eight (G₀ : Subgroup (Sp4 F))
    (h : ∀ x ∈ ({e₁ F, e₂ F, f₁ F, f₂ F, e₁ F + e₂ F, f₁ F + f₂ F, e₁ F + f₂ F, f₁ F + e₂ F} :
      Set (V4 F)), ∀ c : F, transv x c ∈ G₀) : G₀ = ⊤ := by
  have hm : ∀ x ∈ ({e₁ F, e₂ F, f₁ F, f₂ F, e₁ F + e₂ F, f₁ F + f₂ F, e₁ F + f₂ F, f₁ F + e₂ F} :
      Set (V4 F)), ∀ c : F, ((transv x c : Sp4 F) : GL (Fin 2 ⊕ Fin 2) F) ∈
        G₀.map (StatedSp 2 F).subtype := fun x hx c => ⟨_, h x hx c, rfl⟩
  have hgen : rootGens F ⊆ G₀.map (StatedSp 2 F).subtype := by
    rintro g (⟨a, b, d, rfl⟩ | ⟨a, b, d, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩)
    · rw [spX_eq]
      exact ⟨_, mul_mem (mul_mem (h _ (by simp) _) (h _ (by simp) _)) (h _ (by simp) _), rfl⟩
    · rw [spY_eq]
      exact ⟨_, mul_mem (mul_mem (h _ (by simp) _) (h _ (by simp) _)) (h _ (by simp) _), rfl⟩
    · rw [spZ_eq]
      exact ⟨_, mul_mem (mul_mem (h _ (by simp) _) (h _ (by simp) _)) (h _ (by simp) _), rfl⟩
    · rw [spZ'_eq]
      exact ⟨_, mul_mem (mul_mem (h _ (by simp) _) (h _ (by simp) _)) (h _ (by simp) _), rfl⟩
  have hle : StatedSp 2 F ≤ G₀.map (StatedSp 2 F).subtype := by
    intro g hg
    rw [← Explicit.sp4_eq_statedSp, sp4_eq_closure] at hg
    exact (Subgroup.closure_le _).2 hgen hg
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨g', hg', he⟩ := hle g.2
  rwa [show g = g' from Subtype.ext he.symm]

@[expose] def wOne (F : Type) [Field F] : Sp4 F :=
  transv (e₁ F) 1 * transv (f₁ F) 1 * transv (e₁ F) 1

@[expose] def wTwo (F : Type) [Field F] : Sp4 F :=
  transv (e₂ F) 1 * transv (f₂ F) 1 * transv (e₂ F) 1

theorem wOne_mulVec (v : V4 F) :
    mat (wOne F) *ᵥ v = v (.inr 0) • e₁ F + v (.inl 1) • e₂ F + v (.inl 0) • f₁ F +
      v (.inr 1) • f₂ F := by
  rw [wOne, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply]
  grind

theorem wTwo_mulVec (v : V4 F) :
    mat (wTwo F) *ᵥ v = v (.inl 0) • e₁ F + v (.inr 1) • e₂ F + v (.inr 0) • f₁ F +
      v (.inl 1) • f₂ F := by
  rw [wTwo, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply]
  grind

omit [CharP F 2] in
theorem transv_mem_of_conj {G₀ : Subgroup (Sp4 F)} {g : Sp4 F} (hg : g ∈ G₀) {x : V4 F}
    (hx : ∀ c : F, transv x c ∈ G₀) (c : F) : transv (mat g *ᵥ x) c ∈ G₀ := by
  rw [← transv_conj]
  exact mul_mem (mul_mem hg (hx c)) (inv_mem hg)

theorem eq_top_of_five (G₀ : Subgroup (Sp4 F)) (h₁ : ∀ c : F, transv (e₁ F) c ∈ G₀)
    (h₂ : ∀ c : F, transv (e₂ F) c ∈ G₀) (h₃ : ∀ c : F, transv (f₁ F) c ∈ G₀)
    (h₄ : ∀ c : F, transv (f₂ F) c ∈ G₀) (h₅ : ∀ c : F, transv (e₁ F + e₂ F) c ∈ G₀) :
    G₀ = ⊤ := by
  have hw1 : wOne F ∈ G₀ := mul_mem (mul_mem (h₁ 1) (h₃ 1)) (h₁ 1)
  have hw2 : wTwo F ∈ G₀ := mul_mem (mul_mem (h₂ 1) (h₄ 1)) (h₂ 1)
  have h6 : ∀ c : F, transv (f₁ F + e₂ F) c ∈ G₀ := by
    intro c
    have := transv_mem_of_conj hw1 h₅ c
    convert this using 2
    rw [wOne_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have h7 : ∀ c : F, transv (e₁ F + f₂ F) c ∈ G₀ := by
    intro c
    have := transv_mem_of_conj hw2 h₅ c
    convert this using 2
    rw [wTwo_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have h8 : ∀ c : F, transv (f₁ F + f₂ F) c ∈ G₀ := by
    intro c
    have := transv_mem_of_conj hw1 h7 c
    convert this using 2
    rw [wOne_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  refine eq_top_of_eight G₀ fun x hx c => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h₁ c, h₂ c, h₃ c, h₄ c, h₅ c, h8 c, h7 c, h6 c]

theorem exists_mulVec_eq_e₁_add_smul {G₀ : Subgroup (Sp4 F)} (h₂ : ∀ c : F, transv (e₂ F) c ∈ G₀)
    (h₄ : ∀ c : F, transv (f₂ F) c ∈ G₀) {l : F} (hl : l ≠ 0) :
    ∃ g ∈ G₀, mat g *ᵥ (e₁ F + e₂ F) = e₁ F + l • e₂ F := by
  refine ⟨transv (f₂ F) l⁻¹ * transv (e₂ F) (l + 1) * transv (f₂ F) 1,
    mul_mem (mul_mem (h₄ _) (h₂ _)) (h₄ _), ?_⟩
  rw [mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply]
  · grind
  · field_simp
    grind

theorem eq_top_of_four {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (G₀ : Subgroup (Sp4 F))
    (h₂ : ∀ c : F, transv (e₂ F) c ∈ G₀) (h₃ : ∀ c : F, transv (f₁ F) c ∈ G₀)
    (h₄ : ∀ c : F, transv (f₂ F) c ∈ G₀) (h₅ : ∀ c : F, transv (e₁ F + e₂ F) c ∈ G₀) :
    G₀ = ⊤ := by
  obtain ⟨g, hg, hge⟩ := exists_mulVec_eq_e₁_add_smul h₂ h₄ hl0
  have h₆ : ∀ c : F, transv (e₁ F + l • e₂ F) c ∈ G₀ := fun c => by
    rw [← hge]
    exact transv_mem_of_conj hg h₅ c
  have hl1' : 1 + l ≠ 0 := fun h => hl1 (by
    have : l = -1 := by linear_combination h
    rw [this, CharTwo.neg_eq])
  refine eq_top_of_five G₀ (fun s => ?_) h₂ h₃ h₄ h₅
  set α := s / (1 + l) with hα
  have hs : s = α * (1 + l) := by rw [hα, div_mul_cancel₀ _ hl1']
  have key : transv (e₁ F) s = transv (e₁ F + e₂ F) (l * α) * transv (e₁ F + l • e₂ F) α *
      transv (e₂ F) (l * α * (1 + l)) := by
    refine ext_mulVec fun v => ?_
    rw [mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec,
      transv_mulVec, hs]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply] <;> grind
  rw [key]
  exact mul_mem (mul_mem (h₅ _) (h₆ _)) (h₂ _)

end CharTwo

theorem exists_ne_zero_ne_one [Finite F] (hq : 2 < Nat.card F) : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun l _ => by
    by_cases hl : l = 0
    · simp [hl]
    · simp [h l hl]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
  omega

theorem le_iSup_xPoint_of {ι : Type*} {g : ι → Sp4 F} {x : V4 F} (i : ι)
    (hi : (pt₀ F).map (mulVecLin (mat (g i))) = F ∙ x) (c : F) :
    transv x c ∈ ⨆ j, (X₂ F).map (MulAut.conj (g j)).toMonoidHom := by
  refine Subgroup.mem_iSup_of_mem i ?_
  rw [X₂_map_conj, hi]
  exact transv_mem_xPoint x c

theorem e₂_ne_zero : e₂ F ≠ 0 := fun h => by simpa using congrFun h (.inl 1)

theorem f₁_ne_zero : f₁ F ≠ 0 := fun h => by simpa using congrFun h (.inr 0)

theorem f₂_ne_zero : f₂ F ≠ 0 := fun h => by simpa using congrFun h (.inr 1)

theorem e₁_add_e₂_ne_zero : e₁ F + e₂ F ≠ 0 := fun h => by simpa using congrFun h (.inl 0)

section CharTwo

variable [CharP F 2]

theorem exists_four_conj_X₂ [Finite F] (hq : 2 < Nat.card F) :
    ∃ g : Fin 4 → Sp4 F, ⨆ i, (X₂ F).map (MulAut.conj (g i)).toMonoidHom = ⊤ := by
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one hq
  obtain ⟨g₁, h₁⟩ := exists_map_pt₀_eq (isPoint_span (e₂_ne_zero (F := F)))
  obtain ⟨g₂, h₂⟩ := exists_map_pt₀_eq (isPoint_span (f₁_ne_zero (F := F)))
  obtain ⟨g₃, h₃⟩ := exists_map_pt₀_eq (isPoint_span (f₂_ne_zero (F := F)))
  obtain ⟨g₄, h₄⟩ := exists_map_pt₀_eq (isPoint_span (e₁_add_e₂_ne_zero (F := F)))
  refine ⟨![g₁, g₂, g₃, g₄], eq_top_of_four hl0 hl1 _ ?_ ?_ ?_ ?_⟩
  · exact le_iSup_xPoint_of 0 h₁
  · exact le_iSup_xPoint_of 1 h₂
  · exact le_iSup_xPoint_of 2 h₃
  · exact le_iSup_xPoint_of 3 h₄

theorem exists_five_conj_X₂ :
    ∃ g : Fin 5 → Sp4 F, ⨆ i, (X₂ F).map (MulAut.conj (g i)).toMonoidHom = ⊤ := by
  obtain ⟨g₀, h₀⟩ := exists_map_pt₀_eq (isPoint_span (e₁_ne_zero (F := F)))
  obtain ⟨g₁, h₁⟩ := exists_map_pt₀_eq (isPoint_span (e₂_ne_zero (F := F)))
  obtain ⟨g₂, h₂⟩ := exists_map_pt₀_eq (isPoint_span (f₁_ne_zero (F := F)))
  obtain ⟨g₃, h₃⟩ := exists_map_pt₀_eq (isPoint_span (f₂_ne_zero (F := F)))
  obtain ⟨g₄, h₄⟩ := exists_map_pt₀_eq (isPoint_span (e₁_add_e₂_ne_zero (F := F)))
  refine ⟨![g₀, g₁, g₂, g₃, g₄], eq_top_of_five _ ?_ ?_ ?_ ?_ ?_⟩
  · exact le_iSup_xPoint_of 0 h₀
  · exact le_iSup_xPoint_of 1 h₁
  · exact le_iSup_xPoint_of 2 h₂
  · exact le_iSup_xPoint_of 3 h₃
  · exact le_iSup_xPoint_of 4 h₄

omit [CharP F 2] in
theorem exists_xPoint_eq_map_conj {p : Submodule F (V4 F)} (hp : IsPoint p) :
    ∃ h : Sp4 F, xPoint p = (X₂ F).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨h, hh⟩ := exists_map_pt₀_eq hp
  exact ⟨h, by rw [X₂_map_conj, hh]⟩

omit [CharP F 2] in
theorem iSup_map_conj_eq_of {ι : Type*} {p : Submodule F (V4 F)} {h : Sp4 F}
    (hph : xPoint p = (X₂ F).map (MulAut.conj h).toMonoidHom) (g : ι → Sp4 F) :
    ⨆ i, (xPoint p).map (MulAut.conj (g i * h⁻¹)).toMonoidHom =
      ⨆ i, (X₂ F).map (MulAut.conj (g i)).toMonoidHom := by
  congr 1
  funext i
  rw [hph, map_conj_map_conj, inv_mul_cancel_right]

theorem exists_four_conj_xPoint [Finite F] (hq : 2 < Nat.card F) {p : Submodule F (V4 F)}
    (hp : IsPoint p) :
    ∃ g : Fin 4 → Sp4 F, ⨆ i, (xPoint p).map (MulAut.conj (g i)).toMonoidHom = ⊤ := by
  obtain ⟨h, hph⟩ := exists_xPoint_eq_map_conj hp
  obtain ⟨g, hg⟩ := exists_four_conj_X₂ hq
  exact ⟨fun i => g i * h⁻¹, by rw [iSup_map_conj_eq_of hph, hg]⟩

theorem exists_five_conj_xPoint {p : Submodule F (V4 F)} (hp : IsPoint p) :
    ∃ g : Fin 5 → Sp4 F, ⨆ i, (xPoint p).map (MulAut.conj (g i)).toMonoidHom = ⊤ := by
  obtain ⟨h, hph⟩ := exists_xPoint_eq_map_conj hp
  obtain ⟨g, hg⟩ := exists_five_conj_X₂ (F := F)
  exact ⟨fun i => g i * h⁻¹, by rw [iSup_map_conj_eq_of hph, hg]⟩

theorem exists_five_conj_transv_of_card_two (hq : Nat.card F = 2) {p : Submodule F (V4 F)}
    (hp : IsPoint p) {t : Sp4 F} (ht : t ∈ xPoint p) (ht1 : t ≠ 1) :
    ∃ g : Fin 5 → Sp4 F, Subgroup.closure (Set.range fun i => g i * t * (g i)⁻¹) = ⊤ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨g, hg⟩ := exists_five_conj_xPoint hp
  refine ⟨g, eq_top_iff.2 (hg ▸ iSup_le fun i => ?_)⟩
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨x, hx, rfl⟩ := exists_eq_span_of_isPoint hp
  obtain ⟨c, rfl⟩ := (mem_xPoint_span hx).1 hs
  obtain ⟨d, rfl⟩ := (mem_xPoint_span hx).1 ht
  have hd : d ≠ 0 := fun h => ht1 (by rw [h, transv_zero])
  have hcd : c = 0 ∨ c = d := by
    classical
    have := Fintype.ofFinite F
    by_contra hne
    push Not at hne
    have hsub : ({0, c, d} : Finset F).card ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hne.1.symm, hd.symm]),
      Finset.card_pair hne.2, hq] at hsub
    omega
  rcases hcd with rfl | rfl
  · rw [transv_zero, map_one]
    exact one_mem _
  · exact Subgroup.subset_closure ⟨i, rfl⟩

end CharTwo

end CFSG.Quasithin.MS93.MSP
