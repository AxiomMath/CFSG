module

public import CFSG.Quasithin.MS93.MSPOff

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

section CharTwo

variable [CharP F 2]

theorem transv_mem_of_pair {G₀ : Subgroup (Sp4 F)} {a b : V4 F} (hab : form F a b = 1)
    (ha : ∀ c : F, transv a c ∈ G₀) (hb : ∀ c : F, transv b c ∈ G₀) (α β c : F) :
    transv (α • a + β • b) c ∈ G₀ := by
  have hba : form F b a = 1 := by rw [form_swap, hab, CharTwo.neg_eq]
  by_cases hβ : β = 0
  · subst hβ
    rw [zero_smul, add_zero, transv_smul_vec]
    exact ha _
  · set g := transv a ((α - 1) / β) * transv b β with hg
    have hgm : g ∈ G₀ := mul_mem (ha _) (hb _)
    have hga : mat g *ᵥ a = α • a + β • b := by
      have hf : form F a (a + (β * 1) • b) = β := by
        rw [map_add, map_smul, form_self, hab]
        simp
      rw [hg, mat_mul_mulVec, transv_mulVec, transv_mulVec, hba, hf, div_mul_cancel₀ _ hβ,
        mul_one]
      module
    rw [← hga, ← transv_conj]
    exact mul_mem (mul_mem hgm (ha c)) (inv_mem hgm)

end CharTwo

abbrev ln₀' (F : Type) [Field F] : Submodule F (V4 F) := Submodule.span F {f₁ F, f₂ F}

theorem mem_ln₀' {v : V4 F} : v ∈ ln₀' F ↔ v (.inl 0) = 0 ∧ v (.inl 1) = 0 := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp
  · rintro ⟨h0, h1⟩
    refine ⟨v (.inr 0), v (.inr 1), ext4 ?_ ?_ ?_ ?_⟩ <;> simp [h0, h1]

theorem isLine_ln₀' : IsLine (ln₀' F) := by
  refine ⟨?_, fun x hx y hy => ?_⟩
  · have hw : f₂ F ∉ F ∙ f₁ F := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, ha⟩
      have := congrFun ha (.inr 1)
      simp at this
    exact finrank_span_pair f₁_ne_zero hw
  · rw [form_apply, (mem_ln₀'.1 hx).1, (mem_ln₀'.1 hx).2, (mem_ln₀'.1 hy).1, (mem_ln₀'.1 hy).2]
    ring

theorem ln₀_inf_ln₀' : ln₀ F ⊓ ln₀' F = ⊥ := by
  refine eq_bot_iff.2 fun v hv => ?_
  obtain ⟨⟨h2, h3⟩, h0, h1⟩ := And.intro (mem_ln₀.1 hv.1) (mem_ln₀'.1 hv.2)
  rw [Submodule.mem_bot]
  exact ext4 h0 h1 h2 h3

theorem transv_mem_qLine {l : Submodule F (V4 F)} (hl : IsLine l) {x : V4 F} (hx : x ∈ l)
    (c : F) : transv x c ∈ qLine l :=
  xPoint_le_qLine hl ((Submodule.span_singleton_le_iff_mem _ _).2 hx) (transv_mem_xPoint x c)

theorem Q₁_sup_qLine_ln₀' [CharP F 2] : Q₁ F ⊔ qLine (ln₀' F) = ⊤ := by
  have hln : ∀ x : V4 F, x ∈ ln₀ F → ∀ c : F, transv x c ∈ Q₁ F ⊔ qLine (ln₀' F) :=
    fun x hx c => Subgroup.mem_sup_left (transv_mem_qLine isLine_ln₀ hx c)
  have hln' : ∀ x : V4 F, x ∈ ln₀' F → ∀ c : F, transv x c ∈ Q₁ F ⊔ qLine (ln₀' F) :=
    fun x hx c => Subgroup.mem_sup_right (transv_mem_qLine isLine_ln₀' hx c)
  exact eq_top_of_five _ (hln _ (mem_ln₀.2 ⟨by simp, by simp⟩))
    (hln _ (mem_ln₀.2 ⟨by simp, by simp⟩)) (hln' _ (mem_ln₀'.2 ⟨by simp, by simp⟩))
    (hln' _ (mem_ln₀'.2 ⟨by simp, by simp⟩)) (hln _ (mem_ln₀.2 ⟨by simp, by simp⟩))

theorem exists_eq_map_tau {l : Submodule F (V4 F)} (hl : IsLine l) (hopp : l ⊓ ln₀ F = ⊥) :
    ∃ (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C),
      l = (ln₀' F).map (mulVecLin (mat (tau hC))) := by
  let π : ↥l →ₗ[F] (Fin 2 → F) :=
    { toFun := fun v j => (v : V4 F) (.inr j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hπ : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h0 := congrFun (hv : π v = 0) 0
    have h1 := congrFun (hv : π v = 0) 1
    have : (v : V4 F) ∈ l ⊓ ln₀ F := ⟨v.2, mem_ln₀.2 ⟨h0, h1⟩⟩
    rw [hopp, Submodule.mem_bot] at this
    exact (Submodule.mem_bot F).2 (Subtype.ext this)
  have hπs : Function.Surjective π := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hπ
    rw [hl.1]
    simp
  obtain ⟨u₀, hu₀⟩ := hπs (Pi.single 0 1)
  obtain ⟨u₁, hu₁⟩ := hπs (Pi.single 1 1)
  have h00 : (u₀ : V4 F) (.inr 0) = 1 := by simpa [π] using congrFun hu₀ 0
  have h01 : (u₀ : V4 F) (.inr 1) = 0 := by simpa [π] using congrFun hu₀ 1
  have h10 : (u₁ : V4 F) (.inr 0) = 0 := by simpa [π] using congrFun hu₁ 0
  have h11 : (u₁ : V4 F) (.inr 1) = 1 := by simpa [π] using congrFun hu₁ 1
  set C : Matrix (Fin 2) (Fin 2) F := !![(u₀ : V4 F) (.inl 0), (u₁ : V4 F) (.inl 0);
    (u₀ : V4 F) (.inl 1), (u₁ : V4 F) (.inl 1)] with hCdef
  have hB := hl.2 _ u₀.2 _ u₁.2
  rw [form_apply, h00, h01, h10, h11] at hB
  have hC : Cᵀ = C := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hCdef]
    all_goals first | linear_combination hB | linear_combination -hB
  refine ⟨C, hC, ?_⟩
  have himg : ∀ j : Fin 2, mat (tau hC) *ᵥ Pi.single (.inr j) 1 = if j = 0 then u₀ else u₁ := by
    intro j
    obtain ⟨e0, e1, e2, e3⟩ := mulVec_blockMat_unitri 0 C (Pi.single (.inr j) 1)
    rw [mat_tau]
    fin_cases j
    · refine ext4 ?_ ?_ ?_ ?_
      · rw [e0]
        simp [hCdef]
      · rw [e1]
        simp [hCdef]
      · rw [e2]
        simp [h00]
      · rw [e3]
        simp [h01]
    · refine ext4 ?_ ?_ ?_ ?_
      · rw [e0]
        simp [hCdef]
      · rw [e1]
        simp [hCdef]
      · rw [e2]
        simp [h10]
      · rw [e3]
        simp [h11]
  have hle : (ln₀' F).map (mulVecLin (mat (tau hC))) ≤ l := by
    rw [Submodule.map_span_le]
    rintro x (rfl | rfl)
    · rw [mulVecLin_apply, himg 0]
      exact u₀.2
    · rw [mulVecLin_apply, himg 1]
      simp only [one_ne_zero, ↓reduceIte]
      exact u₁.2
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [← (Submodule.equivMapOfInjective _ (mulVec_mat_injective _) (ln₀' F)).finrank_eq,
    isLine_ln₀'.1, hl.1]

theorem isLine_map {l : Submodule F (V4 F)} (hl : IsLine l) (g : Sp4 F) :
    IsLine (l.map (mulVecLin (mat g))) := by
  refine ⟨?_, ?_⟩
  · rw [← (Submodule.equivMapOfInjective _ (mulVec_mat_injective g) l).finrank_eq, hl.1]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, form_mat]
    exact hl.2 x hx y hy

theorem map_inf_map (g : Sp4 F) (W W' : Submodule F (V4 F)) :
    (W ⊓ W').map (mulVecLin (mat g)) = W.map (mulVecLin (mat g)) ⊓ W'.map (mulVecLin (mat g)) :=
  Submodule.map_inf _ (mulVec_mat_injective g)

theorem qLine_map (g : Sp4 F) (W : Submodule F (V4 F)) :
    qLine (W.map (mulVecLin (mat g))) = (qLine W).map (MulAut.conj g).toMonoidHom :=
  (fixer_map_conj g W).symm

theorem map_map_mat_inv (g : Sp4 F) (W : Submodule F (V4 F)) :
    (W.map (mulVecLin (mat g⁻¹))).map (mulVecLin (mat g)) = W := by
  ext v
  rw [mem_map_mulVecLin, mem_map_mulVecLin, inv_inv, mat_mulVec_inv]

theorem map_map_mat_inv' (g : Sp4 F) (W : Submodule F (V4 F)) :
    (W.map (mulVecLin (mat g))).map (mulVecLin (mat g⁻¹)) = W := by
  have := map_map_mat_inv g⁻¹ W
  rwa [inv_inv] at this

theorem qLine_sup_qLine_eq_top [CharP F 2] {l l' : Submodule F (V4 F)} (hl : IsLine l)
    (hl' : IsLine l') (hopp : l ⊓ l' = ⊥) : qLine l ⊔ qLine l' = ⊤ := by
  obtain ⟨g, rfl⟩ := exists_map_ln₀_eq hl
  obtain ⟨l'', hl''⟩ : ∃ l'', l'' = l'.map (mulVecLin (mat g⁻¹)) := ⟨_, rfl⟩
  have hgl' : l' = l''.map (mulVecLin (mat g)) := by rw [hl'', map_map_mat_inv]
  have hopp'' : l'' ⊓ ln₀ F = ⊥ := by
    have := congrArg (Submodule.map (mulVecLin (mat g⁻¹))) hopp
    rw [map_inf_map, Submodule.map_bot, map_map_mat_inv', ← hl''] at this
    rw [inf_comm, this]
  have hll : IsLine l'' := hl'' ▸ isLine_map hl' g⁻¹
  obtain ⟨C, hC, hCl⟩ := exists_eq_map_tau hll hopp''
  have h1 : Q₁ F ⊔ qLine l'' = ⊤ := by
    have hτ : tau hC ∈ Q₁ F := tau_mem_Q₁ hC
    rw [hCl, qLine_map]
    have hQ : (Q₁ F).map (MulAut.conj (tau hC)).toMonoidHom = Q₁ F :=
      mem_normalizer_iff_map_conj.1 (P₁_le_normalizer_Q₁ (Q₁_le_P₁ hτ))
    rw [← hQ, ← Subgroup.map_sup, Q₁_sup_qLine_ln₀', Subgroup.map_top_of_surjective]
    exact (MulAut.conj (tau hC)).surjective
  rw [hgl', qLine_map, qLine_map, ← Subgroup.map_sup, h1,
    Subgroup.map_top_of_surjective]
  exact (MulAut.conj g).surjective

section Points

variable [CharP F 2]

@[expose] def muE (a : F) : Sp4 F := transv (f₁ F + e₂ F) a * transv (f₁ F) a * transv (e₂ F) a

theorem muE_mulVec (a : F) (v : V4 F) :
    mat (muE a) *ᵥ v = v + (a * v (.inl 0)) • e₂ F + (a * v (.inr 1)) • f₁ F := by
  rw [muE, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [form_apply] <;> grind

theorem form_f₁ (v : V4 F) : form F (f₁ F) v = v (.inl 0) := by
  rw [form_apply]
  simp [CharTwo.neg_eq]

theorem muE_mem_qPoint (a : F) : muE a ∈ qPoint (F ∙ f₁ F) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [muE_mulVec]
    simp
  · have h0 : v (.inl 0) = 0 := (form_f₁ v).symm.trans (mem_perp_span.1 hv)
    rw [muE_mulVec, h0, mul_zero, zero_smul, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

@[expose] noncomputable def wAlpha (F : Type) [Field F] [CharP F 2] : Sp4 F :=
  lam 1 * muE 1 * lam 1

theorem wAlpha_mulVec (v : V4 F) :
    mat (wAlpha F) *ᵥ v = v (.inl 1) • e₁ F + v (.inl 0) • e₂ F + v (.inr 1) • f₁ F +
      v (.inr 0) • f₂ F := by
  rw [wAlpha, mat_mul_mulVec, mat_mul_mulVec, muE_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [(mulVec_lam _ _).1, (mulVec_lam _ _).2.1,
    (mulVec_lam _ _).2.2.1, (mulVec_lam _ _).2.2.2] <;> grind

omit [CharP F 2] in
theorem transv_mem_X₂ (c : F) : transv (e₁ F) c ∈ X₂ F := by
  rw [show X₂ F = xPoint (F ∙ e₁ F) by rw [← pt₀_eq_span]]
  exact transv_mem_xPoint _ c

theorem Q₂_sup_qPoint_f₁ : Q₂ F ⊔ qPoint (F ∙ f₁ F) = ⊤ := by
  set G₀ := Q₂ F ⊔ qPoint (F ∙ f₁ F)
  have h1 : ∀ c : F, transv (e₁ F) c ∈ G₀ := fun c =>
    Subgroup.mem_sup_left (X₂_le_Q₂ (transv_mem_X₂ c))
  have h3 : ∀ c : F, transv (f₁ F) c ∈ G₀ := fun c =>
    Subgroup.mem_sup_right (xPoint_le_qPoint (isPoint_span f₁_ne_zero) (transv_mem_xPoint _ c))
  have hlam : ∀ a : F, lam a ∈ G₀ := fun a => Subgroup.mem_sup_left (lam_mem_Q₂ a)
  have hmu : ∀ a : F, muE a ∈ G₀ := fun a => Subgroup.mem_sup_right (muE_mem_qPoint a)
  have hw : wAlpha F ∈ G₀ := mul_mem (mul_mem (hlam 1) (hmu 1)) (hlam 1)
  have h2 : ∀ c : F, transv (e₂ F) c ∈ G₀ := fun c => by
    have := transv_mem_of_conj hw h1 c
    convert this using 2
    rw [wAlpha_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have h4 : ∀ c : F, transv (f₂ F) c ∈ G₀ := fun c => by
    have := transv_mem_of_conj hw h3 c
    convert this using 2
    rw [wAlpha_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have h5 : ∀ c : F, transv (e₁ F + e₂ F) c ∈ G₀ := fun c => by
    have := transv_mem_of_conj (hlam 1) h2 c
    convert this using 2
    refine ext4 ?_ ?_ ?_ ?_
    · rw [(mulVec_lam _ _).1]
      simp
    · rw [(mulVec_lam _ _).2.1]
      simp
    · rw [(mulVec_lam _ _).2.2.1]
      simp
    · rw [(mulVec_lam _ _).2.2.2]
      simp
  exact eq_top_of_five G₀ h1 h2 h3 h4 h5

theorem Q₂_sup_zpowers_transv {c : F} (hc : c ≠ 0) :
    Q₂ F ⊔ Subgroup.zpowers (transv (f₁ F) c) = ⊤ := by
  set G₀ := Q₂ F ⊔ Subgroup.zpowers (transv (f₁ F) c)
  have ht : transv (f₁ F) c ∈ G₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have h1 : ∀ d : F, transv (e₁ F) d ∈ G₀ := fun d =>
    Subgroup.mem_sup_left (X₂_le_Q₂ (transv_mem_X₂ d))
  have hte : mat (transv (f₁ F) c) *ᵥ e₁ F = e₁ F + c • f₁ F := by
    rw [transv_mulVec, form_f₁]
    simp
  have hb : ∀ d : F, transv (c⁻¹ • (e₁ F + c • f₁ F)) d ∈ G₀ := fun d => by
    rw [transv_smul_vec, ← hte]
    exact transv_mem_of_conj ht h1 _
  have hab : form F (e₁ F) (c⁻¹ • (e₁ F + c • f₁ F)) = 1 := by
    rw [map_smul, map_add, map_smul, form_self, smul_eq_mul, pairedSympForm_single_inl]
    simp [inv_mul_cancel₀ hc]
  have h3 : ∀ d : F, transv (f₁ F) d ∈ G₀ := fun d => by
    have := transv_mem_of_pair hab h1 hb c⁻¹ 1 d
    convert this using 2
    rw [smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, one_smul, ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add]
  have hw : wOne F ∈ G₀ := mul_mem (mul_mem (h1 1) (h3 1)) (h1 1)
  have hQf : qPoint (F ∙ f₁ F) ≤ G₀ := by
    have hmap : qPoint (F ∙ f₁ F) = (Q₂ F).map (MulAut.conj (wOne F)).toMonoidHom := by
      rw [qPoint_map_conj, pt₀_eq_span, Submodule.map_span, Set.image_singleton, mulVecLin_apply,
        wOne_mulVec]
      congr 3
      refine ext4 ?_ ?_ ?_ ?_ <;> simp
    rw [hmap]
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hw (Subgroup.mem_sup_left hx)) (inv_mem hw)
  refine eq_top_iff.2 ?_
  rw [← Q₂_sup_qPoint_f₁]
  exact sup_le le_sup_left hQf

end Points

end CFSG.Quasithin.MS93.MSP
