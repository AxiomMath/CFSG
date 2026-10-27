module

public import CFSG.Quasithin.MS93.S4AEA

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin.MS93
open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem burnsideMag568_eq_top_of_sub_mem {V : Type*} [AddCommGroup V] [Module F V]
    {f : V → V} {σ : F → F} (hσ : ∀ (c : F) (y : V), f (c • y) = σ c • f y) {c₀ : F}
    (hc₀ : σ c₀ ≠ c₀) {W : Submodule F V} (hW : ∀ y, y - f y ∈ W) : W = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h3 : (c₀ - σ c₀) • f v ∈ W := by
    have e : (c₀ - σ c₀) • f v = (c₀ • v - f (c₀ • v)) - c₀ • (v - f v) := by
      rw [hσ, smul_sub, sub_smul]
      abel
    rw [e]
    exact W.sub_mem (hW (c₀ • v)) (W.smul_mem c₀ (hW v))
  have h4 : f v ∈ W := by
    have hne : c₀ - σ c₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₀)
    have := W.smul_mem (c₀ - σ c₀)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have := W.add_mem (hW v) h4
  rwa [sub_add_cancel] at this

theorem burnsideMag568_commN_eq_pt0_or_fixN_eq_ln01 [Finite F] {E : Subgroup (SL3 F)}
    (hE : E ≤ sStar) (hf : Module.finrank F (fixN E) = 2) (hc : commN E ≠ ⊥) :
    commN E = pt0 ∨ fixN E = ln01 := by
  by_cases hall : ∀ g ∈ E, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0
  · left
    have hle : commN E ≤ pt0 := by
      rw [commN, Submodule.span_le]
      rintro _ ⟨g, hg, x, rfl⟩
      obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hE hg)
      have hc0 : c = 0 := by simpa [coe_uniTri] using hall _ hg
      subst hc0
      rw [uniTri_mulVec]
      refine ⟨?_, ?_⟩ <;> simp
    have hpos : 0 < Module.finrank F (commN E) :=
      Nat.pos_of_ne_zero fun h0 => hc (Submodule.finrank_eq_zero.mp h0)
    have hle1 : Module.finrank F (commN E) ≤ 1 :=
      (Submodule.finrank_mono hle).trans finrank_pt0.le
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_pt0]; omega)
  · right
    push Not at hall
    obtain ⟨g, hg, hg12⟩ := hall
    obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp (hE hg)
    have hc0 : c ≠ 0 := by simpa [coe_uniTri] using hg12
    have hx : ∀ x ∈ fixN E, x 2 = 0 ∧ a * x 1 = 0 := by
      intro x hx
      have h := hx _ hg
      rw [uniTri_mulVec] at h
      have e1 := congrFun h 0
      have e2 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
      have hx2 : x 2 = 0 := by
        have : c * x 2 = 0 := by linear_combination e2
        exact (mul_eq_zero.mp this).resolve_left hc0
      exact ⟨hx2, by linear_combination e1 - b * hx2⟩
    by_cases ha : a = 0
    · have hle : fixN E ≤ ln01 := fun x hx' => (hx x hx').1
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hf, finrank_ln01])
    · exfalso
      have hle : fixN E ≤ pt0 := fun x hx' =>
        ⟨(mul_eq_zero.mp (hx x hx').2).resolve_left ha, (hx x hx').1⟩
      have := (Submodule.finrank_mono hle).trans finrank_pt0.le
      omega

theorem burnsideMag568_map_conj_inv_map_conj {Γ : Type*} [Group Γ] (H : Subgroup Γ) (x : Γ) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have e : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id Γ := by
    ext g
    simp [mul_assoc]
  rw [e, Subgroup.map_id]

theorem burnsideMag568_flag [Finite F] {x : SL3 F} {E : Subgroup (SL3 F)}
    (hE : E ≤ (sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom)
    (hf : Module.finrank F (fixN E) = 2) (hc : commN E ≠ ⊥) :
    commN E = fixN ((sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom) ∨
      fixN E = commN ((sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom) := by
  set E' := E.map (MulAut.conj x⁻¹).toMonoidHom with hE'def
  have hEE : E = E'.map (MulAut.conj x).toMonoidHom := by
    rw [hE'def]
    have := burnsideMag568_map_conj_inv_map_conj E x⁻¹
    rw [inv_inv] at this
    exact this.symm
  have hE' : E' ≤ sStar := by
    have := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hE
    rwa [burnsideMag568_map_conj_inv_map_conj] at this
  have hf' : Module.finrank F (fixN E') = 2 := by
    rw [hEE, finrank_fixN_map_conj] at hf
    exact hf
  have hc' : commN E' ≠ ⊥ := by
    intro h0
    apply hc
    rw [hEE, commN_map_conj, h0, Submodule.map_bot]
  rcases burnsideMag568_commN_eq_pt0_or_fixN_eq_ln01 hE' hf' hc' with h | h
  · left
    rw [hEE, commN_map_conj, fixN_map_conj, h, fixN_sStar]
  · right
    rw [hEE, fixN_map_conj, commN_map_conj, h, commN_sStar]

theorem burnsideMag568_fixN_le_commN_map [Finite F] (x : SL3 F) :
    fixN ((sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom) ≤
      commN ((sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom) := by
  rw [fixN_map_conj, commN_map_conj, fixN_sStar, commN_sStar]
  exact Submodule.map_mono pt0_le_ln01

theorem burnsideMag568_finrank_fixN_map [Finite F] (x : SL3 F) :
    Module.finrank F (fixN ((sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom)) = 1 := by
  rw [finrank_fixN_map_conj, fixN_sStar, finrank_pt0]

theorem burnsideMag568_exists_eq_map_sStar [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {P : Subgroup (SL3 F)} (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) :
    ∃ x : SL3 F, P = (sStar : Subgroup (SL3 F)).map (MulAut.conj x).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SL3 F)
    ((isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF)) (hP.toSylow hPi)
  refine ⟨x, ?_⟩
  have := congrArg (fun Q : Sylow 2 (SL3 F) => (Q : Subgroup (SL3 F))) hx
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
  rw [Subgroup.pointwise_smul_def] at this
  exact this.symm

theorem burnsideMag568_exists_mulVec_sub_eq [Finite F] {E : Subgroup (SL3 F)}
    (hf : Module.finrank F (fixN E) = 2) (hcard : Nat.card E = Nat.card (commN E))
    {v : Fin 3 → F} (hv : v ∉ fixN E) {c : Fin 3 → F} (hc : c ∈ commN E) :
    ∃ g ∈ E, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v = c := by
  let f : E → commN E := fun g =>
    ⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v, sub_mem_commN g.2 v⟩
  have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ (fixN E).zero_mem)
  have htop : fixN E ⊔ (F ∙ v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hdisj : fixN E ⊓ (F ∙ v) = ⊥ := by
      rw [eq_bot_iff]
      intro w ⟨hwE, hwv⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hwv
      rw [Submodule.mem_bot]
      by_contra ha
      have ha' : a ≠ 0 := fun h0 => ha (by rw [h0, zero_smul])
      apply hv
      have := (fixN E).smul_mem a⁻¹ hwE
      rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at this
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixN E) (F ∙ v)
    rw [hdisj, finrank_bot, add_zero, hf, finrank_span_singleton hv0] at h1
    rw [h1, Module.finrank_fin_fun]
  have hinj : Function.Injective f := by
    intro g h hgh
    have hgv : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
      have := congrArg Subtype.val hgh
      simpa [f] using this
    set k : SL3 F := (h : SL3 F)⁻¹ * g with hk
    have hkE : k ∈ E := E.mul_mem (E.inv_mem h.2) g.2
    have hkv : ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
      rw [hk, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hgv,
        Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    let K : Submodule F (Fin 3 → F) :=
      LinearMap.ker (Matrix.toLin' ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) - LinearMap.id)
    have hmemK : ∀ w, w ∈ K ↔ ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
      intro w
      simp [K, sub_eq_zero]
    have hle : fixN E ⊔ (F ∙ v) ≤ K := by
      refine sup_le (fun w hw => (hmemK w).mpr (hw k hkE)) ?_
      rw [Submodule.span_le]
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      exact (hmemK v).mpr hkv
    rw [htop, top_le_iff] at hle
    have hk1 : k = 1 := eq_one_of_mulVec_eq_self fun w => (hmemK w).mp (hle ▸ Submodule.mem_top)
    apply Subtype.ext
    have : (h : SL3 F) * k = g := by rw [hk, mul_inv_cancel_left]
    rw [← this, hk1, mul_one]
  have : Finite E := Finite.of_injective _ Subtype.coe_injective
  have : Finite (commN E) := Finite.of_injective _ Subtype.coe_injective
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  obtain ⟨g, hg⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem burnsideMag568_exists_fix_move {c y : Fin 3 → F} (hc : c ≠ 0)
    (hy : ∀ a : F, y ≠ a • c) :
    ∃ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ c = c ∧
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ≠ y := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨j, hj⟩ : ∃ j, c i * y j - c j * y i ≠ 0 := by
    by_contra h
    push Not at h
    apply hy (y i / c i)
    funext k
    have := h k
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination this
  set w : Fin 3 → F := c i • Pi.single j 1 - c j • Pi.single i 1 with hwdef
  have hwx : ∀ x : Fin 3 → F, w ⬝ᵥ x = c i * x j - c j * x i := by
    intro x
    rw [hwdef, sub_dotProduct, smul_dotProduct, smul_dotProduct, single_one_dotProduct,
      single_one_dotProduct, smul_eq_mul, smul_eq_mul]
  have hw : w ⬝ᵥ c = 0 := by rw [hwx]; ring
  set A : Matrix (Fin 3) (Fin 3) F := 1 + Matrix.vecMulVec c w with hAdef
  have hA : ∀ x, A *ᵥ x = x + (w ⬝ᵥ x) • c := by
    intro x
    rw [hAdef, Matrix.add_mulVec, Matrix.one_mulVec]
    congr 1
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hdet : A.det = 1 := by
    rw [hAdef, Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow, hw,
      add_zero]
  refine ⟨⟨A, hdet⟩, ?_, ?_⟩
  · change A *ᵥ c = c
    rw [hA, hw, zero_smul, add_zero]
  · change A *ᵥ y ≠ y
    rw [hA, hwx]
    intro h
    have h' : (c i * y j - c j * y i) • c = 0 := by
      have := congrArg (· - y) h
      simpa using this
    rcases smul_eq_zero.mp h' with h1 | h1
    · exact hj h1
    · exact hc h1

theorem burnsideMag568_fix_of_line [CharP F 2] {ℓ : Submodule F (Fin 3 → F)}
    (hℓ : Module.finrank F ℓ = 1) {g : SL3 F} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (hgℓ : ∀ x ∈ ℓ, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ ℓ) :
    ∀ x ∈ ℓ, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
  obtain ⟨c₀, hc₀, hspan⟩ := finrank_eq_one_iff'.mp hℓ
  obtain ⟨lam, hlam⟩ := hspan ⟨_, hgℓ _ c₀.2⟩
  have hlam' : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (c₀ : Fin 3 → F) =
      lam • (c₀ : Fin 3 → F) := by
    have := congrArg Subtype.val hlam
    simpa using this.symm
  have hpow : ∀ m : ℕ, ((g ^ m : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (c₀ : Fin 3 → F) =
      lam ^ m • (c₀ : Fin 3 → F) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hlam',
        Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have hc₀' : (c₀ : Fin 3 → F) ≠ 0 := fun h0 => hc₀ (Subtype.ext h0)
  have hl1 : lam ^ 2 ^ k = 1 := by
    have h1 := hpow (2 ^ k)
    rw [hg, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
    have h2 : (lam ^ 2 ^ k - 1) • (c₀ : Fin 3 → F) = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hc₀')
  have hl : lam = 1 := by
    have h1 : (lam - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, hl1, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)
  intro x hx
  obtain ⟨a, ha⟩ := hspan ⟨x, hx⟩
  have hx' : x = a • (c₀ : Fin 3 → F) := by
    have := congrArg Subtype.val ha
    simpa using this.symm
  rw [hx', Matrix.mulVec_smul, hlam', hl, one_smul]

end CFSG.Quasithin.MS93.S4L
