module

public import CFSG.Quasithin.EmptyFaithful.S146zNAmtD

public section

namespace CFSG.Quasithin.A6Amt

section Restriction

variable {V : Type} [CommGroup V]

theorem res_pow_two_eq_one {W : Subgroup V} {γ : MulAut V} (hγ : γ ∈ stabSub W) (h : γ ^ 2 = 1) :
    (res hγ) ^ 2 = 1 := by
  have h1 : (⟨γ, hγ⟩ : stabSub W) ^ 2 = 1 := Subtype.ext (by simpa using h)
  calc (res hγ) ^ 2 = resHom W ((⟨γ, hγ⟩ : stabSub W) ^ 2) := (map_pow (resHom W) _ 2).symm
    _ = 1 := by rw [h1, map_one]

end Restriction

section Stabilizer

variable {V : Type} [CommGroup V] [Finite V] {Γ L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
  {s : MulAut V}

theorem Ctx.swap_of_not_stab (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V}
    (hγ : γ ∈ Γ) (h : γ ∉ stabSub W₁) :
    (∀ u, γ u ∈ W₂ ↔ u ∈ W₁) ∧ (∀ u, γ u ∈ W₁ ↔ u ∈ W₂) := by
  rcases c.stab_or_swap F hγ with ⟨h1, _⟩ | h1
  · exact absurd h1 h
  · exact h1

theorem Ctx.stab₂ (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V} (hγ : γ ∈ Γ)
    (h₁ : γ ∈ stabSub W₁) : γ ∈ stabSub W₂ := by
  rcases c.stab_or_swap F hγ with ⟨_, h2⟩ | ⟨h2, _⟩
  · exact h2
  · exact absurd ((tw_eq_iff.mpr h₁).symm.trans (tw_eq_iff.mpr h2)) (c.ne F)

omit [Finite V] in
theorem Ctx.conj_mem_stab (c : Ctx Γ L W₁ W₂ s) {γ : MulAut V} (h₂ : γ ∈ stabSub W₂) :
    s⁻¹ * γ * s ∈ stabSub W₁ := by
  intro u
  have : (s⁻¹ * γ * s) u = s⁻¹ (γ (s u)) := by simp [MulAut.mul_apply]
  rw [this, ← c.hW₂s (γ (s u)), h₂ (s u), c.hW₂s (s u)]
  simp

theorem Ctx.eq_one_of_res (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V}
    (hγ : γ ∈ Γ) (h₁ : γ ∈ stabSub W₁) (h : res h₁ = 1) : γ = 1 := by
  have hfix₁ : ∀ u ∈ W₁, γ u = u := (res_eq_one_iff h₁).mp h
  have hcomm : ∀ l ∈ L, γ * l = l * γ := by
    intro l hl
    have hconj : γ * l * γ⁻¹ ∈ L := c.hnorm γ hγ l hl
    have h1 : c.rL ⟨γ * l * γ⁻¹, hconj⟩ = c.rL ⟨l, hl⟩ := by
      rw [c.rL_eq_res, c.rL_eq_res, res_eq_res_iff]
      intro u hu
      have h2 : γ⁻¹ u = u := by
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact (hfix₁ u hu).symm
      have h3 : γ (l u) = l u := hfix₁ _ ((c.mem_W₁_iff hl u).2 hu)
      simp [MulAut.mul_apply, h2, h3]
    have h4 := congrArg Subtype.val (F.inj h1)
    exact (mul_inv_eq_iff_eq_mul.mp h4)
  have hcomm₃ : ∀ l ∈ L, (s⁻¹ * γ * s) * l = l * (s⁻¹ * γ * s) := by
    intro l hl
    have hl' : s * l * s⁻¹ ∈ L := c.hnorm s c.hs l hl
    have e1 : s⁻¹ * γ * s * l = s⁻¹ * (γ * (s * l * s⁻¹)) * s := by group
    have e2 : l * (s⁻¹ * γ * s) = s⁻¹ * ((s * l * s⁻¹) * γ) * s := by group
    rw [e1, e2, hcomm _ hl']
  have h₂ : γ ∈ stabSub W₂ := c.stab₂ F hγ h₁
  have h₃ : s⁻¹ * γ * s ∈ stabSub W₁ := c.conj_mem_stab h₂
  have hn : res h₃ = 1 := by
    refine F.a1 _ fun l => ?_
    ext u
    exact congrArg (fun φ : MulAut V => φ (u : V)) (hcomm₃ l l.2)
  have hfix₃ : ∀ u ∈ W₁, (s⁻¹ * γ * s) u = u := (res_eq_one_iff h₃).mp hn
  have hfix₂ : ∀ w ∈ W₂, γ w = w := by
    intro w hw
    have := hfix₃ (s⁻¹ w) ((c.hW₂s w).1 hw)
    have h5 : s⁻¹ (γ w) = s⁻¹ w := by simpa [MulAut.mul_apply] using this
    exact (s⁻¹ : MulAut V).injective h5
  have hfix : W₁ ⊔ W₂ ≤ fixV (Subgroup.zpowers γ) :=
    sup_le (fun u hu => mem_fixV_zpowers_iff.mpr (hfix₁ u hu))
      (fun u hu => mem_fixV_zpowers_iff.mpr (hfix₂ u hu))
  refine MulEquiv.ext fun v => ?_
  rw [MulAut.one_apply]
  exact mem_fixV_zpowers_iff.mp (hfix (c.hsup ▸ Subgroup.mem_top v))

omit [Finite V] in
theorem Ctx.res_conj_rL (c : Ctx Γ L W₁ W₂ s) {γ : MulAut V} (hγ : γ ∈ Γ) (h₁ : γ ∈ stabSub W₁)
    (l : ↥L) :
    res h₁ * c.rL l * (res h₁)⁻¹ = c.rL ⟨γ * l * γ⁻¹, c.hnorm γ hγ l l.2⟩ := by
  have e : c.rL l = res (c.le_stab l.2) := rfl
  rw [e, ← res_inv h₁, ← res_mul h₁ (c.le_stab l.2),
    ← res_mul ((stabSub W₁).mul_mem h₁ (c.le_stab l.2)) ((stabSub W₁).inv_mem h₁)]
  rfl

omit [Finite V] in
theorem Ctx.res_mem_normalizer (c : Ctx Γ L W₁ W₂ s) {γ : MulAut V} (hγ : γ ∈ Γ)
    (h₁ : γ ∈ stabSub W₁) :
    res h₁ ∈ Subgroup.normalizer (c.rL.range : Set (MulAut ↥W₁)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨_, (c.res_conj_rL hγ h₁ l).symm⟩
  · rintro ⟨l, hl⟩
    refine ⟨⟨γ⁻¹ * l * γ, by simpa using c.hnorm γ⁻¹ (Γ.inv_mem hγ) l l.2⟩, ?_⟩
    have h2 := c.res_conj_rL (Γ.inv_mem hγ) ((stabSub W₁).inv_mem h₁) l
    rw [res_inv h₁, inv_inv] at h2
    have h3 : x = (res h₁)⁻¹ * (res h₁ * x * (res h₁)⁻¹) * res h₁ := by group
    rw [h3, ← hl, h2]
    exact congrArg c.rL (Subtype.ext (by simp))

theorem Ctx.mem_L_of_res (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V}
    (hγ : γ ∈ Γ) (h₁ : γ ∈ stabSub W₁) (h : res h₁ ∈ c.rL.range) : γ ∈ L := by
  obtain ⟨⟨l, hl⟩, hrl⟩ := h
  have hγl : γ⁻¹ * l ∈ stabSub W₁ := (stabSub W₁).mul_mem ((stabSub W₁).inv_mem h₁) (c.le_stab hl)
  have h2 : res hγl = 1 := by
    rw [res_mul ((stabSub W₁).inv_mem h₁) (c.le_stab hl), res_inv h₁, ← hrl, c.rL_eq_res]
    simp
  have h3 := c.eq_one_of_res F (Γ.mul_mem (Γ.inv_mem hγ) (c.hLΓ hl)) hγl h2
  have : γ = l := inv_mul_eq_one.mp h3
  exact this ▸ hl

theorem Ctx.inv_mul_mem_L (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ δ : MulAut V}
    (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) (h₁ : γ ∈ stabSub W₁) (h₂ : δ ∈ stabSub W₁) (hγL : γ ∉ L)
    (hδL : δ ∉ L) : γ⁻¹ * δ ∈ L := by
  have h3 := F.a3 _ (c.res_mem_normalizer hγ h₁) _ (c.res_mem_normalizer hδ h₂)
    (fun h => hγL (c.mem_L_of_res F hγ h₁ h)) (fun h => hδL (c.mem_L_of_res F hδ h₂ h))
  have hmem : γ⁻¹ * δ ∈ stabSub W₁ := (stabSub W₁).mul_mem ((stabSub W₁).inv_mem h₁) h₂
  have h4 : res hmem ∈ c.rL.range := by
    rw [res_mul ((stabSub W₁).inv_mem h₁) h₂, res_inv h₁]
    exact h3
  exact c.mem_L_of_res F (Γ.mul_mem (Γ.inv_mem hγ) hδ) hmem h4

end Stabilizer

section Ranks

variable {V : Type} [CommGroup V] [Finite V] {Γ L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}
  {s : MulAut V}

theorem Ctx.rank_split (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V} (hγ : γ ∈ Γ)
    (h₁ : γ ∈ stabSub W₁) :
    A6Rank γ = A6Rank (res h₁) + A6Rank (res (c.conj_mem_stab (c.stab₂ F hγ h₁))) := by
  have hinf := c.inf_eq_bot F
  have h₂ := c.stab₂ F hγ h₁
  have h₃ := c.conj_mem_stab h₂
  have e1 := rk_fixV_split c.hsup hinf (fun w hw => (h₁ w).2 hw) (fun w hw => (h₂ w).2 hw)
  have e2 := rk_add_rkIdx (fixV (Subgroup.zpowers γ))
  have e3 := rk_fixV_res h₁
  have e4 := rk_fixV_res h₃
  have e5 := rk_inf_fixV_twist c.hW₂s γ
  have e6 := c.rk_V hinf
  have e7 := c.hrk
  unfold A6Rank
  unfold res
  unfold A6Rank at e3 e4
  omega

theorem Ctx.rank_of_mem_L (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {l : MulAut V}
    (hl : l ∈ L) (hl1 : l ≠ 1) (hl2 : l ^ 2 = 1) : A6Rank l = 4 := by
  have h₁ : l ∈ stabSub W₁ := c.le_stab hl
  have hsl : s⁻¹ * l * s ∈ L := by simpa using c.hnorm s⁻¹ (Γ.inv_mem c.hs) l hl
  have e1 := c.rank_split F (c.hLΓ hl) h₁
  have e2 : A6Rank (res h₁) = 2 :=
    F.a2 ⟨l, hl⟩ (fun h => hl1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hl2))
  have e3 : A6Rank (res (c.conj_mem_stab (c.stab₂ F (c.hLΓ hl) h₁))) = 2 := by
    refine F.a2 ⟨s⁻¹ * l * s, hsl⟩ (fun h => hl1 ?_) (Subtype.ext ?_)
    · have : s⁻¹ * l * s = 1 := congrArg Subtype.val h
      have h4 : l = s * (s⁻¹ * l * s) * s⁻¹ := by group
      rw [h4, this]; group
    · have : (s⁻¹ * l * s) ^ 2 = s⁻¹ * l ^ 2 * s := by simp only [pow_two]; group
      simp [this, hl2]
  omega

theorem Ctx.three_le_rank_of_stab (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V}
    (hγ : γ ∈ Γ) (h₁ : γ ∈ stabSub W₁) (hL : γ ∉ L) (h2 : γ ^ 2 = 1) : 3 ≤ A6Rank γ := by
  have h₂ := c.stab₂ F hγ h₁
  have h₃ := c.conj_mem_stab h₂
  have hγ' : s⁻¹ * γ * s ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (Γ.inv_mem c.hs) hγ) c.hs
  have hL' : s⁻¹ * γ * s ∉ L := by
    intro h
    apply hL
    have := c.hnorm s c.hs _ h
    simpa [mul_assoc] using this
  have h2' : (s⁻¹ * γ * s) ^ 2 = 1 := by
    have : (s⁻¹ * γ * s) ^ 2 = s⁻¹ * γ ^ 2 * s := by simp only [pow_two]; group
    rw [this, h2]; group
  have e1 := c.rank_split F hγ h₁
  have e2 := F.a5 _ (c.res_mem_normalizer hγ h₁) _ (c.res_mem_normalizer hγ' h₃)
    (res_pow_two_eq_one h₁ h2) (res_pow_two_eq_one h₃ h2')
    (fun h => hL (c.mem_L_of_res F hγ h₁ h)) (fun h => hL' (c.mem_L_of_res F hγ' h₃ h)) ?_
  · omega
  · intro l l'' hl
    rw [c.res_conj_rL hγ' h₃ l] at hl
    have hl'' : (l'' : MulAut V) = (s⁻¹ * γ * s) * l * (s⁻¹ * γ * s)⁻¹ :=
      (congrArg Subtype.val (F.inj hl)).symm
    rw [c.res_conj_rL hγ h₁ (c.cL l)]
    refine congrArg c.rL (Subtype.ext ?_)
    show γ * ((c.cL l : ↥L) : MulAut V) * γ⁻¹ = ((c.cL l'' : ↥L) : MulAut V)
    rw [c.cL_apply l, c.cL_apply l'', hl'']
    group

theorem Ctx.four_le_rank_of_swap (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {γ : MulAut V}
    (hγ : γ ∈ Γ) (h : γ ∉ stabSub W₁) : 4 ≤ A6Rank γ := by
  have h1 := (c.swap_of_not_stab F hγ h).2
  have := rk_le_rkIdx_of_swap (c.inf_eq_bot F) (f := γ) fun w hw => (h1 w).2 hw
  rw [c.rk_W₂] at this
  exact this

theorem Ctx.three_le_rank (c : Ctx Γ L W₁ W₂ s) (F : A6Facts c.rL c.cL) {a : MulAut V}
    (ha : a ∈ Γ) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) : 3 ≤ A6Rank a := by
  by_cases hst : a ∈ stabSub W₁
  · by_cases hL : a ∈ L
    · have := c.rank_of_mem_L F hL ha1 ha2
      omega
    · exact c.three_le_rank_of_stab F ha hst hL ha2
  · have := c.four_le_rank_of_swap F ha hst
    omega

end Ranks

end CFSG.Quasithin.A6Amt
