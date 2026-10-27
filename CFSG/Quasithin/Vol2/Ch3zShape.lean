module

public import CFSG.Quasithin.Vol2.Ch3zBlocks
public import CFSG.Quasithin.Vol2.Ch3zRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6

namespace Ch3z

variable {V : Type} [CommGroup V]

theorem apply_mem_commV_of_mem {H : Subgroup (MulAut V)} {h : MulAut V} (hh : h ∈ H) {u : V}
    (hu : u ∈ commV H) : h u ∈ commV H :=
  G6.apply_mem_commV (fun _ hx => H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)) hu

@[expose] def SymBlk (M H : Subgroup (MulAut V)) (m : ℕ) : Prop :=
  3 ≤ m ∧ Odd m ∧ ∃ (θ : ↥H ≃* Equiv.Perm (Fin m)) (β : ↥(coreMod m) →* V),
    (∀ (x : ↥H) (u : ↥(coreMod m)), β (coreAct m (θ x) u) = (x : MulAut V) (β u)) ∧
    β.range = commV H ∧ β.ker = ⊥ ∧
    (m = 7 → ∃ p : Fin m, ((M ⊓ H).subgroupOf H).map θ.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin m)) p)

variable {X T M : Subgroup (MulAut V)} {𝓗 : Finset (Subgroup (MulAut V))}

theorem BlkCtx.symBlk_or_bad (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) :
    (∃ m, SymBlk M H m) ∨
      ∃ e : ℕ, 2 ≤ e ∧ NatBlockData H (commV H) e ∧
        M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rcases h.types H hH with ⟨e, he1, hbin, hM⟩ | ⟨k, hk1, π, hreal, hM⟩
  · have hZ : commV H ⊓ fixV (ffJ X) = ⊥ := by rw [h.fixV_ffJ, inf_bot_eq]
    rw [hZ] at hbin
    have hnat := natBlockData_of_binaryNatural hbin
    by_cases he : e = 1
    · subst he
      left
      have hsym : IsSymCore H (commV H) 3 :=
        isSymCore_three_of_natBlock h.hV (fun _ hx _ hu => apply_mem_commV_of_mem hx hu) hnat
      obtain ⟨θ, β, hβeq, hβr, hβk⟩ := hsym
      refine ⟨3, by norm_num, by decide, θ, β, hβeq, hβr, hβk, fun h3 => absurd h3 (by norm_num)⟩
    · right
      exact ⟨e, by omega, hnat, hM⟩
  · left
    obtain ⟨θ, β, hθπ, hβeq, hβr, hβk⟩ := isSymCore_of_realizes' hreal
    refine ⟨2 * k + 1, by omega, odd_two_mul_add_one k, θ, β, hβeq, hβr, hβk, fun _ => ?_⟩
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [hM, Subgroup.map_map]
    have hcomp : θ.toMonoidHom.comp π = MonoidHom.id _ := by
      refine MonoidHom.ext fun σ => ?_
      have := θ.apply_symm_apply σ
      rw [hθπ] at this
      exact this
    rw [hcomp, Subgroup.map_id]

section Structure

theorem le_blocks_ne {𝓗 : Finset (Subgroup (MulAut V))} {H H' : Subgroup (MulAut V)}
    (hH' : H' ∈ 𝓗) (hne : H' ≠ H) : H' ≤ ⨆ H'' ∈ 𝓗, ⨆ (_ : H'' ≠ H), H'' :=
  le_iSup₂_of_le H' hH' (le_iSup (fun _ : H' ≠ H => H') hne)

theorem BlkCtx.indep₂ (h : BlkCtx X T M 𝓗) {H₁ H₂ : Subgroup (MulAut V)} (h₁ : H₁ ∈ 𝓗)
    (h₂ : H₂ ∈ 𝓗) (hne : H₁ ≠ H₂) {a b : MulAut V} (ha : a ∈ H₁) (hb : b ∈ H₂) (hab : a * b = 1) :
    a = 1 ∧ b = 1 := by
  have ha1 : a = 1 := by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab
    have hmem : a ∈ H₁ ⊓ ⨆ H'' ∈ 𝓗, ⨆ (_ : H'' ≠ H₁), H'' :=
      ⟨ha, le_blocks_ne h₂ hne.symm (this ▸ H₂.inv_mem hb)⟩
    rw [h.inf_blocks h₁] at hmem
    exact Subgroup.mem_bot.mp hmem
  subst ha1
  exact ⟨rfl, by simpa using hab⟩

theorem BlkCtx.indep₃ (h : BlkCtx X T M 𝓗) {H₁ H₂ H₃ : Subgroup (MulAut V)} (h₁ : H₁ ∈ 𝓗)
    (h₂ : H₂ ∈ 𝓗) (h₃ : H₃ ∈ 𝓗) (h12 : H₁ ≠ H₂) (h13 : H₁ ≠ H₃) (h23 : H₂ ≠ H₃)
    {a b c : MulAut V} (ha : a ∈ H₁) (hb : b ∈ H₂) (hc : c ∈ H₃) (habc : a * b * c = 1) :
    a = 1 ∧ b = 1 ∧ c = 1 := by
  have ha1 : a = 1 := by
    have : a = (b * c)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact habc
    have hmem : a ∈ H₁ ⊓ ⨆ H'' ∈ 𝓗, ⨆ (_ : H'' ≠ H₁), H'' := by
      refine ⟨ha, ?_⟩
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (le_blocks_ne h₂ h12.symm hb)
        (le_blocks_ne h₃ h13.symm hc))
    rw [h.inf_blocks h₁] at hmem
    exact Subgroup.mem_bot.mp hmem
  subst ha1
  rw [one_mul] at habc
  obtain ⟨hb1, hc1⟩ := h.indep₂ h₂ h₃ h23 hb hc habc
  exact ⟨rfl, hb1, hc1⟩

theorem BlkCtx.nonempty (h : BlkCtx X T M 𝓗) : 𝓗.Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hJ : ffJ X = ⊥ := by rw [h.ffJ_eq, hne]; simp
  have hX : X = T := by rw [h.eq_sup, hJ, bot_sup_eq]
  exact absurd hX (ne_of_gt h.mp.lt)

end Structure

section S7

abbrev Om7 : Type := {s : Finset (Fin 7) // s.card = 2}

instance : MulAction (Equiv.Perm (Fin 7)) Om7 where
  smul σ s := ⟨s.1.map σ.toEmbedding, by rw [Finset.card_map]; exact s.2⟩
  one_smul s := Subtype.ext (by
    show s.1.map (1 : Equiv.Perm (Fin 7)).toEmbedding = s.1
    ext x
    rw [Finset.mem_map_equiv]
    rfl)
  mul_smul σ τ s := Subtype.ext (by
    show s.1.map (σ * τ).toEmbedding = (s.1.map τ.toEmbedding).map σ.toEmbedding
    rw [Finset.map_map]
    rfl)

theorem card_Om7 : Nat.card Om7 = 21 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem exists_swap_fix_move : ∀ (s : Om7) (p : Fin 7), ∃ a b : Fin 7,
    Equiv.swap a b • s = s ∧ Equiv.swap a b p ≠ p := by
  decide +kernel

theorem exists_swap_not_fix : ∀ s : Om7, ∃ a b : Fin 7, Equiv.swap a b • s ≠ s := by
  decide +kernel


theorem false_of_sym7 {Γ : Type*} [Group Γ] [Finite Γ] {T M : Subgroup Γ}
    (mp : MinParabolic (⊤ : Subgroup Γ) T M) (θ : Γ ≃* Equiv.Perm (Fin 7)) (p : Fin 7)
    (hM : M.map θ.toMonoidHom = MulAction.stabilizer (Equiv.Perm (Fin 7)) p) : False := by
  set T' : Subgroup (Equiv.Perm (Fin 7)) := T.map θ.toMonoidHom with hT'
  have hT'p : IsPGroup 2 T' := mp.isSylow.2.1.map θ.toMonoidHom
  have hmod := hT'p.card_modEq_card_fixedPoints (α := Om7)
  rw [card_Om7] at hmod
  have hne : Nat.card (MulAction.fixedPoints T' Om7) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have h1 : (21 : ℕ) % 2 = 0 % 2 := hmod
    omega
  obtain ⟨⟨s₀, hs₀⟩⟩ : Nonempty (MulAction.fixedPoints T' Om7) :=
    (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
  have hfix : ∀ σ ∈ T', σ • s₀ = s₀ := fun σ hσ => hs₀ ⟨σ, hσ⟩
  have hTK : T ≤ (MulAction.stabilizer (Equiv.Perm (Fin 7)) s₀).comap θ.toMonoidHom := by
    intro t ht
    exact hfix (θ t) ⟨t, ht, rfl⟩
  have hKtop : (MulAction.stabilizer (Equiv.Perm (Fin 7)) s₀).comap θ.toMonoidHom < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    obtain ⟨a, b, hab⟩ := exists_swap_not_fix s₀
    have hmem : θ.symm (Equiv.swap a b) ∈
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) s₀).comap θ.toMonoidHom := by
      rw [htop]; trivial
    exact hab (by simpa using hmem)
  have hKM := mp.le_of_lt hTK hKtop
  obtain ⟨a, b, hab, hmove⟩ := exists_swap_fix_move s₀ p
  have h1 : θ.symm (Equiv.swap a b) ∈
      (MulAction.stabilizer (Equiv.Perm (Fin 7)) s₀).comap θ.toMonoidHom := by
    simpa using hab
  have h2 : Equiv.swap a b ∈ M.map θ.toMonoidHom := ⟨θ.symm (Equiv.swap a b), hKM h1, by simp⟩
  rw [hM] at h2
  exact hmove h2


end S7

section Classification

variable [Finite V]

@[expose] def ShapeOne (X : Subgroup (MulAut V)) (m : ℕ) : Prop := (m = 3 ∨ m = 5) ∧ IsSymCore X ⊤ m

omit [Finite V] in
theorem BlkCtx.card_le_two (h : BlkCtx X T M 𝓗) (hX : IsRankTwoQuotient ↥X)
    (hsym : ∀ H ∈ 𝓗, ∃ m, SymBlk M H m) : 𝓗.card ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨H₁, h₁, H₂, h₂, H₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hc
  obtain ⟨m₁, hm₁, -, θ₁, -⟩ := hsym H₁ h₁
  obtain ⟨m₂, hm₂, -, θ₂, -⟩ := hsym H₂ h₂
  obtain ⟨m₃, hm₃, -, θ₃, -⟩ := hsym H₃ h₃
  exact false_of_three_blocks hX (h.mem_le h₁) (h.mem_le h₂) (h.mem_le h₃) θ₁ θ₂ θ₃ hm₁ hm₂ hm₃
    (fun a ha b hb => h.comm_of_ne h₁ h₂ h12 ha hb) (fun a ha b hb => h.comm_of_ne h₁ h₃ h13 ha hb)
    (fun a ha b hb => h.comm_of_ne h₂ h₃ h23 ha hb)
    (fun a ha b hb c hc habc => h.indep₃ h₁ h₂ h₃ h12 h13 h23 ha hb hc habc)

theorem BlkCtx.shape_of_card_one (h : BlkCtx X T M 𝓗) (hX : IsRankTwoQuotient ↥X)
    (hcard : 𝓗.card = 1) (hsym : ∀ H ∈ 𝓗, ∃ m, SymBlk M H m) : ∃ m, ShapeOne X m := by
  obtain ⟨H₁, h𝓗⟩ := Finset.card_eq_one.mp hcard
  have hH₁ : H₁ ∈ 𝓗 := by rw [h𝓗]; exact Finset.mem_singleton_self _
  obtain ⟨m, hm3, hmodd, θ, β, hβeq, hβr, hβk, hm7⟩ := hsym H₁ hH₁
  have hH₁X : H₁ ≤ X := h.mem_le hH₁
  have hm9 : m < 9 := by
    by_contra hge
    push Not at hge
    exact false_of_one_block hX hH₁X θ hge
  have hmcases : m = 3 ∨ m = 5 ∨ m = 7 := by
    obtain ⟨k, hk⟩ := hmodd
    omega
  have hJ : ffJ X = H₁ := by rw [h.ffJ_eq, h𝓗]; simp
  have hV : commV H₁ = ⊤ := by
    have := h.iSup_comm
    rw [h𝓗] at this
    simpa using this
  have hXH : X = H₁ := by
    refine le_antisymm (fun x hx => ?_) hH₁X
    have hnorm : x ∈ Subgroup.normalizer (H₁ : Set (MulAut V)) := hJ ▸ B6.le_normalizer_ffJ X hx
    obtain ⟨y, hyH, hxy⟩ := exists_mem_eq_on_of_normalizes hmcases ⟨θ, β, hβeq, hβr, hβk⟩ x
      (fun w _ => by rw [hV]; trivial) (fun w _ => by rw [hV]; trivial) hnorm
    have : x = y := MulEquiv.ext fun w => hxy w (by rw [hV]; trivial)
    rw [this]
    exact hyH
  subst hXH
  have hm35 : m = 3 ∨ m = 5 := by
    rcases hmcases with h3 | h5 | h7
    · exact Or.inl h3
    · exact Or.inr h5
    · exfalso
      obtain ⟨p, hp⟩ := hm7 h7
      subst h7
      have hMX : M ≤ X := h.mp.maximal.1.le
      rw [inf_eq_left.mpr hMX] at hp
      exact false_of_sym7 h.mp.subgroupOf θ p hp
  refine ⟨m, hm35, θ, β, hβeq, ?_, hβk⟩
  rw [hβr, hV]

end Classification

end Ch3z

end CFSG.Quasithin
