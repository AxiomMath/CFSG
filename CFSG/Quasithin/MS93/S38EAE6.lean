module

public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.MS93.S38EAE6Pack

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin Equiv

@[expose] def IsInvA6 (σ : Perm (Fin 6)) : Prop := σ * σ = 1 ∧ Perm.sign σ = 1 ∧ σ ≠ 1

instance : DecidablePred IsInvA6 := fun σ => by unfold IsInvA6; infer_instance

@[expose] def ev (i : Fin 6) : Fin 6 → ZMod 2 := Pi.single i 1

@[expose] def pv (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := fun k => v (σ⁻¹ k)

@[expose] def Good (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : Prop :=
  (∀ k, v (σ k) = v k) ∧ ∀ k, σ k = k → v k = 0

instance (σ : Perm (Fin 6)) : DecidablePred (Good σ) := fun v => by unfold Good; infer_instance

theorem exists_fix_of_isInvA6 : ∀ σ : Perm (Fin 6), IsInvA6 σ → ∃ j, σ j = j :=
  fun _ h => S38EAPack.exists_fix h

theorem exists_two_moved : ∀ σ : Perm (Fin 6), IsInvA6 σ →
    ∃ i k, σ i ≠ i ∧ σ k ≠ k ∧ k ≠ i ∧ k ≠ σ i :=
  fun _ h => S38EAPack.exists_two_moved h

theorem exists_ne_of_isInvA6 : ∀ σ₁ : Perm (Fin 6), IsInvA6 σ₁ → ∀ σ₂ : Perm (Fin 6),
    IsInvA6 σ₂ → σ₁ ≠ σ₂ → ∃ i, σ₂ i ≠ i ∧ σ₁ i ≠ σ₂ i :=
  fun _ h₁ _ h₂ hne => S38EAPack.exists_ne h₁ h₂ hne

theorem exists_moved_ne : ∀ σ : Perm (Fin 6), σ ≠ 1 → ∃ i k, σ i ≠ i ∧ k ≠ i ∧ σ i ≠ k := by
  intro σ hσ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := not_forall.1 fun h => hσ (Equiv.ext h)
  obtain ⟨k, hk1, hk2⟩ := (by decide : ∀ a b : Fin 6, ∃ k, k ≠ a ∧ b ≠ k) i (σ i)
  exact ⟨i, k, hi, hk1, hk2⟩

theorem pv_sub_ev : ∀ σ : Perm (Fin 6), ∀ i j, σ j = j →
    pv σ (ev i + ev j) - (ev i + ev j) = ev i + ev (σ i) := by
  intro σ i j hj
  have e : pv σ (ev i + ev j) = ev (σ i) + ev j := by
    funext k
    simp only [pv, ev, Pi.add_apply, Pi.single_apply, Perm.inv_eq_iff_eq, hj]
  rw [e]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply]
  generalize ev (σ i) k = a
  generalize ev i k = b
  generalize ev j k = c
  revert a b c
  decide

theorem good_ev : ∀ σ : Perm (Fin 6), σ * σ = 1 → ∀ i, Good σ (ev i + ev (σ i)) := by
  intro σ hσ i
  have hσk : ∀ k, σ (σ k) = k := fun k => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · have h1 : σ k = i ↔ k = σ i := ⟨fun h => by rw [← h, hσk], fun h => by rw [h, hσk]⟩
    have h2 : σ k = σ i ↔ k = i := σ.injective.eq_iff
    simp only [ev, Pi.add_apply, Pi.single_apply, h1, h2]
    rw [add_comm]
  · simp only [ev, Pi.add_apply, Pi.single_apply]
    by_cases hki : k = i
    · subst hki
      rw [hk]
      simp only [eq_self_iff_true, ↓reduceIte]
      decide
    · have hks : k ≠ σ i := fun h => hki (by rw [← hk, h, hσk])
      rw [if_neg hki, if_neg hks, add_zero]

theorem not_good_ev : ∀ σ : Perm (Fin 6), ∀ i t, t ≠ i → σ i ≠ t → ¬ Good σ (ev i + ev t) := by
  intro σ i t hti hσi hg
  have hv : (ev i + ev t) i = 1 := by
    simp only [ev, Pi.add_apply, Pi.single_apply, eq_self_iff_true, ↓reduceIte,
      if_neg (Ne.symm hti), add_zero]
  by_cases hfix : σ i = i
  · have h0 := hg.2 i hfix
    rw [hv] at h0
    exact absurd h0 (by decide)
  · have h0 := hg.1 i
    rw [hv] at h0
    simp only [ev, Pi.add_apply, Pi.single_apply, if_neg hfix, if_neg hσi, add_zero] at h0
    exact absurd h0 (by decide)

theorem sum_ev_add : ∀ i k : Fin 6, k ≠ i → ∑ l, (ev i + ev k) l = 0 := by
  decide +kernel

theorem pv_ev_ne : ∀ σ : Perm (Fin 6), ∀ i k, σ i ≠ i → k ≠ i → σ i ≠ k →
    pv σ (ev i + ev k) ≠ ev i + ev k := by
  intro σ i k h1 h2 h3 h
  have h0 := congrFun h (σ i)
  have h5 : σ⁻¹ (σ i) = i := by simp
  simp only [pv, ev, Pi.add_apply, Pi.single_apply, h5, eq_self_iff_true,
    ↓reduceIte, if_neg (Ne.symm h2), if_neg h1, if_neg h3, add_zero] at h0
  exact absurd h0 (by decide)

theorem distinct_four : ∀ i p k q : Fin 6, p ≠ i → q ≠ k → k ≠ i → k ≠ p →
    ev i + ev p ≠ 0 ∧ ev k + ev q ≠ 0 ∧ ev i + ev p ≠ ev k + ev q ∧
      ev i + ev p + (ev k + ev q) ≠ 0 ∧ ev i + ev p + (ev k + ev q) ≠ ev i + ev p ∧
      ev i + ev p + (ev k + ev q) ≠ ev k + ev q := by
  decide +kernel

theorem good_zero (σ : Perm (Fin 6)) : Good σ 0 := ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem good_add {σ : Perm (Fin 6)} {v w : Fin 6 → ZMod 2} (hv : Good σ v) (hw : Good σ w) :
    Good σ (v + w) :=
  ⟨fun k => by simp only [Pi.add_apply, hv.1 k, hw.1 k],
    fun k hk => by simp only [Pi.add_apply, hv.2 k hk, hw.2 k hk, add_zero]⟩

private theorem inj_five {α : Type*} {x₀ x₁ x₂ x₃ x₄ : α} (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂)
    (h03 : x₀ ≠ x₃) (h04 : x₀ ≠ x₄) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h14 : x₁ ≠ x₄)
    (h23 : x₂ ≠ x₃) (h24 : x₂ ≠ x₄) (h34 : x₃ ≠ x₄) : Function.Injective ![x₀, x₁, x₂, x₃, x₄] := by
  intro n m hnm
  fin_cases n <;> fin_cases m <;> simp_all

section Card

variable {W : Type*} [CommGroup W]

theorem card_commV_ge_eight [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥H}
    (hR : (H13.altCoreModel 6).RealizesVia H ⊤ ⊥ π) {E : Subgroup (MulAut W)}
    {x₁ x₂ : MulAut W} (hx₁E : x₁ ∈ E) (hx₂E : x₂ ∈ E) (hx₁H : x₁ ∈ H) (hx₂H : x₂ ∈ H)
    (hne : x₁ ≠ x₂) (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1) (hsq₁ : x₁ * x₁ = 1) (hsq₂ : x₂ * x₂ = 1) :
    8 ≤ Nat.card (commV E) := by
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hR
  let D := H13.altCoreModel 6
  let q : ↥D.sec ⧸ D.ker.subgroupOf D.sec ≃* ↥D.sec :=
    (QuotientGroup.quotientMulEquivOfEq (by exact Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot
  have hqmk : ∀ m : ↥D.sec, q (QuotientGroup.mk m) = m := fun _ => rfl
  let c : W → Fin 6 → ZMod 2 := fun w =>
    Multiplicative.toAdd ((q (β ⟨w, Subgroup.mem_top w⟩) : ↥D.sec) : D.Amb)
  have hcmul : ∀ w w' : W, c (w * w') = c w + c w' := by
    intro w w'
    have e1 : (⟨w * w', Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨w, Subgroup.mem_top _⟩ * ⟨w', Subgroup.mem_top _⟩ := rfl
    have e2 : q (β ⟨w * w', Subgroup.mem_top _⟩) =
        q (β ⟨w, Subgroup.mem_top _⟩) * q (β ⟨w', Subgroup.mem_top _⟩) := by
      rw [e1, map_mul, map_mul]
    show Multiplicative.toAdd ((q (β ⟨w * w', _⟩) : ↥D.sec) : D.Amb) = _
    rw [e2]
    rfl
  have hcone : c 1 = 0 := by
    have h := hcmul 1 1
    rw [mul_one] at h
    exact (left_eq_add.mp h).symm ▸ rfl
  have hcinv : ∀ w : W, c w⁻¹ = -c w := by
    intro w
    have h := hcmul w w⁻¹
    rw [mul_inv_cancel, hcone] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hcsurj : ∀ v : Fin 6 → ZMod 2, ∑ l, v l = 0 → ∃ w : W, c w = v := by
    intro v hv
    have hvm : (Multiplicative.ofAdd v : D.Amb) ∈ D.sec := G6.mem_coreMod.mpr hv
    obtain ⟨u, hu⟩ := hβs (q.symm ⟨_, hvm⟩)
    refine ⟨u, ?_⟩
    show Multiplicative.toAdd ((q (β ⟨(u : W), Subgroup.mem_top _⟩) : ↥D.sec) : D.Amb) = v
    rw [Subtype.coe_eta, hu, MulEquiv.apply_symm_apply]
    rfl
  have hcequiv : ∀ (τ : ↥(alternatingGroup (Fin 6))) (w : W),
      c (((π τ : ↥H) : MulAut W) w) = pv (τ : Perm (Fin 6)) (c w) := by
    intro τ w
    set m := q (β ⟨w, Subgroup.mem_top w⟩) with hm
    have hβm : β ⟨w, Subgroup.mem_top w⟩ = QuotientGroup.mk m := by
      rw [hm]
      exact (q.symm_apply_apply _).symm.trans rfl
    have hact : D.act τ (m : D.Amb) ∈ D.sec := G6.permAct_mem_coreMod _ m.2
    have h1 : β ⟨((π τ : ↥H) : MulAut W) w, Subgroup.mem_top _⟩ =
        QuotientGroup.mk ⟨_, hact⟩ :=
      hβe τ ⟨w, Subgroup.mem_top w⟩ m (Subgroup.mem_top _) hact hβm
    show Multiplicative.toAdd ((q (β ⟨_, Subgroup.mem_top _⟩) : ↥D.sec) : D.Amb) = _
    rw [h1, hqmk]
    funext k
    exact G6.permAct_apply 6 (τ : Perm (Fin 6)) m.1 k
  have hπi : ∀ τ : ↥(alternatingGroup (Fin 6)), π τ = 1 → τ = 1 := by
    intro τ hτ
    by_contra hne1
    have hne1' : (τ : Perm (Fin 6)) ≠ 1 := fun h => hne1 (Subtype.ext h)
    obtain ⟨i, k, hi, hk, hik⟩ := exists_moved_ne _ hne1'
    obtain ⟨w, hw⟩ := hcsurj _ (sum_ev_add i k hk)
    apply pv_ev_ne _ i k hi hk hik
    rw [← hw, ← hcequiv, hτ]
    rfl
  have hinv : ∀ x : MulAut W, x ∈ H → x ≠ 1 → x * x = 1 →
      ∃ τ : ↥(alternatingGroup (Fin 6)), ((π τ : ↥H) : MulAut W) = x ∧
        IsInvA6 (τ : Perm (Fin 6)) := by
    intro x hxH hx1 hxx
    have hπs' : ∀ y : ↥H, ∃ τ : ↥(alternatingGroup (Fin 6)), π τ = y := hπs
    obtain ⟨τ, hτ⟩ := hπs' ⟨x, hxH⟩
    have hτx : ((π τ : ↥H) : MulAut W) = x := congrArg Subtype.val hτ
    refine ⟨τ, hτx, ?_, Perm.mem_alternatingGroup.mp τ.2, ?_⟩
    · have h0 : π τ * π τ = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hτx, hxx]; rfl)
      have h1 : π (τ * τ) = 1 := (MonoidHom.map_mul π τ τ).trans h0
      exact congrArg Subtype.val (hπi _ h1)
    · intro h1
      apply hx1
      rw [← hτx, show τ = 1 from Subtype.ext h1, map_one]
      rfl
  obtain ⟨τ₁, hτ₁, hσ₁⟩ := hinv x₁ hx₁H hx₁ hsq₁
  obtain ⟨τ₂, hτ₂, hσ₂⟩ := hinv x₂ hx₂H hx₂ hsq₂
  set σ₁ : Perm (Fin 6) := τ₁.1 with hσ₁def
  set σ₂ : Perm (Fin 6) := τ₂.1 with hσ₂def
  have hσne : σ₁ ≠ σ₂ := by
    intro h
    apply hne
    rw [← hτ₁, ← hτ₂, show τ₁ = τ₂ from Subtype.ext h]
  have hcomm : ∀ (τ : ↥(alternatingGroup (Fin 6))) (x : MulAut W),
      ((π τ : ↥H) : MulAut W) = x → x ∈ E → ∀ i j, j ≠ i → (τ : Perm (Fin 6)) j = j →
        ∃ a ∈ commV E, c a = ev i + ev ((τ : Perm (Fin 6)) i) := by
    intro τ x hτx hxE i j hji hj
    obtain ⟨u, hu⟩ := hcsurj _ (sum_ev_add i j hji)
    refine ⟨x u * u⁻¹, Subgroup.subset_closure ⟨x, hxE, u, rfl⟩, ?_⟩
    rw [hcmul, hcinv, ← hτx, hcequiv, hu]
    exact (sub_eq_add_neg _ _).symm.trans (pv_sub_ev _ i j hj)
  obtain ⟨j₁, hj₁⟩ := exists_fix_of_isInvA6 σ₁ hσ₁
  obtain ⟨j₂, hj₂⟩ := exists_fix_of_isInvA6 σ₂ hσ₂
  obtain ⟨i, k, hi, hk, hki, hkσ⟩ := exists_two_moved σ₁ hσ₁
  obtain ⟨i', hi', hσi'⟩ := exists_ne_of_isInvA6 σ₁ hσ₁ σ₂ hσ₂ hσne
  have hne_fix : ∀ (σ : Perm (Fin 6)) (a b : Fin 6), σ a ≠ a → σ b = b → b ≠ a :=
    fun σ a b ha hb hba => ha (hba ▸ hb)
  obtain ⟨a, haE, ha⟩ := hcomm τ₁ x₁ hτ₁ hx₁E i j₁ (hne_fix σ₁ i j₁ hi hj₁) hj₁
  obtain ⟨b, hbE, hb⟩ := hcomm τ₁ x₁ hτ₁ hx₁E k j₁ (hne_fix σ₁ k j₁ hk hj₁) hj₁
  obtain ⟨d, hdE, hd⟩ := hcomm τ₂ x₂ hτ₂ hx₂E i' j₂ (hne_fix σ₂ i' j₂ hi' hj₂) hj₂
  obtain ⟨h0a, h0b, hab, h0ab, haba, habb⟩ :=
    distinct_four i (σ₁ i) k (σ₁ k) hi hk hki hkσ
  have hga : Good σ₁ (ev i + ev (σ₁ i)) := good_ev σ₁ hσ₁.1 i
  have hgb : Good σ₁ (ev k + ev (σ₁ k)) := good_ev σ₁ hσ₁.1 k
  have hgd : ¬ Good σ₁ (ev i' + ev (σ₂ i')) :=
    not_good_ev σ₁ i' (σ₂ i') hi' hσi'
  let f : Fin 5 → ↥(commV E) :=
    ![1, ⟨a, haE⟩, ⟨b, hbE⟩, ⟨a * b, (commV E).mul_mem haE hbE⟩, ⟨d, hdE⟩]
  let g : Fin 5 → Fin 6 → ZMod 2 :=
    ![0, ev i + ev (σ₁ i), ev k + ev (σ₁ k), ev i + ev (σ₁ i) + (ev k + ev (σ₁ k)),
      ev i' + ev (σ₂ i')]
  have hfg : ∀ n, c (f n : W) = g n := by
    intro n
    fin_cases n
    · exact hcone
    · exact ha
    · exact hb
    · show c (a * b) = ev i + ev (σ₁ i) + (ev k + ev (σ₁ k))
      rw [hcmul, ha, hb]
    · exact hd
  have hg : Function.Injective g := by
    have hgd0 : ev i' + ev (σ₂ i') ≠ 0 := fun h => hgd (h ▸ good_zero σ₁)
    have hgda : ev i' + ev (σ₂ i') ≠ ev i + ev (σ₁ i) := fun h => hgd (h ▸ hga)
    have hgdb : ev i' + ev (σ₂ i') ≠ ev k + ev (σ₁ k) := fun h => hgd (h ▸ hgb)
    have hgdab : ev i' + ev (σ₂ i') ≠ ev i + ev (σ₁ i) + (ev k + ev (σ₁ k)) :=
      fun h => hgd (h ▸ good_add hga hgb)
    exact inj_five h0a.symm h0b.symm h0ab.symm hgd0.symm hab haba.symm hgda.symm habb.symm
      hgdb.symm hgdab.symm
  have hf : Function.Injective f := by
    intro n m hnm
    apply hg
    rw [← hfg, ← hfg, hnm]
  have h5 : 5 ≤ Nat.card (commV E) := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(commV E) := fun w => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hW _)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h5 ⊢
  by_contra hlt
  have hn2 : n ≤ 2 := by
    by_contra h3
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
  omega

end Card

end CFSG.Quasithin.MS93.S38EA
