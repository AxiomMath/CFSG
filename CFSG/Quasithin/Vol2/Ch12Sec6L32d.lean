module

public import CFSG.Quasithin.Vol2.Ch12Sec6Fin126f
public import CFSG.Quasithin.Vol2.Ch12Sec6L33e

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.LieType.BorelTits S126 S126P S126L1a
  S126L24 F126 L1233 Equiv

abbrev InSp (x y z : Fin 8 → ZMod 2) : Prop :=
  BC z ∨ BC (z + x) ∨ BC (z + y) ∨ BC (z + x + y)

abbrev wz (z : Fin 8 → ZMod 2) : ℕ := (Finset.univ.filter fun i => z i ≠ 0).card

abbrev NsW (z : Fin 8 → ZMod 2) : Prop := wz z = 2 ∨ wz (fun i => z i + 1) = 2

@[expose] def PtHyp (x : Fin 8 → ZMod 2) : Prop := S8 x = 0 ∧ Ev x ∧ ¬ BC x

instance (x : Fin 8 → ZMod 2) : Decidable (PtHyp x) := by
  unfold PtHyp; infer_instance

@[expose] def InvHyp (σ : Perm (Fin 8)) (x y : Fin 8 → ZMod 2) : Prop :=
  InSp x y (fun i => x (σ⁻¹ i)) ∧ InSp x y (fun i => y (σ⁻¹ i))

instance (σ : Perm (Fin 8)) (x y : Fin 8 → ZMod 2) : Decidable (InvHyp σ x y) := by
  unfold InvHyp; infer_instance

@[expose] def LineHyp (x y : Fin 8 → ZMod 2) : Prop :=
  PtHyp x ∧ PtHyp y ∧ ¬ BC (x + y) ∧ InvHyp aP x y ∧ InvHyp bP x y

instance (x y : Fin 8 → ZMod 2) : Decidable (LineHyp x y) := by
  unfold LineHyp; infer_instance

theorem check_line : ∀ x y : Fin 8 → ZMod 2, LineHyp x y → NsW x ∨ NsW y ∨ NsW (x + y) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem nonsing_of_nsW (F : Frame126 T L V) {v : G} (hv : v ∈ V) {m : ↥(coreMod 8)}
    (hm : F.β ⟨v, hv⟩ = QuotientGroup.mk m) (h : NsW (vx m)) : F.Nonsing v := by
  refine ⟨hv, ?_⟩
  rcases h with h | h
  · exact ⟨m, hm.symm, h⟩
  · refine ⟨m * ⟨allOnes 8, allOnes_mem⟩, (mk_mul_allOnes m allOnes_mem).trans hm.symm, ?_⟩
    exact h

omit [Finite G] in
theorem neg_vx_eq (z : Fin 8 → ZMod 2) : -z = z := by
  funext i
  exact ZMod.neg_eq_self_mod_two (z i)

omit [Finite G] in
theorem bc_of_secMk_eq (F : Frame126 T L V) {l v c : G} {σ : Perm (Fin 8)}
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) (hl : ActsAs F l σ) (hv : v ∈ V) (hc : c ∈ V)
    {m m' : ↥(coreMod 8)} (hm : F.β ⟨v, hv⟩ = QuotientGroup.mk m)
    (hm' : F.β ⟨c, hc⟩ = QuotientGroup.mk m') (h : (l * v * l⁻¹)⁻¹ * c ∈ F.V1) :
    BC ((fun i => vx m (σ⁻¹ i)) + vx m') := by
  set w : ↥V := ⟨l * v * l⁻¹, conj_mem hlV ⟨v, hv⟩⟩
  have hw := hl ⟨v, hv⟩ w rfl
  have h1 : ((w⁻¹ * ⟨c, hc⟩ : ↥V) : G) ∈ F.V1 := h
  rw [mem_V1_iff_beta, map_mul, map_inv, hw, hm, hm', dAct_mk, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, mem_W1_iff, vx_mul, vx_inv, vx_coreAct] at h1
  convert h1 using 2
  exact (neg_vx_eq _).symm

theorem exists_nonsing_mem (F : Frame126 T L V) (h : HypF91 T V L F.V1 F.V5 H)
    {A : Subgroup ↥(UT F.V1 F.V5 H)} (hA4 : Nat.card A = 4)
    (hA5 : ∀ w ∈ A, (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5)
    (hAinv : ∀ l (hl : l ∈ H), l ∈ Li L F.V1 → ∀ w ∈ A, thetaH h ⟨l, hl⟩ w ∈ A) :
    ∃ w ∈ A, w ≠ 1 ∧ ∃ (u : G) (hu : u ∈ N1 F.V1), u ∈ F.V5 ∧ F.Nonsing u ∧
      (w : SecQuot (N1 F.V1) F.V1) = secMk (N1 F.V1) F.V1 ⟨u, hu⟩ := by
  classical
  have : Fintype ↥(UT F.V1 F.V5 H) := Fintype.ofFinite _
  have hsq : ∀ w : ↥(UT F.V1 F.V5 H), w * w = 1 := fun w => by
    have := h.isElemAbelian_tilde.2 _ w.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, this]; rfl)
  obtain ⟨a₁, ha₁A, ha₁⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
    rw [this, Subgroup.card_bot] at hA4
    omega
  obtain ⟨a₂, ha₂A, ha₂, ha₂₁⟩ : ∃ a ∈ A, a ≠ 1 ∧ a ≠ a₁ := by
    by_contra hall
    push Not at hall
    have hinj : Function.Injective fun w : ↥A => decide ((w : ↥(UT F.V1 F.V5 H)) = a₁) := by
      intro w w' hww
      have h1 := hall w w.2
      have h2 := hall w' w'.2
      by_cases hw : (w : ↥(UT F.V1 F.V5 H)) = a₁
      · have : (w' : ↥(UT F.V1 F.V5 H)) = a₁ := by simpa [hw] using hww.symm
        exact Subtype.ext (hw.trans this.symm)
      · have : (w' : ↥(UT F.V1 F.V5 H)) ≠ a₁ := by simpa [hw] using hww.symm
        by_cases hw1 : (w : ↥(UT F.V1 F.V5 H)) = 1
        · by_cases hw1' : (w' : ↥(UT F.V1 F.V5 H)) = 1
          · exact Subtype.ext (hw1.trans hw1'.symm)
          · exact absurd (h2 hw1') this
        · exact absurd (h1 hw1) hw
    have := Nat.card_le_card_of_injective _ hinj
    rw [hA4, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    omega
  have ha₁₂ : a₁ * a₂ ≠ 1 := fun he => ha₂₁ (by
    calc a₂ = a₁ * (a₁ * a₂) := by rw [← mul_assoc, hsq, one_mul]
      _ = a₁ := by rw [he, mul_one])
  have hkey : ∀ w ∈ A, w = 1 ∨ w = a₁ ∨ w = a₂ ∨ w = a₁ * a₂ := by
    intro w hw
    by_contra hne
    push Not at hne
    obtain ⟨hw1, hwa1, hwa2, hwa12⟩ := hne
    have hs : ({1, a₁, a₂, a₁ * a₂, w} : Finset ↥(UT F.V1 F.V5 H)) ⊆
        Finset.univ.filter fun z => z ∈ A := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact A.one_mem
      · exact ha₁A
      · exact ha₂A
      · exact A.mul_mem ha₁A ha₂A
      · exact hw
    have h5 : ({1, a₁, a₂, a₁ * a₂, w} : Finset ↥(UT F.V1 F.V5 H)).card = 5 := by
      have e1 : a₁ * a₂ ≠ a₁ := fun he => ha₂ (by
        have := congrArg (a₁⁻¹ * ·) he
        simpa using this)
      have e2 : a₁ * a₂ ≠ a₂ := fun he => ha₁ (by
        have := congrArg (· * a₂⁻¹) he
        simpa using this)
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_pair hwa12.symm]
      · simp [hwa2.symm, e2.symm]
      · simp [ha₂₁.symm, hwa1.symm, Ne.symm e1]
      · simp [ha₁.symm, ha₂.symm, ha₁₂.symm, hw1.symm]
    have := Finset.card_le_card hs
    rw [h5, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hA4] at this
    omega
  have hVpV : F.V5 ≤ V := h.Vp_le_V
  obtain ⟨⟨v₁, hv₁N⟩, hv₁5, hv₁e⟩ := mem_secImg.1 (hA5 a₁ ha₁A)
  obtain ⟨⟨v₂, hv₂N⟩, hv₂5, hv₂e⟩ := mem_secImg.1 (hA5 a₂ ha₂A)
  have hv₁V : v₁ ∈ V := hVpV hv₁5
  have hv₂V : v₂ ∈ V := hVpV hv₂5
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (F.β ⟨v₁, hv₁V⟩)
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective (F.β ⟨v₂, hv₂V⟩)
  have hm₁₂ : F.β ⟨v₁ * v₂, V.mul_mem hv₁V hv₂V⟩ = QuotientGroup.mk (m₁ * m₂) := by
    rw [QuotientGroup.mk_mul, hm₁, hm₂, ← map_mul]
    rfl
  have hsec : ∀ (c : G) (hc : c ∈ N1 F.V1), (secMk (N1 F.V1) F.V1 ⟨c, hc⟩ = 1 ↔ c ∈ F.V1) :=
    fun c hc => secMk_eq_one_iff
  have hnb : ∀ (c : G) (hcV : c ∈ V) (m : ↥(coreMod 8)), F.β ⟨c, hcV⟩ = QuotientGroup.mk m →
      c ∉ F.V1 → ¬ BC (vx m) := by
    intro c hcV m hm hc hbc
    apply hc
    rw [show c = ((⟨c, hcV⟩ : ↥V) : G) from rfl, mem_V1_iff_beta, hm, mem_W1_iff]
    exact hbc
  have hev : ∀ (c : G) (hcV : c ∈ V) (m : ↥(coreMod 8)), F.β ⟨c, hcV⟩ = QuotientGroup.mk m →
      c ∈ F.V5 → Ev (vx m) := by
    intro c hcV m hm hc
    rw [show c = ((⟨c, hcV⟩ : ↥V) : G) from rfl, mem_V5_iff_beta, hm, mem_W5_iff] at hc
    exact hc
  have hA1 : (a₁ : SecQuot (N1 F.V1) F.V1) = secMk (N1 F.V1) F.V1 ⟨v₁, hv₁N⟩ := hv₁e.symm
  have hA2 : (a₂ : SecQuot (N1 F.V1) F.V1) = secMk (N1 F.V1) F.V1 ⟨v₂, hv₂N⟩ := hv₂e.symm
  have hv₁1 : v₁ ∉ F.V1 := fun hv => ha₁ (Subtype.ext (by rw [hA1, (hsec _ _).2 hv]; rfl))
  have hv₂1 : v₂ ∉ F.V1 := fun hv => ha₂ (Subtype.ext (by rw [hA2, (hsec _ _).2 hv]; rfl))
  have hv₁₂N : v₁ * v₂ ∈ N1 F.V1 := (N1 F.V1).mul_mem hv₁N hv₂N
  have hA12 : ((a₁ * a₂ : ↥(UT F.V1 F.V5 H)) : SecQuot (N1 F.V1) F.V1) =
      secMk (N1 F.V1) F.V1 ⟨v₁ * v₂, hv₁₂N⟩ := by
    rw [Subgroup.coe_mul, hA1, hA2, ← map_mul]
    rfl
  have hv₁₂1 : v₁ * v₂ ∉ F.V1 := fun hv => ha₁₂ (Subtype.ext (by
    rw [hA12, (hsec _ _).2 hv]; rfl))
  have hinv : ∀ σ : Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) → σ ^ 3 = 1 →
      (∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4)) → InvHyp σ (vx m₁) (vx m₂) := by
    intro σ hσ hσ3 hσb
    obtain ⟨l, hlL1, hlV, hl⟩ := S126L1b.exists_mem_L1 F hσ hσ3 hσb
    have hlH : l ∈ H := h.L₁T_le_H (Subgroup.mem_sup_left hlL1)
    have himg : ∀ (a : ↥(UT F.V1 F.V5 H)) (v : G) (hvN : v ∈ N1 F.V1) (hvV : v ∈ V)
        (m : ↥(coreMod 8)), F.β ⟨v, hvV⟩ = QuotientGroup.mk m →
        (a : SecQuot (N1 F.V1) F.V1) = secMk (N1 F.V1) F.V1 ⟨v, hvN⟩ → a ∈ A →
        InSp (vx m₁) (vx m₂) (fun i => vx m (σ⁻¹ i)) := by
      intro a v hvN hvV m hm ha haA
      have hmem := hAinv l hlH hlL1 a haA
      have hval : ((thetaH h ⟨l, hlH⟩ a : ↥(UT F.V1 F.V5 H)) : SecQuot (N1 F.V1) F.V1) =
          secMk (N1 F.V1) F.V1 ⟨l * v * l⁻¹, (N1 F.V1).mul_mem ((N1 F.V1).mul_mem
            (le_N1 h hlH) hvN) ((N1 F.V1).inv_mem (le_N1 h hlH))⟩ := by
        rw [thetaH_apply, ha]
        exact thetaH_apply_secMk h ⟨l, hlH⟩ hvN
      have hcase : ∀ (c : G) (hcN : c ∈ N1 F.V1) (hcV : c ∈ V) (m' : ↥(coreMod 8)),
          F.β ⟨c, hcV⟩ = QuotientGroup.mk m' →
          ((thetaH h ⟨l, hlH⟩ a : ↥(UT F.V1 F.V5 H)) : SecQuot (N1 F.V1) F.V1) =
            secMk (N1 F.V1) F.V1 ⟨c, hcN⟩ →
          BC ((fun i => vx m (σ⁻¹ i)) + vx m') := by
        intro c hcN hcV m' hm' he
        rw [hval, secMk_eq_secMk_iff] at he
        exact bc_of_secMk_eq F hlV hl hvV hcV hm hm' he
      rcases hkey _ hmem with h1 | h1 | h1 | h1
      · left
        have h1' : ((thetaH h ⟨l, hlH⟩ a : ↥(UT F.V1 F.V5 H)) : SecQuot (N1 F.V1) F.V1) =
            secMk (N1 F.V1) F.V1 ⟨1, (N1 F.V1).one_mem⟩ := by
          rw [h1]
          exact (map_one _).symm
        have := hcase 1 _ V.one_mem 1 ((map_one F.β).trans (QuotientGroup.mk_one _).symm) h1'
        rwa [vx_one, add_zero] at this
      · right; left
        exact hcase v₁ hv₁N hv₁V m₁ hm₁.symm (by rw [h1, hA1])
      · right; right; left
        exact hcase v₂ hv₂N hv₂V m₂ hm₂.symm (by rw [h1, hA2])
      · right; right; right
        have := hcase (v₁ * v₂) hv₁₂N (V.mul_mem hv₁V hv₂V) (m₁ * m₂) hm₁₂ (by rw [h1, hA12])
        rwa [vx_mul, ← add_assoc] at this
    exact ⟨himg a₁ v₁ hv₁N hv₁V m₁ hm₁.symm hA1 ha₁A, himg a₂ v₂ hv₂N hv₂V m₂ hm₂.symm hA2 ha₂A⟩
  have hline : LineHyp (vx m₁) (vx m₂) := by
    refine ⟨⟨sum8 m₁, hev v₁ hv₁V m₁ hm₁.symm hv₁5, hnb v₁ hv₁V m₁ hm₁.symm hv₁1⟩,
      ⟨sum8 m₂, hev v₂ hv₂V m₂ hm₂.symm hv₂5, hnb v₂ hv₂V m₂ hm₂.symm hv₂1⟩, ?_,
      hinv aP aP_mem aP_pow_three aP_block, hinv bP bP_mem bP_pow_three bP_block⟩
    have := hnb (v₁ * v₂) (V.mul_mem hv₁V hv₂V) (m₁ * m₂) hm₁₂ hv₁₂1
    rwa [vx_mul] at this
  rcases check_line _ _ hline with hx | hx | hx
  · exact ⟨a₁, ha₁A, ha₁, v₁, hv₁N, hv₁5, nonsing_of_nsW F hv₁V hm₁.symm hx, hA1⟩
  · exact ⟨a₂, ha₂A, ha₂, v₂, hv₂N, hv₂5, nonsing_of_nsW F hv₂V hm₂.symm hx, hA2⟩
  · refine ⟨a₁ * a₂, A.mul_mem ha₁A ha₂A, ha₁₂, v₁ * v₂, hv₁₂N, F.V5.mul_mem hv₁5 hv₂5,
      nonsing_of_nsW F (V.mul_mem hv₁V hv₂V) hm₁₂ (by rwa [vx_mul]), hA12⟩

end CFSG.Quasithin.H13.L1232
