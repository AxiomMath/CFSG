module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aLiftX
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LiftData
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.BtDichotomy

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec21.FF81.Lift
open CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem (exists_of_mem_A)

private theorem b2_elemAbelian {G : Type} [Group G] [Finite G]
    {b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ : G}
    (D : Data b b₁ b₂ b₃) (M : Mono b b₁ b₂ b₃ τ ι₁ ι₂ ι₃ σ₁₂ σ₂₃ γ)
    (hirr : ∀ H : Subgroup G, H ≤ BO b₁ b₂ b₃ → H ≠ ⊥ →
      (∀ g ∈ ({ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ} : Set G), ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        H = BO b₁ b₂ b₃)
    (hN3 : ∀ R : Subgroup G, R ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) →
      IsPGroup 3 R → Nat.card R ≤ 3 ^ 8)
    (hbt : ∀ hb : b ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) →
      (∃ t ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
        t * b * t⁻¹ = b⁻¹ ∧ ∀ y ∈ BO b₁ b₂ b₃, t * y * t⁻¹ = y) ∨
      ∃ K NL : Subgroup G, Compl b b₁ b₂ b₃ K NL)
    (hbG : b ∈ commutator G) :
    ∃ E : Subgroup G, E ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  set N := Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) with hNdef
  set B₁ := BO b₁ b₂ b₃ with hB₁def
  set Â := Ahat (BO b₁ b₂ b₃) b with hÂdef
  have hBp : IsPGroup 3 ↥((BB b b₁ b₂ b₃).subgroupOf Â) := D.isPGroup_B.comap_subtype
  obtain ⟨S, hSle⟩ := hBp.exists_le_sylow
  have hS : BB b b₁ b₂ b₃ ≤ (S : Subgroup ↥Â).map Â.subtype := fun z hz =>
    ⟨⟨z, D.B_le_Ahat hz⟩, hSle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  set A0 := (S : Subgroup ↥Â).map Â.subtype with hA0def
  have hÂ : ∀ {x}, x ∈ A0 → x ∈ Â := fun hx => D.A0_le hS hx
  obtain ⟨hτN, hτb⟩ := M.mem τ (by simp)
  obtain ⟨hι₁N, hι₁b⟩ := M.mem ι₁ (by simp)
  obtain ⟨hι₂N, hι₂b⟩ := M.mem ι₂ (by simp)
  obtain ⟨hι₃N, hι₃b⟩ := M.mem ι₃ (by simp)
  obtain ⟨hσ₁₂N, hσ₁₂b⟩ := M.mem σ₁₂ (by simp)
  obtain ⟨hσ₂₃N, hσ₂₃b⟩ := M.mem σ₂₃ (by simp)
  obtain ⟨hγN, hγb⟩ := M.mem γ (by simp)
  obtain ⟨τ', hτ'N, hτ'B, hτ'A⟩ := D.exists_translate' hS hτN
  obtain ⟨ι₁', hι₁'N, hι₁'B, hι₁'A⟩ := D.exists_translate' hS hι₁N
  obtain ⟨ι₂', hι₂'N, hι₂'B, hι₂'A⟩ := D.exists_translate' hS hι₂N
  obtain ⟨ι₃', hι₃'N, hι₃'B, hι₃'A⟩ := D.exists_translate' hS hι₃N
  obtain ⟨σ₁₂', hσ₁₂'N, hσ₁₂'B, hσ₁₂'A⟩ := D.exists_translate' hS hσ₁₂N
  obtain ⟨σ₂₃', hσ₂₃'N, hσ₂₃'B, hσ₂₃'A⟩ := D.exists_translate' hS hσ₂₃N
  obtain ⟨γ', hγ'N, hγ'B, hγ'A⟩ := D.exists_translate' hS hγN
  have hb := D.b_mem_B
  have h₁ : b₁ ∈ BB b b₁ b₂ b₃ := D.B₁_le_B D.mem₁
  have h₂ : b₂ ∈ BB b b₁ b₂ b₃ := D.B₁_le_B D.mem₂
  have h₃ : b₃ ∈ BB b b₁ b₂ b₃ := D.B₁_le_B D.mem₃
  obtain ⟨hAab, hA3⟩ := D.comm_cube_A0 hS (t₁ := ι₁') (t₂ := ι₂') (t₃ := ι₃')
    (by
      rintro t (rfl | rfl | rfl)
      · exact ⟨hι₁'N, by rw [hι₁'B b hb, hι₁b], hι₁'A⟩
      · exact ⟨hι₂'N, by rw [hι₂'B b hb, hι₂b], hι₂'A⟩
      · exact ⟨hι₃'N, by rw [hι₃'B b hb, hι₃b], hι₃'A⟩)
    ⟨by rw [hι₁'B _ h₁, M.s₁.1], by rw [hι₁'B _ h₂, M.s₁.2.1], by rw [hι₁'B _ h₃, M.s₁.2.2]⟩
    ⟨by rw [hι₂'B _ h₁, M.s₂.1], by rw [hι₂'B _ h₂, M.s₂.2.1], by rw [hι₂'B _ h₃, M.s₂.2.2]⟩
    ⟨by rw [hι₃'B _ h₁, M.s₃.1], by rw [hι₃'B _ h₂, M.s₃.2.1], by rw [hι₃'B _ h₃, M.s₃.2.2]⟩
  have hτinv : ∀ y ∈ B₁, τ * y * τ⁻¹ = y⁻¹ := conj_inv_of_closure D.B₁ab (by
    rintro s (rfl | rfl | rfl)
    exacts [M.inv.1, M.inv.2.1, M.inv.2.2])
  obtain ⟨m, hm, hτ₂p⟩ := exists_odd_pow_two τ'
  set τ₂ := τ' ^ m with hτ₂def
  have hτ₂N : τ₂ ∈ N := pow_mem hτ'N m
  have hτ₂A : ∀ x ∈ A0, τ₂ * x * τ₂⁻¹ ∈ A0 := pow_conj_mem hτ'A m
  have hτ₂b : τ₂ * b * τ₂⁻¹ = b := pow_conj_fix (by rw [hτ'B b hb, hτb]) m
  have hτ₂inv : ∀ y ∈ B₁, τ₂ * y * τ₂⁻¹ = y⁻¹ := fun y hy =>
    pow_conj_inv (by rw [hτ'B y (D.B₁_le_B hy), hτinv y hy]) hm
  have hτ₂sq : ∀ x ∈ A0, τ₂ * (τ₂ * x * τ₂⁻¹) * τ₂⁻¹ = x := by
    intro x hx
    have hδ : τ₂ ^ 2 ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
      refine D.mem_cen_of_gens fun z hz => ?_
      have e : τ₂ ^ 2 * z * (τ₂ ^ 2)⁻¹ = τ₂ * (τ₂ * z * τ₂⁻¹) * τ₂⁻¹ := by
        rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
      rw [e]
      rcases hz with rfl | rfl | rfl | rfl
      · rw [hτ₂b, hτ₂b]
      · rw [hτ₂inv _ D.mem₁, show τ₂ * z⁻¹ * τ₂⁻¹ = (τ₂ * z * τ₂⁻¹)⁻¹ by group,
          hτ₂inv _ D.mem₁, inv_inv]
      · rw [hτ₂inv _ D.mem₂, show τ₂ * z⁻¹ * τ₂⁻¹ = (τ₂ * z * τ₂⁻¹)⁻¹ by group,
          hτ₂inv _ D.mem₂, inv_inv]
      · rw [hτ₂inv _ D.mem₃, show τ₂ * z⁻¹ * τ₂⁻¹ = (τ₂ * z * τ₂⁻¹)⁻¹ by group,
          hτ₂inv _ D.mem₃, inv_inv]
    have h2p : IsPGroup 2 (Subgroup.zpowers (τ₂ ^ 2)) :=
      hτ₂p.to_le (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers _) 2))
    have := D.cen_two hS hδ (pow_conj_mem hτ₂A 2) h2p hx
    calc τ₂ * (τ₂ * x * τ₂⁻¹) * τ₂⁻¹ = τ₂ ^ 2 * x * (τ₂ ^ 2)⁻¹ := by
          rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
      _ = x := this
  have H : CFSG.RankThree.PartTwo.Sec21.FF81.B2Construct.Hyp A0 B₁ b τ₂ :=
    { B₁A := D.B₁_le_B.trans hS
      bA := hS hb
      B₁n := fun x hx y hy => by rw [(hÂ hx).1 y hy]; exact hy
      Aab := hAab
      A3 := hA3
      B₁3 := D.B₁3
      b3 := D.b3
      bB₁ := D.b_not_mem
      τ2 := hτ₂sq
      τA := hτ₂A
      τB₁ := hτ₂inv
      τb := hτ₂b
      fix := by
        intro x hx hfx
        have h1 : beta b (τ₂ * x * τ₂⁻¹) = (beta b x)⁻¹ := by
          rw [beta_conj hτ₂b, hτ₂inv _ (beta_mem (hÂ hx))]
        have h2 : beta b (τ₂ * x * τ₂⁻¹) = beta b x := by
          have e : τ₂ * x * τ₂⁻¹ = (τ₂ * x * τ₂⁻¹ * x⁻¹) * x := by group
          rw [e, beta_mul D.B₁ab (D.B_le_Ahat (D.B₁_le_B hfx)) (hÂ hx),
            beta_one_of_mem D.bB₁ hfx, one_mul]
        have h3 : beta b x = 1 :=
          D.eq_one_of_eq_inv (D.B₁3 _ (beta_mem (hÂ hx))) (h1.symm.trans h2)
        rw [← D.B_eq_sup]
        exact D.mem_B_of_mem_A0 hS hx h3 }
  set B₂ := H.B₂ with hB₂def
  have hB₂A : B₂ ≤ A0 := H.le_A
  have hnorm : ∀ g ∈ N, (∀ x ∈ A0, g * x * g⁻¹ ∈ A0) →
      (g⁻¹ * τ₂ * g) * τ₂⁻¹ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) →
      ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := by
    intro g hg hgA hδ x hx
    have hgA' : ∀ x ∈ A0, g⁻¹ * x * g⁻¹⁻¹ ∈ A0 := by
      have hgn := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem hgA
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem hgn) y).mp hy
    have hτ₂A' : ∀ x ∈ A0, τ₂⁻¹ * x * τ₂⁻¹⁻¹ ∈ A0 := by
      have hgn := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem hτ₂A
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem hgn) y).mp hy
    refine H.conj_mem (fun y hy => hgA y hy) (fun y hy => D.B₁N g hg y hy) (fun y hy => ?_) hx
    have hδA : ∀ x ∈ A0, ((g⁻¹ * τ₂ * g) * τ₂⁻¹) * x * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ ∈ A0 := by
      intro z hz
      have e : ((g⁻¹ * τ₂ * g) * τ₂⁻¹) * z * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ =
          g⁻¹ * (τ₂ * (g * (τ₂⁻¹ * z * τ₂⁻¹⁻¹) * g⁻¹) * τ₂⁻¹) * g⁻¹⁻¹ := by group
      rw [e]
      exact hgA' _ (hτ₂A _ (hgA _ (hτ₂A' _ hz)))
    have e : (g⁻¹ * τ₂ * g) * y * (g⁻¹ * τ₂ * g)⁻¹ * (τ₂ * y * τ₂⁻¹)⁻¹ =
        ((g⁻¹ * τ₂ * g) * τ₂⁻¹) * (τ₂ * y * τ₂⁻¹) * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ *
          (τ₂ * y * τ₂⁻¹)⁻¹ := by group
    rw [e]
    exact D.comm_mem_of_cen hS hAab hδ hδA (hτ₂A y hy)
  have hδfix : ∀ g ∈ N, g * b * g⁻¹ = b →
      (g⁻¹ * τ₂ * g) * τ₂⁻¹ ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
    intro g hg hgb
    have hg' : g⁻¹ ∈ N := inv_mem hg
    have hgib : g⁻¹ * b * g⁻¹⁻¹ = b := by
      calc g⁻¹ * b * g⁻¹⁻¹ = g⁻¹ * (g * b * g⁻¹) * g⁻¹⁻¹ := by rw [hgb]
        _ = b := by group
    have hτ₂inv' : ∀ y ∈ B₁, τ₂⁻¹ * y * τ₂⁻¹⁻¹ = y⁻¹ := by
      intro y hy
      have h := hτ₂inv y⁻¹ (inv_mem hy)
      rw [inv_inv] at h
      calc τ₂⁻¹ * y * τ₂⁻¹⁻¹ = τ₂⁻¹ * (τ₂ * y⁻¹ * τ₂⁻¹) * τ₂⁻¹⁻¹ := by rw [h]
        _ = y⁻¹ := by group
    refine D.mem_cen_of_gens fun z hz => ?_
    have e : (g⁻¹ * τ₂ * g) * τ₂⁻¹ * z * ((g⁻¹ * τ₂ * g) * τ₂⁻¹)⁻¹ =
        g⁻¹ * (τ₂ * (g * (τ₂⁻¹ * z * τ₂⁻¹⁻¹) * g⁻¹) * τ₂⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    rcases hz with rfl | hz
    · have : τ₂⁻¹ * z * τ₂⁻¹⁻¹ = z := by
        calc τ₂⁻¹ * z * τ₂⁻¹⁻¹ = τ₂⁻¹ * (τ₂ * z * τ₂⁻¹) * τ₂ := by rw [hτ₂b, inv_inv]
          _ = z := by group
      rw [this, hgb, hτ₂b, hgib]
    · have hzB : z ∈ B₁ := Subgroup.subset_closure hz
      rw [hτ₂inv' z hzB, show g * z⁻¹ * g⁻¹ = (g * z * g⁻¹)⁻¹ by group,
        show τ₂ * (g * z * g⁻¹)⁻¹ * τ₂⁻¹ = (τ₂ * (g * z * g⁻¹) * τ₂⁻¹)⁻¹ by group,
        hτ₂inv _ (D.B₁N g hg z hzB), inv_inv]
      group
  have hfixnorm : ∀ g ∈ N, (∀ x ∈ A0, g * x * g⁻¹ ∈ A0) → g * b * g⁻¹ = b →
      ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := fun g hg hgA hgb =>
    hnorm g hg hgA (hδfix g hg hgb)
  have hγ'b : γ' * b * γ'⁻¹ = b := by rw [hγ'B b hb, hγb]
  obtain ⟨n₀, hcp, hcb, hc₁, hc₂, hc₃⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exists_pow_isPGroup hγ'b
      (by rw [hγ'B _ h₁, M.cyc.1]) (by rw [hγ'B _ h₂, M.cyc.2.1]) (by rw [hγ'B _ h₃, M.cyc.2.2])
  set c := γ' ^ n₀ with hcdef
  have hcN : c ∈ N := pow_mem hγ'N n₀
  have hcA : ∀ x ∈ A0, c * x * c⁻¹ ∈ A0 := pow_conj_mem hγ'A n₀
  have hcB₂ : ∀ x ∈ B₂, c * x * c⁻¹ ∈ B₂ := hfixnorm c hcN hcA hcb
  have hc3 : c ^ 3 ∈ Subgroup.zpowers b ⊔ B₂ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.cube_mem_A H.B₁_le hcb hc₁ hc₂ hc₃ hcp D.CB
  have hsup : Subgroup.zpowers b ⊔ B₂ = A0 := H.sup_eq
  have hcardA := D.card_A0 hS
  have hB₂card : Nat.card B₂ = 3 ^ 6 := by
    have h : Nat.card A0 = 3 * Nat.card B₂ := H.card_A
    rw [hcardA] at h
    norm_num at h ⊢
    omega
  have hPp : IsPGroup 3 ↥(A0 ⊔ Subgroup.zpowers c : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (D.isPGroup_A0 hS) hcp
      ((Subgroup.zpowers_le).2
        (CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem hcA))
  have hPcard : 3 ^ 8 ≤ Nat.card ↥(A0 ⊔ Subgroup.zpowers c : Subgroup G) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have hdvd : 3 ^ 7 ∣ 3 ^ k := by
      rw [← hk, ← hcardA]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h7 : 7 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have hne : k ≠ 7 := by
      intro hk7
      have heq : A0 = A0 ⊔ Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, hk7, hcardA])
      have hcA0 : c ∈ A0 := by
        rw [heq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
      have := (hÂ hcA0).1 b₁ D.mem₁
      rw [hc₁] at this
      exact D.b₁_ne_b₂ this.symm
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPmax : ∀ R : Subgroup G, R ≤ N → IsPGroup 3 R →
      Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c ≤ R →
      R = Subgroup.zpowers b ⊔ B₂ ⊔ Subgroup.zpowers c := by
    intro R hRN hRp hPR
    rw [hsup] at hPR ⊢
    exact (Subgroup.eq_of_le_of_card_ge hPR ((hN3 R hRN hRp).trans hPcard)).symm
  have hSetup := H.toSetup (b₁ := b₁) (b₂ := b₂) (b₃ := b₃) (c := c) rfl D.Bab D.B3 D.Bcard
    D.B₁card ((D.A0_le hS).trans D.Ahat_le_N) hcN hcb hc₁ hc₂ hc₃ hcB₂ hc3 hPmax
  have hB₂p : IsPGroup 3 B₂ := (D.isPGroup_A0 hS).to_le hB₂A
  have hker : ∀ x ∈ B₂, x * b = b * x → x ∈ B₁ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.RankFour.ker_of_cenS H.B₁_le H.inv_comm.2 hB₂p
      (fun x hx hx2 => H.mem_B₁_of_mem_sup (by rw [← D.B_eq_sup]; exact hx) hx2) D.CB
  set T : Set G := {ι₁', ι₂', ι₃', σ₁₂', σ₂₃', γ'} with hTdef
  have hT : ∀ g ∈ T, ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := by
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hfixnorm _ hι₁'N hι₁'A (by rw [hι₁'B b hb, hι₁b])
    · exact hfixnorm _ hι₂'N hι₂'A (by rw [hι₂'B b hb, hι₂b])
    · exact hfixnorm _ hι₃'N hι₃'A (by rw [hι₃'B b hb, hι₃b])
    · exact hfixnorm _ hσ₁₂'N hσ₁₂'A (by rw [hσ₁₂'B b hb, hσ₁₂b])
    · exact hfixnorm _ hσ₂₃'N hσ₂₃'A (by rw [hσ₂₃'B b hb, hσ₂₃b])
    · exact hfixnorm _ hγ'N hγ'A hγ'b
  have hTb : ∀ g ∈ T, g * b * g⁻¹ = b := by
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [hι₁'B b hb, hι₁b]
    · rw [hι₂'B b hb, hι₂b]
    · rw [hι₃'B b hb, hι₃b]
    · rw [hσ₁₂'B b hb, hσ₁₂b]
    · rw [hσ₂₃'B b hb, hσ₂₃b]
    · exact hγ'b
  have hB₁irr : ∀ K : Subgroup G, K ≤ B₁ → K ≠ ⊥ → (∀ g ∈ T, ∀ x ∈ K, g * x * g⁻¹ ∈ K) →
      K = B₁ := by
    intro K hKB₁ hK hKT
    refine hirr K hKB₁ hK ?_
    have tr : ∀ {g g' : G}, (∀ z ∈ BB b b₁ b₂ b₃, g' * z * g'⁻¹ = g * z * g⁻¹) → g' ∈ T →
        ∀ x ∈ K, g * x * g⁻¹ ∈ K := fun hg'B hg'T x hx => by
      rw [← hg'B x (D.B₁_le_B (hKB₁ hx))]
      exact hKT _ hg'T x hx
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact tr hι₁'B (by simp [hTdef])
    · exact tr hι₂'B (by simp [hTdef])
    · exact tr hι₃'B (by simp [hTdef])
    · exact tr hσ₁₂'B (by simp [hTdef])
    · exact tr hσ₂₃'B (by simp [hTdef])
    · exact tr hγ'B (by simp [hTdef])
  have hirr' := CFSG.RankThree.PartTwo.Sec21.FF81.RankFour.irreducible_of_kappa H.B₁_le
    H.inv_comm.2 (fun x hx => H.bB₂ hx) (fun y hy => (D.bB₁ y hy).symm) hker hTb hB₁irr
  have hA0N : A0 ≤ N := (D.A0_le hS).trans D.Ahat_le_N
  have hB₂N : B₂ ≤ N := hB₂A.trans hA0N
  have hno : ∀ (K NL : Subgroup G), Compl b b₁ b₂ b₃ K NL →
      ∀ hb : b ∈ N, (⟨b, hb⟩ : ↥N) ∉ commutator ↥N := by
    intro K NL C hbN hmem
    have hKA : ∀ k ∈ K, k ∈ A0 → k = 1 := by
      intro k hk hkA
      obtain ⟨e, he⟩ := (D.isPGroup_A0 hS) ⟨k, hkA⟩
      have hke : k ^ (3 ^ e) = 1 := by simpa using congrArg Subtype.val he
      have h1 : orderOf k ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hke
      have h2 : orderOf k ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hk
      have hcop : Nat.Coprime (orderOf k) 3 := Nat.Coprime.coprime_dvd_left h2 C.K3
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
      have hi0 : i = 0 := by
        by_contra hi0
        rw [hi] at hcop
        exact absurd (Nat.Coprime.coprime_dvd_left (dvd_pow_self 3 hi0) hcop) (by decide)
      rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
      exact hi
    have hKn : ∀ g ∈ N, g ∈ Subgroup.normalizer (K : Set G) := fun g hg =>
      CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem (C.KN g hg)
    have hB₂N : B₂ ≤ N := hB₂A.trans hA0N
    have hBK : ∀ z ∈ BB b b₁ b₂ b₃ ⊔ K, ∃ y ∈ BB b b₁ b₂ b₃, ∃ k ∈ K, y * k = z := by
      intro z hz
      have h := Subgroup.coe_mul_of_left_le_normalizer_right (BB b b₁ b₂ b₃) K
        (fun y hy => hKn y (D.Ahat_le_N (D.B_le_Ahat hy)))
      have hz' : z ∈ ((BB b b₁ b₂ b₃ ⊔ K : Subgroup G) : Set G) := hz
      rw [h] at hz'
      obtain ⟨y, hy, k, hk, hyk⟩ := hz'
      exact ⟨y, hy, k, hk, hyk⟩
    have hÂdec : ∀ a ∈ Â, ∃ x ∈ A0, ∃ k ∈ K, a = x * k := by
      intro a ha
      obtain ⟨x, hx, hxa⟩ := D.exists_beta_eq hS (beta_mem ha)
      have hc : x⁻¹ * a ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
        refine D.mem_cen_of_beta (mul_mem (inv_mem (hÂ hx)) ha) ?_
        rw [beta_mul D.B₁ab (inv_mem (hÂ hx)) ha, D.beta_inv (hÂ hx), hxa, inv_mul_cancel]
      obtain ⟨z, hz, k, hk, hzk⟩ := hBK _ (C.CK hc)
      exact ⟨x * z, mul_mem hx (hS hz), k, hk, by rw [mul_assoc, hzk, mul_inv_cancel_left]⟩
    have hNdec : ∀ g ∈ N, ∃ x ∈ A0, ∃ k ∈ K, ∃ l ∈ NL, g = x * k * l := by
      intro g hg
      obtain ⟨l, hl, hgl⟩ := C.gen g hg
      obtain ⟨x, hx, k, hk, hxk⟩ := hÂdec _ hgl
      exact ⟨x, hx, k, hk, l, hl, by rw [← hxk, inv_mul_cancel_right]⟩
    set M₀ := B₂ ⊔ K with hM₀
    have hA0M₀ : ∀ x ∈ A0, ∀ m ∈ M₀, x * m * x⁻¹ ∈ M₀ := by
      intro x hx
      have hle : M₀.map (MulAut.conj x).toMonoidHom ≤ M₀ := by
        rw [hM₀, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          refine Subgroup.mem_sup_left ?_
          show x * y * x⁻¹ ∈ B₂
          have hw : x * y * x⁻¹ * y⁻¹ ∈ B₁ := hAab x hx y (hB₂A hy)
          have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
          rw [e]
          exact mul_mem (H.B₁_le hw) hy
        · rintro _ ⟨k, hk, rfl⟩
          exact Subgroup.mem_sup_right (C.KN x (hA0N hx) k hk)
      intro m hm
      exact hle ⟨m, hm, rfl⟩
    have hKM₀ : ∀ k ∈ K, ∀ m ∈ M₀, k * m * k⁻¹ ∈ M₀ := fun k hk m hm =>
      mul_mem (mul_mem (Subgroup.mem_sup_right hk) hm) (inv_mem (Subgroup.mem_sup_right hk))
    have hconjB₂ : ∀ g ∈ N, ∀ y ∈ B₂, g * y * g⁻¹ ∈ M₀ := by
      intro g hg y hy
      obtain ⟨x, hx, k, hk, l, hl, rfl⟩ := hNdec g hg
      obtain ⟨k₁, hk₁, hk₁A⟩ := D.exists_translate_cen hS (C.NLN hl)
      have hl'N : k₁⁻¹ * l ∈ N := mul_mem (inv_mem (D.cen_le_N hk₁)) (C.NLN hl)
      have hl'b : (k₁⁻¹ * l) * b * (k₁⁻¹ * l)⁻¹ = b := by
        rw [D.translate_conj hk₁ (by rw [C.NLb l hl]; exact hb), C.NLb l hl]
      have hy₁ : (k₁⁻¹ * l) * y * (k₁⁻¹ * l)⁻¹ ∈ B₂ := hfixnorm _ hl'N hk₁A hl'b y hy
      obtain ⟨z, hz, k₂, hk₂, hzk⟩ := hBK _ (C.CK hk₁)
      have e : x * k * l * y * (x * k * l)⁻¹ =
          x * (k * (z * (k₂ * ((k₁⁻¹ * l) * y * (k₁⁻¹ * l)⁻¹) * k₂⁻¹) * z⁻¹) * k⁻¹) * x⁻¹ := by
        rw [← hzk]
        group
      rw [e]
      exact hA0M₀ x hx _ (hKM₀ k hk _ (hA0M₀ z (hS hz) _
        (hKM₀ k₂ hk₂ _ (Subgroup.mem_sup_left hy₁))))
    have hNM₀ : ∀ g ∈ N, ∀ m ∈ M₀, g * m * g⁻¹ ∈ M₀ := by
      intro g hg
      have hle : M₀.map (MulAut.conj g).toMonoidHom ≤ M₀ := by
        rw [hM₀, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          exact hconjB₂ g hg y hy
        · rintro _ ⟨k, hk, rfl⟩
          exact Subgroup.mem_sup_right (C.KN g hg k hk)
      intro m hm
      exact hle ⟨m, hm, rfl⟩
    set M := M₀ ⊔ NL with hMdef
    have hA0M : ∀ x ∈ A0, ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
      intro x hx
      have hle : M.map (MulAut.conj x).toMonoidHom ≤ M := by
        rw [hMdef, Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨m, hm, rfl⟩
          exact Subgroup.mem_sup_left (hA0M₀ x hx m hm)
        · rintro _ ⟨l, hl, rfl⟩
          show x * l * x⁻¹ ∈ M
          have hxA : x ∈ Subgroup.zpowers b ⊔ B₂ := by rw [hsup]; exact hx
          obtain ⟨j, -, y, hy, rfl⟩ := exists_of_mem_A D.b3 (fun z hz => H.b_conj_mem hz) hxA
          have hlN := C.NLN hl
          have hlb := C.NLb l hl
          have h1 : l * y⁻¹ * l⁻¹ ∈ M₀ := hconjB₂ l hlN _ (inv_mem hy)
          have h2 : y * (l * y⁻¹ * l⁻¹) ∈ M₀ := mul_mem (Subgroup.mem_sup_left hy) h1
          have h3 := hA0M₀ (b ^ j) (pow_mem (hS hb) j) _ h2
          have hlbj : l * b ^ j * l⁻¹ = b ^ j := by rw [← conj_pow, hlb]
          have e : b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹ =
              b ^ j * (y * (l * y⁻¹ * l⁻¹)) * (b ^ j)⁻¹ := by
            calc b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹
                = b ^ j * (y * (l * y⁻¹ * l⁻¹)) * (l * b ^ j * l⁻¹)⁻¹ := by group
              _ = b ^ j * (y * (l * y⁻¹ * l⁻¹)) * (b ^ j)⁻¹ := by rw [hlbj]
          have hcm : b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹ ∈ M₀ := by rw [e]; exact h3
          have e2 : b ^ j * y * l * (b ^ j * y)⁻¹ =
              (b ^ j * y * l * (b ^ j * y)⁻¹ * l⁻¹) * l := by group
          rw [e2]
          exact mul_mem (Subgroup.mem_sup_left hcm) (Subgroup.mem_sup_right hl)
      intro m hm
      exact hle ⟨m, hm, rfl⟩
    have hNM : ∀ g ∈ N, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
      intro g hg m hm
      obtain ⟨x, hx, k, hk, l, hl, rfl⟩ := hNdec g hg
      have hkM : k ∈ M := Subgroup.mem_sup_left (Subgroup.mem_sup_right hk)
      have hlM : l ∈ M := Subgroup.mem_sup_right hl
      have e : x * k * l * m * (x * k * l)⁻¹ = x * (k * l * m * (k * l)⁻¹) * x⁻¹ := by group
      rw [e]
      exact hA0M x hx _ (mul_mem (mul_mem (mul_mem hkM hlM) hm) (inv_mem (mul_mem hkM hlM)))
    have hMn : (M.subgroupOf N).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hNM g g.2 n hn⟩
    have hle : commutator ↥N ≤ M.subgroupOf N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g _ h _
      obtain ⟨x, hx, k, hk, l, hl, hg⟩ := hNdec g g.2
      obtain ⟨x', hx', k', hk', l', hl', hh⟩ := hNdec h h.2
      have hπ : ∀ (u : ↥N) (y : G) (hy : y ∈ A0) (k₀ : G) (_ : k₀ ∈ K) (l₀ : G) (_ : l₀ ∈ NL),
          (u : G) = y * k₀ * l₀ →
          (QuotientGroup.mk' (M.subgroupOf N) u) =
            QuotientGroup.mk' (M.subgroupOf N) ⟨y, hA0N hy⟩ := by
        intro u y hy k₀ hk₀ l₀ hl₀ hu
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        show (u : G)⁻¹ * y ∈ M
        rw [hu, show (y * k₀ * l₀)⁻¹ * y = (k₀ * l₀)⁻¹ * (y⁻¹ * y) by group, inv_mul_cancel,
          mul_one]
        exact inv_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right hk₀))
          (Subgroup.mem_sup_right hl₀))
      have key : QuotientGroup.mk' (M.subgroupOf N) (g * h * g⁻¹ * h⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπ g x hx k hk l hl hg,
          hπ h x' hx' k' hk' l' hl' hh, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        show x * x' * x⁻¹ * x'⁻¹ ∈ M
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (H.B₁_le (hAab x hx x' hx')))
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at key
      exact key
    have hbM : b ∈ M := Subgroup.mem_subgroupOf.mp (hle hmem)
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left M₀ NL
      (fun l hl => CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.mem_normalizer_of_conj_mem
        (hNM₀ l (C.NLN hl)))
    have hbM' : b ∈ ((M₀ ⊔ NL : Subgroup G) : Set G) := hbM
    rw [hcoe] at hbM'
    obtain ⟨m, hm, l, hl, hml⟩ := hbM'
    have hM₀Â : M₀ ≤ Â := sup_le (hB₂A.trans (D.A0_le hS)) (C.KC.trans D.cen_le_Ahat)
    have hlÂ : l ∈ Â := by
      have e : l = m⁻¹ * b := by rw [← hml, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem (hM₀Â hm)) (D.B_le_Ahat hb)
    have hlC : l ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
      refine D.mem_cen_of_beta hlÂ ?_
      rw [beta_def, C.NLb l hl, mul_inv_cancel]
    have hlB₁ : l ∈ B₁ := C.NLC ⟨hl, hlC⟩
    have hbM₀ : b ∈ M₀ := by
      rw [← hml]
      exact mul_mem hm (Subgroup.mem_sup_left (H.B₁_le hlB₁))
    have hcoe₂ := Subgroup.coe_mul_of_left_le_normalizer_right B₂ K
      (fun y hy => hKn y (hB₂N hy))
    have hbM₀' : b ∈ ((B₂ ⊔ K : Subgroup G) : Set G) := hbM₀
    rw [hcoe₂] at hbM₀'
    obtain ⟨y, hy, k, hk, hyk⟩ := hbM₀'
    have hkA : k ∈ A0 := by
      have e : k = y⁻¹ * b := by rw [← hyk, inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem (hB₂A hy)) (hS hb)
    have hk1 := hKA k hk hkA
    simp only [hk1, mul_one] at hyk
    rw [hyk] at hy
    exact D.b_not_mem (H.mem_B₁_of_mem_sup (by rw [← D.B_eq_sup]; exact hb) hy)
  have hbN' : ∀ hb : b ∈ N, (⟨b, hb⟩ : ↥N) ∈ commutator ↥N →
      ∃ s : G, s * b₁ * s⁻¹ = b₁⁻¹ ∧ ∀ x ∈ B₂, s * x * s⁻¹ * x⁻¹ ∈ B₁ := by
    intro hbN hmem
    obtain ⟨t, htN, htb, htB₁⟩ | ⟨K, NL, C⟩ := hbt hbN hmem
    swap
    · exact absurd hmem (hno K NL C hbN)
    have hs₀N : t * τ ∈ N := mul_mem htN hτN
    have hs₀inv : ∀ z ∈ BB b b₁ b₂ b₃, (t * τ) * z * (t * τ)⁻¹ = z⁻¹ := by
      refine conj_inv_of_closure D.Bab ?_
      intro z hz
      have e : (t * τ) * z * (t * τ)⁻¹ = t * (τ * z * τ⁻¹) * t⁻¹ := by group
      rw [e]
      rcases hz with rfl | hz
      · rw [hτb, htb]
      · have hzB : z ∈ B₁ := Subgroup.subset_closure hz
        rw [hτinv z hzB, show t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ by group, htB₁ z hzB]
    obtain ⟨s, hsN, hsB, hsA⟩ := D.exists_translate' hS hs₀N
    have hsinv : ∀ z ∈ BB b b₁ b₂ b₃, s * z * s⁻¹ = z⁻¹ := fun z hz => by
      rw [hsB z hz, hs₀inv z hz]
    have hsinv' : ∀ z ∈ BB b b₁ b₂ b₃, s⁻¹ * z * s⁻¹⁻¹ = z⁻¹ := by
      intro z hz
      have h := hsinv z⁻¹ (inv_mem hz)
      rw [inv_inv] at h
      calc s⁻¹ * z * s⁻¹⁻¹ = s⁻¹ * (s * z⁻¹ * s⁻¹) * s⁻¹⁻¹ := by rw [h]
        _ = z⁻¹ := by group
    have hδ : (s⁻¹ * τ₂ * s) * τ₂⁻¹ ∈
        Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
      refine D.mem_cen_of_gens fun z hz => ?_
      have hzB : z ∈ BB b b₁ b₂ b₃ := Subgroup.subset_closure hz
      have hz' : τ₂⁻¹ * z * τ₂⁻¹⁻¹ ∈ BB b b₁ b₂ b₃ := D.conj_mem_B (inv_mem hτ₂N) hzB
      have e : (s⁻¹ * τ₂ * s) * τ₂⁻¹ * z * ((s⁻¹ * τ₂ * s) * τ₂⁻¹)⁻¹ =
          s⁻¹ * (τ₂ * (s * (τ₂⁻¹ * z * τ₂⁻¹⁻¹) * s⁻¹) * τ₂⁻¹) * s⁻¹⁻¹ := by group
      rw [e, hsinv _ hz', show τ₂ * (τ₂⁻¹ * z * τ₂⁻¹⁻¹)⁻¹ * τ₂⁻¹ = z⁻¹ by group,
        hsinv' z⁻¹ (inv_mem hzB), inv_inv]
    have hsB₂ := hnorm s hsN hsA hδ
    refine ⟨s, by rw [hsinv _ h₁], fun x hx => ?_⟩
    have hxA := hB₂A hx
    have hsx : beta b (s * x * s⁻¹) = beta b x := by
      have hsb : s⁻¹ * b * s⁻¹⁻¹ = b⁻¹ := hsinv' b hb
      have e1 : beta b (s * x * s⁻¹) =
          s * (x * (s⁻¹ * b * s⁻¹⁻¹) * x⁻¹ * (s⁻¹ * b * s⁻¹⁻¹)⁻¹) * s⁻¹ := by
        rw [beta_def]; group
      rw [e1, hsb, inv_inv]
      have e2 : x * b⁻¹ * x⁻¹ * b = (beta b x)⁻¹ := by
        rw [beta_def]
        have hβc : Commute (x * b * x⁻¹ * b⁻¹) b :=
          (D.bB₁ _ (beta_mem (hÂ hxA))).symm
        calc x * b⁻¹ * x⁻¹ * b = b⁻¹ * ((x * b * x⁻¹ * b⁻¹)⁻¹ * b) := by group
          _ = b⁻¹ * (b * (x * b * x⁻¹ * b⁻¹)⁻¹) := by rw [hβc.inv_left.eq]
          _ = (x * b * x⁻¹ * b⁻¹)⁻¹ := by group
      rw [e2, hsinv _ (D.B₁_le_B (inv_mem (beta_mem (hÂ hxA)))), inv_inv]
    have hw : s * x * s⁻¹ * x⁻¹ ∈ BB b b₁ b₂ b₃ := by
      refine D.mem_B_of_mem_A0 hS (mul_mem (hsA x hxA) (inv_mem hxA)) ?_
      rw [beta_mul D.B₁ab (hÂ (hsA x hxA)) (inv_mem (hÂ hxA)), hsx, D.beta_inv (hÂ hxA),
        mul_inv_cancel]
    exact H.mem_B₁_of_mem_sup (by rw [← D.B_eq_sup]; exact hw)
      (mul_mem (hsB₂ x hx) (inv_mem hx))
  have hB₂3 := CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exp_three_of_irreducible' hSetup hT
    hirr' hB₂card hbN' hbG
  refine ⟨B₂, hB₂N, ?_, hB₂card⟩
  exact ⟨IsMulCommutative.of_setLike_mul_comm H.inv_comm.2, hB₂3⟩

theorem exists_elemAbelian_six {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hB₁ : ∀ m ∈ nB b z, ∀ y ∈ bOne z, m * y * m⁻¹ ∈ bOne z) :
    ∃ E : Subgroup G, E ≤ nB b z ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 := by
  let b₁ := GGFF.zs z 0
  let b₂ := GGFF.zs z 1
  let b₃ := GGFF.zs z 2
  have D : Data b b₁ b₂ b₃ := lift_data h hB₁
  obtain ⟨τ, ι₁, ι₂, ι₃, σ₁₂, σ₂₃, γ, _hL, M, hirr⟩ := exists_mono_irreducible h
  have hBB : (BB b b₁ b₂ b₃ : Subgroup G) = GGFF.Bt b z := by
    show Subgroup.closure ({b, b₁, b₂, b₃} : Set G) = GGFF.Bt b z
    rw [show ({b, b₁, b₂, b₃} : Set G) = {b, GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} from by
      ext x; simp [b₁, b₂, b₃]]
    exact (GGFF.SettingCore.Bt_eq_closure b z).symm
  have hmono : ∀ n ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) → ∀ x ∈ ({b₁, b₂, b₃} : Set G),
        n * x * n⁻¹ ∈ ({b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} : Set G) := by
    intro n hn hnb x hx
    have hn' : n ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G) := by
      rwa [hBB] at hn
    have hnb' : n * b * n⁻¹ ∈ Subgroup.zpowers b := by
      rcases hnb with h | h
      · rw [h]; exact Subgroup.mem_zpowers b
      · rw [h]; exact inv_mem (Subgroup.mem_zpowers b)
    have hsq : ∀ j : Fin 3, GGFF.zs z j ^ 2 = (GGFF.zs z j)⁻¹ := by
      intro j
      have := h.settingCore.zs_sq j
      rwa [show (2 : ZMod 3).val = 2 from rfl] at this
    have key : ∀ i : Fin 3, n * GGFF.zs z i * n⁻¹ ∈
        ({GGFF.zs z 0, (GGFF.zs z 0)⁻¹, GGFF.zs z 1, (GGFF.zs z 1)⁻¹,
          GGFF.zs z 2, (GGFF.zs z 2)⁻¹} : Set G) := by
      intro i
      obtain ⟨j, e, he, hje⟩ := h.facts.stab n hn' hnb' i
      rcases he with rfl | rfl
      · rw [pow_one] at hje
        rw [hje]
        fin_cases j <;> simp
      · rw [hsq j] at hje
        rw [hje]
        fin_cases j <;> simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact key 0
    · exact key 1
    · exact key 2
  have hτN : τ ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) :=
    (M.mem τ (by simp)).1
  have hτb : τ * b * τ⁻¹ = b := (M.mem τ (by simp)).2
  have hτ : ∀ y ∈ BO b₁ b₂ b₃, τ * y * τ⁻¹ = y⁻¹ := by
    refine conj_inv_of_closure D.B₁ab ?_
    rintro x (rfl | rfl | rfl)
    exacts [M.inv.1, M.inv.2.1, M.inv.2.2]
  have hN3 : ∀ R : Subgroup G, R ≤ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) →
      IsPGroup 3 R → Nat.card R ≤ 3 ^ 8 :=
    fun R hRN hR => D.card_le_of_isPGroup hτN hτb hτ hmono R hRN hR
  have hbt : ∀ hb : b ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) →
      (∃ t ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G),
        t * b * t⁻¹ = b⁻¹ ∧ ∀ y ∈ BO b₁ b₂ b₃, t * y * t⁻¹ = y) ∨
      ∃ K NL : Subgroup G, Compl b b₁ b₂ b₃ K NL :=
    bt_dichotomy h hB₁
  have hbG : b ∈ commutator G := by
    have htop : commutator G = ⊤ := by
      rcases h.simple.eq_bot_or_eq_top_of_normal (commutator G) with hbot | htop
      · exfalso
        obtain ⟨x, y, hxy⟩ := h.nonab
        refine hxy ?_
        have hmem : x * y * x⁻¹ * y⁻¹ ∈ commutator G :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [hbot, Subgroup.mem_bot] at hmem
        have h1 := mul_inv_eq_one.mp hmem
        rwa [mul_inv_eq_iff_eq_mul] at h1
      · exact htop
    rw [htop]
    exact Subgroup.mem_top b
  obtain ⟨E, hE, hEelem, hEcard⟩ := b2_elemAbelian D M hirr hN3 hbt hbG
  refine ⟨E, ?_, hEelem, hEcard⟩
  rw [hBB] at hE
  exact hE

end CFSG.StandardType.FF81.PropOne

end
