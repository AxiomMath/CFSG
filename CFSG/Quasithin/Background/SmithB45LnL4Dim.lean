module

public import CFSG.Quasithin.Background.SmithB42LnL4Dim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45Ln

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.B42Ln CFSG.Quasithin.SmithCurtis

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

section Weyl

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G4 W)

@[expose] def allW : Fin 24 → List (Fin 3) :=
  ![[], [0], [1], [2], [0, 1], [0, 2], [1, 0], [1, 2], [2, 1], [0, 1, 0], [0, 1, 2], [0, 2, 1],
    [1, 0, 2], [1, 2, 1], [2, 1, 0], [0, 1, 0, 2], [0, 1, 2, 1], [0, 2, 1, 0], [1, 0, 2, 1],
    [1, 2, 1, 0], [0, 1, 0, 2, 1], [0, 1, 2, 1, 0], [1, 0, 2, 1, 0], [0, 1, 0, 2, 1, 0]]

theorem allW_spec : ∀ i j : Fin 24, i ≠ j →
    ((allW j).map sw).prod⁻¹ * ((allW i).map sw).prod ≠ 1 := by
  decide

theorem form_allW {f : Module.Dual (ZMod 2) W} (hf : ∀ z ∈ augSub ρ L4, f z = 0) {y : W}
    {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ) (hfy : f y = 1) (hμ : ∀ s, μ s = 1)
    (i j : Fin 24) :
    f (ρ (nW4 (cs4.wordProd (allW j)))⁻¹ (ρ (nW4 (cs4.wordProd (allW i))) y)) =
      if i = j then 1 else 0 := by
  rw [← map_inv, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  obtain ⟨ω, hω, hw⟩ := cs4.exists_isReduced
    ((cs4.wordProd (allW j))⁻¹ * cs4.wordProd (allW i))
  rw [hw, form_nW4 ρ hf ht hfy hω]
  split_ifs with hij
  · subst hij
    rw [inv_mul_cancel] at hw
    have h0 : ω = [] := by
      have := hω
      rw [CoxeterSystem.IsReduced, ← hw, CoxeterSystem.length_one] at this
      exact List.eq_nil_of_length_eq_zero this.symm
    rw [h0]
    rfl
  · cases ω with
    | nil =>
      exfalso
      apply allW_spec i j hij
      have hπ := congrArg piW4 hw
      rw [map_mul, map_inv, piW4_wordProd, piW4_wordProd, piW4_wordProd] at hπ
      rw [hπ]
      rfl
    | cons s ω' => exact coinv4_eq_zero List.mem_cons_self (hμ s)

theorem twentyfour_le_finrank [Finite W] {ρ : Representation (ZMod 2) G4 W} (hρ : IsSimpleRep ρ)
    {y : W} {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ) (hμ : ∀ s, μ s = 1) :
    24 ≤ Module.finrank (ZMod 2) W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, hfy⟩ := datum4.exists_form hρ ht.1 ht.2.1
  have hval := form_allW ρ hf ht hfy hμ
  have hli : LinearIndependent (ZMod 2) fun i : Fin 24 =>
      ρ (nW4 (cs4.wordProd (allW i))) y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (fun z => f (ρ (nW4 (cs4.wordProd (allW j)))⁻¹ z)) hg
    simp only [map_sum, map_smul, smul_eq_mul, hval, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero] at h1
    exact h1
  simpa using hli.fintype_card_le_finrank

end Weyl

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem codes_q4_two {T : Finset (Fin 64)} (hT : IsCodeGroup T) (h16 : 16 ≤ T.card) :
    (2 : Fin 64) ∈ T ∧ (4 : Fin 64) ∈ T := by
  classical
  have hsub : T ⊆ Finset.univ.filter InQ4 := by
    intro c hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, mem_q4 c (hT.sq c hc) (h16.trans (Finset.card_le_card ?_))⟩
    intro d hd
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hT.sq d hd, hT.comm c hc d hd⟩
  have hle := Finset.card_le_card hsub
  rw [card_q4] at hle
  have heq : T = Finset.univ.filter InQ4 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_q4]; omega)
  refine ⟨?_, ?_⟩ <;> rw [heq, Finset.mem_filter] <;> exact ⟨Finset.mem_univ _, by decide⟩

theorem le_of_codes16 (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hAG : A ≤ G) (hel : IsElemAbelian2 A) {h : G4}
    (hT : IsCodeGroup (codesOf (A.comap (fL4 e)) h))
    (h16 : 16 ≤ (codesOf (A.comap (fL4 e)) h).card) : A ≤ L := by
  intro a₀ ha₀
  by_contra ha₀L
  obtain ⟨P, hP⟩ := exists_conjG4_eq hHyp hZ e (hAG ha₀) ha₀L
  have hfix := conjG4_fix hHyp e hel ha₀ (hAG ha₀)
  obtain ⟨h2, h4⟩ := codes_q4_two hT h16
  exact not_fixed_compat hP h (cx := 2) (cy := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (hfix _ (mem_codesOf.1 h2)) (hfix _ (mem_codesOf.1 h4))

theorem exists_inv_of_outer (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {a₀ : MulAut V} (ha₀G : a₀ ∈ G) (ha₀L : a₀ ∉ L)
    (ha₀2 : a₀ * a₀ = 1) :
    ∃ x : G4, x * x = 1 ∧ x ≠ 1 ∧
      (fixV (Subgroup.zpowers (fL4 e x))).index ≤ (fixV (Subgroup.zpowers a₀)).index ^ 2 := by
  obtain ⟨P, hP⟩ := exists_conjG4_eq hHyp hZ e ha₀G ha₀L
  have hPs := transpose_P4 hHyp e ha₀G ha₀2 hP
  obtain ⟨γ, hγ2, hx1, hx2⟩ := exists_conj_mul_inv4 hPs hP
  refine ⟨conjG4 hHyp e ha₀G γ * γ, hx2, hx1, ?_⟩
  set γ' := fL4 e γ with hγ'
  have hγ'inv : γ'⁻¹ = γ' := by
    rw [hγ', ← map_inv, inv_eq_of_mul_eq_one_right hγ2]
  have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀2
  have hxeq : fL4 e (conjG4 hHyp e ha₀G γ * γ) = a₀ * (γ' * a₀ * γ'⁻¹) := by
    rw [map_mul, fL4_apply, conjG4_spec, ← fL4_apply, ← hγ', hγ'inv, ha₀inv]
    group
  set B : Fin 2 → Subgroup (MulAut V) :=
    ![Subgroup.zpowers a₀, (Subgroup.zpowers a₀).map (MulAut.conj γ').toMonoidHom] with hB
  have hle : Subgroup.zpowers (fL4 e (conjG4 hHyp e ha₀G γ * γ)) ≤ ⨆ i, B i := by
    rw [Subgroup.zpowers_le, hxeq]
    refine Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem 0 (Subgroup.mem_zpowers a₀))
      (Subgroup.mem_iSup_of_mem 1 ⟨a₀, Subgroup.mem_zpowers a₀, ?_⟩)
    show (MulAut.conj γ') a₀ = _
    rw [MulAut.conj_apply]
  have h1 := index_fixV_le_prod B hle
  rw [Fin.prod_univ_two] at h1
  have hB1 : (fixV (B 1)).index = (fixV (B 0)).index :=
    CFSG.QuasithinUnique.B42A57.index_fixV_conj _ _
  rw [hB1] at h1
  calc _ ≤ (fixV (B 0)).index * (fixV (B 0)).index := h1
    _ = (fixV (Subgroup.zpowers a₀)).index ^ 2 := (sq _).symm

theorem card_le_or_l4Model [Module (ZMod 2) (Additive V)] (hHyp : B4Hyp G L)
    (hZ : Subgroup.center ↥L = ⊥) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hA : IsA2 G A)
    (h2F : (fixV A).index ≤ Nat.card A ^ 2) :
    Nat.card V ≤ 2 ^ 18 ∨ L4Model (repOf4 (phiOf4 e)) := by
  classical
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Nontrivial V := nontrivial_of_equiv4 e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfixL : fixV L = ⊥ :=
    CFSG.QuasithinUnique.B42A57.fixV_eq_bot_of_irr hHyp.2.2.2 (exists_not_comm4 e)
  have hρ : SmithCurtis.IsSimpleRep (repOf4 (phiOf4 e)) :=
    isSimpleRep_repOf4 (phiOf4 e) (irr_of_isIrrSec hHyp.2.2.2)
  have hAG : A ≤ G := hA.1
  have hel : IsElemAbelian2 A := hA.2.2
  have hcS := comm_of_comap4 (e := e) hel
  have h2S := sq_of_comap4 (e := e) hel
  have hcardA := card_le_two_mul_comap4 hHyp hZ e hAG
  set S := A.comap (fL4 e) with hS
  have hbound : ∀ {r : ℕ}, Nat.card V ≤ (fixV A).index ^ r → (Nat.card A ^ 2) ^ r ≤ 2 ^ 18 →
      Nat.card V ≤ 2 ^ 18 ∨ L4Model (repOf4 (phiOf4 e)) := fun h1 h2 =>
    Or.inl (h1.trans ((Nat.pow_le_pow_left h2F _).trans h2))
  have houter : ∀ a₀ ∈ A, a₀ ∉ L → ∃ P : GL (Fin 4) (ZMod 2), ∃ haG : a₀ ∈ G,
      (∀ x : G4, ((conjG4 hHyp e haG x : G4) : 𝕄₄) =
        (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)) ∧
      ∀ b ∈ S, conjG4 hHyp e haG b = b := by
    intro a₀ ha₀ ha₀L
    obtain ⟨P, hP⟩ := exists_conjG4_eq hHyp hZ e (hAG ha₀) ha₀L
    exact ⟨P, hAG ha₀, hP, conjG4_fix hHyp e hel ha₀ (hAG ha₀)⟩
  obtain ⟨k, hk⟩ := (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq S h2S).exists_card_eq
  by_cases hk0 : k = 0
  · subst hk0
    have hAL : ¬ A ≤ L := by
      intro hAL
      apply hA.2.1
      have h1 := card_comap4_eq e hAL
      rw [← hS, hk, pow_zero] at h1
      exact Subgroup.card_eq_one.1 h1.symm
    obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    have hA2 : Nat.card A ≤ 2 := by rw [hk, pow_zero] at hcardA; omega
    have ha₀2 : a₀ * a₀ = 1 := by rw [← pow_two]; exact hel.2 a₀ ha₀
    obtain ⟨x, hx2, hx1, hxi⟩ := exists_inv_of_outer hHyp hZ e (hAG ha₀) ha₀L ha₀2
    have hB0 : (fixV (Subgroup.zpowers a₀)).index ≤ 4 := by
      refine (index_fixV_mono ((Subgroup.zpowers_le).2 ha₀)).trans (h2F.trans ?_)
      calc Nat.card A ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hA2 2
        _ = 4 := by norm_num
    have h3 : (fixV (Subgroup.zpowers (fL4 e x))).index ≤ 16 :=
      hxi.trans ((Nat.pow_le_pow_left hB0 2).trans (by norm_num))
    left
    calc Nat.card V ≤ _ := card_le_of_inv4 e hfixL hx2 hx1 (Subgroup.mem_zpowers _)
      _ ≤ 16 ^ 4 := Nat.pow_le_pow_left h3 4
      _ ≤ 2 ^ 18 := by norm_num
  by_cases hk1 : k = 1
  · subst hk1
    have hSne : S ≠ ⊥ := by
      intro h0
      have h1 : Nat.card S = 1 := Subgroup.card_eq_one.2 h0
      rw [hk] at h1
      norm_num at h1
    obtain ⟨⟨b, hbS⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hSne
    have hb1' : b ≠ 1 := fun h0 => hb1 (by subst h0; rfl)
    refine hbound (card_le_of_inv4 e hfixL (h2S b hbS) hb1' hbS) ?_
    have hA4 : Nat.card A ≤ 4 := by rw [hk] at hcardA; omega
    calc (Nat.card A ^ 2) ^ 4 ≤ (4 ^ 2) ^ 4 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hA4 2) 4
      _ ≤ 2 ^ 18 := by norm_num
  have hk2 : 2 ≤ k := by omega
  obtain ⟨h, hh⟩ := exists_conj_le_U4 (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq S h2S)
  set T := codesOf S h with hTdef
  have hT : IsCodeGroup T := isCodeGroup_codesOf hcS h2S
  have hTc : T.card = 2 ^ k := by rw [card_codesOf hh, hk]
  have hmemA : ∀ c ∈ T, fL4 e (h⁻¹ * uOf c * h) ∈ A := fun c hc => mem_codesOf.1 hc
  have hk4 : k ≤ 4 := by
    by_contra hk4
    have h32 : 32 ≤ T.card := by
      rw [hTc]
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := (codes_q4 hT (by omega)).1
    omega
  have hA16 : Nat.card A ≤ 16 := by
    by_cases hk4' : k = 4
    · have hAL : A ≤ L := le_of_codes16 hHyp hZ e hAG hel hT (by rw [hTc, hk4']; norm_num)
      rw [← card_comap4_eq e hAL, ← hS, hk, hk4']
      norm_num
    · have : 2 ^ k ≤ 8 := by
        calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      rw [hk] at hcardA
      omega
  have h4T : 4 ≤ T.card := by
    rw [hTc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  by_cases htv : ∃ x ∈ T, x ∈ tvL
  · by_cases hntv : ∃ y ∈ T, y ∈ ntvL
    ·
      obtain ⟨x, hxT, hx⟩ := htv
      obtain ⟨y, hyT, hy⟩ := hntv
      refine hbound (card_le_of_pair e hfixL hx hy (hT.comm x hxT y hyT) (hmemA x hxT)
        (hmemA y hyT)) ?_
      calc (Nat.card A ^ 2) ^ 2 ≤ (16 ^ 2) ^ 2 :=
            Nat.pow_le_pow_left (Nat.pow_le_pow_left hA16 2) 2
        _ ≤ 2 ^ 18 := by norm_num
    ·
      push Not at hntv
      have hall : ∀ c ∈ T, c ≠ 0 → c ∈ tvL := fun c hc hc0 =>
        (hT.inv_cases hc hc0).resolve_right (hntv c hc)
      by_cases hAL : A ≤ L
      · have hSA : Nat.card S = Nat.card A := card_comap4_eq e hAL
        by_cases hk2' : k = 2
        · subst hk2'
          obtain ⟨x, hxT, -, -, hx0, -, -⟩ := exists_two_codes h4T
          have hb1 : h⁻¹ * uOf x * h ≠ 1 := by
            intro h0
            apply hx0
            have : uOf x = 1 := by
              calc uOf x = h * (h⁻¹ * uOf x * h) * h⁻¹ := by group
                _ = 1 := by rw [h0]; group
            rw [← code4_up4 x]
            exact (congrArg (fun g : G4 => code4 (g : 𝕄₄)) this).trans (by decide)
          refine hbound (card_le_of_inv4 e hfixL (h2S _ (mem_codesOf.1 hxT)) hb1 (hmemA x hxT))
            ?_
          rw [← hSA, hk]
          norm_num
        by_cases hk3 : k = 3
        · subst hk3
          have h8 : T.card = 8 := by rw [hTc]; norm_num
          rcases model_of_regular e hρ (B := A) (h := h) (by
            rcases codes_regular hT h8 hall with ⟨a, b, c⟩ | ⟨a, b, c⟩
            · exact Or.inl ⟨hmemA _ a, hmemA _ b, hmemA _ c⟩
            · exact Or.inr ⟨hmemA _ a, hmemA _ b, hmemA _ c⟩) with h1 | h1
          · refine hbound h1 ?_
            rw [← hSA, hk]
            norm_num
          · exact Or.inr h1
        · exfalso
          have hk4' : k = 4 := by omega
          subst hk4'
          have := (codes_q4 hT (by rw [hTc]; norm_num)).2.2
          exact absurd (hntv 18 this) (by decide)
      · exfalso
        obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
        obtain ⟨P, haG, hP, hfix⟩ := houter a₀ ha₀ ha₀L
        obtain ⟨x, hxT, y, hyT, hx0, hy0, hxy⟩ := exists_two_codes h4T
        exact not_fixed_compat hP h (hall x hxT hx0) (hall y hyT hy0) hxy (hT.comm x hxT y hyT)
          (hall _ (hT.mul_mem x hxT y hyT) (code_mul_ne_zero (hT.sq y hyT) hxy))
          (hfix _ (mem_codesOf.1 hxT)) (hfix _ (mem_codesOf.1 hyT))
  ·
    push Not at htv
    have hall : ∀ c ∈ T, c ≠ 0 → c ∈ ntvL := fun c hc hc0 =>
      (hT.inv_cases hc hc0).resolve_left (htv c hc)
    by_cases hk2' : k = 2
    · subst hk2'
      obtain ⟨x, hxT, y, hyT, hx0, hy0, hxy⟩ := exists_two_codes h4T
      refine hbound (card_le_of_pair0 e hfixL (hall x hxT hx0) (hall y hyT hy0) hxy
        (hT.comm x hxT y hyT) (hall _ (hT.mul_mem x hxT y hyT)
          (code_mul_ne_zero (hT.sq y hyT) hxy)) (hmemA x hxT) (hmemA y hyT)) ?_
      have hA8 : Nat.card A ≤ 8 := by rw [hk] at hcardA; omega
      calc (Nat.card A ^ 2) ^ 3 ≤ (8 ^ 2) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hA8 2) 3
        _ ≤ 2 ^ 18 := by norm_num
    · exfalso
      by_cases hk3 : k = 3
      · subst hk3
        exact codes_not_ntv hT (by rw [hTc]; norm_num) hall
      · have hk4' : k = 4 := by omega
        subst hk4'
        have := (codes_q4 hT (by rw [hTc]; norm_num)).2.1
        exact absurd (htv 4 this) (by decide)

end CFSG.Quasithin.B45Ln
