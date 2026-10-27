module

public import CFSG.Quasithin.Background.SmithB42LnL4Codes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open Matrix CFSG.Assembly.LowTwoRank

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem card_le_of_inv4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hfixL : fixV L = ⊥)
    {B : Subgroup (MulAut V)} {b : G4} (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbB : fL4 e b ∈ B) :
    Nat.card V ≤ (fixV B).index ^ 4 := by
  obtain ⟨c, hc | hc⟩ := exists_conj_t0_or_s0_4 hb2 hb1
  · have hE := entries_ok.1
    refine card_le_pow_of_entry e hfixL (E_t0.conj hE) (fun j => uOf (E_t0.fc j))
      (E_t0.closure_eq_top hE) c fun j => ?_
    have e1 : c⁻¹ * uOf (E_t0.fc j) * c = b := by
      have hj : E_t0.fc j = 1 := by fin_cases j; rfl
      rw [hj, ← hc]
      group
    rw [e1]
    exact hbB
  · have hE := entries_ok.2.1
    refine card_le_pow_of_entry e hfixL (E_s0.conj hE) (fun j => uOf (E_s0.fc j))
      (E_s0.closure_eq_top hE) c fun j => ?_
    have e1 : c⁻¹ * uOf (E_s0.fc j) * c = b := by
      have hj : E_s0.fc j = 18 := by fin_cases j; rfl
      rw [hj, ← hc]
      group
    rw [e1]
    exact hbB

theorem exists_of_pairGood {tab : List (Fin 64 × Fin 64 × (Fin 4 → ℕ) × (Fin 4 → ℕ) × Fin 2)}
    {f₀ f₁ : Fin 2 → Fin 64} {cx cy : Fin 64} (h : PairGood tab f₀ f₁ cx cy) :
    ∃ (D : G4) (r : Fin 2), D * uOf cx * D⁻¹ = uOf (f₀ r) ∧ D * uOf cy * D⁻¹ = uOf (f₁ r) := by
  unfold PairGood at h
  split at h
  · rename_i t _
    obtain ⟨hgi, hx, hy⟩ := h
    have hig : toM4 t.2.2.2.1 * toM4 t.2.2.1 = 1 :=
      (mul_eq_one_comm_of_card_eq (Fin 4) (Fin 4) (ZMod 2) rfl).mp hgi
    have hinv : ((ofMI (toM4 t.2.2.1) (toM4 t.2.2.2.1) hgi)⁻¹ : G4) =
        ofMI (toM4 t.2.2.2.1) (toM4 t.2.2.1) hig := inv_eq_of_mul_eq_one_right (Subtype.ext hgi)
    refine ⟨ofMI (toM4 t.2.2.1) (toM4 t.2.2.2.1) hgi, t.2.2.2.2, ?_, ?_⟩ <;> rw [hinv] <;>
      apply Subtype.ext
    · exact hx
    · exact hy
  · exact h.elim

theorem conj_pair {D h : G4} {cx f : Fin 64} (hD : D * uOf cx * D⁻¹ = uOf f) :
    (D * h)⁻¹ * uOf f * (D * h) = h⁻¹ * uOf cx * h := by
  rw [← hD]
  group

theorem card_le_of_pair (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hfixL : fixV L = ⊥)
    {B : Subgroup (MulAut V)} {h : G4} {cx cy : Fin 64} (hx : cx ∈ tvL) (hy : cy ∈ ntvL)
    (hc : up4 cx * up4 cy = up4 cy * up4 cx) (hxB : fL4 e (h⁻¹ * uOf cx * h) ∈ B)
    (hyB : fL4 e (h⁻¹ * uOf cy * h) ∈ B) : Nat.card V ≤ (fixV B).index ^ 2 := by
  obtain ⟨D, r, hDx, hDy⟩ := exists_of_pairGood (pairTab4_spec cx hx cy hy hc)
  fin_cases r
  · have hE := entries_ok.2.2.1
    refine card_le_pow_of_entry e hfixL (E_R1.conj hE) (fun j => uOf (E_R1.fc j))
      (E_R1.closure_eq_top hE) (D * h) fun j => ?_
    fin_cases j
    · exact (conj_pair (f := 2) hDx).symm ▸ hxB
    · exact (conj_pair (f := 12) hDy).symm ▸ hyB
  · have hE := entries_ok.2.2.2.1
    refine card_le_pow_of_entry e hfixL (E_R2.conj hE) (fun j => uOf (E_R2.fc j))
      (E_R2.closure_eq_top hE) (D * h) fun j => ?_
    fin_cases j
    · exact (conj_pair (f := 1) hDx).symm ▸ hxB
    · exact (conj_pair (f := 33) hDy).symm ▸ hyB

theorem card_le_of_pair0 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (hfixL : fixV L = ⊥)
    {B : Subgroup (MulAut V)} {h : G4} {cx cy : Fin 64} (hx : cx ∈ ntvL) (hy : cy ∈ ntvL)
    (hxy : cx ≠ cy) (hc : up4 cx * up4 cy = up4 cy * up4 cx)
    (hp : code4 (up4 cx * up4 cy) ∈ ntvL) (hxB : fL4 e (h⁻¹ * uOf cx * h) ∈ B)
    (hyB : fL4 e (h⁻¹ * uOf cy * h) ∈ B) : Nat.card V ≤ (fixV B).index ^ 3 := by
  obtain ⟨D, r, hDx, hDy⟩ := exists_of_pairGood (pairTab0_spec cx hx cy hy hxy hc hp)
  fin_cases r
  · have hE := entries_ok.2.2.2.2.1
    refine card_le_pow_of_entry e hfixL (E_R3.conj hE) (fun j => uOf (E_R3.fc j))
      (E_R3.closure_eq_top hE) (D * h) fun j => ?_
    fin_cases j
    · exact (conj_pair (f := 12) hDx).symm ▸ hxB
    · exact (conj_pair (f := 22) hDy).symm ▸ hyB
  · have hE := entries_ok.2.2.2.2.2
    refine card_le_pow_of_entry e hfixL (E_R4.conj hE) (fun j => uOf (E_R4.fc j))
      (E_R4.closure_eq_top hE) (D * h) fun j => ?_
    fin_cases j
    · exact (conj_pair (f := 18) hDx).symm ▸ hxB
    · exact (conj_pair (f := 33) hDy).symm ▸ hyB

theorem regular_checks :
    xM4 1 = pm (Equiv.swap 0 1) * up4 2 * pm (Equiv.swap 0 1)⁻¹ ∧
    xM4 2 = pm (Equiv.swap 0 2) * up4 4 * pm (Equiv.swap 0 2)⁻¹ ∧
    yM4 0 = pm (Equiv.swap 0 1) * up4 1 * pm (Equiv.swap 0 1)⁻¹ ∧
    yM4 1 = pm (Equiv.swap 0 2) * up4 1 * pm (Equiv.swap 0 2)⁻¹ ∧
    xM4 0 = pm (Equiv.swap 1 3) * up4 4 * pm (Equiv.swap 1 3)⁻¹ ∧
    xM4 1 = pm (Equiv.swap 2 3) * up4 16 * pm (Equiv.swap 2 3)⁻¹ ∧
    yM4 1 = pm (Equiv.swap 1 3) * up4 32 * pm (Equiv.swap 1 3)⁻¹ ∧
    yM4 2 = pm (Equiv.swap 2 3) * up4 32 * pm (Equiv.swap 2 3)⁻¹ ∧
    xM4 0 = pm 1 * up4 1 * pm 1⁻¹ ∧ xM4 2 = pm 1 * up4 32 * pm 1⁻¹ := by
  decide

theorem n4_eq (s : Fin 3) : n4 s = x4 s * y4 s * x4 s := by
  rw [y4_eq, ← mul_assoc, ← mul_assoc, x4_mul_self, one_mul, mul_assoc, x4_mul_self, mul_one]

theorem model_of_parabolic [Module (ZMod 2) (Additive V)] (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    (hρ : SmithCurtis.IsSimpleRep (repOf4 (phiOf4 e))) {B : Subgroup (MulAut V)}
    (C : Fin 3 → G4) (F : Fin 3 → G4) (D : G4) (hF : ∀ j, fL4 e (D⁻¹ * F j * D) ∈ B)
    {s t : Fin 3} (hst : s ≠ t)
    (hx : ∀ r, x4 r ∈ Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹})
    (hys : y4 s ∈ Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹})
    (hyt : y4 t ∈ Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹}) :
    Nat.card V ≤ (fixV B).index ^ 3 ∨ L4Model (repOf4 (phiOf4 e)) := by
  set X := Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹} with hXdef
  have h := index_le_pow_of_entry e C F D hF (X := X) le_rfl
  by_cases h0 : fixV (X.map (fL4 e)) = ⊥
  · left
    rwa [h0, Subgroup.index_bot] at h
  · right
    have : Finite (Additive V) := inferInstanceAs (Finite V)
    obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h0
    have hfix : ∀ g ∈ X, repOf4 (phiOf4 e) g (Additive.ofMul (v : V)) = Additive.ofMul (v : V) := by
      intro g hg
      rw [repOf4_apply, ← fL4_apply]
      exact congrArg Additive.ofMul (hv (fL4 e g) ⟨g, hg, rfl⟩)
    have hns : ∀ r, y4 r ∈ X → n4 r ∈ X := fun r hy => by
      rw [n4_eq]
      exact X.mul_mem (X.mul_mem (hx r) hy) (hx r)
    refine l4Model_of_fixed hρ (x := Additive.ofMul (v : V)) ?_ ?_ hst (hfix _ (hns s hys))
      (hfix _ (hns t hyt))
    · intro h1
      apply hv1
      exact Subtype.ext (Additive.ofMul.injective h1)
    · intro u hu
      exact hfix u (mem_of_x4_mem hx hu)

theorem mem_closure_conj {k m : ℕ} {C : Fin k → G4} {F : Fin m → G4} (i : Fin k) (j : Fin m)
    {g : G4} (hg : g = C i * F j * (C i)⁻¹) :
    g ∈ Subgroup.closure {x | ∃ i j, x = C i * F j * (C i)⁻¹} :=
  Subgroup.subset_closure ⟨i, j, hg⟩

theorem conj_perm_eq {g : G4} {σ : Equiv.Perm (Fin 4)} {c : Fin 64}
    (h : (g : 𝕄₄) = pm σ * up4 c * pm σ⁻¹) : g = permHom σ * uOf c * (permHom σ)⁻¹ := by
  rw [permHom_inv]
  exact Subtype.ext h

theorem model_of_regular [Module (ZMod 2) (Additive V)] (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    (hρ : SmithCurtis.IsSimpleRep (repOf4 (phiOf4 e))) {B : Subgroup (MulAut V)} {h : G4}
    (hreg : (fL4 e (h⁻¹ * uOf 1 * h) ∈ B ∧ fL4 e (h⁻¹ * uOf 2 * h) ∈ B ∧
      fL4 e (h⁻¹ * uOf 4 * h) ∈ B) ∨ (fL4 e (h⁻¹ * uOf 4 * h) ∈ B ∧
      fL4 e (h⁻¹ * uOf 16 * h) ∈ B ∧ fL4 e (h⁻¹ * uOf 32 * h) ∈ B)) :
    Nat.card V ≤ (fixV B).index ^ 3 ∨ L4Model (repOf4 (phiOf4 e)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := regular_checks
  rcases hreg with ⟨h1, h2, h4⟩ | ⟨h4, h16, h32⟩
  · set σs : Fin 3 → Equiv.Perm (Fin 4) := ![1, Equiv.swap 0 1, Equiv.swap 0 2]
    set cs : Fin 3 → Fin 64 := ![1, 2, 4]
    have hF : ∀ j, fL4 e (h⁻¹ * uOf (cs j) * h) ∈ B := fun j => by
      fin_cases j
      · exact h1
      · exact h2
      · exact h4
    refine model_of_parabolic e hρ (fun i => permHom (σs i)) (fun j => uOf (cs j)) h hF
      (s := 0) (t := 1) (by decide) (fun r => ?_) (mem_closure_conj 1 0 (conj_perm_eq c3))
      (mem_closure_conj 2 0 (conj_perm_eq c4))
    fin_cases r
    · exact mem_closure_conj 0 0 (conj_perm_eq c9)
    · exact mem_closure_conj 1 1 (conj_perm_eq c1)
    · exact mem_closure_conj 2 2 (conj_perm_eq c2)
  · set σs : Fin 3 → Equiv.Perm (Fin 4) := ![1, Equiv.swap 2 3, Equiv.swap 1 3]
    set cs : Fin 3 → Fin 64 := ![4, 16, 32]
    have hF : ∀ j, fL4 e (h⁻¹ * uOf (cs j) * h) ∈ B := fun j => by
      fin_cases j
      · exact h4
      · exact h16
      · exact h32
    refine model_of_parabolic e hρ (fun i => permHom (σs i)) (fun j => uOf (cs j)) h hF
      (s := 1) (t := 2) (by decide) (fun r => ?_) (mem_closure_conj 2 2 (conj_perm_eq c7))
      (mem_closure_conj 1 2 (conj_perm_eq c8))
    fin_cases r
    · exact mem_closure_conj 2 0 (conj_perm_eq c5)
    · exact mem_closure_conj 1 1 (conj_perm_eq c6)
    · exact mem_closure_conj 0 2 (conj_perm_eq c10)

theorem exists_two_codes {T : Finset (Fin 64)} (h4 : 4 ≤ T.card) :
    ∃ x ∈ T, ∃ y ∈ T, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y := by
  classical
  have h1 : 2 ≤ ((T.erase 0).card) := by
    have := Finset.pred_card_le_card_erase (s := T) (a := 0)
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < (T.erase 0).card)
  obtain ⟨hx0, hxT⟩ := Finset.mem_erase.1 hx
  obtain ⟨hy0, hyT⟩ := Finset.mem_erase.1 hy
  exact ⟨x, hxT, y, hyT, hx0, hy0, hxy⟩

theorem l4Model_of_offender_core [Module (ZMod 2) (Additive V)] (hHyp : B4HypCore G L)
    (hZ : Subgroup.center ↥L = ⊥) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    (hA : IsFFStarOffender G A) : L4Model (repOf4 (phiOf4 e)) := by
  classical
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Nontrivial V := nontrivial_of_equiv4 e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfixL : fixV L = ⊥ :=
    CFSG.QuasithinUnique.B42A57.fixV_eq_bot_of_irr hHyp.2.2 (exists_not_comm4 e)
  have hρ : SmithCurtis.IsSimpleRep (repOf4 (phiOf4 e)) :=
    isSimpleRep_repOf4 (phiOf4 e) (irr_of_isIrrSec hHyp.2.2)
  by_cases hd : Module.finrank (ZMod 2) (Additive V) < 12
  · exact l4Model_of_finrank_lt hρ hd
  push Not at hd
  have hV12 : 2 ^ 12 ≤ Nat.card V := by
    rw [card_eq_two_pow_finrank]
    exact Nat.pow_le_pow_right (by norm_num) hd
  have hidx : (fixV A).index ≤ Nat.card A := CFSG.QuasithinUnique.B42A57.index_fixV_le hA
  have hAG : A ≤ G := hA.1
  have hel : IsElemAbelian2 A := hA.2.2.1
  have hcS := comm_of_comap4 (e := e) hel
  have h2S := sq_of_comap4 (e := e) hel
  have hcardA := card_le_two_mul_comap4_core hHyp hZ e hAG
  set S := A.comap (fL4 e) with hS
  have hbound : ∀ {r : ℕ}, Nat.card V ≤ (fixV A).index ^ r → Nat.card A ^ r < 2 ^ 12 →
      L4Model (repOf4 (phiOf4 e)) := by
    intro r h1 h2
    have := Nat.pow_le_pow_left hidx r
    omega
  have houter : ∀ a₀ ∈ A, a₀ ∉ L → ∃ P : GL (Fin 4) (ZMod 2), ∃ haG : a₀ ∈ G,
      (∀ x : G4, ((conjG4_core hHyp e haG x : G4) : 𝕄₄) =
        (P : 𝕄₄) * ((x⁻¹ : G4) : 𝕄₄)ᵀ * ((P⁻¹ : GL (Fin 4) (ZMod 2)) : 𝕄₄)) ∧
      ∀ b ∈ S, conjG4_core hHyp e haG b = b := by
    intro a₀ ha₀ ha₀L
    obtain ⟨P, hP⟩ := exists_conjG4_eq_core hHyp hZ e (hAG ha₀) ha₀L
    exact ⟨P, hAG ha₀, hP, conjG4_fix_core hHyp e hel ha₀ (hAG ha₀)⟩
  obtain ⟨k, hk⟩ := (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq S h2S).exists_card_eq
  by_cases hk0 : k = 0
  · subst hk0
    have hS1 : ∀ s ∈ S, s = 1 := by
      intro s hs
      have h1 : Nat.card S = 1 := by rw [hk, pow_zero]
      rw [Subgroup.card_eq_one] at h1
      rw [h1] at hs
      exact (Subgroup.mem_bot).1 hs
    have hAL : ¬ A ≤ L := by
      intro hAL
      apply hA.2.1
      have h1 := card_comap4_eq e hAL
      rw [← hS, hk, pow_zero] at h1
      exact Subgroup.card_eq_one.1 h1.symm
    obtain ⟨a₀, ha₀, ha₀L⟩ := Set.not_subset.1 hAL
    obtain ⟨P, haG, hP, -⟩ := houter a₀ ha₀ ha₀L
    have hA2 : Nat.card A ≤ 2 := by rw [hk, pow_zero] at hcardA; omega
    have ha₀2 : a₀ * a₀ = 1 := by rw [← pow_two]; exact hel.2 a₀ ha₀
    have hPs := transpose_P4_core hHyp e haG ha₀2 hP
    obtain ⟨γ, hγ2, hx1, hx2⟩ := exists_conj_mul_inv4 hPs hP
    set γ' := fL4 e γ with hγ'
    have hγ'inv : γ'⁻¹ = γ' := by
      rw [hγ', ← map_inv, inv_eq_of_mul_eq_one_right hγ2]
    have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀2
    have hxeq : fL4 e (conjG4_core hHyp e haG γ * γ) = a₀ * (γ' * a₀ * γ'⁻¹) := by
      rw [map_mul, fL4_apply, conjG4_spec_core, ← fL4_apply, ← hγ', hγ'inv, ha₀inv]
      group
    set B : Fin 2 → Subgroup (MulAut V) :=
      ![Subgroup.zpowers a₀, (Subgroup.zpowers a₀).map (MulAut.conj γ').toMonoidHom] with hB
    have hle : Subgroup.zpowers (fL4 e (conjG4_core hHyp e haG γ * γ)) ≤ ⨆ i, B i := by
      rw [Subgroup.zpowers_le, hxeq]
      refine Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem 0 (Subgroup.mem_zpowers a₀))
        (Subgroup.mem_iSup_of_mem 1 ⟨a₀, Subgroup.mem_zpowers a₀, ?_⟩)
      show (MulAut.conj γ') a₀ = _
      rw [MulAut.conj_apply]
    have h1 := index_fixV_le_prod B hle
    rw [Fin.prod_univ_two] at h1
    have hB0 : (fixV (B 0)).index ≤ 2 :=
      (index_fixV_mono ((Subgroup.zpowers_le).2 ha₀)).trans (hidx.trans hA2)
    have hB1 : (fixV (B 1)).index = (fixV (B 0)).index :=
      CFSG.QuasithinUnique.B42A57.index_fixV_conj _ _
    have h2 := card_le_of_inv4 e hfixL hx2 hx1 (Subgroup.mem_zpowers _)
    have h3 : (fixV (Subgroup.zpowers (fL4 e (conjG4_core hHyp e haG γ * γ)))).index ≤ 4 := by
      rw [hB1] at h1
      calc _ ≤ (fixV (B 0)).index * (fixV (B 0)).index := h1
        _ ≤ 2 * 2 := Nat.mul_le_mul hB0 hB0
        _ = 4 := by norm_num
    have h4 := Nat.pow_le_pow_left h3 4
    exfalso
    have : (4 : ℕ) ^ 4 < 2 ^ 12 := by norm_num
    omega
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
    calc Nat.card A ^ 4 ≤ 4 ^ 4 := Nat.pow_le_pow_left hA4 4
      _ < 2 ^ 12 := by norm_num
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
  have hA32 : Nat.card A ≤ 32 := by
    have : 2 ^ k ≤ 16 := by
      calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
        _ = 16 := by norm_num
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
      calc Nat.card A ^ 2 ≤ 32 ^ 2 := Nat.pow_le_pow_left hA32 2
        _ < 2 ^ 12 := by norm_num
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
          · exact h1
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
      calc Nat.card A ^ 3 ≤ 8 ^ 3 := Nat.pow_le_pow_left hA8 3
        _ < 2 ^ 12 := by norm_num
    · exfalso
      by_cases hk3 : k = 3
      · subst hk3
        exact codes_not_ntv hT (by rw [hTc]; norm_num) hall
      · have hk4' : k = 4 := by omega
        subst hk4'
        have := (codes_q4 hT (by rw [hTc]; norm_num)).2.1
        exact absurd (htv 4 this) (by decide)

theorem l4Model_of_offender [Module (ZMod 2) (Additive V)] (hHyp : B4Hyp G L)
    (hZ : Subgroup.center ↥L = ⊥) (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    (hA : IsFFStarOffender G A) : L4Model (repOf4 (phiOf4 e)) :=
  l4Model_of_offender_core hHyp.core hZ e hA

end CFSG.Quasithin.B42Ln
