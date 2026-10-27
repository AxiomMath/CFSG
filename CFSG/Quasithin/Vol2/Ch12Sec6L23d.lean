module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19b
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N Equiv
open scoped IsMulCommutative

namespace S126L23d

@[expose] def ValidQ (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Prop :=
  t.1.val / 2 ≠ t.2.1.val / 2 ∧ t.1.val / 2 ≠ t.2.2.1.val / 2 ∧ t.1.val / 2 ≠ t.2.2.2.val / 2 ∧
    t.2.1.val / 2 ≠ t.2.2.1.val / 2 ∧ t.2.1.val / 2 ≠ t.2.2.2.val / 2 ∧
    t.2.2.1.val / 2 ≠ t.2.2.2.val / 2 ∧ (t.1.val < 4 ↔ t.2.1.val < 4)

instance (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Decidable (ValidQ t) := by
  unfold ValidQ
  infer_instance

theorem card_validQ : (Finset.univ.filter ValidQ).card = 128 := by
  decide +kernel

theorem div_two_eq_iff : ∀ x y : Fin 8, x.val / 2 = y.val / 2 ↔ (y = x ∨ y = partner x) := by
  decide

theorem partner_even : ∀ i : Fin 8, i.val % 2 = 1 → ∃ j : Fin 8, j.val % 2 = 0 ∧ i = partner j := by
  decide

theorem eq_of_presPart {σ τ : Perm (Fin 8)} (hσ : ∀ i, σ (partner i) = partner (σ i))
    (hτ : ∀ i, τ (partner i) = partner (τ i)) (h0 : σ 0 = τ 0) (h2 : σ 2 = τ 2)
    (h4 : σ 4 = τ 4) (h6 : σ 6 = τ 6) : σ = τ := by
  have hev : ∀ j : Fin 8, j.val % 2 = 0 → σ j = τ j := by
    intro j hj
    fin_cases j <;> simp_all
  ext i
  by_cases hi : i.val % 2 = 0
  · rw [hev i hi]
  · obtain ⟨j, hj, rfl⟩ := partner_even i (by omega)
    rw [hσ, hτ, hev j hj]

theorem validQ_of_presPart {σ : Perm (Fin 8)} (h : PresPart σ) :
    ValidQ (σ 0, σ 2, σ 4, σ 6) := by
  have hne : ∀ a b : Fin 8, b ≠ a → b ≠ partner a → (σ a).val / 2 ≠ (σ b).val / 2 := by
    intro a b hba hbp e
    rcases (div_two_eq_iff _ _).1 e with e | e
    · exact hba (σ.injective e)
    · rw [← h.1] at e
      exact hbp (σ.injective e)
  refine ⟨hne 0 2 (by decide) (by decide), hne 0 4 (by decide) (by decide),
    hne 0 6 (by decide) (by decide), hne 2 4 (by decide) (by decide),
    hne 2 6 (by decide) (by decide), hne 4 6 (by decide) (by decide), ?_⟩
  rcases h.2 with h' | h'
  · exact iff_of_true (h' 0 (by decide)) (h' 2 (by decide))
  · exact iff_of_false (not_lt.2 (h' 0 (by decide))) (not_lt.2 (h' 2 (by decide)))

theorem mem_P8_of_presPart {σ : Perm (Fin 8)} (h : PresPart σ) :
    σ ∈ CFSG.QuasithinUnique.Claim2526.P8 := by
  classical
  let S : Finset (Perm (Fin 8)) := Finset.univ.filter PresPart
  let f : Perm (Fin 8) → Fin 8 × Fin 8 × Fin 8 × Fin 8 := fun τ => (τ 0, τ 2, τ 4, τ 6)
  have hinj : Set.InjOn f S := by
    intro τ hτ τ' hτ' e
    simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hτ hτ'
    simp only [f, Prod.mk.injEq] at e
    exact eq_of_presPart hτ.1 hτ'.1 e.1 e.2.1 e.2.2.1 e.2.2.2
  have hmaps : ∀ τ ∈ S, f τ ∈ Finset.univ.filter ValidQ := by
    intro τ hτ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    exact validQ_of_presPart hτ
  have hS : S.card ≤ 128 := card_validQ ▸ Finset.card_le_card_of_injOn f hmaps hinj
  have hP8 : (CFSG.QuasithinUnique.Claim2526.P8 : Set (Perm (Fin 8))).toFinset ⊆ S := by
    intro τ hτ
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hτ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact S126Ex.presPart_of_mem (S126Ex.P8_le_presSub hτ)
  have hcard : (CFSG.QuasithinUnique.Claim2526.P8 : Set (Perm (Fin 8))).toFinset.card = 128 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact CFSG.QuasithinUnique.Claim2526.card_P8
  have heq := Finset.eq_of_subset_of_card_le hP8 (by omega)
  have hσS : σ ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  rw [← heq] at hσS
  simpa using hσS

theorem fixD_chk : ∀ x : Fin 8 → ZMod 2,
    ((∀ i, x (tf 1 0 i) = x i) ∨ ∀ i, x (tf 1 0 i) = x i + 1) →
    ((∀ i, x (tf 2 0 i) = x i) ∨ ∀ i, x (tf 2 0 i) = x i + 1) →
    ((∀ i, x (tf 0 1 i) = x i) ∨ ∀ i, x (tf 0 1 i) = x i + 1) →
    ((∀ i, x (tf 0 2 i) = x i) ∨ ∀ i, x (tf 0 2 i) = x i + 1) →
    ((∀ i, x (S126L1c.bsw i) = x i) ∨ ∀ i, x (S126L1c.bsw i) = x i + 1) →
    (∀ i, x i = x 0) ∨ ∀ i, x i = x 0 + (if i.val < 4 then 0 else 1) := by
  decide +kernel

theorem zmod2_cases' : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

theorem fix_of_dAct {σ : Perm (Fin 8)} {m : ↥(coreMod 8)}
    (h : dAct σ (QuotientGroup.mk m) = QuotientGroup.mk m) :
    (∀ i, Multiplicative.toAdd (m : PermMod 8) (σ⁻¹ i) = Multiplicative.toAdd (m : PermMod 8) i) ∨
      ∀ i, Multiplicative.toAdd (m : PermMod 8) (σ⁻¹ i) =
        Multiplicative.toAdd (m : PermMod 8) i + 1 := by
  rw [dAct_mk] at h
  have h1 : (QuotientGroup.mk (coreAct 8 σ m * m⁻¹) : D8) = 1 := by
    rw [QuotientGroup.mk_mul, h, QuotientGroup.mk_inv, mul_inv_cancel]
  have key : ∀ i, Multiplicative.toAdd ((coreAct 8 σ m * m⁻¹ : ↥(coreMod 8)) : PermMod 8) i =
      Multiplicative.toAdd (m : PermMod 8) (σ⁻¹ i) - Multiplicative.toAdd (m : PermMod 8) i := by
    intro i
    rw [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply,
      coreAct_coe, permAct_apply, sub_eq_add_neg]
  rcases (S126FE.mk_eq_one_iff _).1 h1 with e | e
  · left
    intro i
    have hk := key i
    rw [e] at hk
    exact (sub_eq_zero.1 hk.symm)
  · right
    intro i
    have hk := key i
    rw [e] at hk
    have h1' : (1 : ZMod 2) = Multiplicative.toAdd (m : PermMod 8) (σ⁻¹ i) -
        Multiplicative.toAdd (m : PermMod 8) i := hk
    rw [eq_sub_iff_add_eq] at h1'
    rw [← h1', add_comm]

theorem toAdd_e0123 : ∀ i : Fin 8,
    Multiplicative.toAdd (eset {0, 1, 2, 3} : PermMod 8) i = if i.val < 4 then 1 else 0 := by
  decide

theorem mk_eq_e0123 {m : ↥(coreMod 8)}
    (h : (∀ i, Multiplicative.toAdd (m : PermMod 8) i = if i.val < 4 then 1 else 0) ∨
      ∀ i, Multiplicative.toAdd (m : PermMod 8) i = if i.val < 4 then 0 else 1) :
    (QuotientGroup.mk m : D8) = S126L19.e0123 := by
  rw [S126L19.e0123, ← mul_inv_eq_one, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    S126FE.mk_eq_one_iff]
  have hv : ∀ i, Multiplicative.toAdd ((m * (⟨eset {0, 1, 2, 3}, S126L19.e0123_mem⟩ :
      ↥(coreMod 8))⁻¹ : ↥(coreMod 8)) : PermMod 8) i =
      Multiplicative.toAdd (m : PermMod 8) i - (if i.val < 4 then 1 else 0) := by
    intro i
    rw [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply,
      toAdd_e0123, sub_eq_add_neg]
  rcases h with h | h
  · left
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [hv, h]
    change _ = (0 : ZMod 2)
    exact sub_self _
  · right
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [hv, h]
    change _ = (1 : ZMod 2)
    split_ifs <;> decide

theorem mem_W1_of_fix {y : D8} (h : ∀ σ ∈ S126L1c.Q8, dAct σ y = y) : y ∈ W1 := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨h1, h2, h3, h4, h5⟩ := S126L1c.mem_Q8
  have conv : ∀ u v : Fin 4, tau u v ∈ S126L1c.Q8 →
      (∀ i, Multiplicative.toAdd (m : PermMod 8) (tf u v i) =
        Multiplicative.toAdd (m : PermMod 8) i) ∨
      ∀ i, Multiplicative.toAdd (m : PermMod 8) (tf u v i) =
        Multiplicative.toAdd (m : PermMod 8) i + 1 := fun u v huv => by
    have := fix_of_dAct (h _ huv)
    simp only [tau_inv_apply] at this
    exact this
  have hb := fix_of_dAct (h _ h5)
  rw [S126L1c.bsw_inv] at hb
  set x := Multiplicative.toAdd (m : PermMod 8) with hx
  rcases fixD_chk x (conv 1 0 h1) (conv 2 0 h2) (conv 0 1 h3) (conv 0 2 h4) hb with c | c
  ·
    have hm : m = 1 ∨ m = S126FE.eOm := by
      rcases zmod2_cases' (x 0) with h0 | h0
      · left
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext i
        rw [← hx, c i, h0]
        rfl
      · right
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext i
        rw [← hx, c i, h0]
        rfl
    rw [(S126FE.mk_eq_one_iff m).2 hm]
    exact W1.one_mem
  · rw [mk_eq_e0123 ?_]
    · exact S126L19a.e0123_mem_W1
    rcases zmod2_cases' (x 0) with h0 | h0
    · right
      intro i
      rw [← hx, c i, h0, zero_add]
    · left
      intro i
      rw [← hx, c i, h0]
      split_ifs <;> decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem fix_T_mem_V1 (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hvT : v ∈ Subgroup.centralizer (T : Set G)) : v ∈ F.V1 := by
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTL := hyp.normalizes
  have hcardA := S126L1c.card_autOn hH hLV
  let f : ↥(alternatingGroup (Fin 8)) →* MulAut ↥V := (autOn L V).subtype.comp F.π
  have hfi : Function.Injective f := Subtype.val_injective.comp (S126N.pi_bijective F hH).1
  have hfr : f.range = autOn L V := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact (F.π σ).2
    · intro hx
      obtain ⟨σ, hσ⟩ := F.π_surj ⟨x, hx⟩
      exact ⟨σ, by simp [f, hσ]⟩
  have hsylTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hS := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hsylTL hLV
  have hS64 : Nat.card ↥(autOn (T ⊓ L) V) = 2 ^ 6 :=
    S126L1c.card_of_isSylowTwoOf hS (m := 315) (by rw [hcardA, card_A8]; norm_num) (by decide)
  let P₀ : Subgroup ↥(alternatingGroup (Fin 8)) := (autOn (T ⊓ L) V).comap f
  have hP₀ : Nat.card P₀ = 64 := by
    have h1 : P₀.map f = autOn (T ⊓ L) V := by
      rw [Subgroup.map_comap_eq, hfr]
      exact inf_of_le_right hS.1
    have h2 : Nat.card (P₀.map f) = Nat.card P₀ :=
      Nat.card_congr (Subgroup.equivMapOfInjective P₀ f hfi).toEquiv.symm
    rw [← h2, h1, hS64]
    norm_num
  let P : Subgroup (Perm (Fin 8)) := P₀.map (alternatingGroup (Fin 8)).subtype
  have hP : Nat.card P = 64 := by
    rw [← hP₀]
    exact Nat.card_congr (Subgroup.equivMapOfInjective P₀ _ Subtype.val_injective).toEquiv.symm
  have hact : ∀ σ ∈ P₀, ∃ t ∈ T ⊓ L, ActsAs F t σ := by
    intro σ hσ
    obtain ⟨t, ht, htTL, hta⟩ := mem_autOn_iff_exists.mp (show f σ ∈ autOn (T ⊓ L) V from hσ)
    exact ⟨t, htTL, actsAs_of_pi F ht σ hta⟩
  have hPQ : P ≤ S126L1c.Q8 := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨t, htTL, hta⟩ := hact σ hσ
    obtain ⟨τ, hτP, hτ⟩ := actsAs_of_mem_T F htTL.1
    have e : (σ : Perm (Fin 8)) = τ := ActsAs.unique hta hτ (hLV htTL.2)
    refine ⟨?_, σ.2⟩
    change (σ : Perm (Fin 8)) ∈ _
    rw [e]
    exact mem_P8_of_presPart hτP
  have hPeq : P = S126L1c.Q8 := Subgroup.eq_of_le_of_card_ge hPQ (by
    have := S126L1c.card_Q8_le
    omega)
  have hfix : ∀ σ ∈ S126L1c.Q8, dAct σ (F.β ⟨v, hv⟩) = F.β ⟨v, hv⟩ := by
    intro σ hσ
    rw [← hPeq] at hσ
    obtain ⟨σ', hσ', rfl⟩ := hσ
    obtain ⟨t, htTL, hta⟩ := hact σ' hσ'
    have hc : t * v * t⁻¹ = v := by
      rw [Subgroup.mem_centralizer_iff.1 hvT t htTL.1, mul_inv_cancel_right]
    have := hta ⟨v, hv⟩ ⟨v, hv⟩ hc.symm
    exact this.symm
  refine Subgroup.mem_map.2 ⟨⟨v, hv⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  exact mem_W1_of_fix hfix

omit [IsMulCommutative ↥V] in
theorem eq_of_card_two {K : Subgroup G} (hK : Nat.card K = 2) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  by_contra hne
  have := S126L1c.card_ge_three hx hy hx1 hy1 hne
  omega

theorem card_W1 : Nat.card W1 = 2 := by
  classical
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨S126L19.e0123, S126L19a.e0123_mem_W1⟩, fun h => S126L19a.e0123_ne_one
    (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨y, hy⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases S126L19a.mem_W1 hy with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem part2 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    V ⊓ quasithinOmegaOneCenter T = F.V1 ∧ Nat.card ↥F.V1 = 2 := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_reduced (hVT.trans le_sup_right) hred
  have hβ : Function.Injective F.β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    have h1 : (w : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨w.2, (F.β_ker w).1 hw⟩
    rw [hZ] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h1))
  have hcard : Nat.card ↥F.V1 = 2 := by
    have e1 : Nat.card ↥F.V1 = Nat.card ↥(W1.comap F.β) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv.symm
    have e2 : (W1.comap F.β).map F.β = W1 := Subgroup.map_comap_eq_self_of_surjective F.β_surj W1
    have e3 : Nat.card ↥((W1.comap F.β).map F.β) = Nat.card ↥(W1.comap F.β) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ hβ).toEquiv.symm
    rw [e1, ← e3, e2, card_W1]
  refine ⟨le_antisymm ?_ ?_, hcard⟩
  · rintro x ⟨hxV, hxZ⟩
    have hle : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
      (Subgroup.closure_le _).2 fun z hz => hz.1
    exact fix_T_mem_V1 F hH hxV (hle hxZ).2
  · intro x hx
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨w.2, Subgroup.subset_closure ⟨⟨hVT w.2, ?_⟩, hVe.2 _ w.2⟩⟩
    show (w : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hN := S126L19b.T_le_normalizer_V1 (F := F) h1222 hH ht
    have hxt : t * (w : G) * t⁻¹ ∈ F.V1 := (Subgroup.mem_normalizer_iff.1 hN _).1 hx
    by_cases hw1 : (w : G) = 1
    · rw [hw1, mul_one, one_mul]
    have hwt1 : t * (w : G) * t⁻¹ ≠ 1 := fun h => hw1 (by
      calc (w : G) = t⁻¹ * (t * w * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group)
    have e := eq_of_card_two hcard hxt hx hwt1 hw1
    calc t * (w : G) = t * w * t⁻¹ * t := by group
      _ = w * t := by rw [e]; rfl

end S126L23d

end CFSG.Quasithin.H13
