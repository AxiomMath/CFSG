module

public import CFSG.Quasithin.H13.U3S13227

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

@[expose] def InE8 (σ : Perm (Fin 6)) : Prop := ∀ i : Fin 6, (σ i : ℕ) / 2 = (i : ℕ) / 2

instance : DecidablePred InE8 := fun σ => by unfold InE8; infer_instance

@[expose] def e8F : Fin 8 → Perm (Fin 6) :=
  ![1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3, swap 4 5, swap 0 1 * swap 4 5,
    swap 2 3 * swap 4 5, swap 0 1 * swap 2 3 * swap 4 5]

@[expose] def e8Xor (i j : Fin 8) : Fin 8 :=
  ⟨((i : ℕ) ^^^ (j : ℕ)) % 8, Nat.mod_lt _ (by norm_num)⟩

theorem e8F_inj : ∀ i j : Fin 8, e8F i = e8F j → i = j := by decide +kernel

theorem e8F_surj : ∀ σ : Perm (Fin 6), InE8 σ → ∃ i, e8F i = σ := by decide +kernel

theorem e8F_zero : e8F 0 = 1 := rfl

theorem e8F_mul : ∀ i j, e8F i * e8F j = e8F (e8Xor i j) := by decide +kernel

theorem inE8_of_inD6_conj :
    ∀ σ : Perm (Fin 6), InD6 σ → InD6 (c2perm * σ * c2perm⁻¹) → InE8 σ := by
  decide +kernel

theorem e8F_inv : ∀ i, (e8F i)⁻¹ = e8F i := by decide +kernel

theorem fix_W2_of_inE8 : ∀ σ : Perm (Fin 6), InE8 σ → ∀ x : P6, U3.InW2 x →
    G6.permAct 6 σ x = x := by
  decide +kernel

theorem inE8_of_fix : ∀ σ : Perm (Fin 6), G6.permAct 6 σ (A6.pv 0 1) = A6.pv 0 1 →
    G6.permAct 6 σ (A6.pv 2 3) = A6.pv 2 3 → InE8 σ := by
  decide +kernel

theorem inD6_of_inE8 : ∀ σ : Perm (Fin 6), InE8 σ → InD6 σ := by decide +kernel

@[expose] def swF : Fin 8 → Perm (Fin 6) :=
  ![1, 1, 1, swap 1 2 * swap 4 5, 1, swap 1 2 * swap 2 5 * swap 5 3 * swap 3 4,
    swap 0 5 * swap 5 3 * swap 3 2 * swap 1 4, 1]

@[expose] def e8CandS : Fin 4 → Finset (Fin 8) := ![{0, 3}, {0, 5}, {0, 6}, {0, 3, 4, 7}]

@[expose] def e8ConjW : Fin 4 → Perm (Fin 6) := ![swF 3, swF 5, swF 6, swap 1 2 * swap 4 5]

theorem e8_cand_props : ∀ k : Fin 4, Perm.sign (e8ConjW k) = 1 ∧ (0 : Fin 8) ∈ e8CandS k ∧
    (∀ i ∈ e8CandS k, ∀ j ∈ e8CandS k, e8Xor i j ∈ e8CandS k) ∧
    ∀ j ∈ e8CandS k, InD6 (e8ConjW k * e8F j * (e8ConjW k)⁻¹) := by
  decide +kernel

theorem e8_offenders : ∀ f : Fin 8 → Bool, f 0 = true →
    (∀ i j : Fin 8, f i = true → f j = true → f (e8Xor i j) = true) →
    (∃ i, i ≠ 0 ∧ f i = true) →
    32 ≤ (Finset.univ.filter (fun i => f i = true)).card *
      (Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
        ∀ i, f i = true → G6.permAct 6 (e8F i) x = x)).card →
    ((Finset.univ.filter (fun i => f i = true)).card = 2 ∧
        (Finset.univ.filter (fun i => f i = true)).card *
          (Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
            ∀ i, f i = true → G6.permAct 6 (e8F i) x = x)).card = 32) ∨
      ∃ k : Fin 4, 2 * (Finset.univ.filter (fun i => f i = true ∧ i ∈ e8CandS k)).card =
          (Finset.univ.filter (fun i => f i = true)).card ∧
        ∃ j ∈ e8CandS k, f j = true ∧ ¬ InE8 (e8ConjW k * e8F j * (e8ConjW k)⁻¹) := by
  decide +kernel

@[expose] def e8CandSub (k : Fin 4) : Subgroup (Perm (Fin 6)) where
  carrier := {σ | ∃ j ∈ e8CandS k, e8F j = σ}
  one_mem' := ⟨0, (e8_cand_props k).2.1, e8F_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨e8Xor i j, (e8_cand_props k).2.2.1 i hi j hj, (e8F_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, hi, (e8F_inv i).symm⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_card_coords_E8 (S : A6.Setting134 G T L V) {A : Subgroup G}
    (hAN : A ≤ normalizer (V : Set G))
    (hAE : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → InE8 (S.frame.ρ a)) :
    ∃ f : Fin 8 → Bool,
      (∀ i, f i = true ↔ ∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = e8F i) ∧
      (A ⊓ centralizer (V : Set G)).relIndex A =
        (Finset.univ.filter (fun i => f i = true)).card ∧
      Nat.card ↥(V ⊓ centralizer (A : Set G)) =
        (Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
          ∀ i, f i = true → G6.permAct 6 (e8F i) x = x)).card := by
  classical
  have hinj := e8F_inj
  have hsurj := e8F_surj
  let f : Fin 8 → Bool := fun i =>
    decide (∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = e8F i)
  have hf : ∀ i, f i = true ↔
      ∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = e8F i := fun i =>
    decide_eq_true_iff
  refine ⟨f, hf, ?_, ?_⟩
  · rw [← card_autOn_eq_relIndex hAN]
    set X := (A.subgroupOf (normalizer (V : Set G))).map S.frame.ρ with hX
    have h1 : Nat.card ↥(autOn A V) = Nat.card ↥X :=
      Nat.card_congr (mapMulEquivOfKer (conjAct V) S.frame.ρ (s134_conjAct_eq_one_iff_rho S)
        (A.subgroupOf (normalizer (V : Set G)))).toEquiv
    rw [h1]
    let φ : {i : Fin 8 // f i = true} → ↥X := fun i => ⟨e8F i.1, by
      obtain ⟨a, ha, hρ⟩ := (hf i.1).1 i.2
      exact ⟨a, mem_subgroupOf.2 ha, hρ⟩⟩
    have hφ : Function.Bijective φ := by
      refine ⟨fun i j hij => Subtype.ext (hinj _ _ (congrArg Subtype.val hij)), fun σ => ?_⟩
      obtain ⟨a, ha, hρ⟩ := σ.2
      obtain ⟨i, hi⟩ := hsurj _ (hAE a (mem_subgroupOf.1 ha))
      exact ⟨⟨i, (hf i).2 ⟨a, mem_subgroupOf.1 ha, hi.symm⟩⟩, Subtype.ext (hi.trans hρ)⟩
    have e : {i : Fin 8 // f i = true} ≃ ↥X := Equiv.ofBijective φ hφ
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · set s := Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
      ∀ i, f i = true → G6.permAct 6 (e8F i) x = x) with hs
    have hfwd : ∀ w : ↥(V ⊓ centralizer (A : Set G)),
        (S.frame.ψ ⟨w, w.2.1⟩ : P6) ∈ s := by
      intro w
      rw [hs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, G6.mem_coreMod.1 (S.frame.ψ ⟨w, w.2.1⟩).2, fun i hi => ?_⟩
      obtain ⟨a, ha, hρ⟩ := (hf i).1 hi
      have hc : (a : G) * w * (a : G)⁻¹ = w := by
        rw [mem_centralizer_iff.mp w.2.2 a ha, mul_inv_cancel_right]
      have := congrArg Subtype.val ((S.conj_eq_iff a ⟨w, w.2.1⟩).1 hc)
      rw [G6.coreAct_coe, hρ] at this
      exact this
    have hbwd : ∀ x : ↥s, ((S.frame.ψ.symm ⟨x.1, G6.mem_coreMod.2
        (Finset.mem_filter.1 x.2).2.1⟩ : ↥V) : G) ∈ V ⊓ centralizer (A : Set G) := by
      intro x
      refine ⟨(S.frame.ψ.symm _).2, mem_centralizer_iff.2 fun a ha => ?_⟩
      set v : ↥V := S.frame.ψ.symm ⟨x.1, G6.mem_coreMod.2 (Finset.mem_filter.1 x.2).2.1⟩
        with hv
      obtain ⟨i, hi⟩ := hsurj _ (hAE ⟨a, hAN ha⟩ ha)
      have hfi : f i = true := (hf i).2 ⟨⟨a, hAN ha⟩, ha, hi.symm⟩
      have hfix := (Finset.mem_filter.1 x.2).2.2 i hfi
      have hc : (a : G) * v * a⁻¹ = v := by
        refine (S.conj_eq_iff ⟨a, hAN ha⟩ v).2 (Subtype.ext ?_)
        rw [G6.coreAct_coe, ← hi, hv, MulEquiv.apply_symm_apply]
        exact hfix
      calc a * (v : G) = a * v * a⁻¹ * a := by group
        _ = v * a := by rw [hc]
    have e : ↥(V ⊓ centralizer (A : Set G)) ≃ ↥s :=
      { toFun := fun w => ⟨S.frame.ψ ⟨w, w.2.1⟩, hfwd w⟩
        invFun := fun x => ⟨_, hbwd x⟩
        left_inv := fun w => by
          apply Subtype.ext
          show ((S.frame.ψ.symm ⟨(S.frame.ψ ⟨w, w.2.1⟩ : P6), _⟩ : ↥V) : G) = w
          rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
        right_inv := fun x => by
          apply Subtype.ext
          show ((S.frame.ψ (⟨_, (hbwd x).1⟩ : ↥V)) : P6) = x
          have : (⟨_, (hbwd x).1⟩ : ↥V) =
              S.frame.ψ.symm ⟨x.1, G6.mem_coreMod.2 (Finset.mem_filter.1 x.2).2.1⟩ := rfl
          rw [this, MulEquiv.apply_symm_apply] }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem s134_sylow_L2T (S : A6.Setting134 G T L V) : IsSylowTwoOf T (l2Of S ⊔ T) :=
  A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right

theorem s134_R2_le_T (S : A6.Setting134 G T L V) : pCoreOf 2 (l2Of S ⊔ T) ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf (s134_sylow_L2T S)

theorem s134_rho_E8 (S : A6.Setting134 G T L V) {g : G} (hg : g ∈ pCoreOf 2 (l2Of S ⊔ T))
    (hgN : g ∈ normalizer (V : Set G)) : InE8 (S.frame.ρ ⟨g, hgN⟩) := by
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  have hgT := s134_R2_le_T S hg
  have hcg : c * g * c⁻¹ ∈ pCoreOf 2 (l2Of S ⊔ T) :=
    (mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (l2Of S ⊔ T) (mem_sup_left hcL2)) g).1 hg
  have hcgN : c * g * c⁻¹ ∈ normalizer (V : Set G) := mul_mem (mul_mem hcN hgN) (inv_mem hcN)
  have h1 : InD6 (S.frame.ρ ⟨c * g * c⁻¹, hcgN⟩) := S.frame.T_D _ (s134_R2_le_T S hcg)
  have e : (⟨c * g * c⁻¹, hcgN⟩ : ↥(normalizer (V : Set G))) =
      ⟨c, hcN⟩ * ⟨g, hgN⟩ * (⟨c, hcN⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hcρ] at h1
  exact inE8_of_inD6_conj _ (S.frame.T_D _ hgT) h1

theorem s134_pCoreOf_L_le_T (S : A6.Setting134 G T L V) : pCoreOf 2 L ≤ T :=
  (A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)

theorem s134_mem_T_of_inD6 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {x : G}
    (hx : x ∈ L ⊔ T) (hxN : x ∈ normalizer (V : Set G)) (hD : InD6 (S.frame.ρ ⟨x, hxN⟩)) :
    x ∈ T := by
  obtain ⟨l, hl, t, ht, rfl⟩ := s134_mul_decomp S hx
  have hlN : l ∈ normalizer (V : Set G) := S.frame.L_le hl
  have htN : t ∈ normalizer (V : Set G) := S.frame.T_le ht
  have e : (⟨l * t, hxN⟩ : ↥(normalizer (V : Set G))) = ⟨l, hlN⟩ * ⟨t, htN⟩ := rfl
  rw [e, map_mul] at hD
  have hlD : InD6 (S.frame.ρ ⟨l, hlN⟩) := by
    have := D6sub.mul_mem (show S.frame.ρ ⟨l, hlN⟩ * S.frame.ρ ⟨t, htN⟩ ∈ D6sub from hD)
      (D6sub.inv_mem (show S.frame.ρ ⟨t, htN⟩ ∈ D6sub from S.frame.T_D _ ht))
    rwa [mul_inv_cancel_right] at this
  have hlA : S.frame.ρ ⟨l, hlN⟩ ∈ alternatingGroup (Fin 6) :=
    (S.frame.image_L _).1 ⟨⟨l, hlN⟩, hl, rfl⟩
  obtain ⟨g, ⟨hgT, hgL⟩, hgρ⟩ := s134_exists_TL S hlD hlA
  have hgl : (g : G)⁻¹ * l ∈ L ⊓ centralizer (V : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem hgL) hl, (s134_rho_eq_one_iff S (g⁻¹ * ⟨l, hlN⟩)).1 ?_⟩
    rw [map_mul, map_inv, hgρ, inv_mul_cancel]
  have hT : (g : G)⁻¹ * l ∈ T :=
    s134_pCoreOf_L_le_T S (((s134_centralizer_le_o2Z S).trans (o2Z_le_pCoreOf_of_a6 he)) hgl)
  have hlT : l ∈ T := by
    have := T.mul_mem hgT hT
    rwa [mul_inv_cancel_left] at this
  exact T.mul_mem hlT ht

theorem s134_inE8_of_mem_centralizer_V2 (S : A6.Setting134 G T L V)
    (g : ↥(normalizer (V : Set G))) (hg : (g : G) ∈ centralizer (v2Of S : Set G)) :
    InE8 (S.frame.ρ g) := by
  obtain ⟨⟨h01, c01⟩, ⟨h23, c23⟩, -⟩ := pv_W2
  have hfix : ∀ x : P6, U3.InW2 x → ∀ hx : x ∈ G6.coreMod 6,
      G6.permAct 6 (S.frame.ρ g) x = x := by
    intro x hxW hx
    set v : ↥V := S.frame.ψ.symm ⟨x, hx⟩ with hv
    have hvV2 : (v : G) ∈ v2Of S := by
      show (v : G) ∈ S.pre W2sub
      refine S.mem_pre.2 ⟨v.2, ?_⟩
      show U3.InW2 ((S.frame.ψ ⟨(v : G), v.2⟩ : ↥(G6.coreMod 6)) : P6)
      rw [Subtype.coe_eta, hv, MulEquiv.apply_symm_apply]
      exact hxW
    have hc : (g : G) * v * (g : G)⁻¹ = v := by
      rw [← mem_centralizer_iff.mp hg v hvV2, mul_inv_cancel_right]
    have := congrArg Subtype.val ((S.conj_eq_iff g v).1 hc)
    rw [G6.coreAct_coe, hv, MulEquiv.apply_symm_apply] at this
    exact this
  exact inE8_of_fix _ (hfix _ h01 c01) (hfix _ h23 c23)

theorem s134_mem_centralizer_V2_of_inE8 (S : A6.Setting134 G T L V)
    (g : ↥(normalizer (V : Set G))) (hg : InE8 (S.frame.ρ g)) :
    (g : G) ∈ centralizer (v2Of S : Set G) := by
  refine mem_centralizer_iff.2 fun v hv => ?_
  have hv' : v ∈ S.pre W2sub := hv
  obtain ⟨hvV, hvW⟩ := S.mem_pre.1 hv'
  have hc : (g : G) * v * (g : G)⁻¹ = v := by
    refine (S.conj_eq_iff g ⟨v, hvV⟩).2 (Subtype.ext ?_)
    rw [G6.coreAct_coe]
    exact fix_W2_of_inE8 _ hg _ hvW
  calc v * (g : G) = (g : G) * v * (g : G)⁻¹ * g := by rw [hc]
    _ = g * v := by group

theorem s134_one_lt_pRank (S : A6.Setting134 G T L V) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) : 1 < Open.pRank 2 T := by
  have h1 := hA.2.2 V S.V_le_T (s134_elemAbelian_V S)
  have h2 : Nat.card A * 2 ^ 0 = 2 ^ Open.pRank 2 T :=
    (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at h2
  rw [S.card_V, h2] at h1
  by_contra h
  have h3 : 2 ^ Open.pRank 2 T ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem s134_le_thompsonJi_one (S : A6.Setting134 G T L V) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) : A ≤ thompsonJi T 1 :=
  (le_iSup₂_of_le A (isMaxElemAbelian_iff_corank_zero.mp hA) le_rfl :
    A ≤ thompsonJi T 0).trans (thompsonJi_mono zero_le_one (s134_one_lt_pRank S hA))

theorem s134_no_conj (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hJ1 : thompsonJi T 1 ≤ centralizer (v2Of S : Set G)) {A B : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hBA : B ≤ A) (hB2 : Nat.card A = 2 * Nat.card B)
    {w : Perm (Fin 6)} (hw : Perm.sign w = 1)
    (hwD : ∀ b : ↥(normalizer (V : Set G)), (b : G) ∈ B → InD6 (w * S.frame.ρ b * w⁻¹))
    (hwE : ∃ b : ↥(normalizer (V : Set G)), (b : G) ∈ B ∧ ¬ InE8 (w * S.frame.ρ b * w⁻¹)) :
    False := by
  obtain ⟨g, hgL, hgρ⟩ := (S.frame.image_L w).2 (Perm.mem_alternatingGroup.2 hw)
  have hAN : A ≤ normalizer (V : Set G) := hA.1.trans S.frame.T_le
  have hconj : ∀ b : ↥(normalizer (V : Set G)), (b : G) ∈ B →
      (g : G) * b * (g : G)⁻¹ ∈ T ∧ ∃ hN : (g : G) * b * (g : G)⁻¹ ∈ normalizer (V : Set G),
        S.frame.ρ ⟨_, hN⟩ = w * S.frame.ρ b * w⁻¹ := by
    intro b hb
    have hN : (g : G) * b * (g : G)⁻¹ ∈ normalizer (V : Set G) := (g * b * g⁻¹).2
    have hρ : S.frame.ρ ⟨_, hN⟩ = w * S.frame.ρ b * w⁻¹ := by
      have e : (⟨_, hN⟩ : ↥(normalizer (V : Set G))) = g * b * g⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hgρ]
    have hx : (g : G) * b * (g : G)⁻¹ ∈ L ⊔ T :=
      mul_mem (mul_mem (mem_sup_left hgL) (mem_sup_right (hA.1 (hBA hb))))
        (inv_mem (mem_sup_left hgL))
    exact ⟨s134_mem_T_of_inD6 S he hx hN (by rw [hρ]; exact hwD b hb), hN, hρ⟩
  set B' := B6.conjSub (g : G) B with hB'
  have hB'T : B' ≤ T := by
    intro x hx
    rw [hB', B6.mem_conjSub] at hx
    have hxN : (g : G)⁻¹ * x * g ∈ normalizer (V : Set G) := hAN (hBA hx)
    have := (hconj ⟨_, hxN⟩ hx).1
    simpa [mul_assoc] using this
  have hBe : IsElemAbelian 2 B := B6.isElemAbelian_iff.2
    ⟨fun a ha b hb => (B6.isElemAbelian_iff.1 hA.2.1).1 a (hBA ha) b (hBA hb),
      fun a ha => hA.2.1.2 a (hBA ha)⟩
  have hB'1 : IsElemAbelianCorank T 1 B' := by
    refine ⟨hB'T, B6.isElemAbelian_conjSub hBe _, ?_⟩
    rw [hB', B6.card_conjSub, pow_one]
    have h2 := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    rw [pow_zero, mul_one, hB2] at h2
    rw [← h2, mul_comm]
  have hB'J : B' ≤ centralizer (v2Of S : Set G) :=
    (le_iSup₂_of_le B' hB'1 le_rfl : B' ≤ thompsonJi T 1).trans hJ1
  obtain ⟨b, hb, hbE⟩ := hwE
  obtain ⟨-, hN, hρ⟩ := hconj b hb
  have hmem : (g : G) * b * (g : G)⁻¹ ∈ B' := by
    rw [hB', B6.mem_conjSub]
    simpa [mul_assoc] using hb
  apply hbE
  rw [← hρ]
  exact s134_inE8_of_mem_centralizer_V2 S _ (hB'J hmem)

theorem s134_offender (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hJ1 : thompsonJi T 1 ≤ centralizer (v2Of S : Set G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAC : ¬ A ≤ centralizer (V : Set G)) :
    (A ⊓ centralizer (V : Set G)).relIndex A = 2 ∧
      Nat.card V = (A ⊓ centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ centralizer (A : Set G)) := by
  classical
  have hAN : A ≤ normalizer (V : Set G) := hA.1.trans S.frame.T_le
  have hAE : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → InE8 (S.frame.ρ a) :=
    fun a ha => s134_inE8_of_mem_centralizer_V2 S a (hJ1 (s134_le_thompsonJi_one S hA ha))
  obtain ⟨f, hf, hrel, hcard⟩ := s134_card_coords_E8 S hAN hAE
  have hineq := card_le_relIndex_mul_card (s134_elemAbelian_V S) S.V_le_T hA
  rw [hrel, hcard, S.card_V] at hineq
  have hf0 : f 0 = true := (hf 0).2 ⟨1, A.one_mem, by rw [map_one, e8F_zero]⟩
  have hfx : ∀ i j, f i = true → f j = true → f (e8Xor i j) = true := by
    intro i j hi hj
    obtain ⟨a, ha, hai⟩ := (hf i).1 hi
    obtain ⟨b, hb, hbj⟩ := (hf j).1 hj
    exact (hf _).2 ⟨a * b, A.mul_mem ha hb, by rw [map_mul, hai, hbj, e8F_mul]⟩
  have hfne : ∃ i, i ≠ 0 ∧ f i = true := by
    obtain ⟨a, ha, haC⟩ := IsConcreteLE.not_le_iff_exists.1 hAC
    obtain ⟨i, hi⟩ := e8F_surj _ (hAE ⟨a, hAN ha⟩ ha)
    refine ⟨i, fun h0 => haC ?_, (hf i).2 ⟨⟨a, hAN ha⟩, ha, hi.symm⟩⟩
    have : S.frame.ρ ⟨a, hAN ha⟩ = 1 := by rw [← hi, h0, e8F_zero]
    exact (s134_rho_eq_one_iff S _).1 this
  rcases e8_offenders f hf0 hfx hfne hineq with ⟨h2, h32⟩ | ⟨k, hk2, j, hjk, hfj, hjE⟩
  · refine ⟨by rw [hrel, h2], ?_⟩
    rw [hrel, hcard, S.card_V, h32]
  exfalso
  set B := A ⊓ ((e8CandSub k).comap S.frame.ρ).map (normalizer (V : Set G)).subtype with hBdef
  have hBA : B ≤ A := inf_le_left
  have hmemB : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A →
      (∃ j ∈ e8CandS k, e8F j = S.frame.ρ a) → (a : G) ∈ B :=
    fun a ha hj => ⟨ha, a, hj, rfl⟩
  have hBmem : ∀ b : ↥(normalizer (V : Set G)), (b : G) ∈ B →
      ∃ j ∈ e8CandS k, e8F j = S.frame.ρ b := by
    rintro b ⟨-, b', hb', hbb'⟩
    have : b' = b := Subtype.ext hbb'
    rw [← this]
    exact hb'
  obtain ⟨fB, hfB, hrelB, -⟩ := s134_card_coords_E8 S (hBA.trans hAN) fun b hb => hAE b (hBA hb)
  have hfBf : ∀ i, fB i = true ↔ f i = true ∧ i ∈ e8CandS k := by
    intro i
    constructor
    · intro h
      obtain ⟨b, hb, hbi⟩ := (hfB i).1 h
      refine ⟨(hf i).2 ⟨b, hBA hb, hbi⟩, ?_⟩
      obtain ⟨j', hj', hj'e⟩ := hBmem b hb
      rw [hbi] at hj'e
      rwa [← e8F_inj _ _ hj'e]
    · rintro ⟨h, hi⟩
      obtain ⟨a, ha, hai⟩ := (hf i).1 h
      exact (hfB i).2 ⟨a, hmemB a ha ⟨i, hi, hai.symm⟩, hai⟩
  have hBC : B ⊓ centralizer (V : Set G) = A ⊓ centralizer (V : Set G) := by
    refine le_antisymm (inf_le_inf_right _ hBA) fun x hx => ⟨?_, hx.2⟩
    have hxN : x ∈ normalizer (V : Set G) := hAN hx.1
    refine hmemB ⟨x, hxN⟩ hx.1 ⟨0, (e8_cand_props k).2.1, ?_⟩
    rw [e8F_zero, eq_comm]
    exact (s134_rho_eq_one_iff S ⟨x, hxN⟩).2 hx.2
  have hcardA := relIndex_mul_card (A ⊓ centralizer (V : Set G)) A
  have hcardB := relIndex_mul_card (B ⊓ centralizer (V : Set G)) B
  rw [inf_eq_left.2 inf_le_left] at hcardA
  rw [inf_eq_left.2 inf_le_left] at hcardB
  rw [hBC] at hcardB
  rw [hBC] at hrelB
  have hfilt : Finset.univ.filter (fun i => fB i = true) =
      Finset.univ.filter (fun i => f i = true ∧ i ∈ e8CandS k) :=
    Finset.filter_congr fun i _ => hfBf i
  have hB2 : Nat.card A = 2 * Nat.card B := by
    rw [← hcardA, ← hcardB, hrel, ← hk2, hrelB, hfilt]
    ring
  refine s134_no_conj S he hJ1 hA hBA hB2 (e8_cand_props k).1 (fun b hb => ?_) ?_
  · obtain ⟨j', hj', hj'e⟩ := hBmem b hb
    rw [← hj'e]
    exact (e8_cand_props k).2.2.2 j' hj'
  · obtain ⟨a, ha, haj⟩ := (hf j).1 hfj
    exact ⟨a, hmemB a ha ⟨j, hjk, haj.symm⟩, by rw [haj]; exact hjE⟩

end CFSG.Quasithin.H13.U3
