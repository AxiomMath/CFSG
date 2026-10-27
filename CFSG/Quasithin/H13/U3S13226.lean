module

public import CFSG.Quasithin.H13.U3S1344A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

@[expose] def k4xF : Fin 8 → Perm (Fin 6) :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2, swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3 * swap 4 5,
    swap 0 3 * swap 1 2 * swap 4 5]

theorem k4xF_inj : ∀ i j : Fin 8, k4xF i = k4xF j → i = j := by decide +kernel

theorem k4xF_surj : ∀ σ ∈ K4xList, ∃ i, k4xF i = σ := by decide +kernel

theorem k4xF_zero : k4xF 0 = 1 := by decide +kernel

theorem k4xF_not_K4 : ∀ i : Fin 8, 4 ≤ (i : ℕ) → k4xF i ∉ K4List := by decide +kernel

theorem K4x_sign : ∀ σ ∈ K4xList, Perm.sign σ = 1 → σ ∈ K4List := by decide +kernel

theorem K4_le_K4x : ∀ σ ∈ K4List, σ ∈ K4xList := by decide +kernel

theorem k4x_card_mul_le : ∀ f : Fin 8 → Bool,
    (Finset.univ.filter (fun i => f i = true)).card *
      (Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
        ∀ i, f i = true → G6.permAct 6 (k4xF i) x = x)).card ≤ 32 := by
  decide +kernel

theorem k4_card_mul_lt : ∀ f : Fin 8 → Bool, (∀ i : Fin 8, 4 ≤ (i : ℕ) → f i = false) →
    (∃ i, i ≠ 0 ∧ f i = true) →
    (Finset.univ.filter (fun i => f i = true)).card *
      (Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
        ∀ i, f i = true → G6.permAct 6 (k4xF i) x = x)).card < 32 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_elemAbelian_V (S : A6.Setting134 G T L V) : IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => S.frame.ψ.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩,
    fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : ↥V) ^ 2 = 1 := by
    apply S.frame.ψ.injective
    rw [map_pow, map_one]
    exact Subtype.ext (sq_P6 _)
  simpa using congrArg Subtype.val h

theorem s134_V_le_r1Of (S : A6.Setting134 G T L V) : V ≤ r1Of T L V := by
  intro v hv
  refine (s134_mem_r1Of_iff S).2 ⟨S.V_le_T hv, fun hx => ?_⟩
  have hc : v ∈ centralizer (V : Set G) := mem_centralizer_iff.2 fun w hw =>
    congrArg Subtype.val ((s134_elemAbelian_V S).1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  rw [(s134_rho_eq_one_iff S ⟨v, hx⟩).2 hc]
  exact List.mem_cons_self

theorem s134_cT_le_r1Of (S : A6.Setting134 G T L V) :
    T ⊓ centralizer (V : Set G) ≤ r1Of T L V := by
  intro x hx
  refine (s134_mem_r1Of_iff S).2 ⟨hx.1, fun hxN => ?_⟩
  rw [(s134_rho_eq_one_iff S ⟨x, hxN⟩).2 hx.2]
  exact List.mem_cons_self

theorem s134_card_coords (S : A6.Setting134 G T L V) {A : Subgroup G}
    (hAN : A ≤ normalizer (V : Set G))
    (hAK : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → S.frame.ρ a ∈ K4xList) :
    ∃ f : Fin 8 → Bool,
      (∀ i, f i = true ↔ ∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = k4xF i) ∧
      (A ⊓ centralizer (V : Set G)).relIndex A =
        (Finset.univ.filter (fun i => f i = true)).card ∧
      Nat.card ↥(V ⊓ centralizer (A : Set G)) =
        (Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
          ∀ i, f i = true → G6.permAct 6 (k4xF i) x = x)).card := by
  classical
  have hinj := k4xF_inj
  have hsurj := k4xF_surj
  let f : Fin 8 → Bool := fun i =>
    decide (∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = k4xF i)
  have hf : ∀ i, f i = true ↔
      ∃ a : ↥(normalizer (V : Set G)), (a : G) ∈ A ∧ S.frame.ρ a = k4xF i := fun i =>
    decide_eq_true_iff
  refine ⟨f, hf, ?_, ?_⟩
  ·
    rw [← card_autOn_eq_relIndex hAN]
    set X := (A.subgroupOf (normalizer (V : Set G))).map S.frame.ρ with hX
    have h1 : Nat.card ↥(autOn A V) = Nat.card ↥X :=
      Nat.card_congr (mapMulEquivOfKer (conjAct V) S.frame.ρ (s134_conjAct_eq_one_iff_rho S)
        (A.subgroupOf (normalizer (V : Set G)))).toEquiv
    rw [h1]
    let φ : {i : Fin 8 // f i = true} → ↥X := fun i => ⟨k4xF i.1, by
      obtain ⟨a, ha, hρ⟩ := (hf i.1).1 i.2
      exact ⟨a, mem_subgroupOf.2 ha, hρ⟩⟩
    have hφ : Function.Bijective φ := by
      refine ⟨fun i j hij => Subtype.ext (hinj _ _ (congrArg Subtype.val hij)), fun σ => ?_⟩
      obtain ⟨a, ha, hρ⟩ := σ.2
      obtain ⟨i, hi⟩ := hsurj _ (hAK a (mem_subgroupOf.1 ha))
      exact ⟨⟨i, (hf i).2 ⟨a, mem_subgroupOf.1 ha, hi.symm⟩⟩,
        Subtype.ext (hi.trans hρ)⟩
    have e : {i : Fin 8 // f i = true} ≃ ↥X := Equiv.ofBijective φ hφ
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  ·
    set s := Finset.univ.filter (fun x : P6 => (∑ i, Multiplicative.toAdd x i = 0) ∧
      ∀ i, f i = true → G6.permAct 6 (k4xF i) x = x) with hs
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
      obtain ⟨i, hi⟩ := hsurj _ (hAK ⟨a, hAN ha⟩ ha)
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

theorem s134_relIndex_mul_card_le (S : A6.Setting134 G T L V) {A : Subgroup G}
    (hAN : A ≤ normalizer (V : Set G))
    (hAK : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → S.frame.ρ a ∈ K4xList) :
    (A ⊓ centralizer (V : Set G)).relIndex A * Nat.card ↥(V ⊓ centralizer (A : Set G)) ≤ 32 := by
  obtain ⟨f, -, h1, h2⟩ := s134_card_coords S hAN hAK
  rw [h1, h2]
  exact k4x_card_mul_le f

theorem s134_relIndex_mul_card_lt (S : A6.Setting134 G T L V) {A : Subgroup G}
    (hAN : A ≤ normalizer (V : Set G))
    (hAK : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → S.frame.ρ a ∈ K4List)
    (hA : ¬ A ≤ centralizer (V : Set G)) :
    (A ⊓ centralizer (V : Set G)).relIndex A * Nat.card ↥(V ⊓ centralizer (A : Set G)) < 32 := by
  have hsurj := k4xF_surj
  have h0 := k4xF_zero
  have h4 := k4xF_not_K4
  have hK4x := K4_le_K4x
  obtain ⟨f, hf, h1, h2⟩ := s134_card_coords S hAN fun a ha => hK4x _ (hAK a ha)
  rw [h1, h2]
  refine k4_card_mul_lt f (fun i hi => ?_) ?_
  · by_contra hfi
    obtain ⟨a, ha, hρ⟩ := (hf i).1 (Bool.not_eq_false _ ▸ hfi)
    exact h4 i hi (hρ ▸ hAK a ha)
  · obtain ⟨x, hxA, hxC⟩ := IsConcreteLE.not_le_iff_exists.1 hA
    obtain ⟨i, hi⟩ := hsurj _ (hK4x _ (hAK ⟨x, hAN hxA⟩ hxA))
    refine ⟨i, fun h0i => hxC ?_, (hf i).2 ⟨⟨x, hAN hxA⟩, hxA, hi.symm⟩⟩
    rw [h0i, h0] at hi
    exact (s134_rho_eq_one_iff S ⟨x, hAN hxA⟩).1 hi.symm

theorem s134_lemma13_2_2_six (S : A6.Setting134 G T L V) :
    CFSG.Open.pRank 2 (r1Of T L V ⊓ centralizer (V : Set G)) = CFSG.Open.pRank 2 (r1Of T L V) ∧
      (∀ A, IsMaxElemAbelian (r1Of T L V ⊓ centralizer (V : Set G)) A →
        IsMaxElemAbelian (r1Of T L V) A) ∧
      V ≤ thompsonJ (r1Of T L V) := by
  have hV := s134_elemAbelian_V S
  have hVR := s134_V_le_r1Of S
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (r1Of T L V)
  have hAN : A ≤ normalizer (V : Set G) :=
    hA.1.trans ((r1Of_le_T T L V).trans S.frame.T_le)
  have hAK : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → S.frame.ρ a ∈ K4xList :=
    fun a ha => ((s134_mem_r1Of_iff S).1 (hA.1 ha)).2 a.2
  have hle := card_le_relIndex_mul_card hV hVR hA
  have hge := s134_relIndex_mul_card_le S hAN hAK
  rw [S.card_V] at hle
  obtain ⟨-, hpr, hsub, hVJ, -⟩ := B24_three hV hVR hA (by rw [S.card_V]; omega)
  refine ⟨hpr, hsub, hVJ.trans (((B2F.omegaOneCenterOf_le_centerOf _).trans inf_le_left).trans
    (iSup₂_le fun A' hA' => le_iSup₂_of_le A' (hsub A' hA') le_rfl))⟩

theorem s134_pCoreOf_LT_le (S : A6.Setting134 G T L V) :
    pCoreOf 2 (L ⊔ T) ≤ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred : IsTwoReducedIn (L ⊔ T) (reducedAggregate (L ⊔ T)) :=
    isTwoReducedIn_reducedAggregate (L ⊔ T)
  refine le_trans ?_ (centralizer_le S.irr.1)
  refine hred.2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 _)
    (LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => ?_
  obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact one_mem _

theorem s134_cT (S : A6.Setting134 G T L V) :
    T ⊓ centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  have hOV : pCoreOf 2 L ≤ centralizer (V : Set G) :=
    (A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (s134_pCoreOf_LT_le S)
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp S.h13.faithful.1.2.1
  have hCo := centralizer_le_o2Z_of_isA6On S.frame.L_le hOV S.fsu.quasisimple (s134_isA6On S)
  have hZ : ∀ c ∈ L ⊓ centralizer (V : Set G), ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
    fun c hc l hl => (A6.mem_o2Z_iff.1 (hCo hc)).2 l hl
  have hOT : pCoreOf 2 L ≤ T :=
    (A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  refine A6.inf_centralizer_eq_pCoreOf S.h13.sylow.1
    (pCoreOf_le_of_sylow S.h13.sylow le_sup_right) S.frame.L_le S.frame.T_le
    (s134_pCoreOf_LT_le S) fun l hl t ht => hOT ?_
  exact A6.comm_mem_of_centralizer (LieType.BorelTits.pCoreOf_le 2 L)
    (LieType.BorelTits.le_normalizer_pCoreOf 2 L) hperf S.frame.L_le hZ (S.T_le_NL ht.1) ht.2 hl

theorem s134_thompsonJ_r1Of_le (S : A6.Setting134 G T L V)
    (hT6 : ∀ t : ↥(normalizer (V : Set G)), (t : G) ∈ T → Perm.sign (S.frame.ρ t) = 1) :
    thompsonJ (r1Of T L V) ≤ centralizer (V : Set G) := by
  have hV := s134_elemAbelian_V S
  have hVR := s134_V_le_r1Of S
  have hK4 := K4x_sign
  refine iSup₂_le fun A hA => ?_
  by_contra hAC
  have hAN : A ≤ normalizer (V : Set G) :=
    hA.1.trans ((r1Of_le_T T L V).trans S.frame.T_le)
  have hAK : ∀ a : ↥(normalizer (V : Set G)), (a : G) ∈ A → S.frame.ρ a ∈ K4List :=
    fun a ha => hK4 _ (((s134_mem_r1Of_iff S).1 (hA.1 ha)).2 a.2)
      (hT6 a (r1Of_le_T T L V (hA.1 ha)))
  have hle := card_le_relIndex_mul_card hV hVR hA
  have hlt := s134_relIndex_mul_card_lt S hAN hAK hAC
  rw [S.card_V] at hle
  omega

theorem s134_thompsonJ_r1Of_eq (S : A6.Setting134 G T L V)
    (hT6 : ∀ t : ↥(normalizer (V : Set G)), (t : G) ∈ T → Perm.sign (S.frame.ρ t) = 1) :
    thompsonJ (r1Of T L V) = thompsonJ (pCoreOf 2 (L ⊔ T)) := by
  rw [← s134_cT S]
  exact thompsonJ_eq_of_le (le_inf ((iSup₂_le fun _ hA => hA.1).trans (r1Of_le_T T L V))
    (s134_thompsonJ_r1Of_le S hT6)) (s134_cT_le_r1Of S)

end CFSG.Quasithin.H13.U3
