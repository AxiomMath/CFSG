module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPathUnique
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPathExists

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

theorem finite_gPath [Finite V] (s : ℕ) : Finite (GPath Γ s) :=
  Finite.of_injective (fun p => fun i : Fin (s + 1) => p i) (by
    intro p q h
    apply GPath.ext'
    intro i hi
    have := congrFun h ⟨i, by omega⟩
    simpa using this)

theorem exists_closed_isGoodPath [Finite V] [Finite H] {n : ℕ} (hn : 3 ≤ n)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w) (hL : ∀ z, LocalFacts H Γ z)
    {p : GPath Γ (n + 1)} (hp : p.NoBack) :
    ∃ (t : ℕ) (x : ℤ → V), 0 < t ∧ (∀ i, x (i + t) = x i) ∧ (∀ i, Γ.Adj (x i) (x (i + 1))) ∧
      (∀ i, x i ≠ x (i + 2)) ∧ (∀ i : ℕ, i ≤ n + 1 → x i = p i) ∧
      ∀ (i : ℤ) (s : ℕ) (q : GPath Γ s), (∀ j : ℕ, j ≤ s → q j = x (i + j)) → IsGoodPath H q := by
  classical
  let S := {W : GPath Γ (n + 1) // IsGoodPath H W}
  haveI hGfin : Finite (GPath Γ (n + 1)) := finite_gPath (n + 1)
  haveI hSfin : Finite S := Finite.of_injective Subtype.val (fun _ _ h => Subtype.ext h)
  have hex : ∀ W : S, ∃ w, ∃ h : Γ.Adj (W.1 (n + 1)) w, IsGoodPath H (W.1.snoc w h) :=
    fun W => exists_isGoodPath_snoc hn hM hne hL (s := n + 1) (by omega) W.2
  let cont : S → V := fun W => Classical.choose (hex W)
  have cont_adj : ∀ W : S, Γ.Adj (W.1 (n + 1)) (cont W) :=
    fun W => Classical.choose (Classical.choose_spec (hex W))
  have cont_good : ∀ W : S, IsGoodPath H (W.1.snoc (cont W) (cont_adj W)) :=
    fun W => Classical.choose_spec (Classical.choose_spec (hex W))
  let σ : S → S := fun W =>
    ⟨(W.1.snoc (cont W) (cont_adj W)).drop 1 (by omega),
      (cont_good W).drop 1 (by omega)⟩
  have σ_apply : ∀ (W : S) (j : ℕ), j ≤ n → (σ W).1 j = W.1 (j + 1) := by
    intro W j hj
    show (W.1.snoc (cont W) (cont_adj W)).drop 1 (by omega) j = W.1 (j + 1)
    rw [GPath.drop_apply _ _ _ (by omega)]
    rw [show 1 + j = j + 1 by omega]
    exact GPath.snoc_of_le _ _ _ (by omega)
  have σ_last : ∀ W : S, (σ W).1 (n + 1) = cont W := by
    intro W
    show (W.1.snoc (cont W) (cont_adj W)).drop 1 (by omega) (n + 1) = cont W
    rw [GPath.drop_apply _ _ _ (by omega)]
    rw [show 1 + (n + 1) = (n + 1) + 1 by omega, GPath.snoc_last]
  have σ_inj : Function.Injective σ := by
    intro W W' hWW'
    let V : GPath Γ (n + 1) := (σ W).1
    let V' : GPath Γ (n + 1) := (σ W').1
    have hV : V = V' := congrArg Subtype.val hWW'
    have hV0 : V 0 = W.1 1 := σ_apply W 0 (by omega)
    have hV0' : V' 0 = W'.1 1 := σ_apply W' 0 (by omega)
    have hlast : V (n + 1) = cont W := by
      show (σ W).1 (n + 1) = cont W
      exact σ_last W
    have hlast' : V' (n + 1) = cont W' := by
      show (σ W').1 (n + 1) = cont W'
      exact σ_last W'
    have hadjW : Γ.Adj (V.rev (n + 1)) (W.1 0) := by
      rw [GPath.rev_apply _ (by omega)]
      rw [show n + 1 - (n + 1) = 0 by omega]
      rw [show V 0 = W.1 1 from hV0]
      exact (W.1.adj 0 (by omega)).symm
    have hadjW' : Γ.Adj (V.rev (n + 1)) (W'.1 0) := by
      rw [GPath.rev_apply _ (by omega)]
      rw [show n + 1 - (n + 1) = 0 by omega]
      rw [show V 0 = W'.1 1 by rw [hV]; exact hV0']
      exact (W'.1.adj 0 (by omega)).symm
    have hgoodW : IsGoodPath H (V.rev.snoc (W.1 0) hadjW) := by
      have heq : V.rev.snoc (W.1 0) hadjW = (W.1.snoc (cont W) (cont_adj W)).rev := by
        apply GPath.ext'
        intro i hi
        by_cases hi' : i ≤ n + 1
        · rw [GPath.snoc_of_le _ _ _ hi', GPath.rev_apply _ hi']
          rw [GPath.rev_apply _ (by omega)]
          have hVval : V (n + 1 - i) = (W.1.snoc (cont W) (cont_adj W)) (n + 2 - i) := by
            show (W.1.snoc (cont W) (cont_adj W)).drop 1 (by omega) (n + 1 - i) =
              (W.1.snoc (cont W) (cont_adj W)) (n + 2 - i)
            rw [GPath.drop_apply _ _ _ (by omega)]
            rw [show 1 + (n + 1 - i) = n + 2 - i by omega]
          rw [hVval]
        · have hi2 : i = n + 2 := by omega
          subst hi2
          rw [GPath.snoc_last, GPath.rev_apply _ (by omega)]
          rw [show n + 2 - (n + 2) = 0 by omega, GPath.snoc_of_le _ _ _ (by omega)]
      rw [heq]
      exact (cont_good W).rev
    have hgoodW' : IsGoodPath H (V.rev.snoc (W'.1 0) hadjW') := by
      have heq : V.rev.snoc (W'.1 0) hadjW' = (W'.1.snoc (cont W') (cont_adj W')).rev := by
        apply GPath.ext'
        intro i hi
        by_cases hi' : i ≤ n + 1
        · rw [GPath.snoc_of_le _ _ _ hi', GPath.rev_apply _ hi']
          rw [GPath.rev_apply _ (by omega)]
          have hVval : V (n + 1 - i) = (W'.1.snoc (cont W') (cont_adj W')) (n + 2 - i) := by
            rw [show V (n + 1 - i) = V' (n + 1 - i) from by rw [hV]]
            show (W'.1.snoc (cont W') (cont_adj W')).drop 1 (by omega) (n + 1 - i) =
              (W'.1.snoc (cont W') (cont_adj W')) (n + 2 - i)
            rw [GPath.drop_apply _ _ _ (by omega)]
            rw [show 1 + (n + 1 - i) = n + 2 - i by omega]
          rw [hVval]
        · have hi2 : i = n + 2 := by omega
          subst hi2
          rw [GPath.snoc_last, GPath.rev_apply _ (by omega)]
          rw [show n + 2 - (n + 2) = 0 by omega,
            GPath.snoc_of_le _ _ _ (by omega)]
      rw [heq]
      exact (cont_good W').rev
    have h0 : W.1 0 = W'.1 0 :=
      isGoodPath_snoc_unique hn hW hL (s := n + 1) (by omega) hadjW hadjW' hgoodW hgoodW'
    apply Subtype.ext
    apply GPath.ext'
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      exact h0
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j ≤ n := by omega
      calc
        W.1 (j + 1) = (σ W).1 j := (σ_apply W j hj).symm
        _ = (σ W').1 j := congrArg (fun q : GPath Γ (n + 1) => q j) hV
        _ = W'.1 (j + 1) := σ_apply W' j hj
  obtain ⟨t, ht, hσt⟩ : ∃ t : ℕ, 0 < t ∧ σ^[t] = id := by
    let e : Equiv.Perm S := Equiv.ofBijective σ (Function.Injective.bijective_of_finite σ_inj)
    have he : ⇑e = σ := by
      funext W
      exact Equiv.ofBijective_apply σ _ W
    refine ⟨orderOf e, orderOf_pos e, ?_⟩
    have hc : ⇑(e ^ orderOf e) = (⇑e)^[orderOf e] := Equiv.Perm.coe_pow e (orderOf e)
    rw [pow_orderOf_eq_one, Equiv.Perm.coe_one, he] at hc
    exact hc.symm
  let pS : S :=
    ⟨p, isGoodPath_of_noBack hn hM hne (fun z => (hL z).kernel_le) (by omega) hp⟩
  let Wof : ℤ → S := fun i => σ^[((i % (t : ℤ)).toNat)] pS
  let x : ℤ → V := fun i => (Wof i).1 0
  have hiter_mod : ∀ u : ℕ, σ^[u] = σ^[u % t] := by
    have hmul : ∀ q : ℕ, σ^[q * t] = id := by
      intro q
      rw [Nat.mul_comm, Function.iterate_mul, hσt, Function.iterate_id]
    intro u
    conv_lhs => rw [← Nat.mod_add_div' u t]
    rw [add_comm, Function.iterate_add, hmul, Function.id_comp]
  have σ_iter_apply : ∀ (m j : ℕ) (W : S), j + m ≤ n + 1 → (σ^[m] W).1 j = W.1 (j + m) := by
    intro m
    induction m with
    | zero =>
      intro j W _
      simp
    | succ m ih =>
      intro j W h
      rw [Function.iterate_succ, Function.comp_apply]
      rw [ih j (σ W) (by omega)]
      rw [σ_apply W (j + m) (by omega)]
      rw [show j + m + 1 = j + (m + 1) by omega]
  have hres : ∀ (i : ℤ) (m : ℕ),
      (((i + (m : ℤ)) % (t : ℤ)).toNat) = ((i % (t : ℤ)).toNat + m) % t := by
    intro i m
    have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast ht.ne'
    have hk : (((i % (t : ℤ)).toNat : ℤ)) = i % (t : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg i htZ)
    have h1 : ((i + (m : ℤ)) % (t : ℤ)) = (i % (t : ℤ) + (m : ℤ)) % (t : ℤ) :=
      (Int.emod_add_emod i (t : ℤ) (m : ℤ)).symm
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (Int.emod_nonneg (i + (m : ℤ)) htZ)]
    rw [Int.natCast_emod]
    rw [Nat.cast_add, hk]
    exact h1
  have Wof_add_nat : ∀ (i : ℤ) (m : ℕ), Wof (i + (m : ℤ)) = σ^[m] (Wof i) := by
    intro i m
    unfold Wof
    rw [hres i m]
    rw [Nat.add_comm]
    rw [(hiter_mod (m + ((i % (t : ℤ)).toNat))).symm]
    exact Function.iterate_add_apply σ m ((i % (t : ℤ)).toNat) pS
  have Wof_apply : ∀ (i : ℤ) (m : ℕ), m ≤ n + 1 → (Wof i).1 m = x (i + (m : ℤ)) := by
    intro i m hm
    show (Wof i).1 m = (Wof (i + (m : ℤ))).1 0
    rw [Wof_add_nat i m]
    have h := σ_iter_apply m 0 (Wof i) (by omega)
    simpa using h.symm
  have x_nat : ∀ i : ℕ, x (i : ℤ) = (σ^[i] pS).1 0 := by
    intro i
    show (Wof (i : ℤ)).1 0 = (σ^[i] pS).1 0
    congr 1
    unfold Wof
    have h1 : (((i : ℤ) % (t : ℤ)).toNat) = i % t := by
      have hc : ((i : ℤ) % (t : ℤ)) = ((i % t : ℕ) : ℤ) := by
        rw [← Int.natCast_emod i t]
      rw [hc]
      exact Int.toNat_natCast (i % t)
    rw [h1, ← hiter_mod i]
  have x_base : ∀ i : ℕ, i ≤ n + 1 → x (i : ℤ) = p i := by
    intro i hi
    rw [x_nat i]
    have h := σ_iter_apply i 0 pS (by omega)
    simpa using h
  have x_period : ∀ i : ℤ, x (i + (t : ℤ)) = x i := by
    intro i
    show (Wof (i + (t : ℤ))).1 0 = (Wof i).1 0
    congr 1
    unfold Wof
    rw [Int.add_emod_right]
  have x_adj : ∀ i : ℤ, Γ.Adj (x i) (x (i + 1)) := by
    intro i
    have hW : Wof (i + 1) = σ (Wof i) := by
      simpa using Wof_add_nat i 1
    have hx1 : x (i + 1) = (Wof i).1 1 := by
      show (Wof (i + 1)).1 0 = (Wof i).1 1
      rw [hW, σ_apply (Wof i) 0 (by omega)]
    rw [hx1]
    simpa using (Wof i).1.adj 0 (by omega)
  have x_ne : ∀ i : ℤ, x i ≠ x (i + 2) := by
    intro i
    have hW : Wof (i + 2) = σ^[2] (Wof i) := by
      simpa using Wof_add_nat i 2
    have hx2 : x (i + 2) = (Wof i).1 2 := by
      show (Wof (i + 2)).1 0 = (Wof i).1 2
      rw [hW]
      have h := σ_iter_apply 2 0 (Wof i) (by omega)
      simpa using h
    rw [hx2]
    simpa using (Wof i).2.1 0 (by omega)
  have window_adj : ∀ k : ℤ, Γ.Adj ((Wof k).1 (n + 1)) (x (k + (n + 2))) := by
    intro k
    have h1 : (Wof k).1 (n + 1) = x (k + (n + 1)) := by
      simpa using Wof_apply k (n + 1) (by omega)
    rw [h1]
    have h2 := x_adj (k + ((n + 1 : ℕ) : ℤ))
    have hidx : k + ((n + 1 : ℕ) : ℤ) + 1 = k + (n + 2) := by
      push_cast
      ring
    rwa [hidx] at h2
  have cont_eq : ∀ k : ℤ, cont (Wof k) = x (k + (n + 2)) := by
    intro k
    have h1 : Wof (k + 1) = σ (Wof k) := by
      simpa using Wof_add_nat k 1
    calc
      cont (Wof k) = (σ (Wof k)).1 (n + 1) := (σ_last (Wof k)).symm
      _ = (Wof (k + 1)).1 (n + 1) := by rw [← h1]
      _ = x ((k + 1) + (n + 1)) := Wof_apply (k + 1) (n + 1) (by omega)
      _ = x (k + (n + 2)) := by
        congr 1
        omega
  have window_succ_good : ∀ k : ℤ,
      IsGoodPath H ((Wof k).1.snoc (x (k + (n + 2))) (window_adj k)) := by
    intro k
    have heq : (Wof k).1.snoc (x (k + (n + 2))) (window_adj k) =
        (Wof k).1.snoc (cont (Wof k)) (cont_adj (Wof k)) := by
      apply GPath.ext'
      intro j hj
      change (Wof k).1.snoc (x (k + (n + 2))) (window_adj k) j =
        (Wof k).1.snoc (cont (Wof k)) (cont_adj (Wof k)) j
      by_cases hjn : j ≤ n + 1
      · rw [GPath.snoc_of_le _ _ _ hjn, GPath.snoc_of_le _ _ _ hjn]
      · have hj' : j = n + 2 := by omega
        subst hj'
        rw [GPath.snoc_last, GPath.snoc_last]
        exact (cont_eq k).symm
    rw [heq]
    exact cont_good (Wof k)
  have good_cast : ∀ {m n : ℕ} (h : m = n) {q : GPath Γ m}, IsGoodPath H q →
      IsGoodPath H (GPath.castLength h q) := by
    intro m n h q hq
    exact (isGoodPath_castLength h).mpr hq
  have window_good : ∀ (s : ℕ) (k : ℤ) (q : GPath Γ s),
      (∀ j : ℕ, j ≤ s → q j = x (k + (j : ℤ))) → IsGoodPath H q := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro k q hq
      by_cases hs : s ≤ n + 1
      · have hqeq : q = (Wof k).1.take s hs := by
          apply GPath.ext'
          intro j hj
          rw [GPath.take_apply_of_le _ _ _ hj, Wof_apply k j (by omega)]
          exact hq j (by omega)
        rw [hqeq]
        exact (Wof k).2.take s hs
      · by_cases hs2 : s = n + 2
        · subst hs2
          have hqeq : q = (Wof k).1.snoc (x (k + (n + 2))) (window_adj k) := by
            apply GPath.ext'
            intro j hj
            by_cases hjn : j ≤ n + 1
            · rw [GPath.snoc_of_le _ _ _ hjn, Wof_apply k j (by omega)]
              exact hq j (by omega)
            · have hj' : j = n + 2 := by omega
              subst hj'
              rw [GPath.snoc_last]
              exact hq (n + 2) le_rfl
          rw [hqeq]
          exact window_succ_good k
        · have hs3 : n + 2 < s := by omega
          have hsm1 : s - 1 ≤ s := by omega
          let U : GPath Γ (s - 1) := q.take (s - 1) hsm1
          have hU : IsGoodPath H U := by
            apply ih (s - 1) (by omega) k U
            intro j hj
            show q.take (s - 1) hsm1 j = x (k + (j : ℤ))
            rw [GPath.take_apply_of_le _ _ _ hj]
            exact hq j (by omega)
          obtain ⟨w, hw, hUw⟩ :=
            exists_isGoodPath_snoc hn hM hne hL (s := s - 1) (by omega) hU
          let b : ℕ := s - 1 - (n + 1)
          have hb : b ≤ s - 1 := by omega
          let V : GPath Γ (s - 1 - b) := U.drop b hb
          have hVlen : n + 1 ≤ s - 1 - b := by omega
          have hVlast : V (s - 1 - b) = q (s - 1) := by
            show U.drop b hb (s - 1 - b) = q (s - 1)
            rw [GPath.drop_apply _ _ _ le_rfl]
            rw [show b + (s - 1 - b) = s - 1 by omega]
            rw [GPath.take_apply_of_le _ _ _ le_rfl]
          have hUlast : U (s - 1) = q (s - 1) := by
            show q.take (s - 1) hsm1 (s - 1) = q (s - 1)
            rw [GPath.take_apply_of_le _ _ _ le_rfl]
          have hadjW : Γ.Adj (V (s - 1 - b)) w := by
            rw [hVlast, ← hUlast]
            exact hw
          have hadjQ : Γ.Adj (V (s - 1 - b)) (q s) := by
            rw [hVlast]
            have h := q.adj (s - 1) (by omega)
            rwa [show s - 1 + 1 = s by omega] at h
          have hlenW : (s - 1 + 1) - b = (s - 1 - b) + 1 := by omega
          have hlenQ : s - b = (s - 1 - b) + 1 := by omega
          have hgoodW : IsGoodPath H (V.snoc w hadjW) := by
            have hdrop : IsGoodPath H ((U.snoc w hw).drop b (by omega)) :=
              hUw.drop b (by omega)
            have heq : V.snoc w hadjW =
                GPath.castLength hlenW ((U.snoc w hw).drop b (by omega)) := by
              apply GPath.ext'
              intro j hj
              rw [GPath.castLength_apply]
              by_cases hjs : j ≤ s - 1 - b
              · rw [GPath.snoc_of_le _ _ _ hjs]
                show U.drop b hb j = (U.snoc w hw).drop b (by omega) j
                rw [GPath.drop_apply _ _ _ hjs, GPath.drop_apply _ _ _ (by omega)]
                rw [GPath.snoc_of_le _ _ _ (by omega)]
              · have hj' : j = (s - 1 - b) + 1 := by omega
                subst hj'
                rw [GPath.snoc_last]
                show w = (U.snoc w hw).drop b (by omega) ((s - 1 - b) + 1)
                rw [GPath.drop_apply _ _ _ (by omega)]
                rw [show b + ((s - 1 - b) + 1) = (s - 1) + 1 by omega,
                  GPath.snoc_last]
            rw [heq]
            exact good_cast hlenW hdrop
          have hgoodQ : IsGoodPath H (V.snoc (q s) hadjQ) := by
            have hdropq : IsGoodPath H (q.drop b (by omega)) := by
              apply ih (s - b) (by omega) (k + (b : ℤ)) (q.drop b (by omega))
              intro j hj
              rw [GPath.drop_apply _ _ _ hj]
              have hkb : (k + (b : ℤ)) + (j : ℤ) = k + ((b + j : ℕ) : ℤ) := by
                push_cast
                ring
              rw [hkb]
              exact hq (b + j) (by omega)
            have heq : V.snoc (q s) hadjQ =
                GPath.castLength hlenQ (q.drop b (by omega)) := by
              apply GPath.ext'
              intro j hj
              rw [GPath.castLength_apply]
              by_cases hjs : j ≤ s - 1 - b
              · rw [GPath.snoc_of_le _ _ _ hjs]
                show U.drop b hb j = q.drop b (by omega) j
                rw [GPath.drop_apply _ _ _ hjs, GPath.drop_apply _ _ _ (by omega)]
                rw [GPath.take_apply_of_le _ _ _ (by omega)]
              · have hj' : j = (s - 1 - b) + 1 := by omega
                subst hj'
                rw [GPath.snoc_last]
                show q s = q.drop b (by omega) ((s - 1 - b) + 1)
                rw [GPath.drop_apply _ _ _ (by omega)]
                rw [show b + ((s - 1 - b) + 1) = s by omega]
            rw [heq]
            exact good_cast hlenQ hdropq
          have hwq : w = q s :=
            isGoodPath_snoc_unique hn hW hL (s := s - 1 - b) hVlen hadjW hadjQ hgoodW hgoodQ
          have hlenU : (s - 1) + 1 = s := by omega
          have hadjU : Γ.Adj (U (s - 1)) (q s) := by
            rw [hUlast]
            have h := q.adj (s - 1) (by omega)
            rwa [show s - 1 + 1 = s by omega] at h
          have hgood_snoc : IsGoodPath H (U.snoc (q s) hadjU) := by
            have heqsnoc : U.snoc (q s) hadjU = U.snoc w hw := by
              apply GPath.ext'
              intro j hj
              by_cases hjs : j ≤ s - 1
              · rw [GPath.snoc_of_le _ _ _ hjs, GPath.snoc_of_le _ _ _ hjs]
              · have hj' : j = (s - 1) + 1 := by omega
                subst hj'
                rw [GPath.snoc_last, GPath.snoc_last]
                exact hwq.symm
            rw [heqsnoc]
            exact hUw
          have hqeq : q = GPath.castLength hlenU (U.snoc (q s) hadjU) := by
            apply GPath.ext'
            intro j hj
            rw [GPath.castLength_apply]
            by_cases hjs : j ≤ s - 1
            · rw [GPath.snoc_of_le _ _ _ hjs]
              show q j = U j
              rw [show U = q.take (s - 1) hsm1 from rfl,
                GPath.take_apply_of_le _ _ _ hjs]
            · have hj' : j = (s - 1) + 1 := by omega
              subst hj'
              rw [GPath.snoc_last, hlenU]
          rw [hqeq]
          exact good_cast hlenU hgood_snoc
  refine ⟨t, x, ht, x_period, x_adj, x_ne, x_base, ?_⟩
  intro i s q hq
  exact window_good s i q (fun j hj => by
    have := hq j hj
    simpa using this)

end CFSG.Quasithin.Stroth.WeissDelta

end
