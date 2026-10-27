module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCFixB
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

section General

variable {G : Type} [Group G]

structure SevenSevenMinimal (V H E V₁ V₂ V₃ A : Subgroup G) : Prop
    extends SevenSevenModule V H E V₁ V₂ V₃ A where
  minimal : ∀ S : Subgroup G, SevenSevenModule V H E V₁ V₂ V₃ S → S ≤ A → S = A

theorem exists_sevenSevenMinimal_le [Finite G] {V H E V₁ V₂ V₃ A₀ : Subgroup G}
    (hA₀ : SevenSevenModule V H E V₁ V₂ V₃ A₀) :
    ∃ A : Subgroup G, A ≤ A₀ ∧ SevenSevenMinimal V H E V₁ V₂ V₃ A := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun S : Subgroup G => (S : Set G)) (fun _ _ h => SetLike.coe_injective h)
  let s : Set (Subgroup G) := {S | SevenSevenModule V H E V₁ V₂ V₃ S ∧ S ≤ A₀}
  have hs : s.Nonempty := ⟨A₀, hA₀, le_rfl⟩
  obtain ⟨A, hAs, hmin⟩ := (Set.toFinite s).exists_minimalFor (fun S : Subgroup G => S) s hs
  refine ⟨A, hAs.2, { toSevenSevenModule := hAs.1, minimal := ?_ }⟩
  intro S hS hSA
  exact le_antisymm hSA (hmin (j := S) ⟨hS, hSA.trans hAs.2⟩ hSA)

private def seven_seven_c_min_chain (S X : Subgroup G) : ℕ → Subgroup G
  | 0 => S
  | n + 1 => ⁅seven_seven_c_min_chain S X n, X⁆

private theorem seven_seven_c_min_normalizer_commutator {S X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (S : Set G)) :
    X ≤ Subgroup.normalizer ((⁅S, X⁆ : Subgroup G) : Set G) := by
  have hXX : X ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun y hy z hz => X.mul_mem (X.mul_mem hy hz) (X.inv_mem hy)
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.map_commutator (H₁ := S) (H₂ := X) (f := (MulAut.conj x : G →* G)),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXX hx)]

private theorem seven_seven_c_min_commutator_le {S X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (S : Set G)) : ⁅S, X⁆ ≤ S :=
  Subgroup.commutator_le.mpr fun s hs x hx => by
    rw [commutatorElement_def]
    rw [show s * x * s⁻¹ * x⁻¹ = s * (x * s⁻¹ * x⁻¹) by group]
    exact S.mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hX hx) s⁻¹).mp (S.inv_mem hs))

private theorem seven_seven_c_min_chain_shrink [Finite G] (S X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (S : Set G)) :
    (∀ n, X ≤ Subgroup.normalizer (seven_seven_c_min_chain S X n : Set G)) ∧
      (∀ n, seven_seven_c_min_chain S X (n + 1) ≤ seven_seven_c_min_chain S X n) := by
  have hnorm : ∀ n, X ≤ Subgroup.normalizer (seven_seven_c_min_chain S X n : Set G) := by
    intro n
    induction n with
    | zero => exact hX
    | succ n ih => exact seven_seven_c_min_normalizer_commutator ih
  exact ⟨hnorm, fun n => seven_seven_c_min_commutator_le (hnorm n)⟩

private theorem seven_seven_c_min_chain_stabilizes [Finite G] (S X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (S : Set G)) :
    ∃ m, seven_seven_c_min_chain S X (m + 1) = seven_seven_c_min_chain S X m := by
  classical
  obtain ⟨hnorm, hanti⟩ := seven_seven_c_min_chain_shrink S X hX
  by_contra h
  push Not at h
  have hlt : ∀ n, Nat.card ↥(seven_seven_c_min_chain S X (n + 1)) <
      Nat.card ↥(seven_seven_c_min_chain S X n) := fun n =>
    Subgroup.card_lt_of_lt (lt_of_le_of_ne (hanti n) (h n))
  have hbound : ∀ n, Nat.card ↥(seven_seven_c_min_chain S X n) + n ≤ Nat.card ↥S := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        have h1 : Nat.card ↥(seven_seven_c_min_chain S X (n + 1)) + 1 ≤
            Nat.card ↥(seven_seven_c_min_chain S X n) := hlt n
        calc Nat.card ↥(seven_seven_c_min_chain S X (n + 1)) + (n + 1)
            = Nat.card ↥(seven_seven_c_min_chain S X (n + 1)) + 1 + n := by ring
          _ ≤ Nat.card ↥(seven_seven_c_min_chain S X n) + n := Nat.add_le_add_right h1 n
          _ ≤ Nat.card ↥S := ih
  have hpos : 0 < Nat.card ↥(seven_seven_c_min_chain S X (Nat.card ↥S)) :=
    Nat.card_pos_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  have := hbound (Nat.card ↥S)
  omega

private theorem seven_seven_c_min_chain_bot_of_stable {S X : Subgroup G} {m : ℕ}
    (hm : seven_seven_c_min_chain S X m = ⊥) :
    ∀ j, m ≤ j → seven_seven_c_min_chain S X j = ⊥ := by
  intro j hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction k with
  | zero => exact hm
  | succ k ih =>
      show ⁅seven_seven_c_min_chain S X (m + k), X⁆ = ⊥
      rw [ih (Nat.le_add_right m k), Subgroup.commutator_bot_left]

private theorem seven_seven_c_min_commutator_mem_normalizer {I : Subgroup G} {a x : G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) (ha : a ∈ I) : ⁅a, x⁆ ∈ I := by
  rw [commutatorElement_def]
  rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
  exact I.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hx a⁻¹).mp (I.inv_mem ha))

private theorem seven_seven_c_min_inv_eq_self {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {a : G} (ha : a ∈ I) : a⁻¹ = a := by
  apply inv_eq_of_mul_eq_one_right
  simpa [pow_two] using hI.2 a ha

private def seven_seven_c_min_T {I : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) : ↥I → ↥I :=
  fun a => ⟨⁅(a : G), x⁆, seven_seven_c_min_commutator_mem_normalizer hx a.2⟩

private def seven_seven_c_min_conjHom {I : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) : ↥I →* ↥I where
  toFun a := ⟨x * (a : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx (a : G)).mp a.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    group

private theorem seven_seven_c_min_sq_eq_one {I : Subgroup G} (hI : IsElemAbelian 2 I)
    (u : ↥I) : u * u = 1 := by
  ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  simpa [pow_two] using hI.2 (u : G) u.2

private theorem seven_seven_c_min_T_eq_mul {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {x : G} (hx : x ∈ Subgroup.normalizer (I : Set G)) (a : ↥I) :
    seven_seven_c_min_T hx a = a * seven_seven_c_min_conjHom hx a := by
  ext
  show ⁅(a : G), x⁆ = (a : G) * (x * (a : G) * x⁻¹)
  rw [commutatorElement_def, seven_seven_c_min_inv_eq_self hI a.2]
  group

private theorem seven_seven_c_min_conjHom_iter {I : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) (k : ℕ) (a : ↥I) :
    (((seven_seven_c_min_conjHom hx)^[k]) a : G) = x ^ k * (a : G) * (x ^ k)⁻¹ := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change x * ((((seven_seven_c_min_conjHom hx)^[k]) a : ↥I) : G) * x⁻¹ =
        x ^ (k + 1) * (a : G) * (x ^ (k + 1))⁻¹
      rw [ih a]
      group

private theorem seven_seven_c_min_conjHom_iter_mul {I : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) (k : ℕ) (u v : ↥I) :
    ((seven_seven_c_min_conjHom hx)^[k]) (u * v) =
      ((seven_seven_c_min_conjHom hx)^[k]) u * ((seven_seven_c_min_conjHom hx)^[k]) v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply',
        Function.iterate_succ_apply']

private theorem seven_seven_c_min_T_iter {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {x : G} (hx : x ∈ Subgroup.normalizer (I : Set G)) :
    ∀ s (a : ↥I), ((seven_seven_c_min_T hx)^[2 ^ s]) a =
      a * ((seven_seven_c_min_conjHom hx)^[2 ^ s]) a := by
  intro s
  induction s with
  | zero =>
      intro a
      rw [pow_zero, Function.iterate_one, Function.iterate_one]
      exact seven_seven_c_min_T_eq_mul hI hx a
  | succ s ih =>
      intro a
      have h2 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
      have hL : ((seven_seven_c_min_T hx)^[2 ^ (s + 1)]) a =
          ((seven_seven_c_min_T hx)^[2 ^ s])
            (((seven_seven_c_min_T hx)^[2 ^ s]) a) := by
        rw [h2, Function.iterate_add_apply]
      have hR : ((seven_seven_c_min_conjHom hx)^[2 ^ (s + 1)]) a =
          ((seven_seven_c_min_conjHom hx)^[2 ^ s])
            (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a) := by
        rw [h2, Function.iterate_add_apply]
      have hstep : ((seven_seven_c_min_T hx)^[2 ^ s])
            (((seven_seven_c_min_T hx)^[2 ^ s]) a) =
          (a * ((seven_seven_c_min_conjHom hx)^[2 ^ s]) a) *
            (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a *
              ((seven_seven_c_min_conjHom hx)^[2 ^ s])
                (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a)) := by
        rw [ih (((seven_seven_c_min_T hx)^[2 ^ s]) a), ih a,
          seven_seven_c_min_conjHom_iter_mul]
      rw [hL, hR, hstep]
      have hu : ((seven_seven_c_min_conjHom hx)^[2 ^ s]) a *
          ((seven_seven_c_min_conjHom hx)^[2 ^ s]) a = 1 :=
        seven_seven_c_min_sq_eq_one hI _
      calc (a * ((seven_seven_c_min_conjHom hx)^[2 ^ s]) a) *
            (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a *
              ((seven_seven_c_min_conjHom hx)^[2 ^ s])
                (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a))
          = a * (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a *
              ((seven_seven_c_min_conjHom hx)^[2 ^ s]) a) *
              ((seven_seven_c_min_conjHom hx)^[2 ^ s])
                (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a) := by group
        _ = a * ((seven_seven_c_min_conjHom hx)^[2 ^ s])
                (((seven_seven_c_min_conjHom hx)^[2 ^ s]) a) := by rw [hu, mul_one]

theorem exists_commutator_eq_of_not_isPGroup [Finite G] {I X : Subgroup G}
    (hI : IsElemAbelian 2 I) (hXI : X ≤ Subgroup.normalizer (I : Set G))
    (hX : ¬ IsPGroup 2 ↥X) (hC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (I : Set G))) :
    ∃ A : Subgroup G, A ≤ I ∧ X ≤ Subgroup.normalizer (A : Set G) ∧ ⁅A, X⁆ = A ∧ A ≠ ⊥ := by
  classical
  obtain ⟨hnorm, hanti⟩ := seven_seven_c_min_chain_shrink I X hXI
  obtain ⟨m, hm⟩ := seven_seven_c_min_chain_stabilizes I X hXI
  have hleI : ∀ n, seven_seven_c_min_chain I X n ≤ I := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (seven_seven_c_min_commutator_le (hnorm n)).trans ih
  refine ⟨seven_seven_c_min_chain I X m, hleI m, hnorm m, ?_, ?_⟩
  · rw [← show seven_seven_c_min_chain I X (m + 1) =
        ⁅seven_seven_c_min_chain I X m, X⁆ from rfl]
    exact hm
  · intro hbot
    have hbot' : seven_seven_c_min_chain I X m = ⊥ := hbot
    have horder : ∀ y : ↥X, ∃ k, orderOf y = 2 ^ k := by
      intro y
      have hyN : (y : G) ∈ Subgroup.normalizer (I : Set G) := hXI y.2
      let T := seven_seven_c_min_T hyN
      let c := seven_seven_c_min_conjHom hyN
      have hTmem : ∀ j (a : ↥I),
          (((T^[j]) a : ↥I) : G) ∈ seven_seven_c_min_chain I X j := by
        intro j
        induction j with
        | zero => intro a; exact a.2
        | succ j ih =>
            intro a
            rw [Function.iterate_succ_apply']
            exact Subgroup.commutator_mem_commutator (ih a) y.2
      have hTbot : T^[2 ^ m] = (fun _ : ↥I => (1 : ↥I)) := by
        funext a
        have hmem := hTmem (2 ^ m) a
        rw [seven_seven_c_min_chain_bot_of_stable hbot' (2 ^ m)
          (le_of_lt Nat.lt_two_pow_self)] at hmem
        exact Subtype.ext (Subgroup.mem_bot.mp hmem)
      have hxpow_mem : (y : G) ^ (2 ^ m) ∈ Subgroup.centralizer (I : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
        have h1 : ((T^[2 ^ m]) ⟨a, ha⟩) = 1 := congrFun hTbot ⟨a, ha⟩
        have h2 := seven_seven_c_min_T_iter hI hyN m ⟨a, ha⟩
        rw [h1] at h2
        have h3 : ((c^[2 ^ m]) ⟨a, ha⟩) = (⟨a, ha⟩ : ↥I)⁻¹ :=
          (inv_eq_of_mul_eq_one_right h2.symm).symm
        have h4 : (y : G) ^ (2 ^ m) * a * ((y : G) ^ (2 ^ m))⁻¹ = a := by
          have hconj := seven_seven_c_min_conjHom_iter hyN (2 ^ m) ⟨a, ha⟩
          rw [h3] at hconj
          rw [← hconj]
          simp only [Subgroup.coe_inv]
          exact seven_seven_c_min_inv_eq_self hI ha
        exact (mul_inv_eq_iff_eq_mul.mp h4).symm
      have hmemC : (y : G) ^ (2 ^ m) ∈
          (X ⊓ Subgroup.centralizer (I : Set G) : Subgroup G) :=
        ⟨Subgroup.pow_mem X y.2 (2 ^ m), hxpow_mem⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hC) ⟨(y : G) ^ (2 ^ m), hmemC⟩
      rw [Subgroup.orderOf_mk, orderOf_pow] at hk
      have hdvd : Nat.gcd (orderOf (y : G)) (2 ^ m) ∣ 2 ^ m := Nat.gcd_dvd_right _ _
      obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      refine ⟨j + k, ?_⟩
      rw [← Subgroup.orderOf_coe y]
      calc orderOf (y : G) = Nat.gcd (orderOf (y : G)) (2 ^ m) *
            (orderOf (y : G) / Nat.gcd (orderOf (y : G)) (2 ^ m)) :=
            (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
        _ = Nat.gcd (orderOf (y : G)) (2 ^ m) * 2 ^ k := by rw [hk]
        _ = 2 ^ j * 2 ^ k := by rw [hjeq]
        _ = 2 ^ (j + k) := (pow_add 2 j k).symm
    exact hX (IsPGroup.iff_orderOf.mpr horder)

theorem exists_mem_sdiff_forall_commutator_mem [Finite G] {P A B : Subgroup G}
    (hP : IsPGroup 2 ↥P) (hA : IsPGroup 2 ↥A) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hBA : B < A) : ∃ a ∈ A, a ∉ B ∧ ∀ n ∈ P, ⁅a, n⁆ ∈ B := by
  classical
  haveI hAc : IsMulCommutative ↥A :=
    ⟨⟨fun x y => Subtype.ext (hAab x x.2 y y.2)⟩⟩
  letI : CommGroup ↥A := IsMulCommutative.instCommGroup
  letI : MulAction ↥P ↥A := MulAction.compHom ↥A (Subgroup.inclusion hPA)
  have hcoe : ∀ (p : ↥P) (a : ↥A), ((p • a : ↥A) : G) = (p : G) * (a : G) * (p : G)⁻¹ :=
    fun _ _ => rfl
  haveI hq : MulAction.QuotientAction ↥P (B.subgroupOf A) := by
    refine ⟨fun p a a' h => ?_⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hB : ((a⁻¹ * a' : ↥A) : G) ∈ B := Subgroup.mem_subgroupOf.mp h
    have hconj : (p : G) * ((a⁻¹ * a' : ↥A) : G) * (p : G)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hPB p.2) _).mp hB
    show (((p • a)⁻¹ * (p • a') : ↥A) : G) ∈ B
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe p a, hcoe p a']
    have heq : ((p : G) * (a : G) * (p : G)⁻¹)⁻¹ * ((p : G) * (a' : G) * (p : G)⁻¹) =
        (p : G) * ((a⁻¹ * a' : ↥A) : G) * (p : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact hconj
  haveI : Finite (↥A ⧸ B.subgroupOf A) := inferInstance
  obtain ⟨n, hn⟩ := hA.index (B.subgroupOf A)
  rw [Subgroup.index_eq_card] at hn
  have hne_top : B.subgroupOf A ≠ ⊤ := by
    intro htop
    exact hBA.not_ge (Subgroup.subgroupOf_eq_top.mp htop)
  have hone_lt : 1 < (B.subgroupOf A).index := Subgroup.one_lt_index_of_ne_top hne_top
  have hnpos : 0 < n := by
    rcases n with _ | n
    · rw [pow_zero] at hn
      rw [Subgroup.index_eq_card, hn] at hone_lt
      exact absurd hone_lt (lt_irrefl 1)
    · exact Nat.succ_pos n
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    nth_rewrite 1 [show n = (n - 1) + 1 from (Nat.succ_pred_eq_of_pos hnpos).symm]
    rw [pow_succ']
  have heven : Even (Nat.card (↥A ⧸ B.subgroupOf A)) := by
    rw [hn]
    exact ⟨2 ^ (n - 1), by rw [hpow]; ring⟩
  have hmod := hP.card_modEq_card_fixedPoints (↥A ⧸ B.subgroupOf A)
  have hQ : Nat.card (↥A ⧸ B.subgroupOf A) ≡ 0 [MOD 2] := by
    rw [hn]
    exact Nat.modEq_zero_iff_dvd.mpr ⟨2 ^ (n - 1), hpow⟩
  have hmod' : Nat.card (MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A)) ≡ 0 [MOD 2] :=
    hmod.symm.trans hQ
  have hfixed_one : (QuotientGroup.mk (1 : ↥A) : ↥A ⧸ B.subgroupOf A) ∈
      MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A) := by
    intro p
    rw [MulAction.Quotient.smul_mk]
    have h : (p : ↥P) • (1 : ↥A) = 1 := by
      change ((Subgroup.inclusion hPA p : ↥(Subgroup.normalizer (A : Set G)))) • (1 : ↥A) = 1
      exact smul_one _
    rw [h]
  have hnonempty : Nonempty (MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A)) :=
    ⟨⟨_, hfixed_one⟩⟩
  have heven_fixed : Even (Nat.card (MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A))) :=
    even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hmod')
  have hcard_ge2 : 2 ≤ Nat.card (MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A)) := by
    rcases heven_fixed with ⟨k, hk⟩
    have hge1 : 0 < Nat.card (MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A)) := Nat.card_pos
    omega
  obtain ⟨q, hqfix, hqne⟩ : ∃ q ∈ MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A),
      q ≠ QuotientGroup.mk (1 : ↥A) := by
    by_contra h
    push Not at h
    haveI : Subsingleton (MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A)) :=
      ⟨fun x y => Subtype.ext (by rw [h x x.2, h y y.2])⟩
    have hcard1 : Nat.card (MulAction.fixedPoints ↥P (↥A ⧸ B.subgroupOf A)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, hnonempty⟩
    omega
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have ha_not : a ∉ B.subgroupOf A := by
    intro h
    exact hqne ((QuotientGroup.eq_one_iff a).mpr h)
  refine ⟨(a : G), a.2, fun haB => ha_not (Subgroup.mem_subgroupOf.mpr haB), ?_⟩
  intro p hp
  let pp : ↥P := ⟨p, hp⟩
  have hfix : (QuotientGroup.mk (pp • a) : ↥A ⧸ B.subgroupOf A) = QuotientGroup.mk a :=
    hqfix pp
  have hmem : (pp • a)⁻¹ * a ∈ B.subgroupOf A := QuotientGroup.eq.mp hfix
  have hBG : (((pp • a)⁻¹ * a : ↥A) : G) ∈ B := Subgroup.mem_subgroupOf.mp hmem
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at hBG
  have hsmul : ((pp • a : ↥A) : G) = p * (a : G) * p⁻¹ := rfl
  rw [hsmul] at hBG
  have hmemA : p * (a : G)⁻¹ * p⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hPA hp) (a : G)⁻¹).mp (A.inv_mem a.2)
  have hcomm : (a : G) * (p * (a : G)⁻¹ * p⁻¹) = (p * (a : G)⁻¹ * p⁻¹) * (a : G) :=
    hAab (a : G) a.2 (p * (a : G)⁻¹ * p⁻¹) hmemA
  rw [commutatorElement_def,
    show (a : G) * p * (a : G)⁻¹ * p⁻¹ = (a : G) * (p * (a : G)⁻¹ * p⁻¹) by group, hcomm]
  have heq : (p * (a : G)⁻¹ * p⁻¹) * (a : G) =
      ((p * (a : G) * p⁻¹)⁻¹) * (a : G) := by
    congr 1
    group
  rw [heq]
  exact hBG

end General

section Min

variable {G : Type} [Group G] [Finite G]

variable {V H E J V₁ V₂ V₃ A B : Subgroup G}

theorem centralizer_iSub_le_pCoreOf [Finite G] {V H E : Subgroup G} (h : Hyp711 V H E) :
    kSub V H E ⊓ Subgroup.centralizer (iSub V H E : Set G) ≤ pCoreOf 2 (kSub V H E) := by
  have h4 := seven_four h.elemAbelian h.ti h.abelian h.le h.normal h.omega_le
  have hodd : CFSG.QuasithinUnique.oddCoreIn (kSub V H E) = ⊥ := h.oddCore
  rwa [hodd, sup_bot_eq] at h4

theorem eq_or_eq_of_sevenSevenMinimal (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    (hB : B = A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) :
    B < A ∧ ∀ S : Subgroup G, B ≤ S → S ≤ A →
      V₁ ⊔ V₂ ⊔ V₃ ≤ Subgroup.normalizer (S : Set G) → S = B ∨ S = A := by
  classical
  have hBA : B ≤ A := hB.trans_le inf_le_left
  have hBC : B ≤ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) :=
    hB.trans_le inf_le_right
  have hBlt : B < A := by
    refine lt_of_le_of_ne hBA ?_
    intro hBeq
    have hAle : A ≤ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) := by
      rw [hBeq] at hBC
      exact hBC
    have hcomm : ⁅A, V₁ ⊔ V₂ ⊔ V₃⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAle
    rw [hA.commutator_eq] at hcomm
    exact hA.ne_bot hcomm
  refine ⟨hBlt, ?_⟩
  intro S hBS hSA hSN
  by_cases hSBeq : S = B
  · exact Or.inl hSBeq
  · obtain ⟨m, hm⟩ := seven_seven_c_min_chain_stabilizes S (V₁ ⊔ V₂ ⊔ V₃) hSN
    obtain ⟨hnorm, hanti⟩ :=
      seven_seven_c_min_chain_shrink S (V₁ ⊔ V₂ ⊔ V₃) hSN
    have hchainS : ∀ n, seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) n ≤ S := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
          exact (seven_seven_c_min_commutator_le (hnorm n)).trans ih
    by_cases hTbot : seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) m = ⊥
    ·
      have hex : ∃ j, seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) j ≤ B :=
        ⟨m, by rw [hTbot]; exact bot_le⟩
      let j := Nat.find hex
      have hjB : seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) j ≤ B := Nat.find_spec hex
      have hjmin : ∀ i < j, ¬ seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) i ≤ B :=
        fun i hi => Nat.find_min hex hi
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · exfalso
          have hSleB : S ≤ B := by
            have hzero : seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) 0 = S := rfl
            rw [h0] at hjB
            rw [← hzero]
            exact hjB
          exact hSBeq (le_antisymm hSleB hBS)
        · exact hpos
      have hi_lt : j - 1 < j := Nat.sub_lt hjpos zero_lt_one
      have hnotle : ¬ seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) (j - 1) ≤ B :=
        hjmin (j - 1) hi_lt
      obtain ⟨s, hsSi, hsB⟩ := Set.not_subset.mp hnotle
      have hsj : seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) j =
          ⁅seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) (j - 1), V₁ ⊔ V₂ ⊔ V₃⁆ := by
        have hj : j = (j - 1) + 1 := by omega
        conv_lhs => rw [hj]
        rfl
      have hcomm_mem : ∀ x ∈ V₁ ⊔ V₂ ⊔ V₃, ⁅s, x⁆ ∈ B := by
        intro x hx
        have hmem : ⁅s, x⁆ ∈ ⁅seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) (j - 1),
            V₁ ⊔ V₂ ⊔ V₃⁆ := Subgroup.commutator_mem_commutator hsSi hx
        rw [← hsj] at hmem
        exact hjB hmem
      have hsA : s ∈ A := hSA (hchainS (j - 1) hsSi)
      have hsinB : s ∈ B :=
        mem_of_forall_commutator_mem_inf_centralizer h hc hA.toSevenSevenModule hB s hsA
          hcomm_mem
      exact absurd hsinB hsB
    ·
      have hTmod : SevenSevenModule V H E V₁ V₂ V₃
          (seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) m) :=
        { le_iSub := (hchainS m).trans (hSA.trans hA.le_iSub)
          normalizes := hnorm m
          commutator_eq := by
            rw [← show seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) (m + 1) =
              ⁅seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) m, V₁ ⊔ V₂ ⊔ V₃⁆ from rfl]
            exact hm
          ne_bot := hTbot }
      have hTA : seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) m ≤ A := (hchainS m).trans hSA
      have hTeq : seven_seven_c_min_chain S (V₁ ⊔ V₂ ⊔ V₃) m = A :=
        hA.minimal _ hTmod hTA
      refine Or.inr (le_antisymm hSA ?_)
      rw [← hTeq]
      exact hchainS m

theorem commutator_le_inf_centralizer_of_sevenSevenMinimal (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenMinimal V H E V₁ V₂ V₃ A)
    (hB : B = A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) :
    ⁅A, J ⊓ (V₁ ⊔ V₂ ⊔ V₃)⁆ ≤ B := by
  classical
  set X : Subgroup G := V₁ ⊔ V₂ ⊔ V₃ with hXdef
  set P : Subgroup G := J ⊓ X with hPdef
  have hBlt : B < A := (eq_or_eq_of_sevenSevenMinimal h hc hA hB).1
  have hBA : B ≤ A := hB.trans_le inf_le_left
  have hBC : B ≤ Subgroup.centralizer (X : Set G) := hB.trans_le inf_le_right
  have hXH : X ≤ H := by
    rw [hXdef]
    exact sup_le (sup_le (h.omega_le V₁ hc.mem₁) (h.omega_le V₂ hc.mem₂))
      (h.omega_le V₃ hc.mem₃)
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hXJN : X ≤ Subgroup.normalizer (J : Set G) :=
    hXH.trans (le_normalizer_of_subgroupOf_normal hJH h.jnormal)
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun x hx n hn => ?_
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hXJN hx) n).mp hn.1,
      X.mul_mem (X.mul_mem hx hn.2) (X.inv_mem hx)⟩
  have hP2 : IsPGroup 2 ↥P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le fun p hp => h.pcore_le hp.1
  have hIea : IsElemAbelian 2 (iSub V H E) :=
    seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le
  have hAea : IsElemAbelian 2 A := hIea.mono hA.le_iSub
  have hA2 : IsPGroup 2 ↥A := CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hAea
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
    seven_seven_c_fix_b_mul_comm_of_le_iSub h hA.le_iSub
  have hXA : X ≤ Subgroup.normalizer (A : Set G) := by
    rw [hXdef]
    exact hA.normalizes
  have hPA : P ≤ Subgroup.normalizer (A : Set G) := (inf_le_right : P ≤ X).trans hXA
  have hXB : X ≤ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun x hx b hb => ?_
    have hcomm : x * b = b * x := (Subgroup.mem_centralizer_iff.mp (hBC hb)) x hx
    have heq : x * b * x⁻¹ = b := by rw [hcomm]; group
    rw [heq]
    exact hb
  have hPB : P ≤ Subgroup.normalizer (B : Set G) := (inf_le_right : P ≤ X).trans hXB
  obtain ⟨a, haA, haB, haP⟩ :=
    exists_mem_sdiff_forall_commutator_mem hP2 hA2 hAab hPA hPB hBlt
  let S : Subgroup G :=
    { carrier := {a | a ∈ A ∧ ∀ n ∈ P, ⁅a, n⁆ ∈ B}
      one_mem' := ⟨A.one_mem, fun n _ => by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro a b ⟨haA, ha'⟩ ⟨hbA, hb'⟩
        refine ⟨A.mul_mem haA hbA, fun n hn => ?_⟩
        rw [commutator_mul_of_mem_normalizer hAab (hPA hn) haA hbA]
        exact B.mul_mem (ha' n hn) (hb' n hn)
      inv_mem' := by
        rintro a ⟨haA, ha'⟩
        refine ⟨A.inv_mem haA, fun n hn => ?_⟩
        have hmul := commutator_mul_of_mem_normalizer hAab (hPA hn) (A.inv_mem haA) haA
        have hone : ⁅a⁻¹ * a, n⁆ = 1 := by rw [inv_mul_cancel]; simp
        have h1 : ⁅a⁻¹, n⁆ * ⁅a, n⁆ = 1 := by rw [← hmul, hone]
        rw [eq_inv_iff_mul_eq_one.mpr h1]
        exact B.inv_mem (ha' n hn) }
  have hSleA : S ≤ A := fun a ha => ha.1
  have hBS : B ≤ S := by
    intro b hb
    refine ⟨hBA hb, fun n hn => ?_⟩
    have hcomm : n * b = b * n :=
      (Subgroup.mem_centralizer_iff.mp (hBC hb)) n hn.2
    have hone : ⁅b, n⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hcomm.symm
    rw [hone]
    exact B.one_mem
  have hXS : X ≤ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun x hx a ha => ?_
    obtain ⟨haA, haP⟩ := ha
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hXA hx) a).mp haA, fun n hn => ?_⟩
    have hxn : x⁻¹ * n * x ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hXP (X.inv_mem hx)) n).mp hn
    have hconjB : x * ⁅a, x⁻¹ * n * x⁆ * x⁻¹ ∈ B := by
      have hcomm : x * ⁅a, x⁻¹ * n * x⁆ = ⁅a, x⁻¹ * n * x⁆ * x :=
        (Subgroup.mem_centralizer_iff.mp (hBC (haP (x⁻¹ * n * x) hxn))) x hx
      rw [show x * ⁅a, x⁻¹ * n * x⁆ * x⁻¹ = ⁅a, x⁻¹ * n * x⁆ by rw [hcomm]; group]
      exact haP (x⁻¹ * n * x) hxn
    have hconv : x * ⁅a, x⁻¹ * n * x⁆ * x⁻¹ = ⁅x * a * x⁻¹, n⁆ := by
      rw [conjugate_commutatorElement]
      rw [show x * (x⁻¹ * n * x) * x⁻¹ = n by group]
    rwa [← hconv]
  have hSneB : S ≠ B := by
    intro hSB
    exact haB (by rw [← hSB]; exact ⟨haA, haP⟩)
  have hcases := (eq_or_eq_of_sevenSevenMinimal h hc hA hB).2 S hBS hSleA hXS
  have hSA : S = A := by
    rcases hcases with h' | h'
    · exact absurd h' hSneB
    · exact h'
  refine Subgroup.commutator_le.mpr fun a ha n hn => ?_
  exact ((show a ∈ S from by rw [hSA]; exact ha).2 n hn)

end Min

end CFSG.LocalAnalysis.WeakClosure81
