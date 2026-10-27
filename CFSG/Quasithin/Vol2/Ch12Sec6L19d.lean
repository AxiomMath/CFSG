module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19a S126L19b S126L19c Equiv
open scoped IsMulCommutative

namespace S126L19d

@[expose] def q1 : Perm (Fin 8) := g1 * g2 * (bsw * g1 * bsw⁻¹)

@[expose] def q2 : Perm (Fin 8) := bsw * q1 * bsw⁻¹

@[expose] def q3 : Perm (Fin 8) := bsw * g2

theorem sign_q1 : Equiv.Perm.sign q1 = 1 := by
  decide +kernel

theorem sign_q2 : Equiv.Perm.sign q2 = 1 := by
  decide +kernel

theorem sign_q3 : Equiv.Perm.sign q3 = 1 := by
  decide +kernel

theorem q1_mem : q1 ∈ Q8 :=
  ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ g1_mem g2_mem)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ bsw_mem g1_mem) (Subgroup.inv_mem _ bsw_mem)),
    Equiv.Perm.mem_alternatingGroup.2 sign_q1⟩

theorem q2_mem : q2 ∈ Q8 :=
  ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ bsw_mem q1_mem.1) (Subgroup.inv_mem _ bsw_mem),
    Equiv.Perm.mem_alternatingGroup.2 sign_q2⟩

theorem q3_mem : q3 ∈ Q8 :=
  ⟨Subgroup.mul_mem _ bsw_mem g2_mem, Equiv.Perm.mem_alternatingGroup.2 sign_q3⟩

@[expose] def sq1 : Perm (Fin 8) := swap 0 1 * swap 2 3

@[expose] def sq2 : Perm (Fin 8) := swap 4 5 * swap 6 7

@[expose] def sq3 : Perm (Fin 8) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

theorem q1_sq : (q1 ^ 2)⁻¹ = sq1 := by
  decide +kernel

theorem q2_sq : (q2 ^ 2)⁻¹ = sq2 := by
  decide +kernel

theorem q3_sq : (q3 ^ 2)⁻¹ = sq3 := by
  decide +kernel

theorem sq_chk2 : ∀ x : Fin 8 → ZMod 2, x 0 = 0 →
    (∀ i, x (sq1 i) + x (sq1 0) = x i) → (∀ i, x (sq2 i) + x (sq2 0) = x i) →
    (∀ i, x (sq3 i) + x (sq3 0) = x i) → (Finset.univ.filter fun i => x i ≠ 0).card ≠ 2 := by
  decide +kernel

theorem sq_chk6 : ∀ x : Fin 8 → ZMod 2, x 0 = 0 →
    (∀ i, x (sq1 i) + x (sq1 0) = x i) → (∀ i, x (sq2 i) + x (sq2 0) = x i) →
    (∀ i, x (sq3 i) + x (sq3 0) = x i) → (Finset.univ.filter fun i => x i ≠ 0).card ≠ 6 := by
  decide +kernel

theorem wt_iota_of_nonsing {y : D8} (hy : IsNonsing y) :
    (Finset.univ.filter fun i => Multiplicative.toAdd (iota y) i ≠ 0).card = 2 ∨
      (Finset.univ.filter fun i => Multiplicative.toAdd (iota y) i ≠ 0).card = 6 := by
  obtain ⟨m, rfl, hm⟩ := hy
  rw [iota_mk]
  rcases nrm_eq m with h | h
  · left
    rw [h]
    exact hm
  · right
    rw [h]
    have := wt_add_ones (Multiplicative.toAdd (m : PermMod 8))
    change (Finset.univ.filter fun i => (Multiplicative.toAdd (m : PermMod 8) + ones8) i ≠ 0).card
      = 6
    rw [this]
    change 8 - wt (m : PermMod 8) = 6
    rw [hm]

theorem not_fix_squares {P : Subgroup (Perm (Fin 8))} (hPA : P ≤ alternatingGroup (Fin 8))
    (hP2 : IsPGroup 2 P) (hP64 : 64 ≤ Nat.card P) {y : D8} (hy : IsNonsing y)
    (h : ∀ σ ∈ P, dAct (σ ^ 2) y = y) : False := by
  obtain ⟨g, hg⟩ := S126Ex.exists_conj_le_P8 hP2
  let P' := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hP'le : P' ≤ Q8 := by
    rintro _ ⟨q, hq, rfl⟩
    have e : (MulAut.conj g⁻¹).toMonoidHom q = g⁻¹ * q * g := by
      simp
    rw [e]
    refine ⟨hg q hq, ?_⟩
    have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
    have := hn.conj_mem q (hPA hq) g⁻¹
    rwa [inv_inv] at this
  have hcard : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.equivMapOfInjective P _ (MulAut.conj g⁻¹).injective).toEquiv.symm
  have hP'eq : P' = Q8 := Subgroup.eq_of_le_of_card_ge hP'le (by
    have := card_Q8_le
    omega)
  have hfix : ∀ ρ ∈ Q8, dAct (ρ ^ 2) (dAct g⁻¹ y) = dAct g⁻¹ y := by
    intro ρ hρ
    rw [← hP'eq] at hρ
    obtain ⟨q, hq, rfl⟩ := hρ
    have e : (MulAut.conj g⁻¹).toMonoidHom q = g⁻¹ * q * g := by
      simp
    rw [e, show (g⁻¹ * q * g) ^ 2 = g⁻¹ * q ^ 2 * g by rw [pow_two, pow_two]; group, ← dAct_mul,
      show g⁻¹ * q ^ 2 * g * g⁻¹ = g⁻¹ * q ^ 2 by group, dAct_mul, h q hq]
  set y' := dAct g⁻¹ y with hy'
  have hy'n : IsNonsing y' := hasWt_dAct g⁻¹ hy
  have hc : ∀ ρ ∈ Q8, ∀ i, Multiplicative.toAdd (iota y') ((ρ ^ 2)⁻¹ i) +
      Multiplicative.toAdd (iota y') ((ρ ^ 2)⁻¹ 0) = Multiplicative.toAdd (iota y') i :=
    fun ρ hρ i => cond_of_fix (hfix ρ hρ) i
  have c1 : ∀ i, Multiplicative.toAdd (iota y') (sq1 i) + Multiplicative.toAdd (iota y') (sq1 0) =
      Multiplicative.toAdd (iota y') i := by
    have := hc _ q1_mem
    rwa [q1_sq] at this
  have c2 : ∀ i, Multiplicative.toAdd (iota y') (sq2 i) + Multiplicative.toAdd (iota y') (sq2 0) =
      Multiplicative.toAdd (iota y') i := by
    have := hc _ q2_mem
    rwa [q2_sq] at this
  have c3 : ∀ i, Multiplicative.toAdd (iota y') (sq3 i) + Multiplicative.toAdd (iota y') (sq3 0) =
      Multiplicative.toAdd (iota y') i := by
    have := hc _ q3_mem
    rwa [q3_sq] at this
  have h2 := sq_chk2 _ (iota_zero y') c1 c2 c3
  have h6 := sq_chk6 _ (iota_zero y') c1 c2 c3
  rcases wt_iota_of_nonsing hy'n with h | h
  · exact h2 h
  · exact h6 h

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem sq_mem_of_relIndex_le_two {H K : Subgroup G} (h : H.relIndex K ≤ 2)
    {t : G} (ht : t ∈ K) : t * t ∈ H := by
  have hpos : 0 < H.relIndex K := by
    have h1 := Subgroup.relIndex_mul_card H K
    have h2 : 0 < Nat.card K := Nat.card_pos
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at h1; omega
  rcases (by omega : H.relIndex K = 1 ∨ H.relIndex K = 2) with h1 | h2
  · have : K ≤ H := by
      have := Subgroup.relIndex_eq_one.1 h1
      exact this
    exact this (K.mul_mem ht ht)
  · have := Subgroup.mul_self_mem_of_index_two (H := H.subgroupOf K) h2 ⟨t, ht⟩
    exact this

theorem not_conj_nonsing (h1262 : Theorem12_6_2) (h1222 : Stmt12_2_2) {F : Frame126 T L V}
    (E : Frame126E F) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)
    {h : G} {u : ↥V} (hu : IsNonsing (F.β u)) (hhu : h * ((v4 E : ↥V) : G) * h⁻¹ = u) :
    False := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus
  have hu1 : (u : G) ≠ 1 := fun h1 => ne_one_of_nonsing hu (by
    rw [show u = 1 from Subtype.ext h1, map_one])
  have hCM := h1262 G T L V F hH u ⟨u.2, hu⟩
  have hCN : Subgroup.centralizer ({(u : G)} : Set G) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) := by
    intro c hc
    refine ⟨hCM hc, mem_normalizer_of_TI hTI u.2 hu1 (hCM hc) ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 hc
  set T4 := T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) with hT4def
  have hT4idx : T4.relIndex T = 2 := relIndex_T4 E h1222 hH hZ
  have hX := conj_le_centralizer (g := h) (show T4 ≤ Subgroup.centralizer
    ({((v4 E : ↥V) : G)} : Set G) from inf_le_right)
  rw [hhu] at hX
  have hX2 : IsPGroup 2 (B6.conjSub h T4) :=
    (hyp.sylow.1.to_le inf_le_left).of_equiv
      (Subgroup.equivMapOfInjective T4 _ (MulAut.conj h).injective)
  have hTM : T ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf hyp.normalizes hTV
  obtain ⟨k, hkM, hk⟩ := exists_conjSub_le hyp.sylow hTM (hX.trans hCN) hX2
  set u' : ↥V := ⟨k * u * k⁻¹, conj_mem hkM.2 u⟩ with hu'
  obtain ⟨σk, hσk⟩ := exists_actsAs F hH hkM.1 hkM.2
  have hu'n : IsNonsing (F.β u') := (hasWt_iff F hσk u u' rfl).2 hu
  have hXu' : B6.conjSub (k * h) T4 ≤ T ⊓ Subgroup.centralizer ({(u' : G)} : Set G) := by
    rw [B6.conjSub_mul]
    refine le_inf hk ?_
    have := conj_le_centralizer (g := k) hX
    exact this
  have hidx : (T ⊓ Subgroup.centralizer ({(u' : G)} : Set G)).relIndex T ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (T ⊓ Subgroup.centralizer ({(u' : G)} : Set G)) T
    have h2 := Subgroup.relIndex_mul_card T4 T
    rw [inf_of_le_left inf_le_left] at h1
    rw [inf_of_le_left (inf_le_left : T4 ≤ T), hT4idx] at h2
    have h3 : Nat.card T4 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({(u' : G)} : Set G)) := by
      rw [← B6.card_conjSub T4 (k * h)]
      exact Subgroup.card_le_of_le hXu'
    have hpos : 0 < Nat.card T4 := Nat.card_pos
    by_contra hc
    push Not at hc
    have h4 : 3 * Nat.card T4 ≤ Nat.card T := by
      rw [← h1]
      exact Nat.mul_le_mul hc h3
    rw [← h2] at h4
    have e : Nat.card ↥(T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G)) =
        Nat.card T4 := by rw [hT4def]
    rw [e] at h4
    omega
  have hsq : ∀ t ∈ T, t * t * (u' : G) = u' * (t * t) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.1 (sq_mem_of_relIndex_le_two hidx ht).2
  obtain ⟨P, hPA, hP2, hP64, hP⟩ := exists_sylow_pi F hH
  refine not_fix_squares hPA hP2 hP64 hu'n fun σ hσ => ?_
  obtain ⟨hσA, t, htT, ht, hta⟩ := hP σ hσ
  have hact : ActsAs F t σ := actsAs_of_pi F ht ⟨σ, hσA⟩ hta
  have hact2 := hact.pow ht 2
  rw [pow_two t] at hact2
  have h1 := hact2 u' u' (by
    have := hsq t htT
    calc (u' : G) = u' * (t * t) * (t * t)⁻¹ := by group
      _ = t * t * u' * (t * t)⁻¹ := by rw [this])
  exact h1.symm

omit [IsMulCommutative ↥V] in
theorem centralizer_le_M (h331 : Stmt3_3_1) (hH : Hyp126 G T L V) {x : G} (hx1 : x ≠ 1)
    (hxT : x ∈ T) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxC : x ∈ Subgroup.centralizer (T : Set G)) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hyp := hH.hyp
  have hP2 : IsPGroup 2 (Subgroup.zpowers x) := hyp.sylow.1.to_le (Subgroup.zpowers_le.2 hxT)
  have hP1 : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (by
    have := Subgroup.mem_zpowers x
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hCN : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hcx := Subgroup.mem_centralizer_singleton_iff.1 hc
    have key : ∀ k : ℤ, c * x ^ k * c⁻¹ = x ^ k := fun k => by
      rw [← conj_zpow, show c * x * c⁻¹ = x by rw [hcx, mul_inv_cancel_right]]
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [key]
      exact Subgroup.zpow_mem_zpowers x k
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      have : y = x ^ k := by
        calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
          _ = c⁻¹ * x ^ k * c := by rw [hk]
          _ = c⁻¹ * (c * x ^ k * c⁻¹) * c := by rw [key]
          _ = x ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem_zpowers x k
  have hLT : L ⊔ T ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    refine le_trans ?_ hCN
    refine sup_le (fun l hl => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hxL l hl
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hxC t ht
  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨Subgroup.zpowers x, hP1, hP2, rfl⟩ : IsTwoLocal _)
  have hM'eq := huniq M' hM' (hLT.trans hle)
  exact hCN.trans (hle.trans hM'eq.le)

section Weights

variable {F : Frame126 T L V} (E : Frame126E F)

@[expose] noncomputable def ew (u : ↥V) : ℕ := wt ((E.γ u : ↥(coreMod 8)) : PermMod 8)

omit [Finite G] in
theorem ew_cases (u : ↥V) : ew E u = 0 ∨ ew E u = 2 ∨ ew E u = 4 ∨ ew E u = 6 ∨ ew E u = 8 :=
  wt_cases _ (E.γ u).2

omit [Finite G] in
theorem eq_one_of_ew {u : ↥V} (h : ew E u = 0) : u = 1 := by
  apply E.γ.injective
  rw [map_one]
  exact Subtype.ext (Multiplicative.toAdd.injective (eq_zero_of_wt0 _ h))

omit [Finite G] in
theorem eq_z0_of_ew {u : ↥V} (h : ew E u = 8) : u = z0 E := by
  apply E.γ.injective
  rw [gamma_z0]
  exact Subtype.ext (Multiplicative.toAdd.injective (eq_ones_of_wt8 _ h))

omit [Finite G] in
theorem ew_v4 : ew E (v4 E) = 4 := by
  rw [ew, gamma_v4]
  change wt (eset {0, 1, 2, 3}) = 4
  rw [wt_eset]
  rfl

omit [Finite G] in
theorem nonsing_of_ew {u : ↥V} (h : ew E u = 2 ∨ ew E u = 6) : IsNonsing (F.β u) := by
  rw [E.β_eq]
  rcases h with h | h
  · exact ⟨E.γ u, rfl, h⟩
  · refine ⟨E.γ u * ⟨allOnes 8, allOnes_mem⟩, mk_mul_allOnes _ allOnes_mem, ?_⟩
    change (Finset.univ.filter fun i => (Multiplicative.toAdd ((E.γ u : ↥(coreMod 8)) :
      PermMod 8) + ones8) i ≠ 0).card = 2
    rw [wt_add_ones]
    change 8 - ew E u = 2
    rw [h]

omit [Finite G] in
theorem wt4_of_ew {u : ↥V} (h : ew E u = 4) : HasWt 4 (F.β u) := by
  rw [E.β_eq]
  exact ⟨E.γ u, rfl, h⟩

omit [Finite G] in
theorem ew_of_nonsing {u : ↥V} (h : IsNonsing (F.β u)) : ew E u = 2 ∨ ew E u = 6 := by
  rcases ew_cases E u with h0 | h2 | h4 | h6 | h8
  · exact absurd (by rw [eq_one_of_ew E h0, map_one]) (ne_one_of_nonsing h)
  · exact Or.inl h2
  · exact absurd (wt4_of_ew E h4) fun h' => not_nonsing_and_wt4 h h'
  · exact Or.inr h6
  · exact absurd (by rw [eq_z0_of_ew E h8, beta_z0]) (ne_one_of_nonsing h)

omit [Finite G] in
theorem ew_of_wt4 {u : ↥V} (h : HasWt 4 (F.β u)) : ew E u = 4 := by
  rcases ew_cases E u with h0 | h2 | h4 | h6 | h8
  · exfalso
    rw [eq_one_of_ew E h0, map_one] at h
    obtain ⟨m, hm, hm4⟩ := h
    rcases (mk_eq_one_iff m).1 hm with rfl | rfl
    · rw [show ((1 : ↥(coreMod 8)) : PermMod 8) = 1 from rfl, wt_one] at hm4
      exact absurd hm4 (by norm_num)
    · rw [show ((eOm : ↥(coreMod 8)) : PermMod 8) = allOnes 8 from rfl, wt_allOnes] at hm4
      exact absurd hm4 (by norm_num)
  · exact absurd h fun h' => not_nonsing_and_wt4 (nonsing_of_ew E (Or.inl h2)) h'
  · exact h4
  · exact absurd h fun h' => not_nonsing_and_wt4 (nonsing_of_ew E (Or.inr h6)) h'
  · exfalso
    rw [eq_z0_of_ew E h8, beta_z0] at h
    obtain ⟨m, hm, hm4⟩ := h
    rcases (mk_eq_one_iff m).1 hm with rfl | rfl
    · rw [show ((1 : ↥(coreMod 8)) : PermMod 8) = 1 from rfl, wt_one] at hm4
      exact absurd hm4 (by norm_num)
    · rw [show ((eOm : ↥(coreMod 8)) : PermMod 8) = allOnes 8 from rfl, wt_allOnes] at hm4
      exact absurd hm4 (by norm_num)

omit [Finite G] in
theorem exists_L_conj {u w : ↥V} (h : ew E u = ew E w) :
    ∃ l ∈ L, l * (u : G) * l⁻¹ = w := by
  by_cases h0 : ew E u = 0
  · have hu := eq_one_of_ew E h0
    have hw := eq_one_of_ew E (show ew E w = 0 by rw [← h, h0])
    rw [hu, hw]
    exact ⟨1, L.one_mem, by simp⟩
  by_cases h8 : ew E u = 8
  · have hu := eq_z0_of_ew E h8
    have hw := eq_z0_of_ew E (show ew E w = 8 by rw [← h, h8])
    rw [hu, hw]
    exact ⟨1, L.one_mem, by group⟩
  have hk : ew E u ≤ 6 := by
    rcases ew_cases E u with h' | h' | h' | h' | h' <;> omega
  obtain ⟨σ, hσ⟩ := exists_perm (x := ((E.γ u : ↥(coreMod 8)) : PermMod 8))
    (y := ((E.γ w : ↥(coreMod 8)) : PermMod 8)) (k := ew E u) hk rfl h.symm
  obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π σ).2
  refine ⟨l, hlL, ?_⟩
  have h1 := E.equi σ u
  rw [← hla] at h1
  have h2 : coreAct 8 σ (E.γ u) = E.γ w := Subtype.ext (by rw [coreAct_coe]; exact hσ)
  rw [h2] at h1
  exact congrArg Subtype.val (E.γ.injective h1)

end Weights

section Fusion

variable (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (h3228 : Stmt3_2_2_eight)
  (hA8 : FactA8SolvNormPartition) (h1262 : Theorem12_6_2) (hNF : NoFuse1261926)
  {F : Frame126 T L V} (E : Frame126E F) (hH : Hyp126 G T L V)
  (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥)

omit [Finite G] in
theorem z0_ne_one' : ((z0 E : ↥V) : G) ≠ 1 := by
  intro h
  apply eOm_ne_one
  rw [← gamma_z0 E, show z0 E = 1 from Subtype.ext h, map_one]

omit [Finite G] in
theorem z0_sq : ((z0 E : ↥V) : G) * ((z0 E : ↥V) : G) = 1 := by
  have h1 : z0 E * z0 E = 1 := by
    apply E.γ.injective
    rw [map_mul, gamma_z0, eOm_mul_self, map_one]
  exact congrArg Subtype.val h1

include h331 h1222 hH hZ in
theorem centralizer_z0 :
    Subgroup.centralizer ({((z0 E : ↥V) : G)} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  centralizer_le_M h331 hH (z0_ne_one' E) (hH.hyp.irrPlus.1.trans
    (reducedAggregate_le_pCoreOf _ |>.trans
      (pCoreOf_le_of_le_normalizer hH.hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)))
      (z0 E).2) (z0_mem E)
    (Subgroup.mem_centralizer_iff.2 fun _ ht => z0_comm E h1222 hH hZ ht)

include h1222 hH hZ h1262 E in
theorem class_nonsing {g : G} {u w : ↥V} (hw : (w : G) = g * u * g⁻¹)
    (hu : IsNonsing (F.β u)) : IsNonsing (F.β w) := by
  rcases ew_cases E w with h0 | h2 | h4 | h6 | h8
  · exfalso
    have hw1 : (w : G) = 1 := congrArg Subtype.val (eq_one_of_ew E h0)
    apply ne_one_of_nonsing hu
    have : u = 1 := Subtype.ext (by
      calc (u : G) = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [← hw, hw1]; group)
    rw [this, map_one]
  · exact nonsing_of_ew E (Or.inl h2)
  · exfalso
    obtain ⟨l, -, hl⟩ := exists_L_conj E (show ew E (v4 E) = ew E w by rw [ew_v4, h4])
    refine not_conj_nonsing h1262 h1222 E hH hZ (h := g⁻¹ * l) hu ?_
    calc g⁻¹ * l * ((v4 E : ↥V) : G) * (g⁻¹ * l)⁻¹ = g⁻¹ * (l * (v4 E : G) * l⁻¹) * g := by group
      _ = g⁻¹ * (g * u * g⁻¹) * g := by rw [hl, hw]
      _ = u := by group
  · exact nonsing_of_ew E (Or.inr h6)
  · exfalso
    have hwz : (w : G) = z0 E := congrArg Subtype.val (eq_z0_of_ew E h8)
    have hTz : T ≤ Subgroup.centralizer ({((z0 E : ↥V) : G)} : Set G) := fun t ht => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact z0_comm E h1222 hH hZ ht
    have h1 := conj_le_centralizer (g := g⁻¹) hTz
    rw [show g⁻¹ * ((z0 E : ↥V) : G) * g⁻¹⁻¹ = u by rw [← hwz, hw]; group] at h1
    exact not_two_central h1262 h1222 F hH ⟨u.2, hu⟩ (sylow_conj hH.hyp.sylow g⁻¹) h1

include h331 h1222 h1228 h3228 hA8 hH hZ h1262 in
theorem class_z0 {g : G} {u w : ↥V} (hw : (w : G) = g * u * g⁻¹) (hu : u = z0 E) :
    w = z0 E := by
  have hw' : (u : G) = g⁻¹ * w * g⁻¹⁻¹ := by rw [hw]; group
  have hβu : F.β u = 1 := by rw [hu, beta_z0]
  rcases ew_cases E w with h0 | h2 | h4 | h6 | h8
  · exfalso
    apply z0_ne_one' E
    rw [← hu, hw', congrArg Subtype.val (eq_one_of_ew E h0)]
    simp
  · exact absurd hβu (ne_one_of_nonsing (class_nonsing h1222 h1262 E hH hZ hw'
      (nonsing_of_ew E (Or.inl h2))))
  · exfalso
    obtain ⟨l, -, hl⟩ := exists_L_conj E (show ew E (v4 E) = ew E w by rw [ew_v4, h4])
    refine false_of_conj h331 h1222 h1228 h3228 hA8 E hH hZ (g := g⁻¹ * l)
      (x := ((z0 E : ↥V) : G)) ?_ (centralizer_z0 h331 h1222 E hH hZ) (z0_mem E)
    rw [← hu, hw', ← hl]
    group
  · exact absurd hβu (ne_one_of_nonsing (class_nonsing h1222 h1262 E hH hZ hw'
      (nonsing_of_ew E (Or.inr h6))))
  · exact eq_z0_of_ew E h8

omit [Finite G] in
theorem ew_z0 : ew E (z0 E) = 8 := by
  rw [ew, gamma_z0]
  exact wt_allOnes

include h331 h1222 h1228 h3228 hA8 hH hZ h1262 in
theorem class_4 {g : G} {u w : ↥V} (hw : (w : G) = g * u * g⁻¹) (hu : ew E u = 4) :
    ew E w = 4 := by
  have hw' : (u : G) = g⁻¹ * w * g⁻¹⁻¹ := by rw [hw]; group
  rcases ew_cases E w with h0 | h2 | h4 | h6 | h8
  · exfalso
    have hu1 : u = 1 := Subtype.ext (by rw [hw', congrArg Subtype.val (eq_one_of_ew E h0)]; simp)
    rw [hu1] at hu
    exact absurd hu (by rw [ew, map_one]; decide)
  · exact absurd (wt4_of_ew E hu) fun h' => not_nonsing_and_wt4
      (class_nonsing h1222 h1262 E hH hZ hw' (nonsing_of_ew E (Or.inl h2))) h'
  · exact h4
  · exact absurd (wt4_of_ew E hu) fun h' => not_nonsing_and_wt4
      (class_nonsing h1222 h1262 E hH hZ hw' (nonsing_of_ew E (Or.inr h6))) h'
  · exfalso
    have h1 := class_z0 h331 h1222 h1228 h3228 hA8 h1262 E hH hZ hw' (eq_z0_of_ew E h8)
    rw [h1, ew_z0] at hu
    exact absurd hu (by norm_num)

omit [Finite G] in
theorem ew_mul_z0 (w : ↥V) : ew E (w * z0 E) = 8 - ew E w := by
  rw [ew, map_mul, gamma_z0]
  change (Finset.univ.filter fun i => (Multiplicative.toAdd ((E.γ w : ↥(coreMod 8)) :
    PermMod 8) + ones8) i ≠ 0).card = 8 - ew E w
  rw [wt_add_ones]
  rfl

include h1222 hH hZ h1262 hNF in
theorem class_2 {g : G} {u w : ↥V} (hw : (w : G) = g * u * g⁻¹) (hu : ew E u = 2) :
    ew E w = 2 := by
  have hun := nonsing_of_ew E (Or.inl hu)
  rcases ew_of_nonsing E (class_nonsing h1222 h1262 E hH hZ hw hun) with h2 | h6
  · exact h2
  · exfalso
    have hwz : ew E (w * z0 E) = 2 := by rw [ew_mul_z0, h6]
    obtain ⟨l, hlL, hl⟩ := exists_L_conj E (show ew E u = ew E (w * z0 E) by rw [hu, hwz])
    have hlz : l * ((z0 E : ↥V) : G) = z0 E * l := Subgroup.mem_centralizer_iff.1 (z0_mem E) l hlL
    refine hNF G T L V F hH u (z0 E) (l⁻¹ * g) ⟨u.2, hun⟩
      (h1262 G T L V F hH u ⟨u.2, hun⟩) ⟨(z0 E).2, z0_mem E⟩ (z0_ne_one' E) ?_
    have hzz := z0_sq E
    have e1 : (w : G) = l * u * l⁻¹ * z0 E := by
      have : ((w * z0 E : ↥V) : G) = l * u * l⁻¹ := hl.symm
      calc (w : G) = (w : G) * (z0 E : G) * (z0 E : G) := by rw [mul_assoc, hzz, mul_one]
        _ = l * u * l⁻¹ * z0 E := by rw [← this]; rfl
    calc l⁻¹ * g * (u : G) * (l⁻¹ * g)⁻¹ = l⁻¹ * (g * u * g⁻¹) * l := by group
      _ = l⁻¹ * (l * u * l⁻¹ * z0 E) * l := by rw [← hw, e1]
      _ = u * (l⁻¹ * ((z0 E : ↥V) : G) * l) := by group
      _ = u * z0 E := by
        rw [show l⁻¹ * ((z0 E : ↥V) : G) * l = l⁻¹ * (((z0 E : ↥V) : G) * l) by group, ← hlz]
        group

include h331 h1222 h1228 h3228 hA8 h1262 hNF in
theorem fusion_of_ne_bot (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹ := by
  obtain ⟨E⟩ := exists_frame126E h1222 F hH hZ
  intro u hu g hy
  set u' : ↥V := ⟨u, hu⟩ with hu'
  set w' : ↥V := ⟨g * u * g⁻¹, hy⟩ with hw'
  have hw : (w' : G) = g * u' * g⁻¹ := rfl
  have hw2 : (u' : G) = g⁻¹ * w' * g⁻¹⁻¹ := by rw [hw]; group
  have heq : ew E u' = ew E w' := by
    rcases ew_cases E u' with h | h | h | h | h
    · have hu1 := eq_one_of_ew E h
      have hw1 : w' = 1 := Subtype.ext (by
        rw [hw, show (u' : G) = 1 from congrArg Subtype.val hu1]
        simp)
      rw [h, hw1, ew, map_one]
      decide
    · rw [h, class_2 h1222 h1262 hNF E hH hZ hw h]
    · rw [h, class_4 h331 h1222 h1228 h3228 hA8 h1262 E hH hZ hw h]
    · rcases ew_of_nonsing E (class_nonsing h1222 h1262 E hH hZ hw
        (nonsing_of_ew E (Or.inr h))) with h2 | h6
      · have := class_2 h1222 h1262 hNF E hH hZ hw2 h2
        omega
      · rw [h, h6]
    · rw [h, class_z0 h331 h1222 h1228 h3228 hA8 h1262 E hH hZ hw (eq_z0_of_ew E h), ew_z0]
  exact exists_L_conj E heq

end Fusion

omit [IsMulCommutative ↥V] in
theorem exists_sylow_of_even (hT : quasithinIsSylowTwo T) {H K P : Subgroup G} (hKH : K ≤ H)
    (hPK : P ≤ K) (hP : IsPGroup 2 P) (hPT : 2 * Nat.card P = Nat.card T)
    (h2 : 2 ∣ K.relIndex H) :
    ∃ S : Subgroup G, quasithinIsSylowTwo S ∧ S ≤ H ∧ ∀ Q : Subgroup G, Q ≤ H →
      (Q.subgroupOf H).Normal → IsPGroup 2 Q → Q ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPH : P ≤ H := hPK.trans hKH
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  set S : Subgroup G := (Q : Subgroup ↥H).map H.subtype with hSdef
  have hSH : S ≤ H := Subgroup.map_subtype_le _
  have hSsub : S.subgroupOf H = Q :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hPS : P ≤ S := fun p hp => ⟨⟨p, hPH hp⟩, hQ (Subgroup.mem_subgroupOf.2 hp), rfl⟩
  have hS2 : IsPGroup 2 S := Q.isPGroup'.map _
  have hSidx : ¬ 2 ∣ S.relIndex H := by
    change ¬ 2 ∣ (S.subgroupOf H).index
    rw [hSsub]
    exact Q.not_dvd_index
  have hcard : 2 * Nat.card P ≤ Nat.card S := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hPS
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · exfalso
      have hm0 : m ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hm
        exact (Nat.card_pos (α := S)).ne' hm
      have hm1 : m = 1 := by omega
      rw [hm1, mul_one] at hm
      have hSP : P = S := Subgroup.eq_of_le_of_card_ge hPS hm.le
      apply hSidx
      rw [← hSP, ← Subgroup.relIndex_mul_relIndex P K H hPK hKH]
      exact Dvd.dvd.mul_left h2 _
    · rw [hm, mul_comm]
      exact Nat.mul_le_mul_left _ hm2
  have hST : Nat.card S ≤ Nat.card T := by
    obtain ⟨a, ha⟩ := hS2.exists_card_eq
    obtain ⟨b, hb⟩ := hT.1.exists_card_eq
    have h1 : Nat.card S ∣ Nat.card T * T.index := by
      rw [Subgroup.card_mul_index]
      exact Subgroup.card_subgroup_dvd_card S
    have hc : Nat.Coprime (2 ^ a) T.index :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hT.2)
    rw [ha] at h1 ⊢
    exact Nat.le_of_dvd Nat.card_pos (hc.dvd_of_dvd_mul_right h1)
  have hSeq : Nat.card S = Nat.card T := by omega
  refine ⟨S, ⟨hS2, ?_⟩, hSH, fun Q' hQ'H hQ'n hQ'2 => ?_⟩
  · have h1 := Subgroup.card_mul_index S
    have h2' := Subgroup.card_mul_index T
    rw [hSeq, ← h2'] at h1
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h1]
    exact hT.2
  · have h1 : IsPGroup 2 (Q'.subgroupOf H) :=
      hQ'2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ'H).symm
    have h2'' := h1.le_sylow_of_normal Q
    intro q hq
    exact ⟨⟨q, hQ'H hq⟩, h2'' (Subgroup.mem_subgroupOf.2 hq), rfl⟩

theorem part2 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h3228 : Stmt3_2_2_eight) (hA8 : FactA8SolvNormPartition) (h1229 : Stmt12_2_9)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hLZ6 : L = ⁅L, thompsonJ T⁆ → V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
      L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    ∀ v : G, F.Wt4 v → ¬ 2 ∣ (Subgroup.normalizer (L : Set G) ⊓
      Subgroup.centralizer ({v} : Set G)).relIndex (Subgroup.centralizer ({v} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E⟩ := exists_frame126E h1222 F hH hZ
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_reduced (hVT.trans le_sup_right) hred
  rintro v ⟨hvV, hv4⟩ h2
  set v' : ↥V := ⟨v, hvV⟩ with hv'
  have hew := ew_of_wt4 E hv4
  obtain ⟨l, hlL, hl⟩ := exists_L_conj E (show ew E (v4 E) = ew E v' by rw [ew_v4, hew])
  set T4 := T ⊓ Subgroup.centralizer ({((v4 E : ↥V) : G)} : Set G) with hT4def
  have hlM : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have hPM : B6.conjSub l T4 ≤ Subgroup.normalizer (L : Set G) ⊓
      Subgroup.centralizer ({v} : Set G) := by
    refine le_inf (conjSub_le_of_mem (Subgroup.le_normalizer hlM)
      (inf_le_left.trans hyp.normalizes)) ?_
    have := conj_le_centralizer (g := l) (show T4 ≤ Subgroup.centralizer
      ({((v4 E : ↥V) : G)} : Set G) from inf_le_right)
    rwa [hl] at this
  have hP2 : IsPGroup 2 (B6.conjSub l T4) :=
    (hyp.sylow.1.to_le inf_le_left).of_equiv
      (Subgroup.equivMapOfInjective T4 _ (MulAut.conj l).injective)
  have hPT : 2 * Nat.card (B6.conjSub l T4) = Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card T4 T
    rw [inf_of_le_left (inf_le_left : T4 ≤ T), relIndex_T4 E h1222 hH hZ] at h1
    rw [B6.card_conjSub]
    exact h1
  obtain ⟨S, hS, hSH, hnorm⟩ := exists_sylow_of_even hyp.sylow inf_le_right hPM hP2 hPT h2
  have hvS : v ∈ S := by
    refine hnorm (Subgroup.zpowers v) (Subgroup.zpowers_le.2
      (Subgroup.mem_centralizer_singleton_iff.2 rfl)) ⟨fun n hn g => ?_⟩
      (hyp.sylow.1.to_le (Subgroup.zpowers_le.2 (hVT hvV))) (Subgroup.mem_zpowers v)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hgv := Subgroup.mem_centralizer_singleton_iff.1 g.2
    have : (g : G) * v ^ k * (g : G)⁻¹ = v ^ k := by
      rw [← conj_zpow, show (g : G) * v * (g : G)⁻¹ = v by rw [hgv, mul_inv_cancel_right]]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hk, this]
    exact Subgroup.zpow_mem_zpowers v k
  obtain ⟨h, -, hh⟩ := A4.exists_conj_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_top)
    (isSylowTwoOf_of_quasithinIsSylowTwo hS le_top)
  set x := h⁻¹ * v * h with hxdef
  have hxT : x ∈ T := (hh v).1 hvS
  have hxC : x ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hs : h * t * h⁻¹ ∈ S := (hh _).2 (by rwa [show h⁻¹ * (h * t * h⁻¹) * h = t by group])
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hSH hs)
    calc t * x = h⁻¹ * ((h * t * h⁻¹) * v) * h := by rw [hxdef]; group
      _ = h⁻¹ * (v * (h * t * h⁻¹)) * h := by rw [h1]
      _ = x * t := by rw [hxdef]; group
  have hv1 : v ≠ 1 := by
    intro h1
    have h1' : v' = 1 := Subtype.ext h1
    have : ew E v' = 0 := by
      rw [h1', ew, map_one]
      decide
    rw [hew] at this
    exact absurd this (by norm_num)
  have hx1 : x ≠ 1 := fun h1 => hv1 (by
    calc v = h * x * h⁻¹ := by rw [hxdef]; group
      _ = 1 := by rw [h1]; group)
  have hx2 : x ^ 2 = 1 := by
    have hv2 := hVe.2 v hvV
    rw [hxdef, pow_two]
    calc h⁻¹ * v * h * (h⁻¹ * v * h) = h⁻¹ * (v * v) * h := by group
      _ = 1 := by rw [← pow_two, hv2]; group
  have hxZ : x ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hxT, hxC⟩, hx2⟩
  have hz0Z : ((z0 E : ↥V) : G) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨hVT (z0 E).2, Subgroup.mem_centralizer_iff.2
      fun _ ht => z0_comm E h1222 hH hZ ht⟩, ?_⟩
    rw [pow_two]
    exact z0_sq E
  have hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro hb
    have : ((z0 E : ↥V) : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hz0Z, z0_mem E⟩
    rw [hb, Subgroup.mem_bot] at this
    exact z0_ne_one' E this
  have hLJ := (h1229 G T L V hyp).2 ((h1229 G T L V hyp).1 hZL)
  have hLZ := hLZ6 hLJ hZ
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l' hl'
    exact (Subgroup.mem_centralizer_iff.1 (hLZ hl') x hxZ).symm
  have hCx := centralizer_le_M h331 hH hx1 hxT hxL hxC
  refine false_of_conj h331 h1222 h1228 h3228 hA8 E hH hZ (g := h⁻¹ * l) (x := x) ?_ hCx hxL
  have hl' : l * ((v4 E : ↥V) : G) * l⁻¹ = v := hl
  rw [hxdef, ← hl']
  group

end S126L19d

end CFSG.Quasithin.H13
