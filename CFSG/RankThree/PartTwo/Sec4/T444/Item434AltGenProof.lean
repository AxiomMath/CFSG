module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltCtx
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltGen
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Alt

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Equiv Equiv.Perm Subgroup Item434AltPerm

section PermFacts

variable {n : ℕ}

theorem map_conj_alternatingGroup (g : Perm (Fin n)) :
    (alternatingGroup (Fin n)).map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin n) := by
  have hN : (alternatingGroup (Fin n)).Normal := inferInstance
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hN.conj_mem x hx g
  · intro x hx
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, hN.conj_mem x hx g⁻¹, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conj_mem_and_coprime {g τ : Perm (Fin n)} (hτ : sign τ = 1) (hτ2 : τ ^ 2 = 1) :
    g * τ * g⁻¹ ∈ alternatingGroup (Fin n) ∧ Nat.Coprime (orderOf (g * τ * g⁻¹)) 3 := by
  refine ⟨?_, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hτ, mul_one,
      Int.units_mul_self]
  · have h2 : (g * τ * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hτ2, mul_one, mul_inv_cancel]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2) (by norm_num)

theorem alternatingGroup_le_closure_conj {r : ℕ} {gens : Fin r → Perm (Fin n)}
    (hgen : alternatingGroup (Fin n) ≤ closure (Set.range gens)) (g : Perm (Fin n)) :
    alternatingGroup (Fin n) ≤
      closure ((MulAut.conj g).toMonoidHom '' Set.range gens) := by
  rw [← MonoidHom.map_closure, ← map_conj_alternatingGroup g]
  exact Subgroup.map_mono hgen

theorem exists_le_commute {G : Type*} [Group G] (β : G →* Perm (Fin n)) {A : Subgroup G}
    {P₀ P : Subgroup (Perm (Fin n))} {g : Perm (Fin n)}
    (hg : A.map β = P₀.map (MulAut.conj g).toMonoidHom) (hP : P ≤ P₀) {τ : Perm (Fin n)}
    (hτ : ∀ x ∈ P, x * τ = τ * x) :
    ∃ B : Subgroup G, B ≤ A ∧
      Nat.card B = Nat.card (A ⊓ β.ker : Subgroup G) * Nat.card P ∧
      ∀ b ∈ B, β b * (g * τ * g⁻¹) = g * τ * g⁻¹ * β b := by
  set P' := P.map (MulAut.conj g).toMonoidHom with hP'
  have hP'A : P' ≤ A.map β := by
    rw [hg]
    exact Subgroup.map_mono hP
  refine ⟨A ⊓ P'.comap β, inf_le_left, ?_, ?_⟩
  · rw [card_inf_comap β hP'A, hP', Subgroup.card_map_of_injective (MulAut.conj g).injective]
  · intro b hb
    obtain ⟨x, hx, hxb⟩ := (Subgroup.mem_inf.mp hb).2
    rw [← hxb]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h := hτ x hx
    calc g * x * g⁻¹ * (g * τ * g⁻¹) = g * (x * τ) * g⁻¹ := by group
      _ = g * (τ * x) * g⁻¹ := by rw [h]
      _ = g * τ * g⁻¹ * (g * x * g⁻¹) := by group

theorem sign_eq_one_of_pow_three {σ : Perm (Fin n)} (hσ : σ ^ 3 = 1) : sign σ = 1 := by
  have h : sign σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem card_sup_zpowers_eq_nine {x y : Perm (Fin n)} (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy : y ^ 3 = 1) (hxy : x * y = y * x) (hne : ∀ k : Fin 3, y ≠ x ^ (k : ℕ)) :
    Nat.card (zpowers x ⊔ zpowers y : Subgroup (Perm (Fin n))) = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hxe : CFSG.Assembly.IsElemAbelian 3 (zpowers x) := by
    refine ⟨inferInstance, fun a ha => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hyx : y ∉ zpowers x := by
    rw [mem_zpowers_iff_mem_range_orderOf, hox, Finset.mem_image]
    rintro ⟨k, hk, hky⟩
    exact hne ⟨k, Finset.mem_range.mp hk⟩ hky.symm
  obtain ⟨-, hcard⟩ := Sec5.isElemAbelian_sup_zpowers hxe hyx hy fun a ha => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.zpow_left hxy k).eq)
  rw [hcard, Nat.card_zpowers, hox]

end PermFacts

section F0

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {n : ℕ} [NeZero n]

theorem false_of_altF0 (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) (hf : F0Facts n)
    (h2 : (Nat.card (Perm (Fin n))).factorization 3 = 2) {r : ℕ} (gens : Fin r → Perm (Fin n))
    (hgen : alternatingGroup (Fin n) ≤ closure (Set.range gens))
    (hspec : ∀ i, sign (gens i) = 1 ∧ gens i ^ 2 = 1 ∧
      (gens i * c1 n = c1 n * gens i ∨ gens i * c2 n = c2 n * gens i)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set β := altPerm hn e with hβ
  have hker : β.ker = Subgroup.centralizer (layer G : Set G) := ker_altPerm h.isQuasisimple hn e
  have hEp : IsPGroup 3 (A.map β) := h.isE27.isPGroup.map β
  have hE9 : Nat.card (A.map β) ≤ 9 := card_le_nine_of_isPGroup h2 hEp
  have hA27 := card_eq_card_inf_ker_mul_card_map β A
  rw [h.isE27.2, hker] at hA27
  have hC3 := h.card_inf_centralizer_layer_le
  have hCE : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 ∧
      Nat.card (A.map β) = 9 := by
    set c := Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G)
    set d := Nat.card (A.map β)
    have hc3 : c = 3 := by
      by_contra hc
      have : c ≤ 2 := by omega
      have : c * d ≤ 2 * 9 := Nat.mul_le_mul this hE9
      omega
    refine ⟨hc3, ?_⟩
    rw [hc3] at hA27
    omega
  obtain ⟨g, hg⟩ := exists_eq_map_conj_F0 hf h2 hEp hCE.2
  apply h.not_le
  refine layer_le_of_gens h hn e (alternatingGroup_le_closure_conj hgen g) ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  obtain ⟨hsign, hsq, hcomm⟩ := hspec i
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨hmem, hcop⟩ := conj_mem_and_coprime (g := g) hsign hsq
  refine ⟨hmem, hcop, ?_⟩
  obtain ⟨c, hcF, hc3, hc1, hci⟩ : ∃ c : Perm (Fin n), c ∈ F0 n ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧
      gens i * c = c * gens i := by
    have hab := isElemAbelian_F0 hf
    have h1 : c1 n ≠ 1 := by
      intro h1
      have := congrFun (hf.inj ![1, 0] (by rw [hf.e1, h1])) 0
      simp at this
    have h2' : c2 n ≠ 1 := by
      intro h1
      have := congrFun (hf.inj ![0, 1] (by rw [hf.e2, h1])) 1
      simp at this
    rcases hcomm with hc | hc
    · exact ⟨c1 n, mem_sup_left (mem_zpowers _), hab.2 _ (mem_sup_left (mem_zpowers _)), h1, hc⟩
    · exact ⟨c2 n, mem_sup_right (mem_zpowers _), hab.2 _ (mem_sup_right (mem_zpowers _)), h2',
        hc⟩
  have hcP : ∀ x ∈ zpowers c, x * gens i = gens i * x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left hci.symm k).eq)
  obtain ⟨B, hBA, hBcard, hBcomm⟩ := exists_le_commute β hg (zpowers_le.mpr hcF) hcP
  refine ⟨B, hBA, ?_, hBcomm⟩
  rw [hBcard, hker, hCE.1, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]

theorem false_of_alt_seven (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin 7)) : False :=
  false_of_altF0 h (Or.inr (by norm_num)) e f0Facts_seven factorization_seven gens7
    closure_gens7 fun i => by
      obtain ⟨h1, h2, h3, h4⟩ := gens7_spec i
      refine ⟨h1, h2, ?_⟩
      rcases lt_or_ge (i : ℕ) 3 with hi | hi
      · exact Or.inl (h3 hi)
      · exact Or.inr (h4 hi)

theorem false_of_alt_eight (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin 8)) : False :=
  false_of_altF0 h (Or.inr (by norm_num)) e f0Facts_eight factorization_eight gens8
    closure_gens8 fun i => by
      obtain ⟨h1, h2, h3, h4⟩ := gens8_spec i
      refine ⟨h1, h2, ?_⟩
      rcases lt_or_ge (i : ℕ) 3 with hi | hi
      · exact Or.inl (h3 hi)
      · exact Or.inr (h4 hi)

end F0

section A0

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {n : ℕ} [NeZero n]

theorem A0_le_alternatingGroup (hf : A0Facts n) : A0 n ≤ alternatingGroup (Fin n) := by
  intro x hx
  exact sign_eq_one_of_pow_three ((isElemAbelian_A0 hf).2 x hx)

theorem exists_E27_le_layer (h : Ctx434Core G A M Q) (hn : n = 5 ∨ 7 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) (hf : A0Facts n)
    (hZ : Subgroup.center (layer G) = ⊥) :
    ∃ D : Subgroup G, D ≤ layer G ∧ CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 27 := by
  set β := altPerm hn e with hβ
  have hLk : layer G ⊓ β.ker = ⊥ := by
    rw [layer_inf_ker_altPerm h.isQuasisimple, hZ, Subgroup.map_bot]
  have hinj : ∀ x ∈ layer G, ∀ y ∈ layer G, β x = β y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ layer G ⊓ β.ker :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hx) hy,
        by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]⟩
    rw [hLk, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem)
  have hA0L : A0 n ≤ (layer G).map β := by
    rw [map_layer_altPerm]
    exact A0_le_alternatingGroup hf
  refine ⟨layer G ⊓ (A0 n).comap β, inf_le_left, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨haL, haA⟩ := Subgroup.mem_inf.mp a.2
    obtain ⟨hbL, hbA⟩ := Subgroup.mem_inf.mp b.2
    refine hinj _ (mul_mem haL hbL) _ (mul_mem hbL haL) ?_
    change β ((a : G) * b) = β ((b : G) * a)
    rw [map_mul, map_mul]
    exact commute_of_mem_A0 hf haA hbA
  · intro x hx
    obtain ⟨hxL, hxA⟩ := Subgroup.mem_inf.mp hx
    refine hinj _ (pow_mem hxL 3) _ (one_mem _) ?_
    rw [map_pow, map_one]
    exact (isElemAbelian_A0 hf).2 _ hxA
  · rw [card_inf_comap β hA0L, hLk, Subgroup.card_bot, one_mul, card_A0 hf]

theorem false_of_altA0 (h : Ctx434Core G A M Q) (hn8 : 8 ≤ n)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin n)) (hf : WFacts n)
    (h4 : (Nat.card (Perm (Fin n))).factorization 3 = 4) {r : ℕ} (gens : Fin r → Perm (Fin n))
    (hgen : alternatingGroup (Fin n) ≤ closure (Set.range gens))
    (hspec : ∀ i, sign (gens i) = 1 ∧ gens i ^ 2 = 1 ∧
      ∃ x ∈ A0 n, ∃ y ∈ A0 n, x ≠ 1 ∧ (∀ k : Fin 3, y ≠ x ^ (k : ℕ)) ∧
        gens i * x = x * gens i ∧ gens i * y = y * gens i) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : n = 5 ∨ 7 ≤ n := Or.inr (by omega)
  have hA := hf.toA0Facts
  set β := altPerm hn e with hβ
  have hker : β.ker = Subgroup.centralizer (layer G : Set G) := ker_altPerm h.isQuasisimple hn e
  have hZ := center_layer_eq_bot_of_eight_le h e hn8
  obtain ⟨D, hDL, hDe, hD27⟩ := exists_E27_le_layer h hn e hA hZ
  have hC1 := inf_centralizer_layer_eq_bot_of_le h hZ hDL hDe hD27
  have hA27 := card_eq_card_inf_ker_mul_card_map β A
  rw [h.isE27.2, hker, hC1, Subgroup.card_bot, one_mul] at hA27
  have hEe := CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 β A h.isE27.1
  obtain ⟨g, hg⟩ := exists_eq_map_conj_A0 hf h4 hEe hA27.symm
  apply h.not_le
  refine layer_le_of_gens h hn e (alternatingGroup_le_closure_conj hgen g) ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  obtain ⟨hsign, hsq, x, hx, y, hy, hx1, hne, hxi, hyi⟩ := hspec i
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨hmem, hcop⟩ := conj_mem_and_coprime (g := g) hsign hsq
  refine ⟨hmem, hcop, ?_⟩
  have hab := isElemAbelian_A0 hA
  have hP : zpowers x ⊔ zpowers y ≤ A0 n := sup_le (zpowers_le.mpr hx) (zpowers_le.mpr hy)
  have hle : zpowers x ⊔ zpowers y ≤ Subgroup.centralizer {gens i} :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxi.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyi.symm))
  have hPc : ∀ z ∈ zpowers x ⊔ zpowers y, z * gens i = gens i * z := fun z hz =>
    mem_centralizer_singleton_iff.mp (hle hz)
  obtain ⟨B, hBA, hBcard, hBcomm⟩ := exists_le_commute β hg hP hPc
  refine ⟨B, hBA, ?_, hBcomm⟩
  rw [hBcard, hker, hC1, Subgroup.card_bot, one_mul,
    card_sup_zpowers_eq_nine (hab.2 x hx) hx1 (hab.2 y hy) (commute_of_mem_A0 hA hx hy) hne]

structure PairFacts (n : ℕ) [NeZero n] : Prop where
  c1_ne : c1 n ≠ 1
  c2_ne : c2 n ≠ 1
  c21 : ∀ k : Fin 3, c2 n ≠ c1 n ^ (k : ℕ)
  c31 : ∀ k : Fin 3, c3 n ≠ c1 n ^ (k : ℕ)
  c32 : ∀ k : Fin 3, c3 n ≠ c2 n ^ (k : ℕ)

theorem c1_mem_A0 : c1 n ∈ A0 n := mem_sup_left (mem_sup_left (mem_zpowers _))

theorem c2_mem_A0 : c2 n ∈ A0 n := mem_sup_left (mem_sup_right (mem_zpowers _))

theorem c3_mem_A0 : c3 n ∈ A0 n := mem_sup_right (mem_zpowers _)

theorem pairFacts_ten : PairFacts 10 where
  c1_ne := by decide +kernel
  c2_ne := by decide +kernel
  c21 := by decide +kernel
  c31 := by decide +kernel
  c32 := by decide +kernel

theorem pairFacts_eleven : PairFacts 11 where
  c1_ne := by decide +kernel
  c2_ne := by decide +kernel
  c21 := by decide +kernel
  c31 := by decide +kernel
  c32 := by decide +kernel

theorem spec_of_pairs {r : ℕ} {gens : Fin r → Perm (Fin n)} (hp : PairFacts n) (i : Fin r)
    (hsign : sign (gens i) = 1) (hsq : gens i ^ 2 = 1)
    (h12 : (i : ℕ) < 2 → gens i * c1 n = c1 n * gens i ∧ gens i * c2 n = c2 n * gens i)
    (h13 : 2 ≤ (i : ℕ) → (i : ℕ) < 4 →
      gens i * c1 n = c1 n * gens i ∧ gens i * c3 n = c3 n * gens i)
    (h23 : 4 ≤ (i : ℕ) → gens i * c2 n = c2 n * gens i ∧ gens i * c3 n = c3 n * gens i) :
    sign (gens i) = 1 ∧ gens i ^ 2 = 1 ∧
      ∃ x ∈ A0 n, ∃ y ∈ A0 n, x ≠ 1 ∧ (∀ k : Fin 3, y ≠ x ^ (k : ℕ)) ∧
        gens i * x = x * gens i ∧ gens i * y = y * gens i := by
  refine ⟨hsign, hsq, ?_⟩
  rcases lt_or_ge (i : ℕ) 2 with hi | hi
  · exact ⟨c1 n, c1_mem_A0, c2 n, c2_mem_A0, hp.c1_ne, hp.c21, (h12 hi).1, (h12 hi).2⟩
  rcases lt_or_ge (i : ℕ) 4 with hi' | hi'
  · exact ⟨c1 n, c1_mem_A0, c3 n, c3_mem_A0, hp.c1_ne, hp.c31, (h13 hi hi').1, (h13 hi hi').2⟩
  · exact ⟨c2 n, c2_mem_A0, c3 n, c3_mem_A0, hp.c2_ne, hp.c32, (h23 hi').1, (h23 hi').2⟩

theorem false_of_alt_ten (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin 10)) : False :=
  false_of_altA0 h (by norm_num) e wFacts_ten factorization_ten gens10 closure_gens10 fun i => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := gens10_spec i
    exact spec_of_pairs pairFacts_ten i h1 h2 h3 h4 h5

theorem false_of_alt_eleven (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* alternatingGroup (Fin 11)) : False :=
  false_of_altA0 h (by norm_num) e wFacts_eleven factorization_eleven gens11 closure_gens11
    fun i => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := gens11_spec i
      exact spec_of_pairs pairFacts_eleven i h1 h2 h3 h4 h5

end A0

end CFSG.RankThree.PartTwo.Sec4.Item434Alt
