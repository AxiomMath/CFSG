module

public import CFSG.RankThree.PartTwo.Sec8.HeringBMemDefs
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofIrred

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open Subgroup CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec8.Item812Res12
open CFSG.Assembly.RankThreeEven (projSp)

section Base

variable {H : Type*} [Group H] {z : Fin 3 → H} {t₀ : H}

theorem eq_bot_or_eq_baseA' (hf : WreathFacts z t₀) {s : H}
    (hs : ∀ w, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)) {U : Subgroup H} (hUA : U ≤ baseA z)
    (htU : ∀ u ∈ U, t₀ * u * t₀⁻¹ ∈ U) (hsU : ∀ u ∈ U, s * u * s⁻¹ ∈ U) :
    U = ⊥ ∨ U = baseA z := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := irred_checks
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
  obtain ⟨w, hw⟩ := (mem_baseA_iff hf).mp (hUA y.2)
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hy1
    apply Subtype.ext
    rw [← hw]
    simp [vecElt]
  have hwU : vecElt z w ∈ U := by rw [hw]; exact y.2
  have hrot : ∀ v, vecElt z v ∈ U → vecElt z (Item8KFacts3.rotV v) ∈ U := fun v hv => by
    have := htU _ hv
    rwa [conj_vecElt hf] at this
  have hsgn : ∀ v, vecElt z v ∈ U → vecElt z (sgnV v) ∈ U := fun v hv => by
    have := hsU _ hv
    rwa [hs] at this
  have hadd : ∀ v v', vecElt z v ∈ U → vecElt z v' ∈ U → vecElt z (v + v') ∈ U :=
    fun v v' hv hv' => by
      rw [vecElt_add hf]
      exact U.mul_mem hv hv'
  have hP : ∀ v, vecElt z v ∈ U → vecElt z (v + sgnV v) ∈ U := fun v hv =>
    hadd _ _ hv (hsgn v hv)
  have p0 : vecElt z (Pi.single 0 (2 * w 0)) ∈ U := by
    rw [← c2 w]
    exact hrot _ (hP _ (hrot _ (hrot _ hwU)))
  have p1 : vecElt z (Pi.single 1 (2 * w 1)) ∈ U := by
    rw [← c3 w]
    exact hrot _ (hrot _ (hP _ (hrot _ hwU)))
  have p2 : vecElt z (Pi.single 2 (2 * w 2)) ∈ U := by
    rw [← c1 w]
    exact hP _ hwU
  obtain ⟨i, hi⟩ := c5 w hw0
  have hpi : vecElt z (Pi.single i (2 * w i)) ∈ U := by
    fin_cases i
    · exact p0
    · exact p1
    · exact p2
  have hei : vecElt z (Pi.single i 1) ∈ U := by
    rcases c4 i (2 * w i) hi with h | h
    · rwa [h] at hpi
    · rw [← h]
      exact hadd _ _ hpi hpi
  have hz : ∀ j, z j ∈ U := by
    intro j
    rw [← vecElt_single_one (z := z) j]
    rcases c8 i j with rfl | rfl | rfl
    · exact hei
    · rw [← c7]
      exact hrot _ hei
    · rw [← c7, ← c7]
      exact hrot _ (hrot _ hei)
  refine le_antisymm hUA ?_
  exact sup_le (sup_le (zpowers_le.mpr (hz 0)) (zpowers_le.mpr (hz 1))) (zpowers_le.mpr (hz 2))

theorem mem_normalizer_baseA_of_sgn (hf : WreathFacts z t₀) {s : H}
    (hs : ∀ w, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)) :
    s ∈ Subgroup.normalizer (baseA z : Set H) := by
  have c6 : ∀ w : Fin 3 → ZMod 3, sgnV (sgnV w) = w := irred_checks.2.2.2.2.2.1
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨w, rfl⟩ := (mem_baseA_iff hf).mp hx
    rw [hs]
    exact vecElt_mem_baseA hf _
  · intro hx
    obtain ⟨w, hw⟩ := (mem_baseA_iff hf).mp hx
    have e1 : x = vecElt z (sgnV w) := by
      have h1 : s * vecElt z (sgnV w) * s⁻¹ = s * x * s⁻¹ := by rw [hs, c6, hw]
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    rw [e1]
    exact vecElt_mem_baseA hf _

theorem sk_comm (hf : WreathFacts z t₀) {s : H}
    (hs : ∀ w, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)) (k : Fin 3) (a : ZMod 3) :
    (t₀ ^ ((k : ℕ) + 1) * s * (t₀ ^ ((k : ℕ) + 1))⁻¹) * vecElt z (Pi.single k a) =
      vecElt z (Pi.single k a) * (t₀ ^ ((k : ℕ) + 1) * s * (t₀ ^ ((k : ℕ) + 1))⁻¹) := by
  have hsg : sgnV (Pi.single 2 a) = Pi.single 2 a := by
    funext i
    fin_cases i <;> simp [sgnV]
  have hs2 : s * vecElt z (Pi.single 2 a) * s⁻¹ = vecElt z (Pi.single 2 a) := by
    rw [hs, hsg]
  have hconj : t₀ ^ ((k : ℕ) + 1) * vecElt z (Pi.single 2 a) * (t₀ ^ ((k : ℕ) + 1))⁻¹ =
      vecElt z (Pi.single k a) := by
    fin_cases k
    · show t₀ ^ (0 + 1) * vecElt z (Pi.single 2 a) * (t₀ ^ (0 + 1))⁻¹ = _
      rw [zero_add, pow_one, conj_vecElt hf]
      congr 1
      funext i
      fin_cases i <;> simp
    · show t₀ ^ (1 + 1) * vecElt z (Pi.single 2 a) * (t₀ ^ (1 + 1))⁻¹ = _
      rw [Item812Res5.conj_sq_vecElt hf]
      congr 1
      funext i
      fin_cases i <;> simp
    · show t₀ ^ (2 + 1) * vecElt z (Pi.single 2 a) * (t₀ ^ (2 + 1))⁻¹ = _
      rw [pow_succ, sq, show t₀ * t₀ * t₀ = 1 by rw [← pow_three', hf.pow_t]]
      simp
  rw [← hconj]
  set T := t₀ ^ ((k : ℕ) + 1) with hT
  set V := vecElt z (Pi.single 2 a) with hV
  have h1 : s * V = V * s := by
    have := hs2
    calc s * V = s * V * s⁻¹ * s := by group
      _ = V * s := by rw [this]
  calc T * s * T⁻¹ * (T * V * T⁻¹) = T * (s * V) * T⁻¹ := by group
    _ = T * (V * s) * T⁻¹ := by rw [h1]
    _ = T * V * T⁻¹ * (T * s * T⁻¹) := by group

end Base

section Model


theorem irred_model {E S H₀ U : Subgroup H6} {u g : H6}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hSE : S ≤ E)
    (hS9 : Nat.card S = 9) (huE : u ∈ E) (huS : u ∉ S) (hP : Group.IsPerfect H₀) (hSH : S ≤ H₀)
    (hH : H₀ ≤ Subgroup.centralizer ({u} : Set H6)) (hgN : g ∈ Subgroup.normalizer (E : Set H6))
    (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1) (hgnt : ∃ e ∈ E, g * e * g⁻¹ ≠ e) (hUE : U ≤ E)
    (hUs : ∀ s ∈ Subgroup.normalizer (E : Set H6), s * u = u * s →
      s ∈ Subgroup.normalizer (U : Set H6))
    (hUg : g ∈ Subgroup.normalizer (U : Set H6)) : U = ⊥ ∨ U = E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf := wreathFacts_zH
  have hW := Item812Res5.card_wreathW_zH_eq_pow
  have h81 := card_wreathW_zH
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  obtain ⟨k, hk⟩ := hg3
  have hgp : IsPGroup 3 (zpowers g : Subgroup H6) := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨k, Subtype.ext ?_⟩
    show (x : H6) ^ 3 ^ k = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hR : IsPGroup 3 (E ⊔ zpowers g : Subgroup H6) :=
    IsPGroup.to_sup_of_normal_left' hEp hgp (zpowers_le.mpr hgN)
  obtain ⟨x, hx⟩ := Item812Res5.exists_map_conj_le_wreathW hW hR
  set c : H6 →* H6 := (MulAut.conj x⁻¹).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj x⁻¹).injective
  have hcxy : ∀ y, c y = x⁻¹ * y * x := fun y => by simp [hc, MulAut.conj_apply]
  have hEW : E.map c ≤ wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := (Subgroup.map_mono le_sup_left).trans hx
  have hEA : E.map c = baseA zH :=
    eq_baseA_of_le_wreathW hf h81 hEW (Item812Res5.isElemAbelian_map_hom c hE)
      (by rw [Subgroup.card_map_of_injective hcinj, hE27])
  have hgW : c g ∈ wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := hx ⟨g, Subgroup.mem_sup_right (mem_zpowers g), rfl⟩
  obtain ⟨v, j, hvj⟩ := mem_wreathW hf hgW
  have hj : j ≠ 0 := by
    rintro rfl
    obtain ⟨e, he, hge⟩ := hgnt
    have hgA : c g ∈ E.map c := by
      rw [hEA, hvj, Fin.val_zero, pow_zero, mul_one]
      exact vecElt_mem_baseA hf v
    obtain ⟨g₁, hg₁, hg₁g⟩ := hgA
    have hg₁eq : g₁ = g := hcinj hg₁g
    subst hg₁eq
    apply hge
    have h1 : e * g₁ = g₁ * e :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨g₁, hg₁⟩)
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hUA' : U.map c ≤ baseA zH := hEA ▸ Subgroup.map_mono hUE
  have hUg' : ∀ u₀ ∈ U.map c, c g * u₀ * (c g)⁻¹ ∈ U.map c := by
    rintro _ ⟨u₁, hu₁, rfl⟩
    exact ⟨g * u₁ * g⁻¹, (Subgroup.mem_normalizer_iff.mp hUg u₁).mp hu₁, by simp⟩
  have htconj : ∀ a ∈ baseA zH, CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * a * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ ∈ baseA zH := fun a ha =>
    conj_t_mem_baseA hf ha
  have hcomm : ∀ a ∈ baseA zH, vecElt zH v * a = a * vecElt zH v := by
    intro a ha
    obtain ⟨w, rfl⟩ := (mem_baseA_iff hf).mp ha
    rw [← vecElt_add hf, ← vecElt_add hf, add_comm]
  have hgact : ∀ u₀ ∈ baseA zH, c g * u₀ * (c g)⁻¹ = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))⁻¹ := by
    intro u₀ hu₀
    have hmem : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))⁻¹ ∈ baseA zH := by
      have : ∀ n : ℕ, ∀ a ∈ baseA zH, CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n * a * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n)⁻¹ ∈ baseA zH := by
        intro n
        induction n with
        | zero => intro a ha; simpa using ha
        | succ n ih =>
          intro a ha
          have := htconj _ (ih a ha)
          rwa [show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (n + 1) * a * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (n + 1))⁻¹ =
            CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n * a * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n)⁻¹) * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ by rw [pow_succ']; group]
      exact this _ _ hu₀
    rw [hvj]
    have h1 := hcomm _ hmem
    calc vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) * u₀ * (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))⁻¹
        = vecElt zH v * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))⁻¹) * (vecElt zH v)⁻¹ := by group
      _ = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))⁻¹ := by
        rw [h1]
        group
  have htU' : ∀ u₀ ∈ U.map c, CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * u₀ * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ ∈ U.map c := by
    have hj12 : (j : ℕ) = 1 ∨ (j : ℕ) = 2 := Item812Res5.val_eq_one_or_two hj
    have hj' : ∀ u₀ ∈ U.map c, CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))⁻¹ ∈ U.map c := by
      intro u₀ hu₀
      rw [← hgact u₀ (hUA' hu₀)]
      exact hUg' u₀ hu₀
    rcases hj12 with h1 | h2
    · intro u₀ hu₀
      have := hj' u₀ hu₀
      rwa [h1, pow_one] at this
    · intro u₀ hu₀
      have h3 := hj' _ (hj' u₀ hu₀)
      rw [h2] at h3
      have e : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2 * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2 * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2)⁻¹) * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2)⁻¹ = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * u₀ * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ := by
        have ht3 : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 3 = 1 := hf.pow_t
        calc CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2 * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2 * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2)⁻¹) * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 2)⁻¹ = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 4 * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 4)⁻¹ := by
              group
          _ = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 3) * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 3)⁻¹ := by group
          _ = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * u₀ * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ := by rw [ht3]; group
      rwa [e] at h3
  have hu'A : c u ∈ baseA zH := hEA ▸ ⟨u, huE, rfl⟩
  obtain ⟨xu, hxu⟩ := (mem_baseA_iff hf).mp hu'A
  have hS'A : S.map c ≤ baseA zH := hEA ▸ Subgroup.map_mono hSE
  have hS'9 : Nat.card (S.map c) = 9 := by rw [Subgroup.card_map_of_injective hcinj, hS9]
  have hu'S : vecElt zH xu ∉ S.map c := by
    rw [hxu]
    rintro ⟨s₁, hs₁, hs₁u⟩
    exact huS (hcinj hs₁u ▸ hs₁)
  have hP' : Group.IsPerfect (H₀.map c) := @Group.IsPerfect.map _ _ _ _ _ c hP
  have hSH' : S.map c ≤ H₀.map c := Subgroup.map_mono hSH
  have hH' : H₀.map c ≤ Subgroup.centralizer ({vecElt zH xu} : Set H6) := by
    rintro _ ⟨h₁, hh₁, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hxu, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.mp (hH hh₁)
  obtain ⟨k₀, hk₀, hxk, -⟩ := Item8KFacts3.coord_eq_zero_of_perfect hS'A hS'9 hu'S hP' hSH' hH'
  have hxsingle : xu = Pi.single k₀ (xu k₀) := by
    funext i
    by_cases hi : i = k₀
    · subst hi; simp
    · simp [Pi.single_apply, hi, hxk i hi]
  set sk : H6 := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ ((k₀ : ℕ) + 1) * sH6 * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ ((k₀ : ℕ) + 1))⁻¹ with hsk
  have hsk_comm : sk * c u = c u * sk := by
    rw [← hxu, hxsingle]
    exact sk_comm hf sH6_conj k₀ (xu k₀)
  have hsN : sH6 ∈ Subgroup.normalizer (baseA zH : Set H6) :=
    mem_normalizer_baseA_of_sgn hf sH6_conj
  have htN : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ∈ Subgroup.normalizer (baseA zH : Set H6) := t_mem_normalizer hf
  have hskN : sk ∈ Subgroup.normalizer (baseA zH : Set H6) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ htN _) hsN)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ htN _))
  set sM : H6 := x * sk * x⁻¹ with hsM
  have hcsM : ∀ y, c (sM * y * sM⁻¹) = sk * c y * sk⁻¹ := by
    intro y
    rw [hcxy, hcxy, hsM]
    group
  have hsMN : sM ∈ Subgroup.normalizer (E : Set H6) := by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    have h1 : c e ∈ baseA zH := hEA ▸ ⟨e, he, rfl⟩
    have h2 : sk * c e * sk⁻¹ ∈ baseA zH := (Subgroup.mem_normalizer_iff.mp hskN _).mp h1
    rw [← hEA] at h2
    obtain ⟨e₂, he₂, he₂eq⟩ := h2
    have : sM * e * sM⁻¹ = e₂ := by
      apply hcinj
      rw [hcsM, he₂eq]
    rw [this]
    exact he₂
  have hsMu : sM * u = u * sM := by
    apply hcinj
    have h1 : c sM = sk := by
      rw [hcxy, hsM]
      group
    rw [map_mul c sM u, map_mul c u sM, h1, hsk_comm]
  have hsMU : sM ∈ Subgroup.normalizer (U : Set H6) := hUs sM hsMN hsMu
  have hskU : ∀ u₀ ∈ U.map c, sk * u₀ * sk⁻¹ ∈ U.map c := by
    rintro _ ⟨u₁, hu₁, rfl⟩
    refine ⟨sM * u₁ * sM⁻¹, (Subgroup.mem_normalizer_iff.mp hsMU u₁).mp hu₁, ?_⟩
    rw [hcsM]
  have htn : ∀ n : ℕ, ∀ u₀ ∈ U.map c, CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n)⁻¹ ∈ U.map c := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih =>
      intro a ha
      have := htU' _ (ih a ha)
      rw [show CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (n + 1) * a * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (n + 1))⁻¹ =
        CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n * a * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ n)⁻¹) * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ by rw [pow_succ']; group]
      exact this
  have htinv : (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ ((k₀ : ℕ) + 1))⁻¹ = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (2 * ((k₀ : ℕ) + 1)) := by
    have ht3 : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ 3 = 1 := hf.pow_t
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show (k₀ : ℕ) + 1 + 2 * ((k₀ : ℕ) + 1) = 3 * ((k₀ : ℕ) + 1) by ring, pow_mul,
      ht3, one_pow]
  have hsU' : ∀ u₀ ∈ U.map c, sH6 * u₀ * sH6⁻¹ ∈ U.map c := by
    intro u₀ hu₀
    have h1 := htn ((k₀ : ℕ) + 1) u₀ hu₀
    have h2 := hskU _ h1
    have h3 := htn (2 * ((k₀ : ℕ) + 1)) _ h2
    rw [← htinv] at h3
    have e : (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ ((k₀ : ℕ) + 1))⁻¹ * (sk * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ ((k₀ : ℕ) + 1) * u₀ * (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ ((k₀ : ℕ) + 1))⁻¹) *
        sk⁻¹) * ((CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ ((k₀ : ℕ) + 1))⁻¹)⁻¹ = sH6 * u₀ * sH6⁻¹ := by
      rw [hsk]
      group
    rw [e] at h3
    exact h3
  have hfin := eq_bot_or_eq_baseA' hf sH6_conj hUA' htU' hsU'
  rcases hfin with h0 | h1
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ hcinj).mp h0
  · right
    rw [← hEA] at h1
    exact Subgroup.map_injective hcinj h1

end Model

section Final


theorem kF812U3Irred_holds : KF812U3Irred := by
  intro M _ _ ⟨e⟩ E S H u g hE hE27 hSE hS9 huE huS hP hSH hHu hgN hg3 hgnt U hUE hUs hUg
  set e' : M ≃* H6 := e.trans sp62Equiv with he'
  set f : M →* H6 := e'.toMonoidHom with hf
  have hfi : Function.Injective f := e'.injective
  have hN : ∀ K : Subgroup M, Subgroup.normalizer ((K.map f : Subgroup H6) : Set H6) =
      (Subgroup.normalizer (K : Set M)).map f := fun K =>
    (Subgroup.map_equiv_normalizer_eq K e').symm
  have hEa : CFSG.Assembly.IsElemAbelian 3 (E.map f) :=
    Item812Res5.isElemAbelian_map_hom f hE
  have hHu' : H.map f ≤ Subgroup.centralizer ({f u} : Set H6) := by
    rintro _ ⟨h₁, hh₁, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg f (Subgroup.mem_centralizer_singleton_iff.mp (hHu hh₁))
  obtain ⟨k, hk⟩ := hg3
  obtain ⟨e₀, he₀, hge₀⟩ := hgnt
  have key := irred_model (E := E.map f) (S := S.map f) (H₀ := H.map f) (U := U.map f)
    (u := f u) (g := f g) hEa (by rw [Subgroup.card_map_of_injective hfi, hE27])
    (Subgroup.map_mono hSE) (by rw [Subgroup.card_map_of_injective hfi, hS9]) ⟨u, huE, rfl⟩
    (fun ⟨s₁, hs₁, hs₁u⟩ => huS (hfi hs₁u ▸ hs₁)) (@Group.IsPerfect.map _ _ _ _ _ f hP)
    (Subgroup.map_mono hSH) hHu' (by rw [hN]; exact ⟨g, hgN, rfl⟩)
    ⟨k, by rw [← map_pow, hk, map_one]⟩
    ⟨f e₀, ⟨e₀, he₀, rfl⟩, fun h => hge₀ (hfi (by simpa using h))⟩ (Subgroup.map_mono hUE)
    (by
      intro s' hs' hcomm
      rw [hN] at hs' ⊢
      obtain ⟨s₁, hs₁, rfl⟩ := hs'
      exact ⟨s₁, hUs s₁ hs₁ (hfi (by simpa using hcomm)), rfl⟩)
    (by rw [hN]; exact ⟨g, hUg, rfl⟩)
  rcases key with h0 | h1
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ hfi).mp h0)
  · exact Or.inr (Subgroup.map_injective hfi h1)

end Final


end CFSG.RankThree.PartTwo.Sec8.HeringBMem
