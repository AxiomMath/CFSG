module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofTau

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open CFSG.Assembly (IsElemAbelian)
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section TauMain

variable {K : Type} [Field K]

theorem commute_of_normalizes_small {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    (hE : Nat.card E ≤ 4) {u : G} {p : ℕ} (hp : p.Prime) (hp5 : 4 < p) (hu : u ^ p = 1)
    (hnorm : ∀ e ∈ E, u * e * u⁻¹ ∈ E) {e : G} (he : e ∈ E) : u * e = e * u := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hpow : ∀ k : ℕ, ∀ e ∈ E, u ^ k * e * (u ^ k)⁻¹ ∈ E := by
    intro k
    induction k with
    | zero => intro e he; simpa using he
    | succ k ih =>
      intro e he
      have h1 := hnorm _ (ih e he)
      rw [show u ^ (k + 1) * e * (u ^ (k + 1))⁻¹ = u * (u ^ k * e * (u ^ k)⁻¹) * u⁻¹ by group]
      exact h1
  let f : Fin 5 → E := fun k => ⟨u ^ (k : ℕ) * e * (u ^ (k : ℕ))⁻¹, hpow k e he⟩
  have hcard : Fintype.card E < Fintype.card (Fin 5) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hd : ∃ d : ℕ, 1 ≤ d ∧ d ≤ 4 ∧ u ^ d * e = e * u ^ d := by
    have key : ∀ a b : Fin 5, a < b → f a = f b →
        u ^ ((b : ℕ) - a) * e = e * u ^ ((b : ℕ) - a) := by
      intro a b hab h
      have h1 : u ^ (a : ℕ) * e * (u ^ (a : ℕ))⁻¹ = u ^ (b : ℕ) * e * (u ^ (b : ℕ))⁻¹ :=
        congrArg Subtype.val h
      have hb : (b : ℕ) = a + ((b : ℕ) - a) := by omega
      rw [hb, pow_add] at h1
      have h2 : e = u ^ ((b : ℕ) - a) * e * (u ^ ((b : ℕ) - a))⁻¹ := by
        have := congrArg (fun x => (u ^ (a : ℕ))⁻¹ * x * u ^ (a : ℕ)) h1
        rw [show (u ^ (a : ℕ))⁻¹ * (u ^ (a : ℕ) * e * (u ^ (a : ℕ))⁻¹) * u ^ (a : ℕ) = e by group,
          show (u ^ (a : ℕ))⁻¹ * (u ^ (a : ℕ) * u ^ ((b : ℕ) - a) * e *
            (u ^ (a : ℕ) * u ^ ((b : ℕ) - a))⁻¹) * u ^ (a : ℕ) =
            u ^ ((b : ℕ) - a) * e * (u ^ ((b : ℕ) - a))⁻¹ by group] at this
        exact this
      calc u ^ ((b : ℕ) - a) * e = u ^ ((b : ℕ) - a) * e * (u ^ ((b : ℕ) - a))⁻¹ *
            u ^ ((b : ℕ) - a) := by group
        _ = e * u ^ ((b : ℕ) - a) := by rw [← h2]
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨(j : ℕ) - i, by omega, by omega, key i j h hfij⟩
    · exact ⟨(i : ℕ) - j, by omega, by omega, key j i h hfij.symm⟩
  obtain ⟨d, hd1, hd4, hde⟩ := hd
  have hcop : Nat.Coprime d p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hum : u = (u ^ d) ^ m := by
    rw [← pow_mul]
    calc u = u ^ (d * m % p) := by rw [hm.2, pow_one]
      _ = u ^ (d * m % p) * (u ^ p) ^ (d * m / p) := by rw [hu, one_pow, mul_one]
      _ = u ^ (d * m) := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [hum]
  exact ((Commute.pow_left hde m) : Commute _ e).eq

theorem eq_one_or_eq_of_card_two {G : Type*} [Group G] {E : Subgroup G} (hE : Nat.card E = 2)
    {t : G} (htE : t ∈ E) (ht1 : t ≠ 1) {z : G} (hz : z ∈ E) : z = 1 ∨ z = t := by
  classical
  by_contra h
  push Not at h
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype E := Fintype.ofFinite E
  have hsub : ({⟨1, E.one_mem⟩, ⟨t, htE⟩, ⟨z, hz⟩} : Finset E) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hc := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hE] at hc
  rw [Finset.card_insert_of_notMem, Finset.card_pair] at hc
  · omega
  · intro h'; exact h.2 (congrArg Subtype.val h').symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h' => ht1 (congrArg Subtype.val h').symm,
      fun h' => h.1 (congrArg Subtype.val h').symm⟩

theorem outerCentConcl_of_tau [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    {T : Subgroup (MulAut (projectiveSL 3 K))}
    (h1 : MulAut.conj (proj 3 K tauOne) ∈
      Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K))))
    (h2 : MulAut.conj (proj 3 K tauTwo) ∈
      Subgroup.centralizer (T : Set (MulAut (projectiveSL 3 K)))) :
    OuterCentConcl (innP K) T := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp4 : 4 < p := by
    rcases (by omega : p = 4 ∨ 4 < p) with h | h
    · exfalso
      rw [h] at hp
      norm_num at hp
    · exact h
  have : Finite (MulAut (projectiveSL 3 K)) :=
    Finite.of_injective (fun σ : MulAut (projectiveSL 3 K) => (σ : projectiveSL 3 K → _))
      (fun a b h => MulEquiv.ext (congrFun h))
  set τ₁ := MulAut.conj (proj 3 K tauOne) with hτ₁
  set τ₂ := MulAut.conj (proj 3 K tauTwo) with hτ₂
  have hτ₁N : τ₁ ∈ threeClosureIn (innP K) T := Subgroup.subset_closure
    ⟨Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, h1⟩, by rw [hτ₁, ← map_pow, ← map_pow, tauOne_pow_three,
      map_one, map_one]⟩
  have hτ₂N : τ₂ ∈ threeClosureIn (innP K) T := Subgroup.subset_closure
    ⟨Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, h2⟩, by rw [hτ₂, ← map_pow, ← map_pow, tauTwo_pow_three,
      map_one, map_one]⟩
  have ha1 : ∀ x ∈ innP K, x ^ 2 = 1 → x ≠ 1 → τ₁ * x = x * τ₁ → τ₂ * x = x * τ₂ → False := by
    rintro _ ⟨y, rfl⟩ hx2 hx1 hc1 hc2
    refine not_commute_tau hp3 (y := y) (conj_injective_three (by rw [map_pow, hx2, map_one]))
      (fun h => hx1 (by rw [h, map_one])) ?_ ?_
    · exact conj_injective_three (by rw [map_mul, map_mul]; exact hc1)
    · exact conj_injective_three (by rw [map_mul, map_mul]; exact hc2)
  refine ⟨fun P hPN hP2 hNP x hx n hn => ?_, fun P hP hP2 => ?_⟩
  ·
    have hP1 : P = ⊥ := by
      by_contra hne
      obtain ⟨t, htP, ht1, ht2, htc⟩ := exists_central_involution hP2 hne
      let E : Subgroup (MulAut (projectiveSL 3 K)) :=
        { carrier := {z | z ∈ P ∧ (∀ w ∈ P, w * z = z * w) ∧ z ^ 2 = 1}
          mul_mem' := by
            rintro a b ⟨haP, hac, ha2⟩ ⟨hbP, hbc, hb2⟩
            refine ⟨P.mul_mem haP hbP, fun w hw => ?_, ?_⟩
            · rw [← mul_assoc, hac w hw, mul_assoc, hbc w hw, ← mul_assoc]
            · have hab : a * b = b * a := hbc a haP
              rw [(Commute.mul_pow hab 2), ha2, hb2, one_mul]
          one_mem' := ⟨P.one_mem, fun w _ => by rw [mul_one, one_mul], one_pow 2⟩
          inv_mem' := by
            rintro a ⟨haP, hac, ha2⟩
            refine ⟨P.inv_mem haP, fun w hw => ?_, by rw [inv_pow, ha2, inv_one]⟩
            have h' : a * w = w * a := (hac w hw).symm
            calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
              _ = a⁻¹ * (w * a) * a⁻¹ := by rw [h']
              _ = a⁻¹ * w := by group }
      have hmemE : ∀ z, z ∈ E ↔ z ∈ P ∧ (∀ w ∈ P, w * z = z * w) ∧ z ^ 2 = 1 := fun z => Iff.rfl
      have htE : t ∈ E := (hmemE t).mpr ⟨htP, htc, ht2⟩
      have hEP : E ≤ P := fun z hz => ((hmemE z).mp hz).1
      have hEI : E ≤ innP K := fun z hz =>
        (Subgroup.mem_inf.mp (threeClosureIn_le (innP K) T (hPN (hEP hz)))).1
      have hEn : ∀ τ ∈ threeClosureIn (innP K) T, ∀ z ∈ E, τ * z * τ⁻¹ ∈ E := by
        intro τ hτ z hz
        obtain ⟨hzP, hzc, hz2⟩ := (hmemE z).mp hz
        have hPn := Subgroup.mem_normalizer_iff.mp (hNP hτ)
        refine (hmemE _).mpr ⟨(hPn z).mp hzP, fun w hw => ?_, ?_⟩
        · have hw' : τ⁻¹ * w * τ ∈ P := by
            have := (hPn (τ⁻¹ * w * τ)).mpr
            apply this
            simpa [mul_assoc] using hw
          have h' := hzc _ hw'
          calc w * (τ * z * τ⁻¹) = τ * ((τ⁻¹ * w * τ) * z) * τ⁻¹ := by group
            _ = τ * (z * (τ⁻¹ * w * τ)) * τ⁻¹ := by rw [h']
            _ = τ * z * τ⁻¹ * w := by group
        · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
      let EY : Subgroup (projectiveSL 3 K) :=
        E.comap (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K))
      have hEYe : IsElemAbelian 2 EY := by
        refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
        · apply conj_injective_three
          rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
          exact ((hmemE _).mp b.2).2.1 _ (hEP a.2)
        · apply conj_injective_three
          rw [map_pow, map_one]
          exact ((hmemE _).mp ha).2.2
      have hcardEY : Nat.card EY = Nat.card E := by
        have hmap : EY.map (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) = E :=
          Subgroup.map_comap_eq_self hEI
        rw [← hmap, Subgroup.card_map_of_injective conj_injective_three]
      have hE4 : Nat.card E ≤ 4 := hcardEY ▸ card_elemAbelian_le_four_projectiveSL hp2 hEYe
      have hE2 : IsPGroup 2 E := hP2.to_le hEP
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hE2
      have hEt : 1 < Nat.card E := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro h
        rw [h, Subgroup.mem_bot] at htE
        exact ht1 htE
      have hk' : k = 1 ∨ k = 2 := by
        rcases k with _ | _ | _ | k
        · rw [pow_zero] at hk; omega
        · left; rfl
        · right; rfl
        · rw [hk] at hE4
          have : 2 ^ 3 ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      rcases hk' with rfl | rfl
      ·
        rw [pow_one] at hk
        have hfix : ∀ τ ∈ threeClosureIn (innP K) T, τ * t = t * τ := by
          intro τ hτ
          rcases eq_one_or_eq_of_card_two hk htE ht1 (hEn τ hτ t htE) with h | h
          · exfalso
            apply ht1
            calc t = τ⁻¹ * (τ * t * τ⁻¹) * τ := by group
              _ = 1 := by rw [h]; group
          · calc τ * t = τ * t * τ⁻¹ * τ := by group
              _ = t * τ := by rw [h]
        exact ha1 t (hEI htE) ht2 ht1 (hfix τ₁ hτ₁N) (hfix τ₂ hτ₂N)
      ·
        have hu : (τ₁ * τ₂) ^ p = 1 := by
          rw [hτ₁, hτ₂, ← map_mul, ← map_mul, ← map_pow, ← map_pow]
          have : (tauOne * tauTwo : SL(3, K)) ^ p = 1 := by
            apply Subtype.ext
            rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
              Matrix.SpecialLinearGroup.coe_one]
            change ((mOne : Matrix (Fin 3) (Fin 3) K) * mTwo) ^ p = 1
            rw [mOne_mul_mTwo, uMat_pow_char (by omega)]
          rw [this, map_one, map_one]
        have hEfin : Finite E := Subgroup.instFiniteSubtypeMem E
        have hucomm : ∀ e ∈ E, (τ₁ * τ₂) * e = e * (τ₁ * τ₂) := fun e he =>
          commute_of_normalizes_small (by rw [hk]; norm_num) hp hp4 hu
            (fun e he => hEn _ (Subgroup.mul_mem _ hτ₁N hτ₂N) e he) he
        obtain ⟨e, heE, he1, het⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ t := by
          by_contra h
          push Not at h
          have hsub : ∀ z ∈ E, z = 1 ∨ z = t := fun z hz => by
            by_cases hz1 : z = 1
            · exact Or.inl hz1
            · exact Or.inr (h z hz hz1)
          have : Nat.card E ≤ 2 := by
            classical
            have : Fintype E := Fintype.ofFinite E
            have hs : (Finset.univ : Finset E) ⊆ {⟨1, E.one_mem⟩, ⟨t, htE⟩} := by
              intro z _
              rcases hsub z z.2 with h' | h'
              · simp [Subtype.ext_iff, h']
              · simp [Subtype.ext_iff, h']
            have hc := Finset.card_le_card hs
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
            exact hc.trans Finset.card_le_two
          rw [hk] at this
          norm_num at this
        obtain ⟨⟨y₁, rfl⟩, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mpr ⟨hEI htE, htE⟩)
        obtain ⟨⟨y₂, rfl⟩, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mpr ⟨hEI heE, heE⟩)
        refine not_commute_u_four hp3 hEYe (y₁ := y₁) (y₂ := y₂) htE heE
          (fun h => ht1 (by rw [h, map_one])) (fun h => he1 (by rw [h, map_one]))
          (fun h => het (by rw [h])) ?_ ?_
        · apply conj_injective_three
          simp only [map_mul]
          exact hucomm _ htE
        · apply conj_injective_three
          simp only [map_mul]
          exact hucomm _ heE
    rw [hP1, Subgroup.mem_bot] at hx
    rw [hx, one_mul, mul_one]
  ·
    by_cases hP1 : P = ⊥
    · subst hP1
      exact isCyclic_of_subsingleton
    · exfalso
      obtain ⟨t, htP, ht1, ht2, -⟩ := exists_central_involution hP2 hP1
      have ht := hP htP
      have htI : t ∈ innP K := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1
      have htN := (Subgroup.mem_inf.mp ht).2
      exact ha1 t htI ht2 ht1 (Subgroup.mem_centralizer_iff.mp htN τ₁ hτ₁N)
        (Subgroup.mem_centralizer_iff.mp htN τ₂ hτ₂N)

end TauMain

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
