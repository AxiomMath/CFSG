module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Skeleton
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Heis

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

section Criteria

variable {G : Type*} [Group G]

@[expose] def Heis1412 (a b : G) : Prop :=
  IsPGroup 5 (Subgroup.closure ({a, b} : Set G)) ∧ b ^ 5 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1 ∧
    Commute (a * b * a⁻¹ * b⁻¹) a ∧ Commute (a * b * a⁻¹ * b⁻¹) b

@[expose] def Excl1412 (α : MulAut G) : Prop :=
  (∃ (x : G) (q k : ℕ), q.Prime ∧ q ≠ 2 ∧ 1 ≤ k ∧ (∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1) ∧
    q ^ k ∣ orderOf (α x * x⁻¹)) ∨
  (∃ (x₁ x₂ w : G) (q k : ℕ), q.Prime ∧ q ≠ 2 ∧ 1 ≤ k ∧
    (∀ e : ℕ, 1 ≤ e → e ≤ 12 → ¬ q ^ k ∣ 2 ^ e - 1) ∧
    w ∈ Subgroup.closure ({α x₁ * x₁⁻¹, α x₂ * x₂⁻¹} : Set G) ∧ q ^ k ∣ orderOf w) ∨
  (∃ x₁ x₂ c d : G, c ∈ Subgroup.closure ({α x₁ * x₁⁻¹, α x₂ * x₂⁻¹} : Set G) ∧
    d ∈ Subgroup.closure ({α x₁ * x₁⁻¹, α x₂ * x₂⁻¹} : Set G) ∧ Heis1412 c d)

theorem Heis1412.map_equiv {H : Type*} [Group H] (e : G ≃* H) {a b : G}
    (hab : Heis1412 (e a) (e b)) : Heis1412 a b := by
  obtain ⟨h5, hb, hz, hza, hzb⟩ := hab
  have hmap : (Subgroup.closure ({a, b} : Set G)).map e.toMonoidHom =
      Subgroup.closure ({e a, e b} : Set H) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hiso : Subgroup.closure ({a, b} : Set G) ≃* Subgroup.closure ({e a, e b} : Set H) :=
    ((Subgroup.closure ({a, b} : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  refine ⟨h5.of_equiv hiso.symm, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, hb, map_one]
  · intro h1
    apply hz
    simp only [← map_mul, ← map_inv, h1, map_one]
  · apply e.injective
    have := hza.eq
    simp only [map_mul, map_inv] at this ⊢
    exact this
  · apply e.injective
    have := hzb.eq
    simp only [map_mul, map_inv] at this ⊢
    exact this

theorem Excl1412.of_congr {H : Type*} [Group H] (e : G ≃* H) {α : MulAut G}
    (hα : Excl1412 (MulAut.congr e α)) : Excl1412 α := by
  have he : ∀ y : H, MulAut.congr e α y * y⁻¹ = e (α (e.symm y) * (e.symm y)⁻¹) := fun y => by
    simp [MulAut.congr_apply]
  have hmap : ∀ y₁ y₂ : H, (Subgroup.closure ({α (e.symm y₁) * (e.symm y₁)⁻¹,
      α (e.symm y₂) * (e.symm y₂)⁻¹} : Set G)).map e.toMonoidHom =
      Subgroup.closure ({MulAut.congr e α y₁ * y₁⁻¹, MulAut.congr e α y₂ * y₂⁻¹} : Set H) := by
    intro y₁ y₂
    rw [MonoidHom.map_closure, Set.image_pair, he, he]
    rfl
  have hmem : ∀ (y₁ y₂ w : H), w ∈ Subgroup.closure ({MulAut.congr e α y₁ * y₁⁻¹,
      MulAut.congr e α y₂ * y₂⁻¹} : Set H) → e.symm w ∈ Subgroup.closure
        ({α (e.symm y₁) * (e.symm y₁)⁻¹, α (e.symm y₂) * (e.symm y₂)⁻¹} : Set G) := by
    intro y₁ y₂ w hw
    rw [← hmap] at hw
    obtain ⟨w', hw', hw'e⟩ := hw
    have : w' = e.symm w := by
      rw [← hw'e]
      simp
    rwa [← this]
  rcases hα with ⟨y, q, k, hq, hq2, hk, h8, hy⟩ | ⟨y₁, y₂, w, q, k, hq, hq2, hk, h12, hw, hy⟩ |
    ⟨y₁, y₂, c, d, hc, hd, hy⟩
  · refine Or.inl ⟨e.symm y, q, k, hq, hq2, hk, h8, ?_⟩
    rwa [he, MulEquiv.orderOf_eq] at hy
  · refine Or.inr (Or.inl ⟨e.symm y₁, e.symm y₂, e.symm w, q, k, hq, hq2, hk, h12,
      hmem y₁ y₂ w hw, ?_⟩)
    rwa [MulEquiv.orderOf_eq]
  · refine Or.inr (Or.inr ⟨e.symm y₁, e.symm y₂, e.symm c, e.symm d, hmem y₁ y₂ c hc,
      hmem y₁ y₂ d hd, ?_⟩)
    refine Heis1412.map_equiv e ?_
    simpa using hy

theorem Excl1412.conj (β : MulAut G) {α : MulAut G} (hα : Excl1412 α) :
    Excl1412 (β * α * β⁻¹) := by
  refine Excl1412.of_congr (β⁻¹ : MulAut G) ?_
  have e : MulAut.congr (β⁻¹ : MulAut G) (β * α * β⁻¹) = α := by
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  rw [e]
  exact hα

end Criteria

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem relIndex_centralizer_conj1412 {I : Subgroup X} (hI : I.Normal) (g x : X) :
    (centralizer ({g * x * g⁻¹} : Set X)).relIndex I =
      (centralizer ({x} : Set X)).relIndex I := by
  have hcomap : (centralizer ({g * x * g⁻¹} : Set X)).comap
      (MulAut.conj g).toMonoidHom = centralizer ({x} : Set X) := by
    ext y
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := hy.symm
          _ = g * (y * x) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    · intro hy
      calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hy]
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  rw [← hcomap, Subgroup.relIndex_comap]
  congr 1
  exact (Subgroup.normal_iff_map_conj_eq.mp hI g).symm

private theorem le_of_two_pow_le_prod_sixteen {d e : ℕ} (h : 2 ^ e ≤ ∏ _i : Fin d, (16 : ℕ)) :
    e ≤ 4 * d := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

private theorem false_of_excl1412_two (h : Hyp1411 X L S) {π : X →* X ⧸ CFSG.pPrimeCore 3 X}
    (hπ : π = QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) (hsimp : IsSimpleGroup ↥(L.map π))
    {I : Subgroup X} (hIn : I.Normal) (hI : Sec3.IsElemTwo I)
    (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) {t : X} (htt : t * t = 1)
    (hle : (centralizer ({t} : Set X)).relIndex I ≤ 16) [(L.map π).Normal]
    {x : ↥(L.map π)} {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk : 1 ≤ k)
    (h8 : ∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1)
    (hx : q ^ k ∣ orderOf (MulAut.conjNormal (π t) x * x⁻¹)) : False := by
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hbot : (centralizer (I : Set X)).map π ⊓ L.map π = ⊥ := by
    subst hπ
    exact map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  obtain ⟨ℓ, -, hℓ⟩ := x.2
  set u : Fin 2 → X := ![t, ℓ * t⁻¹ * ℓ⁻¹] with hu
  have hun : ∀ i, u i ∈ normalizer (I : Set X) := fun i => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hu16 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 16 := by
    intro i
    fin_cases i
    · exact hle
    · change (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 16
      rw [htinv, relIndex_centralizer_conj1412 hIn]
      exact hle
  set y : X := t * (ℓ * t⁻¹ * ℓ⁻¹) with hy
  have hymem : y ∈ closure (Set.range u) :=
    mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩)
  obtain ⟨N, -, hpow, hN⟩ :=
    exists_pow_mem_centralizer_closure_prime_pow hI u hun (fun _ => 16) hu16 hymem
  have himg : π y = ((ψ x * x⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ, hy,
      map_mul, map_inv]
    group
  have h1 : (ψ x * x⁻¹) ^ (2 * N) = 1 := by
    apply Subtype.ext
    have hmem : ((((ψ x * x⁻¹) ^ (2 * N) : ↥(L.map π))) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : q ^ k ∣ N * 2 := by
    rw [mul_comm]
    exact hx.trans (orderOf_dvd_of_pow_eq_one h1)
  have hcop : Nat.Coprime (q ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  obtain ⟨e, he1, he, hediv⟩ := hN q k hq hq2 hk (hcop.dvd_of_dvd_mul_right hdvd)
  exact h8 e he1 (by simpa using le_of_two_pow_le_prod_sixteen he) hediv

private theorem map_closure_three1412 {π : X →* X ⧸ CFSG.pPrimeCore 3 X} [(L.map π).Normal]
    {t : X} {x₁ x₂ : ↥(L.map π)} {ℓ₁ ℓ₂ : X} (hℓ₁ : π ℓ₁ = x₁) (hℓ₂ : π ℓ₂ = x₂) :
    (closure ({t * (ℓ₁ * t⁻¹ * ℓ₁⁻¹), t * (ℓ₂ * t⁻¹ * ℓ₂⁻¹)} : Set X)).map π =
      (closure ({MulAut.conjNormal (π t) x₁ * x₁⁻¹, MulAut.conjNormal (π t) x₂ * x₂⁻¹} :
        Set ↥(L.map π))).map (L.map π).subtype := by
  have himg : ∀ (ℓ : X) (x : ↥(L.map π)), π ℓ = x →
      π (t * (ℓ * t⁻¹ * ℓ⁻¹)) = ((MulAut.conjNormal (π t) x * x⁻¹ : ↥(L.map π)) :
        X ⧸ CFSG.pPrimeCore 3 X) := by
    intro ℓ x hℓ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, ← hℓ, map_mul,
      map_inv]
    group
  rw [MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair,
    himg ℓ₁ x₁ hℓ₁, himg ℓ₂ x₂ hℓ₂]
  rfl

private theorem false_of_excl1412_three (h : Hyp1411 X L S) {π : X →* X ⧸ CFSG.pPrimeCore 3 X}
    (hπ : π = QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) (hsimp : IsSimpleGroup ↥(L.map π))
    {I : Subgroup X} (hIn : I.Normal) (hI : Sec3.IsElemTwo I)
    (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) {t : X} (htt : t * t = 1)
    (hle : (centralizer ({t} : Set X)).relIndex I ≤ 16) [(L.map π).Normal]
    {x₁ x₂ w : ↥(L.map π)} {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk : 1 ≤ k)
    (h12 : ∀ e : ℕ, 1 ≤ e → e ≤ 12 → ¬ q ^ k ∣ 2 ^ e - 1)
    (hw : w ∈ closure ({MulAut.conjNormal (π t) x₁ * x₁⁻¹, MulAut.conjNormal (π t) x₂ * x₂⁻¹} :
      Set ↥(L.map π)))
    (hx : q ^ k ∣ orderOf w) : False := by
  have hbot : (centralizer (I : Set X)).map π ⊓ L.map π = ⊥ := by
    subst hπ
    exact map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  obtain ⟨ℓ₁, -, hℓ₁⟩ := x₁.2
  obtain ⟨ℓ₂, -, hℓ₂⟩ := x₂.2
  set u : Fin 3 → X := ![t, ℓ₁ * t⁻¹ * ℓ₁⁻¹, ℓ₂ * t⁻¹ * ℓ₂⁻¹] with hu
  have hun : ∀ i, u i ∈ normalizer (I : Set X) := fun i => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc' : ∀ ℓ : X, (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 16 := fun ℓ => by
    rw [htinv, relIndex_centralizer_conj1412 hIn]
    exact hle
  have hu16 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 16 := by
    intro i
    fin_cases i
    · exact hle
    · exact hc' ℓ₁
    · exact hc' ℓ₂
  set D₀ : Subgroup X := closure ({t * (ℓ₁ * t⁻¹ * ℓ₁⁻¹), t * (ℓ₂ * t⁻¹ * ℓ₂⁻¹)} : Set X)
    with hD₀
  have hD₀u : D₀ ≤ closure (Set.range u) := by
    rw [hD₀, closure_le]
    rintro _ (rfl | rfl)
    · exact mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩)
    · exact mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨2, rfl⟩)
  have hwD : (w : X ⧸ CFSG.pPrimeCore 3 X) ∈ D₀.map π := by
    rw [map_closure_three1412 hℓ₁ hℓ₂]
    exact ⟨w, hw, rfl⟩
  obtain ⟨y, hyD, hyw⟩ := hwD
  obtain ⟨N, -, hpow, hN⟩ :=
    exists_pow_mem_centralizer_closure_prime_pow hI u hun (fun _ => 16) hu16 (hD₀u hyD)
  have h1 : w ^ (2 * N) = 1 := by
    apply Subtype.ext
    have hmem : (((w ^ (2 * N) : ↥(L.map π))) : X ⧸ CFSG.pPrimeCore 3 X) ∈
        (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, hyw, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : q ^ k ∣ N * 2 := by
    rw [mul_comm]
    exact hx.trans (orderOf_dvd_of_pow_eq_one h1)
  have hcop : Nat.Coprime (q ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  obtain ⟨e, he1, he, hediv⟩ := hN q k hq hq2 hk (hcop.dvd_of_dvd_mul_right hdvd)
  exact h12 e he1 (by simpa using le_of_two_pow_le_prod_sixteen he) hediv

private theorem false_of_excl1412_heis (h : Hyp1411 X L S)
    (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {π : X →* X ⧸ CFSG.pPrimeCore 3 X}
    (hπ : π = QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) (hsimp : IsSimpleGroup ↥(L.map π))
    {I : Subgroup X} (hIn : I.Normal) (hI : Sec3.IsElemTwo I)
    (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) {t : X} (htt : t * t = 1)
    (hle : (centralizer ({t} : Set X)).relIndex I ≤ 16) [(L.map π).Normal]
    {x₁ x₂ c d : ↥(L.map π)}
    (hc : c ∈ closure ({MulAut.conjNormal (π t) x₁ * x₁⁻¹, MulAut.conjNormal (π t) x₂ * x₂⁻¹} :
      Set ↥(L.map π)))
    (hd : d ∈ closure ({MulAut.conjNormal (π t) x₁ * x₁⁻¹, MulAut.conjNormal (π t) x₂ * x₂⁻¹} :
      Set ↥(L.map π)))
    (hx : Heis1412 c d) : False := by
  have hbot : (centralizer (I : Set X)).map π ⊓ L.map π = ⊥ := by
    subst hπ
    exact map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  have hker : π.ker = CFSG.pCore 2 X := by
    rw [hπ, QuotientGroup.ker_mk', hK]
  obtain ⟨ℓ₁, -, hℓ₁⟩ := x₁.2
  obtain ⟨ℓ₂, -, hℓ₂⟩ := x₂.2
  set u : Fin 3 → X := ![t, ℓ₁ * t⁻¹ * ℓ₁⁻¹, ℓ₂ * t⁻¹ * ℓ₂⁻¹] with hu
  have hun : ∀ i, u i ∈ normalizer (I : Set X) := fun i => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc' : ∀ ℓ : X, (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 16 := fun ℓ => by
    rw [htinv, relIndex_centralizer_conj1412 hIn]
    exact hle
  have hu16 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 16 := by
    intro i
    fin_cases i
    · exact hle
    · exact hc' ℓ₁
    · exact hc' ℓ₂
  obtain ⟨U, hUI, hUcard, hUy⟩ := exists_subgroup_normalized_closure hI u hun (fun _ => 16) hu16
  have hU12 : Nat.card U ≤ 2 ^ 12 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hUcard
    exact hUcard.trans (by norm_num)
  have hU2 : IsPGroup 2 U := fun g =>
    ⟨1, Subtype.ext (by simpa [pow_two] using hI.2 _ (hUI g.2))⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU2
  have hk12 : k ≤ 12 := by
    rw [hk] at hU12
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hU12
  set D₀ : Subgroup X := closure ({t * (ℓ₁ * t⁻¹ * ℓ₁⁻¹), t * (ℓ₂ * t⁻¹ * ℓ₂⁻¹)} : Set X)
    with hD₀
  have hD₀u : D₀ ≤ closure (Set.range u) := by
    rw [hD₀, closure_le]
    rintro _ (rfl | rfl)
    · exact mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩)
    · exact mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨2, rfl⟩)
  have hmapD := map_closure_three1412 (t := t) hℓ₁ hℓ₂
  rw [← hD₀] at hmapD
  obtain ⟨h5, hd5, hz1, hza, hzb⟩ := hx
  set C : Subgroup (X ⧸ CFSG.pPrimeCore 3 X) :=
    (closure ({c, d} : Set ↥(L.map π))).map (L.map π).subtype with hCdef
  have hC5 : IsPGroup 5 C := h5.map _
  have hCD : C ≤ D₀.map π := by
    rw [hmapD, hCdef]
    refine map_mono ((Subgroup.closure_le _).mpr ?_)
    rintro _ (rfl | rfl)
    · exact hc
    · exact hd
  set D₂ : Subgroup X := D₀ ⊓ C.comap π with hD₂
  have hD₂map : D₂.map π = C := by
    refine le_antisymm ((map_mono inf_le_right).trans (map_comap_le _ _)) fun y hy => ?_
    obtain ⟨z, hzD, hzy⟩ := hCD hy
    exact ⟨z, ⟨hzD, show π z ∈ C by rw [hzy]; exact hy⟩, hzy⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P'⟩ : Nonempty (Sylow 5 ↥D₂) := inferInstance
  set P : Subgroup X := (P' : Subgroup ↥D₂).map D₂.subtype with hPdef
  have hPD₂ : P ≤ D₂ := map_subtype_le _
  have hP5 : IsPGroup 5 P := P'.isPGroup'.map _
  have hPinj : ∀ y ∈ P, π y = 1 → y = 1 := by
    intro y hy hy1
    have hyQ : y ∈ CFSG.pCore 2 X := by rw [← hker]; exact hy1
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨y, hyQ⟩
    obtain ⟨m, hm⟩ := hP5 ⟨y, hy⟩
    have hn' : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hm' : y ^ 5 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcop : Nat.Coprime (2 ^ n) (5 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
    have h1 : orderOf y = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn')
        (orderOf_dvd_of_pow_eq_one hm')
    exact orderOf_eq_one_iff.mp h1
  have hPinj' : ∀ y ∈ P, ∀ z ∈ P, π y = π z → y = z := by
    intro y hy z hz hyz
    have := hPinj (y⁻¹ * z) (mul_mem (inv_mem hy) hz) (by rw [map_mul, map_inv, hyz,
      inv_mul_cancel])
    calc y = y * (y⁻¹ * z) := by rw [this, mul_one]
      _ = z := by group
  have hPC : P.map π = C := by
    have hle : P.map π ≤ C := (map_mono hPD₂).trans hD₂map.le
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hcardP : Nat.card (P.map π) = Nat.card P := by
      refine Nat.card_congr (Equiv.ofBijective (fun y : P => (⟨π y, y, y.2, rfl⟩ : P.map π))
        ⟨fun y z hyz => Subtype.ext (hPinj' y y.2 z z.2 (congrArg Subtype.val hyz)), ?_⟩).symm
      rintro ⟨_, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    have hcardP' : Nat.card P = 5 ^ (Nat.card ↥D₂).factorization 5 := by
      rw [hPdef, Subgroup.card_map_of_injective D₂.subtype_injective]
      exact P'.card_eq_multiplicity
    set f : ↥D₂ →* X ⧸ CFSG.pPrimeCore 3 X := π.comp D₂.subtype with hf
    have hfrange : f.range = C := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hD₂map]
    have hD₂card : Nat.card ↥D₂ = Nat.card f.ker * Nat.card f.range := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have hker2 : IsPGroup 2 f.ker := by
      rintro ⟨y, hy⟩
      have hyQ : (y : X) ∈ CFSG.pCore 2 X := by
        rw [← hker]
        exact hy
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨_, hyQ⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hn
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hker2
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hC5
    have hfac : (Nat.card ↥D₂).factorization 5 = m := by
      rw [hD₂card, hn, hfrange, hm, Nat.factorization_mul (by positivity) (by positivity),
        Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_five]
      simp
    rw [hcardP, hcardP', hfac, hm]
  have hcC : ((c : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) ∈ C :=
    ⟨c, subset_closure (Set.mem_insert _ _), rfl⟩
  have hdC : ((d : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) ∈ C :=
    ⟨d, subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)), rfl⟩
  rw [← hPC] at hcC hdC
  obtain ⟨ch, hchP, hch⟩ := hcC
  obtain ⟨dh, hdhP, hdh⟩ := hdC
  have hzP : ch * dh * ch⁻¹ * dh⁻¹ ∈ P :=
    mul_mem (mul_mem (mul_mem hchP hdhP) (inv_mem hchP)) (inv_mem hdhP)
  have hzπ : π (ch * dh * ch⁻¹ * dh⁻¹) = ((c * d * c⁻¹ * d⁻¹ : ↥(L.map π)) :
      X ⧸ CFSG.pPrimeCore 3 X) := by
    simp only [map_mul, map_inv, hch, hdh, Subgroup.coe_mul, Subgroup.coe_inv]
  have hPN : P ≤ normalizer (U : Set X) := fun y hy =>
    (hUy y (hD₀u (hPD₂ hy).1)).2.1
  set τ : P →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hPN) with hτ
  have hτinj : ∀ y : P, τ y = 1 → y = 1 := by
    intro y hy
    have hyU : ∀ w ∈ U, (y : X) * w * (y : X)⁻¹ = w := by
      intro w hw
      have e := congrArg (fun σ : MulAut U => ((σ ⟨w, hw⟩ : U) : X)) hy
      simp only [hτ, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at e
      exact e
    obtain ⟨hyI, -, hyC⟩ := hUy y (hD₀u (hPD₂ y.2).1)
    have hsq := sq_mem_centralizer_of_centralizes hI hUI hyI hyC hyU
    have hyL : π (y : X) ∈ L.map π := by
      have := hD₂map ▸ mem_map_of_mem π (hPD₂ y.2)
      exact (map_subtype_le _) this
    have hmem : π (y : X) ^ 2 ∈ (centralizer (I : Set X)).map π ⊓ L.map π :=
      ⟨⟨_, hsq, map_pow _ _ _⟩, pow_mem hyL 2⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    obtain ⟨n, hn⟩ := hP5 y
    have hn' : π (y : X) ^ 5 ^ n = 1 := by
      have := congrArg (fun z : P => π (z : X)) hn
      simpa using this
    have hcop : Nat.Coprime 2 (5 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    have h1 : orderOf (π (y : X)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hmem)
        (orderOf_dvd_of_pow_eq_one hn')
    exact Subtype.ext (hPinj y y.2 (orderOf_eq_one_iff.mp h1))
  have hτinj' : ∀ y z : P, τ y = τ z → y = z := by
    intro y z hyz
    have := hτinj (y⁻¹ * z) (by rw [map_mul, map_inv, hyz, inv_mul_cancel])
    calc y = y * (y⁻¹ * z) := by rw [this, mul_one]
      _ = z := by group
  have : Finite (MulAut U) := Finite.of_injective (fun σ : MulAut U => (σ : U → U))
    fun σ σ' hσσ' => MulEquiv.ext (congrFun hσσ')
  have hd5X : dh ^ 5 = 1 :=
    hPinj' _ (pow_mem hdhP 5) _ (one_mem _) (by
      rw [map_pow, hdh, map_one, ← Subgroup.coe_pow, hd5, Subgroup.coe_one])
  have hzX : ch * dh * ch⁻¹ * dh⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    apply Subtype.ext
    rw [← hzπ, h1, map_one, Subgroup.coe_one]
  have hzaX : ch * dh * ch⁻¹ * dh⁻¹ * ch = ch * (ch * dh * ch⁻¹ * dh⁻¹) := by
    refine hPinj' _ (mul_mem hzP hchP) _ (mul_mem hchP hzP) ?_
    have := congrArg Subtype.val hza.eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    simp only [map_mul, map_inv, hch, hdh]
    exact this
  have hzbX : ch * dh * ch⁻¹ * dh⁻¹ * dh = dh * (ch * dh * ch⁻¹ * dh⁻¹) := by
    refine hPinj' _ (mul_mem hzP hdhP) _ (mul_mem hdhP hzP) ?_
    have := congrArg Subtype.val hzb.eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    simp only [map_mul, map_inv, hch, hdh]
    exact this
  set chP : P := ⟨ch, hchP⟩ with hchPdef
  set dhP : P := ⟨dh, hdhP⟩ with hdhPdef
  have hdP5 : dhP ^ 5 = 1 := Subtype.ext (by simpa [hdhPdef] using hd5X)
  have hzP1 : chP * dhP * chP⁻¹ * dhP⁻¹ ≠ 1 := fun h1 =>
    hzX (by simpa [hchPdef, hdhPdef] using congrArg Subtype.val h1)
  have hzPa : Commute (chP * dhP * chP⁻¹ * dhP⁻¹) chP :=
    Subtype.ext (by simpa [hchPdef, hdhPdef] using hzaX)
  have hzPb : Commute (chP * dhP * chP⁻¹ * dhP⁻¹) dhP :=
    Subtype.ext (by simpa [hchPdef, hdhPdef] using hzbX)
  refine false_of_heisenberg_five_mulAut (U := U) hk hk12 (a := τ chP) (b := τ dhP) ?_ ?_ ?_ ?_
  · rw [← map_pow, hdP5, map_one]
  · intro h1
    apply hzP1
    apply hτinj
    simpa only [map_mul, map_inv] using h1
  · simpa only [map_mul, map_inv] using hzPa.map τ
  · simpa only [map_mul, map_inv] using hzPb.map τ

theorem noSmall1412_of_forall_excl (h : Hyp1411 X L S)
    (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X)
    (hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥)
    (hE : ∀ α : MulAut ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))), orderOf α = 2 →
      Excl1412 α) :
    NoSmall1412 X L S := by
  intro I hIn hI hLI t htS htQ htt
  by_contra hle
  push Not at hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hψ2 : ψ * ψ = 1 := by
    rw [hψ, ← map_mul, ← map_mul, htt, map_one, map_one]
  have hψ1 : ψ ≠ 1 := by
    obtain ⟨l, hl, hne⟩ := exists_not_commute_of_hyp1411 h hZ htS htQ
    intro h1
    apply hne
    have e1 := congrArg (fun f : MulAut ↥(L.map π) =>
      ((f ⟨π l, mem_map_of_mem _ hl⟩ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X)) h1
    simp only [hψ, MulAut.conjNormal_apply, MulAut.one_apply] at e1
    calc π t * π l = π t * π l * (π t)⁻¹ * π t := by group
      _ = π l * π t := by rw [e1]
  have hord : orderOf ψ = 2 := orderOf_eq_prime (by rw [sq]; exact hψ2) hψ1
  rcases hE ψ hord with ⟨x, q, k, hq, hq2, hk, h8, hx⟩ |
    ⟨x₁, x₂, w, q, k, hq, hq2, hk, h12, hw, hx⟩ | ⟨x₁, x₂, c, d, hc, hd, hx⟩
  · exact false_of_excl1412_two h hπ hsimp hIn hI hLI htt hle hq hq2 hk h8 hx
  · exact false_of_excl1412_three h hπ hsimp hIn hI hLI htt hle hq hq2 hk h12 hw hx
  · exact false_of_excl1412_heis h hK hπ hsimp hIn hI hLI htt hle hc hd hx

end CFSG.RankThree.PartTwo.Sec20
