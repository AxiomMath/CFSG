module

public import Certificates.Certificate14997
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer

public section

namespace CFSG.RankThree.PartOne.SEITZX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits TauCeti CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Bits

variable {K : Type} [Field K] [CharP K 2]

theorem hasBits_pow {g : adjointGroup ReeTag.F4.tag K} {A : ℕ} (h : HasBits K g A) (n : ℕ) :
    HasBits K (g ^ n) (matPowB A n) := by
  induction n with
  | zero => exact hasBits_one
  | succ n ih =>
    rw [pow_succ']
    exact h.mul ih

theorem hasBits_codes (w : List ℕ) : HasBits K (evalG K (wordOfCodes w)) (codeBits w) :=
  hasBits_evalG (wordOfCodes w)

theorem hasBits_prod (c : PlaneCert) : ∀ idxs : List ℕ,
    HasBits K ((idxs.map fun k => evalG K (wordOfCodes (c.gens.getD k ([], 0, 0)).1)).prod)
      (c.prodBits idxs)
  | [] => hasBits_one
  | k :: ks => by
    rw [List.map_cons, List.prod_cons]
    exact (hasBits_codes _).mul (hasBits_prod c ks)

theorem hasBits_elem (c : PlaneCert) (i j : ℕ) :
    HasBits K (evalG K (wordOfCodes c.wa) ^ i * evalG K (wordOfCodes c.wb) ^ j)
      (c.elemBits i j) :=
  (hasBits_pow (hasBits_codes c.wa) i).mul (hasBits_pow (hasBits_codes c.wb) j)

end Bits

section Facts

variable {K : Type} [Field K] [CharP K 2]

theorem PlaneCert.facts (c : PlaneCert) (hc : c.check = true) :
    evalG K (wordOfCodes c.wa) ^ c.p = 1 ∧ evalG K (wordOfCodes c.wb) ^ c.p = 1 ∧
    evalG K (wordOfCodes c.wa) * evalG K (wordOfCodes c.wb) =
      evalG K (wordOfCodes c.wb) * evalG K (wordOfCodes c.wa) ∧
    evalG K (wordOfCodes c.wa) ≠ 1 ∧
    (∀ j < c.p, evalG K (wordOfCodes c.wb) ≠ evalG K (wordOfCodes c.wa) ^ j) ∧
    (∀ g ∈ c.gens,
      evalG K (wordOfCodes c.wa) ^ g.2.1 * evalG K (wordOfCodes c.wb) ^ g.2.2 ≠ 1 ∧
      evalG K (wordOfCodes g.1) *
          (evalG K (wordOfCodes c.wa) ^ g.2.1 * evalG K (wordOfCodes c.wb) ^ g.2.2) =
        (evalG K (wordOfCodes c.wa) ^ g.2.1 * evalG K (wordOfCodes c.wb) ^ g.2.2) *
          evalG K (wordOfCodes g.1)) ∧
    (∀ t < 8, ((c.targets.getD t []).map
      fun k => evalG K (wordOfCodes (c.gens.getD k ([], 0, 0)).1)).prod =
        evalG K (wordOfCodes (targetWord t))) := by
  unfold PlaneCert.check at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  have hA := hasBits_codes (K := K) c.wa
  have hB := hasBits_codes (K := K) c.wb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hasBits_pow hA c.p).eq_iff hasBits_one).2 h1
  · exact ((hasBits_pow hB c.p).eq_iff hasBits_one).2 h2
  · exact ((hA.mul hB).eq_iff (hB.mul hA)).2 h3
  · intro h
    exact h4 ((hA.eq_iff hasBits_one).1 h)
  · intro j hj h
    exact h5 j hj (((hB.eq_iff (hasBits_pow hA j)).1 h).symm)
  · intro g hg
    have hC := hasBits_elem (K := K) c g.2.1 g.2.2
    have hS := hasBits_codes (K := K) g.1
    obtain ⟨h6a, h6b⟩ := h6 g hg
    refine ⟨fun h => h6a ((hC.eq_iff hasBits_one).1 h), ?_⟩
    exact ((hS.mul hC).eq_iff (hC.mul hS)).2 h6b
  · intro t ht
    have hT := hasBits_prod (K := K) c (c.targets.getD t [])
    exact (hT.eq_iff (hasBits_codes (targetWord t))).2 (h7 t ht)

end Facts

section Group

@[expose] def zSet {G : Type*} [Group G] (E : Subgroup G) : Set G :=
  {k | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}

theorem isPGroup_closure_pair {G : Type*} [Group G] {p : ℕ} {A B : G} (hA : A ^ p = 1)
    (hB : B ^ p = 1) (hAB : A * B = B * A) : IsPGroup p (Subgroup.closure ({A, B} : Set G)) := by
  have hcomm : ∀ x ∈ ({A, B} : Set G), ∀ y ∈ ({A, B} : Set G), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hAB
    · exact hAB.symm
    · rfl
  have h1 : Subgroup.closure ({A, B} : Set G) ≤ Subgroup.centralizer ({A, B} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  have h2 : Subgroup.closure ({A, B} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({A, B} : Set G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.1 (h1 hy) x hx
    exact this.symm
  have hpow : ∀ x ∈ Subgroup.closure ({A, B} : Set G), x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hA
      · exact hB
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      have hc : Commute x y := Subgroup.mem_centralizer_iff.1 (h2 hy) x hx
      rw [hc.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro x
  exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hpow x x.2)⟩

theorem card_closure_pair {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {A B : G}
    (hA : A ^ p = 1) (hB : B ^ p = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1)
    (hBA : ∀ j < p, B ≠ A ^ j) (h3 : ¬ p ^ 3 ∣ Nat.card G) :
    Nat.card (Subgroup.closure ({A, B} : Set G)) = p ^ 2 := by
  set E := Subgroup.closure ({A, B} : Set G) with hE
  have hEp : IsPGroup p E := isPGroup_closure_pair hA hB hAB
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hordA : orderOf A = p := orderOf_eq_prime hA hA1
  have hzA : Nat.card (Subgroup.zpowers A) = p := by rw [Nat.card_zpowers, hordA]
  have hAE : A ∈ E := Subgroup.subset_closure (by simp)
  have hBE : B ∈ E := Subgroup.subset_closure (by simp)
  have hzle : Subgroup.zpowers A ≤ E := (Subgroup.zpowers_le).2 hAE
  have hBnot : B ∉ Subgroup.zpowers A := by
    intro hB'
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hB'
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have hnn : 0 ≤ z % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
    have hlt : z % (p : ℤ) < p := Int.emod_lt_of_pos z hp0
    have hpA : A ^ (z % (p : ℤ)).toNat = B := by
      rw [← hz, ← zpow_natCast, Int.toNat_of_nonneg hnn]
      have : z = (p : ℤ) * (z / p) + z % p := (Int.mul_ediv_add_emod z p).symm
      conv_rhs => rw [this, zpow_add, zpow_mul, zpow_natCast, hA, one_zpow, one_mul]
    exact hBA _ (by omega) hpA.symm
  have hdvd : p ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card E
  have hn3 : n < 3 := by
    by_contra h
    exact h3 ((pow_dvd_pow p (not_lt.1 h)).trans hdvd)
  have hpdvd : p ∣ p ^ n := by
    have := Subgroup.card_dvd_of_le hzle
    rwa [hzA, hn] at this
  have hn1 : n ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hpdvd
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 hpdvd)
  have hn2 : n ≠ 1 := by
    rintro rfl
    have := Subgroup.eq_of_le_of_card_ge hzle (by rw [hn, hzA]; simp)
    exact hBnot (this ▸ hBE)
  have : n = 2 := by omega
  rw [hn, this]

theorem exists_conj_eq_of_card_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (h3 : ¬ p ^ 3 ∣ Nat.card G) {E₀ E₁ : Subgroup G} (h0 : Nat.card E₀ = p ^ 2)
    (h1 : Nat.card E₁ = p ^ 2) : ∃ g : G, E₁.map (MulAut.conj g).toMonoidHom = E₀ := by
  have hidx : ∀ E : Subgroup G, Nat.card E = p ^ 2 → ¬ p ∣ E.index := by
    intro E hE hd
    apply h3
    have h := E.card_mul_index
    rw [hE] at h
    rw [← h]
    obtain ⟨m, hm⟩ := hd
    rw [hm]
    exact ⟨m, by ring⟩
  have hp0 : IsPGroup p E₀ := IsPGroup.of_card h0
  have hp1 : IsPGroup p E₁ := IsPGroup.of_card h1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hp1.toSylow (hidx E₁ h1)) (hp0.toSylow (hidx E₀ h0))
  refine ⟨g, ?_⟩
  have := congrArg (fun S : Sylow p G => (S : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
  rw [← this, Subgroup.pointwise_smul_def]
  rfl

theorem closure_zSet_eq_top_of_map {G : Type*} [Group G] {E₀ E₁ : Subgroup G} (g : G)
    (hg : E₁.map (MulAut.conj g).toMonoidHom = E₀) (h : Subgroup.closure (zSet E₀) = ⊤) :
    Subgroup.closure (zSet E₁) = ⊤ := by
  have hsub : zSet E₀ ⊆ (MulAut.conj g).toMonoidHom '' zSet E₁ := by
    rintro k ⟨x, hx, hx1, hk⟩
    rw [← hg] at hx
    obtain ⟨x₁, hx₁, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨g⁻¹ * k * g, ⟨x₁, hx₁, ?_, ?_⟩, ?_⟩
    · rintro rfl
      exact hx1 (map_one _)
    · have hk' : k * (g * x₁ * g⁻¹) = (g * x₁ * g⁻¹) * k := hk
      calc g⁻¹ * k * g * x₁ = g⁻¹ * (k * (g * x₁ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x₁ * g⁻¹) * k) * g := by rw [hk']
        _ = x₁ * (g⁻¹ * k * g) := by group
    · show g * (g⁻¹ * k * g) * g⁻¹ = k
      group
  have hle : (⊤ : Subgroup G) ≤ (Subgroup.closure (zSet E₁)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure, ← h]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro k _
  obtain ⟨c, hc, hck⟩ := hle (Subgroup.mem_top ((MulAut.conj g) k))
  have : c = k := (MulAut.conj g).injective hck
  exact this ▸ hc

end Group

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem xElement_one_mul_self (i : Fin ReeTag.F4.tag.rank) :
    xElement (τ := ReeTag.F4.tag) (K := K) i 1 * xElement i 1 = 1 := by
  rw [← xElement_add, CharTwo.add_self_eq_zero, xElement_zero]

omit [Finite K] in
theorem yElement_one_eq (i : Fin ReeTag.F4.tag.rank) :
    yElement (τ := ReeTag.F4.tag) (K := K) i 1 =
      xElement i 1 * weylElement ReeTag.F4.tag K i * xElement i 1 := by
  have hn : weylElement ReeTag.F4.tag K i =
      xElement (τ := ReeTag.F4.tag) (K := K) i 1 * yElement i 1 * xElement i 1 := by
    have h := ReeTag.weylElementOf_eq (t := ReeTag.F4) (K := K) i 1
    simp only [inv_one, Units.val_one, CharTwo.neg_eq] at h
    exact h
  rw [hn]
  have hx := xElement_one_mul_self (K := K) i
  calc yElement (τ := ReeTag.F4.tag) (K := K) i 1
      = (xElement i 1 * xElement i 1) * yElement i 1 * (xElement i 1 * xElement i 1) := by
        rw [hx]; simp
    _ = xElement i 1 * (xElement i 1 * yElement i 1 * xElement i 1) * xElement i 1 := by group

omit [Finite K] [CharP K 2] in
theorem evalG_targetWord_x (i : Fin 4) :
    evalG K (wordOfCodes (targetWord i.val)) = xElement (idx i) 1 := by
  have h1 : i.val < 4 := i.2
  simp [targetWord, wordOfCodes, letterOfCode, h1, Letter.elt]

omit [Finite K] [CharP K 2] in
theorem evalG_targetWord_y (i : Fin 4) :
    evalG K (wordOfCodes (targetWord (i.val + 4))) =
      xElement (idx i) 1 * weylElement ReeTag.F4.tag K (idx i) * xElement (idx i) 1 := by
  have h1 : i.val < 4 := i.2
  have h2 : ¬ (i.val + 4 < 4) := by omega
  have hF : (⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = i := Fin.ext (Nat.mod_eq_of_lt h1)
  simp [targetWord, wordOfCodes, letterOfCode, h1, h2, Letter.elt, mul_assoc, hF]

theorem PlaneCert.generation (hK : Nat.card K = 2) (c : PlaneCert) (hc : c.check = true)
    [hp : Fact c.p.Prime] (h3 : ¬ c.p ^ 3 ∣ Nat.card (adjointGroup ReeTag.F4.tag K))
    {E₁ : Subgroup (adjointGroup ReeTag.F4.tag K)} (hE₁ : Nat.card E₁ = c.p ^ 2) :
    Subgroup.closure (zSet E₁) = ⊤ := by
  obtain ⟨hAp, hBp, hAB, hA1, hBA, hgens, htargets⟩ := c.facts (K := K) hc
  set A := evalG K (wordOfCodes c.wa) with hAdef
  set B := evalG K (wordOfCodes c.wb) with hBdef
  have hE₀ : Nat.card (Subgroup.closure ({A, B} : Set (adjointGroup ReeTag.F4.tag K))) =
      c.p ^ 2 := card_closure_pair hAp hBp hAB hA1 hBA h3
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq h3 hE₀ hE₁
  refine closure_zSet_eq_top_of_map g hg ?_
  set E₀ := Subgroup.closure ({A, B} : Set (adjointGroup ReeTag.F4.tag K)) with hE₀def
  have hAE : A ∈ E₀ := Subgroup.subset_closure (by simp)
  have hBE : B ∈ E₀ := Subgroup.subset_closure (by simp)
  have hsmem : ∀ k : ℕ, evalG K (wordOfCodes (c.gens.getD k ([], 0, 0)).1) ∈
      Subgroup.closure (zSet E₀) := by
    intro k
    by_cases hk : k < c.gens.length
    · have hmem : c.gens.getD k ([], 0, 0) ∈ c.gens := by
        rw [List.getD_eq_getElem _ _ hk]
        exact List.getElem_mem hk
      obtain ⟨hne, hcomm⟩ := hgens _ hmem
      refine Subgroup.subset_closure ⟨A ^ (c.gens.getD k ([], 0, 0)).2.1 *
        B ^ (c.gens.getD k ([], 0, 0)).2.2, mul_mem (pow_mem hAE _) (pow_mem hBE _), hne, hcomm⟩
    · rw [List.getD_eq_default _ _ (not_lt.1 hk)]
      simp [wordOfCodes]
  have htarg : ∀ t < 8, evalG K (wordOfCodes (targetWord t)) ∈ Subgroup.closure (zSet E₀) := by
    intro t ht
    rw [← htargets t ht]
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact hsmem k
  rw [eq_top_iff, ← closure_xElement_yElement (τ := ReeTag.F4.tag) (K := K), Subgroup.closure_le]
  rintro _ ⟨i, c', rfl | rfl⟩
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [xElement_zero]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg i.val (by omega)
      rwa [show targetWord i.val = targetWord (⟨i.val, hi⟩ : Fin 4).val from rfl,
        evalG_targetWord_x (K := K) ⟨i.val, hi⟩] at this
  · rcases eq_zero_or_eq_one_of_card_eq_two hK c' with rfl | rfl
    · rw [show yElement (τ := ReeTag.F4.tag) (K := K) i 0 = 1 from
        Subtype.ext (Units.ext (yOp_zero i))]
      exact one_mem _
    · have hi : i.val < 4 := i.2
      have := htarg (i.val + 4) (by omega)
      rw [show targetWord (i.val + 4) = targetWord ((⟨i.val, hi⟩ : Fin 4).val + 4) from rfl,
        evalG_targetWord_y (K := K) ⟨i.val, hi⟩] at this
      rw [yElement_one_eq]
      exact this

end Main

section Models

theorem exists_adjointF4_two_model {q : TauCeti.PrimePower} (hq : q.p = 2) (he : q.exponent = 1)
    {K : Type} [Group K] (hiso : IsoLie K (.F4 q)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X), Nat.card X = 2 ∧
      Nonempty (K ≃* adjointGroup ReeTag.F4.tag X) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e0
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hmodel
  rw [hq, he] at hX
  exact ⟨X, inferInstance, inferInstance, by simpa using hX, ⟨e⟩⟩

theorem prime_eq_five_or_seven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 3311126603366400) : p = 5 ∨ p = 7 := by
  have hN : (3311126603366400 : ℕ) = 2 ^ 24 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 := by norm_num
  have hpd : p ∣ 3311126603366400 := (dvd_pow_self p two_ne_zero).trans h
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hd
  rw [hN] at hpd h
  simp only [Nat.Prime.dvd_mul hp] at hpd
  rcases hpd with (((((h1 | h1) | h1) | h1) | h1) | h1)
  · have := key 2 Nat.prime_two (hp.dvd_of_dvd_pow h1); omega
  · have := key 3 Nat.prime_three (hp.dvd_of_dvd_pow h1); omega
  · exact Or.inl (key 5 Nat.prime_five (hp.dvd_of_dvd_pow h1))
  · exact Or.inr (key 7 (by norm_num) (hp.dvd_of_dvd_pow h1))
  · have := key 13 (by norm_num) h1; subst this; norm_num at h
  · have := key 17 (by norm_num) h1; subst this; norm_num at h

theorem extSeitzAtInner_F4_two :
    ∀ q : TauCeti.PrimePower, q.p = 2 → q.exponent = 1 → ExtSeitzAtInner (.F4 q) := by
  intro q hq he K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := exists_adjointF4_two_model hq he hiso
  have : CharP X 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hX)
  have hG : Nat.card (adjointGroup ReeTag.F4.tag X) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := X)
    rw [hX] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have hp2N : p ^ 2 ∣ 3311126603366400 := by
    rw [← hG, ← hcard₁]
    exact Subgroup.card_subgroup_dvd_card E₁
  have hc := (Certificates.certificate14997 : cert5.check = true ∧ cert7.check = true)
  rcases prime_eq_five_or_seven hp hp5 hp2N with rfl | rfl
  · have : Fact (Nat.Prime cert5.p) := ⟨by show Nat.Prime 5; norm_num⟩
    exact PlaneCert.generation hX cert5 hc.1 (by rw [hG]; decide) hcard₁
  · have : Fact (Nat.Prime cert7.p) := ⟨by show Nat.Prime 7; norm_num⟩
    exact PlaneCert.generation hX cert7 hc.2 (by rw [hG]; decide) hcard₁

end Models

end CFSG.RankThree.PartOne.SEITZX
