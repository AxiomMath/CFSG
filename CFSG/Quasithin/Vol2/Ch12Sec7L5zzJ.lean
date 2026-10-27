module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5k
public import CFSG.Quasithin.Vol2.Ch8Sec2KG
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def L34E16Parabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPSL 3 2 2 X →
    ∀ A : Subgroup X, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      Nat.card ↥A = 16 →
      ∃ Q : Subgroup X, A ≤ Q ∧ Nat.card ↥Q = 960 ∧
        Q ≤ Subgroup.normalizer (A : Set X) ∧ pCoreOf 2 Q = A

namespace S127.L34C

variable {K : Type} [Group K]

@[expose] def omegaCenter (K : Type) [Group K] : Subgroup K where
  carrier := {z | z ∈ Subgroup.center K ∧ z ^ 2 = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
    have hab : a * b = b * a := (Subgroup.mem_center_iff.mp ha b).symm
    rw [(Commute.mul_pow hab 2), ha2, hb2, one_mul]
  one_mem' := ⟨Subgroup.one_mem _, one_pow 2⟩
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow, ha2, inv_one]⟩

@[expose] def omegaR (E : Subgroup K) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Subgroup K where
  carrier := {x | (∃ e ∈ E, x * e⁻¹ ∈ Subgroup.center K) ∧ x ^ 2 = 1}
  mul_mem' := by
    rintro x y ⟨⟨ex, hex, hx⟩, hx2⟩ ⟨⟨ey, hey, hy⟩, hy2⟩
    set c := x * ex⁻¹ with hc
    set d := y * ey⁻¹ with hd
    have hxe : x = c * ex := by rw [hc]; group
    have hye : y = d * ey := by rw [hd]; group
    have hcz : ∀ g, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hx g).symm
    have hdz : ∀ g, d * g = g * d := fun g => (Subgroup.mem_center_iff.mp hy g).symm
    have hcomm : Commute x y := by
      rw [hxe, hye]
      exact Commute.mul_left (Commute.mul_right (hcz d) (hcz ey))
        (Commute.mul_right (hdz ex).symm (hEc ex hex ey hey))
    refine ⟨⟨ex * ey, E.mul_mem hex hey, ?_⟩, ?_⟩
    · have e : x * y * (ex * ey)⁻¹ = c * (ex * d * ex⁻¹) := by rw [hxe, hye]; group
      rw [e, ← hdz ex, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ hx hy
    · rw [hcomm.mul_pow 2, hx2, hy2, one_mul]
  one_mem' := ⟨⟨1, E.one_mem, by simp⟩, one_pow 2⟩
  inv_mem' := by
    rintro x ⟨⟨ex, hex, hx⟩, hx2⟩
    refine ⟨⟨ex⁻¹, E.inv_mem hex, ?_⟩, by rw [inv_pow, hx2, inv_one]⟩
    set c := x * ex⁻¹ with hc
    have hxe : x = c * ex := by rw [hc]; group
    have hcz : ∀ g, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hx g).symm
    have e : x⁻¹ * ex⁻¹⁻¹ = ex⁻¹ * c⁻¹ * ex := by rw [hxe]; group
    have hci : c⁻¹ * ex = ex * c⁻¹ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hx) ex).symm
    rw [e, mul_assoc, hci, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.inv_mem _ hx

section Quotient

variable [Finite K]

omit [Finite K] in
theorem center_quot_eq_bot (hKq : CFSG.Open.IsQuasisimple K) :
    Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
  have := hKq.2
  rcases (inferInstance : (Subgroup.center (K ⧸ Subgroup.center K)).Normal).eq_bot_or_eq_top with
    h | h
  · exact h
  · exfalso
    have hle : commutator K ≤ Subgroup.center K := by
      rw [commutator, Subgroup.commutator_le]
      intro g _ k _
      rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      have hc := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (k : K ⧸ Subgroup.center K))
        (g : K ⧸ Subgroup.center K)
      rw [hc]
      group
    rw [hKq.1] at hle
    obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ Subgroup.center K)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [QuotientGroup.eq]
    exact hle (Subgroup.mem_top _)

omit [Finite K] in
theorem center_quotient_eq (hKq : CFSG.Open.IsQuasisimple K) {W : Subgroup K} [W.Normal]
    (hWZ : W ≤ Subgroup.center K) :
    Subgroup.center (K ⧸ W) = (Subgroup.center K).map (QuotientGroup.mk' W) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective W g
    refine ⟨x, ?_, rfl⟩
    have hxZ : (x : K ⧸ Subgroup.center K) ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
      have hk := Subgroup.mem_center_iff.mp hg (QuotientGroup.mk' W k)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hk
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact hWZ hk
    rw [center_quot_eq_bot hKq, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxZ
    exact hxZ
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective W g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]

end Quotient

end S127.L34C

open S127.L34C in
theorem l34CoverFact_of (hKG : KG82CoverL34) (hB : L34E16Parabolic) : L34CoverFact := by
  intro K _ _ hKq hZ hpsl E hEc hE2 hcard z₀ hz₀
  by_contra hne
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center K with hZdef
  have hO1Z : omegaCenter K ≤ Z := fun z hz => hz.1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  have hO1dvd : Nat.card ↥(omegaCenter K) ∣ 2 ^ n := hn ▸ Subgroup.card_dvd_of_le hO1Z
  obtain ⟨j, hjn, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hO1dvd
  have hO1lt : Nat.card ↥(omegaCenter K) < Nat.card ↥Z := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hO1Z) fun h => hne ?_
    have heq := Subgroup.eq_of_le_of_card_ge hO1Z h.ge
    exact (heq ▸ hz₀ : z₀ ∈ omegaCenter K).2
  rw [hj, hn] at hO1lt
  have hjn' : j < n := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hO1lt
  obtain ⟨W, hWc, hO1W, hWZ⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := n - 1) (by rw [hj]; exact Nat.pow_dvd_pow 2 (by omega))
    (by rw [hn]; exact Nat.pow_dvd_pow 2 (by omega)) hO1Z
  have hZW : Nat.card ↥Z = 2 * Nat.card ↥W := by
    rw [hn, hWc, ← pow_succ']
    congr 1
    omega
  have hWn : W.Normal := ⟨fun w hw g => by
    rw [Subgroup.mem_center_iff.mp (hWZ hw) g, mul_inv_cancel_right]
    exact hw⟩
  set φ := QuotientGroup.mk' W with hφ
  have hcen := center_quotient_eq hKq hWZ
  have hmapZ : Nat.card ↥(Z.map φ) * Nat.card ↥W = Nat.card ↥Z := by
    set f : ↥Z →* K ⧸ W := φ.comp Z.subtype with hf
    have hker : f.ker = W.subgroupOf Z := by
      ext x
      simp [hf, hφ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hrange : f.range = Z.map φ := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWZ).toEquiv] at h1
    exact h1.symm
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  have hcardZh : Nat.card ↥(Subgroup.center (K ⧸ W)) = 2 := by
    rw [hcen]
    rw [hZW] at hmapZ
    exact Nat.eq_of_mul_eq_mul_right hWpos hmapZ
  let e : (K ⧸ W) ⧸ Subgroup.center (K ⧸ W) ≃* K ⧸ Z :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient W Z hWZ)
  have hpslh : IsPSL 3 2 2 ((K ⧸ W) ⧸ Subgroup.center (K ⧸ W)) := by
    obtain ⟨hadm, F, _, _, hF, ⟨e'⟩⟩ := hpsl
    exact ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e.trans e'⟩⟩
  have hquasi : CFSG.Open.IsQuasisimple (K ⧸ W) := by
    refine ⟨?_, ?_⟩
    · have h1 : (commutator K).map φ = commutator (K ⧸ W) := by
        rw [commutator, commutator, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective W)]
      rw [← h1, hKq.1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective W)]
    · have := hKq.2
      exact e.isSimpleGroup
  set Eb := E.map (QuotientGroup.mk' Z) with hEb
  have hEbcard : Nat.card ↥Eb = 16 := by
    set f : ↥E →* K ⧸ Z := (QuotientGroup.mk' Z).comp E.subtype with hf
    have hker : f.ker = Z.subgroupOf E := by
      ext x
      simp [hf, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hrange : f.range = Eb := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker] at h1
    have h2 : Nat.card ↥(Z.subgroupOf E) = Nat.card ↥(E ⊓ Z) := by
      rw [← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_comm]
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card ↥(E ⊓ Z) := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  have hEbc : ∀ a ∈ Eb, ∀ b ∈ Eb, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  have hEb2 : ∀ a ∈ Eb, a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE2 a ha, map_one]
  obtain ⟨Q, hEbQ, hQcard, hQN, hQcore⟩ := hB (K ⧸ Z) hpsl Eb hEbc hEb2 hEbcard
  set ψ : K ⧸ W →* K ⧸ Z := QuotientGroup.map W Z (MonoidHom.id K) (fun w hw => hWZ hw)
    with hψ
  have hψφ : ∀ x : K, ψ (φ x) = (x : K ⧸ Z) := fun x => rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨φ x, hψφ x⟩
  set P := Q.comap ψ with hP
  have hcenP : Subgroup.center (K ⧸ W) ≤ P := by
    rw [hcen]
    rintro _ ⟨z, hz, rfl⟩
    show ψ (φ z) ∈ Q
    rw [hψφ, (QuotientGroup.eq_one_iff z).mpr hz]
    exact Q.one_mem
  have hKZ : Nat.card (K ⧸ Z) = 20160 := by
    obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := QA12.exists_equiv_projectiveSL hpsl
    rw [Nat.card_congr e'.toEquiv, RankThree.PartTwo.KFacts.L34.card_projectiveSL hF]
  have hKW : Nat.card (K ⧸ W) = 40320 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup W
    rw [hKZ, hZW] at h1
    rw [h1] at h2
    have h3 : (40320 : ℕ) * Nat.card ↥W = Nat.card (K ⧸ W) * Nat.card ↥W := by
      rw [← h2]
      ring
    exact (Nat.eq_of_mul_eq_mul_right hWpos h3).symm
  have hQi : Q.index = 21 := by
    have h1 := Subgroup.card_mul_index Q
    rw [hQcard, hKZ] at h1
    omega
  have hPcard : Nat.card ↥P = 2 * 960 := by
    have h1 := Subgroup.card_mul_index P
    have h2 : P.index = 21 := by rw [hP, Subgroup.index_comap_of_surjective Q hψs, hQi]
    rw [h2, hKW] at h1
    omega
  have hRP := hKG (K ⧸ W) hquasi hcardZh hpslh P hcenP hPcard
  have hψO : ∀ x ∈ pCoreOf 2 P, ψ x ∈ Eb := by
    rintro _ ⟨p, hp, rfl⟩
    have h1 := map_pCore_le 2 (ψ.subgroupComap Q) (ψ.subgroupComap_surjective Q hψs)
      ⟨p, hp, rfl⟩
    rw [← hQcore]
    exact ⟨_, h1, rfl⟩
  set Vh := (omegaR E hEc).map φ with hVh
  have hcommV : ∀ x ∈ pCoreOf 2 P, ∀ p ∈ P, ⁅x, p⁆ ∈ Vh := by
    intro x hx p hp
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective W x
    obtain ⟨p₀, rfl⟩ := QuotientGroup.mk'_surjective W p
    obtain ⟨e, he, hex⟩ := hψO _ hx
    rw [hψφ] at hex
    have hc : e⁻¹ * x₀ ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hex
    have hpQ : (p₀ : K ⧸ Z) ∈ Q := hp
    have hpN := hQN hpQ
    have hconj : (p₀ * e⁻¹ * p₀⁻¹ : K) ∈ omegaR E hEc := by
      have h1 : ((p₀ * e⁻¹ * p₀⁻¹ : K) : K ⧸ Z) ∈ Eb := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv]
        exact (Subgroup.mem_normalizer_iff.mp hpN _).mp (Eb.inv_mem ⟨e, he, rfl⟩)
      obtain ⟨e', he', he'eq⟩ := h1
      refine ⟨⟨e', he', ?_⟩, ?_⟩
      · have h2 : (p₀ * e⁻¹ * p₀⁻¹)⁻¹ * e' ∈ Z := by
          rw [← QuotientGroup.eq]
          exact he'eq.symm
        set a := p₀ * e⁻¹ * p₀⁻¹ with ha
        have h3 : e'⁻¹ * a ∈ Z := by
          have := Subgroup.inv_mem _ h2
          rwa [mul_inv_rev, inv_inv] at this
        have h4 : a * e'⁻¹ = e'⁻¹ * a := by
          have hcomm := Subgroup.mem_center_iff.mp h3 e'
          calc a * e'⁻¹ = (e' * (e'⁻¹ * a)) * e'⁻¹ := by group
            _ = ((e'⁻¹ * a) * e') * e'⁻¹ := by rw [hcomm]
            _ = e'⁻¹ * a := by group
        rw [h4]
        exact h3
      · have he2' : e * e = 1 := by rw [← pow_two]; exact hE2 e he
        rw [pow_two]
        calc p₀ * e⁻¹ * p₀⁻¹ * (p₀ * e⁻¹ * p₀⁻¹) = p₀ * (e * e)⁻¹ * p₀⁻¹ := by group
          _ = 1 := by rw [he2', inv_one, mul_one, mul_inv_cancel]
    have he1 : e ∈ omegaR E hEc := ⟨⟨e, he, by rw [mul_inv_cancel]; exact Subgroup.one_mem _⟩,
      hE2 e he⟩
    refine ⟨e * (p₀ * e⁻¹ * p₀⁻¹), Subgroup.mul_mem _ he1 hconj, ?_⟩
    set c := e⁻¹ * x₀ with hcdef
    have hx₀ : x₀ = e * c := by rw [hcdef]; group
    have hcz : ∀ g, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hc g).symm
    show φ (e * (p₀ * e⁻¹ * p₀⁻¹)) = ⁅φ x₀, φ p₀⁆
    rw [← map_commutatorElement, commutatorElement_def, hx₀]
    congr 1
    calc e * (p₀ * e⁻¹ * p₀⁻¹) = e * c * p₀ * (e * c)⁻¹ * p₀⁻¹ := by
          rw [mul_inv_rev, mul_assoc e c p₀, hcz p₀]
          group
      _ = _ := rfl
  obtain ⟨z₁, hz₁Z, hz₁W⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hWZ fun h => by
    rw [h] at hZW
    omega)
  have hz₁ : φ z₁ ∈ pCoreOf 2 P := by
    refine le_pCoreOf_of_le_normalizer 2 hcenP ?_ ?_ (hcen ▸ ⟨z₁, hz₁Z, rfl⟩)
    · intro p _
      exact Subgroup.mem_normalizer_fintype fun c hc => (inferInstance :
        (Subgroup.center (K ⧸ W)).Normal).conj_mem c hc p
    · exact IsPGroup.of_card (n := 1) (by rw [hcardZh]; norm_num)
  have hzV : φ z₁ ∈ Vh := by
    rw [← hRP] at hz₁
    exact (Subgroup.commutator_le.mpr hcommV) hz₁
  obtain ⟨v, ⟨⟨ev, hev, hvZ⟩, hv2⟩, hvz⟩ := hzV
  have hvW : v⁻¹ * z₁ ∈ W := by
    rw [← QuotientGroup.eq]
    exact hvz
  have hvZ' : v ∈ Z := by
    have : v = z₁ * (v⁻¹ * z₁)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hz₁Z (Subgroup.inv_mem _ (hWZ hvW))
  have hvW' : v ∈ W := hO1W ⟨hvZ', hv2⟩
  apply hz₁W
  have : z₁ = v * (v⁻¹ * z₁) := by group
  rw [this]
  exact W.mul_mem hvW' hvW

end CFSG.Quasithin.H13
