module

public import CFSG.Quasithin.EmptyFaithful.T1531In66a
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.Quasithin.T1531O4
open CFSG.LieType.BorelTits

section Helpers

theorem perm_three_key : ∀ g : Equiv.Perm (Fin 3), g ^ 2 = 1 →
    (∀ c : Equiv.Perm (Fin 3), (g * (c * g * c⁻¹)) ^ 2 = 1) → g = 1 := by
  decide +kernel

theorem mulAut_key {E : Type*} [Group E] [IsKleinFour E] (σ : MulAut E) (h1 : σ ^ 2 = 1)
    (h2 : ∀ τ : MulAut E, (σ * (τ * σ * τ⁻¹)) ^ 2 = 1) : σ = 1 := by
  let e := CFSG.kleinFourAutomorphismEquivSymmetricThree E
  have h := perm_three_key (e σ) (by rw [← map_pow, h1, map_one]) (fun c => by
    obtain ⟨τ, rfl⟩ := e.surjective c
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, h2 τ, map_one])
  exact e.injective (by rw [h, map_one])

theorem sq_eq_one_of_pow {E : Type*} [Group E] [IsKleinFour E] {σ : MulAut E} {n : ℕ}
    (h : σ ^ 2 ^ n = 1) : σ ^ 2 = 1 := by
  have h6 : orderOf σ ∣ 2 * 3 := by
    have := orderOf_dvd_natCard σ
    rw [CFSG.kleinFour_automorphism_card] at this
    simpa using this
  have hn : orderOf σ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  have hcop : Nat.Coprime (orderOf σ) 3 :=
    Nat.Coprime.coprime_dvd_left hn (Nat.Coprime.pow_left n (by norm_num))
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h6)

theorem dvd_card_of_mem {α : Type*} [Group α] {A : Subgroup α} {a : α} (ha : a ∈ A) :
    orderOf a ∣ Nat.card A := by
  have := orderOf_dvd_natCard (⟨a, ha⟩ : A)
  rwa [Subgroup.orderOf_mk] at this

variable {G : Type*} [Group G]

theorem conjAct_apply_coe''' (W : Subgroup G) (g : Subgroup.normalizer (W : Set G)) (w : W) :
    ((conjAct W g w : W) : G) = g * w * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply W g w

theorem conjAct_eq_one_iff''' (W : Subgroup G) (x : Subgroup.normalizer (W : Set G)) :
    conjAct W x = 1 ↔ (x : G) ∈ Subgroup.centralizer (W : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff x

theorem mem_autOn_iff''' {X V : Subgroup G} {a : MulAut V} :
    a ∈ autOn X V ↔ ∃ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ X ∧
      conjAct V ⟨x, hx⟩ = a :=
  CFSG.Quasithin.AutOn.mem_autOn_iff_exists

theorem conjAct_mem_autOn {X V : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hxX : x ∈ X) : conjAct V ⟨x, hx⟩ ∈ autOn X V :=
  mem_autOn_iff'''.mpr ⟨x, hx, hxX, rfl⟩

end Helpers

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem isKleinFour_E (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E) :
    IsKleinFour ↥E := by
  have hsq : ∀ x : ↥E, x ^ 2 = 1 := fun x => Subtype.ext (by
    have := c.hyp.elemAbelian.2 (x : G) (L.le_V x.2)
    simpa using this)
  have hexp : Monoid.exponent ↥E = 2 := by
    have hdvd : Monoid.exponent ↥E ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hsub : Subsingleton ↥E := Monoid.exp_eq_one_iff.mp h1
      have := Nat.card_of_subsingleton (1 : ↥E)
      rw [L.card_eq] at this
      omega
    · exact h2
  exact ⟨L.card_eq, hexp⟩

theorem induces_GL (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) : autOn (YE153 Mc M E ⊔ TE153 T E) E = ⊤ := by
  have := isKleinFour_E c L
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := line_facts c L
  obtain ⟨hYV, y, hyYE, ⟨e, heE, hye⟩, hy3⟩ := Y_facts h113 c L
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer
  have hYEN : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hTEN : TE153 T E ≤ Subgroup.normalizer (E : Set G) := inf_le_right
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := hYEN hyYE
  have hyH : y ∈ YE153 Mc M E ⊔ TE153 T E := Subgroup.mem_sup_left hyYE
  have hσ₃ : conjAct E ⟨y, hyN⟩ ∈ autOn (YE153 Mc M E ⊔ TE153 T E) E := conjAct_mem_autOn hyN hyH
  have hσ₃ne : conjAct E ⟨y, hyN⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨y, hyN⟩).1 h
    apply hye
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e heE
    rw [← h1]
    group
  have hσ₃3 : conjAct E ⟨y, hyN⟩ ^ 3 = 1 := by
    have hy3N : y ^ 3 ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hyN 3
    have e1 : conjAct E ⟨y, hyN⟩ ^ 3 = conjAct E ⟨y ^ 3, hy3N⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact Subgroup.centralizer_le L.le_V hy3
  have hord₃ : orderOf (conjAct E ⟨y, hyN⟩) = 3 := orderOf_eq_prime hσ₃3 hσ₃ne
  obtain ⟨t₀, ht₀TE, e', he'E, hte'⟩ := c8
  have ht₀N : t₀ ∈ Subgroup.normalizer (E : Set G) := hTEN ht₀TE
  have ht₀V : t₀ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    hMN (c.hyp.T_le ht₀TE.1)
  have ht₀H : t₀ ∈ YE153 Mc M E ⊔ TE153 T E := Subgroup.mem_sup_right ht₀TE
  have hσ₂ : conjAct E ⟨t₀, ht₀N⟩ ∈ autOn (YE153 Mc M E ⊔ TE153 T E) E :=
    conjAct_mem_autOn ht₀N ht₀H
  have hσ₂ne : conjAct E ⟨t₀, ht₀N⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨t₀, ht₀N⟩).1 h
    apply hte'
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e' he'E
    rw [← h1]
    group
  have hσ₂2 : conjAct E ⟨t₀, ht₀N⟩ ^ 2 = 1 := by
    have hsqV : conjAct (VZ T M) ⟨t₀ * t₀, (Subgroup.normalizer _).mul_mem ht₀V ht₀V⟩ = 1 := by
      have hmem := c2 _ (conjAct_mem_autOn ht₀V ht₀TE)
      rw [← map_mul] at hmem
      exact hmem
    have hC : t₀ * t₀ ∈ Subgroup.centralizer (VZ T M : Set G) :=
      (conjAct_eq_one_iff''' _ _).1 hsqV
    have ht₀N2 : t₀ * t₀ ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer _).mul_mem ht₀N ht₀N
    have e1 : conjAct E ⟨t₀, ht₀N⟩ ^ 2 = conjAct E ⟨t₀ * t₀, ht₀N2⟩ := by
      rw [← map_pow, pow_two]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact Subgroup.centralizer_le L.le_V hC
  have hord₂ : orderOf (conjAct E ⟨t₀, ht₀N⟩) = 2 := orderOf_eq_prime hσ₂2 hσ₂ne
  have h3 : 3 ∣ Nat.card (autOn (YE153 Mc M E ⊔ TE153 T E) E) := by
    have := dvd_card_of_mem hσ₃
    rwa [hord₃] at this
  have h2 : 2 ∣ Nat.card (autOn (YE153 Mc M E ⊔ TE153 T E) E) := by
    have := dvd_card_of_mem hσ₂
    rwa [hord₂] at this
  have h6 : 6 ∣ Nat.card (autOn (YE153 Mc M E ⊔ TE153 T E) E) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
  have hdvd : Nat.card (autOn (YE153 Mc M E ⊔ TE153 T E) E) ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card (autOn (YE153 Mc M E ⊔ TE153 T E) E)
    rwa [CFSG.kleinFour_automorphism_card] at this
  exact CFSG.kleinFour_automorphism_subgroup_eq_top_of_card_six E _ (Nat.dvd_antisymm hdvd h6)

omit [Finite G] in
theorem le_centralizer_of_normal {E K Q : Subgroup G} [IsKleinFour ↥E]
    (hKN : K ≤ Subgroup.normalizer (E : Set G)) (hK : autOn K E = ⊤) (hQK : Q ≤ K)
    (hnorm : K ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) :
    Q ≤ Subgroup.centralizer (E : Set G) := by
  have hsq : ∀ q ∈ Q, ∀ hq : q ∈ Subgroup.normalizer (E : Set G), conjAct E ⟨q, hq⟩ ^ 2 = 1 := by
    intro q hq hqN
    obtain ⟨n, hn⟩ := hQ ⟨q, hq⟩
    refine sq_eq_one_of_pow (n := n) ?_
    have : (⟨q, hqN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [← map_pow, this, map_one]
  intro q hq
  have hqN : q ∈ Subgroup.normalizer (E : Set G) := hKN (hQK hq)
  have h1 := mulAut_key (conjAct E ⟨q, hqN⟩) (hsq q hq hqN) (fun τ => by
    have hτ : τ ∈ autOn K E := hK ▸ Subgroup.mem_top τ
    obtain ⟨k, hkN, hkK, rfl⟩ := mem_autOn_iff'''.mp hτ
    have hkq : k * q * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hnorm hkK) q).mp hq
    have hqq : q * (k * q * k⁻¹) ∈ Q := Q.mul_mem hq hkq
    have hqqN : q * (k * q * k⁻¹) ∈ Subgroup.normalizer (E : Set G) := hKN (hQK hqq)
    have e1 : conjAct E ⟨q, hqN⟩ * (conjAct E ⟨k, hkN⟩ * conjAct E ⟨q, hqN⟩ *
        (conjAct E ⟨k, hkN⟩)⁻¹) = conjAct E ⟨q * (k * q * k⁻¹), hqqN⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact hsq _ hqq hqqN)
  exact (conjAct_eq_one_iff''' E ⟨q, hqN⟩).1 h1

end Main

section Final

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

omit [Finite G] in
theorem le_normalizer_inf_centralizer {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (E : Set G)) :
    H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ H, ∀ x ∈ Subgroup.centralizer (E : Set G), g * x * g⁻¹ ∈
      Subgroup.centralizer (E : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hgN := hHN hg
    have h1 : g⁻¹ * e * g ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg)) e).mp he
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hx (g⁻¹ * e * g) h1
    calc e * (g * x * g⁻¹) = g * ((g⁻¹ * e * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * e * g)) * g⁻¹ := by rw [h2]
      _ = (g * x * g⁻¹) * e := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxH, hxC⟩
    exact ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), key g hg x hxC⟩
  · rintro ⟨hxH, hxC⟩
    have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    refine ⟨?_, ?_⟩
    · rw [h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg
    · rw [h1]
      have := key g⁻¹ (H.inv_mem hg) _ hxC
      simpa using this

theorem isPGroup_inf_centralizer (c : Ctx153 G T Mc M V₁ V₂ t) (r49 : Res15349 T Mc M V₁)
    (L : LineData153 T M V₁ V₂ E) :
    IsPGroup 2 ↥((YE153 Mc M E ⊔ TE153 T E) ⊓ Subgroup.centralizer (E : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := line_facts c L
  set N : Subgroup G := (YE153 Mc M E ⊔ TE153 T E) ⊓ Subgroup.centralizer (E : Set G) with hN
  have hHYT : YE153 Mc M E ⊔ TE153 T E ≤ Y153 Mc M ⊔ T :=
    sup_le_sup ((oTwoUpper_le _).trans inf_le_left) inf_le_left
  have hHM : YE153 Mc M E ⊔ TE153 T E ≤ M := hHYT.trans (sup_le (Y153_le Mc M) c.hyp.T_le)
  have hdvd1 : Nat.card ↥(Y153 Mc M ⊔ T) ∣ Nat.card (Y153 Mc M) * Nat.card T := by
    have := S143.card_sup_mul_card_inf_of_le_normalizer (R := Y153 Mc M) (U := T)
      (c.hyp.T_le.trans (le_normalizer_Y153 Mc M))
    exact Dvd.intro _ this
  have hNY : Nat.card ↥N ∣ Nat.card (Y153 Mc M) * Nat.card T :=
    (Subgroup.card_dvd_of_le (inf_le_left.trans hHYT)).trans hdvd1
  have hY9 : Nat.card (OTwoQuot (Y153 Mc M)) = 9 := by
    obtain ⟨e⟩ := r49.case_one.2
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3))]
    simp
  have hYcard : Nat.card (Y153 Mc M) = Nat.card (OTwoQuot (Y153 Mc M)) *
      Nat.card (CFSG.Open.pCore 2 ↥(Y153 Mc M)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hTp : IsPGroup 2 T := c.hyp.qtfe.sylow.1
  have hPp : IsPGroup 2 (CFSG.Open.pCore 2 ↥(Y153 Mc M)) :=
    CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(Y153 Mc M)) 2
  have hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥N → q = 2 := by
    intro q hq hqN
    have := Fact.mk hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) q hqN
    by_contra hq2
    have h1 : q ∣ Nat.card (Y153 Mc M) * Nat.card T := hqN.trans hNY
    have hq3 : q = 3 := by
      rcases (Nat.Prime.dvd_mul hq).mp h1 with h | h
      · rw [hYcard, hY9] at h
        rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
        · have : q ∣ 3 ^ 2 := by simpa using h'
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow this)
        · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hPp
          rw [hk] at h'
          exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h')) hq2
      · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hTp
        rw [hk] at h
        exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)) hq2
    subst hq3
    have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have hx3 : (x : G) ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
    have hxN : (x : G) ∈ N := x.2
    have hxC : (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) :=
      c9 x (hHM hxN.1) hx3 hxN.2
    have hxMC : (x : G) ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) := ⟨hHM hxN.1, hxC⟩
    apply r49.threePrime_C
    have := dvd_card_of_mem hxMC
    rwa [hxo] at this
  have hpos : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {q} hq hqd => hprime q hq hqd)

end Final

theorem stage15366B (h11 : StageLemma14111) (h113 : StageLemma14113) : Stage15366B := by
  intro G _ _ T Mc M V₁ V₂ E t c r45 r46 r49 L
  have := isKleinFour_E c L
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := line_facts c L
  obtain ⟨hYV, -⟩ := Y_facts h113 c L
  have hGL := induces_GL h113 c L
  have hN2 := isPGroup_inf_centralizer c r49 L
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.le_normalizer
  have hYEN : YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hTEN : TE153 T E ≤ Subgroup.normalizer (E : Set G) := inf_le_right
  have hHN : YE153 Mc M E ⊔ TE153 T E ≤ Subgroup.normalizer (E : Set G) := sup_le hYEN hTEN
  have hCEN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hpCoreH : pCoreOf 2 (YE153 Mc M E ⊔ TE153 T E) =
      (YE153 Mc M E ⊔ TE153 T E) ⊓ Subgroup.centralizer (E : Set G) := by
    refine le_antisymm (le_inf (pCoreOf_le 2 _) ?_) ?_
    · exact le_centralizer_of_normal hHN hGL (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _)
        (pCoreOf_isPGroup 2 _)
    · exact le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_inf_centralizer hHN) hN2
  refine ⟨c5, ?_, ⟨⟨c1, c3, fun a ha => by rw [pow_two]; exact c2 a ha⟩, c4⟩, c7, ?_, hYV, ?_,
    hpCoreH, hGL, ?_, ?_⟩
  ·
    have hV := c.hyp.elemAbelian
    have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := c.hyp.T_le.trans hMN
    have hTEV : TE153 T E ≤ Subgroup.normalizer (VZ T M : Set G) := inf_le_left.trans hTN
    have e1 := card_autI_mul_card_inf hV hTN
    have e2 := card_autI_mul_card_inf hV hTEV
    have hCE : TE153 T E ⊓ Subgroup.centralizer (VZ T M : Set G) =
        T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
      refine le_antisymm (inf_le_inf inf_le_left le_rfl) (le_inf (le_inf inf_le_left ?_) inf_le_right)
      intro x hx
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le L.le_V hx.2)
    set m := Nat.card ↥(T ⊓ Subgroup.centralizer (VZ T M : Set G)) with hmdef
    have hm : 0 < m := Nat.card_pos
    have hr := Subgroup.relIndex_mul_card (TE153 T E) T
    rw [inf_eq_left.2 (inf_le_left : TE153 T E ≤ T)] at hr
    have e1' : 8 * m = Nat.card T := by
      have h0 := e1
      rw [show Nat.card ↥(autI hV T) = 8 from c6] at h0
      exact h0
    have e2' : 4 * m = Nat.card (TE153 T E) := by
      have h0 := e2
      rw [show Nat.card ↥(autI hV (TE153 T E)) = 4 from c1, hCE] at h0
      exact h0
    rw [← e1', ← e2'] at hr
    have h8 : 4 * m * (TE153 T E).relIndex T = 4 * m * 2 := by
      calc 4 * m * (TE153 T E).relIndex T = (TE153 T E).relIndex T * (4 * m) := by ring
        _ = 8 * m := hr
        _ = 4 * m * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h8
  ·
    let H := YE153 Mc M E ⊔ TE153 T E
    let φ : ↥H →* MulAut ↥E := (conjAct E).comp (Subgroup.inclusion hHN)
    have hφsurj : Function.Surjective φ := by
      intro σ
      have hσ : σ ∈ autOn H E := hGL ▸ Subgroup.mem_top σ
      obtain ⟨x, hxN, hxH, rfl⟩ := mem_autOn_iff'''.mp hσ
      exact ⟨⟨x, hxH⟩, rfl⟩
    have hkerφ : φ.ker = CFSG.Open.pCore 2 ↥H := by
      have h1 : CFSG.Open.pCore 2 ↥H = (H ⊓ Subgroup.centralizer (E : Set G)).subgroupOf H := by
        rw [← hpCoreH]
        exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
      rw [h1]
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      show conjAct E ⟨(g : G), hHN g.2⟩ = 1 ↔ _
      rw [conjAct_eq_one_iff''']
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)).trans
      (CFSG.kleinFourAutomorphismEquivSymmetricThree E)⟩
  ·
    have hK : autOn (Subgroup.normalizer (E : Set G)) E = ⊤ :=
      eq_top_iff.2 (hGL ▸ A4.autOn_mono hHN)
    exact le_centralizer_of_normal le_rfl hK (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _)
      (pCoreOf_isPGroup 2 _)
  ·
    refine le_antisymm (fun g hg => ?_) (sup_le hHN hCEN)
    have hσ : conjAct E ⟨g, hg⟩ ∈ autOn (YE153 Mc M E ⊔ TE153 T E) E := hGL ▸ Subgroup.mem_top _
    obtain ⟨h, hhN, hhH, hhg⟩ := mem_autOn_iff'''.mp hσ
    have h1 : conjAct E ⟨h⁻¹ * g, (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem hhN) hg⟩ = 1 := by
      have e1 : (⟨h⁻¹ * g, (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem hhN) hg⟩ :
          ↥(Subgroup.normalizer (E : Set G))) = ⟨h, hhN⟩⁻¹ * ⟨g, hg⟩ := Subtype.ext rfl
      rw [e1, map_mul, map_inv, hhg, inv_mul_cancel]
    have h2 : h⁻¹ * g ∈ Subgroup.centralizer (E : Set G) := (conjAct_eq_one_iff''' E _).1 h1
    have e3 : g = h * (h⁻¹ * g) := by group
    rw [e3]
    exact Subgroup.mul_mem_sup hhH h2
  ·
    rw [Hyp153.lemma_15_3_4 h11 c.hyp]
    exact Subgroup.centralizer_le c7

end CFSG.Quasithin
