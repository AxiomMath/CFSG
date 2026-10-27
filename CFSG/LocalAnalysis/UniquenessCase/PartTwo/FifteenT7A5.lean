module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem s15_T7_mul_mem_of_mQuot_le_one {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {A : Subgroup P} (hA : E3.mQuot ⊤ A ≤ 1) {x y : P} (hx : x ∉ A) (hy : y ∉ A) :
    x * y ∈ A := by
  have hP' : IsPGroup 2 ↥(⊤ : Subgroup P) := hP.to_subgroup _
  have h := E3.relIndex_eq_two_pow hP' A
  rw [Subgroup.relIndex_top_right] at h
  have hidx : A.index = 2 := by
    have h0 : E3.mQuot ⊤ A ≠ 0 := fun h0 => by
      rw [h0, pow_zero, Subgroup.index_eq_one] at h
      exact hx (h ▸ Subgroup.mem_top x)
    have h1 : E3.mQuot ⊤ A = 1 := by omega
    rw [h, h1, pow_one]
  exact (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hx hy)

section Alt5

open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

@[expose] noncomputable def s15T7AltImage : Subgroup (MulAut ↥(G6.coreMod 5)) :=
  (alternatingGroup (Fin 5)).map (G6.coreAct 5)

@[expose] def s15T7ToEven (x : ↥(G6.coreMod 5)) : ↥(CFSG.QuasithinUnique.evenWeight 5) :=
  ⟨Multiplicative.toAdd x.1, G6.mem_coreMod.1 x.2⟩

@[expose] def s15T7OfEven (w : ↥(CFSG.QuasithinUnique.evenWeight 5)) : ↥(G6.coreMod 5) :=
  ⟨Multiplicative.ofAdd w.1, w.2⟩

theorem s15_T7_toEven_ofEven (w : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
    s15T7ToEven (s15T7OfEven w) = w := rfl

theorem s15_T7_ofEven_vact (σ : Equiv.Perm (Fin 5))
    (w : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
    s15T7OfEven (CFSG.QuasithinUnique.A5.Delta5.vact σ w) = G6.coreAct 5 σ (s15T7OfEven w) := rfl

theorem s15_T7_alt5_centralizer {q : MulAut ↥(G6.coreMod 5)}
    (hq : ∀ γ ∈ alternatingGroup (Fin 5), q * G6.coreAct 5 γ = G6.coreAct 5 γ * q) : q = 1 := by
  let g : ↥(CFSG.QuasithinUnique.evenWeight 5) → ↥(CFSG.QuasithinUnique.evenWeight 5) :=
    fun w => s15T7ToEven (q (s15T7OfEven w))
  have hadd : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    show s15T7ToEven (q (s15T7OfEven (x + y))) = _
    have : s15T7OfEven (x + y) = s15T7OfEven x * s15T7OfEven y := rfl
    rw [this, map_mul]
    rfl
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : q (s15T7OfEven x) = q (s15T7OfEven y) := congrArg s15T7OfEven hxy
    exact congrArg s15T7ToEven (q.injective h1)
  have hcomm : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → ∀ w,
      g (CFSG.QuasithinUnique.A5.Delta5.vact σ w) =
        CFSG.QuasithinUnique.A5.Delta5.vact σ (g w) := by
    intro σ hσ w
    have hσ' : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hσ
    have h1 := congrArg (fun φ : MulAut ↥(G6.coreMod 5) => φ (s15T7OfEven w)) (hq σ hσ')
    simp only [MulAut.mul_apply] at h1
    show s15T7ToEven (q (s15T7OfEven (CFSG.QuasithinUnique.A5.Delta5.vact σ w))) = _
    rw [s15_T7_ofEven_vact, h1]
    rfl
  have hrig := CFSG.QuasithinUnique.A5.Delta5.rigid g hadd hinj hcomm
  refine MulEquiv.ext fun x => ?_
  exact congrArg s15T7OfEven (hrig (s15T7ToEven x))

theorem s15_T7_coreAct_injective : Function.Injective (G6.coreAct 5) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine CFSG.QuasithinUnique.A5.Delta5.pact_faithful σ fun x hx => ?_
  have := congrArg (fun φ : MulAut ↥(G6.coreMod 5) => s15T7ToEven (φ (s15T7OfEven ⟨x, hx⟩))) hσ
  exact congrArg Subtype.val this

theorem s15_T7_alt5_normalizer {q : MulAut ↥(G6.coreMod 5)}
    (hq : q ∈ normalizer (s15T7AltImage : Set (MulAut ↥(G6.coreMod 5)))) :
    ∃ σ : Equiv.Perm (Fin 5), q = G6.coreAct 5 σ := by
  let c : ↥(alternatingGroup (Fin 5)) →* MulAut ↥(G6.coreMod 5) :=
    (G6.coreAct 5).comp (alternatingGroup (Fin 5)).subtype
  have hcinj : Function.Injective c := s15_T7_coreAct_injective.comp Subtype.val_injective
  have hrange : c.range = s15T7AltImage := by
    ext x
    simp [c, s15T7AltImage, MonoidHom.mem_range, Subgroup.mem_map]
  have hq' : q ∈ normalizer (c.range : Set (MulAut ↥(G6.coreMod 5))) := by
    rw [hrange]; exact hq
  let e : ↥(alternatingGroup (Fin 5)) ≃* ↥c.range := MonoidHom.ofInjective hcinj
  let ρ : MulAut ↥c.range := normalizerMonoidHom c.range ⟨q, hq'⟩
  let ψ : ↥(alternatingGroup (Fin 5)) ≃* ↥(alternatingGroup (Fin 5)) := (e.trans ρ).trans e.symm
  obtain ⟨σ, hσ⟩ := CFSG.QuasithinUnique.A5.Delta5.aut_inner ψ
  have hψ : ∀ a : ↥(alternatingGroup (Fin 5)), c (ψ a) = q * c a * q⁻¹ := by
    intro a
    have h1 : e (ψ a) = ρ (e a) := by simp [ψ]
    exact congrArg Subtype.val h1
  have key : ∀ a : ↥(alternatingGroup (Fin 5)), (G6.coreAct 5 σ)⁻¹ * q * G6.coreAct 5 a =
      G6.coreAct 5 a * ((G6.coreAct 5 σ)⁻¹ * q) := by
    intro a
    have h1 := hψ a
    have h2 : c (ψ a) = G6.coreAct 5 σ * c a * (G6.coreAct 5 σ)⁻¹ := by
      show G6.coreAct 5 ((ψ a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = _
      rw [hσ a, map_mul, map_mul, map_inv]
      rfl
    rw [h2] at h1
    have h3 : G6.coreAct 5 σ * c a * (G6.coreAct 5 σ)⁻¹ * q = q * c a := by
      rw [h1]; group
    calc (G6.coreAct 5 σ)⁻¹ * q * G6.coreAct 5 a
        = (G6.coreAct 5 σ)⁻¹ * (q * c a) := by rw [mul_assoc]; rfl
      _ = (G6.coreAct 5 σ)⁻¹ * (G6.coreAct 5 σ * c a * (G6.coreAct 5 σ)⁻¹ * q) := by rw [h3]
      _ = G6.coreAct 5 a * ((G6.coreAct 5 σ)⁻¹ * q) := by
        show _ = c a * _
        group
  have h1 := s15_T7_alt5_centralizer (q := (G6.coreAct 5 σ)⁻¹ * q) (fun γ hγ => key ⟨γ, hγ⟩)
  exact ⟨σ, (inv_mul_eq_one.mp h1).symm⟩

theorem s15_T7_perm5_transvection : ∀ σ : Equiv.Perm (Fin 5),
    (∀ x₁ x₂ : Fin 5 → ZMod 2, isEven x₁ → isEven x₂ → pact σ x₁ ≠ x₁ → pact σ x₂ ≠ x₂ →
      pact σ (x₁ + x₂) = x₁ + x₂) →
    σ = 1 ∨ ∃ i j : Fin 5, i ≠ j ∧ σ = Equiv.swap i j := by
  decide +kernel

theorem s15_T7_perm5_swap_witness : ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
    Equiv.swap i j ≠ Equiv.swap k l →
    ∃ x₁ x₂ : Fin 5 → ZMod 2, isEven x₁ ∧ isEven x₂ ∧
      ¬ (pact (Equiv.swap i j) x₁ = x₁ ∧ pact (Equiv.swap k l) x₁ = x₁) ∧
      ¬ (pact (Equiv.swap i j) x₂ = x₂ ∧ pact (Equiv.swap k l) x₂ = x₂) ∧
      ¬ (pact (Equiv.swap i j) (x₁ + x₂) = x₁ + x₂ ∧
        pact (Equiv.swap k l) (x₁ + x₂) = x₁ + x₂) := by
  decide +kernel

theorem s15_T7_coreMod5_sq (x : ↥(G6.coreMod 5)) : x ^ 2 = 1 := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  simp [pow_two, h]

theorem s15_T7_alt5_fix {σ : Equiv.Perm (Fin 5)} {A : Subgroup ↥(G6.coreMod 5)}
    (hA : E3.mQuot ⊤ A ≤ 1) (hσ : ∀ a ∈ A, G6.coreAct 5 σ a = a) : σ = 1 ∨ σ.IsSwap := by
  have hP : IsPGroup 2 ↥(G6.coreMod 5) := isPGroup_two_of_sq_eq_one s15_T7_coreMod5_sq
  refine s15_T7_perm5_transvection σ fun x₁ x₂ h1 h2 n1 n2 => ?_
  have hy1 : s15T7OfEven ⟨x₁, h1⟩ ∉ A := fun h => n1 (by
    have := hσ _ h
    exact congrArg (fun z : ↥(G6.coreMod 5) => (s15T7ToEven z).1) this)
  have hy2 : s15T7OfEven ⟨x₂, h2⟩ ∉ A := fun h => n2 (by
    have := hσ _ h
    exact congrArg (fun z : ↥(G6.coreMod 5) => (s15T7ToEven z).1) this)
  have hmul := hσ _ (s15_T7_mul_mem_of_mQuot_le_one hP hA hy1 hy2)
  exact congrArg (fun z : ↥(G6.coreMod 5) => (s15T7ToEven z).1) hmul

theorem s15_T7_alt5_swap_unique {σ τ : Equiv.Perm (Fin 5)} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    {A : Subgroup ↥(G6.coreMod 5)} (hA : E3.mQuot ⊤ A ≤ 1)
    (hσA : ∀ a ∈ A, G6.coreAct 5 σ a = a) (hτA : ∀ a ∈ A, G6.coreAct 5 τ a = a) : σ = τ := by
  obtain ⟨i, j, hij, rfl⟩ := hσ
  obtain ⟨k, l, hkl, rfl⟩ := hτ
  by_contra hne
  obtain ⟨x₁, x₂, h1, h2, n1, n2, n12⟩ := s15_T7_perm5_swap_witness i j k l hij hkl hne
  have hP : IsPGroup 2 ↥(G6.coreMod 5) := isPGroup_two_of_sq_eq_one s15_T7_coreMod5_sq
  have hfix : ∀ z : ↥(G6.coreMod 5), z ∈ A →
      pact (Equiv.swap i j) (s15T7ToEven z).1 = (s15T7ToEven z).1 ∧
      pact (Equiv.swap k l) (s15T7ToEven z).1 = (s15T7ToEven z).1 := fun z hz =>
    ⟨congrArg (fun z : ↥(G6.coreMod 5) => (s15T7ToEven z).1) (hσA z hz),
      congrArg (fun z : ↥(G6.coreMod 5) => (s15T7ToEven z).1) (hτA z hz)⟩
  have hy1 : s15T7OfEven ⟨x₁, h1⟩ ∉ A := fun h => n1 (hfix _ h)
  have hy2 : s15T7OfEven ⟨x₂, h2⟩ ∉ A := fun h => n2 (hfix _ h)
  exact n12 (hfix _ (s15_T7_mul_mem_of_mQuot_le_one hP hA hy1 hy2))

theorem s15_T7_alt5_model_card_le_two {Q : Subgroup (MulAut ↥(G6.coreMod 5))}
    (hQN : Q ≤ normalizer (s15T7AltImage : Set (MulAut ↥(G6.coreMod 5))))
    {A : Subgroup ↥(G6.coreMod 5)} (hA : E3.mQuot ⊤ A ≤ 1)
    (hfix : ∀ q ∈ Q, ∀ a ∈ A, q a = a) : Nat.card ↥Q ≤ 2 := by
  by_cases hall1 : ∀ q ∈ Q, q = 1
  · have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 hall1
    rw [this]
    simp
  · push Not at hall1
    obtain ⟨q₀, hq₀, hq₀1⟩ := hall1
    obtain ⟨σ₀, hσ₀⟩ := s15_T7_alt5_normalizer (hQN hq₀)
    have hσ₀1 : σ₀ ≠ 1 := fun h => hq₀1 (by rw [hσ₀, h, map_one])
    have hσ₀s : σ₀.IsSwap :=
      (s15_T7_alt5_fix hA fun a ha => by rw [← hσ₀]; exact hfix q₀ hq₀ a ha).resolve_left hσ₀1
    refine s15_T7_card_le_two_of_unique (q₀ := q₀) (fun q hq => ?_) hq₀1
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · refine Or.inr ?_
      obtain ⟨σ, hσ⟩ := s15_T7_alt5_normalizer (hQN hq)
      have hσ1 : σ ≠ 1 := fun h => hq1 (by rw [hσ, h, map_one])
      have hσs : σ.IsSwap :=
        (s15_T7_alt5_fix hA fun a ha => by rw [← hσ]; exact hfix q hq a ha).resolve_left hσ1
      have := s15_T7_alt5_swap_unique hσs hσ₀s hA (fun a ha => by rw [← hσ]; exact hfix q hq a ha)
        (fun a ha => by rw [← hσ₀]; exact hfix q₀ hq₀ a ha)
      rw [hσ, hσ₀, this]

theorem s15_T7_altDn5_ker : (FFModel.altDn 5).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz1
  have hsq : G6.allOnes 5 * G6.allOnes 5 = 1 := by decide +kernel
  have hnot : G6.allOnes 5 ∉ G6.coreMod 5 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hord : orderOf (G6.allOnes 5) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) (by decide +kernel)
  have hmod := zpow_mod_orderOf (G6.allOnes 5) k
  rw [hord] at hmod
  simp only [Nat.cast_ofNat] at hmod
  rw [← hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]
  · exfalso
    apply hnot
    rw [← hmod, h, zpow_one] at hz2
    exact hz2

theorem s15_T7_exists_iso {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U : Subgroup W}
    (hH : AlternatingNatural H U ⊥ 5) :
    ∃ (π : ↥(alternatingGroup (Fin 5)) →* ↥H) (ε : ↥U ≃* ↥(G6.coreMod 5)),
      Function.Surjective π ∧ (∀ h : ↥H, ∀ u ∈ U, (h : MulAut W) u ∈ U) ∧
      ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U),
        ε ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ = G6.coreAct 5 γ (ε u) := by
  obtain ⟨π, hπs, -, -, hHU, -, -, -, β, hβs, hβk, hβe⟩ := hH
  have hkerbot : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    rw [s15_T7_altDn5_ker, Subgroup.bot_subgroupOf]
  let E : ↥(FFModel.altDn 5).sec ⧸ (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec →*
      ↥(FFModel.altDn 5).sec :=
    QuotientGroup.lift _ (MonoidHom.id ↥(FFModel.altDn 5).sec) (by rw [hkerbot]; exact bot_le)
  have hE : ∀ m : ↥(FFModel.altDn 5).sec, E (QuotientGroup.mk m) = m := fun m => rfl
  let ε₀ : ↥U →* ↥(G6.coreMod 5) := E.comp β
  have hinj : Function.Injective ε₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 : ε₀ u = m := by
      show E (β u) = m
      rw [← hm]
      exact hE m
    have h2 : m = 1 := h1 ▸ hu
    have h3 : β u = 1 := by rw [← hm, h2]; rfl
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 h3))
  have hsurj : Function.Surjective ε₀ := by
    intro m
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    exact ⟨u, by show E (β u) = m; rw [hu]; exact hE m⟩
  let ε : ↥U ≃* ↥(G6.coreMod 5) := MulEquiv.ofBijective ε₀ ⟨hinj, hsurj⟩
  refine ⟨π, ε, hπs, hHU, fun γ u hu => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have h1 : ε u = m := by
    show E (β u) = m
    rw [← hm]
    exact hE m
  have hmem : (FFModel.altDn 5).act γ m.1 ∈ (FFModel.altDn 5).sec :=
    G6.permAct_mem_coreMod (γ : Equiv.Perm (Fin 5)) m.2
  have h2 := hβe γ u m hu hmem hm.symm
  show E (β ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) = G6.coreAct 5 γ (ε u)
  rw [h2, hE, h1]
  rfl

theorem s15_T7_alt5_card_le_two {W : Type} [CommGroup W] [Finite W]
    {H Q : Subgroup (MulAut W)} {U A : Subgroup W} (hH : AlternatingNatural H U ⊥ 5)
    (hQN : Q ≤ normalizer (H : Set (MulAut W)))
    (hA : E3.mQuot U A ≤ 1) (hfix : ∀ q ∈ Q, ∀ a ∈ A, q a = a) :
    Nat.card ↥(autSub Q U) ≤ 2 := by
  obtain ⟨π, ε, hπs, hHU, hεe⟩ := s15_T7_exists_iso hH
  have hπstab : ∀ γ, ((π γ : ↥H) : MulAut W) ∈ stabSub U := by
    intro γ
    rw [mem_stabSub]
    intro u
    refine ⟨fun hu => ?_, hHU (π γ) u⟩
    have := hHU (π γ)⁻¹ _ hu
    simpa using this
  let Φ : ↥(stabSub U) →* MulAut ↥(G6.coreMod 5) :=
    ((MulAut.congr ε).toMonoidHom).comp (resHom U)
  have hΦ : ∀ g : ↥(stabSub U), ∀ x : ↥(G6.coreMod 5),
      Φ g x = ε (resHom U g (ε.symm x)) := fun g x => rfl
  have hF1 : ∀ γ : ↥(alternatingGroup (Fin 5)),
      Φ ⟨((π γ : ↥H) : MulAut W), hπstab γ⟩ = G6.coreAct 5 γ := by
    intro γ
    refine MulEquiv.ext fun x => ?_
    rw [hΦ]
    have h := hεe γ (ε.symm x) (by
      have := ((resHom U ⟨((π γ : ↥H) : MulAut W), hπstab γ⟩) (ε.symm x)).2
      exact this)
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have hF2 : ∀ g : ↥(stabSub U), (g : MulAut W) ∈ Q → ∀ i ∈ s15T7AltImage,
      Φ g * i * (Φ g)⁻¹ ∈ s15T7AltImage := by
    intro g hg i hi
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hi
    have hπγ : ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) ∈ H := (π ⟨γ, hγ⟩).2
    have hconj : (g : MulAut W) * ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) * (g : MulAut W)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.1 (hQN hg) _).1 hπγ
    obtain ⟨γ', hγ'⟩ := hπs ⟨_, hconj⟩
    refine Subgroup.mem_map.2 ⟨γ'.1, γ'.2, ?_⟩
    have h1 : (G6.coreAct 5) γ = Φ ⟨((π ⟨γ, hγ⟩ : ↥H) : MulAut W), hπstab _⟩ :=
      (hF1 ⟨γ, hγ⟩).symm
    have h2 : (G6.coreAct 5) γ'.1 = Φ ⟨((π γ' : ↥H) : MulAut W), hπstab _⟩ := (hF1 γ').symm
    rw [h1, h2, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := congrArg Subtype.val hγ'
    simpa using this
  let Qm : Subgroup (MulAut ↥(G6.coreMod 5)) :=
    (autSub Q U).map (MulAut.congr ε).toMonoidHom
  have hQmN : Qm ≤ normalizer (s15T7AltImage : Set (MulAut ↥(G6.coreMod 5))) := by
    intro q hq
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨g, hgQ, rfl⟩ := mem_autSub.1 hφ
    have hΦg : (MulAut.congr ε).toMonoidHom (resHom U g) = Φ g := rfl
    rw [hΦg, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hF2 g hgQ h hh, fun hh => ?_⟩
    have h1 := hF2 g⁻¹ (inv_mem hgQ) _ hh
    have e : Φ g⁻¹ * (Φ g * h * (Φ g)⁻¹) * (Φ g⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    rwa [e] at h1
  have hAm' : E3.mQuot ⊤ ((A.subgroupOf U).map (ε : ↥U →* ↥(G6.coreMod 5))) ≤ 1 := by
    have h1 : E3.mQuot (⊤ : Subgroup ↥(G6.coreMod 5))
        ((A.subgroupOf U).map (ε : ↥U →* ↥(G6.coreMod 5))) = E3.mQuot U A := by
      rw [← s15_T7_mQuot_top_subgroupOf U A]
      unfold E3.mQuot
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, Subgroup.index_map_equiv]
    omega
  have hfix' : ∀ q ∈ Qm, ∀ a ∈ (A.subgroupOf U).map (ε : ↥U →* ↥(G6.coreMod 5)), q a = a := by
    intro q hq a ha
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨g, hgQ, rfl⟩ := mem_autSub.1 hφ
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ha
    show ε (resHom U g (ε.symm (ε u))) = ε u
    rw [MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    exact hfix _ hgQ _ (Subgroup.mem_subgroupOf.1 hu)
  have hcard : Nat.card ↥Qm = Nat.card ↥(autSub Q U) :=
    Subgroup.card_map_of_injective (MulEquiv.injective _)
  rw [← hcard]
  exact s15_T7_alt5_model_card_le_two hQmN hAm' hfix'

end Alt5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
