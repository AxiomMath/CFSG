module

public import CFSG.Quasithin.EmptyFaithful.F918C7
public import CFSG.Quasithin.Background.F918C9
public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.Quasithin.Background.F918C8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def AsI161A6 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut W)) (V : Subgroup W), (∀ x ∈ L, ∀ v ∈ V, x v ∈ V) →
      XMod.commOf ↥L V = V → AlternatingNatural L V (V ⊓ fixV L) 6 → Nat.card ↥(V ⊓ fixV L) ≤ 2

section Cards

variable {W : Type} [CommGroup W]

theorem card_eq_of_realizesVia {D : FFModel} {L : Subgroup (MulAut W)} {V Z : Subgroup W}
    {π : D.Gam →* ↥L} (h : D.RealizesVia L V Z π) :
    Nat.card ↥V = Nat.card ↥Z * Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨-, hZV, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hker : β.ker = Z.subgroupOf V := by
    ext u
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_ker_mul_card_range β
  rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv] at h1
  exact h1.symm

theorem card_natQuot_three {F : Type} [Field F] (hF : Nat.card F = 2) :
    Nat.card (↥(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).sec ⧸
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).ker.subgroupOf (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).sec) = 8 := by
  have e := (B5.natQuotEquiv (Multiplicative (Fin 3 → F)))
  show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 3 → F))) ⧸
    (⊥ : Subgroup (Multiplicative (Fin 3 → F))).subgroupOf ⊤) = 8
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → F) = 8
  rw [Nat.card_fun, Nat.card_fin, hF]
  norm_num

theorem card_D6 : Nat.card (↥(FFModel.altDn 6).sec ⧸
    (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec) = 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, Explicit.card_dnZ (by norm_num),
    Explicit.card_coreMod (by norm_num)] at h
  have h6 : (if Even 6 then 2 else 1) = 2 := by decide
  rw [h6] at h
  show Nat.card (↥(G6.coreMod 6) ⧸
    ((Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6))) = 16
  have h32 : (2 : ℕ) ^ (6 - 1) = 32 := by norm_num
  omega

end Cards

section NaturalLike

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

omit [Finite G] in
theorem mIdx_eq_of_card {J : Subgroup G} {k : ℕ} (hJ : (V₁.relIndex J) = 2 ^ k) : mIdx J V₁ = k := by
  unfold mIdx
  rw [hJ, padicValNat.prime_pow]

theorem isNaturalLike_of_naturalType (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hirr : IsIrrPlusTildeT h hIU) (hK : conjClosure K T = K) (hS' : IsSimpleGroup (KBar K))
    (hne : autIH V₁ I H K ≠ ⊥) (hL : KbarIsL3Two K ∨ KbarIsA6 K)
    (hnat : ModNaturalType (autIH V₁ I H K) (subM V₁ (conjClosure I H) I))
    (hI161 : AsI161A6)
    (hC3 : IsPSL 3 2 1 ↥(autIH V₁ I H K) →
      subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H K) = ⊥) :
    IsNaturalLike K V₁ I := by
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := MulEquiv.isSimpleGroup (kbarEquiv K).symm
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_autI h hIU hS hne
  set V' := subM V₁ (conjClosure I H) I with hV'
  set L' := autIH V₁ I H K with hL'
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK ▸ hKI
  have hV₁N : K ≤ Subgroup.normalizer (V₁ : Set G) := hKH.trans h.H_le_normalizer_V₁
  have hirrBot : V' ⊓ fixV L' = ⊥ →
      IsIrredOnSection K I V₁ ∧ V₁ ≠ I := by
    intro hC
    have hfix : XMod.fixed ↥L' V' = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have : w ∈ V' ⊓ fixV L' := ⟨hw.1, fun x hx => hw.2 ⟨x, hx⟩⟩
      rw [hC] at this
      exact this
    have hV₁bot : subM V₁ (conjClosure I H) V₁ = ⊥ := by
      unfold subM
      rw [tildeOf_eq_bot_of_le le_rfl, Subgroup.bot_subgroupOf]
    have hsec : XMod.IsIrrSec ↥L' (subM V₁ (conjClosure I H) V₁) V' := by
      rw [hV₁bot, ← hfix]
      have := hirr'.1.2.2.2
      rwa [hK] at this
    have hne' : V₁ ≠ I := by
      intro heq
      have h1 : subM V₁ (conjClosure I H) V₁ = V' := congrArg (subM V₁ (conjClosure I H)) heq
      have := hsec.1
      rw [h1] at this
      exact lt_irrefl _ this
    refine ⟨⟨lt_of_le_of_ne hV₁I hne', hKI', hV₁N, fun J hV₁J hJI hKJ => ?_⟩, hne'⟩
    exact eq_or_eq_of_isIrrSec h.H_le_normalizer_V₁ hIHN hIH hKH le_rfl hV₁J hJI
      (le_conjClosure I H) hKJ hsec
  have hcommI : ⁅I, K⁆ ⊔ V₁ = I := by
    have h1 := tildeOf_commutator_eq h hV₁I hIU hKI hirr'.1.2.2.1
    rw [hK] at h1
    have hcI : ⁅I, K⁆ ≤ I := by
      refine Subgroup.commutator_le.mpr fun i hi k hk => ?_
      have h2 : k * i⁻¹ * k⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp (hKI' hk) i⁻¹).mp (I.inv_mem hi)
      have e : i * k * i⁻¹ * k⁻¹ = i * (k * i⁻¹ * k⁻¹) := by group
      rw [commutatorElement_def, e]
      exact I.mul_mem hi h2
    have hIN : I ≤ Subgroup.normalizer (V₁ : Set G) := (le_conjClosure I H).trans hIHN
    refine eq_of_secImg_eq (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) le_sup_right hV₁I
      (sup_le (hcI.trans hIN) Subgroup.le_normalizer) hIN ?_
    show tildeOf V₁ (⁅I, K⁆ ⊔ V₁) = tildeOf V₁ I
    rw [tildeOf_sup' (hcI.trans hIN) Subgroup.le_normalizer, tildeOf_eq_bot_of_le le_rfl,
      sup_bot_eq, h1]
  obtain ⟨eK⟩ : Nonempty (↥L' ≃* KBar K) := ⟨e.symm.trans (kbarEquiv K).symm⟩
  rcases hL with ⟨⟨eL⟩⟩ | ⟨⟨eA⟩⟩
  ·
    have hPSL : IsPSL 3 2 1 ↥L' :=
      CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two (eK.trans eL)
    have hC := hC3 hPSL
    obtain ⟨F, hF, hFfin, hcard, π, hπ⟩ := hnat.1 hPSL
    have hF2 : Nat.card F = 2 := by simpa using hcard
    have hV8 : Nat.card ↥V' = 8 := by
      have := card_eq_of_realizesVia hπ
      rw [hC, Subgroup.card_bot, card_natQuot_three hF2] at this
      simpa using this
    have hrel : V₁.relIndex I = 2 ^ 3 := by
      rw [← card_subM hIHN hV₁I (le_conjClosure I H)]
      exact hV8
    obtain ⟨hirrSec, -⟩ := hirrBot hC
    exact Or.inl ⟨⟨eL⟩, mIdx_eq_of_card hrel, hirrSec⟩
  ·
    have hAlt : IsAlt 6 ↥L' := ⟨eK.trans eA⟩
    obtain ⟨π, hπ⟩ : ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥L',
        (FFModel.altDn 6).RealizesVia L' V' (V' ⊓ fixV L') π := hnat.2 hAlt
    have hcardV := card_eq_of_realizesVia hπ
    rw [card_D6] at hcardV
    refine Or.inr ⟨⟨eA⟩, ?_⟩
    by_cases hC : V' ⊓ fixV L' = ⊥
    · have hV16 : Nat.card ↥V' = 16 := by
        rw [hC, Subgroup.card_bot] at hcardV
        simpa using hcardV
      have hrel : V₁.relIndex I = 2 ^ 4 := by
        rw [← card_subM hIHN hV₁I (le_conjClosure I H)]
        exact hV16
      obtain ⟨hirrSec, -⟩ := hirrBot hC
      exact Or.inl ⟨mIdx_eq_of_card hrel, hirrSec, hcommI⟩
    · have hle2 : Nat.card ↥(V' ⊓ fixV L') ≤ 2 := by
        have hexp : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w ^ 2 = 1 := fun w => by
          apply Subtype.ext
          have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).2
            (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) w.2
          simpa using this
        have hinv : ∀ x ∈ L', ∀ v ∈ V', x v ∈ V' := fun x hx v hv => by
          have := hirr'.1.2.1
          rw [hK] at this
          exact this ⟨x, hx⟩ v hv
        have hcomm' : XMod.commOf ↥L' V' = V' := by
          have := hirr'.1.2.2.1
          rwa [hK] at this
        exact hI161 _ hexp L' V' hinv hcomm' (hnat.2 hAlt)
      have hge : Nat.card ↥(V' ⊓ fixV L') ≠ 1 := by
        intro h1
        exact hC (Subgroup.card_eq_one.mp h1)
      have hpos := Nat.card_pos (α := ↥(V' ⊓ fixV L'))
      have h2 : Nat.card ↥(V' ⊓ fixV L') = 2 := by omega
      have hV32 : Nat.card ↥V' = 2 ^ 5 := by
        rw [h2] at hcardV
        simpa using hcardV
      have hrel : V₁.relIndex I = 2 ^ 5 := by
        rw [← card_subM hIHN hV₁I (le_conjClosure I H)]
        exact hV32
      exact Or.inr ⟨mIdx_eq_of_card hrel, hcommI⟩

end NaturalLike

end CFSG.Quasithin
