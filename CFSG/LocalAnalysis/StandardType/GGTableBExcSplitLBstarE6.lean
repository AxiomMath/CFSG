module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcSplitL

section GenericR

variable {p r : ℕ} {R : Type} [Group R]

theorem ggInnerDiagBound_of_elt' [Finite R] (hp : p.Prime) {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : TableBOrth.GGBstarElt p r R) : GGInnerDiagBound p r R I := by
  intro Eb Eh hEbI hEb hr h3 hle hEh hcard hnot
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E₀ := Eb.comap (MulAut.conj : R →* MulAut R) with hE₀
  have hmap : E₀.map (MulAut.conj : R →* MulAut R) = Eb := by
    rw [hE₀, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI φ (hEbI hφ) (hEb.2 φ hφ)
  have hcardE₀ : Nat.card E₀ = Nat.card Eb := by
    rw [Nat.card_congr (E₀.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hE₀e : IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEb a.2 b.2
    · rw [map_pow, map_one]
      exact hEb.2 _ hx
  obtain ⟨φ, hφEh, hφI⟩ := Set.not_subset.mp hnot
  have hφEb : φ ∉ Eb := fun h' => hφI (hEbI h')
  have hφp : φ ^ p = 1 := hEh.2 φ hφEh
  have hφfix : ∀ e ∈ E₀, φ e = e := by
    intro e he
    have hce : MulAut.conj e ∈ Eh := hle he
    have hcomm := TableB.IsElemAbelian.comm hEh hφEh hce
    apply hinj
    rw [← TableBOrth.mulAut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
  obtain ⟨U, hU, hU2, hUE, hUφ⟩ := h E₀ hE₀e (hcardE₀ ▸ hr) (hcardE₀ ▸ h3) φ hφp hφfix
  have hM : Eb ⊔ Subgroup.zpowers φ = Eh := by
    refine CorFourTwoOpen.eq_of_lt_of_card_le_mul hp
      (CorFourTwoOpen.isPGroup_of_elemAbelian hEh) ?_
      (sup_le hle (Subgroup.zpowers_le.mpr hφEh)) hcard
    refine lt_of_le_of_ne le_sup_left fun h' => hφEb ?_
    rw [h']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers φ)
  have hle2 : Eb ⊔ Subgroup.zpowers φ ≤ TableBOrth.stabSubgroup U := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr (TableBOrth.mem_stabSubgroup_of_le hUφ))
    intro ψ hψ
    obtain ⟨e, rfl⟩ := hI ψ (hEbI hψ) (hEb.2 ψ hψ)
    refine TableBOrth.mem_stabSubgroup_of_le fun u hu => ?_
    have heE : e ∈ E₀ := by
      rw [hE₀, Subgroup.mem_comap]
      exact hψ
    rw [MulAut.conj_apply]
    exact hUE e heE u hu
  refine ⟨U, hU, hU2, fun ψ hψ u hu => ?_⟩
  have h1 : U.map ψ.toMonoidHom = U := hle2 (hM ▸ hψ)
  rw [← h1]
  exact ⟨u, hu, rfl⟩

end GenericR

section Diag


theorem rootDiagUnit_conj_mem_posUnipotent {τ : Tag} {K : Type} [Field K]
    (b : Fin τ.rank → Kˣ) {x : ModGL τ K} (hx : x ∈ posUnipotent τ K) :
    rootDiagUnit τ b * x * (rootDiagUnit τ b)⁻¹ ∈ posUnipotent τ K := by
  have hle : posUnipotent τ K ≤
      (posUnipotent τ K).comap (MulAut.conj (rootDiagUnit τ b)).toMonoidHom := by
    show rootSpan τ K {α | IsRoot τ α ∧ 0 < height α} ≤ _
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      rootDiagUnit_conj_pinnedX b hα.1]
    exact (le_iSup₂ (f := fun β (_ : β ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}) =>
      rootSubgroup τ K β) α hα) (Subgroup.subset_closure ⟨_, rfl⟩)
  exact hle hx

theorem ggBstarElt_adjoint_of_nfDiag {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hfull : ∀ b : Fin τ.rank → Kˣ, (∀ i, b i ^ p = 1) → rootDiagUnit τ b ∈ torusGroup τ K)
    (hN : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ≠ 0)
    (hT : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ τ.rank ≤ Nat.card E →
      ∃ g : adjointGroup τ K, E.map (MulAut.conj g).toMonoidHom = TableBExc.torusPow τ K p)
    (hnf : ∀ φ : MulAut (adjointGroup τ K), φ ^ p = 1 → ∃ (a : adjointGroup τ K)
      (b : Fin τ.rank → Kˣ) (σ : K ≃+* K), σ ^ p = 1 ∧ ∀ x : adjointGroup τ K,
        (φ x : ModGL τ K) = (a : ModGL τ K) * rootDiagUnit τ b *
          Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) * (rootDiagUnit τ b)⁻¹ *
            (a : ModGL τ K)⁻¹) :
    TableBOrth.GGBstarElt p τ.rank (adjointGroup τ K) := by
  have : Fact p.Prime := ⟨hp⟩
  intro E₀ hE₀ hr _ φ hφ hfix
  obtain ⟨g, hg⟩ := hT E₀ hE₀ hr
  set V := TableBExc.torusPow τ K p with hV
  set φ' : MulAut (adjointGroup τ K) := MulAut.conj g * φ * (MulAut.conj g)⁻¹ with hφ'
  have hφ'app : ∀ x, φ' x = g * φ (g⁻¹ * x * g) * g⁻¹ := fun x => by
    simp only [hφ', MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hφapp : ∀ x, φ (g⁻¹ * x * g) = g⁻¹ * φ' x * g := fun x => by
    rw [hφ'app]
    group
  have hφ'p : φ' ^ p = 1 := by rw [hφ', conj_pow, hφ, mul_one, mul_inv_cancel]
  have hgV : ∀ e ∈ E₀, g * e * g⁻¹ ∈ V := fun e he => by
    rw [← hg]
    exact ⟨e, he, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hφ'V : ∀ v ∈ V, φ' v = v := by
    intro v hv
    rw [← hg] at hv
    obtain ⟨e, he, rfl⟩ := hv
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφ'app,
      show g⁻¹ * (g * e * g⁻¹) * g = e by group, hfix e he]
  obtain ⟨a, b, σ, hσp, haσ⟩ := hnf φ' hφ'p
  have haV : ∀ v ∈ V, (a : ModGL τ K) * v * (a : ModGL τ K)⁻¹ = v := by
    intro v hv
    have hcomm := rootDiagUnit_mul_comm_of_mem_torusGroup b
      (ExcFrames.mem_torusPow_iff_coe.mp hv).1
    have h1 := haσ v
    rw [hφ'V v hv, ExcFrames.units_map_entrywise_eq_self hσp
      (ExcFrames.mem_torusPow_iff_coe.mp hv), mul_assoc (a : ModGL τ K) (rootDiagUnit τ b),
      hcomm] at h1
    rw [show (a : ModGL τ K) * ((v : ModGL τ K) * rootDiagUnit τ b) * (rootDiagUnit τ b)⁻¹ *
      (a : ModGL τ K)⁻¹ = (a : ModGL τ K) * v * (a : ModGL τ K)⁻¹ by group] at h1
    exact h1.symm
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hdV : ∀ j : Fin τ.rank, ∃ v ∈ V,
      (v : ModGL τ K) = rootDiagUnit τ (Pi.mulSingle j ζ) := by
    intro j
    have hH := hfull (Pi.mulSingle j ζ) fun i => by
      by_cases hij : i = j
      · subst hij
        rw [Pi.mulSingle_eq_same, hζ]
      · rw [Pi.mulSingle_eq_of_ne hij, one_pow]
    refine ⟨⟨_, CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hH⟩,
      ExcFrames.mem_torusPow_iff_coe.mpr ⟨hH, ?_⟩, rfl⟩
    rw [rootDiagUnit_pow', ← Pi.mulSingle_pow, hζ, Pi.mulSingle_one, rootDiagUnit_one]
  obtain ⟨h₀, hh₀, u₀, hu₀, hau⟩ := exists_eq_mul_of_commute_mulSingle hp2 hζo a.2 fun j => by
    obtain ⟨v, hv, hveq⟩ := hdV j
    have h1 := haV v hv
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [← hveq, mul_inv_eq_iff_eq_mul]
    exact h1.symm
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hUC : posUnipotent τ K ≤ adjointGroup τ K :=
    le_sup_right.trans (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  set U : Subgroup (adjointGroup τ K) := (posUnipotent τ K).comap (adjointGroup τ K).subtype
    with hUdef
  have hHN : ∀ t ∈ torusGroup τ K, ∀ x ∈ posUnipotent τ K, t * x * t⁻¹ ∈ posUnipotent τ K :=
    fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (hTB.2.2.1 ht) x).mp hx
  have hφ'U : ∀ u ∈ U, φ' u ∈ U := by
    intro u hu
    show ((φ' u : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K
    rw [haσ u, hau]
    have hσu : Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) ∈ posUnipotent τ K :=
      entrywise_mem_rootSpan hu
    have hw := rootDiagUnit_conj_mem_posUnipotent b hσu
    have h1 : u₀ * (rootDiagUnit τ b * Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) *
        (rootDiagUnit τ b)⁻¹) * u₀⁻¹ ∈ posUnipotent τ K := mul_mem (mul_mem hu₀ hw) (inv_mem hu₀)
    have h2 := hHN h₀ hh₀ _ h1
    rw [show h₀ * u₀ * rootDiagUnit τ b * Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) *
      (rootDiagUnit τ b)⁻¹ * (h₀ * u₀)⁻¹ = h₀ * (u₀ * (rootDiagUnit τ b *
        Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * (rootDiagUnit τ b)⁻¹) * u₀⁻¹) *
          h₀⁻¹ by group]
    exact h2
  have hVU : ∀ v ∈ V, ∀ u ∈ U, v * u * v⁻¹ ∈ U := fun v hv u hu =>
    hHN _ (ExcFrames.mem_torusPow_iff_coe.mp hv).1 _ hu
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hcard := card_posUnipotent (τ := τ) (K := K)
    have hle : posUnipotent τ K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxU : (⟨x, hUC hx⟩ : adjointGroup τ K) ∈ U := hx
      rw [hbot, Subgroup.mem_bot] at hxU
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hxU
    rw [hle, Subgroup.card_bot] at hcard
    have hK2 : 1 < Nat.card K := Finite.one_lt_card
    have := Nat.one_lt_pow hN hK2
    omega
  have hU2 : IsPGroup 2 U :=
    (isPGroup_posUnipotent 2 τ).comap_of_injective _ (adjointGroup τ K).subtype_injective
  refine ⟨U.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hU2.map _, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective]
    exact hUne
  · rintro e he _ ⟨u, hu, rfl⟩
    refine ⟨g * e * g⁻¹ * u * (g * e * g⁻¹)⁻¹, hVU _ (hgV e he) u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨φ' u, hφ'U u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hφapp]


theorem nf_E6 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (φ : MulAut (adjointGroup .E6 K)) (hφ : φ ^ p = 1) :
    ∃ (a : adjointGroup .E6 K) (b : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K), σ ^ p = 1 ∧
      ∀ x : adjointGroup .E6 K, (φ x : ModGL .E6 K) = (a : ModGL .E6 K) * rootDiagUnit .E6 b *
        Units.map (entrywiseHom σ.toRingHom) (x : ModGL .E6 K) * (rootDiagUnit .E6 b)⁻¹ *
          (a : ModGL .E6 K)⁻¹ := by
  obtain ⟨Θ, -, hΘ, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  obtain ⟨-, -, hall⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, b, σ, ε, hgε⟩ := hall φ
  have hpow : Θ φ ^ p = 1 := by rw [← map_pow, hφ, map_one]
  rw [hΘ φ g b σ ε hgε] at hpow
  have h1 : σ ^ p = 1 := by
    have := congrArg Prod.fst hpow
    rwa [Prod.pow_fst, Prod.fst_one] at this
  have h2 : (Multiplicative.ofAdd (((ε : ℕ) : ZMod (exactE .E6)))) ^ p = 1 := by
    have := congrArg Prod.snd hpow
    rwa [Prod.pow_snd, Prod.snd_one] at this
  have hε : (ε : ℕ) = 0 := by
    rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h2
    have h3 : (((p * (ε : ℕ) : ℕ)) : ZMod (exactE .E6)) = 0 := by exact_mod_cast h2
    have hdvd : exactE .E6 ∣ p * (ε : ℕ) := (ZMod.natCast_eq_zero_iff _ _).mp h3
    have hdvd2 : 2 ∣ p * (ε : ℕ) := hdvd
    have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have h4 : 2 ∣ (ε : ℕ) := h2p.dvd_of_dvd_mul_left hdvd2
    have h5 : (ε : ℕ) < 2 := ε.2
    omega
  refine ⟨g, b, σ, h1, fun x => ?_⟩
  rw [hgε x, hε]
  have hQ : exactQ Tag.E6 K 0 = 1 := pow_zero _
  rw [hQ, inv_one, mul_one, mul_one]

end Diag

section RecipeE6

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggInnerDiagBound_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpq : p ∣ Nat.card K - 1) :
    GGInnerDiagBound p 6 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have := TableBExc.finite_recipeGroup .E6 K
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  exact ggInnerDiagBound_of_elt' hp
    (fun φ hφ hφp => mem_range_conj_of_mem_recipeID_E6 hp hp3 hφ hφp)
    (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (TableBOrth.ggBstarElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K).symm
      (ggBstarElt_adjoint_of_nfDiag (τ := .E6) hp hp2 hpq
        (fun b hb => TableBExc.fullp_E6 hp.one_lt hcop b hb)
        (by rw [CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E6]; norm_num)
        (TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq)
        fun φ hφ => nf_E6 hp hp2 φ hφ))

end RecipeE6

end ExcSplitL

open ExcSplitL

@[expose] def GGExcLSplitE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n - 1

section Labels


theorem largeEvenLabelAll_innerDiagBound_excLSplitE6 {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGExcLSplitE6Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hp3, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag hpn hn
  subst htag
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨6, TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, ggInnerDiagBound_E6 hp hp2 hp3 hpq⟩

theorem ggBstarInnerDiagLInputOn_excLSplitE6 (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGExcLSplitE6Label p lab :=
  ggBstarInnerDiagLInputOn_of_labels' ggLNoncyclicInput_holds fun _ _ hp hlab h =>
    largeEvenLabelAll_innerDiagBound_excLSplitE6 hp hlab h.2

end Labels

end CFSG.StandardType

end
