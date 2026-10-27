module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE6
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRank
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankGeneral
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Frames
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

namespace ExcFieldAutCentRankE6

section Assembly


theorem ggPsiInnerDiag_inv {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*} [Group G]
    {ψ : U →* G} {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (h : GGPsiInnerDiag Δ ψ c) : GGPsiInnerDiag Δ ψ c⁻¹ := by
  obtain ⟨g, hg, hall⟩ := h
  have hg' : c * g⁻¹ * c⁻¹ ∈ ψ.range :=
    (Subgroup.mem_normalizer_iff.mp hc _).mp (ψ.range.inv_mem hg)
  refine ⟨c * g⁻¹ * c⁻¹, hg', fun γ hγ => ?_⟩
  obtain ⟨t, ht, htz⟩ := hall γ hγ
  refine ⟨t⁻¹, Subgroup.inv_mem _ ht, fun z hz => ?_⟩
  have hz' : t⁻¹ * z * t ∈ Δ.rootGroup γ := by
    have htN : t ∈ Subgroup.normalizer (Δ.rootGroup γ : Set U) := by
      simp only [ggTorus, Subgroup.mem_iInf] at ht
      exact ht γ hγ
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) z).mp hz
  have h4 : (c * g) * ψ z * (c * g)⁻¹ = ψ (t⁻¹ * z * t) := by
    have h1 := htz _ hz'
    have hz'' : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
    rw [hz''] at h1
    calc (c * g) * ψ z * (c * g)⁻¹
        = (c * g) * ((c * g)⁻¹ * ψ (t⁻¹ * z * t) * (c * g)) * (c * g)⁻¹ := by rw [h1]
      _ = ψ (t⁻¹ * z * t) := by group
  have hA : (c⁻¹ * (c * g⁻¹ * c⁻¹))⁻¹ * ψ z * (c⁻¹ * (c * g⁻¹ * c⁻¹)) =
      (c * g) * ψ z * (c * g)⁻¹ := by
    congr 2 <;> group
  rw [hA, h4]
  simp only [inv_inv]

theorem ggPsiInnerDiag_of_induced_conj_diag {G : Type} [Group G] {f : ℕ}
    {ψ : (ggU .E6 0 f).K →* G}
    {χ : adjointGroup .E6 (GaloisField 2 f) →* G} (hχ : Function.Injective χ)
    (hval : ∀ u, ψ u = χ (e6Isogeny (GaloisField 2 f) u))
    (hker : ψ.ker ≤ Subgroup.center (ggU .E6 0 f).K) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    {g : adjointGroup .E6 (GaloisField 2 f)} {a : Fin Tag.E6.rank → (GaloisField 2 f)ˣ}
    (hact : ∀ u : adjointGroup .E6 (GaloisField 2 f),
      c⁻¹ * χ u * c = χ ((MulAut.conj g * rootDiagAut .E6 (GaloisField 2 f) a) u)) :
    GGPsiInnerDiag (ggU .E6 0 f).D ψ c := by
  classical
  have hodd : Odd (Nat.card (e6Isogeny (GaloisField 2 f)).ker) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker
      (GaloisField 2 f) (p := 2)
    exact Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  have hinv : ∀ δ ∈ (e6Datum (GaloisField 2 f)).roots,
      ∀ z ∈ (e6Datum (GaloisField 2 f)).rootGroup δ, z * z = 1 := by
    intro δ _ z hz
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 f)).mp hz
    rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
  obtain ⟨a₀, ha₀⟩ := e6Isogeny_surjective (GaloisField 2 f) g
  have ha₀' : ((e6Isogeny (GaloisField 2 f) a₀ : adjointGroup .E6 (GaloisField 2 f)) :
      ModGL .E6 (GaloisField 2 f)) = (g : ModGL .E6 (GaloisField 2 f)) := by rw [ha₀]
  refine MpStdE6.ggPsiInnerDiag_of_conj_diag (e6Datum (GaloisField 2 f))
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center
      (GaloisField 2 f)) hodd hinv a (fun δ hδ => RootDetectExc.hdiag_E6
        (GaloisField 2 f) δ hδ a) hc a₀ ?_
  intro y₁ y₂ h12
  have h1 : χ (e6Isogeny (GaloisField 2 f) y₂) =
      χ ((MulAut.conj g * rootDiagAut .E6 (GaloisField 2 f) a)
        (e6Isogeny (GaloisField 2 f) y₁)) := by
    calc χ (e6Isogeny (GaloisField 2 f) y₂) = ψ y₂ := (hval y₂).symm
      _ = c⁻¹ * ψ y₁ * c := h12
      _ = c⁻¹ * χ (e6Isogeny (GaloisField 2 f) y₁) * c := by rw [hval y₁]
      _ = χ ((MulAut.conj g * rootDiagAut .E6 (GaloisField 2 f) a)
            (e6Isogeny (GaloisField 2 f) y₁)) := hact _
  have h2 : (e6Isogeny (GaloisField 2 f) y₂ : adjointGroup .E6 (GaloisField 2 f)) =
      (MulAut.conj g * rootDiagAut .E6 (GaloisField 2 f) a)
        (e6Isogeny (GaloisField 2 f) y₁) := hχ h1
  simp only [h2, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_rootDiagAut, ha₀']
  group

private theorem exists_centralizing_elemAbelian_field_E6
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : ↥(e6Data_valid.minGroup (GaloisField 2 f)) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (ggU .E6 n f).D .E6 n f ψ)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : orderOf y = p)
    (hdf : GGPsiDiagField (ggU .E6 n f).D ψ y)
    (hni : ¬ GGPsiInnerDiag (ggU .E6 n f).D ψ y) :
    ∃ E₀ : Subgroup G, E₀ ≤ G₀ ∧ IsElemAbelian p E₀ ∧ (∀ x ∈ E₀, y * x = x * y) ∧
      Nat.card Bs ≤ p * Nat.card E₀ := by
  classical
  have hpp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpres : GGPresentsG0 G₀ (ggU .E6 n f).D .E6 n f ψ := hS.presents
  have hrange : ψ.range = G₀ := hS.range_eq
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hker : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 f)) :=
    hpres.2.1.2
  have hperf : commutator ↥ψ.range = ⊤ := by rw [hrange]; exact hpres.2.2.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]; exact hS.centralizer_eq_bot
  have hf0 : f ≠ 0 := by omega
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  have hkerEq : ψ.ker = Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 f)) := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
    rw [hCψ, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχ, hval⟩ :=
    ExcNonsplit.exists_factor_e6Isogeny (k := GaloisField 2 f) (ψ := ψ) hkerEq
  have hχrange : χ.range = G₀ := by
    rw [← hrange]
    ext u
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨u, rfl⟩ := e6Isogeny_surjective (GaloisField 2 f) c
      exact ⟨u, (hval u).symm⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e6Isogeny (GaloisField 2 f) u, hval u⟩
  have hCχ : Subgroup.centralizer (χ.range : Set G) = ⊥ := by
    rw [hχrange]; exact hS.centralizer_eq_bot
  have hyN : y ∈ Subgroup.normalizer (χ.range : Set G) := by rw [hχrange]; exact hyM
  obtain ⟨α, hα⟩ := OutdiagModel.exists_induces hχ hyN
  have hαk : ∀ (k : ℕ) u, χ ((α ^ k) u) = y ^ k * χ u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ← hα ((α ^ k) u), ih u, pow_succ]
      group
  have hyp1 : y ^ p = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hαp : α ^ p = 1 := by
    refine MulEquiv.ext fun u => hχ ?_
    rw [hαk, hyp1]
    simp
  have hnin : ∀ h : adjointGroup .E6 (GaloisField 2 f), α ≠ MulAut.conj h := by
    intro h hh
    apply hni
    refine ggPsiInnerDiag_of_mem_range _ ?_
    have hc : (χ h)⁻¹ * y ∈ Subgroup.centralizer (G₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [← hrange] at hx
      obtain ⟨u, rfl⟩ := hx
      have hv : ψ u = χ (e6Isogeny (GaloisField 2 f) u) := (hval u).symm
      have e : y * ψ u * y⁻¹ = χ h * ψ u * (χ h)⁻¹ := by
        rw [hv, hα (e6Isogeny (GaloisField 2 f) u), hh]
        simp [MulAut.conj_apply, map_mul, map_inv]
      calc ψ u * ((χ h)⁻¹ * y) = (χ h)⁻¹ * (χ h * ψ u * (χ h)⁻¹) * y := by group
        _ = (χ h)⁻¹ * (y * ψ u * y⁻¹) * y := by rw [e]
        _ = (χ h)⁻¹ * y * ψ u := by group
    rw [hS.centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hc
    rw [← hc]
    obtain ⟨a, rfl⟩ := e6Isogeny_surjective (GaloisField 2 f) h
    exact ⟨a, (hval a).symm⟩
  have hyNψ : y ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hyM
  have hnd : ∀ (g : adjointGroup .E6 (GaloisField 2 f))
      (a : Fin Tag.E6.rank → (GaloisField 2 f)ˣ),
      α ≠ MulAut.conj g * rootDiagAut .E6 (GaloisField 2 f) a := by
    intro g a hga
    apply hni
    have hb : GGPsiInnerDiag (ggU .E6 n f).D ψ y⁻¹ :=
      ggPsiInnerDiag_of_induced_conj_diag hχ (fun u => (hval u).symm) hker
        (Subgroup.inv_mem _ hyNψ) (g := g) (a := a) (fun u => by rw [inv_inv, hα u, hga])
    have hinv := ggPsiInnerDiag_inv (ggU .E6 n f).D (Subgroup.inv_mem _ hyNψ) hb
    simpa using hinv
  obtain ⟨Θ, -, hΘ, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) (GaloisField 2 f)
  obtain ⟨d, T, r, j, ψ', hd, hTord, hcard, hT, hTjord, hαβ, hψr, hΘα, hψα⟩ :=
    CFSG.RankThree.Chevalley.exists_conj_entrywise_of_not_innerDiag_of_quotient .E6 (Or.inl rfl) hf
      (GaloisField 2 f) hK hpp hp2 Θ hΘ α hαp hnd
  set σ : GaloisField 2 f ≃+* GaloisField 2 f := T ^ j with hσ
  have hσp1 : σ ^ p = 1 := by
    rw [hσ]
    rw [← hTjord]
    exact pow_orderOf_eq_one (T ^ j)
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 : orderOf σ = p := by rw [hσ]; exact hTjord
    rw [h1, orderOf_one] at h2
    have hp2le : 2 ≤ p := hpp.two_le
    omega
  set e : ℕ := orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) with hedef
  haveI : Finite (fixSubfield σ) :=
    Finite.of_injective (Subtype.val : fixSubfield σ → GaloisField 2 f) Subtype.val_injective
  haveI : CharP (fixSubfield σ) 2 := Subfield.charP (fixSubfield σ) 2
  have hefix : orderOf ((Nat.card (fixSubfield σ) : ℕ) : ZMod p) = e :=
    orderOf_card_fixSubfield_eq hpp hp2 σ hσ1 hσp1
  obtain ⟨E, hE, hEcard⟩ := exists_E6 (K := fixSubfield σ) (p := p) (e := e) hpp hp2 hefix
  let Ead : Subgroup (adjointGroup .E6 (GaloisField 2 f)) :=
    E.map (fixedFieldInclusion (τ := .E6) σ)
  have hEad : IsElemAbelian p Ead := hE.map _
  have hEadcard : Nat.card Ead = Nat.card E :=
    Subgroup.card_map_of_injective (fixedFieldInclusion_injective σ)
  have hEadfix : ∀ u ∈ Ead, entrywiseAdjointAut .E6 σ u = u := by
    rintro _ ⟨u, -, rfl⟩
    exact entrywise_fixedFieldInclusion σ u
  let E₁ : Subgroup (adjointGroup .E6 (GaloisField 2 f)) := Ead.map ψ'⁻¹.toMonoidHom
  have hE₁ : IsElemAbelian p E₁ := hEad.map ψ'⁻¹.toMonoidHom
  have hE₁card : Nat.card E₁ = Nat.card Ead :=
    Subgroup.card_map_of_injective ψ'⁻¹.injective
  have hE₁fix : ∀ u ∈ E₁, α u = u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ψ'.injective ?_
    change ψ' (α (ψ'⁻¹ v)) = ψ' (ψ'⁻¹ v)
    have hδ : ψ' * α * ψ'⁻¹ = entrywiseAdjointAut .E6 σ := hψα
    have h2 : ψ' (α (ψ'⁻¹ v)) = v := by
      have h3 : (ψ' * α * ψ'⁻¹) v = v := by rw [hδ, hEadfix v hv]
      simpa [MulAut.mul_apply] using h3
    rw [h2, MulAut.apply_inv_self]
  let E₀ : Subgroup G := E₁.map χ
  have hE₀ : IsElemAbelian p E₀ := hE₁.map χ
  have hE₀card : Nat.card E₀ = Nat.card E₁ := Subgroup.card_map_of_injective hχ
  have hE₀le : E₀ ≤ G₀ := by
    rw [← hχrange]
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  have hE₀comm : ∀ x ∈ E₀, y * x = x * y := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 := hα v
    rw [hE₁fix v hv] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hBsbound : Nat.card Bs ≤ p ^ degCount .E6 e := by
    by_cases hcase : p = 3 ∧ 3 ∣ Nat.card (GaloisField 2 f) - 1
    ·
      obtain ⟨rfl, h3⟩ := hcase
      obtain ⟨χ₁, hχ₁, hχ₁range, hind⟩ := OutdiagE6.exists_model hS
      have hC₁ : Subgroup.centralizer (χ₁.range : Set G) = ⊥ := by
        rw [hχ₁range]; exact hS.centralizer_eq_bot
      have hBsN' : Bs ≤ Subgroup.normalizer (G₀ : Set G) := hS.bstar_le
      have hBsN'' : Bs ≤ Subgroup.normalizer (χ₁.range : Set G) := by
        rw [hχ₁range]; exact hBsN'
      let S : Subgroup (MulAut (adjointGroup .E6 (GaloisField 2 f))) :=
        OutdiagModel.inducedSub χ₁ Bs
      have hS3 : IsElemAbelian 3 S := OutdiagModel.isElemAbelian_inducedSub hχ₁ hS.elem
      have hScard : Nat.card S = Nat.card Bs :=
        OutdiagModel.card_inducedSub hχ₁ hC₁ hBsN''
      have hSI : S ≤ (TableBExc.E6Three.hatAut .E6 (GaloisField 2 f)).range := by
        rintro α ⟨b, hb, hbα⟩
        obtain ⟨α', hα'D, hα'⟩ := hind b (hBsN' hb) (hS.innerDiag b hb)
        rw [OutdiagModel.Induces.unique hχ₁ hbα hα']
        rw [NoOffE6Three.hatAut_range_eq_sup]
        simpa [LayerSixE.inndiagAut] using hα'D
      have h6 := (TableBExc.E6Three.card_le_and_normalizes_of_le_hatAut (K := GaloisField 2 f)
        h3 hS3 hSI).1
      have he1 : e = 1 := by
        have hmod : (1 : ℕ) ≡ Nat.card (GaloisField 2 f) [MOD 3] :=
          (Nat.modEq_iff_dvd' Nat.card_pos).2 h3
        have hcast : ((Nat.card (GaloisField 2 f) : ℕ) : ZMod 3) = 1 := by
          rw [show (1 : ZMod 3) = ((1 : ℕ) : ZMod 3) by norm_num]
          exact (ZMod.natCast_eq_natCast_iff _ _ 3).2 hmod.symm
        rw [hedef, hcast, orderOf_one]
      rw [hScard] at h6
      rw [he1]
      exact h6
    ·
      have hp3 : (p ≠ 3 ∨ ¬ 3 ∣ Nat.card (GaloisField 2 f) - 1) := by
        by_contra h
        push Not at h
        exact hcase h
      have hBsr : Bs ≤ χ.range := by
        intro b hb
        have hbN : b ∈ Subgroup.normalizer (ψ.range : Set G) := by
          rw [hrange]; exact hS.bstar_le hb
        have hbp : b ^ p = 1 := hS.elem.2 b hb
        have hbm : b ∈ ψ.range :=
          ExcFrames.mem_range_of_innerDiag_E6 hpp hp3 ψ hker hperf hCψ hbN hbp (hS.innerDiag b hb)
        rw [hχrange]
        rwa [hrange] at hbm
      obtain ⟨hBel, hBcard⟩ :=
        ExcFieldAutCentRankF4.pullback_elemAbelian χ hχ p Bs hBsr hS.elem
      have hB := rankLE_E6 (K := GaloisField 2 f) (p := p) (e := e) hpp hp2 rfl
        (Bs.comap χ) hBel
      rwa [hBcard] at hB
  by_cases h0 : degCount .E6 e = 0
  · have hBs1 : Nat.card Bs ≤ 1 := by simpa [h0] using hBsbound
    have hBspos : 0 < Nat.card Bs := Nat.card_pos
    have hBsone : Nat.card Bs = 1 := by omega
    refine ⟨E₀, hE₀le, hE₀, hE₀comm, ?_⟩
    rw [hBsone]
    have hEpos : 0 < Nat.card E₀ := Nat.card_pos
    calc 1 ≤ p := hpp.one_lt.le
      _ ≤ p * Nat.card E₀ := Nat.le_mul_of_pos_right p hEpos
  · have hm : 1 ≤ degCount .E6 e := Nat.pos_of_ne_zero h0
    have hpow : p ^ degCount .E6 e = p * p ^ (degCount .E6 e - 1) := by
      conv_lhs => rw [show degCount .E6 e = (degCount .E6 e - 1) + 1 by omega]
      rw [pow_succ]
      ring
    refine ⟨E₀, hE₀le, hE₀, hE₀comm, ?_⟩
    calc Nat.card Bs ≤ p ^ degCount .E6 e := hBsbound
      _ = p * p ^ (degCount .E6 e - 1) := hpow
      _ ≤ p * Nat.card E := Nat.mul_le_mul_left p hEcard
      _ = p * Nat.card E₀ := by rw [hE₀card, hE₁card, hEadcard]

end Assembly

end ExcFieldAutCentRankE6

section Final


theorem ggExcFieldAutCentRank_E6 : GGExcFieldAutCentRank .E6 := by
  intro G _ _ p Bs G₀ n f ψ hS y hyM hyp hdf hni
  exact ExcFieldAutCentRankE6.exists_centralizing_elemAbelian_field_E6 hS hyM hyp hdf hni

end Final

end CFSG.StandardType
