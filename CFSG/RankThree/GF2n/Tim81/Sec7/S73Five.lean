module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split
public import CFSG.RankThree.GF2n.Tim81.Sec7.S71TI
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Base
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Images
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Setup
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Odd
import CFSG.Timmesfeld.Bridge.RootStructR2ManySection
import CFSG.Quasithin.Vol2.KGFactInspPerf
import CFSG.Timmesfeld.Bridge.SchurNarrowTransport

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open CFSG.RankThree.GF2n.Tim81.Sec7 (rOf oOf yOf)
open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.RootMany
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem IsSUImage.toTop {K : Type} [Group K] {X : Subgroup K} {Δ : Set (Subgroup K)} {f m : ℕ}
    {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm) :
    IsSUImage (⊤ : Subgroup ↥X) ((fun D : Subgroup K => D.subgroupOf X) '' Δ) f m hf hm := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  let Ψ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* ↥X :=
    Φ.codRestrict X fun x => hrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · refine eq_top_iff.mpr ?_
    intro x hx
    have hx' : (x : K) ∈ Φ.range := hrange ▸ x.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hx'
    exact ⟨y, Subtype.ext hy⟩
  · intro U
    constructor
    · rintro ⟨D, hD, rfl⟩
      obtain ⟨x, rfl⟩ := (hΔ D).mp hD
      refine ⟨x, ?_⟩
      rw [CFSG.map_codRestrict_eq_subgroupOf]
    · rintro ⟨x, rfl⟩
      refine ⟨(conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) m).rootGroup
        (unitaryLongRoot m hm)) x).map Φ, (hΔ _).mpr ⟨x, rfl⟩, ?_⟩
      rw [CFSG.map_codRestrict_eq_subgroupOf]

theorem IsSUImage.congr_rank {K : Type} [Group K] {X : Subgroup K} {Δ : Set (Subgroup K)}
    {f m m' : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm) (e : m = m')
    (hm' : 2 ≤ m') : IsSUImage X Δ f m' hf hm' := by
  subst e
  exact hX

section SecModLemmas

variable {R : Type*} [Group R] (Esec Asec Bsec B₁ B₂ : Subgroup R) [Asec.Normal]

private theorem secSub_mono [Fact (CFSG.Timmesfeld.Bridge.RootMany.IsElemSection Esec Asec)]
    (h : B₁ ≤ B₂) : secSub Esec Asec B₁ ≤ secSub Esec Asec B₂ := by
  intro v hv
  obtain ⟨e, he, rfl⟩ := (mem_secSub Esec Asec).mp hv
  exact (mem_secSub Esec Asec).mpr ⟨e, h he, rfl⟩

private theorem secSub_inf [Fact (CFSG.Timmesfeld.Bridge.RootMany.IsElemSection Esec Asec)]
    (hA₂ : Asec ≤ B₂) :
    secSub Esec Asec B₁ ⊓ secSub Esec Asec B₂ = secSub Esec Asec (B₁ ⊓ B₂) := by
  refine le_antisymm ?_
    (le_inf (secSub_mono Esec Asec (B₁ ⊓ B₂) B₁ inf_le_left)
      (secSub_mono Esec Asec (B₁ ⊓ B₂) B₂ inf_le_right))
  intro v hv
  obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.mp hv
  obtain ⟨e₁, he₁, rfl⟩ := (mem_secSub Esec Asec).mp hv₁
  obtain ⟨e₂, he₂, heq⟩ := (mem_secSub Esec Asec).mp hv₂
  have hmem : (e₂ : R)⁻¹ * e₁ ∈ Asec := (secMk_eq_secMk_iff Esec Asec e₂ e₁).mp heq
  have he₁' : (e₁ : R) ∈ B₂ := by
    have h := B₂.mul_mem he₂ (hA₂ hmem)
    simpa using h
  exact (mem_secSub Esec Asec).mpr ⟨e₁, ⟨he₁, he₁'⟩, rfl⟩

private theorem secSub_eq_bot_iff [Fact (CFSG.Timmesfeld.Bridge.RootMany.IsElemSection Esec Asec)]
    (hAB : Asec ≤ Bsec) (hBE : Bsec ≤ Esec) :
    secSub Esec Asec Bsec = ⊥ ↔ Bsec = Asec := by
  constructor
  · intro h
    refine le_antisymm ?_ hAB
    intro x hx
    have hmem : secMk Esec Asec ⟨x, hBE hx⟩ ∈ secSub Esec Asec Bsec :=
      (mem_secSub Esec Asec).mpr ⟨⟨x, hBE hx⟩, hx, rfl⟩
    rw [h, Submodule.mem_bot, secMk_eq_zero_iff] at hmem
    exact hmem
  · intro h
    rw [h, eq_bot_iff]
    intro v hv
    obtain ⟨e, he, rfl⟩ := (mem_secSub Esec Asec).mp hv
    rw [Submodule.mem_bot, secMk_eq_zero_iff]
    exact he

private theorem secSub_eq_top_iff [Fact (CFSG.Timmesfeld.Bridge.RootMany.IsElemSection Esec Asec)]
    (hAB : Asec ≤ Bsec) (hBE : Bsec ≤ Esec) :
    secSub Esec Asec Bsec = ⊤ ↔ Bsec = Esec := by
  constructor
  · intro h
    refine le_antisymm hBE ?_
    intro x hx
    have hmem : secMk Esec Asec ⟨x, hx⟩ ∈ secSub Esec Asec Bsec := by
      rw [h]; exact Submodule.mem_top
    exact (secMk_mem_secSub_iff Esec Asec hAB ⟨x, hx⟩).mp hmem
  · intro h
    rw [h, eq_top_iff]
    intro v _
    obtain ⟨e, rfl⟩ := secMk_surjective Esec Asec v
    exact (mem_secSub Esec Asec).mpr ⟨e, e.2, rfl⟩

end SecModLemmas

private theorem span_secRep_eq_secSub_commutator {R : Type*} [Group R] [Finite R]
    (Esec Asec C : Subgroup R) [Asec.Normal] [Esec.Normal]
    [Fact (CFSG.Timmesfeld.Bridge.RootMany.IsElemSection Esec Asec)]
    (hCN : C ≤ Subgroup.normalizer (Esec : Set R)) :
    Submodule.span (ZMod 2) {u : CFSG.Timmesfeld.Bridge.RootMany.SecMod Esec Asec |
        ∃ c ∈ C, ∃ w, u = secRep Esec Asec c w - w} =
      secSub Esec Asec ⁅C, Esec⁆ := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro u ⟨c, hc, w, rfl⟩
    obtain ⟨e, rfl⟩ := secMk_surjective Esec Asec w
    rw [secRep_mk, sub_eq_add_neg, ← secMk_inv, ← secMk_mul]
    refine (mem_secSub Esec Asec).mpr ⟨secConj Esec c e * e⁻¹, ?_, rfl⟩
    have hmem : ((secConj Esec c e * e⁻¹ : ↥Esec) : R) ∈ ⁅C, Esec⁆ := by
      have h := Subgroup.commutator_mem_commutator (H₁ := C) (H₂ := Esec) hc e.2
      have heq : ((secConj Esec c e * e⁻¹ : ↥Esec) : R) = ⁅c, (e : R)⁆ := by
        simp [secConj, commutatorElement_def]
      rwa [heq]
    exact hmem
  · intro v hv
    obtain ⟨e, he, rfl⟩ := (mem_secSub Esec Asec).mp hv
    have hle : ⁅C, Esec⁆ ≤ secPre Esec Asec
        (Submodule.span (ZMod 2) {u : CFSG.Timmesfeld.Bridge.RootMany.SecMod Esec Asec |
          ∃ c ∈ C, ∃ w, u = secRep Esec Asec c w - w}) := by
      rw [Subgroup.commutator_le]
      intro c hc e' he'
      have hcE : c * e' * c⁻¹ ∈ Esec :=
        (Subgroup.mem_normalizer_iff.mp (hCN hc) e').mp he'
      have hmemE : ⁅c, e'⁆ ∈ Esec :=
        Esec.mul_mem hcE (Esec.inv_mem he')
      refine (mem_secPre Esec Asec).mpr ⟨hmemE, ?_⟩
      have hgen : secMk Esec Asec ⟨⁅c, e'⁆, hmemE⟩ =
          secRep Esec Asec c (secMk Esec Asec ⟨e', he'⟩) -
            secMk Esec Asec ⟨e', he'⟩ := by
        rw [secRep_mk, sub_eq_add_neg, ← secMk_inv, ← secMk_mul]
        congr 1
      rw [hgen]
      exact Submodule.subset_span ⟨c, hc, _, rfl⟩
    have h := (mem_secPre Esec Asec).mp (hle he) |>.2
    simpa using h

section RepresentationLemmas

variable {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]

private theorem submodule_eq_bot_or_top_of_isIrreducible {ρ : Representation (ZMod 2) K W}
    (hρ : ρ.IsIrreducible) (U : Submodule (ZMod 2) W)
    (hU : ∀ g, U.map (ρ g) ≤ U) : U = ⊥ ∨ U = ⊤ := by
  let X : Subrepresentation ρ :=
    { toSubmodule := U
      apply_mem_toSubmodule := fun g v hv =>
        (hU g) (Submodule.mem_map.mpr ⟨v, hv, rfl⟩) }
  rcases hρ.eq_bot_or_eq_top X with h | h
  · left
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [show (⊥ : Subrepresentation ρ).toSubmodule = (⊥ : Submodule (ZMod 2) W) from rfl] at h'
    simpa [X] using h'
  · right
    have h' := congrArg Subrepresentation.toSubmodule h
    rw [show (⊤ : Subrepresentation ρ).toSubmodule = (⊤ : Submodule (ZMod 2) W) from rfl] at h'
    simpa [X] using h'

private theorem card_lt_of_submodule_ne_top [Finite W] {U : Submodule (ZMod 2) W}
    (hU : U ≠ ⊤) : Nat.card ↥U < Nat.card W := by
  have h : (↑U : Set W) ⊂ Set.univ := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨Set.subset_univ _, by simpa using hU⟩
  simpa using Set.Finite.card_lt_card (Set.toFinite (Set.univ : Set W)) h

private theorem card_quotient_lt_of_ne_bot [Finite W] {U : Submodule (ZMod 2) W}
    (hU : U ≠ ⊥) : Nat.card (W ⧸ U) < Nat.card W := by
  have hne : ∃ x : W, x ∈ U ∧ x ≠ 0 := by
    simpa [Submodule.eq_bot_iff] using hU
  obtain ⟨x, hx, hx0⟩ := hne
  haveI : Nontrivial ↥U := ⟨⟨x, hx⟩, ⟨0, U.zero_mem⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  haveI : Finite ↥U := Subtype.finite
  have h1 : 1 < Nat.card ↥U := Finite.one_lt_card
  have h2 := Submodule.card_eq_card_quotient_mul_card U
  have h3 : Nat.card (W ⧸ U) < Nat.card (W ⧸ U) * Nat.card ↥U :=
    (Nat.lt_mul_iff_one_lt_right Nat.card_pos).2 h1
  simpa [h2, mul_comm] using h3

end RepresentationLemmas

private theorem exists_moved_vector {K W : Type*} [Group K] [AddCommGroup W]
    [Module (ZMod 2) W] (σ : Representation (ZMod 2) K W)
    (hσ : ∃ g, σ g ≠ 1) : ∃ x ∈ (⊤ : Subgroup K), ∃ w, σ x w ≠ w := by
  obtain ⟨x, hx⟩ := hσ
  refine ⟨x, Subgroup.mem_top x, ?_⟩
  by_contra h
  push Not at h
  exact hx (LinearMap.ext h)

private theorem submodule_dichotomy_of_isIrreducible {K W : Type*} [Group K]
    [AddCommGroup W] [Module (ZMod 2) W] {σ : Representation (ZMod 2) K W}
    (hσ : σ.IsIrreducible) :
    ∀ V : Submodule (ZMod 2) W, (∀ x ∈ (⊤ : Subgroup K), V.map (σ x) ≤ V) →
      V = ⊥ ∨ V = ⊤ :=
  fun V hV => submodule_eq_bot_or_top_of_isIrreducible hσ V (fun g => hV g (Subgroup.mem_top g))

theorem SU3ModuleBound.false_of_invariant_submodule (hSU3 : SU3ModuleBound) {K : Type}
    [Group K] [Finite K] (Δ : Set (Subgroup K)) (f : ℕ) (hf : 1 ≤ f) (hf2 : 2 ≤ f)
    (hX : IsSUImage (⊤ : Subgroup K) Δ f 3 hf (Nat.le_succ 2))
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) K W) (hnt : ∃ x, ∃ w, ρ x w ≠ w)
    (hperf : commutator K = ⊤) {U : Submodule (ZMod 2) W}
    (hU : ∀ g, U.map (ρ g) ≤ U) (hUbot : U ≠ ⊥) (hUtop : U ≠ ⊤)
    (hcard : Nat.card W = (2 ^ f) ^ 6) : False := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hU' : ∀ g v, v ∈ U → ρ g v ∈ U := fun g v hv =>
    (hU g) (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
  let Xs : Subrepresentation ρ := { toSubmodule := U, apply_mem_toSubmodule := hU' }
  have hcardU : Nat.card ↥U < Nat.card W := card_lt_of_submodule_ne_top hUtop
  have hcardQ : Nat.card (W ⧸ U) < Nat.card W := card_quotient_lt_of_ne_bot hUbot
  have hcard' : Nat.card W = (2 ^ f) ^ 6 := hcard
  have hntTop : ∃ x ∈ (⊤ : Subgroup K), ∃ w, ρ x w ≠ w := by
    obtain ⟨x, w, hw⟩ := hnt
    exact ⟨x, Subgroup.mem_top x, w, hw⟩
  have hrestrict : Xs.toRepresentation = 1 := by
    by_contra hne
    have hex : ∃ g, Xs.toRepresentation g ≠ 1 := by
      by_contra h
      exact hne (MonoidHom.ext (fun x => by
        have hx := not_exists.mp h x
        simpa using not_not.mp hx))
    obtain ⟨Y, i1, i2, i3, σ, hσirr, hσnt, hcardY⟩ :=
      exists_irreducible_subquotient_of_perfect hperf _ Xs.toRepresentation rfl hex
    have hirrσ := submodule_dichotomy_of_isIrreducible hσirr
    have hσntTop := exists_moved_vector σ hσnt
    have hle := hSU3 K (⊤ : Subgroup K) Δ f hf hf2 hX Y σ hσntTop hirrσ
    have hle' : (2 ^ f) ^ 6 ≤ Nat.card ↥U := le_trans hle (by simpa [Xs] using hcardY)
    omega
  have hquotient : Xs.quotient = 1 := by
    by_contra hne
    have hex : ∃ g, Xs.quotient g ≠ 1 := by
      by_contra h
      exact hne (MonoidHom.ext (fun x => by
        have hx := not_exists.mp h x
        simpa using not_not.mp hx))
    obtain ⟨Y, i1, i2, i3, σ, hσirr, hσnt, hcardY⟩ :=
      exists_irreducible_subquotient_of_perfect hperf _ Xs.quotient rfl hex
    have hirrσ := submodule_dichotomy_of_isIrreducible hσirr
    have hσntTop := exists_moved_vector σ hσnt
    have hle := hSU3 K (⊤ : Subgroup K) Δ f hf hf2 hX Y σ hσntTop hirrσ
    have hle' : (2 ^ f) ^ 6 ≤ Nat.card (W ⧸ U) :=
      le_trans hle (by simpa [Xs] using hcardY)
    omega
  have hfix : ∀ g, ∀ x ∈ U, ρ g x = x := by
    intro g x hx
    have h1 : Xs.toRepresentation g = 1 := DFunLike.congr_fun hrestrict g
    have h := congrArg (fun f : U →ₗ[ZMod 2] U => f ⟨x, hx⟩) h1
    exact (Subrepresentation.toRepresentation_apply_coe).mp h
  have hquot : ∀ g, ∀ u : W, ρ g u - u ∈ U := by
    intro g u
    have h1 : Xs.quotient g = 1 := DFunLike.congr_fun hquotient g
    have h := congrArg (fun f : (W ⧸ U) →ₗ[ZMod 2] (W ⧸ U) =>
      f (Submodule.Quotient.mk u)) h1
    have h2 : (Xs.quotient g) (Submodule.Quotient.mk (p := U) u) =
        (Submodule.Quotient.mk (p := U) ((ρ g) u) : W ⧸ U) :=
      Subrepresentation.quotient_apply_mk Xs g u
    rw [h2] at h
    have h' : (Submodule.Quotient.mk (p := U) (ρ g u) : W ⧸ U) =
        (Submodule.Quotient.mk (p := U) u : W ⧸ U) := by
      simpa using h
    exact (Submodule.Quotient.eq U).mp h'
  obtain ⟨x, w, hw⟩ := hnt
  have h1 := eq_one_of_trivial_of_perfect hperf ρ U hfix hquot x
  rw [h1] at hw
  exact hw (by simp)

theorem r0Of_le_M (hS : Sec6Hyp M V) (X : Subgroup G) : r0Of M V X ≤ M := by
  unfold r0Of
  exact iSup₂_le fun C hC => (hS.sec5.le_M_of_mem_sigmaSet hC.1).1

noncomputable def r0BarMap (hS : Sec6Hyp M V) (A B : Subgroup G) :
    ↥(r0Of M V (A ⊔ B)) →* ↥(imgQ M (r0Of M V (A ⊔ B))) :=
  ((QuotientGroup.mk' (pCore 2 ↥M)).comp
    (Subgroup.inclusion (r0Of_le_M hS (A ⊔ B)))).codRestrict _
    fun r => mk_mem_imgQ (U := r0Of M V (A ⊔ B))
      (x := Subgroup.inclusion (r0Of_le_M hS (A ⊔ B)) r) r.2

theorem r0BarMap_apply (hS : Sec6Hyp M V) (A B : Subgroup G)
    (r : ↥(r0Of M V (A ⊔ B))) :
    ((r0BarMap hS A B r : ↥(imgQ M (r0Of M V (A ⊔ B)))) : MBar M) =
      QuotientGroup.mk' (pCore 2 ↥M) ⟨(r : G), r0Of_le_M hS (A ⊔ B) r.2⟩ := by
  rw [r0BarMap, MonoidHom.codRestrict_apply]
  rfl

theorem r0BarMap_surjective (hS : Sec6Hyp M V) (A B : Subgroup G) :
    Function.Surjective (r0BarMap hS A B) := by
  intro z
  obtain ⟨x, hx, hxz⟩ := mem_imgQ_iff.mp z.2
  refine ⟨⟨(x : G), hx⟩, ?_⟩
  have h1 : ((r0BarMap hS A B ⟨(x : G), hx⟩ : ↥(imgQ M (r0Of M V (A ⊔ B)))) : MBar M) =
      QuotientGroup.mk' (pCore 2 ↥M) x := by
    rw [r0BarMap_apply]
  exact Subtype.ext (h1.trans hxz)

private theorem r0BarMap_ker (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    (hS7 : p0Of M V (A ⊔ B) ≤ r0Of M V (A ⊔ B)) :
    (r0BarMap hS A B).ker = (p0Of M V (A ⊔ B)).subgroupOf (r0Of M V (A ⊔ B)) := by
  ext z
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hz
    have hz' : QuotientGroup.mk' (pCore 2 ↥M) ⟨(z : G), r0Of_le_M hS (A ⊔ B) z.2⟩ = 1 := by
      rw [← r0BarMap_apply hS A B z]
      exact congrArg Subtype.val hz
    have hzP : (z : G) ∈ Pc M V :=
      (hS.mk_eq_one_iff ⟨(z : G), r0Of_le_M hS (A ⊔ B) z.2⟩).mp hz'
    have hmem : (z : G) ∈ r0Of M V (A ⊔ B) ⊓ Pc M V := ⟨z.2, hzP⟩
    rwa [L2Datum.r0_inf_Pc hD hS7] at hmem
  · intro hz
    refine Subtype.ext ?_
    rw [r0BarMap_apply]
    exact (hS.mk_eq_one_iff ⟨(z : G), r0Of_le_M hS (A ⊔ B) z.2⟩).mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1

private theorem subgroupOf_imgQ_eq_map_r0BarMap (hS : Sec6Hyp M V)
    {C : Subgroup G} (hC : C ∈ sigmaSet M V) (hCX : C ≤ cenOf (A ⊔ B)) :
    (imgQ M C).subgroupOf (imgQ M (r0Of M V (A ⊔ B))) =
      (C.subgroupOf (r0Of M V (A ⊔ B))).map (r0BarMap hS A B) := by
  have hCR0 : C ≤ r0Of M V (A ⊔ B) := le_iSup₂_of_le C ⟨hC, hCX⟩ le_rfl
  ext x
  constructor
  · intro hx
    have hxC : (x : MBar M) ∈ imgQ M C := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨c, hcC, hcx⟩ := mem_imgQ_iff.mp hxC
    refine Subgroup.mem_map.mpr ⟨⟨(c : G), hCR0 hcC⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hcC
    · exact Subtype.ext hcx
  · rintro ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (mk_mem_imgQ (Subgroup.mem_subgroupOf.mp hc))

private theorem odd_normal_le_center {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) {Z : Subgroup K} (hZ : Z.Normal) (hodd : Odd (Nat.card Z))
    (heven : ∃ H : Subgroup K, Even (Nat.card H) ∧ ¬ H ≤ Z) :
    Z ≤ Subgroup.center K := by
  rcases (CFSG.LocalCores.quasisimple_normal_subgroups hK hZ) with htop | hle
  · obtain ⟨H, hH2, hHZ⟩ := heven
    exfalso
    have hKodd : Odd (Nat.card K) := by
      rw [htop] at hodd
      rwa [Nat.card_congr (Subgroup.topEquiv (G := K)).toEquiv] at hodd
    have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_subgroup_dvd_card H
    exact (Nat.not_even_iff_odd.mpr (hKodd.of_dvd_nat hdvd)) hH2
  · exact hle

private theorem false_of_two_quotient_center {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (h2 : IsPGroup 2 (K ⧸ Subgroup.center K)) : False := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.1
  have hgt : ⊥ < Subgroup.center (K ⧸ Subgroup.center K) := h2.bot_lt_center
  have htop : Subgroup.center (K ⧸ Subgroup.center K) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center _)).resolve_left (ne_of_gt hgt)
  have hcomm := Subgroup.center_eq_top_iff.mp htop
  obtain ⟨a, b, hab⟩ := hK.2.2
  exact hab (hcomm.is_comm.comm a b)

private theorem normal_le_center_of_two_quotient {K : Type*} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) {Z : Subgroup K} (hZ : Z.Normal)
    (h : Z = ⊤ → IsPGroup 2 (K ⧸ Subgroup.center K)) : Z ≤ Subgroup.center K := by
  rcases (CFSG.LocalCores.quasisimple_normal_subgroups hK hZ) with htop | hle
  · exact (false_of_two_quotient_center hK (h htop)).elim
  · exact hle

namespace L2Datum
theorem isQuasisimple_imgQ_r0 (hS : Sec7Hyp M V n f)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (r0Of M V (A ⊔ B)))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) : CFSG.IsQuasisimple ↥(imgQ M (r0Of M V (A ⊔ B))) := by
  obtain ⟨Φ, hker, hrange, -⟩ := hS9 hS.one_le h5
  let Ψ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (n - 2)) →*
      ↥(imgQ M (r0Of M V (A ⊔ B))) :=
    Φ.codRestrict _ fun x => hrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hsurj : Function.Surjective Ψ := by
    intro z
    have hz : (z : MBar M) ∈ Φ.range := hrange.symm ▸ z.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hz
    exact ⟨y, Subtype.ext hy⟩
  have hker' : Ψ.ker ≤ Subgroup.center
      ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (n - 2)) := by
    rw [MonoidHom.ker_codRestrict]
    exact hker
  have hSU : CFSG.IsQuasisimple
      ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (n - 2)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Unitary.isQuasisimple_SU (card_galoisField_two_mul hS.one_le) (by omega) (by
      intro hcon
      have hf2 : 2 ≤ f := by
        have h4 : 4 ≤ 2 ^ f := by
          rw [← hS.card_V]
          exact hS.sec5.toRootHyp.four_le_card
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have : 2 ^ f = 2 := congrArg Prod.snd hcon
      omega)
  exact CFSG.LocalCores.isQuasisimple_of_surjective hSU Ψ hsurj hker'

private theorem image_oOf_inf_r0_central (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (r0Of M V (A ⊔ B)))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) :
    ((oOf M h ⊓ r0Of M V (A ⊔ B)).subgroupOf (r0Of M V (A ⊔ B))).map
        (r0BarMap hS.toSec6Hyp A B) ≤
      Subgroup.center ↥(imgQ M (r0Of M V (A ⊔ B))) := by
  classical
  let hS6' : Sec6Hyp M V := hS.toSec6Hyp
  set R0 : Subgroup G := r0Of M V (A ⊔ B)
  set P0 : Subgroup G := p0Of M V (A ⊔ B)
  set O : Subgroup G := oOf M h
  have hKbar : CFSG.IsQuasisimple ↥(imgQ M R0) := isQuasisimple_imgQ_r0 hS hS9 h5
  let ψ := r0BarMap hS6' A B
  have hψ : Function.Surjective ψ := r0BarMap_surjective hS6' A B
  have hR0R : R0 ≤ rOf M h :=
    (L2Datum.r0_le_inf_cenOf hS6' hD).trans (L2Datum.inf_cenOf_le_rOf hD)
  have hRnormO : rOf M h ≤ Subgroup.normalizer (O : Set G) := Sec7.rOf_le_normalizer_oOf M h
  have hN1 : ((O ⊓ R0).subgroupOf R0).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf, inf_eq_left.mpr inf_le_right]
    exact (le_inf (hR0R.trans hRnormO) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let Z1 : Subgroup ↥(imgQ M R0) := ((O ⊓ R0).subgroupOf R0).map ψ
  have hZ1_normal : Z1.Normal := hN1.map ψ hψ
  have hZ1_odd : Odd (Nat.card Z1) := by
    have hodd : Odd (Nat.card ↥((O ⊓ R0).subgroupOf R0)) := by
      rw [show Nat.card ↥((O ⊓ R0).subgroupOf R0) = Nat.card ↥(O ⊓ R0) from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := O ⊓ R0) (K := R0)
          inf_le_right).toEquiv]
      have hdvd : Nat.card ↥(O ⊓ R0) ∣ Nat.card ↥O := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := O ⊓ R0) (K := O)
          inf_le_left).toEquiv]
        exact Subgroup.card_subgroup_dvd_card ((O ⊓ R0).subgroupOf O)
      exact (Sec7.odd_card_oOf M h).of_dvd_nat hdvd
    exact hodd.of_dvd_nat (Subgroup.card_map_dvd (H := (O ⊓ R0).subgroupOf R0) ψ)
  have hne : (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}).Nonempty := by
    obtain ⟨Φ, -, -, hΔ⟩ := hS9 hS.one_le h5
    exact ⟨_, (hΔ _).mpr ⟨1, rfl⟩⟩
  obtain ⟨U', hU'⟩ := hne
  obtain ⟨C, hC, -⟩ := hU'
  have hCcard : Nat.card (imgQ M C) = Nat.card V := hS6'.card_imgQ_of_mem_sigmaSet hC.1
  have hf0 : f ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hS.one_le)
  have hevenC : Even (Nat.card (imgQ M C)) := by
    rw [hCcard, hS.card_V]
    exact (Nat.even_pow).mpr ⟨even_two, hf0⟩
  have hZ1_ne_top : Z1 ≠ ⊤ := by
    intro htop
    have hdvd : Nat.card (imgQ M C) ∣ Nat.card ↥(imgQ M R0) :=
      Subgroup.card_dvd_of_le (imgQ_mono (le_iSup₂_of_le C ⟨hC.1, hC.2⟩ le_rfl))
    have hZ1_top_card : Nat.card Z1 = Nat.card ↥(imgQ M R0) := by
      rw [htop]
      exact Nat.card_congr (Subgroup.topEquiv (G := ↥(imgQ M R0))).toEquiv
    have hoddK : Odd (Nat.card ↥(imgQ M R0)) := hZ1_top_card ▸ hZ1_odd
    exact (Nat.not_even_iff_odd.mpr (hoddK.of_dvd_nat hdvd)) hevenC
  have hCbar_le : imgQ M C ≤ (imgQ M R0 : Subgroup (MBar M)) :=
    imgQ_mono (le_iSup₂_of_le C ⟨hC.1, hC.2⟩ le_rfl)
  let Cbar : Subgroup ↥(imgQ M R0) := (imgQ M C).subgroupOf (imgQ M R0)
  have hCbar_card : Nat.card Cbar = Nat.card (imgQ M C) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCbar_le).toEquiv
  have hevenCbar : Even (Nat.card Cbar) := by rw [hCbar_card]; exact hevenC
  have hnot : ¬ Cbar ≤ Z1 := by
    intro hle
    have hdvd : Nat.card Cbar ∣ Nat.card Z1 := Subgroup.card_dvd_of_le hle
    exact (Nat.not_even_iff_odd.mpr (hZ1_odd.of_dvd_nat hdvd)) hevenCbar
  exact odd_normal_le_center hKbar hZ1_normal hZ1_odd ⟨Cbar, hevenCbar, hnot⟩

private theorem image_U_inf_r0_central (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    (hS6 : {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)})
    (hS7 : p0Of M V (A ⊔ B) ≤ r0Of M V (A ⊔ B))
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (r0Of M V (A ⊔ B)))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) :
    ((inSubgroup (Op_p'p 2) (rOf M h) ⊓ r0Of M V (A ⊔ B)).subgroupOf
        (r0Of M V (A ⊔ B))).map (r0BarMap hS.toSec6Hyp A B) ≤
      Subgroup.center ↥(imgQ M (r0Of M V (A ⊔ B))) := by
  classical
  let hS6' : Sec6Hyp M V := hS.toSec6Hyp
  set R0 : Subgroup G := r0Of M V (A ⊔ B)
  set P0 : Subgroup G := p0Of M V (A ⊔ B)
  set U : Subgroup G := inSubgroup (Op_p'p 2) (rOf M h)
  set P : Subgroup G := Pc M V
  have hKbar : CFSG.IsQuasisimple ↥(imgQ M R0) := isQuasisimple_imgQ_r0 hS hS9 h5
  let ψ := r0BarMap hS6' A B
  have hψ : Function.Surjective ψ := r0BarMap_surjective hS6' A B
  have hkerψ : ψ.ker = P0.subgroupOf R0 := r0BarMap_ker hS6' hD hS7
  have hR0R : R0 ≤ rOf M h :=
    (L2Datum.r0_le_inf_cenOf hS6' hD).trans (L2Datum.inf_cenOf_le_rOf hD)
  have hP0R : P0 ≤ rOf M h := L2Datum.p0_le_rOf hS6' hD
  have hP0P : P0 ≤ P := inf_le_left
  have hP2 : IsPGroup 2 P := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP0_2 : IsPGroup 2 P0 := hP2.to_le hP0P
  have hRnormP0 : rOf M h ≤ Subgroup.normalizer (P0 : Set G) :=
    L2Datum.rOf_le_normalizer_p0 hS6' hD hS1
  have hP0U : P0 ≤ U := Sec7.le_Op_p'p_rOf_of_normal hP0R hRnormP0 hP0_2
  have hRnormR0 : rOf M h ≤ Subgroup.normalizer (R0 : Set G) :=
    L2Datum.rOf_le_normalizer_r0 hS6' hD hS6
  have hRnormU : rOf M h ≤ Subgroup.normalizer (U : Set G) := Sec7.rOf_le_normalizer_Op_p'p M h
  have hN2 : ((U ⊓ R0).subgroupOf R0).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf, inf_eq_left.mpr inf_le_right]
    exact (le_inf (hR0R.trans hRnormU) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let Z2 : Subgroup ↥(imgQ M R0) := ((U ⊓ R0).subgroupOf R0).map ψ
  have hZ2_normal : Z2.Normal := hN2.map ψ hψ
  refine normal_le_center_of_two_quotient hKbar hZ2_normal ?_
  intro htop
  have hR0U : R0 ≤ U := by
    intro s hs
    have hmem : ψ ⟨s, hs⟩ ∈ Z2 := by
      rw [show Z2 = ⊤ from htop]
      exact Subgroup.mem_top _
    obtain ⟨v, hv, hvψ⟩ := Subgroup.mem_map.mp hmem
    have hvU : (v : G) ∈ U := (Subgroup.mem_subgroupOf.mp hv).1
    have hker : ψ (v⁻¹ * ⟨s, hs⟩) = 1 := by
      rw [map_mul, map_inv, hvψ, inv_mul_cancel]
    have hP0 : (v⁻¹ * ⟨s, hs⟩ : ↥R0) ∈ P0.subgroupOf R0 := by
      rw [← hkerψ]
      exact MonoidHom.mem_ker.mpr hker
    have hP0G : (v : G)⁻¹ * s ∈ P0 := Subgroup.mem_subgroupOf.mp hP0
    have : (v : G) * ((v : G)⁻¹ * s) ∈ U := U.mul_mem hvU (hP0U hP0G)
    simpa using this
  have hZ1_cent := image_oOf_inf_r0_central hS hD hS9 h5
  rw [isPGroup_iff_pow_pow_eq_one]
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) q
  obtain ⟨s, rfl⟩ := hψ k
  obtain ⟨j, hj⟩ := Sec7.exists_pow_mem_oOf (hR0U s.2)
  refine ⟨j, ?_⟩
  have hpow : ψ (s ^ 2 ^ j) = ψ s ^ 2 ^ j := map_pow ψ s (2 ^ j)
  rw [← map_pow, ← hpow]
  refine (QuotientGroup.eq_one_iff _).mpr (hZ1_cent ?_)
  exact Subgroup.mem_map.mpr ⟨⟨s ^ 2 ^ j, R0.pow_mem s.2 _⟩,
    Subgroup.mem_subgroupOf.mpr ⟨hj, R0.pow_mem s.2 _⟩, rfl⟩

private abbrev fiveR0 (M V A B : Subgroup G) : Subgroup G := r0Of M V (A ⊔ B)

private abbrev fiveP0 (M V A B : Subgroup G) : Subgroup G := p0Of M V (A ⊔ B)

private structure IrredBase (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B) : Type where
  Esec : Subgroup ↥(fiveR0 M V A B)
  Asec : Subgroup ↥(fiveR0 M V A B)
  hE : Esec = (fiveP0 M V A B).subgroupOf (fiveR0 M V A B)
  hA : Asec = V.subgroupOf (fiveR0 M V A B)
  hSec : RootMany.SecHyp (fiveR0 M V A B) (fiveP0 M V A B) (fiveP0 M V A B) V
  [normalE : Esec.Normal]
  [normalA : Asec.Normal]
  [elemSection : Fact (RootMany.IsElemSection Esec Asec)]

private noncomputable def irredBase (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B) :
    IrredBase hS hD hS1 hS3 hS5 hS7 := by
  classical
  have hP0R : fiveP0 M V A B ≤ rOf M h := L2Datum.p0_le_rOf hS.toSec6Hyp hD
  have hR0R : fiveR0 M V A B ≤ rOf M h :=
    (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans (L2Datum.inf_cenOf_le_rOf hD)
  have hRnormP0 : rOf M h ≤ Subgroup.normalizer (fiveP0 M V A B : Set G) :=
    L2Datum.rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1
  have hSec : RootMany.SecHyp (fiveR0 M V A B) (fiveP0 M V A B) (fiveP0 M V A B) V :=
    { le := L2Datum.V_le_p0 hS.toSec6Hyp hD
      le_R := hS7
      conj_E := fun r hr e he =>
        (Subgroup.mem_normalizer_iff.mp (hRnormP0 (hR0R hr)) e).mp he
      conj_A := fun r hr x hx =>
        (Subgroup.mem_normalizer_iff.mp
          (hS.sec5.toRootHyp.toHyp.le_normalizer (Subgroup.mem_inf.mp (hR0R hr)).1) x).mp hx
      comm := fun x hx y hy => by
        have h := Subgroup.commutator_mem_commutator (H₁ := fiveP0 M V A B)
          (H₂ := fiveP0 M V A B) hx hy
        rwa [hS3] at h
      sq := hS5
      ker := fun k hk e he => by
        have h := Subgroup.commutator_mem_commutator (H₁ := fiveP0 M V A B)
          (H₂ := fiveP0 M V A B) hk he
        rwa [hS3] at h }
  let Esec : Subgroup ↥(fiveR0 M V A B) := (fiveP0 M V A B).subgroupOf (fiveR0 M V A B)
  let Asec : Subgroup ↥(fiveR0 M V A B) := V.subgroupOf (fiveR0 M V A B)
  letI : Esec.Normal := hSec.normal_E
  letI : Asec.Normal := hSec.normal_A
  letI : Fact (RootMany.IsElemSection Esec Asec) := ⟨hSec.isElemSection⟩
  exact IrredBase.mk Esec Asec rfl rfl hSec

private structure IrredModuleCore (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B) : Type where
  base : IrredBase hS hD hS1 hS3 hS5 hS7
  [baseNormalE : base.Esec.Normal]
  [baseNormalA : base.Asec.Normal]
  [baseElemSection : Fact (RootMany.IsElemSection base.Esec base.Asec)]
  ψ : ↥(fiveR0 M V A B) →* ↥(imgQ M (fiveR0 M V A B))
  hψ_eq : ψ = r0BarMap hS.toSec6Hyp A B
  hψ : Function.Surjective ψ
  hkerψ : ψ.ker = base.Esec
  ρ : Representation (ZMod 2) ↥(imgQ M (fiveR0 M V A B))
    (RootMany.SecMod base.Esec base.Asec)
  hρ : ∀ r, ρ (ψ r) = secRep base.Esec base.Asec r
  hcardW : Nat.card (RootMany.SecMod base.Esec base.Asec) = Nat.card V ^ (2 * n - 4)

private noncomputable def irredModuleCore (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (base : IrredBase hS hD hS1 hS3 hS5 hS7) (h5 : 5 ≤ n) :
    IrredModuleCore hS hD hS1 hS2 hS3 hS5 hS7 := by
  classical
  letI : base.Esec.Normal := base.normalE
  letI : base.Asec.Normal := base.normalA
  letI : Fact (RootMany.IsElemSection base.Esec base.Asec) := base.elemSection
  let W := RootMany.SecMod base.Esec base.Asec
  letI : AddCommGroup W := inferInstance
  letI : Module (ZMod 2) W := inferInstance
  letI : Finite W := inferInstance
  let ψ : ↥(fiveR0 M V A B) →* ↥(imgQ M (fiveR0 M V A B)) := r0BarMap hS.toSec6Hyp A B
  have hψ : Function.Surjective ψ := r0BarMap_surjective hS.toSec6Hyp A B
  have hkerψ : ψ.ker = base.Esec := by
    rw [r0BarMap_ker hS.toSec6Hyp hD hS7, base.hE]
  have hker_le : ψ.ker ≤ (secRep base.Esec base.Asec).ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hkE : k ∈ base.Esec := by rwa [hkerψ] at hk
    rw [base.hE] at hkE
    have hkP0 : (k : G) ∈ fiveP0 M V A B := Subgroup.mem_subgroupOf.mp hkE
    refine (secRep_eq_one_iff base.Esec base.Asec k).mpr fun e he => ?_
    rw [base.hE] at he
    have heP0 : (e : G) ∈ fiveP0 M V A B := Subgroup.mem_subgroupOf.mp he
    have hmem : (k : G) * (e : G) * (k : G)⁻¹ * (e : G)⁻¹ ∈ V :=
      base.hSec.ker (k : G) hkP0 (e : G) heP0
    simpa [base.hA] using Subgroup.mem_subgroupOf.mpr hmem
  let ρ : Representation (ZMod 2) ↥(imgQ M (fiveR0 M V A B)) W :=
    (QuotientGroup.lift ψ.ker (secRep base.Esec base.Asec) hker_le).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom
  have hρ : ∀ r : ↥(fiveR0 M V A B), ρ (ψ r) = secRep base.Esec base.Asec r := by
    intro r
    have he : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ r) =
        (r : ↥(fiveR0 M V A B) ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    dsimp only [ρ]
    rw [MonoidHom.comp_apply]
    change (QuotientGroup.lift ψ.ker (secRep base.Esec base.Asec) hker_le)
      ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ r)) = _
    rw [he, QuotientGroup.lift_mk]
  have hcardW : Nat.card W = Nat.card V ^ (2 * n - 4) := by
    have hWmul : Nat.card W * Nat.card V = Nat.card V ^ (2 * n - 3) := by
      change Nat.card (RootMany.SecMod base.Esec base.Asec) * Nat.card V =
        Nat.card V ^ (2 * n - 3)
      have h := RootMany.card_secMod base.Esec base.Asec
      rw [base.hE] at h
      rw [base.hSec.card_E] at h
      rw [base.hA] at h
      rw [base.hSec.card_A] at h
      rw [hS2] at h
      simpa [base.hE, base.hA] using h
    have hexp : 2 * n - 3 = (2 * n - 4) + 1 := by omega
    rw [hexp, pow_succ] at hWmul
    exact Nat.mul_right_cancel Nat.card_pos hWmul
  exact IrredModuleCore.mk base ψ rfl hψ hkerψ ρ hρ hcardW

private structure IrredModule (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) : Type where
  core : IrredModuleCore hS hD hS1 hS2 hS3 hS5 hS7
  Δ : Set (Subgroup (MBar M))
  hΔ : Δ = imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}
  hTop : IsSUImage (⊤ : Subgroup ↥(imgQ M (fiveR0 M V A B)))
    ((fun D : Subgroup (MBar M) => D.subgroupOf (imgQ M (fiveR0 M V A B))) '' Δ)
    f (n - 2) hS.one_le (by omega)

private noncomputable def irredModule (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (core : IrredModuleCore hS hD hS1 hS2 hS3 hS5 hS7) :
    IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 := by
  classical
  let Δ : Set (Subgroup (MBar M)) :=
    imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}
  have hS9' : IsSUImage (imgQ M (fiveR0 M V A B)) Δ f (n - 2) hS.one_le (by omega) :=
    hS9 hS.one_le h5
  have hTop : IsSUImage (⊤ : Subgroup ↥(imgQ M (fiveR0 M V A B)))
      ((fun D : Subgroup (MBar M) => D.subgroupOf (imgQ M (fiveR0 M V A B))) '' Δ)
      f (n - 2) hS.one_le (by omega) := IsSUImage.toTop hS9'
  exact { core := core, Δ := Δ, hΔ := rfl, hTop := hTop }

theorem exists_commutator_not_mem_V (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B)) {C : Subgroup G}
    (hC : C ∈ sigmaSet M V) (hCX : C ≤ cenOf (A ⊔ B)) :
    ∃ p ∈ p0Of M V (A ⊔ B), ∃ c ∈ C, ⁅p, c⁆ ∉ V := by
  classical
  let P0 := p0Of M V (A ⊔ B)
  have hcomm : ⁅P0, C⁆ = ⁅Pc M V, C⁆ :=
    (L2Datum.commutator_Pc_eq_p0 hS hD hS1 hC hCX).symm
  have hcardComm : Nat.card ↥⁅P0, C⁆ = Nat.card V ^ 3 := by
    rw [hcomm]
    exact hS.sec5.card_commutator_Pc hC
  by_contra h
  push Not at h
  have hle : ⁅P0, C⁆ ≤ V := (Subgroup.commutator_le).mpr h
  have hcardle : Nat.card ↥⁅P0, C⁆ ≤ Nat.card V :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  have hq : 2 ≤ Nat.card V := by
    have := hS.sec5.toRootHyp.four_le_card
    omega
  have hlt : Nat.card V < Nat.card V ^ 3 := by
    have hq2 : Nat.card V * Nat.card V ≥ 4 := by nlinarith
    nlinarith [hS.card_V]
  omega

private theorem irredNt (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (D : IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5) :
    ∃ x ∈ (⊤ : Subgroup ↥(imgQ M (fiveR0 M V A B))),
      ∃ w : RootMany.SecMod D.core.base.Esec D.core.base.Asec, D.core.ρ x w ≠ w := by
  classical
  let W := RootMany.SecMod D.core.base.Esec D.core.base.Asec
  let ψ := D.core.ψ
  let ρ := D.core.ρ
  let Esec := D.core.base.Esec
  let Asec := D.core.base.Asec
  let R0 := fiveR0 M V A B
  let P0 := fiveP0 M V A B
  letI : Esec.Normal := D.core.base.normalE
  letI : Asec.Normal := D.core.base.normalA
  letI : Fact (RootMany.IsElemSection Esec Asec) := D.core.base.elemSection
  have hρ : ∀ r : ↥R0, ρ (ψ r) = secRep Esec Asec r := D.core.hρ
  have hR0R : R0 ≤ rOf M h :=
    (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans (L2Datum.inf_cenOf_le_rOf hD)
  have hS9' : IsSUImage (imgQ M (fiveR0 M V A B)) D.Δ f (n - 2) hS.one_le (by omega) :=
    D.hΔ ▸ hS9 hS.one_le h5
  have hne : D.Δ.Nonempty := by
    obtain ⟨Φ, -, -, hΔ⟩ := hS9'
    exact ⟨_, (hΔ _).mpr ⟨1, rfl⟩⟩
  obtain ⟨U, hU⟩ := hne
  rw [D.hΔ] at hU
  obtain ⟨C, hC, -⟩ := hU
  obtain ⟨p, hpP0, c, hcC, hpc⟩ := exists_commutator_not_mem_V hS hD hS1 hC.1 hC.2
  have hcR0 : c ∈ R0 := (le_iSup₂_of_le C ⟨hC.1, hC.2⟩ le_rfl : C ≤ R0) hcC
  have hpR0 : p ∈ R0 := hS7 hpP0
  let c' : ↥R0 := ⟨c, hcR0⟩
  let p' : ↥R0 := ⟨p, hpR0⟩
  have hpE : p' ∈ Esec := by
    rw [show Esec = (fiveP0 M V A B).subgroupOf (fiveR0 M V A B) from D.core.base.hE]
    exact Subgroup.mem_subgroupOf.mpr hpP0
  let e' : Esec := ⟨p', hpE⟩
  have hprod : (c' * p' * c'⁻¹ : ↥R0) ∈ Esec := by
    simpa [c', p'] using D.core.base.normalE.conj_mem p' hpE c'
  let d' : Esec := ⟨c' * p' * c'⁻¹, hprod⟩
  refine ⟨ψ c', Subgroup.mem_top _, secMk Esec Asec e', ?_⟩
  intro heq
  rw [hρ, secRep_mk] at heq
  have heq' : secMk Esec Asec d' = secMk Esec Asec e' := by
    simpa [d', c', p', e', secConj] using heq
  have hmem := (secMk_eq_secMk_iff Esec Asec d' e').mp heq'
  rw [show Asec = V.subgroupOf (fiveR0 M V A B) from D.core.base.hA] at hmem
  have hcoe : ((d' : ↥R0)⁻¹ * (e' : ↥R0) : G) ∈ V :=
    Subgroup.mem_subgroupOf.mp hmem
  have hEqG : ((d' : ↥R0)⁻¹ * (e' : ↥R0) : G) = p⁻¹ * ⁅p, c⁆ * p := by
    simp [d', e', c', p', commutatorElement_def]
    group
  rw [hEqG] at hcoe
  have hpM : p ∈ M := (Subgroup.mem_inf.mp (hR0R (hS7 hpP0))).1
  have hnorm : p ∈ Subgroup.normalizer (V : Set G) :=
    hS.sec5.toRootHyp.toHyp.le_normalizer hpM
  have hpcV : ⁅p, c⁆ ∈ V := by
    have h := (Subgroup.mem_normalizer_iff.mp hnorm (p⁻¹ * ⁅p, c⁆ * p)).mp hcoe
    have h1 : p * (p⁻¹ * ⁅p, c⁆ * p) * p⁻¹ = ⁅p, c⁆ := by group
    rwa [h1] at h
  exact hpc hpcV

private theorem irredSpan (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (D : IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5)
    [hEn : D.core.base.Esec.Normal] [hAn : D.core.base.Asec.Normal]
    [hEs : Fact (RootMany.IsElemSection D.core.base.Esec D.core.base.Asec)] :
    ∀ C ∈ {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)},
      Submodule.span (ZMod 2) {u : RootMany.SecMod D.core.base.Esec D.core.base.Asec |
        ∃ a ∈ (imgQ M C).subgroupOf (imgQ M (fiveR0 M V A B)), ∃ w,
          u = D.core.ρ a w - w} =
      secSub D.core.base.Esec D.core.base.Asec
        ((⁅C, fiveP0 M V A B⁆).subgroupOf (fiveR0 M V A B)) := by
  classical
  let W := RootMany.SecMod D.core.base.Esec D.core.base.Asec
  let ψ := D.core.ψ
  let ρ := D.core.ρ
  let Esec := D.core.base.Esec
  let Asec := D.core.base.Asec
  let R0 := fiveR0 M V A B
  let P0 := fiveP0 M V A B
  letI : Esec.Normal := hEn
  letI : Asec.Normal := hAn
  letI : Fact (RootMany.IsElemSection Esec Asec) := hEs
  intro C hC
  have hAeq := subgroupOf_imgQ_eq_map_r0BarMap hS.toSec6Hyp hC.1 hC.2
  have hset : {u : W | ∃ a ∈ (C.subgroupOf R0).map ψ, ∃ w, u = ρ a w - w} =
      {u : W | ∃ c ∈ C.subgroupOf R0, ∃ w, u = secRep Esec Asec c w - w} := by
    ext u
    constructor
    · rintro ⟨a, ⟨c, hc, rfl⟩, w, rfl⟩
      exact ⟨c, hc, w, by rw [D.core.hρ]⟩
    · rintro ⟨c, hc, w, rfl⟩
      exact ⟨ψ c, ⟨c, hc, rfl⟩, w, by rw [D.core.hρ]⟩
  rw [hAeq, ← D.core.hψ_eq]
  change Submodule.span (ZMod 2) {u : W | ∃ a ∈ (C.subgroupOf R0).map ψ, ∃ w,
      u = ρ a w - w} = secSub Esec Asec ((⁅C, P0⁆).subgroupOf R0)
  rw [hset, span_secRep_eq_secSub_commutator Esec Asec (C.subgroupOf R0)
    Subgroup.le_normalizer_of_normal]
  have harg : ⁅C.subgroupOf R0, Esec⁆ = (⁅C, P0⁆).subgroupOf R0 := by
    rw [show Esec = (fiveP0 M V A B).subgroupOf (fiveR0 M V A B) from D.core.base.hE]
    exact CFSG.GroupTheory.commutator_subgroupOf_eq
      (le_iSup₂_of_le C ⟨hC.1, hC.2⟩ le_rfl) hS7
  rw [harg]

private theorem irredSub (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (D : IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5)
    {C E : Subgroup G} (hC : C ∈ {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)})
    (hE : E ∈ {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) :
    D.core.base.Asec ≤ (⁅C, fiveP0 M V A B⁆).subgroupOf (fiveR0 M V A B) ∧
    D.core.base.Asec ≤ (⁅E, fiveP0 M V A B⁆).subgroupOf (fiveR0 M V A B) := by
  classical
  let Asec := D.core.base.Asec
  let R0 := fiveR0 M V A B
  let P0 := fiveP0 M V A B
  have hAeq : Asec = V.subgroupOf R0 := D.core.base.hA
  constructor
  · intro x hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hxV : (x : G) ∈ V := by
      change x ∈ D.core.base.Asec at hx
      rw [D.core.base.hA] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hcommC : ⁅P0, C⁆ = ⁅Pc M V, C⁆ :=
      (L2Datum.commutator_Pc_eq_p0 hS hD hS1 hC.1 hC.2).symm
    have := hS.sec5.V_le_commutator hC.1
    rw [← hcommC, ← Subgroup.commutator_comm C P0] at this
    exact this hxV
  · intro x hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hxV : (x : G) ∈ V := by
      change x ∈ D.core.base.Asec at hx
      rw [D.core.base.hA] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hcommE : ⁅P0, E⁆ = ⁅Pc M V, E⁆ :=
      (L2Datum.commutator_Pc_eq_p0 hS hD hS1 hE.1 hE.2).symm
    have := hS.sec5.V_le_commutator hE.1
    rw [← hcommE, ← Subgroup.commutator_comm E P0] at this
    exact this hxV

private theorem irredTIcond (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (h71TI : Sec7.Stmt71TI M V)
    (D : IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5)
    [hEn : D.core.base.Esec.Normal] [hAn : D.core.base.Asec.Normal]
    [hEs : Fact (RootMany.IsElemSection D.core.base.Esec D.core.base.Asec)] :
    ∀ X : Subgroup ↥(imgQ M (fiveR0 M V A B)),
      X ∈ (fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M (fiveR0 M V A B))) '' D.Δ →
    ∀ Y : Subgroup ↥(imgQ M (fiveR0 M V A B)),
      Y ∈ (fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M (fiveR0 M V A B))) '' D.Δ →
      Submodule.span (ZMod 2) {u : RootMany.SecMod D.core.base.Esec D.core.base.Asec |
        ∃ a ∈ X, ∃ w, u = D.core.ρ a w - w} =
        Submodule.span (ZMod 2) {u : RootMany.SecMod D.core.base.Esec D.core.base.Asec |
          ∃ b ∈ Y, ∃ w, u = D.core.ρ b w - w} ∨
      Submodule.span (ZMod 2) {u : RootMany.SecMod D.core.base.Esec D.core.base.Asec |
        ∃ a ∈ X, ∃ w, u = D.core.ρ a w - w} ⊓
        Submodule.span (ZMod 2) {u : RootMany.SecMod D.core.base.Esec D.core.base.Asec |
          ∃ b ∈ Y, ∃ w, u = D.core.ρ b w - w} = ⊥ := by
  classical
  let Esec := D.core.base.Esec
  let Asec := D.core.base.Asec
  let R0 := fiveR0 M V A B
  let P0 := fiveP0 M V A B
  letI : Esec.Normal := hEn
  letI : Asec.Normal := hAn
  letI : Fact (RootMany.IsElemSection Esec Asec) := hEs
  rintro X ⟨A', hA', rfl⟩ Y ⟨B', hB', rfl⟩
  rw [D.hΔ] at hA' hB'
  obtain ⟨C, hC, rfl⟩ := hA'
  obtain ⟨D', hD', rfl⟩ := hB'
  rw [irredSpan hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 D C hC,
    irredSpan hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 D D' hD']
  have h71 := h71TI C hC.1 D' hD'.1
  rw [L2Datum.commutator_Pc_eq_p0 hS hD hS1 hC.1 hC.2,
    L2Datum.commutator_Pc_eq_p0 hS hD hS1 hD'.1 hD'.2] at h71
  rcases h71 with heq | hinf
  · left
    have heq' : ⁅C, P0⁆ = ⁅D', P0⁆ := by
      rw [Subgroup.commutator_comm C P0, Subgroup.commutator_comm D' P0]
      exact heq
    rw [heq']
  · right
    obtain ⟨hA₁, hA₂⟩ := irredSub hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 D hC hD'
    have hAeq : Asec = V.subgroupOf R0 := D.core.base.hA
    rw [secSub_inf Esec Asec _ _ hA₂]
    have hsub : (⁅C, P0⁆).subgroupOf R0 ⊓ (⁅D', P0⁆).subgroupOf R0 = Asec := by
      have hsub : (⁅C, P0⁆ ⊓ ⁅D', P0⁆).subgroupOf R0 =
          (⁅C, P0⁆).subgroupOf R0 ⊓ (⁅D', P0⁆).subgroupOf R0 := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      have hinf' : ⁅C, P0⁆ ⊓ ⁅D', P0⁆ = V := by
        rw [Subgroup.commutator_comm C P0, Subgroup.commutator_comm D' P0]
        exact hinf
      rw [← hsub, hinf', show V.subgroupOf R0 = Asec from D.core.base.hA.symm]
    rw [hsub]
    have hEeq : Esec = (fiveP0 M V A B).subgroupOf R0 := D.core.base.hE
    exact (secSub_eq_bot_iff Esec Asec Asec (le_refl Asec) (fun x hx => by
      change x ∈ D.core.base.Asec at hx
      rw [D.core.base.hA] at hx
      change x ∈ D.core.base.Esec
      rw [D.core.base.hE]
      exact Subgroup.mem_subgroupOf.mpr
        ((L2Datum.V_le_p0 hS.toSec6Hyp hD) (Subgroup.mem_subgroupOf.mp hx)))).mpr rfl

private theorem irredHf2 (hS : Sec7Hyp M V n f) : 2 ≤ f := by
  have h4 : 4 ≤ 2 ^ f := by
    rw [← hS.card_V]
    exact hS.sec5.toRootHyp.four_le_card
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)

private theorem irredUInvariant (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (D : IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5)
    [hEn : D.core.base.Esec.Normal] [hAn : D.core.base.Asec.Normal]
    [hEs : Fact (RootMany.IsElemSection D.core.base.Esec D.core.base.Asec)]
    {N : Subgroup G} (hNR0 : fiveR0 M V A B ≤ Subgroup.normalizer (N : Set G)) :
    ∀ x ∈ (⊤ : Subgroup ↥(imgQ M (fiveR0 M V A B))),
      (secSub D.core.base.Esec D.core.base.Asec (N.subgroupOf (fiveR0 M V A B))).map
        (D.core.ρ x) ≤
      secSub D.core.base.Esec D.core.base.Asec (N.subgroupOf (fiveR0 M V A B)) := by
  classical
  let Esec := D.core.base.Esec
  let Asec := D.core.base.Asec
  let R0 := fiveR0 M V A B
  letI : Esec.Normal := hEn
  letI : Asec.Normal := hAn
  letI : Fact (RootMany.IsElemSection Esec Asec) := hEs
  intro x hx
  obtain ⟨r, rfl⟩ := D.core.hψ x
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  obtain ⟨e, he, rfl⟩ := (mem_secSub Esec Asec).mp hw
  rw [D.core.hρ, secRep_mk]
  refine (mem_secSub Esec Asec).mpr ⟨secConj Esec r e, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr
    ((Subgroup.mem_normalizer_iff.mp (hNR0 r.2) (e : G)).mp (Subgroup.mem_subgroupOf.mp he))

private theorem irredNsub (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (D : IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5)
    [hEn : D.core.base.Esec.Normal] [hAn : D.core.base.Asec.Normal]
    [hEs : Fact (RootMany.IsElemSection D.core.base.Esec D.core.base.Asec)]
    {N : Subgroup G} (hVN : V ≤ N) (hNP0 : N ≤ fiveP0 M V A B) :
    N.subgroupOf (fiveR0 M V A B) ≤ D.core.base.Esec ∧
    D.core.base.Asec ≤ N.subgroupOf (fiveR0 M V A B) := by
  classical
  let Esec := D.core.base.Esec
  let Asec := D.core.base.Asec
  let R0 := fiveR0 M V A B
  let P0 := fiveP0 M V A B
  letI : Esec.Normal := hEn
  letI : Asec.Normal := hAn
  letI : Fact (RootMany.IsElemSection Esec Asec) := hEs
  constructor
  · intro x hx
    change x ∈ D.core.base.Esec
    rw [D.core.base.hE]
    exact Subgroup.mem_subgroupOf.mpr (hNP0 (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    have hxV : (x : G) ∈ V := by
      change x ∈ D.core.base.Asec at hx
      rw [D.core.base.hA] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr (hVN hxV)

private theorem irredFinal (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = fiveP0 M V A B)
    (hS2 : Nat.card ↥(fiveP0 M V A B) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅fiveP0 M V A B, fiveP0 M V A B⁆ = V)
    (hS5 : ∀ x ∈ fiveP0 M V A B, x * x ∈ V)
    (hS7 : fiveP0 M V A B ≤ fiveR0 M V A B)
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (fiveR0 M V A B))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) (hSU3 : SU3ModuleBound) (hTI : UnitaryTIModule)
    (h71TI : Sec7.Stmt71TI M V)
    (D : IrredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5)
    [hEn : D.core.base.Esec.Normal] [hAn : D.core.base.Asec.Normal]
    [hEs : Fact (RootMany.IsElemSection D.core.base.Esec D.core.base.Asec)]
    {N : Subgroup G} (hVN : V ≤ N) (hNP0 : N ≤ fiveP0 M V A B)
    (hNR0 : fiveR0 M V A B ≤ Subgroup.normalizer (N : Set G)) :
    N = V ∨ N = fiveP0 M V A B := by
  classical
  let Esec := D.core.base.Esec
  let Asec := D.core.base.Asec
  let R0 := fiveR0 M V A B
  let P0 := fiveP0 M V A B
  letI : Esec.Normal := hEn
  letI : Asec.Normal := hAn
  letI : Fact (RootMany.IsElemSection Esec Asec) := hEs
  have hf2 : 2 ≤ f := irredHf2 hS
  obtain ⟨hNsub, hAsub⟩ := irredNsub hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 D hVN hNP0
  have hX : secSub Esec Asec (N.subgroupOf R0) = ⊥ ∨
      secSub Esec Asec (N.subgroupOf R0) = ⊤ := by
    have hU := irredUInvariant hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 D hNR0
    by_cases h6 : 6 ≤ n
    · have hm : 4 ≤ n - 2 := by omega
      have hcard : Nat.card (RootMany.SecMod Esec Asec) = (2 ^ f) ^ (2 * (n - 2)) := by
        rw [D.core.hcardW, show 2 * n - 4 = 2 * (n - 2) by omega,
          show Nat.card ↥V = 2 ^ f from hS.card_V]
      exact hTI (↥(imgQ M R0)) (⊤ : Subgroup ↥(imgQ M R0))
        ((fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M R0)) '' D.Δ) f (n - 2)
        hS.one_le hm hf2 D.hTop (RootMany.SecMod Esec Asec) D.core.ρ
        (irredNt hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 D)
        (irredTIcond hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 h71TI D) hcard _ hU
    · have hn5 : n = 5 := by omega
      have hcard : Nat.card (RootMany.SecMod Esec Asec) = (2 ^ f) ^ 6 := by
        rw [D.core.hcardW, show 2 * n - 4 = 6 by omega,
          show Nat.card ↥V = 2 ^ f from hS.card_V]
      by_contra h
      push Not at h
      have hnt' : ∃ x, ∃ w : RootMany.SecMod Esec Asec, D.core.ρ x w ≠ w := by
        obtain ⟨x, -, w, hw⟩ := irredNt hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 D
        exact ⟨x, w, hw⟩
      have hU' : ∀ g, Submodule.map (D.core.ρ g) (secSub Esec Asec (N.subgroupOf R0)) ≤
          secSub Esec Asec (N.subgroupOf R0) := fun g => hU g (Subgroup.mem_top g)
      exact hSU3.false_of_invariant_submodule
        ((fun E : Subgroup (MBar M) => E.subgroupOf (imgQ M R0)) '' D.Δ)
        f hS.one_le hf2 (by simpa [hn5] using D.hTop) D.core.ρ hnt'
        (isQuasisimple_imgQ_r0 hS hS9 h5).1.commutator_eq_top hU' h.1 h.2 hcard
  rcases hX with h | h
  · left
    have hN0 : N.subgroupOf R0 = Asec :=
      (secSub_eq_bot_iff Esec Asec (N.subgroupOf R0) hAsub hNsub).mp h
    have hNR0' : N ≤ R0 := hNP0.trans hS7
    have hVR0 : V ≤ R0 := (L2Datum.V_le_p0 hS.toSec6Hyp hD).trans hS7
    calc N = (N.subgroupOf R0).map R0.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hNR0').symm
      _ = Asec.map R0.subtype := by rw [hN0]
      _ = V := by
        rw [show Asec = V.subgroupOf R0 from D.core.base.hA,
          Subgroup.map_subgroupOf_eq_of_le hVR0]
  · right
    have hN0 : N.subgroupOf R0 = Esec :=
      (secSub_eq_top_iff Esec Asec (N.subgroupOf R0) hAsub hNsub).mp h
    have hNR0' : N ≤ R0 := hNP0.trans hS7
    calc N = (N.subgroupOf R0).map R0.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hNR0').symm
      _ = Esec.map R0.subtype := by rw [hN0]
      _ = P0 := by
        rw [show Esec = P0.subgroupOf R0 from D.core.base.hE,
          Subgroup.map_subgroupOf_eq_of_le hS7]

theorem irred_five_of (hS : Sec7Hyp M V n f) (hSU3 : SU3ModuleBound) (hTI : UnitaryTIModule)
    (h71TI : Sec7.Stmt71TI M V) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    (hS2 : Nat.card ↥(p0Of M V (A ⊔ B)) = Nat.card V ^ (2 * n - 3))
    (hS3 : ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ = V)
    (hS5 : ∀ x ∈ p0Of M V (A ⊔ B), x * x ∈ V)
    (hS7 : p0Of M V (A ⊔ B) ≤ r0Of M V (A ⊔ B))
    (hS9 : ∀ (hf : 1 ≤ f) (h5 : 5 ≤ n),
      IsSUImage (imgQ M (r0Of M V (A ⊔ B)))
        (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
          (Nat.le_sub_of_add_le (Nat.le_of_succ_le h5)))
    (h5 : 5 ≤ n) :
    ∀ N : Subgroup G, V ≤ N → N ≤ p0Of M V (A ⊔ B) → r0Of M V (A ⊔ B) ≤
      Subgroup.normalizer (N : Set G) → N = V ∨ N = p0Of M V (A ⊔ B) := by
  classical
  let base := irredBase hS hD hS1 hS3 hS5 hS7
  let core := irredModuleCore hS hD hS1 hS2 hS3 hS5 hS7 base h5
  let D := irredModule hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 core
  letI : D.core.base.Esec.Normal := D.core.baseNormalE
  letI : D.core.base.Asec.Normal := D.core.baseNormalA
  letI : Fact (RootMany.IsElemSection D.core.base.Esec D.core.base.Asec) :=
    D.core.baseElemSection
  intro N hVN hNP0 hNR0
  exact irredFinal hS hD hS1 hS2 hS3 hS5 hS7 hS9 h5 hSU3 hTI h71TI D hVN hNP0 hNR0

theorem irred_five (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hSU3 : SU3ModuleBound) (hTI : UnitaryTIModule) (h71TI : Sec7.Stmt71TI M V)
    (hD : L2Datum M V A B h) (h5 : 5 ≤ n) :
    ∀ N : Subgroup G, V ≤ N → N ≤ p0Of M V (A ⊔ B) → r0Of M V (A ⊔ B) ≤
      Subgroup.normalizer (N : Set G) → N = V ∨ N = p0Of M V (A ⊔ B) := by
  obtain ⟨hS1, hS2, hS3, -, hS5, -, hS7, -, hS9, -⟩ := h72 A B h hD
  exact irred_five_of hS hSU3 hTI h71TI hD hS1 hS2 hS3 hS5 hS7 hS9 h5

private theorem commutator_mem_image (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS6 : {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)})
    {u : G} (hu : u ∈ inSubgroup (Op_p'p 2) (rOf M h)) (huM : u ∈ M) :
    ∀ k ∈ (imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)),
      QuotientGroup.mk' (pCore 2 ↥M) ⟨u, huM⟩ * k *
        (QuotientGroup.mk' (pCore 2 ↥M) ⟨u, huM⟩)⁻¹ * k⁻¹ ∈
      ((((inSubgroup (Op_p'p 2) (rOf M h) ⊓ r0Of M V (A ⊔ B)).subgroupOf
          (r0Of M V (A ⊔ B))).map (r0BarMap hS.toSec6Hyp A B)).map
        (imgQ M (r0Of M V (A ⊔ B))).subtype) := by
  classical
  let hS6' : Sec6Hyp M V := hS.toSec6Hyp
  set R0 : Subgroup G := r0Of M V (A ⊔ B)
  set U : Subgroup G := inSubgroup (Op_p'p 2) (rOf M h)
  let ψ := r0BarMap hS6' A B
  have hψ : Function.Surjective ψ := r0BarMap_surjective hS6' A B
  have hR0R : R0 ≤ rOf M h :=
    (L2Datum.r0_le_inf_cenOf hS6' hD).trans (L2Datum.inf_cenOf_le_rOf hD)
  have hRnormR0 : rOf M h ≤ Subgroup.normalizer (R0 : Set G) :=
    L2Datum.rOf_le_normalizer_r0 hS6' hD hS6
  have hRnormU : rOf M h ≤ Subgroup.normalizer (U : Set G) := Sec7.rOf_le_normalizer_Op_p'p M h
  let Z2 : Subgroup ↥(imgQ M R0) := ((U ⊓ R0).subgroupOf R0).map ψ
  let Z2' : Subgroup (MBar M) := Z2.map (imgQ M R0).subtype
  have huR : u ∈ rOf M h := by
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact x.2
  intro k hk
  obtain ⟨s, hs⟩ := hψ (⟨k, hk⟩ : ↥(imgQ M R0))
  have hkval : k = (ψ s : MBar M) := (congrArg Subtype.val hs).symm
  rw [hkval]
  have sM : (s : G) ∈ M := (hR0R s.2 |> Subgroup.mem_inf.mp).1
  have hcomm : ⁅u, (s : G)⁆ ∈ U ⊓ R0 := by
    refine ⟨?_, ?_⟩
    · have hsU : (s : G) * u⁻¹ * (s : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hRnormU (hR0R s.2)) u⁻¹).mp (U.inv_mem hu)
      have : u * ((s : G) * u⁻¹ * (s : G)⁻¹) ∈ U := U.mul_mem hu hsU
      have hEq : u * ((s : G) * u⁻¹ * (s : G)⁻¹) = u * (s : G) * u⁻¹ * (s : G)⁻¹ := by group
      change ⁅u, (s : G)⁆ ∈ U
      rw [commutatorElement_def]
      simpa [hEq] using this
    · have hsu : u * (s : G) * u⁻¹ ∈ R0 :=
        (Subgroup.mem_normalizer_iff.mp (hRnormR0 huR) (s : G)).mp s.2
      have : (u * (s : G) * u⁻¹) * (s : G)⁻¹ ∈ R0 := R0.mul_mem hsu (R0.inv_mem s.2)
      change ⁅u, (s : G)⁆ ∈ R0
      rw [commutatorElement_def]
      exact this
  have hcommM : ⁅u, (s : G)⁆ ∈ M := (hR0R hcomm.2 |> Subgroup.mem_inf.mp).1
  have hmap : ((ψ (⟨⁅u, (s : G)⁆, hcomm.2⟩ : ↥R0) : ↥(imgQ M R0)) : MBar M) =
      QuotientGroup.mk' (pCore 2 ↥M) ⟨u, huM⟩ *
        QuotientGroup.mk' (pCore 2 ↥M) ⟨(s : G), sM⟩ *
        (QuotientGroup.mk' (pCore 2 ↥M) ⟨u, huM⟩)⁻¹ *
        (QuotientGroup.mk' (pCore 2 ↥M) ⟨(s : G), sM⟩)⁻¹ := by
    rw [r0BarMap_apply]
    rw [show (⟨⁅u, (s : G)⁆, hcommM⟩ : ↥M) =
      (⁅(⟨u, huM⟩ : ↥M), (⟨(s : G), sM⟩ : ↥M)⁆ : ↥M) from
      Subtype.ext (by rfl)]
    rw [map_commutatorElement]
    rfl
  have hψs : ((ψ s : ↥(imgQ M R0)) : MBar M) =
      QuotientGroup.mk' (pCore 2 ↥M) ⟨(s : G), sM⟩ := r0BarMap_apply hS6' A B s
  rw [hψs, ← hmap]
  exact Subgroup.mem_map.mpr ⟨(ψ (⟨⁅u, (s : G)⁆, hcomm.2⟩ : ↥R0) : ↥(imgQ M R0)),
    Subgroup.mem_map.mpr ⟨⟨⁅u, (s : G)⁆, hcomm.2⟩,
      Subgroup.mem_subgroupOf.mpr hcomm, rfl⟩, rfl⟩

theorem commutator_U_r0 (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) (h5 : 5 ≤ n) {u : G}
    (hu : u ∈ inSubgroup (Op_p'p 2) (rOf M h)) {r : G} (hr : r ∈ r0Of M V (A ⊔ B)) :
    ⁅u, r⁆ ∈ Pc M V := by
  classical
  obtain ⟨hS1, -, -, -, -, hS6, hS7, -, hS9, -⟩ := h72 A B h hD
  let hS6' : Sec6Hyp M V := hS.toSec6Hyp
  set R0 : Subgroup G := r0Of M V (A ⊔ B)
  set U : Subgroup G := inSubgroup (Op_p'p 2) (rOf M h)
  have hKbar : CFSG.IsQuasisimple ↥(imgQ M R0) := isQuasisimple_imgQ_r0 hS hS9 h5
  let ψ := r0BarMap hS6' A B
  have hψ : Function.Surjective ψ := r0BarMap_surjective hS6' A B
  have hR0R : R0 ≤ rOf M h :=
    (L2Datum.r0_le_inf_cenOf hS6' hD).trans (L2Datum.inf_cenOf_le_rOf hD)
  have hRnormR0 : rOf M h ≤ Subgroup.normalizer (R0 : Set G) :=
    L2Datum.rOf_le_normalizer_r0 hS6' hD hS6
  have hRnormU : rOf M h ≤ Subgroup.normalizer (U : Set G) := Sec7.rOf_le_normalizer_Op_p'p M h
  let Z2 : Subgroup ↥(imgQ M R0) := ((U ⊓ R0).subgroupOf R0).map ψ
  have hZ2_cent := image_U_inf_r0_central hS hD hS1 hS6 hS7 hS9 h5
  have hZ2_cent' : ∀ c ∈ Z2, ∀ k ∈ (⊤ : Subgroup ↥(imgQ M R0)), c * k = k * c := by
    intro c hc k hk
    exact (Subgroup.mem_center_iff.mp (hZ2_cent hc) k).symm
  let Z2' : Subgroup (MBar M) := Z2.map (imgQ M R0).subtype
  have hZ2'_cent : ∀ c ∈ Z2', ∀ k ∈ (imgQ M R0 : Subgroup (MBar M)), c * k = k * c := by
    intro c hc k hk
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hc
    simpa using congrArg Subtype.val (hZ2_cent' z hz ⟨k, hk⟩ (Subgroup.mem_top _))
  have hK : ⁅(imgQ M R0 : Subgroup (MBar M)), imgQ M R0⁆ = imgQ M R0 := by
    have hmap := Subgroup.map_subtype_commutator (imgQ M R0)
    rw [hKbar.1.commutator_eq_top, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have huR : u ∈ rOf M h := by
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact x.2
  have huM : u ∈ M := (Subgroup.mem_inf.mp huR).1
  have hrM : r ∈ M := (hR0R hr |> Subgroup.mem_inf.mp).1
  have hx := commutator_mem_image hS hD hS6 hu huM
  have hZ2'le : Z2' ≤ (imgQ M R0 : Subgroup (MBar M)) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact z.2
  have hcentral := CFSG.Quasithin.H13.KGInspOdd.centralizes_of_commutator_mem hK
    hZ2'le hZ2'_cent hx
  have hcommR : QuotientGroup.mk' (pCore 2 ↥M) ⟨u, huM⟩ *
      QuotientGroup.mk' (pCore 2 ↥M) ⟨r, hrM⟩ =
      QuotientGroup.mk' (pCore 2 ↥M) ⟨r, hrM⟩ *
        QuotientGroup.mk' (pCore 2 ↥M) ⟨u, huM⟩ :=
    hcentral (QuotientGroup.mk' (pCore 2 ↥M) ⟨r, hrM⟩) (mk_mem_imgQ (x := ⟨r, hrM⟩) hr)
  have h1 : QuotientGroup.mk' (pCore 2 ↥M) (⁅(⟨u, huM⟩ : ↥M), (⟨r, hrM⟩ : ↥M)⁆) = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcommR
  have hmem := (hS.mk_eq_one_iff (⁅(⟨u, huM⟩ : ↥M), (⟨r, hrM⟩ : ↥M)⁆)).mp h1
  have hcoe : ((⁅(⟨u, huM⟩ : ↥M), (⟨r, hrM⟩ : ↥M)⁆ : ↥M) : G) = ⁅u, r⁆ := by
    exact map_commutatorElement (Subgroup.subtype M) (⟨u, huM⟩ : ↥M) (⟨r, hrM⟩ : ↥M)
  rwa [hcoe] at hmem

theorem mem_p0_of_two_five (hS : Sec7Hyp M V n f) (h71 : Sec7.Stmt71 M V)
    (h72 : Sec7.Stmt72 M V n f) (hAut : UnitaryAutCentralizer) (hD : L2Datum M V A B h)
    (h5 : 5 ≤ n) {y : G} (hyR : y ∈ rOf M h) (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hyR₀ : ∀ r ∈ r0Of M V (A ⊔ B), ⁅y, r⁆ ∈ Pc M V) : y ∈ p0Of M V (A ⊔ B) := by
  obtain ⟨hS1, -, -, -, -, -, -, -, hS9, -⟩ := h72 A B h hD
  have hf2 : 2 ≤ f := irredHf2 hS
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hXM : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  have hhM : h ∈ M := hXM hD.mem
  have hyM : y ∈ M := hyR.1
  have hP0R : p0Of M V (A ⊔ B) ≤ rOf M h := L2Datum.p0_le_rOf hS.toSec6Hyp hD
  have hR0R : r0Of M V (A ⊔ B) ≤ rOf M h :=
    (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans (L2Datum.inf_cenOf_le_rOf hD)
  let ybar : MBar M := QuotientGroup.mk' (pCore 2 ↥M) ⟨y, hyM⟩
  have hy2M : IsPGroup 2 (Subgroup.zpowers (⟨y, hyM⟩ : ↥M)) := by
    have hcomap : (Subgroup.zpowers y).subgroupOf M = Subgroup.zpowers (⟨y, hyM⟩ : ↥M) := by
      ext z
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [← hcomap]
    exact hy2.comap_of_injective M.subtype M.subtype_injective
  have hybar2 : IsPGroup 2 (Subgroup.zpowers ybar) := by
    have h := IsPGroup.map hy2M (QuotientGroup.mk' (pCore 2 ↥M))
    rwa [MonoidHom.map_zpowers] at h
  have hybarR0 : ybar ∈ Subgroup.centralizer (imgQ M (r0Of M V (A ⊔ B)) : Set (MBar M)) :=
    (Sec6Hyp.mk_mem_centralizer_imgQ_iff hS.toSec6Hyp
      ((L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans inf_le_left) ⟨y, hyM⟩).mpr hyR₀
  have hperp := L2Datum.perpRoots_eq hS.toSec6Hyp hD
  have hybarperp : ybar ∈ Subgroup.centralizer
      (perpRoots (imgQ M '' sigmaSet M V) (imgQ M A ⊔ imgQ M B) : Set (MBar M)) := by
    rw [hperp]
    exact hybarR0
  have hybarh : ybar ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩} : Set (MBar M)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyh : h * y = y * h := Subgroup.mem_centralizer_iff.mp hyR.2 h (Subgroup.mem_zpowers h)
    have hcomm : (⟨y, hyM⟩ : ↥M) * ⟨h, hhM⟩ = ⟨h, hhM⟩ * ⟨y, hyM⟩ := Subtype.ext hyh.symm
    rw [← map_mul, ← map_mul, hcomm]
  have hodd := Sec6Hyp.odd_card_centralizer_imgQ_m0Of hS.toSec6Hyp h71
  have hAut' := hAut (MBar M) (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f n
    hS.one_le h5 hf2 (hS.sec5.imgQ_m0Of_normal) hS.m0 hodd
    (imgQ M A) ⟨A, hD.memA, rfl⟩ (imgQ M B) ⟨B, hD.memB, rfl⟩
    (Sec6Hyp.isL2Gen_imgQ hS.toSec6Hyp hD.memA hD.memB hD.l2)
    (QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩) ?_ ?_ ybar ⟨hybarperp, hybarh⟩ hybar2
  · have hybar1 : ybar = 1 :=
      CFSG.Timmesfeld.Bridge.eq_one_of_mem_odd_of_mem_two hodd hybar2 hAut'
        (Subgroup.mem_zpowers ybar)
    have hyP : y ∈ Pc M V := (hS.mk_eq_one_iff ⟨y, hyM⟩).mp hybar1
    rw [← hS1]
    exact Subgroup.mem_inf.mpr ⟨hyP, hyR.2⟩
  · have hmem : (QuotientGroup.mk' (pCore 2 ↥M) ⟨h, hhM⟩) ∈
        imgQ M (A ⊔ B) := mk_mem_imgQ hD.mem
    rwa [imgQ_sup hAM hBM] at hmem
  · rw [L2Datum.orderOf_mk hS.toSec6Hyp hD hhM, hS.card_V]

end L2Datum

end CFSG.RankThree.GF2n.Tim81
