module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOmNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorCalib
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorCount
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorFrame
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorEta
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorHyp
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorIso
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorTorus
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalMarking
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.RankThree.Classical2

private theorem oaChart_map_orthDerived {F V V' : Type} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup V'] [Module F V'] {Q : QuadraticForm F V} {Q' : QuadraticForm F V'}
    (Θ : V' ≃ₗ[F] V) (hΘ : ∀ v, Q (Θ v) = Q' v) :
    (orthDerived Q').map Θ.autCongr.toMonoidHom = orthDerived Q := by
  have hO : (TauCeti.QuadraticMap.orthogonalGroup Q').map Θ.autCongr.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    simp only [Subgroup.mem_map, TauCeti.QuadraticMap.mem_orthogonalGroup_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨h, hh, rfl⟩ v
      rw [LinearEquiv.autCongr_apply_apply, hΘ, hh, ← hΘ, Θ.apply_symm_apply]
    · intro hg
      refine ⟨Θ.autCongr.symm g, fun v => ?_, MulEquiv.apply_symm_apply _ _⟩
      rw [LinearEquiv.autCongr_symm_apply_apply, ← hΘ, ← hΘ, Θ.apply_symm_apply, hg]
  show (⁅_, _⁆ : Subgroup (V' ≃ₗ[F] V')).map _ = ⁅_, _⁆
  rw [Subgroup.map_commutator, hO]

theorem exists_normOmega_chart_calibrated {G : Type} [Group G] [Finite G] {L Bs : Subgroup G}
    {x : G} {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hBsL : ∀ b : Bs, (b : G) ∈ L ↔ eta b i0 = 1) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * n) (ψ : L ≃* orthDerived Q)
    {K : Type} [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (E : QuadExt F K (unitaryInvolution K 2 1)) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ∃ (π : Fin (n - 1) ≃ {i : Fin n // i ≠ i0}) (χ : normOmega E (n - 1) ≃* L),
      ∀ (b : Bs) (hb : (b : G) ∈ L) (v : (F × F) × (Fin (n - 1) → K)),
        (((χ.symm ⟨b, hb⟩ : ↥(normOmega E (n - 1))) :
            ((F × F) × (Fin (n - 1) → K)) ≃ₗ[F] ((F × F) × (Fin (n - 1) → K)))) v =
          (v.1, fun i => ζ ^ (Multiplicative.toAdd (eta b (π i))).val * v.2 i) := by
  classical
  have hm3 : 3 ≤ n - 1 := by omega
  have hm2 : 2 ≤ n - 1 := by omega
  have hF : Nat.card F = 2 := OrthAnchor.card_eq_two_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  obtain ⟨hEab, hEcard, hEsc⟩ := OrthAnchor.bsL_data eta hBsL hx hxL hLx hstar
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup ↥(orthDerived Q), A = (Bs.subgroupOf L).map ψ.toMonoidHom :=
    ⟨_, rfl⟩
  have hAab : CFSG.Open.IsElemAbelian 3 A := hAdef ▸ CFSG.SectionRank.isElemAbelian_map hEab _
  have hAcard : Nat.card A = 3 ^ (n - 1) := by
    rw [hAdef, Subgroup.card_map_of_injective ψ.injective, hEcard]
  have hAsc : ∀ g ∈ Subgroup.centralizer (A : Set ↥(orthDerived Q)), g ^ 3 = 1 → g ∈ A := by
    intro g hg hg3
    have hc : ψ.symm g ∈ Subgroup.centralizer (Bs.subgroupOf L : Set ↥L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hgh := Subgroup.mem_centralizer_iff.mp hg (ψ h)
        (hAdef ▸ Subgroup.mem_map_of_mem ψ.toMonoidHom hh)
      apply ψ.injective
      rw [map_mul, map_mul, ψ.apply_symm_apply]
      exact hgh
    have h3 : ψ.symm g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    have hmem := hEsc _ hc h3
    rw [hAdef]
    exact ⟨_, hmem, ψ.apply_symm_apply g⟩
  obtain ⟨k, M, _, _, _, τ, U, _, _, Φ, hcardM, hτsq, hpolar, hN, hEdiag, hEfull⟩ :=
    exists_normFrame_of_isElemAbelian_orth hF hQ hAab hAsc
  have hkcard : Nat.card A = 3 ^ k := OrthAnchor.card_normFrame_torus Φ hcardM hEdiag hEfull
  have hkm : k = n - 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hkcard.symm.trans hAcard)
  subst hkm
  have hdimU : Module.finrank F U = 2 := by
    have := OrthAnchor.finrank_normFrame hF Φ hcardM
    omega
  obtain ⟨e, f, he, hf, hef⟩ := OrthAnchor.exists_hypPair_of_normFrame hF hQ hAsc Φ hdimU hpolar hN
    fun a ha => (hEdiag a ha).imp fun _ h => h.2
  obtain ⟨Θ, hΘQ, hΘA, hΘA'⟩ := OrthAnchor.exists_normHyp_isometry_of_normFrame hF Φ hcardM hτsq
    hdimU hN hEdiag hEfull he hf hef E hζ
  let χ₀ : normOmega E (n - 1) ≃* orthDerived Q :=
    (Θ.autCongr.subgroupMap (normOmega E (n - 1))).trans
      (MulEquiv.subgroupCongr (by
        rw [← MulEquiv.toMonoidHom_eq_coe]
        exact oaChart_map_orthDerived Θ hΘQ))
  have hχ₀ : ∀ (g : normOmega E (n - 1)) (w : V),
      ((χ₀ g : orthDerived Q) : V ≃ₗ[F] V) w =
        Θ ((g : ((F × F) × (Fin (n - 1) → K)) ≃ₗ[F] ((F × F) × (Fin (n - 1) → K))) (Θ.symm w)) := by
    intro g w
    simp only [χ₀, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.coe_subgroupMap_apply, LinearEquiv.autCongr_apply_apply]
  let χ₁ : normOmega E (n - 1) ≃* L := χ₀.trans ψ.symm
  let τt := OrthAnchor.zetaTorus E hm2 hζ
  have hχ₀τ : ∀ (t : Fin (n - 1) → Multiplicative (ZMod 3)) (a : orthDerived Q),
      (∀ v, (a : V ≃ₗ[F] V) (Θ v) =
        Θ (v.1, fun i => ζ ^ (Multiplicative.toAdd (t i)).val * v.2 i)) → χ₀ (τt t) = a := by
    intro t a hat
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    rw [hχ₀, OrthAnchor.zetaTorus_apply, ← hat, Θ.apply_symm_apply]
  have hcor1 : ∀ (b : ↥Bs) (hb : (b : G) ∈ L), ∃ t, χ₁.symm ⟨b, hb⟩ = τt t := by
    intro b hb
    have hmem : ψ ⟨b, hb⟩ ∈ A := by
      rw [hAdef]
      exact Subgroup.mem_map_of_mem ψ.toMonoidHom (Subgroup.mem_subgroupOf.mpr b.2)
    obtain ⟨t, ht⟩ := hΘA _ hmem
    refine ⟨t, ?_⟩
    apply χ₁.injective
    rw [MulEquiv.apply_symm_apply]
    change ⟨b, hb⟩ = ψ.symm (χ₀ (τt t))
    rw [hχ₀τ t _ ht, MulEquiv.symm_apply_apply]
  have hcor2 : ∀ t, ((χ₁ (τt t) : L) : G) ∈ Bs := by
    intro t
    obtain ⟨a, ha, hat⟩ := hΘA' t
    rw [hAdef] at ha
    obtain ⟨h, hh, rfl⟩ := ha
    change ((ψ.symm (χ₀ (τt t)) : L) : G) ∈ Bs
    rw [hχ₀τ t _ hat]
    change ((ψ.symm (ψ h) : L) : G) ∈ Bs
    rw [MulEquiv.symm_apply_apply]
    exact Subgroup.mem_subgroupOf.mp hh
  let β : (Fin (n - 1) → Multiplicative (ZMod 3)) →* ↥Bs :=
    { toFun := fun t => ⟨(χ₁ (τt t) : G), hcor2 t⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply Subtype.ext
        simp }
  have hβ : ∀ t, ((β t : ↥Bs) : G) = (χ₁ (τt t) : G) := fun _ => rfl
  have hβL : ∀ t, ((β t : ↥Bs) : G) ∈ L := fun t => (χ₁ (τt t)).2
  have hβinj : Function.Injective β := by
    intro s t hst
    have h1 : χ₁ (τt s) = χ₁ (τt t) := Subtype.ext (by rw [← hβ, ← hβ, hst])
    exact OrthAnchor.zetaTorus_injective E hm2 hζ (χ₁.injective h1)
  have hβsymm : ∀ (t : Fin (n - 1) → Multiplicative (ZMod 3)) (b : ↥Bs) (hb : (b : G) ∈ L),
      χ₁.symm ⟨b, hb⟩ = τt t → β t = b := by
    intro t b hb h
    apply Subtype.ext
    rw [hβ, ← h, MulEquiv.apply_symm_apply]
  obtain ⟨π₀⟩ : Nonempty (Fin (n - 1) ≃ {i : Fin n // i ≠ i0}) := by
    rw [← Fintype.card_eq, Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
  let T₀ : (Fin (n - 1) → Multiplicative (ZMod 3)) →* (Fin (n - 1) → Multiplicative (ZMod 3)) :=
    { toFun := fun t j => eta (β t) (π₀ j)
      map_one' := by
        funext j
        simp
      map_mul' := fun s t => by
        funext j
        simp }
  have hT₀ : ∀ t j, T₀ t j = eta (β t) (π₀ j) := fun _ _ => rfl
  have hT₀inj : Function.Injective T₀ := by
    intro s t hst
    apply hβinj
    apply eta.injective
    funext i
    by_cases hi : i = i0
    · subst hi
      rw [(hBsL _).mp (hβL s), (hBsL _).mp (hβL t)]
    · have h := congrFun hst (π₀.symm ⟨i, hi⟩)
      rwa [hT₀, hT₀, Equiv.apply_symm_apply] at h
  let T : MulAut (Fin (n - 1) → Multiplicative (ZMod 3)) :=
    MulEquiv.ofBijective T₀ ⟨hT₀inj, Finite.injective_iff_surjective.mp hT₀inj⟩
  have hT : ∀ t j, T t j = eta (β t) (π₀ j) := fun _ _ => rfl
  have hkey : ∀ γ : MulAut (Fin (n - 1) → Multiplicative (ZMod 3)),
      (∃ φ ∈ ggInduced L Bs, ∀ (y : ↥Bs) (j : Fin (n - 1)),
        eta (φ y) (π₀ j) = γ (fun k => eta y (π₀ k)) j) →
      SpCoord.IsSignedPerm ⇑(T⁻¹ * γ * T) := by
    rintro γ ⟨φ, ⟨h, hhL, -, hφ⟩, hγ⟩
    have hφL : ∀ t, ((φ (β t) : ↥Bs) : G) ∈ L := fun t => by
      rw [hφ]
      exact L.mul_mem (L.mul_mem hhL (hβL t)) (L.inv_mem hhL)
    have hnorm : ∀ t, ∃ t', χ₁.symm ⟨h, hhL⟩ * τt t * (χ₁.symm ⟨h, hhL⟩)⁻¹ = τt t' ∧
        β t' = φ (β t) := by
      intro t
      obtain ⟨t', ht'⟩ := hcor1 (φ (β t)) (hφL t)
      refine ⟨t', ?_, hβsymm t' _ _ ht'⟩
      rw [← ht']
      apply χ₁.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hφ, hβ]
    obtain ⟨ρ, ε, hε, hρ⟩ := OrthAnchor.zetaTorus_normalizer E hm2 hζ (χ₁.symm ⟨h, hhL⟩)
      fun t => (hnorm t).imp fun _ h => h.1
    refine ⟨ρ, ε, hε, fun t i => ?_⟩
    obtain ⟨t', ht'1, ht'2⟩ := hnorm t
    have hTt' : (T⁻¹ * γ * T) t = t' := by
      rw [MulAut.mul_apply, MulAut.mul_apply]
      apply T.injective
      rw [MulAut.apply_inv_self]
      funext j
      rw [hT t' j, ht'2, hγ]
      exact congrFun (congrArg γ (funext (hT t))) j
    rw [hTt']
    exact hρ t t' ht'1 i
  obtain ⟨ρ', ε', hε', hT'⟩ := OrthAnchor.isSignedPerm_of_conj_generators hm3
    (fun i => hkey _ (OrthAnchor.exists_ggInduced_sgnAut_of_bCoordinateBlock eta hA π₀ i))
    fun a b hab => hkey _ (OrthAnchor.exists_ggInduced_swap_of_bCoordinateBlock eta hA π₀ hab)
  let S : Finset (Fin (n - 1)) := Finset.univ.filter fun i => ε' i = -1
  let Ξ := normOmegaConj E (normBar_mem_orthogonalGroup E S)
  refine ⟨ρ'.trans π₀, Ξ.symm.trans χ₁, fun b hb v => ?_⟩
  obtain ⟨t, ht⟩ := hcor1 b hb
  have hβt : β t = b := hβsymm t b hb ht
  have h1 : (Ξ.symm.trans χ₁).symm ⟨b, hb⟩ = τt (fun i => if i ∈ S then (t i)⁻¹ else t i) := by
    rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm, ht]
    exact OrthAnchor.normOmegaConj_normBar_zetaTorus E hm2 hζ S t
  rw [h1, OrthAnchor.zetaTorus_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  have hi := hT' t i
  rw [hT, hβt] at hi
  simp only [Equiv.trans_apply]
  congr 3
  by_cases hiS : i ∈ S
  · have hεi : ε' i = -1 := (Finset.mem_filter.mp hiS).2
    rw [if_pos hiS, toAdd_inv, hi, hεi, neg_one_mul]
  · have hεi : ε' i = 1 := (hε' i).resolve_right fun h =>
      hiS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [if_neg hiS, hi, hεi, one_mul]

theorem exists_omKFrame_calibrated {G : Type} [Group G] [Finite G] {L Bs : Subgroup G}
    {x : G} {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hBsL : ∀ b : Bs, (b : G) ∈ L ↔ eta b i0 = 1) (hx : x ∈ Bs) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * n) (ψ : L ≃* orthDerived Q)
    {K : Type} [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (E : QuadExt F K (unitaryInvolution K 2 1)) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ∃ π' : Fin (n - 1 + 1) ≃ Fin n, π' (Fin.last (n - 1)) = i0 ∧
      ∃ (κ : normOmega E (n - 1) →* G) (χ : Multiplicative (ZMod 3) →* Kˣ),
        GGSecFiveBPermOmKFrame E Bs L eta π' κ χ := by
  obtain ⟨π, χ, hχ⟩ :=
    exists_normOmega_chart_calibrated hn eta hBsL hx hxL hLx hstar hA hQ hdim ψ E hζ
  obtain ⟨π', hπ', hframe⟩ := OrthAnchor.omKFrame_of_calibrated eta hBsL hx hxL hLx hA E
    (OrthAnchor.zetaChar hζ) (OrthAnchor.zetaChar_injective hζ) (OrthAnchor.zetaChar_apply hζ)
    π χ hχ
  exact ⟨π', hπ', _, _, hframe⟩

private theorem oaH_exists_zeta_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    ∃ ζ : K, ζ ^ 2 + ζ + 1 = 0 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hcard : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
    simp
  obtain ⟨ζ, -, hζnotmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hζ0 : ζ ≠ 0 := by
    intro h
    apply hζnotmem
    simp [h]
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hζnotmem
    simp [h]
  have hζ3 : ζ ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one ζ hζ0
    rw [← Nat.card_eq_fintype_card] at h
    rw [hK] at h
    norm_num at h
    exact h
  have hprod : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
    calc
      (ζ - 1) * (ζ ^ 2 + ζ + 1) = ζ ^ 3 - 1 := by ring
      _ = 0 := by rw [hζ3]; ring
  have hζm1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  exact ⟨ζ, (mul_eq_zero.mp hprod).resolve_left hζm1⟩

section Context


theorem exists_omKFrame_of_qTwoOrth_over {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {n : ℕ}
    (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) p Bs L)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    p = 3 ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (F : Type) (_ : Field F) (_ : Algebra F K)
        (E : QuadExt F K (unitaryInvolution K 2 1)), Nat.card F = 2 ∧
        ∃ π' : Fin (n - 1 + 1) ≃ Fin n, π' (Fin.last (n - 1)) = i0 ∧
          ∃ (κ : normOmega E (n - 1) →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
            GGSecFiveBPermOmKFrame E Bs L eta π' κ χ := by
  obtain ⟨hp, -, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hX, lab, hlab, hraw⟩ := hLab
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hR', hna, θ, hθ⟩ := hQ
  obtain ⟨hS, hN, hinner⟩ := hθ
  obtain ⟨hCoordB, hnlab, htag⟩ := hS
  have hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L := by
    refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hR, hna, θ, hP⟩
    exact ⟨hR, hna, θ, rfl, hP.2.1, hP.2.2⟩
  have htag' : (lab.tag = .D ∧ 5 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank) := by
    rcases hCoordB with ⟨hBC, hr, hpn⟩ | ⟨htwD, hr, hpn⟩ | ⟨hD, hr, hodd, hn1, hp3⟩ |
        ⟨hA, hr, hn1, hp3⟩
    · rcases hBC with hB | hC
      · rw [hB] at htag; simp at htag
      · rw [hC] at htag; simp at htag
    · refine Or.inr ⟨htwD, ?_⟩
      rw [hr]; exact hn
    · refine Or.inl ⟨hD, ?_⟩
      rw [hr]
      have h4 : n ≠ 4 := by
        intro h; rw [h] at hodd; norm_num at hodd
      omega
    · rw [hA] at htag; simp at htag
  have hp3 : p = 3 := by
    rcases hCoordB with ⟨hBC, hr, hpn⟩ | ⟨htwD, hr, hpn⟩ | ⟨hD, hr, hodd, hn1, hp3⟩ |
        ⟨hA, hr, hn1, hp3⟩
    · rcases hBC with hB | hC
      · rw [hB] at htag; simp at htag
      · rw [hC] at htag; simp at htag
    · rcases hpn with hdiv | ⟨heven, hdiv⟩
      · have : p ∣ 1 := by simpa [hnlab] using hdiv
        have hp2 := hp.two_le
        have hle := Nat.le_of_dvd (by norm_num : 0 < 1) this
        omega
      · have : p ∣ 3 := by simpa [hnlab] using hdiv
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
    · exact hp3
    · exact hp3
  have hrank : lab.rank = n := by
    rcases hCoordB with ⟨hBC, hr, hpn⟩ | ⟨htwD, hr, hpn⟩ | ⟨hD, hr, hodd, hn1, hp3⟩ |
        ⟨hA, hr, hn1, hp3⟩
    · rcases hBC with hB | hC
      · rw [hB] at htag; simp at htag
      · rw [hC] at htag; simp at htag
    · exact hr
    · exact hr
    · rw [hA] at htag; simp at htag
  subst p
  have hq2 : GGLabQTwo 3 lab := by
    rw [GGLabQTwo]
    omega
  obtain ⟨F₀, hFieldF, hFiniteF, hCharF, V, hAddV, hModV, hFinDimV, Q, hF2, hQ', hdim, htype,
      hT, hZ, θ', e, he, hinner'⟩ :=
    QTwoOrthogonalCav.exists_orthogonal_original_realization hq2 htag' hmark hN
  let : Field F₀ := hFieldF
  let : Finite F₀ := hFiniteF
  let : CharP F₀ 2 := hCharF
  let : AddCommGroup V := hAddV
  let : Module F₀ V := hModV
  let : FiniteDimensional F₀ V := hFinDimV
  have hBsL : ∀ b : ↥Bs, ((b : G) ∈ L ↔ eta b i0 = 1) :=
    ggBstar_mem_iff_coord_eq_one hcfg hZ hN eta i0 hL
  have hxL : x ∉ L := by
    intro hxL
    have hxcenter : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2))
    have hxbot : (⟨x, hxL⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := by
      rw [← hZ]
      exact hxcenter
    have hxeq1 : (⟨x, hxL⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hxbot
    exact hx1 (congrArg Subtype.val hxeq1)
  letI : Fintype F₀ := Fintype.ofFinite F₀
  have hF0card : Fintype.card F₀ = 2 := by
    rw [← Nat.card_eq_fintype_card, hF2]
  let σ : ZMod 2 ≃+* F₀ := ZMod.ringEquivOfPrime F₀ Nat.prime_two hF0card
  letI algF₀K : Algebra F₀ K :=
    ((ZMod.castHom (dvd_refl 2) K).comp σ.symm.toRingHom).toAlgebra
  have hF2_1 : Nat.card F₀ = 2 ^ 1 := by rw [hF2]; norm_num
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let E : QuadExt F₀ K (unitaryInvolution K 2 1) :=
    CFSG.ClassicalInvolution.PhanDn.quadExt_of_card_of_char_two 1 hF2_1 hK'
  obtain ⟨ζ, hζeq⟩ := oaH_exists_zeta_of_card_four hK
  have hdim' : Module.finrank F₀ V = 2 * n := by
    rw [hdim, hrank]
  obtain ⟨π', hπ', κ, χ, hframe⟩ :=
    exists_omKFrame_calibrated hn eta hBsL hxBs hxL hLx hstar hL hQ' hdim' e E hζeq
  exact ⟨rfl, hZ, hN, F₀, inferInstance, algF₀K, E, hF2, π', hπ', κ, χ, hframe⟩

theorem exists_omKFrame_of_qTwoOrth {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {n : ℕ}
    (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) p Bs L) :
    p = 3 ∧ Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt F K (unitaryInvolution K 2 1)), Nat.card F = 2 ∧
        ∃ π' : Fin (n - 1 + 1) ≃ Fin n, π' (Fin.last (n - 1)) = i0 ∧
          ∃ (κ : normOmega E (n - 1) →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
            GGSecFiveBPermOmKFrame E Bs L eta π' κ χ := by
  obtain ⟨hp3, hZ, hN, F, hFieldF, hAlgFK, E, hF2, π', hπ', κ, χ, hframe⟩ :=
    exists_omKFrame_of_qTwoOrth_over (K := GaloisField 2 2) hcfg hn eta hL hLab
      (by
        rw [GaloisField.card 2 2 (by norm_num)]
        norm_num)
  exact ⟨hp3, hZ, hN, F, GaloisField 2 2, hFieldF, inferInstance, hAlgFK, inferInstance,
    inferInstance, E, hF2, π', hπ', κ, χ, hframe⟩

end Context

end CFSG.StandardType

end
