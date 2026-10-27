module

public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenAsmA
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalReflAux

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open QuadraticMap Module
open CFSG.StandardType.OmNsRootGen RealKGOmega SpCoord
open CFSG.RankThree.Classical2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem exists_totallySingular_three :
    ∃ T : Submodule K (Fin 4 ⊕ Fin 4 → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qPlusForm K 4 v = 0 := by
  classical
  let v : Fin 3 → (Fin 4 ⊕ Fin 4 → K) := fun i =>
    Pi.single (Sum.inl ⟨i.val, by omega⟩) (1 : K)
  have hli : LinearIndependent K v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 := congrFun hg (Sum.inl ⟨i.val, by omega⟩)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, Pi.single_apply] at h1
    rw [Finset.sum_eq_single_of_mem i hi] at h1
    · simpa using h1
    · intro j hj hji
      rw [if_neg]
      · ring
      · intro h
        exact hji (Fin.ext (by simpa using congrArg Fin.val (Sum.inl_injective h))).symm
  have hsupp : ∀ x ∈ Submodule.span K (Set.range v), ∀ k : Fin 4, x (Sum.inr k) = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩ k
      simp [v]
    · intro k; simp
    · intro a b _ _ ha hb k
      simp [ha k, hb k]
    · intro c a _ ha k
      simp [ha k]
  refine ⟨Submodule.span K (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · intro x hx
    rw [TableBOrth.qPlusForm, CFSG.LieType.Universal.Spin.quadPlus_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [hsupp x hx k, mul_zero]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

private theorem frameData (hK : Nat.card K = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 2 * 4) {E : Subgroup ↥(orthDerived Q)}
    (hE : IsElemAbelian 3 E) (hcardE : Nat.card E = 3 ^ 4)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ (U : Fin 4 → Submodule K V) (e : Fin 4 → ↥(orthDerived Q)) (u : Fin 4 → V) (c t : K)
      (τ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥(orthDerived Q)),
      IsCoherentFrame Q 3 U e E u c t ∧ Function.Injective τ ∧ τ.range = E ∧
        (∀ a, τ (Pi.mulSingle a (Multiplicative.ofAdd 1)) = e a) ∧ (⨆ j, U j) = ⊤ ∧
        (∀ f, Module.finrank K
          (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
            ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V)) =
          2 * (Finset.univ.filter (fun a => f a = 1)).card) := by
  classical
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hpq : 3 ∣ Nat.card K + 1 := by simp [hK]
  obtain ⟨k, U, e, hF, hcase⟩ :=
    OmNsRootGen.exists_planeFrame_of_selfCentralizing (F := K) (V := V) (Q := Q) (p := 3) (ℓ := 4)
      hQ hp hp2 hpq hdim (by norm_num) hE hsc
  obtain ⟨τ₀, hτ₀inj, hτ₀E, hτ₀, -⟩ := CFSG.StandardType.OmNsRootGen.exists_frameTorus hF hp
  have hk : k = 4 := by
    have h1 : Nat.card E = 3 ^ k := by
      rw [← hτ₀E]
      rw [Nat.card_congr (MonoidHom.ofInjective hτ₀inj).toEquiv.symm]
      simp [Nat.card_fun, Nat.card_zmod]
    have : 3 ^ k = 3 ^ 4 := by rw [← h1, hcardE]
    exact Nat.pow_right_injective (by norm_num) this
  subst hk
  have htop : (⨆ j, U j) = ⊤ := by
    rcases hcase with ⟨-, htop⟩ | ⟨hcon, -⟩
    · exact htop
    · exact absurd hcon (by norm_num)
  obtain ⟨e', u, c, t, hF', -⟩ :=
    OmNsRootGen.exists_coherentFrame (Q := Q) (p := 3) (U := U) (e := e) (E := E) hF hp hp2 hpq
      (by norm_num : 1 ≤ 4)
  obtain ⟨τ, hτinj, hτE, hτ, hact⟩ :=
    CFSG.StandardType.OmNsRootGen.exists_frameTorus hF'.toIsPlaneFrame hp
  have hfixdim : ∀ f, Module.finrank K
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        ((τ f : ↥(orthDerived Q)) : V ≃ₗ[K] V)) =
      2 * (Finset.univ.filter (fun a => f a = 1)).card :=
    fun f => finrank_fixedSpace_tau hF'.toIsPlaneFrame hp hQ hdim hτ hact f
  exact ⟨U, e', u, c, t, τ, hF', hτinj, hτE, hτ, htop, hfixdim⟩

end CFSG.StandardType.E6QTwo

end

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open QuadraticMap Module
open CFSG.StandardType.OmNsRootGen RealKGOmega SpCoord
open CFSG.RankThree.Classical2

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}
variable {U : Fin 4 → Submodule K V} {e : Fin 4 → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)} {u : Fin 4 → V} {c t : K}

private theorem omPlusRefl_false_left {i j : Fin 4} (hij : i < j) :
    omPlusRefl 3 (⟨(i, j), hij⟩, false) (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
      Pi.mulSingle j (Multiplicative.ofAdd 1) := by
  decide +kernel +revert

private theorem omPlusRefl_false_right {i j : Fin 4} (hij : i < j) :
    omPlusRefl 3 (⟨(i, j), hij⟩, false) (Pi.mulSingle j (Multiplicative.ofAdd 1)) =
      Pi.mulSingle i (Multiplicative.ofAdd 1) := by
  decide +kernel +revert

private theorem omPlusRefl_false_of_ne {i j d : Fin 4} (hij : i < j) (hdi : d ≠ i)
    (hdj : d ≠ j) :
    omPlusRefl 3 (⟨(i, j), hij⟩, false) (Pi.mulSingle d (Multiplicative.ofAdd 1)) =
      Pi.mulSingle d (Multiplicative.ofAdd 1) := by
  decide +kernel +revert

private theorem omPlusRefl_true_left {i j : Fin 4} (hij : i < j) :
    omPlusRefl 3 (⟨(i, j), hij⟩, true) (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
      (Pi.mulSingle j (Multiplicative.ofAdd 1))⁻¹ := by
  decide +kernel +revert

private theorem omPlusRefl_true_right {i j : Fin 4} (hij : i < j) :
    omPlusRefl 3 (⟨(i, j), hij⟩, true) (Pi.mulSingle j (Multiplicative.ofAdd 1)) =
      (Pi.mulSingle i (Multiplicative.ofAdd 1))⁻¹ := by
  decide +kernel +revert

private theorem omPlusRefl_true_of_ne {i j d : Fin 4} (hij : i < j) (hdi : d ≠ i)
    (hdj : d ≠ j) :
    omPlusRefl 3 (⟨(i, j), hij⟩, true) (Pi.mulSingle d (Multiplicative.ofAdd 1)) =
      Pi.mulSingle d (Multiplicative.ofAdd 1) := by
  decide +kernel +revert

private theorem frameSwap_conj (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 2 * 4) (hF : IsCoherentFrame Q 3 U e E u c t)
    (τ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (Multiplicative.ofAdd 1)) = e d)
    {i j : Fin 4} (hij : i < j) (f : Fin 4 → Multiplicative (ZMod 3)) :
    (⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim (by norm_num)⟩ :
        ↥(orthDerived Q)) * τ f *
      (⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim (by norm_num)⟩ :
        ↥(orthDerived Q))⁻¹ =
      τ (omPlusRefl 3 (⟨(i, j), hij⟩, false) f) := by
  let sw : ↥(orthDerived Q) :=
    ⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim (by norm_num)⟩
  have hsw2 : sw * sw = 1 := Subtype.ext (frameSwap_mul_self hF hij.ne)
  have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
  refine conj_eq_of_mulSingle τ sw (omPlusRefl 3 (⟨(i, j), hij⟩, false)) ?_ f
  intro d
  rw [hswinv]
  by_cases hdi : d = i
  · subst d
    have hs := omPlusRefl_false_left hij
    rw [hs, hτ j, hτ i]
    exact Subtype.ext (frameSwap_conj_left hF hij.ne)
  · by_cases hdj : d = j
    · subst d
      have hs := omPlusRefl_false_right hij
      rw [hs, hτ i, hτ j]
      exact Subtype.ext (frameSwap_conj_right hF hij.ne)
    · have hs := omPlusRefl_false_of_ne hij hdi hdj
      rw [hs, hτ d]
      exact Subtype.ext (frameSwap_conj_of_ne hF hij.ne hdi hdj)

private theorem signedSwap_conj (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 2 * 4) (hF : IsCoherentFrame Q 3 U e E u c t)
    (τ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥(orthDerived Q))
    (hτ : ∀ d, τ (Pi.mulSingle d (Multiplicative.ofAdd 1)) = e d)
    {i j : Fin 4} (hij : i < j) (f : Fin 4 → Multiplicative (ZMod 3)) :
    (⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim (by norm_num) hF⟩ :
        ↥(orthDerived Q)) * τ f *
      (⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim (by norm_num) hF⟩ :
        ↥(orthDerived Q))⁻¹ =
      τ (omPlusRefl 3 (⟨(i, j), hij⟩, true) f) := by
  let sw : ↥(orthDerived Q) :=
    ⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim (by norm_num) hF⟩
  have hsw2 : sw * sw = 1 := Subtype.ext (signedSwap_mul_self hF hij.ne)
  have hswinv : sw⁻¹ = sw := inv_eq_of_mul_eq_one_right hsw2
  refine conj_eq_of_mulSingle τ sw (omPlusRefl 3 (⟨(i, j), hij⟩, true)) ?_ f
  intro d
  rw [hswinv]
  by_cases hdi : d = i
  · subst d
    have hs : τ (omPlusRefl 3 (⟨(i, j), hij⟩, true) (Pi.mulSingle i (Multiplicative.ofAdd 1))) =
        (e j)⁻¹ := by
      rw [omPlusRefl_true_left hij, ← hτ j, ← map_inv]
    rw [hs, hτ i]
    exact Subtype.ext (signedSwap_conj_left hF hij.ne)
  · by_cases hdj : d = j
    · subst d
      have hs : τ (omPlusRefl 3 (⟨(i, j), hij⟩, true) (Pi.mulSingle j (Multiplicative.ofAdd 1))) =
          (e i)⁻¹ := by
        rw [omPlusRefl_true_right hij, ← hτ i, ← map_inv]
      rw [hs, hτ j]
      exact Subtype.ext (signedSwap_conj_right hF hij.ne)
    · have hs := omPlusRefl_true_of_ne hij hdi hdj
      rw [hs, hτ d]
      exact Subtype.ext (signedSwap_conj_of_ne hF hij.ne hdi hdj)

private theorem mem_normalizer_of_conj_torus
    {g : ↥(orthDerived Q)} {τ : (Fin 4 → Multiplicative (ZMod 3)) →* ↥(orthDerived Q)}
    (hτE : τ.range = E) {w : MulAut (Fin 4 → Multiplicative (ZMod 3))}
    (hgw : ∀ f, g * τ f * g⁻¹ = τ (w f)) (hg2 : g * g = 1) :
    g ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp (hτE ▸ hb)
    rw [hgw f]
    exact hτE ▸ MonoidHom.mem_range.mpr ⟨w f, rfl⟩
  · intro hb
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp (hτE ▸ hb)
    have hb' : b = τ (w f) := by
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = g * (τ f) * g⁻¹ := by rw [← hf, hginv]
        _ = τ (w f) := hgw f
    rw [hb']
    exact hτE ▸ MonoidHom.mem_range.mpr ⟨w f, rfl⟩

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open QuadraticMap Module
open CFSG.StandardType.OmNsRootGen RealKGOmega SpCoord
open CFSG.RankThree.Classical2

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}
variable {U : Fin 4 → Submodule K V} {e : Fin 4 → ↥(orthDerived Q)}
  {E : Subgroup ↥(orthDerived Q)} {u : Fin 4 → V} {c t : K}

private theorem frameSignedData (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 2 * 4)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E) (hcardE : Nat.card E = 3 ^ 4)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥E,
      (∀ g : ↥(orthDerived Q), g ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) →
        ∀ w : MulAut (Fin 4 → Multiplicative (ZMod 3)),
          (∀ f, g * (Θ f : ↥(orthDerived Q)) * g⁻¹ =
            (Θ (w f) : ↥(orthDerived Q))) → IsSignedPerm ⇑w) ∧
      (∀ (a : Fin 4) (g : ↥(orthDerived Q)),
        (∀ f, g * (Θ f : ↥(orthDerived Q)) * g⁻¹ =
          (Θ (sgnAut a f) : ↥(orthDerived Q))) → False) ∧
      (∀ x : OmPlusIdx 4, ∃ g ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)),
        ∀ f, g * (Θ f : ↥(orthDerived Q)) * g⁻¹ =
          (Θ (omPlusRefl 3 x f) : ↥(orthDerived Q))) ∧
      (∀ f, Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          (((Θ f : ↥E) : ↥(orthDerived Q)) : V ≃ₗ[K] V)) =
        2 * (Finset.univ.filter (fun a => f a = 1)).card) := by
  classical
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hpq : 3 ∣ Nat.card K + 1 := by simp [hK]
  have hpq' : ¬ 3 ∣ Nat.card K - 1 := by simp [hK]
  obtain ⟨U, e, u, c, t, τ, hF, hτinj, hτE, hτ, htop, hfixdim⟩ :=
    frameData (K := K) (V := V) (Q := Q) hK hQ hdim hE hcardE hsc
  let Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥E :=
    (MonoidHom.ofInjective hτinj).trans (MulEquiv.subgroupCongr hτE)
  have hΘ : ∀ f, (Θ f : ↥(orthDerived Q)) = τ f := fun f => rfl
  refine ⟨Θ, ?_, ?_, ?_, ?_⟩
  · intro g hgN w hw
    refine isSignedPerm_of_normalizer (g := g) (w := w) hQ hp hp2 hpq hT hF (by norm_num) hsc
      hτinj hτE hτ ?_
    intro f
    rw [← hΘ f, ← hΘ (w f)]
    exact hw f
  · intro a g hg
    have hv : ∃ v ∈ U a, v ≠ 0 ∧ Q v ≠ 0 := by
      obtain ⟨v, hvU, hv0⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.exists_ne_zero_mem_of_finrank_eq_two (U a)
          (hF.finrank_eq a)
      refine ⟨v, hvU, hv0, ?_⟩
      intro hQv
      refine hF.not_isPlusType a ⟨Submodule.span K ({⟨v, hvU⟩} : Set ↥(U a)), ?_, ?_⟩
      · rw [finrank_span_singleton (fun h => hv0 (congrArg Subtype.val h)), hF.finrank_eq a]
      · intro x hx
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hx
        simp [QuadraticMap.comp_apply, QuadraticMap.map_smul, hQv]
    obtain ⟨v, hvU, -, hQv⟩ := hv
    exact not_induces_sgnAut hQ hp hpq' hF.toIsPlaneFrame htop hτ hvU hQv g
      (fun f => by rw [← hΘ f, ← hΘ (sgnAut a f)]; exact hg f)
  · rintro ⟨⟨⟨i, j⟩, hij⟩, s | s⟩
    ·
      let g : ↥(orthDerived Q) :=
        ⟨frameSwap Q e u c t i j, frameSwap_mem_orthDerived hQ hdim (by norm_num)⟩
      have hconj : ∀ f, g * τ f * g⁻¹ = τ (omPlusRefl 3 (⟨(i, j), hij⟩, false) f) :=
        frameSwap_conj hQ hdim hF τ hτ hij
      have hgN : g ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) :=
        mem_normalizer_of_conj_torus hτE hconj (Subtype.ext (frameSwap_mul_self hF hij.ne))
      refine ⟨g, hgN, fun f => ?_⟩
      rw [hΘ f, hΘ (omPlusRefl 3 (⟨(i, j), hij⟩, false) f)]
      exact hconj f
    ·
      let g : ↥(orthDerived Q) :=
        ⟨signedSwap Q e u c t i j, signedSwap_mem_orthDerived hQ hdim (by norm_num) hF⟩
      have hconj : ∀ f, g * τ f * g⁻¹ = τ (omPlusRefl 3 (⟨(i, j), hij⟩, true) f) :=
        signedSwap_conj hQ hdim hF τ hτ hij
      have hgN : g ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) :=
        mem_normalizer_of_conj_torus hτE hconj (Subtype.ext (signedSwap_mul_self hF hij.ne))
      refine ⟨g, hgN, fun f => ?_⟩
      rw [hΘ f, hΘ (omPlusRefl 3 (⟨(i, j), hij⟩, true) f)]
      exact hconj f
  · intro f
    rw [hΘ f]
    exact hfixdim f

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open QuadraticMap Module
open CFSG.StandardType.OmNsRootGen RealKGOmega SpCoord
open CFSG.RankThree.Classical2
open CFSG.StandardType.OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem mem_normalizer_map_iff {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (E : Subgroup G) (g : G) :
    e g ∈ Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup G') : Set G') ↔
      g ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    rw [← Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective (K := E),
      ← Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective (K := E),
      show e.toMonoidHom (g * x * g⁻¹) =
        e.toMonoidHom g * e.toMonoidHom x * (e.toMonoidHom g)⁻¹ by simp]
    exact h (e x)
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [show e g * e x * (e g)⁻¹ = e (g * x * g⁻¹) by simp]
    change e.toMonoidHom x ∈ Subgroup.map e.toMonoidHom E ↔
      e.toMonoidHom (g * x * g⁻¹) ∈ Subgroup.map e.toMonoidHom E
    rw [Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective (K := E),
      Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective (K := E)]
    exact h x

public theorem frameSignedData_RPlus (hK : Nat.card K = 2)
    {E : Subgroup (OrthRest.RPlus K 4)} (hE : IsElemAbelian 3 E)
    (hcardE : Nat.card E = 3 ^ 4)
    (hsc : ∀ g : OrthRest.RPlus K 4, (∀ x ∈ E, g * x = x * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥E,
      (∀ g : OrthRest.RPlus K 4, g ∈ Subgroup.normalizer (E : Set (OrthRest.RPlus K 4)) →
        ∀ w : MulAut (Fin 4 → Multiplicative (ZMod 3)),
          (∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ =
            (Θ (w f) : OrthRest.RPlus K 4)) → IsSignedPerm ⇑w) ∧
      (∀ (a : Fin 4) (g : OrthRest.RPlus K 4),
        (∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ =
          (Θ (sgnAut a f) : OrthRest.RPlus K 4)) → False) ∧
      (∀ x : OmPlusIdx 4, ∃ g ∈ Subgroup.normalizer (E : Set (OrthRest.RPlus K 4)),
        ∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ =
          (Θ (omPlusRefl 3 x f) : OrthRest.RPlus K 4)) ∧
      (∀ f, Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          ((((CFSG.StandardType.OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)) (Θ f) :
              ↥(orthDerived (TableBOrth.qPlusForm K 4)))) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) =
        2 * (Finset.univ.filter (fun a => f a = 1)).card) := by
  classical
  set e := CFSG.StandardType.OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) with he
  set E' : Subgroup ↥(orthDerived (TableBOrth.qPlusForm K 4)) := E.map e.toMonoidHom with hE'def
  have hmem : ∀ x : OrthRest.RPlus K 4,
      e x ∈ E' ↔ x ∈ E :=
    fun x => Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective (K := E)
  have hE' : IsElemAbelian 3 E' := hE.map e.toMonoidHom
  have hcardE' : Nat.card E' = 3 ^ 4 := by
    rw [← hcardE]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E e.toMonoidHom e.injective).toEquiv).symm
  have hsc' : ∀ g : ↥(orthDerived (TableBOrth.qPlusForm K 4)),
      (∀ x ∈ E', g * x = x * g) → g ^ 3 = 1 → g ∈ E' := by
    intro g' hcomm hg3
    obtain ⟨g, rfl⟩ := e.surjective g'
    rw [hmem g]
    refine hsc g ?_ ?_
    · intro x hx
      have h1 := hcomm (e x) ((hmem x).mpr hx)
      exact e.injective (by simpa [map_mul] using h1)
    · exact e.injective (by rw [map_pow, hg3, map_one])
  have hQ := TableBOrth.nondegenerate_qPlusForm (K := K) 4
  have hdim : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by simp
  have hT := exists_totallySingular_three (K := K)
  obtain ⟨Θ', hsigned, hnosgn, hlifts, hfixdim⟩ :=
    frameSignedData (K := K) (V := Fin 4 ⊕ Fin 4 → K) (Q := TableBOrth.qPlusForm K 4)
      hK hQ hdim hT hE' hcardE' hsc'
  let eE : ↥E ≃* ↥E' := Subgroup.equivMapOfInjective E e.toMonoidHom e.injective
  let Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥E := Θ'.trans eE.symm
  have hΘe : ∀ f, e (Θ f : OrthRest.RPlus K 4) =
      (Θ' f : ↥(orthDerived (TableBOrth.qPlusForm K 4))) := by
    intro f
    have h1 : eE (Θ f) = Θ' f := by simp [Θ]
    have h2 : ((eE (Θ f) : ↥E') : ↥(orthDerived (TableBOrth.qPlusForm K 4))) =
        e (Θ f : OrthRest.RPlus K 4) :=
      Subgroup.coe_equivMapOfInjective_apply E e.toMonoidHom e.injective (Θ f)
    rw [← h2, h1]
  refine ⟨Θ, ?_, ?_, ?_, ?_⟩
  · intro g hgN w hw
    refine hsigned (e g) ((mem_normalizer_map_iff e E g).mpr hgN) w ?_
    intro f
    have h1 := congrArg e (hw f)
    simpa [map_mul, hΘe f, hΘe (w f)] using h1
  · intro a g hg
    refine hnosgn a (e g) ?_
    intro f
    have h1 := congrArg e (hg f)
    simpa [map_mul, hΘe f, hΘe (sgnAut a f)] using h1
  · intro x
    obtain ⟨g', hgN', hconj⟩ := hlifts x
    refine ⟨e.symm g', ?_, ?_⟩
    · refine (mem_normalizer_map_iff e E (e.symm g')).mp ?_
      simpa [hE'def] using hgN'
    · intro f
      refine e.injective ?_
      have h1 := hconj f
      simpa [map_mul, hΘe f, hΘe (omPlusRefl 3 x f), e.apply_symm_apply] using h1
  · intro f
    rw [hΘe f]
    exact hfixdim f

end CFSG.StandardType.E6QTwo
