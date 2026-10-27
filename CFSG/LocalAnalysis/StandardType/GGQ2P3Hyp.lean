module

public import CFSG.LocalAnalysis.StandardType.GGQ2HypRestrict
public import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentre
public import CFSG.LocalAnalysis.StandardType.GGQ2A4Pm
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims
import CFSG.LocalAnalysis.StandardType.GGQ2LabelCartan
import CFSG.LocalAnalysis.StandardType.GGQ2LDatumLongest
import CFSG.LocalAnalysis.StandardType.GGQ2SubRestrict

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2P3P_reflGp_map {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (hp2 : p ≠ 2) :
    reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) =
      (ggReflGp p Bs).map (ggLin (p := p) ι) := by
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hST : ggLin (p := p) ι '' {φ | φ ∈ ggAutomizer ⊤ Bs ∧ GGIsReflection p φ} =
      {t | t ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι) ∧ IsReflLin t} := by
    ext t
    constructor
    · rintro ⟨φ, ⟨hφA, hφr⟩, hφt⟩
      refine ⟨Subgroup.mem_map.mpr ⟨φ, hφA, hφt⟩, ?_⟩
      obtain ⟨c, f, hcf, hφc⟩ := exists_of_ggIsReflection (p := p) ι hφr
      exact ⟨c, f, hcf, hφt.symm.trans (ggLin_eq_reflection ι hcf hφc)⟩
    · rintro ⟨htlin, ht⟩
      rw [Subgroup.mem_map] at htlin
      obtain ⟨φ, hφA, hφt⟩ := htlin
      obtain ⟨c, g, hg, ht_eq⟩ := ht
      exact ⟨φ, ⟨hφA, ggIsReflection_of_eq_reflection hp2 ι hg (hφt.trans ht_eq)⟩, hφt⟩
  rw [reflGp, ggReflGp, MonoidHom.map_closure, hST]

private theorem ggQ2P3P_exists_inducing {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {ρ : MulAut ↥Bs} (hρ : ρ ∈ ggReflGp p Bs) :
    ∃ rG ∈ Subgroup.closure {h : G | ∃ φ : MulAut ↥Bs, GGQ2Ind Bs h φ ∧ GGIsReflection p φ},
      GGQ2Ind Bs rG ρ := by
  let T : Subgroup G :=
    Subgroup.closure {h : G | ∃ φ : MulAut ↥Bs, GGQ2Ind Bs h φ ∧ GGIsReflection p φ}
  rw [ggReflGp] at hρ
  refine Subgroup.closure_induction (p := fun φ _ => ∃ rG ∈ T, GGQ2Ind Bs rG φ) ?_ ?_ ?_ ?_ hρ
  · intro φ hφ
    obtain ⟨g, -, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ.1
    exact ⟨g, Subgroup.subset_closure ⟨φ, ⟨hgN, hgφ⟩, hφ.2⟩, hgN, hgφ⟩
  · exact ⟨1, T.one_mem, Subgroup.one_mem _, fun b => by simp⟩
  · intro a b ha hb iha ihb
    obtain ⟨rG, hrG, hrN, hra⟩ := iha
    obtain ⟨sG, hsG, hsN, hsb⟩ := ihb
    exact ⟨rG * sG, T.mul_mem hrG hsG, Subgroup.mul_mem _ hrN hsN, fun c => by
      rw [MulAut.mul_apply, hra (b c), hsb c]; group⟩
  · intro a ha iha
    obtain ⟨rG, hrG, hrN, hra⟩ := iha
    exact ⟨rG⁻¹, T.inv_mem hrG, Subgroup.inv_mem _ hrN, fun c => by
      rw [inv_apply_of_forall hra c, inv_inv]⟩

theorem ggQ2P3P_transvectionFree {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (hNT : GGNoTransvection p Bs) :
    TransvectionFree ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) := by
  rintro g hg ⟨u, ψ, hu, hψ, hψu, hgv⟩
  rw [Subgroup.mem_map] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  obtain ⟨k, -, hkN, hkφ⟩ := mem_ggAutomizer_iff.mp hφ
  exact hNT φ ⟨k, Subgroup.mem_top k, hkN, hkφ⟩
    (ggIsTransvection_of_apply ι hu hψ hψu hgv)

private theorem ggQ2P3P_reflAbsIrred {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (h2 : 2 ≤ Module.finrank (ZMod 3) M.V)
    (habs : ZS.AbsIrred 3 (reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)))) :
    GGQ2ReflAbsIrred 3 Bs := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have : Nontrivial M.V := Module.nontrivial_of_finrank_pos (R := ZMod 3) (M := M.V) (by omega)
  have hrefl : reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)) =
      (ggReflGp 3 Bs).map (ggLin (p := 3) M.model) :=
    ggQ2P3P_reflGp_map (p := 3) M.model (by decide)
  let ρ : Representation (ZMod 3) ↥(ggReflGp 3 Bs) M.V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 3) (M := M.V)).comp
      ((ggLin (p := 3) M.model).comp (ggReflGp 3 Bs).subtype)
  have hρ : ∀ (g : ↥(ggReflGp 3 Bs)) (v : M.V), ρ g v = ggLin (p := 3) M.model g v :=
    fun _ _ => rfl
  refine ⟨M.V, M.instAddCommGroup, M.instModule, M.model, ?_⟩
  change Theory.Representation.IsAbsolutelyIrreducible ρ
  apply ggQ2Mix_isAbsolutelyIrreducible (ρ := ρ)
  · intro U hU
    refine habs.1 U ?_
    intro a ha w hw
    rw [hrefl] at ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    have h := hU ⟨g, hg⟩ w hw
    rwa [hρ ⟨g, hg⟩ w] at h
  · intro T hT
    obtain ⟨μ, hμ⟩ := habs.2 T (fun a ha => by
      rw [hrefl] at ha
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      exact hT ⟨g, hg⟩)
    exact ⟨μ, hμ⟩

theorem ggQ2_p3_of_linPm {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x)
    (h : ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model),
      ∃ r ∈ reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)),
        ∃ ε : ZMod 3, ε ≠ 0 ∧ a M.xV = ε • r M.xV) :
    GGQ2P3 3 Bs x := by
  intro g hg
  have hrefl : reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)) =
      (ggReflGp 3 Bs).map (ggLin (p := 3) M.model) :=
    ggQ2P3P_reflGp_map (p := 3) M.model (by decide)
  obtain ⟨r, hr, ε, hε, hεr⟩ := h (ggLin (p := 3) M.model (ggConjAut Bs hg))
    (Subgroup.mem_map_of_mem (ggLin (p := 3) M.model)
      (ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg))
  rw [hrefl] at hr
  obtain ⟨ρ', hρ', hρ'eq⟩ := Subgroup.mem_map.mp hr
  obtain ⟨rG, hrG, hInd⟩ := ggQ2P3P_exists_inducing (p := 3) hρ'
  refine ⟨rG, hrG, ?_⟩
  have hεr' : ggLin (p := 3) M.model (ggConjAut Bs hg) M.xV =
      ε • ggLin (p := 3) M.model ρ' M.xV := by
    rw [hεr, ← hρ'eq]
  have hmem : (ggLin (p := 3) M.model (ρ'⁻¹ * ggConjAut Bs hg)) M.xV ∈
      Submodule.span (ZMod 3) {M.xV} := by
    have h1 : (ggLin (p := 3) M.model (ρ'⁻¹ * ggConjAut Bs hg)) M.xV = ε • M.xV := by
      rw [map_mul, LinearEquiv.mul_apply, hεr', map_smul, map_inv]
      simp
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  let b0 : ↥Bs := ⟨x, M.hx⟩
  have key : (ρ'⁻¹ * ggConjAut Bs hg) b0 = b0 ^ a.val := by
    apply Additive.ofMul.injective
    apply M.model.injective
    have h1 : ggLin (p := 3) M.model (ρ'⁻¹ * ggConjAut Bs hg)
        (M.model (Additive.ofMul b0)) =
        M.model (Additive.ofMul ((ρ'⁻¹ * ggConjAut Bs hg) b0)) :=
      ggLin_apply_ofMul M.model _ b0
    have h2 : ggLin (p := 3) M.model (ρ'⁻¹ * ggConjAut Bs hg)
        (M.model (Additive.ofMul b0)) = a • M.model (Additive.ofMul b0) := ha.symm
    rw [← h1, h2, ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3),
      ZMod.natCast_zmod_val]
  have hG : rG⁻¹ * (g * x * g⁻¹) * rG = x ^ a.val := by
    have h1 : (((ρ'⁻¹ * ggConjAut Bs hg) b0 : ↥Bs) : G) = rG⁻¹ * (g * x * g⁻¹) * rG := by
      rw [MulAut.mul_apply, inv_apply_of_forall (φ := ρ') (h := rG) hInd.2]
      rfl
    rw [← h1, key]
    exact Subgroup.coe_pow Bs b0 a.val
  have hconj : g * x * g⁻¹ = (rG * x * rG⁻¹) ^ a.val := by
    rw [conj_pow, ← hG]
    group
  have hle : Subgroup.zpowers (g * x * g⁻¹) ≤ Subgroup.zpowers (rG * x * rG⁻¹) := by
    rw [Subgroup.zpowers_le, hconj]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers]
  have o1 : orderOf (g * x * g⁻¹) = orderOf x := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  have o2 : orderOf (rG * x * rG⁻¹) = orderOf x := by
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj rG).toMonoidHom (MulAut.conj rG).injective x
  rw [o1, o2]

theorem ggQ2_p3_of_hypDatum (hK : GGReflClassOmegaInput) {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {x : G} (hNT : GGNoTransvection 3 Bs) (hAbs : ¬ GGQ2ReflAbsIrred 3 Bs)
    (M : GGQ2LDatum 3 Bs L x) (hcard : 3 ≤ Fintype.card M.Λ)
    (hhyp : Module.finrank (ZMod 3) M.coSpan + 1 = Module.finrank (ZMod 3) M.V)
    (h5 : 5 ≤ Module.finrank (ZMod 3) M.coSpan) : GGQ2P3 3 Bs x := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have : Nonempty M.Λ := Fintype.card_pos_iff.mp (by omega)
  have h2 : 2 ≤ Module.finrank (ZMod 3) M.V := by
    rw [← hhyp]
    omega
  have hNotAbs : ¬ ZS.AbsIrred 3 (reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model))) :=
    fun habs => hAbs (ggQ2P3P_reflAbsIrred M h2 habs)
  refine ggQ2_p3_of_linPm M ?_
  intro a ha
  exact ggQ2Hyp_pm hK (V := M.V) (ι := M.Λ)
    ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model))
    (ggQ2P3P_transvectionFree M.model hNT)
    M.coroot M.root M.root_coroot_two (fun i => ggLin (p := 3) M.model (M.simple i))
    M.simple_apply
    (fun i => by
      rw [ggQ2P3P_reflGp_map (p := 3) M.model (by decide)]
      exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_reflGp i))
    M.xV (fun z hz => M.mem_span_xV_of_root hz) (M.pairing_connected hcard)
    h5 hhyp hNotAbs a ha

theorem ggQ2_p3_of_topDatum {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (hAbs : ¬ GGQ2ReflAbsIrred 3 Bs) (M : GGQ2LDatum 3 Bs L x) (hcard : 3 ≤ Fintype.card M.Λ)
    (htop : M.coSpan = ⊤) (h2 : 2 ≤ Module.finrank (ZMod 3) M.V) : GGQ2P3 3 Bs x := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have : Nonempty M.Λ := Fintype.card_pos_iff.mp (by omega)
  have hNotAbs : ¬ ZS.AbsIrred 3 (reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model))) :=
    fun habs => hAbs (ggQ2P3P_reflAbsIrred M h2 habs)
  refine ggQ2_p3_of_linPm M ?_
  intro a ha
  exact ggQ2Hyp_pm_top (V := M.V) (ι := M.Λ)
    ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model))
    M.coroot M.root M.root_coroot_two (fun i => ggLin (p := 3) M.model (M.simple i))
    M.simple_apply
    (fun i => by
      rw [ggQ2P3P_reflGp_map (p := 3) M.model (by decide)]
      exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_reflGp i))
    M.xV (fun z hz => M.mem_span_xV_of_root hz) (M.pairing_connected hcard)
    htop h2 hNotAbs a ha

theorem ggQ2_p3_of_negDatum {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (hNT : GGNoTransvection 3 Bs) (hAbs : ¬ GGQ2ReflAbsIrred 3 Bs)
    (M : GGQ2LDatum 3 Bs L x) (hcard : 3 ≤ Fintype.card M.Λ)
    (hhyp : Module.finrank (ZMod 3) M.coSpan + 1 = Module.finrank (ZMod 3) M.V)
    (h2 : 2 ≤ Module.finrank (ZMod 3) M.coSpan)
    (hw : ∃ φ ∈ ggAutomizer L Bs, ∀ i, ggLin (p := 3) M.model φ (M.coroot i) = -M.coroot i) :
    GGQ2P3 3 Bs x := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have : Nonempty M.Λ := Fintype.card_pos_iff.mp (by omega)
  have h2V : 2 ≤ Module.finrank (ZMod 3) M.V := by
    rw [← hhyp]
    omega
  have hNotAbs : ¬ ZS.AbsIrred 3 (reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model))) :=
    fun habs => hAbs (ggQ2P3P_reflAbsIrred M h2V habs)
  have hsR : ∀ i, ggLin (p := 3) M.model (M.simple i) ∈
      reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)) := fun i => by
    rw [ggQ2P3P_reflGp_map (p := 3) M.model (by decide)]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_reflGp i)
  obtain ⟨φ, hφ, hφneg⟩ := hw
  have hwR : ggLin (p := 3) M.model φ ∈
      reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)) := by
    have hle : Subgroup.closure (Set.range M.simple) ≤
        (reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model))).comap
          (ggLin (p := 3) M.model) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hsR i
    rw [M.automizer_L] at hφ
    exact hle hφ
  have hwH : ∀ h ∈ Submodule.span (ZMod 3) (Set.range M.coroot),
      ggLin (p := 3) M.model φ h = -h := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact hφneg i
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, hu, hv, neg_add]
    | smul t u _ hu => rw [map_smul, hu, smul_neg]
  refine ggQ2_p3_of_linPm M ?_
  intro a ha
  exact ggQ2Hyp_pm_neg (V := M.V) (ι := M.Λ)
    ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model))
    (ggQ2P3P_transvectionFree M.model hNT)
    M.coroot M.root M.root_coroot_two (fun i => ggLin (p := 3) M.model (M.simple i))
    M.simple_apply hsR
    M.xV (fun z hz => M.mem_span_xV_of_root hz) (M.pairing_connected hcard)
    h2 hhyp ⟨_, hwR, hwH⟩ hNotAbs a ha

theorem ggQ2_p3_of_kerDatum {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hxH : M.xV ∈ M.coSpan)
    (hker : ∀ κ : M.Λ → ZMod 3, (∀ i, ∑ j, (M.cartan i j : ZMod 3) * κ j = 0) → κ = 0) :
    GGQ2P3 3 Bs x := by
  have hroot : ∀ i, M.root i M.xV = 0 := by
    intro i
    have hmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [M.fixed_x]
      exact Submodule.mem_span_singleton_self _
    have hsi : M.simple i ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have h1 := mem_ggFixedSubmodule_iff.mp hmem (M.simple i) hsi
    rw [M.simple_apply, sub_eq_self] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact h
    · have h2 := M.root_coroot_two i
      rw [h, map_zero] at h2
      exact absurd h2 (by decide)
  obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hxH
  have hκ0 : κ = 0 := by
    refine hker κ (fun i => ?_)
    have h := hroot i
    rw [← hκ, map_sum] at h
    simpa only [map_smul, M.pairing, smul_eq_mul, mul_comm] using h
  have hx0 : M.model (Additive.ofMul ⟨x, M.hx⟩) = M.model 0 := by
    rw [map_zero]
    change M.xV = 0
    rw [← hκ, hκ0]
    simp
  have hx1 : x = 1 := by
    have h := M.model.injective hx0
    have h' : (⟨x, M.hx⟩ : ↥Bs) = 1 := by simpa using h
    simpa using congrArg Subtype.val h'
  subst hx1
  intro g _
  exact ⟨1, Subgroup.one_mem _, by simp⟩

private theorem ggQ2P3P_cartan_twA {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (htag : labL.tag = .twA) (hlab : GGQ2TBLabel labL) :
    ∃ e : Fin labL.rank ≃ M.Λ,
      ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A labL.rank i j := by
  rcases ggQ2_label_cartan M hW hlab with ⟨-, ⟨e, he⟩⟩ | ⟨hb, -⟩ | ⟨hd, -⟩ | ⟨h7, -⟩ |
    hF4 | hE6 | hE8
  · exact ⟨e, he⟩
  · rcases hb with hb | hb <;> rw [htag] at hb <;> exact absurd hb (by decide)
  · rcases hd with hd | hd <;> rw [htag] at hd <;> exact absurd hd (by decide)
  · rw [htag] at h7; exact absurd h7 (by decide)
  · rw [htag] at hF4; exact absurd hF4 (by decide)
  · rw [htag] at hE6; exact absurd hE6 (by decide)
  · rw [htag] at hE8; exact absurd hE8 (by decide)

theorem ggQ2_p3_of_A4FullDatum {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (hNT : GGNoTransvection 3 Bs) (hAbs : ¬ GGQ2ReflAbsIrred 3 Bs)
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (htag : labL.tag = .twA) (h4 : labL.rank = 4) (hF : M.ShapeFull) : GGQ2P3 3 Bs x := by
  rcases labL with ⟨tag, rank, n⟩
  have h4' : rank = 4 := h4
  have htag' : tag = .twA := htag
  subst rank
  have hlab : GGQ2TBLabel ⟨tag, 4, n⟩ := Or.inl ⟨htag', by omega⟩
  obtain ⟨e, he⟩ := ggQ2P3P_cartan_twA M hW htag' hlab
  have h2V : 2 ≤ Module.finrank (ZMod 3) M.V := by
    have h := ggQ2LD_dim_nonheart M (Or.inl hF)
    have hc : Fintype.card M.Λ = 4 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  let K : GGQ2A4Conf M.V :=
    { c := fun i => M.coroot (e i)
      α := fun i => M.root (e i)
      x := M.xV
      pairing := fun i j => by
        show M.root (e i) (M.coroot (e j)) = ggA4C i j
        rw [M.pairing (e i) (e j), he i j]
        exact ggA4C_eq_cast i j
      root_x := fun i => M.root_xV (e i)
      ind := hF.2.1.comp (fun i => e i) e.injective
      x_notMem := by
        change M.xV ∉ Submodule.span (ZMod 3) (Set.range (M.coroot ∘ e))
        rw [EquivLike.range_comp M.coroot e]
        exact hF.2.2.1 }
  have hKF : K.Full := by
    change Submodule.span (ZMod 3) (Set.range (M.coroot ∘ e)) ⊔
      Submodule.span (ZMod 3) {M.xV} = ⊤
    rw [EquivLike.range_comp M.coroot e]
    exact hF.2.2.2
  let A : Subgroup (M.V ≃ₗ[ZMod 3] M.V) :=
    (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
  have hTF : TransvectionFree A := ggQ2P3P_transvectionFree M.model hNT
  have hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A) :=
    fun habs => hAbs (ggQ2P3P_reflAbsIrred M h2V habs)
  have hsA : ∀ i, K.s i ∈ A := by
    intro i
    have hs : K.s i = ggLin (p := 3) M.model (M.simple (e i)) := by
      refine LinearEquiv.ext fun v => ?_
      rw [GGQ2A4Conf.s_apply]
      exact (M.simple_apply (e i) v).symm
    rw [hs]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_top (e i))
  refine ggQ2_p3_of_linPm M ?_
  intro a ha
  exact ggQ2A4_pm K hKF A hTF hsA hNotAbs a ha

theorem ggQ2_p3_of_A5HeartDatum {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (hNT : GGNoTransvection 3 Bs) (hAbs : ¬ GGQ2ReflAbsIrred 3 Bs)
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (htag : labL.tag = .twA) (h5 : labL.rank = 5) (hB : M.ShapeB) : GGQ2P3 3 Bs x := by
  rcases labL with ⟨tag, rank, n⟩
  have h5' : rank = 5 := h5
  have htag' : tag = .twA := htag
  subst rank
  have hlab : GGQ2TBLabel ⟨tag, 5, n⟩ := Or.inl ⟨htag', by omega⟩
  obtain ⟨e, he⟩ := ggQ2P3P_cartan_twA M hW htag' hlab
  have hVdim : Module.finrank (ZMod 3) M.V = 5 := by
    have h := ggQ2LD_dim_heart M (Or.inl hB)
    have hc : Fintype.card M.Λ = 5 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  have h2V : 2 ≤ Module.finrank (ZMod 3) M.V := by omega
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hindK : LinearIndependent (ZMod 3) (fun j : Fin 4 => M.coroot (e j.castSucc)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg0 : g = 0 := by
      refine ggA4_nondeg g (fun i => ?_)
      rw [ggA4B_single]
      have h := congrArg (fun v => M.root (e i.castSucc) v) hg
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
      calc ∑ j : Fin 4, ggA4C i j * g j
          = ∑ j : Fin 4, g j * M.root (e i.castSucc) (M.coroot (e j.castSucc)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [M.pairing (e i.castSucc) (e j.castSucc), he i.castSucc j.castSucc,
              ggA5_restrict i j]
            ring
        _ = 0 := h
    intro i
    exact congrFun hg0 i
  have hHdimK : Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc)))) = 4 := by
    rw [finrank_span_eq_card hindK]
    exact Fintype.card_fin 4
  have hx_notMem : M.xV ∉
      Submodule.span (ZMod 3) (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) := by
    intro hmem
    have hle : Submodule.span (ZMod 3)
        (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) ≤ M.coSpan := by
      refine Submodule.span_mono ?_
      rintro v ⟨j, rfl⟩
      exact ⟨e j.castSucc, rfl⟩
    exact hB.2.2.1 (hle hmem)
  have hsup : Submodule.span (ZMod 3)
      (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) ⊔
      Submodule.span (ZMod 3) {M.xV} = ⊤ := by
    have hfdH : FiniteDimensional (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc)))) :=
      Module.Finite.span_of_finite _ (Set.finite_range _)
    have hfdS : FiniteDimensional (ZMod 3) (Submodule.span (ZMod 3) {M.xV}) :=
      Module.Finite.span_of_finite _ (Set.finite_singleton M.xV)
    have hx0 : M.xV ≠ 0 := by
      intro h0
      exact hx_notMem (h0 ▸ Submodule.zero_mem _)
    have hdisj : Submodule.span (ZMod 3)
        (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) ⊓
        Submodule.span (ZMod 3) {M.xV} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro v ⟨hvH, hvS⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hvS
      rw [← hc] at hvH
      by_cases hc0 : c = 0
      · rw [hc0, zero_smul] at hc
        exact hc.symm
      · exact absurd (by
          have hxx : M.xV = c⁻¹ • (c • M.xV) := by
            rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [hxx]
          exact Submodule.smul_mem _ _ hvH) hx_notMem
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod 3) (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))))
      (Submodule.span (ZMod 3) {M.xV})
    rw [hdisj, finrank_bot, hHdimK, finrank_span_singleton hx0] at hfin
    have hdim : Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3)
        (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) ⊔
          Submodule.span (ZMod 3) {M.xV}) = Module.finrank (ZMod 3) M.V := by
      omega
    exact Submodule.eq_top_of_finrank_eq hdim
  let K : GGQ2A4Conf M.V :=
    { c := fun j => M.coroot (e j.castSucc)
      α := fun j => M.root (e j.castSucc)
      x := M.xV
      pairing := fun i j => by
        show M.root (e i.castSucc) (M.coroot (e j.castSucc)) = ggA4C i j
        rw [M.pairing (e i.castSucc) (e j.castSucc), he i.castSucc j.castSucc]
        exact ggA5_restrict i j
      root_x := fun i => M.root_xV (e i.castSucc)
      ind := hindK
      x_notMem := hx_notMem }
  have hKF : K.Full := hsup
  let A : Subgroup (M.V ≃ₗ[ZMod 3] M.V) :=
    (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
  have hTF : TransvectionFree A := ggQ2P3P_transvectionFree M.model hNT
  have hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A) :=
    fun habs => hAbs (ggQ2P3P_reflAbsIrred M h2V habs)
  have hsA : ∀ i, K.s i ∈ A := by
    intro i
    have hs : K.s i = ggLin (p := 3) M.model (M.simple (e i.castSucc)) := by
      refine LinearEquiv.ext fun v => ?_
      rw [GGQ2A4Conf.s_apply]
      exact (M.simple_apply (e i.castSucc) v).symm
    rw [hs]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_top (e i.castSucc))
  refine ggQ2_p3_of_linPm M ?_
  intro a ha
  exact ggQ2A4_pm K hKF A hTF hsA hNotAbs a ha

private theorem ggQ2P3P_ggA4B_sub (u v w : Fin 4 → ZMod 3) :
    ggA4B u (v - w) = ggA4B u v - ggA4B u w := by
  simp only [ggA4B, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem ggQ2P3P_ggA4B_sum_single (u n : Fin 4 → ZMod 3) :
    ggA4B u n = ∑ k, u k * ggA4B (Pi.single k 1) n := by
  change (∑ i, ∑ j, u i * ggA4C i j * n j) =
    ∑ k, u k * ggA4B (Pi.single k 1) n
  simp only [ggA4B_single, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ggQ2_A5ShapeC_not_stab {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (hNT : GGNoTransvection 3 Bs) (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel}
    (hW : GGQ2LabelWeyl labL M.coxeter) (htag : labL.tag = .twA) (h5 : labL.rank = 5)
    (hC : M.ShapeC)
    (hRH : ∀ r ∈ reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)), ∀ h ∈ M.coSpan,
      r h ∈ M.coSpan)
    (hRx : ¬ ∀ r ∈ reflGp ((ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)),
      r M.xV ∈ Submodule.span (ZMod 3) {M.xV}) : False := by
  rcases labL with ⟨tag, rank, n⟩
  have h5' : rank = 5 := h5
  have htag' : tag = .twA := htag
  subst rank
  have hlab : GGQ2TBLabel ⟨tag, 5, n⟩ := Or.inl ⟨htag', by omega⟩
  obtain ⟨e, he⟩ := ggQ2P3P_cartan_twA M hW htag' hlab
  have hcardΛ : Fintype.card M.Λ = 5 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hcodim : Module.finrank (ZMod 3) M.coSpan = 4 := by
    have h := hC.2.1
    omega
  have hVdim : Module.finrank (ZMod 3) M.V = 6 := by
    have h := hC.2.2.2.1
    omega
  have hcard : 3 ≤ Fintype.card M.Λ := by omega
  have hindK : LinearIndependent (ZMod 3) (fun j : Fin 4 => M.coroot (e j.castSucc)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg0 : g = 0 := by
      refine ggA4_nondeg g (fun i => ?_)
      rw [ggA4B_single]
      have h := congrArg (fun v => M.root (e i.castSucc) v) hg
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
      calc ∑ j : Fin 4, ggA4C i j * g j
          = ∑ j : Fin 4, g j * M.root (e i.castSucc) (M.coroot (e j.castSucc)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [M.pairing (e i.castSucc) (e j.castSucc), he i.castSucc j.castSucc,
              ggA5_restrict i j]
            ring
        _ = 0 := h
    intro i
    exact congrFun hg0 i
  have hx_notMem : M.xV ∉
      Submodule.span (ZMod 3) (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) := by
    intro hmem
    have hle : Submodule.span (ZMod 3)
        (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) ≤ M.coSpan := by
      refine Submodule.span_mono ?_
      rintro v ⟨j, rfl⟩
      exact ⟨e j.castSucc, rfl⟩
    exact hC.2.2.1 (hle hmem)
  let K : GGQ2A4Conf M.V :=
    { c := fun j => M.coroot (e j.castSucc)
      α := fun j => M.root (e j.castSucc)
      x := M.xV
      pairing := fun i j => by
        show M.root (e i.castSucc) (M.coroot (e j.castSucc)) = ggA4C i j
        rw [M.pairing (e i.castSucc) (e j.castSucc), he i.castSucc j.castSucc]
        exact ggA5_restrict i j
      root_x := fun i => M.root_xV (e i.castSucc)
      ind := hindK
      x_notMem := hx_notMem }
  have hKH : K.H = M.coSpan := by
    have hle : K.H ≤ M.coSpan := by
      change Submodule.span (ZMod 3)
          (Set.range (fun j : Fin 4 => M.coroot (e j.castSucc))) ≤
        Submodule.span (ZMod 3) (Set.range M.coroot)
      refine Submodule.span_mono ?_
      rintro v ⟨j, rfl⟩
      exact ⟨e j.castSucc, rfl⟩
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [K.finrank_H, hcodim]
  have hcheckFirst : ∀ i : Fin 4,
      ((CartanMatrix.A 5 i.castSucc (Fin.last 4) : ℤ) : ZMod 3) =
        ggA4B (Pi.single i 1) (ggA4F 4) := by
    intro i
    fin_cases i <;> decide +kernel
  have hcheckLast : ∀ j : Fin 4,
      ((CartanMatrix.A 5 (Fin.last 4) j.castSucc : ℤ) : ZMod 3) =
        ggA4B (ggA4F 4) (Pi.single j 1) := by
    intro j
    fin_cases j <;> decide +kernel
  have hc4 : M.coroot (e (Fin.last 4)) = K.κ (ggA4F 4) := by
    have hmem : M.coroot (e (Fin.last 4)) ∈ K.H := by
      rw [hKH]
      exact Submodule.subset_span ⟨e (Fin.last 4), rfl⟩
    obtain ⟨m, hm⟩ := (GGQ2A4Conf.mem_H_iff (K := K)).mp hmem
    have hmi : ∀ i : Fin 4,
        ggA4B (Pi.single i 1) m = ggA4B (Pi.single i 1) (ggA4F 4) := by
      intro i
      calc ggA4B (Pi.single i 1) m
          = K.α i (K.κ m) := (K.α_κ i m).symm
        _ = K.α i (M.coroot (e (Fin.last 4))) := by rw [hm]
        _ = M.root (e i.castSucc) (M.coroot (e (Fin.last 4))) := rfl
        _ = ((CartanMatrix.A 5 i.castSucc (Fin.last 4) : ℤ) : ZMod 3) := by
            rw [M.pairing (e i.castSucc) (e (Fin.last 4)), he i.castSucc (Fin.last 4)]
        _ = ggA4B (Pi.single i 1) (ggA4F 4) := hcheckFirst i
    have hm4 : m = ggA4F 4 := by
      refine sub_eq_zero.mp (ggA4_nondeg (m - ggA4F 4) (fun i => ?_))
      rw [ggQ2P3P_ggA4B_sub, hmi i, sub_self]
    calc M.coroot (e (Fin.last 4)) = K.κ m := hm.symm
      _ = K.κ (ggA4F 4) := by rw [hm4]
  have hψ : M.root (e (Fin.last 4)) (K.κ (ggA4F 4)) = 2 := by
    rw [← hc4]
    exact M.root_coroot_two (e (Fin.last 4))
  have hψH : ∀ n, M.root (e (Fin.last 4)) (K.κ n) = ggA4B (ggA4F 4) n := by
    intro n
    rw [GGQ2A4Conf.κ_apply, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc ∑ j : Fin 4, n j * M.root (e (Fin.last 4)) (K.c j)
        = ∑ j : Fin 4,
            n j * ((CartanMatrix.A 5 (Fin.last 4) j.castSucc : ℤ) : ZMod 3) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          change n j * M.root (e (Fin.last 4)) (M.coroot (e j.castSucc)) = _
          rw [M.pairing (e (Fin.last 4)) (e j.castSucc), he (Fin.last 4) j.castSucc]
      _ = ∑ j : Fin 4, n j * ggA4B (ggA4F 4) (Pi.single j 1) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hcheckLast j]
      _ = ggA4B (ggA4F 4) n := by
          rw [ggA4B_symm (ggA4F 4) n, ggQ2P3P_ggA4B_sum_single n (ggA4F 4)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ggA4B_symm (Pi.single j 1) (ggA4F 4)]
  have hψx : M.root (e (Fin.last 4)) K.x = 0 := M.root_xV (e (Fin.last 4))
  let A : Subgroup (M.V ≃ₗ[ZMod 3] M.V) :=
    (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
  have hTF : TransvectionFree A := ggQ2P3P_transvectionFree M.model hNT
  have hsR : ∀ i, ggLin (p := 3) M.model (M.simple i) ∈ reflGp A := fun i => by
    rw [ggQ2P3P_reflGp_map (p := 3) M.model (by decide)]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_reflGp i)
  have h : Module.reflection hψ ∈ A := by
    have heq : Module.reflection hψ =
        ggLin (p := 3) M.model (M.simple (e (Fin.last 4))) := by
      refine LinearEquiv.ext fun v => ?_
      rw [Module.reflection_apply (y := v) hψ, M.simple_apply (e (Fin.last 4)) v, hc4]
    rw [heq]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_top (e (Fin.last 4)))
  have hsA : ∀ i, K.s i ∈ A := by
    intro i
    have hs : K.s i = ggLin (p := 3) M.model (M.simple (e i.castSucc)) := by
      refine LinearEquiv.ext fun v => ?_
      rw [GGQ2A4Conf.s_apply]
      exact (M.simple_apply (e i.castSucc) v).symm
    rw [hs]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_top (e i.castSucc))
  have hcen : ∀ (c₀ : M.V) (φ : Module.Dual (ZMod 3) M.V) (hφ : φ c₀ = 2),
      Module.reflection hφ ∈ A → c₀ ∈ K.H := by
    intro c₀ φ hφ ht
    have hc0 : c₀ ∈ M.coSpan :=
      ggQ2Sub_refl_centre (V := M.V) (ι := M.Λ) A hTF M.coroot M.root M.root_coroot_two
        (fun i => ggLin (p := 3) M.model (M.simple i)) M.simple_apply hsR M.xV
        (fun z hz => M.mem_span_xV_of_root hz) M.coSpan le_rfl hRH hRx hφ ht
    rw [hKH]
    exact hc0
  have hneg : ∀ r ∈ reflGp A, ¬ ∀ h ∈ K.H, r h = -h := by
    intro r hr hrneg
    have h2 : 2 ≤ Module.finrank (ZMod 3) M.coSpan := by omega
    have hUtop : M.coSpan ≠ ⊤ := by
      intro htop
      have h6 : Module.finrank (ZMod 3) M.coSpan = 6 := by
        rw [htop, finrank_top, hVdim]
      omega
    have hnotneg := ggQ2Sub_not_neg (V := M.V) (ι := M.Λ) A hTF M.coroot M.root
      M.root_coroot_two (fun i => ggLin (p := 3) M.model (M.simple i)) M.simple_apply hsR
      M.xV (fun z hz => M.mem_span_xV_of_root hz) (fun i => M.root_xV i)
      (M.pairing_connected hcard) h2 M.coSpan le_rfl hUtop hRH hRx r hr
    exact hnotneg (by
      intro u hu
      exact hrneg u (by simpa [hKH] using hu))
  have hfixrefl : ∀ t ∈ A, IsReflLin (p := 3) t → t M.xV = M.xV :=
    ggQ2A4_refl_fix_of_ext K A hTF hsA hcen hneg (k := 4) hψ hψH hψx h
  apply hRx
  intro r hr
  have hrf : r M.xV = M.xV := by
    rw [reflGp] at hr
    refine Subgroup.closure_induction (p := fun r _ => r M.xV = M.xV) ?_ ?_ ?_ ?_ hr
    · rintro t ⟨htA, htR⟩
      exact hfixrefl t htA htR
    · simp
    · intro a b _ _ ha hb
      rw [LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha
      have h := congrArg (fun v => a⁻¹ v) ha
      simpa using h.symm
  rw [hrf]
  exact Submodule.mem_span_singleton_self _

theorem ggQ2_p3_of_shapeCDatum (hK : GGReflClassOmegaInput) {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {x : G} (hNT : GGNoTransvection 3 Bs) (hAbs : ¬ GGQ2ReflAbsIrred 3 Bs)
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (hC : M.ShapeC) : GGQ2P3 3 Bs x := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hC5 : 6 ≤ Fintype.card M.Λ ∨ (labL.tag = .twA ∧ labL.rank = 5) :=
    ggQ2LD_shapeC_card M hW hlab hC
  have hcard5 : 5 ≤ Fintype.card M.Λ := by
    rcases hC5 with h6 | ⟨htag, h5⟩
    · omega
    · have hc : Fintype.card M.Λ = 5 := by
        rw [ggQ2LD_card_lie hW hlab]
        simp [GGQ2LieRank, htag, h5]
      omega
  have hcard : 3 ≤ Fintype.card M.Λ := by omega
  have : Nonempty M.Λ := Fintype.card_pos_iff.mp (by omega)
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.coSpan := by
    have h := hC.2.1
    omega
  have hdim : Module.finrank (ZMod 3) M.coSpan + 2 = Module.finrank (ZMod 3) M.V := by
    have h1 := hC.2.1
    have h2 := hC.2.2.2.1
    omega
  have h2V : 2 ≤ Module.finrank (ZMod 3) M.V := by omega
  let A : Subgroup (M.V ≃ₗ[ZMod 3] M.V) :=
    (ggAutomizer ⊤ Bs).map (ggLin (p := 3) M.model)
  have hTF : TransvectionFree A := ggQ2P3P_transvectionFree M.model hNT
  have hNotAbs : ¬ ZS.AbsIrred 3 (reflGp A) :=
    fun habs => hAbs (ggQ2P3P_reflAbsIrred M h2V habs)
  have hsR : ∀ i, ggLin (p := 3) M.model (M.simple i) ∈ reflGp A := fun i => by
    rw [ggQ2P3P_reflGp_map (p := 3) M.model (by decide)]
    exact Subgroup.mem_map_of_mem (ggLin (p := 3) M.model) (M.simple_mem_reflGp i)
  have hH5 : (∀ r ∈ reflGp A, ∀ h ∈ M.coSpan, r h ∈ M.coSpan) →
      (¬ ∀ r ∈ reflGp A, r M.xV ∈ Submodule.span (ZMod 3) {M.xV}) →
        5 ≤ Module.finrank (ZMod 3) M.coSpan := by
    intro hRH hRx
    rcases hC5 with h6 | ⟨htag, h5⟩
    · have h := hC.2.1
      omega
    · exact (ggQ2_A5ShapeC_not_stab hNT M hW htag h5 hC hRH hRx).elim
  refine ggQ2_p3_of_linPm M ?_
  intro a ha
  exact ggQ2Codim2_pm hK (V := M.V) (ι := M.Λ) A hTF M.coroot M.root
    M.root_coroot_two (fun i => ggLin (p := 3) M.model (M.simple i)) M.simple_apply hsR
    M.xV (fun z hz => M.mem_span_xV_of_root hz) (fun i => M.root_xV i)
    (M.pairing_connected hcard) hdim h4 hH5 hNotAbs a ha

end CFSG.StandardType

end
