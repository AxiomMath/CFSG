module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGK0KacRow
import CFSG.LocalAnalysis.StandardType.GGK0LangModel
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeE6
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInj
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
import CFSG.LocalAnalysis.StandardType.GGFinModelEps
import CFSG.LocalAnalysis.StandardType.MarkingChevalley

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.StandardType.RecipeExcLang

theorem K0LangMark.nonempty_congr {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ}
    {R R' : Type} [Group R] [Group R'] {I : Set (MulAut R)} {phi : MulAut R}
    (h : Nonempty (K0LangMark Omega lab p R I phi)) (e : R ≃* R') :
    Nonempty (K0LangMark Omega lab p R' (MulAut.congr e '' I) (MulAut.congr e phi)) := by
  obtain ⟨A⟩ := h
  exact ⟨{ A with
    iota := A.iota.comp e.symm.toMonoidHom
    iota_inj := A.iota_inj.comp e.symm.injective
    iota_range := by
      rw [← A.iota_range]
      ext x
      constructor
      · rintro ⟨r', rfl⟩
        exact ⟨e.symm r', rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨e r, by simp⟩
    modelAction := (MulAut.congr e).toMonoidHom.comp A.modelAction
    modelAction_inj := (MulAut.congr e).injective.comp A.modelAction_inj
    modelAction_range := by
      have hI := A.modelAction_range
      ext f
      constructor
      · rintro ⟨x, rfl⟩
        have hx : A.modelAction x ∈ Set.range (fun x => A.modelAction x) := ⟨x, rfl⟩
        rw [hI] at hx
        exact ⟨A.modelAction x, hx, rfl⟩
      · rintro ⟨f', hf', rfl⟩
        rw [← hI] at hf'
        obtain ⟨x, rfl⟩ := hf'
        exact ⟨x, rfl⟩
    modelAction_compat := fun g r => by
      simpa [MulAut.congr_apply] using A.modelAction_compat g (e.symm r)
    action_eq := congrArg (MulAut.congr e) A.action_eq }⟩

private theorem k0LangMark_markID_of_adjoint
    {lab : LargeEvenLabel} {p : ℕ} {τ : Tag} {K : Type} [Field K] [Finite K]
    (h : ∀ y : inndiagGroup τ K, orderOf (inndiagConj τ K y) = p →
      Nonempty (K0LangMark GGL lab p (adjointGroup τ K) (Set.range (inndiagConj τ K))
        (inndiagConj τ K y))) :
    ∀ φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K)),
      φ ∈ markIDImage (IsRoot τ) K (adjointGroup τ K) → orderOf φ = p →
      Nonempty (K0LangMark GGL lab p (LargeEvenCenterQuot (adjointGroup τ K))
        (markIDImage (IsRoot τ) K (adjointGroup τ K)) φ) := by
  intro φ hφ hφp
  obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hφ
  have hwp : orderOf (inndiagConj τ K w) = p := by
    rw [← hw, MulEquiv.orderOf_eq]
    exact hφp
  obtain ⟨M⟩ := h w hwp
  set E := centerQuotEquivOfBot (center_adjointGroup_eq_bot (τ := τ) (K := K)) with hE
  have hcongr : MulAut.congr E.symm = (autEquiv τ K).symm := by
    rw [hE]
    rfl
  have hI : MulAut.congr E.symm '' Set.range (inndiagConj τ K) =
      markIDImage (IsRoot τ) K (adjointGroup τ K) := by
    ext x
    constructor
    · rintro ⟨f, ⟨v, rfl⟩, rfl⟩
      rw [hcongr]
      exact inndiagConj_mem_markID v
    · intro hx
      obtain ⟨v, hv⟩ := exists_inndiagConj_of_mem_markID hx
      refine ⟨inndiagConj τ K v, ⟨v, rfl⟩, ?_⟩
      rw [hcongr, MulEquiv.symm_apply_eq]
      exact hv.symm
  have hphi : MulAut.congr E.symm (inndiagConj τ K w) = φ := by
    rw [hcongr, MulEquiv.symm_apply_eq]
    exact hw.symm
  have hM := K0LangMark.nonempty_congr ⟨M⟩ E.symm
  rw [hI, hphi] at hM
  exact hM

private theorem k0LangMark_transport_chev {τ : Tag} {K : Type} [Field K] {P : LargeEvenRawCont}
    (h : P (LargeEvenCenterQuot (adjointGroup τ K)) (markIDImage (IsRoot τ) K (adjointGroup τ K))
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K))) :
    P (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
  have hA : ∀ A : Subgroup (ModGL τ K), A = adjointGroup τ K →
      P (LargeEvenCenterQuot A) (markIDImage (IsRoot τ) K A)
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K A) := by
    intro A hA
    subst hA
    exact h
  have hB := hA _ (chevH_false_eq_adjointGroup K τ)
  have hC : P (LargeEvenCenterQuot (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false))
      (markIDImage (LargeEvenIsRoot τ.cartan) K
        (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false))
      (RecipeFieldExcInn.markFieldImage (LargeEvenIsRoot τ.cartan) K
        (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false)) :=
    (largeEvenIsRoot_eq_isRoot τ).symm ▸ hB
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      P (LargeEvenCenterQuot H) (LargeEvenChevIDImage τ.cartan K H)
        (LargeEvenChevFieldImage τ.cartan K H) from
    key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  rw [RecipeExcLang.largeEvenChevIDImage_eq]
  exact hC

theorem largeEvenLabelAll_k0LangMark_untw
    {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (h : ∀ T : GGKacType, ggKacTypeOfLabel lab = some (T, false) →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ lab.n →
        ∀ y : inndiagGroup (absTag T) K, orderOf (inndiagConj (absTag T) K y) = p →
          Nonempty (K0LangMark GGL lab p (adjointGroup (absTag T) K)
            (Set.range (inndiagConj (absTag T) K)) (inndiagConj (absTag T) K y))) :
    LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
      Nonempty (K0LangMark GGL lab p R I phi)) := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases htag with ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeChevalley_and
      (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
        Nonempty (K0LangMark GGL ⟨.F4, l, n⟩ p R I phi))
      (fun K _ _ hK => k0LangMark_transport_chev
        (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
          Nonempty (K0LangMark GGL ⟨.F4, l, n⟩ p R I phi))
        (k0LangMark_markID_of_adjoint (τ := .F4) (fun y hy => h .F4 rfl K hK y hy))) hQ
  · exact recipeChevalley_and
      (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
        Nonempty (K0LangMark GGL ⟨.E6, l, n⟩ p R I phi))
      (fun K _ _ hK => k0LangMark_transport_chev
        (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
          Nonempty (K0LangMark GGL ⟨.E6, l, n⟩ p R I phi))
        (k0LangMark_markID_of_adjoint (τ := .E6) (fun y hy => h .E6 rfl K hK y hy))) hQ
  · exact recipeChevalley_and
      (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
        Nonempty (K0LangMark GGL ⟨.E7, l, n⟩ p R I phi))
      (fun K _ _ hK => k0LangMark_transport_chev
        (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
          Nonempty (K0LangMark GGL ⟨.E7, l, n⟩ p R I phi))
        (k0LangMark_markID_of_adjoint (τ := .E7) (fun y hy => h .E7 rfl K hK y hy))) hQ
  · exact recipeChevalley_and
      (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
        Nonempty (K0LangMark GGL ⟨.E8, l, n⟩ p R I phi))
      (fun K _ _ hK => k0LangMark_transport_chev
        (P := fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
          Nonempty (K0LangMark GGL ⟨.E8, l, n⟩ p R I phi))
        (k0LangMark_markID_of_adjoint (τ := .E8) (fun y hy => h .E8 rfl K hK y hy))) hQ

theorem k0LangMark_untw_nonempty
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p) {T : GGKacType}
    (hT : ggKacTypeOfLabel lab = some (T, false)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ lab.n) (y : inndiagGroup (absTag T) K)
    (hy : orderOf (inndiagConj (absTag T) K y) = p) :
    Nonempty (K0LangMark GGL lab p (adjointGroup (absTag T) K)
      (Set.range (inndiagConj (absTag T) K)) (inndiagConj (absTag T) K y)) := by
  classical
  have hp : p.Prime := hpair.1
  have hp2 : p ≠ 2 := hpair.2.1
  have hn : 1 ≤ lab.n := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    rcases Nat.eq_zero_or_pos lab.n with h | h
    · rw [h] at h2
      norm_num at h2
    · exact h
  have hτ : absTag T = .F4 ∨ absTag T = .E6 ∨ absTag T = .E7 ∨ absTag T = .E8 := by
    cases T <;> simp [absTag]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := by
    have hcard : Fintype.card K = 2 ^ lab.n := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    exact charP_of_card_eq_prime_pow (p := 2) (f := lab.n) hcard
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra K GGL := (IsAlgClosed.lift : K →ₐ[ZMod 2] GGL).toRingHom.toAlgebra
  have hFr : ∀ c : GGL, ggFrobT lab.n c = c ^ Nat.card K := by
    intro c
    rw [ggFrobT_apply, hK]
  have hbij : Function.Bijective (ggFrobT lab.n) :=
    bijective_iterateFrobenius GGL 2 lab.n
  let u : ModGL (absTag T) GGL := baseChangeGL (algebraMap K GGL) (y : ModGL (absTag T) K)
  have hfixed := CFSG.HardMathSupport.C14ExcBridgeE6.fixed_eq_map_inndiag
    (τ := absTag T) (K := K) (L := GGL) (ggFrobT lab.n) hFr hbij
  have hu_mem : u ∈ (inndiagGroup (absTag T) K).map (baseChangeGL (algebraMap K GGL)) :=
    ⟨(y : ModGL (absTag T) K), y.2, rfl⟩
  rw [← hfixed] at hu_mem
  have hu : u ∈ adjointGroup (absTag T) GGL := hu_mem.1
  have huF : entrywiseFrobGL (absTag T) GGL 2 lab.n u = u := hu_mem.2
  have hinj : Function.Injective (inndiagConj (absTag T) K) :=
    inndiagConj_injective_of_card_eq_two_pow (τ := absTag T) (K := K) (n := lab.n) hK
  have hyord : orderOf y = p :=
    (orderOf_injective (inndiagConj (absTag T) K) hinj y).symm.trans hy
  have hyp : (y : ModGL (absTag T) K) ^ p = 1 := by
    rw [← hyord]
    exact congrArg (Subtype.val) (pow_orderOf_eq_one y)
  have hyne : y ≠ 1 := by
    intro h1
    apply hp.ne_one
    rw [← hyord, h1, orderOf_one]
  have hup : u ^ p = 1 := by
    change (baseChangeGL (algebraMap K GGL) (y : ModGL (absTag T) K)) ^ p = 1
    rw [← map_pow, hyp, map_one]
  have hune : u ≠ 1 := by
    intro h1
    apply hyne
    have h2 : (y : ModGL (absTag T) K) = 1 := by
      refine baseChangeGL_injective (algebraMap K GGL) ?_
      rw [map_one]
      exact h1
    exact Subtype.ext h2
  obtain ⟨ζ, hζ⟩ := exists_zeta GGL hp hp2
  obtain ⟨row, hrowT, g, μ, w, nodeMap, frobLinear, hg, hgu, hgw, hsurj, hker, hroot, heval,
    hspan, hfr, hnodes, hstd⟩ :=
    exists_k0KacPart hpair hn hT hu huF hup hζ
  have hgw' : Units.map (entrywiseHom (ggFrobT lab.n)) g =
      g * canonicalRep (coxeterSystem (absTag T)) GGL w :=
    (inv_mul_eq_iff_eq_mul).1 hgw
  obtain ⟨S, iota, act, hmem, hq, hΦ, hnS, hiota_inj, hiota_range, hact_inj, hact_range,
    hcompat, hact_y, hρ⟩ :=
    exists_k0LangModel (τ := absTag T) hτ hn hK hg hgw'
  have htw : row.tw = false := by
    have h2 : (row.T, row.tw) = (T, false) := by
      rw [← Option.some.injEq]
      exact row.type_eq.symm.trans hT
    exact (Prod.ext_iff.1 h2).2
  have hζp : ζ ^ p = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have ha_pow : ∀ i, (fun j : Fin (absTag T).rank => ζ ^ μ j) i ^ p = 1 := by
    intro i
    show (ζ ^ μ i) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  have ha_model : rootDiagUnit (absTag T) (fun j => ζ ^ μ j) ∈ S.D.model := by
    rw [← hgu]
    exact hmem y
  have ha_torus : rootDiagUnit (absTag T) (fun j => ζ ^ μ j) ∈ S.D.torus := by
    rw [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.torus,
      CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
    exact ⟨rootDiagUnit_mem_torusGroup _,
      ((CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.mem_model S.D).1 ha_model).2⟩
  have ha_ne : rootDiagUnit (absTag T) (fun j => ζ ^ μ j) ≠ 1 := by
    intro h1
    apply hune
    have h2 : g⁻¹ * u * g = 1 := by rw [hgu, h1]
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h2]
      _ = 1 := by group
  have hact : act ⟨rootDiagUnit (absTag T) (fun j => ζ ^ μ j), ha_model⟩ =
      inndiagConj (absTag T) K y := by
    rw [← hact_y y]
    congr 1
    exact Subtype.ext hgu.symm
  let A : K0LangMark GGL lab p (adjointGroup (absTag T) K)
      (Set.range (inndiagConj (absTag T) K)) (inndiagConj (absTag T) K y) :=
    { row := row
      tau := absTag T
      tau_eq := by rw [hrowT]
      setup := S
      q_eq := hq
      fr := ggFrobT lab.n
      fr_eq := ggFrobT_apply lab.n
      phi_split := fun _ g => hΦ g
      phi_twisted := fun h => by
        rw [htw] at h
        cases h
      iota := iota
      iota_inj := hiota_inj
      iota_range := hiota_range
      modelAction := act
      modelAction_inj := hact_inj
      modelAction_range := hact_range
      modelAction_compat := hcompat
      a := fun j => ζ ^ μ j
      a_pow := ha_pow
      a_torus := ha_torus
      a_model := ha_model
      a_ne := ha_ne
      action_eq := hact
      zeta := ζ
      zeta_order := hζ
      nodeMap := nodeMap
      nodeMap_surj := hsurj
      nodeMap_ker := hker
      node_isRoot := hroot
      node_eval := heval
      kernel_span_eq := hspan
      epsilon := if row.d = 1 then 1 else -1
      epsilon_eq := rfl
      frobLinear := frobLinear
      frob_roots := fun v hv => (hfr v hv).trans (hρ v hv).symm
      frob_nodes := hnodes
      node_std := hstd }
  exact ⟨A⟩


theorem k0LangMark_hA_untw
    {tag : LargeEvenLieTag} (htag : tag = .F4 ∨ tag = .E6 ∨ tag = .E7 ∨ tag = .E8) :
    ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
      lab.tag = tag → LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I →
        orderOf phi = p → Nonempty (K0LangMark GGL lab p R I phi)) := by
  rintro p lab - hpair rfl
  exact largeEvenLabelAll_k0LangMark_untw htag fun T hT K _ _ hK y hy =>
    k0LangMark_untw_nonempty hpair hT K hK y hy

end CFSG.StandardType.GGK0MarkedKacIface1587

end
