module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4_pd_transport (hPD : GGProjDegreeF4) {G : Type} [Group G] {M₀ Hb L : Subgroup G}
    (hHb : Hb ≤ M₀) (hL : L ≤ M₀) {K : Type} [Field K] [IsAlgClosed K] [CharP K 2] {d : ℕ}
    (Φ : ↥M₀ →* (Matrix.GeneralLinearGroup (Fin d) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)))
    (hinj : ∀ (b : G) (hb : b ∈ Hb), Φ ⟨b, hHb hb⟩ = 1 → b = 1)
    (hcard : Nat.card Hb = 3 ^ 4) (hab : IsElemAbelian 3 Hb)
    [Fact (Nat.Prime 3)] {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Hb ≃+ V}
    {φ : Γ → MulAut ↥Hb} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι C φ h α)
    (hF4 : ∃ e : Fin 4 ≃ Γ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i))
    (hGen : ggAutomizer L Hb = Subgroup.closure (Set.range φ)) : 24 ≤ d := by
  let Q := Matrix.GeneralLinearGroup (Fin d) K ⧸
    Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)
  let H₀ : Subgroup ↥M₀ := Hb.subgroupOf M₀
  let A : Subgroup Q := H₀.map Φ
  let Nb : Subgroup G := L ⊓ Subgroup.normalizer (Hb : Set G)
  let N : Subgroup Q := (Nb.subgroupOf M₀).map Φ
  have hinjH₀ : Function.Injective (Φ.domRestrict H₀) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply] at hx
    have hxmem : ((x : ↥M₀) : G) ∈ Hb := Subgroup.mem_subgroupOf.mp x.2
    have hxe : Φ ⟨((x : ↥M₀) : G), hHb hxmem⟩ = 1 := by
      simpa using hx
    have hx1 : ((x : ↥M₀) : G) = 1 := hinj _ hxmem hxe
    apply Subtype.ext
    apply Subtype.ext
    exact hx1
  let e : ↥Hb ≃* ↥A :=
    (Subgroup.subgroupOfEquivOfLe hHb).symm.trans
      ((MonoidHom.ofInjective hinjH₀).trans
        (MulEquiv.subgroupCongr (MonoidHom.restrict_range H₀ Φ)))
  have e_coe : ∀ b : ↥Hb, (e b : Q) = Φ ⟨(b : G), hHb b.2⟩ := by
    intro b
    have hz : (((Subgroup.subgroupOfEquivOfLe hHb).symm b : ↥H₀) : ↥M₀) =
        ⟨(b : G), hHb b.2⟩ := rfl
    simp only [e, MulEquiv.trans_apply, MonoidHom.ofInjective_apply, MonoidHom.domRestrict_apply,
      MulEquiv.subgroupCongr_apply, hz]
  have hA : IsElemAbelian 3 A :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hab M₀) Φ
  have hcardA : Nat.card A = 3 ^ 4 := by
    rw [← Nat.card_congr e.toEquiv, hcard]
  let ι'' : Additive ↥A ≃+ V := (MulEquiv.toAdditive e.symm).trans ι
  let φ'' : Γ → MulAut ↥A := fun i => (MulAut.congr e) (φ i)
  let M : MulAut ↥Hb →* MulAut ↥A := (MulAut.congr e).toMonoidHom
  have conj_mem : ∀ (x : G) (hxL : x ∈ L) (hxN : x ∈ Subgroup.normalizer (Hb : Set G)),
      ∀ a ∈ A, Φ ⟨x, hL hxL⟩ * a * (Φ ⟨x, hL hxL⟩)⁻¹ ∈ A := by
    intro x hxL hxN a ha
    obtain ⟨hh, hhH₀, hha⟩ := Subgroup.mem_map.mp ha
    have hhHb : ((hh : ↥M₀) : G) ∈ Hb := Subgroup.mem_subgroupOf.mp hhH₀
    have hmem : x * (hh : G) * x⁻¹ ∈ Hb :=
      (Subgroup.mem_normalizer_iff.mp hxN ((hh : ↥M₀) : G)).mp hhHb
    refine Subgroup.mem_map.mpr ⟨⟨x * (hh : G) * x⁻¹, hHb hmem⟩,
      Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    have hprod : (⟨x * (hh : G) * x⁻¹, hHb hmem⟩ : ↥M₀) =
        (⟨x, hL hxL⟩ : ↥M₀) * hh * (⟨x, hL hxL⟩ : ↥M₀)⁻¹ :=
      Subtype.ext (by simp)
    rw [hprod, map_mul, map_mul, map_inv, hha]
  have transport_conj : ∀ (x : G) (hxL : x ∈ L)
      (hxN : x ∈ Subgroup.normalizer (Hb : Set G)),
      (Φ ⟨x, hL hxL⟩ ∈ Subgroup.normalizer (A : Set Q)) ∧
      ∀ a : ↥A, ((MulAut.congr e (ggConjAut Hb hxN)) a : Q) =
        Φ ⟨x, hL hxL⟩ * (a : Q) * (Φ ⟨x, hL hxL⟩)⁻¹ := by
    intro x hxL hxN
    constructor
    · rw [Subgroup.mem_normalizer_iff]
      intro a
      refine ⟨conj_mem x hxL hxN a, fun ha => ?_⟩
      have hxinv : Φ ⟨x⁻¹, hL (L.inv_mem hxL)⟩ = (Φ ⟨x, hL hxL⟩)⁻¹ := by
        rw [show (⟨x⁻¹, hL (L.inv_mem hxL)⟩ : ↥M₀) = (⟨x, hL hxL⟩ : ↥M₀)⁻¹ from
          Subtype.ext (by simp), map_inv]
      have hmem := conj_mem x⁻¹ (L.inv_mem hxL) (Subgroup.inv_mem _ hxN)
        (Φ ⟨x, hL hxL⟩ * a * (Φ ⟨x, hL hxL⟩)⁻¹) ha
      rw [hxinv] at hmem
      have h1 : (Φ ⟨x, hL hxL⟩)⁻¹ * (Φ ⟨x, hL hxL⟩ * a * (Φ ⟨x, hL hxL⟩)⁻¹) *
          ((Φ ⟨x, hL hxL⟩)⁻¹)⁻¹ = a := by group
      rwa [h1] at hmem
    · intro a
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      set b : ↥Hb := e.symm a with hb
      have hb_eq : e b = a := by rw [hb]; exact MulEquiv.apply_symm_apply e a
      have hbQ : Φ ⟨(b : G), hHb b.2⟩ = (a : Q) := by
        rw [← e_coe b, hb_eq]
      have hmem_b : x * (b : G) * x⁻¹ ∈ Hb :=
        (Subgroup.mem_normalizer_iff.mp hxN (b : G)).mp b.2
      have hconjAut : (ggConjAut Hb hxN b : ↥Hb) = ⟨x * (b : G) * x⁻¹, hmem_b⟩ :=
        Subtype.ext (ggConjAut_apply Hb hxN b)
      rw [hconjAut, e_coe]
      have hprod : (⟨x * (b : G) * x⁻¹, hHb hmem_b⟩ : ↥M₀) =
          (⟨x, hL hxL⟩ : ↥M₀) * ⟨(b : G), hHb b.2⟩ * (⟨x, hL hxL⟩ : ↥M₀)⁻¹ :=
        Subtype.ext (by simp)
      rw [hprod, map_mul, map_mul, map_inv, hbQ]
  have hD_mem : ∀ i, φ'' i ∈ ggInduced ⊤ A := by
    intro i
    have hφi : φ i ∈ ggAutomizer L Hb := by
      rw [hGen]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hφind : φ i ∈ ggInduced L Hb := by
      rw [ggAutomizer_eq] at hφi
      exact hφi
    obtain ⟨g, hgN, hgL, hgφ⟩ := exists_ggConjAut_eq_of_mem_ggInduced hφind
    have hconj := transport_conj g hgL hgN
    refine ⟨Φ ⟨g, hL hgL⟩, Subgroup.mem_top _, hconj.1, fun a => ?_⟩
    rw [show φ'' i = (MulAut.congr e) (φ i) from rfl, ← hgφ]
    exact hconj.2 a
  have hD'' : GGExtDatum ι'' C φ'' h α :=
    { mem := hD_mem
      lin := by
        intro o w
        change (ggLin (p := 3) ((MulEquiv.toAdditive e.symm).trans ι)
          ((MulAut.congr e) (φ o))) w = w - α o w • h o
        rw [ggLin_mulEquiv_congr (p := 3) e ι (φ o), hD.lin o w]
      pair := hD.pair
      indep := hD.indep
      diag := hD.diag }
  have hmap_le : Subgroup.map M (ggAutomizer L Hb) ≤ ggAutomizer N A := by
    intro ψ hψ
    rw [Subgroup.mem_map] at hψ
    obtain ⟨φi, hφi, rfl⟩ := hψ
    have hφind : φi ∈ ggInduced L Hb := by
      rw [ggAutomizer_eq] at hφi
      exact hφi
    obtain ⟨g, hgN, hgL, hgφ⟩ := exists_ggConjAut_eq_of_mem_ggInduced hφind
    have hconj := transport_conj g hgL hgN
    rw [← hgφ]
    refine Subgroup.subset_closure ⟨Φ ⟨g, hL hgL⟩, ?_, hconj.1, fun a => hconj.2 a⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hL hgL⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hgL, hgN⟩), rfl⟩
  have hmap_ge : ggAutomizer N A ≤ Subgroup.map M (ggAutomizer L Hb) := by
    intro ψ hψ
    have hψind : ψ ∈ ggInduced N A := by
      rw [ggAutomizer_eq] at hψ
      exact hψ
    obtain ⟨gbar, hgbarN, _, hgbarφ⟩ := hψind
    obtain ⟨hh, hhNb, hhΦ⟩ := Subgroup.mem_map.mp hgbarN
    have hhMemInf : (hh : G) ∈ Nb := Subgroup.mem_subgroupOf.mp hhNb
    have hgL : (hh : G) ∈ L := (Subgroup.mem_inf.mp hhMemInf).1
    have hgN : (hh : G) ∈ Subgroup.normalizer (Hb : Set G) :=
      (Subgroup.mem_inf.mp hhMemInf).2
    have hgbar_eq : Φ ⟨(hh : G), hL hgL⟩ = gbar :=
      (congrArg Φ (Subtype.ext rfl)).trans hhΦ
    have hconj := transport_conj (hh : G) hgL hgN
    refine Subgroup.mem_map.mpr ⟨ggConjAut Hb hgN, ?_, ?_⟩
    · exact Subgroup.subset_closure (ggConjAut_mem_ggInduced hgL hgN)
    · change (MulAut.congr e) (ggConjAut Hb hgN) = ψ
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      rw [hconj.2 a, hgbar_eq, hgbarφ a]
  have hmap : ggAutomizer N A = Subgroup.map M (ggAutomizer L Hb) :=
    le_antisymm hmap_ge hmap_le
  have hgen'' : ggAutomizer N A = Subgroup.closure (Set.range φ'') := by
    have hrange : Set.range φ'' = M '' Set.range φ := by
      change Set.range (M ∘ φ) = M '' Set.range φ
      rw [Set.range_comp]
    rw [hmap, hGen, MonoidHom.map_closure, hrange]
  have hring : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  exact hPD K d hring A N hA hcardA Γ C V ι'' φ'' h α hD'' hF4 hgen''

end CFSG.StandardType

end
