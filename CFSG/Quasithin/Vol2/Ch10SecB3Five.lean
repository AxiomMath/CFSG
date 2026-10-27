module

public import CFSG.Quasithin.Vol2.Ch10SecB3Two
public import CFSG.Quasithin.Vol2.Ch10SecC8H1A
public import CFSG.Quasithin.Vol2.Ch10SecB3End

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem realizes_subgroupOf {D : FFModel} {L U W : Subgroup G} [IsMulCommutative ↥U]
    [IsMulCommutative ↥W] (hWU : W ≤ U) (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hC : ∀ l ∈ L, l ∈ Subgroup.centralizer (U : Set G) ↔ l ∈ Subgroup.centralizer (W : Set G))
    (h : D.Realizes (V := ↥W) (autOn L W) ⊤ ⊥) :
    D.Realizes (V := ↥U) (autOn L U) (W.subgroupOf U) ⊥ := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨ψ, hψ⟩ := SecC.exists_autOnEquiv hLW hLU fun l hl => (hC l hl).symm
  let e : ↥(⊤ : Subgroup ↥W) ≃* ↥(W.subgroupOf U) :=
    Subgroup.topEquiv.trans (Subgroup.subgroupOfEquivOfLe hWU).symm
  have he : ∀ u : ↥(⊤ : Subgroup ↥W), (((e u : ↥(W.subgroupOf U)) : ↥U) : G) = ((u : ↥W) : G) :=
    fun _ => rfl
  refine ⟨_, SecC.realizesVia_transport hπ ψ e (fun u => ?_) bot_le
    (fun h' u hu => InternalSec.autOn_inv_subgroupOf hLW h' h'.2 u hu) (fun h' z hz => ?_)
    (fun g u hu => ?_)⟩
  · rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h1
      apply Subtype.ext
      have := congrArg Subtype.val h1
      exact this
    · intro h1
      apply Subtype.ext
      have := congrArg Subtype.val h1
      exact this
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · obtain ⟨⟨l, hlN⟩, hl, hg⟩ := SecB.mem_autOn_iff.mp g.2
    have hg' : g = ⟨conjAct W ⟨l, hLW hl⟩, SecB.mem_autOn_iff.mpr ⟨⟨l, hLW hl⟩, hl, rfl⟩⟩ :=
      Subtype.ext hg.symm
    subst hg'
    rw [hψ l hl]
    apply Subtype.ext
    rw [conjAct_apply_coe, he, he, conjAct_apply_coe]

theorem realizes_conjugate_subgroupOf {D : FFModel} {L U W : Subgroup G} [IsMulCommutative ↥U]
    {s : G} (hsL : s ∈ Subgroup.normalizer (L : Set G)) (hsU : s ∈ Subgroup.normalizer (U : Set G))
    (h : D.Realizes (V := ↥U) (autOn L U) (W.subgroupOf U) ⊥) :
    D.Realizes (V := ↥U) (autOn L U) ((CFSG.conjugate W s).subgroupOf U) ⊥ := by
  obtain ⟨π, hπ⟩ := h
  set σ : MulAut ↥U := (conjAct U ⟨s, hsU⟩)⁻¹ with hσ
  have h2 := SecA.realizesVia_map_conj hπ σ
  have hH : (autOn L U).map (MulAut.conj σ).toMonoidHom = autOn L U := by
    rw [hσ, ← SecA.autOn_conjugate hsU, SecA.conjugate_eq_self_iff.mpr hsL]
  have hσs : ∀ v : ↥U, ((σ.symm v : ↥U) : G) = s * v * s⁻¹ := fun v =>
    conjAct_apply_coe U ⟨s, hsU⟩ v
  have hW : (W.subgroupOf U).map σ.toMonoidHom = (CFSG.conjugate W s).subgroupOf U := by
    ext v
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      SecA.mem_conjugate_iff, hσs]
  have h3 : D.Realizes (V := ↥U) ((autOn L U).map (MulAut.conj σ).toMonoidHom)
      ((W.subgroupOf U).map σ.toMonoidHom) ((⊥ : Subgroup ↥U).map σ.toMonoidHom) := ⟨_, h2⟩
  rwa [hH, hW, Subgroup.map_bot] at h3

variable [Finite G] {T L I : Subgroup G}

theorem mem_centralizer_iff_of_le_fsuUL
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Hyp10 G T L I)
    {W : Subgroup G} (hWU : W ≤ fsuUL T L I) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hne : ⁅W, L⁆ ≠ ⊥) :
    ∀ l ∈ L, l ∈ Subgroup.centralizer (fsuUL T L I : Set G) ↔
      l ∈ Subgroup.centralizer (W : Set G) := by
  intro l hl
  refine ⟨fun h => Subgroup.centralizer_le hWU h, fun h => ?_⟩
  have h1 := SecA.inf_centralizer_le_pCoreOf h37 h38 hyp hLW hne ⟨hl, h⟩
  exact Subgroup.centralizer_le (fsuUL_le' T L I) (SecA.pCoreOf_le_centralizer_fsuVM h322 hyp h1)

omit [Finite G] in
theorem le_centralizer_conjugate_iff {L W : Subgroup G} {s : G}
    (hsL : s ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate W s ≤ Subgroup.centralizer (L : Set G) ↔
      W ≤ Subgroup.centralizer (L : Set G) := by
  have key : ∀ (X : Subgroup G) (g : G), g ∈ Subgroup.normalizer (L : Set G) →
      X ≤ Subgroup.centralizer (L : Set G) →
      CFSG.conjugate X g ≤ Subgroup.centralizer (L : Set G) := by
    intro X g hg hX x hx
    rw [SecA.mem_conjugate_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hgl : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg l).mp hl
    have h1 := Subgroup.mem_centralizer_iff.mp (hX hx) _ hgl
    have h2 : g * (l * x) * g⁻¹ = g * (x * l) * g⁻¹ := by
      calc g * (l * x) * g⁻¹ = g * l * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * l * g⁻¹) := h1
        _ = g * (x * l) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  refine ⟨fun h => ?_, key W s hsL⟩
  have h1 := key _ s⁻¹ ((Subgroup.normalizer _).inv_mem hsL) h
  rwa [SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one] at h1

theorem commutator_fsuUL_eq_bot_five
    (hF : FactCommL3Pair) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Hyp10 G T L I)
    (h5 : Case10_1_1Five T L I) {A : Subgroup G} (hA : A ≤ cenL0 T L I) :
    ⁅fsuUL T L I, A⁆ = ⊥ := by
  obtain ⟨-, s, hsT, hsN, W, hWU, hLW, hsum, hinf, ⟨hWab, K, hKf, hKfin, hK, hR⟩, hnot⟩ := h5
  set U := fsuUL T L I with hUdef
  have hVab : IsMulCommutative ↥(fsuVM T L I) := (SecA.isElemAbelian_fsuVM hyp).1
  have hUab : IsMulCommutative ↥U := SecA.isMulCommutative_of_le (fsuUL_le' T L I)
  have hLV := L_le_normalizer_fsuVM T L I
  have hLU : L ≤ Subgroup.normalizer (U : Set G) :=
    SecA.le_normalizer_commutator hLV Subgroup.le_normalizer
  have hsU : s ∈ Subgroup.normalizer (U : Set G) :=
    SecA.le_normalizer_commutator
      (Subgroup.zpowers_le.mpr (SecA.le_normalizer_fsuVM T L I hsT))
      (Subgroup.zpowers_le.mpr hsN) (Subgroup.mem_zpowers s)
  have hWsU : CFSG.conjugate W s ≤ U := le_sup_right.trans hsum.le
  have hLWs : L ≤ Subgroup.normalizer (CFSG.conjugate W s : Set G) :=
    SecA.le_normalizer_conjugate_of hsN hLW
  have hWL : ¬ W ≤ Subgroup.centralizer (L : Set G) := by
    intro h
    have hU : U ≤ Subgroup.centralizer (L : Set G) := by
      rw [← hsum]
      exact sup_le h ((le_centralizer_conjugate_iff hsN).mpr h)
    apply SecA.commutator_fsuVM_ne_bot hyp.fsu
    have h1 := SecC.commutator_fsuUL_eq hyp
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hU] at h1
    exact h1.symm
  have hne : ⁅W, L⁆ ≠ ⊥ := fun h =>
    hWL (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hne' : ⁅CFSG.conjugate W s, L⁆ ≠ ⊥ := fun h =>
    hWL ((le_centralizer_conjugate_iff hsN).mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h))
  have R1 := realizes_subgroupOf hWU hLU hLW
    (mem_centralizer_iff_of_le_fsuUL h37 h38 h322 hyp hWU hLW hne) hR
  have R2 := realizes_conjugate_subgroupOf hsN hsU R1
  have hnot' := InternalSec.not_secIsoL_of_not_isXSectionIso hWU hWsU hLU hLW hLWs hnot
  have hc : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ Subgroup.centralizer (U : Set G) :=
    fun a ha l hl => Subgroup.centralizer_le (fsuUL_le' T L I)
      ((mem_cenL0.mp (hA ha)).2 l (SecA.le_fsuL0 T L hl))
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haN := cenL0_le_normalizer_fsuUL T L I (hA ha)
  have hx : conjAct U ⟨a, haN⟩ ∈ autOn A U := SecB.mem_autOn_iff.mpr ⟨⟨a, haN⟩, ha, rfl⟩
  have hx1 := hF ↥U (autOn L U) (W.subgroupOf U) ((CFSG.conjugate W s).subgroupOf U)
    (InternalSec.sup_subgroupOf_eq_top hWU hWsU hsum) (InternalSec.inf_subgroupOf_eq_bot hinf)
    ⟨K, hKf, hKfin, hK, R1⟩ ⟨K, hKf, hKfin, hK, R2⟩ hnot' (conjAct U ⟨a, haN⟩)
    (fun h hh => autOn_comm hc _ hx h hh)
  have h1 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : G)) hx1
  simp only [conjAct_apply_coe, MulAut.one_apply] at h1
  calc a * u = a * u * a⁻¹ * a := by group
    _ = u * a := by rw [h1]

theorem trivOnV_of_five
    (hF : FactCommL3Pair) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Hyp10 G T L I)
    (h5 : Case10_1_1Five T L I) (H : Subgroup G) : TrivOnV T L I H := by
  intro p _ _ _ A hA _ hAp
  exact commutator_fsuVM_eq_bot_of_U h37 h38 hyp
    (fun _ hA' _ => commutator_fsuUL_eq_bot_five hF h37 h38 h322 hyp h5 hA') hA hAp

end CFSG.Quasithin.Vol2.Ch10.SecB
