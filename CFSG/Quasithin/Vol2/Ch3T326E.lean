module

public import CFSG.Quasithin.Vol2.Ch3T326A
public import CFSG.Quasithin.Vol2.Ch8Sec3L0Cent
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open T325 (V₀_le_V V_le_VM M_le_NVM)
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Ctx

variable [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem not_le_normalizer : ¬ T ≤ Subgroup.normalizer (L : Set G) := by
  intro h
  apply c.ne
  refine le_antisymm (le_conjClosure L T) (conjClosure_le fun t ht l hl => ?_)
  exact (Subgroup.mem_normalizer_iff.mp (h ht) l).mp hl

theorem exists_t : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
  by_contra h
  push Not at h
  exact c.not_le_normalizer h

theorem L₀_eq (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    conjClosure L T = L ⊔ CFSG.conjugate L t :=
  Vol2.Ch10.SecA.fsuL0_eq_sup_of_fsu hA37 hA38 c.fsu c.not_le_normalizer ht htn

theorem L_le_NVM : L ≤ Subgroup.normalizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) :=
  c.L_le_L₀.trans (Subgroup.le_normalizer.trans (M_le_NVM T (conjClosure L T) V₀))

omit c in
theorem L₀_le_NVM (_c : Ctx T L V₀) : conjClosure L T ≤ Subgroup.normalizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) :=
  Subgroup.le_normalizer.trans (M_le_NVM T (conjClosure L T) V₀)

theorem T_le_NVM : T ≤ Subgroup.normalizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) :=
  c.T_le_M.trans (M_le_NVM T (conjClosure L T) V₀)

theorem pCoreOf_L_le : pCoreOf 2 L ≤ Subgroup.centralizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) := by
  rw [← Vol2.Ch10.SecA.inf_pCoreOf_fsuL0 c.fsu.maximal.1]
  exact inf_le_right.trans c.pCoreOf_L₀_le

theorem not_le_centralizer_VM : ¬ L ≤ Subgroup.centralizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  intro h
  have hL₀ : conjClosure L T ≤ Subgroup.centralizer (VM : Set G) := by
    refine conjClosure_le fun s hs l hl => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hsv : s⁻¹ * v * s ∈ VM := by
      have := (Subgroup.mem_normalizer_iff.mp (c.T_le_NVM (T.inv_mem hs)) v).mp hv
      simpa using this
    have hl' := Subgroup.mem_centralizer_iff.mp (h hl) _ hsv
    calc v * (s * l * s⁻¹) = s * ((s⁻¹ * v * s) * l) * s⁻¹ := by group
      _ = s * (l * (s⁻¹ * v * s)) * s⁻¹ := by rw [hl']
      _ = s * l * s⁻¹ * v := by group
  apply c.V₀_ne_bot
  rw [← c.comm_V₀, eq_bot_iff, Subgroup.commutator_le]
  intro v hv l hl
  have := Subgroup.mem_centralizer_iff.1 (hL₀ hl) v
    ((V₀_le_V T V₀).trans (V_le_VM T (conjClosure L T) V₀) hv)
  rw [Subgroup.mem_bot, commutatorElement_def, this]
  group

theorem quasi_LVM : CFSG.IsQuasisimple ↥(autOn L
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  refine isQuasisimple_autOn c.L_le_NVM c.fsu.quasisimple
    (fun x hx => c.pCoreOf_L_le ⟨x, ?_, rfl⟩) ?_
  · try with_reducible rfl
    exact hx
  · by_contra hcon
    push Not at hcon
    exact c.not_le_centralizer_VM fun l hl => hcon l hl

theorem commute_autOn (hA37 : Vol2Native.A37ForSQTKCat) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {a b : MulAut ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))}
    (ha : a ∈ autOn L (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G))))
    (hb : b ∈ autOn (CFSG.conjugate L t) (conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))) : a * b = b * a := by
  set VM := conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
    with hVM
  obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp ha
  obtain ⟨x, hxL, rfl⟩ := Setup.mem_autOn_iff.mp hb
  have hcomm : ⁅(g : G), (x : G)⁆ ∈ Subgroup.centralizer (VM : Set G) :=
    c.pCoreOf_L_le (Vol2.Ch10.SecA.commutator_conjugate_le_of_fsu hA37 c.fsu ht htn
      (Subgroup.commutator_mem_commutator hgL hxL)).1
  ext v
  rw [MulAut.mul_apply, MulAut.mul_apply]
  simp only [Setup.coe_conjAct_apply]
  set u := (x : G) * ((g : G) * v * (g : G)⁻¹) * (x : G)⁻¹ with hu
  have huVM : u ∈ VM := by
    have hgv : (g : G) * v * (g : G)⁻¹ ∈ VM := (Subgroup.mem_normalizer_iff.mp g.2 v).mp v.2
    exact (Subgroup.mem_normalizer_iff.mp x.2 _).mp hgv
  have hc := Subgroup.mem_centralizer_iff.mp hcomm u huVM
  rw [commutatorElement_def] at hc
  calc (g : G) * ((x : G) * v * (x : G)⁻¹) * (g : G)⁻¹ =
        (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ * u * ((g : G) * x * (g : G)⁻¹ * (x : G)⁻¹)⁻¹ := by
          rw [hu]; group
    _ = u := by rw [← hc]; group

end Ctx

end CFSG.Quasithin.H13.T326
