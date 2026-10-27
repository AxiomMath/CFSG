module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneTwo
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFour
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFiveLift
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFiveConj

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def IsDegenerate (F H : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1 ∧
    (∀ f ∈ F, ∃ h ∈ H, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - h v ∈ centralizerSpace F) ∧
    ∃ t ∈ F, t ≠ 1 ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      t v - v ∈ centralizerSpace F

@[expose] def kerSection (F : Subgroup (U ≃ₗ[ZMod p] U)) : Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure {t | t ∈ F ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
    t v - v ∈ centralizerSpace F}

theorem mem_kerSection_iff {F : Subgroup (U ≃ₗ[ZMod p] U)} {t : U ≃ₗ[ZMod p] U} :
    t ∈ kerSection F ↔ t ∈ F ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      t v - v ∈ centralizerSpace F := by
  constructor
  · intro ht
    let S : Subgroup (U ≃ₗ[ZMod p] U) :=
      { carrier := {s | s ∈ F ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
          s v - v ∈ centralizerSpace F}
        one_mem' := ⟨F.one_mem, by intro v _; simp⟩
        mul_mem' := by
          rintro s u ⟨hsF, hs⟩ ⟨huF, hu⟩
          refine ⟨F.mul_mem hsF huF, fun v hv => ?_⟩
          have huv : u v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
            apply_mem_commutatorSpace huF hv
          have h1 : s (u v) - u v ∈ centralizerSpace F := hs (u v) huv
          have h2 : u v - v ∈ centralizerSpace F := hu v hv
          have heq : (s * u) v - v = (s (u v) - u v) + (u v - v) := by
            rw [LinearEquiv.mul_apply]; abel
          rw [heq]
          exact (centralizerSpace F).add_mem h1 h2
        inv_mem' := by
          rintro s ⟨hsF, hs⟩
          refine ⟨F.inv_mem hsF, fun v hv => ?_⟩
          have hsv : s.symm v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
            apply_mem_commutatorSpace (F.inv_mem hsF) hv
          have h1 : s (s.symm v) - s.symm v ∈ centralizerSpace F := hs (s.symm v) hsv
          rw [LinearEquiv.apply_symm_apply] at h1
          change s.symm v - v ∈ centralizerSpace F
          have heq : s.symm v - v = -(v - s.symm v) := by abel
          rw [heq]
          exact (centralizerSpace F).neg_mem h1 }
    have hle : kerSection F ≤ S := by
      rw [kerSection]
      exact (Subgroup.closure_le S).mpr fun t ht => ht
    exact hle ht
  · rintro ⟨htF, ht⟩
    rw [kerSection]
    exact Subgroup.subset_closure ⟨htF, ht⟩

theorem kerSection_le {F : Subgroup (U ≃ₗ[ZMod p] U)} : kerSection F ≤ F :=
  (Subgroup.closure_le _).mpr fun _ hg => hg.1

theorem conj_mem_kerSection {F : Subgroup (U ≃ₗ[ZMod p] U)} {f t : U ≃ₗ[ZMod p] U}
    (hf : f ∈ F) (ht : t ∈ kerSection F) :
    f * t * f⁻¹ ∈ kerSection F := by
  obtain ⟨htF, htV⟩ := mem_kerSection_iff.mp ht
  refine mem_kerSection_iff.mpr ⟨F.mul_mem (F.mul_mem hf htF) (F.inv_mem hf), fun v hv => ?_⟩
  have hw : f⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    apply_mem_commutatorSpace (F.inv_mem hf) hv
  have h1 : t (f⁻¹ v) - f⁻¹ v ∈ centralizerSpace F := htV (f⁻¹ v) hw
  have hmap := map_centralizerSpace_of_mem_normalizer (H := F) (Subgroup.le_normalizer hf)
  have h2 : f (t (f⁻¹ v) - f⁻¹ v) ∈ centralizerSpace F := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (f := (f : U →ₗ[ZMod p] U)) h1
  change f (t (f⁻¹ v)) - v ∈ centralizerSpace F
  rw [show f (t (f⁻¹ v)) - v = f (t (f⁻¹ v) - f⁻¹ v) by
    rw [map_sub]; simp]
  exact h2

private theorem reflGen_closure_insert {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} (hH : ReflGen p H) (ha : IsRefl p a) :
    ReflGen p (Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))) := by
  unfold ReflGen
  set F := Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) with hFdef
  have hmem : a ∈ F := by
    rw [hFdef]
    exact Subgroup.subset_closure (Set.mem_insert a _)
  have hHmem : H ≤ F := by
    intro h hh
    rw [hFdef]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have hS : H ≤ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ F ∧ IsRefl p t} := by
    rw [hH]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨htH, htr⟩
    exact Subgroup.subset_closure ⟨hHmem htH, htr⟩
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun _ hx => hx.1)
  rw [hFdef]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Subgroup.subset_closure ⟨hmem, ha⟩
  · exact hS hx

private theorem commutatorSpace_closure_insert [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (a : U ≃ₗ[ZMod p] U) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))) =
      HardMathSupport.Kantor79.commutatorSpace H ⊔
        HardMathSupport.Kantor79.movedSpace a := by
  classical
  let x : Option H → (U ≃ₗ[ZMod p] U) := fun o => o.elim a (fun h => h.1)
  have hrange : Set.range x = insert a (H : Set (U ≃ₗ[ZMod p] U)) := by
    ext z; constructor
    · rintro ⟨o, rfl⟩; cases o with
      | none => exact Set.mem_insert _ _
      | some h => exact Set.mem_insert_of_mem _ h.2
    · rintro (rfl | hz)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨z, hz⟩, rfl⟩
  have hsub : Subgroup.closure (Set.range (fun h : H => (h : U ≃ₗ[ZMod p] U))) = H := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun h hh =>
      Subgroup.subset_closure ⟨⟨h, hh⟩, rfl⟩
    rintro _ ⟨h, rfl⟩
    exact h.2
  have hH : (⨆ h : H, HardMathSupport.Kantor79.movedSpace (h : U ≃ₗ[ZMod p] U)) =
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [← HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
      (fun h : H => (h : U ≃ₗ[ZMod p] U)), hsub]
  rw [show Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) =
      Subgroup.closure (Set.range x) by rw [hrange],
    HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace x, iSup_option]
  simp only [x, Option.elim_none, Option.elim_some]
  rw [hH]
  exact sup_comm _ _

private theorem not_movedSpace_le_of_maximal (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    (htab : TFNegOrGen p l) {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K → SplitSupport K l →
      K = H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (haH : a ∉ H) :
    ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H := by
  intro hmov
  have hHF : H ≤ F := by
    rw [hF]
    exact fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have haF : a ∈ F := by
    rw [hF]
    exact Subgroup.subset_closure (Set.mem_insert a _)
  have hVeq : HardMathSupport.Kantor79.commutatorSpace F =
      HardMathSupport.Kantor79.commutatorSpace H := by
    have hsup := commutatorSpace_closure_insert (H := H) a
    rw [← hF] at hsup
    rw [hsup, sup_eq_left.mpr hmov]
  have hFgen : ReflGen p F := by
    rw [hF]
    exact reflGen_closure_insert hH ha
  have hFisR : IsRGroup p F := ⟨hFgen, hFt⟩
  have hirr : IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) := by
    intro X _ hXVF hXinv
    have hXH : ∀ h ∈ H, ∀ x ∈ X, h x ∈ X := fun h hh => hXinv h (hHF hh)
    have hXVH : X ≤ HardMathSupport.Kantor79.commutatorSpace H := by
      rw [← hVeq]; exact hXVF
    rcases hHs.2.2 X bot_le hXVH hXH with hX | hX
    · exact Or.inl hX
    · exact Or.inr (by rw [hVeq]; exact hX)
  have hl : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l := by
    rw [hVeq]; exact hHs.2.1
  have hdF : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact ⟨x, hHF hx, y, hHF hy, hxr, hyr, hxy⟩
  have hsplit : SplitSupport F l :=
    splitSupport_of_irredOnSection hp (fun _ => htab) hFisR hirr hl hdF
  have hFH : F = H := hmax F le_rfl hHF hFgen hsplit
  exact haH (hFH ▸ haF)

private theorem not_invariant_commutatorSpace (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace a ≤
      HardMathSupport.Kantor79.commutatorSpace H)
    (haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))) :
    ¬ (∀ f ∈ F, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
      f w ∈ HardMathSupport.Kantor79.commutatorSpace H) := by
  intro hInv
  have hHF : H ≤ F := by
    rw [hF]
    exact fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have haF : a ∈ F := by
    rw [hF]
    exact Subgroup.subset_closure (Set.mem_insert a _)
  have hafix : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H, a w = w :=
    fun w hw => apply_eq_self_of_not_movedSpace_le ha.2 (fun w hw => hInv a haF w hw) hnot hw
  have hafix_sub : a ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.commutatorSpace H : Set U) := by
    rw [mem_fixingSubgroup_iff]
    intro w hw
    simpa using hafix w hw
  refine haC (Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
  exact (commute_of_mem_fixing_of_mem_reflSubgroupIn hp hFt ⟨haF, hafix_sub⟩
    (le_reflSubgroupIn hHF hH le_rfl hh)).symm

private theorem finrank_commutatorSpace_eq_succ [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (ha : IsRefl p a) (hHs : SplitSupport H l)
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace a ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1 := by
  have hsup := commutatorSpace_closure_insert (H := H) a
  rw [← hF] at hsup
  have hline : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace a) = 1 := ha.2
  have hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓
      HardMathSupport.Kantor79.movedSpace a = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    by_contra hv0
    have hspan : HardMathSupport.Kantor79.movedSpace a = Submodule.span (ZMod p) {v} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hline hv.2 hv0
    exact hnot (by
      rw [hspan]
      exact Submodule.span_le.mpr (by rintro w rfl; exact hv.1))
  rw [hsup]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace H) (HardMathSupport.Kantor79.movedSpace a)
  rw [hinf, finrank_bot, add_zero, hHs.2.1, hline] at hsum
  exact hsum

private theorem le_of_eq_closure_insert {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))) :
    H ≤ F := by
  rw [hF]
  exact fun h hh => Subgroup.subset_closure (Set.mem_insert_of_mem a hh)

private theorem mem_of_eq_closure_insert {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))) :
    a ∈ F := by
  rw [hF]
  exact Subgroup.subset_closure (Set.mem_insert a _)

private theorem reducible_section_le_centralizer (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    {X : Submodule (ZMod p) U} (hXinv : ∀ f ∈ F, ∀ x ∈ X, f x ∈ X)
    (hXVF : X ≤ HardMathSupport.Kantor79.commutatorSpace F)
    (hXne' : X ≠ HardMathSupport.Kantor79.commutatorSpace F) :
    X ≤ centralizerSpace H := by
  have hHF : H ≤ F := le_of_eq_closure_insert hF
  have hXH : ∀ h ∈ H, ∀ x ∈ X, h x ∈ X := fun h hh => hXinv h (hHF hh)
  have hirrH : IrredOnSection H
      (HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H)
      (HardMathSupport.Kantor79.commutatorSpace H) := by
    rw [hHs.1.inf_eq_bot]
    exact hHs.2.2
  rcases commutatorSpace_le_or_le_centralizerSpace hp hH hirrH hXH with hVHX | hXVc
  · exfalso
    have hge : l ≤ Module.finrank (ZMod p) X := by
      have hmono := Submodule.finrank_mono hVHX
      rwa [hHs.2.1] at hmono
    have hle : Module.finrank (ZMod p) X ≤ l + 1 := by
      have hmono := Submodule.finrank_mono hXVF
      rwa [hdim] at hmono
    have hfin : Module.finrank (ZMod p) X = l ∨ Module.finrank (ZMod p) X = l + 1 := by omega
    rcases hfin with hfl | hfl
    · have hXVH : X = HardMathSupport.Kantor79.commutatorSpace H :=
        (Submodule.eq_of_le_of_finrank_eq hVHX (by rw [hHs.2.1, hfl])).symm
      exact not_invariant_commutatorSpace hp hF hFt ha hH hnot haC (hXVH ▸ hXinv)
    · exact hXne' (Submodule.eq_of_le_of_finrank_eq hXVF (by rw [hfl, hdim]))
  · exact hXVc

private theorem line_inf_centralizer_finrank [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hHs : SplitSupport H l)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hVHleVF : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F)
    (hXW : X ≤ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H)
    (hXne : X ≠ ⊥) :
    Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) = 1 := by
  have hW0ne : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H ≠ ⊥ := by
    intro hbot
    exact hXne (le_bot_iff.mp (hXW.trans (le_of_eq hbot)))
  have hW0bot : (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) ⊓
      HardMathSupport.Kantor79.commutatorSpace H = ⊥ := by
    rw [inf_assoc, inf_comm (centralizerSpace H) (HardMathSupport.Kantor79.commutatorSpace H),
      hHs.1.inf_eq_bot, inf_bot_eq]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H)
    (HardMathSupport.Kantor79.commutatorSpace H)
  rw [hW0bot, finrank_bot, add_zero, hHs.2.1] at hsum
  have hle : Module.finrank (ZMod p) ↥((HardMathSupport.Kantor79.commutatorSpace F ⊓
      centralizerSpace H) ⊔ HardMathSupport.Kantor79.commutatorSpace H) ≤ l + 1 := by
    rw [← hdim]
    exact Submodule.finrank_mono (sup_le inf_le_left hVHleVF)
  have hpos : 0 < Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0ne
    have hmono : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {v}) ≤
        Module.finrank (ZMod p)
          ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) :=
      Submodule.finrank_mono (Submodule.span_le.mpr (by rintro w rfl; exact hv))
    rw [finrank_span_singleton hv0] at hmono
    omega
  omega

private theorem reducible_section_finrank_one [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hW0fin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) = 1)
    (hXW : X ≤ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H)
    (hXne : X ≠ ⊥) :
    Module.finrank (ZMod p) X = 1 := by
  have hle : Module.finrank (ZMod p) X ≤ 1 := by
    rw [← hW0fin]
    exact Submodule.finrank_mono hXW
  have hpos : 0 < Module.finrank (ZMod p) X := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    have hmono : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {v}) ≤
        Module.finrank (ZMod p) X :=
      Submodule.finrank_mono (Submodule.span_le.mpr (by rintro w rfl; exact hv))
    rw [finrank_span_singleton hv0] at hmono
    omega
  omega

private theorem degenerate_a_fixes_line (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a)
    (haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (hW0fin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) = 1)
    (hW0inv : ∀ f ∈ F, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H,
      f w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) :
    ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H, a w = w := by
  intro w hw
  by_contra hne
  have hxne : a w - w ≠ 0 := sub_ne_zero.mpr hne
  have hxVa : a w - w ∈ HardMathSupport.Kantor79.movedSpace a := ⟨w, by simp⟩
  have hxW : a w - w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H :=
    (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H).sub_mem
      (hW0inv a (mem_of_eq_closure_insert hF) w hw) hw
  have hVa : HardMathSupport.Kantor79.movedSpace a = Submodule.span (ZMod p) {a w - w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one ha.2 hxVa hxne
  have hW0 : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H =
      Submodule.span (ZMod p) {a w - w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hW0fin hxW hxne
  have hVaW : HardMathSupport.Kantor79.movedSpace a ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H := by
    rw [hVa, hW0]
  have haR : a ∈ reflSubgroupIn p F (HardMathSupport.Kantor79.commutatorSpace F ⊓
      centralizerSpace H) :=
    Subgroup.subset_closure ⟨mem_of_eq_closure_insert hF, ha, fun v => hVaW ⟨v, rfl⟩⟩
  have hcomm : ∀ h ∈ H, Commute h a := by
    intro h hh
    have hhfix : h ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
        ((HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H :
          Submodule (ZMod p) U) : Set U) := by
      rw [mem_fixingSubgroup_iff]
      intro u hu
      exact (mem_centralizerSpace.mp hu.2) h hh
    exact commute_of_mem_fixing_of_mem_reflSubgroupIn hp hFt
      ⟨(le_of_eq_closure_insert hF) hh, hhfix⟩ haR
  exact haC (Subgroup.mem_centralizer_iff.mpr fun h hh => hcomm h hh)

private theorem degenerate_fixes_line {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hafix : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H, a w = w) :
    ∀ f ∈ F, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H, f w = w := by
  intro f hf w hw
  have hf' : f ∈ Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) := by
    rwa [← hF]
  clear hf
  induction hf' using Subgroup.closure_induction with
  | mem g hg =>
      rcases Set.mem_insert_iff.mp hg with rfl | hgH
      · exact hafix w hw
      · exact (mem_centralizerSpace.mp hw.2) g hgH
  | one => rfl
  | mul x y hx hy ihx ihy => rw [LinearEquiv.mul_apply, ihy, ihx]
  | inv x hx ihx =>
      calc x⁻¹ w = x⁻¹ (x w) := by rw [ihx]
        _ = w := LinearEquiv.symm_apply_apply x w

private theorem line_inf_centralizer_of_reducible (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hred : ¬ IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) :
    Module.finrank (ZMod p)
        ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) = 1 ∧
      (∀ f ∈ F, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H,
        f w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H) := by
  have hHF : H ≤ F := le_of_eq_closure_insert hF
  have hVHleVF : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F := by
    rw [commutatorSpace_le_iff]
    intro h hh v
    exact Submodule.subset_span ⟨h, hHF hh, v, rfl⟩
  rw [IrredOnSection] at hred
  push Not at hred
  obtain ⟨X, -, hXVF, hXinv, hXne, hXne'⟩ := hred
  have hXVc := reducible_section_le_centralizer hp hF hFt ha hH hHs haC hnot hdim hXinv hXVF
    hXne'
  have hXW : X ≤ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H :=
    le_inf hXVF hXVc
  have hW0fin := line_inf_centralizer_finrank hHs hdim hVHleVF hXW hXne
  have hXfin := reducible_section_finrank_one hW0fin hXW hXne
  have hXeq : X = HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H :=
    Submodule.eq_of_le_of_finrank_eq hXW (by rw [hXfin, hW0fin])
  exact ⟨hW0fin, hXeq ▸ hXinv⟩

private theorem degenerate_inf_finrank (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hred : ¬ IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) :
    Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1 := by
  obtain ⟨hW0fin, hW0inv⟩ :=
    line_inf_centralizer_of_reducible hp hF hFt ha hH hHs haC hnot hdim hred
  have hHF : H ≤ F := le_of_eq_closure_insert hF
  have hafix := degenerate_a_fixes_line hp hF hFt ha haC hW0fin hW0inv
  have hFfix := degenerate_fixes_line hF hafix
  have hVFleVH : centralizerSpace F ≤ centralizerSpace H := by
    intro v hv
    exact (mem_centralizerSpace).mpr fun h hh => (mem_centralizerSpace.mp hv) h (hHF hh)
  have hWeq : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F =
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace H := by
    refine le_antisymm (fun v hv => ⟨hv.1, hVFleVH hv.2⟩) fun v hv => ⟨hv.1, ?_⟩
    exact (mem_centralizerSpace).mpr fun f hf => hFfix f hf v hv
  rw [hWeq]
  exact hW0fin

private theorem exists_kerSection_ne_one {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} (hHF : H ≤ F) (haF : a ∈ F) (haH : a ∉ H)
    (hsecond : ∀ f ∈ F, ∃ h ∈ H, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - h v ∈ centralizerSpace F) :
    ∃ t ∈ F, t ≠ 1 ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      t v - v ∈ centralizerSpace F := by
  obtain ⟨h, hhH, hha⟩ := hsecond a haF
  refine ⟨h⁻¹ * a, F.mul_mem (F.inv_mem (hHF hhH)) haF, ?_, ?_⟩
  · intro ht
    refine haH ?_
    have haeq : a = h := by
      simpa using congrArg (fun g => h * g) ht
    rw [haeq]
    exact hhH
  · intro v hv
    have hfix : h⁻¹ (a v - h v) = a v - h v :=
      (mem_centralizerSpace.mp (hha v hv)) h⁻¹ (F.inv_mem (hHF hhH))
    have h1 : (h⁻¹ * a) v - v = h⁻¹ (a v - h v) := by
      simp [LinearEquiv.mul_apply]
    rw [h1, hfix]
    exact hha v hv

private theorem isDegenerate_of_not_irredOnSection (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {l : ℕ} (htab : TFNegOrGen p l) (hcop : TFCoprimeWitness p l)
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K → SplitSupport K l →
      K = H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (haH : a ∉ H) (haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hirr : ¬ IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F)) :
    IsDegenerate F H := by
  have hHF : H ≤ F := le_of_eq_closure_insert hF
  have haF : a ∈ F := mem_of_eq_closure_insert hF
  have hFgen : ReflGen p F := by rw [hF]; exact reflGen_closure_insert hH ha
  have hW := degenerate_inf_finrank hp hF hFt ha hH hHs haC hnot hdim hirr
  obtain ⟨F₁, hF₁F, hF₁gen, hF₁l, hlift⟩ :=
    exists_reflGen_lift hp htab hFgen hHF hHs hd hdim hW
  have hsecond := exists_mem_sub_mem_of_lift hp htab hcop ⟨hFgen, hFt⟩ hHF hH hHs hmax hd hdim hW
    hF₁F hF₁gen hF₁l hlift
  exact ⟨hW, hsecond, exists_kerSection_ne_one hHF haF haH hsecond⟩

theorem splitSupport_succ_or_degenerate (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    (htab : TFNegOrGen p l)
    (htab' : l + 1 < Module.finrank (ZMod p) U → TFNegOrGen p (l + 1))
    (hcop : TFCoprimeWitness p l) {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hF : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))))
    (hFt : QTwoLin.TransvectionFree F) (ha : IsRefl p a) (hH : ReflGen p H)
    (hHs : SplitSupport H l)
    (hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K → SplitSupport K l →
      K = H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (haH : a ∉ H) (haC : a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1 ∧
      (SplitSupport F (l + 1) ∨ IsDegenerate F H) := by
  have hHF : H ≤ F := le_of_eq_closure_insert hF
  have hFgen : ReflGen p F := by rw [hF]; exact reflGen_closure_insert hH ha
  have hnot : ¬ HardMathSupport.Kantor79.movedSpace a ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    not_movedSpace_le_of_maximal hp htab hF hFt ha hH hHs hmax hd haH
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1 :=
    finrank_commutatorSpace_eq_succ hF ha hHs hnot
  have hdF : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact ⟨x, hHF hx, y, hHF hy, hxr, hyr, hxy⟩
  refine ⟨hdim, ?_⟩
  by_cases hirr : IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F)
  · exact Or.inl (splitSupport_of_irredOnSection hp htab' ⟨hFgen, hFt⟩ hirr hdim hdF)
  · exact Or.inr (isDegenerate_of_not_irredOnSection hp htab hcop hF hFt ha hH hHs hmax hd haH
      haC hnot hdim hirr)

end CFSG.StandardType.ZS
