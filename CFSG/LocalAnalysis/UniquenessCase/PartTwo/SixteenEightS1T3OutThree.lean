module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutThreeA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutThreeB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private theorem s16t3_map_injective (x : MulAut W) :
    Function.Injective (fun I : Subgroup W => I.map x.toMonoidHom) := by
  intro I I' h
  have h1 := congrArg (Subgroup.map (x⁻¹).toMonoidHom) h
  rw [Subgroup.map_map, Subgroup.map_map] at h1
  have hcomp : (x⁻¹).toMonoidHom.comp x.toMonoidHom = MonoidHom.id W := by ext w; simp
  rwa [hcomp, Subgroup.map_id, Subgroup.map_id] at h1

private noncomputable def s16t3_irrSetActFun (h : ThreeNat A L T) (a : ↥A) :
    Equiv.Perm ↥(irrSet L) :=
  Equiv.ofBijective
    (fun I : ↥(irrSet L) =>
      ⟨(I : Subgroup W).map (a : MulAut W).toMonoidHom,
        map_mem_irrSet (fun x hx => conj_mem_of_mem_normalizer (h.normal a.2) hx)
          (fun x hx => inv_conj_mem_of_mem_normalizer (h.normal a.2) hx) I.2⟩)
    ⟨fun I I' hII' => Subtype.ext (s16t3_map_injective (a : MulAut W)
        (Subtype.ext_iff.mp hII')),
     fun I' => ⟨⟨(I' : Subgroup W).map ((a : MulAut W)⁻¹).toMonoidHom,
        map_mem_irrSet
          (fun x hx => conj_mem_of_mem_normalizer (h.normal (A.inv_mem a.2)) hx)
          (fun x hx => inv_conj_mem_of_mem_normalizer (h.normal (A.inv_mem a.2)) hx) I'.2⟩, by
       apply Subtype.ext
       show ((I' : Subgroup W).map ((a : MulAut W)⁻¹).toMonoidHom).map
           (a : MulAut W).toMonoidHom = (I' : Subgroup W)
       rw [Subgroup.map_map]
       have hcomp : (a : MulAut W).toMonoidHom.comp ((a : MulAut W)⁻¹).toMonoidHom =
           MonoidHom.id W := by ext w; simp
       rw [hcomp, Subgroup.map_id]⟩⟩

private lemma s16t3_irrSetActFun_apply (h : ThreeNat A L T) (a : ↥A) (I : ↥(irrSet L)) :
    (s16t3_irrSetActFun h a I : Subgroup W) = (I : Subgroup W).map (a : MulAut W).toMonoidHom :=
  rfl

private noncomputable def s16t3_irrSetAct (h : ThreeNat A L T) :
    ↥A →* Equiv.Perm ↥(irrSet L) where
  toFun := s16t3_irrSetActFun h
  map_one' := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    simp only [s16t3_irrSetActFun_apply, Equiv.Perm.one_apply]
    exact Subgroup.map_id _
  map_mul' a b := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    simp only [s16t3_irrSetActFun_apply, Equiv.Perm.mul_apply]
    rw [Subgroup.map_map]
    congr 1

private lemma s16t3_irrSetAct_apply (h : ThreeNat A L T) (a : ↥A) (I : ↥(irrSet L)) :
    (s16t3_irrSetAct h a I : Subgroup W) = (I : Subgroup W).map (a : MulAut W).toMonoidHom :=
  rfl

theorem s16t3_eq_of_iso_of_card_three (h : ThreeNat A L T)
    (h3 : Nat.card ↥(irrSet L) = 3) {J J' : Subgroup W}
    (hJ : J ∈ irrSet L) (hJ' : J' ∈ irrSet L) (hiso : XMod.Iso ↥L J' J) : J' = J := by
  have hcardQ : Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) // XMod.IsIrr ↥L Y} = 3 :=
    (s16t3_card_irrSet_eq_quot h.quasi).symm.trans h3
  exact s16t3_eq_of_tilde_eq h.quasi hJ hJ'
    (s16t3_eq_of_iso_of_card_quot_three h.elem h.quasi h.comm h.sum hcardQ
      (s16t3_isIrr_tilde_of_mem_irrSet h.quasi hJ) (s16t3_isIrr_tilde_of_mem_irrSet h.quasi hJ')
      (s16t3_tilde_iso_of_iso h.quasi hJ hJ' hiso))

theorem ThreeNat.three_dvd_card_outer (h : ThreeNat A L T) (h3 : Nat.card ↥(irrSet L) = 3) :
    3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) := by
  classical
  let φ : ↥A →* Equiv.Perm ↥(irrSet L) := s16t3_irrSetAct h
  let A₀ : Subgroup ↥A := φ.ker
  let P : Subgroup (Equiv.Perm ↥(irrSet L)) := φ.range
  have hmem_A0_iff : ∀ a : ↥A, a ∈ A₀ ↔
      ∀ J ∈ irrSet L, J.map (a : MulAut W).toMonoidHom = J := by
    intro a
    constructor
    · intro ha J hJ
      have h2 := congrArg (fun σ : Equiv.Perm ↥(irrSet L) =>
        (σ ⟨J, hJ⟩ : Subgroup W)) (show φ a = 1 from ha)
      simpa [φ, s16t3_irrSetAct_apply] using h2
    · intro ha
      show φ a = 1
      apply Equiv.ext
      intro J
      apply Subtype.ext
      show (φ a J : Subgroup W) = ((1 : Equiv.Perm ↥(irrSet L)) J : Subgroup W)
      change (s16t3_irrSetAct h a J : Subgroup W) = (J : Subgroup W)
      rw [s16t3_irrSetAct_apply]
      exact ha J J.2
  have hdvd : 3 ∣ Nat.card (↥A ⧸ A₀) := by
    have hquot : Nat.card (↥A ⧸ A₀) = Nat.card ↥P :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [hquot]
    letI : MulAction ↥P ↥(irrSet L) :=
      { smul := fun p x => (p : Equiv.Perm ↥(irrSet L)) x
        one_smul := fun _ => rfl
        mul_smul := fun p q x => by
          show (((p * q : ↥P) : Equiv.Perm ↥(irrSet L)) x) =
            ((p : Equiv.Perm ↥(irrSet L)) ((q : Equiv.Perm ↥(irrSet L)) x))
          rw [Subgroup.coe_mul]
          rfl }
    have hpre : MulAction.IsPretransitive ↥P ↥(irrSet L) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨g, hg, hgI⟩ := h.trans x.1 x.2 y.1 y.2
      have hgA : g ∈ A := (Subgroup.mem_inf.mp hg).1
      have hgP : φ ⟨g, hgA⟩ ∈ P := MonoidHom.mem_range.mpr ⟨⟨g, hgA⟩, rfl⟩
      refine ⟨⟨φ ⟨g, hgA⟩, hgP⟩, ?_⟩
      change ((φ ⟨g, hgA⟩) x) = y
      apply Subtype.ext
      show ((s16t3_irrSetAct h ⟨g, hgA⟩ x : ↥(irrSet L)) : Subgroup W) = (y : Subgroup W)
      rw [s16t3_irrSetAct_apply]
      exact hgI.symm
    obtain ⟨I, hI, -⟩ := h.exists_natural_irr
    have hd : Nat.card ↥(irrSet L) ∣ Nat.card ↥P := by
      haveI : Nonempty ↥(irrSet L) := ⟨⟨I, hI⟩⟩
      obtain ⟨x⟩ := ‹Nonempty ↥(irrSet L)›
      rw [← MulAction.index_stabilizer_of_transitive (G := ↥P) x]
      exact (MulAction.stabilizer ↥P x).index_dvd_card
    rwa [h3] at hd
  have hL_A0 : ∀ l (hl : l ∈ L), (⟨l, h.le hl⟩ : ↥A) ∈ A₀ := by
    intro l hl
    refine (hmem_A0_iff ⟨l, h.le hl⟩).mpr fun J hJ => ?_
    have hstab := stableUnder_of_mem_irrSet hJ
    ext u
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hstab l hl v hv
    · intro hu
      exact ⟨l⁻¹ u, hstab l⁻¹ (L.inv_mem hl) u hu, by simp⟩
  have hC_A0 : ∀ a (ha : a ∈ A), (∀ l ∈ L, a * l = l * a) →
      (⟨a, ha⟩ : ↥A) ∈ A₀ := by
    intro a ha hc
    refine (hmem_A0_iff ⟨a, ha⟩).mpr fun J hJ => ?_
    have hJ' : J.map a.toMonoidHom ∈ irrSet L :=
      map_mem_irrSet (fun x hx => conj_mem_of_mem_normalizer (h.normal ha) hx)
        (fun x hx => inv_conj_mem_of_mem_normalizer (h.normal ha) hx) hJ
    have hV : XMod.IsInv ↥L J :=
      fun l u hu => stableUnder_of_mem_irrSet hJ (l : MulAut W) l.2 u hu
    have hiso : XMod.Iso ↥L (J.map a.toMonoidHom) J :=
      CFSG.Quasithin.SmithD391.iso_smul_of_comm (Λ := L) hV hc
    exact s16t3_eq_of_iso_of_card_three h h3 hJ hJ' hiso
  let c : ↥A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion h.normal)
  let ψ : ↥A →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp c
  have hker_le : ψ.ker ≤ A₀ := by
    intro a ha
    have haψ : ψ a = 1 := MonoidHom.mem_ker.mp ha
    have hinner : c a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
      (QuotientGroup.eq_one_iff (c a)).mp haψ
    obtain ⟨l, hl⟩ := hinner
    have hconj : ∀ x ∈ L, (a : MulAut W) * x * (a : MulAut W)⁻¹ =
        (l : MulAut W) * x * (l : MulAut W)⁻¹ := by
      intro x hx
      have h1 := congrArg Subtype.val
        (congrArg (fun f : MulAut ↥L => f ⟨x, hx⟩) hl)
      rw [MulAut.conj_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [show (↑((c a) ⟨x, hx⟩) : MulAut W) =
          (a : MulAut W) * x * (a : MulAut W)⁻¹ from
        Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨a, h.normal a.2⟩ ⟨x, hx⟩] at h1
      exact h1.symm
    have hkc : ∀ x ∈ L, ((l : MulAut W)⁻¹ * (a : MulAut W)) * x =
        x * ((l : MulAut W)⁻¹ * (a : MulAut W)) := by
      intro x hx
      have h := hconj x hx
      calc ((l : MulAut W)⁻¹ * (a : MulAut W)) * x
          = (l : MulAut W)⁻¹ * ((a : MulAut W) * x) := by group
        _ = (l : MulAut W)⁻¹ * (((l : MulAut W) * x * (l : MulAut W)⁻¹) *
              (a : MulAut W)) := by rw [← h]; group
        _ = x * ((l : MulAut W)⁻¹ * (a : MulAut W)) := by group
    have hkA : ((l : MulAut W)⁻¹ * (a : MulAut W)) ∈ A :=
      A.mul_mem (A.inv_mem (h.le l.2)) a.2
    have hk : ∀ J ∈ irrSet L, J.map ((l : MulAut W)⁻¹ * (a : MulAut W)).toMonoidHom = J :=
      fun J hJ => (hmem_A0_iff ⟨_, hkA⟩).mp (hC_A0 _ hkA hkc) J hJ
    have hlJ : ∀ J ∈ irrSet L, J.map (l : MulAut W).toMonoidHom = J :=
      fun J hJ => (hmem_A0_iff ⟨(l : MulAut W), h.le l.2⟩).mp
        (hL_A0 (l : MulAut W) l.2) J hJ
    refine (hmem_A0_iff a).mpr fun J hJ => ?_
    have hae : (a : MulAut W) =
        (l : MulAut W) * ((l : MulAut W)⁻¹ * (a : MulAut W)) := by group
    have hcomp : (a : MulAut W).toMonoidHom =
        ((l : MulAut W).toMonoidHom).comp
          (((l : MulAut W)⁻¹ * (a : MulAut W)).toMonoidHom) := by
      ext u
      exact congrArg (fun f : MulAut W => f u) hae
    rw [hcomp, ← Subgroup.map_map, hk J hJ, hlJ J hJ]
  have hdvd2 : Nat.card (↥A ⧸ A₀) ∣ Nat.card (↥A ⧸ ψ.ker) :=
    Subgroup.index_dvd_of_le hker_le
  have hdvd3 : Nat.card (↥A ⧸ ψ.ker) ∣
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) :=
    Subgroup.card_dvd_of_injective (QuotientGroup.kerLift ψ)
      (QuotientGroup.kerLift_injective ψ)
  exact dvd_trans (dvd_trans hdvd hdvd2) hdvd3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
