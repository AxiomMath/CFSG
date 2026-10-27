module

public import CFSG.OddTranspositions.PartThree.Twelve.Six
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.OddTranspositions.PartThree.Nine.Setup

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
  CFSG.LocalAnalysis.WeakClosure81

theorem exists_spModel {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (h : IsSymplecticTransvection X m f s) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (ψ : X ≃* StatedSp k F),
      m = 2 * k ∧ Nat.card F = 2 ^ f ∧ ∀ x, x ∈ E ↔ ∃ v, v ≠ 0 ∧ ψ x = spTransvection v 1 := by
  classical
  obtain ⟨k, hmk, F, _, _, hF, e, hrank⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  let ψ₀ : X →* StatedSp k F := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hinj : Function.Injective ψ₀ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hsurj : Function.Surjective ψ₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ψ : X ≃* StatedSp k F := MulEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩
  have hψ : ∀ x, ψ x = e (QuotientGroup.mk x) := fun x => rfl
  obtain ⟨u, c, hu, hc, hψs⟩ := borel86_spn_eq_spTransvection hrank
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hc hr
  have hs1 : ψ s = spTransvection (r • u) 1 := by
    rw [hψ, hψs, spTransvection_smul_eq, mul_one, ← hr]
  have hu0 : r • u ≠ 0 := smul_ne_zero hr0 hu
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  refine ⟨k, F, inferInstance, inferInstance, ψ, hmk, hF, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨g, rfl⟩ := isConj_iff.mp ((hEs x).mp hx)
    refine ⟨spEnd (ψ g) (r • u), fun h0 => hu0 ?_, ?_⟩
    · rw [← spEnd_spEnd_inv_apply (ψ g)⁻¹ (r • u), inv_inv, h0, map_zero]
    · rw [map_mul, map_mul, map_inv, hs1, conj_spTransvection]
  · rintro ⟨v, hv, hψx⟩
    obtain ⟨g, hg⟩ := exists_spEnd_eq hu0 hv
    obtain ⟨g', rfl⟩ := ψ.surjective g
    refine (hEs x).mpr (isConj_iff.mpr ⟨g', ψ.injective ?_⟩)
    rw [map_mul, map_mul, map_inv, hs1, conj_spTransvection, hg, hψx]

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure SpChart (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) (k : ℕ) (F : Type) [Field F]
    where
  ρ : Halpha D hC.alpha →* StatedSp k F
  vec : G → (Fin k ⊕ Fin k → F)
  surjective : Function.Surjective ρ
  ker_eq : ρ.ker = CFSG.solvableRadical (Halpha D hC.alpha)
  vec_ne_zero : ∀ z ∈ commSet D hC.d, vec z ≠ 0
  map_eq : ∀ z (hz : z ∈ commSet D hC.d),
    ρ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ = spTransvection (vec z) 1
  exists_vec : ∀ v, v ≠ 0 → ∃ z ∈ commSet D hC.d, vec z = v
  injOn : Set.InjOn vec (commSet D hC.d)
  commute_iff : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
    (Commute z z' ↔ spForm k F (vec z) (vec z') = 0)

theorem exists_spChart (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ}
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s) :
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2),
      n = 2 * k ∧ Nat.card F = 2 ^ f ∧ Nonempty (SpChart hC hα k F) := by
  classical
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨k, F, _, _, ψ, hnk, hF, hE⟩ := exists_spModel (imageClass_isClass hC) hZ hs hSp
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  set R := CFSG.solvableRadical (Halpha D hC.alpha) with hRdef
  let ρ : Halpha D hC.alpha →* StatedSp k F := ψ.toMonoidHom.comp (QuotientGroup.mk' R)
  have hρ : ∀ h, ρ h = ψ (QuotientGroup.mk' R h) := fun h => rfl
  have hmem : ∀ z (hz : z ∈ commSet D hC.d),
      QuotientGroup.mk' R (⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ : Halpha D hC.alpha) ∈
        imageClass hC :=
    fun z hz => ⟨_, mem_DstarH_of_mem_commSet hC hα hz, rfl⟩
  let vec : G → (Fin k ⊕ Fin k → F) := fun z =>
    if hz : z ∈ commSet D hC.d then Classical.choose ((hE _).mp (hmem z hz)) else 0
  have hvec : ∀ z (hz : z ∈ commSet D hC.d), vec z ≠ 0 ∧
      ρ ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ = spTransvection (vec z) 1 := by
    intro z hz
    simp only [vec, dif_pos hz]
    exact Classical.choose_spec ((hE _).mp (hmem z hz))
  have hne := (subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs
    hSp).2
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
  refine ⟨k, F, inferInstance, inferInstance, inferInstance, hnk, hF,
    ⟨{ ρ := ρ, vec := vec, surjective := ψ.surjective.comp (QuotientGroup.mk'_surjective R),
       ker_eq := ?_, vec_ne_zero := fun z hz => (hvec z hz).1, map_eq := fun z hz => (hvec z hz).2,
       exists_vec := ?_, injOn := ?_, commute_iff := ?_ }⟩⟩
  · ext h
    rw [MonoidHom.mem_ker, hρ, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  · intro v hv
    obtain ⟨x, hx, hxv⟩ := (hE (ψ.symm (spTransvection v 1))).mpr
      ⟨v, hv, MulEquiv.apply_symm_apply _ _⟩
    have hxG : (x : G) ∈ commSet D hC.d := by
      rw [← Nine.DalphaStar_eq_commSet hC hα]
      exact (mem_DstarH_iff hC).mp hx
    refine ⟨x, hxG, ?_⟩
    have h1 : ρ ⟨x, mem_Halpha_of_mem_commSet hC hα hxG⟩ = spTransvection v 1 := by
      rw [hρ, show (⟨(x : G), mem_Halpha_of_mem_commSet hC hα hxG⟩ : Halpha D hC.alpha) = x
        from rfl, hxv, MulEquiv.apply_symm_apply]
    rw [(hvec x hxG).2] at h1
    exact eq_of_spTransvection_eq one_ne_zero hv h1
  · intro z hz z' hz' h
    have h1 := (hvec z hz).2
    rw [h, ← (hvec z' hz').2, hρ, hρ] at h1
    exact congrArg Subtype.val (hinj (mem_DstarH_of_mem_commSet hC hα hz)
      (mem_DstarH_of_mem_commSet hC hα hz') (ψ.injective h1))
  · intro z hz z' hz'
    rw [commute_iff_commute_mk hC hMZ hα hz hz']
    have hc : ∀ a b : Halpha D hC.alpha ⧸ R, Commute a b ↔ Commute (ψ a) (ψ b) :=
      fun a b => ⟨fun h => h.map ψ, fun h => ψ.injective (by rw [map_mul, map_mul]; exact h.eq)⟩
    rw [hc, ← hρ, ← hρ, (hvec z hz).2, (hvec z' hz').2,
      commute_spTransvection_iff one_ne_zero one_ne_zero]

omit [Finite G] in
theorem commute_d_of_mem_Halpha (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    (h : Halpha D hC.alpha) : Commute (h : G) hC.d := by
  have hle : Halpha D hC.alpha ≤ Subgroup.centralizer {hC.d} := by
    rw [Halpha, Subgroup.closure_le]
    intro z hz
    rw [Nine.DalphaStar_eq_commSet hC hα] at hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr hz.2.1.eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle h.2)

omit [Finite G] in
theorem SpChart.vec_conj {hC : HypothesisC D} {hα : hC.alpha = {hC.d}} {k : ℕ} {F : Type}
    [Field F] [CharP F 2] (c : SpChart hC hα k F) (h : Halpha D hC.alpha) {z : G}
    (hz : z ∈ commSet D hC.d) :
    (h : G) * z * (h : G)⁻¹ ∈ commSet D hC.d ∧
      c.vec ((h : G) * z * (h : G)⁻¹) = spEnd (c.ρ h) (c.vec z) := by
  have hcd := commute_d_of_mem_Halpha hC hα h
  have hmem : (h : G) * z * (h : G)⁻¹ ∈ commSet D hC.d := by
    refine ⟨hC.setup.conj_mem _ hz.1, ?_, fun he => hz.2.2 ?_⟩
    · have h1 : Commute ((h : G) * z * (h : G)⁻¹) ((h : G) * hC.d * (h : G)⁻¹) :=
        (hz.2.1.map (MulAut.conj (h : G)).toMonoidHom)
      rwa [hcd.eq, mul_inv_cancel_right] at h1
    · have h1 : z = (h : G)⁻¹ * hC.d * (h : G) := by rw [← he]; group
      rw [h1, mul_assoc, ← hcd.eq, inv_mul_cancel_left]
  refine ⟨hmem, ?_⟩
  have h1 : c.ρ ⟨(h : G) * z * (h : G)⁻¹, mem_Halpha_of_mem_commSet hC hα hmem⟩ =
      c.ρ (h * ⟨z, mem_Halpha_of_mem_commSet hC hα hz⟩ * h⁻¹) := rfl
  rw [map_mul, map_mul, map_inv, c.map_eq z hz, conj_spTransvection, c.map_eq _ hmem] at h1
  have hne : spEnd (c.ρ h) (c.vec z) ≠ 0 := fun h0 => c.vec_ne_zero z hz (by
    rw [← spEnd_spEnd_inv_apply (c.ρ h)⁻¹ (c.vec z), inv_inv, h0, map_zero])
  exact eq_of_spTransvection_eq one_ne_zero hne h1

end CFSG.OddTranspositions.PartThree
