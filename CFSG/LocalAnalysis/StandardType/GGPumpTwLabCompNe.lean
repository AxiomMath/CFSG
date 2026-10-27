module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabDefs
import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l04fHL1B_eq_top_of_central
    {G R : Type} [Group G] [Finite G] [Group R] [Finite R]
    (hperf : commutator G = ⊤) (ψ : G →* R)
    (hk : ψ.ker ≤ Subgroup.center G) (J : Subgroup G)
    (hcard : Nat.card R ≤ Nat.card (↥J ⧸ Subgroup.center ↥J)) : J = ⊤ := by
  let f : ↥J →* R := ψ.comp J.subtype
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : ψ (x : G) = 1 := MonoidHom.mem_ker.mp hx
    have hxZ : (x : G) ∈ Subgroup.center G := hk (MonoidHom.mem_ker.mpr hx1)
    exact Subgroup.mem_center_iff.mp hxZ (y : G)
  have hquot_le : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card f.range := by
    have h1 : Nat.card ↥J = Nat.card (↥J ⧸ Subgroup.center ↥J) *
        Nat.card (Subgroup.center ↥J) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
    have h2 : Nat.card f.ker * Nat.card f.range = Nat.card ↥J :=
      Subgroup.card_ker_mul_card_range f
    have hkcard : Nat.card f.ker ≤ Nat.card (Subgroup.center ↥J) :=
      Subgroup.card_le_of_le hfker
    have hpos : 0 < Nat.card (Subgroup.center ↥J) := Nat.card_pos
    have hmain : Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J) ≤
        Nat.card f.range * Nat.card (Subgroup.center ↥J) := by
      calc Nat.card (↥J ⧸ Subgroup.center ↥J) * Nat.card (Subgroup.center ↥J)
          = Nat.card ↥J := h1.symm
        _ = Nat.card f.ker * Nat.card f.range := h2.symm
        _ ≤ Nat.card (Subgroup.center ↥J) * Nat.card f.range :=
              Nat.mul_le_mul_right _ hkcard
        _ = Nat.card f.range * Nat.card (Subgroup.center ↥J) := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hmain hpos
  have hfrange : f.range = ⊤ := Subgroup.eq_top_of_le_card f.range (hcard.trans hquot_le)
  have hfrange_eq : f.range = J.map ψ := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmap : J.map ψ = ⊤ := by
    rw [← hfrange_eq, hfrange]
  have hJN : J ⊔ ψ.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : ψ g ∈ J.map ψ := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨j, hj, hjg⟩ := Subgroup.mem_map.mp hg
    have hker : j⁻¹ * g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjg, inv_mul_cancel]
    have hmul := Subgroup.mul_mem_sup hj hker
    rwa [mul_inv_cancel_left] at hmul
  have hJnorm : J.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    rw [eq_top_iff]
    intro g _
    have hle : J ⊔ ψ.ker ≤ Subgroup.normalizer (J : Set G) :=
      sup_le Subgroup.le_normalizer (hk.trans (Subgroup.center_le_normalizer (J : Set G)))
    exact hle (by rw [hJN]; exact Subgroup.mem_top g)
  have hker_comm : IsMulCommutative ↥ψ.ker := by
    refine IsMulCommutative.of_comm fun x y => ?_
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hk x.2) (y : G)).symm
  have : J.Normal := hJnorm
  have hcomm : commutator G ≤ J :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := J) (H := ψ.ker) hJN hker_comm
  rw [hperf] at hcomm
  exact top_le_iff.mp hcomm

theorem ggPumpTw_component_label_ne
    {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {lab : LargeEvenLabel} (hR : GGHasLabel lab R)
    {e : MulAut L'} (he : e ≠ 1) {J : Subgroup L'}
    (hJ : CFSG.Assembly.IsComponentOf J (ggFixSub e)) :
    ¬ GGHasLabel lab (J ⧸ Subgroup.center J) := by
  intro hJlab
  obtain ⟨eiso⟩ := nonempty_mulEquiv_of_ggHasLabel hJlab hR
  have : Finite R := Finite.of_surjective ψ hψ
  have hcard : Nat.card R ≤ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    le_of_eq (Nat.card_congr eiso.toEquiv).symm
  have hJtop : J = ⊤ := l04fHL1B_eq_top_of_central hperf ψ hker J hcard
  have hfix : ∀ x : L', e x = x := by
    intro x
    have hx : x ∈ J := by rw [hJtop]; exact Subgroup.mem_top x
    exact (mem_ggFixSub).mp (hJ.1 hx)
  exact he (MulEquiv.ext hfix)

theorem ggPumpTwLabAt_of_component_exclusion
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : ∀ (R : Type) [Group R] [Finite R], Subgroup.center R = ⊥ →
      ∀ φ : MulAut R, CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind R lab φ →
        φ ^ 3 = 1 → ∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub φ) →
          ∀ f : ℕ, ¬ GGPumpTwJLab f (↥J ⧸ Subgroup.center ↥J)) :
    GGPumpTwLabAt lab := by
  refine LargeEvenLabelAll.mono ?_ (TCJ.ggTCJ_datum_marking hlab)
  intro R _ I F hP L' _ _ ψ hψ hker _hperf e J f _he1 he3 hφ hJ hJlab
  obtain ⟨φ, hφI, hφind⟩ := hφ
  obtain ⟨hJb, ⟨eJ⟩⟩ := TCJ.ggTCJ_descent ψ hψ hker e φ hφind J hJ
  have hna : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨-, a, b, hab⟩ := ggQuasisimple_centerQuot hJb.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨(a : R), (b : R), fun h => hab
      (congrArg (QuotientGroup.mk : ↥(J.map ψ) → ↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ))
        (Subtype.ext h))⟩
  have : Finite R := hP.1
  have : IsSimpleGroup R := (hP.2 hna).1
  have hcen : Subgroup.center R = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hφ3 : φ ^ 3 = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have he : e (e (e l)) = l := by
      simpa [pow_succ, MulAut.mul_apply] using congrArg (fun a : MulAut L' => a l) he3
    change φ (φ (φ (ψ l))) = ψ l
    rw [hφind l, hφind (e l), hφind (e (e l)), he]
  have hJlab' : GGPumpTwJLab f (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) := by
    rcases hJlab with ⟨h3, hU⟩ | ⟨h3, hA⟩ | hD
    · exact Or.inl ⟨h3, ggHasLabel_of_mulEquiv eJ hU⟩
    · exact Or.inr (Or.inl ⟨h3, ggHasLabel_of_mulEquiv eJ hA⟩)
    · exact Or.inr (Or.inr (ggHasLabel_of_mulEquiv eJ hD))
  exact False.elim (h R hcen φ ((hP.2 hna).2 φ hφI) hφ3 (J.map ψ) hJb f hJlab')

end CFSG.StandardType

end
