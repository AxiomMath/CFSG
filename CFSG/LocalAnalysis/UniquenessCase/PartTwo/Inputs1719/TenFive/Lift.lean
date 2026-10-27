module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.LiftGood
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.SpecialRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.OrbitRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invert
import CFSG.Quasithin.Background.E6TwentyTwoA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem sixteen_le_rk_commSub_of_good (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : MulAut W} (hx : orderOf x = p)
    (h : IsSpecialGood p x ∨ IsOrbitGood p x) : 16 ≤ rk ↥(commSub ⊤ (zpowers x)) := by
  rcases h with ⟨H, e, N, hxH, hH, heN, h3⟩ | ⟨U, k, hxU, hU, hk, hcount⟩
  · exact sixteen_le_rk_commSub_of_isSpecialType hW hp hp2 hH heN h3 hxH hx
  · exact hk.trans (le_rk_commSub_of_conj_hyperplanes hW hp hp2 hU hxU hx hcount)

private noncomputable def conjAction {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    [hN : (L.subgroupOf Y).Normal] : ↥Y →* MulAut ↥L :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe hLY)).toMonoidHom.comp
    (MulAut.conjNormal (G := ↥Y) (H := L.subgroupOf Y))

omit [Finite W] in
private theorem conjAction_apply {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    [hN : (L.subgroupOf Y).Normal] (y : ↥Y) (l : ↥L) :
    (((conjAction hLY y) l : ↥L) : MulAut W) =
      (y : MulAut W) * (l : MulAut W) * (y : MulAut W)⁻¹ := by
  have he : ((Subgroup.subgroupOfEquivOfLe hLY).symm l : ↥Y) =
      ⟨(l : MulAut W), hLY l.2⟩ := by
    apply Subtype.ext
    have h := Subgroup.subgroupOfEquivOfLe_apply_coe hLY
      ((Subgroup.subgroupOfEquivOfLe hLY).symm l)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  rw [conjAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.trans_apply, Subgroup.subgroupOfEquivOfLe_apply_coe,
    MulAut.conjNormal_apply, he]
  simp

private theorem mulAut_mul_inv_mul_eq {G : Type*} [Group G] (σ : MulAut G) {a b : G}
    (hb : σ b * b⁻¹ ∈ Subgroup.center G) :
    σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹) := by
  have hc : ∀ g : G, g * (σ b * b⁻¹) = (σ b * b⁻¹) * g :=
    fun g => Subgroup.mem_center_iff.mp hb g
  rw [map_mul, mul_inv_rev]
  calc (σ a * σ b) * (b⁻¹ * a⁻¹)
      = σ a * (σ b * b⁻¹) * a⁻¹ := by group
    _ = σ a * ((σ b * b⁻¹) * a⁻¹) := by rw [mul_assoc]
    _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [← hc a⁻¹]
    _ = (σ a * a⁻¹) * (σ b * b⁻¹) := by rw [mul_assoc]

theorem exists_quotAut_of_involution {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hLq : CFSG.IsQuasisimple ↥L)
    (hO2 : O2Trivial L) {t : MulAut W} (htY : t ∈ Y) (ht : orderOf t = 2) :
    ∃ (σ : MulAut ↥L) (σ' : MulAut (↥L ⧸ center ↥L)),
      (∀ l : ↥L, ((σ l : ↥L) : MulAut W) = t * l * t⁻¹) ∧
      (∀ l : ↥L, σ' (l : ↥L ⧸ center ↥L) = ((σ l : ↥L) : ↥L ⧸ center ↥L)) ∧
      orderOf σ' = 2 := by
  classical
  have hN : (L.subgroupOf Y).Normal := hLn
  let σ : MulAut ↥L := conjAction hLY ⟨t, htY⟩
  have hσ : ∀ l : ↥L, ((σ l : ↥L) : MulAut W) = t * l * t⁻¹ := by
    intro l
    simpa [σ] using conjAction_apply hLY ⟨t, htY⟩ l
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hσ2 : σ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro l
    rw [pow_two, MulAut.mul_apply]
    change σ (σ l) = l
    apply Subtype.ext
    have h1 := hσ l
    have h2 := hσ (σ l)
    rw [h2, h1]
    have ht2' : t * t = 1 := by simpa [pow_two] using ht2
    have htinv2 : t⁻¹ * t⁻¹ = 1 := by
      rw [← mul_inv_rev, ht2', inv_one]
    calc t * (t * (l : MulAut W) * t⁻¹) * t⁻¹
        = (t * t) * (l : MulAut W) * (t⁻¹ * t⁻¹) := by group
      _ = (l : MulAut W) := by rw [ht2', htinv2]; group
  have hcenter : (Subgroup.center ↥L).map σ.toMonoidHom = Subgroup.center ↥L :=
    Subgroup.map_center_eq σ
  let σ' : MulAut (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) σ hcenter
  have hσ' : ∀ l : ↥L, σ' (l : ↥L ⧸ Subgroup.center ↥L) =
      ((σ l : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by
    intro l
    exact QuotientGroup.congr_mk (Subgroup.center ↥L) (Subgroup.center ↥L) σ hcenter l
  have hσ'2 : σ' ^ 2 = 1 := by
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro l
    have hss : σ (σ l) = l := by
      have h := congrArg (fun f : MulAut ↥L => f l) hσ2
      simpa [pow_two, MulAut.mul_apply] using h
    rw [pow_two, MulAut.mul_apply, hσ' l, hσ' (σ l), hss]
    rfl
  have hσ'ne : σ' ≠ 1 := by
    intro hσ'1
    have hmem : ∀ l : ↥L, σ l * l⁻¹ ∈ Subgroup.center ↥L := by
      intro l
      have h1 : ((σ l : ↥L) : ↥L ⧸ Subgroup.center ↥L) =
          (l : ↥L ⧸ Subgroup.center ↥L) := by
        calc ((σ l : ↥L) : ↥L ⧸ Subgroup.center ↥L) =
              σ' (l : ↥L ⧸ Subgroup.center ↥L) := (hσ' l).symm
          _ = (l : ↥L ⧸ Subgroup.center ↥L) := by rw [hσ'1]; rfl
      simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp h1
    let f : ↥L →* Subgroup.center ↥L :=
      { toFun := fun l => ⟨σ l * l⁻¹, hmem l⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          exact mulAut_mul_inv_mul_eq σ (hmem b) }
    have hf1 : ∀ l : ↥L, f l = 1 := by
      intro l
      have htop : (⊤ : Subgroup ↥L) ≤ f.ker := by
        rw [← Group.isPerfect_def.mp hLq.1]
        exact Abelianization.commutator_subset_ker f
      exact MonoidHom.mem_ker.mp (htop (Subgroup.mem_top l))
    have hσ1 : σ = 1 := by
      apply MulEquiv.ext
      intro l
      have h := congrArg (fun x : Subgroup.center ↥L => (x : ↥L)) (hf1 l)
      have h2 : σ l * l⁻¹ = 1 := by simpa [f] using h
      simpa using (mul_inv_eq_one.mp h2)
    have hcent : t ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := hσ ⟨l, hl⟩
      rw [hσ1] at h
      have hl' : (l : MulAut W) = t * l * t⁻¹ := by simpa using h
      calc l * t = (t * l * t⁻¹) * t := by conv_lhs => rw [hl']
        _ = t * l := by group
    have htL : t ∈ L :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.mem_of_mem_centralizer_of_fstar_eq
        hLY hF htY hcent
    let P : Subgroup (MulAut W) := Subgroup.zpowers t
    have hPL : P ≤ L := Subgroup.zpowers_le.mpr htL
    have hPcent : P.subgroupOf L ≤ Subgroup.center ↥L := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1
        (Subgroup.zpowers_le.mpr hcent (Subgroup.mem_subgroupOf.mp hx)) (z : MulAut W) z.2
    have hPnormal : (P.subgroupOf L).Normal := Subgroup.normal_of_le_center hPcent
    have hP2 : IsPGroup 2 P := by
      apply IsPGroup.of_card (n := 1)
      show Nat.card ↥(Subgroup.zpowers t) = 2 ^ 1
      rw [Nat.card_zpowers, ht]
      norm_num
    have hPbot : P = ⊥ := hO2 P hPL hPnormal hP2
    have htbot : t ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hPbot]
      exact Subgroup.mem_zpowers t
    have ht1 : t = 1 := by simpa using htbot
    rw [ht1] at ht
    simp at ht
  exact ⟨σ, σ', hσ, hσ', orderOf_eq_prime hσ'2 hσ'ne⟩

theorem eight_le_mParam_of_involInvertsGood (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hF : Fstar Y = L) (hLq : CFSG.IsQuasisimple ↥L) (hO2 : O2Trivial L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZp : Nat.Coprime (Nat.card (center ↥L)) p)
    (hI : InvolInvertsGood p (↥L ⧸ center ↥L)) : 8 ≤ E3.mParam Y := by
  have hY : ∃ t ∈ Y, orderOf t = 2 := by
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
      ((E6.two_dvd_card_of_isQuasisimple hLq).trans (Subgroup.card_dvd_of_le hLY))
    exact ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht⟩
  refine eight_le_mParam_of_forall_inverts hW hp hp2 hY ?_
  intro t htY ht
  obtain ⟨σ, σ', hσ, hσ', hord⟩ := exists_quotAut_of_involution hLY hLn hF hLq hO2 htY ht
  obtain ⟨y, hy, hσy, hgood⟩ := hI σ' hord
  obtain ⟨x, hx, hσx, hxgood⟩ := exists_lift_good hp hZp σ σ' hσ' hy hσy hgood
  have hxW : orderOf (x : MulAut W) = p := (Subgroup.orderOf_coe x).trans hx
  refine ⟨(x : MulAut W), hxW, ?_, ?_⟩
  · rw [← hσ x, hσx]
    rfl
  · exact sixteen_le_rk_commSub_of_good hW hp hp2 hxW
      (hxgood.imp (IsSpecialGood.map L.subtype_injective) (IsOrbitGood.map L.subtype_injective))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
