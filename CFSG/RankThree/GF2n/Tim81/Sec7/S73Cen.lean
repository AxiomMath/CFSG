module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Aut
import CFSG.RankThree.GF2n.Tim81.RootHypConj
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Delta
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem EpsIn.mem_normalizer_conj_of_forall_mk_eq (hE : EpsIn M V h) {t : G}
    (htY : t ∈ Subgroup.normalizer (yOf h : Set G))
    (hσ : ∀ (y : G) (hy : y ∈ yOf h) (hty : t * y * t⁻¹ ∈ yOf h),
      (QuotientGroup.mk (⟨t * y * t⁻¹, hty⟩ : ↥(yOf h)) : YBar h) =
        QuotientGroup.mk ⟨y, hy⟩)
    {x : G} (hx : x ∈ yOf h) : t ∈ Subgroup.normalizer (conjSubgroup x V : Set G) := by
  have hle : conjSubgroup t (conjSubgroup x V) ≤ conjSubgroup x V := by
    rintro _ ⟨w, hw, rfl⟩
    have hwY : w ∈ yOf h := hE.conjSubgroup_le_yOf hx hw
    have htw : t * w * t⁻¹ ∈ yOf h := (Subgroup.mem_normalizer_iff.mp htY w).mp hwY
    have heq := hσ w hwY htw
    rw [QuotientGroup.eq] at heq
    have hO : (t * w * t⁻¹)⁻¹ * w ∈ inSubgroup (pPrimeCore 2) (yOf h) := ⟨_, heq, rfl⟩
    have h1 : w * ((t * w * t⁻¹)⁻¹ * w)⁻¹ ∈
        conjSubgroup x V ⊔ inSubgroup (pPrimeCore 2) (yOf h) :=
      Subgroup.mul_mem_sup hw (Subgroup.inv_mem _ hO)
    have hmem : t * w * t⁻¹ ∈
        conjSubgroup x V ⊔ inSubgroup (pPrimeCore 2) (yOf h) := by
      rwa [show w * ((t * w * t⁻¹)⁻¹ * w)⁻¹ = t * w * t⁻¹ by group] at h1
    have hw2 : w ^ 2 = 1 :=
      (CFSG.CGT.Timmesfeld75.isElemAbelian_conjSubgroup hE.root.elem x).2 w hw
    have hsq : t * w * t⁻¹ * (t * w * t⁻¹) = 1 := by
      calc t * w * t⁻¹ * (t * w * t⁻¹) = t * (w * w) * t⁻¹ := by group
        _ = 1 := by rw [← pow_two, hw2, mul_one, mul_inv_cancel]
    exact hE.mem_conj_of_mul_self_eq_one_of_mem_sup hx hmem hsq
  exact conjSubgroup_eq_self_iff.mp
    (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_conjSubgroup _ _).symm))

theorem EpsIn.conj_le_cenOf_of_inv (hE : EpsIn M V h) {P : Subgroup G}
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h P)
    {X₀ : Subgroup (YBar h)}
    (hX₀ : ∀ α : MulAut (YBar h), X₀.map α.toMonoidHom = X₀)
    (hC : Subgroup.centralizer (X₀ : Set (YBar h)) = ⊥) (hf : 1 ≤ f)
    (hn : 4 ≤ n)
    (hSU : IsSUImage X₀ (barRoots h V) f n hf (Nat.le_trans (Nat.le_add_left 2 2) hn))
    {c : G} (hcY : c ∈ yOf h) (hcR : c ∉ rOf M h) (hh : h * h ≠ 1) {a t : G}
    (htA : t ∈ conjSubgroup a V) (ht : t * h * t⁻¹ = h⁻¹)
    (htP : ∀ p ∈ P, t * p = p * t) (htc : t * c = c * t) {x : G} (hx : x ∈ yOf h) :
    conjSubgroup x V ≤ cenOf (conjSubgroup a V) := by
  have htY := mem_normalizer_yOf_of_conj_eq_inv ht
  obtain ⟨σ, hσ⟩ := exists_mulAut_yBar_conj htY
  have hfix : ∀ (y : G) (hy : y ∈ yOf h), t * y = y * t →
      σ (QuotientGroup.mk (⟨y, hy⟩ : ↥(yOf h))) = QuotientGroup.mk ⟨y, hy⟩ := by
    intro y hy hty
    have h1 : t * y * t⁻¹ = y := by rw [hty, mul_inv_cancel_right]
    have hty' : t * y * t⁻¹ ∈ yOf h := by rw [h1]; exact hy
    rw [hσ y hy hty']
    congr 1
    exact Subtype.ext h1
  have hσP : ∀ z ∈ barY h P, σ z = z := by
    rintro _ ⟨⟨p, hpY⟩, hpP, rfl⟩
    exact hfix p hpY (htP p (Subgroup.mem_subgroupOf.mp hpP))
  have hσ1 := hE.eq_one_of_forall_apply_eq hP hX₀ hC hf hn hSU hcY hcR hσP
    (hfix c hcY htc)
  have hσ' : ∀ (y : G) (hy : y ∈ yOf h) (hty : t * y * t⁻¹ ∈ yOf h),
      (QuotientGroup.mk (⟨t * y * t⁻¹, hty⟩ : ↥(yOf h)) : YBar h) =
        QuotientGroup.mk ⟨y, hy⟩ := by
    intro y hy hty
    rw [← hσ y hy hty, hσ1, MulAut.one_apply]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hh
    rw [one_mul, inv_one, mul_one] at ht
    calc h * h = h * h⁻¹ := by rw [← ht]
      _ = 1 := mul_inv_cancel h
  exact hE.root.conj_le_centralizer_of_mem_normalizer htA ht1
    (hE.mem_normalizer_conj_of_forall_mk_eq htY hσ' hx)

theorem EpsIn.y0Of_le_cenOf (hE : EpsIn M V h) (hD : L2Datum M V A B h)
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h (p0Of M V (A ⊔ B)))
    {X₀ : Subgroup (YBar h)}
    (hX₀ : ∀ α : MulAut (YBar h), X₀.map α.toMonoidHom = X₀)
    (hC : Subgroup.centralizer (X₀ : Set (YBar h)) = ⊥) (hf : 1 ≤ f)
    (hn : 4 ≤ n)
    (hSU : IsSUImage X₀ (barRoots h V) f n hf (Nat.le_trans (Nat.le_add_left 2 2) hn))
    {c : G} (hcX : c ∈ cenOf (A ⊔ B)) (hcM : c ∉ M) :
    y0Of V (Subgroup.zpowers h) ≤ cenOf (A ⊔ B) := by
  have hcY := hD.cenOf_le_yOf hcX
  have hcR : c ∉ rOf M h := fun hc => hcM hc.1
  have hh := hD.mul_self_ne_one hE.root
  have key : ∀ D ∈ sigmaSet M V, D ≤ A ⊔ B → (∃ t ∈ D, t * h * t⁻¹ = h⁻¹) →
      ∀ x ∈ yOf h, conjSubgroup x V ≤ cenOf D := by
    rintro D ⟨a, rfl, -⟩ hDX ⟨t, htD, ht⟩ x hx
    have hcen : ∀ z ∈ cenOf (A ⊔ B), t * z = z * t := fun z hz =>
      Subgroup.mem_centralizer_iff.mp hz t (hDX htD)
    exact hE.conj_le_cenOf_of_inv hP hX₀ hC hf hn hSU hcY hcR hh htD ht
      (fun p hp => hcen p hp.2) (hcen c hcX) hx
  unfold y0Of
  refine iSup₂_le fun x hx => ?_
  change conjSubgroup x V ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)
  rw [CFSG.centralizer_sup_eq A B]
  exact le_inf (key A hD.memA le_sup_left hD.exists_mem_conj_eq_inv.1 x hx)
    (key B hD.memB le_sup_right hD.exists_mem_conj_eq_inv.2 x hx)

end CFSG.RankThree.GF2n.Tim81
