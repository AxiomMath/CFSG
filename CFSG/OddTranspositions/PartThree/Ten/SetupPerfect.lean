module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
public import CFSG.OddTranspositions.PartThree.Ten.CentralSymSplit
import CFSG.OddTranspositions.PartThree.Ten.SetupQ
import CFSG.OddTranspositions.HalphaQuotient
import CFSG.Timmesfeld.Bridge.Asc72Basic
import Mathlib.GroupTheory.Commutator.Finite
import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ CFSG.BenderSuzuki SemidirectProduct
open scoped commutatorElement

theorem commutator_l2WreathBase {f : ℕ} (hf : 2 ≤ f) (n : ℕ) :
    ⁅l2WreathBase f n, l2WreathBase f n⁆ = l2WreathBase f n := by
  have hP := (Group.isPerfect_def (G := PSL2Model f)).mp (SetupQ.isPerfect_psl2Model hf)
  have hpi : ⁅(⊤ : Subgroup (Fin n → PSL2Model f)), (⊤ : Subgroup (Fin n → PSL2Model f))⁆ = ⊤ := by
    have h := Subgroup.commutator_pi_pi_of_finite
      (fun _ : Fin n => (⊤ : Subgroup (PSL2Model f)))
      (fun _ : Fin n => (⊤ : Subgroup (PSL2Model f)))
    rw [Subgroup.pi_top] at h
    rw [h]
    have h' : (fun _ : Fin n => ⁅(⊤ : Subgroup (PSL2Model f)), (⊤ : Subgroup (PSL2Model f))⁆) =
        fun _ : Fin n => (⊤ : Subgroup (PSL2Model f)) := by
      funext
      rw [← commutator_def, hP]
    rw [h', Subgroup.pi_top]
  rw [l2WreathBase, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hpi]

variable {H : Type*} [Group H] [Finite H] {f n : ℕ}

omit [Finite H] in
theorem comap_base_eq_ker (q : H →* L2Wreath f n) :
    (l2WreathBase f n).comap q = ((SemidirectProduct.rightHom).comp q).ker := by
  rw [l2WreathBase, range_inl_eq_ker_rightHom, MonoidHom.comap_ker]

omit [Finite H] in
theorem exists_mem_commutator_mul_central (hf : 2 ≤ f) (q : H →* L2Wreath f n)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center H) {l : H}
    (hl : l ∈ (l2WreathBase f n).comap q) :
    ∃ m ∈ ⁅(l2WreathBase f n).comap q, (l2WreathBase f n).comap q⁆,
      m⁻¹ * l ∈ Subgroup.center H := by
  set L := (l2WreathBase f n).comap q
  have hmap : ⁅L, L⁆.map q = l2WreathBase f n := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hq,
      commutator_l2WreathBase hf]
  have hql : q l ∈ ⁅L, L⁆.map q := by rw [hmap]; exact hl
  obtain ⟨m, hm, hml⟩ := hql
  refine ⟨m, hm, hker ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hml, inv_mul_cancel]

omit [Finite H] in
theorem isOddTranspClass_map {X : Type*} [Group X] (φ : H →* X) (hφ : Function.Surjective φ)
    {C : Set H} (hC : IsOddTranspClass C) (hne : ∀ c ∈ C, φ c ≠ 1) :
    IsOddTranspClass (φ '' C) := by
  obtain ⟨⟨c₀, rfl⟩, hodd, hgen⟩ := hC
  refine ⟨⟨φ c₀, ?_⟩, hodd.image φ hne, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact MonoidHom.map_isConj φ hx
    · intro hy
      obtain ⟨b, rfl⟩ := isConj_iff.mp hy
      obtain ⟨a, rfl⟩ := hφ b
      refine ⟨a * c₀ * a⁻¹, isConj_iff.mpr ⟨a, rfl⟩, ?_⟩
      simp [map_mul, map_inv]
  · rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective φ hφ]

theorem commutator_comap_base_eq_of_three_le (hf : 2 ≤ f) (hn : 3 ≤ n) (q : H →* L2Wreath f n)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center H) {C : Set H}
    (hC : IsOddTranspClass C) :
    ⁅(l2WreathBase f n).comap q, (l2WreathBase f n).comap q⁆ = (l2WreathBase f n).comap q := by
  classical
  set L := (l2WreathBase f n).comap q with hLdef
  set ρ : H →* Equiv.Perm (Fin n) := (SemidirectProduct.rightHom).comp q with hρdef
  have hLρ : L = ρ.ker := comap_base_eq_ker q
  have hρ : Function.Surjective ρ := SemidirectProduct.rightHom_surjective.comp hq
  have : L.Normal := by rw [hLρ]; exact MonoidHom.normal_ker ρ
  set N := ⁅L, L⁆ with hNdef
  have hNL : N ≤ L := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  have hNρ : N ≤ ρ.ker := hLρ ▸ hNL
  set π : H ⧸ N →* Equiv.Perm (Fin n) := QuotientGroup.lift N ρ hNρ with hπdef
  have hπ : Function.Surjective π := by
    intro σ
    obtain ⟨h, rfl⟩ := hρ σ
    exact ⟨QuotientGroup.mk h, rfl⟩
  have hπker : π.ker ≤ Subgroup.center (H ⧸ N) := by
    rw [hπdef, QuotientGroup.ker_lift, ← hLρ]
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨m, hm, hmz⟩ := exists_mem_commutator_mul_central hf q hq hker hl
    have hm1 : (QuotientGroup.mk' N) m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    have heq : (QuotientGroup.mk' N) l = (QuotientGroup.mk' N) (m⁻¹ * l) := by
      rw [map_mul, map_inv, hm1, inv_one, one_mul]
    rw [heq]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N) ⟨_, hmz, rfl⟩
  have hne : ∀ c ∈ C, (QuotientGroup.mk' N) c ≠ 1 := by
    intro c hc h1
    have hcρ : ρ c = 1 := hNρ ((QuotientGroup.eq_one_iff c).mp h1)
    obtain ⟨⟨c₀, hc₀⟩, -, hgen⟩ := hC
    have hall : ∀ x ∈ C, ρ x = 1 := by
      intro x hx
      rw [hc₀] at hc hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp ((show IsConj c₀ c from hc).symm.trans hx)
      rw [map_mul, map_mul, map_inv, hcρ, mul_one, mul_inv_cancel]
    have htop : (⊤ : Subgroup H) ≤ ρ.ker := by
      rw [← hgen, Subgroup.closure_le]
      exact hall
    have hsw : Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ≠ 1 := by
      rw [Ne, Equiv.swap_eq_one_iff, Fin.mk.injEq]
      omega
    obtain ⟨h, hh⟩ := hρ (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)
    have hh1 := htop (Subgroup.mem_top h)
    rw [MonoidHom.mem_ker, hh] at hh1
    exact hsw hh1
  have hC' := isOddTranspClass_map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hC hne
  have hbot := ker_eq_bot_of_isOddTranspClass_of_three_le hn π hπ hπker hC'
  have hLN : L ≤ N := by
    rw [hπdef, QuotientGroup.ker_lift, ← hLρ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      at hbot
    exact hbot
  exact le_antisymm hNL hLN

theorem commutator_comap_base_eq (hf : 2 ≤ f) (hn : 5 ≤ n) (q : H →* L2Wreath f n)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center H) {C : Set H}
    (hC : IsOddTranspClass C) :
    ⁅(l2WreathBase f n).comap q, (l2WreathBase f n).comap q⁆ = (l2WreathBase f n).comap q :=
  commutator_comap_base_eq_of_three_le hf (by omega) q hq hker hC


theorem tenSetupPerfect_holds : TenSetupPerfect := by
  intro G _ _ D hC f n hT e
  set H := Halpha D hC.alpha
  set q : H →* L2Wreath f n := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
    with hqdef
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker ≤ Subgroup.center H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff x).mp (e.injective (hx.trans (map_one e).symm))
  have hCls : IsOddTranspClass (DstarH hC) :=
    ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩
  have h := commutator_comap_base_eq hT.two_le hT.five_le q hq hker hCls
  change ⁅((l2WreathBase f n).comap q).map H.subtype, ((l2WreathBase f n).comap q).map H.subtype⁆
    = ((l2WreathBase f n).comap q).map H.subtype
  rw [← Subgroup.map_commutator, h]

theorem tenSetupQ_holds : TenSetupQ :=
  tenSetupQ_of_perfect tenSetupPerfect_holds

end CFSG.OddTranspositions.PartThree

end
