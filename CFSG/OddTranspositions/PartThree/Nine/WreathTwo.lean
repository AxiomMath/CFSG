module

public import CFSG.OddTranspositions.PartThree.Nine.Statements
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.Timmesfeld.Bridge.Asc72WreathConn
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki Equiv SemidirectProduct

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem nonempty_quotientCenter_mulEquiv_of_wreath_two (hC : HypothesisC D) {f : ℕ}
    (hf : 2 ≤ f) (Ψ : G ≃* L2Wreath f 2) (hΨu : Ψ hC.d = inr (swap 0 1))
    (hΨD : ∀ x, x ∈ D ↔ IsConj (inr (swap 0 1) : L2Wreath f 2) (Ψ x)) :
    Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model f) := by
  classical
  have hS := hC.setup
  have hτu : Ψ.symm (inr (swap 0 1)) = hC.d := by rw [← hΨu, MulEquiv.symm_apply_apply]
  have hleft : ∀ g ∈ Subgroup.centralizer ({hC.d} : Set G), ∀ p : Fin 2,
      (Ψ g).left p = (Ψ g).left 0 := by
    intro g hg p
    have h1 : Commute (Ψ g) (inr (swap 0 1)) := by
      have h : Commute g hC.d := Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [← hΨu]
      exact h.map Ψ
    have h2 := congrArg (fun w : L2Wreath f 2 => w.left 1) h1.eq
    simp only [mul_left, left_inr, map_one, one_mul, mul_one, right_inr,
      WreathConn.permAct_apply, swap_inv, swap_apply_right] at h2
    fin_cases p
    · rfl
    · exact h2
  let ρ : Subgroup.centralizer ({hC.d} : Set G) →* PSL2Model f :=
    { toFun := fun g => (Ψ g).left 0
      map_one' := by simp
      map_mul' := fun g h => by
        show (Ψ ((g : G) * h)).left 0 = (Ψ g).left 0 * (Ψ h).left 0
        rw [map_mul, mul_left, Pi.mul_apply, WreathConn.permAct_apply, hleft h h.2] }
  have hρ : ∀ g : Subgroup.centralizer ({hC.d} : Set G), ρ g = (Ψ g).left 0 := fun _ => rfl
  have hHC : Halpha D hC.alpha ≤ Subgroup.centralizer ({hC.d} : Set G) :=
    PartThree.Halpha_le_centralizer_d hC
  let ρH : Halpha D hC.alpha →* PSL2Model f := ρ.comp (Subgroup.inclusion hHC)
  obtain ⟨e₀, he₀, hEeq, -⟩ := hC.hE
  have he₀E : e₀ ∈ hC.E := by
    rw [hEeq]
    exact OddLocal.self_mem_orbitIn hC.d e₀
  have hEsub : hC.E ⊆ commSet D hC.d := OddLocal.subset_commSet hS.normal hC.hE
  have hEnorm := OddLocal.closure_commSet_le_normalizer hC.hE
  have hHE : ∀ x ∈ hC.E, x ∈ Halpha D hC.alpha := fun x hx =>
    Subgroup.subset_closure (hC.DalphaStar_alpha.symm ▸ hx)
  have hCcomm : ∀ x ∈ commSet D hC.d, x ∈ Subgroup.centralizer ({hC.d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr hx.2.1.eq
  have hB : IsBenderGroup (PSL2Model f) := .isPSL2 f hf (MulEquiv.refl _)
  have := IsBenderGroup.isSimpleGroup hB
  have hLZ : ∀ t : PSL2Model f, (∀ y, t * y = y * t) → t = 1 := by
    intro t ht
    have hc : Subgroup.center (PSL2Model f) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2Model f)) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
        exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
    have htc : t ∈ Subgroup.center (PSL2Model f) :=
      Subgroup.mem_center_iff.mpr fun y => (ht y).symm
    rw [hc] at htc
    exact htc
  set C₀ : Set (PSL2Model f) := (fun x => (Ψ x).left 0) '' hC.E with hC₀
  have hinv : ∀ s : PSL2Model f, s * s = 1 → ∀ t ∈ C₀, s * t * s⁻¹ ∈ C₀ := by
    rintro s hs _ ⟨x, hx, rfl⟩
    by_cases hs1 : s = 1
    · rw [hs1, one_mul, inv_one, mul_one]
      exact ⟨x, hx, rfl⟩
    have hwΨ : Ψ (Ψ.symm ⟨![s, s⁻¹], swap 0 1⟩) = ⟨![s, s⁻¹], swap 0 1⟩ :=
      MulEquiv.apply_symm_apply _ _
    have hwc : Ψ.symm ⟨![s, s⁻¹], swap 0 1⟩ ∈ commSet D hC.d := by
      refine ⟨(hΨD _).mpr (by rw [hwΨ]; exact WreathConn.isConj_two_mk s), ?_, fun h => hs1 ?_⟩
      · have h1 : Commute (⟨![s, s⁻¹], swap 0 1⟩ : L2Wreath f 2) (inr (swap 0 1)) := by
          have h := WreathConn.commute_two_mk (c := (1 : PSL2Model f)) hs
          have e1 : (⟨![1, 1⁻¹], swap 0 1⟩ : L2Wreath f 2) = inr (swap 0 1) :=
            SemidirectProduct.ext (funext fun m => by fin_cases m <;> simp) rfl
          rw [e1, mul_one] at h
          exact h.symm
        rw [← hτu]
        exact h1.map Ψ.symm
      · have h1 := congrArg (fun g => (Ψ g).left 0) h
        simpa [hwΨ, hΨu] using h1
    have hxE : Ψ.symm ⟨![s, s⁻¹], swap 0 1⟩ * x * (Ψ.symm ⟨![s, s⁻¹], swap 0 1⟩)⁻¹ ∈ hC.E :=
      (Subgroup.mem_set_normalizer_iff.mp (hEnorm (Subgroup.subset_closure hwc)) x).mp hx
    refine ⟨_, hxE, ?_⟩
    have hwC := hCcomm _ hwc
    have hxC := hCcomm x (hEsub hx)
    have h : ρ (⟨_, hwC⟩ * ⟨x, hxC⟩ * (⟨_, hwC⟩ : Subgroup.centralizer ({hC.d} : Set G))⁻¹) =
        ρ ⟨_, hwC⟩ * ρ ⟨x, hxC⟩ * (ρ ⟨_, hwC⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hρ ⟨_, hwC⟩, hwΨ] at h
    exact h
  have hnorm : ∀ g : PSL2Model f, ∀ t ∈ C₀, g * t * g⁻¹ ∈ C₀ := by
    intro g
    have hg : g ∈ Subgroup.closure {t : PSL2Model f | t * t = 1} := by
      rw [WreathConn.closure_mul_self_eq_one_eq_top hf]
      trivial
    induction hg using Subgroup.closure_induction_left with
    | one =>
      intro t ht
      simpa using ht
    | mul_left s hs g _ ih =>
      intro t ht
      have e : s * g * t * (s * g)⁻¹ = s * (g * t * g⁻¹) * s⁻¹ := by group
      rw [e]
      exact hinv s hs _ (ih t ht)
    | inv_mul_cancel s hs g _ ih =>
      intro t ht
      have hs0 : s * s = 1 := hs
      have hs2 : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs0, inv_one]
      have e : s⁻¹ * g * t * (s⁻¹ * g)⁻¹ = s⁻¹ * (g * t * g⁻¹) * s⁻¹⁻¹ := by group
      rw [e]
      exact hinv s⁻¹ hs2 _ (ih t ht)
  have hle : Subgroup.normalClosure C₀ ≤ Subgroup.closure C₀ := by
    apply Subgroup.closure_mono
    intro x hx
    obtain ⟨t, ht, htx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp htx
    exact hnorm g t ht
  have he₀1 : (Ψ e₀).left 0 ≠ 1 := by
    intro h
    apply he₀.2.2
    apply Ψ.injective
    rw [hΨu, WreathConn.eq_two_mk ((hΨD e₀).mp he₀.1), h]
    exact SemidirectProduct.ext (funext fun m => by fin_cases m <;> simp) rfl
  have htop : Subgroup.normalClosure C₀ = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun h => he₀1 ?_
    have hmem := Subgroup.subset_normalClosure (s := C₀) ⟨e₀, he₀E, rfl⟩
    rw [h, SetLike.mem_coe, Subgroup.mem_bot] at hmem
    exact hmem
  have hsurj : Function.Surjective ρH := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← htop]
    refine hle.trans ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hHE x hx⟩, rfl⟩
  have hker : ρH.ker = Subgroup.center (Halpha D hC.alpha) := by
    ext h
    rw [MonoidHom.mem_ker]
    constructor
    · intro hh
      have h0 : (Ψ (h : G)).left 0 = 1 := hh
      have hl : (Ψ (h : G)).left = 1 := funext fun p => (hleft h (hHC h.2) p).trans h0
      have hr : ∀ σ : Perm (Fin 2), σ = 1 ∨ σ = swap 0 1 := by decide
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      rcases hr (Ψ (h : G)).right with hr | hr
      · have h1 : (h : G) = 1 := Ψ.injective (by rw [map_one]; exact SemidirectProduct.ext hl hr)
        rw [h1, mul_one, one_mul]
      · have h1 : (h : G) = hC.d := Ψ.injective (by rw [hΨu]; exact SemidirectProduct.ext hl hr)
        rw [h1]
        exact Subgroup.mem_centralizer_singleton_iff.mp (hHC g.2)
    · intro hz
      refine hLZ _ fun t => ?_
      obtain ⟨y, rfl⟩ := hsurj t
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρH hsurj)⟩

end CFSG.OddTranspositions.PartThree.Nine
