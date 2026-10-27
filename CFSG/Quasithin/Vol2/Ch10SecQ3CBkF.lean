module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkE
public import CFSG.Quasithin.EmptyFaithful.S1417Glue

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem natData_of_autI {W X : Subgroup G} (hel : IsElemAbelian 2 W)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hWX : W ≤ Subgroup.normalizer (X : Set G))
    (hOX : blockQ X ≤ Subgroup.centralizer (W : Set G))
    {K₀ : Subgroup (MulAut (IntMod W hel))} (hK₀ : autI hel X = K₀)
    {C : Subgroup (IntMod W hel)} (hC : commV K₀ ⊓ C = ⊥) {j n : ℕ} (hj : 2 ≤ j) (hn : 2 ≤ n)
    (hnat : E2.IsL2Natural K₀ C j)
    (hXF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    NatData X ⁅W, X⁆ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, e, β, hβs, hβk, hβe⟩ := hnat
  obtain ⟨F', _, _, hF', ⟨eX⟩⟩ := hXF
  set φ := convHom hel X hXW with hφ
  have hφK : ∀ x, φ x ∈ K₀ := fun x => hK₀ ▸ (range_convHom hel X hXW ▸ ⟨x, rfl⟩)
  set α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (φ.codRestrict K₀ hφK) with hα
  have hαs : Function.Surjective α := by
    intro γ
    have h1 : ((e.symm γ : ↥K₀) : MulAut (IntMod W hel)) ∈ φ.range := by
      rw [range_convHom, hK₀]
      exact (e.symm γ).2
    obtain ⟨x, hx⟩ := h1
    refine ⟨x, ?_⟩
    have : φ.codRestrict K₀ hφK x = e.symm γ := Subtype.ext hx
    rw [hα, MonoidHom.comp_apply, this]
    exact e.apply_symm_apply γ
  obtain ⟨hαk, hjn⟩ := ker_eq_pCore hj hn hF hF' α hαs eX
  subst hjn
  have hcomm : ⁅W, X⁆ = (commV K₀).map (S1417.inclMod hel) := by
    rw [S1417.commutator_eq_map_commV hel hXW, hK₀]
  have hinj : Function.Injective (S1417.inclMod hel) := IntMod.val_injective
  let ψ : ↥(commV K₀) ≃* ↥⁅W, X⁆ :=
    (Subgroup.equivMapOfInjective (commV K₀) (S1417.inclMod hel) hinj).trans
      (MulEquiv.subgroupCongr hcomm.symm)
  have hψ : ∀ u, ((ψ u : ↥⁅W, X⁆) : G) = (u : IntMod W hel).val := fun u => rfl
  have hWX' : ⁅W, X⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hXW
  have hW2 : IsPGroup 2 W := fun g => ⟨1, Subtype.ext (by simpa using hel.2 g g.2)⟩
  refine ⟨CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hWX)
      (SecA.le_normalizer_commutator hXW Subgroup.le_normalizer) (hW2.to_le hWX'),
    fun u hu => ?_, fun u hu => hel.2 u (hWX' hu),
    SecA.le_normalizer_commutator hXW Subgroup.le_normalizer, F, inferInstance, inferInstance, hF,
    α, hαs, hαk, β.comp ψ.symm.toMonoidHom, ⟨?_, hβs.comp ψ.symm.surjective⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hOX hq) u (hWX' hu)).symm
  · rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : ψ.symm u ∈ β.ker := hu
    rw [hβk, Subgroup.mem_subgroupOf, hC, Subgroup.mem_bot] at h1
    have : ψ.symm u = 1 := Subtype.ext h1
    simpa using congrArg ψ this
  · intro ℓ u v huv
    set u₀ := ψ.symm u
    set v₀ := ψ.symm v
    have hu₀ : ((u₀ : IntMod W hel)).val = u := by
      rw [← hψ, MulEquiv.apply_symm_apply]
    have hv₀ : ((v₀ : IntMod W hel)).val = v := by
      rw [← hψ, MulEquiv.apply_symm_apply]
    set h : ↥K₀ := φ.codRestrict K₀ hφK ℓ
    have hh : ((h : MulAut (IntMod W hel)) (u₀ : IntMod W hel)) = (v₀ : IntMod W hel) := by
      apply IntMod.val_injective
      change (convHom hel X hXW ℓ u₀).val = _
      rw [convHom_apply, convI_apply_val, hu₀, hv₀, huv]
      rfl
    have hmem : (h : MulAut (IntMod W hel)) (u₀ : IntMod W hel) ∈ commV K₀ := hh ▸ v₀.2
    have := hβe h u₀ hmem
    have hv₀' : (⟨_, hmem⟩ : ↥(commV K₀)) = v₀ := Subtype.ext hh
    rw [hv₀'] at this
    exact this

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
