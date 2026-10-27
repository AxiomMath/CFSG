module

public import CFSG.Quasithin.Background.C126NatFstarAux
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2
open scoped Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem hasNaturalFstar_of_single_block {P V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hPN : P ≤ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))} (hL : autI hV P = L) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsL2Natural L (fixV (autI hV (twoResidual P))) n) : HasNaturalFstar P V := by
  obtain ⟨-, F, iF, iFin, hF, e, β₀, hβs, hβk, hβe⟩ := hnat
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Finite F := Finite.of_fintype F
  have hperf : ⁅L, L⁆ = L := commutator_eq_of_equiv_sl2 h4 e
  let ι' : ↥(autI hV P) ≃* SL(2, F) := (MulEquiv.subgroupCongr hL).trans e
  let ι : ↥(autOn P V) ≃* SL(2, F) := ι'
  have hKP : fstarPre P V = P :=
    fstarPre_eq_of_generalizedFitting_eq_top hPN (generalizedFitting_eq_top_of_equiv_sl2 h4 ι)
  have hN : autI hV (twoResidual P) = autI hV P := autI_twoResidual_eq_of_perfect hV hPN hL hperf
  obtain ⟨incl, hincl_val, hincl_surj⟩ := exists_incl hV hPN hL
  refine ⟨n, by omega, ?_⟩
  rw [hKP]
  let ε₀ : ↥P →* ↥(autOn P V) :=
    ((conjAct V).comp (Subgroup.inclusion hPN)).codRestrict (autOn P V)
      (fun g => ⟨⟨g, hPN g.2⟩, Subgroup.mem_subgroupOf.2 g.2, rfl⟩)
  let ε : ↥P →* SL(2, F) := ι.toMonoidHom.comp ε₀
  let hP : ↥P → ↥L := fun g => ⟨convI hV ⟨g, hPN g.2⟩, by
    rw [← hL]
    exact convI_mem_autI hV g.2 (hPN g.2)⟩
  have hεmat : ∀ g : ↥P, ε g = e (hP g) := fun g => rfl
  have hεker : ∀ g : ↥P, ε g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro g
    rw [hεmat, MulEquiv.map_eq_one_iff]
    have h1 : hP g = 1 ↔ convI hV ⟨g, hPN g.2⟩ = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1]
    exact convI_eq_one_iff hV ⟨g, hPN g.2⟩
  have hεsurj : Function.Surjective ε := by
    intro s
    have hx : (e.symm s : MulAut (IntMod V hV)) ∈ autI hV P := by
      rw [hL]
      exact (e.symm s).2
    obtain ⟨g, hgP, hg⟩ := (mem_autI hV).1 hx
    refine ⟨⟨g, hgP⟩, ?_⟩
    rw [hεmat]
    have : hP ⟨g, hgP⟩ = e.symm s := Subtype.ext hg
    rw [this]
    exact e.apply_symm_apply s
  have hnormL : ∀ x : ↥L, ∀ y : MulAut (IntMod V hV), y ∈ L →
      (x : MulAut (IntMod V hV)) * y * (x : MulAut (IntMod V hV))⁻¹ ∈ L :=
    fun x y hy => L.mul_mem (L.mul_mem x.2 hy) (L.inv_mem x.2)
  have hEQ : ∀ (k : ↥P) (u v : ↥⁅V, P⁆), (v : G) = (k : G) * (u : G) * (k : G)⁻¹ →
      Multiplicative.toAdd (β₀.comp incl v) =
        (ε k : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β₀.comp incl u) := by
    intro k u v hv
    have hu : ((hP k : ↥L) : MulAut (IntMod V hV)) (incl u : IntMod V hV) ∈ commV L :=
      G6.apply_mem_commV (hnormL _) (incl u).2
    have hv' : incl v = ⟨((hP k : ↥L) : MulAut (IntMod V hV)) (incl u : IntMod V hV), hu⟩ := by
      apply Subtype.ext
      apply IntMod.val_injective
      rw [hincl_val v]
      show (v : G) = ((convI hV ⟨(k : G), hPN k.2⟩) (incl u : IntMod V hV)).val
      rw [convI_apply_val, hincl_val u, hv]
    show Multiplicative.toAdd (β₀ (incl v)) = _
    rw [hv', hβe (hP k) (incl u) hu]
    rfl
  have hW1V : ⁅V, P⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hPN
  have hβker : (β₀.comp incl).ker =
      (⁅V, P⁆ ⊓ Subgroup.centralizer (P : Set G)).subgroupOf ⁅V, P⁆ := by
    ext u
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hfix : ∀ z : ↥(commV L), (z : IntMod V hV) ∈ fixV (autI hV (twoResidual P)) ↔
        (z : IntMod V hV).val ∈ Subgroup.centralizer (twoResidual P : Set G) := fun z =>
      mem_fixV_autI hV ((twoResidual_le P).trans hPN) _
    constructor
    · intro h1
      have h2 : incl u ∈ β₀.ker := h1
      rw [hβk, Subgroup.mem_subgroupOf] at h2
      have h3 := (hfix (incl u)).1 h2.2
      rw [hincl_val] at h3
      refine ⟨u.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨o, ho, hgo⟩ := exists_mul_mem_twoResidual hV hPN hN hg
      have hc : (u : G) * (g * o⁻¹) = (g * o⁻¹) * u :=
        Subgroup.mem_centralizer_iff.1 hgo u (hW1V u.2)
      have hoc : o * (u : G) = u * o := Subgroup.mem_centralizer_iff.1 h3 o ho
      calc g * (u : G) = (g * o⁻¹) * (o * u) := by group
        _ = (g * o⁻¹) * (u * o) := by rw [hoc]
        _ = ((g * o⁻¹) * u) * o := by group
        _ = (u * (g * o⁻¹)) * o := by rw [hc]
        _ = u * g := by group
    · rintro ⟨-, hc⟩
      have h2 : incl u ∈ β₀.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        refine ⟨(incl u).2, (hfix (incl u)).2 ?_⟩
        rw [hincl_val]
        exact Subgroup.centralizer_le (twoResidual_le P) hc
      exact h2
  refine ⟨F, iF, iFin, hF, ε, ?_, ?_, β₀.comp incl, hβs.comp hincl_surj, hβker, hEQ⟩
  · ext k
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hεker k
  · rw [MonoidHom.range_eq_top.2 hεsurj, commutator_sl2_eq_top h4]

end CFSG.Quasithin.C126.Nat
