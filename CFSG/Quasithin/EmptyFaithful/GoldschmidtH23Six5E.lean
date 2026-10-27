module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5BHelp
public import CFSG.Quasithin.EmptyFaithful.T1515C6Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)
include d

theorem A₀_le_autI {Mc : Subgroup G} (hTMc : T ≤ Mc) {Y' : Subgroup G} (hY : Y' ≤ M ⊓ Mc)
    (hYa : autI hV Y' = Subgroup.zpowers d.S.a₂) :
    d.S.A₁ ⊔ d.S.A₂ ≤ autI hV (M ⊓ Mc) := by
  have hA0M : d.S.A₁ ⊔ d.S.A₂ ≤ autI hV M := by
    rw [d.hsup]
    exact Jhat_le _
  have hnormA : autI hV M ≤ Subgroup.normalizer ((d.S.A₁ ⊔ d.S.A₂ : Subgroup _) : Set _) := by
    intro g hg
    exact Subgroup.mem_normalizer_fintype fun n hn => d.hnorm g hg n hn
  have hTb : IsSylowTwoOf (autI hV T) (autI hV M) := isSylowTwoOf_autOn' d.hsyl d.hMN
  have hS2 : IsSylowTwoOf (autI hV T ⊓ (d.S.A₁ ⊔ d.S.A₂)) (d.S.A₁ ⊔ d.S.A₂) :=
    A4.isSylowTwoOf_inf_normal hTb hA0M hnormA
  have hTK : autI hV T ≤ autI hV (M ⊓ Mc) := autI_mono hV (le_inf d.hTM hTMc)
  have ha₂ : d.S.a₂ ∈ autI hV (M ⊓ Mc) := by
    have : d.S.a₂ ∈ autI hV Y' := hYa ▸ Subgroup.mem_zpowers _
    exact autI_mono hV hY this
  have hτ : d.S.τ ∈ autI hV (M ⊓ Mc) := hTK d.hτ
  rw [d.S.A₀_eq_closure hS2]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ((rfl | rfl) | hx)
  · exact ha₂
  · exact (autI hV (M ⊓ Mc)).mul_mem ((autI hV (M ⊓ Mc)).mul_mem hτ ha₂)
      ((autI hV (M ⊓ Mc)).inv_mem hτ)
  · exact hTK hx.1

theorem caseI {Mc : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hVeq : V = V154 T Mc M) (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    {Y' : Subgroup G} (hY : Y' ≤ M ⊓ g1_1516 d.Z₁) (hYa : autI hV Y' = Subgroup.zpowers d.S.a₂) :
    ¬ (M ⊓ g1_1516 d.Z₁) ≤ Mc := by
  intro hle
  have hYle : Y' ≤ M ⊓ Mc := fun y hy => ⟨(hY hy).1, hle (hY hy)⟩
  have hA0 : d.S.A₁ ⊔ d.S.A₂ ≤ autI hV (M ⊓ Mc) := d.A₀_le_autI hq.t_le_mc hYle hYa
  subst hVeq
  have hmB : mBar0 T Mc M = d.S.A₁ ⊔ d.S.A₂ := by
    rw [d.hsup]
    exact JhatOn_eq hV
  have hM0 : m0Of T Mc M ≤ Mc := by
    intro h hh
    obtain ⟨hhM, hhN, hhA⟩ := mem_preOn.1 hh
    have hmem : convI hV ⟨h, hhN⟩ ∈ autI hV (M ⊓ Mc) := hA0 (hmB ▸ hhA)
    obtain ⟨⟨g, hgN⟩, hgK, hgeq⟩ := (mem_autI hV).1 hmem
    have hc : g⁻¹ * h ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
      have h1 : convI hV ⟨g⁻¹ * h, (Subgroup.normalizer _).mul_mem
          ((Subgroup.normalizer _).inv_mem hgN) hhN⟩ = 1 := by
        have : (⟨g⁻¹ * h, (Subgroup.normalizer _).mul_mem
          ((Subgroup.normalizer _).inv_mem hgN) hhN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
            ⟨g, hgN⟩⁻¹ * ⟨h, hhN⟩ := rfl
        rw [this, map_mul, map_inv, hgeq, inv_mul_cancel]
      exact (convI_eq_one_iff hV _).1 h1
    have : h = g * (g⁻¹ * h) := by group
    rw [this]
    exact Mc.mul_mem hgK.2 (h15.centralizer_le hc)
  have hVle : V154 T Mc M ≤ VZ T Mc := by
    rw [h15.gen]
    refine conjClosure_le fun h hh z hz => ?_
    exact mem_conjClosure (hM0 hh) hz.1
  have hord := h19.two.2 Mc ⟨hq.mc_max, hq.t_le_mc⟩
  have hMcN : Mc ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
    intro h hh
    obtain ⟨a, ha, c, hc, rfl⟩ := hord h hh
    exact (Subgroup.normalizer _).mul_mem (d.hMN ha.2)
      (Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hVle hc.2))
  have hloc : IsTwoLocal (Subgroup.normalizer (V154 T Mc M : Set G)) := by
    refine ⟨V154 T Mc M, ?_, ?_, rfl⟩
    · intro hb
      have h256 := d.hcard
      have : Nat.card (IntMod (V154 T Mc M) hV) = 1 := by
        change Nat.card (V154 T Mc M) = 1
        rw [hb, Subgroup.card_bot]
      omega
    · intro x
      exact ⟨1, by simpa using Subtype.ext (hV.2 x x.2)⟩
  have heq := hq.mc_max.2 _ hloc hMcN
  exact not_le_mc_of_isMf hq hM (by rw [← heq]; exact d.hMN)

end Six5Data

end CFSG.Quasithin
