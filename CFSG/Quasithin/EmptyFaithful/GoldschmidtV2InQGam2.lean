module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtV2InQGamma

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped commutatorElement

namespace V2InQ

theorem card_mulAut_vt3 : Nat.card (MulAut (Multiplicative (Vt 3))) = 168 := by
  have h := CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 2)
    (MulEquiv.refl (Multiplicative (Fin 3 → ZMod 2)))
  rw [h, CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide

theorem matrix_ext_of_mulVec {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ v : Vt 3, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.ext fun i j => by
    have := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this

variable {G : Type} [Group G] {L : Subgroup G} {e : ↥L →* SLt 3}
  {β : ↥(blockU L) →* Multiplicative (Vt 3)}

theorem comm_mem_blockZ_of_gamma_eq_one (hs : LnStr L e β)
    (g : ↥(Subgroup.normalizer (L : Set G))) (hg : gammaMap hs g = 1) {u : G} (hu : u ∈ blockU L) :
    u⁻¹ * (g.1 * u * g.1⁻¹) ∈ blockZ L := by
  have h1 : β (sigmaU g.1 g.2 ⟨u, hu⟩) = β ⟨u, hu⟩ := by
    have := gammaMap_apply hs g ⟨u, hu⟩
    rw [hg] at this
    exact this.symm
  have hb : g.1 * u * g.1⁻¹ ∈ blockU L := by
    have := (sigmaU g.1 g.2 ⟨u, hu⟩).2
    rwa [sigmaU_coe] at this
  have hsig : sigmaU g.1 g.2 ⟨u, hu⟩ = ⟨g.1 * u * g.1⁻¹, hb⟩ :=
    Subtype.ext (sigmaU_coe g.1 g.2 ⟨u, hu⟩)
  exact s151v_beta_inj hs hu hb (by rw [← hsig]; exact h1.symm)

theorem comm_mem_blockQ_of_gamma_eq_one (hs : LnStr L e β)
    (g : ↥(Subgroup.normalizer (L : Set G))) (hg : gammaMap hs g = 1) {ℓ : G} (hℓ : ℓ ∈ L) :
    g.1 * ℓ * g.1⁻¹ * ℓ⁻¹ ∈ blockQ L := by
  have hgL : g.1 * ℓ * g.1⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 g.2 ℓ).1 hℓ
  set ℓ₁ : ↥L := ⟨ℓ, hℓ⟩ with hℓ₁
  set ℓ₂ : ↥L := ⟨g.1 * ℓ * g.1⁻¹, hgL⟩ with hℓ₂
  have key : ∀ v : Vt 3, (e ℓ₂ : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v =
      (e ℓ₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := by
    intro v
    obtain ⟨u, hu⟩ := hs.βsurj (Multiplicative.ofAdd v)
    have hw : ℓ * (u : G) * ℓ⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 (s151v_L_le_normalizer_blockU L hℓ) _).1 u.2
    set w : ↥(blockU L) := ⟨ℓ * u * ℓ⁻¹, hw⟩ with hwdef
    have hu' : β (sigmaU g.1 g.2 u) = β u := by
      have := gammaMap_apply hs g u
      rw [hg] at this
      exact this.symm
    have hw' : β (sigmaU g.1 g.2 w) = β w := by
      have := gammaMap_apply hs g w
      rw [hg] at this
      exact this.symm
    have e1 := hs.equiv ℓ₁ u w rfl
    have hℓ₂c : (ℓ₂ : G) = g.1 * ℓ * g.1⁻¹ := rfl
    have hwc : (w : G) = ℓ * u * ℓ⁻¹ := rfl
    have e2 := hs.equiv ℓ₂ (sigmaU g.1 g.2 u) (sigmaU g.1 g.2 w) (by
      rw [sigmaU_coe, sigmaU_coe, Subgroup.coe_inv, hℓ₂c, hwc]
      group)
    rw [hw', hu'] at e2
    rw [hu, toAdd_ofAdd] at e1 e2
    exact e2.symm.trans e1
  have heq : e ℓ₂ = e ℓ₁ := Subtype.ext (matrix_ext_of_mulVec key)
  have hker : ℓ₂ * ℓ₁⁻¹ ∈ e.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
  rw [hs.ker] at hker
  have hmem : ((ℓ₂ * ℓ₁⁻¹ : ↥L) : G) ∈ blockQ L :=
    ⟨ℓ₂ * ℓ₁⁻¹, hker, rfl⟩
  have e3 : ((ℓ₂ * ℓ₁⁻¹ : ↥L) : G) = g.1 * ℓ * g.1⁻¹ * ℓ⁻¹ := rfl
  rwa [e3] at hmem

end V2InQ

end CFSG.Quasithin
