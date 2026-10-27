module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.card_sup_commXbarPre_eq_pow_nine (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hdim : Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 8) :
    Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ 9 := by
  rw [hc.card_sup_commXbarPre_eq hD φ hφπ,
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(cmComm M Q Z B K γ M₀ φ)), hdim, hD.card]
  ring

theorem Ctx.eq_or_eq_of_invariant {G' : Type*} [Group G'] (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (θ : ↥(XbarH M Q Z B) →* G') (hθ : Function.Surjective θ)
    (ρ : G' →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)))
    (hρ : ∀ s, ρ (θ s) = cmCommAct hc φ s)
    (hirr : ∀ U : AddSubgroup ↥(cmComm M Q Z B K γ M₀ φ), (∀ g, ∀ u ∈ U, ρ g u ∈ U) →
      U = ⊥ ∨ U = ⊤)
    (W : Subgroup G) (hZW : Z ≤ W) (hWY : W ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (hinv : ∀ g ∈ XbarPre M Q Z B, ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    W = Z ∨ W = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ := by
  have hYQ : (Z ⊔ ⁅Q, XbarPre M Q Z B⁆ : Subgroup G) ≤ Q :=
    sup_le hc.Z_le_Q (commutator_le_Q hc)
  have hWQ : W ≤ Q := hWY.trans hYQ
  have hπC : ∀ y ∈ (Z ⊔ ⁅Q, XbarPre M Q Z B⁆ : Subgroup G),
      M₀.π y ∈ cmComm M Q Z B K γ M₀ φ := fun y hy =>
    (hc.mem_img_sup_iff_mem_cmComm hD φ hφπ _).mp ⟨y, hy, hYQ hy, rfl⟩
  let U : AddSubgroup ↥(cmComm M Q Z B K γ M₀ φ) :=
    (M₀.img W).comap (cmComm M Q Z B K γ M₀ φ).subtype.toAddMonoidHom
  have hmemU : ∀ u : ↥(cmComm M Q Z B K γ M₀ φ), u ∈ U ↔ (u : M₀.E) ∈ M₀.img W :=
    fun u => Iff.rfl
  have hUinv : ∀ g : G', ∀ u ∈ U, ρ g u ∈ U := by
    intro g u hu
    obtain ⟨s, rfl⟩ := hθ g
    rw [hρ s, hmemU]
    obtain ⟨w, hwW, hwQ, hwu⟩ := (hmemU u).mp hu
    have hsX : ((s : ↥(H0 M Z)) : G) ∈ XbarPre M Q Z B := (mem_XbarH_iff hc s.1).mp s.2
    have hsw := hinv _ hsX w hwW
    refine ⟨_, hsw, hWQ hsw, ?_⟩
    rw [hφπ (s : ↥(H0 M Z)) w hwQ, hwu]
    rfl
  rcases hirr U hUinv with h0 | h1
  · left
    refine le_antisymm (fun w hw => ?_) hZW
    have hmem : (⟨M₀.π w, hπC w (hWY hw)⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ U :=
      ⟨w, hw, hWQ hw, rfl⟩
    rw [h0, AddSubgroup.mem_bot] at hmem
    exact (M₀.π_ker w (hWQ hw)).mp (congrArg Subtype.val hmem)
  · right
    refine le_antisymm hWY fun y hy => ?_
    have hmem : (⟨M₀.π y, hπC y hy⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) ∈ U := by
      rw [h1]
      trivial
    exact (M₀.mem_img_iff hZW (hYQ hy)).mp hmem

end CFSG.RankThree.GF2n.Stroth80
