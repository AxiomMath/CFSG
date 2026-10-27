module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tu
public import CFSG.Quasithin.Vol2.Ch11SecO8B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] def KindJ (X : Type) [Group X] (m : ℕ) : Prop :=
  2 ≤ m ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
    (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∨
      Nonempty (X ≃* ↥(Assembly.LowTwoRank.StatedSp 2 K)) ∨
      Nonempty (X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆))

omit [Finite Γ] in
theorem autOn_fix_centralizer {J W : Subgroup Γ} :
    ∀ h ∈ autOn J W, ∀ z ∈ (Subgroup.centralizer (J : Set Γ)).subgroupOf W, h z = z := by
  intro h hh z hz
  obtain ⟨g, hgJ, rfl⟩ := Setup.mem_autOn_iff.mp hh
  apply Subtype.ext
  rw [Setup.coe_conjAct_apply]
  have h1 : (g : Γ) * (z : Γ) = (z : Γ) * g := Subgroup.mem_centralizer_iff.mp hz g hgJ
  rw [h1, mul_inv_cancel_right]

theorem not_surjective_L45_of_kind {X : Type} [Group X] {m : ℕ} (hX : KindJ X m) {k : ℕ}
    (hk : k = 4 ∨ k = 5) (π : ↥(Assembly.LowTwoRank.StatedSL k (ZMod 2)) →* X) :
    ¬ Function.Surjective π := by
  intro hπ
  obtain ⟨hm, K, _, _, hK, he⟩ := hX
  rcases he with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Ch11.SecC.B51.not_surjective_L45_SL3 hk hm hK (e.toMonoidHom.comp π)
      (e.surjective.comp hπ)
  · exact Ch11.SecC.B51.not_surjective_L45_Sp4 hk hm hK (e.toMonoidHom.comp π)
      (e.surjective.comp hπ)
  · exact Ch11.SecC.B51.not_surjective_L45_G2 KGNat.factG2DerivedOrder_holds hk hm hK
      (e.toMonoidHom.comp π) (e.surjective.comp hπ)

theorem not_case1iii {V : Type} [CommGroup V] [Finite V] {G Jst : Subgroup (MulAut V)} {m k : ℕ}
    (hX : KindJ ↥Jst m) (h : B51Case1iii G Jst k) : False := by
  obtain ⟨-, hk, π, U₁, U₂, -, h₁, -⟩ := h
  exact not_surjective_L45_of_kind hX hk π h₁.1

theorem not_case1iv {V : Type} [CommGroup V] [Finite V] {G Jst : Subgroup (MulAut V)} {m : ℕ}
    (hX : KindJ ↥Jst m) (h : B51Case1iv G Jst) : False := by
  obtain ⟨-, k, hk, j, hj, -, I', π, -, -, -, hreal⟩ := h
  exact not_surjective_L45_of_kind hX hk π (hreal ⟨0, by omega⟩).1

section Case1i


theorem torus_case1i {R J L V₁ V : Subgroup Γ} {n m : ℕ} (hV : IsElemAbelian 2 V)
    [IsMulCommutative ↥V] (hC : K2Ctx R J L V₁ V n) (hV₁U : V₁ ≤ ⁅V, J⁆)
    (hX : KindJ ↥(autOn J V) m) {G : Subgroup (MulAut ↥V)} (hi : B51Case1i G (autOn J V)) :
    ∃ y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ), y ∉ Subgroup.centralizer (V₁ : Set Γ) ∧
      (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ)) ∧
      y ^ (2 ^ n - 1) ∈ Subgroup.centralizer (V₁ : Set Γ) := by
  have hJV := hC.hJV
  have hUV : ⁅V, J⁆ ≤ V := by
    rw [← Ch11.SecC.B51.map_commV_autOn hJV]
    exact Subgroup.map_subtype_le _
  have hJU : J ≤ Subgroup.normalizer ((⁅V, J⁆ : Subgroup Γ) : Set Γ) :=
    le_sup_right.trans (A3.sup_le_normalizer_commutator V J)
  have : IsMulCommutative ↥⁅V, J⁆ := Ch11.SecC.B51.isMulCommutative_of_le hUV
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  have hW2U : ∀ w : ↥⁅V, J⁆, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hV.2 w (hUV w.2))
  have hB := hi.2.1
  rw [Ch11.SecC.B51.commV_autOn hJV, Ch11.SecC.B51.fixV_autOn hJV,
    Ch11.SecC.B51.inf_subgroupOf_eq] at hB
  obtain ⟨hm, K, _, _, hK, he⟩ := hX
  rcases he with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have h2 := Ch11.SecC.B51.binaryNaturalSL_res hJV hJU hUV
      (Ch11.SecC.factB42SL3_holds K m hm hK ↥V hW2 _ _ _ ⟨e⟩ hB)
    rw [Ch11.SecC.B51.inf_subgroupOf_self] at h2
    obtain ⟨K', _, _, hK', π, hR⟩ := h2
    exact torus_of_natural hV hC hUV hJU hV₁U
      (torusData_SL3 hm hK' hW2U hR autOn_fix_centralizer)
  · have h2 := Ch11.SecC.B51.binaryNaturalSp4_res hJV hJU hUV
      (Ch11.SecC.factB42Sp4_holds K m hm hK ↥V hW2 _ _ _ ⟨e⟩ hB)
    rw [Ch11.SecC.B51.inf_subgroupOf_self] at h2
    obtain ⟨K', _, _, hK', π, hR⟩ := h2
    exact torus_of_natural hV hC hUV hJU hV₁U
      (torusData_Sp4 hm hK' hW2U hR autOn_fix_centralizer)
  · have h2 := Ch11.SecC.B51.g2Natural_res hJV hJU hUV
      (Ch11.SecC.factB42G2_holds K m hm hK ↥V hW2 _ _ _ ⟨e⟩ hB)
    rw [Ch11.SecC.B51.inf_subgroupOf_self] at h2
    obtain ⟨K', _, _, hK', hreal⟩ := h2
    have : CharP K' 2 := KGNat.charP_two_of_card (by omega) hK'
    obtain ⟨c, hc0, hc1⟩ :=
      B42G2Id.exists_ne_zero_ne_one_of_three_le (K := K') (hK' ▸ B42G2Id.three_le_two_pow hm)
    have hc : quasithinG2 K' = ⁅quasithinG2 K', quasithinG2 K'⁆ := by
      rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
        JonesParshall.cayley_commutator_eq hc0 hc1]
    rw [hc] at hreal
    obtain ⟨π, hR⟩ := hreal
    exact torus_of_natural hV hC hUV hJU hV₁U
      (torusData_G2 hm hK' hW2U hR autOn_fix_centralizer)

end Case1i

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
