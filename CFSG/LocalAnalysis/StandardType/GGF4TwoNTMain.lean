module

public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTHalfCount
public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTPlane
public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTFrame
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCent
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBInputs

public section

namespace CFSG.StandardType.F4TwoNonToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.StandardType.TableBF4TwoTB CFSG.StandardType.HalfMaxF4

theorem ggF4TwoNonToralSolvInput_of_cent
    (h : GGF4TwoThreeCCentInput) : GGF4TwoNonToralSolvInput := by
  intro K _ _ _ hK E hE hcard3 hSC' hnotframe e heE he1
  have hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E := by
    intro x hx hx3
    exact hSC' x hx3 fun y hy => (Subgroup.mem_centralizer_iff.1 hx y hy).symm
  have hP : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn3 : 3 ≤ n := by
    rw [hn] at hcard3
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard3
  have hcardE : Nat.card E = 3 ^ 3 := by
    by_contra hne
    have hn4 : 4 ≤ n := by
      rw [hn] at hne
      have : n ≠ 3 := fun h => hne (by rw [h])
      omega
    obtain ⟨c, hc⟩ := exists_conj_frame_of_card_F4 K hK E hE
      (by rw [hn]; exact Nat.pow_le_pow_right (by norm_num) hn4)
    exact hnotframe ⟨c, hc⟩
  have hnd := isEmpty_langPlaneData_of_selfCentralizing K hK hE hcardE hSC
  obtain ⟨P, heP, hPE, hPc, D, hD⟩ := exists_regular_plane K hK hE hcardE hnd heE he1
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => hE.2 x (hPE hx)
  obtain ⟨a, ha, h12⟩ := threeC_data_of_regular_plane K hK hPc hP3 D hD heP he1
  have he3 : e ^ 3 = 1 := hE.2 e heE
  have he'3 : (D.c * e * D.c⁻¹) ^ 3 = 1 := by
    rw [conj_pow, he3]
    group
  have he'1 : D.c * e * D.c⁻¹ ≠ 1 := by
    intro h1
    apply he1
    have := congrArg (fun z => D.c⁻¹ * z * D.c) h1
    simpa [mul_assoc] using this
  have hsolv := h K hK (D.c * e * D.c⁻¹) D.g0 a he'3 he'1 D.hg0C ha h12
  let f : Subgroup.centralizer ({e} : Set (adjointGroup .F4 K)) →*
      Subgroup.centralizer ({D.c * e * D.c⁻¹} : Set (adjointGroup .F4 K)) :=
    ((MulAut.conj D.c).toMonoidHom.comp (Subgroup.centralizer ({e} : Set _)).subtype).codRestrict _
      (fun x => by
        have hx := (Subgroup.mem_centralizer_singleton_iff.1 x.2)
        rw [Subgroup.mem_centralizer_singleton_iff]
        change (D.c * (x : adjointGroup .F4 K) * D.c⁻¹) * (D.c * e * D.c⁻¹) =
          (D.c * e * D.c⁻¹) * (D.c * (x : adjointGroup .F4 K) * D.c⁻¹)
        calc (D.c * (x : adjointGroup .F4 K) * D.c⁻¹) * (D.c * e * D.c⁻¹)
            = D.c * ((x : adjointGroup .F4 K) * e) * D.c⁻¹ := by group
          _ = D.c * (e * (x : adjointGroup .F4 K)) * D.c⁻¹ := by rw [hx]
          _ = (D.c * e * D.c⁻¹) * (D.c * (x : adjointGroup .F4 K) * D.c⁻¹) := by group)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : D.c * (x : adjointGroup .F4 K) * D.c⁻¹ = D.c * (y : adjointGroup .F4 K) * D.c⁻¹ :=
      congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  exact solvable_of_solvable_injective hf

end CFSG.StandardType.F4TwoNonToral
