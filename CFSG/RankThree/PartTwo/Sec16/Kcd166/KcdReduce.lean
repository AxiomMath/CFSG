module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.KcdTransport
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrKcdA5
public import CFSG.RankThree.PartTwo.Sec16.Kcd166.RTwo

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS

@[expose] def GFlatAt166 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 3 < p →
    CFSG.Assembly.RankThreeEven.localRank p G < 3 →
    ∀ X : Subgroup G, Group.IsPerfect ↥X →
      Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) →
    ∀ d : ↥X, d ^ 3 = 1 →
      (d : ↥X ⧸ aschbacherSolvableCore 3 ↥X) ∈
        Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) →
    ∀ I₁ : Subgroup ↥X, Group.IsPerfect ↥I₁ → I₁ ≤ Subgroup.centralizer ({d} : Set ↥X) →
      IsPGroup 2 ↥(I₁ ⊓ aschbacherSolvableCore 3 ↥X) →
      Nonempty (↥(I₁.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))) ≃*
        alternatingGroup (Fin 5)) →
    ∀ N M : Subgroup ↥X, N.Normal → M.Normal → N < M → M ≤ aschbacherSolvableCore 3 ↥X →
      (∀ K : Subgroup ↥X, K.Normal → N ≤ K → K ≤ M → K = N ∨ K = M) →
      (∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) → (∀ x ∈ M, x ^ p ∈ N) →
      ∀ m ∈ M, (∀ i ∈ I₁, m * i * m⁻¹ * i⁻¹ ∈ N) → m * d * m⁻¹ * d⁻¹ ∈ N

private theorem isPerfect_of_mem_thetaComponentsAt {G : Type} [Group G] {b : G}
    {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 b) : Group.IsPerfect ↥X := by
  obtain ⟨L, hL, rfl⟩ := hX
  have := hL.1
  exact Group.IsPerfect.ofSurjective
    (f := (L.equivMapOfInjective _ (Subgroup.subtype_injective _)).toMonoidHom)
    (L.equivMapOfInjective _ (Subgroup.subtype_injective _)).surjective

theorem step166KcdA5_of_gFlatAt166
    (hG : GFlatAt166) : Step166KcdA5 := by
  intro G _ _ A c L Y₀ h hJ d hdA hd1 hdc b hb X hX hXL _ M J P p hp hp3 _ _ _ _ _ _ _ hAJ
    hPU _ hAP hPJ hIX hIA5 hUθ hUidem
  obtain ⟨hUp', hUD', hUd', I₁, hI₁p, hI₁d, hUI₁, hI₁2, hI₁A5⟩ :=
    exists_iOne_at h hJ hdA hd1 hdc hb hXL hp hp3 hAJ hPU hAP hPJ hIX hIA5 hUθ hUidem
  haveI : Fact p.Prime := ⟨hp⟩
  have hθs : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥X) :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
  have hU'bot := eq_bot_of_gflat inferInstance hθs hUp' hUD' hUd' hUI₁
    (hG G p hp hp3 (h.localRank_lt p hp hp3) X (isPerfect_of_mem_thetaComponentsAt hX)
      (isTripleCover_quot h hJ hdA hd1 hdc hXL) _
      (Subtype.ext (h.toSec14Std.isE27.1.2 d hdA)) (mk_mem_center h hJ hdA hd1 hdc hXL)
      I₁ hI₁p hI₁d hI₁2 hI₁A5)
  have hUX : ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤ X :=
    hUθ.trans (Subgroup.map_subtype_le _)
  have hUmap : ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ =
      ((⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆).subgroupOf X).map
        X.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUX]
  rw [hUmap, hU'bot, Subgroup.map_bot]

end CFSG.RankThree.PartTwo.Sec16.Kcd166
