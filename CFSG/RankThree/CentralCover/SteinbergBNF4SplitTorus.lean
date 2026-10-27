module

public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem F4_split_torus_actual_central_cover_two_local_rank {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) [Fintype K] (hp : p.Prime) (hp2 : p ≠ 2) (_hpq : p ∣ Fintype.card K - 1)
    (φ : Y →* adjointGroup .F4 K) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {ζ : Kˣ} (hζo : orderOf ζ = p) :
    ∃ D : Subgroup (adjointGroup .F4 K), (∀ g, g ∈ D ↔ ∃ a : Fin Tag.F4.rank → ZMod p,
        (g : ModGL .F4 K) = (List.ofFn fun i => torusElt .F4 K i (ζ ^ (a i).val)).prod) ∧
      IsElemAbelian p D ∧ Nat.card D = p ^ 4 ∧
      (∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x) ∧
      ∃ R : Subgroup G, R ≤ Y ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ ∃ A : Subgroup G,
        A ≤ Y ⊓ Subgroup.normalizer (R : Set G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 4 ∧
        4 ≤ localRank p G := by
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  have hdet : IsUnit ((Tag.F4.cartan.det : ℤ) : ZMod p) := by
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  obtain ⟨hDab, hcard, hF, R, hRY, hR1, hR2, A, hA, hAab, hAcard, hrank⟩ :=
    chevalley_split_torus_witness Y hp hp2 hdet ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) φ hφ
      hker hζo hζ
  exact ⟨_, mem_range_chevTorus_iff ζ hζ, hDab, hcard, hF, R, hRY, hR1, hR2, A, hA, hAab, hAcard,
    hrank⟩

end CFSG.RankThree.CentralCover
