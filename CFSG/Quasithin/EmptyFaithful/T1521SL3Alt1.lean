module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Iface
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Fix
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.Quasithin.L3Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem centralizes_of_model_alt1 (hM : L3ModelAut) {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} {n : ℕ} (hn : 1 < n) (hL : IsPSL 3 2 n ↥L)
    (hP : IsSylowTwoOf P L) {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) :
    ∀ l ∈ L, v * l = l * v := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  let φ : ↥L ≃* projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have h1 : conjAct L ⟨v, hv⟩ = 1 :=
    hM K n (by omega) hK ↥L φ (A4.toSylow hP) (conjAct L ⟨v, hv⟩)
      fun z hz hzo => conjAct_fix_of_odd hP hv hc hz hzo
  intro l hl
  have h2 : conjAct L ⟨v, hv⟩ ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [h1]; rfl
  have h3 := congrArg (fun x : ↥L => (x : G)) h2
  have h4 : v * l * v⁻¹ = l := h3
  calc v * l = (v * l * v⁻¹) * v := by group
    _ = l * v := by rw [h4]

end CFSG.Quasithin.L3Aut
