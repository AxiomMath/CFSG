module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCore
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerLastChoice
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Polynomial Module CFSG.RankThree.Classical

section Core

theorem choiceTwo_psp {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n : ℕ} {ψ : StatedSp n (GaloisField 2 1) →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (Symplectic.rootDatum n (GaloisField 2 1)) .PSp n 1 ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) {b : G} {L₁ : Subgroup G}
    (hpair : GGStepTwoPair 3 B Bs x L D J b L₁) :
    ∃ m ∈ ggG0 3 B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) 3 := by
  classical
  have hK : Nat.card (GaloisField 2 1) = 2 := by rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have : NeZero n := ⟨by omega⟩
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 1)) := hctx.2.2.2.2.1.2
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 1)) := hker ha
    rw [AutPSp.center_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  have hG₀ : ψ.range = ggG0 3 B x L D J := hctx.range_eq
  have hBs := hctx.bstar
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hG₀]
    exact s1.1
  have hmem : ∀ c ∈ Bs, c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 1) hrk ψ hker
      (hctx.2.2.2.2.2.2.1.2 c hc)
    rw [hCψ, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hE3 : ∀ Y ∈ Bs.comap ψ, Y ^ 3 = 1 := fun Y hY =>
    hψ (by rw [map_pow, map_one]; exact hBs.2.1.2 _ hY)
  have hEc : ∀ Y ∈ Bs.comap ψ, ∀ Y' ∈ Bs.comap ψ, Y * Y' = Y' * Y := fun Y hY Y' hY' =>
    hψ (by rw [map_mul, map_mul]; exact TableB.IsElemAbelian.comm hBs.2.1 hY hY')
  have hEsc : ∀ Z, (∀ Y ∈ Bs.comap ψ, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ Bs.comap ψ := by
    intro Z hZ hZ3
    refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun c hc => ?_)
      (by rw [← map_pow, hZ3, map_one])
    obtain ⟨Y, rfl⟩ := hmem c hc
    rw [← map_mul, ← map_mul, hZ Y hc]
  have hpK : ((3 : ℕ) : GaloisField 2 1) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (GaloisField 2 1) 2]
    norm_num
  have hne : ¬ IsUnit (cyclotomic 3 (GaloisField 2 1)) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero 3 _),
      natDegree_cyclotomic, Nat.totient_prime Nat.prime_three]
    norm_num
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero 3 _)
  have : Fact (Irreducible g) := ⟨hg⟩
  obtain ⟨F⟩ := ChoiceTwo.exists_frame hK hgd hE3 hEc hEsc
  have hζo : IsPrimitiveRoot (AdjoinRoot.root g) 3 :=
    NSFrame.root_isPrimitiveRoot Nat.prime_three hpK hgd
  have : Module.Finite (GaloisField 2 1) (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have hL : finrank (GaloisField 2 1) (AdjoinRoot g) = 2 := by
    rw [(CoordSL.rootPB g).finrank]
    exact SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) hpK hgd (by rw [hK])
  have hBsF : ∀ c, c ∈ Bs ↔ ∃ f, ψ (F.tor f) = c := by
    intro c
    constructor
    · intro hc
      obtain ⟨Y, rfl⟩ := hmem c hc
      obtain ⟨f, hf⟩ := F.mem_tor Y hc
      exact ⟨f, by rw [hf]⟩
    · rintro ⟨f, rfl⟩
      exact F.tor_mem f
  have hs : 4 ≤ F.s := by
    have h1 : Nat.card Bs ≤ 3 ^ F.s := by
      have := Nat.card_le_card_of_surjective
        (fun f : Fin F.s → ZMod 3 => (⟨ψ (F.tor f), (hBsF _).mpr ⟨f, rfl⟩⟩ : Bs))
        (fun c => by
          obtain ⟨f, hf⟩ := (hBsF c).mp c.2
          exact ⟨f, Subtype.ext hf⟩)
      rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin F.s),
        Fintype.card_fin] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hctx.pow_four_le_card_bstar.trans h1)
  obtain ⟨β, rfl⟩ := (hBsF b).mp hpair.1
  have hβ : β ≠ 0 := fun h => hpair.2.1 (by rw [h, F.tor_zero, map_one])
  have hL₁ := hpair.2.2.1
  rw [← hG₀] at hL₁
  have hJcomp := hctx.j_isComponentOf_inf
  have hJq : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJcomp.2.2
  have hJG : J ≤ ψ.range := hG₀ ▸ hctx.le_ggG0
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := fun j hj =>
    (Subgroup.mem_inf.mp (hJcomp.1 hj)).2
  obtain ⟨m, hm, g', hg'L, hnc, hgc, hcop⟩ := F.choice_core (Bs := Bs) hK hζo hL hs hψ hBsF hβ
    hL₁ hpair.2.2.2 hctx.d_le_bstar (by rw [hctx.card_d]; norm_num) hJq hJG hJD
    hctx.card_bstar_inf_centralizer_le
  rw [hG₀] at hm
  exact ⟨m, hm, g', hg'L, hnc, hgc, hcop⟩

end Core

section Tag

theorem ggStepTwoChoiceThreeTwoTag_PSp : GGStepTwoChoiceThreeTwoTag .PSp := by
  intro G _ _ p B Bs x L D J n ψ hctx s1 _ b L₁ hpair hp3 _
  subst hp3
  exact choiceTwo_psp (ψ := ψ) hctx s1 hpair

end Tag

end CFSG.StandardType
