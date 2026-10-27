module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.Vol2.Ch11SecAKDe
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.JonesParshallG2Derived
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Quasithin CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.TypeList
open CFSG.Assembly.LowTwoRank

namespace B42R

variable {W : Type} [CommGroup W] [Finite W] {G₁ K₁ : Subgroup (MulAut W)}

theorem finite_mulAut : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

theorem two_le_pRank_of_le (h2 : ∀ y ∈ G₁, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁) {Y : Subgroup (MulAut W)}
    (hY : Y ≤ G₁) (hr : 2 ≤ CFSG.Open.pRank 3 Y) : 2 ≤ CFSG.Open.pRank 3 K₁ := by
  have : Finite (MulAut W) := finite_mulAut
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Y
  have hEK : E ≤ K₁ := by
    intro y hy
    obtain ⟨e, he⟩ := h2 y (hY (hEY hy))
    have hy3 : y ^ 3 = 1 := hE.2 y hy
    have h4 : (4 : ℕ) ^ e % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have hpow : y ^ (2 ^ e * 2 ^ e) = y := by
      rw [← mul_pow, show (2 : ℕ) * 2 = 4 by norm_num, ← Nat.div_add_mod (4 ^ e) 3, h4, pow_add,
        pow_mul, hy3, one_pow, one_mul, pow_one]
    rw [← hpow, pow_mul]
    exact K₁.pow_mem he _
  exact hr.trans (CFSG.SectionRank.le_pRank (by norm_num) hEK hE hcard)

theorem two_le_pRank_range {Γ : Type*} [Group Γ] [Finite Γ] (f : Γ →* MulAut W)
    (hf : Function.Injective f) (hΓ : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Γ)) :
    2 ≤ CFSG.Open.pRank 3 f.range := by
  have : Finite (MulAut W) := finite_mulAut
  rw [MonoidHom.range_eq_map]
  exact hΓ.trans (CFSG.SectionRank.pRank_le_map (by norm_num) f hf ⊤)

theorem two_le_pRank_of_equiv {Γ : Type*} [Group Γ] [Finite Γ] {Y : Subgroup (MulAut W)}
    (e : Γ ≃* ↥Y) (hΓ : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Γ)) :
    2 ≤ CFSG.Open.pRank 3 Y := by
  have h := two_le_pRank_range (Y.subtype.comp e.toMonoidHom)
    (Y.subtype_injective.comp e.injective) hΓ
  have hr : (Y.subtype.comp e.toMonoidHom).range = Y := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rwa [hr] at h

@[expose] def Case5Five (G₁ A : Subgroup (MulAut W)) : Prop :=
  ∃ π : Equiv.Perm (Fin 5) →* ↥(ffJ G₁), (FFModel.symDn 5).RealizesVia (ffJ G₁) ⊤ ⊥ π ∧
    ∃ T : Set (Equiv.Perm (Fin 5)), (∀ t ∈ T, t.IsSwap) ∧ T.Pairwise Commute ∧
      A.subgroupOf (ffJ G₁) = (Subgroup.closure T).map π

theorem cases_of_rank (hB4 : B4Hyp G₁ K₁) (hKG : K₁ ≤ G₁) (h2 : ∀ y ∈ G₁, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁)
    (hr : CFSG.Open.pRank 3 K₁ ≤ 1) (hZ : Subgroup.center ↥K₁ = ⊥) {A : Subgroup (MulAut W)}
    (hconc : B42Conclusion G₁ K₁ A) :
    B42Case1 G₁ K₁ A ∨ B42Case2 G₁ K₁ ∨ Case5Five G₁ A := by
  classical
  have hq : CFSG.IsQuasisimple ↥K₁ := hB4.2.2.1
  have : Nontrivial ↥K₁ := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hJ : ffJ G₁ ≤ G₁ := B6.ffJ_le G₁
  have kill : ∀ Y : Subgroup (MulAut W), Y ≤ G₁ → 2 ≤ CFSG.Open.pRank 3 Y → False :=
    fun Y hY h => absurd (two_le_pRank_of_le h2 hY h) (by omega)
  rcases hconc with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact Or.inl c1
  · exact Or.inr (Or.inl c2)
  · exfalso
    obtain ⟨⟨m, hm, -⟩, -⟩ := c3
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv hm
    exact kill _ hJ (two_le_pRank_of_equiv e FFC.threeRank2_statedSp.pRank_two_le)
  · exfalso
    obtain ⟨⟨m, hm, -, -⟩, -⟩ := c4
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_of_g2Natural hm
    have : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card
      (by have := one_le_of_card_eq_pow hK; omega) hK
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.exists_orderOf_sl2 (p := 3) hK (by
      rw [pow_mul]
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp
        (by simpa using (show 1 ≡ 2 ^ 2 [MOD 3] by decide).pow m))
    have hc := CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.two_le_pRank_cayley hg
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (MulEquiv.subgroupCongr (Alt57Model.quasithinG2_eq_cayleyGroup (K := K)))] at hc
    exact kill _ hJ (two_le_pRank_of_equiv e hc)
  · obtain ⟨⟨m, hm57, π, hπ, T, hT⟩, -⟩ := c5
    rcases hm57 with rfl | rfl
    · exact Or.inr (Or.inr ⟨π, hπ, T, hT⟩)
    · exfalso
      have hinj := hπ.injective_of_faithful (G64.symDn_faithful (by norm_num))
      exact kill _ hJ (two_le_pRank_of_equiv (Γ := Equiv.Perm (Fin 7))
        (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) (FFC.threeRank2_perm (by norm_num)).pRank_two_le)
  · exfalso
    obtain ⟨-, ⟨π, hπ⟩, -⟩ := c6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alt_isSimple (by norm_num)
    obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple (Γ := alternatingGroup (Fin 6)) π hπ.1
    exact kill _ hKG (two_le_pRank_of_equiv e (FFC.threeRank2_alt (by norm_num)).pRank_two_le)
  · exfalso
    obtain ⟨-, -, ⟨α, π, hπ⟩, -⟩ := c7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alt_isSimple (by norm_num)
    obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple (Γ := alternatingGroup (Fin 7)) π hπ.1
    exact kill _ hKG (two_le_pRank_of_equiv e (FFC.threeRank2_alt (by norm_num)).pRank_two_le)
  · exfalso
    obtain ⟨-, -, -, K, hK, hKfin, Γ₀, -, -, hHat, -, π, hπ, -⟩ := c8
    have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
    have e := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    have h1 : Nat.card (Subgroup.center ↥Γ₀) = Nat.card (Subgroup.center ↥K₁) :=
      Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hZ, Subgroup.card_bot, hHat.2.1] at h1
    exact absurd h1 (by norm_num)
  · exfalso
    obtain ⟨-, m, hm, hnat, -⟩ := c9
    obtain ⟨π, hπ⟩ := G64.BinaryNaturalSL.exists_zmod hnat
    have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
    have e := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    rcases hm with rfl | rfl
    · exact kill _ hKG (two_le_pRank_of_equiv e R3c.two_le_pRank_three_statedSL_four_two)
    · exact kill _ hKG (two_le_pRank_of_equiv e R3c.two_le_pRank_three_statedSL_five_two)
  · exfalso
    obtain ⟨⟨π, hπ⟩, -⟩ := c10
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      isSimple_sl_zmod2 4 (by norm_num)
    have : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) :=
      (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.isSimpleGroup
    obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple (Γ := ↥(StatedSL 4 (ZMod 2))) π hπ.1
    exact kill _ hKG (two_le_pRank_of_equiv e R3c.two_le_pRank_three_statedSL_four_two)
  · exfalso
    obtain ⟨-, -, -, -, π, hπ, -⟩ := c11
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      isSimple_sl_zmod2 5 (by norm_num)
    have : IsSimpleGroup ↥(StatedSL 5 (ZMod 2)) :=
      (specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm.isSimpleGroup
    obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple (Γ := ↥(StatedSL 5 (ZMod 2))) π hπ.1
    exact kill _ hKG (two_le_pRank_of_equiv e R3c.two_le_pRank_three_statedSL_five_two)

end B42R

end CFSG.Quasithin.H13.L32A.C
