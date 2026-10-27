module

public import CFSG.RankThree.PartTwo.Sec21.U4FourGroupLines
public import CFSG.RankThree.PartTwo.Sec21.Item228Closed
public import CFSG.RankThree.PartTwo.CTU6.ExtCU
public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRank229
public import CFSG.RankThree.PartTwo.Sec21.CurtisTitsBridge
public import CFSG.RankThree.PartTwo.Sec21.Item2131One
public import CFSG.RankThree.PartTwo.Sec21.Item228U54

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open URoots (V3 centerVec apply_coord coord_mul coord_pow coord_center_mem_commOf
  card_zpowers_coord mem_centralizer_sup_of_fixed)

variable {G : Type} [Group G]

theorem commute_kOf_of_swapRefl_lines [Finite G] (h612 : Item612Sec21) (h222 : Item222)
    (h228 : Item228) (hKW : KOfWellDefinedAll)
    (hU4 : ∀ b : ℕ, 0 < b → Even b → U4FourGroupLines b)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (hD : coordGL f '' dStar A = swapRefl)
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) (hc : ψ * φ = φ * ψ) :
    ∀ x ∈ kOf A φ, ∀ y ∈ kOf A ψ, x * y = y * x := by
  have hK := hKW G A E U c L hpair
  obtain ⟨-, hX2, -⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  have hcases : ⁅kOf A φ, kOf A ψ⁆ = ⊥ ∨ ∃ b : ℕ, 0 < b ∧ Even b ∧
      Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 b) := by
    rcases hX2 hc with hb | ⟨-, m, hm0, hm4, -, -, eY, -⟩ | ⟨-, -, eY, -⟩
    · exact Or.inl hb
    · exact Or.inr ⟨m / 2, by omega, ⟨m / 4, by omega⟩, eY⟩
    · exact Or.inr ⟨2, by norm_num, even_two, eY⟩
  rcases hcases with hb | ⟨b, hb0, hbe, eY⟩
  · intro x hx y hy
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  exfalso
  set Y : Subgroup G := kOf A φ ⊔ kOf A ψ with hYdef
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hsw : ∀ d ∈ dStar A, coordGL f d ∈ swapReflList := fun d hd =>
    mem_swapReflList_of_mem_swapRefl (hD ▸ ⟨d, hd, rfl⟩)
  have hMN : coordGL f φ ≠ coordGL f ψ := fun h => hne (coordGL_injective f h).symm
  have hMNc : coordGL f φ * coordGL f ψ = coordGL f ψ * coordGL f φ := by
    rw [← map_mul, ← map_mul, hc]
  obtain ⟨hzM, hzN, hu0, hspan, hnot⟩ :=
    commPairFacts_of_mem_swapRefl _ (hsw φ hφ) _ (hsw ψ hψ) hMN hMNc
  set M : Mat3 := ((coordGL f φ : GL (Fin 3) (ZMod 3)) : Mat3) with hM
  set N : Mat3 := ((coordGL f ψ : GL (Fin 3) (ZMod 3)) : Mat3) with hN
  have hwM : ((f (Multiplicative.ofAdd (centerVec M)) : A) : G) ∈ kOf A φ :=
    map_commOf_le_kOf h222 hpair hK hφ ⟨_, coord_center_mem_commOf f φ, rfl⟩
  have hwN : ((f (Multiplicative.ofAdd (centerVec N)) : A) : G) ∈ kOf A ψ :=
    map_commOf_le_kOf h222 hpair hK hψ ⟨_, coord_center_mem_commOf f ψ, rfl⟩
  have hzY : ((f (Multiplicative.ofAdd (fixVec M N)) : A) : G) ∈
      Subgroup.centralizer (Y : Set G) :=
    mem_centralizer_sup_of_fixed h222 hpair hK hφ hψ _
      ⟨(mem_fixedSubgroupOf φ _).mpr (by rw [apply_coord, ← hM, hzM]),
        (mem_fixedSubgroupOf ψ _).mpr (by rw [apply_coord, ← hN, hzN])⟩
  have hdec : ∀ a : A, ∃ k : ZMod 3, ∃ y : A, (y : G) ∈ Y ∧
      a = f (Multiplicative.ofAdd (k • fixVec M N)) * y := by
    intro a
    obtain ⟨k, α, β, hv⟩ := hspan (Multiplicative.toAdd (f.symm a))
    refine ⟨k, f (Multiplicative.ofAdd (centerVec M)) ^ α.val *
      f (Multiplicative.ofAdd (centerVec N)) ^ β.val, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
      exact Y.mul_mem (Y.pow_mem (Subgroup.mem_sup_left hwM) _)
        (Y.pow_mem (Subgroup.mem_sup_right hwN) _)
    · have ha : a = f (Multiplicative.ofAdd (Multiplicative.toAdd (f.symm a))) := by simp
      rw [coord_pow, coord_pow, coord_mul, coord_mul, ← add_assoc, ← hv, ← ha]
  have huY : ((f (Multiplicative.ofAdd (centerVec M + centerVec N)) : A) : G) ∈ Y := by
    rw [← coord_mul, Subgroup.coe_mul]
    exact Y.mul_mem (Subgroup.mem_sup_left hwM) (Subgroup.mem_sup_right hwN)
  set ℓ : Subgroup G :=
    Subgroup.zpowers ((f (Multiplicative.ofAdd (centerVec M + centerVec N)) : A) : G) with hℓ
  have hℓF : ℓ ≤ A ⊓ Y := Subgroup.zpowers_le.mpr ⟨Subtype.prop _, huY⟩
  have hAYe : IsElemAbelian 3 (A ⊓ Y) :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
      (hAe.1.is_comm.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩))⟩⟩, fun x hx => hAe.2 x hx.1⟩
  obtain ⟨V, hVY, hVe, hV4, hFN, hFC⟩ := hU4 b hb0 hbe G Y eY (A ⊓ Y) ℓ inf_le_right hAYe hℓF
    (card_zpowers_coord f hu0)
  have hzV : ∀ k : ZMod 3, ((f (Multiplicative.ofAdd (k • fixVec M N)) : A) : G) ∈
      Subgroup.centralizer (V : Set G) := by
    intro k
    rw [← coord_pow, Subgroup.coe_pow]
    exact Subgroup.pow_mem _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVY) hzY) _
  have hVA : V ∈ fourGroups A := by
    refine mem_fourGroups_iff.mpr ⟨fun a ha => ?_, hVe, hV4⟩
    obtain ⟨k, y, hyY, hay⟩ := hdec ⟨a, ha⟩
    have hay' : a = ((f (Multiplicative.ofAdd (k • fixVec M N)) : A) : G) * y :=
      congrArg Subtype.val hay
    rw [hay']
    exact Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ (hzV k))
      (hFN ⟨y.2, hyY⟩)
  obtain ⟨a, haV, hdiag⟩ := exists_bodyDiag_of_fourGroup h612 h222 hpair hA27 f hD hVA
  obtain ⟨k, y, hyY, hay⟩ := hdec a
  have hyV : (y : G) ∈ Subgroup.centralizer (V : Set G) := by
    have hy : (y : G) = ((f (Multiplicative.ofAdd (k • fixVec M N)) : A) : G)⁻¹ * a := by
      rw [hay, Subgroup.coe_mul, inv_mul_cancel_left]
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hzV k)) haV
  have hyℓ : (y : G) ∈ ℓ := hFC ▸ ⟨⟨y.2, hyY⟩, hyV⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hyℓ
  have hyj : y = f (Multiplicative.ofAdd ((j : ZMod 3) • (centerVec M + centerVec N))) := by
    apply Subtype.ext
    have hsm : ((j : ZMod 3) • (centerVec M + centerVec N)) = j • (centerVec M + centerVec N) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
    rw [← hj, hsm, ofAdd_zsmul, map_zpow, Subgroup.coe_zpow]
  have hcoord : Multiplicative.toAdd (f.symm a) =
      (j : ZMod 3) • (centerVec M + centerVec N) + k • fixVec M N := by
    rw [hay, hyj, coord_mul, MulEquiv.symm_apply_apply, toAdd_ofAdd, add_comm]
  exact hnot (j : ZMod 3) k (hcoord ▸ hdiag)

theorem rank3II_22_9_of_lines (h2130 : Item2130) (h2131 : Item2131One) (h222 : Item222)
    (h228 : Item228) (hKW : KOfWellDefinedAll) (h76 : CurtisTitsRankThree)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h612 : Item612Sec21)
    (hR4 : Item229UnitaryRoots) (hZ : CentralExtensionTrivial229)
    (hLR : LocalRankLowerBound229) : Item229 := by
  intro G _ _ A E U c L hpair hA27
  have hK := hKW G A E U c L hpair
  exact item229_of_kOf_facts h2130 h2131 h222 h228 hKW h76 hR4 hZ hLR hpair hA27
    (fun φ hφ ψ hψ h3 => exists_kOf_sup_SL3' h222 h228 h45 h66 hpair hA27 hK hφ hψ h3)
    (fun f hS φ hφ ψ hψ hne hc => commute_kOf_of_swapRefl_lines h612 h222 h228 hKW
      (fun _ hb hbe => U4FourLines.u4FourGroupLines hb hbe) hpair hA27 f hS hφ hψ hne hc)

theorem rank3II_22_9_of_items_lines
    (h2130 : Item2130) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (h228 : Item228) (hKW : KOfWellDefinedAll) (h612 : Item612Sec21)
    (hZ : CentralExtensionTrivial229) : Item229 :=
  have h2131 : Item2131One := item2131One_of h2130 h222 h45 h66
  rank3II_22_9_of_lines h2130 h2131 h222 h228 hKW (curtisTitsRankThree_of CTU6.extCurtisTitsCThreeU) h45 h66 h612
    (item229UnitaryRoots_of_item228 h2131 h222 h228 hKW) hZ
    KFacts.KS21LocalRank.localRankLowerBound229

end CFSG.RankThree.PartTwo.Sec21
