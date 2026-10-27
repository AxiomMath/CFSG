module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSL3Module
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSL3Param
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.X7a CFSG.RankThree.FFModules
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix

theorem exists_cover_of_isSL3
    {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥) {e : ℕ} (hS : IsSL3 ↥L e) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL(3, F) →* ↥L),
      Nat.card F = 2 ^ e ∧ CFSG.QuasithinUnique.Setup.X7Sec.Cover φ := by
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  obtain ⟨-, -, -, hJ⟩ := hirr
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hS.1.1
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.QuasithinUnique.Setup.Family.odd_card_center_of_irreducible
      (fun w => by rw [← pow_two]; exact hI w) fun U hU => hJ U hU bot_le le_top
  rcases hS.2 with ⟨-, hmodel⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have he : 1 ≤ e := by
      obtain ⟨-, K, iK, iKfin, hK, -⟩ := hmodel
      by_contra h
      have h0 : e = 0 := by omega
      rw [h0, pow_zero] at hK
      exact (Finite.one_lt_card (α := K)).ne' hK
    exact CFSG.QuasithinUnique.Setup.X7Sec.exists_cover_of_model hperf hodd he hmodel
  all_goals exact absurd h0 (by norm_num)

theorem k14_5SmallFor_sl3 :
    K14_5SmallFor fun L _ e => IsSL3 L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  obtain ⟨F, _, _, φ, hFcard, hφ⟩ := exists_cover_of_isSL3 hI hirr hS
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard
  have hF : Fintype.card F = 2 ^ e := by rw [← Nat.card_eq_fintype_card, hFcard]
  have hne : n = e := nParam_eq_of_cover hI hq hirr hS hF hφ hPL hpar hinf hN
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := I) fun v => by
    rw [← pow_two]
    exact hI v
  have hirr' := hirr
  obtain ⟨hlt, -, -, hJ⟩ := hirr'
  have : Nontrivial I := by
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    exact ⟨⟨v, 1, fun h => hv (h ▸ Subgroup.one_mem _)⟩⟩
  have : Nontrivial W := by
    obtain ⟨v, hv⟩ := exists_ne (1 : I)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  set ρ := CFSG.Quasithin.B42SL3.repOf θ φ with hρdef
  have hirrρ : ρ.IsIrreducible :=
    CFSG.Quasithin.B42SL3.repOf_irreducible θ (fun U hU => hJ U hU bot_le le_top) hφ.surjective
  have hker := CFSG.Quasithin.B42SL3.repOf_ker θ hφ
  have ht₀ : (up3 (0 : F) 0 1) * up3 0 0 1 = 1 := by
    rw [up3_mul, ← up3_zero]
    congr 1
    · simp
    · simp
    · exact CharTwo.add_self_eq_zero 1
  have hφt₀ : φ (up3 0 0 1) ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := hφ.ker_le _ h
    have h01 := congrFun (congrFun hc 0) 1
    simp [up3_coe, upMat, Matrix.scalar_apply] at h01
  have hnt : ∃ x, ρ x ≠ 1 := by
    refine ⟨up3 0 0 1, fun h => hφt₀ ?_⟩
    have h1 : binPsi θ ((φ (up3 0 0 1) : ↥L) : MulAut I) = 1 := by
      refine LinearEquiv.ext fun w => ?_
      have := LinearMap.congr_fun h w
      rw [hρdef, CFSG.Quasithin.B42SL3.repOf_apply] at this
      exact this
    exact Subtype.ext ((binPsi θ).injective (h1.trans (map_one _).symm))
  have hev : Even (Nat.card ↥X) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (φ (up3 0 0 1)) = 2 :=
      orderOf_eq_prime (by rw [pow_two, ← map_mul, ht₀, map_one]) hφt₀
    have hdvdL : 2 ∣ Nat.card ↥L := hord ▸ orderOf_dvd_natCard _
    exact even_iff_two_dvd.2 (hdvdL.trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  set a : W ≃ₗ[ZMod 2] W := binPsi θ t with hadef
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := by rw [hadef, ← map_mul, htt, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    have h1 : t = 1 := (binPsi θ).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have haN : ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y := fun x =>
    CFSG.Quasithin.B42SL3.intertwines_map θ hφ.surjective (Q := zpowers t)
      (zpowers_le.mpr (hXN htX)) a (Subgroup.mem_map_of_mem _ (mem_zpowers t)) x
  have hrk : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ e + 1 := by
    have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    let t' : ↥X := ⟨t, htX⟩
    have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
    have h1 := finrank_quotient_fixSub_subRep θ X (zpowers t')
    rw [MonoidHom.map_zpowers, CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147.fixSub_zpowers_eq_ker
      (subRep θ X) ht'] at h1
    have h2 := (LinearMap.ker (subRep θ X t' - 1)).finrank_quotient_add_finrank
    have h3 := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - 1)
    have hsame : subRep θ X t' - 1 = a.toLinearMap - 1 := rfl
    rw [hsame] at h1 h2
    have h4 : rkIdx (fixV (zpowers (X.subtype t'))) = E3.mParam X := htm
    omega
  obtain ⟨ψ, hψ, E, hE⟩ := natural_of_rank_le hF (by omega) ρ hirrρ hnt hker a ha2 ha1 haN hrk
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hρx : ∀ w, ρ x w = w := fun w => by
      rw [hρdef, CFSG.Quasithin.B42SL3.repOf_apply, hx, OneMemClass.coe_one, map_one]
      rfl
    have hψx : ψ x = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one]
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      obtain ⟨w, rfl⟩ := E.surjective v
      rw [← hE x w, hρx, Matrix.one_mulVec]
    rw [← hψ x, hψx, map_one]
  let φ' : SL(3, F) ≃* ↥L := MulEquiv.ofBijective φ ⟨hφinj, hφ.surjective⟩
  let ψe : SL(3, F) ≃* SL(3, F) :=
    { ψ with invFun := ψ, left_inv := hψ, right_inv := hψ }
  let Θ : ↥L ≃* ↥(StatedSL 3 F) :=
    φ'.symm.trans (ψe.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F))
  have hreal : (FFModel.nat (StatedSL 3 F)).Realizes L ⊤ ⊥ := by
    refine realizes_nat_of_equiv θ Θ E fun l w => ?_
    obtain ⟨x, rfl⟩ := φ'.surjective l
    have h1 : binPsi θ ((φ' x : ↥L) : MulAut I) w = ρ x w := rfl
    have hΘ : Θ (φ' x) = CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F (ψ x) := by
      simp only [Θ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rfl
    rw [h1, hE x w, hΘ]
    rfl
  have hSLn : IsSLn ↥L 3 e := ⟨F, inferInstance, inferInstance, hFcard,
    ⟨φ'.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)⟩⟩
  have hBin : BinaryNaturalSL L ⊤ ⊥ 3 e := ⟨F, inferInstance, inferInstance, hFcard, hreal⟩
  exact Or.inl ⟨e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hSLn, hBin⟩)))), Or.inl hne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
