module

public import CFSG.RankThree.PartTwo.Sec21.Item22Sec7
public import CFSG.RankThree.PartOne.S12.InputsCT
import CFSG.RankThree.PartTwo.Sec21.Item22L2
import CFSG.RankThree.PartOne.S12.AmbientTransport
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartOne.CTP.PhanBridge
import CFSG.RankThree.PartOne.CTP.PhanFour
import CFSG.RankThree.PartOne.CTP.UnitaryEdge

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SUid)
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem phan_ctTorusCondition [Finite G] {r : ℕ} {E : Subgroup G} {K : Fin r → Subgroup G}
    (h : IsChainSystem r E K) : PartOne.CTTorusCondition 3 E K := by
  have key : ∀ (H : Subgroup G) (c : ℕ), H ≤ E → Nat.card E = c * Nat.card H →
      H.relIndex E = c := by
    intro H c hHE hc
    have h1 := Subgroup.relIndex_mul_card H E
    rw [inf_eq_left.mpr hHE, hc] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  refine ⟨fun i => ⟨h.split i, key _ 3 inf_le_left (h.index i)⟩, fun i j hij => ?_⟩
  exact key _ (3 ^ 2) inf_le_left (by rw [h.index₂ i j hij]; norm_num)

theorem phan_centrallyUThree_of_isSUThree {Y : Subgroup G} {m : ℕ} (hm : 1 < m)
    (h : IsSUThree Y m) : PartOne.CentrallyUThree m ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine Or.inl ⟨GaloisField 2 (2 * m), inferInstance, inferInstance, hF,
      ⟨e.trans (MulEquiv.subgroupCongr ?_)⟩⟩
    rw [PartOne.statedSU_eq_closure_det]
    rfl
  · have hne : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := by
      intro h
      have h2 : 2 ^ m = 2 := congrArg Prod.snd h
      have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Or.inr ⟨⟨Nat.prime_two, by omega, le_rfl, hne⟩, GaloisField 2 (2 * m), inferInstance,
      inferInstance, hF, ⟨e.trans ((MulEquiv.subgroupCongr
        (PartOne.projImage_statedSU_eq_projSU 3 2 m).symm).trans
        (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm)⟩⟩

theorem nonempty_equiv_projSU_of_phanSystem
    {X : Type} [Group X] {n m p : ℕ}
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ m + 1)
    {E : Subgroup X} [CFSG.IsElementaryAbelian p E] {U : Fin n → Subgroup X}
    (hgen : ⨆ i, U i = ⊤) (hSL : ∀ i, Nonempty (SL(2, GaloisField 2 m) ≃* U i))
    (hcomm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hadj : ∀ i j : Fin n, (i : ℕ) + 1 = j → PartOne.CentrallyUThree m ↥(U i ⊔ U j))
    (htor : PartOne.CTTorusCondition p E U) :
    Nonempty (X ⧸ Subgroup.center X ≃* projSU (n + 1) 2 m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hF : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
  have hF₀ : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hfd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m (GaloisField 2 (2 * m)) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨σ⟩ := PartOne.CTP.exists_suid_two_equiv_sl hF hF₀
  have hW : CFSG.ClassicalInvolution.Phan.WeakPhanA (GaloisField 2 (2 * m)) 2 m n U
      (fun i j => U i ⊔ U j) :=
    { iso := fun i => ⟨σ.trans (hSL i).some⟩
      join := fun i j _ => rfl
      comm := hcomm
      pair := by
        intro i j hij
        have hne : i ≠ j := by
          rintro rfl
          omega
        obtain ⟨θ₀, hsurj, hker₀⟩ :=
          PartOne.CTP.exists_su3_surj_of_centrallyUThree hF (hadj i j hij.symm)
        let θ : SUid (unitaryInvolution (GaloisField 2 (2 * m)) 2 m) 3 →* X :=
          (U i ⊔ U j).subtype.comp θ₀
        have hrange : θ.range = U i ⊔ U j := by
          rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
            Subgroup.range_subtype]
        have hker : θ.ker ≤ Subgroup.center
            (SUid (unitaryInvolution (GaloisField 2 (2 * m)) 2 m) 3) :=
          fun x hx => hker₀ (Subtype.ext hx)
        have hE : PartOne.CTP.EdgeTorus p E (U i) (U j) :=
          ⟨(htor.1 i).1, (htor.1 i).2, (htor.1 j).1, (htor.1 j).2, htor.2 i j hne⟩
        obtain ⟨c, hc1, hc2⟩ := PartOne.CTP.unitary_edge_standardPair hfd hq hp hp2 hpq θ hker
          hE hrange.symm hF₀ hF₀ (hSL i).some (hSL j).some
        exact ⟨θ, c, hrange, hker, Or.inl ⟨hc1, hc2⟩⟩
      gen := hgen }
  obtain ⟨θ, hθs, hθk⟩ :=
    PartOne.CTP.weakPhan_recognition_of_four_le (GaloisField 2 (2 * m)) 2 m hF hq hn hW
  exact PartOne.projSU_of_statedClassicalModel
    (PartOne.CTP.statedClassicalModel_psu_of_surjective hF hq (by omega) θ hθs hθk)

theorem phanChain :
    PhanChain := by
  intro G _ _ r E K m hr hm hodd hC hK hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKI : ∀ i, K i ≤ ⨆ i, K i := fun i => le_iSup K i
  have hEI : E ≤ ⨆ i, K i := hC.le
  have hE : CFSG.IsElementaryAbelian 3 E :=
    { toIsMulCommutative := hC.elem.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hC.elem.2 x x.2) }
  have : CFSG.IsElementaryAbelian 3 (E.subgroupOf (⨆ i, K i)) :=
    PartOne.isElementaryAbelian_of_equiv (Subgroup.subgroupOfEquivOfLe hEI).symm hE
  refine nonempty_equiv_projSU_of_phanSystem (E := E.subgroupOf (⨆ i, K i))
    (U := fun i => (K i).subgroupOf (⨆ i, K i)) (by omega) (by omega) Nat.prime_three
    (by norm_num) (by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hodd)
    (PartOne.iSup_subgroupOf_eq_top hKI rfl) (fun i => ?_) (fun i j hij x hx y hy => ?_)
    (fun i j hij => ?_) (PartOne.ctTorusCondition_subgroupOf hEI hKI (phan_ctTorusCondition hC))
  · exact ⟨(projSLTwoEquivSL (GaloisField 2 m)).symm.trans
      ((hK i).some.symm.trans (Subgroup.subgroupOfEquivOfLe (hKI i)).symm)⟩
  · exact Subtype.ext (hC.commute i j hij (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
      (Subgroup.mem_subgroupOf.mp hy))
  · obtain ⟨e⟩ := PartOne.nonempty_sup_subgroupOf_equiv (hKI i) (hKI j)
    exact PartOne.centrallyUThree_of_equiv e.symm
      (phan_centrallyUThree_of_isSUThree hm (hU i j hij))

end CFSG.RankThree.PartTwo.Sec21
