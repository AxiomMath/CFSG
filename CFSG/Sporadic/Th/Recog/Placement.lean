module

public import CFSG.Sporadic.Th.Recog.PlacementFacts
public import CFSG.ClassicalInvolution.Solomon73.Commutator
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.ClassBound
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27G2Facts
public import Certificates.Certificate320001
public import Certificates.Certificate320002
public import Certificates.Certificate320004
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Th.Max3.CentA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Recognition.PresentedWords
open CFSG.ClassicalInvolution.Solomon73 (orders_of_mulEquiv exists_cycle_of_mulEquiv)
open CFSG.OddStandard.SmallF3.HarrisU33 (card_inf_centralizer_mul_le mem_iff_of_card_le)
open Place

section Placement


private theorem orderOf_ne_eight {X : Subgroup J} (ψ : ↥X ≃* GL (Fin 3) (ZMod 2)) {g : J}
    (hg : g ∈ X) : orderOf g ≠ 8 := by
  intro h8
  have key : ∀ n : ℕ, (⟨g, hg⟩ : ↥X) ^ n = 1 → 8 ∣ n := fun n h => by
    rw [← h8]
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val h)
  rcases @orders_of_mulEquiv ↥X inferInstance ψ ⟨g, hg⟩ with h | h | h <;> have := key _ h <;>
    omega

private theorem hgen_mem (j : Fin 5) :
    hgen j ∈ Subgroup.closure (Set.range lJ) ⊓ Subgroup.centralizer {hswJ 0} :=
  ⟨hgen_mem_K₀ j, Subgroup.mem_centralizer_singleton_iff.2 (hgen_comm j)⟩

private theorem wprod_hgen_mem (w : List (Fin 5 × Bool)) :
    wprod hgen w ∈ Subgroup.closure (Set.range lJ) ⊓ Subgroup.centralizer {hswJ 0} :=
  CFSG.Certificates.signedProd_mem hgen_mem w

private theorem exists_good
    (hC : Nat.card ↥(Subgroup.closure (Set.range lJ) ⊓ Subgroup.centralizer {hswJ 0}) ≤ 576)
    {X : Subgroup J} (hX0 : X ≤ Subgroup.closure (Set.range lJ))
    (ψ : ↥X ≃* GL (Fin 3) (ZMod 2)) (hv : ∀ j, v j ∈ X) (i : Fin 2) :
    ∃ m ∈ good i, z i m ∈ X := by
  set H := Subgroup.closure (Set.range lJ) ⊓ Subgroup.centralizer {hswJ 0} with hH
  have ha : hswJ 0 ∈ X :=
    v_mul_v_mul_self ▸ X.mul_mem (X.mul_mem (hv 0) (hv 1)) (X.mul_mem (hv 0) (hv 1))
  obtain ⟨κ, hκ3, hκa, hκv⟩ := @exists_cycle_of_mulEquiv ↥X inferInstance ψ ⟨hswJ 0, ha⟩
    ⟨v i, hv i⟩ (Subtype.ext hswJ_zero_mul_self) (Subtype.ext (v_mul_self i))
    (fun h => hswJ_zero_ne_one (congrArg Subtype.val h))
    (fun h => v_ne_one i (congrArg Subtype.val h))
    (fun h => hswJ_zero_ne_v i (congrArg Subtype.val h)) (Subtype.ext (hswJ_zero_comm_v i))
  have k3 : (κ : J) ^ 3 = 1 := by simpa using congrArg Subtype.val hκ3
  have ka : (κ : J) * hswJ 0 * (κ : J)⁻¹ = v i := by simpa using congrArg Subtype.val hκa
  have kv : (κ : J) * v i * (κ : J)⁻¹ = hswJ 0 * v i := by simpa using congrArg Subtype.val hκv
  have hga : (wp i)⁻¹ * κ * hswJ 0 = hswJ 0 * ((wp i)⁻¹ * κ) := by
    have h := wp_conj_a i
    calc (wp i)⁻¹ * κ * hswJ 0 = (wp i)⁻¹ * ((κ : J) * hswJ 0 * (κ : J)⁻¹) * κ := by group
      _ = (wp i)⁻¹ * (wp i * hswJ 0 * (wp i)⁻¹) * κ := by rw [ka, h]
      _ = hswJ 0 * ((wp i)⁻¹ * κ) := by group
  have hgv : (wp i)⁻¹ * κ * v i = v i * ((wp i)⁻¹ * κ) := by
    have h := wp_conj_v i
    calc (wp i)⁻¹ * κ * v i = (wp i)⁻¹ * ((κ : J) * v i * (κ : J)⁻¹) * κ := by group
      _ = (wp i)⁻¹ * (wp i * v i * (wp i)⁻¹) * κ := by rw [kv, h]
      _ = v i * ((wp i)⁻¹ * κ) := by group
  have hgK : (wp i)⁻¹ * κ ∈ Subgroup.closure (Set.range lJ) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (wp_mem_K₀ i)) (hX0 κ.2)
  have hgH : (wp i)⁻¹ * κ ∈ H ⊓ Subgroup.centralizer {v i} :=
    ⟨⟨hgK, Subgroup.mem_centralizer_singleton_iff.2 hga⟩,
      Subgroup.mem_centralizer_singleton_iff.2 hgv⟩
  have h18 := card_inf_centralizer_mul_le H (v i) (List.ofFn (orb i))
    (fun w hw => by
      obtain ⟨r, rfl⟩ := List.mem_ofFn.1 hw
      exact wprod_hgen_mem _)
    (by simpa [List.map_ofFn, Function.comp_def] using orb_nodup i)
  rw [List.length_ofFn] at h18
  have hmem : ∀ q, cent i q ∈ H ⊓ Subgroup.centralizer {v i} := by
    intro q
    have h4 : ∀ u, four i u ∈ H ⊓ Subgroup.centralizer {v i} := by
      have haH : hswJ 0 ∈ H ⊓ Subgroup.centralizer {v i} :=
        ⟨⟨hswJ_zero_mem_K₀, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩,
          Subgroup.mem_centralizer_singleton_iff.2 (hswJ_zero_comm_v i)⟩
      have hvH : v i ∈ H ⊓ Subgroup.centralizer {v i} := by
        have : v i = wp i * hswJ 0 * (wp i)⁻¹ := (wp_conj_a i).symm
        refine ⟨⟨?_, Subgroup.mem_centralizer_singleton_iff.2 (hswJ_zero_comm_v i).symm⟩,
          Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (wp_mem_K₀ i) hswJ_zero_mem_K₀)
          (Subgroup.inv_mem _ (wp_mem_K₀ i))
      intro u
      fin_cases u
      · exact Subgroup.one_mem _
      · exact haH
      · exact hvH
      · exact Subgroup.mul_mem _ haH hvH
    refine Subgroup.mul_mem _ ⟨wprod_hgen_mem _, ?_⟩ (h4 _)
    exact Subgroup.mem_centralizer_singleton_iff.2 (rep_comm i _)
  have hcard : Nat.card ↥(H ⊓ Subgroup.centralizer {v i}) ≤ (List.ofFn (cent i)).length := by
    rw [List.length_ofFn]
    have : Nat.card ↥(H ⊓ Subgroup.centralizer {v i}) * 18 ≤ 576 := by
      rw [mul_comm]; exact h18.trans hC
    omega
  obtain ⟨q, hq⟩ := List.mem_ofFn.1 ((mem_iff_of_card_le _ (List.ofFn (cent i))
    (fun g hg => by obtain ⟨q, rfl⟩ := List.mem_ofFn.1 hg; exact hmem q) (cent_nodup i)
    hcard _).1 hgH)
  set m := (split32 q).1
  set u := (split32 q).2
  have hκ : (κ : J) = z i m * four i u := by
    have : cent i q = (wp i)⁻¹ * κ := hq
    rw [cent] at this
    rw [z, mul_assoc, this, mul_inv_cancel_left]
  have h4X : ∀ u, four i u ∈ X := by
    intro u
    fin_cases u
    · exact X.one_mem
    · exact ha
    · exact hv i
    · exact X.mul_mem ha (hv i)
  have hzX : z i m ∈ X := by
    have : z i m = κ * (four i u)⁻¹ := by rw [hκ, mul_inv_cancel_right]
    rw [this]
    exact X.mul_mem κ.2 (X.inv_mem (h4X u))
  refine ⟨m, ?_, hzX⟩
  rcases coset_cases i m with h | h | h
  · exact h
  · exact absurd (hκ ▸ k3) (h u)
  · exact absurd h (orderOf_ne_eight ψ (X.mul_mem (hv _) hzX))

theorem placement_of_card_le
    (hC : Nat.card ↥(Subgroup.closure (Set.range lJ) ⊓ Subgroup.centralizer {hswJ 0}) ≤ 576)
    (X : Subgroup J) (hX0 : X ≤ Subgroup.closure (Set.range lJ))
    (hX : Nonempty (↥X ≃* GL (Fin 3) (ZMod 2)))
    (hc : hswJ 2 ∈ X) (hdcd : hswJ 3 * hswJ 2 * hswJ 3 ∈ X)
    (hd : ∀ x ∈ X, hswJ 3 * x * (hswJ 3)⁻¹ ∈ X) :
    ∃ i : Fin 2, ∀ (k : Twist) (j : Fin 2), wprod hswJ (xw (k, i) j) ∈ X := by
  obtain ⟨ψ⟩ := hX
  have hv : ∀ j, v j ∈ X := by
    intro j
    fin_cases j
    · exact v_zero ▸ hdcd
    · exact v_one ▸ hc
  obtain ⟨m₀, hm₀, hz₀⟩ := exists_good hC hX0 ψ hv 0
  obtain ⟨m₁, hm₁, hz₁⟩ := exists_good hC hX0 ψ hv 1
  rcases pair_cases hm₀ hm₁ with ⟨x, hx⟩ | h8
  · refine ⟨x, fun k j => ?_⟩
    rw [xw_eq]
    refine CFSG.Certificates.signedProd_mem (fun q => ?_) _
    fin_cases q
    · exact hv 0
    · exact hv 1
    · show z 0 (pair x).1 ∈ X
      rw [hx]
      exact hz₀
    · show z 1 (pair x).2 ∈ X
      rw [hx]
      exact hz₁
  · exact absurd h8 (orderOf_ne_eight ψ (X.mul_mem hz₀ (hd _ (X.mul_mem (hv 0) hz₁))))

end Placement

section PlacementGhat


theorem card_K₀_inf_centralizer_le :
    Nat.card ↥(Subgroup.closure (Set.range lJ) ⊓ Subgroup.centralizer {hswJ 0}) ≤ 576 := by
  obtain ⟨e⟩ := nonempty_K₀_ghat
  let a' : ↥(Subgroup.closure (Set.range lJ)) := ⟨hswJ 0, hswJ_zero_mem_K₀⟩
  have h2 : orderOf (e a') = 2 := by
    rw [@MulEquiv.orderOf_eq ↥(Subgroup.closure (Set.range lJ)) inferInstance
      CFSG.GH74.QTGen4.Recog.G23.Ghat inferInstance e a', Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hswJ_zero_mul_self) hswJ_zero_ne_one
  rw [← CFSG.GH74.GLS.IVK.GHInv.card_centralizer_subtype _ a',
    @CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv ↥(Subgroup.closure (Set.range lJ))
      CFSG.GH74.QTGen4.Recog.G23.Ghat inferInstance inferInstance e a']
  exact (CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three.card_centralizer_of_orderOf_eq_two
    (K := ZMod 3) (Nat.card_zmod 3) h2).le

theorem placement (X : Subgroup J) (hX0 : X ≤ Subgroup.closure (Set.range lJ))
    (hX : Nonempty (↥X ≃* GL (Fin 3) (ZMod 2)))
    (hc : hswJ 2 ∈ X) (hdcd : hswJ 3 * hswJ 2 * hswJ 3 ∈ X)
    (hd : ∀ x ∈ X, hswJ 3 * x * (hswJ 3)⁻¹ ∈ X) :
    ∃ i : Fin 2, ∀ (k : Twist) (j : Fin 2), wprod hswJ (xw (k, i) j) ∈ X :=
  placement_of_card_le card_K₀_inf_centralizer_le X hX0 hX hc hdcd hd

end PlacementGhat

end CFSG.Sporadic.Th.Recog
