module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly

variable {d p : ℕ} {K : Type} [Field K] [Finite K]

theorem card_le_of_subset_conjAut (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hpd : Nat.Coprime p d) {X : Subgroup (MulAut (projectiveSL d K))} (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K)) :
    Nat.card X ≤ p ^ (d - 1) :=
  (exists_diagonalizing_slLift hp hpK hd hpd X
    (fun _ hx _ hy => TableB.IsElemAbelian.comm hX hx hy) hX.2
    (fun _ hx => hXI hx)).choose_spec.2.1

theorem linearAutGroup_normal (hd : 3 ≤ d) : (linearAutGroup d K).Normal :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_normal_of_three_le hd

theorem card_le_mul_card_inf_linear (hp : p.Prime) (hp2 : p ≠ 2) (hd : 3 ≤ d)
    {Eh : Subgroup (MulAut (projectiveSL d K))} (hEh : IsElemAbelian p Eh) :
    Nat.card Eh ≤ p * Nat.card (Eh ⊓ linearAutGroup d K : Subgroup _) := by
  have := Fact.mk hp
  have : (linearAutGroup d K).Normal := linearAutGroup_normal hd
  obtain ⟨g, -, hgen⟩ := (standard_outer_quotients (K := K) (n := d)).2.2.2.2.2.1
  have hEhE : ∀ x ∈ Eh, x ∈ semilinearAutGroup d K := by
    intro x hx
    apply CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
      hd
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hEh.2 x hx)) with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.odd_of_ne_two hp2
  let f : Eh →* MulAut (projectiveSL d K) ⧸ linearAutGroup d K :=
    (QuotientGroup.mk' (linearAutGroup d K)).comp Eh.subtype
  have hrange : f.range ≤ Subgroup.zpowers (QuotientGroup.mk' (linearAutGroup d K) g) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := hgen x (hEhE x x.2)
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk' (linearAutGroup d K) g) ^ (-k) =
      QuotientGroup.mk' (linearAutGroup d K) (x : MulAut (projectiveSL d K))
    rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      _root_.zpow_neg,
      inv_inv]
    exact hk
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hcyc : IsCyclic f.range := by
    let e := Subgroup.subgroupOfEquivOfLe hrange
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hrange_le : Nat.card f.range ≤ p := by
    refine TableB.card_le_of_isCyclic hp.pos hcyc ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (by simpa using hEh.2 x x.2)
    rw [this, map_one]
  have hker_le : Nat.card f.ker ≤ Nat.card (Eh ⊓ linearAutGroup d K : Subgroup _) := by
    refine Nat.card_le_card_of_injective
      (fun x : f.ker => (⟨((x : Eh) : MulAut (projectiveSL d K)), (x : Eh).2,
        (QuotientGroup.eq_one_iff _).mp x.2⟩ : (Eh ⊓ linearAutGroup d K : Subgroup _))) ?_
    intro x y hxy
    have h1 := congrArg (fun z : (Eh ⊓ linearAutGroup d K : Subgroup (MulAut (projectiveSL d K))) =>
      (z : MulAut (projectiveSL d K))) hxy
    exact Subtype.ext (Subtype.ext h1)
  calc Nat.card Eh = Nat.card f.range * Nat.card f.ker := (TableB.card_range_mul_card_ker f).symm
    _ ≤ p * Nat.card (Eh ⊓ linearAutGroup d K : Subgroup _) := Nat.mul_le_mul hrange_le hker_le

theorem ggBstarBound_coprime (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 3 ≤ d) (hpd : Nat.Coprime p d) :
    GGBstarBound p (d - 1) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have h1 := card_le_mul_card_inf_linear hp hp2 hd hEh
  have h2 : Nat.card (Eh ⊓ linearAutGroup d K : Subgroup _) ≤ p ^ (d - 1) :=
    card_le_of_subset_conjAut hp hpK (by omega) hpd (TableB.isElemAbelian_mono hEh inf_le_left)
      (fun x hx => mem_linearAutGroup_iff.mp hx.2)
  have h4 : p ^ (d + 1) ≤ Nat.card Eh :=
    calc p ^ (d + 1) = p ^ 2 * p ^ (d - 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
  have h5 : Nat.card Eh ≤ p ^ d :=
    calc Nat.card Eh ≤ p * Nat.card (Eh ⊓ linearAutGroup d K : Subgroup _) := h1
      _ ≤ p * p ^ (d - 1) := Nat.mul_le_mul_left _ h2
      _ = p ^ d := by rw [← pow_succ']; congr 1; omega
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h4.trans h5)
  omega

theorem ggBstarBound_of_card_lt {R : Type} [Group R] {I : Set (MulAut R)} {r : ℕ}
    (h : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3) : GGBstarBound p r R I := by
  intro Eb Eh hEbI hEb _ h3 _ _ _
  exact absurd h3 (not_le.mpr (h Eb hEbI hEb))

theorem ggBstarBound_small (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d) (hd3 : d ≤ 3)
    (hpd : Nat.Coprime p d) :
    GGBstarBound p 0 (projectiveSL d K) (Set.range (conjAut d K)) :=
  ggBstarBound_of_card_lt fun _ hXI hX =>
    (card_le_of_subset_conjAut hp hpK hd hpd hX hXI).trans_lt
      (Nat.pow_lt_pow_right hp.one_lt (by omega))

end CFSG.StandardType.TypeA
