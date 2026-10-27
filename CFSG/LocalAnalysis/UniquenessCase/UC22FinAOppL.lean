module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem opp_eq_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 (Opp p H))) : ⁅Opp p H, Opp p H⁆ = Opp p H := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (Subgroup.commutator_le_self _) ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨hxH, k, hk⟩
  have hxR : x ∈ Opp p H := Subgroup.subset_closure ⟨hxH, k, hk⟩
  let π : ↥(Opp p H) →* Bar2 (Opp p H) := QuotientGroup.mk' (CFSG.pCore 2 ↥(Opp p H))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let D : Subgroup ↥(Opp p H) := _root_.commutator ↥(Opp p H)
  have hDn : D.Normal := inferInstanceAs (_root_.commutator ↥(Opp p H)).Normal
  have hDmap : D.map π = ⊤ := by
    change (_root_.commutator ↥(Opp p H)).map π = ⊤
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ,
      ← _root_.commutator_def]
    exact hq.1
  let x' : ↥(Opp p H) := ⟨x, hxR⟩
  obtain ⟨c, hcD, hc⟩ := Subgroup.mem_map.mp (hDmap ▸ Subgroup.mem_top (π x') :
    π x' ∈ D.map π)
  have hker : c⁻¹ * x' ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hc, inv_mul_cancel]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(Opp p H)))
    (⟨c⁻¹ * x', by simpa [π] using hker⟩ : ↥(CFSG.pCore 2 ↥(Opp p H)))
  rw [Subgroup.orderOf_mk] at hn
  have hquot : (QuotientGroup.mk' D) x' = (QuotientGroup.mk' D) (c⁻¹ * x') := by
    have h : x' = c * (c⁻¹ * x') := by group
    conv_lhs => rw [h]
    rw [map_mul, show (QuotientGroup.mk' D) c = 1 from (QuotientGroup.eq_one_iff c).mpr hcD,
      one_mul]
  have h1 : orderOf ((QuotientGroup.mk' D) x') ∣ p ^ k := by
    have : orderOf x' = p ^ k := (Subgroup.orderOf_mk x hxR).trans hk
    rw [← this]
    exact orderOf_map_dvd (QuotientGroup.mk' D) x'
  have h2 : orderOf ((QuotientGroup.mk' D) x') ∣ 2 ^ n := by
    rw [hquot]
    exact hn ▸ orderOf_map_dvd (QuotientGroup.mk' D) (c⁻¹ * x')
  have hcop : Nat.Coprime (p ^ k) (2 ^ n) :=
    Nat.Coprime.pow k n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hone : orderOf ((QuotientGroup.mk' D) x') = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hx'D : x' ∈ D := (QuotientGroup.eq_one_iff x').mp (by simpa using orderOf_eq_one_iff.mp hone)
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨x', hx'D, rfl⟩

theorem opp_sup_mem_hSet (D : Data G) {p : ℕ} {H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    {L : Subgroup G} (hL : L ∈ calL D.T D.M) (hLR : L ≤ Opp p H) :
    Opp p H ⊔ D.T ∈ hSet D.T D.M := by
  have hRH : Opp p H ≤ H := pElementSubgroup_le p H
  have hSH : Opp p H ⊔ D.T ≤ H := sup_le hRH hH.1
  have hP2 : pCoreOf 2 H ≤ pCoreOf 2 (Opp p H ⊔ D.T) :=
    uc22p20b_le_pCoreOf ((uc22p20b_pCoreOf_le_T D hH.1).trans le_sup_right)
      (uc22p20b_isPGroup_pCoreOf H) fun k hk x hx =>
        uc22p20b_conj_mem_pCoreOf_self (hSH hk) hx
  refine ⟨le_sup_right, fun h => uc22p20i_not_le_M D hL (hLR.trans (le_sup_left.trans h)), ?_⟩
  intro x ⟨hxS, hxC⟩
  refine hP2 (hH.2.2 ⟨hSH hxS, ?_⟩)
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hP2)) hxC

theorem opp_mem_calL (D : Data G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) (hq : CFSG.Open.IsQuasisimple (Bar2 (Opp p H))) {L : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hLR : L ≤ Opp p H) : Opp p H ∈ calL D.T D.M := by
  have hperf := opp_eq_commutator hp hp2 hq
  have hTN : D.T ≤ normalizer (Opp p H : Set G) := hH.1.trans (le_normalizer_pElementSubgroup p H)
  refine ⟨hTN, hperf, opp_sup_mem_hSet D hH hL hLR, Opp p H, ⟨IsSubnormal.refl _, hperf, hq⟩, ?_⟩
  have : Nonempty ↥D.T := ⟨⟨1, D.T.one_mem⟩⟩
  have hmap : ∀ t : ↥D.T, (Opp p H).map (MulAut.conj (t : G)).toMonoidHom = Opp p H :=
    fun t => Subgroup.mem_normalizer_iff_map_conj_eq.1 (hTN t.2)
  simp only [hmap, iSup_const]
