module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem unitHeart_noInternal {N : ℕ} (h3 : 3 ∣ N) (S : Finset (Fin N)) (hS : 4 ≤ S.card)
    (vx : ↥(UnitRaw.heart N)) (hvx : vx ≠ 0)
    (hcent : UnitRaw.centH S = Submodule.span (ZMod 3) {vx})
    (hin : vx ∈ UnitRaw.insideH S) : False := by
  classical
  have hvc : vx ∈ UnitRaw.centH S := by
    rw [hcent]
    exact Submodule.mem_span_singleton_self vx
  obtain ⟨w, hwv, hw0, hws⟩ := (UnitRaw.mem_inside_iff S (vx : UnitRaw.Vfull N)).1 hin
  obtain ⟨w', hw'v, hw'c⟩ := (UnitRaw.mem_cent_iff S (vx : UnitRaw.Vfull N)).1 hvc
  have hdiff : w - w' ∈ UnitRaw.oneLine N := by
    have h : (UnitRaw.oneLine N).mkQ w = (UnitRaw.oneLine N).mkQ w' := hwv.trans hw'v.symm
    exact (Submodule.Quotient.eq _).1 h
  obtain ⟨c, hc⟩ := (UnitRaw.mem_oneLine _).1 hdiff
  have hconst : ∀ i ∈ S, ∀ j ∈ S, w i = w j := by
    intro i hi j hj
    have h1 : w i = w' i + c := by
      have := congrFun hc i
      simp only [Pi.sub_apply] at this
      linear_combination this
    have h2 : w j = w' j + c := by
      have := congrFun hc j
      simp only [Pi.sub_apply] at this
      linear_combination this
    rw [h1, h2, hw'c i hi j hj]
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨i0, hi0⟩ := hSne
  set lam : ZMod 3 := w i0 with hlam
  have hwdef : ∀ i, w i = if i ∈ S then lam else 0 := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact hconst i hi i0 hi0
    · rw [if_neg hi]
      exact hw0 i hi
  have hsum : ∑ i, w i = (S.card : ZMod 3) * lam := by
    simp_rw [hwdef]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hvx
    have hw : w = 0 := by
      funext i
      rw [hwdef i, h0]
      simp
    have : (vx : UnitRaw.Vfull N) = 0 := by rw [← hwv, hw, map_zero]
    exact Subtype.ext this
  have hS3 : (S.card : ZMod 3) = 0 := by
    have := hws
    rw [hsum] at this
    exact (mul_eq_zero.1 this).resolve_right hlam0
  have hS3' : 3 ∣ S.card := (ZMod.natCast_eq_zero_iff _ _).1 hS3
  have hC3 : 3 ∣ (Sᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    exact Nat.dvd_sub h3 hS3'
  by_cases hSc : (Sᶜ).Nonempty
  · have hcard : 1 < (Sᶜ).card := by
      have hpos : 0 < (Sᶜ).card := Finset.card_pos.2 hSc
      obtain ⟨k, hk⟩ := hC3
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
    set u : UnitRaw.W N := Pi.single a 1 - Pi.single b 1 with hu
    have huker : u ∈ LinearMap.ker (UnitRaw.sumFun N) := by
      rw [LinearMap.mem_ker, UnitRaw.sumFun_apply, hu]
      simp [Finset.sum_sub_distrib]
    have huheart : (UnitRaw.oneLine N).mkQ u ∈ UnitRaw.heart N :=
      ⟨u, huker, rfl⟩
    have hucent : ((⟨(UnitRaw.oneLine N).mkQ u, huheart⟩ : ↥(UnitRaw.heart N))) ∈
        UnitRaw.centH S := by
      rw [UnitRaw.mem_centH_iff, UnitRaw.mem_cent_iff]
      refine ⟨u, rfl, ?_⟩
      intro i hi j hj
      have hia : i ≠ a := fun h => (Finset.mem_compl.1 ha) (h ▸ hi)
      have hib : i ≠ b := fun h => (Finset.mem_compl.1 hb) (h ▸ hi)
      have hja : j ≠ a := fun h => (Finset.mem_compl.1 ha) (h ▸ hj)
      have hjb : j ≠ b := fun h => (Finset.mem_compl.1 hb) (h ▸ hj)
      simp [hu, Pi.single_apply, hia, hib, hja, hjb]
    rw [hcent] at hucent
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hucent
    have hμ' : μ • (UnitRaw.oneLine N).mkQ w = (UnitRaw.oneLine N).mkQ u := by
      have := congrArg Subtype.val hμ
      simpa [← hwv] using this
    have hdiff2 : μ • w - u ∈ UnitRaw.oneLine N := by
      have h : (UnitRaw.oneLine N).mkQ (μ • w) = (UnitRaw.oneLine N).mkQ u := by
        rw [map_smul]
        exact hμ'
      exact (Submodule.Quotient.eq _).1 h
    obtain ⟨c2, hc2⟩ := (UnitRaw.mem_oneLine _).1 hdiff2
    have hA := congrFun hc2 a
    have hB := congrFun hc2 b
    have hwa : w a = 0 := hw0 a (Finset.mem_compl.1 ha)
    have hwb : w b = 0 := hw0 b (Finset.mem_compl.1 hb)
    simp [hu, Pi.single_apply, hwa, hwb, hab, Ne.symm hab] at hA hB
    have : (1 : ZMod 3) = -1 := by
      rw [← neg_neg (1 : ZMod 3)]
      linear_combination hB - hA
    exact absurd this (by decide)
  ·
    have hSall : ∀ i, i ∈ S := by
      intro i
      by_contra hi
      exact hSc ⟨i, Finset.mem_compl.2 hi⟩
    apply hvx
    have hw : w ∈ UnitRaw.oneLine N := by
      rw [UnitRaw.mem_oneLine]
      exact ⟨lam, funext fun i => by rw [hwdef i, if_pos (hSall i)]⟩
    have : (vx : UnitRaw.Vfull N) = 0 := by
      rw [← hwv]
      exact (Submodule.Quotient.mk_eq_zero _).2 hw
    exact Subtype.ext this

theorem inLLeafCases_unitHeart (N : ℕ) : InLLeafCases (classicalCatalogue (.unitHeart N)) := by
  show InLLeafCases (unitHeartEntry N)
  intro vx hvx S hS _ _ hcent hin
  exact (unitHeart_noInternal hS.2.1 S hS.2.2 vx hvx hcent hin).elim

end CFSG.StandardType.GGQ2Frame

end
