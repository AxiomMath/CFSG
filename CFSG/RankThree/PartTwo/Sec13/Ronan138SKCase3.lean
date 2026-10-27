module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_case3 {A L E F : Subgroup G} {c x y t : G} (hfr : Frame138 A L E F c x y t)
    (hcΩ : Subgroup.zpowers c ∉ omegaA E) (hdΩ : E ⊓ L ∉ omegaA E) {e : G} {K : Subgroup G}
    (hD : Sec13Data G E e K) (heF : e ∈ F)
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (K ⊓ Subgroup.normalizer (E : Set G)) (E ⊓ K)))
    (hWB : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G))
    (hΩ : omegaA E = orbitIn (Subgroup.normalizer (E : Set G)) (Subgroup.zpowers e))
    (hΩ9 : (omegaA E).ncard = 9) (hB9 : Nat.card (E ⊓ K : Subgroup G) = 9) : False := by
  have hE3 : CFSG.Assembly.IsElemAbelian 3 E := hfr.hH.2.2.2.1
  set B := E ⊓ K with hBdef
  have heE : e ∈ E := hD.mem_A
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := hD.ne_one
  have hKe : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hk)
  have heB : e ∉ B := by
    intro heB
    rcases eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr heB) (fun k hk => by
      apply mem_normalizer_of_map_le
      rw [MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      change k * e * k⁻¹ ∈ Subgroup.zpowers e
      rw [hKe k (Subgroup.mem_inf.mp hk).1, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers e) with h0 | h0
    · exact he1 (by simpa using (Subgroup.zpowers_eq_bot).mp h0)
    · have : Nat.card (Subgroup.zpowers e) = Nat.card B := by rw [h0]
      rw [card_zpowers_of_pow_three he3 he1, hB9] at this
      norm_num at this
  have hBE : B ≤ E := inf_le_left
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun a b => Subtype.ext (hfr.hEab a (hBE a.2) b (hBE b.2))⟩⟩,
      fun z hz => hE3.2 z (hBE hz)⟩
  obtain ⟨-, he27⟩ := isElemAbelian_zpowers_sup_of_card_nine he3 heB le_rfl hB9
    (fun z hz => hBe.2 z hz) (fun z hz => hfr.hEab e heE z (hBE hz))
  have hEeB : E = Subgroup.zpowers e ⊔ B :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr heE) hBE)
      (by rw [he27, hfr.hE27])).symm
  have hepts : Subgroup.zpowers e ∈ pointsOff E B :=
    ⟨Subgroup.zpowers_le.mpr heE, card_zpowers_of_pow_three he3 he1,
      fun hle => heB (hle (Subgroup.mem_zpowers e))⟩
  have hΩpts : omegaA E ⊆ pointsOff E B := by
    intro X hX
    rw [hΩ] at hX
    obtain ⟨w, hwE, rfl⟩ := hX
    exact map_conj_mem_pointsOff hwE (hWB hwE) hepts
  have hΩeq : omegaA E = pointsOff E B :=
    Set.eq_of_subset_of_ncard_le hΩpts
      (by rw [ncard_pointsOff hE3 heE hEeB heB hB9, hΩ9])
      (Set.toFinite _)
  have hmemB : ∀ a ∈ E, a ^ 3 = 1 → a ≠ 1 → Subgroup.zpowers a ∉ omegaA E → a ∈ B := by
    intro a haE ha3 ha1 haΩ
    by_contra haB
    apply haΩ
    rw [hΩeq]
    exact ⟨Subgroup.zpowers_le.mpr haE, card_zpowers_of_pow_three ha3 ha1,
      fun hle => haB (hle (Subgroup.mem_zpowers a))⟩
  have hcB : c ∈ B := hmemB c hfr.hcE hfr.hc3 hfr.hc1 hcΩ
  have hdB : ⁅x, y⁆ ∈ B := hmemB _ hfr.hdE hfr.hd3 hfr.hd1 (by rw [← hfr.hEL]; exact hdΩ)
  obtain ⟨α, β, heq⟩ := hfr.hZgen e (Subgroup.mem_inf.mpr ⟨heE, heF⟩)
  exact heB (heq ▸ mul_mem (pow_mem hcB α) (pow_mem hdB β))

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
