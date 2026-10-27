module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6ShortRoot
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec56Defs
import CFSG.GH74.GLS.LU.Local.GenCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

section H6


theorem closure_z0u_le_cen :
    Subgroup.closure {zH 0, zH 1 * zH 2} ≤ Subgroup.centralizer {sH} := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · exact sH_comm_z0.symm
  · exact sH_comm_u.symm

theorem isPGroup_closure_z0u : IsPGroup 3 (Subgroup.closure {zH 0, zH 1 * zH 2}) := by
  refine (isPGroup_baseA wreathFacts_zH).to_le ?_
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact z_mem_baseA 0
  · exact mul_mem (z_mem_baseA 1) (z_mem_baseA 2)

theorem card_closure_z0u : Nat.card (Subgroup.closure {zH 0, zH 1 * zH 2}) = 9 := by
  have hz : ∀ a b : ZMod 3, vecElt zH ![a, b, b] ∈ Subgroup.closure {zH 0, zH 1 * zH 2} := by
    intro a b
    have h12 : Commute (zH 1) (zH 2) := zH_comm 1 2
    simp only [vecElt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [mul_assoc, ← h12.mul_pow]
    exact mul_mem (pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)
  have hinj : Function.Injective (fun p : ZMod 3 × ZMod 3 =>
      (⟨vecElt zH ![p.1, p.2, p.2], hz p.1 p.2⟩ : Subgroup.closure {zH 0, zH 1 * zH 2})) := by
    intro p q h
    have e := vecElt_injective wreathFacts_zH (congrArg Subtype.val h)
    have h0 := congrFun e 0
    have h1 := congrFun e 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    exact Prod.ext h0 h1
  have hge : 9 ≤ Nat.card (Subgroup.closure {zH 0, zH 1 * zH 2}) := by
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, Nat.card_zmod] at h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp isPGroup_closure_z0u
  have hdvd : Nat.card (Subgroup.closure {zH 0, zH 1 * zH 2}) ∣ 4608 :=
    card_cen_sH ▸ Subgroup.card_dvd_of_le closure_z0u_le_cen
  rw [hk] at hdvd hge ⊢
  have hk3 : k < 3 := by
    by_contra h
    push_neg at h
    have h27 : 3 ^ 3 ∣ 4608 := (pow_dvd_pow 3 h).trans hdvd
    norm_num at h27
  interval_cases k <;> simp_all

theorem conj_three_elt {l : H6} (hl : l ∈ Subgroup.centralizer {sH}) (h3 : l ^ 3 = 1) :
    ∃ c ∈ Subgroup.centralizer {sH}, c * l * c⁻¹ ∈ Subgroup.closure {zH 0, zH 1 * zH 2} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card (Subgroup.centralizer {sH})).factorization 3 = 2 := by
    rw [card_cen_sH, show (4608 : ℕ) = 3 ^ 2 * 512 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hord : ∃ n : ℕ, orderOf l = 3 ^ n := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨n, hn, hnE⟩ := CFSG.GH74.GLS.LU.Local.exists_conj_mem_of_sylow 3 closure_z0u_le_cen
    (by rw [card_closure_z0u, hfac] <;> norm_num) hl hord
  exact ⟨n⁻¹, inv_mem hn, by rwa [inv_inv]⟩

theorem card_le_of_normal {Y : Subgroup H6} (hY : Y ≤ Subgroup.centralizer {sH})
    (hN : Subgroup.centralizer {sH} ≤ Nor Y) (hc : Nat.Coprime (Nat.card Y) 3) :
    Nat.card Y ≤ 128 := by
  have hdvd : Nat.card Y ∣ 3 ^ 2 * 2 ^ 9 := by
    rw [show (3 ^ 2 * 2 ^ 9 : ℕ) = 4608 by norm_num, ← card_cen_sH]
    exact Subgroup.card_dvd_of_le hY
  have h2 : Nat.card Y ∣ 2 ^ 9 := (Nat.Coprime.pow_right 2 hc).dvd_of_dvd_mul_left hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact card_le_of_isPGroup hY (IsPGroup.of_card hk) hN

end H6

section Main


theorem kf_sp6ShortRootCen : KF_Sp6ShortRootCen := by
  intro X _ _ L hL b₁ b₂ b₃ hb₁ hb₂ hb₃ hB _ hmono s hs hs2 hs1 hsu hsw
  obtain ⟨f, hf, hfL, rfl, rfl, rfl, rfl⟩ :=
    exists_hom_sH hL hb₁ hb₂ hb₃ hB hmono hs hs2 hs1 hsu hsw
  have hLs : L ⊓ Cen (f sH) = (Subgroup.centralizer {sH}).map f := by
    rw [← hfL, ← map_inf_cen hf, top_inf_eq]
  refine ⟨fun l hl h3 => ?_, fun Y hY hN hc => ?_, ?_⟩
  · rw [hLs] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    obtain ⟨c, hc, hcE⟩ := conj_three_elt hl' (hf (by rw [map_pow, h3, map_one]))
    refine ⟨f c, by rw [hLs]; exact Subgroup.mem_map_of_mem f hc, ?_⟩
    have hmem := Subgroup.mem_map_of_mem f hcE
    simp only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, map_mul,
      map_inv] at hmem
    exact hmem
  · rw [hLs] at hY hN
    obtain ⟨Y', rfl⟩ : ∃ Y' : Subgroup H6, Y = Y'.map f :=
      ⟨Y.comap f, (Subgroup.map_comap_eq_self (hY.trans (Subgroup.map_le_range f _))).symm⟩
    rw [Subgroup.card_map_of_injective hf] at hc ⊢
    refine card_le_of_normal (fun x hx => ?_) (fun c hcC => ?_) hc
    · exact (Subgroup.mem_map_iff_mem hf).mp (hY (Subgroup.mem_map_of_mem f hx))
    · have hn := hN (Subgroup.mem_map_of_mem f hcC)
      rw [Nor, Subgroup.mem_normalizer_iff] at hn ⊢
      intro x
      have h1 := hn (f x)
      rw [Subgroup.mem_map_iff_mem hf, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem hf] at h1
      exact h1
  · rw [hLs, Subgroup.card_map_of_injective hf, card_cen_sH]
    norm_num

end Main

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR
