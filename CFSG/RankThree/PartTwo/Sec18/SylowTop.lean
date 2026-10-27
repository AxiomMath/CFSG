module

public import CFSG.RankThree.PartTwo.Sec18.SylowFusion
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.RankThree.PartOne.S12.Sec15Final
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

namespace SylowTop

theorem isSylowOf_top_of_normalizer_le {p : ℕ} [Fact p.Prime] {T M : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M)
    (hN : Subgroup.normalizer (T : Set G) ≤ M) : CFSG.ABGLocalTools.IsSylowOf p T ⊤ := by
  obtain ⟨S, hTS⟩ := hT.isPGroup.exists_le_sylow
  have hTS' : T = S := by
    by_contra hne
    obtain ⟨y, hyS, hyT, hyN⟩ :=
      Late.exists_mem_normalizer_not_mem_of_lt S.isPGroup' (lt_of_le_of_ne hTS hne)
    have hQ : T ⊔ Subgroup.zpowers y = T :=
      hT.eq_of_le le_sup_left (sup_le hT.le (Subgroup.zpowers_le.mpr (hN hyN)))
        (S.isPGroup'.to_le (sup_le hTS (Subgroup.zpowers_le.mpr hyS)))
    exact hyT (hQ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hT.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right, hTS']
  exact S.not_dvd_index

theorem le_of_isSylowOf {p : ℕ} [Fact p.Prime] {N P K : Subgroup G} (hNK : N ≤ K)
    [(N.subgroupOf K).Normal] (hN : IsPGroup p N) (hP : CFSG.ABGLocalTools.IsSylowOf p P K) :
    N ≤ P := by
  obtain ⟨Q, rfl⟩ := hP
  have hN' : IsPGroup p (N.subgroupOf K) := hN.comap_subtype
  intro x hx
  exact ⟨⟨x, hNK hx⟩, hN'.le_sylow_of_normal Q hx, rfl⟩

end SylowTop


namespace SylowTop

variable {A M H : Subgroup G} {c : G}

theorem normalizer_le_of_le_normalizer_zpowers (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (h1844 : Item184_4) (hH : Sec18H G A M H c) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G)))
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ inSubgroup perfectResidual H with hB
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 _ x.2)⟩
  have hAP : A ≤ P := le_of_isSylowOf (Subgroup.le_normalizer (H := A)) hA3 hP
  have hPC : P ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec11.le_centralizer_of_le_normalizer_zpowers (orderOf_eq_three_of_sec18H h184 hH)
      hP.isPGroup (hP.le.trans hWc)
  have hBK := SylowFusion.isSylowOf_lc h1812 h184 hH
  have hPK : P ⊓ lc H c = B :=
    hBK.eq_of_le (le_inf (inf_le_left.trans hAP) hBK.le) inf_le_right
      (hP.isPGroup.to_le inf_le_left)
  intro x hx
  have hxP : ∀ y ∈ P, x * y * x⁻¹ ∈ P := fun y hy => (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  have hxP' : ∀ y ∈ P, x⁻¹ * y * x ∈ P := fun y hy => by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
  have hxcA : x * c * x⁻¹ ∈ A := by
    refine Item183NMProof.mem_of_commute_of_sec18Std hH.toSec18Std ?_ fun a ha => ?_
    · rw [conj_pow, pow_three_eq_one_of_sec18H hH, mul_one, mul_inv_cancel]
    · have h := Subgroup.mem_centralizer_singleton_iff.mp (hPC (hxP' a (hAP ha)))
      calc a * (x * c * x⁻¹) = x * (x⁻¹ * a * x * c) * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * a * x)) * x⁻¹ := by rw [h]
        _ = x * c * x⁻¹ * a := by group
  have hxc : x * c * x⁻¹ ∈ Subgroup.zpowers c := by
    have hmem : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈
        conjugatesIn (Subgroup.zpowers c) A := by
      refine ⟨⟨x, rfl⟩, ?_⟩
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hxcA
    rw [h1844 G A M H c hH] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    have h1 : x * c * x⁻¹ ∈ (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers c)
    rw [hwx] at h1
    obtain ⟨z, hz, hzw⟩ := h1
    rw [← hzw]
    exact (Subgroup.mem_normalizer_iff.mp (hWc hw) z).mp hz
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hxc i
  have hxL := normalizer_zpowers_le_normalizer_lc h1842 hH hxN
  have hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
    intro b hb
    rw [← hPK] at hb ⊢
    exact ⟨hxP b hb.1, (Subgroup.mem_normalizer_iff.mp hxL b).mp hb.2⟩
  apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
  intro a ha
  have hle : A ≤ A.comap (MulAut.conj x).toMonoidHom := by
    refine (eq_zpowers_sup_of_sec18H h1812 h184 hH).le.trans (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le]
      exact hxcA
    · intro b hb
      exact (hxB b hb).1
  exact hle ha

end SylowTop

open SylowTop in
theorem item184_6_of (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    (h1844 : Item184_4) (h1845 : Item184_5) : Item184_6 := by
  intro G _ _ A M H c hH P hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isSylowOf_top_of_normalizer_le hP ?_
  rcases h1845 G A M H c hH P hP with ⟨hWc, -, -⟩ | ⟨-, -, hAP, hchar, -⟩
  · exact normalizer_le_of_le_normalizer_zpowers h1812 h184 h1842 h1844 hH hP hWc
  · exact CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_of_characteristic hAP hchar

end CFSG.RankThree.PartTwo.Sec18
