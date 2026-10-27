module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCCard

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

section Frame

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {m : ℕ}
  {V VT : Type} [Group V] [Group VT]

private lemma qTwoLMFrameC_split_pow_eq_one_of_mem {x : G} {L : Subgroup G}
    (hxL : x ∉ L) (hord : orderOf x = 3) {k : ℕ} (hk : x ^ k ∈ L) : x ^ k = 1 := by
  by_contra hne
  have hx3 : x ^ 3 = 1 := by simpa [hord] using pow_orderOf_eq_one x
  have hmod : x ^ (k % 3) = x ^ k := by simpa [hord] using pow_mod_orderOf x k
  have hkL : x ^ (k % 3) ∈ L := by rw [hmod]; exact hk
  have hkmod : k % 3 ≠ 0 := by
    intro h0
    exact hne (by rw [← hmod, h0, pow_zero])
  have hcases : k % 3 = 1 ∨ k % 3 = 2 := by
    have := Nat.mod_lt k (by norm_num : 0 < 3)
    omega
  rcases hcases with hc | hc
  · exact hxL (by rwa [hc, pow_one] at hkL)
  · have hx2L : x ^ 2 ∈ L := by rwa [hc] at hkL
    have h4 : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul]
      norm_num
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hx3, one_mul]
    exact hxL (by
      have h5 : (x ^ 2) ^ 2 ∈ L := pow_mem hx2L 2
      rwa [h4] at h5)

theorem qTwoLMFrameC_split (F : QTwoFrame m V VT Bs L x) (hxL : x ∉ L)
    (hV : IsAugModel m V F.permV) (hVT : IsAugModel m VT F.permVT) :
    ∀ b ∈ Bs, ∃ t ∈ Bs ⊓ L, ∃ k : ℕ, b = t * x ^ k := by
  let γ := ggGamma L F.hN
  let T := Bs ⊓ L
  let φ : ↥T →* ↥γ.range :=
    MonoidHom.codRestrict (γ.comp (Subgroup.inclusion (show T ≤ Bs from inf_le_left)))
      γ.range (fun t => ⟨Subgroup.inclusion (show T ≤ Bs from inf_le_left) t, rfl⟩)
  have hcardT : Nat.card ↥T = 3 ^ (m - 1) := qTwoLMFrameC_card_T F hVT
  have hcardW : Nat.card ↥γ.range = 3 ^ (m - 1) := qTwoLMFrameC_card_W F hV
  have hinj : Function.Injective φ := by
    intro a b hab
    have h2 : γ (Subgroup.inclusion (show T ≤ Bs from inf_le_left) a) =
        γ (Subgroup.inclusion (show T ≤ Bs from inf_le_left) b) :=
      congrArg (fun z : ↥γ.range => (z : MulAut ↥L)) hab
    have hmem : (((Subgroup.inclusion (show T ≤ Bs from inf_le_left) a)⁻¹ *
        Subgroup.inclusion (show T ≤ Bs from inf_le_left) b : ↥Bs) : G) ∈
        Subgroup.zpowers x := by
      rw [← F.ker ((Subgroup.inclusion (show T ≤ Bs from inf_le_left) a)⁻¹ *
        Subgroup.inclusion (show T ≤ Bs from inf_le_left) b)]
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
    have hmemL : (((Subgroup.inclusion (show T ≤ Bs from inf_le_left) a)⁻¹ *
        Subgroup.inclusion (show T ≤ Bs from inf_le_left) b : ↥Bs) : G) ∈ L := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (inv_mem (by simpa using a.2.2)) (by simpa using b.2.2)
    have hkL : x ^ k ∈ L := by rw [hk]; exact hmemL
    have h1 : x ^ k = 1 := qTwoLMFrameC_split_pow_eq_one_of_mem hxL F.hord hkL
    have hprod : ((Subgroup.inclusion (show T ≤ Bs from inf_le_left) a : ↥Bs) : G)⁻¹ *
        ((Subgroup.inclusion (show T ≤ Bs from inf_le_left) b : ↥Bs) : G) = 1 := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hk.symm.trans h1
    exact Subtype.ext (by simpa using inv_mul_eq_one.mp hprod)
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (le_of_eq (hcardW.trans hcardT.symm))
  intro b hb
  have hy : γ ⟨b, hb⟩ ∈ γ.range := ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨t, ht⟩ := hbij.2 ⟨γ ⟨b, hb⟩, hy⟩
  have h2 : γ (Subgroup.inclusion (show T ≤ Bs from inf_le_left) t) = γ ⟨b, hb⟩ :=
    congrArg (fun z : ↥γ.range => (z : MulAut ↥L)) ht
  have hmem : (((Subgroup.inclusion (show T ≤ Bs from inf_le_left) t)⁻¹ * ⟨b, hb⟩ :
      ↥Bs) : G) ∈ Subgroup.zpowers x := by
    rw [← F.ker ((Subgroup.inclusion (show T ≤ Bs from inf_le_left) t)⁻¹ * ⟨b, hb⟩)]
    rw [map_mul, map_inv, h2, inv_mul_cancel]
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  refine ⟨(t : G), t.2, k, ?_⟩
  have hcoeeq : (((Subgroup.inclusion (show T ≤ Bs from inf_le_left) t)⁻¹ * ⟨b, hb⟩ :
      ↥Bs) : G) = (t : G)⁻¹ * b := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  rw [hcoeeq] at hk
  rw [hk]
  group

theorem qTwoLMFrameC_normalizer_of_centralizer {B : Subgroup G} (F : QTwoFrame m V VT Bs L x)
    (hG : GGThmIHyp 3 B x L) (hm : 3 ≤ m) (hVT : IsAugModel m VT F.permVT) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.normalizer (L : Set G) := by
  have hS := hG.2.2.2.2.2.2.1
  have hE : IsElemAbelian 3 (Bs ⊓ L) := TableB.isElemAbelian_mono F.elemAb inf_le_left
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
    refine ⟨Bs ⊓ L, inf_le_right, TableB.isPGroup_of_isElemAbelian hE, ?_⟩
    refine TableB.not_isCyclic_of_card (p := 3) (by norm_num) ?_ ?_
    · intro y hy
      exact F.elemAb.2 y (Subgroup.mem_inf.mp hy).1
    · rw [qTwoLMFrameC_card_T F hVT]
      exact Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 2 ≤ m - 1)
  intro g hg
  exact mem_normalizer_of_sstar hS hnc hg

end Frame

end CFSG.StandardType.QTwo

end
