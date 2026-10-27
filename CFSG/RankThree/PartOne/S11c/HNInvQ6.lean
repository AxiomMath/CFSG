module

public import CFSG.RankThree.PartOne.S11c.HNInvPair
public import CFSG.Sporadic.HNOddCore.SixD

public noncomputable section

namespace CFSG.RankThree.PartOne.HNRed

open Equiv Subgroup
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CFSG.Blueprint.NativeSporadic (Carrier)

section Abstract

theorem exists_hom_of_normalizer {C : Type*} [Group C] {Ω : Type*} (φ : C →* Perm Ω)
    (D : Subgroup (Perm Ω)) (hφ : φ.range ≤ normalizer (D : Set (Perm Ω)))
    (hcent : ∀ z : Perm Ω, (∀ d ∈ D, z * d = d * z) → z = 1) {S : Type*} [Group S]
    (χ : D ≃* S) : ∃ q : C →* MulAut S, ∀ x : C, q x = 1 → φ x = 1 := by
  let φ' : C →* normalizer (D : Set (Perm Ω)) := φ.codRestrict _ (fun x => hφ ⟨x, rfl⟩)
  refine ⟨(MulAut.congr χ).toMonoidHom.comp (D.normalizerMonoidHom.comp φ'), fun x hx => ?_⟩
  have h1 : D.normalizerMonoidHom (φ' x) = 1 := by
    have h : (MulAut.congr χ) (D.normalizerMonoidHom (φ' x)) = 1 := hx
    exact (MulEquiv.map_eq_one_iff _).1 h
  have h2 : φ' x ∈ D.normalizerMonoidHom.ker := h1
  rw [Subgroup.normalizerMonoidHom_ker, mem_subgroupOf, mem_centralizer_iff] at h2
  exact hcent (φ x) (fun d hd => (h2 d hd).symm)

theorem eq_one_or_eq_of_card_two {G : Type*} [Group G] (K : Subgroup G) (hK : Nat.card K = 2)
    {t : G} (ht : t ∈ K) (ht1 : t ≠ 1) {x : G} (hx : x ∈ K) : x = 1 ∨ x = t := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : K)).1 hK
  by_cases hx1 : (⟨x, hx⟩ : K) = 1
  · exact Or.inl (congrArg Subtype.val hx1)
  · right
    have hT : (⟨t, ht⟩ : K) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
    exact congrArg Subtype.val ((huniq _ hx1).trans (huniq _ hT).symm)

end Abstract

section Centralizer

theorem eq_zero_of_Hsub_fixed
    {p : Fin 1100} (h : ∀ g ∈ Hsub, g p = p) : p = 0 := by
  have hi := (labD p).2
  have hp := (labD_iff hi p).1 rfl
  have hsame : ∀ q : Fin 1100, labD q = labD p → q = p := by
    intro q hq
    have hq' := (labD_iff hi q).1 (by rw [hq])
    obtain ⟨g, hg, hgp⟩ := orbit_rel hi hp hq'
    rw [← hgp]
    exact h _ (mem_subgroupOf.1 hg)
  have hcard : Nat.card {q : Fin 1100 // labD q = labD p} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((hsame a a.2).trans (hsame b b.2).symm)⟩, ⟨⟨p, rfl⟩⟩⟩
  rw [card_labD] at hcard
  have hzero : labD p = 0 := by
    generalize labD p = i at hcard ⊢
    fin_cases i <;> simp_all
  exact (hsame 0 (by rw [labD_zero, hzero])).symm

theorem centralizer_Dsub_trivial
    {z : Perm (Fin 1100)} (hz : ∀ d ∈ Dsub, z * d = d * z) : z = 1 := by
  have h0 : z 0 = 0 := by
    apply eq_zero_of_Hsub_fixed
    intro g hg
    have h1 := Equiv.congr_fun (hz g (Hsub_le hg)) 0
    rw [Perm.mul_apply, Perm.mul_apply, Hsub_fix hg] at h1
    exact h1.symm
  refine Equiv.ext fun p => ?_
  obtain ⟨d, hd, rfl⟩ := Dsub_transitive 0 p
  have h1 := Equiv.congr_fun (hz d hd) 0
  rw [Perm.mul_apply, Perm.mul_apply, h0] at h1
  exact h1

end Centralizer

section Main

theorem val_t6C : ((t6C : C6) : JH) = aJ := by
  unfold t6C
  exact Subtype.coe_mk _ _

theorem exists_q6 :
    ∃ q : C6 →* MulAut (Carrier .HS), ∀ x : C6, q x = 1 → (x : JH) = 1 ∨ (x : JH) = aJ := by
  obtain ⟨χ⟩ := nonempty_Dsub_mulEquiv_HS
  obtain ⟨q, hq⟩ := exists_hom_of_normalizer phi6 Dsub range_le_normalizer_D
    (fun _ hz => centralizer_Dsub_trivial hz) χ
  refine ⟨q, fun x hx => ?_⟩
  have hker : x ∈ phi6.ker := hq x hx
  rcases eq_one_or_eq_of_card_two phi6.ker card_ker_phi6 t6C_mem_ker t6C_ne_one hker with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h]
    exact val_t6C

end Main

end CFSG.RankThree.PartOne.HNRed
