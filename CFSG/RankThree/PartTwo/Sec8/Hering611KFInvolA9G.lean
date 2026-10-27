module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolK
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolA9
import CFSG.RankThree.PartTwo.Sec8.Hering611KFBridge

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section A9


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem exists_field_involution_a9 (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hA9 : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* alternatingGroup (Fin 9)))
    (hcK : c ∈ K) :
    ∃ s : G, s ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L s .field := by
  classical
  obtain ⟨hcN, h3, h1, hP, hPq⟩ := exists_bridge_image h45 C
  obtain ⟨e⟩ := hA9
  have hc3 : c ^ 3 = 1 := C.mem_S.1.1.2 c C.c_mem
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set γ : K ⧸ aschbacherSolvableCore 3 K := π ⟨c, hcK⟩ with hγ
  have hγ3 : γ ^ 3 = 1 := by
    rw [hγ, ← map_pow]
    have : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hα : Item426.thetaAut K hcN = MulAut.conj γ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      rw [Item426.thetaAut_mk]
      change π (compAction K ⟨c, hcN⟩ k) = γ * π k * γ⁻¹
      rw [hγ, ← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hγ1 : γ ≠ 1 := by
    intro h
    apply h1
    rw [hα, h, map_one]
  have hfix : Item426.fixSub (Item426.thetaAut K hcN) =
      Subgroup.centralizer ({γ} : Set (K ⧸ aschbacherSolvableCore 3 K)) := by
    ext x
    rw [Item426.mem_fixSub, Subgroup.mem_centralizer_singleton_iff, hα]
    change γ * x * γ⁻¹ = x ↔ x * γ = γ * x
    constructor
    · intro h
      calc x * γ = γ * x * γ⁻¹ * γ := by rw [h]
        _ = γ * x := by group
    · intro h
      calc γ * x * γ⁻¹ = x * γ * γ⁻¹ := by rw [h]
        _ = x := by group
  rw [hfix] at hP
  obtain ⟨ePA⟩ := hPq
  have hq : Nat.card (((Sec11.sec11K L d).subgroupOf K).map π ⧸
      aschbacherSolvableCore 3 (((Sec11.sec11K L d).subgroupOf K).map π)) = 360 := by
    rw [Nat.card_congr ePA.toEquiv, nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨t, ht2, hinv, hS6⟩ := exists_inverting_s6act e hγ3 hγ1 hP hq
  exact exists_field_involution_inv h45 C hcK ht2 hinv hS6

end A9

end CFSG.RankThree.PartTwo.Sec8.Hering611
