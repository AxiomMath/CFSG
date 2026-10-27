module

public import CFSG.RankThree.PartTwo.Sec16.Item16Statements
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Holds
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

@[expose] def Claim164 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
    L ⊔ (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G))

omit [Finite G] in
theorem rank3II_16_4_of {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L : Subgroup G} (h163 : Item163 A LB c L) (hfr : Claim164 A c L) : Item164 A LB c := by
  intro Y hY
  obtain ⟨hW, -, -, hLY, -⟩ := h163 Y hY
  exact hfr.trans (sup_le (hLY.trans Subgroup.le_normalizer) (inf_le_right.trans hW))

theorem normalizer_zpowers_le_normalizer_L {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h3 : 3 ∣ Nat.card L) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  have hz : Subgroup.zpowers ((MulAut.conj g) c) = Subgroup.zpowers c := by
    have hmap : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers ((MulAut.conj g) c) := MonoidHom.map_zpowers _ _
    rw [← hmap]
    exact Late.map_conj_eq_of_mem_normalizer hg
  have hLg : L.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have := map_mem_thetaComponentsAt (MulAut.conj g) h.mem_lA.1
    rwa [thetaComponentsAt_eq_thetaComponentsIn, centralizer_singleton_eq_of_zpowers_eq hz,
      ← thetaComponentsAt_eq_thetaComponentsIn] at this
  have h3' : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 _ hLg h3'
  exact mem_normalizer_of_map_conj_eq heq

omit [Finite G] in
theorem three_dvd_card_of_j2 {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    3 ∣ Nat.card L := by
  have hc : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := KFacts.KS14.card_eq_of_j2 hJ
  refine (show (3 : ℕ) ∣ 604800 by norm_num).trans ?_
  rw [← hc]
  exact Subgroup.card_quotient_dvd_card _

theorem claim164_of_j2 (h415 : Sec4.Item4_15) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hAL : A ≤ Subgroup.zpowers c ⊔ L) : Claim164 A c L := by
  intro g hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φJ⟩ := hJ
  have hgL : L.map (MulAut.conj g).toMonoidHom = L := Late.map_conj_eq_of_mem_normalizer
    (normalizer_zpowers_le_normalizer_L h (three_dvd_card_of_j2 ⟨φJ⟩) hg)
  have hgz : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c :=
    Late.map_conj_eq_of_mem_normalizer hg
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    center_eq_bot_of_mulEquiv φJ (KFacts.KS14.center_nativeJ2_eq_bot h415)
  have hcL : c ∉ L := not_mem_of_center_eq_bot h.toSec13Data hZ
  have hcA : c ∈ A := h.mem_A
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c hcA
  have hcC : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hx)
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hA'le : A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.zpowers c ⊔ L := by
    calc A.map (MulAut.conj g).toMonoidHom ≤
          (Subgroup.zpowers c ⊔ L).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hAL
      _ = Subgroup.zpowers c ⊔ L := by rw [Subgroup.map_sup, hgz, hgL]
  have hcA' : c ∈ A.map (MulAut.conj g).toMonoidHom := by
    have hg' : g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := inv_mem hg
    have h1 : g⁻¹ * c * g⁻¹⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hg' c).mp (Subgroup.mem_zpowers c)
    have h2 : g⁻¹ * c * g⁻¹⁻¹ ∈ A := Subgroup.zpowers_le.mpr hcA h1
    refine ⟨_, h2, ?_⟩
    change g * (g⁻¹ * c * g⁻¹⁻¹) * g⁻¹ = c
    group
  have h27 : Nat.card A = 27 := h.toSec13Data.card_eq
  have h27' : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h27]
  obtain ⟨l', hl'L, hl'⟩ := KFacts.KS14.j2_exists_conjugate_of_card_twentySeven_of_quot h415 hN3
    ⟨φJ⟩ hcC hcL hc3 hAL hA'le hcA hcA' h27 h27'
  have hl'H : l' ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c (h.le_centralizer hl'L)
  have hW : l' * g ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_map_conj_eq ?_
    have e1 : A.map (MulAut.conj (l' * g)).toMonoidHom =
        (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l').toMonoidHom := by
      rw [Late.map_conj_map_conj]
    rw [e1, hl']
    change (A.map (MulAut.conj l'⁻¹).toMonoidHom).map (MulAut.conj l').toMonoidHom = A
    rw [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one]
  have hmem : l' * g ∈
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) :=
    ⟨mul_mem hl'H hg, hW⟩
  have e : g = l'⁻¹ * (l' * g) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (inv_mem hl'L) hmem

theorem le_sup_of_card_inf {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) : A ≤ Subgroup.zpowers c ⊔ L := by
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
  have hcard := (isElemAbelian_zpowers_sup_of_card_nine (h.isElemAbelian.2 c h.mem_A)
    (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
    (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [h.toSec13Data.card_eq, hcard])).symm
  rw [hAeq]
  exact sup_le_sup_left inf_le_right _

theorem claim164_of_j2_of_item131 (h415 : Sec4.Item4_15) (h131 : Item131)
    (hspor : SporadicModels131) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Claim164 A c L := by
  obtain ⟨hcL, h9⟩ := card_inf_eq_nine_of_j2 h131 hspor h.toSec13Data hJ
  exact claim164_of_j2 h415 h hJ (le_sup_of_card_inf h hcL h9)

end CFSG.RankThree.PartTwo.Sec16
