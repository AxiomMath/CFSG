module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3EightTorusE9Holds
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229G898
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.Quasithin.Background.RonanF615QTK
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76SL3Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Linear
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem uc22s213_card_center_sylow_su38
    {X : Type} [Group X] [Finite X]
    (hX : IsSU3 X 3) (hZ : Nat.card (center X) = 3) (S : Sylow 3 X) :
    Nat.card (center (S : Subgroup X)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hF, hd, hFc, -, ⟨ψ⟩⟩ :=
    PartTwo.Inputs1719.exists_mulEquiv_unitarySU_three_of_isSU3 hX (by rw [hZ])
  have : Finite F := hd.finite
  let eH : ↥(CFSG.Open.StatedSU 3 8 F) ≃* X := ψ
  have h3 : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units, hFc]; norm_num
  obtain ⟨ω, hord⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3
  have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
  have hω9 : ω ^ (8 + 1) = 1 := by rw [show 8 + 1 = 3 * 3 from rfl, pow_mul, hω, one_pow]
  have hD := CFSG.Open.StatedCenterThree.diagGL_mem (K := F) (q := 8) (by norm_num) hω9
  have hC := CFSG.Open.StatedCenterThree.cyc3GL_mem (K := F) (q := 8) (by norm_num)
  have hS := CFSG.Open.StatedCenterThree.scalar_mem (K := F) (q := 8) (by norm_num) (by norm_num) hω
  let d : ↥(CFSG.Open.StatedSU 3 8 F) := ⟨_, hD⟩
  let c : ↥(CFSG.Open.StatedSU 3 8 F) := ⟨_, hC⟩
  let s : ↥(CFSG.Open.StatedSU 3 8 F) := ⟨_, hS⟩
  have hsZ : s ∈ center ↥(CFSG.Open.StatedSU 3 8 F) :=
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Matrix.GeneralLinearGroup.scalar_commute ω (g : GL (Fin 3) F)).symm
  have hs3 : s ^ 3 = 1 := Subtype.ext (by
    change Matrix.GeneralLinearGroup.scalar (Fin 3) ω ^ 3 = 1
    rw [← map_pow, hω, map_one])
  have hE : IsPGroup 3 (closure {d, c}) :=
    RankThreeTheoremC.CentralOmega.isPGroup_closure_of_conj_eq_mul hsZ hs3
      (Subtype.ext (RankThreeTheoremC.CentralOmega.diagGL_pow_three hω))
      (Subtype.ext RankThreeTheoremC.CentralOmega.cyc3GL_pow_three)
      (Subtype.ext (RankThreeTheoremC.CentralOmega.cyc3GL_conj_diagGL hω))
  obtain ⟨P, hP⟩ := (hE.map eH.toMonoidHom).exists_le_sylow
  have hZP : ∀ x ∈ (P : Subgroup X), (∀ y ∈ (P : Subgroup X), x * y = y * x) →
      x ∈ center X := by
    intro x _ hx
    have hdP : eH d ∈ (P : Subgroup X) :=
      hP (mem_map_of_mem _ (subset_closure (Set.mem_insert _ _)))
    have hcP : eH c ∈ (P : Subgroup X) :=
      hP (mem_map_of_mem _ (subset_closure (Set.mem_insert_of_mem _ rfl)))
    have hxd := congrArg eH.symm (hx _ hdP)
    have hxc := congrArg eH.symm (hx _ hcP)
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at hxd hxc
    have hcen := AGL81TheoremCD.Section7.mem_center_of_commute_diagGL_cyc3GL hord hD hC hxd hxc
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro g
    apply eH.symm.injective
    rw [map_mul, map_mul]
    exact hcen (eH.symm g)
  have hZXP : center X ≤ (P : Subgroup X) :=
    IsPGroup.le_sylow_of_normal (IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])) P
  have heq : (center (P : Subgroup X)).map (P : Subgroup X).subtype = center X := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hZP z z.2 fun y hy =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm
    · intro x hx
      exact ⟨⟨x, hZXP hx⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_center_iff.mp hx g), rfl⟩
  have hPc : Nat.card (center (P : Subgroup X)) = Nat.card (center X) := by
    rw [← heq, card_map_of_injective (P : Subgroup X).subtype_injective]
  rw [Nat.card_congr (centerCongr (Sylow.equiv S P)).toEquiv, hPc, hZ]

theorem uc22s213_pRank_mulAut_su38 {X : Type} [Group X] [Finite X] (hX : IsSU3 X 3) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  have hpn : ¬ p ∣ 2 * 3 := fun h => by
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  have hpq : ¬ p ∣ 2 ^ 3 + 1 := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (hp.dvd_of_dvd_pow (n := 2) (by norm_num at h ⊢; exact h)))
  obtain ⟨E, -, hEel, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MulAut X))
  have hle := UCK.u3RankOne X 3 hX p hp hp2 hpq E
    (fun φ hφ => uc22ine229_mem_inner hX hp hp3 hpn (hEel.2 φ hφ)) hEel
  rw [hEc] at hle
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (by rwa [pow_one])

theorem uc22s213_pRank_three_su38
    {X : Type} [Group X] [Finite X] (hX : IsSU3 X 3)
    (hZ : Nat.card (center X) = 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨F, hF, hd, hFc, -, ⟨ψ⟩⟩ :=
    PartTwo.Inputs1719.exists_mulEquiv_unitarySU_three_of_isSU3 hX (by rw [hZ])
  have : Finite F := hd.finite
  refine le_antisymm ?_ ?_
  · rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.Quasithin.RonanF615.pRank_three_le_two_of_statedSU (n := 3)
      ⟨F, hF, inferInstance, by rw [hFc]; norm_num, ⟨ψ.symm⟩⟩
  · obtain ⟨-, E, -, -, hEel, hEc, -⟩ :=
      PartTwo.Inputs1719.k_SU3EightTorusE9_holds X hX (by rw [hZ])
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hEel (k := 2) (by rw [hEc]; norm_num)

theorem uc22s213_typeFacts_su38
    {X : Type} [Group X] [Finite X] (hX : IsSU3 X 3)
    (hZ : Nat.card (center X) = 3) :
    Nat.card (center X) ≤ 3 ∧ (∀ S : Sylow 3 X, Nat.card (center (S : Subgroup X)) = 3) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1) ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  ⟨hZ.le, uc22s213_card_center_sylow_su38 hX hZ,
    fun _ hp hp2 hp3 => uc22s213_pRank_mulAut_su38 hX hp hp2 hp3,
    (uc22s213_pRank_three_su38 hX hZ).ge⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
