module

public import CFSG.Milestones.ASVolI.F429.bC6U5Model
public import CFSG.Milestones.ASVolI.F429.aC5U5
public import CFSG.Milestones.ASVolI.F429.bC6D4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section C6U5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.BA CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5


theorem burnsideF429b_c6_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) (hf : 2 ≤ f) (_hev : ¬ Odd Gp.index) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C6 .U5 f Gp M₁ M₂ T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, _, hK, Ψ, hB, -, -⟩ := burnsideF429a_U5_setup5 hyp
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set φ : hypPSU hK 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (u5PtP hK ⊓ u5LnP hK).map φ := burnsideF429_inf_eq_map Ψ hB
  have hS : S = (hypProjUnitriangular hK 2 1).map φ := by
    rw [hSdef, hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF429a_U5_pCoreOf_borel]
  have hmemS : ∀ x, x ∈ T → x ∈ Gp → x ∈ S := fun x hx hg => by
    rw [hSdef, ← burnsideF429_T_inf_Gp hyp hT]
    exact ⟨hx, hg⟩
  have hc := hyp.centralizer_trivial
  set V := (Vsub hK).map (hypProj hK 2 1) with hVdef
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hRcard : Nat.card ↥(V.map φ) = (2 ^ f) ^ 4 := by
    rw [Subgroup.card_map_of_injective hφ, burnsideF429b_U5_card_V]
  have hlt : (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hlt2 : 2 * (2 ^ f) ^ 3 < (2 ^ f) ^ 4 := by
    have h3 : 0 < (2 ^ f) ^ 3 := by positivity
    calc 2 * (2 ^ f) ^ 3 < 2 ^ f * (2 ^ f) ^ 3 := Nat.mul_lt_mul_of_pos_right (by omega) h3
      _ = (2 ^ f) ^ 4 := by ring
  have hstab : ∀ x ∈ M₁ ⊓ M₂, ∀ y, (Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm y ∈
      hypProjUnitriangular hK 2 1 ↔ y ∈ hypProjUnitriangular hK 2 1 := by
    intro x hx y
    have hrN := burnsideF429_le_normalizer_pCore_inf (Gp := Gp) (M₁ ⊓ M₂) hx
    have hmemU : ∀ z : hypPSU hK 2 1, z ∈ hypProjUnitriangular hK 2 1 ↔ φ z ∈ S := by
      intro z
      rw [hS]
      exact (Subgroup.mem_map_iff_mem hφ).symm
    rw [hmemU, hmemU, hφx, hφx, burnsideF429b_conjAut_apply]
    exact ((Subgroup.mem_normalizer_iff.1 hrN) _).symm
  have hnotS : ∀ x ∈ T, x ∉ S → (Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm ∉
      (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).range := fun x hxT hxS h =>
    hxS (hmemS x hxT (burnsideF429b_mem_of_conjAut_inner hc Ψ h))
  have hRS : V.map φ ≤ S := by
    rw [hS]
    exact Subgroup.map_mono (burnsideF429b_U5_V_le_U hK)
  have hle : S ≤ φ.range := by
    rw [hS]
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  refine burnsideF429_c6_of_unique (burnsideF429_sbar_le hT) hRS
    (burnsideF429b_isElemAbelian_map φ (burnsideF429b_U5_V_comm hK) (burnsideF429b_U5_V_sq hK))
    ?_ ?_ ?_
  ·
    intro B hBS hBe
    have hBc := isMulCommutative_iff_of_setLike.mp hBe.1
    have hB2 : ∀ x ∈ B, x * x = 1 := fun x hx => by rw [← sq]; exact hBe.2 x hx
    have hB₀U : B.comap φ ≤ hypProjUnitriangular hK 2 1 := fun y hy => by
      have hy' : φ y ∈ (hypProjUnitriangular hK 2 1).map φ := hS ▸ hBS hy
      exact (Subgroup.mem_map_iff_mem hφ).1 hy'
    have hmap : (B.comap φ).map φ = B := Subgroup.map_comap_eq_self (hBS.trans hle)
    rcases burnsideF429b_U5_elemAb hK hB₀U
        (fun x hx y hy => hφ (by rw [map_mul, map_mul]; exact hBc _ hx _ hy))
        (fun x hx => hφ (by rw [map_mul, map_one]; exact hB2 _ hx)) with h | h
    · left
      rw [← hmap]
      exact Subgroup.map_mono h
    · right
      rw [hRcard, ← hmap, Subgroup.card_map_of_injective hφ]
      exact h.trans_lt hlt
  ·
    intro A hAT hAe hAS
    obtain ⟨t, htA, htS⟩ := SetLike.not_le_iff_exists.1 hAS
    have hinvA : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hAe.2 a ha
    have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := isMulCommutative_iff_of_setLike.mp hAe.1
    have hA1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := by
      refine burnsideF429b_card_le_two_mul htA fun a ha haS => ?_
      refine hmemS _ (hAT (A.mul_mem htA ha)) (burnsideF429b_mem_of_conjAut_inner hc Ψ ?_)
      have hE := burnsideF429b_U5_mul_mem_Eext hK (hstab t (hT.1 (hAT htA)))
        (hstab a (hT.1 (hAT ha))) (burnsideF429b_conjAut_sq Ψ (hinvA t htA))
        (burnsideF429b_conjAut_sq Ψ (hinvA a ha)) (hnotS t (hAT htA) htS)
        (hnotS a (hAT ha) haS)
      rw [← burnsideF429b_conjAut_mul] at hE
      have hta2 : (t * a) ^ 2 ^ 1 = 1 := by
        rw [pow_one, sq]
        calc t * a * (t * a) = t * (a * t) * a := by group
          _ = t * (t * a) * a := by rw [hcommA a ha t htA]
          _ = (t * t) * (a * a) := by group
          _ = 1 := by rw [hinvA t htA, hinvA a ha, one_mul]
      obtain ⟨u, -, hu⟩ := (borelAutDiag_u5 hK).E_two _ hE 1 (by
        rw [← burnsideF429b_conjAut_pow, hta2, burnsideF429b_conjAut_one])
      exact ⟨u, hu.symm⟩
    have hA2 : Nat.card ↥(A ⊓ S) ≤ (2 ^ f) ^ 3 := by
      have hmap : ((A ⊓ S).comap φ).map φ = A ⊓ S :=
        Subgroup.map_comap_eq_self (inf_le_right.trans hle)
      rw [← hmap, Subgroup.card_map_of_injective hφ]
      have hB₀U : (A ⊓ S).comap φ ≤ hypProjUnitriangular hK 2 1 := fun y hy => by
        have hy' : φ y ∈ (hypProjUnitriangular hK 2 1).map φ := hS ▸ hy.2
        exact (Subgroup.mem_map_iff_mem hφ).1 hy'
      rcases burnsideF429b_U5_elemAb hK hB₀U
          (fun x hx y hy => hφ (by rw [map_mul, map_mul]; exact hcommA _ hx.1 _ hy.1))
          (fun x hx => hφ (by rw [map_mul, map_one]; exact hinvA _ hx.1)) with h | h
      · exact burnsideF429b_U5_card_fixed_V hK (hstab t (hT.1 (hAT htA)))
          (burnsideF429b_conjAut_sq Ψ (hinvA t htA)) (hnotS t (hAT htA) htS) _ h
          fun y hy => burnsideF429b_conjAut_fix Ψ (by rw [← hφx]; exact hcommA t htA _ hy.1)
      · exact h
    calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := hA1
      _ ≤ 2 * (2 ^ f) ^ 3 := Nat.mul_le_mul_left 2 hA2
      _ < (2 ^ f) ^ 4 := hlt2
      _ = Nat.card ↥(V.map φ) := hRcard.symm
  ·
    rintro x ⟨hxT, hxR⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hT.2.1 ⟨x, hxT⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    refine hmemS x hxT (burnsideF429b_mem_of_conjAut_inner hc Ψ ?_)
    refine burnsideF429b_U5_inner_of_fix_V hK (hstab x (hT.1 hxT)) (fun y hy => ?_)
      (n := n) (by rw [← burnsideF429b_conjAut_pow, hn, burnsideF429b_conjAut_one])
    refine burnsideF429b_conjAut_fix Ψ ?_
    rw [← hφx]
    exact (Subgroup.mem_centralizer_iff.1 hxR _ (Subgroup.mem_map_of_mem φ hy)).symm

end C6U5

end CFSG.ASVolI
