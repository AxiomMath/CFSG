module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod3A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4

variable {K : Type} [Field K] [Finite K]

private theorem s16c11_case5_conj_congr_comp (m : MulAut (VM K)) :
    (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.congr m).toMonoidHom =
      MonoidHom.id (MulAut (VM K)) := by
  apply MonoidHom.ext
  intro x
  change (MulAut.conj m⁻¹) ((MulAut.congr m) x) = x
  rw [CFSG.Quasithin.H13.S127.Mod.congr_eq, MulAut.conj_apply, inv_inv]
  group

private theorem s16c11_case5_map_conj_map_congr (m : MulAut (VM K))
    (A : Subgroup (MulAut (VM K))) :
    (A.map (MulAut.congr m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map, s16c11_case5_conj_congr_comp, Subgroup.map_id]

theorem s16c11_case5_torus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {S : Subgroup (MulAut (VM K))}
    (hSN : S ≤ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))) ⊓
      Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))))
    (hS2 : IsPGroup 2 ↥S)
    (hSodd : ¬ 2 ∣ S.relIndex (Subgroup.normalizer ((rho (K := K)).range :
      Set (MulAut (VM K))) ⊓ Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))))) :
    ∃ D : Subgroup (MulAut (VM K)), D ≤ (rho (K := K)).range ∧ Nat.card ↥D = 3 ∧
      D ⊓ s16c11C5Scal K = ⊥ ∧
      ∀ A ∈ E3.aSet 2 S, D ≤ Subgroup.normalizer (A : Set (MulAut (VM K))) := by
  classical
  haveI : Finite (MulAut (VM K)) := inferInstance
  haveI : CharP K 2 := s16c11_case5_charP hK
  have hSN' : S ≤ s16c11_case5_N1 (K := K) := by
    unfold s16c11_case5_N1 s16c11_case5_Omega
    exact hSN
  obtain ⟨m, hmN1, hmS⟩ :=
    CFSG.Quasithin.H13.S127.Mod.exists_conj_le
      (H := s16c11_case5_N1 (K := K)) (S := s16c11_case5_S0 (K := K)) (A := S)
      (s16c11_case5_S0_le_N1 (K := K))
      (s16c11_case5_isSylowIn_S0 (K := K) hK).isPGroup
      (s16c11_case5_isSylowIn_S0 (K := K) hK).not_dvd_relIndex hSN' hS2
  unfold s16c11_case5_N1 s16c11_case5_Omega at hmN1
  have hmNo : m ∈ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K))) :=
    (Subgroup.mem_inf.mp hmN1).1
  have hmC : m ∈ Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))) :=
    (Subgroup.mem_inf.mp hmN1).2
  refine ⟨(s16c11_case5_D0 (K := K)).map (MulAut.conj m⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  ·
    have hmapΩ : (rho (K := K)).range.map (MulAut.conj m⁻¹).toMonoidHom =
        (rho (K := K)).range :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hmNo)
    calc (s16c11_case5_D0 (K := K)).map (MulAut.conj m⁻¹).toMonoidHom
        ≤ (rho (K := K)).range.map (MulAut.conj m⁻¹).toMonoidHom :=
          Subgroup.map_mono s16c11_case5_D0_le_range
      _ = (rho (K := K)).range := hmapΩ
  ·
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj m⁻¹).toMonoidHom)
      (MulAut.conj m⁻¹).injective, s16c11_case5_card_D0 hK]
  ·
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxD, hxScal⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hxD
    change (MulAut.conj m⁻¹) d ∈ s16c11C5Scal K at hxScal
    change (MulAut.conj m⁻¹) d = 1
    rw [MulAut.conj_apply, inv_inv] at hxScal ⊢
    have hmx := (Subgroup.mem_centralizer_iff.mp hmC) (m⁻¹ * d * m) hxScal
    have hxd : d = m⁻¹ * d * m := by
      calc d = m * (m⁻¹ * d * m) * m⁻¹ := by group
        _ = (m⁻¹ * d * m) * m * m⁻¹ := by rw [← hmx]
        _ = m⁻¹ * d * m := by group
    have hdScal : d ∈ s16c11C5Scal K := hxd ▸ hxScal
    have hmem : d ∈ s16c11_case5_D0 (K := K) ⊓ s16c11C5Scal K := ⟨hd, hdScal⟩
    rw [s16c11_case5_D0_inf_Scal hK] at hmem
    rw [Subgroup.mem_bot.mp hmem]
    group
  ·
    intro A hA
    have hA'S0 : A.map (MulAut.congr m).toMonoidHom ≤ s16c11_case5_S0 (K := K) := by
      rintro y ⟨a, ha, rfl⟩
      change (MulAut.congr m) a ∈ s16c11_case5_S0 (K := K)
      rw [CFSG.Quasithin.H13.S127.Mod.congr_eq]
      exact hmS a (hA.1 ha)
    have hAmem : A.map (MulAut.congr m).toMonoidHom ∈
        E3.aSet 2 (s16c11_case5_S0 (K := K)) :=
      CFSG.Quasithin.H13.S127.Mod.aSet_map_congr hA m hA'S0
    have hD0N := s16c11_case5_D0_le_normalizer_of_mem_aSet hK hAmem
    have hstep : (s16c11_case5_D0 (K := K)).map (MulAut.conj m⁻¹).toMonoidHom ≤
        Subgroup.normalizer (((A.map (MulAut.congr m).toMonoidHom).map
          (MulAut.conj m⁻¹).toMonoidHom) : Set (MulAut (VM K))) :=
      (Subgroup.map_mono hD0N).trans
        (Subgroup.le_normalizer_map (MulAut.conj m⁻¹).toMonoidHom)
    rw [s16c11_case5_map_conj_map_congr m A] at hstep
    exact hstep

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
