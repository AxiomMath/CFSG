module

public import CFSG.Quasithin.Vol2.Ch11SecS12O
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3I

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem le_normalizer_Ptheta_of_le (hF : Nat.card F = 4)
    (hS0 : CFSG.QuasithinUnique.IsSylowTwoOf (S0P F) ⊤) {P : Subgroup (PGL3 F)} (hPt : P ≠ ⊤)
    (hNP : Subgroup.normalizer (S0P F : Set (PGL3 F)) ≤ P) :
    ∃ j : Fin 2, P ≤ Subgroup.normalizer (Ptheta F j : Set (PGL3 F)) := by
  have hsup := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.sup_normalizer_S0P hF hS0
  set H := (P ⊓ (thetaP F).range).comap (thetaP F) with hH
  have hUH : projUnitriangular 3 F ≤ H := by
    intro u hu
    have h1 : thetaP F u ∈ S0P F := ⟨u, hu, rfl⟩
    exact ⟨hNP (Subgroup.le_normalizer h1), ⟨u, rfl⟩⟩
  have hHt : H ≠ ⊤ := by
    intro hH'
    apply hPt
    rw [eq_top_iff, ← hsup]
    refine sup_le hNP ?_
    rintro _ ⟨y, rfl⟩
    have : y ∈ H := hH' ▸ Subgroup.mem_top y
    exact this.1
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hHt
  have hUM : projUnitriangular 3 F ≤ M := hUH.trans hHM
  obtain ⟨j, rfl⟩ := ((residual_std hF).2.2.1 M hUM).mp (IsCoatom.covBy_top hM)
  refine ⟨j, fun p hp => ?_⟩
  have hp' : p ∈ Subgroup.normalizer (S0P F : Set (PGL3 F)) ⊔ (thetaP F).range :=
    hsup ▸ Subgroup.mem_top p
  have hRn : ((thetaP F).range).Normal := by
    rw [range_thetaP_eq hF]
    infer_instance
  obtain ⟨n, hn, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hp'
  refine Subgroup.mul_mem _ (normalizer_S0P_le j hn) (Subgroup.le_normalizer ?_)
  obtain ⟨y, rfl⟩ := hr
  have hyP : thetaP F y ∈ P := by
    have := P.mul_mem (P.inv_mem (hNP hn)) hp
    rwa [inv_mul_cancel_left] at this
  exact ⟨y, hHM ⟨hyP, ⟨y, rfl⟩⟩, rfl⟩

theorem exists_conj_normalizer (hF : Nat.card F = 4) {P : Subgroup (PGL3 F)}
    (hP : IsMaxParabolic2 ⊤ P) :
    ∃ c : PGL3 F, ∃ j : Fin 2, CFSG.QuasithinUnique.IsSylowTwoOf (S0P F) ⊤ ∧
      P.map (MulAut.conj c).toMonoidHom = Subgroup.normalizer (Ptheta F j : Set (PGL3 F)) := by
  obtain ⟨⟨-, S, hS, hNS⟩, hPt, hmax⟩ := hP
  obtain ⟨c₀, rfl⟩ := exists_conj_S0P hF hS
  have hS0 : CFSG.QuasithinUnique.IsSylowTwoOf (S0P F) ⊤ := by
    have := isSylowTwoOf_map (MulAut.conj c₀⁻¹) hS
    rwa [Subgroup.map_map, show (MulAut.conj c₀⁻¹).toMonoidHom.comp (MulAut.conj c₀).toMonoidHom =
      MonoidHom.id _ by ext x; simp [MulAut.conj_apply, mul_assoc], Subgroup.map_id] at this
  have hconj : ∀ Q : Subgroup (PGL3 F),
      (Q.map (MulAut.conj c₀).toMonoidHom).map (MulAut.conj c₀⁻¹).toMonoidHom = Q := fun Q => by
    rw [Subgroup.map_map, show (MulAut.conj c₀⁻¹).toMonoidHom.comp (MulAut.conj c₀).toMonoidHom =
      MonoidHom.id _ by ext x; simp [MulAut.conj_apply, mul_assoc], Subgroup.map_id]
  have hconj' : ∀ Q : Subgroup (PGL3 F),
      (Q.map (MulAut.conj c₀⁻¹).toMonoidHom).map (MulAut.conj c₀).toMonoidHom = Q := fun Q => by
    rw [Subgroup.map_map, show (MulAut.conj c₀).toMonoidHom.comp (MulAut.conj c₀⁻¹).toMonoidHom =
      MonoidHom.id _ by ext x; simp [MulAut.conj_apply, mul_assoc], Subgroup.map_id]
  have hNS' : Subgroup.normalizer ((S0P F).map (MulAut.conj c₀).toMonoidHom : Set (PGL3 F)) =
      (Subgroup.normalizer (S0P F : Set (PGL3 F))).map (MulAut.conj c₀).toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq _ _).symm
  set P' := P.map (MulAut.conj c₀⁻¹).toMonoidHom with hP'
  have hNP' : Subgroup.normalizer (S0P F : Set (PGL3 F)) ≤ P' := by
    rw [← hconj (Subgroup.normalizer (S0P F : Set (PGL3 F))), hP', ← hNS']
    exact Subgroup.map_mono (le_inf le_top le_rfl |>.trans hNS)
  have hP't : P' ≠ ⊤ := by
    intro h
    apply hPt
    rw [← hconj' P, ← hP', h, Subgroup.map_top_of_surjective _ (MulAut.conj c₀).surjective]
  obtain ⟨j, hj⟩ := le_normalizer_Ptheta_of_le hF hS0 hP't hNP'
  refine ⟨c₀⁻¹, j, hS0, le_antisymm hj ?_⟩
  have hQpar : IsParabolic2 ⊤
      ((Subgroup.normalizer (Ptheta F j : Set (PGL3 F))).map (MulAut.conj c₀).toMonoidHom) := by
    refine ⟨le_top, (S0P F).map (MulAut.conj c₀).toMonoidHom, hS, ?_⟩
    rw [top_inf_eq, hNS']
    exact Subgroup.map_mono (normalizer_S0P_le (F := F) j)
  have hQt : (Subgroup.normalizer (Ptheta F j : Set (PGL3 F))).map (MulAut.conj c₀).toMonoidHom ≠
      ⊤ := by
    intro h
    apply CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.normalizer_Ptheta_ne_top hF j
    rw [← hconj (Subgroup.normalizer (Ptheta F j : Set (PGL3 F))), h,
      Subgroup.map_top_of_surjective _ (MulAut.conj c₀⁻¹).surjective]
  have hPQ : P ≤ (Subgroup.normalizer (Ptheta F j : Set (PGL3 F))).map
      (MulAut.conj c₀).toMonoidHom := by
    rw [← hconj' P]
    exact Subgroup.map_mono hj
  have hQP := hmax _ hQpar hQt hPQ
  rw [← hconj (Subgroup.normalizer (Ptheta F j : Set (PGL3 F))), hQP]

theorem exists_conj_perfectCore (hF : Nat.card F = 4) {P : Subgroup (PGL3 F)}
    (hP : IsMaxParabolic2 ⊤ P) :
    ∃ c : PGL3 F, ∃ j : Fin 2, (perfectCore P).map (MulAut.conj c).toMonoidHom = Ptheta F j := by
  obtain ⟨c, j, hS0, hc⟩ := exists_conj_normalizer hF hP
  refine ⟨c, j, ?_⟩
  rw [map_perfectCore, hc]
  exact CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.perfectCore_normalizer_Ptheta hS0 hF j

end CFSG.Quasithin.H13.Ch4.B414.M
