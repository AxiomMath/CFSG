module

public import CFSG.Sporadic.Schreier.Co3First
public import CFSG.Quasithin.SteinbergBTSymplecticThreeFreeTriangular

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

open scoped Pointwise
open CFSG.Open CFSG.Sporadic.Schreier.Co3 CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.Quasithin.SteinbergBT

theorem co3T_le_co3M :
    co3T ≤ co3M := by
  rw [co3M_eq_centralizer]
  exact le_inf co3T_le_P co3T_le_centralizer_Z

theorem eq_co3T_of_le_co3M
    {Y : Subgroup (Equiv.Perm (Fin 276))} (hTY : co3T ≤ Y) (hYM : Y ≤ co3M)
    (h3 : ¬ 3 ∣ Nat.card Y) : Y = co3T := by
  classical
  have hκX : ∀ m : co3M, co3Kappa m ∈ co3X36 := fun m => by
    rw [← co3Kappa_range]
    exact ⟨m, rfl⟩
  let φ : co3M →* StatedSp 3 (ZMod 2) :=
    co3Sp6Equiv.symm.toMonoidHom.comp (co3Kappa.codRestrict co3X36 hκX)
  have hφker : φ.ker = co3Kappa.ker := by
    ext m
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, MonoidHom.codRestrict_apply]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext (by simpa using h)⟩
  have hTM := co3T_le_co3M
  set T' := co3T.subgroupOf co3M with hT'
  set Y' := Y.subgroupOf co3M with hY'
  have hTY' : T' ≤ Y' := fun x hx => hTY hx
  have hkerT : φ.ker ≤ T' := by
    rw [hφker, co3Kappa_ker, Subgroup.zpowers_le, hT', Subgroup.mem_subgroupOf]
    exact co3Z_mem_T
  have hcardT' : Nat.card T' = 1024 := by
    rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, card_co3T]
  have hcardφT : Nat.card (T'.map φ) = 512 := by
    let ψ : T' →* StatedSp 3 (ZMod 2) := φ.comp T'.subtype
    have hr : ψ.range = T'.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hk : Nat.card ψ.ker = 2 := by
      have : ψ.ker = φ.ker.subgroupOf T' := by
        ext t
        rfl
      rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerT).toEquiv, hφker,
        card_ker_co3Kappa]
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hk, hr, hcardT'] at h
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPg : IsPGroup 2 (T'.map φ) := IsPGroup.of_card (n := 9) (by rw [hcardφT]; norm_num)
  have hidx : ¬ 2 ∣ (T'.map φ).index := by
    have h := (T'.map φ).card_mul_index
    rw [hcardφT, card_statedSp_three_two] at h
    have hi : (T'.map φ).index = 2835 := by omega
    rw [hi]
    decide
  have hcardB : Nat.card (borelSubgroup 3 (ZMod 2)) = 512 := by
    rw [card_borelSubgroup, Nat.card_zmod]
    norm_num
  have hBPg : IsPGroup 2 (borelSubgroup 3 (ZMod 2)) :=
    IsPGroup.of_card (n := 9) (by rw [hcardB]; norm_num)
  have hBidx : ¬ 2 ∣ (borelSubgroup 3 (ZMod 2)).index := by
    have h := (borelSubgroup 3 (ZMod 2)).card_mul_index
    rw [hcardB, card_statedSp_three_two] at h
    have hi : (borelSubgroup 3 (ZMod 2)).index = 2835 := by omega
    rw [hi]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 3 (ZMod 2)) (hBPg.toSylow hBidx)
    (hPg.toSylow hidx)
  have hgB : MulAut.conj g • borelSubgroup 3 (ZMod 2) = T'.map φ := by
    have h1 := congrArg
      (fun S : Sylow 2 (StatedSp 3 (ZMod 2)) => (S : Subgroup ↥(StatedSp 3 (ZMod 2)))) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    exact h1
  let A : Subgroup (StatedSp 3 (ZMod 2)) :=
    (Y'.map φ).map (MulAut.conj g⁻¹ : StatedSp 3 (ZMod 2) ≃* _).toMonoidHom
  have hBA : borelSubgroup 3 (ZMod 2) ≤ A := by
    intro x hx
    have hcx : MulAut.conj g x ∈ T'.map φ := by
      rw [← hgB]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hx
    refine Subgroup.mem_map.mpr ⟨MulAut.conj g x, Subgroup.map_mono hTY' hcx, ?_⟩
    simp [MulAut.conj_apply]
    group
  have hcardA : Nat.card A = Nat.card (Y'.map φ) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have h3A : ¬ 3 ∣ Nat.card A := by
    intro h
    apply h3
    have h1 : Nat.card (Y'.map φ) ∣ Nat.card Y' := Subgroup.card_map_dvd _ _
    rw [hY', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv] at h1
    exact (hcardA ▸ h).trans h1
  have hAB : A ≤ borelSubgroup 3 (ZMod 2) :=
    (even_symplectic_three_free_sylow_overgroups_are_triangular).1 A
      (unipotent_le_borelSubgroup.trans hBA) h3A
  have hYT : Y'.map φ = T'.map φ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hTY') ?_).symm
    rw [hcardφT, ← hcardA, ← hcardB]
    exact Subgroup.card_le_of_le hAB
  have hY'T' : Y' ≤ T' := by
    calc Y' ≤ (Y'.map φ).comap φ := Subgroup.le_comap_map _ _
      _ = T' := by rw [hYT, Subgroup.comap_map_eq, sup_eq_left.2 hkerT]
  refine le_antisymm (fun y hy => ?_) hTY
  have := hY'T' (show (⟨y, hYM hy⟩ : co3M) ∈ Y' from hy)
  exact this

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K
