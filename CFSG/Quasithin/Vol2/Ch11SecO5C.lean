module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG.O5

open CFSG.GorensteinWalter

theorem inverts_map_conj {G : Type*} [Group G] {U : Subgroup G} {s : G} (g : G)
    (hs : ∀ x ∈ U, s * x * s⁻¹ = x⁻¹) :
    ∀ y ∈ U.map (MulAut.conj g).toMonoidHom, (g * s * g⁻¹) * y * (g * s * g⁻¹)⁻¹ = y⁻¹ := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * s * g⁻¹ * (g * x * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * (s * x * s⁻¹) * g⁻¹ := by group
    _ = (g * x * g⁻¹)⁻¹ := by rw [hs x hx]; group

theorem reflection_mul {G : Type*} [Group G] {U : Subgroup G} (hUcyc : IsCyclic U) {w u₀ : G}
    (hwU : w ∉ U) (hwsq : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) (hu₀ : u₀ ∈ U) :
    w * u₀ ≠ 1 ∧ (w * u₀) * (w * u₀) = 1 ∧ ∀ x ∈ U, (w * u₀) * x * (w * u₀)⁻¹ = x⁻¹ := by
  have hw : w⁻¹ = w := inv_eq_of_mul_eq_one_left hwsq
  refine ⟨fun h => hwU ?_, ?_, fun x hx => ?_⟩
  · rw [eq_inv_of_mul_eq_one_left h]
    exact U.inv_mem hu₀
  · calc (w * u₀) * (w * u₀) = (w * u₀ * w⁻¹) * u₀ := by rw [hw]; group
      _ = 1 := by rw [hwinv u₀ hu₀]; group
  · let : CommGroup U := IsCyclic.commGroup
    have hc : u₀ * x * u₀⁻¹ = x := by
      have := congrArg Subtype.val (mul_comm (⟨u₀, hu₀⟩ : U) ⟨x, hx⟩)
      simp only [Subgroup.coe_mul] at this
      rw [this]
      group
    calc (w * u₀) * x * (w * u₀)⁻¹ = w * (u₀ * x * u₀⁻¹) * w⁻¹ := by group
      _ = x⁻¹ := by rw [hc, hwinv x hx]

variable {K : Type} [Field K] [Finite K]

theorem exists_inverted_conj_of_reflection (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {t : PGL2 K} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    {U : Subgroup (PGL2 K)} {w : PGL2 K} (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hUJ : ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) :
    ∃ g : PGL2 K, ∀ y ∈ U.map (MulAut.conj g).toMonoidHom, t * y * t⁻¹ = y⁻¹ := by
  set J : Subgroup (PGL2 K) := commutator (PGL2 K) with hJdef
  have hJ : J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  have hJi : J.index = 2 := by rw [hJ]; exact pgl2_psl2Range_index_eq_two K hK
  obtain ⟨u₀, hu₀U, hu₀J⟩ := IsConcreteLE.not_le_iff_exists.mp hUJ
  rw [← hJ] at hu₀J
  obtain ⟨hw1', hw2', hwinv'⟩ := reflection_mul hUcyc hwU hwsq hwinv hu₀U
  have hw1 : w ≠ 1 := fun h => hwU (h ▸ U.one_mem)
  have hinv : ∀ {s : PGL2 K}, s ≠ 1 → s * s = 1 → BenderSuzuki.PFAppendixIII.IsInvolution s :=
    fun hs1 hs2 => ⟨hs1, by rw [pow_two]; exact hs2⟩
  obtain ⟨s, hs1, hs2, hsinv, hsJ⟩ : ∃ s : PGL2 K, s ≠ 1 ∧ s * s = 1 ∧
      (∀ x ∈ U, s * x * s⁻¹ = x⁻¹) ∧ (s ∈ J ↔ t ∈ J) := by
    have hmem : w * u₀ ∈ J ↔ ¬ w ∈ J := by
      rw [Subgroup.mul_mem_iff_of_index_two hJi]
      tauto
    by_cases hwJ : (w ∈ J ↔ t ∈ J)
    · exact ⟨w, hw1, hwsq, hwinv, hwJ⟩
    · exact ⟨w * u₀, hw1', hw2', hwinv', by rw [hmem]; tauto⟩
  have hconj : IsConj s t := by
    by_cases htJ : t ∈ J
    · obtain ⟨g, -, hg⟩ := pgl2_inner_involutions_conjugate hK hcard (hsJ.mpr htJ) (hinv hs1 hs2)
        htJ (hinv ht1 ht2)
      exact isConj_iff.mpr ⟨g, hg⟩
    · exact pgl2_outer_involutions_conjugate K hK hcard (hinv hs1 hs2) (hinv ht1 ht2)
        (fun h => htJ (hsJ.mp h)) htJ
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  exact ⟨g, inverts_map_conj g hsinv⟩

end CFSG.Quasithin.Vol2.Ch11.SecG.O5
