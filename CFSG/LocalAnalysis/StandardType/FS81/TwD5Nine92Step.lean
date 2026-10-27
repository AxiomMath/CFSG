module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Struct
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Base
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92StepAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem exists_eq_mul_zpow_of_conj_mem_sup {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) {y : G} (hy : y ∈ Subgroup.centralizer ({B.b 2} : Set G))
    (hyJ : ∀ x ∈ nineJ K (B.b 2),
      y * x * y⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    (hyP : y * b₀ * y⁻¹ ∈ Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)) :
    ∃ d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G),
      ∃ k : ℤ, y = d * B.b 2 ^ k := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G)
  let J : Subgroup G := nineJ K (B.b 2)
  let P : Subgroup G := Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)
  have hKC0 : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.2.1
  have hJK : J ≤ K := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hJH : J ≤ H := by
    dsimp only [J]
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hy2 : y * B.b 2 * y⁻¹ = B.b 2 := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [h]
    group
  have hyN : y ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : Subgroup.map (MulAut.conj y).toMonoidHom P ≤ P := by
      rw [show P = Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) from rfl,
        Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (Subgroup.zpowers_le.mpr hyP) ?_
      rw [Subgroup.zpowers_le]
      change y * B.b 2 * y⁻¹ ∈ Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)
      rw [hy2]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (B.b 2))
    have hcard : Nat.card ↥(Subgroup.map (MulAut.conj y).toMonoidHom P) = Nat.card ↥P :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hyCJ : ∀ x ∈ J, y * x * y⁻¹ = x :=
    centralizes_nineJ_of_forall_orderOf_eq_pow_three hstd hB hrec hy hyJ
      (by simpa only [P] using hyN)
  have hKCs : K ⊓ H = Subgroup.zpowers (B.b 2) ⊔ J := by
    simpa only [H, J] using inf_centralizer_eq_zpowers_sup_nineJ hstd hB hrec
  have hcommBJ : ∀ a ∈ Subgroup.zpowers (B.b 2), ∀ b ∈ J, Commute a b := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbH : b ∈ H := hJH hb
    have hcomm_b : Commute b (B.b 2) := Subgroup.mem_centralizer_singleton_iff.mp hbH
    exact hcomm_b.symm.zpow_left m
  have hyCent : ∀ k ∈ K ⊓ H, y * k * y⁻¹ = k := by
    intro k hk
    rw [hKCs] at hk
    obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hcommBJ).mp hk
    have ha' : y * a * y⁻¹ = a := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [show y * B.b 2 ^ m * y⁻¹ = (y * B.b 2 * y⁻¹) ^ m by rw [conj_zpow], hy2]
    calc y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      _ = a * b := by rw [ha', hyCJ b hb]
  have hybj : ∀ j : Fin (5 + 1), j ≠ 0 → y * B.b j * y⁻¹ = B.b j := by
    intro j hj
    refine hyCent (B.b j) ⟨hB.2.2 j hj, ?_⟩
    change B.b j ∈ Subgroup.centralizer ({B.b 2} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (B.comm j 2).eq
  obtain ⟨c, hcne, hce⟩ := exists_zmod_eq_of_conj_mem_sup hstd hB hrec
    (hybj 1 (by decide)) hyP
  have hy0 : y * b₀ * y⁻¹ = b₀ :=
    conj_b₀_eq_self_of_exists_zmod hB.2.1 hrec hcne hce hybj
  have hyC0 : y ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * b₀ = (y * b₀ * y⁻¹) * y := by group
      _ = b₀ * y := by rw [hy0]
  exact exists_eq_mul_zpow_of_mem_centralizer_inf hstd hB hrec ⟨hyC0, hy⟩ hyCJ

end CFSG.StandardType.FrameRoute.FS81

end
