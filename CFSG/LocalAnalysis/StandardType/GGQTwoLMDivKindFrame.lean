module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindDiag
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}
  {L0 : Type} [Group L0]

theorem qTwoLMDivKind_map_diag_eq {E : Type} [Group E] (πSU : Su F0 2 1 m →* L0)
    (ρ : E →* MulAut L0)
    (hdiag : ∀ b : E, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u')
    (b : E) {u : Su F0 2 1 m} (hu : u ∈ qTwoLMDivKind_diag F0 m) : ρ b (πSU u) = πSU u := by
  obtain ⟨g, ⟨e, he⟩, hgu⟩ := hdiag b
  obtain ⟨d, hd⟩ := hu
  obtain ⟨u', hu', hρ⟩ := hgu u
  have hcomm : g * (u : GL (Fin m) F0) = (u : GL (Fin m) F0) * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he, hd]
    exact Matrix.commute_diagonal e d
  have h_eq : (u' : GL (Fin m) F0) = (u : GL (Fin m) F0) := by
    rw [hu', hcomm]
    group
  rw [hρ, Subtype.ext h_eq]

private theorem qTwoLMDivKindFrame_conj_eq {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (c : ↥L →* L0)
    (hc_ker : c.ker ≤ Subgroup.center ↥L) (hc_two : IsPGroup 2 c.ker)
    (πSU : Su F0 2 1 m →* L0) (ρ : ↥Bs →* MulAut L0)
    (hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u')
    (hρ : ∀ (b : ↥Bs) (l : ↥L),
      c ⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ =
        ρ b (c l))
    {t : ↥L} (ht : t ^ 3 = 1) {u : Su F0 2 1 m} (hu : u ∈ qTwoLMDivKind_diag F0 m)
    (htu : πSU u = c t) (b : ↥Bs) : (b : G) * t * (b : G)⁻¹ = t := by
  have htG : (t : G) ^ 3 = 1 := by
    simpa using congrArg (fun x : ↥L => (x : G)) ht
  let t' : ↥L := ⟨(b : G) * t * (b : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hN b.2) t).mp t.2⟩
  have ht'_eq : (t' : G) = (b : G) * t * (b : G)⁻¹ := rfl
  have hct' : c t' = c t := by
    have h1 : c t' = ρ b (c t) := hρ b t
    rw [h1, ← htu]
    exact qTwoLMDivKind_map_diag_eq πSU ρ hdiag b hu
  let δ : ↥L := t⁻¹ * t'
  have hδ_ker : δ ∈ c.ker := by
    rw [MonoidHom.mem_ker]
    change c (t⁻¹ * t') = 1
    rw [map_mul, map_inv, hct']
    group
  have ht'_pow : t' ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ht'_eq, Subgroup.coe_one, conj_pow, htG]
    group
  have hδ_pow : δ ^ 3 = 1 := by
    have hcomm : Commute t δ := (Subgroup.mem_center_iff.mp (hc_ker hδ_ker)) t
    have ht'_δ : t' = t * δ := by
      calc t' = t * (t⁻¹ * t') := by group
        _ = t * δ := rfl
    have hcube : (t * δ) ^ 3 = t ^ 3 * δ ^ 3 := hcomm.mul_pow 3
    rw [← ht'_δ, ht'_pow, ht] at hcube
    simpa using hcube.symm
  have hδ_one : δ = 1 := by
    have h := hc_two.orderOf_coprime (by norm_num : Nat.Coprime 2 3) ⟨δ, hδ_ker⟩
    rw [Subgroup.orderOf_mk] at h
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes h dvd_rfl (orderOf_dvd_of_pow_eq_one hδ_pow))
  exact congrArg Subtype.val (inv_mul_eq_one.mp hδ_one).symm

theorem qTwoLMDivKind_mem_of_cube {B Bs L : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (c : ↥L →* L0)
    (hc_ker : c.ker ≤ Subgroup.center ↥L) (hc_two : IsPGroup 2 c.ker)
    (πSU : Su F0 2 1 m →* L0) (ρ : ↥Bs →* MulAut L0)
    (hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u')
    (hρ : ∀ (b : ↥Bs) (l : ↥L),
      c ⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ =
        ρ b (c l))
    {t : ↥L} (ht : t ^ 3 = 1) {u : Su F0 2 1 m} (hu : u ∈ qTwoLMDivKind_diag F0 m)
    (htu : πSU u = c t) : (t : G) ∈ Bs := by
  refine hBs.2.2.2 (t : G) (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    (by simpa using congrArg (fun x : ↥L => (x : G)) ht)
  have h : b * (t : G) * b⁻¹ = t :=
    qTwoLMDivKindFrame_conj_eq hN c hc_ker hc_two πSU ρ hdiag hρ ht hu htu ⟨b, hb⟩
  calc b * (t : G) = b * t * b⁻¹ * b := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = t * b := by rw [h]

end CFSG.StandardType.QTwo

end
