module

public import CFSG.Quasithin.MS93.S510Tv
public import CFSG.Quasithin.MS93.S5B58Sp

public section

namespace CFSG.Quasithin.MS93.S59R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

theorem centralizer_sup {Γ : Type*} [Group Γ] (A B : Subgroup Γ) :
    Subgroup.centralizer ((A ⊔ B : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer (A : Set Γ) ⊓ Subgroup.centralizer (B : Set Γ) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
  · rintro x ⟨hA, hB⟩
    have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set Γ) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hA y hy)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hB y hy)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy))

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section InM

theorem relIndex_centralizer_eq_pow_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) :
    ∃ r : ℕ, (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = (2 ^ k) ^ r := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have h1 := S5B.relIndex_centralizer_mul_card h hlift c hEM
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  rw [MSP.card_V4, hFq, Module.natCard_eq_pow_finrank (K := F), hFq] at h1
  have hd4 : Module.finrank F (MSP.fixSp ((E.subgroupOf M).map a)) ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp ((E.subgroupOf M).map a))
    simpa using this
  refine ⟨4 - Module.finrank F (MSP.fixSp ((E.subgroupOf M).map a)), ?_⟩
  have e : (2 ^ k) ^ 4 = (2 ^ k) ^ (4 - Module.finrank F (MSP.fixSp ((E.subgroupOf M).map a))) *
      (2 ^ k) ^ Module.finrank F (MSP.fixSp ((E.subgroupOf M).map a)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e] at h1
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h1

theorem relIndex_le_of_relIndex_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k) :
    (Subgroup.centralizer (Uq M T L : Set G)).relIndex E ≤ 2 ^ k := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  obtain ⟨p, hp, -, -, hX⟩ := S510.exists_point_of_relIndex h hd hEM hrel
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hker : a.ker ≤ (Subgroup.centralizer (Uq M T L : Set G)).subgroupOf M := by
    intro m hm
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : a m = 1 := hm
    have hconj : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn m.2) u).1 hu
    have hv := c.vec_commutator m ⟨u, hu⟩ hconj
    rw [h1, MSP.mat_one, Matrix.one_mulVec, sub_self] at hv
    have h0 := (c.vec_eq_zero_iff _).1 hv
    have h2 := hlift m m.2 u hu h0.2
    calc u * m = (m : G) * u * (m : G)⁻¹ * m := by rw [h2]
      _ = m * u := by group
  rw [← Subgroup.relIndex_subgroupOf hEM]
  calc ((Subgroup.centralizer (Uq M T L : Set G)).subgroupOf M).relIndex (E.subgroupOf M)
      ≤ a.ker.relIndex (E.subgroupOf M) :=
        Subgroup.relIndex_le_of_le_left hker (by
          rw [Subgroup.relIndex]
          exact Subgroup.index_ne_zero_of_finite)
    _ = Nat.card ((E.subgroupOf M).map a) := Subgroup.relIndex_ker (E.subgroupOf M) a
    _ ≤ Nat.card (MSP.xPoint p) := Subgroup.card_le_of_le hX
    _ = 2 ^ k := by rw [MSP.card_xPoint hp, hFq]

end InM

section Vertex

theorem relIndex_centralizer_eq_pow (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) :
    ∃ r : ℕ, (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = (2 ^ k) ^ r := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M]
  exact relIndex_centralizer_eq_pow_M h hd hE₀M

theorem relIndex_le_of_relIndex (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k) :
    (Subgroup.centralizer (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal)).relIndex E ≤
      2 ^ k := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S5B.relIndex_centralizer_imM h.le hE₀M (Uq_le h.L_le)]
  exact relIndex_le_of_relIndex_M h hd hE₀M hrel

theorem relIndex_centralizer_one_or (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) {u : (puAmalgam h.le).Universal} (hu : u ∈ stab _ δ) :
    (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L δ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) = 1 ∨
      2 ^ k ≤ (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L δ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) := by
  set U := S5.uSub h.le L δ
  set N := U ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)
  have hE₂ : E ⊔ Subgroup.zpowers u ≤ stab _ δ :=
    sup_le hE ((Subgroup.zpowers_le).2 hu)
  obtain ⟨r₁, hr₁⟩ := relIndex_centralizer_eq_pow h hd hδ hE
  obtain ⟨r₂, hr₂⟩ := relIndex_centralizer_eq_pow h hd hδ hE₂
  have hC : Subgroup.centralizer ((E ⊔ Subgroup.zpowers u : Subgroup _) :
      Set (puAmalgam h.le).Universal) =
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) := by
    rw [centralizer_sup, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hA : Subgroup.centralizer ((E ⊔ Subgroup.zpowers u : Subgroup _) :
      Set (puAmalgam h.le).Universal) ⊓ U =
      Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) ⊓ N := by
    rw [hC]
    ext x
    simp only [N, Subgroup.mem_inf]
    tauto
  have hAN : Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) ⊓ N ≤ N := inf_le_right
  have hNU : N ≤ U := inf_le_left
  have key := Subgroup.relIndex_mul_relIndex _ _ _ hAN hNU
  have hk1 : (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) ⊓ N).relIndex N =
      (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal)).relIndex N :=
    Subgroup.inf_relIndex_right _ _
  have hk2 : (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) ⊓ N).relIndex U =
      (2 ^ k) ^ r₂ := by
    rw [← hA, Subgroup.inf_relIndex_right]
    exact hr₂
  rw [hk1, hk2] at key
  have hNrel : N.relIndex U = (2 ^ k) ^ r₁ := by
    rw [show N = Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ⊓ U from inf_comm _ _,
      Subgroup.inf_relIndex_right, hr₁]
  rw [hNrel] at key
  have hq : 2 ≤ 2 ^ k := Nat.le_self_pow (by have := hd.1; omega) 2
  set X := (Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal)).relIndex N
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact absurd key.symm (by positivity)
  rcases le_or_gt r₂ r₁ with hle | hlt
  · left
    have h1 : X * (2 ^ k) ^ r₁ ≤ 1 * (2 ^ k) ^ r₁ := by
      rw [key, one_mul]
      exact Nat.pow_le_pow_right (by omega) hle
    have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
    omega
  · right
    have e : (2 ^ k) ^ r₂ = (2 ^ k) ^ (r₂ - r₁) * (2 ^ k) ^ r₁ := by
      rw [← pow_add]
      congr 1
      omega
    rw [e] at key
    have hX : X = (2 ^ k) ^ (r₂ - r₁) := Nat.eq_of_mul_eq_mul_right (by positivity) key
    rw [hX]
    calc 2 ^ k = (2 ^ k) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ k) ^ (r₂ - r₁) := Nat.pow_le_pow_right (by omega) (by omega)

end Vertex

end CFSG.Quasithin.MS93.S59R
