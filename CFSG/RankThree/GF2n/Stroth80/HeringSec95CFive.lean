module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CThree

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {hc : Ctx M Q Z B} {n : ℕ} {t : G}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.isSingV_of_mem_comm_sup (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {x : G}
    (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t)
    (hA2 : ∀ v ∈ Vt M (LB M Q B) B Z t, IsSingV M Q Z B t ⁅x, v⁆) {s : G}
    (hsS : s ∈ (⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ ⊔ Z : Subgroup G)) :
    IsSingV M Q Z B t s := by
  classical
  obtain ⟨w, hw, hind, hEw, -, hvec, -⟩ := C.plane_facts hs hxL hxN
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  have ht : t ∈ LB M Q B := hs.mem
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  obtain ⟨hsV, a, b, hab⟩ := hvec s hsS
  obtain ⟨y, hy⟩ := exists_eichler_sub_eq' hQnd C.hQu hw C.hu0 hind a b
  obtain ⟨v, hv⟩ := exists_secVec_eq C.ψ y
  have hVRn : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht
  have h1 := secVec_comm C.φ C.ψ C.hψ hVRn ⟨x, hxR⟩ v
  rw [hEw, hv, hy, ← hab] at h1
  have hmem : ⁅x, (v : G)⁆ * s⁻¹ ∈ Z := (secVec_eq_iff C.ψ _ ⟨s, hsV⟩).mp h1
  obtain ⟨ρ, hρ, b', hb', hZ⟩ := hA2 v v.2
  refine ⟨ρ, hρ, b', hb', ?_⟩
  have e : s * (ρ * b' * ρ⁻¹)⁻¹ =
      (⁅x, (v : G)⁆ * s⁻¹)⁻¹ * (⁅x, (v : G)⁆ * (ρ * b' * ρ⁻¹)⁻¹) := by group
  rw [e]
  exact Z.mul_mem (Z.inv_mem hmem) hZ

end Coord

theorem exists_notCN_conj95 {hc : Ctx M Q Z B} {t g : G}
    (hgL : conjSubgroup g (LB M Q B) = LB M Q B) (hnot : ¬ conjSubgroup g (N1 hc t) ≤ N1 hc t) :
    ∃ x ∈ conjSubgroup g (N1 hc t), x ∉ hc.CN t := by
  by_contra hcon
  push Not at hcon
  apply hnot
  intro x hx
  have hxL : x ∈ LB M Q B := by
    have : x ∈ conjSubgroup g (LB M Q B) :=
      mem_conjSubgroup.mpr (Subgroup.mem_inf.mp (mem_conjSubgroup.mp hx)).1
    rwa [hgL] at this
  exact ⟨hxL, hcon x hx⟩

theorem mem_normalizer_BZ95 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {z : G} (hzM : z ∈ M) (hzL : conjSubgroup z (LB M Q B) = LB M Q B) :
    z ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  exact (hc.mem_normalizer_LB_iff h35 hzM).mp (conjSubgroup_eq_self_iff.mp hzL)

theorem B_le_inf_conj95 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {z : G} (hzM : z ∈ M) (hzL : conjSubgroup z (LB M Q B) = LB M Q B) :
    B ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) := by
  have ht : t ∈ LB M Q B := hs.mem
  have hzBZ := mem_normalizer_BZ95 h34 hs hzM hzL
  have hBV : (B ⊔ Z : Subgroup G) ≤ Vt M (LB M Q B) B Z t :=
    sup_le (hc.B_le_Vt ht) sec39_Z_le_Vt
  intro b hb
  refine ⟨hc.B_le_Vt ht hb, ?_⟩
  show b ∈ conjSubgroup z (Vt M (LB M Q B) B Z t)
  rw [mem_conjSubgroup]
  have hz' : z⁻¹ ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G)).inv_mem hzBZ
  have h1 := (Subgroup.mem_normalizer_iff.mp hz' b).mp (Subgroup.mem_sup_left hb)
  have h2 := hBV h1
  simpa using h2

theorem isSingV_conj95 {hc : Ctx M Q Z B} {t z : G} (hzM : z ∈ M)
    (hzBZ : z ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G)) {u : G}
    (hu : IsSingV M Q Z B t (z⁻¹ * u * z)) :
    ∃ ρ ∈ conjSubgroup z (Rt M (LB M Q B) t), ∃ b ∈ B, u * (ρ * b * ρ⁻¹)⁻¹ ∈ Z := by
  obtain ⟨ρ, hρ, b, hb, hZ⟩ := hu
  have hZN : ∀ g ∈ M, ∀ ζ ∈ Z, g * ζ * g⁻¹ ∈ Z := fun g hg ζ hζ =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg) ζ).mp hζ
  have hbBZ : z * b * z⁻¹ ∈ (B ⊔ Z : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hzBZ b).mp (Subgroup.mem_sup_left hb)
  have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun b' hb' =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hb'))
  obtain ⟨b₁, hb₁, ζ, hζ, hbe⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hbBZ
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hρ₁M : z * ρ * z⁻¹ ∈ M := M.mul_mem (M.mul_mem hzM hρM) (M.inv_mem hzM)
  have hb₁M : b₁ ∈ M := hc.hyp.Q_normal.1 (hc.le hb₁)
  have hPM : z * ρ * z⁻¹ * b₁ * (z * ρ * z⁻¹)⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hρ₁M hb₁M) (M.inv_mem hρ₁M)
  refine ⟨z * ρ * z⁻¹, conj_mem95 z hρ, b₁, hb₁, ?_⟩
  have h1 : u * (z * (ρ * b * ρ⁻¹) * z⁻¹)⁻¹ ∈ Z := by
    have := hZN z hzM _ hZ
    have e : z * ((z⁻¹ * u * z) * (ρ * b * ρ⁻¹)⁻¹) * z⁻¹ = u * (z * (ρ * b * ρ⁻¹) * z⁻¹)⁻¹ := by
      group
    rwa [e] at this
  set P : G := z * ρ * z⁻¹ * b₁ * (z * ρ * z⁻¹)⁻¹ with hP
  set ζ' : G := z * ρ * z⁻¹ * ζ * (z * ρ * z⁻¹)⁻¹ with hζ'
  have hζ'Z : ζ' ∈ Z := hZN _ hρ₁M ζ hζ
  have e2 : z * (ρ * b * ρ⁻¹) * z⁻¹ = P * ζ' := by
    have hbeq : z * b * z⁻¹ = b₁ * ζ := hbe.symm
    calc z * (ρ * b * ρ⁻¹) * z⁻¹ = (z * ρ * z⁻¹) * (z * b * z⁻¹) * (z * ρ * z⁻¹)⁻¹ := by group
      _ = (z * ρ * z⁻¹) * (b₁ * ζ) * (z * ρ * z⁻¹)⁻¹ := by rw [hbeq]
      _ = P * ζ' := by rw [hP, hζ']; group
  rw [e2] at h1
  have e3 : u * P⁻¹ = (u * (P * ζ')⁻¹) * (P * ζ' * P⁻¹) := by group
  rw [e3]
  exact Z.mul_mem h1 (hZN P hPM ζ' hζ'Z)

section Singular

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Z0 : Subgroup G} {z : G}

theorem isSingV_of_mem_inf_conj95 (h34 : Stroth34Statement) (h91b : Stroth91bStatement)
    (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) (hn7 : 7 ≤ n) (hcen : Centre95 hc t Z0)
    (hzM : z ∈ M) (hzL : conjSubgroup z (LB M Q B) = LB M Q B)
    (hzN : ∀ c ∈ Z0, z * c * z⁻¹ ∈ hc.CN t)
    (hex : ∃ x ∈ conjSubgroup z (N1 hc t), x ∉ hc.CN t) :
    ∀ u ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t),
      IsSingV M Q Z B t u := by
  classical
  obtain ⟨x₀, hx₀z, hx₀N⟩ := hex
  have hx₀L : x₀ ∈ LB M Q B := by
    have : x₀ ∈ conjSubgroup z (LB M Q B) :=
      mem_conjSubgroup.mpr (Subgroup.mem_inf.mp (mem_conjSubgroup.mp hx₀z)).1
    rwa [hzL] at this
  obtain ⟨K, fK, finK, hK2, hnrm, ⟨C⟩⟩ := exists_coord95 h34 hs hr
  have hA2 := isTypeA2_of_conj95 h34 h91b hs hr hn7 hzM hzL hx₀z hx₀N
  obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ ∈ N1 hc t, z * y₀ * z⁻¹ = x₀ :=
    ⟨z⁻¹ * x₀ * z, mem_conjSubgroup.mp hx₀z, by group⟩
  obtain ⟨-, hY⟩ := C.cent_eq_inf h34 h91b hs hr hcen hzM hzN (Subgroup.mem_inf.mp hy₀).2
    hx₀L hx₀N
  intro u hu
  rw [← hY] at hu
  exact C.isSingV_of_mem_comm_sup hs hx₀L hx₀N hA2.2 hu

end Singular

end HS9

end CFSG.RankThree.GF2n.Stroth80
