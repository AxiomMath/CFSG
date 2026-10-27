module

public import CFSG.Quasithin.MS93.S46Qj
public import CFSG.Quasithin.MS93.S4AVtx

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A

section Ker

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem stab_inf_centralizer_uloc_le_qv {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    stab _ δ ⊓ Subgroup.centralizer (Uloc h.le L δ : Set (puAmalgam h.le).Universal) ≤
      Qv _ δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  rintro x ⟨hxs, hxc⟩
  rw [stab_eq_map_vEmb h.le g] at hxs
  obtain ⟨m, -, rfl⟩ := hxs
  have hU := puTrans_eq_map_vEmb h.le (S4A.Uq_normal h) g
  have hmc : (m : G) ∈ Subgroup.centralizer (Uq M T L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : vEmb h.le g ⟨u, Uq_le h.L_le hu⟩ ∈ Uloc h.le L (g • baseA _) := by
      rw [Uloc, hU]
      exact ⟨⟨u, Uq_le h.L_le hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hxc _ hu'
    have h2 : (⟨u, Uq_le h.L_le hu⟩ : ↥M) * m = m * ⟨u, Uq_le h.L_le hu⟩ :=
      vEmb_injective h.le g (by rw [map_mul, map_mul]; exact this)
    exact congrArg Subtype.val h2
  have hmQ : (m : G) ∈ pCoreOf 2 M := by
    rw [← QjAux.inf_centralizer_Uq_eq h hφ]
    exact ⟨m.2, hmc⟩
  have hPn : ((pCoreOf 2 M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le' M)).2 (le_normalizer_pCoreOf M)
  rw [h.qv_eq hδ, puTrans_eq_map_vEmb h.le hPn g]
  exact ⟨m, Subgroup.mem_subgroupOf.mpr hmQ, rfl⟩

omit hφ in
theorem isPGroup_qv_of_isMVtx {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    IsPGroup 2 ↥(Qv (puAmalgam h.le) δ) := by
  obtain ⟨ρ, hρ⟩ := exists_adj (puAmalgam h.le) δ
  have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
  exact (isPGroup_qv _ h.hyp20 hρH).to_le (qv_le_qv _ h.hyp20 hδ hρ)

theorem toSL3_eq_one_iff_mem_qv {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam h.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc h.le L δ) ⊥ ψ false 1)
    (x : ↥(stab (puAmalgam h.le) δ)) :
    toSL3 ψ x = 1 ↔ (x : (puAmalgam h.le).Universal) ∈ Qv _ δ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  rw [toSL3_eq_one_iff hψ]
  constructor
  · intro hx
    refine stab_inf_centralizer_uloc_le_qv h hφ hδ ⟨x.2, ?_⟩
    show (x : (puAmalgam h.le).Universal) ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := hx u hu
    calc u * (x : (puAmalgam h.le).Universal)
        = (x : (puAmalgam h.le).Universal) * u * ((x : (puAmalgam h.le).Universal))⁻¹ *
            (x : (puAmalgam h.le).Universal) := by rw [this]
      _ = x * u := by group
  · intro hx u hu
    have hc := Subgroup.mem_centralizer_iff.mp
      (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hδ) hx) u
      (uloc_le_zm h hfull hδ hu)
    rw [← hc, mul_inv_cancel_right]

theorem pow_two_pow_eq_one_of_toSL3_eq_one {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam h.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc h.le L δ) ⊥ ψ false 1)
    (x : ↥(stab (puAmalgam h.le) δ)) (hx : toSL3 ψ x = 1) : ∃ e : ℕ, x ^ 2 ^ e = 1 := by
  have hxQ := (toSL3_eq_one_iff_mem_qv h hφ hδ hψ x).mp hx
  obtain ⟨e, he⟩ := isPGroup_qv_of_isMVtx h hδ ⟨x, hxQ⟩
  refine ⟨e, Subtype.ext ?_⟩
  have := congrArg Subtype.val he
  simpa using this

theorem card_natImage_eq_relIndex {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(stab (puAmalgam h.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc h.le L δ) ⊥ ψ false 1)
    {A : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ stab _ δ) :
    Nat.card ↥(natImage ψ A) = (Qv _ δ).relIndex A := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hfinS := finite_stab h hδ
  have hfinA : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective hA)
  have h1 := card_natImage_mul hψ hA
  have hinf : A ⊓ Subgroup.centralizer (Uloc h.le L δ : Set (puAmalgam h.le).Universal) =
      Qv _ δ ⊓ A := by
    apply le_antisymm
    · intro x hx
      exact ⟨stab_inf_centralizer_uloc_le_qv h hφ hδ ⟨hA hx.1, hx.2⟩, hx.1⟩
    · intro x hx
      refine ⟨hx.2, ?_⟩
      exact Subgroup.centralizer_le (uloc_le_zm h hfull hδ)
        (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hδ) hx.1)
  rw [hinf] at h1
  have h2 := relIndex_mul_card_inf (Qv (puAmalgam h.le) δ) A
  have : Finite ↥(Qv (puAmalgam h.le) δ ⊓ A) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right : Qv _ δ ⊓ A ≤ A))
  have hpos : 0 < Nat.card ↥(Qv (puAmalgam h.le) δ ⊓ A) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

end Ker

end CFSG.Quasithin.MS93.S46
