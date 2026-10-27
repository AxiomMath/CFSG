module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5CIdx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2
public import CFSG.Quasithin.EmptyFaithful.T1515A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)
include d

theorem stab_of_mem_Sg {s : G} (hs : s ∈ d.Sg) :
    d.S.Stab₁ (convI hV ⟨s, d.hTN hs.1⟩) ∧ d.S.Stab₂ (convI hV ⟨s, d.hTN hs.1⟩) :=
  ⟨stab_of_mem_normalizer_map (d.hTN hs.1) hs.2,
    stab_of_mem_normalizer_map (d.hTN hs.1) (d.mem_normalizer_V₂ (d.hTM hs.1) hs.2)⟩

theorem val_mem_centralizer_Sg_iff {w : IntMod V hV} :
    IntMod.val w ∈ Subgroup.centralizer (d.Sg : Set G) ↔ w ∈ fixV (autI hV d.Sg) := by
  constructor
  · intro hw g hg
    obtain ⟨⟨s, hsN⟩, hsS, rfl⟩ := (mem_autI hV).1 hg
    apply IntMod.val_injective
    rw [← conj_val hsN]
    have := Subgroup.mem_centralizer_iff.mp hw s hsS
    calc s * IntMod.val w * s⁻¹ = IntMod.val w * s * s⁻¹ := by rw [← this]
      _ = IntMod.val w := by group
  · intro hw
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    have hsN := d.hTN hs.1
    have h1 := hw _ (convI_mem_autI hV hs hsN)
    have h2 := congrArg IntMod.val h1
    rw [← conj_val hsN] at h2
    calc s * IntMod.val w = (s * IntMod.val w * s⁻¹) * s := by group
      _ = IntMod.val w * s := by rw [h2]

theorem Z₁_ne_bot : d.Z₁ ≠ ⊥ := by
  intro hbot
  have hP2 : IsPGroup 2 (autI hV d.Sg) := isPGroup_autI_of (d.hsyl.2.1.to_le inf_le_left)
  have hst : ∀ g ∈ autI hV d.Sg, d.S.Stab₁ g := by
    intro g hg
    obtain ⟨⟨s, hsN⟩, hsS, rfl⟩ := (mem_autI hV).1 hg
    exact (d.stab_of_mem_Sg hsS).1
  obtain ⟨z, hz, hz1, hzfix⟩ :=
    d.S.exists_fixed_W₁ (fun w => IntMod.sq_eq_one w) d.hcard hP2 hst
  have hzZ : IntMod.val z ∈ d.Z₁ :=
    ⟨d.val_mem_V₁ hz, (d.val_mem_centralizer_Sg_iff).2 (fun g hg => hzfix g hg)⟩
  rw [hbot, Subgroup.mem_bot] at hzZ
  exact hz1 (IntMod.val_injective hzZ)

theorem Z₁_le_V₁ : d.Z₁ ≤ d.V₁ := inf_le_left

theorem Z₂_le_V₂ : d.Z₂ ≤ d.V₂ := inf_le_left

theorem Z₁_inf_Z₂ : d.Z₁ ⊓ d.Z₂ = ⊥ := by
  refine le_bot_iff.1 ?_
  rw [← d.V₁_inf_V₂]
  exact inf_le_inf inf_le_left inf_le_left

theorem centralizer_le_normalizer {m : G} (hm : m ∈ M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) :
    m ∈ Subgroup.normalizer (d.V₁ : Set G) := by
  by_contra hn
  obtain ⟨hs1, -⟩ := d.swap_of_not_mem_normalizer hm.1 hn
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ d.Z₁, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact d.Z₁_ne_bot ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hc : m * z * m⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hm.2 z hzZ
    calc m * z * m⁻¹ = z * m * m⁻¹ := by rw [← this]
      _ = z := by group
  have h2 : z ∈ d.V₁ ⊓ d.V₂ := ⟨d.Z₁_le_V₁ hzZ, hc ▸ hs1 z (d.Z₁_le_V₁ hzZ)⟩
  rw [d.V₁_inf_V₂, Subgroup.mem_bot] at h2
  exact hz1 h2

theorem s1516_eq : s1516 T d.Z₁ = d.Sg := by
  ext x
  constructor
  · rintro ⟨hxT, hxc⟩
    exact ⟨hxT, d.centralizer_le_normalizer ⟨d.hTM hxT, hxc⟩⟩
  · rintro ⟨hxT, hxN⟩
    refine ⟨hxT, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hz.2 x ⟨hxT, hxN⟩).symm

theorem s_normal : T ≤ Subgroup.normalizer (s1516 T d.Z₁ : Set G) := by
  rw [d.s1516_eq]
  have hidx : (d.Sg.subgroupOf T).index = 2 := d.relIndex_Sg
  have : (d.Sg.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).1 this

theorem sylow : IsSylowTwoOf (s1516 T d.Z₁) (g1_1516 d.Z₁ ⊓ M) := by
  rw [d.s1516_eq]
  have hX : g1_1516 d.Z₁ ⊓ M ≤ M ⊓ Subgroup.normalizer (d.V₁ : Set G) := fun m hm =>
    ⟨hm.2, d.centralizer_le_normalizer ⟨hm.2, hm.1⟩⟩
  have hSgX : d.Sg ≤ g1_1516 d.Z₁ ⊓ M := fun x hx =>
    ⟨Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm, d.hTM hx.1⟩
  refine ⟨hSgX, d.hsyl.2.1.to_le inf_le_left, ?_⟩
  have h := Subgroup.relIndex_mul_relIndex d.Sg (g1_1516 d.Z₁ ⊓ M)
    (M ⊓ Subgroup.normalizer (d.V₁ : Set G)) hSgX hX
  intro hd
  exact d.relIndex_Sg_N (h ▸ dvd_mul_of_dvd_left hd _)

theorem J_le_Sg (hJ : autI hV (thompsonJi T 1) ≤ d.S.A₁ ⊔ d.S.A₂) :
    thompsonJi T 1 ≤ d.Sg := by
  intro j hj
  have hjT : j ∈ T := Setting1516.thompsonJi_le_self1516 T 1 hj
  have hjN : j ∈ Subgroup.normalizer (V : Set G) := d.hTN hjT
  have hρ : convI hV ⟨j, hjN⟩ ∈ autI hV (thompsonJi T 1) := convI_mem_autI hV hj hjN
  exact ⟨hjT, mem_normalizer_map hjN (d.S.stab_of_mem_A₀ (hJ hρ)).1⟩

theorem Z_le_sup (hZV : quasithinOmegaOneCenter T ≤ V) :
    quasithinOmegaOneCenter T ≤ d.Z₁ ⊔ d.Z₂ := by
  intro z hz
  have hzV : z ∈ V := hZV hz
  have hzc := (quasithinOmegaOneCenter_le_center T hz).2
  set w : IntMod V hV := IntMod.mk hV ⟨z, hzV⟩ with hw
  have hwz : IntMod.val w = z := rfl
  have hfix : w ∈ fixV (autI hV d.Sg) := by
    refine (d.val_mem_centralizer_Sg_iff).1 ?_
    rw [hwz]
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    exact (Subgroup.mem_centralizer_iff.mp hzc s hs.1)
  have hP : ∀ g ∈ autI hV d.Sg, d.S.Stab₁ g ∧ d.S.Stab₂ g := by
    intro g hg
    obtain ⟨⟨s, hsN⟩, hsS, rfl⟩ := (mem_autI hV).1 hg
    exact d.stab_of_mem_Sg hsS
  have hmem : w ∈ (d.S.W₁ ⊓ fixV (autI hV d.Sg)) ⊔ (d.S.W₂ ⊓ fixV (autI hV d.Sg)) := by
    rw [← d.S.fixV_eq_sup hP]
    exact hfix
  obtain ⟨w₁, hw₁, w₂, hw₂, hww⟩ := Subgroup.mem_sup.1 hmem
  have h1 : IntMod.val w₁ ∈ d.Z₁ :=
    ⟨d.val_mem_V₁ hw₁.1, (d.val_mem_centralizer_Sg_iff).2 hw₁.2⟩
  have h2 : IntMod.val w₂ ∈ d.Z₂ :=
    ⟨d.val_mem_V₂ hw₂.1, (d.val_mem_centralizer_Sg_iff).2 hw₂.2⟩
  rw [← hwz, ← hww]
  exact Subgroup.mul_mem_sup h1 h2

end Six5Data

end CFSG.Quasithin
