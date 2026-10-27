module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Local
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Invol
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Index

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.Ch3z

theorem relIndex_step_le_four {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}
    {V : Subgroup G} {y : G} (hB1 : B69One) (h : Ch3z.Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hV : IsElemAbelian 2 V) (hyH : y ∈ H) (hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hy3 : ∀ v ∈ V, y ^ 3 * v * (y ^ 3)⁻¹ = v)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @Ch3z.BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    {K₀ : Subgroup (MulAut ↥(chiefMod L N))} (hK₀ : K₀ ∈ 𝓗)
    (hK₀nat : @Ch3z.NatBlockData ↥(chiefMod L N) (chiefCG (h.hE hstep)) K₀
        (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (h.hE hstep)) K₀) 2)
    (hyK : chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩ ∈ K₀)
    (hAV : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) (hTV : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ N) ≤
      4 * (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ L) := by
  letI : CommGroup ↥(chiefMod L N) := chiefCG (h.hE hstep)
  haveI : Finite ↥(chiefMod L N) := inferInstance
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := h.hNL hstep
  have hE : IsElemAbelian 2 (chiefMod L N) := h.hE hstep
  have hVN : V ⊓ N ≤ N := inf_le_right
  have hWA : V ⊓ L ≤ V ⊓ N := inf_le_inf_left V hstep.2.2.1.le
  obtain ⟨ι, hι⟩ : ∃ ι : ↥(V ⊓ N) →* ↥(chiefMod L N),
      ∀ a, ι a = chiefIota hNL (Subgroup.inclusion hVN a) :=
    ⟨(chiefIota hNL).comp (Subgroup.inclusion hVN), fun a => rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ↥(chiefMod L N) →* ↥(chiefMod L N),
      ∀ m, σ m = chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩ m :=
    ⟨MulEquiv.toMonoidHom (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩), fun m => rfl⟩
  have hker : ∀ a : ↥(V ⊓ N), ι a = 1 ↔ (a : G) ∈ V ⊓ L := by
    intro a
    rw [hι, Subgroup.mem_inf]
    constructor
    · intro h1
      exact ⟨(Subgroup.mem_inf.mp a.2).1, (chiefIota_eq_one_iff hNL _).mp h1⟩
    · intro h1
      exact (chiefIota_eq_one_iff hNL _).mpr h1.2
  have hyA : ∀ a ∈ V ⊓ N, y * a * y⁻¹ ∈ V ⊓ N := fun a ha =>
    Subgroup.mem_inf.mpr ⟨hyV a (Subgroup.mem_inf.mp ha).1,
      hstep.1.2 y hyH a (Subgroup.mem_inf.mp ha).2⟩
  have hAc : ∀ a ∈ V ⊓ N, ∀ b ∈ V ⊓ N, a * b = b * a := fun a ha b hb' =>
    congrArg Subtype.val
      (hV.1.is_comm.comm ⟨a, (Subgroup.mem_inf.mp ha).1⟩ ⟨b, (Subgroup.mem_inf.mp hb').1⟩)
  have hA2 : ∀ a ∈ V ⊓ N, a ^ 2 = 1 := fun a ha => hV.2 a (Subgroup.mem_inf.mp ha).1
  have hy3' : ∀ a ∈ V ⊓ N, y ^ 3 * a * (y ^ 3)⁻¹ = a := fun a ha =>
    hy3 a (Subgroup.mem_inf.mp ha).1
  have hM2 : ∀ m : ↥(chiefMod L N), m ^ 2 = 1 := chiefMod_sq hE
  have hσ : ∀ a : ↥(V ⊓ N), ι ⟨y * (a : G) * y⁻¹, hyA a a.2⟩ = σ (ι a) := by
    intro a
    rw [hσdef, hι, hι]
    exact (chiefPsi_iota (Setting.hHL hstep) (Setting.hHN hstep) hNL ⟨y, hyH⟩
      (Subgroup.inclusion hVN a) (hstep.1.2 y hyH (a : G) (Subgroup.mem_inf.mp a.2).2)).symm
  have hsub : Set.range ι ⊆
      ((Subgroup.map (chiefIota hNL) ((V ⊓ N).subgroupOf N) : Subgroup ↥(chiefMod L N)) :
        Set ↥(chiefMod L N)) := by
    rintro _ ⟨a, rfl⟩
    exact SetLike.mem_coe.mpr (Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hVN a, Subgroup.mem_subgroupOf.mpr a.2, (hι a).symm⟩)
  obtain ⟨c, hc, hcV, hc2, hcY, hcW⟩ :=
    exists_conj_involution hB1 h hstep hnc hctx hK₀ hAV hTV
  have hcob := coboundary_le_four_of_natBlock h hstep hctx hK₀ hK₀nat hyH hyK hc hcV hc2 hcY hcW
  have hb : Set.ncard ((fun m => σ m * m⁻¹) '' (Set.range ι)) ≤ 4 := by
    have hsub' : (fun m => σ m * m⁻¹) '' (Set.range ι) ⊆
        (fun v => chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩ v * v⁻¹) ''
          ((Subgroup.map (chiefIota hNL) ((V ⊓ N).subgroupOf N) : Subgroup ↥(chiefMod L N)) :
            Set ↥(chiefMod L N)) := by
      rintro _ ⟨m, ⟨a, rfl⟩, rfl⟩
      refine ⟨ι a, hsub (Set.mem_range_self a), ?_⟩
      simp only [hσdef]
    exact (Set.ncard_le_ncard hsub').trans hcob
  exact relIndex_centralizer_le_of_local hAc hA2 hyA hy3' hWA ι hker σ hσ hM2 4 hb

theorem relIndex_step_le_one {G : Type} [Group G] [Finite G] {H U L N : Subgroup G} {V : Subgroup G} {y : G}
    (hUe : IsElemAbelian 2 U) (hstep : IsChiefStep H U L N) (hc : IsCentralStep H L N) (hV : IsElemAbelian 2 V)
    (hyH : y ∈ H) (hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V) (hy3 : ∀ v ∈ V, y ^ 3 * v * (y ^ 3)⁻¹ = v) :
    (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ N) ≤
      (Subgroup.centralizer ({y} : Set G)).relIndex (V ⊓ L) := by
  have hNU : N ≤ U := hstep.1.1
  have hLU : L ≤ U := hstep.2.1.1
  have hE : IsElemAbelian 2 (chiefMod L N) := D15Proof.isElemAbelian_secImg_of_le (L := L) hUe hNU
  have hcomm : ∀ x ∈ U, ∀ u ∈ U, x * u = u * x := fun x hx u hu =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨x, hx⟩ ⟨u, hu⟩)
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := by
    intro n hn
    have hnU : n ∈ U := hNU hn
    have hnU' : n⁻¹ ∈ U := inv_mem hnU
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      rw [hcomm n hnU l (hLU hl), mul_inv_cancel_right]
      exact hl
    · intro hnl
      have hmU : n * l * n⁻¹ ∈ U := hLU hnl
      have hc1 : n⁻¹ * (n * l * n⁻¹) = n * l * n⁻¹ * n⁻¹ := hcomm n⁻¹ hnU' _ hmU
      have hlm : l = n * l * n⁻¹ := by
        calc l = n⁻¹ * (n * l * n⁻¹) * n := by group
          _ = n * l * n⁻¹ * n⁻¹ * n := by rw [hc1]
          _ = n * l * n⁻¹ := by group
      rw [hlm]
      exact hnl
  have hVN : V ⊓ N ≤ N := inf_le_right
  have hWA : V ⊓ L ≤ V ⊓ N := inf_le_inf_left V hstep.2.2.1.le
  letI : CommGroup ↥(chiefMod L N) := chiefCG hE
  haveI : Finite ↥(chiefMod L N) := inferInstance
  obtain ⟨ι, hι⟩ : ∃ ι : ↥(V ⊓ N) →* ↥(chiefMod L N),
      ∀ a, ι a = chiefIota hNL (Subgroup.inclusion hVN a) :=
    ⟨(chiefIota hNL).comp (Subgroup.inclusion hVN), fun a => rfl⟩
  have hker : ∀ a : ↥(V ⊓ N), ι a = 1 ↔ (a : G) ∈ V ⊓ L := by
    intro a
    rw [hι, Subgroup.mem_inf]
    constructor
    · intro h1
      exact ⟨(Subgroup.mem_inf.mp a.2).1, (chiefIota_eq_one_iff hNL _).mp h1⟩
    · intro h1
      exact (chiefIota_eq_one_iff hNL _).mpr h1.2
  have hyA : ∀ a ∈ V ⊓ N, y * a * y⁻¹ ∈ V ⊓ N := fun a ha =>
    Subgroup.mem_inf.mpr ⟨hyV a (Subgroup.mem_inf.mp ha).1,
      hstep.1.2 y hyH a (Subgroup.mem_inf.mp ha).2⟩
  have hAc : ∀ a ∈ V ⊓ N, ∀ b ∈ V ⊓ N, a * b = b * a := fun a ha b hb' =>
    congrArg Subtype.val
      (hV.1.is_comm.comm ⟨a, (Subgroup.mem_inf.mp ha).1⟩ ⟨b, (Subgroup.mem_inf.mp hb').1⟩)
  have hA2 : ∀ a ∈ V ⊓ N, a ^ 2 = 1 := fun a ha => hV.2 a (Subgroup.mem_inf.mp ha).1
  have hy3' : ∀ a ∈ V ⊓ N, y ^ 3 * a * (y ^ 3)⁻¹ = a := fun a ha =>
    hy3 a (Subgroup.mem_inf.mp ha).1
  have hσ : ∀ a : ↥(V ⊓ N), ι ⟨y * (a : G) * y⁻¹, hyA a a.2⟩ =
      (MonoidHom.id ↥(chiefMod L N)) (ι a) := by
    intro a
    have haN : (a : G) ∈ N := (Subgroup.mem_inf.mp a.2).2
    have hyaN : y * (a : G) * y⁻¹ ∈ N := hstep.1.2 y hyH (a : G) haN
    have hcN : y * (a : G) * y⁻¹ * (a : G)⁻¹ ∈ N := mul_mem hyaN (inv_mem haN)
    have hcL : y * (a : G) * y⁻¹ * (a : G)⁻¹ ∈ L := hc y hyH (a : G) haN
    have hfac : (⟨y * (a : G) * y⁻¹, hyaN⟩ : ↥N) =
        ⟨y * (a : G) * y⁻¹ * (a : G)⁻¹, hcN⟩ * Subgroup.inclusion hVN a :=
      Subtype.ext (by
        show y * (a : G) * y⁻¹ = y * (a : G) * y⁻¹ * (a : G)⁻¹ * (a : G)
        group)
    rw [hι, hι]
    show chiefIota hNL ⟨y * (a : G) * y⁻¹, hyaN⟩ = chiefIota hNL (Subgroup.inclusion hVN a)
    rw [hfac, map_mul, (chiefIota_eq_one_iff hNL ⟨y * (a : G) * y⁻¹ * (a : G)⁻¹, hcN⟩).mpr hcL,
      one_mul]
  have hb : Set.ncard ((fun m => (MonoidHom.id ↥(chiefMod L N)) m * m⁻¹) '' (Set.range ι)) ≤ 1 := by
    have hsub : (fun m => (MonoidHom.id ↥(chiefMod L N)) m * m⁻¹) '' (Set.range ι) ⊆
        ({1} : Set ↥(chiefMod L N)) := by
      rintro _ ⟨m, ⟨a, rfl⟩, rfl⟩
      show ι a * (ι a)⁻¹ ∈ ({1} : Set ↥(chiefMod L N))
      exact Set.mem_singleton_iff.mpr (mul_inv_cancel _)
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_singleton (1 : ↥(chiefMod L N))).le
  have key := relIndex_centralizer_le_of_local hAc hA2 hyA hy3' hWA ι hker
    (MonoidHom.id ↥(chiefMod L N)) hσ (chiefMod_sq hE) 1 hb
  rw [one_mul] at key
  exact key

end CFSG.Quasithin.H13.L319.S66

end
