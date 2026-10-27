module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Tools
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Module
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom Equiv

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Sit27 (α β : Geo H M) : Prop where
  adj : (graph (H ⊔ M) H M).Adj α β
  vα : vtype α = false
  bα : bAt α = bMin H M
  b2 : 2 ≤ bMin H M
  norm : stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv β : Subgroup G) : Set G)
  ncen : ¬ Zv β ≤ centerOf (stab β)

namespace Sit27

variable {α β : Geo H M}

omit [Finite G] in
theorem nbr (P : Sit27 α β) : β ∈ nbrs α := P.adj

omit [Finite G] in
theorem nbr' (P : Sit27 α β) : α ∈ nbrs β := P.adj.symm

omit [Finite G] in
theorem vβ (P : Sit27 α β) : vtype β = true := by
  have h := vtype_ne_of_adj P.adj
  rw [P.vα] at h
  cases hv : vtype β
  · exact absurd hv.symm h
  · rfl

theorem centralizer_Zv_right (hA : F53Amalgam H M S) (P : Sit27 α β) :
    stab β ⊓ Subgroup.centralizer (Zv β : Set G) = Qv β := by
  rcases centralizer_Zv_dichotomy hA β with h | h
  · exact h
  · exact absurd (h ▸ omegaOneCenter_le_centerOf_self (stab β)) P.ncen

theorem inf_centralizer_eq (hA : F53Amalgam H M S) (P : Sit27 α β) :
    stab α ⊓ Subgroup.centralizer ((Zv α ⊔ Zv β : Subgroup G) : Set G) = Qv α ⊓ Qv β := by
  apply le_antisymm
  · rintro x ⟨hxs, hxc⟩
    have hxZα : x ∈ stab α ⊓ Subgroup.centralizer (Zv α : Set G) :=
      ⟨hxs, Subgroup.centralizer_le (fun z hz => Subgroup.mem_sup_left hz) hxc⟩
    rw [centralizer_Zv_eq_Qv_of_bAt hA P.bα] at hxZα
    refine ⟨hxZα, ?_⟩
    have hxZβ : x ∈ stab β ⊓ Subgroup.centralizer (Zv β : Set G) :=
      ⟨Qv_le_stab_of_mem_nbrs hA P.nbr hxZα,
        Subgroup.centralizer_le (fun z hz => Subgroup.mem_sup_right hz) hxc⟩
    rwa [P.centralizer_Zv_right hA] at hxZβ
  · rintro x ⟨hxα, hxβ⟩
    refine ⟨pCoreOf_le 2 _ hxα, ?_⟩
    have hle : (Zv α ⊔ Zv β : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun z hz => ?_) (fun z hz => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 x hxα)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA β hz).2 x hxβ)).symm
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))

theorem normalizer_inf (hA : F53Amalgam H M S) (P : Sit27 α β) :
    stab α ≤ Subgroup.normalizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) := by
  rw [← P.inf_centralizer_eq hA]
  exact SitSigma.normalizer_inf_centralizer P.norm

omit [Finite G] in
theorem Zv_right_le_Qv (P : Sit27 α β) : Zv β ≤ Qv α := by
  have h1 := P.b2
  have h2 := bMin_le_bAt (H := H) (M := M) β
  exact Zv_le_Qv_of_dist_lt (by rw [dist_eq_one_iff_adj.mpr P.adj.symm]; omega)

theorem relIndex_inf_left (hA : F53Amalgam H M S) (h28 : Hss28At H M) (P : Sit27 α β) :
    (Qv α ⊓ Qv β).relIndex (Qv α) = 2 := by
  have hq := h28 (by have := P.b2; omega) α β P.adj P.bα
  have hn : Qv α ≤ Subgroup.normalizer (Qv β : Set G) :=
    (Qv_le_stab_of_mem_nbrs hA P.nbr).trans (le_normalizer_pCoreOf 2 (stab β))
  rw [relIndex_inf_eq_relIndex_sup hn, hq, inf_comm]
  exact relIndex_Qv_inf_true hA P.nbr' P.vβ

theorem relIndex_inf_right (hA : F53Amalgam H M S) (h28 : Hss28At H M) (P : Sit27 α β) :
    (Qv β ⊓ Qv α).relIndex (Qv β) = 8 := by
  have hq := h28 (by have := P.b2; omega) α β P.adj P.bα
  have hn : Qv β ≤ Subgroup.normalizer (Qv α : Set G) :=
    (Qv_le_stab_of_mem_nbrs hA P.nbr').trans (le_normalizer_pCoreOf 2 (stab α))
  rw [relIndex_inf_eq_relIndex_sup hn, sup_comm, hq]
  exact relIndex_Qv_inf_false hA P.nbr P.vα

theorem card_map_eq_eight (hA : F53Amalgam H M S) (h28 : Hss28At H M) (P : Sit27 α β)
    {ψ : ↥(stab α) →* Perm (Fin 5)} (hψk : ψ.ker = (Qv α).subgroupOf (stab α)) :
    Nat.card (((Qv β).subgroupOf (stab α)).map ψ) = 8 := by
  rw [← relIndex_inf_eq_card_map hψk (Qv_le_stab_of_mem_nbrs hA P.nbr')]
  exact P.relIndex_inf_right hA h28

theorem normalClosure_sup_eq_top (hA : F53Amalgam H M S) (h28 : Hss28At H M) (P : Sit27 α β) :
    Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) : Set ↥(stab α)) ⊔
      (Qv α).subgroupOf (stab α) = ⊤ := by
  obtain ⟨ψ, hψ, hψk⟩ := exists_quotHom_five (quot_stab_five hA P.vα)
  replace hψk : ψ.ker = (Qv α).subgroupOf (stab α) := hψk
  have htop := normalClosure_map_eq_top_five ψ hψ _ (P.card_map_eq_eight hA h28 hψk)
  rw [eq_top_iff]
  intro x _
  have : ψ x ∈ (Subgroup.normalClosure
      (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) : Set ↥(stab α))).map ψ := by
    rw [htop]; trivial
  obtain ⟨l, hl, hlx⟩ := this
  have hx : x = l * (l⁻¹ * x) := by group
  rw [hx]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ?_)
  rw [← hψk, MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]

theorem normalClosure_eq_top_or (hA : F53Amalgam H M S) (h28 : Hss28At H M) (P : Sit27 α β) :
    Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
        Set ↥(stab α)) = ⊤ ∨
      Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
          Set ↥(stab α)) ⊓ (Qv α).subgroupOf (stab α) ≤ (Qv β).subgroupOf (stab α) := by
  set L := Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
    Set ↥(stab α)) with hL
  set U : Subgroup G := L.map (stab α).subtype with hU
  have hBle : Qv β ≤ stab α := Qv_le_stab_of_mem_nbrs hA P.nbr'
  have hQβU : Qv β ≤ U := fun x hx =>
    ⟨⟨x, hBle hx⟩, Subgroup.le_normalClosure (show (⟨x, hBle hx⟩ : ↥(stab α)) ∈
      (Qv β).subgroupOf (stab α) from hx), rfl⟩
  have hNle : Qv α ⊓ Qv β ≤ U ⊓ Qv α := fun x hx => ⟨hQβU hx.2, hx.1⟩
  have hmul := Subgroup.relIndex_mul_relIndex (Qv α ⊓ Qv β) (U ⊓ Qv α) (Qv α) hNle inf_le_right
  rw [P.relIndex_inf_left hA h28] at hmul
  have hne0 : (Qv α ⊓ Qv β).relIndex (U ⊓ Qv α) ≠ 0 :=
    ((Qv α ⊓ Qv β).subgroupOf (U ⊓ Qv α)).index_ne_zero_of_finite
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hmul) with h1 | h2
  ·
    left
    have hQU : Qv α ≤ U := fun x hx => ((Subgroup.relIndex_eq_one.mp h1) hx).1
    rw [eq_top_iff, ← P.normalClosure_sup_eq_top hA h28]
    refine sup_le le_rfl fun x hx => ?_
    obtain ⟨l, hl, hlx⟩ := hQU (Subgroup.mem_subgroupOf.mp hx)
    rwa [show x = l from Subtype.ext hlx.symm]
  ·
    right
    rw [h2] at hmul
    have h1 : (Qv α ⊓ Qv β).relIndex (U ⊓ Qv α) = 1 := by omega
    intro x ⟨hxL, hxQ⟩
    have hxU : (x : G) ∈ U ⊓ Qv α := ⟨⟨x, hxL, rfl⟩, Subgroup.mem_subgroupOf.mp hxQ⟩
    exact ((Subgroup.relIndex_eq_one.mp h1) hxU).2

theorem false_of_inf_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (h28 : Hss28At H M)
    (P : Sit27 α β)
    (hle : Subgroup.normalClosure (((Qv β).subgroupOf (stab α) : Subgroup ↥(stab α)) :
      Set ↥(stab α)) ⊓ (Qv α).subgroupOf (stab α) ≤ (Qv β).subgroupOf (stab α)) : False := by
  obtain ⟨ψ, hψ, hψk⟩ := exists_quotHom_five (quot_stab_five hA P.vα)
  replace hψk : ψ.ker = (Qv α).subgroupOf (stab α) := hψk
  set B : Subgroup ↥(stab α) := (Qv β).subgroupOf (stab α) with hBdef
  set L := Subgroup.normalClosure (B : Set ↥(stab α)) with hL
  set U : Subgroup G := L.map (stab α).subtype with hU
  have hBle : Qv β ≤ stab α := Qv_le_stab_of_mem_nbrs hA P.nbr'
  have hind := not_two_dvd_index_normalClosure_five ψ hψ B (P.card_map_eq_eight hA h28 hψk)
    (by rw [hψk]; exact hle)
  have hBL : B ≤ L := Subgroup.le_normalClosure
  have hQβU : Qv β ≤ U := fun x hx =>
    ⟨⟨x, hBle hx⟩, hBL (show (⟨x, hBle hx⟩ : ↥(stab α)) ∈ B from hx), rfl⟩
  have hUs : U ≤ stab α := Subgroup.map_subtype_le L
  have hsyl : IsSylowTwoOf (Qv β ⊓ U) U := by
    rw [inf_eq_left.mpr hQβU]
    refine ⟨hQβU, pCoreOf_isPGroup 2 _, ?_⟩
    have h1 : (Qv β).relIndex U = B.relIndex L := by
      have e1 : B.map (stab α).subtype = Qv β := Subgroup.map_subgroupOf_eq_of_le hBle
      rw [← e1, hU, Subgroup.relIndex_map_map_of_injective _ _ (stab α).subtype_injective]
    have h2 : ((Qv β).subgroupOf U).index = (B.subgroupOf L).index := h1
    rw [h2]; exact hind
  have hzle : Zv β ≤ pCoreOf 2 U :=
    le_trans (le_inf P.Zv_right_le_Qv ((Zv_le_Qv hA β).trans hQβU)) (pCoreOf_inf_le hUs)
  have hgen : U ⊔ (stab α ⊓ stab β) = stab α := by
    apply le_antisymm (sup_le hUs inf_le_left)
    have h1 : (L ⊔ (Qv α).subgroupOf (stab α)).map (stab α).subtype = stab α := by
      rw [P.normalClosure_sup_eq_top hA h28, Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le
      (show Qv α ≤ stab α from pCoreOf_le 2 _)] at h1
    exact h1.symm.le.trans (sup_le_sup_left (Qv_le_inf hA P.nbr) _)
  have hsit : SitSigma α β U := ⟨P.adj, hUs, hsyl, hzle, hgen⟩
  have hZα := h26 (by have := P.b2; omega) α β U hsit hQβU
  have hcen : stab α ≤ Subgroup.centralizer (Zv α : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      ((Subgroup.mem_centralizer_iff.mp (hZα hz).2) x hx).symm
  have hc := centralizer_Zv_eq_Qv_of_bAt hA P.bα
  rw [inf_eq_left.mpr hcen] at hc
  exact pCoreOf_ne_stab hA α hc.symm

end Sit27

end F53.Stellmacher

end CFSG.Quasithin
