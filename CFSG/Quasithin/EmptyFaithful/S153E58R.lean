module

public import CFSG.Quasithin.EmptyFaithful.S153E58F

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E58

open S153E57

section Index

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem UCT_mul_mem (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx) (h52 : Concl15352 cx)
    {x y : G} (hx : x ∈ T) (hy : y ∈ T) (hxn : x ∉ UCT153 T M V₁ Mc) (hyn : y ∉ UCT153 T M V₁ Mc) :
    x⁻¹ * y ∈ UCT153 T M V₁ Mc := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, -, -, -, -, -, hS, -, -, -⟩ := S153E.exists_bar_model cx
  have hT8 : Nat.card ↥(autI hV T) = 8 := hS.card_T cx.c.hyp.isSylowTwoOf_autI
  obtain ⟨-, hK4, -⟩ : IsNonabelian153 (UH153 T M V₁ Mc) ∧
      IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) ∧
      (autOn (UH153 T M V₁ Mc) (VZ T M) ≤ autOn T (VZ T M) ∧
        autOn (UH153 T M V₁ Mc) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M) ∧
        ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω ∧
          IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) Ω) := by
    rcases h51.two with h | ⟨hab, -, -, -⟩
    · exact ⟨h.1, h.2.1, h.2.2⟩
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := h52
      exact hne (B2F.isElemAbelian_comm hab ha hb)
  have hU4 : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := hK4.1
  have hle : autI hV (UH153 T M V₁ Mc) ≤ autI hV T := S153E.autI_U_le_T cx
  have hidx : ((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T)).index = 2 := by
    have hmul := Subgroup.card_mul_index ((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T))
    have hc : Nat.card ↥((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T)) = 4 := by
      rw [← hU4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hc, hT8] at hmul
    omega
  have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := S153E.T_le_N cx hx
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := S153E.T_le_N cx hy
  have hxyN : x⁻¹ * y ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hyN
  have key : ∀ z : G, z ∈ T → ∀ hzN : z ∈ Subgroup.normalizer (VZ T M : Set G),
      convI hV ⟨z, hzN⟩ ∈ autI hV (UH153 T M V₁ Mc) → z ∈ UCT153 T M V₁ Mc := by
    intro z hzT hzN hz
    obtain ⟨u, huU, hu⟩ := (mem_autI hV).1 hz
    have h1 : convI hV (u⁻¹ * ⟨z, hzN⟩) = 1 := by
      rw [map_mul, map_inv, hu]
      exact inv_mul_cancel _
    have hc : ((u⁻¹ * ⟨z, hzN⟩ : Subgroup.normalizer (VZ T M : Set G)) : G) ∈
        Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 h1
    have e : z = (u : G) * ((u : G)⁻¹ * z) := by group
    rw [e]
    exact Subgroup.mul_mem_sup huU ⟨T.mul_mem (T.inv_mem (S153E.U_le_T cx huU)) hzT, by simpa using hc⟩
  let ax : ↥(autI hV T) := ⟨convI hV ⟨x, hxN⟩, convI_mem_autI hV hx hxN⟩
  let ay : ↥(autI hV T) := ⟨convI hV ⟨y, hyN⟩, convI_mem_autI hV hy hyN⟩
  have hax : ax ∉ (autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T) := fun h =>
    hxn (key x hx hxN (Subgroup.mem_subgroupOf.1 h))
  have hay : ay ∉ (autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T) := fun h =>
    hyn (key y hy hyN (Subgroup.mem_subgroupOf.1 h))
  have hmem : ax⁻¹ * ay ∈ (autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T) := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    constructor
    · intro h
      exfalso
      apply hax
      simpa using Subgroup.inv_mem _ h
    · intro h
      exact absurd h hay
  have h2 : convI hV ⟨x⁻¹ * y, hxyN⟩ ∈ autI hV (UH153 T M V₁ Mc) := by
    have h := Subgroup.mem_subgroupOf.1 hmem
    have e : convI hV ⟨x⁻¹ * y, hxyN⟩ = (convI hV ⟨x, hxN⟩)⁻¹ * convI hV ⟨y, hyN⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e]
    exact h
  exact key (x⁻¹ * y) (T.mul_mem (T.inv_mem hx) hy) hxyN h2

end Index

section Rho

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem rho_mem_K_of_UCT (cx : Ctx15350 T Mc M V₁ V₂ t)
    {K : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))}
    {u₁ : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))} (hu₁ : u₁ ∈ Pt T M V₁ Mc)
    (hfixK : ∀ h ∈ HStar153 T M V₁ Mc, h u₁ = u₁ → h ∈ K) (n : NZ T)
    (hn : (n : G) ∈ UCT153 T M V₁ Mc) : rho cx n ∈ K := by
  let S : Subgroup G := (K.comap (rho cx)).map (NZ T).subtype
  have hU : UH153 T M V₁ Mc ≤ S := by
    intro u hu
    refine Subgroup.mem_map.2 ⟨⟨u, U_le_NZ cx hu⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, rho_eq_one_of_mem_U cx ⟨u, U_le_NZ cx hu⟩ hu]
    exact K.one_mem
  have hC : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ S := by
    intro c hc
    have hcMc : c ∈ Mc := S153E.T_le_Mc cx hc.1
    have hcN : c ∈ NZ T := Mc_le_NZ cx hcMc
    refine Subgroup.mem_map.2 ⟨⟨c, hcN⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    apply hfixK _ (rho_mem_XStar (B := Mc) cx ⟨c, hcN⟩ hcMc)
    obtain ⟨u, rfl⟩ := piU_surjective cx u₁
    have huP : (u : G) ∈ VZ T M ⊓ UH153 T M V₁ Mc := (mem_Pt_iff cx u).1 hu₁
    rw [← piU_conj cx ⟨c, hcN⟩ hcMc u]
    congr 1
    apply Subtype.ext
    have h1 : (c : G) * u = u * c := (Subgroup.mem_centralizer_iff.1 hc.2 _ huP.1).symm
    show c * (u : G) * c⁻¹ = u
    rw [h1]
    group
  have hS : UCT153 T M V₁ Mc ≤ S := sup_le hU hC
  obtain ⟨n', hn', hnn⟩ := Subgroup.mem_map.1 (hS hn)
  have : n' = n := Subtype.ext hnn
  rw [Subgroup.mem_comap] at hn'
  rwa [this] at hn'

theorem rho_not_mem_K_of_not_UCT (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx) (h52 : Concl15352 cx)
    {K : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))}
    (hKH : K ≤ HStar153 T M V₁ Mc) (hidx : K.relIndex (HStar153 T M V₁ Mc) = 2)
    (hUCT : ∀ n : NZ T, (n : G) ∈ UCT153 T M V₁ Mc → rho cx n ∈ K) {t₂ : G} (ht₂ : t₂ ∈ T)
    (hn : t₂ ∉ UCT153 T M V₁ Mc) : rho cx ⟨t₂, t₁_mem_NZ cx ht₂⟩ ∉ K := by
  intro hK
  have hTK : XStar153 T M V₁ Mc T ≤ K := by
    intro x hx
    obtain ⟨n, hnT, rfl⟩ := (mem_XStar_iff cx T x).1 hx
    by_cases hnU : (n : G) ∈ UCT153 T M V₁ Mc
    · exact hUCT n hnU
    · have h1 : t₂⁻¹ * (n : G) ∈ UCT153 T M V₁ Mc := UCT_mul_mem cx h51 h52 ht₂ hnT hn hnU
      have h2 := hUCT (⟨t₂, t₁_mem_NZ cx ht₂⟩⁻¹ * n) (by simpa using h1)
      have : rho cx n = rho cx ⟨t₂, t₁_mem_NZ cx ht₂⟩ * rho cx (⟨t₂, t₁_mem_NZ cx ht₂⟩⁻¹ * n) := by
        rw [map_mul, map_inv]
        group
      rw [this]
      exact K.mul_mem hK h2
  have hSyl := S153E.isSylowTwoOf_HStar_T cx
  have hTH : XStar153 T M V₁ Mc T ≤ HStar153 T M V₁ Mc := hSyl.1
  apply hSyl.2.2
  have e := Subgroup.relIndex_mul_relIndex (XStar153 T M V₁ Mc T) K (HStar153 T M V₁ Mc) hTK hKH
  show 2 ∣ (XStar153 T M V₁ Mc T).relIndex (HStar153 T M V₁ Mc)
  rw [← e, hidx]
  exact Dvd.intro_left _ rfl

end Rho

end S153E58

end CFSG.Quasithin
