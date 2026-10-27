module

public import CFSG.Quasithin.H13.NQCatA314Gen
public import CFSG.Quasithin.Background.A312SporJ1
public import CFSG.Quasithin.Background.A3Structure314Excl
public import CFSG.Sporadic.J1
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint CFSG.Quasithin.E2P.SporB
  CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Quasithin.A312S CFSG.Quasithin.A312S.J1 CFSG.Sporadic.J1
open scoped Pointwise

theorem exists_mulEquiv_map_eq {Γ P : Type} [Group Γ] [Finite Γ] [Group P] [Finite P]
    (φ : P ≃* Γ) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) {T : Subgroup P}
    (hT : IsSylowTwoOf T ⊤) : ∃ ψ : P ≃* Γ, T.map ψ.toMonoidHom = S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let US : Sylow 2 Γ := hS₀.2.1.toSylow (by
    have := hS₀.2.2
    have e : (S₀.subgroupOf ⊤).index = S₀.index := Subgroup.relIndex_top_right _
    rwa [e] at this)
  have hTi : ¬ 2 ∣ T.index := by
    have := hT.2.2
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
    rwa [e] at this
  let TS : Sylow 2 Γ := (hT.2.1.toSylow hTi).mapSurjective (f := φ.toMonoidHom) φ.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ TS US
  refine ⟨φ.trans (MulAut.conj g), ?_⟩
  have h1 : (US : Subgroup Γ) = S₀ := rfl
  rw [← h1, ← hg, Sylow.coe_subgroup_smul]
  show T.map (φ.trans (MulAut.conj g)).toMonoidHom =
    (T.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_map]
  rfl

theorem exists_centralizer_of_model {Γ P : Type} [Group Γ] [Finite Γ] [Group P] [Finite P]
    (φ : P ≃* Γ) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) {d n : ℕ}
    (hord : ∀ Z : Subgroup Γ, S₀ ≤ Z → Z ≠ ⊤ → d ∣ Nat.card Z → Nat.card Z = n)
    (hall : ∀ Z : Subgroup Γ, S₀ ≤ Z → Nat.card Z = n →
      ∃ u : Γ, orderOf u = 2 ∧ Z = Subgroup.centralizer ({u} : Set Γ))
    {T X : Subgroup P} (hT : IsSylowTwoOf T ⊤) (hTX : T ≤ X) (hXt : X ≠ ⊤)
    (hd : d ∣ Nat.card X) :
    Nat.card X = n ∧ ∃ z : P, orderOf z = 2 ∧ X = Subgroup.centralizer ({z} : Set P) := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_map_eq φ hS₀ hT
  have hSX : S₀ ≤ X.map ψ.toMonoidHom := hψ ▸ Subgroup.map_mono hTX
  have hcard : Nat.card (X.map ψ.toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective ψ.injective
  have hXt' : X.map ψ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hXt
    rw [eq_top_iff]
    intro x _
    have h1 : ψ x ∈ X.map ψ.toMonoidHom := h ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hye⟩ := h1
    rwa [← ψ.injective hye]
  have hn := hord _ hSX hXt' (hcard ▸ hd)
  obtain ⟨u, hu2, hu⟩ := hall _ hSX hn
  refine ⟨hcard ▸ hn, ψ.symm u, by rw [MulEquiv.orderOf_eq]; exact hu2, ?_⟩
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h1 : ψ x ∈ Subgroup.centralizer ({u} : Set Γ) := hu ▸ Subgroup.mem_map_of_mem _ hx
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1
  · intro hx
    have h1 : ψ x ∈ X.map ψ.toMonoidHom := by
      rw [hu, Subgroup.mem_centralizer_singleton_iff]
      have := congrArg ψ hx
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    obtain ⟨y, hy, hye⟩ := h1
    rwa [← ψ.injective hye]

theorem j1_card_centralizer
    (u : ↥J) (hou : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set ↥J)) = 120 := by
  set t : NativeSporadic.J1 := nativeEquiv.symm u with ht
  have hot : orderOf t = 2 := by rw [ht, MulEquiv.orderOf_eq]; exact hou
  set u' : Equiv.Perm (Fin 3080) :=
    ((CFSG.Sporadic.Schreier.j1PermEquiv t : CFSG.Sporadic.Schreier.j1P) :
      Equiv.Perm (Fin 3080)) with hu'
  have hu'P : u' ∈ CFSG.Sporadic.Schreier.j1P := (CFSG.Sporadic.Schreier.j1PermEquiv t).2
  have hou' : orderOf u' = 2 := by
    rw [hu', Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hot
  obtain ⟨h120, -, -⟩ := CFSG.Sporadic.Schreier.j1P_involution_centralizer u' hu'P hou'
  set φ := CFSG.Sporadic.Schreier.j1PermEquiv with hφ
  have hCt : Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.J1)) = 120 := by
    have e1 : Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.J1)) =
        Nat.card ((Subgroup.centralizer ({t} : Set NativeSporadic.J1)).map
          φ.toMonoidHom) := (Subgroup.card_map_of_injective φ.injective).symm
    rw [map_centralizer_equiv φ t] at e1
    have e2 : Nat.card (Subgroup.centralizer ({φ t} : Set ↥CFSG.Sporadic.Schreier.j1P)) =
        Nat.card ((Subgroup.centralizer ({φ t} : Set ↥CFSG.Sporadic.Schreier.j1P)).map
          CFSG.Sporadic.Schreier.j1P.subtype) :=
      (Subgroup.card_map_of_injective CFSG.Sporadic.Schreier.j1P.subtype_injective).symm
    rw [map_centralizer_subtype] at e2
    rw [e1, e2, ← h120]
  have e1 := map_centralizer_equiv nativeEquiv t
  have hut' : nativeEquiv t = u := by rw [ht, MulEquiv.apply_symm_apply]
  rw [hut'] at e1
  rw [← e1, Subgroup.card_map_of_injective nativeEquiv.injective, hCt]

theorem j1_overgroup_card
    (Z : Subgroup ↥J) (hSZ : j1S ≤ Z) (hZt : Z ≠ ⊤) (h60 : 60 ∣ Nat.card Z) :
    Nat.card Z = 120 := by
  obtain ⟨j, hj, hZ⟩ := j1_all Z hSZ
  have hj17 : j < 17 := by
    by_contra h
    have h17 : j = 17 := by
      have : j ≤ 17 := hj
      omega
    apply hZt
    rw [hZ, h17]
    unfold memberOrTop
    rw [ite_eq_right (by simp)]
  have hZY : Z = j1Y j := by
    rw [hZ]
    exact list_member (L := #[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21]) hj17
  rw [hZY, j1_Y_card hj17] at h60 ⊢
  revert h60
  interval_cases j <;> decide

theorem j1_overgroup_centralizer
    (Z : Subgroup ↥J) (hSZ : j1S ≤ Z) (h120 : Nat.card Z = 120) :
    ∃ u : ↥J, orderOf u = 2 ∧ Z = Subgroup.centralizer ({u} : Set ↥J) := by
  obtain ⟨u, -, hou, hle⟩ :=
    (Certificates.certificate7128 Z (by rw [j1_S_eq]; exact hSZ)).2 h120
  exact ⟨u, hou, Subgroup.eq_of_le_of_card_ge hle (by rw [j1_card_centralizer u hou, h120])⟩

theorem desc_j1
    (G : Type) [Group G] [Finite G] (L T B : Subgroup G) (hT : IsSylowTwoOf T L)
    (hB : B ∈ lFamily T) (hBL : B ≤ L) (hne : B ≠ L) (hJ : IsSporadic .J1 ↥L)
    (hA : IsAlt 5 ↥B) :
    ∃ z : G, z ∈ L ∧ orderOf z = 2 ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨eL⟩ := hJ
  have : IsSimpleGroup (NativeSporadic.Carrier .J1) := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hLs : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hTL := hT.1
  have hBc : Nat.card B = 60 := A314.card_isAlt_five hA
  have hX := sup_ne_of_isSimpleGroup hB hBL hne hLs
  have hXT : T.subgroupOf L ≤ (B ⊔ T).subgroupOf L := Subgroup.subgroupOf_mono L le_sup_right
  have hXt : (B ⊔ T).subgroupOf L ≠ ⊤ := fun h =>
    hX (le_antisymm (sup_le hBL hTL) (Subgroup.subgroupOf_eq_top.mp h))
  have hd : 60 ∣ Nat.card ↥((B ⊔ T).subgroupOf L) := by
    rw [card_sup_subgroupOf hBL hTL, ← hBc]
    exact card_dvd_sup B T
  obtain ⟨hXc, z', hz'2, hXeq⟩ := @exists_centralizer_of_model ↥J ↥L (Subgroup.toGroup _) _ _ _
    (eL.trans nativeEquiv) j1S j1_sylow 60 120 j1_overgroup_card
    j1_overgroup_centralizer (T.subgroupOf L) ((B ⊔ T).subgroupOf L)
    (isSylowTwoOf_top_subgroupOf hT) hXT hXt hd
  set z : G := (z' : G) with hzdef
  have hCX : L ⊓ Subgroup.centralizer ({z} : Set G) = B ⊔ T := by
    ext g
    constructor
    · rintro ⟨hgL, hgc⟩
      have h1 : (⟨g, hgL⟩ : L) ∈ Subgroup.centralizer ({z'} : Set ↥L) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgc)
      rw [← hXeq] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hg
      have hgL : g ∈ L := sup_le hBL hTL hg
      have h1 : (⟨g, hgL⟩ : L) ∈ (B ⊔ T).subgroupOf L := Subgroup.mem_subgroupOf.mpr hg
      rw [hXeq, Subgroup.mem_centralizer_singleton_iff] at h1
      exact ⟨hgL, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)⟩
  refine ⟨z, z'.2, by rw [hzdef, Subgroup.orderOf_coe, hz'2], ?_⟩
  rw [hCX]
  rw [card_sup_subgroupOf hBL hTL] at hXc
  exact (A312S.perfectCore_eq_of_index_two le_sup_left (by rw [hXc, hBc])
    (perfect_of_mem_cComp hB)).symm

end CFSG.Quasithin.H13.NQCat.A314D
