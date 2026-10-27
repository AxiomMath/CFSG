module

public import CFSG.Quasithin.Vol2.Ch9Sec3FFCCore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtMain
public import CFSG.Quasithin.EmptyFaithful.S1421QA21G2

public section

namespace CFSG.Quasithin.H13.Ch9.FFC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem isSylowTwoOf_map_of_surjective {X X' : Type*} [Group X] [Group X'] {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) {f : X →* X'} (hf : Function.Surjective f) :
    IsSylowTwoOf (U.map f) ⊤ := by
  refine ⟨le_top, hU.2.1.map f, fun hd => hU.2.2 ?_⟩
  have h1 : ((U.map f).subgroupOf ⊤).index = (U.map f).index := Subgroup.relIndex_top_right _
  have h2 : (U.subgroupOf ⊤).index = U.index := Subgroup.relIndex_top_right _
  rw [h1] at hd
  rw [h2]
  exact hd.trans (Subgroup.index_map_dvd U hf)

section Block

variable {Y : Type} [Group Y] [Finite Y] {T B L : Subgroup Y}

theorem block_data (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hL : L ∈ cComp ⊤)
    (hBL : B < L) (hLn : L.Normal) (hTB : T ≤ Subgroup.normalizer (B : Set Y)) :
    IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ ∧ Group.IsPerfect ↥L ∧
      Group.IsPerfect ↥(B.subgroupOf L) ∧ ¬ Group.IsSolvable ↥(B.subgroupOf L) ∧
      B.subgroupOf L ≠ ⊤ ∧
      (T ⊓ L).subgroupOf L ≤ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  have hBc : B ∈ cComp (B ⊔ T) := hB
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hBc)
  have eB : ↥(B.subgroupOf L) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL.le
  refine ⟨CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (A4.isSylowTwoOf_inf_normal hT le_top (Subgroup.normalizer_eq_top_iff.mpr hLn).ge),
    Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hL),
    Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective,
    fun _ => not_isSolvable_of_mem_cComp hBc
      (Group.isSolvable_of_isSolvable_injective (f := eB.symm.toMonoidHom) eB.symm.injective),
    fun h => hBL.ne (le_antisymm hBL.le fun x hx => ?_), ?_⟩
  · have hx' : (⟨x, hx⟩ : ↥L) ∈ B.subgroupOf L := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx'
  · rw [← Subgroup.subgroupOf_normalizer_eq hBL.le]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hTB (Subgroup.mem_subgroupOf.mp hx).1)

omit [Finite Y] in
theorem mem_normalizer_of_subgroupOf (hBL : B ≤ L) {d : Y} (hd : d ∈ L)
    (h : (⟨d, hd⟩ : ↥L) ∈ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    d ∈ Subgroup.normalizer (B : Set Y) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hBL] at h
  exact Subgroup.mem_subgroupOf.mp h

end Block

section Lie


theorem exists_borelPkg {X : Type} [Group X] [Finite X]
    (h : IsPSL 3 2 2 X ∨ IsPSp4 2 2 X ∨ IsG2 2 2 X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup X, QA21.BorelPkg X U P := by
  rcases h with h | h | h
  · obtain ⟨P, hP, hE⟩ := Rk2.rank2PkgExt_exists_psl3 le_rfl h hU
    exact ⟨P, ⟨hP.res, hP.norm, hE.solvable_le_normalizer⟩⟩
  · obtain ⟨P, hP, hE⟩ := Rk2.rank2PkgExt_exists_sp4 le_rfl h hU
    exact ⟨P, ⟨hP.res, hP.norm, hE.solvable_le_normalizer⟩⟩
  · exact QA21.borelPkg_g2 h hU

theorem le_normalizer_of_borel {X : Type} [Group X] [Finite X]
    (h : IsPSL 3 2 2 X ∨ IsPSp4 2 2 X ∨ IsG2 2 2 X) (hX : Group.IsPerfect X) {U B D : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hB : Group.IsPerfect ↥B) (hBs : ¬ Group.IsSolvable ↥B)
    (hBX : B ≠ ⊤) (hUB : U ≤ Subgroup.normalizer (B : Set X)) (hD : Group.IsSolvable ↥(D ⊔ U)) :
    D ≤ Subgroup.normalizer (B : Set X) := by
  obtain ⟨P, hP⟩ := exists_borelPkg h hU
  exact le_normalizer_of_residual hP.res hP.norm hP.solv hU.2.1 hX hB hBs hBX hUB hD

theorem le_normalizer_of_isLie {X : Type} [Group X] [Finite X]
    (h : IsSL3 4 X ∨ IsPSp4 2 2 X ∨ IsG2 2 2 X) (hX : Group.IsPerfect X) {U B D : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hB : Group.IsPerfect ↥B) (hBs : ¬ Group.IsSolvable ↥B)
    (hBX : B ≠ ⊤) (hUB : U ≤ Subgroup.normalizer (B : Set X)) (hD : Group.IsSolvable ↥(D ⊔ U)) :
    D ≤ Subgroup.normalizer (B : Set X) := by
  rcases h with h | h | h
  · obtain ⟨X', _, _, π, hπ, hker, -, hX'⟩ := exists_isPSL_of_isSL3 h
    have hKs : Group.IsSolvable ↥π.ker := by
      have : IsMulCommutative ↥π.ker := ⟨⟨fun a b => Subtype.ext
        ((Subgroup.mem_center_iff.mp (hker a.2) b).symm)⟩⟩
      infer_instance
    have hKN : π.ker ≤ Subgroup.normalizer (B : Set X) := fun z hz =>
      Subgroup.mem_normalizer_iff.mpr fun b => by
        have hzc := Subgroup.mem_center_iff.mp (hker hz)
        rw [← hzc b, mul_inv_cancel_right]
    refine le_normalizer_of_surjective π hker hB (le_normalizer_of_borel (Or.inl hX')
      (Group.IsPerfect.ofSurjective hπ) (isSylowTwoOf_map_of_surjective hU hπ)
      (map_isPerfect hB π) ?_ ?_ ((Subgroup.map_mono hUB).trans (Subgroup.le_normalizer_map π))
      ?_)
    ·
      intro hs
      apply hBs
      have hbot : B.map π = ⊥ := by
        by_contra hne
        have : Nontrivial ↥(B.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
        have : Group.IsPerfect ↥(B.map π) := map_isPerfect hB π
        exact Group.IsPerfect.not_isSolvable _ hs
      have hle : B ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp hbot
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    ·
      intro htop
      apply hBX
      have hle : (⊤ : Subgroup X) ≤ π.ker ⊔ B := by
        intro x _
        have hx : π x ∈ B.map π := htop ▸ Subgroup.mem_top (π x)
        obtain ⟨b, hb, hbx⟩ := hx
        have hk : b⁻¹ * x ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hbx, inv_mul_cancel]
        have e : x = b * (b⁻¹ * x) := by group
        rw [e]
        exact mul_mem (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left hk)
      exact top_le_iff.mp (CFSG.Goldschmidt.G37.le_of_perfect_of_le_sup
        (Group.IsPerfect.top_iff.mpr hX) hle hKN hKs)
    · rw [← Subgroup.map_sup]
      exact Group.isSolvable_of_surjective (π.subgroupMap_surjective (D ⊔ U))
  · exact le_normalizer_of_borel (Or.inr (Or.inl h)) hX hU hB hBs hBX hUB hD
  · exact le_normalizer_of_borel (Or.inr (Or.inr h)) hX hU hB hBs hBX hUB hD

theorem le_normalizer_of_inner_lie {Y : Type} [Group Y] [Finite Y] {T B L D : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hL : L ∈ cComp ⊤) (hBL : B < L)
    (hLn : L.Normal) (hLie : IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L) (hD3 : IsPGroup 3 D)
    (hDL : D ≤ L) (hDT : (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y))
    (hTB : T ≤ Subgroup.normalizer (B : Set Y)) : D ≤ Subgroup.normalizer (B : Set Y) := by
  obtain ⟨hU, hX, hBp, hBs, hBX, hUB⟩ := block_data hT hB hL hBL hLn hTB
  have hle : (D.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map L.subtype ≤ D ⊔ T := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx).1
  have : Group.IsSolvable ↥(D ⊔ T) := isSolvable_sup_of_mul_comm hD3 hT.2.1 hDT
  have hDU : Group.IsSolvable ↥(D.subgroupOf L ⊔ (T ⊓ L).subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion hle).comp (Subgroup.equivMapOfInjective _ L.subtype
        L.subtype_injective).toMonoidHom)
      ((Subgroup.inclusion_injective hle).comp (MulEquiv.injective _))
  have hmain := le_normalizer_of_isLie hLie hX hU hBp hBs hBX hUB hDU
  exact fun d hd => mem_normalizer_of_subgroupOf hBL.le (hDL hd)
    (hmain (Subgroup.mem_subgroupOf.mpr hd))

end Lie

end CFSG.Quasithin.H13.Ch9.FFC
