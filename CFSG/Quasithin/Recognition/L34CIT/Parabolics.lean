module

public import CFSG.Quasithin.Recognition.L34CIT.PointsLines
public import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.Defs

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

namespace Config

@[expose] def swap (C : Config A) : Config A where
  T := C.T
  L := C.M
  M := C.L
  card_T := C.card_T
  L_le := C.M_le
  M_le := C.L_le
  isElemAbelian_L := C.isElemAbelian_M
  isElemAbelian_M := C.isElemAbelian_L
  card_L := C.card_M
  card_M := C.card_L
  eq_or_eq := fun E hE hEA hEc => Or.comm.mp (C.eq_or_eq E hE hEA hEc)
  card_inf := by simpa [inf_comm] using C.card_inf
  inf_le_centralizer := by simpa [inf_comm] using C.inf_le_centralizer
  mul_self_mem := fun x hx => by simpa [inf_comm] using C.mul_self_mem x hx
  mem_or_mem := fun x hx hx2 => Or.comm.mp (C.mem_or_mem x hx hx2)
  centralizer_L := fun x hx hxZ => by
    have hxZ' : x ∉ C.L ⊓ C.M := by simpa [inf_comm] using hxZ
    simpa using C.centralizer_M x hx hxZ'
  centralizer_M := fun x hx hxZ => by
    have hxZ' : x ∉ C.L ⊓ C.M := by simpa [inf_comm] using hxZ
    simpa using C.centralizer_L x hx hxZ'
  isPGroup_centralizer := C.isPGroup_centralizer
  centralizer_L_le := C.centralizer_M_le
  centralizer_M_le := C.centralizer_L_le
  quotL := C.quotM
  quotL_surjective := C.quotM_surjective
  ker_quotL := C.ker_quotM
  quotM := C.quotL
  quotM_surjective := C.quotL_surjective
  ker_quotM := C.ker_quotL
  exists_conj_L := C.exists_conj_M
  exists_conj_M := C.exists_conj_L
  exists_fpf_L := C.exists_fpf_M
  exists_fpf_M := C.exists_fpf_L

@[simp] theorem swap_T (C : Config A) : C.swap.T = C.T := rfl

@[simp] theorem swap_L (C : Config A) : C.swap.L = C.M := rfl

@[simp] theorem swap_M (C : Config A) : C.swap.M = C.L := rfl

abbrev K₁ (C : Config A) : Subgroup A := normalizer (C.L : Set A)

abbrev K₂ (C : Config A) : Subgroup A := normalizer (C.M : Set A)

noncomputable def Tbar (C : Config A) [Finite A] :
    Sylow 2 (alternatingGroup (Fin 5)) :=
  C.isSylow_normalizer_L.mapSurjective C.quotL_surjective

@[simp] theorem coe_Tbar (C : Config A) [Finite A] :
    (C.Tbar : Subgroup (alternatingGroup (Fin 5))) =
      ((C.T : Subgroup A).subgroupOf (C.K₁)).map C.quotL := by
  rw [Tbar, Sylow.coe_mapSurjective, C.coe_isSylow_normalizer_L]

theorem comap_Tbar (C : Config A) [Finite A] :
    (C.Tbar : Subgroup (alternatingGroup (Fin 5))).comap C.quotL =
      (C.T : Subgroup A).subgroupOf C.K₁ := by
  ext x
  rw [Subgroup.mem_comap, coe_Tbar, Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, htx⟩
    have hx : ((x : C.K₁)⁻¹ * t : C.K₁) ∈ C.quotL.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, htx]
      group
    rw [C.ker_quotL] at hx
    have hxL : ((x : C.K₁)⁻¹ * (t : C.K₁) : C.K₁) ∈ C.L.subgroupOf C.K₁ := hx
    have hxL' : (((x : C.K₁)⁻¹ * (t : C.K₁) : C.K₁) : A) ∈ C.L := hxL
    have hmem : (((t : C.K₁)⁻¹ * (x : C.K₁) : C.K₁) : A) ∈ C.L := by
      simpa [mul_assoc] using C.L.inv_mem hxL'
    have hxT : (x : A) ∈ C.T := by
      have hxeq : (x : A) = (t : C.K₁) * (((t : C.K₁)⁻¹ * (x : C.K₁) : C.K₁) : A) := by
        simp [mul_assoc]
      rw [hxeq]
      exact C.T.mul_mem ht (C.L_le hmem)
    exact hxT
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem normalizer_T_eq_inf (C : Config A) [Finite A] :
    normalizer (C.T : Set A) =
      normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A) := by
  refine le_antisymm C.normalizer_T_le ?_
  intro k hk
  rw [Subgroup.mem_inf] at hk
  have hL : MulAut.conj k • C.L = C.L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hk.1
  have hM : MulAut.conj k • C.M = C.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hk.2
  have h : MulAut.conj k • (C.T : Subgroup A) = (C.T : Subgroup A) := by
    rw [show (C.T : Subgroup A) = C.L ⊔ C.M from C.sup_eq.symm, Subgroup.smul_sup, hL, hM]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem normalizer_T_subgroupOf_eq (C : Config A) [Finite A] :
    (normalizer (C.T : Set A)).subgroupOf C.K₁ =
      (normalizer ((C.Tbar : Subgroup (alternatingGroup (Fin 5))) :
        Set (alternatingGroup (Fin 5)))).comap C.quotL := by
  rw [Subgroup.comap_normalizer_eq_of_surjective
    (C.Tbar : Subgroup (alternatingGroup (Fin 5))) C.quotL_surjective,
    C.comap_Tbar]
  exact Subgroup.subgroupOf_normalizer_eq C.T_le_normalizer_L

theorem card_normalizer_T (C : Config A) [Finite A] :
    Nat.card (normalizer (C.T : Set A)) = 192 := by
  have hcardN : Nat.card ↥((normalizer (C.T : Set A)).subgroupOf C.K₁) =
      Nat.card (normalizer (C.T : Set A)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (C.normalizer_T_le.trans inf_le_left)).toEquiv
  have hcardH : Nat.card ↥(normalizer (C.Tbar : Set (alternatingGroup (Fin 5)))) = 12 :=
    CFSG.GroupTheory.AlternatingFive.card_normalizer_sylow_two C.Tbar
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hidx : (normalizer (C.Tbar : Set (alternatingGroup (Fin 5)))).index = 5 := by
    have hmul := Subgroup.index_mul_card
      (normalizer (C.Tbar : Set (alternatingGroup (Fin 5))))
    rw [hcardH, hcardA5] at hmul
    omega
  have hidxcomap :
      ((normalizer (C.Tbar : Set (alternatingGroup (Fin 5)))).comap C.quotL).index = 5 := by
    rw [Subgroup.index_comap_of_surjective
      (normalizer (C.Tbar : Set (alternatingGroup (Fin 5)))) C.quotL_surjective]
    exact hidx
  have hcardcomap :
      Nat.card ↥((normalizer (C.Tbar : Set (alternatingGroup (Fin 5)))).comap C.quotL) = 192 := by
    have hmul := Subgroup.index_mul_card
      ((normalizer (C.Tbar : Set (alternatingGroup (Fin 5)))).comap C.quotL)
    rw [hidxcomap, C.card_normalizer_L] at hmul
    omega
  rw [← hcardN, C.normalizer_T_subgroupOf_eq]
  exact hcardcomap

theorem relIndex_inf_normalizer_L (C : Config A) [Finite A] :
    (normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A)).relIndex
        (normalizer (C.L : Set A)) = 5 := by
  have hmul := Subgroup.relIndex_mul_card
    (normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A))
    (normalizer (C.L : Set A))
  have hinf : (normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A)) ⊓
      normalizer (C.L : Set A) =
        normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A) := by
    rw [inf_comm (normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A))
      (normalizer (C.L : Set A)), ← inf_assoc, inf_idem]
  have hcard : Nat.card ↥(normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A)) = 192 := by
    rw [← C.normalizer_T_eq_inf]
    exact C.card_normalizer_T
  rw [hinf, hcard, C.card_normalizer_L] at hmul
  omega

theorem le_normalizer_L_of_le_sylow (C : Config A) [Finite A] {P : Sylow 2 A}
    (hP : C.L ≤ (P : Subgroup A)) : (P : Subgroup A) ≤ C.K₁ := by
  obtain ⟨g, hg⟩ := C.exists_conj_eq P
  have hL : MulAut.conj g • C.L = C.L := by
    have h1 : C.L ≤ MulAut.conj g • (C.T : Subgroup A) := by
      simpa [hg] using hP
    have h := C.conj_eq_of_le_L (a := 1) (g := g) (by simpa using h1)
    simpa using h.symm
  have hK : g ∈ C.K₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hL
  intro p hp
  rw [hg] at hp
  change p ∈ (C.T : Subgroup A).map (MulAut.conj g).toMonoidHom at hp
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hp
  have hmem : g * t * g⁻¹ ∈ C.K₁ :=
    C.K₁.mul_mem (C.K₁.mul_mem hK (C.T_le_normalizer_L ht)) (C.K₁.inv_mem hK)
  simpa [MulAut.conj_apply] using hmem

noncomputable def sylowContainingToFun (C : Config A) [Finite A] :
    {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} → Sylow 2 C.K₁ :=
  fun P => P.1.subtype (C.le_normalizer_L_of_le_sylow P.2)

theorem ncard_sylow_ge_L (C : Config A) [Finite A] :
    {P : Sylow 2 A | C.L ≤ (P : Subgroup A)}.ncard = 5 := by
  rw [← Nat.card_coe_set_eq]
  have hcard_sylow : Nat.card (Sylow 2 C.K₁) = 5 := by
    rw [Sylow.card_eq_index_normalizer C.isSylow_normalizer_L]
    have hcardN :
        Nat.card ↥(normalizer (C.isSylow_normalizer_L : Set C.K₁)) = 192 := by
      have hsub : normalizer (C.isSylow_normalizer_L : Set C.K₁) =
          (normalizer (C.T : Set A)).subgroupOf C.K₁ := by
        change normalizer ((C.isSylow_normalizer_L : Subgroup C.K₁) : Set C.K₁) =
          (normalizer (C.T : Set A)).subgroupOf C.K₁
        rw [C.coe_isSylow_normalizer_L]
        exact (Subgroup.subgroupOf_normalizer_eq C.T_le_normalizer_L).symm
      rw [hsub]
      have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (C.normalizer_T_le.trans inf_le_left)).toEquiv
      rw [hcard, C.card_normalizer_T]
    have hmul := Subgroup.index_mul_card
      (normalizer (C.isSylow_normalizer_L : Set C.K₁))
    rw [hcardN, C.card_normalizer_L] at hmul
    omega
  have hinj : Function.Injective C.sylowContainingToFun := by
    intro P P' h
    exact Subtype.ext (Sylow.subtype_injective h)
  have hsurj : Function.Surjective C.sylowContainingToFun := by
    intro Q
    obtain ⟨P, hP⟩ := Sylow.exists_comap_subtype_eq (p := 2) (H := C.K₁) Q
    have hLQ : C.L.subgroupOf C.K₁ ≤ (Q : Subgroup C.K₁) := by
      have hLp : IsPGroup 2 ↥(C.L.subgroupOf C.K₁) := by
        refine IsPGroup.of_card (n := 4) ?_
        rw [show Nat.card ↥(C.L.subgroupOf C.K₁) = Nat.card ↥C.L from
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := C.L) (K := C.K₁)
            Subgroup.le_normalizer)]
        rw [C.card_L]
        norm_num
      exact hLp.le_sylow_of_normal Q
    have hLP : C.L ≤ (P : Subgroup A) := by
      intro l hl
      have hlK : l ∈ C.K₁ := Subgroup.le_normalizer hl
      have hmem : (⟨l, hlK⟩ : C.K₁) ∈ (Q : Subgroup C.K₁) := hLQ hl
      rw [← hP] at hmem
      exact hmem
    refine ⟨⟨P, hLP⟩, ?_⟩
    apply Sylow.ext
    rw [sylowContainingToFun, Sylow.coe_subtype]
    change (P : Subgroup A).subgroupOf C.K₁ = (Q : Subgroup C.K₁)
    rw [← hP]
    rfl
  change Nat.card {P : Sylow 2 A // C.L ≤ (P : Subgroup A)} = 5
  exact (Nat.card_congr (Equiv.ofBijective C.sylowContainingToFun ⟨hinj, hsurj⟩)).trans
    hcard_sylow

theorem comap_image_point (C : Config A) [Finite A] {P : Sylow 2 A}
    (hP : C.L ≤ (P : Subgroup A)) :
    ∃ Pbar : Sylow 2 (alternatingGroup (Fin 5)),
      (Pbar : Subgroup (alternatingGroup (Fin 5))).comap C.quotL =
        (P : Subgroup A).subgroupOf C.K₁ := by
  let hPK : (P : Subgroup A) ≤ C.K₁ := C.le_normalizer_L_of_le_sylow hP
  let Q : Sylow 2 C.K₁ := P.subtype hPK
  let Pbar : Sylow 2 (alternatingGroup (Fin 5)) := Q.mapSurjective C.quotL_surjective
  refine ⟨Pbar, ?_⟩
  have hcoe : (Pbar : Subgroup (alternatingGroup (Fin 5))) =
      (Q : Subgroup C.K₁).map C.quotL := by
    dsimp only [Pbar]
    rw [Sylow.coe_mapSurjective]
  rw [hcoe]
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, htx⟩
    change ((t : C.K₁) : A) ∈ P at ht
    have hx : ((x : C.K₁)⁻¹ * t : C.K₁) ∈ C.quotL.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, htx]
      group
    rw [C.ker_quotL] at hx
    have hxL' : (((x : C.K₁)⁻¹ * (t : C.K₁) : C.K₁) : A) ∈ C.L := hx
    have hmem : (((t : C.K₁)⁻¹ * (x : C.K₁) : C.K₁) : A) ∈ C.L := by
      simpa [mul_assoc] using C.L.inv_mem hxL'
    have hxP : (x : A) ∈ P := by
      have hxeq : (x : A) = (t : C.K₁) * (((t : C.K₁)⁻¹ * (x : C.K₁) : C.K₁) : A) := by
        simp [mul_assoc]
      rw [hxeq]
      exact P.mul_mem ht (hP hmem)
    exact hxP
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem inf_eq_L_of_ne (C : Config A) [Finite A] {P P' : Sylow 2 A}
    (hP : C.L ≤ (P : Subgroup A)) (hP' : C.L ≤ (P' : Subgroup A)) (hne : P ≠ P') :
    (P : Subgroup A) ⊓ P' = C.L := by
  obtain ⟨Pbar, hPbar⟩ := C.comap_image_point hP
  obtain ⟨P'bar, hP'bar⟩ := C.comap_image_point hP'
  have hbarne : Pbar ≠ P'bar := by
    intro h
    apply hne
    apply Sylow.ext
    have hcomap : (Pbar : Subgroup (alternatingGroup (Fin 5))).comap C.quotL =
        (P'bar : Subgroup (alternatingGroup (Fin 5))).comap C.quotL := by rw [h]
    rw [hPbar, hP'bar] at hcomap
    have hinf := Subgroup.subgroupOf_inj.mp hcomap
    rwa [inf_eq_left.mpr (C.le_normalizer_L_of_le_sylow hP),
      inf_eq_left.mpr (C.le_normalizer_L_of_le_sylow hP')] at hinf
  have hbot := CFSG.GroupTheory.AlternatingFive.inf_eq_bot_of_ne hbarne
  have hsubL : ((P : Subgroup A) ⊓ P').subgroupOf C.K₁ = C.L.subgroupOf C.K₁ := by
    have hsubinf : ((P : Subgroup A) ⊓ P').subgroupOf C.K₁ =
        (P : Subgroup A).subgroupOf C.K₁ ⊓ (P' : Subgroup A).subgroupOf C.K₁ := by
      ext x
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hcomapinf : (Pbar ⊓ P'bar : Subgroup (alternatingGroup (Fin 5))).comap C.quotL =
        (P : Subgroup A).subgroupOf C.K₁ ⊓ (P' : Subgroup A).subgroupOf C.K₁ := by
      rw [Subgroup.comap_inf, hPbar, hP'bar]
    rw [hsubinf, ← hcomapinf, hbot, MonoidHom.comap_bot, C.ker_quotL]
  have hinf := Subgroup.subgroupOf_inj.mp hsubL
  rwa [inf_eq_left.mpr (inf_le_left.trans (C.le_normalizer_L_of_le_sylow hP)),
    inf_eq_left.mpr (Subgroup.le_normalizer (H := C.L))] at hinf

theorem line_le_normalizer_point (C : Config A) [Finite A] {a b : A}
    (h : ∃ P : Sylow 2 A, MulAut.conj a • C.L ≤ (P : Subgroup A) ∧
      MulAut.conj b • C.M ≤ (P : Subgroup A)) :
    MulAut.conj b • C.M ≤ normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A) := by
  obtain ⟨P, hX, hY⟩ := h
  obtain ⟨p, hp⟩ := C.exists_conj_eq P
  have hX' : MulAut.conj a • C.L ≤ MulAut.conj p • (C.T : Subgroup A) := by rwa [hp] at hX
  have hY' : MulAut.conj b • C.M ≤ MulAut.conj p • (C.T : Subgroup A) := by rwa [hp] at hY
  have hXeq := C.conj_eq_of_le_L hX'
  have hYeq := C.conj_eq_of_le_M hY'
  have hmap : MulAut.conj p • C.M ≤ MulAut.conj p • normalizer (C.L : Set A) :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.M_le_normalizer_L
  have hnorm : MulAut.conj p • normalizer (C.L : Set A) =
      normalizer ((MulAut.conj p • C.L : Subgroup A) : Set A) :=
    Subgroup.map_equiv_normalizer_eq C.L (MulAut.conj p)
  rw [hXeq, hYeq]
  rwa [hnorm] at hmap

theorem card_inf_point_line (C : Config A) [Finite A] {a b : A}
    (h : ∃ P : Sylow 2 A, MulAut.conj a • C.L ≤ (P : Subgroup A) ∧
      MulAut.conj b • C.M ≤ (P : Subgroup A)) :
    Nat.card ↥(MulAut.conj a • C.L ⊓ MulAut.conj b • C.M) = 4 := by
  obtain ⟨P, hX, hY⟩ := h
  obtain ⟨p, hp⟩ := C.exists_conj_eq P
  have hX' : MulAut.conj a • C.L ≤ MulAut.conj p • (C.T : Subgroup A) := by rwa [hp] at hX
  have hY' : MulAut.conj b • C.M ≤ MulAut.conj p • (C.T : Subgroup A) := by rwa [hp] at hY
  have hXeq := C.conj_eq_of_le_L hX'
  have hYeq := C.conj_eq_of_le_M hY'
  rw [hXeq, hYeq]
  have hmapinf : MulAut.conj p • (C.L ⊓ C.M : Subgroup A) =
      MulAut.conj p • C.L ⊓ MulAut.conj p • C.M := by
    exact Subgroup.map_inf C.L C.M (MulAut.conj p).toMonoidHom (MulAut.conj p).injective
  rw [← hmapinf, card_conj, C.card_inf]

theorem mem_point_or_line_of_mem_sylow (C : Config A) [Finite A] {p x : A}
    (hxP : x ∈ MulAut.conj p • (C.T : Subgroup A)) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    x ∈ MulAut.conj p • C.L ∨ x ∈ MulAut.conj p • C.M := by
  have hxT : (MulAut.conj p)⁻¹ • x ∈ C.T :=
    (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hxP
  have hxT' : p⁻¹ * x * p ∈ C.T := by
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hxT
  have hx2' : (p⁻¹ * x * p) * (p⁻¹ * x * p) = 1 := by
    calc (p⁻¹ * x * p) * (p⁻¹ * x * p) = p⁻¹ * (x * x) * p := by group
      _ = 1 := by rw [hx2]; group
  have hx1' : p⁻¹ * x * p ≠ 1 := by
    intro h
    apply hx1
    calc x = p * (p⁻¹ * x * p) * p⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases C.mem_or_mem (p⁻¹ * x * p) hxT' hx2' with hL | hM
  · left
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hL
  · right
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hM

theorem eq_line_of_two_points_geom (C : Config A) [Finite A]
    {X X' Y Y' : Subgroup A}
    (hX : ∃ a : A, X = MulAut.conj a • C.L)
    (hX' : ∃ b : A, X' = MulAut.conj b • C.L)
    (hY : ∃ c : A, Y = MulAut.conj c • C.M)
    (hY' : ∃ d : A, Y' = MulAut.conj d • C.M)
    (hne : X ≠ X')
    (hXY : ∃ P : Sylow 2 A, X ≤ (P : Subgroup A) ∧ Y ≤ (P : Subgroup A))
    (hX'Y : ∃ P : Sylow 2 A, X' ≤ (P : Subgroup A) ∧ Y ≤ (P : Subgroup A))
    (hXY' : ∃ P : Sylow 2 A, X ≤ (P : Subgroup A) ∧ Y' ≤ (P : Subgroup A))
    (hX'Y' : ∃ P : Sylow 2 A, X' ≤ (P : Subgroup A) ∧ Y' ≤ (P : Subgroup A)) :
    Y = Y' := by
  obtain ⟨a, rfl⟩ := hX
  obtain ⟨b, rfl⟩ := hX'
  obtain ⟨c, rfl⟩ := hY
  obtain ⟨d, rfl⟩ := hY'
  have hX'ea : IsElemAbelian 2 (MulAut.conj b • C.L) := isElemAbelian_conj C.isElemAbelian_L b
  have hneR : MulAut.conj b • C.L ⊓ MulAut.conj c • C.M ≠ ⊥ := by
    intro hbot
    have hcard := C.card_inf_point_line hX'Y
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨e, he⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hneR
  have hneR' : MulAut.conj b • C.L ⊓ MulAut.conj d • C.M ≠ ⊥ := by
    intro hbot
    have hcard := C.card_inf_point_line hX'Y'
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨f, hf⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hneR'
  have he1 : (e : A) ≠ 1 := fun h => he (Subtype.ext h)
  have hf1 : (f : A) ≠ 1 := fun h => hf (Subtype.ext h)
  have he2 : (e : A) * (e : A) = 1 := by
    have := hX'ea.2 e e.2.1
    simpa [pow_two] using this
  have hf2 : (f : A) * (f : A) = 1 := by
    have := hX'ea.2 f f.2.1
    simpa [pow_two] using this
  have hcomm : (e : A) * (f : A) = (f : A) * (e : A) := by
    haveI := hX'ea.1
    exact congrArg Subtype.val (mul_comm' (⟨(e : A), e.2.1⟩ : ↥(MulAut.conj b • C.L))
      ⟨(f : A), f.2.1⟩)
  have heN : (e : A) ∈ normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A) :=
    C.line_le_normalizer_point hXY e.2.2
  have hfN : (f : A) ∈ normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A) :=
    C.line_le_normalizer_point hXY' f.2.2
  have hze : IsPGroup 2 ↥(Subgroup.zpowers (e : A)) :=
    (CFSG.Open.isElemAbelian_zpowers (p := 2) (by simpa [pow_two] using he2)).isPGroup
  have hzf : IsPGroup 2 ↥(Subgroup.zpowers (f : A)) :=
    (CFSG.Open.isElemAbelian_zpowers (p := 2) (by simpa [pow_two] using hf2)).isPGroup
  have hzf_norm : Subgroup.zpowers (f : A) ≤
      normalizer (Subgroup.zpowers (e : A) : Set A) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : Commute ((f : A) ^ m) ((e : A) ^ n) :=
      (Commute.zpow_zpow hcomm n m).symm
    have hzw : ((f : A) ^ m) * ((e : A) ^ n) * ((f : A) ^ m)⁻¹ = (e : A) ^ n := by
      rw [hc.eq]
      group
    rw [hzw]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  have hef2 : IsPGroup 2 ↥(Subgroup.zpowers (e : A) ⊔ Subgroup.zpowers (f : A)) :=
    hze.to_sup_of_normal_left' hzf hzf_norm
  have hef_norm : (Subgroup.zpowers (e : A) ⊔ Subgroup.zpowers (f : A)) ≤
      normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact heN
    · rw [Subgroup.zpowers_le]
      exact hfN
  have hXp : IsPGroup 2 ↥(MulAut.conj a • C.L) :=
    (isElemAbelian_conj C.isElemAbelian_L a).isPGroup
  have hsup2 : IsPGroup 2 ↥(MulAut.conj a • C.L ⊔
      (Subgroup.zpowers (e : A) ⊔ Subgroup.zpowers (f : A))) :=
    hXp.to_sup_of_normal_left' hef2 hef_norm
  obtain ⟨P, hPle⟩ := hsup2.exists_le_sylow
  have hXP : MulAut.conj a • C.L ≤ (P : Subgroup A) := le_trans le_sup_left hPle
  have heP : (e : A) ∈ (P : Subgroup A) :=
    hPle (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have hfP : (f : A) ∈ (P : Subgroup A) :=
    hPle (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have he_notX : (e : A) ∉ MulAut.conj a • C.L := by
    intro heX
    have hbot := C.inf_eq_bot_of_ne_L hne
    have : (e : A) ∈ (⊥ : Subgroup A) := by
      rw [← hbot]
      exact ⟨heX, e.2.1⟩
    exact he1 (by simpa using this)
  obtain ⟨p, hp⟩ := C.exists_conj_eq P
  have hXP' : MulAut.conj a • C.L ≤ MulAut.conj p • (C.T : Subgroup A) := by rwa [hp] at hXP
  have hXeqp : MulAut.conj a • C.L = MulAut.conj p • C.L := C.conj_eq_of_le_L hXP'
  have heP' : (e : A) ∈ MulAut.conj p • (C.T : Subgroup A) := by rwa [hp] at heP
  have he_lineP : (e : A) ∈ MulAut.conj p • C.M := by
    rcases C.mem_point_or_line_of_mem_sylow (p := p) heP' he2 he1 with heX | heM
    · exact absurd (by rwa [← hXeqp] at heX) he_notX
    · exact heM
  have hYeqP : MulAut.conj c • C.M = MulAut.conj p • C.M := by
    by_contra hnecp
    have hinf := C.inf_eq_bot_of_ne_M hnecp
    have hmem : (e : A) ∈ (⊥ : Subgroup A) := by
      rw [← hinf]
      exact ⟨e.2.2, he_lineP⟩
    exact he1 (by simpa using hmem)
  have hfP' : (f : A) ∈ MulAut.conj p • (C.T : Subgroup A) := by rwa [hp] at hfP
  have hf_lineP : (f : A) ∈ MulAut.conj p • C.M := by
    rcases C.mem_point_or_line_of_mem_sylow (p := p) hfP' hf2 hf1 with hfX | hfM
    · exact absurd (by rwa [← hXeqp] at hfX) (by
        intro hfX'
        have hbot := C.inf_eq_bot_of_ne_L hne
        have : (f : A) ∈ (⊥ : Subgroup A) := by
          rw [← hbot]
          exact ⟨hfX', f.2.1⟩
        exact hf1 (by simpa using this))
    · exact hfM
  have hY'eqP : MulAut.conj d • C.M = MulAut.conj p • C.M := by
    by_contra hnedp
    have hinf := C.inf_eq_bot_of_ne_M hnedp
    have hmem : (f : A) ∈ (⊥ : Subgroup A) := by
      rw [← hinf]
      exact ⟨f.2.2, hf_lineP⟩
    exact hf1 (by simpa using hmem)
  exact hYeqP.trans hY'eqP.symm

theorem eq_line_of_two_points (C : Config A) [Finite A] :
    ∀ h ∈ normalizer (C.L : Set A), ∀ g ∈ normalizer (C.M : Set A),
      g ∉ normalizer (C.L : Set A) → ∀ l ∈ normalizer (C.L : Set A),
        ∀ m ∈ normalizer (C.M : Set A), g * l = h * m →
          h ∈ normalizer (C.M : Set A) := by
  intro h hh g hg gK l hl m hm hglhm
  let K₁ := normalizer (C.L : Set A)
  let K₂ := normalizer (C.M : Set A)
  have hInc1 : CFSG.Quasithin.A94.He42Plane.Inc K₁ K₂
      ((1 : A) : A ⧸ K₁) ((1 : A) : A ⧸ K₂) :=
    (CFSG.Quasithin.A94.He42Plane.he42pl_inc_iff_exists K₁ K₂ 1 1).2
      ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  have hIncX'Y : CFSG.Quasithin.A94.He42Plane.Inc K₁ K₂
      ((g : A) : A ⧸ K₁) ((1 : A) : A ⧸ K₂) :=
    (CFSG.Quasithin.A94.He42Plane.he42pl_inc_iff_exists K₁ K₂ g 1).2
      ⟨1, Subgroup.one_mem _, g, hg, by simp⟩
  have hIncXY' : CFSG.Quasithin.A94.He42Plane.Inc K₁ K₂
      ((1 : A) : A ⧸ K₁) ((h : A) : A ⧸ K₂) :=
    (CFSG.Quasithin.A94.He42Plane.he42pl_inc_iff_exists K₁ K₂ 1 h).2
      ⟨h, hh, 1, Subgroup.one_mem _, by simp⟩
  have hIncX'Y' : CFSG.Quasithin.A94.He42Plane.Inc K₁ K₂
      ((g : A) : A ⧸ K₁) ((h : A) : A ⧸ K₂) :=
    (CFSG.Quasithin.A94.He42Plane.he42pl_inc_iff_exists K₁ K₂ g h).2
      ⟨l, hl, m, hm, hglhm⟩
  have hne : MulAut.conj (1 : A) • C.L ≠ MulAut.conj g • C.L := by
    intro heq
    apply gK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h2 : MulAut.conj g • C.L = C.L := by simpa using heq.symm
    exact h2
  have hYeq : MulAut.conj (1 : A) • C.M = MulAut.conj h • C.M :=
    C.eq_line_of_two_points_geom ⟨1, rfl⟩ ⟨g, rfl⟩ ⟨1, rfl⟩ ⟨h, rfl⟩ hne
      ((C.inc_iff 1 1).mp hInc1) ((C.inc_iff g 1).mp hIncX'Y)
      ((C.inc_iff 1 h).mp hIncXY') ((C.inc_iff g h).mp hIncX'Y')
  have hM : MulAut.conj h • C.M = C.M := by simpa using hYeq.symm
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hM

theorem relIndex_inf_normalizer_M (C : Config A) [Finite A] :
    (normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A)).relIndex
        (normalizer (C.M : Set A)) = 5 := by
  simpa [inf_comm] using C.swap.relIndex_inf_normalizer_L

theorem ncard_sylow_ge_M (C : Config A) [Finite A] :
    {P : Sylow 2 A | C.M ≤ (P : Subgroup A)}.ncard = 5 :=
  C.swap.ncard_sylow_ge_L

end Config

end CFSG.Quasithin.L34CIT
