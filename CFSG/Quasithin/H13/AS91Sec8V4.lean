module

public import CFSG.Quasithin.H13.AS91MainB
public import CFSG.Quasithin.H13.AS91Sec8Four
public import CFSG.Quasithin.H13.AS91Sec7Eight

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)
open CFSG.Monster.Code (mem_AutPerm_of_basis)

namespace M24G

@[expose] def flagPerm : Equiv.Perm (Fin 24) where
  toFun :=
    ![0, 1, 3, 2, 4, 5, 7, 6, 16, 17, 19, 18, 20, 21, 23, 22, 12, 13, 15, 14, 8, 9, 11, 10]
  invFun :=
    ![0, 1, 3, 2, 4, 5, 7, 6, 20, 21, 23, 22, 16, 17, 19, 18, 8, 9, 11, 10, 12, 13, 15, 14]
  left_inv := by decide
  right_inv := by decide

private theorem flagPerm_basis :
    ∀ i : Fin 12, CFSG.Monster.Code.B i ∘ ⇑flagPerm ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem flagPerm_basis' :
    ∀ i : Fin 12, CFSG.Monster.Code.B i ∘ ⇑flagPerm⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem flagPerm_mem : flagPerm ∈ M24g :=
  mem_AutPerm_of_basis flagPerm_basis flagPerm_basis'

abbrev octMasksE0 : List ℕ :=
  [255, 65280, 16711680, 3855, 61455, 4080, 61680, 983055, 15728655, 983280, 15728880,
    986880, 15732480, 1044480, 15790080]

theorem octsOf_sextE0_eq : octsOf sextE0 = (octMasksE0.map maskFin).toFinset := by
  decide +kernel

theorem octMasksE0_orbits :
    ∀ m ∈ octMasksE0,
      maskFin m ∈ trioC ∨ ({maskFin m, flagPerm • maskFin m,
        flagPerm • (flagPerm • maskFin m),
        flagPerm • (flagPerm • (flagPerm • maskFin m))} :
          Finset (Finset (Fin 24))).card = 4 := by
  decide +kernel

theorem octsOf_sextE0_orbit_aux {o : Finset (Fin 24)} (ho : o ∈ octsOf sextE0) :
    o ∈ trioC ∨ ({o, flagPerm • o, flagPerm • (flagPerm • o),
      flagPerm • (flagPerm • (flagPerm • o))} : Finset (Finset (Fin 24))).card = 4 := by
  rw [octsOf_sextE0_eq, List.mem_toFinset, List.mem_map] at ho
  obtain ⟨m, hm, rfl⟩ := ho
  exact octMasksE0_orbits m hm

theorem flagPerm_smul_trioFin_zero :
    flagPerm • trioFin 0 = trioFin 0 := by
  rw [trioFin_zero_eq]
  show flagPerm • trioC = trioC
  decide +kernel

theorem flagPerm_smul_sextFin_zero :
    flagPerm • sextFin 0 = sextFin 0 := by
  rw [sextFin_zero_eq]
  decide +kernel

theorem eq_trioFin_zero_of_flagPerm
    {T : Finset (Finset (Fin 24))}
    (hT : T ⊆ octsOf (sextFin 0)) (hcard : T.card = 3) (hfix : flagPerm • T = T) :
    T = trioFin 0 := by
  rw [sextFin_zero_eq] at hT
  have hsub : T ⊆ trioC := by
    intro o ho
    rcases octsOf_sextE0_orbit_aux (hT ho) with h | h
    · exact h
    · exfalso
      have h1 : flagPerm • o ∈ T := by
        have h' := Finset.smul_mem_smul_finset (a := flagPerm) ho
        rwa [hfix] at h'
      have h2 : flagPerm • (flagPerm • o) ∈ T := by
        have h' := Finset.smul_mem_smul_finset (a := flagPerm) h1
        rwa [hfix] at h'
      have h3 : flagPerm • (flagPerm • (flagPerm • o)) ∈ T := by
        have h' := Finset.smul_mem_smul_finset (a := flagPerm) h2
        rwa [hfix] at h'
      have hsub4 : ({o, flagPerm • o, flagPerm • (flagPerm • o),
          flagPerm • (flagPerm • (flagPerm • o))} : Finset (Finset (Fin 24))) ⊆ T := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        exacts [ho, h1, h2, h3]
      have hle := Finset.card_le_card hsub4
      omega
  have hcardE : trioC.card = 3 := by decide
  rw [trioFin_zero_eq]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcardE, hcard])

theorem eq_of_forall_smul_eq
    {l U l' : Finset (Finset (Fin 24))} (hl : IsTrio l) (hU : IsSextet U) (hlU : TrioIn l U)
    (hl' : IsTrio l') (hl'U : TrioIn l' U)
    (hfix : ∀ m ∈ M24g, m • l = l → m • U = U → m • l' = l') : l' = l := by
  obtain ⟨σ, hσ, hσl, hσU⟩ := exists_smul_trio_sextet hl (isTrio_trioFin (p := 0) (by norm_num)) hU
    (isSextet_sextFin (q := 0) (by norm_num)) hlU
    (by rw [trioFin_zero_eq, sextFin_zero_eq]; exact sub_trioC)
  set m : S24 := σ⁻¹ * flagPerm * σ with hm_def
  have hm : m ∈ M24g :=
    Subgroup.mul_mem M24g (Subgroup.mul_mem M24g (Subgroup.inv_mem M24g hσ) flagPerm_mem) hσ
  have hml : m • l = l := by
    rw [hm_def, mul_smul, mul_smul, hσl, flagPerm_smul_trioFin_zero, ← hσl, inv_smul_smul]
  have hmU : m • U = U := by
    rw [hm_def, mul_smul, mul_smul, hσU, flagPerm_smul_sextFin_zero, ← hσU, inv_smul_smul]
  have hl'fix : flagPerm • (σ • l') = σ • l' := by
    have h := hfix m hm hml hmU
    have hconj : σ * m = flagPerm * σ := by
      rw [hm_def]
      group
    calc flagPerm • (σ • l') = (flagPerm * σ) • l' := (mul_smul _ _ _).symm
      _ = (σ * m) • l' := by rw [hconj]
      _ = σ • (m • l') := mul_smul _ _ _
      _ = σ • l' := by rw [h]
  have hsub : σ • l' ⊆ octsOf (sextFin 0) := by
    have h := (trioIn_smul_iff σ).2 hl'U
    rwa [hσU] at h
  have hcard : (σ • l').card = 3 := by
    rw [Finset.card_smul_finset]
    exact hl'.1
  have hEq : σ • l' = trioFin 0 := eq_trioFin_zero_of_flagPerm hsub hcard hl'fix
  calc l' = σ⁻¹ • (σ • l') := (inv_smul_smul σ l').symm
    _ = σ⁻¹ • trioFin 0 := by rw [hEq]
    _ = l := by rw [← hσl, inv_smul_smul]

end M24G

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem mem_G2_of_mem_normalizer (hLU : Stmt5_LineU) {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) (ρ : ResM24 c) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    (hyx : y ≠ c.x0) {g : G} (hg : g ∈ c.G3 ⊓ stabilizer G c.x0)
    (hN : g ∈ Subgroup.normalizer
      ((c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y : Subgroup G) : Set G)) :
    g ∈ c.G2 := by
  classical
  have hg1 : g ∈ c.G1 := by
    rw [← c.stab_x0]
    exact hg.2
  let h : ↥c.G1 := ⟨g, hg1⟩
  have hfix : ∀ m ∈ M24g, m • ρ.l₀ = ρ.l₀ → m • ρ.U₀ = ρ.U₀ →
      m • (ρ.φ h • ρ.l₀) = ρ.φ h • ρ.l₀ := by
    intro m hm hml hmU
    obtain ⟨hm1, hφm⟩ := ρ.exists_φ_eq hm
    have hG2m : (hm1 : G) ∈ c.G2 := (ρ.stab₂ hm1).mpr (by rw [hφm]; exact hml)
    have hG3m : (hm1 : G) ∈ c.G3 := (ρ.stab₃ hm1).mpr (by rw [hφm]; exact hmU)
    have hm1s : (hm1 : G) ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact hm1.2
    have hm1x : (hm1 : G) • c.x0 = c.x0 := MulAction.mem_stabilizer_iff.mp hm1s
    have hmy : (hm1 : G) • y ∈ c.ptsL := smul_mem_objOf_base hG2m hy
    have hmyx : (hm1 : G) • y ≠ c.x0 := by
      intro hcon
      apply hyx
      calc y = (hm1 : G)⁻¹ • ((hm1 : G) • y) := (inv_smul_smul _ y).symm
        _ = (hm1 : G)⁻¹ • c.x0 := by rw [hcon]
        _ = c.x0 := by
          calc (hm1 : G)⁻¹ • c.x0 = (hm1 : G)⁻¹ • ((hm1 : G) • c.x0) := by rw [hm1x]
            _ = c.x0 := inv_smul_smul _ _
    obtain ⟨e, heE, hey⟩ := c.E_transitive hy hmy hyx hmyx
    have he1 : e ∈ c.G1 := c.E_le_G1 heE
    have he3 : e ∈ c.G3 := c.E_le_G3 heE
    have hex : e • c.x0 = c.x0 := by
      have hs : e ∈ stabilizer G c.x0 := by rw [c.stab_x0]; exact he1
      exact MulAction.mem_stabilizer_iff.mp hs
    have hex' : e⁻¹ • c.x0 = c.x0 := by
      calc e⁻¹ • c.x0 = e⁻¹ • (e • c.x0) := by rw [hex]
        _ = c.x0 := inv_smul_smul _ _
    set i : G := e⁻¹ * (hm1 : G) with hi
    have hiG1 : i ∈ c.G1 := by
      rw [hi]
      exact mul_mem (inv_mem he1) hm1.2
    have hiG3 : i ∈ c.G3 := by
      rw [hi]
      exact mul_mem (inv_mem he3) hG3m
    have hix : i • c.x0 = c.x0 := by
      rw [hi, mul_smul, hm1x, hex']
    have hiy : i • y = y := by
      rw [hi, mul_smul, ← hey, inv_smul_smul]
    have hiI : i ∈ c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨hiG3, MulAction.mem_stabilizer_iff.mpr hix⟩,
        MulAction.mem_stabilizer_iff.mpr hiy⟩
    have heKer : ρ.φ ⟨e, he1⟩ = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [ρ.ker_eq]
      exact Subgroup.mem_subgroupOf.mpr heE
    have hφi : ρ.φ ⟨i, hiG1⟩ = m := by
      have hieq : (⟨i, hiG1⟩ : ↥c.G1) = ⟨e, he1⟩⁻¹ * hm1 := by
        ext
        simp [hi]
      rw [hieq, map_mul, map_inv, heKer, hφm, inv_one, one_mul]
    have hi' : g⁻¹ * i * g ∈ c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y := by
      have hginv : g⁻¹ ∈ Subgroup.normalizer
          ((c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ hN
      have h' := (Subgroup.mem_normalizer_iff.mp hginv i).mp hiI
      simpa using h'
    have hi'G1 : g⁻¹ * i * g ∈ c.G1 := by
      rw [← c.stab_x0]
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hi').1).2
    have hi'G2 : g⁻¹ * i * g ∈ c.G2 := by
      refine hLU G z hJ c y hy hyx (Subgroup.mem_inf.mpr ⟨hi'G1, ?_⟩)
      exact (Subgroup.mem_inf.mp hi').2
    have hfixi : ρ.φ ⟨g⁻¹ * i * g, hi'G1⟩ • ρ.l₀ = ρ.l₀ :=
      (ρ.stab₂ ⟨g⁻¹ * i * g, hi'G1⟩).mp hi'G2
    have hconj : ρ.φ ⟨g⁻¹ * i * g, hi'G1⟩ = (ρ.φ h)⁻¹ * m * ρ.φ h := by
      have heq : (⟨g⁻¹ * i * g, hi'G1⟩ : ↥c.G1) = h⁻¹ * ⟨i, hiG1⟩ * h := by
        ext
        simp [h]
      rw [heq, map_mul, map_mul, map_inv, hφi]
    have hmul : m * ρ.φ h = ρ.φ h * ρ.φ ⟨g⁻¹ * i * g, hi'G1⟩ := by
      have hm : m = ρ.φ h * ρ.φ ⟨g⁻¹ * i * g, hi'G1⟩ * (ρ.φ h)⁻¹ := by
        rw [hconj]
        group
      rw [hm]
      group
    calc m • (ρ.φ h • ρ.l₀) = (m * ρ.φ h) • ρ.l₀ := (mul_smul m (ρ.φ h) ρ.l₀).symm
      _ = (ρ.φ h * ρ.φ ⟨g⁻¹ * i * g, hi'G1⟩) • ρ.l₀ := by rw [hmul]
      _ = ρ.φ h • (ρ.φ ⟨g⁻¹ * i * g, hi'G1⟩ • ρ.l₀) := mul_smul _ _ _
      _ = ρ.φ h • ρ.l₀ := by rw [hfixi]
  have hl' : IsTrio (ρ.φ h • ρ.l₀) := (M24G.isTrio_smul_iff (ρ.φ_mem h)).2 ρ.isTrio_l₀
  have hl'U : M24G.TrioIn (ρ.φ h • ρ.l₀) ρ.U₀ := by
    have hTU := (M24G.trioIn_smul_iff (ρ.φ h)).2 ρ.trioIn_l₀_U₀
    rwa [(ρ.stab₃ h).mp hg.1] at hTU
  have hl'eq : ρ.φ h • ρ.l₀ = ρ.l₀ :=
    M24G.eq_of_forall_smul_eq ρ.isTrio_l₀ ρ.isSextet_U₀ ρ.trioIn_l₀_U₀ hl' hl'U hfix
  exact (ρ.stab₂ h).mpr hl'eq

theorem hypV_v4 (hLU : Stmt5_LineU) {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) (ρ : ResM24 c) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    (hyx : y ≠ c.x0) :
    ∀ g ∈ c.G3 ⊓ stabilizer G c.x0,
      g ∈ Subgroup.normalizer
        ((c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y : Subgroup G) : Set G) →
      g ∈ Subgroup.normalizer ((stabilizer G c.x0 ⊓ stabilizer G y : Subgroup G) : Set G) := by
  intro g hg hN
  have hG2 : g ∈ c.G2 := mem_G2_of_mem_normalizer hLU hJ c ρ hy hyx hg hN
  have hK : (c.K : Subgroup G).map (MulAut.conj g).toMonoidHom = c.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.mem_normalizer_K hG2)
  have hI : (c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y : Subgroup G).map
      (MulAut.conj g).toMonoidHom = c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
  have hsup : (c.K ⊔ c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y).map
      (MulAut.conj g).toMonoidHom = c.K ⊔ c.G3 ⊓ stabilizer G c.x0 ⊓ stabilizer G y := by
    rw [Subgroup.map_sup, hK, hI]
  rw [c.inf_stab_eq' hy (hLU G z hJ c y hy hyx)]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hsup

end Loc49

end CFSG.Quasithin.H13.AS91
