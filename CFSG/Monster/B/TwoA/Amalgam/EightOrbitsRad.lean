module

public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsLocal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)

@[expose] def radV
    (v v' : CVert) : Subgroup Shat :=
  (CFSG.pCore 2 ↥(vStab v ⊓ vStab v')).map (vStab v ⊓ vStab v').subtype

theorem radV_le
    (v v' : CVert) : radV v v' ≤ vStab v ⊓ vStab v' := Subgroup.map_subtype_le _

section Edge

variable (s : Shat)

theorem conj_mem_P1_of_mem_pairStab
    {y : Shat}
    (hy : y ∈ vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf a0S) s)) :
    ((s * y * s⁻¹ : Shat) : Dfull) ∈ P1 := by
  have h1 : cvMul cv0 (s * y * s⁻¹) = cv0 := (cvMul_cvMul_eq_iff (s := s) cv0 y).1 hy.1
  have hE : ((s * y * s⁻¹ : Shat) : Dfull) ∈ Eam := (cvMul_cv0_iff _).1 h1
  exact mem_Pc_zero_of_fix_partner (e := ⟨_, hE⟩) ((cvMul_cvMul_eq_iff (s := s) _ y).1 hy.2)

@[expose] def p1ToS (p : P1) : Shat := s⁻¹ * ⟨p, Jhat_le_Shat (P1_le_Jhat p.2)⟩ * s

theorem conj_p1ToS (p : P1) : s * p1ToS s p * s⁻¹ = ⟨p, Jhat_le_Shat (P1_le_Jhat p.2)⟩ := by
  rw [p1ToS]
  group

theorem p1ToS_mem
    (p : P1) :
    p1ToS s p ∈ vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf a0S) s) := by
  have hpE : ((⟨p, Jhat_le_Shat (P1_le_Jhat p.2)⟩ : Shat) : Dfull) ∈ Eam := Pc_le_Eam 0 p.2
  have e := conj_p1ToS s p
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_vStab, cvMul_cvMul_eq_iff, e]
    exact (cvMul_cv0_iff _).2 hpE
  · rw [mem_vStab, cvMul_cvMul_eq_iff, e]
    exact fix_partner_of_mem_Pc_zero (e := ⟨_, hpE⟩) p.2

@[expose] def pairToP1 :
    ↥(vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf a0S) s)) ≃* P1 where
  toFun y := ⟨((s * y * s⁻¹ : Shat) : Dfull), conj_mem_P1_of_mem_pairStab s y.2⟩
  invFun p := ⟨p1ToS s p, p1ToS_mem s p⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    show ((s⁻¹ * (s * (y : Shat) * s⁻¹) * s : Shat) : Dfull) = ((y : Shat) : Dfull)
    congr 1
    group
  right_inv p := by
    apply Subtype.ext
    show ((s * (s⁻¹ * ⟨p, Jhat_le_Shat (P1_le_Jhat p.2)⟩ * s) * s⁻¹ : Shat) : Dfull) = p
    rw [show s * (s⁻¹ * ⟨(p : Dfull), Jhat_le_Shat (P1_le_Jhat p.2)⟩ * s) * s⁻¹ =
      ⟨(p : Dfull), Jhat_le_Shat (P1_le_Jhat p.2)⟩ by group]
  map_mul' y z := by
    apply Subtype.ext
    show ((s * ((y : Shat) * z) * s⁻¹ : Shat) : Dfull) =
      ((s * y * s⁻¹ : Shat) : Dfull) * ((s * z * s⁻¹ : Shat) : Dfull)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem coe_pairToP1
    (y : ↥(vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf a0S) s))) :
    ((pairToP1 s y : P1) : Dfull) = ((s * y * s⁻¹ : Shat) : Dfull) := rfl

theorem mem_radV_iff
    (y : Shat) :
    y ∈ radV (cvMul cv0 s) (cvMul (cvOf a0S) s) ↔
      y ∈ vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf a0S) s) ∧
        ((s * y * s⁻¹ : Shat) : Dfull) ∈ N1 := by
  have hcore := CFSG.pCore_map_iso 2 (pairToP1 s)
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    have h1 : pairToP1 s z ∈ CFSG.pCore 2 P1 := by
      rw [← hcore]
      exact ⟨z, hz, rfl⟩
    rw [← pCore_P1]
    exact ⟨_, h1, rfl⟩
  · rintro ⟨hy, hN⟩
    rw [← pCore_P1] at hN
    obtain ⟨p, hp, hpy⟩ := hN
    rw [← hcore] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    refine ⟨z, hz, ?_⟩
    have h2 : ((pairToP1 s z : P1) : Dfull) = ((pairToP1 s ⟨y, hy⟩ : P1) : Dfull) :=
      (congrArg Subtype.val hzp).trans hpy
    have h3 := (pairToP1 s).injective (Subtype.ext h2)
    exact congrArg Subtype.val h3

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)

include hadj hfeq hfB in
theorem mem_radStar_iff_rhoV
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) (γ : GStar) :
    γ ∈ radStar ↔ ∃ (y : Shat) (hy : y ∈ radV (cvMul cv0 s) (cvMul (cvOf a0S) s)),
      rhoV θ (rfl : cvMul cv0 s = cvMul cv0 s)
        ⟨y, ((radV_le _ _).trans inf_le_left) hy⟩ = γ := by
  constructor
  · intro hγ
    rw [← map_cNE_eq_radStar hk0 hk hadj hfeq hfB] at hγ
    obtain ⟨n, hn, rfl⟩ := hγ
    set e : Eam := ⟨n, Pc_le_Eam 0 n.2⟩
    have hnN : (n : Dfull) ∈ N1 := cNE_le_N1 hn
    refine ⟨s⁻¹ * toS e * s, (mem_radV_iff s _).2 ⟨p1ToS_mem s n, ?_⟩, ?_⟩
    · rw [show s * (s⁻¹ * toS e * s) * s⁻¹ = toS e by group, coe_toS]
      exact hnN
    · exact rhoV_conj_toS θ rfl n
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy2, hN⟩ := (mem_radV_iff s y).1 hy
    have h := rho1_mem_radStar hadj hfeq hfB (n := ⟨_, conj_mem_P1_of_mem_pairStab s hy2⟩) hN
    rw [rhoV_apply]
    exact h

end Edge

section Pair

variable (s : Shat) {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
  (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))

include hk0 hk in
theorem pairStab_le :
    vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf (jhatS k)) s) ≤
      vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf a0S) s) := by
  intro y hy
  obtain ⟨hyv, hyw⟩ := Subgroup.mem_inf.1 hy
  have hQ := (native_type_four_pair_stabilizer_parabolic_projection k hk0 hk).1
  have h1 : cvMul cv0 (s * y * s⁻¹) = cv0 := (cvMul_cvMul_eq_iff (s := s) cv0 y).1 hyv
  have h2 := (cvMul_cvMul_eq_iff (s := s) (cvOf (jhatS k)) y).1 hyw
  have hq := (hQ (s * y * s⁻¹)).1 ⟨h1, h2⟩
  have hE : ((s * y * s⁻¹ : Shat) : Dfull) ∈ Eam := (cvMul_cv0_iff _).1 h1
  refine Subgroup.mem_inf.2 ⟨hyv, ?_⟩
  rw [mem_vStab, cvMul_cvMul_eq_iff]
  exact fix_partner_of_mem_Pc_zero (e := ⟨_, hE⟩) (Q4_le_P1 hq)

include hk0 hk in
theorem conj_mem_Q4
    {y : Shat} (hy : y ∈ vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf (jhatS k)) s)) :
    ((s * y * s⁻¹ : Shat) : Dfull) ∈ Q4 k := by
  have hQ := (native_type_four_pair_stabilizer_parabolic_projection k hk0 hk).1
  exact (hQ (s * y * s⁻¹)).1 ⟨(cvMul_cvMul_eq_iff (s := s) cv0 y).1 hy.1,
    (cvMul_cvMul_eq_iff (s := s) (cvOf (jhatS k)) y).1 hy.2⟩

@[expose] def pairProj :
    ↥(vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf (jhatS k)) s)) →* Unitary.Usig :=
  p1Proj.comp ((pairToP1 s).toMonoidHom.comp (Subgroup.inclusion (pairStab_le s hk0 hk)))

theorem pairProj_apply
    (y : ↥(vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf (jhatS k)) s))) :
    pairProj s hk0 hk y =
      p1Proj ⟨((s * y * s⁻¹ : Shat) : Dfull),
        conj_mem_P1_of_mem_pairStab s (pairStab_le s hk0 hk y.2)⟩ := rfl

include hk0 hk in
theorem range_pairProj
    (hτ : psiW (labE k) = Unitary.tauW) :
    (pairProj s hk0 hk).range = Unitary.Atau := by
  have hmap := map_Q4 hk0 hk
  rw [hτ] at hmap
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    have hq := conj_mem_Q4 s hk0 hk y.2
    have h : jhatToKv0 ⟨_, P1_le_Jhat (Q4_le_P1 hq)⟩ ∈ Unitary.Usig ⊓ wStab Unitary.tauW := by
      rw [← hmap]
      exact ⟨⟨_, P1_le_Jhat (Q4_le_P1 hq)⟩, hq, rfl⟩
    exact h.2
  · intro ha
    have h : (a : Kstab v0) ∈ ((Q4 k).subgroupOf Jhat).map jhatToKv0 := by
      rw [hmap]
      exact ⟨a.2, ha⟩
    obtain ⟨g, hg, hga⟩ := h
    have hgQ : (g : Dfull) ∈ Q4 k := hg
    have hgP : (g : Dfull) ∈ P1 := Q4_le_P1 hgQ
    have e := conj_p1ToS s ⟨g, hgP⟩
    have hQ := (native_type_four_pair_stabilizer_parabolic_projection k hk0 hk).1
    have hfix := (hQ (s * p1ToS s ⟨g, hgP⟩ * s⁻¹)).2 (by rw [e]; exact hgQ)
    have hy : p1ToS s ⟨g, hgP⟩ ∈ vStab (cvMul cv0 s) ⊓ vStab (cvMul (cvOf (jhatS k)) s) :=
      ⟨(cvMul_cvMul_eq_iff (s := s) cv0 _).2 hfix.1, (cvMul_cvMul_eq_iff (s := s) _ _).2 hfix.2⟩
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    rw [pairProj_apply, coe_p1Proj, ← hga]
    congr 1
    apply Subtype.ext
    show ((s * p1ToS s ⟨g, hgP⟩ * s⁻¹ : Shat) : Dfull) = g
    rw [e]

end Pair

end CFSG.Monster.B.TwoA.Amalgam
