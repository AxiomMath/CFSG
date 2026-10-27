module

public import CFSG.RankThree.GF2n.Stroth80.Sec108PhiCard
public import CFSG.RankThree.GF2n.Stroth80.Sec108PhiLB
public import CFSG.RankThree.GF2n.Stroth80.Sec108FixBeta
public import CFSG.LinearAlgebra.SqrtDiag
public import CFSG.LinearAlgebra.AlternatingSL
public import CFSG.ClassicalGroups.SpecialLinear.LineStabilizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private noncomputable def sqrtDiagAddHom (K : Type) [Field K] [CharP K 2] [PerfectRing K 2] :
    Matrix (Fin 3) (Fin 3) K →+ (Fin 3 → K) where
  toFun := CFSG.LinearAlgebra.sqrtDiag
  map_zero' := (CFSG.LinearAlgebra.sqrtDiag_eq_zero_iff 0).mpr (by intro i; rfl)
  map_add' := CFSG.LinearAlgebra.sqrtDiag_add

private noncomputable def deltaVec (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : AddSubgroup (Fin 3 → AM.K) :=
  (Subgroup.toAddSubgroup' (D.phiHom AM).range).map (sqrtDiagAddHom AM.K)

private noncomputable def deltaLB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : AddSubgroup (Fin 3 → AM.K) :=
  (Subgroup.toAddSubgroup' (((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM))).map
    (sqrtDiagAddHom AM.K)

private theorem card_toAddSubgroup' {A : Type} [AddGroup A]
    (S : Subgroup (Multiplicative A)) :
    Nat.card ↥(Subgroup.toAddSubgroup' S) = Nat.card ↥S := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨Multiplicative.ofAdd x.1,
        (Subgroup.mem_toAddSubgroup' S x.1).mp x.2⟩
      invFun := fun y => ⟨(y : Multiplicative A).toAdd,
        (Subgroup.mem_toAddSubgroup' S (y : Multiplicative A).toAdd).mpr (by simpa using y.2)⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (by simp) }

private theorem mem_deltaVec_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {v : Fin 3 → AM.K} :
    v ∈ deltaVec D AM ↔ ∃ n : ↥(hc.CN t),
      CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩) = v := by
  rw [deltaVec, AddSubgroup.mem_map]
  constructor
  · rintro ⟨S, hS, hSv⟩
    rw [Subgroup.mem_toAddSubgroup'] at hS
    obtain ⟨n, hn⟩ := hS
    refine ⟨n, ?_⟩
    have hphi : D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ = S := by
      rw [← D.phiHom_apply AM n, hn, toAdd_ofAdd]
    change CFSG.LinearAlgebra.sqrtDiag S = v at hSv
    rw [hphi, hSv]
  · rintro ⟨n, rfl⟩
    refine ⟨D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_toAddSubgroup']
    exact ⟨n, by rw [← D.phiHom_apply AM n, ofAdd_toAdd]⟩

private theorem mem_range_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {S : Matrix (Fin 3) (Fin 3) AM.K} :
    S ∈ Subgroup.toAddSubgroup' (D.phiHom AM).range ↔
      ∃ n : ↥(hc.CN t), D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ = S := by
  rw [Subgroup.mem_toAddSubgroup']
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← D.phiHom_apply AM n, hn, toAdd_ofAdd]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [← D.phiHom_apply AM n, ofAdd_toAdd]⟩

private theorem mem_deltaLB_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {v : Fin 3 → AM.K} :
    v ∈ deltaLB D AM ↔ ∃ l : ↥(hc.CN t), (l : G) ∈ LB M Q B ∧
      CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨l, D.CN_le_H0 l.2⟩) = v := by
  rw [deltaLB, AddSubgroup.mem_map]
  constructor
  · rintro ⟨S, hS, hSv⟩
    rw [Subgroup.mem_toAddSubgroup'] at hS
    rw [Subgroup.mem_map] at hS
    obtain ⟨l, hl, hSl⟩ := hS
    refine ⟨l, hl, ?_⟩
    have hphi : D.phiMat AM ⟨l, D.CN_le_H0 l.2⟩ = S := by
      rw [← D.phiHom_apply AM l, hSl, toAdd_ofAdd]
    change CFSG.LinearAlgebra.sqrtDiag S = v at hSv
    rw [hphi, hSv]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨D.phiMat AM ⟨l, D.CN_le_H0 l.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
    exact ⟨l, hl, by rw [← D.phiHom_apply AM l, ofAdd_toAdd]⟩

private theorem exists_conj_phiMat (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (A : Matrix.SpecialLinearGroup (Fin 3) AM.K)
    {n : G} (hn : n ∈ hc.CN t) :
    ∃ (n' : G) (hn' : n' ∈ hc.CN t), (A : Matrix (Fin 3) (Fin 3) AM.K) *
        D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ * (A : Matrix (Fin 3) (Fin 3) AM.K)ᵀ =
      D.phiMat AM ⟨n', D.CN_le_H0 hn'⟩ := by
  obtain ⟨r, hrRC, hrH, hrA⟩ := D.bV_spec AM A
  have hrC : r ∈ Subgroup.centralizer ({t} : Set G) := hrRC.2
  have hrR : r ∈ Rt M (LB M Q B) t := hrRC.1
  refine ⟨r * n * r⁻¹, D.conj_mem_CN hrR hn, ?_⟩
  have hcommut : ⁅r, t⁆ ∈ Q := by
    have h1 : ⁅r, t⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hrC t (Set.mem_singleton t)).symm
    rw [h1]
    exact Q.one_mem
  have h := D.phiMat_conj AM (m := ⟨n, D.CN_le_H0 hn⟩) (r := ⟨r, hrH⟩)
    (fun e => Sec108Data.phi_comm_of_comm_mem AM hcommut e) hrA
    (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (D.comm_t_of_mem_CN AM hn)
  rw [← h]
  rfl

private theorem deltaVec_invariant (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (A : Matrix.SpecialLinearGroup (Fin 3) AM.K)
    {v : Fin 3 → AM.K} (hv : v ∈ deltaVec D AM) :
    (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ v ∈ deltaVec D AM := by
  rw [mem_deltaVec_iff] at hv ⊢
  obtain ⟨n, rfl⟩ := hv
  obtain ⟨n', hn', hconj⟩ := exists_conj_phiMat D AM A n.2
  have hsym : (D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩)ᵀ = D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ :=
    D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM n.2 he)
      (D.comm_t_of_mem_CN AM n.2)
  rw [← CFSG.LinearAlgebra.sqrtDiag_mul_mul_transpose hsym (A : Matrix (Fin 3) (Fin 3) AM.K)]
  rw [hconj]
  exact ⟨⟨n', hn'⟩, rfl⟩

private theorem range_invariant (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (A : Matrix.SpecialLinearGroup (Fin 3) AM.K)
    {S : Matrix (Fin 3) (Fin 3) AM.K}
    (hS : S ∈ Subgroup.toAddSubgroup' (D.phiHom AM).range) :
    (A : Matrix (Fin 3) (Fin 3) AM.K) * S * (A : Matrix (Fin 3) (Fin 3) AM.K)ᵀ ∈
      Subgroup.toAddSubgroup' (D.phiHom AM).range := by
  rw [mem_range_iff] at hS ⊢
  obtain ⟨n, rfl⟩ := hS
  obtain ⟨n', hn', hconj⟩ := exists_conj_phiMat D AM A n.2
  rw [hconj]
  exact ⟨⟨n', hn'⟩, rfl⟩

private theorem sqrtDiag_injOn_range (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (hΔ : deltaVec D AM = ⊤)
    {S T : Matrix (Fin 3) (Fin 3) AM.K}
    (hS : S ∈ Subgroup.toAddSubgroup' (D.phiHom AM).range)
    (hT : T ∈ Subgroup.toAddSubgroup' (D.phiHom AM).range)
    (h : CFSG.LinearAlgebra.sqrtDiag S = CFSG.LinearAlgebra.sqrtDiag T) : S = T := by
  let Mset := Subgroup.toAddSubgroup' (D.phiHom AM).range
  let f : ↥Mset →+ (Fin 3 → AM.K) :=
    { toFun := fun x => CFSG.LinearAlgebra.sqrtDiag x.1
      map_zero' := (CFSG.LinearAlgebra.sqrtDiag_eq_zero_iff 0).mpr (by intro i; rfl)
      map_add' := fun x y => CFSG.LinearAlgebra.sqrtDiag_add x.1 y.1 }
  have hfr : f.range = deltaVec D AM := by
    ext v
    rw [AddMonoidHom.mem_range, deltaVec, AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard_range : Nat.card ↥f.range = Nat.card AM.K ^ 3 := by
    rw [hfr, hΔ, AddSubgroup.card_top, Nat.card_fun, Nat.card_fin]
  have hMcard : Nat.card ↥Mset ≤ Nat.card AM.K ^ 3 := by
    change Nat.card ↥(Subgroup.toAddSubgroup' (D.phiHom AM).range) ≤ Nat.card AM.K ^ 3
    rw [card_toAddSubgroup' (D.phiHom AM).range, AM.glob.card]
    exact D.card_range_phiHom_le AM
  have hcard_ker : Nat.card ↥f.ker ≤ 1 := by
    have hkr := AddSubgroup.card_ker_mul_card_range f
    rw [hcard_range] at hkr
    have hpos : 0 < Nat.card AM.K ^ 3 := pow_pos Nat.card_pos 3
    have hle : Nat.card ↥f.ker * Nat.card AM.K ^ 3 ≤ 1 * Nat.card AM.K ^ 3 := by
      rw [one_mul, hkr]
      exact hMcard
    exact Nat.le_of_mul_le_mul_right hle hpos
  have hker_bot : f.ker = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    have hcard1 : Nat.card ↥f.ker = 1 := le_antisymm hcard_ker Nat.card_pos
    have hsub : Subsingleton ↥f.ker := (Nat.card_eq_one_iff_unique.mp hcard1).1
    have h1 : (⟨x, hx⟩ : ↥f.ker) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  have hmem : S - T ∈ Mset := Mset.sub_mem hS hT
  have hzero : f ⟨S - T, hmem⟩ = 0 := by
    have hsub : (⟨S - T, hmem⟩ : ↥Mset) = ⟨S, hS⟩ - ⟨T, hT⟩ := Subtype.ext rfl
    rw [hsub, map_sub,
      show f ⟨S, hS⟩ = CFSG.LinearAlgebra.sqrtDiag S from rfl,
      show f ⟨T, hT⟩ = CFSG.LinearAlgebra.sqrtDiag T from rfl, h, sub_self]
  have hbot : (⟨S - T, hmem⟩ : ↥Mset) ∈ f.ker := hzero
  rw [hker_bot, AddSubgroup.mem_bot] at hbot
  exact sub_eq_zero.mp (congrArg Subtype.val hbot)

private theorem deltaLB_invariant (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM)
    (A : Matrix.SpecialLinearGroup (Fin 3) AM.K)
    (hAβ : (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ β = β)
    {s : Fin 3 → AM.K} (hs : s ∈ deltaLB D AM) :
    (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ s ∈ deltaLB D AM := by
  rw [mem_deltaLB_iff] at hs ⊢
  obtain ⟨l, hl, rfl⟩ := hs
  have hsym : (D.phiMat AM ⟨l, D.CN_le_H0 l.2⟩)ᵀ = D.phiMat AM ⟨l, D.CN_le_H0 l.2⟩ :=
    D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM l.2 he) (D.comm_t_of_mem_CN AM l.2)
  obtain ⟨r, hrRC, hrH, hrN, hrA⟩ := D.exists_fix_beta AM hβ hβB A hAβ
  have hrC : r ∈ Subgroup.centralizer ({t} : Set G) := hrRC.2
  have hrR : r ∈ Rt M (LB M Q B) t := hrRC.1
  have hcommut : ⁅r, t⁆ ∈ Q := by
    have h1 : ⁅r, t⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hrC t (Set.mem_singleton t)).symm
    rw [h1]
    exact Q.one_mem
  have hconj := D.phiMat_conj AM (m := ⟨l, D.CN_le_H0 l.2⟩) (r := ⟨r, hrH⟩)
    (fun e => Sec108Data.phi_comm_of_comm_mem AM hcommut e) hrA
    (fun e he => D.fix_Vsp_of_mem_CN AM l.2 he) (D.comm_t_of_mem_CN AM l.2)
  have hn'LB : r * (l : G) * r⁻¹ ∈ LB M Q B :=
    (Subgroup.mem_normalizer_iff.mp hrN (l : G)).mp hl
  have hn'CN : r * (l : G) * r⁻¹ ∈ hc.CN t := D.conj_mem_CN hrR l.2
  rw [← CFSG.LinearAlgebra.sqrtDiag_mul_mul_transpose hsym (A : Matrix (Fin 3) (Fin 3) AM.K)]
  rw [← hconj]
  exact ⟨⟨r * (l : G) * r⁻¹, hn'CN⟩, hn'LB, rfl⟩

private theorem card_deltaLB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (hΔ : deltaVec D AM = ⊤) :
    Nat.card (deltaLB D AM) = Nat.card Z ^ 2 := by
  classical
  let H := ((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)
  have hHle : H ≤ (D.phiHom AM).range := Subgroup.map_le_range _ _
  let e : ↥H → ↥(deltaLB D AM) := fun S =>
    ⟨CFSG.LinearAlgebra.sqrtDiag (S : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)).toAdd,
      AddSubgroup.mem_map_of_mem _
        ((Subgroup.mem_toAddSubgroup' H
          (S : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)).toAdd).mpr
          (by simpa using S.2))⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro S T hST
      have hmat : (S : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)).toAdd =
          (T : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)).toAdd := by
        apply sqrtDiag_injOn_range D AM hΔ
          ((Subgroup.mem_toAddSubgroup' (D.phiHom AM).range
            (S : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)).toAdd).mpr
            (by simpa using hHle S.2))
          ((Subgroup.mem_toAddSubgroup' (D.phiHom AM).range
            (T : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)).toAdd).mpr
            (by simpa using hHle T.2))
        exact congrArg Subtype.val hST
      apply Subtype.ext
      exact Multiplicative.ext hmat
    · intro v
      obtain ⟨l, hl, hvl⟩ := (mem_deltaLB_iff D AM).mp v.2
      refine ⟨⟨D.phiHom AM l, Subgroup.mem_map_of_mem _ hl⟩, ?_⟩
      apply Subtype.ext
      dsimp only [e]
      rw [D.phiHom_apply AM l]
      exact hvl
  calc Nat.card (deltaLB D AM) = Nat.card ↥H :=
        (Nat.card_congr (Equiv.ofBijective e hbij)).symm
    _ = Nat.card Z ^ 2 := D.card_map_phiHom_LB AM

private theorem deltaVec_ne_top (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : deltaVec D AM ≠ ⊤ := by
  intro htop
  obtain ⟨β, hβ, hβB⟩ := D.exists_coord_Bsp AM
  have hcard := card_deltaLB D AM htop
  have hne := CFSG.ClassicalGroups.SpecialLinear.card_ne_pow_of_fixer_invariant
    (K := AM.K) (m := 3) (k := 2) (by norm_num) (by norm_num) (by norm_num) hβ
    (deltaLB D AM) (fun g hg hgβ s hs => by
      let A : Matrix.SpecialLinearGroup (Fin 3) AM.K :=
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 AM.K).symm ⟨g, hg⟩
      have hAcoe : (A : Matrix (Fin 3) (Fin 3) AM.K) =
          (g : Matrix (Fin 3) (Fin 3) AM.K) := by
        have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 AM.K A
        rw [show CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 AM.K A =
          ⟨g, hg⟩ from MulEquiv.apply_symm_apply _ _] at h
        exact h.symm
      have hAβ : (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ β = β := by
        rw [hAcoe]
        exact hgβ
      have hres := deltaLB_invariant D AM hβ hβB A hAβ hs
      rwa [hAcoe] at hres)
  exact hne (by rw [hcard, AM.glob.card])

theorem Sec108Data.sqrtDiag_phiMat_eq_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n : G} (hn : n ∈ hc.CN t) :
    CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) = 0 := by
  classical
  have hbot : deltaVec D AM = ⊥ :=
    (CFSG.LinearAlgebra.eq_bot_or_eq_top_of_specialLinear_invariant (deltaVec D AM)
      (fun A v hv => deltaVec_invariant D AM A hv)).resolve_right (deltaVec_ne_top D AM)
  have hmem : CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩) ∈ deltaVec D AM :=
    (mem_deltaVec_iff D AM).mpr ⟨⟨n, hn⟩, rfl⟩
  rw [hbot, AddSubgroup.mem_bot] at hmem
  exact hmem

theorem Sec108Data.phiMat_diag (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {n : G} (hn : n ∈ hc.CN t) (i : Fin 3) : D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ i i = 0 := by
  exact (CFSG.LinearAlgebra.sqrtDiag_eq_zero_iff _).mp (D.sqrtDiag_phiMat_eq_zero AM hn) i

theorem Sec108Data.exists_phiMat_eq (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (A : Matrix (Fin 3) (Fin 3) AM.K)
    (hA : Aᵀ = A) (hd : ∀ i, A i i = 0) :
    ∃ n, ∃ hn : n ∈ hc.CN t, D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ = A := by
  classical
  let X := Subgroup.toAddSubgroup' (D.phiHom AM).range
  have hHle : ((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM) ≤
      (D.phiHom AM).range := Subgroup.map_le_range _ _
  have hcardH : Nat.card ↥(((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)) =
      Nat.card Z ^ 2 := D.card_map_phiHom_LB AM
  have hcardle : Nat.card Z ^ 2 ≤ Nat.card ↥(D.phiHom AM).range := by
    rw [← hcardH]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hHle)
      (Subgroup.inclusion_injective hHle)
  have hXcard : 1 < Nat.card ↥X := by
    change 1 < Nat.card ↥(Subgroup.toAddSubgroup' (D.phiHom AM).range)
    rw [card_toAddSubgroup' (D.phiHom AM).range]
    refine lt_of_lt_of_le ?_ hcardle
    calc 1 < 4 ^ 2 := by norm_num
      _ ≤ Nat.card Z ^ 2 := Nat.pow_le_pow_left hc.hyp.q4 2
  have hne_bot : X ≠ ⊥ := by
    intro hbot
    rw [hbot] at hXcard
    rw [AddSubgroup.card_bot] at hXcard
    omega
  obtain ⟨S₀, hS₀, hS₀ne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne_bot)
  obtain ⟨n₀, hn₀⟩ := (mem_range_iff D AM).mp hS₀
  have hS₀t : S₀ᵀ = -S₀ := by
    rw [← hn₀, CharTwo.neg_eq]
    exact D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM n₀.2 he)
      (D.comm_t_of_mem_CN AM n₀.2)
  have hS₀d : ∀ i, S₀ i i = 0 := by
    intro i
    rw [← hn₀]
    exact D.phiMat_diag AM n₀.2 i
  have hS₀ne0 : S₀ ≠ 0 := by
    intro h0
    apply hS₀ne
    rw [h0]
    exact (⊥ : AddSubgroup (Matrix (Fin 3) (Fin 3) AM.K)).zero_mem
  have hAX : A ∈ X :=
    CFSG.LinearAlgebra.mem_of_specialLinear_invariant X
      (fun B S hS => range_invariant D AM B hS) hS₀ hS₀t hS₀d hS₀ne0
      (by rw [CharTwo.neg_eq]; exact hA) hd
  obtain ⟨n, hn⟩ := (mem_range_iff D AM).mp hAX
  exact ⟨n, n.2, hn⟩

private theorem card_range_phiHom (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Nat.card (D.phiHom AM).range = Nat.card AM.K ^ 3 := by
  refine le_antisymm ?_ ?_
  · rw [AM.glob.card]
    exact D.card_range_phiHom_le AM
  · let f : (Fin 3 → AM.K) → ↥(D.phiHom AM).range := fun a =>
      ⟨Multiplicative.ofAdd (CFSG.LinearAlgebra.crossMatrix a), by
        have hsym : (CFSG.LinearAlgebra.crossMatrix a)ᵀ =
            CFSG.LinearAlgebra.crossMatrix a := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [CFSG.LinearAlgebra.crossMatrix, CharTwo.neg_eq]
        have hdiag : ∀ i, CFSG.LinearAlgebra.crossMatrix a i i = 0 := by
          intro i
          fin_cases i <;> simp [CFSG.LinearAlgebra.crossMatrix]
        obtain ⟨n, hn, hA⟩ := D.exists_phiMat_eq AM (CFSG.LinearAlgebra.crossMatrix a) hsym hdiag
        refine ⟨⟨n, hn⟩, ?_⟩
        rw [← hA, ← D.phiHom_apply AM ⟨n, hn⟩]
        exact ofAdd_toAdd _⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h : CFSG.LinearAlgebra.crossMatrix a = CFSG.LinearAlgebra.crossMatrix b := by
        have h' := congrArg (fun x : ↥(D.phiHom AM).range =>
          (x : Multiplicative (Matrix (Fin 3) (Fin 3) AM.K)).toAdd) hab
        simpa [f] using h'
      have h0 : a 0 = b 0 := by
        have h' := congrFun (congrFun h 1) 2
        simp [CFSG.LinearAlgebra.crossMatrix] at h'
        exact h'
      have h1 : a 1 = b 1 := by
        have h' := congrFun (congrFun h 0) 2
        simpa [CFSG.LinearAlgebra.crossMatrix] using h'
      have h2 : a 2 = b 2 := by
        have h' := congrFun (congrFun h 1) 0
        simpa [CFSG.LinearAlgebra.crossMatrix] using h'
      ext i
      fin_cases i <;> assumption
    have hle := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_fun] using hle

private theorem root_le_CN (D : Sec108Data hc t Y) : Y ≤ hc.CN t := by
  have hYQB : Y ≤ QB Y := IsZConjugate.le_QB_self hc.hyp D.sit.conj
  have hYM : Y ≤ M := ((smith_1_12 D.sit).1).trans inf_le_left
  intro y hy
  rw [D.CN_eq]
  exact Subgroup.mem_sup_right ⟨hYQB hy, hYM hy⟩

private theorem root_le_normalizer_Q (D : Sec108Data hc t Y) :
    Y ≤ Subgroup.normalizer (Q : Set G) :=
  fun y hy => hc.hyp.Q_normal.2 (((smith_1_12 D.sit).1).trans inf_le_left hy)

private theorem card_root_sup_Q (D : Sec108Data hc t Y) :
    Nat.card ↥(Y ⊔ Q) = Nat.card Z * Nat.card Q := by
  have h := card_sup_mul_card_inf_of_normalizer (A := Q) (C := Y) (root_le_normalizer_Q D)
  rw [inf_comm, (smith_1_12 D.sit).2, Subgroup.card_bot, mul_one] at h
  obtain ⟨g, hg⟩ := D.sit.conj
  have hYcard : Nat.card ↥Y = Nat.card Z := by rw [hg, card_conjSubgroup]
  calc Nat.card ↥(Y ⊔ Q) = Nat.card ↥(Q ⊔ Y) := by rw [sup_comm]
    _ = Nat.card ↥Q * Nat.card ↥Y := h
    _ = Nat.card Z * Nat.card Q := by rw [hYcard, mul_comm]

private theorem phiHom_eq_one_of_mem_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {y : G} (hy : y ∈ Y)
    (hyCN : y ∈ hc.CN t) : D.phiHom AM ⟨y, hyCN⟩ = 1 := by
  have hyfix : ∀ u ∈ (D.nu AM).range, AM.φ ⟨y, D.CN_le_H0 hyCN⟩ u = u := by
    intro u hu
    simpa using D.root_fix_range_nu AM hy hu
  have hyzero : D.phiMat AM ⟨y, D.CN_le_H0 hyCN⟩ = 0 :=
    (D.phiMat_eq_zero_iff AM (m := ⟨y, D.CN_le_H0 hyCN⟩)
      (fun e he => D.fix_Vsp_of_mem_CN AM hyCN he)
      (D.comm_t_of_mem_CN AM hyCN)).mpr hyfix
  rw [← ofAdd_toAdd (D.phiHom AM ⟨y, hyCN⟩), D.phiHom_apply AM ⟨y, hyCN⟩, hyzero]
  rfl

private theorem phiHom_eq_one_of_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {q : G} (hq : q ∈ Q)
    (hqCN : q ∈ hc.CN t) : D.phiHom AM ⟨q, hqCN⟩ = 1 := by
  have hqphi : AM.φ ⟨q, hc.Q_le_H0' hq⟩ = 1 := (AM.φ_ker _).mpr hq
  have hqfix : ∀ u ∈ (D.nu AM).range, AM.φ ⟨q, D.CN_le_H0 hqCN⟩ u = u := by
    intro u hu
    simpa using congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f u) hqphi
  have hqzero : D.phiMat AM ⟨q, D.CN_le_H0 hqCN⟩ = 0 :=
    (D.phiMat_eq_zero_iff AM (m := ⟨q, D.CN_le_H0 hqCN⟩)
      (fun e he => D.fix_Vsp_of_mem_CN AM hqCN he)
      (D.comm_t_of_mem_CN AM hqCN)).mpr hqfix
  rw [← ofAdd_toAdd (D.phiHom AM ⟨q, hqCN⟩), D.phiHom_apply AM ⟨q, hqCN⟩, hqzero]
  rfl

private theorem card_ker_phiHom (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Nat.card ↥(D.phiHom AM).ker = Nat.card Z * Nat.card Q := by
  haveI := hc.normal_Q_in_M
  have hCN : Nat.card ↥(hc.CN t) = Nat.card (bar M Q (hc.CN t)) * Nat.card Q :=
    (bar_card_mul_card_of_le (Ctx.Q_le_CN hc D.good.1.mem_LB)
      (fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1)).symm
  have hkr := Subgroup.card_ker_mul_card_range (D.phiHom AM)
  rw [hCN, D.card_bar_CN, card_range_phiHom D AM, AM.glob.card] at hkr
  have hEq : Nat.card ↥(D.phiHom AM).ker * Nat.card Z ^ 3 =
      (Nat.card Z * Nat.card Q) * Nat.card Z ^ 3 := by
    rw [hkr]
    ring
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 3) hEq

private theorem card_root_subgroup (D : Sec108Data hc t Y) :
    Nat.card ↥((Y ⊔ Q).subgroupOf (hc.CN t)) = Nat.card Z * Nat.card Q := by
  have hYQle : Y ⊔ Q ≤ hc.CN t :=
    sup_le (root_le_CN D) (hc.Q_le_CN' D.good.1.mem_LB)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYQle).toEquiv]
  exact card_root_sup_Q D

private theorem root_subgroup_le_ker (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ((Y ⊔ Q).subgroupOf (hc.CN t)) ≤ (D.phiHom AM).ker := by
  intro x hx
  have hxYQ : (x : G) ∈ Y ⊔ Q := Subgroup.mem_subgroupOf.mp hx
  have hxYQ' : (x : G) ∈ (((Y ⊔ Q : Subgroup G)) : Set G) := hxYQ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Y Q (root_le_normalizer_Q D)] at hxYQ'
  obtain ⟨y, hy, q, hq, hyq⟩ := hxYQ'
  have hyCN : y ∈ hc.CN t := root_le_CN D hy
  have hqCN : q ∈ hc.CN t := hc.Q_le_CN' D.good.1.mem_LB hq
  have hxeq : x = ⟨y, hyCN⟩ * ⟨q, hqCN⟩ := by
    ext
    show (x : G) = y * q
    exact hyq.symm
  show D.phiHom AM x = 1
  rw [hxeq, map_mul, phiHom_eq_one_of_mem_root D AM hy hyCN,
    phiHom_eq_one_of_mem_Q D AM hq hqCN, mul_one]

private theorem ker_phiHom_eq_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ((Y ⊔ Q).subgroupOf (hc.CN t)) = (D.phiHom AM).ker := by
  refine Subgroup.eq_of_le_of_card_ge (root_subgroup_le_ker D AM) ?_
  rw [card_ker_phiHom D AM, card_root_subgroup D]

private theorem phiMat_eq_zero_of_root_mul (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n y : G} (hn : n ∈ hc.CN t)
    (hy : y ∈ Y) (hq : y⁻¹ * n ∈ Q) :
    D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ = 0 := by
  have hyCN : y ∈ hc.CN t := root_le_CN D hy
  have hqCN : y⁻¹ * n ∈ hc.CN t := hc.Q_le_CN' D.good.1.mem_LB hq
  have hnEq : (⟨n, hn⟩ : ↥(hc.CN t)) = ⟨y, hyCN⟩ * ⟨y⁻¹ * n, hqCN⟩ := by
    ext
    show n = y * (y⁻¹ * n)
    group
  have hphi : D.phiHom AM ⟨n, hn⟩ = 1 := by
    rw [hnEq, map_mul, phiHom_eq_one_of_mem_root D AM hy hyCN,
      phiHom_eq_one_of_mem_Q D AM hq hqCN, mul_one]
  have hzero := congrArg Multiplicative.toAdd hphi
  simpa [D.phiHom_apply AM ⟨n, hn⟩] using hzero

theorem Sec108Data.phiMat_eq_zero_iff_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n : G} (hn : n ∈ hc.CN t) :
    D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ = 0 ↔ ∃ y ∈ Y, y⁻¹ * n ∈ Q := by
  classical
  constructor
  · intro h0
    have hphi : D.phiHom AM ⟨n, hn⟩ = 1 := by
      rw [← ofAdd_toAdd (D.phiHom AM ⟨n, hn⟩), D.phiHom_apply AM ⟨n, hn⟩, h0]
      rfl
    have hmem : (⟨n, hn⟩ : ↥(hc.CN t)) ∈ (D.phiHom AM).ker := hphi
    have hmemH : (⟨n, hn⟩ : ↥(hc.CN t)) ∈ (Y ⊔ Q).subgroupOf (hc.CN t) := by
      rw [ker_phiHom_eq_root D AM]
      exact hmem
    have hYQ : n ∈ Y ⊔ Q := Subgroup.mem_subgroupOf.mp hmemH
    have hYQ' : n ∈ (((Y ⊔ Q : Subgroup G)) : Set G) := hYQ
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Y Q (root_le_normalizer_Q D)] at hYQ'
    obtain ⟨y, hy, q, hq, hyq⟩ := hYQ'
    refine ⟨y, hy, ?_⟩
    rw [← hyq]
    simpa using hq
  · rintro ⟨y, hy, hq⟩
    exact phiMat_eq_zero_of_root_mul D AM hn hy hq

end CFSG.RankThree.GF2n.Stroth80
