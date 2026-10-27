module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocal
public import CFSG.Quasithin.Recognition.Stroth.SubconstNaturalL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.Assembly.RankThreeEvenDefs

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ShultStronglyClosedTI.LinearModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace L2

variable {m : ℕ} (hm : 2 ≤ m)

abbrev L2K (m : ℕ) : Type := GaloisField 2 m
private theorem exists_conj_borel_eq_psl2Borel (hm : 2 ≤ m) :
    ∃ (U B : Subgroup (PSL2MatrixGroup (L2K m))) (hU : Nat.card U = 2 ^ m),
      RankOneData (PSL2MatrixGroup (L2K m)) U B ∧
        ∃ x : PSL2MatrixGroup (L2K m),
          psl2Borel (L2K m) = B.map (MulAut.conj x).toMonoidHom := by
  classical
  have hKcard : Nat.card (L2K m) = 2 ^ m := GaloisField.card 2 m (by omega)
  obtain ⟨U, B, hdata, hUcard⟩ := CFSG.Quasithin.Stroth.rankOneData_psl2 m hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t : ↥(⊤ : Subgroup (PSL2MatrixGroup (L2K m))) ≃* PSL2MatrixGroup (L2K m) := Subgroup.topEquiv
  let U' : Subgroup ↥(⊤ : Subgroup (PSL2MatrixGroup (L2K m))) := U.map t.symm.toMonoidHom
  let B' : Subgroup ↥(⊤ : Subgroup (PSL2MatrixGroup (L2K m))) := B.map t.symm.toMonoidHom
  have hdata' : RankOneData ↥(⊤ : Subgroup (PSL2MatrixGroup (L2K m))) U' B' := hdata.map t.symm
  letI : Fintype (ℙ (L2K m) (Fin 2 → (L2K m))) := Fintype.ofFinite _
  have hcardModel : Fintype.card (ℙ (L2K m) (Fin 2 → (L2K m))) = 1 + Nat.card U' := by
    have hline : Nat.card (ℙ (L2K m) (Fin 2 → (L2K m))) = 2 ^ m + 1 := by
      rw [Projectivization.card_of_finrank_two (L2K m) (Fin 2 → (L2K m)) (by simp), hKcard]
    have hcardU' : Nat.card U' = Nat.card U :=
      Subgroup.card_map_of_injective t.symm.injective
    rw [← Nat.card_eq_fintype_card, hline, hcardU', hUcard]
    omega
  have h2 : MulAction.IsMultiplyPretransitive (PSL2MatrixGroup (L2K m))
      (ℙ (L2K m) (Fin 2 → (L2K m))) 2 :=
    (linearPointAction_psl2 (K := (L2K m)) hKcard).isMultiplyPretransitive
  have htop : (⊤ : Subgroup (PSL2MatrixGroup (L2K m))) ≠ ⊥ := top_ne_bot
  obtain ⟨x, hx⟩ := exists_stabilizer_eq_conj_of_rankOneData
    (Y := PSL2MatrixGroup (L2K m)) (N := (⊤ : Subgroup (PSL2MatrixGroup (L2K m))))
    htop h2 hdata' hcardModel (psl2ProjectiveInfinity (L2K m))
  have hx' : (MulAction.stabilizer (PSL2MatrixGroup (L2K m))
      (psl2ProjectiveInfinity (L2K m))).subgroupOf
        (⊤ : Subgroup (PSL2MatrixGroup (L2K m))) =
      B'.map (MulAut.conj x).toMonoidHom := hx
  have hcomp : (t.toMonoidHom.comp (MulAut.conj x).toMonoidHom).comp t.symm.toMonoidHom =
      (MulAut.conj (t x)).toMonoidHom := by
    ext b
    simp [MulAut.conj_apply, mul_assoc]
  have hmap : (B'.map (MulAut.conj x).toMonoidHom).map t.toMonoidHom =
      B.map (MulAut.conj (t x)).toMonoidHom := by
    rw [show B' = B.map t.symm.toMonoidHom from rfl]
    rw [Subgroup.map_map, Subgroup.map_map]
    change B.map (((t.toMonoidHom.comp (MulAut.conj x).toMonoidHom).comp
      t.symm.toMonoidHom)) = B.map (MulAut.conj (t x)).toMonoidHom
    rw [hcomp]
  have ht : t.toMonoidHom = (⊤ : Subgroup (PSL2MatrixGroup (L2K m))).subtype := rfl
  have hxmap := congrArg (Subgroup.map t.toMonoidHom) hx'
  rw [ht] at hxmap hmap
  rw [Subgroup.map_subgroupOf_eq_of_le le_top] at hxmap
  refine ⟨U, B, hUcard, hdata, t x, ?_⟩
  change MulAction.stabilizer (PSL2MatrixGroup (L2K m)) (psl2ProjectiveInfinity (L2K m)) =
    B.map (MulAut.conj (t x)).toMonoidHom
  rw [hxmap, hmap]

structure L2Setup (X Ω : Type) [Group X] [MulAction X Ω]
    (N : Subgroup X) (m : ℕ) where
  e : ↥N ≃* PSL2MatrixGroup (L2K m)
  theta : Ω ≃ ℙ (L2K m) (Fin 2 → (L2K m))
  theta_smul : ∀ (n : ↥N) (ω : Ω), theta (n • ω) = e n • theta ω
  U : Subgroup ↥N
  B : Subgroup ↥N
  T : Subgroup ↥N
  hU : U = (psl2UpperUnipotentSubgroup (L2K m)).map e.symm.toMonoidHom
  hB : B = (psl2Borel (L2K m)).map e.symm.toMonoidHom
  hT : T = (torus (L2K m)).map e.symm.toMonoidHom
  hUleB : U ≤ B
  hUnorm : (U.subgroupOf B).Normal
  hU2 : IsPGroup 2 U
  hUcard : Nat.card U = 2 ^ m
  hBcard : Nat.card B = 2 ^ m * (2 ^ m - 1)
  hTcard : Nat.card T = 2 ^ m - 1
  hTcyc : IsCyclic T
  model : LinearPointAction (PSL2MatrixGroup (L2K m))
    (ℙ (L2K m) (Fin 2 → (L2K m))) (2 ^ m)
    (psl2ProjectiveInfinity (L2K m)) (psl2ProjectiveZero (L2K m))
    (psl2UpperUnipotentSubgroup (L2K m)) (torus (L2K m))

theorem exists_l2Setup {X Ω : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω]
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (m : ℕ) (hm : 2 ≤ m)
    (N : Subgroup X) (hN : N.Normal)
    (e : ↥N ≃* PSL2MatrixGroup (L2K m))
    (hΩ : Fintype.card Ω = 2 ^ m + 1) :
    Nonempty (L2Setup X Ω N m) := by
  classical
  letI : N.Normal := hN
  have hKcard : Nat.card (L2K m) = 2 ^ m := GaloisField.card 2 m (by omega)
  let L := linearPointAction_psl2 (K := (L2K m)) hKcard
  obtain ⟨U_d, B_d, hUcard_d, hdata_d, x₀, hB₀⟩ := exists_conj_borel_eq_psl2Borel (m := m) hm
  have hdataN : RankOneData ↥N (U_d.map e.symm.toMonoidHom) (B_d.map e.symm.toMonoidHom) :=
    hdata_d.map e.symm
  have hNbot : N ≠ ⊥ := by
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hdata_d.ne_bot
    have heu1 : e.symm u ≠ 1 := by
      intro h
      apply hu1
      have h' : e.symm u = e.symm (1 : U_d) := by simpa using h
      exact Subtype.ext (e.symm.injective h')
    intro hbot
    apply heu1
    apply Subtype.ext
    rw [Subgroup.coe_one]
    have hmem : ((e.symm u : ↥N) : X) ∈ (⊥ : Subgroup X) := by
      rw [← hbot]
      exact (e.symm u).2
    exact Subgroup.mem_bot.mp hmem
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩ]; positivity)
  let ω₀ : Ω := Classical.arbitrary Ω
  have hcardN : Fintype.card Ω = 1 + Nat.card (U_d.map e.symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hΩ, hUcard_d]
    omega
  obtain ⟨y, hy⟩ := exists_stabilizer_eq_conj_of_rankOneData
    (Y := X) (N := N) hNbot h2 hdataN hcardN ω₀
  have hBd : B_d = ((psl2Borel (L2K m)).map (MulAut.conj x₀⁻¹).toMonoidHom) := by
    have hcomp : (MulAut.conj x₀⁻¹).toMonoidHom.comp (MulAut.conj x₀).toMonoidHom =
        MonoidHom.id (PSL2MatrixGroup (L2K m)) := by
      ext b
      simp [MulAut.conj_apply, mul_assoc]
    rw [hB₀, Subgroup.map_map, hcomp, Subgroup.map_id]
  haveI : MulAction.IsPreprimitive X Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  haveI : MulAction.IsQuasiPreprimitive X Ω := inferInstance
  have hfixed : MulAction.fixedPoints N Ω ≠ ⊤ := by
    intro htop
    apply hNbot
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
    intro x
    have hx : x ∈ MulAction.fixedPoints N Ω := by rw [htop]; exact Set.mem_univ x
    simpa using hx ⟨n, hn⟩
  haveI : MulAction.IsPretransitive N Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N) hfixed
  haveI h2P : MulAction.IsMultiplyPretransitive (PSL2MatrixGroup (L2K m))
      (ℙ (L2K m) (Fin 2 → (L2K m))) 2 := L.isMultiplyPretransitive
  haveI : MulAction.IsPretransitive (PSL2MatrixGroup (L2K m))
      (ℙ (L2K m) (Fin 2 → (L2K m))) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let a_d : ℙ (L2K m) (Fin 2 → (L2K m)) := x₀⁻¹ • psl2ProjectiveInfinity (L2K m)
  let a₀ : ℙ (L2K m) (Fin 2 → (L2K m)) := (e y) • a_d
  have hBd_stab : B_d = MulAction.stabilizer (PSL2MatrixGroup (L2K m)) a_d := by
    change B_d = MulAction.stabilizer (PSL2MatrixGroup (L2K m))
      (x₀⁻¹ • psl2ProjectiveInfinity (L2K m))
    rw [hBd, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rfl
  have hstab : (MulAction.stabilizer ↥N ω₀).map e.toMonoidHom =
      MulAction.stabilizer (PSL2MatrixGroup (L2K m)) a₀ := by
    have hyN : MulAction.stabilizer ↥N ω₀ =
        (B_d.map e.symm.toMonoidHom).map (MulAut.conj y).toMonoidHom := by
      rw [← MulAction.stabilizer_subgroupOf]
      exact hy
    rw [hyN, Subgroup.map_map, Subgroup.map_map]
    rw [show e.toMonoidHom.comp (MulAut.conj y).toMonoidHom =
        (MulAut.conj (e y)).toMonoidHom.comp e.toMonoidHom by
      ext b
      simp [MulAut.conj_apply, mul_assoc]]
    rw [show ((MulAut.conj (e y)).toMonoidHom.comp e.toMonoidHom).comp
        e.symm.toMonoidHom = (MulAut.conj (e y)).toMonoidHom by
      ext b
      simp [MulAut.conj_apply, mul_assoc]]
    change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (e y))) B_d =
      MulAction.stabilizer (PSL2MatrixGroup (L2K m)) ((e y) • a_d)
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, ← hBd_stab]
  obtain ⟨theta, htheta⟩ :=
    CFSG.BenderSuzuki.PFchapter4section1.exists_equivariant_equiv_of_stabilizer_map_eq
      e ω₀ a₀ hstab
  let U₀ : Subgroup (PSL2MatrixGroup (L2K m)) := psl2UpperUnipotentSubgroup (L2K m)
  let B₀ : Subgroup (PSL2MatrixGroup (L2K m)) := psl2Borel (L2K m)
  let T₀ : Subgroup (PSL2MatrixGroup (L2K m)) := torus (L2K m)
  have hU₀leB₀ : U₀ ≤ B₀ := by
    rw [show B₀ = MulAction.stabilizer (PSL2MatrixGroup (L2K m))
      (psl2ProjectiveInfinity (L2K m)) from rfl, ← L.sup_eq_stabilizer]
    exact le_sup_left
  have hT₀leB₀ : T₀ ≤ B₀ := by
    rw [show B₀ = MulAction.stabilizer (PSL2MatrixGroup (L2K m))
      (psl2ProjectiveInfinity (L2K m)) from rfl, ← L.sup_eq_stabilizer]
    exact le_sup_right
  have hT₀norm : T₀ ≤ Subgroup.normalizer (U₀ : Set (PSL2MatrixGroup (L2K m))) :=
    hT₀leB₀.trans L.stabilizer_le_normalizer
  have hdisj : Disjoint U₀ T₀ := by
    rw [disjoint_iff]
    exact L.inf_eq_bot
  have hB₀card : Nat.card B₀ = 2 ^ m * (2 ^ m - 1) := by
    rw [show B₀ = U₀ ⊔ T₀ from L.sup_eq_stabilizer.symm,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U₀ T₀ hT₀norm hdisj,
      L.card_U, L.card_T]
  let U : Subgroup ↥N := U₀.map e.symm.toMonoidHom
  let B : Subgroup ↥N := B₀.map e.symm.toMonoidHom
  let T : Subgroup ↥N := T₀.map e.symm.toMonoidHom
  have hUleB : U ≤ B := Subgroup.map_mono hU₀leB₀
  have hU2 : IsPGroup 2 U := by
    obtain ⟨S, hS⟩ := L.exists_sylow
    have hU₀2 : IsPGroup 2 U₀ := by
      change IsPGroup 2 (psl2UpperUnipotentSubgroup (L2K m))
      rw [← hS]
      exact S.isPGroup'
    exact hU₀2.map e.symm.toMonoidHom
  have hUcard : Nat.card U = 2 ^ m := by
    rw [Subgroup.card_map_of_injective e.symm.injective, L.card_U]
  have hBcard : Nat.card B = 2 ^ m * (2 ^ m - 1) := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hB₀card]
  have hTcard : Nat.card T = 2 ^ m - 1 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, L.card_T]
  have hTcyc : IsCyclic T := by
    haveI : IsCyclic T₀ := L.isCyclic
    let eT : T₀ ≃* T := Subgroup.equivMapOfInjective T₀ e.symm.toMonoidHom
      e.symm.injective
    exact isCyclic_of_surjective eT.toMonoidHom eT.surjective
  have hUnorm : (U.subgroupOf B).Normal := by
    have hconj : ∀ b ∈ B, ∀ x ∈ U, b * x * b⁻¹ ∈ U := by
      intro b hb x hx
      rcases Subgroup.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩
      rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
      have hmem : b₀ * u * b₀⁻¹ ∈ U₀ :=
        (Subgroup.mem_normalizer_iff.mp
          (L.stabilizer_le_normalizer (show b₀ ∈ MulAction.stabilizer
            (PSL2MatrixGroup (L2K m)) (psl2ProjectiveInfinity (L2K m)) from hb₀)) u).mp hu
      refine Subgroup.mem_map.mpr ⟨b₀ * u * b₀⁻¹, hmem, ?_⟩
      simp [mul_assoc]
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUleB]
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj b hb x hx
    · intro hx
      have hx' : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ ∈ U :=
        hconj b⁻¹ (B.inv_mem hb) (b * x * b⁻¹) hx
      simpa [mul_assoc] using hx'
  refine ⟨{
    e := e
    theta := theta
    theta_smul := htheta
    U := U
    B := B
    T := T
    hU := rfl
    hB := rfl
    hT := rfl
    hUleB := hUleB
    hUnorm := hUnorm
    hU2 := hU2
    hUcard := hUcard
    hBcard := hBcard
    hTcard := hTcard
    hTcyc := hTcyc
    model := L }⟩

namespace L2Setup

variable {X Ω : Type} [Group X] [MulAction X Ω] {N : Subgroup X} {m : ℕ}

theorem stabilizer_map (S : L2Setup X Ω N m) (ω : Ω) :
    (MulAction.stabilizer ↥N ω).map S.e.toMonoidHom =
      MulAction.stabilizer (PSL2MatrixGroup (L2K m)) (S.theta ω) := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    calc
      S.e n • S.theta ω = S.theta (n • ω) := (S.theta_smul n ω).symm
      _ = S.theta ω := by rw [show n • ω = ω from hn]
  · intro hx
    refine ⟨S.e.symm x, ?_, by simp⟩
    apply S.theta.injective
    rw [S.theta_smul]
    simpa using hx

theorem exists_borel_conj (S : L2Setup X Ω N m) (ω : Ω) :
    ∃ r : ↥N, (S.e r) • psl2ProjectiveInfinity (L2K m) = S.theta ω ∧
      (MulAction.stabilizer X ω).subgroupOf N =
        S.B.map (MulAut.conj r).toMonoidHom := by
  classical
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (PSL2MatrixGroup (L2K m))
    (psl2ProjectiveInfinity (L2K m)) (S.theta ω)
  let r : ↥N := S.e.symm p
  refine ⟨r, ?_, ?_⟩
  · simpa [r] using hp
  · apply Subgroup.map_injective (f := S.e.toMonoidHom) S.e.injective
    rw [MulAction.stabilizer_subgroupOf, S.stabilizer_map ω, ← hp]
    have hcomp : (S.e.toMonoidHom.comp (MulAut.conj r).toMonoidHom).comp
        S.e.symm.toMonoidHom = (MulAut.conj p).toMonoidHom := by
      ext b
      simp [r, MulAut.conj_apply, mul_assoc]
    rw [S.hB, Subgroup.map_map, Subgroup.map_map, hcomp]
    change MulAction.stabilizer (PSL2MatrixGroup (L2K m))
        (p • psl2ProjectiveInfinity (L2K m)) =
      (psl2Borel (L2K m)).map (MulAut.conj p).toMonoidHom
    rw [show psl2Borel (L2K m) = MulAction.stabilizer
      (PSL2MatrixGroup (L2K m)) (psl2ProjectiveInfinity (L2K m)) from rfl,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj]
theorem card_fixed_le_two (S : L2Setup X Ω N m) {t : ↥N} (ht : t ≠ 1) :
    Nat.card {x : Ω // t • x = x} ≤ 2 := by
  classical
  letI : Fintype (ℙ (L2K m) (Fin 2 → (L2K m))) := Fintype.ofFinite _
  let f : {x : Ω // t • x = x} →
      {y : ℙ (L2K m) (Fin 2 → (L2K m)) // S.e t • y = y} := fun x =>
    ⟨S.theta x.1, by
      rw [← S.theta_smul t x.1]
      exact congrArg S.theta x.2⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (S.theta.injective (congrArg Subtype.val hxy))
  have hte : S.e t ≠ 1 := by
    intro h
    exact ht (S.e.injective (by simpa using h))
  haveI : Finite {y : ℙ (L2K m) (Fin 2 → (L2K m)) // S.e t • y = y} :=
    Finite.of_injective (fun y => y.1) Subtype.val_injective
  exact (Nat.card_le_card_of_injective f hf).trans
    (CFSG.GorensteinWalter.psl2_fixedPoint_card_le_two (L2K m) (S.e t) hte)

theorem eq_two_of_fixed (S : L2Setup X Ω N m) [Fintype Ω] {t : ↥N} (ht : t ≠ 1)
    {ω ω' : Ω} (hω : t • ω = ω) (hω' : t • ω' = ω') (hne : ω ≠ ω') :
    ∀ x : Ω, t • x = x → x = ω ∨ x = ω' := by
  classical
  have hcard := S.card_fixed_le_two ht
  intro x hx
  by_contra h
  push Not at h
  obtain ⟨hxω, hxω'⟩ := h
  have h3 : 3 ≤ Nat.card {y : Ω // t • y = y} := by
    let f : Fin 3 → {y : Ω // t • y = y}
      | 0 => ⟨ω, hω⟩
      | 1 => ⟨ω', hω'⟩
      | 2 => ⟨x, hx⟩
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> tauto
    haveI : Finite Ω := Finite.of_fintype Ω
    haveI : Finite {y : Ω // t • y = y} :=
      Finite.of_injective (fun y => y.1) Subtype.val_injective
    simpa using Nat.card_le_card_of_injective f hf
  omega

theorem map_root (S : L2Setup X Ω N m) (r : ↥N) :
    (S.U.map (MulAut.conj r).toMonoidHom).map S.e.toMonoidHom =
      (psl2UpperUnipotentSubgroup (L2K m)).map (MulAut.conj (S.e r)).toMonoidHom := by
  have hcomp : (S.e.toMonoidHom.comp (MulAut.conj r).toMonoidHom).comp
      S.e.symm.toMonoidHom = (MulAut.conj (S.e r)).toMonoidHom := by
    ext b
    simp [MulAut.conj_apply, mul_assoc]
  rw [S.hU, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem exists_torus_conj (S : L2Setup X Ω N m) {ω ω' : Ω} (hne : ω ≠ ω') :
    ∃ r : ↥N, MulAction.stabilizer ↥N ω ⊓ MulAction.stabilizer ↥N ω' =
      S.T.map (MulAut.conj r).toMonoidHom := by
  classical
  let a : ℙ (L2K m) (Fin 2 → (L2K m)) := S.theta ω
  let b : ℙ (L2K m) (Fin 2 → (L2K m)) := S.theta ω'
  have hab : a ≠ b := fun h => hne (S.theta.injective h)
  have h2 := S.model.isMultiplyPretransitive
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨p, hpα, hpβ⟩ := h2 (a := psl2ProjectiveInfinity (L2K m))
    (b := psl2ProjectiveZero (L2K m)) (c := a) (d := b) S.model.ne hab
  let r : ↥N := S.e.symm p
  refine ⟨r, ?_⟩
  have hcomp : (S.e.toMonoidHom.comp (MulAut.conj r).toMonoidHom).comp
      S.e.symm.toMonoidHom = (MulAut.conj p).toMonoidHom := by
    ext c
    simp [r, MulAut.conj_apply, mul_assoc]
  have hωmap : (MulAction.stabilizer ↥N ω).map S.e.toMonoidHom =
      (psl2Borel (L2K m)).map (MulAut.conj p).toMonoidHom := by
    rw [S.stabilizer_map ω, show S.theta ω = a from rfl, ← hpα]
    rw [show psl2Borel (L2K m) = MulAction.stabilizer
      (PSL2MatrixGroup (L2K m)) (psl2ProjectiveInfinity (L2K m)) from rfl,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hω'map : (MulAction.stabilizer ↥N ω').map S.e.toMonoidHom =
      (MulAction.stabilizer (PSL2MatrixGroup (L2K m))
        (psl2ProjectiveZero (L2K m))).map (MulAut.conj p).toMonoidHom := by
    rw [S.stabilizer_map ω', show S.theta ω' = b from rfl, ← hpβ]
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hω : MulAction.stabilizer ↥N ω =
      ((psl2Borel (L2K m)).map S.e.symm.toMonoidHom).map
        (MulAut.conj r).toMonoidHom := by
    apply Subgroup.map_injective (f := S.e.toMonoidHom) S.e.injective
    rw [hωmap, Subgroup.map_map, Subgroup.map_map, hcomp]
  have hω' : MulAction.stabilizer ↥N ω' =
      ((MulAction.stabilizer (PSL2MatrixGroup (L2K m))
        (psl2ProjectiveZero (L2K m))).map S.e.symm.toMonoidHom).map
        (MulAut.conj r).toMonoidHom := by
    apply Subgroup.map_injective (f := S.e.toMonoidHom) S.e.injective
    rw [hω'map, Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hω, hω']
  rw [← Subgroup.map_inf ((psl2Borel (L2K m)).map S.e.symm.toMonoidHom)
    ((MulAction.stabilizer (PSL2MatrixGroup (L2K m))
      (psl2ProjectiveZero (L2K m))).map S.e.symm.toMonoidHom)
    (MulAut.conj r).toMonoidHom (MulAut.conj r).injective]
  rw [← Subgroup.map_inf (psl2Borel (L2K m))
    (MulAction.stabilizer (PSL2MatrixGroup (L2K m))
      (psl2ProjectiveZero (L2K m))) S.e.symm.toMonoidHom S.e.symm.injective]
  have hinf : psl2Borel (L2K m) ⊓
      MulAction.stabilizer (PSL2MatrixGroup (L2K m))
        (psl2ProjectiveZero (L2K m)) = torus (L2K m) := by
    rw [show psl2Borel (L2K m) = MulAction.stabilizer
        (PSL2MatrixGroup (L2K m)) (psl2ProjectiveInfinity (L2K m)) from rfl,
      S.model.stabilizer_inf_stabilizer]
  rw [hinf, ← S.hT]

end L2Setup

end L2

end CFSG.Quasithin.Stroth.WeissDelta
