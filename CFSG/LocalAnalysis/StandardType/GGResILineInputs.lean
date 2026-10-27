module

public import CFSG.LocalAnalysis.StandardType.GGResILinDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDichotomy
public import CFSG.LocalAnalysis.StandardType.GGRealQFour
public import CFSG.LocalAnalysis.StandardType.GGPZWeylB
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
public import CFSG.LocalAnalysis.StandardType.GGB48OmReduce
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenBlock
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResLineJDatum {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs J : Subgroup G)
    (T : GGResLineJType) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (r : Fin T.rank → MulAut ↥Bs) (h : Fin T.rank → V) (α : Fin T.rank → Module.Dual (ZMod p) V),
    (∀ j w, ggLin (p := p) ι (r j) w = w - α j w • h j) ∧ (∀ j, GGIsReflection p (r j)) ∧
      (∀ i j, α i (h j) = (T.cartan i j : ZMod p)) ∧ LinearIndependent (ZMod p) h ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range r)

namespace GGResLineJDatum

theorem transport {G G' : Type} [Group G] [Group G'] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} {Bs' J' : Subgroup G'} (T : GGResLineJType)
    (e : ↥Bs ≃* ↥Bs')
    (haut : ggAutomizer J' Bs' = (ggAutomizer J Bs).map (MulAut.congr e).toMonoidHom)
    (hD : GGResLineJDatum p Bs J T) :
    GGResLineJDatum p Bs' J' T := by
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  let ι' : Additive ↥Bs' ≃+ V := (MulEquiv.toAdditive e.symm).trans ι
  let r' : Fin T.rank → MulAut ↥Bs' := fun j => MulAut.congr e (r j)
  refine ⟨V, instA, instM, ι', r', h, α, ?_, ?_, ?_, ?_, ?_⟩
  · intro j w
    change ggLin (p := p) ((MulEquiv.toAdditive e.symm).trans ι)
      (MulAut.congr e (r j)) w = w - α j w • h j
    rw [ggLin_mulEquiv_congr e ι (r j)]
    exact hform j w
  · intro j
    exact (F4AutRefl.ggIsReflection_congr_iff e (r j)).mpr (hrefl j)
  · exact hpair
  · exact hind
  · calc
      ggAutomizer J' Bs' = (ggAutomizer J Bs).map (MulAut.congr e).toMonoidHom := haut
      _ = (Subgroup.closure (Set.range r)).map (MulAut.congr e).toMonoidHom := by rw [hgen]
      _ = Subgroup.closure ((MulAut.congr e).toMonoidHom '' Set.range r) := by
            rw [MonoidHom.map_closure]
      _ = Subgroup.closure (Set.range r') := by
            rw [← Set.range_comp' (MulAut.congr e).toMonoidHom r]
            rfl

end GGResLineJDatum

theorem ggResLineJDatum_map_mk'_of_coprime {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (T : GGResLineJType) (hpN : ¬ p ∣ Nat.card N) (hBs : IsPGroup p Bs) (hNJ : N ≤ J)
    (hD : GGResLineJDatum p Bs J T) :
    GGResLineJDatum p (Bs.map (QuotientGroup.mk' N)) (J.map (QuotientGroup.mk' N)) T :=
  GGResLineJDatum.transport T (coprimeQuotientSubgroupEquiv hpN hBs)
    (ggAutomizer_map_mk'_of_coprime hpN hBs hNJ) hD

theorem ggAutomizer_card_of_lineJDatum_A2 {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs J : Subgroup G} (hp : p = 3) (hD : GGResLineJDatum p Bs J .A2) :
    Nat.card (ggAutomizer J Bs) = 6 := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  let rV : Fin 2 → MulAut ↥Bs := r
  let hV : Fin 2 → V := h
  let αV : Fin 2 → Module.Dual (ZMod 3) V := α
  have hformV : ∀ j w, ggLin (p := 3) ι (rV j) w = w - αV j w • hV j := by
    intro j w
    simpa [rV, hV, αV] using hform j w
  have hreflV : ∀ j : Fin 2, GGIsReflection 3 (rV j) := by
    intro j
    simpa [rV] using hrefl j
  have hpairV : ∀ i j : Fin 2, αV i (hV j) = (CartanMatrix.A 2 i j : ZMod 3) := by
    intro i j
    simpa [rV, hV, αV, GGResLineJType.cartan] using hpair i j
  have hindV : LinearIndependent (ZMod 3) hV := hind
  have hgenV : ggAutomizer J Bs = Subgroup.closure (Set.range rV) := hgen
  have hC : GGIntCartan (CoxeterMatrix.A 2) (CartanMatrix.A 2) := by
    constructor
    · intro i
      fin_cases i <;> decide
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [CartanMatrix.A] <;> decide
  have hα : ∀ i : Fin 2, αV i (hV i) = 2 := fun i => by
    rw [hpairV i i, hC.1 i]
    norm_num
  have h10 : αV 1 (hV 0) = (2 : ZMod 3) := by
    have h10' : CartanMatrix.A 2 1 0 = -1 := by decide
    rw [hpairV 1 0, h10']
    show ((-1 : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  have h2ne : (2 : ZMod 3) ≠ 0 := by
    intro h
    have hdvd : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
    norm_num at hdvd
  let s0 : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (rV 0)
  let s1 : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (rV 1)
  have hs0 : s0 = Module.reflection (hα 0) := by
    ext v
    rw [show s0 v = v - αV 0 v • hV 0 from hformV 0 v,
      Module.reflection_apply (y := v) (h := hα 0)]
  have hs1 : s1 = Module.reflection (hα 1) := by
    ext v
    rw [show s1 v = v - αV 1 v • hV 1 from hformV 1 v,
      Module.reflection_apply (y := v) (h := hα 1)]
  have hbraid : (s0 * s1) ^ 3 = 1 := by
    have hlift := isLiftable_reflection_of_intCartan hC hV αV hα hpairV
    have h01 := hlift 0 1
    have hM01 : (CoxeterMatrix.A 2) 0 1 = 3 := by decide
    rw [hM01] at h01
    simpa [hs0, hs1] using h01
  have hbraidMul : (rV 0 * rV 1) ^ 3 = 1 := by
    apply ggLin_injective (p := 3) ι
    rw [map_pow, map_mul, map_one]
    simpa [s0, s1] using hbraid
  have hs_ne : s0 ≠ s1 := by
    intro hseq
    have he := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (hV 0)) hseq
    rw [hs0, hs1, Module.reflection_apply (y := hV 0) (h := hα 0),
      Module.reflection_apply (y := hV 0) (h := hα 1), hα 0, h10] at he
    have hsc : (2 : ZMod 3) • hV 0 = (2 : ZMod 3) • hV 1 := sub_right_inj.mp he
    have h01 : hV 0 = hV 1 := smul_right_injective V h2ne hsc
    exact (by decide : (0 : Fin 2) ≠ 1) (hindV.injective h01)
  have hr0sq : rV 0 * rV 0 = 1 := by simpa [pow_two] using (hreflV 0).1
  have hr1sq : rV 1 * rV 1 = 1 := by simpa [pow_two] using (hreflV 1).1
  have hs1sq : s1 * s1 = 1 := by
    calc s1 * s1 = ggLin (p := 3) ι (rV 1 * rV 1) := by rw [map_mul]
      _ = 1 := by rw [hr1sq, map_one]
  have hr0ne : rV 0 ≠ 1 := by
    intro heq
    have hs : s0 = 1 := by
      dsimp [s0]
      rw [heq, map_one]
    have hneg : s0 (hV 0) = -hV 0 := by
      rw [hs0, Module.reflection_apply_self (h := hα 0)]
    have he : -hV 0 = hV 0 := by rw [← hneg, hs]; rfl
    have hsc : (2 : ZMod 3) • hV 0 = 0 := by
      have h' : hV 0 + hV 0 = 0 := by
        have := congrArg (fun x => x + hV 0) he
        simpa using this.symm
      simpa [show (2 : ZMod 3) = 1 + 1 by norm_num, add_smul, one_smul] using h'
    exact hindV.ne_zero 0 ((smul_eq_zero.mp hsc).resolve_left h2ne)
  have hr1ne : rV 1 ≠ 1 := by
    intro heq
    have hs : s1 = 1 := by
      dsimp [s1]
      rw [heq, map_one]
    have hneg : s1 (hV 1) = -hV 1 := by
      rw [hs1, Module.reflection_apply_self (h := hα 1)]
    have he : -hV 1 = hV 1 := by rw [← hneg, hs]; rfl
    have hsc : (2 : ZMod 3) • hV 1 = 0 := by
      have h' : hV 1 + hV 1 = 0 := by
        have := congrArg (fun x => x + hV 1) he
        simpa using this.symm
      simpa [show (2 : ZMod 3) = 1 + 1 by norm_num, add_smul, one_smul] using h'
    exact hindV.ne_zero 1 ((smul_eq_zero.mp hsc).resolve_left h2ne)
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer J Bs
  have hA : A = Subgroup.closure ({rV 0, rV 1} : Set (MulAut ↥Bs)) := by
    dsimp [A]
    rw [hgenV]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hmem0 : rV 0 ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hmem1 : rV 1 ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  let sK : ↥A := ⟨rV 0, hmem0⟩
  let tK : ↥A := ⟨rV 1, hmem1⟩
  have hsK2 : sK * sK = 1 := by
    apply Subtype.ext
    simpa [sK, pow_two] using (hreflV 0).1
  have htK2 : tK * tK = 1 := by
    apply Subtype.ext
    simpa [tK, pow_two] using (hreflV 1).1
  have hsK1 : sK ≠ 1 := by
    intro h
    apply hr0ne
    simpa [sK] using congrArg Subtype.val h
  have htK1 : tK ≠ 1 := by
    intro h
    apply hr1ne
    simpa [tK] using congrArg Subtype.val h
  have hprod_pow : (sK * tK) ^ 3 = 1 := by
    apply Subtype.ext
    simpa [sK, tK] using hbraidMul
  have hprod_ne : sK * tK ≠ 1 := by
    intro h
    have hval : rV 0 * rV 1 = 1 := by
      simpa [sK, tK] using congrArg Subtype.val h
    have hlin : s0 * s1 = 1 := by
      have := congrArg (ggLin (p := 3) ι) hval
      simpa [s0, s1, map_mul, map_one] using this
    have hs0eq : s0 = s1 := by
      calc s0 = s0 * 1 := by rw [mul_one]
        _ = s0 * (s1 * s1) := by rw [hs1sq]
        _ = (s0 * s1) * s1 := by rw [mul_assoc]
        _ = 1 * s1 := by rw [hlin]
        _ = s1 := by rw [one_mul]
    exact hs_ne hs0eq
  have hgenK : Subgroup.closure ({sK, tK} : Set ↥A) = ⊤ := by
    have hmap : (Subgroup.closure ({sK, tK} : Set ↥A)).map A.subtype = A := by
      rw [MonoidHom.map_closure]
      have himg : A.subtype '' ({sK, tK} : Set ↥A) =
          ({rV 0, rV 1} : Set (MulAut ↥Bs)) := by
        ext x
        simp [sK, tK]
      rw [himg, ← hA]
    apply Subgroup.map_injective A.subtype_injective
    rw [hmap, Subgroup.map_top]
    exact (Subgroup.range_subtype A).symm
  let e : DihedralGroup 3 ≃* ↥A :=
    TauCeti.dihedralGroupMulEquiv (s := sK) (t := tK) (n := 3)
      hsK2 htK2 hsK1 htK1 (orderOf_eq_prime hprod_pow hprod_ne) hgenK
  have hcard : Nat.card ↥A = 6 := by
    calc Nat.card ↥A = Nat.card (DihedralGroup 3) := (Nat.card_congr e.toEquiv).symm
      _ = 6 := by rw [DihedralGroup.nat_card]
  simpa [A] using hcard

theorem ggAutomizer_coxeterEquiv_of_reflectionData
    {G : Type} [Group G] [Fact (Nat.Prime 3)] {Bs J : Subgroup G}
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {C : Matrix (Fin n) (Fin n) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (r : Fin n → MulAut ↥Bs) (h : Fin n → V)
    (α : Fin n → Module.Dual (ZMod 3) V)
    (hC : GGIntCartan M C) (hFT : TauCeti.IsFiniteType C)
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r)) :
    ∃ e : ggAutomizer J Bs ≃* M.Group,
      ∀ (i : Fin n) (hri : r i ∈ ggAutomizer J Bs),
        e ⟨r i, hri⟩ = M.simple i := by
  classical
  have hα : ∀ i, α i (h i) = (2 : ZMod 3) := fun i => by
    rw [hpair i i, hC.1 i]
    norm_num
  let s : Fin n → (V ≃ₗ[ZMod 3] V) := fun i => Module.reflection (hα i)
  have hL : M.IsLiftable s := isLiftable_reflection_of_intCartan hC h α hα hpair
  let F : M.Group →* (V ≃ₗ[ZMod 3] V) := M.toCoxeterSystem.lift ⟨s, hL⟩
  have hFsimple : ∀ i, F (M.simple i) = s i := fun i => by
    rw [← CoxeterMatrix.toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]
  have hrange : F.range = Subgroup.closure (Set.range s) := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  have hinj : Function.Injective F :=
    ggCartanFaithful_of_isFiniteType hα hpair (by norm_num : (3 : ℕ) ≠ 2) hFT hC hind
  let eLin : M.Group ≃* ↥(Subgroup.closure (Set.range s)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hlin : ∀ i, ggLin (p := 3) ι (r i) = s i := fun i => by
    ext v
    rw [hform i v, Module.reflection_apply]
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer J Bs
  let R : Subgroup (MulAut ↥Bs) := Subgroup.closure (Set.range r)
  let B : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range s)
  have hA : A = R := by
    simpa [A, R] using hgen
  have himage : ggLin (p := 3) ι '' Set.range r = Set.range s := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hlin i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨r i, ⟨i, rfl⟩, hlin i⟩
  have hmapR : Subgroup.map (ggLin (p := 3) ι) R = B := by
    rw [MonoidHom.map_closure, himage]
  have hmapA : Subgroup.map (ggLin (p := 3) ι) A = B := by
    rw [hA]
    exact hmapR
  let eMapA : A ≃* B :=
    (Subgroup.equivMapOfInjective A (ggLin (p := 3) ι) (ggLin_injective ι)).trans
      (MulEquiv.subgroupCongr hmapA)
  let e : A ≃* M.Group := eMapA.trans eLin.symm
  have heLin_simple : ∀ i, (eLin (M.simple i) : V ≃ₗ[ZMod 3] V) = s i := fun i => by
    dsimp [eLin]
    rw [MonoidHom.ofInjective_apply]
    exact hFsimple i
  have heMapA : ∀ (i : Fin n) (hri : r i ∈ A),
      eMapA ⟨r i, hri⟩ = eLin (M.simple i) := by
    intro i hri
    apply Subtype.ext
    dsimp [eMapA]
    rw [heLin_simple i]
    exact hlin i
  refine ⟨e, ?_⟩
  intro i hri
  change (eMapA.trans eLin.symm) ⟨r i, hri⟩ = M.simple i
  rw [MulEquiv.trans_apply]
  exact (eLin.symm_apply_eq).2 (heMapA i hri)

theorem ggAutomizer_coxeterEquiv_of_lineJDatum
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    {T : GGResLineJType}
    (hp : p = 3) (hD : GGResLineJDatum p Bs J T)
    {M : CoxeterMatrix (Fin T.rank)} {C : Matrix (Fin T.rank) (Fin T.rank) ℤ}
    (hC : GGIntCartan M C) (hFT : TauCeti.IsFiniteType C)
    (hcartan : GGResLineJType.cartan T = C) :
    Nonempty (ggAutomizer J Bs ≃* M.Group) := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  have hpairC : ∀ i j : Fin T.rank, α i (h j) = (C i j : ZMod 3) := by
    intro i j
    rw [hpair i j, hcartan]
  obtain ⟨e, -⟩ := ggAutomizer_coxeterEquiv_of_reflectionData ι r h α hC hFT
    hform hpairC hind hgen
  exact ⟨e⟩

theorem ggAutomizer_card_of_lineJDatum_B2
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hp : p = 3) (hD : GGResLineJDatum p Bs J .B2) :
    Nat.card (ggAutomizer J Bs) = 8 := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hM : coxeterMatrix (isFiniteType_cartanC 2) = CoxeterMatrix.B 2 :=
    coxeterMatrix_cartanC_eq_B 2
  have hC : GGIntCartan (coxeterMatrix (isFiniteType_cartanC 2)) (CartanMatrix.B 2) := by
    rw [hM]
    exact ggIntCartan_B 2
  have hFT : TauCeti.IsFiniteType (CartanMatrix.B 2) :=
    TauCeti.isFiniteType_cartanMatrix_B 2
  have hcartan : GGResLineJType.cartan .B2 = CartanMatrix.B 2 := rfl
  obtain ⟨e⟩ := ggAutomizer_coxeterEquiv_of_lineJDatum
    (T := .B2) (M := coxeterMatrix (isFiniteType_cartanC 2)) (C := CartanMatrix.B 2)
    rfl hD hC hFT hcartan
  calc
    Nat.card (ggAutomizer J Bs) =
        Nat.card (coxeterMatrix (isFiniteType_cartanC 2)).Group := Nat.card_congr e.toEquiv
    _ = Nat.card (CoxeterMatrix.B 2).Group := by rw [hM]
    _ = 2 ^ 2 * Nat.factorial 2 := ggCoxeterB_card 2 (by norm_num)
    _ = 8 := by norm_num

theorem ggAutomizer_card_of_lineJDatum_A3
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hp : p = 3) (hD : GGResLineJDatum p Bs J .A3) :
    Nat.card (ggAutomizer J Bs) = 24 := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hFT : TauCeti.IsFiniteType (CartanMatrix.A 3) :=
    TauCeti.isFiniteType_cartanMatrix_A 3
  have hAeq : coxeterMatrix hFT = CoxeterMatrix.A 3 :=
    coxeterMatrix_eq_of_ggIntCartan hFT (ggIntCartan_A 3)
  have hC : GGIntCartan (coxeterMatrix hFT) (CartanMatrix.A 3) := by
    rw [hAeq]
    exact ggIntCartan_A 3
  have hcartan : GGResLineJType.cartan .A3 = CartanMatrix.A 3 := rfl
  obtain ⟨e⟩ := ggAutomizer_coxeterEquiv_of_lineJDatum
    (T := .A3) (M := coxeterMatrix hFT) (C := CartanMatrix.A 3)
    rfl hD hC hFT hcartan
  calc
    Nat.card (ggAutomizer J Bs) = Nat.card (coxeterMatrix hFT).Group :=
      Nat.card_congr e.toEquiv
    _ = Nat.card (CoxeterMatrix.A 3).Group := by rw [hAeq]
    _ = Nat.factorial 4 := l05nK3a_card_coxeterA 3
    _ = 24 := by norm_num

theorem ggWeylOfType_of_lineJDatum_A3
    {G : Type} [Group G] {Bs J : Subgroup G}
    (hD : GGResLineJDatum 3 Bs J .A3) :
    GGWeylOfType 3 (CoxeterMatrix.A 3) (ggAutomizer J Bs) := by
  have hFact : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  have hFT : TauCeti.IsFiniteType (CartanMatrix.A 3) :=
    TauCeti.isFiniteType_cartanMatrix_A 3
  have hC : GGIntCartan (CoxeterMatrix.A 3) (CartanMatrix.A 3) := ggIntCartan_A 3
  have hpairC : ∀ i j : Fin 3, α i (h j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    simpa [GGResLineJType.cartan] using hpair i j
  obtain ⟨e, he⟩ :=
    letI : Fact (Nat.Prime 3) := hFact
    ggAutomizer_coxeterEquiv_of_reflectionData
      (M := CoxeterMatrix.A 3) (C := CartanMatrix.A 3) ι r h α hC hFT hform hpairC hind hgen
  refine ⟨e.symm, ?_⟩
  intro i
  have hri : r i ∈ ggAutomizer J Bs := by
    rw [hgen]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hsymm : e.symm ((CoxeterMatrix.A 3).simple i) = ⟨r i, hri⟩ := by
    apply e.symm_apply_eq.mpr
    exact (he i hri).symm
  change GGIsReflection 3
    ((e.symm ((CoxeterMatrix.A 3).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs)
  rw [hsymm]
  exact hrefl i

theorem not_exists_inversion_mem_ggTorusWeylAut_of_center_eq_bot
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs J : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ p)
    (hA2 : 2 ≤ Nat.card (ggGamma J hN).range)
    (hcenter : Subgroup.center (ggAutomizer J Bs) = ⊥) :
    ¬ ∃ φ ∈ ggTorusWeylAut p (ggGamma J hN).range,
      ∀ a : ↥(ggGamma J hN).range, φ a = a⁻¹ := by
  classical
  rintro ⟨φ, hφW, hφinv⟩
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let H : Subgroup (MulAut ↥A) :=
    ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A
  let f : ggAutomizer J Bs →* H := ggAutomizerGammaHom hN
  have hInj : Function.Injective f :=
    ggAutomizerGammaHom_injective hp hBs hNoTr hN hZ
  have hcommφ : ∀ ψ : MulAut ↥A, φ * ψ = ψ * φ := by
    intro ψ
    ext a
    rw [MulAut.mul_apply, MulAut.mul_apply, hφinv, hφinv, map_inv]
  have hmem : φ ∈ (f.range.map H.subtype : Set (MulAut ↥A)) := by
    rw [ggAutomizerGammaHom_range (p := p) hBs hSC hN]
    exact hφW
  obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hc
  have hfd : ((f d : H) : MulAut ↥A) = φ := by
    rw [hd]
    exact hca
  have hdcent : d ∈ Subgroup.center (ggAutomizer J Bs) := by
    rw [Subgroup.mem_center_iff]
    intro e
    have hconj : d * e * d⁻¹ = e := by
      apply hInj
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv]
      change ((f d : H) : MulAut ↥A) * ((f e : H) : MulAut ↥A) *
          (((f d : H) : MulAut ↥A))⁻¹ = ((f e : H) : MulAut ↥A)
      rw [hfd]
      rw [hcommφ]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    calc e * d = (d * e * d⁻¹) * d := by rw [hconj]
      _ = d * e := by group
  have hd1 : d = 1 := by
    simpa [hcenter] using hdcent
  have hφ1 : φ = 1 := by
    rw [← hfd, hd1, map_one]
    rfl
  have hA2' : 2 ≤ Nat.card ↥A := by simpa [A] using hA2
  have hnt : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha1⟩ := @exists_ne ↥A hnt 1
  have ha : a = a⁻¹ := by
    have := hφinv a
    simpa [hφ1] using this
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [ha]
    rw [inv_mul_cancel]
  have hAs : IsElemAbelian p A := by
    have hrange : IsElemAbelian p (ggGamma J hN).range :=
      isElemAbelian_range_of_isElemAbelian hBs (ggGamma J hN)
    simpa [A] using hrange
  have hap : a ^ p = 1 := by
    apply Subtype.ext
    exact hAs.2 a a.2
  have hgcd : Nat.gcd p 2 = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp (hp.odd_of_ne_two hp2).coprime_two_right
  have h1 : a = 1 := by
    have hordvd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
    have hord2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
    have hdvd : orderOf a ∣ Nat.gcd p 2 := Nat.dvd_gcd hordvd hord2
    rw [hgcd] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  exact ha1 h1

theorem not_exists_inversion_mem_ggTorusWeylAut_of_lineJDatum_A3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ p)
    (hp : p = 3) (hA2 : 2 ≤ Nat.card (ggGamma J hN).range)
    (hD : GGResLineJDatum p Bs J .A3) :
    ¬ ∃ φ ∈ ggTorusWeylAut p (ggGamma J hN).range,
      ∀ a : ↥(ggGamma J hN).range, φ a = a⁻¹ := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcenter : Subgroup.center (ggAutomizer J Bs) = ⊥ := by
    obtain ⟨eW⟩ := ggAutomizer_coxeterEquiv_of_lineJDatum
      (T := .A3) (M := CoxeterMatrix.A 3) (C := CartanMatrix.A 3)
      rfl hD (ggIntCartan_A 3) (TauCeti.isFiniteType_cartanMatrix_A 3) rfl
    have eW' : ↥(ggAutomizer J Bs) ≃* (CoxeterMatrix.A 3).Group := eW
    have hWcenter : Subgroup.center (CoxeterMatrix.A 3).Group = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [ggCoxeterA_center 3 (by norm_num)]
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    have hd' : eW' d ∈ Subgroup.center (CoxeterMatrix.A 3).Group := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨z, rfl⟩ := eW'.surjective w
      simpa [map_mul] using congrArg eW' (Subgroup.mem_center_iff.mp hd z)
    rw [hWcenter, Subgroup.mem_bot] at hd'
    calc d = eW'.symm (eW' d) := (eW'.symm_apply_apply d).symm
      _ = eW'.symm 1 := by rw [hd']
      _ = 1 := map_one eW'.symm
  exact not_exists_inversion_mem_ggTorusWeylAut_of_center_eq_bot
    (p := 3) Nat.prime_three (by norm_num) hN hBs hSC hNoTr hZ hA2 hcenter

theorem not_exists_inversion_mem_ggTorusWeylAut_of_lineJDatum_A2
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs)
    (hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ p)
    (hp : p = 3) (hA2 : 2 ≤ Nat.card (ggGamma J hN).range)
    (hD : GGResLineJDatum p Bs J .A2) :
    ¬ ∃ φ ∈ ggTorusWeylAut p (ggGamma J hN).range,
      ∀ a : ↥(ggGamma J hN).range, φ a = a⁻¹ := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcenter : Subgroup.center (ggAutomizer J Bs) = ⊥ := by
    obtain ⟨eW⟩ := ggAutomizer_coxeterEquiv_of_lineJDatum
      (T := .A2) (M := CoxeterMatrix.A 2) (C := CartanMatrix.A 2)
      rfl hD (ggIntCartan_A 2) (TauCeti.isFiniteType_cartanMatrix_A 2) rfl
    have eW' : ↥(ggAutomizer J Bs) ≃* (CoxeterMatrix.A 2).Group := eW
    have hWcenter : Subgroup.center (CoxeterMatrix.A 2).Group = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [ggCoxeterA_center 2 (by norm_num)]
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    have hd' : eW' d ∈ Subgroup.center (CoxeterMatrix.A 2).Group := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨z, rfl⟩ := eW'.surjective w
      simpa [map_mul] using congrArg eW' (Subgroup.mem_center_iff.mp hd z)
    rw [hWcenter, Subgroup.mem_bot] at hd'
    calc d = eW'.symm (eW' d) := (eW'.symm_apply_apply d).symm
      _ = eW'.symm 1 := by rw [hd']
      _ = 1 := map_one eW'.symm
  exact not_exists_inversion_mem_ggTorusWeylAut_of_center_eq_bot
    (p := 3) Nat.prime_three (by norm_num) hN hBs hSC hNoTr hZ hA2 hcenter

theorem ggAutomizer_card_of_lineJDatum_B3
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hp : p = 3) (hD : GGResLineJDatum p Bs J .B3) :
    Nat.card (ggAutomizer J Bs) = 48 := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hM : coxeterMatrix (isFiniteType_cartanC 3) = CoxeterMatrix.B 3 :=
    coxeterMatrix_cartanC_eq_B 3
  have hC : GGIntCartan (coxeterMatrix (isFiniteType_cartanC 3)) (CartanMatrix.B 3) := by
    rw [hM]
    exact ggIntCartan_B 3
  have hFT : TauCeti.IsFiniteType (CartanMatrix.B 3) :=
    TauCeti.isFiniteType_cartanMatrix_B 3
  have hcartan : GGResLineJType.cartan .B3 = CartanMatrix.B 3 := rfl
  obtain ⟨e⟩ := ggAutomizer_coxeterEquiv_of_lineJDatum
    (T := .B3) (M := coxeterMatrix (isFiniteType_cartanC 3)) (C := CartanMatrix.B 3)
    rfl hD hC hFT hcartan
  calc
    Nat.card (ggAutomizer J Bs) =
        Nat.card (coxeterMatrix (isFiniteType_cartanC 3)).Group := Nat.card_congr e.toEquiv
    _ = Nat.card (CoxeterMatrix.B 3).Group := by rw [hM]
    _ = 2 ^ 3 * Nat.factorial 3 := ggCoxeterB_card 3 (by norm_num)
    _ = 48 := by norm_num

theorem ggAutomizer_card_of_lineJDatum_C3
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs J : Subgroup G}
    (hp : p = 3) (hD : GGResLineJDatum p Bs J .C3) :
    Nat.card (ggAutomizer J Bs) = 48 := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hM : coxeterMatrix (isFiniteType_cartanC 3) = CoxeterMatrix.B 3 :=
    coxeterMatrix_cartanC_eq_B 3
  have hC : GGIntCartan (coxeterMatrix (isFiniteType_cartanC 3)) (CartanMatrix.C 3) := by
    rw [hM]
    exact ggIntCartan_C 3
  have hFT : TauCeti.IsFiniteType (CartanMatrix.C 3) :=
    TauCeti.isFiniteType_cartanMatrix_C 3
  have hcartan : GGResLineJType.cartan .C3 = CartanMatrix.C 3 := rfl
  obtain ⟨e⟩ := ggAutomizer_coxeterEquiv_of_lineJDatum
    (T := .C3) (M := coxeterMatrix (isFiniteType_cartanC 3)) (C := CartanMatrix.C 3)
    rfl hD hC hFT hcartan
  calc
    Nat.card (ggAutomizer J Bs) =
        Nat.card (coxeterMatrix (isFiniteType_cartanC 3)).Group := Nat.card_congr e.toEquiv
    _ = Nat.card (CoxeterMatrix.B 3).Group := by rw [hM]
    _ = 2 ^ 3 * Nat.factorial 3 := ggCoxeterB_card 3 (by norm_num)
    _ = 48 := by norm_num

theorem linearIndependent_roots_of_lineJDatum_A2
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Bs J : Subgroup G} (ι : Additive ↥Bs ≃+ V)
    {r : Fin 2 → MulAut ↥Bs} {h : Fin 2 → V} {α : Fin 2 → Module.Dual (ZMod 3) V}
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 2 i j : ZMod 3))
    (hind : LinearIndependent (ZMod 3) h)
    (hmem : ∀ j, r j ∈ ggAutomizer J Bs)
    (hNoTr : GGNoTransvection 3 Bs) :
    LinearIndependent (ZMod 3) α := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h2ne : (2 : ZMod 3) ≠ 0 := by
    intro h
    have hdvd : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
    norm_num at hdvd
  have hα : ∀ i : Fin 2, α i (h i) = (2 : ZMod 3) := by
    intro i
    have hi : CartanMatrix.A 2 i i = 2 := by fin_cases i <;> decide
    rw [hpair i i, hi]
    norm_num
  have h10 : α 1 (h 0) = (2 : ZMod 3) := by
    have h10' : CartanMatrix.A 2 1 0 = -1 := by decide
    rw [hpair 1 0, h10']
    show ((-1 : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    have h1 := hα 1
    rw [hzero, LinearMap.zero_apply] at h1
    exact h2ne h1.symm
  · intro c hc
    have hc0 := congrArg (fun f : Module.Dual (ZMod 3) V => f (h 0)) hc
    simp only [LinearMap.smul_apply, smul_eq_mul, h10, hα 0] at hc0
    have hc1 : c = 1 := by
      have h2 : c * 2 = 1 * 2 := by simpa using hc0
      exact mul_right_cancel₀ h2ne h2
    have hαeq : α 0 = α 1 := by
      rw [← hc, hc1, one_smul]
    have hgf : α 1 = (1 : ZMod 3) • α 0 := by
      rw [hαeq, one_smul]
    have hs0 : ggLin (p := 3) ι (r 0) = Module.reflection (hα 0) := by
      ext v
      rw [show ggLin (p := 3) ι (r 0) v = v - α 0 v • h 0 from hform 0 v,
        Module.reflection_apply (y := v) (h := hα 0)]
    have hs1 : ggLin (p := 3) ι (r 1) = Module.reflection (hα 1) := by
      ext v
      rw [show ggLin (p := 3) ι (r 1) v = v - α 1 v • h 1 from hform 1 v,
        Module.reflection_apply (y := v) (h := hα 1)]
    have htrans_apply : ∀ v, ggLin (p := 3) ι (r 0 * r 1) v =
        v + α 0 v • (h 0 - h 1) := by
      intro v
      rw [map_mul, LinearEquiv.mul_apply, hs0, hs1]
      simpa using reflection_mul_reflection_apply_of_eq_smul_dual
        (hf := hα 0) (hg := hα 1) hgf v
    have h01ne : h 0 ≠ h 1 := fun hh =>
      (by decide : (0 : Fin 2) ≠ 1) (hind.injective hh)
    have hw : h 0 - h 1 ≠ 0 := sub_ne_zero.mpr h01ne
    have hf0 : α 0 ≠ 0 := by
      intro hzero
      have h0 := hα 0
      rw [hzero, LinearMap.zero_apply] at h0
      exact h2ne h0.symm
    have hfw : α 0 (h 0 - h 1) = 0 := by
      simpa using apply_sub_smul_of_eq_smul_dual (hf := hα 0) (hg := hα 1) hgf
    have hmemprod : r 0 * r 1 ∈ ggInduced ⊤ Bs :=
      mul_mem_ggInduced (mem_ggInduced_top_of_mem_ggAutomizer (hmem 0))
        (mem_ggInduced_top_of_mem_ggAutomizer (hmem 1))
    have htrans := ggIsTransvection_of_apply (p := 3) ι hw hf0 hfw htrans_apply
    exact (hNoTr (r 0 * r 1) hmemprod) htrans

namespace GGResLineJDatum

theorem exists_mem_inf_of_coroot
    {G : Type} [Group G] {Bs J : Subgroup G} {T : GGResLineJType}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {r : Fin T.rank → MulAut ↥Bs} {h : Fin T.rank → V}
    {α : Fin T.rank → Module.Dual (ZMod 3) V}
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hform : ∀ j w, ggLin (p := 3) ι (r j) w = w - α j w • h j)
    (hpair : ∀ i j, α i (h j) = (T.cartan i j : ZMod 3))
    (hgen : ggAutomizer J Bs = Subgroup.closure (Set.range r))
    (i : Fin T.rank) :
    ∃ e : ↥(Bs ⊓ J), ι (Additive.ofMul (Subgroup.inclusion inf_le_left e)) = h i := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα2 : α i (h i) = 2 := by
    have h2 : T.cartan i i = 2 := by
      cases T <;> fin_cases i <;> decide
    rw [hpair i i, h2]
    norm_num
  have hφJ : r i ∈ ggAutomizer J Bs := by
    rw [hgen]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have hmem := ggCoroot_mem (p := 3) (φ := r i) (hv := h i) (αv := α i)
    (by decide) hBJ ι (hform i) hα2 hφJ
  let c : ↥Bs := Additive.toMul (ι.symm (h i))
  have hcι : ι (Additive.ofMul c) = h i := by
    simp [c]
  have hcJ : (c : G) ∈ J := by
    simpa [c] using hmem
  refine ⟨⟨(c : G), Subgroup.mem_inf.mpr ⟨c.2, hcJ⟩⟩, ?_⟩
  simpa [c, Subgroup.inclusion] using hcι

end GGResLineJDatum

theorem pow_rank_le_card_inf_of_lineJDatum_three
    {G : Type} [Group G] [Finite G] {B Bs J : Subgroup G} {T : GGResLineJType}
    (hBs : GGBstar 3 B Bs)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResLineJDatum 3 Bs J T) :
    3 ^ T.rank ≤ Nat.card ↥(Bs ⊓ J) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  letI := instA
  letI := instM
  haveI hCommBs : IsMulCommutative ↥Bs := hBs.2.1.1
  letI : CommGroup ↥Bs := IsMulCommutative.instCommGroup
  let E : Subgroup G := Bs ⊓ J
  have hEle : E ≤ Bs := inf_le_left
  let incl : ↥E →* ↥Bs := Subgroup.inclusion hEle
  haveI hEea : CFSG.IsElementaryAbelian 3 ↥E := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subgroup.inclusion_injective hEle
      rw [map_mul, map_mul]
      exact mul_comm _ _
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      have hx : ((x : ↥E) : G) ^ 3 = 1 := hBs.2.1.2 ((x : ↥E) : G) (incl x).2
      simpa using hx
  letI : CommGroup ↥E := IsMulCommutative.instCommGroup
  letI : Module (ZMod 3) (Additive ↥E) := CFSG.IsElementaryAbelian.isVectorSpace 3
  let φadd : Additive ↥E →+ V := ι.toAddMonoidHom.comp (MonoidHom.toAdditive incl)
  let φ : Additive ↥E →ₗ[ZMod 3] V := φadd.toZModLinearMap 3
  let W : Submodule (ZMod 3) V := LinearMap.range φ
  have hmem : ∀ i : Fin T.rank, h i ∈ W := by
    intro i
    obtain ⟨e, he⟩ := GGResLineJDatum.exists_mem_inf_of_coroot hBJ hform hpair hgen i
    exact LinearMap.mem_range.mpr ⟨Additive.ofMul e, by simpa [φ, φadd] using he⟩
  have hrankW : T.rank ≤ Module.finrank (ZMod 3) W := by
    have hspan : Submodule.span (ZMod 3) (Set.range h) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmem i
    calc T.rank = Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) := by
          rw [finrank_span_eq_card hind, Fintype.card_fin]
      _ ≤ Module.finrank (ZMod 3) W := Submodule.finrank_mono hspan
  have hWle : Module.finrank (ZMod 3) W ≤ Module.finrank (ZMod 3) (Additive ↥E) := by
    have hW : W = LinearMap.range φ := rfl
    rw [hW]
    exact LinearMap.finrank_range_le φ
  have hrank : T.rank ≤ Module.finrank (ZMod 3) (Additive ↥E) := hrankW.trans hWle
  calc 3 ^ T.rank ≤ 3 ^ Module.finrank (ZMod 3) (Additive ↥E) :=
        Nat.pow_le_pow_iff_right (by norm_num : 1 < 3) |>.mpr hrank
    _ = Nat.card (Additive ↥E) := FiniteField.pow_finrank_eq_natCard 3 (Additive ↥E)
    _ = Nat.card ↥E := Nat.card_congr Additive.toMul

theorem card_inf_ge_nine_of_lineJDatum_B2
    {G : Type} [Group G] [Finite G] {B Bs J : Subgroup G}
    (hBs : GGBstar 3 B Bs)
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (hD : GGResLineJDatum 3 Bs J .B2) :
    9 ≤ Nat.card ↥(Bs ⊓ J) := by
  have h := pow_rank_le_card_inf_of_lineJDatum_three hBs hBJ hD
  rw [show (GGResLineJType.B2).rank = 2 from rfl] at h
  norm_num at h ⊢
  exact h

theorem card_inf_ge_twentyseven_of_lineJDatum_A2_of_split
    {G : Type} [Group G] [Finite G] {B Bs J : Subgroup G}
    (hBs : GGBstar 3 B Bs)
    (hsplit : Bs = (Bs ⊓ J) ⊔ (Bs ⊓ Subgroup.centralizer (J : Set G)))
    (hNoTr : GGNoTransvection 3 Bs)
    (hD : GGResLineJDatum 3 Bs J .A2) :
    27 ≤ Nat.card ↥(Bs ⊓ J) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, instA, instM, ι, r, h, α, hform, _hrefl, hpair, hind, hgen⟩ := hD
  letI := instA
  letI := instM
  haveI hCommBs : IsMulCommutative ↥Bs := hBs.2.1.1
  letI : CommGroup ↥Bs := IsMulCommutative.instCommGroup
  have hmem : ∀ j : Fin 2, r j ∈ ggAutomizer J Bs := by
    intro j
    rw [hgen]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hroots : LinearIndependent (ZMod 3) α :=
    linearIndependent_roots_of_lineJDatum_A2 ι hform hpair hind hmem hNoTr
  let E : Subgroup G := Bs ⊓ J
  have hEle : E ≤ Bs := inf_le_left
  let incl : ↥E →* ↥Bs := Subgroup.inclusion hEle
  haveI hEea : CFSG.IsElementaryAbelian 3 ↥E := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subgroup.inclusion_injective hEle
      rw [map_mul, map_mul]
      exact mul_comm _ _
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      have hx : ((x : ↥E) : G) ^ 3 = 1 := hBs.2.1.2 ((x : ↥E) : G) (incl x).2
      simpa using hx
  letI : CommGroup ↥E := IsMulCommutative.instCommGroup
  letI : Module (ZMod 3) (Additive ↥E) := CFSG.IsElementaryAbelian.isVectorSpace 3
  let φadd : Additive ↥E →+ V := ι.toAddMonoidHom.comp (MonoidHom.toAdditive incl)
  let φ : Additive ↥E →ₗ[ZMod 3] V := φadd.toZModLinearMap 3
  let W : Submodule (ZMod 3) V := LinearMap.range φ
  let U : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hUle : U ≤ Bs := inf_le_left
  have hsup : Bs = (Bs ⊓ J) ⊔ (Bs ⊓ Subgroup.centralizer (J : Set G)) := hsplit
  have hsup' : E.subgroupOf Bs ⊔ U.subgroupOf Bs = ⊤ := by
    apply Subgroup.map_injective Bs.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_subgroupOf_eq_of_le hEle, Subgroup.map_subgroupOf_eq_of_le hUle]
    exact hsup.symm
  have hBJ : Bs ≤ Subgroup.normalizer (J : Set G) := by
    rw [hsup]
    exact sup_le
      (fun e he => Subgroup.le_normalizer (Subgroup.mem_inf.mp he).2)
      (fun u hu => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hu).2)
  have hmemW : ∀ i : Fin 2, h i ∈ W := by
    intro i
    obtain ⟨e, he⟩ := GGResLineJDatum.exists_mem_inf_of_coroot hBJ hform hpair hgen i
    exact LinearMap.mem_range.mpr ⟨Additive.ofMul e, by simpa [φ, φadd] using he⟩
  have hspanW : Submodule.span (ZMod 3) (Set.range h) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmemW i
  suffices h : 3 ≤ Module.finrank (ZMod 3) (Additive ↥E) by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ Module.finrank (ZMod 3) (Additive ↥E) :=
          Nat.pow_le_pow_iff_right (by norm_num : 1 < 3) |>.mpr h
      _ = Nat.card (Additive ↥E) := FiniteField.pow_finrank_eq_natCard 3 (Additive ↥E)
      _ = Nat.card ↥E := Nat.card_congr Additive.toMul
  by_contra hle
  push Not at hle
  have hle2 : Module.finrank (ZMod 3) (Additive ↥E) ≤ 2 := by omega
  have hfinrankW : Module.finrank (ZMod 3) W = 2 := by
    have hge : 2 ≤ Module.finrank (ZMod 3) W := by
      calc 2 = Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) := by
            rw [finrank_span_eq_card hind, Fintype.card_fin]
            rfl
        _ ≤ Module.finrank (ZMod 3) W := Submodule.finrank_mono hspanW
    have hleW : Module.finrank (ZMod 3) W ≤ 2 := by
      calc Module.finrank (ZMod 3) W ≤ Module.finrank (ZMod 3) (Additive ↥E) := by
            rw [show W = LinearMap.range φ from rfl]
            exact LinearMap.finrank_range_le φ
        _ ≤ 2 := hle2
    omega
  have hWeq : W = Submodule.span (ZMod 3) (Set.range h) := by
    have h : Submodule.span (ZMod 3) (Set.range h) = W := by
      apply Submodule.eq_of_le_of_finrank_eq hspanW
      rw [finrank_span_eq_card hind, Fintype.card_fin, hfinrankW]
      rfl
    exact h.symm
  have hαW : ∀ w ∈ W, α (0 : Fin 2) w = α (1 : Fin 2) w := by
    intro w hw
    rw [hWeq] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have h0 := hpair (0 : Fin 2) j
      have h1 := hpair (1 : Fin 2) j
      have hrow : ((GGResLineJType.cartan .A2) (0 : Fin 2) j : ZMod 3) =
          ((GGResLineJType.cartan .A2) (1 : Fin 2) j : ZMod 3) := by
        fin_cases j <;> decide
      rw [h0, h1, hrow]
    | zero => simp
    | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
    | smul a x hx ih => simp [map_smul, ih]
  have hαU : ∀ i : Fin 2, ∀ u : ↥U,
      α i (ι (Additive.ofMul (Subgroup.inclusion hUle u))) = 0 := by
    intro i u
    have hmem_u : (Subgroup.inclusion hUle u : G) ∈ Bs ⊓ Subgroup.centralizer (J : Set G) :=
      ⟨(Subgroup.inclusion hUle u).2, (Subgroup.mem_inf.mp u.2).2⟩
    have hfix := B48Om.ggAutomizer_central_factor_fixed (Bs := Bs) (J := J)
      (φ := ⟨r i, hmem i⟩) (u := (Subgroup.inclusion hUle u : G)) hmem_u
    have hform_u := hform i (ι (Additive.ofMul (Subgroup.inclusion hUle u)))
    rw [ggLin_apply_ofMul (p := 3)] at hform_u
    have hfix' : (r i) (Subgroup.inclusion hUle u) = Subgroup.inclusion hUle u := by
      exact hfix
    rw [hfix'] at hform_u
    have hzero : α i (ι (Additive.ofMul (Subgroup.inclusion hUle u))) • h i = 0 := by
      have heq := hform_u
      have h' : ι (Additive.ofMul (Subgroup.inclusion hUle u)) -
          (ι (Additive.ofMul (Subgroup.inclusion hUle u)) -
            α i (ι (Additive.ofMul (Subgroup.inclusion hUle u))) • h i) = 0 := by
        rw [← heq, sub_self]
      rwa [sub_sub_cancel] at h'
    exact (smul_eq_zero.mp hzero).resolve_right (hind.ne_zero i)
  have hαV : α (0 : Fin 2) = α (1 : Fin 2) := by
    ext v
    let b : ↥Bs := Additive.toMul (ι.symm v)
    have hbv : ι (Additive.ofMul b) = v := by simp [b]
    rw [← hbv]
    have hbTop : b ∈ E.subgroupOf Bs ⊔ U.subgroupOf Bs := by
      rw [hsup']; exact Subgroup.mem_top _
    obtain ⟨e, heE, u, huU, heu⟩ := Subgroup.mem_sup.mp hbTop
    have he : ∃ e' : ↥E, incl e' = e := by
      exact ⟨⟨(e : G), Subgroup.mem_subgroupOf.mp heE⟩, by apply Subtype.ext; rfl⟩
    obtain ⟨e', rfl⟩ := he
    have hu : ∃ u' : ↥U, Subgroup.inclusion hUle u' = u := by
      exact ⟨⟨(u : G), Subgroup.mem_subgroupOf.mp huU⟩, by apply Subtype.ext; rfl⟩
    obtain ⟨u', rfl⟩ := hu
    have hb_eq : b = incl e' * Subgroup.inclusion hUle u' := heu.symm
    rw [hb_eq, ofMul_mul, map_add]
    have he_mem : ι (Additive.ofMul (incl e')) ∈ W := by
      exact LinearMap.mem_range.mpr ⟨Additive.ofMul e', rfl⟩
    have hU_eq : α (0 : Fin 2) (ι (Additive.ofMul (Subgroup.inclusion hUle u'))) = 0 ∧
        α (1 : Fin 2) (ι (Additive.ofMul (Subgroup.inclusion hUle u'))) = 0 :=
      ⟨hαU (0 : Fin 2) u', hαU (1 : Fin 2) u'⟩
    have he_eq := hαW (ι (Additive.ofMul (incl e'))) he_mem
    simp [map_add, he_eq, hU_eq]
  exact (by decide : (0 : Fin 2) ≠ 1) (hroots.injective hαV)

@[expose] def ggResLineJLabel : GGResLineJType → LargeEvenLabel → Prop
  | .A2, lab => (lab.tag = .A ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twA ∧ lab.rank = 2 ∧ 3 ∣ 2 ^ lab.n + 1)
  | .B2, lab => ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨ lab = ⟨.B2der, 0, 1⟩ ∨
      ((lab.tag = .A ∧ (lab.rank = 3 ∨ lab.rank = 4) ∨ lab.tag = .D ∧ lab.rank = 3) ∧
        3 ∣ 2 ^ lab.n + 1) ∨
      ((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4) ∨ lab.tag = .twD ∧ lab.rank = 3) ∧
        3 ∣ 2 ^ lab.n - 1)
  | .A3, lab => ((lab.tag = .A ∨ lab.tag = .D) ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      ((lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ 3 ∣ 2 ^ lab.n + 1)
  | .B3, lab | .C3, lab => ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3) ∨
      (lab.tag = .A ∧ (lab.rank = 5 ∨ lab.rank = 6) ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twA ∧ (lab.rank = 5 ∨ lab.rank = 6) ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twD ∧ lab.rank = 4)

theorem ggTablePRow_B2 {labJ labX : LargeEvenLabel}
    (hJ : ggResLineJLabel .B2 labJ) (hX : LargeEvenInLambda2 labX)
    (hP : GGTablePRow 3 labJ labX) :
    labX = ⟨.C, 3, labJ.n⟩ ∨
      (labX.tag = .A ∧ (labX.rank = 5 ∨ labX.rank = 6) ∧ labX.n = labJ.n ∧
        3 ∣ 2 ^ labX.n + 1) ∨
      (labX.tag = .twA ∧ (labX.rank = 5 ∨ labX.rank = 6) ∧ labX.n = labJ.n ∧
        3 ∣ 2 ^ labX.n - 1) ∨
      labX = ⟨.twD, 4, labJ.n⟩ := by
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  obtain ⟨tX, rX, nX⟩ := labX
  rcases hJ with ⟨ht, hr⟩ | hB2 | ⟨hAD, hplus⟩ | ⟨hAD, hminus⟩
  · rcases ht with rfl | rfl <;> rcases hr with rfl
    · unfold GGTablePRow at hP
      cases tX <;>
        simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
          and_false, or_false, false_or] at hP ⊢
      all_goals simp_all
    · unfold GGTablePRow at hP
      cases tX <;>
        simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
          and_false, or_false, false_or, or_true] at hP ⊢
      all_goals simp_all
  · simp only [LargeEvenLabel.mk.injEq] at hB2
    obtain ⟨rfl, rfl, rfl⟩ := hB2
    unfold GGTablePRow at hP
    cases tX <;>
      simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
        and_true, and_false, or_false, false_or] at hP ⊢
    all_goals simp_all
  · have hplus' : 3 ∣ 2 ^ nJ + 1 := hplus
    have hnot : ¬ 3 ∣ 2 ^ nJ - 1 := by
      intro hminus
      have h2 : 3 ∣ (2 ^ nJ + 1) - (2 ^ nJ - 1) := Nat.dvd_sub hplus' hminus
      have h3 : (2 ^ nJ + 1) - (2 ^ nJ - 1) = 2 := by
        have := Nat.one_le_two_pow (n := nJ)
        omega
      rw [h3] at h2
      norm_num at h2
    rcases hAD with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
    · rcases hr with rfl | rfl
      · unfold GGTablePRow at hP
        cases tX <;>
          simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
            and_false, or_false, false_or, or_true, hnot, hplus'] at hP ⊢
        all_goals simp_all
      · unfold GGTablePRow at hP
        cases tX <;>
          simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
            and_false, or_false, false_or, or_true, hnot, hplus'] at hP ⊢
        all_goals simp_all
    · rcases hr with rfl
      unfold GGTablePRow at hP
      cases tX <;>
        simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
          and_false, or_false, false_or, or_true, hnot, hplus'] at hP ⊢
      all_goals simp_all
  · have hminus' : 3 ∣ 2 ^ nJ - 1 := hminus
    have hnot : ¬ 3 ∣ 2 ^ nJ + 1 := by
      intro hplus
      have h2 : 3 ∣ (2 ^ nJ + 1) - (2 ^ nJ - 1) := Nat.dvd_sub hplus hminus'
      have h3 : (2 ^ nJ + 1) - (2 ^ nJ - 1) = 2 := by
        have := Nat.one_le_two_pow (n := nJ)
        omega
      rw [h3] at h2
      norm_num at h2
    rcases hAD with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
    · rcases hr with rfl | rfl
      · unfold GGTablePRow at hP
        cases tX <;>
          simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
            and_false, or_false, false_or, hnot, hminus'] at hP ⊢
        all_goals simp_all
      · unfold GGTablePRow at hP
        cases tX <;>
          simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
            and_false, or_false, false_or, hnot, hminus'] at hP ⊢
        all_goals simp_all
    · rcases hr with rfl
      unfold GGTablePRow at hP
      cases tX <;>
        simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and,
          and_false, or_false, false_or, hnot, hminus'] at hP ⊢
      all_goals simp_all

namespace ResJCubicBlock

theorem card_ggAutomizer_le_fortyEight_of_lineJDatum
    {G : Type} [Group G] {Bs J : Subgroup G} [Fact (Nat.Prime 3)]
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T) :
    Nat.card (ggAutomizer J Bs) ≤ 48 := by
  cases T
  · rw [ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD]
    norm_num
  · rw [ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD]
    norm_num
  · rw [ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD]
    norm_num
  · rw [ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD]
  · rw [ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD]

end ResJCubicBlock

@[expose] def GGResLineJLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], p = 3 →
    ∀ T : GGResLineJType, GGResLineJDatum p Bs J T →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel T lab ∧
        GGHasLabel lab (J ⧸ Subgroup.center J)

@[expose] def GGTorusAutNotDvdSCJ (p : ℕ) (labJ : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) (rmax bad : ℕ) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → Nat.card A ≤ p ^ rmax → GGTorusSelfCent p A →
      (∃ e ∈ A, ∃ J' : Subgroup L', CFSG.Assembly.IsComponentOf J' (ggFixSub e) ∧
        GGHasLabel labJ (J' ⧸ Subgroup.center J')) →
      ¬ bad ∣ Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)

theorem GGTorusAutCardSCr.notDvdSCJ {p r rmax bad N : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {labJ : LargeEvenLabel}
    (h : GGTorusAutCardSCr p r R I N) (hr : p ^ r ≤ p ^ 3) (hbad : ¬ bad ∣ N) :
    GGTorusAutNotDvdSCJ p labJ R I rmax bad := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 _ hsc _
  have hTB : GGTorusTBGroup p r R I L' ψ A :=
    ⟨hψ, hker, hperf, hA, hAI, hr.trans h3, h3, hsc⟩
  rw [h L' ψ A hTB]
  exact hbad

theorem GGTorusAutCardSC.notDvdSCJ {p r N rmax bad : ℕ} {labJ : LargeEvenLabel}
    {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusAutCardSC p R I r N) (hbad : ¬ bad ∣ N) :
    GGTorusAutNotDvdSCJ p labJ R I rmax bad := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 _hcard hsc _
  have hN := (h L' ψ hψ hker hperf A hA hAI h3 hsc).2
  rw [hN]
  exact hbad

@[expose] def GGPumpLineAutKnown : Prop :=
  ∀ (T : GGResLineJType) (labJ labX : LargeEvenLabel), ggResLineJLabel T labJ →
    LargeEvenInLambda2 labX → GGTablePRow 3 labJ labX →
    ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1) →
    LargeEvenLabelAll labX fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I (T.rank + 1) T.bad

theorem ggTablePRow_three_A2_split {labJ labX : LargeEvenLabel}
    (hJ : labJ.tag = .A ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n - 1)
    (hrow : GGTablePRow 3 labJ labX) (_hΛX : LargeEvenInLambda2 labX) :
    labX = ⟨.A, 3, labJ.n⟩ ∨ labX = ⟨.C, 3, labJ.n⟩ ∨ labX = ⟨.D, 3, labJ.n⟩ ∨
    labX = ⟨.twD, 4, labJ.n⟩ ∨
    (labX.tag = .twA ∧ labX.rank = 5 ∧ 2 * labX.n = labJ.n ∧ 3 ∣ 2 ^ labX.n - 1) ∨
    (labX.tag = .A ∧ (labX.rank = 5 ∨ labX.rank = 6) ∧
      2 * labX.n = labJ.n ∧ 3 ∣ 2 ^ labX.n + 1) := by
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  obtain ⟨ht, hr, _hd⟩ := hJ
  cases ht
  cases hr
  unfold GGTablePRow at hrow
  simp at hrow
  obtain ⟨-, hX⟩ := hrow
  rcases hX with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem ggTablePRow_three_A2_tw {labJ labX : LargeEvenLabel}
    (hJ : labJ.tag = .twA ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n + 1)
    (hrow : GGTablePRow 3 labJ labX) (hΛX : LargeEvenInLambda2 labX) :
    labX = ⟨.twA, 3, labJ.n⟩ ∨ labX = ⟨.C, 3, labJ.n⟩ ∨
    labX = ⟨.twD, 3, labJ.n⟩ ∨ labX = ⟨.twD, 4, labJ.n⟩ ∨
    (labX.tag = .twE6 ∧ labX.rank = 0 ∧ 3 * labX.n = labJ.n) := by
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  obtain ⟨ht, hr, _hd⟩ := hJ
  cases ht
  cases hr
  unfold GGTablePRow at hrow
  simp at hrow
  obtain ⟨-, hX⟩ := hrow
  rcases hX with h | h | ⟨hodd, h⟩ | ⟨hodd, h⟩ | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd hodd (by norm_num)
  · exact absurd hodd (by norm_num)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨htag, hn⟩ := h
    have hrank : labX.rank = 0 := by
      have hlam := hΛX.2
      rw [htag] at hlam
      simpa using hlam
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨htag, hrank, hn⟩)))

private theorem three_dvd_two_pow_add_one_of_three_mul {m n : ℕ} (hn : n = 3 * m)
    (h : 3 ∣ 2 ^ n + 1) : 3 ∣ 2 ^ m + 1 := by
  subst hn
  have h1 : (2 : ZMod 3) ^ (3 * m) = -1 := by
    have h' : ((2 ^ (3 * m) + 1 : ℕ) : ZMod 3) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod 3) 3 _).2 h
    push_cast at h'
    linear_combination h'
  rw [show 3 * m = m * 3 by ring, pow_mul] at h1
  have hx : ((2 : ZMod 3) ^ m) ^ 3 = (2 : ZMod 3) ^ m := by
    have hxall : ∀ x : ZMod 3, x ^ 3 = x := by decide
    exact hxall _
  rw [hx] at h1
  have h2 : ((2 ^ m + 1 : ℕ) : ZMod 3) = 0 := by
    push_cast
    rw [h1]
    ring
  exact (CharP.cast_eq_zero_iff (ZMod 3) 3 _).1 h2

theorem ggTablePRow_three_A2_tw_offE6 {labJ labX : LargeEvenLabel}
    (hJ : labJ.tag = .twA ∧ labJ.rank = 2 ∧ 3 ∣ 2 ^ labJ.n + 1)
    (hrow : GGTablePRow 3 labJ labX) (hΛX : LargeEvenInLambda2 labX)
    (hOff : ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1)) :
    labX = ⟨.twA, 3, labJ.n⟩ ∨ labX = ⟨.C, 3, labJ.n⟩ ∨
    labX = ⟨.twD, 3, labJ.n⟩ ∨ labX = ⟨.twD, 4, labJ.n⟩ := by
  have h := ggTablePRow_three_A2_tw hJ hrow hΛX
  rcases h with h | h | h | h | ⟨htag, _hrank, hn⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exfalso
    exact hOff ⟨htag, three_dvd_two_pow_add_one_of_three_mul hn.symm hJ.2.2⟩

@[expose] def GGPumpLineThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], p = 3 →
    GGResLeviDatum p Bs L J K ggSelI (ggTypRankLt 8) →
    ∀ T : GGResLineJType, GGResLineJDatum p Bs J T → Nat.card Bs = p ^ (T.rank + 2) →
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
    ∀ (z : G) (X : Subgroup G), GGNbr p B x D J z X → J ≤ X →
      ¬ T.bad ∣ Nat.card (ggAutomizer X Bs)

end CFSG.StandardType
