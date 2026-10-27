module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148APGLConjLeaves
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem exists_twoLocal_of_mulEquiv {X P : Type*} [Group X] [Group P] {D : Subgroup X}
    {M : Subgroup P} (φ : ↥D ≃* ↥M) {T E : Subgroup P} (hTM : T ≤ M) (hEM : E ≤ M)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hEN : E ≤ Subgroup.normalizer (T : Set P))
    (hE3 : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ T' E' : Subgroup X, T' ≤ D ∧ T' ≠ ⊥ ∧ IsPGroup 2 T' ∧ E' ≤ D ∧
      E' ≤ Subgroup.normalizer (T' : Set X) ∧ CFSG.Open.IsElemAbelian 3 E' ∧
      Nat.card E' = 9 := by
  set ψ : ↥M →* X := D.subtype.comp φ.symm.toMonoidHom with hψ
  have hψi : Function.Injective ψ := D.subtype_injective.comp φ.symm.injective
  have hψD : ∀ m : ↥M, ψ m ∈ D := fun m => (φ.symm m).2
  refine ⟨(T.subgroupOf M).map ψ, (E.subgroupOf M).map ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨m, -, rfl⟩
    exact hψD m
  · intro h
    apply hT
    rw [Subgroup.map_eq_bot_iff_of_injective _ hψi, Subgroup.subgroupOf_eq_bot] at h
    have h1 := disjoint_iff.mp h
    rwa [inf_eq_left.mpr hTM] at h1
  · exact (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).map ψ
  · rintro _ ⟨m, -, rfl⟩
    exact hψD m
  · refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map ψ)
    intro e he
    rw [Subgroup.mem_subgroupOf] at he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hEN he)) h
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have ha'' : ((a' : ↥M) : P) ∈ E := ha'
      have hb'' : ((b' : ↥M) : P) ∈ E := hb'
      exact congrArg Subtype.val (hE3.1.is_comm.comm ⟨_, ha''⟩ ⟨_, hb''⟩)
    · obtain ⟨m, hm, rfl⟩ := hx
      have hm' : ((m : ↥M) : P) ∈ E := hm
      rw [← map_pow]
      have : m ^ 3 = 1 := Subtype.ext (by simpa using hE3.2 _ hm')
      rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hψi,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE9]

theorem exists_projImage_model {L : Type} [Group L] {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hL : Sec4.IsoLThreePi L p f) :
    ∃ (π : Bool) (K : Type) (_ : Field K) (_ : CharP K p), Sec4.PiField π p f K ∧
      Sec4.ModThree π (p ^ f) ∧ Nonempty (L ≃* projImage (slPi π 3 (p ^ f) K)) := by
  have hp : p.Prime := Fact.out
  rcases hL with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · refine ⟨true, GaloisField p f, inferInstance, inferInstance, ⟨hp, hf, ?_⟩, hq3,
      ⟨φ.trans (MulEquiv.subgroupCongr (projSL_eq_projImage _ _))⟩⟩
    rw [GaloisField.card p f (by omega)]
    rfl
  · refine ⟨false, GaloisField p (2 * f), inferInstance, inferInstance, ⟨hp, hf, ?_⟩, hq3,
      ⟨φ.trans (MulEquiv.subgroupCongr (projSU_eq_projImage _ _))⟩⟩
    rw [GaloisField.card p (2 * f) (by omega)]
    change p ^ (2 * f) = (p ^ f) ^ 2
    rw [← pow_mul, mul_comm]

section PGL

variable {K : Type} [Field K]

omit [Field K] in
theorem mem_normalizer_of_map_le {Q : Type*} [Group Q] [Finite Q] {N : Subgroup Q} {g : Q}
    (hN : N.map (MulAut.conj g).toMonoidHom ≤ N) : g ∈ Subgroup.normalizer (N : Set Q) := by
  have heq : N.map (MulAut.conj g).toMonoidHom = N :=
    Subgroup.eq_of_le_of_card_ge hN (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

omit [Field K] in
theorem isPGroup_zpowers {Q : Type*} [Group Q] {p : ℕ} {g : Q} (hg : g ^ p = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  intro x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm k, _root_.zpow_mul, zpow_natCast, hg, _root_.one_zpow]

theorem mk_mem_projImage {H : Subgroup (GL (Fin 3) K)} {g : GL (Fin 3) K} (hg : g ∈ H) :
    pmk g ∈ projImage H :=
  ⟨g, hg, rfl⟩

theorem finite_pgl [Finite K] : Finite (ProjGenLinGroup (Fin 3) K) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

theorem mk_diagUnits_ne_one {a b c : Kˣ} (hab : a ≠ b) :
    pmk (diagUnits a b c : GL (Fin 3) K) ≠ 1 := by
  intro h
  rw [← map_one pmk, ← Sec12.KS128Move.diagUnits_one] at h
  obtain ⟨u, h1, h2, -⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
  apply hab
  have h12 : a * u = b * u := h1.trans h2.symm
  exact mul_right_cancel h12

theorem mk_diagUnits_ne_one' {a b c : Kˣ} (hbc : b ≠ c) :
    pmk (diagUnits a b c : GL (Fin 3) K) ≠ 1 := by
  intro h
  rw [← map_one pmk, ← Sec12.KS128Move.diagUnits_one] at h
  obtain ⟨u, -, h2, h3⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
  apply hbc
  have h23 : b * u = c * u := h2.trans h3.symm
  exact mul_right_cancel h23

theorem mk_diagTau_facts {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    pmk (diagTau hτ) ^ 3 = 1 ∧ pmk (diagTau hτ) ≠ 1 := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  refine ⟨by rw [← map_pow, diagTau_pow_three hτ, map_one], ?_⟩
  rw [diagTau_eq_diagUnits hτ hτ0]
  refine mk_diagUnits_ne_one fun h => hτ1 ?_
  have h' := congrArg (fun u : Kˣ => (u : K)) h
  simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at h'
  have h2 : τ * (τ - 1) = 0 := by linear_combination -h'
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hτ0
  · linear_combination h3

end PGL

section Odd

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def signOne (K : Type) [Field K] : GL (Fin 3) K := diagUnits (-1) (-1) 1

@[expose] def signTwo (K : Type) [Field K] : GL (Fin 3) K := diagUnits 1 (-1) (-1)

theorem signOne_eq_torusHom : signOne K = torusHom ((-1 : Kˣ), (-1 : Kˣ)) := by
  change diagUnits (-1) (-1) 1 = diagUnits (-1) (-1) ((-1) * (-1))⁻¹
  congr 1
  simp

theorem signTwo_eq_torusHom : signTwo K = torusHom ((1 : Kˣ), (-1 : Kˣ)) := by
  change diagUnits 1 (-1) (-1) = diagUnits 1 (-1) (1 * (-1))⁻¹
  congr 1
  simp

theorem sign_mem_slPi (hK : PiField π p f K) (hodd : Odd (p ^ f)) :
    signOne K ∈ slPi π 3 (p ^ f) K ∧ signTwo K ∈ slPi π 3 (p ^ f) K := by
  have hm : (-1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    rw [mem_rootsOfUnity]
    have he : Even (qSubPi π (p ^ f)) := by
      cases π
      · exact hodd.add_one
      · exact Nat.Odd.sub_odd hodd odd_one
    exact he.neg_one_pow
  have h1 : (1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := one_mem _
  rw [signOne_eq_torusHom, signTwo_eq_torusHom]
  exact ⟨torusHom_mem_slPi hK hm hm, torusHom_mem_slPi hK h1 hm⟩

theorem signOne_mul_signTwo :
    signOne K * signTwo K = (diagUnits (-1) 1 (-1) : GL (Fin 3) K) := by
  rw [signOne, signTwo, diagUnits_mul]
  congr 1 <;> simp

theorem signOne_sq : signOne K ^ 2 = 1 := by
  rw [signOne, Sec12.KS128Move.diagUnits_pow]
  simp [Sec12.KS128Move.diagUnits_one]

theorem signTwo_sq : signTwo K ^ 2 = 1 := by
  rw [signTwo, Sec12.KS128Move.diagUnits_pow]
  simp [Sec12.KS128Move.diagUnits_one]

theorem exists_twoLocal_odd [CharP K p] (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hp2 : p ≠ 2) :
    ∃ T E : Subgroup (ProjGenLinGroup (Fin 3) K), T ≤ projImage (slPi π 3 (p ^ f) K) ∧
      E ≤ projImage (slPi π 3 (p ^ f) K) ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set (ProjGenLinGroup (Fin 3) K)) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Finite K := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := finite_pgl
  have hp : p.Prime := hK.prime
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hneg : (-1 : Kˣ) ≠ 1 := by
    intro h
    have h' : (-1 : K) = 1 := by simpa using congrArg (fun u : Kˣ => (u : K)) h
    have h2 : ((2 : ℕ) : K) = 0 := by
      push_cast
      linear_combination -h'
    rw [CharP.cast_eq_zero_iff K p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨hs1, hs2⟩ := sign_mem_slPi hK hodd
  set t₁ := pmk (signOne K) with ht₁
  set t₂ := pmk (signTwo K) with ht₂
  set d := pmk (diagTau hτ) with hd
  set c := pmk (cycThree : GL (Fin 3) K) with hc
  set T : Subgroup (ProjGenLinGroup (Fin 3) K) := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂
    with hT
  set E : Subgroup (ProjGenLinGroup (Fin 3) K) := Subgroup.zpowers d ⊔ Subgroup.zpowers c
    with hE
  have ht₁2 : t₁ ^ 2 = 1 := by rw [ht₁, ← map_pow, signOne_sq, map_one]
  have ht₂2 : t₂ ^ 2 = 1 := by rw [ht₂, ← map_pow, signTwo_sq, map_one]
  have ht12 : t₁ * t₂ = t₂ * t₁ := by
    rw [ht₁, ht₂, ← map_mul, ← map_mul, signOne, signTwo, Sec12.KS128Move.diagUnits_comm]
  obtain ⟨hd3, hd1⟩ := mk_diagTau_facts hτ hτ1
  have hc3 : c ^ 3 = 1 := by rw [hc, ← map_pow, RonanK432.L3Hard.cycThree_cube, map_one]
  have hdc : c * d = d * c := RonanK432.L3Hard.mk_commute_cycThree_diagTau hτ
  have hcd : c ∉ Subgroup.zpowers d := RonanK432.L3Hard.mk_cycThree_notMem_zpowers hτ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hconj_d : ∀ s : GL (Fin 3) K, (∃ a b e : Kˣ, s = diagUnits a b e) →
      d * pmk s * d⁻¹ = pmk s := by
    rintro s ⟨a, b, e, rfl⟩
    rw [hd, ← map_inv, ← map_mul, ← map_mul, diagTau_eq_diagUnits hτ hτ0,
      Sec12.KS128Move.diagUnits_comm, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_c₁ : c * t₁ * c⁻¹ = t₂ := by
    rw [hc, ht₁, ht₂, ← map_inv, ← map_mul, ← map_mul, signOne,
      cycThree_conj_diagUnits, signTwo]
  have hconj_c₂ : c * t₂ * c⁻¹ = t₁ * t₂ := by
    rw [hc, ht₁, ht₂, ← map_inv, ← map_mul, ← map_mul, ← map_mul, signOne_mul_signTwo, signTwo,
      cycThree_conj_diagUnits]
  have hTN : ∀ g : ProjGenLinGroup (Fin 3) K, g * t₁ * g⁻¹ ∈ T → g * t₂ * g⁻¹ ∈ T →
      g ∈ Subgroup.normalizer (T : Set (ProjGenLinGroup (Fin 3) K)) := by
    intro g h1 h2
    refine mem_normalizer_of_map_le ?_
    rw [hT, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2)
  have ht₁T : t₁ ∈ T := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have ht₂T : t₂ ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine ⟨T, E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sup_le (Subgroup.zpowers_le.mpr (mk_mem_projImage hs1))
      (Subgroup.zpowers_le.mpr (mk_mem_projImage hs2))
  · exact sup_le (Subgroup.zpowers_le.mpr (mk_mem_projImage (diagTau_mem_slPi hπ hq' hτ)))
      (Subgroup.zpowers_le.mpr (mk_mem_projImage (cycThree_mem_slPi hπ)))
  · intro h0
    have h1 : t₁ ∈ (⊥ : Subgroup (ProjGenLinGroup (Fin 3) K)) := h0 ▸ ht₁T
    rw [Subgroup.mem_bot, ht₁, signOne] at h1
    exact mk_diagUnits_ne_one' hneg h1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers ht₁2) (isPGroup_zpowers ht₂2) ?_
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute t₂ t₁ from ht12.symm) j)
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · refine hTN d ?_ ?_
      · rw [ht₁, hconj_d (signOne K) ⟨-1, -1, 1, rfl⟩]
        exact ht₁T
      · rw [ht₂, hconj_d (signTwo K) ⟨1, -1, -1, rfl⟩]
        exact ht₂T
    · refine hTN c ?_ ?_
      · rw [hconj_c₁]
        exact ht₂T
      · rw [hconj_c₂]
        exact T.mul_mem ht₁T ht₂T
  · exact Sec13.isElemAbelian_zpowers_sup hd3 hc3 hdc.symm
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Sec4.card_zpowers_sup_zpowers hc3 (orderOf_eq_prime hd3 hd1) hcd hdc

end Odd

section Even

variable {K : Type} [Field K] {f : ℕ}

@[expose] def rootGL (t : K) : GL (Fin 3) K :=
  ⟨!![1, t, 0; 0, 1, 0; 0, 0, 1], !![1, -t, 0; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem coe_rootGL (t : K) :
    ((rootGL t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, t, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem rootGL_add (s t : K) : rootGL (s + t) = rootGL s * rootGL t := by
  apply Units.ext
  rw [Units.val_mul, coe_rootGL, coe_rootGL, coe_rootGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, add_comm]

theorem rootGL_zero : rootGL (0 : K) = 1 := by
  apply Units.ext
  rw [coe_rootGL, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def rootHom (K : Type) [Field K] : Multiplicative K →* GL (Fin 3) K where
  toFun t := rootGL t.toAdd
  map_one' := rootGL_zero
  map_mul' s t := rootGL_add s.toAdd t.toAdd

theorem diagUnits_conj_rootGL (a b c : Kˣ) (t : K) :
    diagUnits a b c * rootGL t * (diagUnits a b c)⁻¹ =
      rootGL ((a : K) * ((b⁻¹ : Kˣ) : K) * t) := by
  rw [Sec12.KS128Move.diagUnits_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits_eq, coe_diagUnits_eq, coe_rootGL, coe_rootGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> ring

theorem rootGL_mem_slPi (q : ℕ) (t : K) : rootGL t ∈ slPi true 3 q K := by
  rw [mem_slPi_true, coe_rootGL, det_fin_three]
  simp

theorem exists_twoLocal_even [CharP K 2] (hK : PiField true 2 f K) (h9 : 9 ∣ 2 ^ f - 1) :
    ∃ T E : Subgroup (ProjGenLinGroup (Fin 3) K), T ≤ projImage (slPi true 3 (2 ^ f) K) ∧
      E ≤ projImage (slPi true 3 (2 ^ f) K) ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set (ProjGenLinGroup (Fin 3) K)) ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Finite K := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := finite_pgl
  have hcard : Nat.card K = 2 ^ f := hK.card
  have hq : ModThree true (2 ^ f) := by
    change 2 ^ f % 3 = 1
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h9' : 9 ∣ Nat.card K - 1 := by rw [hcard]; exact h9
  have hμ : Nat.card (rootsOfUnity 9 K) = 9 :=
    CFSG.RankThree.Chevalley.card_rootsOfUnity_of_dvd_card_sub_one h9'
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity 9 K)
  rw [hμ] at hg
  set ζ : Kˣ := (g : Kˣ) with hζ
  have hζ9 : ζ ^ 9 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have hζ3 : ζ ^ 3 ≠ 1 := by
    intro h
    have h' : g ^ 3 = 1 := Subtype.ext (by simpa using h)
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hg] at this
    norm_num at this
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  set h₁ : GL (Fin 3) K := diagUnits τu (τu ^ 2) 1 with hh₁
  set h₂ : GL (Fin 3) K := diagUnits ζ ζ (ζ * ζ)⁻¹ with hh₂
  have hdτ : diagTau hτ = h₁ := diagTau_eq_diagUnits hτ hτ0
  have hτu3 : τu ^ 3 = 1 := Units.ext (by simpa [hτu] using hτ)
  have hτu1 : τu ≠ 1 := fun h => hτ1 (by simpa [hτu] using congrArg Units.val h)
  have hh₁S : h₁ ∈ slPi true 3 (2 ^ f) K := by
    rw [← hdτ]
    exact diagTau_mem_slPi (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hτ
  have hh₂S : h₂ ∈ slPi true 3 (2 ^ f) K :=
    torusHom_mem_slPi (a := ζ) (b := ζ) hK (mem_rootsOfUnity_of_card hcard ζ)
      (mem_rootsOfUnity_of_card hcard ζ)
  set d := pmk h₁ with hd
  set e := pmk h₂ with he
  have hd3 : d ^ 3 = 1 := by
    rw [hd, ← hdτ]
    exact (mk_diagTau_facts hτ hτ1).1
  have hd1 : d ≠ 1 := by
    rw [hd, ← hdτ]
    exact (mk_diagTau_facts hτ hτ1).2
  have he3 : e ^ 3 = 1 := by
    rw [he, ← map_pow, hh₂, Sec12.KS128Move.diagUnits_pow]
    have hc : ((ζ * ζ)⁻¹) ^ 3 = ζ ^ 3 := by
      rw [inv_pow, inv_eq_iff_mul_eq_one]
      calc (ζ * ζ) ^ 3 * ζ ^ 3 = ζ ^ 9 := by rw [mul_pow, ← pow_add, ← pow_add]
        _ = 1 := hζ9
    rw [hc, ← Sec12.KS128Move.scalar_eq_diagUnits, ProjGenLinGroup.mk_scalar]
  have hde : d * e = e * d := by
    rw [hd, he, ← map_mul, ← map_mul, hh₁, hh₂, Sec12.KS128Move.diagUnits_comm]
  have hed : e ∉ Subgroup.zpowers d := by
    intro hmem
    rcases RonanK432.mem_zpowers_cases_of_pow_three hd3 hmem with h | h | h
    · rw [he, ← map_one pmk, ← Sec12.KS128Move.diagUnits_one, hh₂] at h
      obtain ⟨u, h1, -, h3⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
      apply hζ3
      have hu : u = ζ⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [hu] at h3
      calc ζ ^ 3 = ((ζ * ζ)⁻¹ * ζ⁻¹)⁻¹ := by group
        _ = 1 := by rw [h3, inv_one]
    · rw [he, hd, hh₂, hh₁] at h
      obtain ⟨u, h1, h2, -⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
      apply hτu1
      have h12 : τu = τu ^ 2 := h1.symm.trans h2
      have h' : τu * τu = τu * 1 := by rw [mul_one, ← pow_two, ← h12]
      exact mul_left_cancel h'
    · rw [he, hd, ← map_inv, hh₂, hh₁, Sec12.KS128Move.diagUnits_inv] at h
      obtain ⟨u, h1, h2, -⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
      apply hτu1
      have h12 : τu⁻¹ = (τu ^ 2)⁻¹ := h1.symm.trans h2
      have h12' : τu = τu ^ 2 := inv_injective h12
      have h' : τu * τu = τu * 1 := by rw [mul_one, ← pow_two, ← h12']
      exact mul_left_cancel h'
  set T : Subgroup (ProjGenLinGroup (Fin 3) K) :=
    (MonoidHom.comp (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _) (rootHom K)).range with hT
  have hmemT : ∀ t : K, pmk (rootGL t) ∈ T := fun t => ⟨Multiplicative.ofAdd t, rfl⟩
  have hTN : ∀ a b c : Kˣ, pmk (diagUnits a b c : GL (Fin 3) K) ∈
      Subgroup.normalizer (T : Set (ProjGenLinGroup (Fin 3) K)) := by
    intro a b c
    refine mem_normalizer_of_map_le ?_
    rintro _ ⟨x, ⟨t, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
      Function.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    change pmk (diagUnits a b c * rootGL t.toAdd * (diagUnits a b c)⁻¹) ∈ T
    rw [diagUnits_conj_rootGL]
    exact hmemT _
  refine ⟨T, Subgroup.zpowers d ⊔ Subgroup.zpowers e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact mk_mem_projImage (rootGL_mem_slPi _ _)
  · exact sup_le (Subgroup.zpowers_le.mpr (mk_mem_projImage hh₁S))
      (Subgroup.zpowers_le.mpr (mk_mem_projImage hh₂S))
  · intro h0
    have h1 : pmk (rootGL (1 : K)) ∈ (⊥ : Subgroup (ProjGenLinGroup (Fin 3) K)) :=
      h0 ▸ hmemT 1
    rw [Subgroup.mem_bot, ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨u, hu⟩ := h1
    have e01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) hu
    simp [coe_rootGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e01
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK2 : IsPGroup 2 (Multiplicative K) := by
      intro x
      refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [pow_one, toAdd_pow, toAdd_one, nsmul_eq_mul]
      push_cast
      rw [h2, zero_mul]
    rw [hT, MonoidHom.range_eq_map]
    exact (hK2.of_equiv Subgroup.topEquiv.symm).map _
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact hTN _ _ _
    · exact hTN _ _ _
  · exact Sec13.isElemAbelian_zpowers_sup hd3 he3 hde
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Sec4.card_zpowers_sup_zpowers he3 (orderOf_eq_prime hd3 hd1) hed hde.symm

end Even

theorem kF148L3TwoLocal : Ronan148A.KF148L3TwoLocal := by
  intro X _ _ D p f _ hf hD hpq
  obtain ⟨π, K, _, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model hf hD
  by_cases hp2 : p = 2
  · subst hp2
    have h9 : 9 ∣ 2 ^ f - 1 := hpq.resolve_left (fun h => h rfl)
    have hπ : π = true := by
      cases π
      · exfalso
        have h := hq
        change 2 ^ f % 3 = 2 at h
        have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
      · rfl
    subst hπ
    obtain ⟨T, E, hTM, hEM, hT, hT2, hEN, hE3, hE9⟩ := exists_twoLocal_even hK h9
    exact exists_twoLocal_of_mulEquiv φ hTM hEM hT hT2 hEN hE3 hE9
  · obtain ⟨T, E, hTM, hEM, hT, hT2, hEN, hE3, hE9⟩ := exists_twoLocal_odd hK hq hp2
    exact exists_twoLocal_of_mulEquiv φ hTM hEM hT hT2 hEN hE3 hE9

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
