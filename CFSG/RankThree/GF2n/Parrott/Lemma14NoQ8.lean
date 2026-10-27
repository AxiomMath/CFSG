module

public import CFSG.RankThree.GF2n.Parrott.Lemma14
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import CFSG.RankThree.GF2n.Parrott.SpinRigidityBridge
public import CFSG.GroupTheory.CentralizerSylowFusion
import all CFSG.RankThree.GF2n.Parrott.Lemma14
import all CFSG.Quasithin.Recognition.U33Defs
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.SylowIntersectionControl.Basic
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.FixDimConj
public import CFSG.RankThree.GF2n.Parrott.Parrott77Lemma6
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.RankThree.GF2n.Parrott.Section2Cases
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid

local notation "P45" => Equiv.Perm (Fin 45)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)

private def tU : List ℕ := [0, 1, 2, 9, 10, 11, 12, 13, 14, 3, 4, 5, 6, 7, 8, 15, 16, 17, 18, 19,
  20, 21, 22, 23, 24, 35, 44, 42, 43, 38, 36, 37, 41, 39, 40, 25, 30, 31, 29, 33, 34, 32, 27, 28,
  26]

private def tV : List ℕ := [0, 1, 2, 6, 8, 7, 3, 5, 4, 12, 14, 13, 9, 11, 10, 15, 16, 22, 19, 18,
  24, 21, 17, 23, 20, 35, 36, 42, 39, 38, 44, 41, 37, 43, 40, 25, 26, 32, 29, 28, 34, 31, 27, 33,
  30]

private def tT : List ℕ := [0, 2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 15, 16, 19, 22, 17,
  20, 23, 18, 21, 24, 25, 26, 29, 32, 27, 30, 33, 28, 31, 34, 35, 36, 39, 42, 37, 40, 43, 38, 41,
  44]

private def tA1 : List ℕ := [0, 12, 9, 23, 43, 33, 21, 41, 31, 1, 11, 13, 2, 14, 10, 16, 15, 38,
  29, 42, 24, 3, 27, 6, 20, 26, 25, 18, 39, 22, 34, 5, 37, 8, 30, 36, 35, 28, 19, 32, 44, 4, 17, 7,
  40]

private def tB1 : List ℕ := [0, 14, 11, 39, 29, 19, 37, 27, 17, 10, 12, 1, 13, 9, 2, 24, 20, 5, 41,
  8, 16, 32, 43, 28, 15, 34, 30, 4, 21, 7, 26, 42, 23, 38, 25, 44, 40, 3, 31, 6, 36, 22, 33, 18,
  35]

private def tA2 : List ℕ := [0, 6, 3, 1, 5, 7, 2, 8, 4, 23, 28, 39, 21, 32, 37, 16, 15, 29, 38, 27,
  24, 9, 42, 12, 20, 30, 34, 17, 13, 19, 25, 43, 10, 41, 26, 44, 40, 11, 22, 14, 36, 31, 18, 33,
  35]

private def tB2 : List ℕ := [0, 8, 5, 4, 6, 1, 7, 3, 2, 33, 38, 19, 31, 42, 17, 24, 20, 11, 32, 14,
  16, 41, 28, 43, 15, 26, 25, 39, 18, 37, 34, 9, 22, 12, 30, 40, 44, 27, 13, 29, 35, 23, 10, 21,
  36]

private theorem permTab_u : permTab u = tU := by decide +kernel

private theorem permTab_v : permTab v = tV := by decide +kernel

private theorem permTab_t : permTab t = tT := by decide +kernel

private theorem permTab_alpha1 : permTab alpha1 = tA1 := by decide +kernel

private theorem permTab_beta1 : permTab beta1 = tB1 := by decide +kernel

private theorem permTab_alpha2 : permTab alpha2 = tA2 := by decide +kernel

private theorem permTab_beta2 : permTab beta2 = tB2 := by decide +kernel

private def prodSpanT : List (List ℕ) → List (List ℕ)
  | [] => [tone]
  | g :: gs => prodSpanT gs ++ (prodSpanT gs).map (tcomp g)

private theorem map_permTab_prodSpan :
    ∀ l : List P45, (prodSpan l).map permTab = prodSpanT (l.map permTab)
  | [] => by simp [prodSpan, prodSpanT, permTab_one]
  | g :: gs => by
    simp only [prodSpan, prodSpanT, List.map_append, List.map_map, List.map_cons,
      ← map_permTab_prodSpan gs]
    congr 1
    apply List.map_congr_left
    intro p _
    simp [permTab_mul]

private def t0T (_ : Unit := ()) : List (List ℕ) := prodSpanT [tU, tV, tT, tA1, tB1, tA2, tB2]

private theorem map_permTab_T0list : (T0list ()).map permTab = t0T () := by
  rw [T0list, tabList_eq, tabList_eq, map_permTab_prodSpan]
  simp [t0T, permTab_u, permTab_v, permTab_t, permTab_alpha1, permTab_beta1, permTab_alpha2,
    permTab_beta2]

private def tW (_ : Unit := ()) : List ℕ := tcomp tA1 tA2

private def cWT (_ : Unit := ()) : List (List ℕ) :=
  (t0T ()).filter fun a => tcomp a (tW ()) == tcomp (tW ()) a

private theorem length_cWT : (cWT ()).length = 64 := by decide +kernel

private def noQ8Check (_ : Unit := ()) : Bool :=
  let L := ((cWT ()).map fun a => (a, tcomp a a)).filter fun p => !(p.2 == tone)
  L.all fun p => L.all fun q => !(q.2 == p.2) || !(tcomp (tcomp p.1 q.1) (tcomp p.1 q.1) == p.2)

private theorem noQ8Check_eq : noQ8Check () = true := by decide +kernel

private theorem noQ8_tables {p q : List ℕ} (hp : p ∈ cWT ()) (hq : q ∈ cWT ())
    (hp1 : tcomp p p ≠ tone) (hqp : tcomp q q = tcomp p p) :
    tcomp (tcomp p q) (tcomp p q) ≠ tcomp p p := by
  have h := noQ8Check_eq
  simp only [noQ8Check, List.all_eq_true] at h
  have hmem : ∀ r ∈ cWT (), tcomp r r ≠ tone →
      (r, tcomp r r) ∈ ((cWT ()).map fun a => (a, tcomp a a)).filter
        fun p => !(p.2 == tone) := by
    intro r hr hr1
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    simpa using hr1
  have h2 := h _ (hmem p hp hp1) _ (hmem q hq (hqp ▸ hp1))
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h2
  rcases h2 with h2 | h2
  · exact absurd hqp h2
  · exact h2

private def tBeta : List ℕ := [15, 35, 25, 9, 11, 10, 3, 5, 4, 12, 14, 13, 6, 8, 7, 0, 16, 44, 30,
  26, 24, 40, 36, 34, 20, 1, 17, 42, 31, 27, 22, 41, 37, 32, 21, 2, 18, 43, 29, 28, 23, 39, 38, 33,
  19]

private theorem permTab_beta : permTab beta = tBeta := by decide +kernel

private theorem tab_conj_gA :
    tcomp (tcomp tU tT) (tcomp (tcomp tA1 tBeta) tB1) =
      tcomp (tcomp (tcomp tA1 tBeta) tB1) (tW ()) := by
  decide +kernel

private theorem pauli_sq_eq :
    (⟨1, 1, 0⟩ : CFSG.Quasithin.Z4StarQ8Model) * ⟨1, 1, 0⟩ = ⟨1, 0, 1⟩ * ⟨1, 0, 1⟩ := by
  decide +kernel

private theorem pauli_mul_sq_eq :
    (⟨1, 1, 0⟩ : CFSG.Quasithin.Z4StarQ8Model) * ⟨1, 0, 1⟩ * (⟨1, 1, 0⟩ * ⟨1, 0, 1⟩) =
      ⟨1, 1, 0⟩ * ⟨1, 1, 0⟩ := by
  decide +kernel

private theorem pauli_sq_ne_one :
    (⟨1, 1, 0⟩ : CFSG.Quasithin.Z4StarQ8Model) * ⟨1, 1, 0⟩ ≠ 1 := by
  decide +kernel


set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)

private def gA : A45 := a1A * bA * b1A

private theorem mul_gA : (uA * tA) * gA = gA * (a1A * a2A) := by
  apply eq_of_permTab_eq
  simp only [gA, permTab_coe_mul]
  rw [permTab_u, permTab_t, permTab_alpha1, permTab_beta, permTab_beta1, permTab_alpha2]
  exact tab_conj_gA

private theorem permTab_w : permTab ((a1A * a2A : A45) : P45) = tW () := by
  rw [permTab_coe_mul]
  change tcomp (permTab alpha1) (permTab alpha2) = tW ()
  rw [permTab_alpha1, permTab_alpha2]
  rfl

private theorem card_centralizer_w :
    Nat.card (Subgroup.centralizer ({a1A * a2A} : Set A45)) = 192 := by
  have hconj : IsConj (uA * tA) (a1A * a2A) := isConj_iff.mpr ⟨gA⁻¹, by
    rw [mul_assoc, inv_inv, mul_gA, ← mul_assoc, inv_mul_cancel, one_mul]⟩
  rw [← CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj hconj]
  exact qa45_involution_centralizers.2.1

private theorem mem_inf_centralizer_w_iff (x : A45) :
    x ∈ sylowTwoQA45 ⊓ Subgroup.centralizer ({a1A * a2A} : Set A45) ↔
      permTab (x : P45) ∈ cWT () := by
  set w : A45 := a1A * a2A with hw
  have hwT : permTab (w : P45) = tW () := permTab_w
  have hcomm : x * w = w * x ↔
      (tcomp (permTab (x : P45)) (tW ()) == tcomp (tW ()) (permTab (x : P45))) = true := by
    rw [beq_iff_eq, ← hwT, ← permTab_coe_mul, ← permTab_coe_mul]
    exact ⟨fun h => by rw [h], fun h => eq_of_permTab_eq h⟩
  rw [Subgroup.mem_inf, mem_sylowTwoQA45_iff, Subgroup.mem_centralizer_singleton_iff, hcomm, cWT,
    List.mem_filter, ← map_permTab_T0list]
  constructor
  · rintro ⟨hx, hxw⟩
    exact ⟨List.mem_map.mpr ⟨_, hx, rfl⟩, hxw⟩
  · rintro ⟨hx, hxw⟩
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
    rw [permTab_injective hpx] at hp
    exact ⟨hp, hxw⟩

private theorem card_inf_centralizer_w :
    Nat.card (sylowTwoQA45 ⊓ Subgroup.centralizer ({a1A * a2A} : Set A45) : Subgroup A45) =
      64 := by
  classical
  set P := sylowTwoQA45 ⊓ Subgroup.centralizer ({a1A * a2A} : Set A45) with hP
  have hnd : (cWT ()).Nodup := by
    have h : (T0list ()).Nodup := Certificates.certificate946017.t0_group.nodup
    rw [cWT, ← map_permTab_T0list]
    exact (h.map permTab_injective).filter _
  have hA : ∀ q ∈ cWT (), ∃ x : A45, permTab (x : P45) = q := by
    intro q hq
    have hq' := (List.mem_filter.mp hq).1
    rw [← map_permTab_T0list] at hq'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
    exact ⟨⟨p, Certificates.certificate946017.t0_group.mem_A hp⟩, rfl⟩
  have hinj : Function.Injective fun x : P => permTab ((x : A45) : P45) :=
    fun x y h => Subtype.ext (eq_of_permTab_eq h)
  have hrange : Set.range (fun x : P => permTab ((x : A45) : P45)) =
      ((cWT ()).toFinset : Set (List ℕ)) := by
    ext q
    rw [Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_inf_centralizer_w_iff (x : A45)).mp x.2
    · intro hq
      obtain ⟨x, hx⟩ := hA q hq
      exact ⟨⟨x, (mem_inf_centralizer_w_iff x).mpr (hx ▸ hq)⟩, hx⟩
  rw [← Nat.card_range_of_injective hinj, hrange, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd, length_cWT]

private theorem isSylowOf_inf_centralizer_w :
    IsSylowOf 2 (sylowTwoQA45 ⊓ Subgroup.centralizer ({a1A * a2A} : Set A45))
      (Subgroup.centralizer ({a1A * a2A} : Set A45)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card inf_le_right ?_
  rw [card_inf_centralizer_w, card_centralizer_w]
  have h : (192 : ℕ) = 2 ^ 6 * 3 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  norm_num

theorem qa45_sq_eq_one_of_le_centralizer_ut {L : Subgroup A45}
    (hL : L ≤ Subgroup.centralizer ({uA * tA} : Set A45)) (hL2 : IsPGroup 2 L)
    {a b : A45} (ha : a ∈ L) (hb : b ∈ L) (hab : a * a = b * b)
    (hab' : (a * b) * (a * b) = a * a) :
    a * a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({a1A * a2A} : Set A45) with hC
  set L' := L.map (MulAut.conj gA⁻¹).toMonoidHom with hL'
  have hL'C : L' ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    have hxc := Subgroup.mem_centralizer_singleton_iff.mp (hL hx)
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have hw : a1A * a2A = gA⁻¹ * (uA * tA) * gA := by
      rw [mul_assoc, mul_gA, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hw]
    calc gA⁻¹ * x * gA * (gA⁻¹ * (uA * tA) * gA) = gA⁻¹ * (x * (uA * tA)) * gA := by group
      _ = gA⁻¹ * ((uA * tA) * x) * gA := by rw [hxc]
      _ = gA⁻¹ * (uA * tA) * gA * (gA⁻¹ * x * gA) := by group
  have hL'2 : IsPGroup 2 L' := hL2.map _
  obtain ⟨Q, hLQ⟩ := (hL'2.comap_subtype : IsPGroup 2 (L'.subgroupOf C)).exists_le_sylow
  have hSsyl : IsSylowOf 2 ((Q : Subgroup C).map C.subtype) C := ⟨Q, rfl⟩
  have hL'S : L' ≤ (Q : Subgroup C).map C.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hL'C]
    exact Subgroup.map_mono hLQ
  obtain ⟨k, -, hk⟩ := isSylowOf_inf_centralizer_w.exists_mem_conj hSsyl
  let φ : A45 ≃* A45 := MulAut.conj (k⁻¹ * gA⁻¹)
  have hφ : ∀ x ∈ L, φ x ∈ sylowTwoQA45 ⊓ C := by
    intro x hx
    have h1 := (hk _).mp (hL'S ⟨x, hx, rfl⟩)
    have e : k⁻¹ * ((MulAut.conj gA⁻¹).toMonoidHom x) * k = φ x := by
      simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [e] at h1
  have hpa := (mem_inf_centralizer_w_iff (φ a)).mp (hφ a ha)
  have hpb := (mem_inf_centralizer_w_iff (φ b)).mp (hφ b hb)
  by_contra h1
  have hA1 : φ a * φ a ≠ 1 := by
    rw [← map_mul]
    exact fun h => h1 (φ.injective (h.trans (map_one φ).symm))
  have htab1 : tcomp (permTab (φ a : P45)) (permTab (φ a : P45)) ≠ tone := by
    rw [← permTab_coe_mul, ← permTab_coe_one]
    exact fun h => hA1 (eq_of_permTab_eq h)
  have htab2 : tcomp (permTab (φ b : P45)) (permTab (φ b : P45)) =
      tcomp (permTab (φ a : P45)) (permTab (φ a : P45)) := by
    rw [← permTab_coe_mul, ← permTab_coe_mul, ← map_mul, ← map_mul, hab]
  apply noQ8_tables hpa hpb htab1 htab2
  rw [← permTab_coe_mul, ← permTab_coe_mul, ← permTab_coe_mul, ← map_mul, ← map_mul, ← map_mul,
    hab']

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem noZ4Q8InCHutQuot :
    NoZ4Q8InCHutQuot (z := z) (D := D) := by
  unfold NoZ4Q8InCHutQuot CHutQuot
  intro L hL ⟨eL⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ := quotientEquivQA45 D
  have hψut : ψ (utq (z := z) (D := D)) = uA * tA := by
    change quotientEquivQA45 D ((utH D : ↥(H z)) : HModJ (z := z)) = _
    rw [quotientEquivQA45_coe, utH, map_mul, qH_uH, qH_tH]
  set L' := L.map ψ.toMonoidHom with hL'
  have hL'C : L' ≤ Subgroup.centralizer ({uA * tA} : Set A45) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hψut]
    have hxc := Subgroup.mem_centralizer_singleton_iff.mp (hL hx)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hxc]
  have hL16 : Nat.card L = 16 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hL'2 : IsPGroup 2 L' := (IsPGroup.of_card (n := 4) (by rw [hL16]; norm_num)).map _
  let a : A45 := ψ (eL.symm ⟨1, 1, 0⟩)
  let b : A45 := ψ (eL.symm ⟨1, 0, 1⟩)
  have ha : a ∈ L' := ⟨_, (eL.symm ⟨1, 1, 0⟩).2, rfl⟩
  have hb : b ∈ L' := ⟨_, (eL.symm ⟨1, 0, 1⟩).2, rfl⟩
  have hsq : ∀ m n : CFSG.Quasithin.Z4StarQ8Model,
      ψ ((eL.symm m : ↥L) : HModJ (z := z)) * ψ ((eL.symm n : ↥L) : HModJ (z := z)) =
        ψ ((eL.symm (m * n) : ↥L) : HModJ (z := z)) := by
    intro m n
    rw [← map_mul, map_mul eL.symm, Subgroup.coe_mul]
  have h1 := qa45_sq_eq_one_of_le_centralizer_ut hL'C hL'2 ha hb
    (by simp only [a, b, hsq, pauli_sq_eq]) (by simp only [a, b, hsq, pauli_mul_sq_eq])
  simp only [a, hsq] at h1
  have h3 : ((eL.symm (⟨1, 1, 0⟩ * ⟨1, 1, 0⟩) : ↥L) : HModJ (z := z)) = 1 := by
    apply ψ.injective
    rw [h1, map_one]
  have h4 : eL.symm (⟨1, 1, 0⟩ * ⟨1, 1, 0⟩) = eL.symm 1 := by
    rw [map_one]
    exact Subtype.ext h3
  exact pauli_sq_ne_one (eL.symm.injective h4)

end CFSG.RankThree.GF2n.Parrott
