module

public import CFSG.Quasithin.Recognition.St84.G24Data
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyFrame
public import Certificates.Data.A5GL42
import CFSG.GroupTheory.NormalizerInfCentralizer
import CFSG.Quasithin.Background.SpecialPGroupCenter

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open Certificates.A5GL42 (aN bN)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

structure G24Frame2 (L1 L2 S : Subgroup G) where
  k : G
  a : G
  b : G
  A : Subgroup G
  W : Subgroup G
  FN : ElemFrame (L2 ⊔ bigB L1 L2 S) (dsQ L2 L1 S) W
  FZ : ElemFrame (L2 ⊔ bigB L1 L2 S) (centerOf (dsQ L2 L1 S)) ⊥
  k_mem : k ∈ bigB L1 L2 S
  k_not_mem : k ∉ L2
  orderOf_k : orderOf k = 3
  comm_k : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L2 L1 S
  cent_Z : ∀ z ∈ centerOf (dsQ L2 L1 S), k * z = z * k
  inf_centralizer : dsQ L2 L1 S ⊓ Subgroup.centralizer ({k} : Set G) = centerOf (dsQ L2 L1 S)
  A_le : A ≤ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)
  inf_A : A ⊓ dsQ L2 L1 S = ⊥
  decomp : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L2 L1 S, ∃ c ∈ A, x = q * c
  card_A : Nat.card A = 180
  k_mem_A : k ∈ A
  a_mem : a ∈ A ⊓ L2
  b_mem : b ∈ A ⊓ L2
  a_sq : a ^ 2 = 1
  b_cube : b ^ 3 = 1
  ab_five : (a * b) ^ 5 = 1
  closure_ab : Subgroup.closure ({a, b} : Set G) = A ⊓ L2
  closure_eq : Subgroup.closure ({a, b, k} : Set G) = A
  mem_W : ∀ x, x ∈ W ↔ x ∈ dsQ L2 L1 S ∧ ∀ l ∈ L2, ⁅x, l⁆ ∈ centerOf (dsQ L2 L1 S)
  card_W : Nat.card W = 2 ^ 6
  FN_a : ∀ p : ↥(L2 ⊔ bigB L1 L2 S), (p : G) = a → glMat (FN.M p) = aN
  FN_b : ∀ p : ↥(L2 ⊔ bigB L1 L2 S), (p : G) = b → glMat (FN.M p) = bN
  FZ_a : ∀ p : ↥(L2 ⊔ bigB L1 L2 S), (p : G) = a → glMat (FZ.M p) = aN
  FZ_b : ∀ p : ↥(L2 ⊔ bigB L1 L2 S), (p : G) = b → glMat (FZ.M p) = bN
  FZ_k : ∀ p : ↥(L2 ⊔ bigB L1 L2 S), (p : G) = k → FZ.M p = 1

@[expose] def G24Frame2.kP (F : G24Frame2 L1 L2 S) : ↥(L2 ⊔ bigB L1 L2 S) :=
  ⟨F.k, (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) F.k_mem⟩

theorem G24Frame2.coe_kP (F : G24Frame2 L1 L2 S) : (F.kP : G) = F.k := rfl

@[expose] def G24Frame2.inv (F : G24Frame2 L1 L2 S) : G24Frame2 L1 L2 S where
  k := F.k⁻¹
  a := F.a
  b := F.b
  A := F.A
  W := F.W
  FN := F.FN
  FZ := F.FZ
  k_mem := (bigB L1 L2 S).inv_mem F.k_mem
  k_not_mem := by
    intro h
    exact F.k_not_mem (by simpa using L2.inv_mem h)
  orderOf_k := by rw [orderOf_inv, F.orderOf_k]
  comm_k := by
    intro x hx
    have hx2 : ⁅F.k, x⁆⁻¹ ∈ dsQ L2 L1 S := (dsQ L2 L1 S).inv_mem (F.comm_k x hx)
    have h1 : ⁅F.k⁻¹, x⁆ = F.k⁻¹ * ⁅F.k, x⁆⁻¹ * F.k := by
      rw [commutatorElement_inv_left, ← commutatorElement_inv (g₁ := F.k) (g₂ := x)]
    rw [h1]
    have hN : F.k⁻¹ ∈ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
      (Subgroup.normalizer _).inv_mem
        (P_le_normalizer_dsQ_right L1 L2 S
          ((le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) F.k_mem))
    simpa using (Subgroup.mem_normalizer_iff.mp hN _).mp hx2
  cent_Z := by
    intro z hz
    have h := F.cent_Z z hz
    exact (show Commute F.k z from h).inv_left.eq
  inf_centralizer := by
    rw [← Subgroup.centralizer_closure ({F.k⁻¹} : Set G),
      Subgroup.closure_singleton_inv, Subgroup.centralizer_closure]
    exact F.inf_centralizer
  A_le := by
    rw [← Subgroup.centralizer_closure ({F.k⁻¹} : Set G),
      Subgroup.closure_singleton_inv, Subgroup.centralizer_closure]
    exact F.A_le
  inf_A := F.inf_A
  decomp := F.decomp
  card_A := F.card_A
  k_mem_A := F.A.inv_mem F.k_mem_A
  a_mem := F.a_mem
  b_mem := F.b_mem
  a_sq := F.a_sq
  b_cube := F.b_cube
  ab_five := F.ab_five
  closure_ab := F.closure_ab
  closure_eq := by
    rw [show ({F.a, F.b, F.k⁻¹} : Set G) = ({F.a, F.b} : Set G) ∪ {F.k⁻¹} from by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto]
    rw [Subgroup.closure_union, Subgroup.closure_singleton_inv, ← Subgroup.closure_union,
      show ({F.a, F.b} : Set G) ∪ {F.k} = {F.a, F.b, F.k} from by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
        tauto,
      F.closure_eq]
  mem_W := F.mem_W
  card_W := F.card_W
  FN_a := F.FN_a
  FN_b := F.FN_b
  FZ_a := F.FZ_a
  FZ_b := F.FZ_b
  FZ_k := by
    intro p hp
    have hpk : p = F.kP⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_inv, G24Frame2.coe_kP, hp]
    rw [hpk, map_inv, F.FZ_k F.kP rfl, inv_one]

theorem G24Frame2.inv_k (F : G24Frame2 L1 L2 S) : F.inv.k = F.k⁻¹ := rfl

@[expose] def v2Block (U : Matrix (Fin 2) (Fin 2) (ZMod 2)) (X : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j =>
    if hi : i.val < 2 then
      if hj : j.val < 2 then U ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else X ⟨i.val, hi⟩ ⟨j.val - 2, by have := j.isLt; omega⟩
    else if j.val < 2 then 0
    else N ⟨i.val - 2, by have := i.isLt; omega⟩ ⟨j.val - 2, by have := j.isLt; omega⟩

@[expose] def v2Frame (k u : G) (n : Fin 4 → G) : Fin 6 → G :=
  ![u, k * u * k⁻¹, n 0, n 1, n 2, n 3]

@[expose] def G24Frame2.Mk (F : G24Frame2 L1 L2 S) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  glMat (F.FN.M F.kP)

@[expose] def G24Frame2.IsNLift (F : G24Frame2 L1 L2 S) (n : Fin 4 → G) : Prop :=
  ∀ j, ∃ h : n j ∈ dsQ L2 L1 S, F.FN.φ ⟨n j, h⟩ = Multiplicative.ofAdd (Pi.single j 1)

theorem G24Frame2.exists_nLift (F : G24Frame2 L1 L2 S) : ∃ n, F.IsNLift n := by
  choose n hn using fun j =>
    F.FN.surj (Multiplicative.ofAdd (Pi.single j (1 : ZMod 2)))
  exact ⟨fun j => (n j : G), fun j => ⟨(n j).2, hn j⟩⟩

theorem G24Frame2.special_data [Finite G] (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S) :
    F.A ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) ∧ Disjoint (dsQ L2 L1 S) F.A ∧
    centerOf (dsQ L2 L1 S) ≤ dsQ L2 L1 S ∧
    (∀ z ∈ centerOf (dsQ L2 L1 S), ∀ x ∈ dsQ L2 L1 S, z * x = x * z) ∧
    (∀ z ∈ centerOf (dsQ L2 L1 S), z ^ 2 = 1) ∧
    (∀ x ∈ dsQ L2 L1 S, x ^ 2 ∈ centerOf (dsQ L2 L1 S)) ∧
    (∀ r ∈ F.A, ∀ z ∈ centerOf (dsQ L2 L1 S), r * z * r⁻¹ ∈ centerOf (dsQ L2 L1 S)) ∧
    dsQ L2 L1 S ⊔ F.A = L2 ⊔ bigB L1 L2 S := by
  have hP2N := P_le_normalizer_dsQ_right L1 L2 S
  have hQ2P2 := dsQ_le_P_right L1 L2 S
  have hAN : F.A ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
    F.A_le.trans (inf_le_left.trans hP2N)
  have hdisj : Disjoint (dsQ L2 L1 S) F.A := by
    rw [disjoint_iff, inf_comm]
    exact F.inf_A
  refine ⟨hAN, hdisj, inf_le_left, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz x hx
    exact (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
  · intro z hz
    exact hD.sq_eq_one_of_mem_centerOf_right hz
  · intro x hx
    exact CFSG.Quasithin.IsSpecialPGroup.pow_mem_centerOf hD.special_right hx
  · intro r hr z hz
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.GroupTheory.mem_normalizer_inf_centralizer (hAN hr) (hAN hr)) z).mp hz
  · refine le_antisymm ?_ ?_
    · exact sup_le hQ2P2 (F.A_le.trans inf_le_left)
    · intro x hx
      obtain ⟨q, hq, c, hc, rfl⟩ := F.decomp x hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hc)

theorem G24Frame2.frame_spec [Finite G] (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S)
    {u : G} {n : Fin 4 → G} (hu : u ∈ F.W) (hn : F.IsNLift n) :
    (∀ i, v2Frame F.k u n i ∈ dsQ L2 L1 S) ∧
    (∀ y ∈ centerOf (dsQ L2 L1 S), ∀ i, y * v2Frame F.k u n i = v2Frame F.k u n i * y) ∧
    (∀ i, v2Frame F.k u n i ^ 2 ∈ centerOf (dsQ L2 L1 S)) ∧
    (∀ i j, ⁅v2Frame F.k u n i, v2Frame F.k u n j⁆ ∈ centerOf (dsQ L2 L1 S)) ∧
    Nat.card ↥(dsQ L2 L1 S) = 2 ^ 6 * Nat.card ↥(centerOf (dsQ L2 L1 S)) := by
  have hP2N := P_le_normalizer_dsQ_right L1 L2 S
  have huQ : u ∈ dsQ L2 L1 S := (F.mem_W u).mp hu |>.1
  have hku : F.k * u * F.k⁻¹ ∈ dsQ L2 L1 S :=
    (Subgroup.mem_normalizer_iff.mp (hP2N (F.kP).2) u).mp huQ
  have hnQ : ∀ j, n j ∈ dsQ L2 L1 S := fun j => (hn j).choose
  have hmem : ∀ i, v2Frame F.k u n i ∈ dsQ L2 L1 S := by
    intro i
    fin_cases i
    · exact huQ
    · exact hku
    · exact hnQ 0
    · exact hnQ 1
    · exact hnQ 2
    · exact hnQ 3
  have hframe : ∀ i, v2Frame F.k u n i ∈ dsQ L2 L1 S := hmem
  refine ⟨hframe, ?_, ?_, ?_, ?_⟩
  · intro y hy i
    exact (Subgroup.mem_centralizer_iff.mp hy.2 _ (hframe i)).symm
  · intro i
    exact CFSG.Quasithin.IsSpecialPGroup.pow_mem_centerOf hD.special_right (hframe i)
  · intro i j
    exact CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
      (Subgroup.commutator_mem_commutator (hframe i) (hframe j))
  · rw [hD.card_dsQ_right, hD.card_centerOf_dsQ_right]
    norm_num

theorem G24Vertex2.conj_eq_of_mem_centerOf {Q : Subgroup G} {z : G} (hz : z ∈ centerOf Q)
    {q : G} (hq : q ∈ Q) : q * z * q⁻¹ = z := by
  have hzq : q * z = z * q := Subgroup.mem_centralizer_iff.mp hz.2 q hq
  rw [hzq, mul_assoc, mul_inv_cancel, mul_one]

theorem G24Frame2.Q2_le_normalizer_W (F : G24Frame2 L1 L2 S) :
    dsQ L2 L1 S ≤ Subgroup.normalizer (F.W : Set G) := by
  have hQ2P2 := dsQ_le_P_right L1 L2 S
  have key : ∀ q ∈ dsQ L2 L1 S, ∀ w, w ∈ F.W → q * w * q⁻¹ ∈ F.W := by
    intro q hq w hw
    have hwQ : w ∈ dsQ L2 L1 S := ((F.mem_W w).mp hw).1
    let Q : Subgroup G := dsQ L2 L1 S
    let qP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨q, hQ2P2 hq⟩
    let wP : ↥Q := ⟨w, hwQ⟩
    let e : ↥Q := ⟨q * w * q⁻¹, Q.mul_mem (Q.mul_mem hq hwQ) (Q.inv_mem hq)⟩
    have hφw : F.FN.φ wP = 1 := (F.FN.ker wP).mpr hw
    have hact := F.FN.act qP wP e rfl
    have hφe : F.FN.φ e = 1 := by
      apply Multiplicative.toAdd.injective
      have h0 : Multiplicative.toAdd (F.FN.φ wP) = 0 := by rw [hφw]; rfl
      simpa [h0] using hact.symm
    exact (F.FN.ker e).mp hφe
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact key q hq w
  · intro hw
    have h1 := key q⁻¹ ((dsQ L2 L1 S).inv_mem hq) (q * w * q⁻¹) hw
    simpa [mul_assoc] using h1

theorem G24Frame2.k_le_normalizer_W (F : G24Frame2 L1 L2 S) :
    F.k ∈ Subgroup.normalizer (F.W : Set G) := by
  have hQ2P2 := dsQ_le_P_right L1 L2 S
  have hk3 : F.k ^ 3 = 1 := by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k
  have key : ∀ w, w ∈ F.W → F.k * w * F.k⁻¹ ∈ F.W := by
    intro w hw
    have hwQ : w ∈ dsQ L2 L1 S := ((F.mem_W w).mp hw).1
    have hkw : F.k * w * F.k⁻¹ ∈ dsQ L2 L1 S := by
      have hcomm := F.comm_k w (hQ2P2 hwQ)
      have e : F.k * w * F.k⁻¹ = ⁅F.k, w⁆ * w := by
        rw [commutatorElement_def]; group
      rw [e]
      exact (dsQ L2 L1 S).mul_mem hcomm hwQ
    let Q : Subgroup G := dsQ L2 L1 S
    let wP : ↥Q := ⟨w, hwQ⟩
    let e : ↥Q := ⟨F.k * w * F.k⁻¹, hkw⟩
    have hφw : F.FN.φ wP = 1 := (F.FN.ker wP).mpr hw
    have hact := F.FN.act F.kP wP e rfl
    have hφe : F.FN.φ e = 1 := by
      apply Multiplicative.toAdd.injective
      have h0 : Multiplicative.toAdd (F.FN.φ wP) = 0 := by rw [hφw]; rfl
      simpa [h0] using hact.symm
    exact (F.FN.ker e).mp hφe
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact key w
  · intro hw
    have h1 := key (F.k * w * F.k⁻¹) hw
    have h2 := key (F.k * (F.k * w * F.k⁻¹) * F.k⁻¹) h1
    have hkk : F.k * F.k * F.k = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using hk3
    have hkkinv : F.k⁻¹ * F.k⁻¹ * F.k⁻¹ = 1 := by
      have h : F.k⁻¹ ^ 3 = 1 := by rw [inv_pow, hk3, inv_one]
      simpa [pow_succ, pow_two, mul_assoc] using h
    have heq : F.k * (F.k * (F.k * w * F.k⁻¹) * F.k⁻¹) * F.k⁻¹ = w := by
      calc F.k * (F.k * (F.k * w * F.k⁻¹) * F.k⁻¹) * F.k⁻¹
          = (F.k * F.k * F.k) * w * (F.k⁻¹ * F.k⁻¹ * F.k⁻¹) := by group
        _ = 1 * w * 1 := by rw [hkk, hkkinv]
        _ = w := by group
    rwa [heq] at h2

theorem G24Frame2.Z2_le_W (F : G24Frame2 L1 L2 S) :
    centerOf (dsQ L2 L1 S) ≤ F.W := by
  intro z hz
  refine (F.mem_W z).mpr ⟨hz.1, fun l hl => ?_⟩
  have hlP : l ∈ L2 ⊔ bigB L1 L2 S :=
    (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S) hl
  have hy : l * z * l⁻¹ ∈ centerOf (dsQ L2 L1 S) :=
    (Subgroup.mem_normalizer_iff.mp
      (P_le_normalizer_centerOf_dsQ_right L1 L2 S hlP) z).mp hz
  have heq : ⁅z, l⁆ = z * (l * z * l⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [heq]
  exact (centerOf (dsQ L2 L1 S)).mul_mem hz
    ((centerOf (dsQ L2 L1 S)).inv_mem hy)

theorem G24Frame2.k_mem_normalizer_Z2 (F : G24Frame2 L1 L2 S) :
    F.k ∈ Subgroup.normalizer (centerOf (dsQ L2 L1 S) : Set G) :=
  P_le_normalizer_centerOf_dsQ_right L1 L2 S F.kP.2

theorem v2Frame_eq_append (k u : G) (n : Fin 4 → G) :
    v2Frame k u n = Fin.append (show Fin 2 → G from ![u, k * u * k⁻¹]) n := by
  funext i
  fin_cases i <;> rfl

theorem v2Block_col_N (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (j : Fin 4) :
    (fun i : Fin 6 => v2Block U X N i (Fin.natAdd 2 j)) =
      Fin.append (fun i : Fin 2 => X i j) (fun k : Fin 4 => N k j) := by
  funext i
  refine Fin.addCases (m := 2) (n := 4) (fun l => ?_) (fun r => ?_) i
  · have hl : l.val ≤ 1 := by omega
    have hj : ¬ (2 + j.val ≤ 1) := by omega
    simp [v2Block, Fin.natAdd, Fin.castAdd, hl, hj]
  · have hi : ¬ (2 + r.val ≤ 1) := by omega
    have hj : ¬ (2 + j.val ≤ 1) := by omega
    have hi2 : ¬ (2 + r.val < 2) := by omega
    have hj2 : ¬ (2 + j.val < 2) := by omega
    simp [v2Block, Fin.natAdd, hi, hj, hi2, hj2]
    exact (Fin.append_right (fun i => X i j) (fun k => N k j) r).symm

theorem v2Block_col_U (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (j : Fin 2) :
    (fun i : Fin 6 => v2Block U X N i (Fin.castAdd 4 j)) =
      fun i : Fin 6 => if h : i.val < 2 then U ⟨i.val, h⟩ j else 0 := by
  funext i
  refine Fin.addCases (m := 2) (n := 4) (fun l => ?_) (fun r => ?_) i
  · have hl : l.val ≤ 1 := by omega
    have hj : j.val ≤ 1 := by omega
    simp [v2Block, Fin.castAdd, hl, hj, Fin.append_left]
  · have hi : ¬ (2 + r.val ≤ 1) := by omega
    have hj : j.val ≤ 1 := by omega
    simp [v2Block, Fin.castAdd, hi, hj, Fin.append_right]

theorem v2Frame_castAdd (k u : G) (n : Fin 4 → G) (j : Fin 2) :
    v2Frame k u n (Fin.castAdd 4 j) =
      (show Fin 2 → G from ![u, k * u * k⁻¹]) j := by
  fin_cases j <;> rfl

theorem v2Frame_natAdd (k u : G) (n : Fin 4 → G) (j : Fin 4) :
    v2Frame k u n (Fin.natAdd 2 j) = n j := by
  fin_cases j <;> rfl

theorem v2Block_castAdd_castAdd (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (a b : Fin 2) : v2Block U X N (Fin.castAdd 4 a) (Fin.castAdd 4 b) = U a b := by
  have ha : (Fin.castAdd 4 a).val < 2 := a.isLt
  have hb : (Fin.castAdd 4 b).val < 2 := b.isLt
  simp only [v2Block, Matrix.of_apply]
  rw [dif_pos ha, dif_pos hb]
  simp

theorem v2Block_castAdd_natAdd (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (a : Fin 2) (d : Fin 4) : v2Block U X N (Fin.castAdd 4 a) (Fin.natAdd 2 d) = X a d := by
  have ha : (Fin.castAdd 4 a).val < 2 := a.isLt
  have hd : ¬ (Fin.natAdd 2 d).val < 2 := by
    simp only [Fin.natAdd, Fin.val_mk]
    omega
  simp only [v2Block, Matrix.of_apply]
  rw [dif_pos ha, dif_neg hd]
  simp

theorem v2Block_natAdd_castAdd (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (c : Fin 4) (b : Fin 2) : v2Block U X N (Fin.natAdd 2 c) (Fin.castAdd 4 b) = 0 := by
  have hc : ¬ (Fin.natAdd 2 c).val < 2 := by
    simp only [Fin.natAdd, Fin.val_mk]
    omega
  have hb : (Fin.castAdd 4 b).val < 2 := b.isLt
  simp only [v2Block, Matrix.of_apply]
  rw [dif_neg hc, if_pos hb]

theorem v2Block_natAdd_natAdd (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (c d : Fin 4) : v2Block U X N (Fin.natAdd 2 c) (Fin.natAdd 2 d) = N c d := by
  have hc : ¬ (Fin.natAdd 2 c).val < 2 := by
    simp only [Fin.natAdd, Fin.val_mk]
    omega
  have hd : ¬ (Fin.natAdd 2 d).val < 2 := by
    simp only [Fin.natAdd, Fin.val_mk]
    omega
  simp only [v2Block, Matrix.of_apply]
  rw [dif_neg hc, if_neg hd]
  simp

end CFSG.Quasithin.F112R.St84
