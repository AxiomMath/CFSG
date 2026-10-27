module

public import CFSG.LocalAnalysis.StandardType.GGFFModel
import CFSG.LocalAnalysis.StandardType.GGFFLocal

public section

namespace CFSG.StandardType.FF81.CentA

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G] {y : Fin 3 → G}

private theorem cafSyl_y_ne_one (hinj : ∀ v, vecElt y v = 1 → v = 0) (i : Fin 3) :
    y i ≠ 1 := by
  intro h
  have h1 : vecElt y (Pi.single i 1) = 1 := by
    rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one, h]
  have h2 := congrFun (hinj _ h1) i
  rw [Pi.single_eq_same] at h2
  exact one_ne_zero h2

private theorem cafSyl_orderOf_y (hp : ∀ i, y i ^ 3 = 1)
    (hinj : ∀ v, vecElt y v = 1 → v = 0) (i : Fin 3) : orderOf (y i) = 3 :=
  orderOf_eq_prime (hp i) (cafSyl_y_ne_one hinj i)

private theorem cafSyl_y_ne (hp : ∀ i, y i ^ 3 = 1) (hc : ∀ i j, y i * y j = y j * y i)
    (hinj : ∀ v, vecElt y v = 1 → v = 0) {i j : Fin 3} (hij : i ≠ j) : y i ≠ y j := by
  intro h
  have hv : vecElt y (Pi.single i 1) = vecElt y (Pi.single j 1) := by
    rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one,
      CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one, h]
  have h1 := GGFF.vecElt_injective hp hc hinj hv
  have h2 := congrFun h1 i
  rw [Pi.single_eq_same] at h2
  simpa [Pi.single_eq_of_ne hij] using h2

private theorem cafSyl_w_notMem_tor (hp : ∀ i, y i ^ 3 = 1) (hc : ∀ i j, y i * y j = y j * y i)
    (hinj : ∀ v, vecElt y v = 1 → v = 0) {w : G}
    (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i)) : w ∉ GGFF.tor y := by
  intro hwB
  have hy0 : y 0 ∈ GGFF.tor y := Subgroup.subset_closure ⟨0, rfl⟩
  have hcomm : w * y 0 = y 0 * w :=
    congrArg Subtype.val
      ((IsMulCommutative.is_comm (self := (GGFF.isElemAbelian_tor hp hc).1)).comm
        (⟨w, hwB⟩ : ↥(GGFF.tor y)) ⟨y 0, hy0⟩)
  have h0 : w * y 0 * w⁻¹ = y 1 := by simpa using hw 0
  have h1 : y 0 = y 1 := by rw [← h0, hcomm, mul_inv_cancel_right]
  exact cafSyl_y_ne hp hc hinj (by decide : (0 : Fin 3) ≠ 1) h1

private theorem cafSyl_conj_vecElt (hc : ∀ i j, y i * y j = y j * y i) {w : G}
    (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i)) (v : Fin 3 → ZMod 3) :
    w * vecElt y v * w⁻¹ = vecElt y (fun j => v ((finRotate 3).symm j)) := by
  have h0 : w * y 0 * w⁻¹ = y 1 := by simpa using hw 0
  have h1 : w * y 1 * w⁻¹ = y 2 := by simpa using hw 1
  have h2 : w * y 2 * w⁻¹ = y 0 := by simpa using hw 2
  have e0 : (finRotate 3).symm 0 = 2 := by decide
  have e1 : (finRotate 3).symm 1 = 0 := by decide
  have e2 : (finRotate 3).symm 2 = 1 := by decide
  simp only [vecElt]
  rw [show w * (y 0 ^ (v 0).val * y 1 ^ (v 1).val * y 2 ^ (v 2).val) * w⁻¹ =
      (w * y 0 ^ (v 0).val * w⁻¹) * (w * y 1 ^ (v 1).val * w⁻¹) *
        (w * y 2 ^ (v 2).val * w⁻¹) by group]
  rw [← conj_pow, h0, ← conj_pow, h1, ← conj_pow, h2]
  simp only [e0, e1, e2]
  have h12 : y 2 ^ (v 1).val * y 0 ^ (v 2).val =
      y 0 ^ (v 2).val * y 2 ^ (v 1).val := (Commute.pow_pow (hc 2 0) _ _).eq
  have h02 : y 1 ^ (v 0).val * y 0 ^ (v 2).val =
      y 0 ^ (v 2).val * y 1 ^ (v 0).val := (Commute.pow_pow (hc 1 0) _ _).eq
  calc y 1 ^ (v 0).val * y 2 ^ (v 1).val * y 0 ^ (v 2).val
      = y 1 ^ (v 0).val * (y 2 ^ (v 1).val * y 0 ^ (v 2).val) := by group
    _ = y 1 ^ (v 0).val * y 0 ^ (v 2).val * y 2 ^ (v 1).val := by rw [h12]; group
    _ = y 0 ^ (v 2).val * y 1 ^ (v 0).val * y 2 ^ (v 1).val := by rw [h02]


open CFSG.RankThree.PartTwo.Sec4.Item434Kit in
private theorem cafSyl_tor_eq_baseA : GGFF.tor y = baseA y := by
  have hrange : Set.range y = ({y 0, y 1, y 2} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  rw [GGFF.tor, baseA, hrange]
  rw [show ({y 0, y 1, y 2} : Set G) = ({y 0} ∪ {y 1}) ∪ {y 2} by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto]
  rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]

open CFSG.RankThree.PartTwo.Sec4.Item434Kit in
private theorem cafSyl_comm_y_of_mem_tor (hp : ∀ i, y i ^ 3 = 1)
    (hc : ∀ i j, y i * y j = y j * y i) {β : G} (hβ : β ∈ GGFF.tor y) (i : Fin 3) :
    β * y i = y i * β := by
  exact congrArg Subtype.val
    ((IsMulCommutative.is_comm (self := (GGFF.isElemAbelian_tor hp hc).1)).comm
      (⟨β, hβ⟩ : ↥(GGFF.tor y)) ⟨y i, Subgroup.subset_closure ⟨i, rfl⟩⟩)

private theorem cafSyl_w3_eq_const (hp : ∀ i, y i ^ 3 = 1)
    (hc : ∀ i j, y i * y j = y j * y i) (hinj : ∀ v, vecElt y v = 1 → v = 0) {w : G}
    (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i)) (hw3 : w ^ 3 ∈ GGFF.tor y) :
    ∃ a : ZMod 3, w ^ 3 = vecElt y (fun _ => a) := by
  obtain ⟨c, hweq⟩ := (GGFF.mem_tor hp hc).mp hw3
  have hcomm : w * w ^ 3 * w⁻¹ = w ^ 3 := by group
  have hconj : vecElt y c = vecElt y (fun j => c ((finRotate 3).symm j)) := by
    rw [← hweq]
    calc w ^ 3 = w * w ^ 3 * w⁻¹ := hcomm.symm
      _ = w * vecElt y c * w⁻¹ := by rw [hweq]
      _ = vecElt y (fun j => c ((finRotate 3).symm j)) := cafSyl_conj_vecElt hc hw c
  have hshift := GGFF.vecElt_injective hp hc hinj hconj
  have h01 : c 0 = c 1 := by
    have := congrFun hshift 1
    simpa [show (finRotate 3).symm 1 = 0 from by decide] using this.symm
  have h12 : c 1 = c 2 := by
    have := congrFun hshift 2
    simpa [show (finRotate 3).symm 2 = 1 from by decide] using this.symm
  refine ⟨c 0, ?_⟩
  rw [hweq]
  congr 1
  funext j
  fin_cases j <;> simp [h01, h12]


private theorem cafSyl_zpowers_inj (hp : ∀ i, y i ^ 3 = 1)
    (hc : ∀ i j, y i * y j = y j * y i) (hinj : ∀ v, vecElt y v = 1 → v = 0) :
    Function.Injective (fun i : Fin 3 => Subgroup.zpowers (y i)) := by
  intro i j hij
  have hij' : Subgroup.zpowers (y i) = Subgroup.zpowers (y j) := hij
  have hy : y i ∈ Subgroup.zpowers (y j) := by
    rw [← hij']
    exact Subgroup.mem_zpowers (y i)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk' : y i = y j ^ ((k : ZMod 3).val) := by
    rw [← hk, ← zpow_natCast, ZMod.val_intCast]
    have h3 := zpow_mod_orderOf (y j) k
    rw [cafSyl_orderOf_y hp hinj j] at h3
    rw [h3]
  have hv : vecElt y (Pi.single i 1) = vecElt y (Pi.single j (k : ZMod 3)) := by
    rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one,
      CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single, hk']
  have hsingle := GGFF.vecElt_injective hp hc hinj hv
  have hcoord := congrFun hsingle i
  rw [Pi.single_eq_same] at hcoord
  by_cases hji : j = i
  · exact hji.symm
  · rw [Pi.single_eq_of_ne (Ne.symm hji)] at hcoord
    exact absurd hcoord one_ne_zero

private theorem cafSyl_w_pow_conj {w : G}
    (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i)) (j : ℕ) (i : Fin 3) :
    w ^ j * y i * (w ^ j)⁻¹ = y ((finRotate 3 ^ j) i) := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    calc (w ^ j * w) * y i * (w ^ j * w)⁻¹
        = w ^ j * (w * y i * w⁻¹) * (w ^ j)⁻¹ := by group
      _ = w ^ j * y (finRotate 3 i) * (w ^ j)⁻¹ := by rw [hw i]
      _ = y ((finRotate 3 ^ j) (finRotate 3 i)) := ih (finRotate 3 i)
      _ = y ((finRotate 3 ^ (j + 1)) i) := by
            rw [pow_succ, Equiv.Perm.mul_apply]

private theorem cafSyl_inv_w_pow_conj {w : G}
    (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i)) (j : ℕ) (i : Fin 3) :
    (w ^ j)⁻¹ * y i * w ^ j = y ((finRotate 3 ^ j).symm i) := by
  have h := cafSyl_w_pow_conj hw j ((finRotate 3 ^ j).symm i)
  rw [Equiv.apply_symm_apply] at h
  have h' : (w ^ j)⁻¹ * (w ^ j * y ((finRotate 3 ^ j).symm i) * (w ^ j)⁻¹) * w ^ j =
      (w ^ j)⁻¹ * y i * w ^ j := by rw [h]
  have h'' : (w ^ j)⁻¹ * (w ^ j * y ((finRotate 3 ^ j).symm i) * (w ^ j)⁻¹) * w ^ j =
      y ((finRotate 3 ^ j).symm i) := by group
  exact (h''.symm.trans h').symm

open CFSG.RankThree.PartTwo.Sec4.Item434Kit in
private theorem cafSyl_perm_pow_eq_one (hp : ∀ i, y i ^ 3 = 1)
    (hc : ∀ i j, y i * y j = y j * y i) (hinj : ∀ v, vecElt y v = 1 → v = 0)
    {x : G} {n : ℕ} (hxn : x ^ n = 1) {σ : Equiv.Perm (Fin 3)} {π : Fin 3 → Fin 3}
    (hσ : ∀ i, σ i = π i)
    (hπ : ∀ i, x * y i * x⁻¹ ∈ Subgroup.zpowers (y (π i))) : σ ^ n = 1 := by
  let L : Fin 3 → Subgroup G := fun i => Subgroup.zpowers (y i)
  have hLinj : Function.Injective L := cafSyl_zpowers_inj hp hc hinj
  have hLmap : ∀ i, (L i).map (MulAut.conj x).toMonoidHom = L (σ i) := by
    intro i
    have hle : Subgroup.zpowers (x * y i * x⁻¹) ≤ Subgroup.zpowers (y (π i)) :=
      Subgroup.zpowers_le.mpr (hπ i)
    have hsem : SemiconjBy x (y i) (x * y i * x⁻¹) := by
      show x * y i = (x * y i * x⁻¹) * x
      group
    have hord : orderOf (x * y i * x⁻¹) = orderOf (y i) :=
      (SemiconjBy.orderOf_eq x hsem).symm
    have heq : Subgroup.zpowers (x * y i * x⁻¹) = Subgroup.zpowers (y (π i)) := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hord, cafSyl_orderOf_y hp hinj i,
        cafSyl_orderOf_y hp hinj (π i)]
    calc (L i).map (MulAut.conj x).toMonoidHom
        = Subgroup.zpowers (x * y i * x⁻¹) := by
          change (Subgroup.zpowers (y i)).map (MulAut.conj x).toMonoidHom =
            Subgroup.zpowers (x * y i * x⁻¹)
          rw [MonoidHom.map_zpowers]
          change Subgroup.zpowers ((MulAut.conj x) (y i)) =
            Subgroup.zpowers (x * y i * x⁻¹)
          rw [MulAut.conj_apply]
      _ = Subgroup.zpowers (y (π i)) := heq
      _ = L (σ i) := by rw [hσ i]
  have hLpow : ∀ m : ℕ, ∀ i,
      (L i).map (MulAut.conj (x ^ m)).toMonoidHom = L ((σ ^ m) i) := by
    intro m
    induction m with
    | zero =>
      intro i
      rw [pow_zero, map_one]
      have h : (1 : MulAut G).toMonoidHom = MonoidHom.id G := by ext y; rfl
      rw [h, Subgroup.map_id, pow_zero, Equiv.Perm.one_apply]
    | succ m ih =>
      intro i
      have hpow : MulAut.conj (x ^ (m + 1)) = MulAut.conj (x ^ m) * MulAut.conj x := by
        rw [pow_succ]
        exact map_mul MulAut.conj (x ^ m) x
      rw [hpow]
      have hcomp : ((MulAut.conj (x ^ m) * MulAut.conj x)).toMonoidHom =
          (MulAut.conj (x ^ m)).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
        ext z
        rfl
      rw [hcomp, ← Subgroup.map_map (L i) (MulAut.conj (x ^ m)).toMonoidHom
        (MulAut.conj x).toMonoidHom, hLmap i, ih (σ i), pow_succ, Equiv.Perm.mul_apply]
  have hn := hLpow n
  apply Equiv.Perm.ext
  intro i
  have h := hn i
  rw [hxn, map_one] at h
  have h1 : (L i).map (1 : MulAut G).toMonoidHom = L i := by
    have h' : (1 : MulAut G).toMonoidHom = MonoidHom.id G := by ext z; rfl
    rw [h', Subgroup.map_id]
  rw [h1] at h
  simpa using hLinj h.symm

open CFSG.RankThree.PartTwo.Sec4.Item434Kit in
private theorem cafSyl_exists_wreath (hp : ∀ i, y i ^ 3 = 1)
    (hc : ∀ i j, y i * y j = y j * y i) (hinj : ∀ v, vecElt y v = 1 → v = 0) {w : G}
    (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i)) (hw3 : w ^ 3 ∈ GGFF.tor y) :
    ∃ t : G, WreathFacts y t ∧
      wreathW y t = GGFF.tor y ⊔ Subgroup.zpowers w ∧
      Nat.card (wreathW y t) = 81 := by
  obtain ⟨a, hw3a⟩ := cafSyl_w3_eq_const hp hc hinj hw hw3
  let b : ZMod 3 := 2 * a
  let β : G := vecElt y (Pi.single (0 : Fin 3) b)
  let t : G := w * β
  have hβmem : β ∈ GGFF.tor y := GGFF.vecElt_mem_tor y _
  have hβ0 : β = y 0 ^ b.val := by
    simpa [β] using vecElt_single (z := y) 0 b
  have hβs1 : vecElt y (Pi.single (1 : Fin 3) b) = y 1 ^ b.val :=
    vecElt_single (z := y) 1 b
  have hβs2 : vecElt y (Pi.single (2 : Fin 3) b) = y 2 ^ b.val :=
    vecElt_single (z := y) 2 b
  have hβ1 : w * β * w⁻¹ = vecElt y (Pi.single (1 : Fin 3) b) := by
    rw [hβ0, hβs1, ← conj_pow]
    rw [show w * y 0 * w⁻¹ = y 1 from by simpa using hw 0]
  have hβ2 : w * (w * β * w⁻¹) * w⁻¹ = vecElt y (Pi.single (2 : Fin 3) b) := by
    rw [hβ1, hβs1, hβs2, ← conj_pow]
    rw [show w * y 1 * w⁻¹ = y 2 from by simpa using hw 1]
  have hβ3 : w ^ 3 * β * (w ^ 3)⁻¹ = β := by
    have hcomm : w ^ 3 * β = β * w ^ 3 :=
      congrArg Subtype.val
        ((IsMulCommutative.is_comm (self := (GGFF.isElemAbelian_tor hp hc).1)).comm
          (⟨w ^ 3, hw3⟩ : ↥(GGFF.tor y)) ⟨β, hβmem⟩)
    rw [hcomm, mul_inv_cancel_right]
  have hcube : (w * β) ^ 3 =
      (w * β * w⁻¹) * (w * (w * β * w⁻¹) * w⁻¹) * (w ^ 3 * β * (w ^ 3)⁻¹) * w ^ 3 := by
    rw [pow_three']
    group
  have hsum : ((Pi.single (1 : Fin 3) b + Pi.single (2 : Fin 3) b) +
      Pi.single (0 : Fin 3) b) + (fun _ => a) = 0 := by
    have hba : (2 : ZMod 3) * a + a = 0 := by
      have h : (2 : ZMod 3) + 1 = 0 := by decide
      calc 2 * a + a = (2 + 1) * a := by ring
        _ = 0 := by rw [h, zero_mul]
    funext j
    fin_cases j <;> simpa [Pi.single, b] using hba
  have ht3 : t ^ 3 = 1 := by
    change (w * β) ^ 3 = 1
    rw [hcube, hβ2, hβ1, hβ3,
      show β = vecElt y (Pi.single (0 : Fin 3) b) from rfl, hw3a]
    rw [← GGFF.vecElt_add hp hc, ← GGFF.vecElt_add hp hc, ← GGFF.vecElt_add hp hc,
      hsum, GGFF.vecElt_zero]
  have hβy : ∀ i, β * y i * β⁻¹ = y i := fun i => by
    rw [cafSyl_comm_y_of_mem_tor hp hc hβmem i, mul_inv_cancel_right]
  have hf : WreathFacts y t := by
    refine ⟨hp, hc, hinj, ht3, ?_, ?_, ?_, ?_⟩
    · change (w * β) * y 0 * (w * β)⁻¹ = y 1
      calc (w * β) * y 0 * (w * β)⁻¹ = w * (β * y 0 * β⁻¹) * w⁻¹ := by group
        _ = w * y 0 * w⁻¹ := by rw [hβy 0]
        _ = y 1 := by simpa using hw 0
    · change (w * β) * y 1 * (w * β)⁻¹ = y 2
      calc (w * β) * y 1 * (w * β)⁻¹ = w * (β * y 1 * β⁻¹) * w⁻¹ := by group
        _ = w * y 1 * w⁻¹ := by rw [hβy 1]
        _ = y 2 := by simpa using hw 1
    · change (w * β) * y 2 * (w * β)⁻¹ = y 0
      calc (w * β) * y 2 * (w * β)⁻¹ = w * (β * y 2 * β⁻¹) * w⁻¹ := by group
        _ = w * y 2 * w⁻¹ := by rw [hβy 2]
        _ = y 0 := by simpa using hw 2
    · intro v hv
      have htmem : t ∈ GGFF.tor y := hv ▸ GGFF.vecElt_mem_tor y v
      apply cafSyl_w_notMem_tor hp hc hinj hw
      have hwt : w = t * β⁻¹ := by change w = (w * β) * β⁻¹; group
      rw [hwt]
      exact (GGFF.tor y).mul_mem htmem ((GGFF.tor y).inv_mem hβmem)
  have hsup : GGFF.tor y ⊔ Subgroup.zpowers w =
      GGFF.tor y ⊔ Subgroup.zpowers t := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [Subgroup.zpowers_le]
      have hwt : w = t * β⁻¹ := by change w = (w * β) * β⁻¹; group
      rw [hwt]
      exact (GGFF.tor y ⊔ Subgroup.zpowers t).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left ((GGFF.tor y).inv_mem hβmem))
    · rw [Subgroup.zpowers_le]
      change w * β ∈ GGFF.tor y ⊔ Subgroup.zpowers w
      exact (GGFF.tor y ⊔ Subgroup.zpowers w).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
        (Subgroup.mem_sup_left hβmem)
  have hwreath : wreathW y t = GGFF.tor y ⊔ Subgroup.zpowers w := by
    calc wreathW y t = baseA y ⊔ Subgroup.zpowers t := rfl
      _ = GGFF.tor y ⊔ Subgroup.zpowers t := by rw [cafSyl_tor_eq_baseA]
      _ = GGFF.tor y ⊔ Subgroup.zpowers w := hsup.symm
  refine ⟨t, hf, hwreath, ?_⟩
  apply le_antisymm
  · let f : (Fin 3 → ZMod 3) × Fin 3 → ↥(wreathW y t) := fun p =>
      ⟨vecElt y p.1 * t ^ (p.2 : ℕ),
        (wreathW y t).mul_mem (Subgroup.mem_sup_left (vecElt_mem_baseA hf p.1))
          (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers t (p.2 : ℕ)))⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨v, j, rfl⟩ := mem_wreathW hf hx
      exact ⟨(v, j), rfl⟩
    have hle := Nat.card_le_card_of_surjective f hsurj
    have hcard : Nat.card ((Fin 3 → ZMod 3) × Fin 3) = 81 := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
      norm_num
    rwa [hcard] at hle
  · exact le_card_wreathW hf

theorem exists_pow_inv_mul_comm (hp : ∀ i, y i ^ 3 = 1) (hc : ∀ i j, y i * y j = y j * y i)
    (hinj : ∀ v, vecElt y v = 1 → v = 0) {w : G} (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i))
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hwQ : w ∈ Q) {x : G} (hxQ : x ∈ Q)
    (hx : ∀ i, ∃ j, x * y i * x⁻¹ ∈ Subgroup.zpowers (y j)) :
    ∃ j : ℕ, ∀ i, (w ^ j)⁻¹ * x * y i = y i * ((w ^ j)⁻¹ * x) := by
  obtain ⟨k, hxk⟩ := hQ.exists_pow_pow_eq_one (⟨x, hxQ⟩ : ↥Q)
  have hxkG : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hxk
  choose π hπ using hx
  have hπinj : Function.Injective π := by
    intro i i' hii
    have hz : x * y i * x⁻¹ ∈ Subgroup.zpowers (y (π i)) := hπ i
    have hz' : x * y i' * x⁻¹ ∈ Subgroup.zpowers (y (π i)) := by
      rw [hii]
      exact hπ i'
    have hzne : x * y i * x⁻¹ ≠ 1 := by
      intro h1
      have h2 : y i = 1 := by
        have := congrArg (fun z => x⁻¹ * z * x) h1
        simpa [mul_assoc] using this
      exact cafSyl_y_ne_one hinj i h2
    have hzne' : x * y i' * x⁻¹ ≠ 1 := by
      intro h1
      have h2 : y i' = 1 := by
        have := congrArg (fun z => x⁻¹ * z * x) h1
        simpa [mul_assoc] using this
      exact cafSyl_y_ne_one hinj i' h2
    have hord := cafSyl_orderOf_y hp hinj (π i)
    have hiz := GGFF.eq_or_eq_inv_of_mem_zpowers hord hz hzne
    have hiz' := GGFF.eq_or_eq_inv_of_mem_zpowers hord hz' hzne'
    have hcases : y i = y i' ∨ y i = (y i')⁻¹ := by
      rcases hiz with h1 | h1 <;> rcases hiz' with h2 | h2
      · left
        have heq : x * y i * x⁻¹ = x * y i' * x⁻¹ := h1.trans h2.symm
        calc y i = x⁻¹ * (x * y i * x⁻¹) * x := by group
          _ = x⁻¹ * (x * y i' * x⁻¹) * x := by rw [heq]
          _ = y i' := by group
      · right
        have heq : x * y i * x⁻¹ = (x * y i' * x⁻¹)⁻¹ := by rw [h1, h2, inv_inv]
        calc y i = x⁻¹ * (x * y i * x⁻¹) * x := by group
          _ = x⁻¹ * (x * y i' * x⁻¹)⁻¹ * x := by rw [heq]
          _ = (y i')⁻¹ := by group
      · right
        have heq : x * y i * x⁻¹ = (x * y i' * x⁻¹)⁻¹ := by rw [h1, h2]
        calc y i = x⁻¹ * (x * y i * x⁻¹) * x := by group
          _ = x⁻¹ * (x * y i' * x⁻¹)⁻¹ * x := by rw [heq]
          _ = (y i')⁻¹ := by group
      · left
        have heq : x * y i * x⁻¹ = x * y i' * x⁻¹ := h1.trans h2.symm
        calc y i = x⁻¹ * (x * y i * x⁻¹) * x := by group
          _ = x⁻¹ * (x * y i' * x⁻¹) * x := by rw [heq]
          _ = y i' := by group
    rcases hcases with h | h
    · have hv : vecElt y (Pi.single i 1) = vecElt y (Pi.single i' 1) := by
        rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one,
          CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one, h]
      have hsingle := GGFF.vecElt_injective hp hc hinj hv
      have hcoord := congrFun hsingle i
      rw [Pi.single_eq_same] at hcoord
      by_cases hii' : i = i'
      · exact hii'
      · rw [Pi.single_eq_of_ne hii'] at hcoord
        exact absurd hcoord one_ne_zero
    · have hv : vecElt y (Pi.single i 1 + Pi.single i' 1) = 1 := by
        rw [GGFF.vecElt_add hp hc]
        rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one,
          CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one, h]
        exact inv_mul_cancel _
      have hzero := hinj _ hv
      have hcoord := congrFun hzero i
      simp only [Pi.add_apply] at hcoord
      rw [Pi.single_eq_same] at hcoord
      by_cases hii' : i = i'
      · exact hii'
      · rw [Pi.single_eq_of_ne hii'] at hcoord
        simpa using hcoord
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective π (Finite.injective_iff_bijective.mp hπinj)
  have hσ : ∀ i, σ i = π i := fun i => rfl
  have hσn : σ ^ 3 ^ k = 1 := cafSyl_perm_pow_eq_one hp hc hinj hxkG hσ hπ
  have hσ3 : σ ^ 3 = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hσ1 : σ = 1 := by simpa using hσn
      rw [hσ1, one_pow]
    · have h6all : ∀ τ : Equiv.Perm (Fin 3), τ ^ 6 = 1 := by decide
      have hgcd : Nat.gcd (3 ^ k) 6 = 3 := by
        have hpow : 3 ^ k = 3 * 3 ^ (k - 1) := by
          rw [show k = (k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm,
            show k - 1 + 1 - 1 = k - 1 by omega]
        have hcop : Nat.Coprime (3 ^ (k - 1)) 2 :=
          Nat.Coprime.pow_left (k - 1) (by norm_num : Nat.Coprime 3 2)
        rw [hpow, show (6 : ℕ) = 3 * 2 by norm_num, Nat.gcd_mul_left, hcop.gcd_eq_one]
      have hg := (pow_gcd_eq_one (a := σ) (m := 3 ^ k) (n := 6)).mpr ⟨hσn, h6all σ⟩
      rwa [hgcd] at hg
  obtain ⟨j, hj⟩ := (by
    have hall : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 →
        ∃ j : Fin 3, τ = finRotate 3 ^ (j : ℕ) := by decide
    exact hall σ hσ3)
  have hπeq : ∀ i, π i = (finRotate 3 ^ (j : ℕ)) i := by
    intro i
    have := congrFun (congrArg (fun τ : Equiv.Perm (Fin 3) => (τ : Fin 3 → Fin 3)) hj) i
    simpa [hσ] using this
  have hmem : ∀ i, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ x * y i * x⁻¹ = y (π i) ^ e := by
    intro i
    have hne : x * y i * x⁻¹ ≠ 1 := by
      intro h1
      have h2 : y i = 1 := by
        have := congrArg (fun z => x⁻¹ * z * x) h1
        simpa [mul_assoc] using this
      exact cafSyl_y_ne_one hinj i h2
    have hsq : y (π i) ^ 2 = (y (π i))⁻¹ := by
      calc y (π i) ^ 2 = y (π i) ^ 3 * (y (π i))⁻¹ := by group
        _ = (y (π i))⁻¹ := by rw [hp (π i), one_mul]
    rcases GGFF.eq_or_eq_inv_of_mem_zpowers (cafSyl_orderOf_y hp hinj (π i)) (hπ i) hne with
      h | h
    · exact ⟨1, Or.inl rfl, by rw [h, pow_one]⟩
    · exact ⟨2, Or.inr rfl, by rw [h]; exact hsq.symm⟩
  choose e he using hmem
  have he1 : ∀ i, e i = 1 ∨ e i = 2 := fun i => (he i).1
  have hxe : ∀ i, x * y i * x⁻¹ = y (π i) ^ e i := fun i => (he i).2
  let c : G := (w ^ (j : ℕ))⁻¹ * x
  have hwj : ∀ i, (w ^ (j : ℕ))⁻¹ * y (π i) * w ^ (j : ℕ) = y i := by
    intro i
    calc (w ^ (j : ℕ))⁻¹ * y (π i) * w ^ (j : ℕ)
        = (w ^ (j : ℕ))⁻¹ * y ((finRotate 3 ^ (j : ℕ)) i) * w ^ (j : ℕ) := by
          rw [hπeq i]
      _ = y ((finRotate 3 ^ (j : ℕ)).symm ((finRotate 3 ^ (j : ℕ)) i)) :=
          cafSyl_inv_w_pow_conj hw (j : ℕ) ((finRotate 3 ^ (j : ℕ)) i)
      _ = y i := by rw [Equiv.symm_apply_apply]
  have hcy : ∀ i, c * y i * c⁻¹ = y i ^ e i := by
    intro i
    calc c * y i * c⁻¹
        = (w ^ (j : ℕ))⁻¹ * (x * y i * x⁻¹) * w ^ (j : ℕ) := by
          change ((w ^ (j : ℕ))⁻¹ * x) * y i * ((w ^ (j : ℕ))⁻¹ * x)⁻¹ =
            (w ^ (j : ℕ))⁻¹ * (x * y i * x⁻¹) * w ^ (j : ℕ)
          group
      _ = (w ^ (j : ℕ))⁻¹ * y (π i) ^ e i * w ^ (j : ℕ) := by rw [hxe i]
      _ = ((w ^ (j : ℕ))⁻¹ * y (π i) * w ^ (j : ℕ)) ^ e i := by
          have hconj := conj_pow (a := (w ^ (j : ℕ))⁻¹) (b := y (π i)) (i := e i)
          simpa using hconj.symm
      _ = y i ^ e i := by rw [hwj i]
  have hc2 : ∀ i, c ^ 2 * y i * (c ^ 2)⁻¹ = y i := by
    intro i
    calc c ^ 2 * y i * (c ^ 2)⁻¹
        = c * (c * y i * c⁻¹) * c⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
      _ = c * y i ^ e i * c⁻¹ := by rw [hcy i]
      _ = (c * y i * c⁻¹) ^ e i := by
          have hconj := conj_pow (a := c) (b := y i) (i := e i)
          simpa using hconj.symm
      _ = (y i ^ e i) ^ e i := by rw [hcy i]
      _ = y i ^ (e i * e i) := by rw [pow_mul]
      _ = y i := by
          rcases he1 i with hei | hei
          · rw [hei]; simp
          · rw [hei, show 2 * 2 = 4 by norm_num]
            calc y i ^ 4 = y i ^ 3 * y i := by group
              _ = y i := by rw [hp i, one_mul]
  have hcQ : c ∈ Q := Q.mul_mem (Q.inv_mem (Q.pow_mem hwQ (j : ℕ))) hxQ
  obtain ⟨k', hck'⟩ := hQ.exists_pow_pow_eq_one (⟨c, hcQ⟩ : ↥Q)
  have hckG : c ^ 3 ^ k' = 1 := by simpa using congrArg Subtype.val hck'
  have hodd : Odd (3 ^ k') := Odd.pow (by norm_num : Odd (3 : ℕ))
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul hckG hodd 1
  have hc2comm : ∀ i, c ^ 2 * y i = y i * c ^ 2 := by
    intro i
    calc c ^ 2 * y i = (c ^ 2 * y i * (c ^ 2)⁻¹) * c ^ 2 := by group
      _ = y i * c ^ 2 := by rw [hc2 i]
  have hc_eq : c = (c ^ 2) ^ m := by
    calc c = c ^ 1 := (pow_one c).symm
      _ = c ^ (2 * m) := hm
      _ = (c ^ 2) ^ m := by rw [pow_mul]
  refine ⟨(j : ℕ), ?_⟩
  intro i
  have hcomm : c * y i = y i * c := by
    let d : G := c ^ 2
    have hdcomm : d * y i = y i * d := hc2comm i
    have hpowcomm : ∀ n : ℕ, d ^ n * y i = y i * d ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        calc d ^ n * d * y i = d ^ n * (d * y i) := by group
          _ = d ^ n * (y i * d) := by rw [hdcomm]
          _ = (d ^ n * y i) * d := by group
          _ = (y i * d ^ n) * d := by rw [ih]
          _ = y i * (d ^ n * d) := by group
    rw [hc_eq]
    change d ^ m * y i = y i * d ^ m
    exact hpowcomm m
  simpa [c] using hcomm

theorem conj_mem_tor_of_mem_normalizer (hp : ∀ i, y i ^ 3 = 1)
    (hc : ∀ i j, y i * y j = y j * y i) (hinj : ∀ v, vecElt y v = 1 → v = 0) {w : G}
    (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i)) (hw3 : w ^ 3 ∈ GGFF.tor y) {x : G}
    (hx : x ∈ Subgroup.normalizer ((GGFF.tor y ⊔ Subgroup.zpowers w : Subgroup G) : Set G)) :
    ∀ β ∈ GGFF.tor y, x * β * x⁻¹ ∈ GGFF.tor y := by
  obtain ⟨t, hf, hwreath, hcard⟩ := cafSyl_exists_wreath hp hc hinj hw hw3
  let E : Subgroup G := (GGFF.tor y).map (MulAut.conj x).toMonoidHom
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    (GGFF.isElemAbelian_tor hp hc).map (MulAut.conj x).toMonoidHom
  have hEcard : Nat.card E = 27 := by
    rw [show E = (GGFF.tor y).map (MulAut.conj x).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj x).injective, GGFF.card_tor hp hc hinj]
  have hEP : E ≤ GGFF.tor y ⊔ Subgroup.zpowers w := by
    rintro e ⟨β, hβ, rfl⟩
    have hβP : β ∈ GGFF.tor y ⊔ Subgroup.zpowers w := Subgroup.mem_sup_left hβ
    have := (Subgroup.mem_normalizer_iff.mp hx β).mp hβP
    simpa [MulAut.conj_apply] using this
  have hEW : E ≤ CFSG.RankThree.PartTwo.Sec4.Item434Kit.wreathW y t := by
    rw [hwreath]
    exact hEP
  have hEeq : E = GGFF.tor y := by
    have h := CFSG.RankThree.PartTwo.Sec4.Item434Kit.eq_baseA_of_le_wreathW hf hcard hEW
      hEab hEcard
    rw [h, ← cafSyl_tor_eq_baseA]
  intro β hβ
  have hmem : (MulAut.conj x).toMonoidHom β ∈ E :=
    Subgroup.mem_map_of_mem _ hβ
  rw [hEeq] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem eq_sup_of_le (hp : ∀ i, y i ^ 3 = 1) (hc : ∀ i j, y i * y j = y j * y i)
    (hinj : ∀ v, vecElt y v = 1 → v = 0) {w : G} (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i))
    (hw3 : w ^ 3 ∈ GGFF.tor y) {H : Subgroup G}
    (hlines : ∀ x ∈ H, (∀ β ∈ GGFF.tor y, x * β * x⁻¹ ∈ GGFF.tor y) →
      ∀ i, ∃ j, x * y i * x⁻¹ ∈ Subgroup.zpowers (y j))
    (hcen : ∀ x ∈ H, (∃ k : ℕ, x ^ 3 ^ k = 1) → (∀ i, x * y i = y i * x) → x ∈ GGFF.tor y)
    {Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsPGroup 3 Q)
    (hPQ : GGFF.tor y ⊔ Subgroup.zpowers w ≤ Q) :
    Q = GGFF.tor y ⊔ Subgroup.zpowers w := by
  set P : Subgroup G := GGFF.tor y ⊔ Subgroup.zpowers w with hP
  by_contra hne
  have hPQ' : P ≤ Q := hPQ
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne ?_
    exact (le_antisymm hPQ' (Subgroup.subgroupOf_eq_top.mp htop)).symm
  have hnc : NormalizerCondition ↥Q :=
    Group.normalizerCondition_of_isNilpotent (h := hQ.isNilpotent)
  obtain ⟨x, hxN, hxnotP⟩ := IsConcreteLE.exists_of_lt (hnc (P.subgroupOf Q) hlt)
  have hxQ : (x : G) ∈ Q := x.2
  have hxH : (x : G) ∈ H := hQH x.2
  have hxNor : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
    have h := hxN
    rw [← Subgroup.subgroupOf_normalizer_eq hPQ'] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hxB : ∀ β ∈ GGFF.tor y, (x : G) * β * (x : G)⁻¹ ∈ GGFF.tor y :=
    conj_mem_tor_of_mem_normalizer hp hc hinj hw hw3 hxNor
  have hwQ : w ∈ Q := hPQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  have hxlines := hlines (x : G) hxH hxB
  obtain ⟨j, hj⟩ := exists_pow_inv_mul_comm hp hc hinj hw hQ hwQ hxQ hxlines
  let c : G := (w ^ j)⁻¹ * (x : G)
  have hcQ : c ∈ Q := Q.mul_mem (Q.inv_mem (Q.pow_mem hwQ j)) x.2
  have hcH : c ∈ H := hQH hcQ
  obtain ⟨k, hck⟩ := hQ.exists_pow_pow_eq_one (⟨c, hcQ⟩ : ↥Q)
  have hckG : c ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hck
  have hcB : c ∈ GGFF.tor y := hcen c hcH ⟨k, hckG⟩ hj
  have hxP : (x : G) ∈ P := by
    have hxeq : (x : G) = w ^ j * c := by
      change (x : G) = w ^ j * ((w ^ j)⁻¹ * (x : G))
      group
    rw [hxeq]
    exact P.mul_mem (P.pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)) j)
      (Subgroup.mem_sup_left hcB)
  exact hxnotP (Subgroup.mem_subgroupOf.mpr hxP)

theorem exists_conj_mem_sup (hp : ∀ i, y i ^ 3 = 1) (hc : ∀ i j, y i * y j = y j * y i)
    (hinj : ∀ v, vecElt y v = 1 → v = 0) {w : G} (hw : ∀ i, w * y i * w⁻¹ = y (finRotate 3 i))
    (hw3 : w ^ 3 ∈ GGFF.tor y) {H : Subgroup G} (hwH : w ∈ H) (hyH : ∀ i, y i ∈ H)
    (hlines : ∀ x ∈ H, (∀ β ∈ GGFF.tor y, x * β * x⁻¹ ∈ GGFF.tor y) →
      ∀ i, ∃ j, x * y i * x⁻¹ ∈ Subgroup.zpowers (y j))
    (hcen : ∀ x ∈ H, (∃ k : ℕ, x ^ 3 ^ k = 1) → (∀ i, x * y i = y i * x) → x ∈ GGFF.tor y)
    {c : G} (hcH : c ∈ H) {k : ℕ} (hck : c ^ 3 ^ k = 1) :
    ∃ h ∈ H, h * c * h⁻¹ ∈ GGFF.tor y ⊔ Subgroup.zpowers w := by
  obtain ⟨t, hf, hwreath, hcard⟩ := cafSyl_exists_wreath hp hc hinj hw hw3
  set P : Subgroup G := GGFF.tor y ⊔ Subgroup.zpowers w with hP
  have hPleH : P ≤ H := by
    rw [hP, GGFF.tor]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hwH)
    exact (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hyH i)
  have hPwreath : P = CFSG.RankThree.PartTwo.Sec4.Item434Kit.wreathW y t :=
    hP.trans hwreath.symm
  have hPgroup : IsPGroup 3 P := by
    rw [hPwreath]
    exact CFSG.RankThree.PartTwo.Sec4.Item434Kit.isPGroup_wreathW hf
  have hPHgroup : IsPGroup 3 ↥(P.subgroupOf H) :=
    hPgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPleH).symm
  obtain ⟨S, hPS⟩ := hPHgroup.exists_le_sylow
  let Q : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hQgroup : IsPGroup 3 Q := S.isPGroup'.map H.subtype
  have hPQ : P ≤ Q := by
    have hmap : Subgroup.map H.subtype (P.subgroupOf H) ≤
        Subgroup.map H.subtype (S : Subgroup ↥H) := Subgroup.map_mono hPS
    rwa [Subgroup.map_subgroupOf_eq_of_le hPleH] at hmap
  have hQeq : Q = P := eq_sup_of_le hp hc hinj hw hw3 hlines hcen hQH hQgroup hPQ
  have hSP : (S : Subgroup ↥H).map H.subtype = P := hQeq
  let c' : ↥H := ⟨c, hcH⟩
  have hc'pow : c' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hck)
  have hdvd : orderOf c' ∣ 3 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hc'pow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hzpc : IsPGroup 3 (Subgroup.zpowers c' : Subgroup ↥H) := by
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, hj]
  obtain ⟨S', hS'⟩ := hzpc.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) S S'
  have hc'S' : c' ∈ (S' : Subgroup ↥H) := hS' (Subgroup.mem_zpowers c')
  have hc'S : (MulAut.conj g)⁻¹ • c' ∈ (S : Subgroup ↥H) := by
    have h := hc'S'
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    exact h
  have hmemH : (g : G)⁻¹ * c * (g : G) ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem g.2) hcH) g.2
  have hsymm : (MulAut.conj g).symm c' = ⟨(g : G)⁻¹ * c * (g : G), hmemH⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [c', MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcoe : (((MulAut.conj g)⁻¹ • c' : ↥H) : G) = (g : G)⁻¹ * c * (g : G) := by
    rw [MulAut.smul_def, MulAut.inv_apply, hsymm]
  have hmemP : (g : G)⁻¹ * c * (g : G) ∈ P := by
    have hmap : H.subtype ((MulAut.conj g)⁻¹ • c') ∈
        (S : Subgroup ↥H).map H.subtype := Subgroup.mem_map_of_mem _ hc'S
    rw [hSP] at hmap
    simpa [hcoe] using hmap
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, ?_⟩
  simpa [hP, inv_inv] using hmemP

end CFSG.StandardType.FF81.CentA

end
