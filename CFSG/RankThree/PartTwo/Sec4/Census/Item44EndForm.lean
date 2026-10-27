module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

structure CommData (P : Type*) [Group P] (z : P) : Prop where
  mem_center : z ∈ Subgroup.center P
  sq_eq_one : z * z = 1
  ne_one : z ≠ 1
  comm_mem : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.zpowers z
  sq_mem : ∀ x : P, x * x ∈ Subgroup.center P

variable {P : Type*} [Group P] {z : P}

namespace CommData

theorem mem_zpowers_iff (h : CommData P z) {c : P} : c ∈ Subgroup.zpowers z ↔ c = 1 ∨ c = z := by
  constructor
  · rintro ⟨n, rfl⟩
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, h.sq_eq_one]
    have hn : z ^ n = z ^ (n % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
      rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      simp only
      rw [hn, h0, zpow_zero]
    · right
      simp only
      rw [hn, h1, zpow_one]
  · rintro (h1 | h1) <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z

theorem card_zpowers (h : CommData P z) : Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq, h.sq_eq_one]) h.ne_one

theorem nonempty_mulEquiv (h : CommData P z) :
    Nonempty (Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := h.card_zpowers
  have := isCyclic_of_prime_card hc
  exact ⟨(zmodCyclicMulEquiv this).symm.trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hc).toAddEquiv)⟩

theorem comm_mem_center (h : CommData P z) (x y : P) : ⁅x, y⁆ ∈ Subgroup.center P :=
  (Subgroup.zpowers_le.mpr h.mem_center) (h.comm_mem x y)

theorem comm_mul_left (h : CommData P z) (x x' y : P) : ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
  have hc := Subgroup.mem_center_iff.mp (h.comm_mem_center x' y) x
  simp only [commutatorElement_def] at hc ⊢
  calc x * x' * y * (x * x')⁻¹ * y⁻¹ = x * (x' * y * x'⁻¹ * y⁻¹) * y * x⁻¹ * y⁻¹ := by group
    _ = x' * y * x'⁻¹ * y⁻¹ * x * y * x⁻¹ * y⁻¹ := by rw [hc]
    _ = x' * y * x'⁻¹ * y⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group

theorem comm_mul_right (h : CommData P z) (x y y' : P) : ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have hc := Subgroup.mem_center_iff.mp (h.comm_mem_center x y') y
  simp only [commutatorElement_def] at hc ⊢
  calc x * (y * y') * x⁻¹ * (y * y')⁻¹ = x * y * x⁻¹ * y⁻¹ * (y * (x * y' * x⁻¹ * y'⁻¹)) * y⁻¹ := by
        group
    _ = x * y * x⁻¹ * y⁻¹ * (x * y' * x⁻¹ * y'⁻¹ * y) * y⁻¹ := by rw [hc]
    _ = x * y * x⁻¹ * y⁻¹ * (x * y' * x⁻¹ * y'⁻¹) := by group

theorem comm_eq_one_of_mem_center {c : P} (hc : c ∈ Subgroup.center P) (y : P) : ⁅c, y⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp hc y).symm

end CommData

theorem isElementaryAbelian_quot (h : CommData P z) :
    IsElementaryAbelian 2 (P ⧸ Subgroup.center P) := by
  have hcomm : ∀ a b : P ⧸ Subgroup.center P, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have := h.comm_mem_center y⁻¹ x⁻¹
        rw [commutatorElement_def] at this
        convert this using 1
        group
  refine { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, sq]
    exact h.sq_mem x

@[expose] noncomputable def commVal (h : CommData P z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) (x y : P) : ZMod 2 :=
  Multiplicative.toAdd (ε ⟨⁅x, y⁆, h.comm_mem x y⟩)

theorem commVal_mul_left (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (x x' y : P) : commVal h ε (x * x') y = commVal h ε x y + commVal h ε x' y := by
  simp only [commVal]
  rw [← toAdd_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [h.comm_mul_left]
  exact (Subgroup.mem_center_iff.mp (h.comm_mem_center x' y) _).symm

theorem commVal_mul_right (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (x y y' : P) : commVal h ε x (y * y') = commVal h ε x y + commVal h ε x y' := by
  simp only [commVal]
  rw [← toAdd_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact h.comm_mul_right x y y'

theorem commVal_eq_zero_iff (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (x y : P) : commVal h ε x y = 0 ↔ ⁅x, y⁆ = 1 := by
  simp only [commVal]
  rw [← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one ε, ε.injective.eq_iff,
    Subtype.ext_iff, OneMemClass.coe_one]

theorem commVal_of_mem_center (h : CommData P z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) {c : P} (hc : c ∈ Subgroup.center P)
    (y : P) : commVal h ε c y = 0 :=
  (commVal_eq_zero_iff h ε c y).mpr (CommData.comm_eq_one_of_mem_center hc y)

theorem commVal_of_mem_center_right (h : CommData P z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) (x : P) {c : P}
    (hc : c ∈ Subgroup.center P) : commVal h ε x c = 0 := by
  rw [commVal_eq_zero_iff, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.mp hc x

@[expose] noncomputable def commB (h : CommData P z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) :
    P ⧸ Subgroup.center P → P ⧸ Subgroup.center P → ZMod 2 :=
  fun a b => Quotient.liftOn₂' a b (commVal h ε) fun x y x' y' hx hy => by
    obtain ⟨c, rfl⟩ : ∃ c, x' = x * c := ⟨x⁻¹ * x', by group⟩
    obtain ⟨d, rfl⟩ : ∃ d, y' = y * d := ⟨y⁻¹ * y', by group⟩
    have hc : c ∈ Subgroup.center P := by
      have := QuotientGroup.leftRel_apply.mp hx
      simpa using this
    have hd : d ∈ Subgroup.center P := by
      have := QuotientGroup.leftRel_apply.mp hy
      simpa using this
    rw [commVal_mul_left, commVal_mul_right, commVal_mul_right, commVal_of_mem_center h ε hc,
      commVal_of_mem_center_right h ε x hd, commVal_of_mem_center_right h ε c hd]
    ring

theorem commB_mk (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (x y : P) : commB h ε (x : P ⧸ Subgroup.center P) y = commVal h ε x y :=
  rfl

theorem commB_mul_left (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (u v t : P ⧸ Subgroup.center P) : commB h ε (u * v) t = commB h ε u t + commB h ε v t := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    induction v using QuotientGroup.induction_on with
    | H x' =>
      induction t using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul]
        exact commVal_mul_left h ε x x' y

theorem commB_mul_right (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (u v t : P ⧸ Subgroup.center P) : commB h ε u (v * t) = commB h ε u v + commB h ε u t := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    induction v using QuotientGroup.induction_on with
    | H y =>
      induction t using QuotientGroup.induction_on with
      | H y' =>
        rw [← QuotientGroup.mk_mul]
        exact commVal_mul_right h ε x y y'

theorem commB_self (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (u : P ⧸ Subgroup.center P) : commB h ε u u = 0 := by
  induction u using QuotientGroup.induction_on with
  | H x => exact (commVal_eq_zero_iff h ε x x).mpr (commutatorElement_self x)

theorem eq_one_of_commB (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    (u : P ⧸ Subgroup.center P) (hu : ∀ v, commB h ε u v = 0) : u = 1 := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    have := (commVal_eq_zero_iff h ε x y).mp (hu y)
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm

@[expose] noncomputable def quotAut : MulAut P →* MulAut (P ⧸ Subgroup.center P) :=
  quotientAutomorphism (Subgroup.center P)

theorem quotAut_mk (σ : MulAut P) (x : P) :
    quotAut σ (x : P ⧸ Subgroup.center P) = (σ x : P ⧸ Subgroup.center P) :=
  quotientAutomorphism_apply (Subgroup.center P) σ x

theorem commB_quotAut (h : CommData P z) (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2))
    {σ : MulAut P} (hσ : σ z = z) (u v : P ⧸ Subgroup.center P) :
    commB h ε (quotAut σ u) (quotAut σ v) = commB h ε u v := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    induction v using QuotientGroup.induction_on with
    | H y =>
      rw [quotAut_mk, quotAut_mk, commB_mk, commB_mk, commVal, commVal]
      congr 2
      apply Subtype.ext
      change ⁅σ x, σ y⁆ = ⁅x, y⁆
      rw [← map_commutatorElement]
      rcases h.mem_zpowers_iff.mp (h.comm_mem x y) with h1 | hz
      · rw [h1, map_one]
      · rw [hz, hσ]

theorem sq_mem_zpowers (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (x : P) : x * x ∈ Subgroup.zpowers z :=
  hZ ▸ h.sq_mem x

@[expose] noncomputable def quadVal (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) (x : P) : ZMod 2 :=
  Multiplicative.toAdd (ε ⟨x * x, sq_mem_zpowers h hZ x⟩)

theorem sq_mul_eq (h : CommData P z) (x y : P) :
    (x * y) * (x * y) = (x * x) * (y * y) * ⁅x, y⁆ := by
  have hyx : y * x = ⁅y, x⁆ * (x * y) := by
    simp only [commutatorElement_def]
    group
  have hinv : ⁅y, x⁆ = ⁅x, y⁆ := by
    have h1 : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := (commutatorElement_inv x y).symm
    rw [h1]
    rcases h.mem_zpowers_iff.mp (h.comm_mem x y) with h1' | hz
    · rw [h1', inv_one]
    · rw [hz, inv_eq_of_mul_eq_one_right h.sq_eq_one]
  have hc := Subgroup.mem_center_iff.mp (h.comm_mem_center x y)
  calc (x * y) * (x * y) = x * (y * x) * y := by group
    _ = x * (⁅x, y⁆ * (x * y)) * y := by rw [hyx, hinv]
    _ = (x * ⁅x, y⁆) * (x * y) * y := by group
    _ = (⁅x, y⁆ * x) * (x * y) * y := by rw [hc x]
    _ = ⁅x, y⁆ * (x * x * (y * y)) := by group
    _ = (x * x) * (y * y) * ⁅x, y⁆ := (hc _).symm

theorem quadVal_mul (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) (x y : P) :
    quadVal h hZ ε (x * y) = quadVal h hZ ε x + quadVal h hZ ε y + commVal h ε x y := by
  simp only [quadVal, commVal]
  rw [← toAdd_mul, ← toAdd_mul, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact sq_mul_eq h x y

theorem quadVal_of_mem_center (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) {c : P} (hc : c ∈ Subgroup.center P) :
    quadVal h hZ ε c = 0 := by
  have hc' : c * c = 1 := by
    rw [hZ] at hc
    rcases h.mem_zpowers_iff.mp hc with rfl | rfl
    · rw [one_mul]
    · exact h.sq_eq_one
  simp only [quadVal]
  rw [← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one ε]
  congr 1
  exact Subtype.ext hc'

@[expose] noncomputable def quadQ (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) : P ⧸ Subgroup.center P → ZMod 2 :=
  fun a => Quotient.liftOn' a (quadVal h hZ ε) fun x x' hx => by
    obtain ⟨c, rfl⟩ : ∃ c, x' = x * c := ⟨x⁻¹ * x', by group⟩
    have hc : c ∈ Subgroup.center P := by
      have := QuotientGroup.leftRel_apply.mp hx
      simpa using this
    rw [quadVal_mul, quadVal_of_mem_center h hZ ε hc, commVal_of_mem_center_right h ε x hc]
    ring

theorem quadQ_mk (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) (x : P) :
    quadQ h hZ ε (x : P ⧸ Subgroup.center P) = quadVal h hZ ε x :=
  rfl

theorem quadQ_mul (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) (u v : P ⧸ Subgroup.center P) :
    quadQ h hZ ε (u * v) = quadQ h hZ ε u + quadQ h hZ ε v + commB h ε u v := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    induction v using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul]
      exact quadVal_mul h hZ ε x y

theorem quadQ_eq_zero_iff (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) (x : P) :
    quadQ h hZ ε (x : P ⧸ Subgroup.center P) = 0 ↔ x * x = 1 := by
  rw [quadQ_mk, quadVal, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one ε,
    ε.injective.eq_iff, Subtype.ext_iff, OneMemClass.coe_one]

theorem quadQ_quotAut (h : CommData P z) (hZ : Subgroup.center P = Subgroup.zpowers z)
    (ε : Subgroup.zpowers z ≃* Multiplicative (ZMod 2)) {σ : MulAut P} (hσ : σ z = z)
    (u : P ⧸ Subgroup.center P) : quadQ h hZ ε (quotAut σ u) = quadQ h hZ ε u := by
  induction u using QuotientGroup.induction_on with
  | H x =>
    rw [quotAut_mk, quadQ_mk, quadQ_mk, quadVal, quadVal]
    congr 2
    apply Subtype.ext
    change σ x * σ x = x * x
    rw [← map_mul]
    rcases h.mem_zpowers_iff.mp (sq_mem_zpowers h hZ x) with h1 | hz
    · rw [h1, map_one]
    · rw [hz, hσ]

end CFSG.RankThree.PartTwo.Sec4.Census
