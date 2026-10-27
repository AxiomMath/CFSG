module

public import CFSG.RankThree.GF2n.Tim79Heis

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement
open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

structure GammaReg (QF V : Subgroup G) (γ : G → K) : Prop where
  V_le : V ≤ QF
  add : ∀ a ∈ V, ∀ b ∈ V, γ (a * b) = γ a + γ b
  inj : ∀ a ∈ V, γ a = 0 → a = 1
  surj : ∀ s : K, ∃ a ∈ V, γ a = s

theorem GammaReg.one (R : GammaReg QF V γ) : γ 1 = 0 := by
  have h := R.add 1 V.one_mem 1 V.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

namespace QuadModel

variable (M₀ : QuadModel QF V K γ)

theorem pi_one : M₀.π 1 = 0 := by
  have h := M₀.π_mul 1 QF.one_mem 1 QF.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem pi_inv {x : G} (hx : x ∈ QF) : M₀.π x⁻¹ = - M₀.π x := by
  have h := M₀.π_mul x hx x⁻¹ (QF.inv_mem hx)
  rw [mul_inv_cancel, pi_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem pi_eq_iff {x y : G} (hx : x ∈ QF) (hy : y ∈ QF) :
    M₀.π x = M₀.π y ↔ x⁻¹ * y ∈ V := by
  rw [← M₀.π_ker _ (QF.mul_mem (QF.inv_mem hx) hy), M₀.π_mul _ (QF.inv_mem hx) _ hy,
    pi_inv M₀ hx, neg_add_eq_zero, eq_comm]

@[expose] def img (S : Subgroup G) : AddSubgroup M₀.E where
  carrier := {e | ∃ x ∈ S, x ∈ QF ∧ M₀.π x = e}
  add_mem' := by
    rintro _ _ ⟨x, hxS, hxQ, rfl⟩ ⟨y, hyS, hyQ, rfl⟩
    exact ⟨x * y, S.mul_mem hxS hyS, QF.mul_mem hxQ hyQ, M₀.π_mul x hxQ y hyQ⟩
  zero_mem' := ⟨1, S.one_mem, QF.one_mem, pi_one M₀⟩
  neg_mem' := by
    rintro _ ⟨x, hxS, hxQ, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hxS, QF.inv_mem hxQ, pi_inv M₀ hxQ⟩

theorem mem_img {S : Subgroup G} {e : M₀.E} :
    e ∈ M₀.img S ↔ ∃ x ∈ S, x ∈ QF ∧ M₀.π x = e := Iff.rfl

theorem pi_mem_img {S : Subgroup G} {x : G} (hxS : x ∈ S) (hxQ : x ∈ QF) :
    M₀.π x ∈ M₀.img S := ⟨x, hxS, hxQ, rfl⟩

theorem mem_img_iff {S : Subgroup G} (hVS : V ≤ S) {x : G} (hx : x ∈ QF) :
    M₀.π x ∈ M₀.img S ↔ x ∈ S := by
  constructor
  · rintro ⟨y, hyS, hyQ, hyx⟩
    have h1 : y⁻¹ * x ∈ V := (pi_eq_iff M₀ hyQ hx).mp hyx
    have h2 : y * (y⁻¹ * x) = x := by group
    rw [← h2]
    exact S.mul_mem hyS (hVS h1)
  · exact fun hxS => pi_mem_img M₀ hxS hx

theorem img_mono {S T : Subgroup G} (h : S ≤ T) : M₀.img S ≤ M₀.img T := by
  rintro _ ⟨x, hxS, hxQ, rfl⟩
  exact ⟨x, h hxS, hxQ, rfl⟩

theorem card_eq {S : Subgroup G} (hS : S ≤ QF) (hVS : V ≤ S) :
    Nat.card S = Nat.card V * Nat.card (M₀.img S) := by
  let φ : S →* Multiplicative M₀.E :=
    { toFun := fun x => Multiplicative.ofAdd (M₀.π x)
      map_one' := by simp [pi_one M₀]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [M₀.π_mul x (hS x.2) y (hS y.2)]
        rfl }
  have hker : φ.ker = V.subgroupOf S := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (M₀.π x) = 1 ↔ _
    rw [← M₀.π_ker _ (hS x.2)]
    exact ofAdd_eq_one
  have hrange : Nat.card φ.range = Nat.card (M₀.img S) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨Multiplicative.toAdd y.1, ?_⟩
        invFun := fun e => ⟨Multiplicative.ofAdd e.1, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun e => rfl }
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
      exact ⟨x, x.2, hS x.2, congrArg Multiplicative.toAdd hx⟩
    · obtain ⟨x, hxS, hxQ, hx⟩ := e.2
      exact MonoidHom.mem_range.mpr ⟨⟨x, hxS⟩, by simp [φ, hx]⟩
  have hcard : Nat.card φ.ker = Nat.card V := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv
  rw [← hcard, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]


theorem comm_iff_B (R : GammaReg QF V γ) {x y : G} (hx : x ∈ QF) (hy : y ∈ QF) :
    x * y = y * x ↔ M₀.B (M₀.π x) (M₀.π y) = 0 := by
  rw [← M₀.comm_eq x hx y hy, ← commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro h
    rw [h]
    exact R.one
  · intro h
    exact R.inj _ (M₀.comm_mem x hx y hy) h

theorem sq_iff_Qf (R : GammaReg QF V γ) {x : G} (hx : x ∈ QF) :
    x ^ 2 = 1 ↔ M₀.Qf (M₀.π x) = 0 := by
  rw [← M₀.sq_eq x hx]
  constructor
  · intro h
    rw [h]
    exact R.one
  · intro h
    exact R.inj _ (M₀.sq_mem x hx) h

theorem isElemAbelian_iff (R : GammaReg QF V γ) {S : Subgroup G} (hS : S ≤ QF) :
    CFSG.Open.IsElemAbelian 2 S ↔ ∀ e ∈ M₀.img S, M₀.Qf e = 0 := by
  constructor
  · rintro ⟨-, hsq⟩ e ⟨x, hxS, hxQ, rfl⟩
    exact (sq_iff_Qf M₀ R hxQ).mp (hsq x hxS)
  · intro h
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · refine (comm_iff_B M₀ R (hS a.2) (hS b.2)).mpr ?_
      have h1 := M₀.Qf_add (M₀.π a) (M₀.π b)
      rw [← M₀.π_mul a (hS a.2) b (hS b.2)] at h1
      have h2 := h _ (pi_mem_img M₀ (S.mul_mem a.2 b.2) (QF.mul_mem (hS a.2) (hS b.2)))
      rw [h _ (pi_mem_img M₀ a.2 (hS a.2)), h _ (pi_mem_img M₀ b.2 (hS b.2)), h2] at h1
      simpa using h1.symm
    · exact (sq_iff_Qf M₀ R (hS hx)).mpr (h _ (pi_mem_img M₀ hx (hS hx)))

theorem commute_iff (R : GammaReg QF V γ) {S T : Subgroup G} (hS : S ≤ QF) (hT : T ≤ QF) :
    (∀ x ∈ S, ∀ y ∈ T, x * y = y * x) ↔ ∀ e ∈ M₀.img S, ∀ f ∈ M₀.img T, M₀.B e f = 0 := by
  constructor
  · rintro h _ ⟨x, hxS, hxQ, rfl⟩ _ ⟨y, hyT, hyQ, rfl⟩
    exact (comm_iff_B M₀ R hxQ hyQ).mp (h x hxS y hyT)
  · intro h x hx y hy
    exact (comm_iff_B M₀ R (hS hx) (hT hy)).mpr
      (h _ (pi_mem_img M₀ hx (hS hx)) _ (pi_mem_img M₀ hy (hT hy)))

@[expose] def IsLine (U : Subgroup G) : Prop :=
  ∃ e : M₀.E, e ≠ 0 ∧ ∀ v : M₀.E, v ∈ M₀.img U ↔ ∃ s : K, v = s • e

variable {M₀}

theorem Qf_zero : M₀.Qf 0 = 0 := by
  simpa using M₀.Qf_smul 0 0

theorem B_comm (e f : M₀.E) : M₀.B e f = - M₀.B f e := by
  have h := M₀.alt (e + f)
  simp only [map_add, LinearMap.add_apply, M₀.alt] at h
  linear_combination h

theorem IsLine.qf_zero (R : GammaReg QF V γ) {U : Subgroup G} (hU : U ≤ QF)
    (hel : CFSG.Open.IsElemAbelian 2 U) {e : M₀.E}
    (he : ∀ v : M₀.E, v ∈ M₀.img U ↔ ∃ s : K, v = s • e) : M₀.Qf e = 0 :=
  (isElemAbelian_iff M₀ R hU).mp hel e ((he e).mpr ⟨1, (one_smul K e).symm⟩)

theorem centralizer_iff (R : GammaReg QF V γ) {U : Subgroup G} (hU : U ≤ QF) {e : M₀.E}
    (he : ∀ v : M₀.E, v ∈ M₀.img U ↔ ∃ s : K, v = s • e) {x : G} (hx : x ∈ QF) :
    x ∈ Subgroup.centralizer (U : Set G) ↔ M₀.B (M₀.π x) e = 0 := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    obtain ⟨u, huU, huQ, hu⟩ := (he e).mpr ⟨1, (one_smul K e).symm⟩
    rw [← hu]
    exact (comm_iff_B M₀ R hx huQ).mp (h u huU).symm
  · intro h u huU
    refine ((comm_iff_B M₀ R (hU huU) hx).mpr ?_)
    obtain ⟨s, hs⟩ := (he _).mp (pi_mem_img M₀ huU (hU huU))
    have h2 : M₀.B e (M₀.π x) = 0 := by rw [B_comm, h, neg_zero]
    rw [hs, map_smul, LinearMap.smul_apply, h2, smul_zero]

theorem img_centralizer (R : GammaReg QF V γ) {U : Subgroup G} (hU : U ≤ QF) {e : M₀.E}
    (he : ∀ v : M₀.E, v ∈ M₀.img U ↔ ∃ s : K, v = s • e) {v : M₀.E} :
    v ∈ M₀.img (QF ⊓ Subgroup.centralizer (U : Set G)) ↔ M₀.B v e = 0 := by
  constructor
  · rintro ⟨x, hx, hxQ, rfl⟩
    exact (centralizer_iff R hU he hxQ).mp hx.2
  · intro h
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
    exact ⟨x, ⟨hxQ, (centralizer_iff R hU he hxQ).mpr h⟩, hxQ, rfl⟩

theorem card_centralizer [Finite G] (R : GammaReg QF V γ) {U : Subgroup G} (hU : U ≤ QF)
    {e : M₀.E} (he0 : e ≠ 0) (he : ∀ v : M₀.E, v ∈ M₀.img U ↔ ∃ s : K, v = s • e) :
    Nat.card QF = Nat.card ↥(QF ⊓ Subgroup.centralizer (U : Set G)) * Nat.card K := by
  let φ : QF →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd (M₀.B (M₀.π x) e)
      map_one' := by simp [pi_one M₀]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [M₀.π_mul x x.2 y y.2, map_add, LinearMap.add_apply]
        rfl }
  have hker : φ.ker = (QF ⊓ Subgroup.centralizer (U : Set G)).subgroupOf QF := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show Multiplicative.ofAdd (M₀.B (M₀.π x) e) = 1 ↔ _
    rw [ofAdd_eq_one, ← centralizer_iff R hU he x.2]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨f, hf⟩ : ∃ f, M₀.B f e ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact he0 (M₀.nondeg e fun f => by rw [B_comm, hcon f, neg_zero])
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj ((Multiplicative.toAdd y / M₀.B f e) • f)
    refine ⟨⟨x, hxQ⟩, ?_⟩
    show Multiplicative.ofAdd (M₀.B (M₀.π x) e) = y
    rw [hx, map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hf]
    rfl
  have hrange : Nat.card φ.range = Nat.card K := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
    exact Nat.card_congr (Subgroup.topEquiv.toEquiv.trans Multiplicative.toAdd)
  have hcard : Nat.card φ.ker = Nat.card ↥(QF ⊓ Subgroup.centralizer (U : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hcard, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]


theorem pi_conj_self {x y : G} (hx : x ∈ QF) (hy : y ∈ QF) : M₀.π (x * y * x⁻¹) = M₀.π y := by
  have h1 : ⁅x, y⁆ ∈ V := M₀.comm_mem x hx y hy
  have h2 : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  rw [h2]
  have h3 : ⁅x, y⁆ ∈ QF := by
    rw [commutatorElement_def]
    exact QF.mul_mem (QF.mul_mem (QF.mul_mem hx hy) (QF.inv_mem hx)) (QF.inv_mem hy)
  rw [M₀.π_mul _ h3 _ hy, (M₀.π_ker _ h3).mpr h1, zero_add]

theorem comm_mem_iff {m x : G} (hx : x ∈ QF) (hm : m * x * m⁻¹ ∈ QF) :
    ⁅m, x⁆ ∈ V ↔ M₀.π (m * x * m⁻¹) = M₀.π x := by
  have h1 : ⁅m, x⁆ = (m * x * m⁻¹) * x⁻¹ := by rw [commutatorElement_def]
  have h2 : ⁅m, x⁆ ∈ QF := by rw [h1]; exact QF.mul_mem hm (QF.inv_mem hx)
  rw [← M₀.π_ker _ h2, h1, M₀.π_mul _ hm _ (QF.inv_mem hx), pi_inv M₀ hx, add_neg_eq_zero]

end QuadModel

theorem GammaReg.conj (R : GammaReg QF V γ) (g : G) :
    GammaReg (conjSubgroup g QF) (conjSubgroup g V) (fun x => γ (g⁻¹ * x * g)) where
  V_le := fun x hx => mem_conjSubgroup.mpr (R.V_le (mem_conjSubgroup.mp hx))
  add := fun a ha b hb => by
    rw [show g⁻¹ * (a * b) * g = g⁻¹ * a * g * (g⁻¹ * b * g) by group]
    exact R.add _ (mem_conjSubgroup.mp ha) _ (mem_conjSubgroup.mp hb)
  inj := fun a ha h => by
    have h1 := R.inj _ (mem_conjSubgroup.mp ha) h
    have h2 : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    rw [h2, h1]
    group
  surj := fun s => by
    obtain ⟨a, ha, h⟩ := R.surj s
    refine ⟨g * a * g⁻¹, mem_conjSubgroup.mpr ?_, ?_⟩
    · rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
      exact ha
    · show γ (g⁻¹ * (g * a * g⁻¹) * g) = s
      rw [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
      exact h

namespace QuadModel

@[expose] def conj (M₀ : QuadModel QF V K γ) (g : G) :
    QuadModel (conjSubgroup g QF) (conjSubgroup g V) K (fun x => γ (g⁻¹ * x * g)) where
  E := M₀.E
  acg := M₀.acg
  mod := M₀.mod
  fin := M₀.fin
  π := fun x => M₀.π (g⁻¹ * x * g)
  B := M₀.B
  Qf := M₀.Qf
  π_mul := fun x hx y hy => by
    rw [show g⁻¹ * (x * y) * g = g⁻¹ * x * g * (g⁻¹ * y * g) by group]
    exact M₀.π_mul _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
  π_surj := fun e => by
    obtain ⟨x, hx, hxe⟩ := M₀.π_surj e
    refine ⟨g * x * g⁻¹, mem_conjSubgroup.mpr ?_, ?_⟩
    · rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx
    · show M₀.π (g⁻¹ * (g * x * g⁻¹) * g) = e
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hxe
  π_ker := fun x hx => by
    rw [M₀.π_ker _ (mem_conjSubgroup.mp hx), mem_conjSubgroup]
  comm_mem := fun x hx y hy => by
    rw [mem_conjSubgroup,
      show g⁻¹ * ⁅x, y⁆ * g = ⁅g⁻¹ * x * g, g⁻¹ * y * g⁆ by
        simp only [commutatorElement_def]; group]
    exact M₀.comm_mem _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
  sq_mem := fun x hx => by
    rw [mem_conjSubgroup, show g⁻¹ * x ^ 2 * g = (g⁻¹ * x * g) ^ 2 by
      rw [pow_two, pow_two]; group]
    exact M₀.sq_mem _ (mem_conjSubgroup.mp hx)
  comm_eq := fun x hx y hy => by
    rw [show g⁻¹ * ⁅x, y⁆ * g = ⁅g⁻¹ * x * g, g⁻¹ * y * g⁆ by
      simp only [commutatorElement_def]; group]
    exact M₀.comm_eq _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
  sq_eq := fun x hx => by
    rw [show g⁻¹ * x ^ 2 * g = (g⁻¹ * x * g) ^ 2 by rw [pow_two, pow_two]; group]
    exact M₀.sq_eq _ (mem_conjSubgroup.mp hx)
  alt := M₀.alt
  nondeg := M₀.nondeg
  Qf_smul := M₀.Qf_smul
  Qf_add := M₀.Qf_add

theorem mem_img_conj (M₀ : QuadModel QF V K γ) (g : G) {S : Subgroup G} (e : (M₀.conj g).E) :
    e ∈ (M₀.conj g).img (conjSubgroup g S) ↔ (show M₀.E from e) ∈ M₀.img S := by
  constructor
  · rintro ⟨x, hxS, hxQ, hx⟩
    exact ⟨g⁻¹ * x * g, mem_conjSubgroup.mp hxS, mem_conjSubgroup.mp hxQ, hx⟩
  · rintro ⟨x, hxS, hxQ, hx⟩
    refine ⟨g * x * g⁻¹, mem_conjSubgroup.mpr ?_, mem_conjSubgroup.mpr ?_, ?_⟩
    · rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hxS
    · rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hxQ
    · show M₀.π (g⁻¹ * (g * x * g⁻¹) * g) = e
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hx

end QuadModel

end CFSG.RankThree.GF2n.Tim79
