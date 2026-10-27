module

public import CFSG.Quasithin.H13.A6S13829a
public import CFSG.Quasithin.H13.A6S13833d

public section

namespace CFSG.Quasithin.H13.A6

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

section Lin6

variable {M : Type*} [AddCommGroup M]

@[expose] def lin6 (m : Fin 6 → M) (h2 : ∀ a : M, a + a = 0) : (Fin 6 → ZMod 2) →+ M where
  toFun x := ∑ p, (x p).val • m p
  map_zero' := by simp
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.add_apply]
    rcases zmodTwo_cases (x p) with h | h <;> rcases zmodTwo_cases (y p) with h' | h' <;>
      rw [h, h'] <;> simp [ZMod.val_one, h2, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem lin6_single (m : Fin 6 → M) (h2 : ∀ a : M, a + a = 0) (p : Fin 6) :
    lin6 m h2 (Pi.single p 1) = m p := by
  simp only [lin6, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single p]
  · simp [ZMod.val_one]
  · intro q _ hq
    simp [hq]
  · simp

theorem vec6_decomp (x : Fin 6 → ZMod 2) : x = ∑ p, x p • (Pi.single p 1 : Fin 6 → ZMod 2) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem additive6_eq_zero (f : (Fin 6 → ZMod 2) →+ M) (hb : ∀ p, f (Pi.single p 1) = 0) :
    ∀ x, f x = 0 := by
  intro x
  rw [vec6_decomp x, map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases zmodTwo_cases (x p) with h | h
  · rw [h, zero_smul, map_zero]
  · rw [h, one_smul, hb]

end Lin6

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

noncomputable abbrev UHin : Subgroup ↥(conjClosure V S.G1) :=
  (conjClosure S.V3 S.G1).subgroupOf (conjClosure V S.G1)

abbrev VUQ : Type := Additive (↥(conjClosure V S.G1) ⧸ S.UHin)

@[expose] noncomputable def cls (v : ↥(conjClosure V S.G1)) : S.VUQ :=
  Additive.ofMul (QuotientGroup.mk v)

theorem cls_eq_iff (v w : ↥(conjClosure V S.G1)) :
    S.cls v = S.cls w ↔ (v : G)⁻¹ * w ∈ conjClosure S.V3 S.G1 := by
  rw [cls, cls, Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

@[expose] noncomputable def cV (h : ↥S.G1) : ↥(conjClosure V S.G1) →* ↥(conjClosure V S.G1) where
  toFun v := ⟨h * v * (h : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V S.G1 h.2) v).mp v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem cV_coe (h : ↥S.G1) (v : ↥(conjClosure V S.G1)) :
    ((S.cV h v : ↥(conjClosure V S.G1)) : G) = h * v * (h : G)⁻¹ := rfl

section Quot

variable [IsMulCommutative ↥(conjClosure V S.G1)]

theorem cls_mul (v w : ↥(conjClosure V S.G1)) : S.cls (v * w) = S.cls v + S.cls w := rfl

theorem cls_eq_zero_iff (v : ↥(conjClosure V S.G1)) :
    S.cls v = 0 ↔ (v : G) ∈ conjClosure S.V3 S.G1 := by
  rw [cls, ← ofMul_one, Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]

theorem cls_add_self (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (a : S.VUQ) : a + a = 0 := by
  induction a using Additive.rec with
  | _ q =>
    induction q using QuotientGroup.induction_on with
    | _ v =>
      show S.cls v + S.cls v = 0
      rw [← cls_mul, cls_eq_zero_iff]
      have h := hF.F911_2.2 v v.2
      have e : ((v * v : ↥(conjClosure V S.G1)) : G) = (v : G) ^ 2 := by
        rw [Subgroup.coe_mul, pow_two]
      rw [e, h]
      exact (conjClosure S.V3 S.G1).one_mem

@[expose] noncomputable def act (h : ↥S.G1) : S.VUQ →+ S.VUQ :=
  (QuotientGroup.map S.UHin S.UHin (S.cV h) fun v hv => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, cV_coe]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 h.2) v).mp
      (Subgroup.mem_subgroupOf.mp hv)).toAdditive

theorem act_cls (h : ↥S.G1) (v : ↥(conjClosure V S.G1)) : S.act h (S.cls v) = S.cls (S.cV h v) :=
  rfl

end Quot

section Hat

variable (ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
  (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2))

@[expose] def rv (h : ↥S.G1) (x : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec x

theorem rv_mul (h k : ↥S.G1) (x : Fin 4 → ZMod 2) : S.rv ρ (h * k) x = S.rv ρ h (S.rv ρ k x) := by
  simp only [rv, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem rv_add (h : ↥S.G1) (x y : Fin 4 → ZMod 2) :
    S.rv ρ h (x + y) = S.rv ρ h x + S.rv ρ h y := Matrix.mulVec_add _ _ _

theorem rv_smul (h : ↥S.G1) (s : ZMod 2) (x : Fin 4 → ZMod 2) :
    S.rv ρ h (s • x) = s • S.rv ρ h x := Matrix.mulVec_smul _ _ _

theorem rv_inv_rv (h : ↥S.G1) (x : Fin 4 → ZMod 2) : S.rv ρ h⁻¹ (S.rv ρ h x) = x := by
  rw [← rv_mul, inv_mul_cancel]
  simp [rv]

theorem pl_rv (h : ↥S.G1) (a b : Fin 4 → ZMod 2) :
    pl (S.rv ρ h a) (S.rv ρ h b) =
      (wedge2 ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec (pl a b) :=
  (wedge2_mulVec_pl _ a b).symm

@[expose] def bv (u : ↥(conjClosure S.V3 S.G1)) : Fin 4 → ZMod 2 := Multiplicative.toAdd (β u)

theorem bv_mul (u v : ↥(conjClosure S.V3 S.G1)) : S.bv β (u * v) = S.bv β u + S.bv β v := by
  simp [bv]

theorem bv_inv (u : ↥(conjClosure S.V3 S.G1)) : S.bv β u⁻¹ = S.bv β u := by
  show Multiplicative.toAdd (β u⁻¹) = Multiplicative.toAdd (β u)
  rw [map_inv β u, toAdd_inv]
  exact neg_eq_of_add_eq_zero_right (add_self_vec4 _)

@[expose] noncomputable def w1 : Fin 4 → ZMod 2 := S.bv β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩

@[expose] noncomputable def w2 : Fin 4 → ZMod 2 := S.bv β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩

@[expose] noncomputable def v04 : G := ((S.frame.ψ.symm ⟨dv 0 4, by decide⟩ : ↥V) : G)

theorem v04_mem_V : S.v04 ∈ V := (S.frame.ψ.symm _).2

theorem v04_not_mem_V3 : S.v04 ∉ S.V3 := by
  intro h
  obtain ⟨hV, hW⟩ := S.mem_pre.1 h
  have e : (⟨S.v04, hV⟩ : ↥V) = S.frame.ψ.symm ⟨dv 0 4, by decide⟩ := rfl
  rw [e, MulEquiv.apply_symm_apply] at hW
  exact absurd (show InW3 (dv 0 4) from hW) (by decide)

@[expose] noncomputable def v0H : ↥(conjClosure V S.G1) :=
  ⟨S.v04, le_conjClosure V S.G1 S.v04_mem_V⟩

end Hat

section HatFacts

variable {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}

theorem bv_eq_zero_iff (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (u : ↥(conjClosure S.V3 S.G1)) : S.bv β u = 0 ↔ (u : G) ∈ fsuV1 T V := by
  rw [bv, toAdd_eq_zero, hβk]

theorem bv_eq_iff (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (u v : ↥(conjClosure S.V3 S.G1)) :
    S.bv β u = S.bv β v ↔ ((u * v⁻¹ : ↥(conjClosure S.V3 S.G1)) : G) ∈ fsuV1 T V := by
  rw [← S.bv_eq_zero_iff hβk, bv_mul, bv_inv]
  constructor
  · intro h
    rw [h, add_self_vec4]
  · exact eq_of_add_eq_zero_vec4

theorem bv_V3 (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (u : ↥(conjClosure S.V3 S.G1)) (hu : (u : G) ∈ S.V3) :
    ∃ s₁ s₂ : ZMod 2, S.bv β u = s₁ • S.w1 β + s₂ • S.w2 β := by
  obtain ⟨hV, hW⟩ := S.mem_pre.1 hu
  have hc := w3_cases _ (S.frame.ψ ⟨(u : G), hV⟩).2 hW
  set y : P6 := (S.frame.ψ ⟨(u : G), hV⟩ : P6) with hy
  have hu1 : S.u1 ∈ V := S.u1_mem_V
  have hu2 : S.u2 ∈ V := S.u2_mem_V
  have key : ∀ (x : G) (hx : x ∈ V),
      (S.frame.ψ ⟨(u : G) * x⁻¹, V.mul_mem hV (V.inv_mem hx)⟩ : P6) =
        y * (S.frame.ψ ⟨x, hx⟩ : P6)⁻¹ := by
    intro x hx
    have e : (⟨(u : G) * x⁻¹, V.mul_mem hV (V.inv_mem hx)⟩ : ↥V) =
        ⟨(u : G), hV⟩ * (⟨x, hx⟩ : ↥V)⁻¹ := rfl
    rw [e, map_mul, map_inv]
    rfl
  rcases hc with h | h | h | h
  · refine ⟨0, 0, ?_⟩
    rw [zero_smul, zero_smul, add_zero, S.bv_eq_zero_iff hβk]
    exact (S.mem_V1_iff_psi hV).2 h
  · refine ⟨1, 0, ?_⟩
    rw [one_smul, zero_smul, add_zero, w1, S.bv_eq_iff hβk]
    refine (S.mem_V1_iff_psi (V.mul_mem hV (V.inv_mem hu1))).2 ?_
    rw [key S.u1 hu1, S.psi_u1]
    exact h
  · refine ⟨0, 1, ?_⟩
    rw [one_smul, zero_smul, zero_add, w2, S.bv_eq_iff hβk]
    refine (S.mem_V1_iff_psi (V.mul_mem hV (V.inv_mem hu2))).2 ?_
    rw [key S.u2 hu2, S.psi_u2]
    exact h
  · refine ⟨1, 1, ?_⟩
    rw [one_smul, one_smul, w1, w2, ← bv_mul, S.bv_eq_iff hβk]
    have h12 : S.u1 * S.u2 ∈ V := V.mul_mem hu1 hu2
    refine (S.mem_V1_iff_psi (V.mul_mem hV (V.inv_mem h12))).2 ?_
    have e : (⟨S.u1 * S.u2, h12⟩ : ↥V) = ⟨S.u1, S.u1_mem_V⟩ * ⟨S.u2, S.u2_mem_V⟩ := rfl
    rw [key _ h12, e, map_mul, Subgroup.coe_mul, S.psi_u1, S.psi_u2]
    exact h

theorem mem_V3_of_bv (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (x : ↥(conjClosure S.V3 S.G1)) {s₁ s₂ : ZMod 2}
    (hx : S.bv β x = s₁ • S.w1 β + s₂ • S.w2 β) : (x : G) ∈ S.V3 := by
  have hV3 : ∀ y : ↥(conjClosure S.V3 S.G1), (y : G) ∈ S.V3 → S.bv β x = S.bv β y →
      (x : G) ∈ S.V3 := by
    intro y hy hxy
    have h1 := (S.bv_eq_iff hβk x y).1 hxy
    have e : (x : G) = ((x * y⁻¹ : ↥(conjClosure S.V3 S.G1)) : G) * y := by
      simp
    rw [e]
    exact S.V3.mul_mem (S.V1_le_V3 h1) hy
  rcases zmodTwo_cases s₁ with h₁ | h₁ <;> rcases zmodTwo_cases s₂ with h₂ | h₂ <;>
    rw [h₁, h₂] at hx <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hx
  · refine hV3 1 S.V3.one_mem ?_
    rw [hx]
    simp [bv]
  · exact hV3 _ S.u2_mem_V3 hx
  · exact hV3 _ S.u1_mem_V3 hx
  · refine hV3 (⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ * ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩)
      (S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3) ?_
    rw [hx, bv_mul]
    rfl

theorem pl_w1_w2_ne_zero
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) :
    pl (S.w1 β) (S.w2 β) ≠ 0 := by
  obtain ⟨-, -, -, -, -, h01a, h01b, h02a, h02b, h21a, h21b, -⟩ := dv_facts
  rw [pl_ne_zero_iff]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [w1, S.bv_eq_zero_iff hβk, S.mem_V1_iff_psi S.u1_mem_V, S.psi_u1] at h
    rcases h with h | h
    · exact h01a h
    · exact h01b h
  · rw [w2, S.bv_eq_zero_iff hβk, S.mem_V1_iff_psi S.u2_mem_V, S.psi_u2] at h
    rcases h with h | h
    · exact h02a h
    · exact h02b h
  · rw [w1, w2, eq_comm, S.bv_eq_iff hβk] at h
    have hm : S.u2 * S.u1⁻¹ ∈ V := V.mul_mem S.u2_mem_V (V.inv_mem S.u1_mem_V)
    rw [show ((⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩ * (⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩ :
      ↥(conjClosure S.V3 S.G1))⁻¹ : ↥(conjClosure S.V3 S.G1)) : G) = S.u2 * S.u1⁻¹ from rfl,
      S.mem_V1_iff_psi hm] at h
    have e : (⟨S.u2 * S.u1⁻¹, hm⟩ : ↥V) = ⟨S.u2, S.u2_mem_V⟩ * (⟨S.u1, S.u1_mem_V⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, S.psi_u2, S.psi_u1] at h
    rcases h with h | h
    · exact h21a h
    · exact h21b h

end HatFacts

theorem exists_comb_of_mem_span {a b x : Fin 4 → ZMod 2}
    (h : x = 0 ∨ x = a ∨ x = b ∨ x = a + b) : ∃ s₁ s₂ : ZMod 2, x = s₁ • a + s₂ • b := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by simp⟩
  · exact ⟨1, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · exact ⟨1, 1, by simp⟩

section PhiSec

variable [IsMulCommutative ↥(conjClosure V S.G1)]
  (ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
  (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2))

open scoped Classical in
@[expose] noncomputable def Phi (ω : Fin 6 → ZMod 2) : S.VUQ :=
  if hω : ∃ k : ↥S.G1, pl (S.rv ρ k (S.w1 β)) (S.rv ρ k (S.w2 β)) = ω then
    S.cls (S.cV (Classical.choose hω) S.v0H) else 0

variable {ρ β}

theorem Phi_spec (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)))
    (k : ↥S.G1) :
    S.Phi ρ β (pl (S.rv ρ k (S.w1 β)) (S.rv ρ k (S.w2 β))) = S.cls (S.cV k S.v0H) := by
  have hex : ∃ k' : ↥S.G1, pl (S.rv ρ k' (S.w1 β)) (S.rv ρ k' (S.w2 β)) =
      pl (S.rv ρ k (S.w1 β)) (S.rv ρ k (S.w2 β)) := ⟨k, rfl⟩
  rw [Phi, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h, hspec⟩ : ∃ h : ↥S.G1, h = Classical.choose hex := ⟨_, rfl⟩
  have hhs : pl (S.rv ρ h (S.w1 β)) (S.rv ρ h (S.w2 β)) =
      pl (S.rv ρ k (S.w1 β)) (S.rv ρ k (S.w2 β)) := hspec ▸ Classical.choose_spec hex
  rw [← hspec]
  have hy : pl (S.rv ρ (h⁻¹ * k) (S.w1 β)) (S.rv ρ (h⁻¹ * k) (S.w2 β)) =
      pl (S.w1 β) (S.w2 β) := by
    rw [rv_mul, rv_mul, pl_rv, ← hhs, ← pl_rv, rv_inv_rv, rv_inv_rv]
  have h0 := S.pl_w1_w2_ne_zero hβk
  obtain ⟨t₁, t₂, ht₁⟩ := exists_comb_of_mem_span (mem_span_of_pl_eq hy h0)
  obtain ⟨t₃, t₄, ht₂⟩ := exists_comb_of_mem_span (mem_span_of_pl_eq
    (by rw [pl_comm, hy]) h0 : S.rv ρ (h⁻¹ * k) (S.w2 β) = 0 ∨ _)
  set y : ↥S.G1 := h⁻¹ * k with hydef
  have hyU : ∀ u ∈ conjClosure S.V3 S.G1, (y : G) * u * (y : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
    fun u hu => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 y.2) u).mp hu
  have hyV3 : ∀ u ∈ S.V3, (y : G) * u * (y : G)⁻¹ ∈ S.V3 := by
    intro u hu
    obtain ⟨s₁, s₂, hs⟩ := S.bv_V3 hβk ⟨u, S.V3_le_UH hu⟩ hu
    refine S.mem_V3_of_bv hβk ⟨_, hyU u (S.V3_le_UH hu)⟩
      (s₁ := s₁ * t₁ + s₂ * t₃) (s₂ := s₁ * t₂ + s₂ * t₄) ?_
    have e := hβe y ⟨u, S.V3_le_UH hu⟩ ⟨_, hyU u (S.V3_le_UH hu)⟩ rfl
    change S.bv β _ = S.rv ρ y (S.bv β ⟨u, S.V3_le_UH hu⟩) at e
    rw [e, hs, rv_add, rv_smul, rv_smul, ht₁, ht₂]
    simp only [smul_add, add_smul, mul_smul]
    abel
  have hyN3 : (y : G) ∈ Subgroup.normalizer (S.V3 : Set G) := S.mem_normalizer_V3_of_le hyV3
  have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := hF.toHypF91.normalizer_le ⟨y.2, hyN3⟩
  have hyv : (y : G) * S.v04 * (y : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hyN _).mp S.v04_mem_V
  have hyv3 : (y : G) * S.v04 * (y : G)⁻¹ ∉ S.V3 := by
    intro h3
    apply S.v04_not_mem_V3
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN3) _).mp h3
    simpa [mul_assoc] using this
  have hmod : (S.v04)⁻¹ * ((y : G) * S.v04 * (y : G)⁻¹) ∈ S.V3 :=
    inv_mul_mem_of_relIndex_two S.relIndex_V3_V S.v04_mem_V hyv S.v04_not_mem_V3 hyv3
  rw [cls_eq_iff, cV_coe, cV_coe]
  have hk : (k : G) = h * y := by rw [hydef]; simp
  have e : ((h : G) * S.v04 * (h : G)⁻¹)⁻¹ * ((k : G) * S.v04 * (k : G)⁻¹) =
      (h : G) * ((S.v04)⁻¹ * ((y : G) * S.v04 * (y : G)⁻¹)) * (h : G)⁻¹ := by
    rw [hk]
    group
  rw [show ((S.v0H : ↥(conjClosure V S.G1)) : G) = S.v04 from rfl, e]
  exact mem_conjClosure h.2 hmod

theorem Phi_zero (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) :
    S.Phi ρ β 0 = 0 := by
  have hne : ¬ ∃ k : ↥S.G1, pl (S.rv ρ k (S.w1 β)) (S.rv ρ k (S.w2 β)) = 0 := by
    rintro ⟨k, hk⟩
    apply S.pl_w1_w2_ne_zero hβk
    rw [← rv_inv_rv (ρ := ρ) S k (S.w1 β), ← rv_inv_rv (ρ := ρ) S k (S.w2 β), pl_rv, hk,
      Matrix.mulVec_zero]
  rw [Phi, dite_eq_right_of_eq_false (eq_false hne)]

end PhiSec

theorem add_self_vec6 (x : Fin 6 → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact (by decide : ∀ s : ZMod 2, s + s = 0) _

theorem pl_single_cases : ∀ i j : Fin 4, pl (Pi.single i 1) (Pi.single j 1) = 0 ∨
    ∃ p : Fin 6, pl (Pi.single i 1) (Pi.single j 1) = Pi.single p 1 := by
  decide

section Theta

variable [IsMulCommutative ↥(conjClosure V S.G1)]
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}

omit [IsMulCommutative ↥(conjClosure V S.G1)] in
theorem exists_k_of_pl (hρs : Function.Surjective ρ)
    (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    {a b : Fin 4 → ZMod 2} (hab : pl a b ≠ 0) :
    ∃ k : ↥S.G1, S.rv ρ k (S.w1 β) = a ∧ S.rv ρ k (S.w2 β) = b := by
  obtain ⟨ha, hb, hne⟩ := (pl_ne_zero_iff a b).1 hab
  obtain ⟨w1n, w2n, w12⟩ := (pl_ne_zero_iff _ _).1 (S.pl_w1_w2_ne_zero hβk)
  obtain ⟨c, d, hcd⟩ := exists_basis_of_pair w1n w2n w12
  obtain ⟨c', d', hcd'⟩ := exists_basis_of_pair ha hb hne
  obtain ⟨g, hg1, hg2, -, -⟩ := exists_GL_map4 hcd hcd'
  obtain ⟨k, hk⟩ := hρs g
  exact ⟨k, by rw [rv, hk, hg1], by rw [rv, hk, hg2]⟩

variable (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hρs : Function.Surjective ρ)
  (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)))
include hF hρs hβk hβe

theorem Phi_equiv (h : ↥S.G1) (a b : Fin 4 → ZMod 2) :
    S.Phi ρ β (pl (S.rv ρ h a) (S.rv ρ h b)) = S.act h (S.Phi ρ β (pl a b)) := by
  by_cases hab : pl a b = 0
  · have h0 : pl (S.rv ρ h a) (S.rv ρ h b) = 0 := by rw [pl_rv, hab, Matrix.mulVec_zero]
    rw [h0, hab, S.Phi_zero hβk, map_zero]
  · obtain ⟨k, hk1, hk2⟩ := S.exists_k_of_pl hρs hβk hab
    have e : pl (S.rv ρ h a) (S.rv ρ h b) =
        pl (S.rv ρ (h * k) (S.w1 β)) (S.rv ρ (h * k) (S.w2 β)) := by
      rw [rv_mul, rv_mul, hk1, hk2]
    rw [e, S.Phi_spec hF hβk hβe, ← hk1, ← hk2, S.Phi_spec hF hβk hβe, act_cls]
    congr 1
    apply Subtype.ext
    simp only [cV_coe, Subgroup.coe_mul]
    group

omit hρs hβe in
theorem Phi_add_right (hline : ∀ a b c : Fin 4 → ZMod 2, pl a b ≠ 0 → pl a c ≠ 0 →
      pl a b ≠ pl a c → S.Phi ρ β (pl a b) + S.Phi ρ β (pl a c) = S.Phi ρ β (pl a (b + c)))
    (a b c : Fin 4 → ZMod 2) :
    S.Phi ρ β (pl a (b + c)) = S.Phi ρ β (pl a b) + S.Phi ρ β (pl a c) := by
  by_cases h1 : pl a b = 0
  · rw [pl_add_right, h1, zero_add, S.Phi_zero hβk, zero_add]
  by_cases h2 : pl a c = 0
  · rw [pl_add_right, h2, add_zero, S.Phi_zero hβk, add_zero]
  by_cases h3 : pl a b = pl a c
  · rw [pl_add_right, h3, add_self_vec6, S.Phi_zero hβk, S.cls_add_self hF]
  exact (hline a b c h1 h2 h3).symm

end Theta

@[expose] noncomputable def Theta [IsMulCommutative ↥(conjClosure V S.G1)]
    (ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2))
    (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) : (Fin 6 → ZMod 2) →+ S.VUQ :=
  lin6 (fun p => S.Phi ρ β (Pi.single p 1)) (S.cls_add_self hF)

section Theta2

variable [IsMulCommutative ↥(conjClosure V S.G1)]
  {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hρs : Function.Surjective ρ)
  (hβk : ∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)))
  (hline : ∀ a b c : Fin 4 → ZMod 2, pl a b ≠ 0 → pl a c ≠ 0 →
      pl a b ≠ pl a c → S.Phi ρ β (pl a b) + S.Phi ρ β (pl a c) = S.Phi ρ β (pl a (b + c)))
include hF hβk hline

theorem Phi_eq_Theta (a b : Fin 4 → ZMod 2) :
    S.Phi ρ β (pl a b) = S.Theta ρ β hF (pl a b) := by
  have key := biadditive_eq_zero (fun a b => S.Phi ρ β (pl a b) - S.Theta ρ β hF (pl a b))
    (fun a b c => by
      rw [pl_comm (a + b), pl_comm a, pl_comm b, S.Phi_add_right hF hβk hline, pl_add_right,
        map_add]
      abel)
    (fun a b c => by
      rw [S.Phi_add_right hF hβk hline, pl_add_right, map_add]
      abel)
    (fun i j => by
      rcases pl_single_cases i j with h | ⟨p, h⟩
      · rw [h, S.Phi_zero hβk, map_zero, sub_zero]
      · rw [h, Theta, lin6_single, sub_self])
  exact sub_eq_zero.mp (key a b)

include hρs hβe in
theorem Theta_equiv (h : ↥S.G1) (x : Fin 6 → ZMod 2) :
    S.Theta ρ β hF ((wedge2 ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec x) = S.act h (S.Theta ρ β hF x) := by
  let f : (Fin 6 → ZMod 2) →+ S.VUQ :=
    { toFun := fun x => S.Theta ρ β hF ((wedge2 ((ρ h : Matrix.GeneralLinearGroup (Fin 4)
        (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec x) - S.act h (S.Theta ρ β hF x)
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Matrix.mulVec_add, map_add]
        abel }
  have hf := additive6_eq_zero f fun p => by
    show S.Theta ρ β hF _ - S.act h (S.Theta ρ β hF _) = 0
    have hp := pl_single p
    rw [← hp, ← pl_rv, ← S.Phi_eq_Theta hF hβk hline, ← S.Phi_eq_Theta hF hβk hline,
      S.Phi_equiv hF hρs hβk hβe, sub_self]
  exact sub_eq_zero.mp (hf x)

include hβe in
theorem Theta_surjective : Function.Surjective (S.Theta ρ β hF) := by
  have hinv : ∀ x ∈ conjClosure V S.G1, x⁻¹ = x := fun x hx => by
    have := hF.F911_2.2 x hx
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  let K' : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ conjClosure V S.G1,
        S.cls ⟨x, hx⟩ ∈ (S.Theta ρ β hF : (Fin 6 → ZMod 2) →+ S.VUQ).range}
      mul_mem' := by
        rintro x y ⟨hx, hxr⟩ ⟨hy, hyr⟩
        refine ⟨(conjClosure V S.G1).mul_mem hx hy, ?_⟩
        have e : (⟨x * y, (conjClosure V S.G1).mul_mem hx hy⟩ : ↥(conjClosure V S.G1)) =
            ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [e, cls_mul]
        exact AddSubgroup.add_mem _ hxr hyr
      one_mem' := ⟨(conjClosure V S.G1).one_mem, by
        have : S.cls (1 : ↥(conjClosure V S.G1)) = 0 :=
          (S.cls_eq_zero_iff 1).2 (conjClosure S.V3 S.G1).one_mem
        rw [show (⟨1, (conjClosure V S.G1).one_mem⟩ : ↥(conjClosure V S.G1)) = 1 from rfl, this]
        exact AddSubgroup.zero_mem _⟩
      inv_mem' := by
        rintro x ⟨hx, hxr⟩
        refine ⟨(conjClosure V S.G1).inv_mem hx, ?_⟩
        have e : (⟨x⁻¹, (conjClosure V S.G1).inv_mem hx⟩ : ↥(conjClosure V S.G1)) = ⟨x, hx⟩ :=
          Subtype.ext (hinv x hx)
        rw [e]
        exact hxr }
  have hle : conjClosure V S.G1 ≤ K' := conjClosure_le fun h hh z hz => by
    refine ⟨mem_conjClosure hh hz, ?_⟩
    by_cases hz3 : z ∈ S.V3
    · have : S.cls ⟨h * z * h⁻¹, mem_conjClosure hh hz⟩ = 0 :=
        (S.cls_eq_zero_iff _).2 (mem_conjClosure hh hz3)
      rw [this]
      exact AddSubgroup.zero_mem _
    · have hm := inv_mul_mem_of_relIndex_two S.relIndex_V3_V S.v04_mem_V hz S.v04_not_mem_V3 hz3
      have e : S.cls ⟨h * z * h⁻¹, mem_conjClosure hh hz⟩ = S.cls (S.cV ⟨h, hh⟩ S.v0H) := by
        rw [cls_eq_iff, cV_coe]
        have e2 : (h * z * h⁻¹)⁻¹ * (h * S.v04 * h⁻¹) = h * ((S.v04)⁻¹ * z)⁻¹ * h⁻¹ := by group
        rw [show ((S.v0H : ↥(conjClosure V S.G1)) : G) = S.v04 from rfl, e2]
        exact mem_conjClosure hh (S.V3.inv_mem hm)
      rw [e, ← S.Phi_spec hF hβk hβe, S.Phi_eq_Theta hF hβk hline]
      exact ⟨_, rfl⟩
  intro q
  induction q using Additive.rec with
  | _ q =>
    induction q using QuotientGroup.induction_on with
    | _ v =>
      obtain ⟨hv, hr⟩ := hle v.2
      exact hr

include hρs hβe in
theorem Theta_injective (hv0 : S.v04 ∉ conjClosure S.V3 S.G1) :
    Function.Injective (S.Theta ρ β hF) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have htop := wedge2_irred (S.Theta ρ β hF).ker (fun g y hy => by
    obtain ⟨k, hk⟩ := hρs g
    rw [AddMonoidHom.mem_ker] at hy ⊢
    rw [← hk, S.Theta_equiv hF hρs hβk hβe hline, hy, map_zero]) hx hx0
  have h1 : pl (S.w1 β) (S.w2 β) ∈ (S.Theta ρ β hF).ker := by
    rw [htop]
    exact AddSubgroup.mem_top _
  rw [AddMonoidHom.mem_ker, ← S.Phi_eq_Theta hF hβk hline] at h1
  have e : pl (S.w1 β) (S.w2 β) = pl (S.rv ρ 1 (S.w1 β)) (S.rv ρ 1 (S.w2 β)) := by
    simp [rv]
  rw [e, S.Phi_spec hF hβk hβe, cls_eq_zero_iff, cV_coe] at h1
  apply hv0
  have h2 : (1 : G) * S.v04 * (1 : G)⁻¹ ∈ conjClosure S.V3 S.G1 := h1
  simpa using h2

end Theta2

end Setting4

end CFSG.Quasithin.H13.A6
