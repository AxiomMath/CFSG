module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3P

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn
open scoped commutatorElement

local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def Agrp (x y u v : G) : Subgroup G := Subgroup.closure {x, y, u, v}

structure PCtx (b : G) (J B : Subgroup G) (u v r₁ r₂ w : G) (P : Subgroup G) (x y : G) : Prop
    extends Ctx b J B u v r₁ r₂ w where
  hP : IsSylowOf 3 P (Nor B)
  hBP : B ≤ P
  hx : x ∈ P
  hy : y ∈ P
  θx : θ b x = u
  θy : θ b y = v
  xy : x * y = y * x

theorem Ctx.exists_PCtx {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G}
    (C : Ctx b J B u v r₁ r₂ w) : ∃ P x y, PCtx b J B u v r₁ r₂ w P x y := by
  obtain ⟨P, hP, hBP⟩ := C.exists_P
  obtain ⟨x, hx, y, hy, h1, h2, h3⟩ := C.exists_comm_pair hP hBP
  exact ⟨P, x, y, { C with hP, hBP, hx, hy, θx := h1, θy := h2, xy := h3 }⟩

namespace PCtx

variable {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G} {P : Subgroup G} {x y : G}
  (K : PCtx b J B u v r₁ r₂ w P x y)
include K

theorem xT : x ∈ T b B (R u v) := K.toCtx.P_le_T K.hP K.hx

theorem yT : y ∈ T b B (R u v) := K.toCtx.P_le_T K.hP K.hy

theorem u_ne : u ≠ 1 := fun h => by
  have := ψ_eq_one K.toCtx.E (p := (1, 0)) (by rw [ψ_10]; exact h)
  exact absurd (Prod.ext_iff.mp this).1 (by decide)

theorem gens_comm : ({x, y, u, v} : Set G).Pairwise Commute := by
  have hxu : Commute x u := (Subgroup.mem_centralizer_iff.mp K.xT.2.1 u K.toCtx.uR).symm
  have hxv : Commute x v := (Subgroup.mem_centralizer_iff.mp K.xT.2.1 v K.toCtx.vR).symm
  have hyu : Commute y u := (Subgroup.mem_centralizer_iff.mp K.yT.2.1 u K.toCtx.uR).symm
  have hyv : Commute y v := (Subgroup.mem_centralizer_iff.mp K.yT.2.1 v K.toCtx.vR).symm
  have hxy : Commute x y := K.xy
  have huv : Commute u v := K.toCtx.comm_R K.toCtx.uR K.toCtx.vR
  intro a ha c hc _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl <;>
    first
    | exact Commute.refl _
    | assumption
    | exact Commute.symm (by assumption)

theorem A_commutative : IsMulCommutative (Agrp x y u v) :=
  Subgroup.isMulCommutative_closure K.gens_comm

theorem A_comm {a c : G} (ha : a ∈ Agrp x y u v) (hc : c ∈ Agrp x y u v) : a * c = c * a := by
  have := K.A_commutative.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩
  exact congrArg Subtype.val this

theorem xA : x ∈ Agrp x y u v := Subgroup.subset_closure (by simp)

theorem yA : y ∈ Agrp x y u v := Subgroup.subset_closure (by simp)

theorem R_le_A : R u v ≤ Agrp x y u v :=
  Subgroup.closure_mono (by intro z hz; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz ⊢; tauto)

theorem A_le_P : Agrp x y u v ≤ P := by
  refine (Subgroup.closure_le _).mpr ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact K.hx
  · exact K.hy
  · exact K.hBP (K.toCtx.R_le_B K.toCtx.uR)
  · exact K.hBP (K.toCtx.R_le_B K.toCtx.vR)

theorem A_le_T : Agrp x y u v ≤ T b B (R u v) := K.A_le_P.trans (K.toCtx.P_le_T K.hP)

theorem mem_R_of_B {a : G} (haB : a ∈ B) (hax : x * a = a * x) : a ∈ R u v := by
  obtain ⟨k, q, rfl⟩ := (K.toCtx.mem_B_iff).mp haB
  have hq := ψ_mem K.toCtx.E q
  have e1 : x * b ^ k.val * x⁻¹ = u ^ k.val * b ^ k.val := by
    rw [← conj_pow, K.toCtx.conj_b_T K.xT, K.θx]
    exact (Commute.mul_pow (K.toCtx.comm_bR K.toCtx.uR).symm _)
  have e2 : x * ψ u v q * x⁻¹ = ψ u v q := K.toCtx.T_cen K.xT hq
  have e3 : x * (b ^ k.val * ψ u v q) * x⁻¹ = u ^ k.val * (b ^ k.val * ψ u v q) := by
    calc x * (b ^ k.val * ψ u v q) * x⁻¹ = (x * b ^ k.val * x⁻¹) * (x * ψ u v q * x⁻¹) := by
          group
      _ = _ := by rw [e1, e2]; group
  have e4 : x * (b ^ k.val * ψ u v q) * x⁻¹ = b ^ k.val * ψ u v q := by
    rw [hax]; group
  have hu : u ^ k.val = 1 := by
    have := e3.symm.trans e4
    simpa using this
  have hk : k = 0 := by
    have h0 : ψ u v (k, 0) = 1 := by
      show u ^ k.val * v ^ (0 : ZMod 3).val = 1
      rw [hu, ZMod.val_zero, pow_zero, mul_one]
    exact (Prod.ext_iff.mp (ψ_eq_one K.toCtx.E h0)).1
  subst hk
  simpa using hq

theorem A_inf_B {a : G} (ha : a ∈ Agrp x y u v) (haB : a ∈ B) : a ∈ R u v :=
  K.mem_R_of_B haB (K.A_comm K.xA ha)

theorem b_not_A : b ∉ Agrp x y u v := fun h => K.toCtx.bJ (K.toCtx.R_le_J (K.A_inf_B h K.toCtx.bB))

noncomputable def θA : Agrp x y u v →* G where
  toFun a := θ b a
  map_one' := K.toCtx.θ_one
  map_mul' a c := K.toCtx.θ_mul (K.A_le_T a.2) (K.A_le_T c.2)

theorem θA_range : (θA K).range = R u v := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩; exact K.toCtx.θ_mem (K.A_le_T a.2)
  · refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨⟨x, K.xA⟩, K.θx⟩
    · exact ⟨⟨y, K.yA⟩, K.θy⟩

theorem θA_ker : (θA K).ker.map (Agrp x y u v).subtype = R u v := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : θ b a = 1 := ha
    exact K.A_inf_B a.2 (K.toCtx.θ_eq_one_mem_B K.hP (K.A_le_P a.2) h1)
  · intro r hr
    refine ⟨⟨r, K.R_le_A hr⟩, ?_, rfl⟩
    show θ b r = 1
    exact K.toCtx.θ_of_cen (K.toCtx.comm_bR hr).symm

theorem card_R : Nat.card (R u v) = 9 := by
  have := K.toCtx.D.hB0.2
  rw [K.toCtx.B0] at this
  rw [this]; norm_num

theorem card_A : Nat.card (Agrp x y u v) = 81 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (θA K).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (θA K)).toEquiv] at h1
  have h2 : Nat.card (θA K).range = 9 := by rw [θA_range K]; exact K.card_R
  have h3 : Nat.card (θA K).ker = 9 := by
    rw [← Subgroup.card_map_of_injective (Agrp x y u v).subtype_injective, θA_ker K]
    exact K.card_R
  rw [h1, h2, h3]

theorem b_nor : b ∈ Nor (Agrp x y u v) := by
  refine L41.mem_nor_of_forall fun a ha => ?_
  have haT := K.A_le_T ha
  have e : b * a * b⁻¹ = a * (θ b a)⁻¹ := by
    have e0 := K.toCtx.conj_b_T haT
    have h1 : a⁻¹ * θ b a * a = θ b a := by
      have := K.toCtx.T_cen (Subgroup.inv_mem _ haT) (K.toCtx.θ_mem haT); simpa using this
    calc b * a * b⁻¹ = a * ((a⁻¹ * θ b a * a)⁻¹ * (a⁻¹ * (θ b a * b) * a)) * b⁻¹ := by group
      _ = a * ((θ b a)⁻¹ * (a⁻¹ * (a * b * a⁻¹) * a)) * b⁻¹ := by rw [h1, ← e0]
      _ = a * (θ b a)⁻¹ := by group
  rw [e]
  exact (Agrp x y u v).mul_mem ha (K.R_le_A ((R u v).inv_mem (K.toCtx.θ_mem haT)))

theorem comm_bA : ⁅Subgroup.zpowers b, Agrp x y u v⁆ = R u v := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro g hg a ha
    have hgB : g ∈ B := (Subgroup.zpowers_le.mpr K.toCtx.bB) hg
    have := K.toCtx.T_comm_B (K.A_le_T ha) hgB
    have e : ⁅g, a⁆ = (a * g * a⁻¹ * g⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]; exact (R u v).inv_mem this
  · rw [Subgroup.commutator_comm]
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    have hx : ⁅x, b⁆ = u := by rw [commutatorElement_def]; exact K.θx
    have hy : ⁅y, b⁆ = v := by rw [commutatorElement_def]; exact K.θy
    have h1 := Subgroup.commutator_mem_commutator K.xA (Subgroup.mem_zpowers b)
    have h2 := Subgroup.commutator_mem_commutator K.yA (Subgroup.mem_zpowers b)
    rw [hx] at h1
    rw [hy] at h2
    rcases hz with h | h
    · rw [h]; exact h1
    · rw [Set.mem_singleton_iff.mp h]; exact h2

theorem P_eq : P = Subgroup.zpowers b ⊔ Agrp x y u v := by
  refine le_antisymm ?_ (sup_le ((Subgroup.zpowers_le).mpr (K.hBP K.toCtx.bB)) K.A_le_P)
  intro z hz
  have hzT := K.toCtx.P_le_T K.hP hz
  obtain ⟨q, hq⟩ := exists_ψ K.toCtx.E (K.toCtx.θ_mem hzT)
  set a := x ^ q.1.val * y ^ q.2.val with ha
  have haA : a ∈ Agrp x y u v := (Agrp x y u v).mul_mem ((Agrp x y u v).pow_mem K.xA _)
    ((Agrp x y u v).pow_mem K.yA _)
  have haT := K.A_le_T haA
  have hθa : θ b a = ψ u v q := by
    rw [ha, K.toCtx.θ_mul ((T b B (R u v)).pow_mem K.xT _) ((T b B (R u v)).pow_mem K.yT _),
      K.toCtx.θ_pow K.xT, K.toCtx.θ_pow K.yT, K.θx, K.θy]; rfl
  have hc : z * a⁻¹ ∈ B := by
    refine K.toCtx.θ_eq_one_mem_B K.hP (P.mul_mem hz (P.inv_mem (K.A_le_P haA))) ?_
    rw [K.toCtx.θ_mul hzT ((T b B (R u v)).inv_mem haT), K.toCtx.θ_inv haT, hθa, ← hq,
      mul_inv_cancel]
  have hB : B ≤ Subgroup.zpowers b ⊔ Agrp x y u v := by
    rw [← K.toCtx.D.hsup, K.toCtx.B0]
    exact sup_le le_sup_left (K.R_le_A.trans le_sup_right)
  have : z = (z * a⁻¹) * a := by group
  rw [this]
  exact Subgroup.mul_mem _ (hB hc) (Subgroup.mem_sup_right haA)

theorem cube_R {a : G} (ha : a ∈ Agrp x y u v) : a ^ 3 ∈ R u v := by
  have haT := K.A_le_T ha
  refine K.A_inf_B ((Agrp x y u v).pow_mem ha 3) (K.toCtx.θ_eq_one_mem_B K.hP
    (P.pow_mem (K.A_le_P ha) 3) ?_)
  rw [K.toCtx.θ_pow haT, K.toCtx.pow3_R (K.toCtx.θ_mem haT)]

end PCtx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
