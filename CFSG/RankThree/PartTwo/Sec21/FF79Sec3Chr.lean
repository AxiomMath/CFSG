module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3A
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn

local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem lin_eq (e₁ e₂ p : Z3) :
    lin e₁ e₂ p = (p.1 * e₁.1 + p.2 * e₂.1, p.1 * e₁.2 + p.2 * e₂.2) := by
  ext <;> simp [lin, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem val_nsmul (e : ZMod 3) (p : Z3) : e.val • p = (e * p.1, e * p.2) := by
  ext <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]

@[expose] def linHom (e₁ e₂ : Z3) : Z3 →+ Z3 :=
  AddMonoidHom.mk' (lin e₁ e₂) (fun p q => by
    rw [lin_eq, lin_eq, lin_eq]; ext <;> simp <;> ring)

theorem Ctx.T_comm_formula {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G}
    (C : Ctx b J B u v r₁ r₂ w) {x : G} (hx : x ∈ T b B (R u v)) (k : ZMod 3) (p : Z3) :
    x * (b ^ k.val * ψ u v p) * x⁻¹ * (b ^ k.val * ψ u v p)⁻¹ = θ b x ^ k.val := by
  have e1 : x * b ^ k.val * x⁻¹ = (θ b x * b) ^ k.val := by rw [← C.conj_b_T hx, conj_pow]
  have e2 : (θ b x * b) ^ k.val = θ b x ^ k.val * b ^ k.val :=
    (Commute.mul_pow (C.comm_bR (C.θ_mem hx)).symm _)
  have e3 : x * ψ u v p * x⁻¹ = ψ u v p := C.T_cen hx (ψ_mem C.E p)
  calc x * (b ^ k.val * ψ u v p) * x⁻¹ * (b ^ k.val * ψ u v p)⁻¹
      = (x * b ^ k.val * x⁻¹) * (x * ψ u v p * x⁻¹) * (ψ u v p)⁻¹ * (b ^ k.val)⁻¹ := by group
    _ = θ b x ^ k.val := by rw [e1, e2, e3]; group

namespace PCtx

variable {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G} {P : Subgroup G} {x y : G}
  (K : PCtx b J B u v r₁ r₂ w P x y)
include K

theorem θ_xy (q : Z3) : θ b (x ^ q.1.val * y ^ q.2.val) = ψ u v q := by
  rw [K.toCtx.θ_mul ((T b B (R u v)).pow_mem K.xT _) ((T b B (R u v)).pow_mem K.yT _),
    K.toCtx.θ_pow K.xT, K.toCtx.θ_pow K.yT, K.θx, K.θy]; rfl

theorem xy_mem (q : Z3) : x ^ q.1.val * y ^ q.2.val ∈ Agrp x y u v :=
  (Agrp x y u v).mul_mem ((Agrp x y u v).pow_mem K.xA _) ((Agrp x y u v).pow_mem K.yA _)

theorem P_decomp {z : G} (hz : z ∈ P) : ∃ k : ZMod 3, ∃ a ∈ Agrp x y u v, z = b ^ k.val * a := by
  have hzT := K.toCtx.P_le_T K.hP hz
  obtain ⟨q, hq⟩ := exists_ψ K.toCtx.E (K.toCtx.θ_mem hzT)
  set a := x ^ q.1.val * y ^ q.2.val with ha
  have haA : a ∈ Agrp x y u v := K.xy_mem q
  have haT := K.A_le_T haA
  have hc : z * a⁻¹ ∈ B := by
    refine K.toCtx.θ_eq_one_mem_B K.hP (P.mul_mem hz (P.inv_mem (K.A_le_P haA))) ?_
    rw [K.toCtx.θ_mul hzT ((T b B (R u v)).inv_mem haT), K.toCtx.θ_inv haT, K.θ_xy q, ← hq,
      mul_inv_cancel]
  obtain ⟨k, p, hkp⟩ := (K.toCtx.mem_B_iff).mp hc
  refine ⟨k, ψ u v p * a, (Agrp x y u v).mul_mem (K.R_le_A (ψ_mem K.toCtx.E p)) haA, ?_⟩
  calc z = (z * a⁻¹) * a := by group
    _ = _ := by rw [hkp, mul_assoc]

theorem θ_bpow_mul {a : G} (ha : a ∈ Agrp x y u v) (k : ℕ) : θ b (b ^ k * a) = θ b a := by
  rw [K.toCtx.θ_mul (K.toCtx.bpow_T k) (K.A_le_T ha), K.toCtx.θ_bpow, one_mul]

theorem mul_bpow {a : G} (ha : a ∈ T b B (R u v)) (n : ℕ) :
    a * b ^ n = θ b a ^ n * b ^ n * a := by
  have e1 : a * b ^ n * a⁻¹ = (θ b a * b) ^ n := by rw [← K.toCtx.conj_b_T ha, conj_pow]
  have e2 : (θ b a * b) ^ n = θ b a ^ n * b ^ n :=
    (Commute.mul_pow (K.toCtx.comm_bR (K.toCtx.θ_mem ha)).symm _)
  calc a * b ^ n = (a * b ^ n * a⁻¹) * a := by group
    _ = _ := by rw [e1, e2]

theorem θ_conj_nor {m : G} {e : ZMod 3} {p : Z3} (he : m⁻¹ * b * m = b ^ e.val * ψ u v p)
    {z : G} (hz : z ∈ T b B (R u v)) : θ b (m * z * m⁻¹) = m * θ b z ^ e.val * m⁻¹ := by
  have h := K.toCtx.T_comm_formula hz e p
  rw [← he] at h
  unfold θ
  calc m * z * m⁻¹ * b * (m * z * m⁻¹)⁻¹ * b⁻¹
      = m * (z * (m⁻¹ * b * m) * z⁻¹ * (m⁻¹ * b * m)⁻¹) * m⁻¹ := by group
    _ = m * θ b z ^ e.val * m⁻¹ := by rw [h]

theorem u_pow_eq_v_pow {i j : ZMod 3} (h : u ^ i.val = v ^ j.val) : i = 0 ∧ j = 0 := by
  have h' : ψ u v (i, -j) = 1 := by
    show u ^ i.val * v ^ (-j).val = 1
    rw [h, ← pow_val_add K.toCtx.E.b3, add_neg_cancel, ZMod.val_zero, pow_zero]
  have := ψ_eq_one K.toCtx.E h'
  exact ⟨(Prod.ext_iff.mp this).1, neg_eq_zero.mp (Prod.ext_iff.mp this).2⟩

theorem nor_A {m : G} (hm : m ∈ Nor P) (hmB : m ∈ Nor B) {a : G} (ha : a ∈ Agrp x y u v) :
    m * a * m⁻¹ ∈ Agrp x y u v := by
  obtain ⟨e, he0, p, he⟩ := K.toCtx.conj_b_form (Subgroup.inv_mem _ hmB)
  rw [inv_inv] at he
  have hmP : ∀ {z : G}, z ∈ P → m * z * m⁻¹ ∈ P := fun hz =>
    (Subgroup.mem_normalizer_iff.mp hm _).mp hz
  have hu3 : u ^ 3 = 1 := K.toCtx.E.a3
  have hv3 : v ^ 3 = 1 := K.toCtx.E.b3
  obtain ⟨i, a₁, ha₁, h1⟩ := K.P_decomp (hmP K.hx)
  obtain ⟨j, a₂, ha₂, h2⟩ := K.P_decomp (hmP K.hy)
  have hθ1 : θ b a₁ = m * u ^ e.val * m⁻¹ := by
    rw [← K.θ_bpow_mul ha₁ i.val, ← h1, K.θ_conj_nor he K.xT, K.θx]
  have hθ2 : θ b a₂ = m * v ^ e.val * m⁻¹ := by
    rw [← K.θ_bpow_mul ha₂ j.val, ← h2, K.θ_conj_nor he K.yT, K.θy]
  have hcomm : (m * x * m⁻¹) * (m * y * m⁻¹) = (m * y * m⁻¹) * (m * x * m⁻¹) := by
    calc (m * x * m⁻¹) * (m * y * m⁻¹) = m * (x * y) * m⁻¹ := by group
      _ = m * (y * x) * m⁻¹ := by rw [K.xy]
      _ = _ := by group
  rw [h1, h2] at hcomm
  have ha₁T := K.A_le_T ha₁
  have ha₂T := K.A_le_T ha₂
  have hc12 := K.A_comm ha₁ ha₂
  have hb1 := (Commute.pow_right (K.toCtx.comm_bR (K.toCtx.θ_mem ha₁T)) (j.val)).pow_left i.val
  have key : θ b a₁ ^ j.val = θ b a₂ ^ i.val := by
    have l1 : b ^ i.val * a₁ * (b ^ j.val * a₂) =
        θ b a₁ ^ j.val * (b ^ i.val * b ^ j.val * (a₁ * a₂)) := by
      calc b ^ i.val * a₁ * (b ^ j.val * a₂) = b ^ i.val * (a₁ * b ^ j.val) * a₂ := by group
        _ = b ^ i.val * (θ b a₁ ^ j.val * b ^ j.val * a₁) * a₂ := by rw [K.mul_bpow ha₁T]
        _ = (b ^ i.val * θ b a₁ ^ j.val) * b ^ j.val * (a₁ * a₂) := by group
        _ = _ := by
          rw [(Commute.pow_pow (K.toCtx.comm_bR (K.toCtx.θ_mem ha₁T)) i.val j.val).eq]; group
    have l2 : b ^ j.val * a₂ * (b ^ i.val * a₁) =
        θ b a₂ ^ i.val * (b ^ i.val * b ^ j.val * (a₁ * a₂)) := by
      calc b ^ j.val * a₂ * (b ^ i.val * a₁) = b ^ j.val * (a₂ * b ^ i.val) * a₁ := by group
        _ = b ^ j.val * (θ b a₂ ^ i.val * b ^ i.val * a₂) * a₁ := by rw [K.mul_bpow ha₂T]
        _ = (b ^ j.val * θ b a₂ ^ i.val) * b ^ i.val * (a₂ * a₁) := by group
        _ = _ := by
          rw [(Commute.pow_pow (K.toCtx.comm_bR (K.toCtx.θ_mem ha₂T)) j.val i.val).eq,
            ← hc12, mul_assoc (θ b a₂ ^ i.val), ← pow_add, ← pow_add, add_comm]; group
    rw [l1, l2] at hcomm
    exact mul_right_cancel hcomm
  rw [hθ1, hθ2, ← conj_pow, ← conj_pow, ← pow_mul, ← pow_mul, conj_pow, conj_pow] at key
  have key' : u ^ (e * j).val = v ^ (e * i).val := by
    have := mul_left_cancel (mul_right_cancel key)
    rw [ZMod.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hu3, ← pow_eq_pow_mod _ hv3]
    exact this
  obtain ⟨hj, hi⟩ := K.u_pow_eq_v_pow key'
  have hi0 : i = 0 := (mul_eq_zero.mp hi).resolve_left he0
  have hj0 : j = 0 := (mul_eq_zero.mp hj).resolve_left he0
  subst hi0 hj0
  have hxA : m * x * m⁻¹ ∈ Agrp x y u v := by rw [h1]; simpa using ha₁
  have hyA : m * y * m⁻¹ ∈ Agrp x y u v := by rw [h2]; simpa using ha₂
  have hle : Agrp x y u v ≤ (Agrp x y u v).comap (MulAut.conj m).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    show (MulAut.conj m) z ∈ Agrp x y u v
    rw [MulAut.conj_apply]
    rcases hz with rfl | rfl | rfl | rfl
    · exact hxA
    · exact hyA
    · exact K.R_le_A (K.toCtx.nor0 hmB K.toCtx.uR)
    · exact K.R_le_A (K.toCtx.nor0 hmB K.toCtx.vR)
  have := hle ha
  simpa [MulAut.conj_apply] using this

theorem exists_cubes : ∃ c₁ c₂ : Z3, x ^ 3 = ψ u v c₁ ∧ y ^ 3 = ψ u v c₂ := by
  obtain ⟨c₁, h1⟩ := exists_ψ K.toCtx.E (K.cube_R K.xA)
  obtain ⟨c₂, h2⟩ := exists_ψ K.toCtx.E (K.cube_R K.yA)
  exact ⟨c₁, c₂, h1, h2⟩

theorem cube_eq {c₁ c₂ : Z3} (h1 : x ^ 3 = ψ u v c₁) (h2 : y ^ 3 = ψ u v c₂) {a : G}
    (ha : a ∈ Agrp x y u v) {q : Z3} (hq : θ b a = ψ u v q) : a ^ 3 = ψ u v (lin c₁ c₂ q) := by
  set aq := x ^ q.1.val * y ^ q.2.val with haq
  have haqA := K.xy_mem q
  have hr : a * aq⁻¹ ∈ R u v := by
    refine K.A_inf_B ((Agrp x y u v).mul_mem ha ((Agrp x y u v).inv_mem haqA))
      (K.toCtx.θ_eq_one_mem_B K.hP (P.mul_mem (K.A_le_P ha) (P.inv_mem (K.A_le_P haqA))) ?_)
    rw [K.toCtx.θ_mul (K.A_le_T ha) ((T b B (R u v)).inv_mem (K.A_le_T haqA)),
      K.toCtx.θ_inv (K.A_le_T haqA), K.θ_xy q, hq, mul_inv_cancel]
  have e : a = (a * aq⁻¹) * aq := by group
  have hc : Commute (a * aq⁻¹) aq :=
    K.A_comm ((Agrp x y u v).mul_mem ha ((Agrp x y u v).inv_mem haqA)) haqA
  have hxy : Commute (x ^ q.1.val) (y ^ q.2.val) := Commute.pow_pow K.xy _ _
  rw [e, hc.mul_pow, K.toCtx.pow3_R hr, one_mul, haq, hxy.mul_pow, ← pow_mul, ← pow_mul,
    mul_comm q.1.val, mul_comm q.2.val, pow_mul, pow_mul, h1, h2, lin, ψ_add K.toCtx.E,
    ψ_nsmul K.toCtx.E, ψ_nsmul K.toCtx.E]

theorem cube_equivariant {c₁ c₂ : Z3} (h1 : x ^ 3 = ψ u v c₁) (h2 : y ^ 3 = ψ u v c₂) {m : G}
    (hm : m ∈ Nor P) (hmB : m ∈ Nor B) {f₁ f₂ : Z3} (hf₁ : m * u * m⁻¹ = ψ u v f₁)
    (hf₂ : m * v * m⁻¹ = ψ u v f₂) {e : ZMod 3} {p : Z3} (he : m⁻¹ * b * m = b ^ e.val * ψ u v p)
    (q : Z3) : lin c₁ c₂ (e.val • lin f₁ f₂ q) = lin f₁ f₂ (lin c₁ c₂ q) := by
  set a := x ^ q.1.val * y ^ q.2.val
  have haA := K.xy_mem q
  have hc := conj_ψ K.toCtx.E hf₁ hf₂
  have hmaA := K.nor_A hm hmB haA
  have hθ : θ b (m * a * m⁻¹) = ψ u v (e.val • lin f₁ f₂ q) := by
    rw [K.θ_conj_nor he (K.A_le_T haA), K.θ_xy q, ← conj_pow, hc, ψ_nsmul K.toCtx.E]
  have l1 := K.cube_eq h1 h2 hmaA hθ
  have l2 : (m * a * m⁻¹) ^ 3 = ψ u v (lin f₁ f₂ (lin c₁ c₂ q)) := by
    rw [conj_pow, K.cube_eq h1 h2 haA (K.θ_xy q), hc]
  exact ψ_inj K.toCtx.E (l1.symm.trans l2)

end PCtx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
