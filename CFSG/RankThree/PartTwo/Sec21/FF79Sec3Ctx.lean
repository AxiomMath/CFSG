module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3Crd
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bGL
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn

local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

structure Ctx (b : G) (J B : Subgroup G) (u v r₁ r₂ w : G) : Prop where
  D : L13b.Data b J B
  B0 : B ⊓ J = R u v
  nd : NormData u v r₁ r₂ w
  r₁J : r₁ ∈ J
  r₂J : r₂ ∈ J
  wJ : w ∈ J
  mono : ∀ g ∈ Nor J, g ∈ Nor (R u v) → InBlocks u v (g * u * g⁻¹) ∧ InBlocks u v (g * v * g⁻¹)
  orbit : ∀ D : Subgroup G, D ≤ B → Nat.card D = 3 →
    ((∃ g ∈ Nor B, conjBy g (Subgroup.zpowers b) = D) ↔ ¬ D ≤ J)

@[expose] def θ (b x : G) : G := x * b * x⁻¹ * b⁻¹

@[expose] def T (b : G) (B R : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Nor B ∧ x ∈ CenS R ∧ θ b x ∈ R}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, by simp [θ]⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨Subgroup.mul_mem _ hx1 hy1, Subgroup.mul_mem _ hx2 hy2, ?_⟩
    have hc : x * θ b y * x⁻¹ = θ b y := by
      rw [← Subgroup.mem_centralizer_iff.mp hx2 _ hy3]; group
    have : θ b (x * y) = θ b y * θ b x := by
      rw [← hc]; unfold θ; group
    rw [this]; exact Subgroup.mul_mem _ hy3 hx3
  inv_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    refine ⟨Subgroup.inv_mem _ hx1, Subgroup.inv_mem _ hx2, ?_⟩
    have hc : x⁻¹ * θ b x * x = θ b x := by
      have := Subgroup.mem_centralizer_iff.mp hx2 _ hx3
      calc x⁻¹ * θ b x * x = x⁻¹ * (x * θ b x) := by rw [mul_assoc, this]
        _ = θ b x := by group
    have : θ b x⁻¹ = (θ b x)⁻¹ := by
      calc θ b x⁻¹ = (x⁻¹ * θ b x * x)⁻¹ := by unfold θ; group
        _ = (θ b x)⁻¹ := by rw [hc]
    rw [this]; exact Subgroup.inv_mem _ hx3

namespace Ctx

variable {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G} (C : Ctx b J B u v r₁ r₂ w)
include C

theorem E : E9Data u v := C.nd.toE9Data

theorem b3 : b ^ 3 = 1 := by rw [← C.D.ord]; exact pow_orderOf_eq_one b

theorem bB : b ∈ B := C.D.hbB

theorem R_le_B : R u v ≤ B := C.B0 ▸ inf_le_left

theorem R_le_J : R u v ≤ J := C.B0 ▸ inf_le_right

theorem J_le_cen : J ≤ Cen b := C.D.hJC

theorem comm_B {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x := C.D.hab x hx y hy

theorem comm_bR {x : G} (hx : x ∈ R u v) : b * x = x * b := C.comm_B C.bB (C.R_le_B hx)

theorem comm_R {x y : G} (hx : x ∈ R u v) (hy : y ∈ R u v) : x * y = y * x :=
  C.comm_B (C.R_le_B hx) (C.R_le_B hy)

theorem uR : u ∈ R u v := Subgroup.subset_closure (Set.mem_insert u _)

theorem vR : v ∈ R u v := Subgroup.subset_closure (Set.mem_insert_of_mem u rfl)

theorem pow3_R {x : G} (hx : x ∈ R u v) : x ^ 3 = 1 := C.E.cube_R hx

theorem pow3_B {x : G} (hx : x ∈ B) : x ^ 3 = 1 := by
  haveI := C.D.hE.1
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem bJ : b ∉ J := C.D.hbJ

theorem bpow_mem_J {k : ZMod 3} (hk : b ^ k.val ∈ J) : k = 0 := by
  have h3 : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases h3 k with rfl | rfl | rfl
  · rfl
  · exact absurd (by have h : b ^ 1 ∈ J := hk; simpa using h) C.bJ
  · exfalso; apply C.bJ
    have h2 : b ^ 2 ∈ J := hk
    have : b = (b ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc b = b ^ 3 * b := by rw [C.b3, one_mul]
        _ = b ^ (2 * 2) := by rw [← pow_succ]
    rw [this]; exact J.pow_mem h2 2

theorem pow_val_add' {x : G} (hx : x ^ 3 = 1) (a c : ZMod 3) :
    x ^ (a + c).val = x ^ a.val * x ^ c.val := pow_val_add hx a c

@[expose] def Bs (C : Ctx b J B u v r₁ r₂ w) : Subgroup G where
  carrier := {x | ∃ k : ZMod 3, ∃ p : Z3, x = b ^ k.val * ψ u v p}
  one_mem' := ⟨0, 0, by simp [ψ_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨k, p, rfl⟩ ⟨l, q, rfl⟩
    refine ⟨k + l, p + q, ?_⟩
    rw [C.pow_val_add' C.b3, ψ_add C.E]
    have : ψ u v p * b ^ l.val = b ^ l.val * ψ u v p :=
      ((Commute.pow_left (C.comm_bR (ψ_mem C.E p)) l.val).eq).symm
    calc b ^ k.val * ψ u v p * (b ^ l.val * ψ u v q)
        = b ^ k.val * (ψ u v p * b ^ l.val) * ψ u v q := by group
      _ = b ^ k.val * b ^ l.val * (ψ u v p * ψ u v q) := by rw [this]; group
  inv_mem' := by
    rintro _ ⟨k, p, rfl⟩
    refine ⟨-k, -p, ?_⟩
    have h1 : b ^ k.val * b ^ (-k).val = 1 := by
      rw [← C.pow_val_add' C.b3, add_neg_cancel]; simp
    have h2 : ψ u v p * ψ u v (-p) = 1 := by
      rw [← ψ_add C.E, add_neg_cancel, ψ_zero]
    rw [inv_eq_iff_mul_eq_one]
    calc b ^ k.val * ψ u v p * (b ^ (-k).val * ψ u v (-p))
        = b ^ k.val * (ψ u v p * b ^ (-k).val) * ψ u v (-p) := by group
      _ = b ^ k.val * (b ^ (-k).val * ψ u v p) * ψ u v (-p) := by
          rw [(Commute.pow_left (C.comm_bR (ψ_mem C.E p)) _).eq.symm]
      _ = (b ^ k.val * b ^ (-k).val) * (ψ u v p * ψ u v (-p)) := by group
      _ = 1 := by rw [h1, h2, one_mul]

theorem mem_B_iff {x : G} : x ∈ B ↔ ∃ k : ZMod 3, ∃ p : Z3, x = b ^ k.val * ψ u v p := by
  constructor
  · intro hx
    have hle : Subgroup.zpowers b ⊔ R u v ≤ C.Bs := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]; exact ⟨1, 0, by show b = b ^ 1 * ψ u v 0; simp [ψ_zero]⟩
      · intro y hy
        obtain ⟨p, rfl⟩ := exists_ψ C.E hy
        exact ⟨0, p, by simp⟩
    have h := C.D.hsup
    rw [C.B0] at h
    rw [← h] at hx
    exact hle hx
  · rintro ⟨k, p, rfl⟩
    exact B.mul_mem (B.pow_mem C.bB _) (C.R_le_B (ψ_mem C.E p))

theorem B_eq {k l : ZMod 3} {p q : Z3} (h : b ^ k.val * ψ u v p = b ^ l.val * ψ u v q) :
    k = l ∧ p = q := by
  have hk : b ^ (k - l).val ∈ J := by
    have e1 : b ^ (k - l).val * b ^ l.val = b ^ k.val := by
      rw [← C.pow_val_add' C.b3, sub_add_cancel]
    have : b ^ (k - l).val = ψ u v q * (ψ u v p)⁻¹ := by
      have hc := (Commute.pow_left (C.comm_bR (ψ_mem C.E q)) l.val).eq
      calc b ^ (k - l).val = b ^ (k - l).val * b ^ l.val * ψ u v p * (ψ u v p)⁻¹ *
            (b ^ l.val)⁻¹ := by group
        _ = b ^ l.val * ψ u v q * (ψ u v p)⁻¹ * (b ^ l.val)⁻¹ := by rw [e1, h]
        _ = ψ u v q * (ψ u v p)⁻¹ := by
          rw [hc]
          have hc2 := (Commute.pow_left (C.comm_bR (Subgroup.inv_mem _ (ψ_mem C.E p))) l.val).eq
          calc ψ u v q * b ^ l.val * (ψ u v p)⁻¹ * (b ^ l.val)⁻¹
              = ψ u v q * (b ^ l.val * (ψ u v p)⁻¹) * (b ^ l.val)⁻¹ := by group
            _ = ψ u v q * (ψ u v p)⁻¹ := by rw [hc2]; group
    rw [this]
    exact C.R_le_J (Subgroup.mul_mem _ (ψ_mem C.E q) (Subgroup.inv_mem _ (ψ_mem C.E p)))
  have hkl : k = l := sub_eq_zero.mp (C.bpow_mem_J hk)
  subst hkl
  exact ⟨rfl, ψ_inj C.E (mul_left_cancel h)⟩

theorem card_zpowers_three {x : G} (hx : x ^ 3 = 1) (h1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 3 := by
  rw [Nat.card_zpowers]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hx h1

theorem conjBy_zpowers (g x : G) :
    conjBy g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  show (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = _
  rw [MonoidHom.map_zpowers]; rfl

theorem conj_b_not_mem {n : G} (hn : n ∈ Nor B) : n * b * n⁻¹ ∉ J := by
  intro hJ
  have hB : n * b * n⁻¹ ∈ B := L13b.conj_mem_of_nor hn C.bB
  have h1 : n * b * n⁻¹ ≠ 1 := fun h => C.bJ (by
    have : b = n⁻¹ * (n * b * n⁻¹) * n := by group
    rw [this, h]; simpa using J.one_mem)
  have h3 : (n * b * n⁻¹) ^ 3 = 1 := C.pow3_B hB
  have hD := (C.orbit (Subgroup.zpowers (n * b * n⁻¹))
    (by rw [Subgroup.zpowers_le]; exact hB) (C.card_zpowers_three h3 h1)).mp
    ⟨n, hn, C.conjBy_zpowers n b⟩
  exact hD (by rw [Subgroup.zpowers_le]; exact hJ)

theorem nor0 {n : G} (hn : n ∈ Nor B) {x : G} (hx : x ∈ R u v) : n * x * n⁻¹ ∈ R u v := by
  by_cases h1 : x = 1
  · subst h1; simpa using (R u v).one_mem
  rw [← C.B0]
  refine ⟨L13b.conj_mem_of_nor hn (C.R_le_B hx), ?_⟩
  by_contra hyJ
  set y := n * x * n⁻¹ with hy
  have hyB : y ∈ B := L13b.conj_mem_of_nor hn (C.R_le_B hx)
  have hy1 : y ≠ 1 := fun h => h1 (by
    have : x = n⁻¹ * y * n := by rw [hy]; group
    rw [this, h]; group)
  have hx3 : x ^ 3 = 1 := C.pow3_R hx
  have hy3 : y ^ 3 = 1 := by rw [hy, conj_pow, hx3]; group
  obtain ⟨g, hg, hgD⟩ := (C.orbit (Subgroup.zpowers y) (by rw [Subgroup.zpowers_le]; exact hyB)
    (C.card_zpowers_three hy3 hy1)).mpr (fun h => hyJ (h (Subgroup.mem_zpowers y)))
  have hxB : x ∈ B := C.R_le_B hx
  have hn' : n⁻¹ * g ∈ Nor B := Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hg
  have hD2 : conjBy (n⁻¹ * g) (Subgroup.zpowers b) = Subgroup.zpowers x := by
    rw [← L41.conjBy_conjBy, hgD, C.conjBy_zpowers]
    congr 1; rw [hy]; group
  have := (C.orbit (Subgroup.zpowers x) (by rw [Subgroup.zpowers_le]; exact hxB)
    (C.card_zpowers_three hx3 h1)).mp ⟨_, hn', hD2⟩
  exact this (by rw [Subgroup.zpowers_le]; exact C.R_le_J hx)

theorem conj_b_form {n : G} (hn : n ∈ Nor B) :
    ∃ k : ZMod 3, k ≠ 0 ∧ ∃ p : Z3, n * b * n⁻¹ = b ^ k.val * ψ u v p := by
  obtain ⟨k, p, hkp⟩ := (C.mem_B_iff).mp (L13b.conj_mem_of_nor hn C.bB)
  refine ⟨k, fun hk => C.conj_b_not_mem hn ?_, p, hkp⟩
  rw [hkp, hk]; simpa using C.R_le_J (ψ_mem C.E p)

theorem T_le_N : T b B (R u v) ≤ Nor B := fun _ h => h.1

theorem T_cen {x : G} (hx : x ∈ T b B (R u v)) {y : G} (hy : y ∈ R u v) : x * y * x⁻¹ = y := by
  rw [← Subgroup.mem_centralizer_iff.mp hx.2.1 y hy]; group

theorem θ_mem {x : G} (hx : x ∈ T b B (R u v)) : θ b x ∈ R u v := hx.2.2

theorem conj_b_T {x : G} (hx : x ∈ T b B (R u v)) : x * b * x⁻¹ = θ b x * b := by
  unfold θ; group

theorem θ_mul {x y : G} (hx : x ∈ T b B (R u v)) (hy : y ∈ T b B (R u v)) :
    θ b (x * y) = θ b x * θ b y := by
  have hc : x * θ b y * x⁻¹ = θ b y := C.T_cen hx (C.θ_mem hy)
  calc θ b (x * y) = (x * θ b y * x⁻¹) * θ b x := by unfold θ; group
    _ = θ b x * θ b y := by rw [hc]; exact C.comm_R (C.θ_mem hy) (C.θ_mem hx)

theorem θ_inv {x : G} (hx : x ∈ T b B (R u v)) : θ b x⁻¹ = (θ b x)⁻¹ := by
  have h := C.θ_mul hx (Subgroup.inv_mem _ hx)
  rw [mul_inv_cancel] at h
  have h1 : θ b (1 : G) = 1 := by simp [θ]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem θ_one : θ b (1 : G) = 1 := by simp [θ]

theorem θ_pow {x : G} (hx : x ∈ T b B (R u v)) (n : ℕ) : θ b (x ^ n) = θ b x ^ n := by
  induction n with
  | zero => simp [θ]
  | succ n ih => rw [pow_succ, C.θ_mul (Subgroup.pow_mem _ hx n) hx, ih, pow_succ]

theorem θ_conj_of_cen (n x : G) (hn : n * b * n⁻¹ = b) :
    θ b (n * x * n⁻¹) = n * θ b x * n⁻¹ := by
  have hb : b = n * b * n⁻¹ := hn.symm
  unfold θ
  conv_lhs => rw [hb]
  group

theorem θ_conj_T {k x : G} (hk : k ∈ T b B (R u v)) (hx : x ∈ T b B (R u v)) :
    θ b (k * x * k⁻¹) = θ b x := by
  rw [C.θ_mul (Subgroup.mul_mem _ hk hx) (Subgroup.inv_mem _ hk), C.θ_mul hk hx, C.θ_inv hk]
  have := C.comm_R (C.θ_mem hk) (C.θ_mem hx)
  rw [this]; group

theorem T_comm_B {x : G} (hx : x ∈ T b B (R u v)) {y : G} (hy : y ∈ B) :
    x * y * x⁻¹ * y⁻¹ ∈ R u v := by
  obtain ⟨k, p, rfl⟩ := (C.mem_B_iff).mp hy
  have e1 : x * b ^ k.val * x⁻¹ = (θ b x * b) ^ k.val := by rw [← C.conj_b_T hx, conj_pow]
  have e2 : (θ b x * b) ^ k.val = θ b x ^ k.val * b ^ k.val :=
    (Commute.mul_pow (C.comm_bR (C.θ_mem hx)).symm _)
  have e3 : x * ψ u v p * x⁻¹ = ψ u v p := C.T_cen hx (ψ_mem C.E p)
  have : x * (b ^ k.val * ψ u v p) * x⁻¹ * (b ^ k.val * ψ u v p)⁻¹ = θ b x ^ k.val := by
    calc x * (b ^ k.val * ψ u v p) * x⁻¹ * (b ^ k.val * ψ u v p)⁻¹
        = (x * b ^ k.val * x⁻¹) * (x * ψ u v p * x⁻¹) * (ψ u v p)⁻¹ * (b ^ k.val)⁻¹ := by group
      _ = θ b x ^ k.val := by rw [e1, e2, e3]; group
  rw [this]; exact Subgroup.pow_mem _ (C.θ_mem hx) _

theorem T_normal {n : G} (hn : n ∈ Nor B) {x : G} (hx : x ∈ T b B (R u v)) :
    n * x * n⁻¹ ∈ T b B (R u v) := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hx.1) (Subgroup.inv_mem _ hn), ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ R u v := by
      have := C.nor0 (Subgroup.inv_mem _ hn) hy; simpa using this
    have := C.T_cen hx hy'
    calc y * (n * x * n⁻¹) = n * (n⁻¹ * y * n) * x * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * y * n) * x⁻¹) * x * n⁻¹ := by rw [this]
      _ = n * x * n⁻¹ * y := by group
  · have hb' : n⁻¹ * b * n ∈ B := by
      have := L13b.conj_mem_of_nor (Subgroup.inv_mem _ hn) C.bB; simpa using this
    have h := C.nor0 hn (C.T_comm_B hx hb')
    have : θ b (n * x * n⁻¹) = n * (x * (n⁻¹ * b * n) * x⁻¹ * (n⁻¹ * b * n)⁻¹) * n⁻¹ := by
      unfold θ; group
    rw [this]; exact h

theorem cenB_le_T : CenS B ≤ T b B (R u v) := by
  intro x hx
  have hxb : x * b * x⁻¹ = b := by
    rw [(Subgroup.mem_centralizer_iff.mp hx b C.bB).symm]; group
  refine ⟨?_, ?_, ?_⟩
  · exact L13b.mem_nor_of_forall fun y hy => by
      rw [(Subgroup.mem_centralizer_iff.mp hx y hy).symm]; group; exact hy
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hx y (C.R_le_B hy)
  · unfold θ; rw [hxb, mul_inv_cancel]; exact (R u v).one_mem

theorem θ_of_cen {x : G} (hx : x * b = b * x) : θ b x = 1 := by
  unfold θ; rw [hx]; group

theorem z_inv {x : G} (hx : x ∈ R u v) : (r₁ * r₂) * x * (r₁ * r₂)⁻¹ = x⁻¹ := by
  obtain ⟨p, rfl⟩ := exists_ψ C.E hx
  have e : (r₁ * r₂) * ψ u v p * (r₁ * r₂)⁻¹ = r₁ * (r₂ * ψ u v p * r₂⁻¹) * r₁⁻¹ := by group
  rw [e, nd_r₂_conj C.nd, nd_r₁_conj C.nd, lin_z, ψ_neg C.E]

end Ctx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
