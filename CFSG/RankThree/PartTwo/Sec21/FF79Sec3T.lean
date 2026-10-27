module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3Ctx

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn

local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem zpow_eq_pow_val {x : G} (hx : x ^ 3 = 1) (m : ℤ) : x ^ m = x ^ (m : ZMod 3).val := by
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  rw [zpow_eq_zpow_emod m h3, ← zpow_natCast, ZMod.val_intCast]; rfl

theorem pow_val_one (x : G) : x ^ (1 : ZMod 3).val = x := by show x ^ 1 = x; exact pow_one x

theorem pow_val_two (x : G) : x ^ (2 : ZMod 3).val = x ^ 2 := rfl

theorem zmod3_cases (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k; decide

namespace Ctx

variable {b : G} {J B : Subgroup G} {u v r₁ r₂ w : G} (C : Ctx b J B u v r₁ r₂ w)
include C

theorem r_nor {r : G} (hr : r ∈ J) (h0 : ∀ y ∈ R u v, r * y * r⁻¹ ∈ R u v) : r ∈ Nor B := by
  refine C.D.nor_B_of_J hr (L13b.mem_nor_of_forall fun y hy => ?_)
  rw [C.B0] at hy ⊢; exact h0 y hy

theorem conj_b_of_J {r : G} (hr : r ∈ J) : r * b * r⁻¹ = b := C.D.conj_b_of_mem_cen (C.J_le_cen hr)

theorem r₁N : r₁ ∈ Nor B := C.r_nor C.r₁J fun y hy => by
  obtain ⟨p, rfl⟩ := exists_ψ C.E hy; rw [nd_r₁_conj C.nd]; exact ψ_mem C.E _

theorem r₂N : r₂ ∈ Nor B := C.r_nor C.r₂J fun y hy => by
  obtain ⟨p, rfl⟩ := exists_ψ C.E hy; rw [nd_r₂_conj C.nd]; exact ψ_mem C.E _

theorem wN : w ∈ Nor B := C.r_nor C.wJ fun y hy => by
  obtain ⟨p, rfl⟩ := exists_ψ C.E hy; rw [nd_w_conj C.nd]; exact ψ_mem C.E _

theorem exists_move : ∃ g ∈ Nor B, ∃ k : ZMod 3, ∃ p : Z3, p ≠ 0 ∧
    g * b * g⁻¹ = b ^ k.val * ψ u v p := by
  have hbu : b * u ∈ B := B.mul_mem C.bB (C.R_le_B C.uR)
  have hbuJ : b * u ∉ J := fun h => C.bJ (by
    have : b = b * u * u⁻¹ := by group
    rw [this]; exact J.mul_mem h (J.inv_mem (C.R_le_J C.uR)))
  have hbu1 : b * u ≠ 1 := fun h => hbuJ (by rw [h]; exact J.one_mem)
  obtain ⟨g, hg, hgD⟩ := (C.orbit (Subgroup.zpowers (b * u))
    (by rw [Subgroup.zpowers_le]; exact hbu) (C.card_zpowers_three (C.pow3_B hbu) hbu1)).mpr
    (fun h => hbuJ (h (Subgroup.mem_zpowers _)))
  obtain ⟨k, hk, p, hp⟩ := C.conj_b_form hg
  refine ⟨g, hg, k, p, fun hp0 => ?_, hp⟩
  have hmem : g * b * g⁻¹ ∈ Subgroup.zpowers (b * u) := by
    rw [← hgD, C.conjBy_zpowers]; exact Subgroup.mem_zpowers _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [zpow_eq_pow_val (C.pow3_B hbu)] at hm
  have hcomm : Commute b u := C.comm_bR C.uR
  rw [hcomm.mul_pow, show u ^ (m : ZMod 3).val = ψ u v ((m : ZMod 3), 0) by simp [ψ], hp,
    hp0] at hm
  obtain ⟨h1, h2⟩ := C.B_eq hm
  have : (m : ZMod 3) = 0 := (Prod.ext_iff.mp h2).1
  rw [this] at h1
  exact hk h1.symm

theorem θ_surj {t : G} (ht : t ∈ R u v) : ∃ x ∈ T b B (R u v), θ b x = t := by
  let L : Subgroup G :=
    { carrier := {t | t ∈ R u v ∧ ∃ x ∈ T b B (R u v), θ b x = t}
      one_mem' := ⟨(R u v).one_mem, 1, (T b B (R u v)).one_mem, by simp [θ]⟩
      mul_mem' := by
        rintro _ _ ⟨h1, x, hx, rfl⟩ ⟨h2, y, hy, rfl⟩
        exact ⟨(R u v).mul_mem h1 h2, x * y, (T b B (R u v)).mul_mem hx hy, C.θ_mul hx hy⟩
      inv_mem' := by
        rintro _ ⟨h1, x, hx, rfl⟩
        exact ⟨(R u v).inv_mem h1, x⁻¹, (T b B (R u v)).inv_mem hx, C.θ_inv hx⟩ }
  have hLR : L ≤ R u v := fun _ h => h.1
  have hinv : ∀ r ∈ J, r ∈ Nor B → ∀ x ∈ L, r * x * r⁻¹ ∈ L := by
    rintro r hrJ hrN _ ⟨h1, x, hx, rfl⟩
    exact ⟨C.nor0 hrN h1, r * x * r⁻¹, C.T_normal hrN hx,
      C.θ_conj_of_cen r x (C.conj_b_of_J hrJ)⟩
  rcases nd_irred C.nd hLR (hinv r₁ C.r₁J C.r₁N) (hinv w C.wJ C.wN) with hL | hL
  · exfalso
    obtain ⟨g, hg, k, p, hp, hgb⟩ := C.exists_move
    set z := r₁ * r₂ with hz
    have hzN : z ∈ Nor B := Subgroup.mul_mem _ C.r₁N C.r₂N
    have hzb : z * b * z⁻¹ = b := by
      rw [hz]
      have e : r₁ * r₂ * b * (r₁ * r₂)⁻¹ = r₁ * (r₂ * b * r₂⁻¹) * r₁⁻¹ := by group
      rw [e, C.conj_b_of_J C.r₂J, C.conj_b_of_J C.r₁J]
    have hzb' : z⁻¹ * b * z = b := by
      calc z⁻¹ * b * z = z⁻¹ * (z * b * z⁻¹) * z := by rw [hzb]
        _ = b := by group
    have hzi : ∀ x ∈ R u v, z * x * z⁻¹ = x⁻¹ := fun x hx => C.z_inv hx
    have hzi' : ∀ x ∈ R u v, z⁻¹ * x * z = x⁻¹ := fun x hx => by
      have h := hzi x⁻¹ (Subgroup.inv_mem _ hx)
      rw [inv_inv] at h
      calc z⁻¹ * x * z = z⁻¹ * (z * x⁻¹ * z⁻¹) * z := by rw [h]
        _ = x⁻¹ := by group
    set c := g⁻¹ * z * g * z⁻¹ with hc
    have hgi : g⁻¹ ∈ Nor B := Subgroup.inv_mem _ hg
    have hcN : c ∈ Nor B :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgi hzN) hg)
        (Subgroup.inv_mem _ hzN)
    have hcC : c ∈ CenS (R u v) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 : g * x⁻¹ * g⁻¹ ∈ R u v := C.nor0 hg (Subgroup.inv_mem _ hx)
      have h2 := hzi _ h1
      have h3 := hzi' x hx
      have : c * x * c⁻¹ = x := by
        calc c * x * c⁻¹ = g⁻¹ * z * g * (z⁻¹ * x * z) * g⁻¹ * z⁻¹ * g := by rw [hc]; group
          _ = g⁻¹ * (z * (g * x⁻¹ * g⁻¹) * z⁻¹) * g := by rw [h3]; group
          _ = x := by rw [h2]; group
      calc x * c = (c * x * c⁻¹) * c := by rw [this]
        _ = c * x := by group
    have hψ := ψ_mem C.E p
    have hβ : g⁻¹ * ψ u v p * g ∈ R u v := by
      have := C.nor0 hgi hψ; simpa using this
    have hθc : θ b c = g⁻¹ * ψ u v p * g := by
      have hzk : z * b ^ k.val * z⁻¹ = b ^ k.val := by rw [← conj_pow, hzb]
      have e1 : c * b * c⁻¹ = g⁻¹ * (z * (g * b * g⁻¹) * z⁻¹) * g := by
        calc c * b * c⁻¹ = g⁻¹ * z * g * (z⁻¹ * b * z) * g⁻¹ * z⁻¹ * g := by rw [hc]; group
          _ = g⁻¹ * (z * (g * b * g⁻¹) * z⁻¹) * g := by rw [hzb']; group
      have e2 : z * (g * b * g⁻¹) * z⁻¹ = (g * b * g⁻¹) * (ψ u v p)⁻¹ * (ψ u v p)⁻¹ := by
        rw [hgb]
        have : z * (b ^ k.val * ψ u v p) * z⁻¹ = (z * b ^ k.val * z⁻¹) * (z * ψ u v p * z⁻¹) := by
          group
        rw [this, hzk, hzi _ hψ]
        group
      have e3 : g⁻¹ * ((g * b * g⁻¹) * (ψ u v p)⁻¹ * (ψ u v p)⁻¹) * g =
          b * (g⁻¹ * ψ u v p * g)⁻¹ * (g⁻¹ * ψ u v p * g)⁻¹ := by group
      have h3 := C.pow3_R hβ
      have e4 : (g⁻¹ * ψ u v p * g)⁻¹ * (g⁻¹ * ψ u v p * g)⁻¹ = g⁻¹ * ψ u v p * g := by
        rw [← mul_inv_rev, inv_eq_iff_mul_eq_one, ← pow_three', h3]
      unfold θ
      rw [e1, e2, e3, mul_assoc b, e4, C.comm_bR hβ]
      group
    have hcT : c ∈ T b B (R u v) := ⟨hcN, hcC, hθc ▸ hβ⟩
    have : θ b c ∈ L := ⟨C.θ_mem hcT, c, hcT, rfl⟩
    rw [hL] at this
    have h1 : g⁻¹ * ψ u v p * g = 1 := by rw [← hθc]; exact this
    have : ψ u v p = 1 := by
      calc ψ u v p = g * (g⁻¹ * ψ u v p * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    exact hp (ψ_eq_one C.E this)
  · rw [← hL] at ht
    obtain ⟨-, x, hx, hθ⟩ := ht
    exact ⟨x, hx, hθ⟩

theorem exists_T_fix {n : G} (hn : n ∈ Nor B) {k : ZMod 3} {p : Z3}
    (h : n * b * n⁻¹ = b ^ k.val * ψ u v p) (hk : k ≠ 0) :
    ∃ s ∈ T b B (R u v), (s * n) * b * (s * n)⁻¹ = b ^ k.val := by
  have hkey : ∀ k : ZMod 3, k ≠ 0 → ∀ p : Z3,
      k.val • (-(k * p.1, k * p.2) : Z3) + p = 0 := by decide
  obtain ⟨s, hs, hθ⟩ := C.θ_surj (ψ_mem C.E (-(k * p.1, k * p.2)))
  refine ⟨s, hs, ?_⟩
  have e1 : s * b ^ k.val * s⁻¹ = (θ b s * b) ^ k.val := by rw [← C.conj_b_T hs, conj_pow]
  have e2 : (θ b s * b) ^ k.val = θ b s ^ k.val * b ^ k.val :=
    (Commute.mul_pow (C.comm_bR (C.θ_mem hs)).symm _)
  have e3 : s * ψ u v p * s⁻¹ = ψ u v p := C.T_cen hs (ψ_mem C.E p)
  calc (s * n) * b * (s * n)⁻¹ = s * (n * b * n⁻¹) * s⁻¹ := by group
    _ = (s * b ^ k.val * s⁻¹) * (s * ψ u v p * s⁻¹) := by rw [h]; group
    _ = θ b s ^ k.val * b ^ k.val * ψ u v p := by rw [e1, e2, e3]
    _ = b ^ k.val * (θ b s ^ k.val * ψ u v p) := by
        rw [← (Commute.pow_pow (C.comm_bR (C.θ_mem hs)) k.val k.val).eq, mul_assoc]
    _ = b ^ k.val := by
        rw [hθ, ← ψ_nsmul C.E, ← ψ_add C.E, hkey k hk p, ψ_zero, mul_one]

theorem mono_N {n : G} (hn : n ∈ Nor B) :
    InBlocks u v (n * u * n⁻¹) ∧ InBlocks u v (n * v * n⁻¹) := by
  obtain ⟨k, hk, p, h⟩ := C.conj_b_form hn
  obtain ⟨s, hs, hsb⟩ := C.exists_T_fix hn h hk
  have hsn : s * n ∈ Nor B := Subgroup.mul_mem _ (C.T_le_N hs) hn
  have hbk : (s * n) * b * (s * n)⁻¹ = b ∨ (s * n) * b * (s * n)⁻¹ = b⁻¹ := by
    rw [hsb]
    rcases zmod3_cases k with rfl | rfl | rfl
    · exact absurd rfl hk
    · left; exact pow_val_one b
    · right; rw [pow_val_two, eq_inv_iff_mul_eq_one, ← pow_succ, C.b3]
  have hJ := C.D.nor_J hbk
  have hR : s * n ∈ Nor (R u v) := L13b.mem_nor_of_forall fun y hy => C.nor0 hsn hy
  obtain ⟨h1, h2⟩ := C.mono (s * n) hJ hR
  have e : ∀ x ∈ R u v, (s * n) * x * (s * n)⁻¹ = n * x * n⁻¹ := fun x hx => by
    have := C.T_cen hs (C.nor0 hn hx)
    calc (s * n) * x * (s * n)⁻¹ = s * (n * x * n⁻¹) * s⁻¹ := by group
      _ = n * x * n⁻¹ := this
  rw [e u C.uR] at h1
  rw [e v C.vR] at h2
  exact ⟨h1, h2⟩

theorem three_mem_T {n : G} (hn : n ∈ Nor B) {m : ℕ} (hm : n ^ (3 ^ m) = 1) :
    n ∈ T b B (R u v) := by
  obtain ⟨hu, hv⟩ := C.mono_N hn
  have hcen := cen_of_mono C.E hu hv hm
  have hC : n ∈ CenS (R u v) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hcen x hx
    calc x * n = (n * x * n⁻¹) * n := by rw [this]
      _ = n * x := by group
  obtain ⟨k, hk, p, h⟩ := C.conj_b_form hn
  refine ⟨hn, hC, ?_⟩
  rcases zmod3_cases k with rfl | rfl | rfl
  · exact absurd rfl hk
  · unfold θ
    rw [h, pow_val_one]
    rw [show b * ψ u v p * b⁻¹ = ψ u v p by rw [C.comm_bR (ψ_mem C.E p)]; group]
    exact ψ_mem C.E p
  · exfalso
    rw [pow_val_two] at h
    have hψ := ψ_mem C.E p
    have hn2 : n ^ 2 * b * (n ^ 2)⁻¹ = b := by
      have e : n ^ 2 * b * (n ^ 2)⁻¹ = n * (n * b * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      rw [e, h]
      have e2 : n * (b ^ 2 * ψ u v p) * n⁻¹ = (n * b * n⁻¹) ^ 2 * (n * ψ u v p * n⁻¹) := by
        rw [conj_pow]; group
      rw [e2, h, hcen _ hψ]
      have hc := C.comm_bR hψ
      have h3 := C.pow3_R hψ
      have hb3 := C.b3
      rw [(Commute.pow_left hc 2).mul_pow 2, ← pow_mul, mul_assoc, ← pow_succ, h3, mul_one,
        show 2 * 2 = 3 + 1 from rfl, pow_succ, hb3, one_mul]
    have hcomm : Commute (n ^ 2) b := by
      have : n ^ 2 * b = b * n ^ 2 := by
        calc n ^ 2 * b = (n ^ 2 * b * (n ^ 2)⁻¹) * n ^ 2 := by group
          _ = b * n ^ 2 := by rw [hn2]
      exact this
    have hodd : Odd (3 ^ m) := Odd.pow (by decide)
    obtain ⟨j, hj⟩ := hodd
    have hnn : n = (n ^ 2) ^ (j + 1) := by
      rw [← pow_mul]
      calc n = n ^ (3 ^ m) * n := by rw [hm, one_mul]
        _ = n ^ (2 * (j + 1)) := by rw [← pow_succ, hj]; ring_nf
    have hnb : n * b * n⁻¹ = b := by
      have : Commute n b := by rw [hnn]; exact hcomm.pow_left _
      rw [this.eq]; group
    rw [hnb] at h
    have := C.B_eq (k := 1) (l := 2) (p := 0) (q := p)
      (by rw [pow_val_one, ψ_zero, mul_one]; exact h)
    exact absurd this.1 (by decide)

theorem pgroup_le_T {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hQN : Q ≤ Nor B) :
    Q ≤ T b B (R u v) := fun x hx => by
  obtain ⟨m, hm⟩ := hQ ⟨x, hx⟩
  exact C.three_mem_T (hQN hx) (by simpa using congrArg Subtype.val hm)

end Ctx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
