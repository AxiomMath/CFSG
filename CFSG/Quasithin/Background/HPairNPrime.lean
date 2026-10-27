module

public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.HSL3Fix

public section

namespace CFSG.Quasithin

namespace H

namespace PairN

open CFSG.Open CFSG.Assembly.LowTwoRank PairG
open scoped Pointwise

section Fix

variable {W : Type*} [Group W]

@[expose] def fixSub (u : MulAut W) : Subgroup W where
  carrier := {w | u w = w}
  mul_mem' {a b} ha hb := by
    change u (a * b) = a * b
    rw [map_mul, show u a = a from ha, show u b = b from hb]
  one_mem' := map_one u
  inv_mem' {a} ha := by
    change u a⁻¹ = a⁻¹
    rw [map_inv, show u a = a from ha]

theorem card_fixSub (u : MulAut W) : Nat.card (fixSub u) = Nat.card {w : W // u w = w} := rfl

theorem card_fix_inv (u : MulAut W) :
    Nat.card {w : W // u⁻¹ w = w} = Nat.card {w : W // u w = w} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  constructor
  · intro h
    calc u w = u (u⁻¹ w) := by rw [h]
      _ = w := MulAut.apply_inv_self W u w
  · intro h
    calc u⁻¹ w = u⁻¹ (u w) := by rw [h]
      _ = w := MulAut.inv_apply_self W u w

variable [Finite W]

theorem card_fix_modEq {p : ℕ} [hp : Fact p.Prime] {u : MulAut W} {k : ℕ} (hu : u ^ p ^ k = 1) :
    Nat.card {w : W // u w = w} ≡ Nat.card W [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers u) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hu)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have h := hP.card_modEq_card_fixedPoints W
  have e : Nat.card (MulAction.fixedPoints (Subgroup.zpowers u) W) =
      Nat.card {w : W // u w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    constructor
    · intro hw
      exact hw ⟨u, Subgroup.mem_zpowers u⟩
    · intro hw g
      have hle : Subgroup.zpowers u ≤ MulAction.stabilizer (MulAut W) w :=
        (Subgroup.zpowers_le).mpr (MulAction.mem_stabilizer_iff.mpr hw)
      exact MulAction.mem_stabilizer_iff.mp (hle g.2)
  rw [e] at h
  exact h.symm

omit [Finite W] in
theorem card_fix_dvd (u : MulAut W) : Nat.card {w : W // u w = w} ∣ Nat.card W := by
  rw [← card_fixSub]
  exact Subgroup.card_subgroup_dvd_card _

theorem eq_one_of_card_fix (u : MulAut W) (h : Nat.card {w : W // u w = w} = Nat.card W) :
    u = 1 := by
  have htop : fixSub u = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [card_fixSub, h])
  ext w
  have : w ∈ fixSub u := htop ▸ Subgroup.mem_top w
  exact this

omit [Finite W] in
theorem eq_one_or_eq_of_dvd_sixteen {n : ℕ} (hn : n ∣ 16) (h5 : n ≡ 1 [MOD 5]) :
    n = 1 ∨ n = 16 := by
  have key : ∀ m : ℕ, m ≤ 16 → m ∣ 16 → m % 5 = 1 → m = 1 ∨ m = 16 := by decide
  exact key n (Nat.le_of_dvd (by norm_num) hn) hn h5

theorem card_fix_eq_one_of_pow_five (hW : Nat.card W = 16) {u : MulAut W} (hu : u ^ 5 = 1)
    (hu1 : u ≠ 1) : Nat.card {w : W // u w = w} = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := card_fix_modEq (p := 5) (k := 1) (u := u) (by rwa [pow_one])
  rw [hW] at hmod
  have hdvd := card_fix_dvd u
  rw [hW] at hdvd
  rcases eq_one_or_eq_of_dvd_sixteen hdvd hmod with h | h
  · exact h
  · exact absurd (eq_one_of_card_fix u (h.trans hW.symm)) hu1

theorem eq_one_of_fix_five (hW : Nat.card W = 16) {u : MulAut W} (hu : u ^ 5 = 1)
    (hu1 : u ≠ 1) {w : W} (hw : u w = w) : w = 1 := by
  have h1 := card_fix_eq_one_of_pow_five hW hu hu1
  have : Subsingleton {w : W // u w = w} := (Nat.card_eq_one_iff_unique.mp h1).1
  exact congrArg Subtype.val (Subsingleton.elim (⟨w, hw⟩ : {w : W // u w = w}) ⟨1, map_one u⟩)

omit [Finite W] in
theorem commute_inv {u v : MulAut W} (huv : u * v = v * u) : v * u⁻¹ = u⁻¹ * v := by
  calc v * u⁻¹ = u⁻¹ * (u * v) * u⁻¹ := by group
    _ = u⁻¹ * (v * u) * u⁻¹ := by rw [huv]
    _ = u⁻¹ * v := by group

omit [Finite W] in
@[expose] def restrFix (u v : MulAut W) (huv : u * v = v * u) : MulAut (fixSub v) where
  toFun w := ⟨u w, by
    change v (u w) = u w
    rw [← MulAut.mul_apply, ← huv, MulAut.mul_apply, show v w = w from w.2]⟩
  invFun w := ⟨u⁻¹ w, by
    change v (u⁻¹ w) = u⁻¹ w
    rw [← MulAut.mul_apply, commute_inv huv, MulAut.mul_apply, show v w = w from w.2]⟩
  left_inv w := Subtype.ext (MulAut.inv_apply_self W u w)
  right_inv w := Subtype.ext (MulAut.apply_inv_self W u w)
  map_mul' a b := Subtype.ext (map_mul u (a : W) b)

omit [Finite W] in
theorem restrFix_pow_apply (u v : MulAut W) (huv : u * v = v * u) (n : ℕ) (w : fixSub v) :
    (((restrFix u v huv) ^ n) w : W) = (u ^ n) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
    rfl

theorem card_fix_of_commute_five (hW : Nat.card W = 16) {u v : MulAut W} (hu : u ^ 5 = 1)
    (hu1 : u ≠ 1) (huv : u * v = v * u) :
    Nat.card {w : W // v w = w} = 1 ∨ v = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set r := restrFix u v huv with hr
  have hr5 : r ^ 5 = 1 := by
    ext w
    have h := restrFix_pow_apply u v huv 5 w
    rw [hu] at h
    exact h
  have hfix : Nat.card {w : fixSub v // r w = w} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, map_one r⟩⟩⟩
    have ha : (a : fixSub v) = 1 := Subtype.ext
      (eq_one_of_fix_five hW hu hu1 (congrArg Subtype.val a.2))
    have hb : (b : fixSub v) = 1 := Subtype.ext
      (eq_one_of_fix_five hW hu hu1 (congrArg Subtype.val b.2))
    exact Subtype.ext (ha.trans hb.symm)
  have hmod := card_fix_modEq (p := 5) (k := 1) (u := r) (by rwa [pow_one])
  rw [hfix, card_fixSub] at hmod
  have hdvd := card_fix_dvd v
  rw [hW] at hdvd
  rcases eq_one_or_eq_of_dvd_sixteen hdvd hmod.symm with h | h
  · exact Or.inl h
  · exact Or.inr (eq_one_of_card_fix v (h.trans hW.symm))

theorem eq_one_of_commute_five_of_two (hW : Nat.card W = 16) {u v : MulAut W} (hu : u ^ 5 = 1)
    (hu1 : u ≠ 1) (huv : u * v = v * u) {k : ℕ} (hv : v ^ 2 ^ k = 1) : v = 1 := by
  rcases card_fix_of_commute_five hW hu hu1 huv with h | h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmod := card_fix_modEq (p := 2) hv
    rw [h, hW] at hmod
    exact absurd hmod (by decide)
  · exact h

end Fix

section Pair

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

omit [Fintype ι] [DecidableEq ι] in
theorem map_V₂_swapAut : (V₂ ι K).map (swapAut ι K).toMonoidHom = V₁ ι K := by
  rw [← map_V₁_swapAut (ι := ι) (K := K), Subgroup.map_map]
  have : (swapAut ι K).toMonoidHom.comp (swapAut ι K).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun _ => rfl
  rw [this, Subgroup.map_id]

omit [Fintype ι] [DecidableEq ι] in
theorem conj_swapAut_mul_pairAut (a b c d : MulAut (StdMod ι K)) :
    (swapAut ι K * pairAut c d) * pairAut a b * (swapAut ι K * pairAut c d)⁻¹ =
      pairAut (d * b * d⁻¹) (c * a * c⁻¹) := by
  rw [_root_.mul_inv_rev, pairAut_inv]
  calc swapAut ι K * pairAut c d * pairAut a b * (pairAut c⁻¹ d⁻¹ * (swapAut ι K)⁻¹) =
      swapAut ι K * (pairAut c d * pairAut a b * pairAut c⁻¹ d⁻¹) * (swapAut ι K)⁻¹ := by
        simp only [mul_assoc]
    _ = pairAut (d * b * d⁻¹) (c * a * c⁻¹) := by
        rw [pairAut_mul, pairAut_mul, swapAut_conj_pairAut]

omit [Fintype ι] [DecidableEq ι] in
theorem map_mul_toMonoidHom (x y : MulAut (PairMod ι K)) (J : Subgroup (PairMod ι K)) :
    J.map (x * y).toMonoidHom = (J.map y.toMonoidHom).map x.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

variable [Nonempty ι] {Γ : Subgroup (GL ι K)} {θ : ↥Γ →* ↥Γ}
variable (hΓ : IsNatIrr Γ) (hθ : Function.Surjective θ)
  (hniso : ¬ Pair.IsoMod (pairImg Γ θ) (V₁ ι K) (V₂ ι K))
include hΓ hθ hniso

theorem map_V₂_eq_V₁ {x : MulAut (PairMod ι K)} (hx : x ∈ pairNorm Γ θ)
    (h : (V₁ ι K).map x.toMonoidHom = V₂ ι K) : (V₂ ι K).map x.toMonoidHom = V₁ ι K := by
  have hid : (V₁ ι K).map (x * x⁻¹).toMonoidHom = V₁ ι K := by
    rw [mul_inv_cancel]
    exact Subgroup.map_id _
  rw [map_mul_toMonoidHom] at hid
  rcases map_V₁_eq_or hΓ hθ hniso (Subgroup.inv_mem _ hx) with h' | h'
  · exfalso
    apply V₁_ne_V₂ (ι := ι) (K := K)
    rw [h', h] at hid
    exact hid.symm
  · rw [h'] at hid
    exact hid

theorem map_V₁_pow_of_swap {x : MulAut (PairMod ι K)} (hx : x ∈ pairNorm Γ θ)
    (h : (V₁ ι K).map x.toMonoidHom = V₂ ι K) (n : ℕ) :
    (V₁ ι K).map (x ^ (2 * n)).toMonoidHom = V₁ ι K ∧
      (V₁ ι K).map (x ^ (2 * n + 1)).toMonoidHom = V₂ ι K := by
  have h2 := map_V₂_eq_V₁ hΓ hθ hniso hx h
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [mul_zero, pow_zero]
      exact Subgroup.map_id _
    · rw [mul_zero, zero_add, pow_one]
      exact h
  | succ n ih =>
    have e1 : x ^ (2 * (n + 1)) = x * x ^ (2 * n + 1) := by
      rw [← pow_succ']
      ring_nf
    have e2 : x ^ (2 * (n + 1) + 1) = x * x ^ (2 * (n + 1)) := by
      rw [← pow_succ']
    have h3 : (V₁ ι K).map (x ^ (2 * (n + 1))).toMonoidHom = V₁ ι K := by
      rw [e1, map_mul_toMonoidHom, ih.2, h2]
    refine ⟨h3, ?_⟩
    rw [e2, map_mul_toMonoidHom, h3, h]

theorem map_V₁_of_pow_odd {x : MulAut (PairMod ι K)} (hx : x ∈ pairNorm Γ θ) {p : ℕ}
    (hp : Odd p) (hxp : x ^ p = 1) : (V₁ ι K).map x.toMonoidHom = V₁ ι K := by
  rcases map_V₁_eq_or hΓ hθ hniso hx with h | h
  · exact h
  · exfalso
    obtain ⟨n, rfl⟩ := hp
    have h1 := (map_V₁_pow_of_swap hΓ hθ hniso hx h n).2
    rw [hxp] at h1
    apply V₁_ne_V₂ (ι := ι) (K := K)
    rw [← h1]
    exact (Subgroup.map_id _).symm

theorem mem_pairSub_iff_map {x : MulAut (PairMod ι K)} (hx : x ∈ pairNorm Γ θ) :
    x ∈ pairSub ι K ↔ (V₁ ι K).map x.toMonoidHom = V₁ ι K := by
  constructor
  · intro hs
    obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp hs
    exact map_V₁_pairAut a b
  · intro h1
    obtain ⟨a, b, rfl⟩ := exists_pairAut hΓ hθ hniso hx h1
    exact pairAut_mem_pairSub a b

theorem map_V₁_eq_V₂_of_not_mem {x : MulAut (PairMod ι K)} (hx : x ∈ pairNorm Γ θ)
    (hxs : x ∉ pairSub ι K) : (V₁ ι K).map x.toMonoidHom = V₂ ι K :=
  (map_V₁_eq_or hΓ hθ hniso hx).resolve_left fun h =>
    hxs ((mem_pairSub_iff_map hΓ hθ hniso hx).mpr h)

theorem eq_swapAut_mul {x : MulAut (PairMod ι K)} (hx : x ∈ pairNorm Γ θ)
    (h : (V₁ ι K).map x.toMonoidHom = V₂ ι K) :
    ∃ c d : MulAut (StdMod ι K), x = swapAut ι K * pairAut c d := by
  have h2 := map_V₂_eq_V₁ hΓ hθ hniso hx h
  obtain ⟨c, d, hcd⟩ := exists_pairAut_of_map (x := swapAut ι K * x)
    (by rw [map_mul_toMonoidHom, h, map_V₂_swapAut])
    (by rw [map_mul_toMonoidHom, h2, map_V₁_swapAut])
  refine ⟨c, d, ?_⟩
  calc x = swapAut ι K * (swapAut ι K * x) := by rw [← mul_assoc, swapAut_mul_self, one_mul]
    _ = swapAut ι K * pairAut c d := by rw [hcd]

theorem exists_swap_mem_sylow {X : Subgroup (MulAut (PairMod ι K))} (hX2 : X ≤ pairNorm Γ θ)
    (hX3 : ∃ x ∈ X, x ∉ pairSub ι K) {S : Subgroup (MulAut (PairMod ι K))}
    (hS : IsSylowIn 2 S X) : ∃ s ∈ S, (V₁ ι K).map s.toMonoidHom = V₂ ι K := by
  by_contra hno
  push Not at hno
  have h' : ∀ s ∈ S, s ∈ pairSub ι K := fun s hs =>
    (mem_pairSub_iff_map hΓ hθ hniso (hX2 (hS.le hs))).mpr
      ((map_V₁_eq_or hΓ hθ hniso (hX2 (hS.le hs))).resolve_right (hno s hs))
  obtain ⟨x, hxX, hx⟩ := hX3
  have hxV := map_V₁_eq_V₂_of_not_mem hΓ hθ hniso (hX2 hxX) hx
  set X₀ := X ⊓ pairSub ι K with hX₀
  have hidx : (X₀.subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, hxX⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hX₀, Subgroup.mem_inf]
    by_cases hb : (b : MulAut (PairMod ι K)) ∈ pairSub ι K
    · refine Or.inr ⟨⟨b.2, hb⟩, fun hbx => hx ?_⟩
      have := (pairSub ι K).mul_mem ((pairSub ι K).inv_mem hb) hbx.2
      simpa using this
    · refine Or.inl ⟨⟨X.mul_mem b.2 hxX, ?_⟩, fun hb' => hb hb'.2⟩
      have hbV := map_V₁_eq_V₂_of_not_mem hΓ hθ hniso (hX2 b.2) hb
      refine (mem_pairSub_iff_map hΓ hθ hniso (hX2 (X.mul_mem b.2 hxX))).mpr ?_
      rw [map_mul_toMonoidHom, hxV, map_V₂_eq_V₁ hΓ hθ hniso (hX2 b.2) hbV]
  have hSX₀ : S ≤ X₀ := fun y hy => ⟨hS.le hy, h' y hy⟩
  have hrel := Subgroup.relIndex_mul_relIndex S X₀ X hSX₀ inf_le_left
  apply hS.not_dvd_relIndex
  rw [← hrel]
  have h2 : X₀.relIndex X = 2 := hidx
  rw [h2]
  exact dvd_mul_left 2 _

theorem isInv_eq {J : Subgroup (PairMod ι K)} (hJ : Pair.IsInv (pairImg Γ θ) J) :
    J = ⊥ ∨ J = V₁ ι K ∨ J = V₂ ι K ∨ J = ⊤ := by
  have hI₁ := isIrr_V₁ (θ := θ) hΓ
  have hI₂ := isIrr_V₂ hΓ hθ
  have hinv1 : Pair.IsInv (pairImg Γ θ) (J ⊓ V₁ ι K) := fun l hl w hw =>
    ⟨hJ l hl w hw.1, isInv_V₁ Γ θ l hl w hw.2⟩
  have hinv2 : Pair.IsInv (pairImg Γ θ) (J ⊓ V₂ ι K) := fun l hl w hw =>
    ⟨hJ l hl w hw.1, isInv_V₂ Γ θ l hl w hw.2⟩
  have hsub1 : J ⊓ V₁ ι K = V₁ ι K → V₁ ι K ≤ J := fun h => h ▸ inf_le_left
  have hsub2 : J ⊓ V₂ ι K = V₂ ι K → V₂ ι K ≤ J := fun h => h ▸ inf_le_left
  rcases hI₁.2 _ inf_le_right hinv1 with h1 | h1 <;>
    rcases hI₂.2 _ inf_le_right hinv2 with h2 | h2
  · by_contra hne
    exact hniso (SL3One.isoMod_of_inf_eq_bot V₁_inf_V₂ V₁_sup_V₂ (isInv_V₁ Γ θ) (isInv_V₂ Γ θ)
      hI₁ hI₂ hJ (fun h => hne (Or.inl h)) h1 h2)
  · right; right; left
    refine le_antisymm (fun x hx => ?_) (hsub2 h2)
    have hx2 : ((1, x.2) : PairMod ι K) ∈ J := hsub2 h2 (mem_V₂.mpr rfl)
    have hx1 : ((x.1, 1) : PairMod ι K) ∈ J ⊓ V₁ ι K := by
      refine ⟨?_, mem_V₁.mpr rfl⟩
      have h := J.mul_mem hx (J.inv_mem hx2)
      have heq : x * ((1, x.2) : PairMod ι K)⁻¹ = (x.1, 1) := Prod.ext (by simp) (by simp)
      rwa [heq] at h
    rw [h1, Subgroup.mem_bot] at hx1
    rw [mem_V₂]
    exact congrArg Prod.fst hx1
  · right; left
    refine le_antisymm (fun x hx => ?_) (hsub1 h1)
    have hx1 : ((x.1, 1) : PairMod ι K) ∈ J := hsub1 h1 (mem_V₁.mpr rfl)
    have hx2 : ((1, x.2) : PairMod ι K) ∈ J ⊓ V₂ ι K := by
      refine ⟨?_, mem_V₂.mpr rfl⟩
      have h := J.mul_mem (J.inv_mem hx1) hx
      have heq : ((x.1, 1) : PairMod ι K)⁻¹ * x = (1, x.2) := Prod.ext (by simp) (by simp)
      rwa [heq] at h
    rw [h2, Subgroup.mem_bot] at hx2
    rw [mem_V₁]
    exact congrArg Prod.snd hx2
  · right; right; right
    rw [eq_top_iff, ← V₁_sup_V₂]
    exact sup_le (hsub1 h1) (hsub2 h2)

theorem congrHom_not_mem_pairSub {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U₁ : Subgroup V} (hinv₁ : Pair.IsInv H U₁) (hU₁ : U₁ ≠ ⊥) {φ : MulAut V}
    (hinf : U₁ ⊓ U₁.map φ.toMonoidHom = ⊥) (e : V ≃* PairMod ι K)
    (he : H.map (congrHom e) = pairImg Γ θ) (hxN : congrHom e φ ∈ pairNorm Γ θ) :
    congrHom e φ ∉ pairSub ι K := by
  intro hx
  have hmodel : Pair.IsInv (pairImg Γ θ) (U₁.map e.toMonoidHom) := by
    intro l hl
    rw [← he] at hl
    obtain ⟨h, hh, rfl⟩ := hl
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨h w, hinv₁ h hh w hw, by simp⟩
  have hmap : (U₁.map φ.toMonoidHom).map e.toMonoidHom =
      (U₁.map e.toMonoidHom).map (congrHom e φ).toMonoidHom := by
    have hcomm : e.toMonoidHom.comp φ.toMonoidHom =
        (congrHom e φ).toMonoidHom.comp e.toMonoidHom :=
      MonoidHom.ext fun v => by
        show e (φ v) = congrHom e φ (e v)
        rw [congrHom_apply, MulEquiv.symm_apply_apply]
    rw [Subgroup.map_map, Subgroup.map_map, hcomm]
  have hinfe : (U₁.map e.toMonoidHom) ⊓ (U₁.map φ.toMonoidHom).map e.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf U₁ (U₁.map φ.toMonoidHom) e.toMonoidHom e.injective, hinf,
      Subgroup.map_bot]
  have hx1 : (V₁ ι K).map (congrHom e φ).toMonoidHom = V₁ ι K :=
    (mem_pairSub_iff_map hΓ hθ hniso hxN).mp hx
  have hx2 := map_V₂_eq hΓ hθ hniso hxN hx1
  have hne : U₁.map e.toMonoidHom ≠ ⊥ := fun h =>
    hU₁ ((Subgroup.map_eq_bot_iff_of_injective U₁ e.injective).mp h)
  rcases isInv_eq hΓ hθ hniso hmodel with h | h | h | h
  · exact hne h
  · rw [hmap, h, hx1, inf_idem] at hinfe
    exact (isIrr_V₁ (θ := θ) hΓ).1 hinfe
  · rw [hmap, h, hx2, inf_idem] at hinfe
    exact (isIrr_V₂ hΓ hθ).1 hinfe
  · rw [hmap, h, Subgroup.map_top_of_surjective _ (congrHom e φ).surjective, inf_idem] at hinfe
    exact (isIrr_V₁ (θ := θ) hΓ).1 (le_bot_iff.mp (hinfe ▸ (le_top : V₁ ι K ≤ ⊤)))

end Pair

theorem nPrime_eq_one_of {M : Type*} [Group M] [Finite M] {X : Subgroup M}
    (h : ∀ B S : Subgroup M, B ≤ X → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Odd (Nat.card B) →
      IsSylowIn 2 S X → (B : Set M) * (S : Set M) = (S : Set M) * (B : Set M) → B = ⊥) :
    E3.nPrime X = 1 := by
  refine le_antisymm ?_ (E3.one_le_nPrime X)
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, -, hYc, hBab, hBodd, hS, hBS⟩
    have hB := h B S hBX hBab hBodd hS hBS
    have hY : Y = ⊥ := le_bot_iff.mp (hB ▸ hYB)
    rw [hY, Subgroup.card_bot] at hYc
    by_contra hc
    push Not at hc
    have h4 : 2 ^ 2 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
    omega

end PairN

end H

end CFSG.Quasithin
