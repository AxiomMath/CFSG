module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalf

theorem two_mul_lt_of_lt_half {n j : ℕ} (hj : j < (n + 1) / 2) : 2 * j < n := by omega

private noncomputable def tPow {G : Type*} [Group G] (g : G) (hg : g ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun a := g ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val +
      (Multiplicative.toAdd b).val) 3, pow_add, pow_mul, hg, one_pow, mul_one]

private noncomputable def tIdx (n : ℕ) (j : Fin ((n + 1) / 2)) : Fin n :=
  ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩

private theorem tIdx_even (n : ℕ) (j : Fin ((n + 1) / 2)) : (tIdx n j).val % 2 = 0 := by
  show (2 * j.val) % 2 = 0
  omega

private noncomputable def tG (n : ℕ) (j : Fin ((n + 1) / 2)) :
    SpecialLinearGroup (Fin (n + 1)) F2 := omegaBlock n (tIdx n j)

private theorem tG_mem (n : ℕ) (j : Fin ((n + 1) / 2)) : tG n j ∈ halfTorus n :=
  Subgroup.subset_closure ⟨tIdx n j, tIdx_even n j, rfl⟩

private theorem tG_pow_mem (n : ℕ) (j : Fin ((n + 1) / 2)) (k : ℕ) :
    (tG n j) ^ k ∈ halfTorus n := Subgroup.pow_mem _ (tG_mem n j) k

private noncomputable def tCoord (n : ℕ) (j : Fin ((n + 1) / 2)) :
    Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin (n + 1)) F2 :=
  tPow (tG n j) (omegaBlock_pow_three n (tIdx n j))

private theorem tCoord_apply (n : ℕ) (j : Fin ((n + 1) / 2))
    (a : Multiplicative (ZMod 3)) :
    tCoord n j a = (tG n j) ^ (Multiplicative.toAdd a).val := rfl

private theorem tCoord_commute (n : ℕ) :
    Pairwise fun i j : Fin ((n + 1) / 2) =>
      ∀ x y : Multiplicative (ZMod 3), Commute (tCoord n i x) (tCoord n j y) := by
  intro i j _ x y
  rw [tCoord_apply, tCoord_apply]
  exact (commute_iff_eq _ _).mpr
    (halfTorus_comm (tG_pow_mem n i (Multiplicative.toAdd x).val)
      (tG_pow_mem n j (Multiplicative.toAdd y).val))

private noncomputable def tPhi (n : ℕ) :
    (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) →*
      SpecialLinearGroup (Fin (n + 1)) F2 :=
  MonoidHom.noncommPiCoprod (tCoord n) (tCoord_commute n)

theorem exists_torusCoord (n : ℕ) :
    ∃ Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n),
      ∀ j : Fin ((n + 1) / 2),
        ((Φ (Pi.mulSingle j (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
          SpecialLinearGroup (Fin (n + 1)) F2) =
          omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩ := by
  have hle : (tPhi n).range ≤ halfTorus n := by
    rw [tPhi, MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    rw [tCoord_apply]
    exact tG_pow_mem n i (Multiplicative.toAdd a).val
  have hge : halfTorus n ≤ (tPhi n).range := by
    rw [halfTorus, Subgroup.closure_le]
    rintro t ⟨k, hk, rfl⟩
    rw [tPhi, MonoidHom.noncommPiCoprod_range]
    let i : Fin ((n + 1) / 2) := ⟨k.val / 2, by omega⟩
    have hik : tIdx n i = k := by
      apply Fin.ext
      show 2 * (k.val / 2) = k.val
      omega
    refine Subgroup.mem_iSup_of_mem i ?_
    refine ⟨Multiplicative.ofAdd (1 : ZMod 3), ?_⟩
    haveI : Fact (1 < 3) := ⟨by norm_num⟩
    rw [tCoord_apply, show omegaBlock n k = tG n i by rw [tG, hik], toAdd_ofAdd]
    change tG n i ^ (1 : ZMod 3).val = tG n i
    rw [ZMod.val_one 3, pow_one]
  let tPhiC : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) →* ↥(halfTorus n) :=
    (tPhi n).codRestrict (halfTorus n) fun x => hle (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hsurj : Function.Surjective tPhiC := by
    intro y
    obtain ⟨d, hd⟩ := hge y.2
    exact ⟨d, Subtype.ext hd⟩
  have hcardD : Nat.card (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) =
      3 ^ ((n + 1) / 2) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_multiplicative, ZMod.card,
      Fintype.card_fin]
  have hcard : Nat.card (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) =
      Nat.card ↥(halfTorus n) := by
    rw [hcardD, card_halfTorus]
  have hbij : Function.Bijective tPhiC :=
    (Nat.bijective_iff_surjective_and_card tPhiC).mpr ⟨hsurj, hcard⟩
  refine ⟨MulEquiv.ofBijective tPhiC hbij, ?_⟩
  intro j
  rw [MulEquiv.ofBijective_apply]
  change tPhi n (Pi.mulSingle j (Multiplicative.ofAdd 1)) =
    omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩
  rw [tPhi, MonoidHom.noncommPiCoprod_mulSingle, tCoord_apply]
  haveI : Fact (1 < 3) := ⟨by norm_num⟩
  rw [toAdd_ofAdd, ZMod.val_one 3, pow_one]
  rfl

end GGHalf

private theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {w : G} (h : ∀ b ∈ H, w * b * w⁻¹ ∈ H) :
    w ∈ Subgroup.normalizer (H : Set G) := by
  have hpow : ∀ n : ℕ, ∀ b ∈ H, w ^ n * b * (w ^ n)⁻¹ ∈ H := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      have h1 := h _ (ih b hb)
      rw [pow_succ', _root_.mul_inv_rev]
      simpa only [mul_assoc] using h1
  have hinv : w⁻¹ = w ^ (Nat.card G - 1) := by
    have h1 : w ^ Nat.card G = 1 := pow_card_eq_one'
    have h2 : 1 ≤ Nat.card G := Nat.card_pos
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel h2, h1]
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  have h3 := hpow (Nat.card G - 1) (w * b * w⁻¹) hb
  rw [← hinv, inv_inv] at h3
  simpa [mul_assoc] using h3

private theorem mem_normalizer_of_act {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {A : Type} [Group A] {T : Subgroup A} {φ : A →* G} {L : Subgroup G}
    (hTle : T.map φ ≤ Bs) (hL : φ.range = L)
    (hact : ∀ b ∈ Bs, ∃ t ∈ T, ∀ l ∈ L, b * l * b⁻¹ = φ t * l * (φ t)⁻¹)
    {a : A} (ha : ∀ t ∈ T, a * t * a⁻¹ ∈ T) :
    φ a ∈ Subgroup.normalizer (Bs : Set G) := by
  refine mem_normalizer_of_conj_mem fun b hb => ?_
  obtain ⟨t, ht, htl⟩ := hact b hb
  have haL : φ a ∈ L := by rw [← hL]; exact ⟨a, rfl⟩
  have hcL : ((φ t)⁻¹ * b) * φ a * ((φ t)⁻¹ * b)⁻¹ = φ a := by
    calc ((φ t)⁻¹ * b) * φ a * ((φ t)⁻¹ * b)⁻¹
        = (φ t)⁻¹ * (b * φ a * b⁻¹) * φ t := by group
      _ = (φ t)⁻¹ * (φ t * φ a * (φ t)⁻¹) * φ t := by rw [htl (φ a) haL]
      _ = φ a := by group
  have hcinv : ((φ t)⁻¹ * b) * (φ a)⁻¹ = (φ a)⁻¹ * ((φ t)⁻¹ * b) := by
    have hc : (φ t)⁻¹ * b * φ a = φ a * ((φ t)⁻¹ * b) := by
      calc (φ t)⁻¹ * b * φ a
          = (φ t)⁻¹ * b * φ a * ((φ t)⁻¹ * b)⁻¹ * ((φ t)⁻¹ * b) := by group
        _ = φ a * ((φ t)⁻¹ * b) := by rw [hcL]
    calc ((φ t)⁻¹ * b) * (φ a)⁻¹
        = (φ a)⁻¹ * ((φ a) * ((φ t)⁻¹ * b)) * (φ a)⁻¹ := by group
      _ = (φ a)⁻¹ * (((φ t)⁻¹ * b) * φ a) * (φ a)⁻¹ := by rw [← hc]
      _ = (φ a)⁻¹ * ((φ t)⁻¹ * b) := by group
  have hmain : φ a * b * (φ a)⁻¹ = φ (a * t * a⁻¹ * t⁻¹) * b := by
    calc φ a * b * (φ a)⁻¹
        = φ a * φ t * ((φ t)⁻¹ * b) * (φ a)⁻¹ := by group
      _ = φ a * φ t * (φ a)⁻¹ * ((φ t)⁻¹ * b) := by
            calc φ a * φ t * ((φ t)⁻¹ * b) * (φ a)⁻¹
                = (φ a * φ t) * (((φ t)⁻¹ * b) * (φ a)⁻¹) := by group
              _ = (φ a * φ t) * ((φ a)⁻¹ * ((φ t)⁻¹ * b)) := by rw [hcinv]
              _ = φ a * φ t * (φ a)⁻¹ * ((φ t)⁻¹ * b) := by group
      _ = φ (a * t * a⁻¹) * ((φ t)⁻¹ * b) := by
            conv_lhs => rw [← map_inv, ← map_mul, ← map_mul]
      _ = φ (a * t * a⁻¹) * (φ t)⁻¹ * b := by group
      _ = φ (a * t * a⁻¹ * t⁻¹) * b := by
            conv_lhs => rw [← map_inv, ← map_mul]
  rw [hmain]
  exact Bs.mul_mem (hTle (Subgroup.mem_map.mpr
    ⟨a * t * a⁻¹ * t⁻¹, T.mul_mem (ha t ht) (T.inv_mem ht), rfl⟩)) hb

theorem GGHalfTorusFrame.mem_normalizer {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {N : ℕ} {T : Subgroup (SpecialLinearGroup (Fin (N + 1)) F2)}
    {ψ : SpecialLinearGroup (Fin (N + 1)) F2 →* G} (hψ : GGHalfTorusFrame Bs X T ψ)
    {a : SpecialLinearGroup (Fin (N + 1)) F2}
    (ha : a ∈ Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin (N + 1)) F2))) :
    ψ a ∈ Subgroup.normalizer (Bs : Set G) :=
  mem_normalizer_of_act hψ.torus_le hψ.range hψ.act
    fun t ht => (Subgroup.mem_normalizer_iff.mp ha t).mp ht

end CFSG.StandardType

end
