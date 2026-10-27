module

public import CFSG.RankThree.SubgroupLists.MitchellFourBlocks
public import CFSG.RankThree.SubgroupLists.MitchellIsoDickson
import CFSG.RankThree.SubgroupLists.MitchellIcosaIso

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem orderOf_isoLeviBar_of_pow_four (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)}
    {x : GL V₄ K} (hxG : x ∈ G) (hxC : x ∈ isoCent K) (hx4 : x ^ 4 = -1) :
    orderOf (isoLeviBar hxG hxC) = 4 := by
  have hL4 : leviBlock (x : Matrix V₄ V₄ K) ^ 4 = -1 := by
    rw [← leviBlock_val_pow hxC, hx4, leviBlock_neg_one]
  have hne := one_ne_neg_one_matTwo h2
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, isoLeviBar_pow, isoLeviBar_eq_one_iff, leviBlock_val_pow hxC]
    rintro (h | h)
    · exact hne (by rw [← hL4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow])
    · exact hne (by rw [← hL4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, neg_one_sq])
  · rw [isoLeviBar_pow, isoLeviBar_eq_one_iff, show 2 ^ (1 + 1) = 4 from rfl, hx4,
      leviBlock_neg_one]
    exact Or.inr rfl

theorem sq_mul_sq_of_mem_isoCent {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) {G : Subgroup (GL V₄ (ZMod p))} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    (hneg : (-1 : GL V₄ (ZMod p)) ∈ G) {x y : GL V₄ (ZMod p)} (hxG : x ∈ G)
    (hxC : x ∈ isoCent (ZMod p)) (hyG : y ∈ G) (hyC : y ∈ isoCent (ZMod p)) (hx4 : x ^ 4 = -1)
    (hy4 : y ^ 4 = -1) :
    x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 ∨ x ^ 2 * y ^ 2 = -(y ^ 2 * x ^ 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP (by omega)
  have hk : x ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hx4, neg_one_sq]
  have hpk : ¬ p ∣ 8 := fun h => by
    have := Nat.le_of_dvd two_pos ((Fact.out : p.Prime).dvd_of_dvd_pow (n := 3) (by simpa using h))
    omega
  have hx1 : x ^ 4 ≠ 1 := by
    rw [hx4]
    intro h
    have h' := congrArg (fun g : GL V₄ (ZMod p) => leviBlock (g : Matrix V₄ V₄ (ZMod p))) h
    simp only [leviBlock_neg_one, Units.val_one, leviBlock_one] at h'
    exact one_ne_neg_one_matTwo h2 h'.symm
  have hcomm := sq_mul_sq_comm_of_orderOf_four (f := 1) (by rw [Nat.card_zmod, pow_one]) _
    (not_dvd_card_isoLeviImage hp7 hU0 hneg hxG hxC hk hpk hx1)
    (orderOf_isoLeviBar_of_pow_four h2 hxG hxC hx4) (orderOf_isoLeviBar_of_pow_four h2 hyG hyC hy4)
  rw [isoLeviBar_pow, isoLeviBar_pow, isoLeviBar_mul, isoLeviBar_mul] at hcomm
  exact eq_or_eq_neg_of_isoLeviBar_eq hU0 hneg _ _ _ _ hcomm

theorem sq_mul_sq_of_isotropic {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ (ZMod p)) ∈ G)
    {v : Matrix V₄ V₄ (ZMod p)} (hvM : v ∈ (cliffSpace : Submodule (ZMod p) _))
    (hvv : cliffB v v = 0) (hv0 : v ≠ 0) {x y : GL V₄ (ZMod p)} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxv : (x : Matrix V₄ V₄ (ZMod p)) * v = v * (x : Matrix V₄ V₄ (ZMod p)))
    (hyv : (y : Matrix V₄ V₄ (ZMod p)) * v = v * (y : Matrix V₄ V₄ (ZMod p)))
    (hx4 : x ^ 4 = -1) (hy4 : y ^ 4 = -1) :
    x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 ∨ x ^ 2 * y ^ 2 = -(y ^ 2 * x ^ 2) := by
  obtain ⟨k, -, hk⟩ := exists_isoFrame (two_ne_zero_of_charP (K := ZMod p) (p := p) (by omega))
    hvM hvv hv0
  have hf4 : ∀ {g : GL V₄ (ZMod p)}, g ^ 4 = -1 → frameHom (RingHom.id (ZMod p)) k g ^ 4 = -1 :=
    fun hg => by rw [← map_pow, hg, frameHom_neg_one]
  have hfneg : ∀ g : GL V₄ (ZMod p),
      frameHom (RingHom.id (ZMod p)) k (-g) = -frameHom (RingHom.id (ZMod p)) k g := fun g => by
    rw [← neg_one_mul, map_mul, frameHom_neg_one, neg_one_mul]
  rcases sq_mul_sq_of_mem_isoCent hp7 (frameGroup_U0 (RingHom.id (ZMod p)) k hU0)
      (frameGroup_neg (RingHom.id (ZMod p)) k hneg) (mem_frameGroup (RingHom.id (ZMod p)) k hxG)
      (hk x (hGS hxG) hxv) (mem_frameGroup (RingHom.id (ZMod p)) k hyG) (hk y (hGS hyG) hyv)
      (hf4 hx4) (hf4 hy4) with h | h
  · left
    apply frameHom_injective (RingHom.id (ZMod p)) k
    simpa only [map_mul, map_pow] using h
  · right
    apply frameHom_injective (RingHom.id (ZMod p)) k
    simpa only [map_mul, map_pow, hfneg] using h

end CFSG.RankThree.SubgroupLists
