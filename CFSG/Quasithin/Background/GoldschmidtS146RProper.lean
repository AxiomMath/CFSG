module

public import CFSG.Quasithin.Background.GoldschmidtS146RAux
public import CFSG.Quasithin.Background.GoldschmidtS146RCtx
public import CFSG.Quasithin.Background.GoldschmidtS146RLat

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem inf_eq_pCoreOf_of_simple {H J K : Subgroup G} [(J.subgroupOf H).Normal] (hKH : K ≤ H)
    (hJH : J ≤ H) (hOJ : pCoreOf 2 K ≤ J) (hKJ : ¬ K ≤ J) (hsimp : IsSimpleGroup (KBar K)) :
    K ⊓ J = pCoreOf 2 K := by
  have hOK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  refine le_antisymm ?_ (le_inf hOK hOJ)
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mp inferInstance
  have hAn : ((K ⊓ J).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, hHJ (hKH hk)⟩)
  have hnorm : (imgJ K (pCoreOf 2 K) (K ⊓ J)).Normal := normal_imgJ hAn
  have := hnorm
  rcases hsimp.eq_bot_or_eq_top_of_normal (imgJ K (pCoreOf 2 K) (K ⊓ J)) with h0 | h1
  · intro x hx
    have hxK : x ∈ K := hx.1
    have : ((⟨x, hxK⟩ : ↥K) : ↥K ⧸ (pCoreOf 2 K).subgroupOf K) ∈
        imgJ K (pCoreOf 2 K) (K ⊓ J) := mem_imgJ.mpr ⟨⟨x, hxK⟩, hx, rfl⟩
    rw [h0] at this
    have h2 := (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp this)
    simpa [Subgroup.mem_subgroupOf] using h2
  · exfalso
    have hOA : pCoreOf 2 K ≤ K ⊓ J := le_inf hOK hOJ
    have := (imgJ_eq_top_iff hOA inf_le_left).mp h1
    apply hKJ
    rw [← this]
    exact inf_le_right

theorem nonab_of_card_ordL2 {Q : Type} [Group Q] (hQ : IsSimpleGroup Q) {m : ℕ} (hm : 2 ≤ m)
    (hcard : Nat.card Q = ordL2 m) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hx4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hx2 : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hcard, ordL2]
    have : 0 < (2 ^ m) ^ 2 - 1 := Nat.sub_pos_of_lt (by omega)
    positivity)
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := h }
  have hp := IsSimpleGroup.prime_card (α := Q)
  rw [hcard, ordL2] at hp
  refine Nat.not_prime_mul (by omega) ?_ hp
  have : 3 ≤ (2 ^ m) ^ 2 - 1 := Nat.le_sub_of_add_le (by omega)
  omega

end Generic

section Proper

variable {G : Type} [Group G] [Finite G] {T M K : Subgroup G}

theorem le_of_mem_cComp_of_le_sup {H₂ K₂ : Subgroup G} (c : Ctx146 T M K)
    (hH₂ : H₂ ≤ K ⊔ T) (hK₂ : K₂ ∈ cComp H₂) : K₂ ≤ K := by
  have hT2 : IsPGroup 2 T := c.sylow.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : Group.IsSolvable ↥T := by
    have := hT2.isNilpotent
    infer_instance
  have hKnorm : ((K.subgroupOf (K ⊔ T))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer c.norm)
  have h1 : perfectCore (K ⊔ T) ≤ K :=
    perfectCore_le_of_sup_solvable le_sup_left hKnorm rfl hTs
  exact (le_perfectCore_of_perfect (le_of_mem_cComp hK₂ |>.trans hH₂)
    (perfect_of_mem_cComp hK₂)).trans h1

theorem pCoreOf_le_kerIn {H₂ : Subgroup G} (c : Ctx146 T M K) (hsyl : IsSylowTwoOf T H₂) :
    pCoreOf 2 H₂ ≤ kerIn (H₂ ⊓ M) H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_kerIn_of_le_normalizer (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H₂)
    ((pCoreOf_two_le_of_isSylowTwoOf hsyl).trans c.le_M)) ?_
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₂

end Proper

end CFSG.Quasithin.GoldS146R
