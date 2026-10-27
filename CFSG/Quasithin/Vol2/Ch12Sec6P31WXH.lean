module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXGP
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXMult
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXLieL2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WInp2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXD

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def L2Multiplier : Prop :=
  ∀ {X : Type} [Group X] [Finite X], CFSG.IsQuasisimple X → ∀ m : ℕ, 3 ≤ m →
    IsPSL 2 2 m (X ⧸ Subgroup.center X) → Subgroup.center X = ⊥

@[expose] def L1StarFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K →
        star H (Li L F.V1) = Subgroup.closure {x | x ∈ star H (Li L F.V1) ∧ x ^ 3 = 1} ∧
        ∃ r ∈ star H (T ⊓ L), ∃ S : Subgroup (HStar H), S ≤ star H (Li L F.V1) ∧
          IsElemAbelian 3 S ∧ Nat.card S = 9 ∧
          ∀ s ∈ S, r * s * r⁻¹ * s ∈ pCoreOf 2 (star H (Li L F.V1))


theorem l2Multiplier_holds :
    L2Multiplier :=
  fun hq m hm h => center_eq_bot_of_isPSL_two_even hq hm h

section Y

variable {Y : Type} [Group Y]

theorem zpowers_le_centralizer {x y : Y} (h : Commute x y) :
    Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers y : Set Y) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  rintro b ⟨l, rfl⟩
  exact ((h.zpow_right l).eq).symm

theorem threeRankLE2_of_noThree
    (h : ∀ {A B C : Subgroup Y}, Nat.card A = 3 → Nat.card B = 3 → Nat.card C = 3 →
      A ≤ Subgroup.centralizer (B : Set Y) → A ≤ Subgroup.centralizer (C : Set Y) →
      B ≤ Subgroup.centralizer (C : Set Y) → A ⊓ B = ⊥ → (A ⊔ B) ⊓ C = ⊥ → False) :
    P31D.ThreeRankLE2 Y := by
  intro x y z hx hy hz hxy hxz hyz hind
  have hx1 : x ≠ 1 := fun h1 => by
    have := (hind 1 0 0 (by simp [h1])).1
    omega
  have hy1 : y ≠ 1 := fun h1 => by
    have := (hind 0 1 0 (by simp [h1])).2.1
    omega
  have hz1 : z ≠ 1 := fun h1 => by
    have := (hind 0 0 1 (by simp [h1])).2.2
    omega
  have hxo : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hyo : orderOf y = 3 := orderOf_eq_prime hy hy1
  have hzo : orderOf z = 3 := orderOf_eq_prime hz hz1
  have hred : ∀ {w : Y}, w ^ 3 = 1 → ∀ i : ℤ, ∃ k : ℕ, w ^ i = w ^ k := by
    intro w hw i
    refine ⟨(i % 3).toNat, ?_⟩
    have h3 : (w ^ (3 : ℤ)) = 1 := by exact_mod_cast hw
    have hi : i = 3 * (i / 3) + i % 3 := by omega
    have hnn : 0 ≤ i % 3 := by omega
    calc w ^ i = w ^ (3 * (i / 3) + i % 3) := by rw [← hi]
      _ = (w ^ (3 : ℤ)) ^ (i / 3) * w ^ (i % 3) := by rw [zpow_add, zpow_mul]
      _ = w ^ (i % 3) := by rw [h3, one_zpow, one_mul]
      _ = w ^ (i % 3).toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  have hinv : ∀ {w : Y}, w ^ 3 = 1 → ∀ k : ℕ, (w ^ k)⁻¹ = w ^ (2 * k) := by
    intro w hw k
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    have : k + 2 * k = 3 * k := by ring
    rw [this, pow_mul, hw, one_pow]
  refine h (A := Subgroup.zpowers x) (B := Subgroup.zpowers y) (C := Subgroup.zpowers z)
    (by rw [Nat.card_zpowers, hxo]) (by rw [Nat.card_zpowers, hyo])
    (by rw [Nat.card_zpowers, hzo]) (zpowers_le_centralizer hxy) (zpowers_le_centralizer hxz)
    (zpowers_le_centralizer hyz) ?_ ?_
  ·
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hw
    have hi : x ^ i = w := hi
    have hj : y ^ j = w := hj
    obtain ⟨i', hi'⟩ := hred hx i
    obtain ⟨j', hj'⟩ := hred hy j
    rw [Subgroup.mem_bot]
    have hxi : x ^ i' = w := by rw [← hi', hi]
    have hyj : y ^ j' = w := by rw [← hj', hj]
    have h1 : x ^ i' * y ^ (2 * j') * z ^ 0 = 1 := by
      rw [← hinv hy j', hyj, hxi, pow_zero, mul_one, mul_inv_cancel]
    obtain ⟨hi3, -, -⟩ := hind _ _ _ h1
    rw [← hxi]
    obtain ⟨t, ht⟩ := hi3
    rw [ht, pow_mul, hx, one_pow]
  ·
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, ⟨k, hk⟩⟩ := hw
    have hk : z ^ k = w := hk
    obtain ⟨a, ⟨i, ha⟩, b, ⟨j, hb⟩, hab⟩ := exists_decomp (zpowers_le_centralizer hxy |> fun hc a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (hc ha) b hb |>.symm) hw1
    have ha : x ^ i = a := ha
    have hb : y ^ j = b := hb
    obtain ⟨i', hi'⟩ := hred hx i
    obtain ⟨j', hj'⟩ := hred hy j
    obtain ⟨k', hk'⟩ := hred hz k
    rw [Subgroup.mem_bot]
    have hxa : x ^ i' = a := by rw [← hi', ha]
    have hyb : y ^ j' = b := by rw [← hj', hb]
    have hzw : z ^ k' = w := by rw [← hk', hk]
    have h1 : x ^ i' * y ^ j' * z ^ (2 * k') = 1 := by
      rw [← hinv hz k', hzw, hxa, hyb, hab, mul_inv_cancel]
    obtain ⟨hi3, hj3, -⟩ := hind _ _ _ h1
    have hxi : x ^ i' = 1 := by obtain ⟨t, ht⟩ := hi3; rw [ht, pow_mul, hx, one_pow]
    have hyj : y ^ j' = 1 := by obtain ⟨t, ht⟩ := hj3; rw [ht, pow_mul, hy, one_pow]
    rw [← hab, ← hxa, ← hyb, hxi, hyj, one_mul]


end Y

theorem isQuasisimple_of_quot_isPSL {X : Type} [Group X] [Finite X] (hL : L2BorelFacts)
    (hperf : Group.IsPerfect X) {m : ℕ} (hm : 2 ≤ m) (h : IsPSL 2 2 m (X ⧸ Subgroup.center X)) :
    CFSG.IsQuasisimple X := by
  haveI hs : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m h).2
  have hP : StarProps (⊤ : Subgroup (X ⧸ Subgroup.center X)) :=
    starProps_of_isPSL hL hm (IsPSL.of_mulEquiv Subgroup.topEquiv.symm h)
  refine ⟨hperf, hs, ?_⟩
  by_contra hcomm
  push Not at hcomm
  exact hP.nonab fun a b => Subtype.ext (hcomm a b)


section GLevel

variable {G : Type} [Group G] [Finite G] {T L V V₁ Vp H K : Subgroup G}

theorem noL2PairF_w31_of (hL : L2BorelFacts) (hM : L2Multiplier) (h1222 : Stmt12_2_2)
    (h1228 : Stmt12_2_8) (hF : L1StarFacts) (hNP : NoPermL_w31) : NoL2PairF_w31 := by
  intro h1229 G _ _ T L V _ F hH hZ H K hIs h918 hK m hm2 hX
  by_contra hm
  have hm3 : 3 ≤ m := by omega
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hsylT := isSylowTwoOf_T h
  have hsylTs := isSylowTwoOf_star hsylT
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hsylT
  have hQM : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) := hQT.trans hH.hyp.normalizes
  obtain ⟨t₀, ht₀, ht₀K⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hall
    push Not at hall
    exact hK (le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.1 (hall t ht) k).1 hk) (le_conjClosure K T))
  have hperf : Group.IsPerfect ↥(star H K) :=
    Group.isPerfect_def.mpr (S126P31.commutator_eq_top_of_perfect
      (perfect_of_mem_cComp (L1233.star_mem_cComp h918.K_cComp)))
  have hq : CFSG.IsQuasisimple ↥(star H K) := isQuasisimple_of_quot_isPSL hL hperf (by omega) hX
  have hZ1 : Subgroup.center ↥(star H K) = ⊥ := hM hq m hm3 hX
  have hX₁ : IsPSL 2 2 m ↥(star H K) :=
    IsPSL.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot) hX
  have hP : StarProps (star H K) := starProps_of_isPSL hL (by omega) hX₁
  have hX₂ : IsPSL 2 2 m ↥(star H (conjSub t₀ K)) :=
    IsPSL.of_mulEquiv (starConjEquiv (hTH ht₀)).symm hX₁
  obtain ⟨hcomm, hinf⟩ := commute_pair_gen h918 hP ht₀ ht₀K
  have hsup := star_conjClosure_eq_sup_gen hH h918 hP ht₀ ht₀K
  have hK0n : (star H (conjClosure K T)).Normal := normal_star h918.K₀_normal
  have hK0n' : (star H K ⊔ star H (conjSub t₀ K)).Normal := hsup ▸ hK0n
  have hTsN : star H T ≤ Subgroup.normalizer (star H (conjClosure K T) : Set (HStar H)) :=
    Subgroup.le_normalizer_of_normal
  have hSs : IsSylowTwoOf (star H T ⊓ star H (conjClosure K T)) (star H (conjClosure K T)) :=
    A4.isSylowTwoOf_inf_normal hsylTs le_top Subgroup.le_normalizer_of_normal
  have hBM : borel (star H (conjClosure K T)) (star H T) ≤
      star H (Subgroup.normalizer (L : Set G) ⊓ H) :=
    le_sup_right.trans (le_star_M h1229 F hH hZ hTH (pCoreOf_ne_bot h) le_sup_left
      (isSolvable_sup_borel hsylTs.2.1 hTsN hSs))
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
  obtain ⟨hLgen, r, hr, S, hSL, hSe, hS9, hSinv⟩ := hF G T L V F hH hZ H K hIs h918
  have hD : PermData (star H T) (star H (Subgroup.normalizer (L : Set G) ⊓ H)) (star H (T ⊓ L)) := by
    refine permData_of_pair (X₁ := star H K) (X₂ := star H (conjSub t₀ K)) hL hm3 ⟨?_, hsylTs, hX₁,
      hX₂, hcomm, hinf, hK0n', ⟨QuotientGroup.mk ⟨t₀, hTH ht₀⟩, mk_mem_star ht₀,
        (L1233.star_conjSub (hTH ht₀)).symm⟩, star_mono (le_inf hH.hyp.normalizes hTH),
      by rw [← hsup]; exact hBM,
      not_le_star_M hKH hQM hIs.2.1, ?_, star_mono (le_inf
        (F126.L1_le_L.trans Subgroup.le_normalizer) hL1H), hLgen, star_mono inf_le_left,
      ⟨r, hr, S, hSL, hSe, hS9, hSinv⟩⟩
    · exact threeRankLE2_of_noThree fun hA hB hC hAB hAC hBC hi hi' =>
        S126P31.false_of_three hH (pCoreOf_ne_bot h) hA hB hC hAB hAC hBC hi hi'
    · intro hd
      exact not_27_dvd_card_normalizer h1222 h1228 F hH
        (hd.trans ((Dvd.intro _ (F126.card_star
          (inf_le_right : Subgroup.normalizer (L : Set G) ⊓ H ≤ H))).trans
          (Subgroup.card_dvd_of_le inf_le_left)))
  exact permData_absurd hNP T L V F hH hZ hTH hQT hD

end GLevel


theorem noL2PairF_w31_holds
    (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (hF : L1StarFacts)
    (hNP : NoPermL_w31) : NoL2PairF_w31 :=
  noL2PairF_w31_of l2BorelFacts_holds l2Multiplier_holds h1222 h1228 hF hNP

end CFSG.Quasithin.H13.P31X
