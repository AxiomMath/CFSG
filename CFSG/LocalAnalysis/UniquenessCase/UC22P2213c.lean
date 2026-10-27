module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
public import Certificates.Certificate113
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.StatedPSLTwo
public import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213c_literal {X : Type} [Group X] {p m : ℕ} {P : Prop}
    (h : (¬ IsSz X m ∧ (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz X m ∧ (2 : ℤ) ^ (2 * m) ≡ -1 [ZMOD (p : ℤ)])) :
    P ∨ (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)] ∨ (IsSz X m ∧ (2 : ℤ) ^ (2 * m) ≡ -1 [ZMOD (p : ℤ)]) :=
  h.elim (fun h => Or.inr (Or.inl h.2)) (fun h => Or.inr (Or.inr h))

theorem uc22p2213c_bar2_equiv (D : Data G) {Ch : Choice2011 G} (hV : S22_V D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    [IsSimpleGroup (Bar2 K)] (hKV : ¬ K ≤ centralizer (c.V : Set G)) :
    Nonempty (Bar2 K ≃* ↥(mbarImage D.M c.V K)) := by
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
  set φ := uc22br4_phi D.M c.V K hKM with hφ
  have hle : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro x hx
    rw [hφ, uc22br4_ker_phi D.M c.V K c.hVM hKM, Subgroup.mem_subgroupOf]
    exact uc22p22f_pCoreOf_le_cent hV h1930 c
      (uc22p22r_pCoreOf_le_of_isSubnormal hK.1 ⟨x, hx, rfl⟩)
  set ψ₀ : Bar2 K →* MBar D.M c.V := QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hle with hψ₀
  have hmem : ∀ z, ψ₀ z ∈ mbarImage D.M c.V K := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hψ₀, QuotientGroup.lift_mk, ← uc22br4_range_phi D.M c.V K hKM]
    exact ⟨k, rfl⟩
  set ψ := ψ₀.codRestrict _ hmem with hψ
  have hs : Function.Surjective ψ := by
    intro z
    obtain ⟨y, hy⟩ := ((uc22br4_range_phi D.M c.V K hKM).symm ▸ z.2 :
      (z : MBar D.M c.V) ∈ φ.range)
    exact ⟨QuotientGroup.mk y, Subtype.ext hy⟩
  refine ⟨MulEquiv.ofBijective ψ ⟨?_, hs⟩⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact h
  · refine absurd ?_ hKV
    rw [← uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM, eq_bot_iff]
    intro z hz
    obtain ⟨w, hw'⟩ := hs ⟨z, hz⟩
    have hw : ψ w = 1 := (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top w)
    have h1 : (ψ w : MBar D.M c.V) = z := congrArg Subtype.val hw'
    rw [Subgroup.mem_bot, ← h1, hw, OneMemClass.coe_one]

theorem uc22p2213c_exists_odd {L : Subgroup G} {n : ℕ}
    (hLS : IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) :
    ∃ s : ℕ, Odd s ∧ 1 < s ∧ s ∣ n := by
  rcases hLS with hS | ⟨hL2, hpow⟩
  · have h3 := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hS
    exact ⟨n, CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hS, by omega, dvd_rfl⟩
  · have hn0 : n ≠ 0 := by
      rintro rfl
      have h0 : Nat.card (Bar2 L) = 0 := by rw [uc22p22r_L2_card hL2]; norm_num
      exact Nat.card_pos.ne' h0
    obtain ⟨k, m, hmo, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0
    refine ⟨m, hmo, ?_, Dvd.intro_left _ rfl⟩
    by_contra h1
    have hm1 : m = 1 := by have := hmo.pos; omega
    exact hpow ⟨k, by rw [hm1, mul_one]⟩

theorem uc22p2213c_witness (D : Data G) (Ch : Choice2011 G)
    (h15 : S21_15C D Ch) (h117 : R117W D) (hV : S22_V D Ch) (h1930 : H1930 D)
    (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hn2 : 2 < n)
    (hLS : IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) :
    ∃ m : ℕ, ((¬ IsSz ↥(mbarImage D.M c.V L) m ∧ (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz ↥(mbarImage D.M c.V L) m ∧ (2 : ℤ) ^ (2 * m) ≡ -1 [ZMOD (p : ℤ)])) ∧
      K2213 D c p L m := by
  have hKV := uc22p2213a_not_le_centralizer D Ch h117 hV h1930 c hL hc2
  rcases h15 h1930 c.toCtx21 L hL hc2 n hLS p hp with ⟨hL2, hcong⟩ | ⟨hSz, hcong⟩
  · haveI : IsSimpleGroup (Bar2 L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
    obtain ⟨e⟩ := uc22p2213c_bar2_equiv D hV h1930 c hL hKV
    have hL2' : IsL2 ↥(mbarImage D.M c.V L) n := CFSG.Blueprint.LieModel.of_mulEquiv e hL2
    have hst : (¬ IsSz ↥(mbarImage D.M c.V L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz ↥(mbarImage D.M c.V L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]) :=
      Or.inl ⟨fun hS => uc22p22g_isSz_isL2_false hS hL2', hcong⟩
    exact ⟨n, hst, hL, uc22p2213c_literal hst,
      Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨hn2, Or.inl hL2'⟩, hc2⟩))⟩
  · haveI : IsSimpleGroup (Bar2 L) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    obtain ⟨e⟩ := uc22p2213c_bar2_equiv D hV h1930 c hL hKV
    have hSz' : IsSz ↥(mbarImage D.M c.V L) n := CFSG.Blueprint.LieModel.of_mulEquiv e hSz
    have hst : (¬ IsSz ↥(mbarImage D.M c.V L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz ↥(mbarImage D.M c.V L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]) :=
      Or.inr ⟨hSz', hcong⟩
    exact ⟨n, hst, hL, uc22p2213c_literal hst,
      Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨hn2, Or.inr hSz'⟩, hc2⟩))⟩

theorem uc22p2213c_of_not_normal (D : Data G) (Ch : Choice2011 G)
    (h17 : S21_17 D Ch) (h15 : S21_15C D Ch) (h117 : R117W D) (hV : S22_V D Ch)
    (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx22b D Ch) {p : ℕ}
    (hp : p ∈ D.sig) {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) :
    (∃ m : ℕ, ((¬ IsSz ↥(mbarImage D.M c.V L) m ∧ (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz ↥(mbarImage D.M c.V L) m ∧ (2 : ℤ) ^ (2 * m) ≡ -1 [ZMOD (p : ℤ)])) ∧
      K2213 D c p L m) ∨
    ((conjSetOf D.M L).ncard = 2 ∧ ∃ n : ℕ, 2 < n ∧ IsL2 (Bar2 L) n ∧ IsPowTwo n) := by
  have hLM : L ≤ D.M := uc22p22a_le_of_isSubnormal hL.1
  have hcl : conjClosure D.M L ≠ L := fun h =>
    hnN (uc22p21j_normal_of_conjClosure_eq hLM h.symm)
  rcases h17 h1930 c.toCtx21 L hL with h1 | ⟨hc2, n, hn2, hL2 | hSz⟩ | ⟨-, -, -, -, he3, -⟩
  · exact absurd h1.symm hcl
  · by_cases hpow : IsPowTwo n
    · exact Or.inr ⟨hc2, n, hn2, hL2, hpow⟩
    · exact Or.inl
        (uc22p2213c_witness D Ch h15 h117 hV h1930 c hp hL hc2 hn2 (Or.inr ⟨hL2, hpow⟩))
  · exact Or.inl (uc22p2213c_witness D Ch h15 h117 hV h1930 c hp hL hc2 hn2 (Or.inl hSz))
  · omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
