module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Shape2214 (X : Type) [Group X] (n : ℕ) : Prop :=
  IsL2 X n ∨ IsSz X n ∨ IsSp4 X n ∨ IsU3 X n

@[expose] def S21_21Used (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, Hyp2120 D c → ∀ p ∈ D.sig,
    ∃ n : ℕ, IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ ∀ r ∈ piSet c.B, r ∣ 2 ^ n - 1

theorem uc22p2214_eq_of_isPowTwo {p n n' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : IsPowTwo n)
    (hn' : IsPowTwo n') (h : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (h' : (2 : ℤ) ^ n' ≡ -1 [ZMOD (p : ℤ)]) :
    n = n' := by
  have key : ∀ {a b : ℕ}, a < b → (2 : ℤ) ^ (2 ^ a) ≡ -1 [ZMOD (p : ℤ)] →
      ¬ (2 : ℤ) ^ (2 ^ b) ≡ -1 [ZMOD (p : ℤ)] := by
    intro a b hab ha hb
    have e : 2 ^ b = 2 ^ a * (2 * 2 ^ (b - a - 1)) := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    have h1 : (2 : ℤ) ^ (2 ^ b) ≡ 1 [ZMOD (p : ℤ)] := by
      rw [e, pow_mul, pow_mul]
      have h2 := (ha.pow 2).pow (2 ^ (b - a - 1))
      simpa using h2
    have h3 : (-1 : ℤ) ≡ 1 [ZMOD (p : ℤ)] := hb.symm.trans h1
    have h4 : (p : ℤ) ∣ 2 := by
      have := Int.ModEq.dvd h3
      simpa using this
    have h5 : p ∣ 2 := by exact_mod_cast h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h5)
  obtain ⟨a, rfl⟩ := hn
  obtain ⟨b, rfl⟩ := hn'
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact absurd h' (key hab h)
  · rfl
  · exact absurd h (key hab h')

theorem uc22p2214_clause4 (D : Data G) (Ch : Choice2011 G) (h2121 : S21_21Used D Ch) (h1930 : H1930 D)
    (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) {n : ℕ}
    (hH : Hyp2120 D { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl }) (hpow : IsPowTwo n)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : c.n ≤ n := by
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  obtain ⟨n', hpow', hpn', hrB⟩ :=
    h2121 h1930 { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } hH p hp
  have hnn : n = n' := uc22p2214_eq_of_isPowTwo hpP hp2 hpow hpow' hpn hpn'
  subst hnn
  rcases Nat.eq_zero_or_pos c.n with h0 | hpos
  · omega
  have hdvd : c.n ∣ n := by
    refine uc22p22i_dvd_of_forall_prime hpos fun r hr hrm => hrB r ?_
    show r ∈ piSet c.B0
    rw [c.hpi]
    exact ⟨hr, hrm⟩
  have hn1 : 0 < n := by
    obtain ⟨k, rfl⟩ := hpow
    exact Nat.two_pow_pos k
  exact Nat.le_of_dvd hn1 hdvd

@[expose] def J1NotL2Sz : Prop :=
  ∀ (X : Type) [Group X], IsJ1 X → (∀ n : ℕ, ¬ IsL2 X n) ∧ (∀ n : ℕ, ¬ IsSz X n)

theorem uc22p2214_ncard_eq_one_of_eq {M K : Subgroup G} (h : K = conjClosure M K) :
    (conjSetOf M K).ncard = 1 := by
  have hsub : conjSetOf M K = {K} := by
    ext K'
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
        conv_rhs => rw [h]
        exact le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) _ ⟨g, hg, rfl⟩ le_rfl
      exact Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    · rintro rfl
      exact ⟨1, M.one_mem, by ext x; simp⟩
  rw [hsub, Set.ncard_singleton]

theorem uc22p2214_equiv_bar2_of_center {D : Data G} {Ch : Choice2011 G} (c : Ctx22b D Ch) {K : Subgroup G}
    (hKC : K ∈ calC D.M) (hq : CFSG.Open.IsQuasisimple ↥(mbarImage D.M c.V K))
    (hZ : Subgroup.center ↥(mbarImage D.M c.V K) = ⊥) (hZ2 : Subgroup.center (Bar2 K) = ⊥) :
    Nonempty (Bar2 K ≃* ↥(mbarImage D.M c.V K)) := by
  obtain ⟨⟨e⟩, -⟩ := uc22p22a_data D c hKC hq
  obtain ⟨e1⟩ := uc22p21k_quotCenter_equiv hZ2
  obtain ⟨e2⟩ := uc22p21k_quotCenter_equiv hZ
  exact ⟨(e1.symm.trans e).trans e2⟩

theorem uc22p2214_j1 (D : Data G) (Ch : Choice2011 G) (h17 : S21_17 D Ch) (hJ : J1NotSp4SU3) (hJL : J1NotL2Sz)
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M)
    (hJK : IsJ1 ↥(mbarImage D.M c.V K)) (hJ1 : uc22p22d_J1Nontrivial) {n : ℕ} (hn : n = 3)
    (hc2 : (conjSetOf D.M K).ncard = 2) : c.n ≤ n := by
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  haveI : Nontrivial ↥(mbarImage D.M c.V K) := hJ1 _ hJK
  have hnt : mbarImage D.M c.V K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hle =>
    hnt ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hle)
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hpc : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  have hq := (uc22br4_isComponentOf_mbarImage D.M c.V K c.hVM hpc hKC hKV).2.2
  have hZ := (hJ _ hJK).1
  rcases h17 h1930 c.toCtx22.toCtx21 K hKC with h1 | ⟨-, k, -, hL | hS⟩ | ⟨-, -, hc, -⟩
  · rw [uc22p2214_ncard_eq_one_of_eq h1] at hc2
    exact absurd hc2 (by norm_num)
  · haveI : IsSimpleGroup (Bar2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL
    obtain ⟨e⟩ := uc22p2214_equiv_bar2_of_center c hKC hq hZ (uc22p22g_center_bot hL)
    exact absurd (CFSG.Blueprint.LieModel.of_mulEquiv e hL) ((hJL _ hJK).1 k)
  · haveI : IsSimpleGroup (Bar2 K) := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS
    have hZ2 : Subgroup.center (Bar2 K) = ⊥ := uc22p21k_center_eq_bot hKC.2.2
    obtain ⟨e⟩ := uc22p2214_equiv_bar2_of_center c hKC hq hZ hZ2
    exact absurd (CFSG.Blueprint.LieModel.of_mulEquiv e hS) ((hJL _ hJK).2 k)
  · rw [hn]
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
