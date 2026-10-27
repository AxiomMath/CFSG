module

public import CFSG.RankThree.SubgroupLists.RootGroupWeights
public import CFSG.RankThree.SubgroupLists.LinearTwoFamily
public import CFSG.RankThree.SubgroupLists.ExtensionField
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.LocalAnalysis.ComponentInitial.LowRankFacts
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Equiv
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem le_two_of_card_sl2_dvd_card_sp4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : p ^ f * ((p ^ f) ^ 2 - 1) ∣ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1))) : f ≤ 2 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp2' : 9 ≤ p ^ 2 := by nlinarith
  have hp4' : 81 ≤ p ^ 4 := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ p ^ 4 := Nat.pow_le_pow_left hp3 4
  have hf4 : f ≤ 4 := by
    have hqd : p ^ f ∣ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := (Dvd.intro _ rfl).trans h
    have hcop : Nat.Coprime (p ^ f) ((p ^ 2 - 1) * (p ^ 4 - 1)) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.mul_right
        (coprime_self_pow_sub_one (by omega) (by norm_num))
        (coprime_self_pow_sub_one (by omega) (by norm_num)))
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hcop.dvd_of_dvd_mul_right hqd)
  by_contra hf2
  interval_cases f
  ·
    have hfac : (p ^ 3) ^ 2 - 1 = (p ^ 2 - 1) * (p ^ 4 + p ^ 2 + 1) := by
      have h1 : 1 ≤ p ^ 2 := by omega
      zify [h1, Nat.one_le_pow 2 (p ^ 3) (by positivity)]
      ring
    rw [hfac, show p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) =
      p ^ 3 * (p ^ 2 - 1) * (p * (p ^ 4 - 1)) by ring,
      show p ^ 3 * ((p ^ 2 - 1) * (p ^ 4 + p ^ 2 + 1)) =
      p ^ 3 * (p ^ 2 - 1) * (p ^ 4 + p ^ 2 + 1) by ring] at h
    have hpos : 0 < p ^ 3 * (p ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
    have h1 := Nat.dvd_of_mul_dvd_mul_left hpos h
    have hcop : Nat.Coprime (p ^ 4 + p ^ 2 + 1) p := by
      apply Nat.coprime_of_dvd
      intro ℓ hℓ hℓm hℓp
      have h2 : ℓ ∣ p ^ 4 + p ^ 2 := Dvd.dvd.add (hℓp.trans (dvd_pow_self p (by norm_num)))
        (hℓp.trans (dvd_pow_self p (by norm_num)))
      have h3 : ℓ ∣ p ^ 4 + p ^ 2 + 1 - (p ^ 4 + p ^ 2) := Nat.dvd_sub hℓm h2
      rw [show p ^ 4 + p ^ 2 + 1 - (p ^ 4 + p ^ 2) = 1 by omega] at h3
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
    have h2 := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_left h1)
    omega
  ·
    have hfac : (p ^ 4) ^ 2 - 1 = (p ^ 4 - 1) * (p ^ 4 + 1) := by
      have h1 : 1 ≤ p ^ 4 := by omega
      zify [h1, Nat.one_le_pow 2 (p ^ 4) (by positivity)]
      ring
    rw [hfac, show p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) =
      p ^ 4 * (p ^ 4 - 1) * (p ^ 2 - 1) by ring,
      show p ^ 4 * ((p ^ 4 - 1) * (p ^ 4 + 1)) = p ^ 4 * (p ^ 4 - 1) * (p ^ 4 + 1) by ring] at h
    have hpos : 0 < p ^ 4 * (p ^ 4 - 1) := Nat.mul_pos (by positivity) (by omega)
    have h1 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mul_dvd_mul_left hpos h)
    have : p ^ 2 ≤ p ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

theorem card_statedSp_two_zmod {p : ℕ} [Fact p.Prime] :
    Nat.card (StatedSp 2 (ZMod p)) = p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem not_isPerfect_sl2_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    ¬ Group.IsPerfect SL(2, F) := by
  classical
  intro hperf
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
  set e := sl2CongrRingEquiv (FiniteField.ringEquivOfCardEq hcard)
  have : Group.IsPerfect SL(2, ZMod 3) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom)
    e.surjective
  set N := CFSG.ClassicalInvolution.sl2ThreeQ
  have := CFSG.ClassicalInvolution.sl2ThreeQ_normal
  have hc : Nat.card (SL(2, ZMod 3) ⧸ N) = 3 := by
    have := CFSG.ClassicalInvolution.sl2ThreeQ_index
    rw [Subgroup.index] at this
    exact this
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : IsCyclic (SL(2, ZMod 3) ⧸ N) := isCyclic_of_prime_card hc
  have : IsMulCommutative (SL(2, ZMod 3) ⧸ N) := ⟨⟨fun a b => by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := SL(2, ZMod 3) ⧸ N)
    obtain ⟨i, rfl⟩ := hg a
    obtain ⟨j, rfl⟩ := hg b
    rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm]⟩⟩
  have hle := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', Group.IsPerfect.commutator_eq_top] at hle
  have htop : N = ⊤ := eq_top_iff.mpr hle
  have := CFSG.ClassicalInvolution.sl2ThreeQ_index
  rw [show CFSG.ClassicalInvolution.sl2ThreeQ = N from rfl, htop, Subgroup.index_top] at this
  omega

@[expose] def rootHomSL2 (F : Type) [Field F] : Multiplicative F →* SL(2, F) where
  toFun b := rootSL2 (Multiplicative.toAdd b)
  map_one' := by rw [toAdd_one, rootSL2_zero]
  map_mul' a b := by rw [toAdd_mul, rootSL2_add]

theorem rootHomSL2_injective {F : Type} [Field F] : Function.Injective (rootHomSL2 F) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hb' : rootSL2 (Multiplicative.toAdd b) = 1 := hb
  have h := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hb'
  simp [rootSL2] at h
  exact h

theorem exists_lift_pow_seven {G : Type*} [Group G]
    (hZ2 : ∀ z ∈ Subgroup.center G, z ^ 2 = 1) (q : G ⧸ Subgroup.center G) (hq : q ^ 7 = 1) :
    ∃ x : G, (x : G ⧸ Subgroup.center G) = q ∧ x ^ 7 = 1 := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hz : x₀ ^ 7 ∈ Subgroup.center G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hq]
  refine ⟨x₀ ^ 8, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, show 8 = 7 + 1 by rfl, pow_succ, hq, one_mul]
  · rw [← pow_mul, show 8 * 7 = 7 * 2 * 4 by rfl, pow_mul, pow_mul, hZ2 _ hz, one_pow]

variable {p : ℕ} [Fact p.Prime]

theorem quasisimple_sp4_of_unique_involution (hp2 : p ≠ 2) {G : Subgroup (GL V₄ (ZMod p))}
    (hGS : G ≤ StatedSp 2 (ZMod p)) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1)
    (hinv : ∀ x ∈ G, x * x = 1 → x = 1 ∨ x = -1) :
    Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, GaloisField p 2)) ∨
      Nonempty (G ≃* SL(2, ZMod 5)) ∨ Nonempty (G ≃* SL(2, GaloisField 3 2)) ∨
      (p = 7 ∧ Nat.card (Subgroup.center G) = 2 ∧
        Nonempty ((G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7))) := by
  classical
  have hp : p.Prime := Fact.out
  have : Group.IsPerfect G := hq.1
  have hnt : Nontrivial G := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have heven : Even (Nat.card G) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact Group.IsPerfect.not_isSolvable G (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hinv' : ∀ x : G, x ^ 2 = 1 → x ≠ 1 → (x : GL V₄ (ZMod p)) = -1 := by
    intro x hx2 hx1
    rcases hinv x x.2 (by rw [← Subgroup.coe_mul, ← sq, hx2, Subgroup.coe_one]) with h | h
    · exact absurd (Subtype.ext h) hx1
    · exact h
  have hnot4 : ¬ CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo G := by
    rintro ⟨E, hE4, hE2⟩
    have : Finite E := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨a, ha⟩ : ∃ a : E, a ≠ 1 := by
      by_contra hall
      push Not at hall
      have : Subsingleton E := ⟨fun x y => (hall x).trans (hall y).symm⟩
      rw [Nat.card_unique] at hE4
      omega
    obtain ⟨b, hb1, hba⟩ : ∃ b : E, b ≠ 1 ∧ b ≠ a := by
      by_contra hall
      push Not at hall
      have hsub : (Set.univ : Set E) ⊆ {1, a} := fun x _ => by
        by_cases hx : x = 1
        · exact Or.inl hx
        · exact Or.inr (hall x hx)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ, Set.ncard_pair ha.symm] at this
      omega
    have h2 : ∀ x : E, ((x : G) : G) ^ 2 = 1 := fun x => by
      have := hE2 x
      rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
    have hne1 : ∀ x : E, x ≠ 1 → (x : G) ≠ 1 := fun x hx h => hx (Subtype.ext h)
    have hab := (hinv' a (h2 a) (hne1 a ha)).trans (hinv' b (h2 b) (hne1 b hb1)).symm
    exact hba (Subtype.ext (Subtype.ext hab)).symm
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  rcases CFSG.BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hnot4 S with
    hcyc | hquat
  · exact absurd hcyc (CFSG.LocalAnalysis.ComponentInitial.perfect_even_sylow_noncyclic heven S)
  have hO : CFSG.oddCore G = ⊥ := by
    apply sSup_eq_bot.mpr
    rintro N ⟨hN, hNodd⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with h | h
    · exfalso
      rw [h, Subgroup.card_top] at hNodd
      exact (Nat.not_even_iff_odd.mpr hNodd) heven
    · rw [eq_bot_iff]
      intro x hx
      rcases hZ x (h hx) with h1 | hm1
      · exact Subgroup.mem_bot.mpr (Subtype.ext h1)
      · exfalso
        have hx2 : (⟨x, hx⟩ : N) ^ 2 = 1 := Subtype.ext (Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_pow, hm1, neg_one_sq, Subgroup.coe_one,
            Subgroup.coe_one]))
        have hx1 : (⟨x, hx⟩ : N) ≠ 1 := fun h0 => by
          have h1 := congrArg (fun y : N => ((y : G) : GL V₄ (ZMod p))) h0
          simp only [Subgroup.coe_one] at h1
          rw [hm1] at h1
          have h2 : (2 : ZMod p) = 0 := by
            have := congrArg (fun g : GL V₄ (ZMod p) =>
              (g : Matrix V₄ V₄ (ZMod p)) (Sum.inl 0) (Sum.inl 0)) h1
            simp at this
            linear_combination -this
          have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
        have hord : orderOf (⟨x, hx⟩ : N) = 2 := orderOf_eq_prime hx2 hx1
        have := orderOf_dvd_natCard (⟨x, hx⟩ : N)
        rw [hord] at this
        exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr this)
  have hperf' : commutator (G ⧸ CFSG.oddCore G) = ⊤ := by
    have : Group.IsPerfect (G ⧸ CFSG.oddCore G) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.commutator_eq_top
  set eO : G ⧸ CFSG.oddCore G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot with heO
  rcases CFSG.ClassicalInvolution.quaternion_sylow_structure_of_perfect S hquat hperf' with
    ⟨F, _, _, hFchar, ⟨e⟩⟩ | ⟨hqY, hZY, ⟨eA⟩⟩
  ·
    have : Fintype F := Fintype.ofFinite F
    set e' : G ≃* SL(2, F) := eO.symm.trans e with he'
    set r := ringChar F with hr
    obtain ⟨f, hrprime, hcardF⟩ := FiniteField.card F r
    have : Fact r.Prime := ⟨hrprime⟩
    have hr2 : r ≠ 2 := hFchar
    have hNF : Nat.card F = r ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcardF]
    have hperfF : Group.IsPerfect SL(2, F) :=
      Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
    by_cases hrp : r = p
    ·
      have hdvd : Nat.card SL(2, F) ∣ Nat.card (StatedSp 2 (ZMod p)) := by
        rw [← Nat.card_congr e'.toEquiv]
        exact Subgroup.card_dvd_of_le hGS
      rw [card_sl2_field, card_statedSp_two_zmod, hNF, hrp] at hdvd
      have hf2 := le_two_of_card_sl2_dvd_card_sp4 hp hp2 f.pos hdvd
      have hfpos := f.pos
      rcases (by omega : (f : ℕ) = 1 ∨ (f : ℕ) = 2) with hf | hf
      · left
        have hc : Fintype.card F = Fintype.card (ZMod p) := by rw [hcardF, hf, hrp, ZMod.card,
          pow_one]
        exact ⟨e'.trans (sl2CongrRingEquiv (FiniteField.ringEquivOfCardEq hc))⟩
      · right; left
        have : Fintype (GaloisField p 2) := Fintype.ofFinite _
        have hc : Fintype.card F = Fintype.card (GaloisField p 2) := by
          rw [hcardF, hf, hrp, ← Nat.card_eq_fintype_card, GaloisField.card p 2 (by norm_num)]
        exact ⟨e'.trans (sl2CongrRingEquiv (FiniteField.ringEquivOfCardEq hc))⟩
    ·
      have hrK : (r : ZMod p) ≠ 0 := by
        intro h
        have := (ZMod.natCast_eq_zero_iff r p).mp h
        exact hrp ((Nat.prime_dvd_prime_iff_eq hp hrprime).mp this).symm
      set u : Multiplicative F →* GL V₄ (ZMod p) :=
        G.subtype.comp (e'.symm.toMonoidHom.comp (rootHomSL2 F)) with hu
      have huinj : Function.Injective u := by
        intro a b hab
        exact rootHomSL2_injective (e'.symm.injective (Subtype.ext hab))
      have ht : ∀ a : Fˣ, ∃ t : GL V₄ (ZMod p), ∀ b : F,
          t * u (Multiplicative.ofAdd b) * t⁻¹ = u (Multiplicative.ofAdd ((a : F) ^ 2 * b)) := by
        intro a
        refine ⟨((e'.symm (torusSL2 a) : G) : GL V₄ (ZMod p)), fun b => ?_⟩
        simp only [hu, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          Subgroup.coe_subtype, rootHomSL2, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
        rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul,
          ← map_mul, torusSL2_conj_rootSL2, mul_inv_cancel_right]
      have hbound := card_sub_one_le_of_root_group hrK u huinj ht
      rw [Fintype.card_sum, Fintype.card_fin, hcardF] at hbound
      have hq9 : r ^ (f : ℕ) ≤ 9 := by omega
      have hr3 : 3 ≤ r := by have := hrprime.two_le; omega
      have hrf : r ≤ r ^ (f : ℕ) := Nat.le_self_pow f.ne_zero r
      have hf2 : (f : ℕ) ≤ 2 := by
        by_contra h
        have : 3 ^ 3 ≤ r ^ (f : ℕ) := (Nat.pow_le_pow_left hr3 _).trans' (Nat.pow_le_pow_right
          (by norm_num) (by omega))
        omega
      have hcases : (r = 3 ∧ (f : ℕ) = 1) ∨ (r = 3 ∧ (f : ℕ) = 2) ∨ (r = 5 ∧ (f : ℕ) = 1) ∨
          (r = 7 ∧ (f : ℕ) = 1) := by
        have hr9 : r ≤ 9 := hrf.trans hq9
        have hfpos := f.pos
        have hf1 : ∀ s : ℕ, 5 ≤ s → s ^ (f : ℕ) ≤ 9 → (f : ℕ) = 1 := by
          intro s hs h9
          by_contra h
          have : s ^ 2 ≤ s ^ (f : ℕ) := Nat.pow_le_pow_right (by omega) (by omega)
          nlinarith
        interval_cases r
        · rcases (by omega : (f : ℕ) = 1 ∨ (f : ℕ) = 2) with h | h
          · exact Or.inl ⟨rfl, h⟩
          · exact Or.inr (Or.inl ⟨rfl, h⟩)
        · exact absurd hrprime (by norm_num)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, hf1 5 le_rfl hq9⟩))
        · exact absurd hrprime (by norm_num)
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, hf1 7 (by norm_num) hq9⟩))
        · exact absurd hrprime (by norm_num)
        · exact absurd hrprime (by norm_num)
      rcases hcases with ⟨hr3', hf1⟩ | ⟨hr3', hf2'⟩ | ⟨hr5, hf1⟩ | ⟨hr7, hf1⟩
      ·
        exact absurd hperfF (not_isPerfect_sl2_three (by rw [hNF, hr3', hf1]; norm_num))
      ·
        right; right; right; left
        have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
        have hc : Fintype.card F = Fintype.card (GaloisField 3 2) := by
          rw [hcardF, hr3', hf2', ← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
        exact ⟨e'.trans (sl2CongrRingEquiv (FiniteField.ringEquivOfCardEq hc))⟩
      ·
        right; right; left
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        have hc : Fintype.card F = Fintype.card (ZMod 5) := by
          rw [hcardF, hr5, hf1, ZMod.card, pow_one]
        exact ⟨e'.trans (sl2CongrRingEquiv (FiniteField.ringEquivOfCardEq hc))⟩
      ·
        exfalso
        have hchar7 : CharP F 7 := hr7 ▸ ringChar.charP F
        have h7F : (7 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 7
        have h3F : (3 : F) ≠ 0 := by
          intro h
          have : (1 : F) = 0 := by linear_combination 5 * h - 2 * h7F
          exact one_ne_zero this
        set x := u (Multiplicative.ofAdd 1) with hx
        have hx7 : x ^ 7 = 1 := by
          rw [hx, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
          rw [show ((7 : ℕ) : F) = 0 by exact_mod_cast h7F, ofAdd_zero, map_one]
        have hx1 : x ≠ 1 := fun h => by
          have := huinj (h.trans (map_one u).symm)
          exact one_ne_zero (congrArg Multiplicative.toAdd this)
        obtain ⟨t, htb⟩ := ht (Units.mk0 3 h3F)
        have hconj : IsConj x (x ^ 2) := by
          refine isConj_iff.mpr ⟨t, ?_⟩
          rw [hx, htb, Units.val_mk0, ← map_pow, ← ofAdd_nsmul]
          congr 2
          rw [nsmul_eq_mul, mul_one]
          push_cast
          linear_combination h7F
        have hxSp : x ∈ StatedSp 2 (ZMod p) := hGS (e'.symm _).2
        have h7p : (7 : ZMod p) ≠ 0 := by
          have h' := hrK
          rw [hr7] at h'
          exact_mod_cast h'
        exact false_of_isConj_sq_of_pow_seven h7p hxSp hx7 hx1 hconj
  ·
    set Y := G ⧸ CFSG.oddCore G
    have hZG : Nat.card (Subgroup.center G) = 2 :=
      (Nat.card_congr (Subgroup.centerCongr eO.symm).toEquiv).trans hZY
    set θ : (G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7) :=
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center Y) eO.symm
        (Subgroup.map_center_eq eO.symm)).trans eA with hθ
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, hZG, ⟨θ⟩⟩)))
    set c : alternatingGroup (Fin 7) := ⟨finRotate 7, Equiv.Perm.mem_alternatingGroup.mpr
      (by decide)⟩ with hc
    set h : alternatingGroup (Fin 7) := ⟨swap 1 2 * swap 2 4 * swap 3 6 * swap 6 5,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ with hh
    have hc7 : c ^ 7 = 1 := Subtype.ext (by decide)
    have hc1 : c ≠ 1 := fun h0 => by
      have := congrArg Subtype.val h0
      revert this
      decide
    have hhc : h * c * h⁻¹ = c ^ 2 := Subtype.ext (by decide)
    have hZ2 : ∀ z ∈ Subgroup.center G, z ^ 2 = 1 := by
      intro z hz
      have h1 : (⟨z, hz⟩ : Subgroup.center G) ^ Nat.card (Subgroup.center G) = 1 :=
        pow_card_eq_one'
      rw [hZG] at h1
      exact congrArg Subtype.val h1
    obtain ⟨x, hxc, hx7⟩ := exists_lift_pow_seven hZ2 (θ.symm c)
      (by rw [← map_pow, hc7, map_one])
    obtain ⟨hl, hhl⟩ := QuotientGroup.mk_surjective (θ.symm h)
    have hconjG : hl * x * hl⁻¹ = x ^ 2 := by
      set y := hl * x * hl⁻¹ with hy
      have hy7 : y ^ 7 = 1 := by rw [hy, conj_pow, hx7, mul_one, mul_inv_cancel]
      have hz : (x ^ 2)⁻¹ * y ∈ Subgroup.center G := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_pow, hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, hhl, hxc, ← map_inv, ← map_mul, ← map_mul, hhc, ← map_pow,
          inv_mul_cancel]
      set z := (x ^ 2)⁻¹ * y with hzdef
      have hyz : y = x ^ 2 * z := by rw [hzdef]; group
      have hzc : ∀ g : G, g * z = z * g := Subgroup.mem_center_iff.mp hz
      have hz7 : z ^ 7 = 1 := by
        have h1 : y ^ 7 = (x ^ 2) ^ 7 * z ^ 7 := by
          rw [hyz]
          exact (show Commute (x ^ 2) z from hzc (x ^ 2)).mul_pow 7
        rw [hy7, ← pow_mul, show 2 * 7 = 7 * 2 by rfl, pow_mul, hx7, one_pow, one_mul] at h1
        exact h1.symm
      have hz1 : z = 1 := by
        have h2 := hZ2 z hz
        calc z = z ^ 7 * (z ^ 2)⁻¹ ^ 3 := by group
          _ = 1 := by rw [hz7, h2, inv_one, one_pow, one_mul]
      rw [hyz, hz1, mul_one]
    by_contra hp7
    have h7p : (7 : ZMod p) ≠ 0 := by
      intro h0
      have := (ZMod.natCast_eq_zero_iff 7 p).mp (by exact_mod_cast h0)
      exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
    have hx1 : (x : GL V₄ (ZMod p)) ≠ 1 := fun h0 => by
      apply hc1
      apply θ.symm.injective
      rw [← hxc, show x = 1 from Subtype.ext h0, QuotientGroup.mk_one, map_one]
    have hconj : IsConj (x : GL V₄ (ZMod p)) ((x : GL V₄ (ZMod p)) ^ 2) := by
      rw [← Subgroup.coe_pow]
      exact G.subtype.map_isConj (isConj_iff.mpr ⟨hl, hconjG⟩)
    exact false_of_isConj_sq_of_pow_seven h7p (hGS x.2)
      (by rw [← Subgroup.coe_pow, hx7, Subgroup.coe_one]) hx1 hconj

end CFSG.RankThree.SubgroupLists
