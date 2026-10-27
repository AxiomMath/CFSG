module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.ClassicalInvolution.Orders.Twisted
import CFSG.Sporadic.Recognition.McLMultiplierCert
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res4Three

theorem conj_injective_of_center_eq_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_center_iff]
  intro h
  have h1 := congrArg (fun φ : MulAut X => φ h) hg
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc h * g = g * h * g⁻¹ * g := by rw [h1]
    _ = g * h := by group

theorem card_le_twentySeven_of_normalForm {X : Type*} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥)
    (h9 : ∀ F : Subgroup X, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 9)
    {C : Subgroup (MulAut X)} (hC : IsCyclic C)
    (hNC : ∀ α : MulAut X, ∃ g : X, ∃ c ∈ C, α = MulAut.conj g * c)
    (B : Subgroup (MulAut X)) (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 27 := by
  set N := (MulAut.conj : X →* MulAut X).range with hNdef
  have hNn : N.Normal := ⟨fun d hd β => by
    obtain ⟨y, rfl⟩ := hd
    exact ⟨β y, (KFacts.mul_mulAutConj_mul_inv β y).symm⟩⟩
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut X)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨g, c, hc, rfl⟩ := hNC b
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, c, hc, rfl⟩
  have h1 := Sec4.card_le_three_mul_card_inf hB hC hCN hBNC
  have hconj := conj_injective_of_center_eq_bot hZ
  set E := (B ⊓ N).comap (MulAut.conj : X →* MulAut X)
  have hle : B ⊓ N ≤ (MulAut.conj : X →* MulAut X).range := inf_le_right
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    have h := Subgroup.card_map_of_injective (K := E) hconj
    rw [Subgroup.map_comap_eq_self hle] at h
    exact h.symm
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hconj ?_)⟩⟩, fun x hx => hconj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hBc _ (Subgroup.mem_comap.mp x.2).1 _ (Subgroup.mem_comap.mp y.2).1
    · rw [map_pow, map_one]
      exact hB.2 _ (Subgroup.mem_comap.mp hx).1
  have := h9 E hE
  omega

theorem card_le_nine_of_pRank_le_two {H : Type*} [Group H] [Finite H]
    (h : CFSG.pRank 3 H ≤ 2) (F : Subgroup H) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    Nat.card F ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFe : CFSG.IsElementaryAbelian 3 F :=
    { is_comm := hF.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hF.2 x x.2) }
  obtain ⟨r, hr⟩ := (CFSG.IsElementaryAbelian.isPGroup 3 F).exists_card_eq
  have hmem : r ∈ {r : ℕ | ∃ A : Subgroup H, CFSG.IsElementaryAbelian 3 A ∧
      Nat.card A = 3 ^ r} := ⟨F, hFe, hr⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup H, CFSG.IsElementaryAbelian 3 A ∧ Nat.card A = 3 ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro s ⟨B, -, hB⟩
    have h1 := Subgroup.card_le_card_group B
    rw [hB] at h1
    exact (Nat.lt_pow_self (by norm_num)).le.trans h1
  have hle : r ≤ 2 := (le_csSup hbdd hmem).trans h
  rw [hr]
  calc 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 9 := by norm_num

theorem eq_one_of_mem_center_of_sylow_comm {X : Type*} [Group X] [Finite X]
    (hX : commutator X = ⊤) {p : ℕ} [Fact p.Prime] (P : Sylow p X)
    (hP : ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a)
    {z : X} (hz : z ∈ Subgroup.center X) {k : ℕ} (hzp : orderOf z = p ^ k) : z = 1 := by
  classical
  let ϕ : (P : Subgroup X) →* Abelianization (P : Subgroup X) := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup X) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hzk
    rw [mul_assoc, ← hzk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow ϕ z hkey
  have h2 : ϕ.transfer z = 1 := by
    have : z ∈ commutator X := hX ▸ Subgroup.mem_top z
    exact (Abelianization.commutator_subset_ker ϕ.transfer) this
  rw [h2] at h1
  have hcomm : commutator (P : Subgroup X) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact Subtype.ext (hP _ b.2 _ a.2)
  have h3 : (⟨z ^ (P : Subgroup X).index, MonoidHom.transfer_eq_pow_aux z hkey⟩ :
      (P : Subgroup X)) = 1 := by
    have h4 : ϕ ⟨z ^ (P : Subgroup X).index, MonoidHom.transfer_eq_pow_aux z hkey⟩ = 1 :=
      h1.symm
    have h5 := (QuotientGroup.eq_one_iff _).mp h4
    rw [hcomm] at h5
    exact (Subgroup.mem_bot).mp h5
  have h6 : z ^ (P : Subgroup X).index = 1 := congrArg Subtype.val h3
  have h7 : p ^ k ∣ (P : Subgroup X).index := hzp ▸ orderOf_dvd_of_pow_eq_one h6
  have hnd := P.not_dvd_index
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hzp
    exact hzp
  · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans h7) hnd

theorem not_dvd_card_center_of_not_sq_dvd {X : Type*} [Group X] [Finite X]
    (hX : commutator X = ⊤) {p : ℕ} (hp : p.Prime)
    (hsq : ¬ p ^ 2 ∣ Nat.card (X ⧸ Subgroup.center X)) :
    ¬ p ∣ Nat.card (Subgroup.center X) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro hpZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) p hpZ
  obtain P : Sylow p X := default
  let f : (P : Subgroup X) →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp (P : Subgroup X).subtype
  have hker : f.ker ≤ Subgroup.center (P : Subgroup X) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hx
    rw [Subgroup.mem_center_iff] at hxZ ⊢
    intro y
    exact Subtype.ext (hxZ y)
  have hfp : IsPGroup p f.range :=
    P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := hfp.exists_card_eq
  have hdvd : p ^ n ∣ Nat.card (X ⧸ Subgroup.center X) :=
    hn ▸ Subgroup.card_subgroup_dvd_card f.range
  have hn1 : n ≤ 1 := by
    by_contra h
    exact hsq ((pow_dvd_pow p (by omega)).trans hdvd)
  have hcyc : IsCyclic f.range := by
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · rw [pow_zero] at hn
      have : Subsingleton f.range := Finite.card_le_one_iff_subsingleton.mp hn.le
      infer_instance
    · rw [pow_one] at hn
      exact isCyclic_of_prime_card hn
  have hcomm := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f.rangeRestrict (by
    rw [MonoidHom.ker_rangeRestrict]; exact hker)
  have h1 := eq_one_of_mem_center_of_sylow_comm hX P
    (fun a ha b hb => congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) z.2
    (k := 1) (by rw [pow_one, Subgroup.orderOf_coe, hz])
  have h2 : z = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem not_sq_dvd_of_eq_mul {N i j m : ℕ} (hN : N = 2 ^ i * 3 ^ j * m) {p : ℕ} (hp : p.Prime)
    (h2 : p ≠ 2) (h3 : p ≠ 3) (hm : ∀ q, q.Prime → q ≠ 2 → q ≠ 3 → q ^ 2 ∣ m → False) :
    ¬ p ^ 2 ∣ N := by
  intro h
  have hc : Nat.Coprime (p ^ 2) (2 ^ i * 3 ^ j) := by
    refine Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr h2)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).mpr h3)
  rw [hN] at h
  exact hm p hp h2 h3 (hc.dvd_of_dvd_mul_left h)

theorem no_sq_of_le {m : ℕ} (hm0 : 0 < m) (hm : m ≤ 99)
    (hc : ∀ q, 5 ≤ q → q ≤ 9 → ¬ q ^ 2 ∣ m) :
    ∀ q, q.Prime → q ≠ 2 → q ≠ 3 → q ^ 2 ∣ m → False := by
  intro q hq h2 h3 hd
  have h5 : 5 ≤ q := by
    have := hq.two_le
    rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with h | h | h | h
    · exact absurd h h2
    · exact absurd h h3
    · exact absurd (h ▸ hq) (by decide)
    · exact h
  have hle : q ^ 2 ≤ m := Nat.le_of_dvd hm0 hd
  have h9 : q ≤ 9 := by nlinarith
  exact hc q h5 h9 hd

theorem card_center_eq_one_of {X : Type*} [Group X] [Finite X] (hX : commutator X = ⊤)
    (hcop : Nat.Coprime (Nat.card (Subgroup.center X)) 6)
    (hsq : ∀ p, p.Prime → p ≠ 2 → p ≠ 3 → ¬ p ^ 2 ∣ Nat.card (X ⧸ Subgroup.center X)) :
    Nat.card (Subgroup.center X) = 1 := by
  by_contra h
  have hp := Nat.minFac_prime h
  have hpd := Nat.minFac_dvd (Nat.card (Subgroup.center X))
  have hc := Nat.Coprime.coprime_dvd_left hpd hcop
  have h2 : (Nat.card (Subgroup.center X)).minFac ≠ 2 := fun h2 => by
    rw [h2] at hc
    exact absurd hc (by decide)
  have h3 : (Nat.card (Subgroup.center X)).minFac ≠ 3 := fun h3 => by
    rw [h3] at hc
    exact absurd hc (by decide)
  exact not_dvd_card_center_of_not_sq_dvd hX hp (hsq _ hp h2 h3) hpd

theorem card_U43 : Nat.card (projSU 4 3 1) = 3265920 :=
  CFSG.PGLModel.card_projSU_four_three

theorem card_L43_dvd : Nat.card (projSL 4 (GaloisField 3 1)) ∣ 12130560 := by
  refine (card_projSL_dvd 4 (GaloisField 3 1)).trans ?_
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)]
  decide

end Res4Three

open Res4Three

theorem rankAutD4_holds :
    ∀ (X : Type) [Group X] (n : ℕ), ChevalleyExceptionalModel X .trialityD4 2 n →
      CFSG.pRank 3 (MulAut X) ≤ 3 := by
  intro X _ f hX
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := hX
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf hm
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have : IsCyclic (RingAut K) := ringAut_isCyclic
  refine Sec4.pRank_three_le_of_card_le (Sec4.card_le_of_mulEquiv_mulAut e fun B hB => ?_)
  refine card_le_twentySeven_of_normalForm
    (center_graphFixedRootGroup_eq_bot σ.surjective)
    (fun F hF => Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hf hK
      (σ := σ.toRingHom) hσ F hF)
    (C := (fieldActorHom (t := TwistTag.D4) σ).range)
    (isCyclic_of_surjective _ (fieldActorHom (t := TwistTag.D4) σ).rangeRestrict_surjective)
    (fun α => ?_) B hB
  obtain ⟨g, δ, rfl⟩ := KFacts.exists_conj_mul_fieldActor hf hK3 hσ α
  exact ⟨g, fieldActor σ δ, ⟨δ, rfl⟩, rfl⟩

theorem rankAutF4_of_twistedF4
    (hF4 : Sec21.TwistedF4EvenThreeRankTwo) :
    ∀ (X : Type) [Group X] (n : ℕ), ReeTitsModel X .twistedF4 2 n →
      CFSG.pRank 3 (MulAut X) ≤ 3 := by
  intro X _ f hX
  have hr := hF4 X f hX
  obtain ⟨hfin, -, -, -, -, hiso⟩ := ReeTag.large_Ree_model_Schreier X 2 f hX
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hX
  have ha : 1 ≤ a := by
    have := hadm.2.2.2.2.2
    omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv _ E.toEquiv
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a K hK'
  have hZX := Sec21.Item223RankResProof.center_eq_bot_of_mulEquiv E hZ
  let φ : X ⧸ Subgroup.center X ≃* ReeTag.F4.reeGamma K a :=
    ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).trans E
  have : IsCyclic (K ≃+* K) := ringAut_isCyclic
  refine Sec4.pRank_three_le_of_card_le (Sec4.card_le_of_mulEquiv_mulAut E fun B hB => ?_)
  refine card_le_twentySeven_of_normalForm hZ (fun F hF => ?_)
    (C := (ReeTag.F4.reeGammaFieldAutHom K a).range)
    (isCyclic_of_surjective _ (ReeTag.F4.reeGammaFieldAutHom K a).rangeRestrict_surjective)
    (fun α => ?_) B hB
  · have h9 := card_le_nine_of_pRank_le_two hr (F.map φ.symm.toMonoidHom)
      (Sec4.isElemAbelian_map _ hF)
    rwa [Subgroup.card_map_of_injective φ.symm.injective] at h9
  · obtain ⟨x, β, rfl⟩ := (KFacts.largeRee_automorphism_normal_form ha hK').1 α
    exact ⟨x, _, ⟨β, rfl⟩, rfl⟩

theorem multiplier_holds :
    ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      Nat.Coprime (Nat.card (Subgroup.center X)) 6 →
      (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
        Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
        Nonempty (X ⧸ Subgroup.center X ≃* projSL 4 (GaloisField 3 1)) ∨
        Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)) →
      Subgroup.center X = ⊥ := by
  intro X _ _ hq hcop hX
  have hperf : commutator X = ⊤ := hq.1.commutator_eq_top
  rw [← Subgroup.card_eq_one]
  rcases hX with hG | he | he | he
  · have hc : Nat.card (X ⧸ Subgroup.center X) = 4245696 := by
      rw [CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two (by norm_num) hG]
      show CFSG.Open.ordG2 (3 ^ 1) = 4245696
      norm_num [CFSG.Open.ordG2]
    refine card_center_eq_one_of hperf hcop fun p hp h2 h3 => ?_
    rw [hc]
    exact not_sq_dvd_of_eq_mul (i := 6) (j := 6) (m := 91) (by norm_num) hp h2 h3
      (no_sq_of_le (by norm_num) (by norm_num) (by decide))
  · obtain ⟨e⟩ := he
    have h3 :=
      CFSG.Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate hq.1 e
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right (by norm_num) hcop) h3
  · obtain ⟨e⟩ := he
    refine card_center_eq_one_of hperf hcop fun p hp h2 h3 hd => ?_
    rw [Nat.card_congr e.toEquiv] at hd
    exact not_sq_dvd_of_eq_mul (N := 12130560) (i := 8) (j := 6) (m := 65) (by norm_num) hp h2
      h3 (no_sq_of_le (by norm_num) (by norm_num) (by decide)) (hd.trans card_L43_dvd)
  · obtain ⟨e⟩ := he
    refine card_center_eq_one_of hperf hcop fun p hp h2 h3 => ?_
    rw [Nat.card_congr e.toEquiv, card_U43]
    exact not_sq_dvd_of_eq_mul (i := 7) (j := 6) (m := 35) (by norm_num) hp h2 h3
      (no_sq_of_le (by norm_num) (by norm_num) (by decide))

end CFSG.RankThree.PartTwo.Sec4
