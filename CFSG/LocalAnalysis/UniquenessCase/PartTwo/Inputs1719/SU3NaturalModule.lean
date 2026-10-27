module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.Quasithin.Background.HSU3
public import CFSG.Quasithin.Background.HSU3NPrime
public import CFSG.Quasithin.Background.HStandard
public import CFSG.Quasithin.Background.HSU3Unitary
public import CFSG.Quasithin.Background.D2Tools
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.HTransport
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3
open scoped Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

noncomputable instance instFieldSK {X : Subgroup (MulAut W)} {n : ℕ}
    (S : CNatModStructSU3 W X n) : Field S.K := S.fieldK

noncomputable instance instFiniteSK {X : Subgroup (MulAut W)} {n : ℕ}
    (S : CNatModStructSU3 W X n) : Finite S.K := S.finiteK

@[expose] noncomputable def su3NatEquiv {X : Subgroup (MulAut W)} {n : ℕ}
    (S : CNatModStructSU3 W X n) : W ≃* StdMod (Fin 3) S.K :=
  Subgroup.topEquiv.symm.trans S.e

theorem su3NatEquiv_apply {X : Subgroup (MulAut W)} {n : ℕ} (S : CNatModStructSU3 W X n)
    (w : W) : su3NatEquiv S w = S.e ⟨w, Subgroup.mem_top w⟩ := rfl

@[expose] noncomputable def natImageX {X : Subgroup (MulAut W)} {n : ℕ}
    (S : CNatModStructSU3 W X n) : Subgroup (MulAut (StdMod (Fin 3) S.K)) :=
  X.map (MulAut.congr (su3NatEquiv S)).toMonoidHom

theorem natImage_smul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (GL ι K)} {g : MulAut (StdMod ι K)} (hg : g ∈ natImage Γ)
    (c : K) (w : StdMod ι K) : g (c • w) = c • g w := by
  obtain ⟨γ, rfl⟩ := hg
  have hw : c • w = Multiplicative.ofAdd (c • Multiplicative.toAdd w) := by
    rw [show w = Multiplicative.ofAdd (Multiplicative.toAdd w) from (ofAdd_toAdd w).symm,
      ← Multiplicative.ofAdd_smul, toAdd_ofAdd]
  rw [hw]
  calc natAut Γ γ (Multiplicative.ofAdd (c • Multiplicative.toAdd w))
      = Multiplicative.ofAdd (toAddMap (natAut Γ γ) (c • Multiplicative.toAdd w)) := rfl
    _ = Multiplicative.ofAdd (Matrix.mulVec (γ : GL ι K) (c • Multiplicative.toAdd w)) := by
          rw [toAddMap_natAut]
    _ = Multiplicative.ofAdd (c • Matrix.mulVec (γ : GL ι K) (Multiplicative.toAdd w)) := by
          rw [Matrix.mulVec_smul]
    _ = c • Multiplicative.ofAdd (Matrix.mulVec (γ : GL ι K) (Multiplicative.toAdd w)) := by
          rw [Multiplicative.ofAdd_smul]
    _ = c • Multiplicative.ofAdd (toAddMap (natAut Γ γ) (Multiplicative.toAdd w)) := by
          rw [toAddMap_natAut]
    _ = c • natAut Γ γ w := by
          rw [show w = Multiplicative.ofAdd (Multiplicative.toAdd w) from (ofAdd_toAdd w).symm]
          rfl

theorem natImage_smul_comm {K : Type} [Field K] {Γ : Subgroup (GL (Fin 3) K)}
    {g : MulAut (StdMod (Fin 3) K)} (hg : g ∈ natImage Γ) (c : K) (w : StdMod (Fin 3) K) :
    c • (g w * w⁻¹) = g (c • w) * (c • w)⁻¹ := by
  rw [smul_mul', smul_inv', ← natImage_smul hg c w]

theorem natImageX_eq {X : Subgroup (MulAut W)} {n : ℕ} (S : CNatModStructSU3 W X n) :
    natImageX S = natImage (StatedSU 3 (2 ^ n) S.K) := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    obtain ⟨A, hA, hAact⟩ := S.map_mem x hx
    refine ⟨⟨A, hA⟩, ?_⟩
    apply MulEquiv.ext
    intro w
    obtain ⟨w', rfl⟩ := (su3NatEquiv S).surjective w
    change (natAut (StatedSU 3 (2 ^ n) S.K) ⟨A, hA⟩) (su3NatEquiv S w') =
      (MulAut.congr (su3NatEquiv S) x) (su3NatEquiv S w')
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.mul_apply]
    rw [su3NatEquiv_apply, su3NatEquiv_apply]
    have h := hAact w' (Subgroup.mem_top w') (Subgroup.mem_top (x w'))
    rw [h]
    rfl
  · rintro g ⟨⟨A, hA⟩, rfl⟩
    obtain ⟨x, hx, hxact⟩ := S.surj A hA
    refine ⟨x, hx, ?_⟩
    apply MulEquiv.ext
    intro w
    obtain ⟨w', rfl⟩ := (su3NatEquiv S).surjective w
    change (MulAut.congr (su3NatEquiv S) x) (su3NatEquiv S w') =
      (natAut (StatedSU 3 (2 ^ n) S.K) ⟨A, hA⟩) (su3NatEquiv S w')
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.mul_apply]
    rw [su3NatEquiv_apply, su3NatEquiv_apply]
    have h := hxact w' (Subgroup.mem_top w') (Subgroup.mem_top (x w'))
    rw [h]
    rfl

theorem one_le_of_cardK {X : Subgroup (MulAut W)} {n : ℕ} (S : CNatModStructSU3 W X n) :
    1 ≤ n := by
  have h2 : 2 ≤ Nat.card S.K := by
    haveI : Fintype S.K := Fintype.ofFinite S.K
    exact Nat.succ_le_of_lt (by simpa using (Fintype.one_lt_card (α := S.K)))
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [S.cardK, h] at h2
    norm_num at h2
  · exact h

theorem charP_cardK {X : Subgroup (MulAut W)} {n : ℕ} (S : CNatModStructSU3 W X n) :
    CharP S.K 2 := by
  exact CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (F := S.K) (n := 2 * n)
    Nat.prime_two (by rw [S.cardK, ← pow_mul, Nat.mul_comm])

theorem pRank_inf_linSub_le {K : Type} [Field K] [Finite K]
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} {n : ℕ}
    [CharP K 2] (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) :
    CFSG.Open.pRank 2 (X ⊓ linSub) ≤ n := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  obtain ⟨E, hEX, hE, hEc⟩ := exists_isElemAbelian_card_pRank (X ⊓ linSub)
  have h2 : Nat.card ↥(E ⊓ linSub) = Nat.card E := by
    rw [inf_eq_left.mpr (hEX.trans inf_le_right)]
  have h3 := SU3.card_inf_linSub_le hn hK ((hEX.trans inf_le_left).trans hXN)
    (isElemAbelian2_iff.mpr hE)
  rw [h2, hEc] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3

theorem rank_of_cNatModSU3 {X L A : Subgroup (MulAut W)} {n : ℕ}
    (hL : CNatModSU3 W L n)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : A ≤ X) :
    CFSG.Open.pRank 2 A ≤ n + 1 := by
  haveI : Finite (MulAut W) := inferInstance
  obtain ⟨S⟩ := hL
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  haveI : CharP S.K 2 := charP_cardK S
  have hn : 1 ≤ n := one_le_of_cardK S
  let e := MulAut.congr (su3NatEquiv S)
  have hL' : L.map e.toMonoidHom = natImage (StatedSU 3 (2 ^ n) S.K) := natImageX_eq S
  have hX' : X.map e.toMonoidHom ≤ natNorm (StatedSU 3 (2 ^ n) S.K) := by
    have h : X.map e.toMonoidHom ≤
        (Subgroup.normalizer (L : Set (MulAut W))).map e.toMonoidHom := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hXN hx, rfl⟩
    rwa [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) L e.bijective, hL'] at h
  have hAle : CFSG.Open.pRank 2 (A.map e.toMonoidHom) ≤
      CFSG.Open.pRank 2 (X.map e.toMonoidHom) :=
    CFSG.SectionRank.pRank_mono (by norm_num)
      (show A.map e.toMonoidHom ≤ X.map e.toMonoidHom from by
      rintro y ⟨a, ha, rfl⟩
      exact ⟨a, hA ha, rfl⟩)
  have hXle : CFSG.Open.pRank 2 (X.map e.toMonoidHom) ≤ n + 1 :=
    SU3.pRank_le hn S.cardK hX'
  have heq : CFSG.Open.pRank 2 (A.map e.toMonoidHom) = CFSG.Open.pRank 2 A :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_map_mulEquiv
      (by norm_num) e A
  omega

theorem linear_rank_of_cNatModSU3 {X L A : Subgroup (MulAut W)} {n : ℕ}
    (hL : CNatModSU3 W L n)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : A ≤ X) :
    CFSG.Open.pRank 2 (A ⊓ L) ≤ n := by
  obtain ⟨S⟩ := hL
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  haveI : CharP S.K 2 := charP_cardK S
  have hn : 1 ≤ n := one_le_of_cardK S
  let e := MulAut.congr (su3NatEquiv S)
  have hL' : L.map e.toMonoidHom = natImage (StatedSU 3 (2 ^ n) S.K) := natImageX_eq S
  have hX' : X.map e.toMonoidHom ≤ natNorm (StatedSU 3 (2 ^ n) S.K) := by
    have h : X.map e.toMonoidHom ≤
        (Subgroup.normalizer (L : Set (MulAut W))).map e.toMonoidHom := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hXN hx, rfl⟩
    rwa [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) L e.bijective, hL'] at h
  have hinf : (A ⊓ L).map e.toMonoidHom ≤ (X.map e.toMonoidHom) ⊓ linSub := by
    refine le_inf (show (A ⊓ L).map e.toMonoidHom ≤ X.map e.toMonoidHom from by
      rintro y ⟨a, ha, rfl⟩
      exact ⟨a, hA ha.1, rfl⟩) ?_
    calc (A ⊓ L).map e.toMonoidHom ≤ L.map e.toMonoidHom := by
          rintro y ⟨a, ha, rfl⟩
          exact ⟨a, ha.2, rfl⟩
      _ = natImage (StatedSU 3 (2 ^ n) S.K) := hL'
      _ ≤ linSub := natImage_le_linSub (StatedSU 3 (2 ^ n) S.K)
  have hmono : CFSG.Open.pRank 2 ((A ⊓ L).map e.toMonoidHom) ≤
      CFSG.Open.pRank 2 ((X.map e.toMonoidHom) ⊓ linSub) :=
    CFSG.SectionRank.pRank_mono (by norm_num) hinf
  have hlin := pRank_inf_linSub_le hn S.cardK hX'
  have heq : CFSG.Open.pRank 2 ((A ⊓ L).map e.toMonoidHom) =
      CFSG.Open.pRank 2 (A ⊓ L) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_map_mulEquiv (by norm_num) e (A ⊓ L)
  omega

theorem index_of_cNatModSU3 {X L A : Subgroup (MulAut W)} {n : ℕ}
    (hL : CNatModSU3 W L n)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : A ≤ X) (hAel : IsElemAbelian 2 A) :
    Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ L) := by
  obtain ⟨S⟩ := hL
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  haveI : CharP S.K 2 := charP_cardK S
  have hn : 1 ≤ n := one_le_of_cardK S
  let e := MulAut.congr (su3NatEquiv S)
  have hL' : L.map e.toMonoidHom = natImage (StatedSU 3 (2 ^ n) S.K) := natImageX_eq S
  have hX' : X.map e.toMonoidHom ≤ natNorm (StatedSU 3 (2 ^ n) S.K) := by
    have h : X.map e.toMonoidHom ≤
        (Subgroup.normalizer (L : Set (MulAut W))).map e.toMonoidHom := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hXN hx, rfl⟩
    rwa [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) L e.bijective, hL'] at h
  set E : Subgroup (MulAut (StdMod (Fin 3) S.K)) := A.map e.toMonoidHom with hE
  have hEA : E ≤ X.map e.toMonoidHom := by
    rintro y ⟨a, ha, rfl⟩
    exact ⟨a, hA ha, rfl⟩
  have hEN : E ≤ natNorm (StatedSU 3 (2 ^ n) S.K) := hEA.trans hX'
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have h := hAel.2 a ha
    simpa using congrArg (e.toMonoidHom) h
  have hΓ := SU3.hasScalarCommutant' hn S.cardK
  have hcard := card_le_two_mul_card_inf_linSub (n := 2 * n) hΓ (by omega)
    (SU3.card_eq_two_pow S.cardK) hEN hE2
  have hlin : E ⊓ linSub = E ⊓ natImage (StatedSU 3 (2 ^ n) S.K) := by
    apply le_antisymm
    · rintro g ⟨hgE, hgl⟩
      exact ⟨hgE, mem_natImage_of_two_pow hn S.cardK (hEN hgE) hgl
        (j := 1) (by simpa using hE2 g hgE)⟩
    · exact inf_le_inf_left _ (natImage_le_linSub (StatedSU 3 (2 ^ n) S.K))
  have hcardE : Nat.card ↥E = Nat.card ↥A := by
    rw [hE]
    exact Subgroup.card_map_of_injective e.injective
  have hcardI : Nat.card ↥(E ⊓ linSub) = Nat.card ↥(A ⊓ L) := by
    rw [hlin, ← hL', ← Subgroup.map_inf_eq A L e.toMonoidHom e.injective]
    exact Subgroup.card_map_of_injective e.injective
  rw [hcardE, hcardI] at hcard
  exact hcard

theorem nontrivial_comm_of_natNorm {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X A : Subgroup (MulAut (StdMod (Fin 3) K))}
    (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) (hAX : A ≤ X)
    (hAel : IsElemAbelian 2 A)
    (hAnL : ¬ A ≤ natImage (StatedSU 3 (2 ^ n) K)) :
    commSub (fixV (A ⊓ natImage (StatedSU 3 (2 ^ n) K))) A ≠ ⊥ := by
  let Γ := StatedSU 3 (2 ^ n) K
  have hΓ := SU3.hasScalarCommutant' hn hK
  obtain ⟨a, haA, haL⟩ := SetLike.not_le_iff_exists.1 hAnL
  have haN : a ∈ natNorm Γ := hXN (hAX haA)
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  have hal : a ∉ linSub := by
    intro hlin
    exact haL (mem_natImage_of_two_pow hn hK haN hlin (j := 1) (by simpa using ha2))
  obtain ⟨σ, hsl⟩ := exists_semilinear hΓ haN
  have hσ : σ ≠ RingEquiv.refl K := by
    intro hσ
    apply hal
    rw [← fieldHom_eq_one_iff hΓ ⟨a, haN⟩]
    exact (fieldHom_eq_iff hΓ ⟨a, haN⟩ (RingEquiv.refl K)).2 (hσ ▸ hsl)
  set U : Subgroup (StdMod (Fin 3) K) := fixV (A ⊓ natImage Γ) with hU
  have hUne : U ≠ ⊥ := by
    by_cases hbot : A ⊓ natImage Γ = ⊥
    · rw [hU, hbot]
      have hfix : fixV (⊥ : Subgroup (MulAut (StdMod (Fin 3) K))) = ⊤ := by
        ext v
        simp [mem_fixV]
      rw [hfix]
      exact top_ne_bot
    · have hP : IsPGroup 2 ↥(A ⊓ natImage Γ) := hAel.isPGroup.to_le inf_le_left
      have hW2 : ∀ v : StdMod (Fin 3) K, v ^ 2 = 1 := by
        intro v
        rw [show v = Multiplicative.ofAdd (Multiplicative.toAdd v) from
          (ofAdd_toAdd v).symm, pow_two, ← ofAdd_add,
          ← ofAdd_zero]
        congr 1
        ext i
        change Multiplicative.toAdd v i + Multiplicative.toAdd v i = 0
        linear_combination (Multiplicative.toAdd v i) * CharTwo.two_eq_zero (R := K)
      have hcardW : Nat.card (StdMod (Fin 3) K) = 2 ^ (6 * n) := by
        rw [card_stdMod, hK, Fintype.card_fin, ← pow_mul, ← pow_mul]
        congr 1
        ring
      have hrk : 0 < rk (StdMod (Fin 3) K) := by
        rw [rk, hcardW, padicValNat.prime_pow]
        omega
      intro hzero
      have hpos := rk_fixV_pos_of_isPGroup_two hW2 hP hrk
      change 0 < rk U at hpos
      rw [hzero] at hpos
      simp [rk_bot] at hpos
  have hsmul : ∀ c : K, ∀ u ∈ U,
      Multiplicative.ofAdd (c • Multiplicative.toAdd u) ∈ U := by
    intro c u hu
    rw [hU, mem_fixV] at hu ⊢
    intro b hb
    have hbl : b ∈ linSub := natImage_le_linSub Γ hb.2
    have hsem : IsSemilinear b (RingEquiv.refl K) := mem_linSub.1 hbl
    have hbu : b u = u := hu b hb
    calc b (Multiplicative.ofAdd (c • Multiplicative.toAdd u))
        = Multiplicative.ofAdd (toAddMap b (c • Multiplicative.toAdd u)) := rfl
      _ = Multiplicative.ofAdd (c • toAddMap b (Multiplicative.toAdd u)) := by
          simpa using congrArg Multiplicative.ofAdd (hsem c (Multiplicative.toAdd u))
      _ = Multiplicative.ofAdd (c • Multiplicative.toAdd (b u)) := rfl
      _ = Multiplicative.ofAdd (c • Multiplicative.toAdd u) := by
          rw [show Multiplicative.toAdd (b u) = Multiplicative.toAdd u from
            congrArg Multiplicative.toAdd hbu]
  have hact : ∃ u ∈ U, a u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hσ
    ext c
    obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUne
    have hx0 : Multiplicative.toAdd u ≠ 0 := by
      intro h0
      have hu1' : u = 1 := by
        rw [show u = Multiplicative.ofAdd (Multiplicative.toAdd u) from
          (ofAdd_toAdd u).symm, h0, ofAdd_zero]
      exact hu1 (Subtype.ext hu1')
    have hcu : Multiplicative.ofAdd (c • Multiplicative.toAdd u) ∈ U := hsmul c u huU
    have hfix1 : a (Multiplicative.ofAdd (c • Multiplicative.toAdd u)) =
        Multiplicative.ofAdd (c • Multiplicative.toAdd u) := hcon _ hcu
    have hfix0 : a u = u := hcon u huU
    have h3 : σ c • Multiplicative.toAdd u = c • Multiplicative.toAdd u := by
      calc σ c • Multiplicative.toAdd u
          = σ c • toAddMap a (Multiplicative.toAdd u) := by
            rw [show toAddMap a (Multiplicative.toAdd u) = Multiplicative.toAdd (a u) from rfl,
              hfix0]
        _ = toAddMap a (c • Multiplicative.toAdd u) := (hsl c _).symm
        _ = Multiplicative.toAdd (a (Multiplicative.ofAdd
              (c • Multiplicative.toAdd u))) := rfl
        _ = Multiplicative.toAdd (Multiplicative.ofAdd
              (c • Multiplicative.toAdd u)) := by rw [hfix1]
        _ = c • Multiplicative.toAdd u := toAdd_ofAdd _
    have hsub : (σ c - c) • Multiplicative.toAdd u = 0 := by
      rw [sub_smul, h3, sub_self]
    have hzero : σ c - c = 0 := (smul_eq_zero.1 hsub).resolve_right hx0
    exact sub_eq_zero.1 hzero
  obtain ⟨u, huU, hau⟩ := hact
  intro hbot
  have hmem : a u * u⁻¹ ∈ commSub U A :=
    Subgroup.subset_closure ⟨a, haA, u, huU, rfl⟩
  rw [hbot] at hmem
  exact hau (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem))

theorem nontrivial_comm_of_cNatModSU3 {X L A : Subgroup (MulAut W)} {n : ℕ}
    (hL : CNatModSU3 W L n)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : A ≤ X) (hAel : IsElemAbelian 2 A) (hAnL : ¬ A ≤ L) :
    commSub (fixV (A ⊓ L)) A ≠ ⊥ := by
  obtain ⟨S⟩ := hL
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  haveI : CharP S.K 2 := charP_cardK S
  have hn : 1 ≤ n := one_le_of_cardK S
  let e := MulAut.congr (su3NatEquiv S)
  let Γ := StatedSU 3 (2 ^ n) S.K
  have hL' : L.map e.toMonoidHom = natImage Γ := natImageX_eq S
  have hX' : X.map e.toMonoidHom ≤ natNorm Γ := by
    have h : X.map e.toMonoidHom ≤
        (Subgroup.normalizer (L : Set (MulAut W))).map e.toMonoidHom := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hXN hx, rfl⟩
    rwa [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) L e.bijective, hL'] at h
  have hA'X : A.map e.toMonoidHom ≤ X.map e.toMonoidHom := by
    rintro y ⟨a, ha, rfl⟩
    exact ⟨a, hA ha, rfl⟩
  have hA'el : IsElemAbelian 2 (A.map e.toMonoidHom) :=
    IsElemAbelian.map hAel e.toMonoidHom
  have hA'nL : ¬ A.map e.toMonoidHom ≤ natImage Γ := by
    intro h
    apply hAnL
    intro a ha
    have hea : e a ∈ natImage Γ := h ⟨a, ha, rfl⟩
    rw [← hL'] at hea
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.1 hea
    have hla : a = l := e.injective hle.symm
    rwa [hla]
  have hcoord := nontrivial_comm_of_natNorm hn S.cardK hX' hA'X hA'el hA'nL
  have hinf : A.map e.toMonoidHom ⊓ natImage Γ = (A ⊓ L).map e.toMonoidHom := by
    rw [← hL', ← Subgroup.map_inf_eq A L e.toMonoidHom e.injective]
  rw [hinf, fixV_map_congr_equiv (su3NatEquiv S) (A ⊓ L),
    commSub_map_mulAutCongr (su3NatEquiv S) (fixV (A ⊓ L)) A] at hcoord
  intro hbot
  exact hcoord (by rw [hbot, Subgroup.map_bot])

theorem semilinear_not_fix_smul {K : Type} [Field K]
    {a : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K}
    (hσ : σ ≠ RingEquiv.refl K) (hsl : IsSemilinear a σ)
    {u : StdMod (Fin 3) K} (hu1 : u ≠ 1)
    (hfixu : a u = u)
    (hfixsmul : ∀ c : K, a (c • u) = c • u) : False := by
  have hx0 : Multiplicative.toAdd u ≠ 0 := by
    intro h0
    apply hu1
    rw [show u = Multiplicative.ofAdd (Multiplicative.toAdd u) from
      (ofAdd_toAdd u).symm, h0, ofAdd_zero]
  have hafix : toAddMap a (Multiplicative.toAdd u) = Multiplicative.toAdd u := by
    rw [show toAddMap a (Multiplicative.toAdd u) = Multiplicative.toAdd (a u) from rfl, hfixu]
  apply hσ
  ext c
  have hcu : c • u = Multiplicative.ofAdd (c • Multiplicative.toAdd u) := by
    rw [show u = Multiplicative.ofAdd (Multiplicative.toAdd u) from (ofAdd_toAdd u).symm,
      ← Multiplicative.ofAdd_smul, toAdd_ofAdd]
  have hcufix : toAddMap a (c • Multiplicative.toAdd u) = c • Multiplicative.toAdd u := by
    rw [show toAddMap a (c • Multiplicative.toAdd u) =
      Multiplicative.toAdd (a (Multiplicative.ofAdd (c • Multiplicative.toAdd u))) from rfl,
      ← hcu, hfixsmul c]
    rw [hcu, toAdd_ofAdd]
  have h3 : σ c • Multiplicative.toAdd u = c • Multiplicative.toAdd u := by
    calc σ c • Multiplicative.toAdd u
        = σ c • toAddMap a (Multiplicative.toAdd u) := by rw [hafix]
      _ = toAddMap a (c • Multiplicative.toAdd u) := (hsl c _).symm
      _ = c • Multiplicative.toAdd u := hcufix
  have hsub : (σ c - c) • Multiplicative.toAdd u = 0 := by
    rw [sub_smul, h3, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 hsub).resolve_right hx0)

theorem not_quadratic_of_natNorm {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X A : Subgroup (MulAut (StdMod (Fin 3) K))}
    (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) (hAX : A ≤ X)
    (hAel : IsElemAbelian 2 A)
    (hAnL : ¬ A ≤ natImage (StatedSU 3 (2 ^ n) K))
    (hAnz : A ⊓ natImage (StatedSU 3 (2 ^ n) K) ≠ ⊥) :
    ¬ IsQuadratic A := by
  let Γ := StatedSU 3 (2 ^ n) K
  have hΓ := SU3.hasScalarCommutant' hn hK
  intro hquad
  obtain ⟨a, haA, haL⟩ := SetLike.not_le_iff_exists.1 hAnL
  have haN : a ∈ natNorm Γ := hXN (hAX haA)
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  have hal : a ∉ linSub := by
    intro hlin
    exact haL (mem_natImage_of_two_pow hn hK haN hlin (j := 1) (by simpa using ha2))
  obtain ⟨σ, hsl⟩ := exists_semilinear hΓ haN
  have hσ : σ ≠ RingEquiv.refl K := by
    intro hσ
    apply hal
    rw [← fieldHom_eq_one_iff hΓ ⟨a, haN⟩]
    exact (fieldHom_eq_iff hΓ ⟨a, haN⟩ (RingEquiv.refl K)).2 (hσ ▸ hsl)
  obtain ⟨⟨t, htA, htL⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAnz
  have htne : t ≠ 1 := by
    intro h
    exact ht1 (Subtype.ext h)
  obtain ⟨w, hw⟩ : ∃ w : StdMod (Fin 3) K, t w ≠ w := by
    by_contra h
    push Not at h
    exact htne (MulEquiv.ext h)
  set u : StdMod (Fin 3) K := t w * w⁻¹
  have hu1 : u ≠ 1 := by
    intro h
    exact hw (mul_inv_eq_one.1 h)
  have huU : u ∈ commV (Subgroup.zpowers t) := by
    rw [commV_eq_commSub, commSub]
    exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, w, Subgroup.mem_top w, rfl⟩
  have hU_le : commV (Subgroup.zpowers t) ≤ fixV A := by
    rw [commV_eq_commSub (Subgroup.zpowers t)]
    have h2 : commSub ⊤ A ≤ fixV A := by
      have h3 : commV A ≤ fixV A := hquad
      rwa [commV_eq_commSub A] at h3
    exact (commSub_mono le_rfl (Subgroup.zpowers_le.2 htA)).trans h2
  have hfixu : a u = u := (mem_fixV.1 (hU_le huU)) a haA
  have hfixsmul : ∀ c : K, a (c • u) = c • u := by
    intro c
    have hgen : t (c • w) * (c • w)⁻¹ ∈ commV (Subgroup.zpowers t) := by
      rw [commV_eq_commSub, commSub]
      exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, c • w, Subgroup.mem_top _, rfl⟩
    rw [natImage_smul_comm htL c w]
    exact (mem_fixV.1 (hU_le hgen)) a haA
  exact semilinear_not_fix_smul hσ hsl hu1 hfixu hfixsmul

theorem isQuadratic_map {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (A : Subgroup (MulAut V)) :
    IsQuadratic (A.map (MulAut.congr e).toMonoidHom) ↔ IsQuadratic A := by
  rw [IsQuadratic, IsQuadratic, commV_map_congr_equiv, fixV_map_congr_equiv]
  exact Subgroup.map_le_map_iff_of_injective e.injective

theorem not_quadratic_of_cNatModSU3 {X L A : Subgroup (MulAut W)} {n : ℕ}
    (hL : CNatModSU3 W L n)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA : A ≤ X) (hAel : IsElemAbelian 2 A) (hAnL : ¬ A ≤ L)
    (hAnz : A ⊓ L ≠ ⊥) :
    ¬ IsQuadratic A := by
  obtain ⟨S⟩ := hL
  letI : Field S.K := S.fieldK
  letI : Finite S.K := S.finiteK
  haveI : CharP S.K 2 := charP_cardK S
  have hn : 1 ≤ n := one_le_of_cardK S
  let e := MulAut.congr (su3NatEquiv S)
  let Γ := StatedSU 3 (2 ^ n) S.K
  have hL' : L.map e.toMonoidHom = natImage Γ := natImageX_eq S
  have hX' : X.map e.toMonoidHom ≤ natNorm Γ := by
    have h : X.map e.toMonoidHom ≤
        (Subgroup.normalizer (L : Set (MulAut W))).map e.toMonoidHom := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, hXN hx, rfl⟩
    rwa [Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom) L e.bijective, hL'] at h
  have hA'X : A.map e.toMonoidHom ≤ X.map e.toMonoidHom := by
    rintro y ⟨a, ha, rfl⟩
    exact ⟨a, hA ha, rfl⟩
  have hA'el : IsElemAbelian 2 (A.map e.toMonoidHom) :=
    IsElemAbelian.map hAel e.toMonoidHom
  have hA'nL : ¬ A.map e.toMonoidHom ≤ natImage Γ := by
    intro h
    apply hAnL
    intro a ha
    have hea : e a ∈ natImage Γ := h ⟨a, ha, rfl⟩
    rw [← hL'] at hea
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.1 hea
    have hla : a = l := e.injective hle.symm
    rwa [hla]
  have hA'nz : A.map e.toMonoidHom ⊓ natImage Γ ≠ ⊥ := by
    intro hbot
    apply hAnz
    have hmap : (A ⊓ L).map e.toMonoidHom = ⊥ := by
      rw [Subgroup.map_inf_eq A L e.toMonoidHom e.injective, hL']
      exact hbot
    have hle : (A ⊓ L).map e.toMonoidHom ≤ (⊥ : Subgroup (MulAut W)).map e.toMonoidHom := by
      rw [Subgroup.map_bot, hmap]
    exact le_bot_iff.1 ((Subgroup.map_le_map_iff_of_injective e.injective).1 hle)
  intro hquad
  exact not_quadratic_of_natNorm hn S.cardK hX' hA'X hA'el hA'nL hA'nz
    ((isQuadratic_map (su3NatEquiv S) A).2 hquad)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
