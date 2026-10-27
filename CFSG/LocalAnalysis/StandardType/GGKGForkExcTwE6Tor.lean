module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Orders
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Fix
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm2
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.SylowFrame

public section

namespace CFSG.StandardType

namespace ExcTwE6Nons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

private theorem ggKGTt_padicValNat_51840_eq_zero {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    padicValNat p 51840 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have hfac : (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 := by norm_num
  rw [hfac] at hdvd
  rcases (hp.dvd_mul).1 hdvd with h | h5
  · rcases (hp.dvd_mul).1 h with h2 | h3
    · have h2' : p ∣ 2 := hp.dvd_of_dvd_pow h2
      have hle := Nat.le_of_dvd (by norm_num) h2'
      omega
    · have h3' : p ∣ 3 := hp.dvd_of_dvd_pow h3
      have hle := Nat.le_of_dvd (by norm_num) h3'
      omega
  · have h5' : p ∣ 5 := h5
    have hle := Nat.le_of_dvd (by norm_num) h5'
    omega

private theorem ggKGTt_charpoly_neg_one_eval_natAbs {r : ℕ} (q : ℕ) :
    ((-1 : Matrix (Fin r) (Fin r) ℤ).charpoly.eval (q : ℤ)).natAbs = (q + 1) ^ r := by
  rw [CFSG.LieType.SeitzGeneration.natAbs_eval_charpoly]
  have hM : (-1 : Matrix (Fin r) (Fin r) ℤ) - (q : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ) =
      (-(q + 1 : ℤ)) • (1 : Matrix (Fin r) (Fin r) ℤ) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs with hij
    · ring
    · ring
  rw [hM, Matrix.det_smul, Matrix.det_one, mul_one]
  rw [Int.natAbs_pow, Int.natAbs_neg]
  have hcast : (q + 1 : ℤ) = ((q + 1 : ℕ) : ℤ) := by norm_num
  rw [hcast, Int.natAbs_natCast, Fintype.card_fin]

private theorem ggKGTt_charpoly_neg_one_ne_zero {r : ℕ} (q : ℕ) :
    (-1 : Matrix (Fin r) (Fin r) ℤ).charpoly.eval (q : ℤ) ≠ 0 := by
  intro h
  have h2 := ggKGTt_charpoly_neg_one_eval_natAbs (r := r) q
  rw [h] at h2
  simp only [Int.natAbs_zero] at h2
  have hpos : 0 < (q + 1) ^ r := pow_pos (Nat.succ_pos q) r
  omega

private theorem ggKGTt_torus_commute
    {L : Type} [Field L] (n : ModGL TwistTag.E6.tag L)
    (Φ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L)
    {h h' : ModGL TwistTag.E6.tag L} (hh : h ∈ twistedTorusOf n Φ)
    (hh' : h' ∈ twistedTorusOf n Φ) : Commute h h' := by
  have h1 : h ∈ torusGroup TwistTag.E6.tag L := (mem_twistedTorusOf.1 hh).1
  have h2 : h' ∈ torusGroup TwistTag.E6.tag L := (mem_twistedTorusOf.1 hh').1
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h1)
    (torusGroup_le_diagonalGroup h2)

private lemma ggKGTt_mul_pow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x y : G}
    (hcomm : Commute x y) {a b : ℕ} (hx : x ^ p ^ a = 1) (hy : y ^ p ^ b = 1) :
    (x * y) ^ p ^ (a + b) = 1 := by
  have hx' : x ^ p ^ (a + b) = 1 := by
    rw [show p ^ (a + b) = p ^ a * p ^ b from pow_add p a b, pow_mul, hx, one_pow]
  have hy' : y ^ p ^ (a + b) = 1 := by
    rw [show p ^ (a + b) = p ^ b * p ^ a by rw [pow_add, mul_comm], pow_mul, hy, one_pow]
  rw [hcomm.mul_pow (p ^ (a + b)), hx', hy', mul_one]

private lemma ggKGTt_inv_pow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x : G} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x⁻¹ ^ p ^ k = 1 := by
  rw [inv_pow, hx, inv_one]

private def ggKGTt_pTorsion {G : Type*} [Group G] (p : ℕ) (TF : Subgroup G)
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) : Subgroup G where
  carrier := {x | x ∈ TF ∧ ∃ k : ℕ, x ^ p ^ k = 1}
  one_mem' := ⟨TF.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxT, k, hxk⟩ ⟨hyT, l, hyl⟩
    exact ⟨TF.mul_mem hxT hyT, k + l,
      ggKGTt_mul_pow_pow_eq_one (hcomm x hxT y hyT) hxk hyl⟩
  inv_mem' := by
    rintro x ⟨hxT, k, hxk⟩
    exact ⟨TF.inv_mem hxT, k, ggKGTt_inv_pow_pow_eq_one hxk⟩

private lemma ggKGTt_pTorsion_le {G : Type*} [Group G] {p : ℕ} {TF : Subgroup G}
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) :
    ggKGTt_pTorsion p TF hcomm ≤ TF := fun _ hx => hx.1

private lemma ggKGTt_pTorsion_isPGroup {G : Type*} [Group G] {p : ℕ} {TF : Subgroup G}
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) :
    IsPGroup p (ggKGTt_pTorsion p TF hcomm) := by
  intro x
  obtain ⟨-, k, hk⟩ := x.2
  exact ⟨k, Subtype.ext hk⟩

private def ggKGTt_pTorsionSub {G : Type*} [Group G] (q : ℕ) (TF : Subgroup G)
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) : Subgroup G where
  carrier := {x | x ^ q = 1 ∧ x ∈ TF}
  one_mem' := ⟨by simp, TF.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxq, hxT⟩ ⟨hyq, hyT⟩
    refine ⟨?_, TF.mul_mem hxT hyT⟩
    rw [(hcomm x hxT y hyT).mul_pow, hxq, hyq, mul_one]
  inv_mem' := by
    rintro x ⟨hxq, hxT⟩
    exact ⟨by rw [inv_pow, hxq, inv_one], TF.inv_mem hxT⟩

theorem exists_twFrame_conj_into_torus
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    (E : Subgroup (twistedE6RootGroup K σ)) (hE : IsElemAbelian p E) (hr : p ^ 5 ≤ Nat.card E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (w : WeylGroup TwistTag.E6.tag) (y : twistedE6RootGroup K σ),
      (∀ c, Fr c = c ^ (2 ^ n)) ∧ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      ExcIsLongest TwistTag.E6.tag w ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 = g0 * canonicalRep
        (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w ∧
      ∀ x ∈ E,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((y⁻¹ * x * y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 ∈
          twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
            (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) := by
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hpq
    norm_num at hpq
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpq
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  let M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ := -1
  have hMeq : M = -1 := rfl
  have hpow : M ^ 2 = 1 := by
    rw [hMeq, pow_two]
    simp
  have hev : M.charpoly.eval ((2 ^ n : ℕ) : ℤ) ≠ 0 := by
    rw [hMeq]
    exact ggKGTt_charpoly_neg_one_ne_zero (2 ^ n)
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ,
      ggKGTc_w0 (TwistTag.E6.tag) • x = Matrix.mulVec M (permLattice TwistTag.E6.perm x) := by
    intro x
    rw [hMeq, ggKGTn_w0_smul, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hwlong : ExcIsLongest TwistTag.E6.tag (ggKGTc_w0 (TwistTag.E6.tag)) := by
    intro α hα hpos i
    rw [ggKGTn_w0_smul]
    simp only [Pi.neg_apply, permLattice, Function.comp_apply]
    exact neg_nonpos.mpr (hpos (TwistTag.E6.perm.symm i))
  by_cases hp7 : 7 ≤ p
  · have hord : (Nat.card (twistedE6RootGroup K σ)).factorization p ≤
        ((M.charpoly.eval ((2 ^ n : ℕ) : ℤ)).natAbs).factorization p := by
      rw [hMeq, ggKGTt_charpoly_neg_one_eval_natAbs]
      simp only [Nat.factorization_def _ hp]
      rw [padicValNat_card_twE6_nonsplit σ hp hp5 hK hσ hpq, padicValNat.pow,
        ggKGTt_padicValNat_51840_eq_zero hp hp7, add_zero]
      have hrank : TwistTag.E6.tag.rank = 6 := rfl
      rw [hrank]
    obtain ⟨Fr, hFr, g0, hg0C, hlang, hconj⟩ :=
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.exists_langFrame_twistedE6_sylow
        (ℓ := 2) (f := n) (K := K) (hℓ := Nat.prime_two) (hf := hn1) (hK := hK)
        (σ := σ) (hσ := hσ) (p := p) (hp := hp) (hp3 := by omega) (M := M)
        (v := ggKGTc_w0 (TwistTag.E6.tag)) (hv := hv) (n := 2) (hn0 := by norm_num)
        (hpow := hpow) (hev := hev) (hord := hord)
    obtain ⟨c, hconjE⟩ := hconj E (fun x hx => hE.2 x hx)
    refine ⟨Fr, g0, ggKGTc_w0 (TwistTag.E6.tag), c⁻¹, hFr, hg0C, hwlong, hlang, ?_⟩
    intro x hx
    have hx' := hconjE x hx
    have hy : (((c⁻¹)⁻¹ * x * c⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        ((c * x * c⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hy]
    obtain ⟨t, htT, ht⟩ := Subgroup.mem_map.1 hx'
    rw [← ht]
    change g0⁻¹ * (MulAut.conj g0 t) * g0 ∈ _
    rw [MulAut.conj_apply]
    convert htT using 1
    group
  ·
    have hp_eq : p = 5 := by
      by_contra h
      have hp6 : p = 6 := by omega
      subst hp6
      norm_num at hp
    have h5dvd : 5 ∣ 2 ^ n + 1 := by rw [← hp_eq]; exact hpq
    have h5val : padicValNat p 51840 = 1 := by
      rw [hp_eq]
      rw [show (51840 : ℕ) = 5 ^ 1 * 10368 by norm_num,
        padicValNat_base_pow_mul (p := 5) (n := 10368) (by norm_num) (by norm_num) 1,
        padicValNat.eq_zero_of_not_dvd (p := 5) (n := 10368) (by norm_num)]
    have hRfact : (Nat.card (twistedE6RootGroup K σ)).factorization p =
        6 * padicValNat p (2 ^ n + 1) + 1 := by
      rw [Nat.factorization_def _ hp, padicValNat_card_twE6_nonsplit σ hp hp5 hK hσ hpq, h5val]
    have hord' : (Nat.card (twistedE6RootGroup K σ)).factorization p ≤
        ((M.charpoly.eval ((2 ^ n : ℕ) : ℤ)).natAbs).factorization p + 1 := by
      rw [hMeq, ggKGTt_charpoly_neg_one_eval_natAbs]
      simp only [Nat.factorization_def _ hp]
      rw [padicValNat_card_twE6_nonsplit σ hp hp5 hK hσ hpq, padicValNat.pow]
      have hrank : TwistTag.E6.tag.rank = 6 := rfl
      rw [hrank, h5val]
    obtain ⟨Fr, hFr, g0, hg0C, hlang, hconj⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_langFrame_twistedE6
        (ℓ := 2) (f := n) (K := K) (hℓ := Nat.prime_two) (hf := hn1) (hK := hK)
        (σ := σ) (hσ := hσ) (p := p) (hp := hp) (hp3 := by omega) (M := M)
        (v := ggKGTc_w0 (TwistTag.E6.tag)) (hv := hv) (n := 2) (hn0 := by norm_num)
        (hpow := hpow) (hev := hev) (hord := hord')
    let nT : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
        (ggKGTc_w0 (TwistTag.E6.tag))
    let ΦT : ModGL TwistTag.E6.tag (AlgebraicClosure K) →* ModGL TwistTag.E6.tag
      (AlgebraicClosure K) :=
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr
    let Tor : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) := twistedTorusOf nT ΦT
    let Y : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
      (MulAut.conj (g0⁻¹)).toMonoidHom.comp
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (twistedE6RootGroup K σ).subtype)
    have hYapp : ∀ z : twistedE6RootGroup K σ,
        Y z = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K)
          * g0 := by
      intro z
      simp [Y, MulAut.conj_apply]
    have hYinj : Function.Injective Y :=
      (MulAut.conj (g0⁻¹)).injective.comp
        ((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
          (Subgroup.subtype_injective _))
    let TF : Subgroup (twistedE6RootGroup K σ) := Tor.comap Y
    have hTF_mem : ∀ x : twistedE6RootGroup K σ,
        x ∈ TF ↔ g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0 ∈ Tor := by
      intro x
      rw [Subgroup.mem_comap, hYapp]
    have hcommTF : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y := by
      intro x hx y hy
      show x * y = y * x
      apply hYinj
      rw [map_mul, map_mul]
      exact (ggKGTt_torus_commute nT ΦT ((Subgroup.mem_comap).1 hx) ((Subgroup.mem_comap).1 hy)).eq
    let Q : Subgroup (twistedE6RootGroup K σ) := ggKGTt_pTorsion p TF hcommTF
    have hQpg : IsPGroup p Q := ggKGTt_pTorsion_isPGroup hcommTF
    have hQle : Q ≤ TF := ggKGTt_pTorsion_le hcommTF
    let ET : Subgroup (twistedE6RootGroup K σ) := ggKGTt_pTorsionSub 5 TF hcommTF
    have hET_mem : ∀ x : twistedE6RootGroup K σ,
        x ∈ ET ↔ x ^ 5 = 1 ∧
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0
            ∈ Tor := by
      intro x
      change x ^ 5 = 1 ∧ x ∈ TF ↔
        x ^ 5 = 1 ∧ g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0 ∈ Tor
      rw [hTF_mem]
    have hET_mem' : ∀ x : twistedE6RootGroup K σ,
        x ∈ ET ↔ x ^ 5 = 1 ∧
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0 ∈
            twistedTorusOf
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
              (ggKGTc_w0 (TwistTag.E6.tag)))
              (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) := by
      intro x
      rw [hET_mem]
    obtain ⟨S⟩ : Nonempty (Sylow p (twistedE6RootGroup K σ)) := Sylow.nonempty
    obtain ⟨c, E'', hE''le_S, hE''card, hE''conj⟩ :=
      hconj (S : Subgroup (twistedE6RootGroup K σ)) S.isPGroup'
    let P0 : Subgroup (twistedE6RootGroup K σ) := E''.map (MulAut.conj c).toMonoidHom
    have hP0TF : P0 ≤ TF := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hTF_mem]
      obtain ⟨t, htT, ht⟩ := Subgroup.mem_map.1 (hE''conj x hx)
      have hcx : (MulEquiv.toMonoidHom (MulAut.conj c)) x = c * x * c⁻¹ := MulAut.conj_apply c x
      rw [hcx, ← ht]
      convert htT using 1
      rw
        [show (MulEquiv.toMonoidHom (MulAut.conj g0)) t = g0 * t * g0⁻¹ from MulAut.conj_apply g0 t]
      group
    have hE''pg : IsPGroup p E'' := by
      have hSp : IsPGroup p (S : Subgroup (twistedE6RootGroup K σ)) := S.isPGroup'
      intro x
      obtain ⟨k, hk⟩ := hSp ⟨x.1, hE''le_S x.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hP0pg : IsPGroup p P0 := hE''pg.map (MulAut.conj c).toMonoidHom
    have hScard : Nat.card (S : Subgroup (twistedE6RootGroup K σ)) =
        p ^ (6 * padicValNat p (2 ^ n + 1) + 1) := by
      rw [Sylow.card_eq_multiplicity, hRfact]
    have hE''card' : p ^ (6 * padicValNat p (2 ^ n + 1)) ≤ Nat.card E'' := by
      have h := hE''card
      rw [hScard, pow_succ'] at h
      exact Nat.le_of_mul_le_mul_left h hp.pos
    have hP0card : p ^ (6 * padicValNat p (2 ^ n + 1)) ≤ Nat.card P0 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact hE''card'
    have hP0Q : P0 ≤ Q := by
      intro x hx
      refine ⟨hP0TF hx, ?_⟩
      obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hP0pg ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    obtain ⟨P, hQ_le_P⟩ := IsPGroup.exists_le_sylow hQpg
    have hPpg : IsPGroup p (P : Subgroup (twistedE6RootGroup K σ)) := Sylow.isPGroup' P
    have hPcard : Nat.card (P : Subgroup (twistedE6RootGroup K σ)) =
        p ^ (6 * padicValNat p (2 ^ n + 1) + padicValNat p 51840) := by
      rw [Sylow.card_eq_multiplicity, Nat.factorization_def _ hp,
        padicValNat_card_twE6_nonsplit σ hp hp5 hK hσ hpq]
    have hPcard5 : Nat.card (P : Subgroup (twistedE6RootGroup K σ)) =
        5 ^ (6 * padicValNat p (2 ^ n + 1) + 1) := by
      rw [hPcard, h5val, hp_eq]
    obtain ⟨Q', hEQ'⟩ := IsPGroup.exists_le_sylow hE.isPGroup
    haveI : MulAction.IsPretransitive (twistedE6RootGroup K σ)
        (Sylow p (twistedE6RootGroup K σ)) := Sylow.isPretransitive_of_finite
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (twistedE6RootGroup K σ) P Q'
    have hQ'map : (Q' : Subgroup (twistedE6RootGroup K σ)) =
        (P : Subgroup (twistedE6RootGroup K σ)).map (MulAut.conj y).toMonoidHom := by
      rw [← hy, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hconjE : ∀ x ∈ E, y⁻¹ * x * y ∈ (P : Subgroup (twistedE6RootGroup K σ)) := by
      intro x hx
      have hxQ' : x ∈ (Q' : Subgroup (twistedE6RootGroup K σ)) := hEQ' hx
      rw [hQ'map, Subgroup.mem_map] at hxQ'
      obtain ⟨z, hzP, hzx⟩ := hxQ'
      have hzx' : y * z * y⁻¹ = x := by simpa [MulAut.conj_apply] using hzx
      have hz : y⁻¹ * x * y = z := by rw [← hzx']; group
      rwa [hz]
    let E' : Subgroup (twistedE6RootGroup K σ) := E.map (MulAut.conj y⁻¹).toMonoidHom
    have hE'_P : E' ≤ (P : Subgroup (twistedE6RootGroup K σ)) := by
      intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      simpa [MulAut.conj_apply] using hconjE e he
    have hE'card : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
    have hE'el : IsElemAbelian p E' := IsElemAbelian.map hE (MulAut.conj y⁻¹).toMonoidHom
    have hfinal : E' ≤ TF → ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
        (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
        (w : WeylGroup TwistTag.E6.tag) (y : twistedE6RootGroup K σ),
        (∀ c, Fr c = c ^ (2 ^ n)) ∧ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
        ExcIsLongest TwistTag.E6.tag w ∧
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w ∧
        ∀ x ∈ E,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((y⁻¹ * x * y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 ∈
            twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
              (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) := by
      intro hE'TF
      refine ⟨Fr, g0, ggKGTc_w0 (TwistTag.E6.tag), y, hFr, hg0C, hwlong, hlang, fun x hx => ?_⟩
      have hxE' : (MulAut.conj y⁻¹).toMonoidHom x ∈ E' := Subgroup.mem_map_of_mem _ hx
      have hxTF : y⁻¹ * x * y ∈ TF := by
        rw [show (MulAut.conj y⁻¹).toMonoidHom x = y⁻¹ * x * y by simp [MulAut.conj_apply]] at hxE'
        exact hE'TF hxE'
      exact (hTF_mem _).1 hxTF
    let T : Subgroup (twistedE6RootGroup K σ) := (P : Subgroup (twistedE6RootGroup K σ)) ⊓ TF
    have hT_le_P : T ≤ (P : Subgroup (twistedE6RootGroup K σ)) := inf_le_left
    have hT_le_TF : T ≤ TF := inf_le_right
    have hQ_le_T : Q ≤ T := le_inf hQ_le_P hQle
    have hP0T : P0 ≤ T := hP0Q.trans hQ_le_T
    have hTcard_ge : p ^ (6 * padicValNat p (2 ^ n + 1)) ≤ Nat.card T :=
      le_trans hP0card (Subgroup.card_le_of_le hP0T)
    have hET_le_Q : ET ≤ Q := by
      intro x hx
      have hx' := (hET_mem x).1 hx
      have hxTF : x ∈ TF := (hTF_mem x).2 hx'.2
      refine ⟨hxTF, ⟨1, ?_⟩⟩
      rw [pow_one, hp_eq]
      exact hx'.1
    have hET_le_T : ET ≤ T := hET_le_Q.trans hQ_le_T
    have hTcard_ge5 : 5 ^ (6 * padicValNat p (2 ^ n + 1)) ≤ Nat.card T := by
      rw [← hp_eq]; exact hTcard_ge
    by_cases hTP : T = (P : Subgroup (twistedE6RootGroup K σ))
    · exact hfinal (hE'_P.trans (hTP ▸ hT_le_TF))
    · have hrel_mul : (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).index * Nat.card T =
          Nat.card (P : Subgroup (twistedE6RootGroup K σ)) := by
        have h := (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).card_mul_index
        rw [show Nat.card (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))) = Nat.card T from
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_P).toEquiv] at h
        rw [mul_comm]
        exact h
      have hidx_dvd : (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).index ∣
          5 ^ (6 * padicValNat p (2 ^ n + 1) + 1) :=
        ⟨Nat.card T, (hrel_mul.trans hPcard5).symm⟩
      obtain ⟨k, hk_le, hk_eq⟩ :=
        (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hidx_dvd
      have hidx_ne1 : (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).index ≠ 1 := by
        intro h1
        apply hTP
        have hle' : (P : Subgroup (twistedE6RootGroup K σ)) ≤ T := by
          have htop : T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ)) = ⊤ :=
            Subgroup.index_eq_one.1 h1
          intro p' hp'
          have hp'' : (⟨p', hp'⟩ : (P : Subgroup (twistedE6RootGroup K σ))) ∈
              T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ)) := by rw [htop]; trivial
          exact (Subgroup.mem_subgroupOf).1 hp''
        exact le_antisymm hT_le_P hle'
      have hk_ne0 : k ≠ 0 := by
        intro hk0
        apply hidx_ne1
        rw [hk_eq, hk0, pow_zero]
      have hk_le1 : k ≤ 1 := by
        have hmul := hrel_mul
        rw [hk_eq, hPcard5] at hmul
        have hD_pos : 0 < 5 ^ (6 * padicValNat p (2 ^ n + 1)) := by positivity
        have h2 : 5 ^ k * 5 ^ (6 * padicValNat p (2 ^ n + 1)) ≤
            5 * 5 ^ (6 * padicValNat p (2 ^ n + 1)) := by
          calc 5 ^ k * 5 ^ (6 * padicValNat p (2 ^ n + 1))
              ≤ 5 ^ k * Nat.card T := Nat.mul_le_mul_left _ hTcard_ge5
            _ = 5 ^ (6 * padicValNat p (2 ^ n + 1) + 1) := hmul
            _ = 5 * 5 ^ (6 * padicValNat p (2 ^ n + 1)) := by
                rw [pow_add, pow_one]; ring
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1
          (Nat.le_of_mul_le_mul_right h2 hD_pos)
      have hk1 : k = 1 := by omega
      have hidx5 : (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).index = 5 := by
        rw [hk_eq, hk1, pow_one]
      have hTPrel : T.relIndex (P : Subgroup (twistedE6RootGroup K σ)) = 5 := by
        rw [show T.relIndex (P : Subgroup (twistedE6RootGroup K σ)) =
              (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).index from rfl, hidx5]
      have hTnorm : (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).Normal := by
        apply Subgroup.normal_of_index_eq_minFac_card
        rw [hidx5, hPcard5,
          Nat.pow_minFac (by omega : 6 * padicValNat p (2 ^ n + 1) + 1 ≠ 0)]
        norm_num
      have hPnormT : (P : Subgroup (twistedE6RootGroup K σ)) ≤
          Subgroup.normalizer (T : Set (twistedE6RootGroup K σ)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hT_le_P).1 hTnorm
      by_cases hE'T : E' ≤ T
      · exact hfinal (hE'T.trans hT_le_TF)
      · obtain ⟨u, huE', huT⟩ := Set.not_subset.1 hE'T
        have huP : u ∈ (P : Subgroup (twistedE6RootGroup K σ)) := hE'_P huE'
        have hnormT : u ∈ Subgroup.normalizer (T : Set (twistedE6RootGroup K σ)) := hPnormT huP
        have hstep : ∀ v : twistedE6RootGroup K σ,
            v ∈ Subgroup.normalizer (T : Set (twistedE6RootGroup K σ)) →
            ∀ e : twistedE6RootGroup K σ, e ∈ ET → v * e * v⁻¹ ∈ ET := by
          intro v hv e he
          have heT : e ∈ T := hET_le_T he
          have hmemT : v * e * v⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hv e).1 heT
          have hepow : e ^ 5 = 1 := ((hET_mem e).1 he).1
          refine (hET_mem (v * e * v⁻¹)).2 ⟨?_, (hTF_mem _).1 (hT_le_TF hmemT)⟩
          calc (v * e * v⁻¹) ^ 5 = v * e ^ 5 * v⁻¹ := by
                rw [show v * e * v⁻¹ = (MulAut.conj v).toMonoidHom e from rfl]
                exact ((map_pow (MulAut.conj v).toMonoidHom e 5)).symm
            _ = 1 := by rw [hepow]; group
        have hETnorm : u ∈ Subgroup.normalizer (ET : Set (twistedE6RootGroup K σ)) := by
          rw [Subgroup.mem_normalizer_iff]
          intro e
          constructor
          · exact hstep u hnormT e
          · intro he
            have h := hstep u⁻¹
              ((Subgroup.normalizer (T : Set (twistedE6RootGroup K σ))).inv_mem hnormT)
              (u * e * u⁻¹) he
            simpa [mul_assoc] using h
        have hu5T : u ^ 5 ∈ T := by
          haveI : (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ))).Normal := hTnorm
          have hmem := Subgroup.pow_index_mem (T.subgroupOf (P : Subgroup (twistedE6RootGroup K σ)))
            (⟨u, huP⟩ : (P : Subgroup (twistedE6RootGroup K σ)))
          rw [hidx5] at hmem
          exact (Subgroup.mem_subgroupOf).1 (by simpa using hmem)
        have hu5cent : u ^ 5 ∈ Subgroup.centralizer (ET : Set (twistedE6RootGroup K σ)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact ((hcommTF (u ^ 5) (hT_le_TF hu5T) e (hT_le_TF (hET_le_T he))).eq).symm
        have hnc : u ∉ Subgroup.centralizer (ET : Set (twistedE6RootGroup K σ)) := by
          intro huc
          let F : TwE6Frame K σ n p ET :=
            { Fr := Fr, v := ggKGTc_w0 (TwistTag.E6.tag), g0 := g0, fr_eq := hFr,
              g0_mem := hg0C, lang := hlang, mem_iff := fun x => by rw [hET_mem, hp_eq] }
          have hwcent : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨
              (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v) := Or.inr ⟨hpq, hwlong⟩
          have hcent := ggKGTwE6_centralizer_eq hK hσ hp hp5 F hwcent u
          have hmem : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (u : ModGL TwistTag.E6.tag K) * g0 ∈ Tor := by
            have h := hcent.1 huc
            change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (u : ModGL TwistTag.E6.tag K) * g0 ∈ Tor
            exact h
          have huTF : u ∈ TF := (hTF_mem u).2 hmem
          have huQ : u ∈ Q := by
            refine ⟨huTF, ?_⟩
            obtain ⟨m, hm⟩ := IsPGroup.exists_pow_pow_eq_one hPpg ⟨u, huP⟩
            exact ⟨m, by simpa using congrArg Subtype.val hm⟩
          exact huT (hQ_le_T huQ)
        have hfix := card_fixed_le_five_cube_tw σ hK hσ h5dvd Fr hFr g0 hg0C
          (ggKGTc_w0 (TwistTag.E6.tag)) hwlong hlang hET_mem' hETnorm hu5cent hnc
        have hcard_le : Nat.card ↥(E' ⊓ T) ≤ 5 ^ 3 := by
          have hval : ∀ x : ↥(E' ⊓ T),
              (x : twistedE6RootGroup K σ) ∈ ET ∧
                u * (x : twistedE6RootGroup K σ) = (x : twistedE6RootGroup K σ) * u := by
            intro x
            refine ⟨(hET_mem (x : twistedE6RootGroup K σ)).2 ⟨?_, ?_⟩, ?_⟩
            · have h := hE'el.2 (x : twistedE6RootGroup K σ) x.2.1
              rwa [hp_eq] at h
            · exact (hTF_mem _).1 (hT_le_TF x.2.2)
            · have hcomm : (x : twistedE6RootGroup K σ) * u = u * (x : twistedE6RootGroup K σ) := by
                have := (isMulCommutative_iff.1 hE'el.1)
                  ⟨(x : twistedE6RootGroup K σ), x.2.1⟩ ⟨u, huE'⟩
                simpa using congrArg Subtype.val this
              exact hcomm.symm
          have hinj : Nat.card ↥(E' ⊓ T) ≤
              Nat.card {e : twistedE6RootGroup K σ // e ∈ ET ∧ u * e = e * u} :=
            Nat.card_le_card_of_injective
              (fun x : ↥(E' ⊓ T) =>
                (⟨(x : twistedE6RootGroup K σ), (hval x).1, (hval x).2⟩ :
                  {e : twistedE6RootGroup K σ // e ∈ ET ∧ u * e = e * u}))
              (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
          exact hinj.trans hfix
        have hrel_le : (E' ⊓ T).relIndex E' ≤ 5 := by
          have h1 : (E' ⊓ T).relIndex E' = T.relIndex E' := by
            rw [inf_comm, Subgroup.inf_relIndex_right]
          rw [h1]
          have hPpos : T.relIndex (P : Subgroup (twistedE6RootGroup K σ)) ≠ 0 := by
            rw [hTPrel]; norm_num
          have h2 := Subgroup.relIndex_le_of_le_right (H := T) (K := E')
            (L := (P : Subgroup (twistedE6RootGroup K σ))) hE'_P hPpos
          rwa [hTPrel] at h2
        have hcard_index : Nat.card E' ≤ 5 * Nat.card ↥(E' ⊓ T) := by
          have hmul := Subgroup.relIndex_mul_card (H := E' ⊓ T) (K := E')
          have hmul' : (E' ⊓ T).relIndex E' * Nat.card ↥(E' ⊓ T) = Nat.card E' := by
            rw [show (E' ⊓ T) ⊓ E' = E' ⊓ T from inf_eq_left.2 inf_le_left] at hmul
            exact hmul
          rw [← hmul']
          exact Nat.mul_le_mul_right _ hrel_le
        have hE'card_le : Nat.card E' ≤ 5 ^ 4 := by
          calc Nat.card E' ≤ 5 * Nat.card ↥(E' ⊓ T) := hcard_index
            _ ≤ 5 * 5 ^ 3 := Nat.mul_le_mul_left 5 hcard_le
            _ = 5 ^ 4 := by norm_num
        have hr5 : 5 ^ 5 ≤ Nat.card E := by rw [hp_eq] at hr; exact hr
        have hb : 5 ^ 5 ≤ Nat.card E' := by rw [hE'card]; exact hr5
        exact absurd (hb.trans hE'card_le) (by norm_num)

end ExcTwE6Nons

end CFSG.StandardType

end
