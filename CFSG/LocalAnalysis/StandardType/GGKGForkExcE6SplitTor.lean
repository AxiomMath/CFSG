module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitTorus
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitOrders
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitFix

public section

namespace CFSG.StandardType

namespace ExcE6Split

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE

private lemma ggKGSy_mul_pow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x y : G}
    (hcomm : Commute x y) {a b : ℕ} (hx : x ^ p ^ a = 1) (hy : y ^ p ^ b = 1) :
    (x * y) ^ p ^ (a + b) = 1 := by
  have hx' : x ^ p ^ (a + b) = 1 := by
    rw [show p ^ (a + b) = p ^ a * p ^ b from pow_add p a b, pow_mul, hx, one_pow]
  have hy' : y ^ p ^ (a + b) = 1 := by
    rw [show p ^ (a + b) = p ^ b * p ^ a by rw [pow_add, mul_comm], pow_mul, hy, one_pow]
  rw [hcomm.mul_pow (p ^ (a + b)), hx', hy', mul_one]

private lemma ggKGSy_inv_pow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x : G} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x⁻¹ ^ p ^ k = 1 := by
  rw [inv_pow, hx, inv_one]

private def ggKGSy_pTorsion {G : Type*} [Group G] (p : ℕ) (TF : Subgroup G)
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) : Subgroup G where
  carrier := {x | x ∈ TF ∧ ∃ k : ℕ, x ^ p ^ k = 1}
  one_mem' := ⟨TF.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxT, k, hxk⟩ ⟨hyT, l, hyl⟩
    exact ⟨TF.mul_mem hxT hyT, k + l,
      ggKGSy_mul_pow_pow_eq_one (hcomm x hxT y hyT) hxk hyl⟩
  inv_mem' := by
    rintro x ⟨hxT, k, hxk⟩
    exact ⟨TF.inv_mem hxT, k, ggKGSy_inv_pow_pow_eq_one hxk⟩

private lemma ggKGSy_pTorsion_le {G : Type*} [Group G] {p : ℕ} {TF : Subgroup G}
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) :
    ggKGSy_pTorsion p TF hcomm ≤ TF := fun _ hx => hx.1

private lemma ggKGSy_pTorsion_isPGroup {G : Type*} [Group G] {p : ℕ} {TF : Subgroup G}
    (hcomm : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y) :
    IsPGroup p (ggKGSy_pTorsion p TF hcomm) := by
  intro x
  obtain ⟨-, k, hk⟩ := x.2
  exact ⟨k, Subtype.ext hk⟩

private def ggKGSy_pTorsionSub {G : Type*} [Group G] (q : ℕ) (TF : Subgroup G)
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

private lemma ggKGSy_commute_of_mem_torus
    {K : Type} [Field K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    {x y : adjointGroup .E6 K}
    (hx : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) ∈
        twistedTorusOf (1 : ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr)))
    (hy : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) ∈
        twistedTorusOf (1 : ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr))) :
    Commute x y := by
  have hx' : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) ∈
      diagonalGroup :=
    torusGroup_le_diagonalGroup (mem_twistedTorusOf.1 hx).1
  have hy' : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) ∈
      diagonalGroup :=
    torusGroup_le_diagonalGroup (mem_twistedTorusOf.1 hy).1
  have hcomm : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) :=
    mul_comm_of_mem_diagonalGroup hx' hy'
  show x * y = y * x
  apply Subtype.ext
  refine baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hcomm]

theorem exists_conj_into_splitTorus
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian p E) (hr : p ^ 6 ≤ Nat.card E) :
    ∃ y : adjointGroup .E6 K, ∀ x ∈ E,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y⁻¹ * x * y : adjointGroup .E6 K) : ModGL .E6 K) ∈
        twistedTorusOf (1 : ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr)) := by
  classical
  let L := AlgebraicClosure K
  let TF : Subgroup (adjointGroup .E6 K) :=
    (twistedTorusOf (1 : ModGL .E6 L) (Units.map (entrywiseHom Fr))).comap
      ((baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype)
  have hTF_mem : ∀ x : adjointGroup .E6 K,
      x ∈ TF ↔ baseChangeGL (algebraMap K L) (x : ModGL .E6 K) ∈
        twistedTorusOf (1 : ModGL .E6 L) (Units.map (entrywiseHom Fr)) :=
    fun _ => Iff.rfl
  have hcommTF : ∀ x ∈ TF, ∀ y ∈ TF, Commute x y := fun x hx y hy =>
    ggKGSy_commute_of_mem_torus Fr ((hTF_mem x).1 hx) ((hTF_mem y).1 hy)
  let Q : Subgroup (adjointGroup .E6 K) := ggKGSy_pTorsion p TF hcommTF
  have hQpg : IsPGroup p Q := ggKGSy_pTorsion_isPGroup hcommTF
  have hQle : Q ≤ TF := ggKGSy_pTorsion_le hcommTF
  let ET : Subgroup (adjointGroup .E6 K) := ggKGSy_pTorsionSub 5 TF hcommTF
  have hET_mem : ∀ x : adjointGroup .E6 K, x ∈ ET ↔ x ^ 5 = 1 ∧
      baseChangeGL (algebraMap K L) (x : ModGL .E6 K) ∈
        twistedTorusOf (1 : ModGL .E6 L) (Units.map (entrywiseHom Fr)) :=
    fun _ => Iff.rfl
  obtain ⟨P0, hP0pg, hP0card, hP0TF⟩ :=
    exists_pgroup_le_splitTorus (K := K) (p := p) hp hp5 Fr hFr
  have hP0Q : P0 ≤ Q := by
    intro x hx
    refine ⟨hP0TF x hx, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hP0pg ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨P, hQ_le_P⟩ := IsPGroup.exists_le_sylow hQpg
  haveI : Fact p.Prime := ⟨hp⟩
  have hPpg : IsPGroup p (P : Subgroup (adjointGroup .E6 K)) := Sylow.isPGroup' P
  have hPcard : Nat.card (P : Subgroup (adjointGroup .E6 K)) =
      p ^ (6 * padicValNat p (Nat.card K - 1) + padicValNat p 51840) := by
    have h1 := Sylow.card_eq_multiplicity P
    rw [Nat.factorization_def (Nat.card (adjointGroup .E6 K)) hp,
      padicValNat_card_adjointGroup_split (K := K) (p := p) hp hp5 hpq] at h1
    exact h1
  obtain ⟨Q', hEQ'⟩ := IsPGroup.exists_le_sylow hE.isPGroup
  haveI : MulAction.IsPretransitive (adjointGroup .E6 K) (Sylow p (adjointGroup .E6 K)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (adjointGroup .E6 K) P Q'
  have hQ'map : (Q' : Subgroup (adjointGroup .E6 K)) =
      (P : Subgroup (adjointGroup .E6 K)).map (MulAut.conj y).toMonoidHom := by
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hconjE : ∀ x ∈ E, y⁻¹ * x * y ∈ (P : Subgroup (adjointGroup .E6 K)) := by
    intro x hx
    have hxQ' : x ∈ (Q' : Subgroup (adjointGroup .E6 K)) := hEQ' hx
    rw [hQ'map, Subgroup.mem_map] at hxQ'
    obtain ⟨z, hzP, hzx⟩ := hxQ'
    have hzx' : y * z * y⁻¹ = x := by simpa [MulAut.conj_apply] using hzx
    have hz : y⁻¹ * x * y = z := by rw [← hzx']; group
    rwa [hz]
  let E' : Subgroup (adjointGroup .E6 K) := E.map (MulAut.conj y⁻¹).toMonoidHom
  have hE'_P : E' ≤ (P : Subgroup (adjointGroup .E6 K)) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    simpa [MulAut.conj_apply] using hconjE e he
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  have hE'el : IsElemAbelian p E' := IsElemAbelian.map hE (MulAut.conj y⁻¹).toMonoidHom
  have hfinal : E' ≤ TF → ∃ y : adjointGroup .E6 K, ∀ x ∈ E,
      baseChangeGL (algebraMap K L) ((y⁻¹ * x * y : adjointGroup .E6 K) : ModGL .E6 K) ∈
        twistedTorusOf (1 : ModGL .E6 L) (Units.map (entrywiseHom Fr)) := by
    intro hE'TF
    refine ⟨y, fun x hx => ?_⟩
    have hxE' : (MulAut.conj y⁻¹).toMonoidHom x ∈ E' := Subgroup.mem_map_of_mem _ hx
    have hxE'' : y⁻¹ * x * y ∈ E' := by simpa [MulAut.conj_apply] using hxE'
    exact (hTF_mem _).1 (hE'TF hxE'')
  let T : Subgroup (adjointGroup .E6 K) := (P : Subgroup (adjointGroup .E6 K)) ⊓ TF
  have hT_le_P : T ≤ (P : Subgroup (adjointGroup .E6 K)) := inf_le_left
  have hT_le_TF : T ≤ TF := inf_le_right
  have hQ_le_T : Q ≤ T := le_inf hQ_le_P hQle
  have hP0T : P0 ≤ T := hP0Q.trans hQ_le_T
  have hTcard_ge : p ^ (6 * padicValNat p (Nat.card K - 1)) ≤ Nat.card T := by
    rw [← hP0card]
    exact Subgroup.card_le_of_le hP0T
  by_cases hp_eq : p = 5
  · have hp5eq : p = 5 := hp_eq
    have hpad5 : padicValNat 5 51840 = 1 := by
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have h : 51840 = 5 * 10368 := by norm_num
      rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self]
      have hz : padicValNat 5 10368 = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        norm_num
      rw [hz, add_zero]
    have hPcard5 : Nat.card (P : Subgroup (adjointGroup .E6 K)) =
        5 ^ (6 * padicValNat p (Nat.card K - 1) + 1) := by
      rw [hPcard, hp5eq, hpad5]
    have hET_le_Q : ET ≤ Q := by
      intro x hx
      have hx' := (hET_mem x).1 hx
      have hxTF : x ∈ TF := (hTF_mem x).2 hx'.2
      refine ⟨hxTF, ⟨1, ?_⟩⟩
      rw [pow_one, hp5eq]
      exact hx'.1
    have hET_le_T : ET ≤ T := hET_le_Q.trans hQ_le_T
    have hTcard_ge5 : 5 ^ (6 * padicValNat p (Nat.card K - 1)) ≤ Nat.card T := by
      rw [← hp5eq]; exact hTcard_ge
    by_cases hTP : T = (P : Subgroup (adjointGroup .E6 K))
    · exact hfinal (hE'_P.trans (hTP ▸ hT_le_TF))
    · have hrel_mul : (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).index * Nat.card T =
          Nat.card (P : Subgroup (adjointGroup .E6 K)) := by
        have h := (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).card_mul_index
        rw [show Nat.card (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))) = Nat.card T from
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_P).toEquiv] at h
        rw [mul_comm]
        exact h
      have hidx_dvd : (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).index ∣
          5 ^ (6 * padicValNat p (Nat.card K - 1) + 1) :=
        ⟨Nat.card T, (hrel_mul.trans hPcard5).symm⟩
      obtain ⟨k, hk_le, hk_eq⟩ :=
        (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hidx_dvd
      have hidx_ne1 : (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).index ≠ 1 := by
        intro h1
        apply hTP
        have hle' : (P : Subgroup (adjointGroup .E6 K)) ≤ T := by
          have htop : T.subgroupOf (P : Subgroup (adjointGroup .E6 K)) = ⊤ :=
            Subgroup.index_eq_one.1 h1
          intro p hp
          have hp' : (⟨p, hp⟩ : (P : Subgroup (adjointGroup .E6 K))) ∈
              T.subgroupOf (P : Subgroup (adjointGroup .E6 K)) := by rw [htop]; trivial
          exact (Subgroup.mem_subgroupOf).1 hp'
        exact le_antisymm hT_le_P hle'
      have hk_ne0 : k ≠ 0 := by
        intro hk0
        apply hidx_ne1
        rw [hk_eq, hk0, pow_zero]
      have hk_le1 : k ≤ 1 := by
        have hmul := hrel_mul
        rw [hk_eq, hPcard5] at hmul
        have hD_pos : 0 < 5 ^ (6 * padicValNat p (Nat.card K - 1)) := by positivity
        have h2 : 5 ^ k * 5 ^ (6 * padicValNat p (Nat.card K - 1)) ≤
            5 * 5 ^ (6 * padicValNat p (Nat.card K - 1)) := by
          calc 5 ^ k * 5 ^ (6 * padicValNat p (Nat.card K - 1))
              ≤ 5 ^ k * Nat.card T := Nat.mul_le_mul_left _ hTcard_ge5
            _ = 5 ^ (6 * padicValNat p (Nat.card K - 1) + 1) := hmul
            _ = 5 * 5 ^ (6 * padicValNat p (Nat.card K - 1)) := by
                rw [pow_add, pow_one]; ring
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1
          (Nat.le_of_mul_le_mul_right h2 hD_pos)
      have hk1 : k = 1 := by omega
      have hidx5 : (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).index = 5 := by
        rw [hk_eq, hk1, pow_one]
      have hTPrel : T.relIndex (P : Subgroup (adjointGroup .E6 K)) = 5 := by
        rw [show T.relIndex (P : Subgroup (adjointGroup .E6 K)) =
              (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).index from rfl, hidx5]
      have hTnorm : (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).Normal := by
        apply Subgroup.normal_of_index_eq_minFac_card
        rw [hidx5, hPcard5,
          Nat.pow_minFac (by omega : 6 * padicValNat p (Nat.card K - 1) + 1 ≠ 0)]
        norm_num
      have hPnormT : (P : Subgroup (adjointGroup .E6 K)) ≤
          Subgroup.normalizer (T : Set (adjointGroup .E6 K)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hT_le_P).1 hTnorm
      by_cases hE'T : E' ≤ T
      · exact hfinal (hE'T.trans hT_le_TF)
      · obtain ⟨u, huE', huT⟩ := Set.not_subset.1 hE'T
        have huP : u ∈ (P : Subgroup (adjointGroup .E6 K)) := hE'_P huE'
        have hnormT : u ∈ Subgroup.normalizer (T : Set (adjointGroup .E6 K)) := hPnormT huP
        have hstep : ∀ v : adjointGroup .E6 K,
            v ∈ Subgroup.normalizer (T : Set (adjointGroup .E6 K)) →
            ∀ e : adjointGroup .E6 K, e ∈ ET → v * e * v⁻¹ ∈ ET := by
          intro v hv e he
          have heT : e ∈ T := hET_le_T he
          have hmemT : v * e * v⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hv e).1 heT
          have hepow : e ^ 5 = 1 := ((hET_mem e).1 he).1
          refine (hET_mem (v * e * v⁻¹)).2
            ⟨?_, (hTF_mem _).1 (hT_le_TF hmemT)⟩
          calc (v * e * v⁻¹) ^ 5 = v * e ^ 5 * v⁻¹ := by
                rw [show v * e * v⁻¹ = (MulAut.conj v).toMonoidHom e from rfl]
                exact ((map_pow (MulAut.conj v).toMonoidHom e 5)).symm
            _ = 1 := by rw [hepow]; group
        have hETnorm : u ∈ Subgroup.normalizer (ET : Set (adjointGroup .E6 K)) := by
          rw [Subgroup.mem_normalizer_iff]
          intro e
          constructor
          · exact hstep u hnormT e
          · intro he
            have h := hstep u⁻¹
              ((Subgroup.normalizer (T : Set (adjointGroup .E6 K))).inv_mem hnormT)
              (u * e * u⁻¹) he
            simpa [mul_assoc] using h
        have hu5T : u ^ 5 ∈ T := by
          haveI : (T.subgroupOf (P : Subgroup (adjointGroup .E6 K))).Normal := hTnorm
          have hmem := Subgroup.pow_index_mem (T.subgroupOf (P : Subgroup (adjointGroup .E6 K)))
            (⟨u, huP⟩ : (P : Subgroup (adjointGroup .E6 K)))
          rw [hidx5] at hmem
          exact (Subgroup.mem_subgroupOf).1 (by simpa using hmem)
        have hu5cent : u ^ 5 ∈ Subgroup.centralizer (ET : Set (adjointGroup .E6 K)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact ((hcommTF (u ^ 5) (hT_le_TF hu5T) e (hT_le_TF (hET_le_T he))).eq).symm
        have h5dvd : 5 ∣ Nat.card K - 1 := by rw [← hp5eq]; exact hpq
        have hnc : u ∉ Subgroup.centralizer (ET : Set (adjointGroup .E6 K)) := by
          intro huc
          obtain ⟨F, hFw, hFg0, hFn⟩ :=
            exists_splitFrame (K := K) (p := 5) Fr hFr (ET := ET) hET_mem
          obtain ⟨Fr', hFr', hΦ'⟩ := F.frob
          have hFr'eq : Fr' = Fr := by
            ext c
            rw [hFr' c, hFr c]
          have hΦeq : F.D.Φ = Units.map (entrywiseHom Fr) := by
            ext g
            rw [hΦ' g, hFr'eq]
          have htor : F.D.torus =
              twistedTorusOf (1 : ModGL .E6 L) (Units.map (entrywiseHom Fr)) := by
            show twistedTorusOf F.D.n F.D.Φ = _
            rw [F.n_eq, hFw, canonicalRep_one, hΦeq]
          have hτ : (.E6 : Tag) = .E6 ∨ (.E6 : Tag) = .E7 ∨ (.E6 : Tag) = .E8 ∨
              (.E6 : Tag) = .F4 := Or.inl rfl
          have hwcent : (5 ∣ Nat.card K - 1 ∧ F.w = 1) ∨
              (5 ∣ Nat.card K + 1 ∧ ExcIsLongest .E6 F.w) := Or.inl ⟨h5dvd, hFw⟩
          have hcent := ggKGExc_centralizer_eq (τ := .E6) (K := K) (p := 5) hτ
            (by norm_num : Nat.Prime 5) (by norm_num) (fun _ => le_rfl) F hwcent u
          have hmem : baseChangeGL (algebraMap K L) (u : ModGL .E6 K) ∈ F.D.torus := by
            have h := hcent.1 huc
            rw [hFg0] at h
            simpa using h
          have huTF : u ∈ TF := (hTF_mem u).2 (htor ▸ hmem)
          have huQ : u ∈ Q := by
            refine ⟨huTF, ?_⟩
            obtain ⟨m, hm⟩ := IsPGroup.exists_pow_pow_eq_one hPpg ⟨u, huP⟩
            exact ⟨m, by simpa using congrArg Subtype.val hm⟩
          exact huT (hQ_le_T huQ)
        have hfix := card_fixed_le_five_cube (K := K) Fr hFr h5dvd (ET := ET) hET_mem
          hETnorm hu5cent hnc
        have hcard_le : Nat.card ↥(E' ⊓ T) ≤ 5 ^ 3 := by
          have hval : ∀ x : ↥(E' ⊓ T),
              (x : adjointGroup .E6 K) ∈ ET ∧
                u * (x : adjointGroup .E6 K) = (x : adjointGroup .E6 K) * u := by
            intro x
            refine ⟨(hET_mem (x : adjointGroup .E6 K)).2 ⟨?_, ?_⟩, ?_⟩
            · have h := hE'el.2 (x : adjointGroup .E6 K) x.2.1
              rwa [hp5eq] at h
            · exact (hTF_mem _).1 (hT_le_TF x.2.2)
            · have hcomm : (x : adjointGroup .E6 K) * u = u * (x : adjointGroup .E6 K) := by
                have := (isMulCommutative_iff.1 hE'el.1)
                  ⟨(x : adjointGroup .E6 K), x.2.1⟩ ⟨u, huE'⟩
                simpa using congrArg Subtype.val this
              exact hcomm.symm
          have hinj : Nat.card ↥(E' ⊓ T) ≤
              Nat.card {e : adjointGroup .E6 K // e ∈ ET ∧ u * e = e * u} :=
            Nat.card_le_card_of_injective
              (fun x : ↥(E' ⊓ T) =>
                (⟨(x : adjointGroup .E6 K), (hval x).1, (hval x).2⟩ :
                  {e : adjointGroup .E6 K // e ∈ ET ∧ u * e = e * u}))
              (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
          exact hinj.trans hfix
        have hrel_le : (E' ⊓ T).relIndex E' ≤ 5 := by
          have h1 : (E' ⊓ T).relIndex E' = T.relIndex E' := by
            rw [inf_comm, Subgroup.inf_relIndex_right]
          rw [h1]
          have hPpos : T.relIndex (P : Subgroup (adjointGroup .E6 K)) ≠ 0 := by
            rw [hTPrel]; norm_num
          have h2 := Subgroup.relIndex_le_of_le_right (H := T) (K := E')
            (L := (P : Subgroup (adjointGroup .E6 K))) hE'_P hPpos
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
        have hr5 : 5 ^ 6 ≤ Nat.card E := by rw [← hp5eq]; exact hr
        have hb : 5 ^ 6 ≤ Nat.card E' := by rw [hE'card]; exact hr5
        exact absurd (hb.trans hE'card_le) (by norm_num)
  · have hp5ne : p ≠ 5 := hp_eq
    have hp7 : 7 ≤ p := by
      by_contra h
      have hle : p ≤ 6 := by omega
      have hcases : p = 5 ∨ p = 6 := by omega
      rcases hcases with h5 | h6
      · exact hp5ne h5
      · rw [h6] at hp; norm_num at hp
    have hv : padicValNat p 51840 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hfac : 51840 = 2 ^ 7 * 3 ^ 4 * 5 := by norm_num
      rw [hfac] at hd
      have h2 : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 := by
        rcases hp.dvd_mul.mp hd with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact Or.inl (hp.dvd_of_dvd_pow h)
          · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inr h)
      rcases h2 with h | h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h; omega
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h; omega
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h; omega
    have hPcard7 : Nat.card (P : Subgroup (adjointGroup .E6 K)) =
        p ^ (6 * padicValNat p (Nat.card K - 1)) := by
      rw [hPcard, hv, add_zero]
    have hTeqP : T = (P : Subgroup (adjointGroup .E6 K)) := by
      apply Subgroup.eq_of_le_of_card_ge hT_le_P
      rw [hPcard7]
      exact hTcard_ge
    exact hfinal (hE'_P.trans (hTeqP ▸ hT_le_TF))

end ExcE6Split

end CFSG.StandardType

end
