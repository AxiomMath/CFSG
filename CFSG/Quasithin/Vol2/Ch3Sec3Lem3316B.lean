module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Lv
public import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.RankThree.PartOne.S11d.PSUModel
public import CFSG.Quasithin.EmptyFaithful.S146zRSL
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace L3316

variable {G : Type} [Group G] [Finite G]

section Lift

variable {L : Subgroup G} {Y : Type} [Group Y] [Finite Y]

@[expose] def liftPre (φ : ↥L →* Y) (P : Subgroup Y) : Subgroup G := (P.comap φ).map L.subtype

@[expose] def liftCore (φ : ↥L →* Y) (P : Subgroup Y) : Subgroup G := perfectCore (liftPre φ P)

omit [Finite G] [Finite Y] in
theorem liftPre_le (φ : ↥L →* Y) (P : Subgroup Y) : liftPre φ P ≤ L := Subgroup.map_subtype_le _

omit [Finite G] [Finite Y] in
theorem liftCore_le (φ : ↥L →* Y) (P : Subgroup Y) : liftCore φ P ≤ L :=
  (perfectCore_le _).trans (liftPre_le φ P)

omit [Finite Y] in
theorem liftCore_eq (φ : ↥L →* Y) (P : Subgroup Y) :
    liftCore φ P = (perfectCore (P.comap φ)).map L.subtype := by
  rw [liftCore, liftPre, map_perfectCore]

omit [Finite Y] in
theorem liftCore_perfect (φ : ↥L →* Y) (P : Subgroup Y) :
    ⁅liftCore φ P, liftCore φ P⁆ = liftCore φ P := perfectCore_perfect _

theorem map_perfectCore_comap {φ : ↥L →* Y} (hφ : Function.Surjective φ) (P : Subgroup Y) :
    (perfectCore (P.comap φ)).map φ = perfectCore P := by
  rw [map_perfectCore, Subgroup.map_comap_eq_self_of_surjective hφ]

theorem exists_hom_sl2_of {φ : ↥L →* Y} (hφ : Function.Surjective φ) (hk : IsPGroup 2 ↥φ.ker)
    {P : Subgroup Y} {K : Type} [Field K]
    {g : ↥(perfectCore P) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : Function.Surjective g) (hgk : IsPGroup 2 ↥g.ker) :
    ∃ f : ↥(liftCore φ P) →* Matrix.SpecialLinearGroup (Fin 2) K,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker := by
  let e₀ : ↥(liftCore φ P) ≃* ↥(perfectCore (P.comap φ)) :=
    (MulEquiv.subgroupCongr (liftCore_eq φ P)).trans
      (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm
  let ψ₁ : ↥(perfectCore (P.comap φ)) →* ↥(perfectCore P) :=
    (MulEquiv.subgroupCongr (map_perfectCore_comap hφ P)).toMonoidHom.comp (φ.subgroupMap _)
  have hψ₁ : Function.Surjective ψ₁ :=
    (MulEquiv.subgroupCongr (map_perfectCore_comap hφ P)).surjective.comp
      (φ.subgroupMap_surjective _)
  have hψ₁v : ∀ y, ((ψ₁ y : ↥(perfectCore P)) : Y) = φ (y : ↥L) := fun y => rfl
  refine ⟨(g.comp ψ₁).comp e₀.toMonoidHom, (hg.comp hψ₁).comp e₀.surjective, ?_⟩
  rintro ⟨x, hx⟩
  have h1 : g (ψ₁ (e₀ x)) = 1 := hx
  obtain ⟨a, ha⟩ := hgk ⟨ψ₁ (e₀ x), h1⟩
  have h2 : ψ₁ ((e₀ x) ^ 2 ^ a) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  have h3 : φ (((e₀ x) ^ 2 ^ a : ↥(perfectCore (P.comap φ))) : ↥L) = 1 := by
    rw [← hψ₁v, h2]
    rfl
  obtain ⟨b, hb⟩ := hk ⟨_, h3⟩
  have h4 : ((e₀ x) ^ 2 ^ a) ^ 2 ^ b = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hb
    simpa using this
  refine ⟨a + b, Subtype.ext ?_⟩
  apply e₀.injective
  show e₀ (x ^ 2 ^ (a + b)) = e₀ 1
  rw [show x ^ 2 ^ (a + b) = (x ^ 2 ^ a) ^ 2 ^ b by rw [← pow_mul, ← pow_add], map_pow,
    map_pow, h4, map_one]

theorem exists_hom_sl2 {φ : ↥L →* Y} (hφ : Function.Surjective φ) (hk : IsPGroup 2 ↥φ.ker)
    {P : Subgroup Y} (hP : Rk2.Rank2Levi P) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (n : ℕ),
      Nat.card K = 2 ^ n ∧ 2 ≤ n ∧
      ∃ f : ↥(liftCore φ P) →* Matrix.SpecialLinearGroup (Fin 2) K,
        Function.Surjective f ∧ IsPGroup 2 ↥f.ker := by
  obtain ⟨K, hF, hFin, hCh, n, hK, hn, g, hg, hgk⟩ := hP
  exact ⟨K, hF, hFin, hCh, n, hK, hn, exists_hom_sl2_of hφ hk hg hgk⟩

omit [Finite G] [Finite Y] in
theorem isMaxParabolic2_liftPre {S₀ : Subgroup G} (hS₀ : IsSylowTwoOf S₀ L) {φ : ↥L →* Y}
    (hφ : Function.Surjective φ) {P : Subgroup Y} (hP : P ⋖ ⊤)
    (hN : Subgroup.normalizer (((S₀.subgroupOf L).map φ : Subgroup Y) : Set Y) ≤ P) :
    IsMaxParabolic2 L (liftPre φ P) ∧
      L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ liftPre φ P := by
  have hB : L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ liftPre φ P := by
    rintro x ⟨hxL, hxN⟩
    have hxN' : x ∈ Subgroup.normalizer (S₀ : Set G) := hxN
    refine ⟨⟨x, hxL⟩, hN ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨x, hxL⟩ * s * ⟨x, hxL⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have hs' : (s : G) ∈ S₀ := hs
      show ((⟨x, hxL⟩ * s * ⟨x, hxL⟩⁻¹ : ↥L) : G) ∈ S₀
      exact (Subgroup.mem_normalizer_iff.mp hxN' _).mp hs'
    · rintro ⟨s, hs, hsy⟩
      have hy : y = φ (⟨x, hxL⟩⁻¹ * s * ⟨x, hxL⟩) := by
        rw [map_mul, map_mul, map_inv, hsy]
        group
      rw [hy]
      refine ⟨_, ?_, rfl⟩
      have hs' : (s : G) ∈ S₀ := hs
      show ((⟨x, hxL⟩⁻¹ * s * ⟨x, hxL⟩ : ↥L) : G) ∈ S₀
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN') _).mp hs'
      simpa [mul_assoc] using this
  have hkP : ∀ k : ↥L, φ k = 1 → (k : G) ∈ liftPre φ P := fun k hk =>
    ⟨k, show φ k ∈ P by rw [hk]; exact P.one_mem, rfl⟩
  refine ⟨⟨⟨liftPre_le φ P, S₀, hS₀, hB⟩, fun heq => hP.lt.ne ?_, fun Q hQ hQL hPQ => ?_⟩, hB⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := hφ y
    have hl : (l : G) ∈ liftPre φ P := by rw [heq]; exact l.2
    obtain ⟨l', hl', hll'⟩ := hl
    rw [← Subtype.ext hll']
    exact hl'
  · have hQL' : Q ≤ L := hQ.1
    have hPQ' : P ≤ (Q.subgroupOf L).map φ := by
      intro y hy
      obtain ⟨l, rfl⟩ := hφ y
      exact ⟨l, hPQ ⟨l, hy, rfl⟩, rfl⟩
    rcases hP.eq_or_eq hPQ' le_top with h | h
    · refine le_antisymm (fun x hx => ?_) hPQ
      have hy : φ ⟨x, hQL' hx⟩ ∈ (Q.subgroupOf L).map φ := ⟨⟨x, hQL' hx⟩, hx, rfl⟩
      rw [h] at hy
      exact ⟨⟨x, hQL' hx⟩, hy, rfl⟩
    · exfalso
      apply hQL
      refine le_antisymm hQL' (fun x hx => ?_)
      have hy : φ ⟨x, hx⟩ ∈ (Q.subgroupOf L).map φ := h ▸ Subgroup.mem_top _
      obtain ⟨q, hq, hqx⟩ := hy
      have hk : φ (q⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hqx, inv_mul_cancel]
      have h1 := Q.mul_mem (hq : (q : G) ∈ Q) (hPQ (hkP _ hk))
      simpa using h1

end Lift

theorem isPSL2_of_equiv_sl2 {X : Type} [Group X] {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : IsPSL 2 2 n X := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨e₁⟩ := CFSG.RankThree.PartOne.nonempty_SL2_mulEquiv_statedProj' (F := K)
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨e.trans e₁⟩⟩
  · intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    omega
  · intro h
    have h2 : 2 ^ n = 3 := congrArg Prod.snd h
    omega

theorem isPSL2_quot_of_hom {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {f : X →* Matrix.SpecialLinearGroup (Fin 2) K} (hf : Function.Surjective f)
    (hk : IsPGroup 2 ↥f.ker) : IsPSL 2 2 n (X ⧸ CFSG.pCore 2 X) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hO : CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
    have : (CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K)).Normal := CFSG.pCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2
      (Matrix.SpecialLinearGroup (Fin 2) K)) with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) K) := by
        have h1 := CFSG.pCore_isPGroup (p := 2) (G := Matrix.SpecialLinearGroup (Fin 2) K)
        rw [h] at h1
        exact h1.of_equiv Subgroup.topEquiv
      have := hp.isNilpotent
      exact CFSG.Quasithin.SL2Sylow.not_isSolvable_sl2 h4 inferInstance
  obtain ⟨e⟩ := L3312.modO2_equiv_of_surjective f hf hk
  have e' : (X ⧸ CFSG.pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  exact isPSL2_of_equiv_sl2 hn hK e'


section Family

variable {L T : Subgroup G}

theorem mem_normalizer_perfectCore {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (perfectCore H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [map_perfectCore, hg]

theorem mem_lFamilyOf_of_hom (hT : quasithinIsSylowTwo T) (hO : pCoreOf 2 (L ⊔ T) ≠ ⊥)
    {X : Subgroup G} (hXL : X ≤ L)
    (hX : ⁅X, X⁆ = X) (hTX : T ≤ Subgroup.normalizer (X : Set G)) {S : Type} [Group S]
    [IsSimpleGroup S] (f : ↥X →* S) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    X ∈ lFamilyOf L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX1 : X ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    exact hab (by rw [Subsingleton.elim x y])
  have hsyl : ∀ H : Subgroup G, T ≤ H → IsSylowTwoOf T H := fun H hTH =>
    ⟨hTH, hT.1, fun h2 => hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  refine ⟨hXL, hT.1, Sec1216Lv.mem_cComp_of_hom hX hX1 hTX f hf hk, (hsyl _ le_sup_right).2.2,
    fun hbot => hO ?_⟩
  have hPT : pCoreOf 2 (L ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (hsyl _ le_sup_right)
  have hle : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (X ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPT.trans le_sup_right)
      ((sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
  rw [hbot, le_bot_iff] at hle
  exact hle

variable {Y : Type} [Group Y] [Finite Y]

theorem liftCore_mem_lFamilyOf (hT : quasithinIsSylowTwo T) (hO : pCoreOf 2 (L ⊔ T) ≠ ⊥)
    {φ : ↥L →* Y} (hφ : Function.Surjective φ)
    (hk : IsPGroup 2 ↥φ.ker) {P : Subgroup Y} (hP : Rk2.Rank2Levi P)
    (hTP : T ≤ Subgroup.normalizer (liftPre φ P : Set G)) : liftCore φ P ∈ lFamilyOf L T := by
  obtain ⟨K, _, _, _, n, hK, hn, f, hf, hfk⟩ := exists_hom_sl2 hφ hk hP
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup hK4
  exact mem_lFamilyOf_of_hom hT hO (liftCore_le φ P) (liftCore_perfect φ P)
    (fun t ht => mem_normalizer_perfectCore (hTP ht)) f hf hfk

theorem le_sup_liftCore {φ : ↥L →* Y} (hφ : Function.Surjective φ)
    (hkT : φ.ker.map L.subtype ≤ T) {P₀ P₁ : Subgroup Y}
    (hgen : perfectCore P₀ ⊔ perfectCore P₁ ⊔ (T.subgroupOf L).map φ = ⊤) :
    L ≤ liftCore φ P₀ ⊔ liftCore φ P₁ ⊔ T := by
  set A := liftCore φ P₀ ⊔ liftCore φ P₁ ⊔ T with hA
  have hcore : ∀ P : Subgroup Y, liftCore φ P ≤ A → perfectCore P ≤ (A.subgroupOf L).map φ := by
    intro P hPA
    rw [← map_perfectCore_comap hφ P]
    refine Subgroup.map_mono fun x hx => ?_
    have h1 : (x : G) ∈ liftCore φ P := by
      rw [liftCore_eq]
      exact ⟨x, hx, rfl⟩
    exact hPA h1
  have htop : (⊤ : Subgroup Y) ≤ (A.subgroupOf L).map φ := by
    rw [← hgen]
    refine sup_le (sup_le (hcore P₀ (le_sup_left.trans le_sup_left))
      (hcore P₁ (le_sup_right.trans le_sup_left))) (Subgroup.map_mono fun x hx => ?_)
    exact Subgroup.mem_sup_right hx
  intro l hl
  obtain ⟨b, hb, hbl⟩ := htop (Subgroup.mem_top (φ ⟨l, hl⟩))
  have hker : b⁻¹ * ⟨l, hl⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbl, inv_mul_cancel]
  have h2 : ((b⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ A := Subgroup.mem_sup_right (hkT ⟨_, hker, rfl⟩)
  have h3 := A.mul_mem (hb : (b : G) ∈ A) h2
  simpa using h3

end Family

end L3316

end CFSG.Quasithin.H13
