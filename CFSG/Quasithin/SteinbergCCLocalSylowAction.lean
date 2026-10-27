module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.SteinbergCCPerfectCentralization
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

variable {H : Type*} [Group H]

@[expose] noncomputable def normalizerCoreQuotConj (X : Subgroup H) :
    normalizer (X : Set H) →* MulAut (X ⧸ CFSG.pCore 2 X) :=
  (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 X)).comp X.normalizerMonoidHom

@[expose] noncomputable def normalizerFrattiniConj (X : Subgroup H) :
    normalizer (X : Set H) →*
      MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  (CFSG.SectionRank.Ccomm.autQuotient (frattini (X ⧸ CFSG.pCore 2 X))).comp
    (normalizerCoreQuotConj X)

theorem apply_mem_of_mem_stabilizer {S : Type*} [Group S] {P₀ : Subgroup S} {γ : MulAut S}
    (hγ : γ ∈ MulAction.stabilizer (MulAut S) P₀) {x : S} (hx : x ∈ P₀) : γ x ∈ P₀ := by
  have h : γ • P₀ = P₀ := hγ
  rw [← h]
  exact smul_mem_pointwise_smul x γ P₀ hx

@[expose] def stabilizerRestrict {S : Type*} [Group S] (P₀ : Subgroup S) :
    MulAction.stabilizer (MulAut S) P₀ →* MulAut P₀ where
  toFun γ :=
    { toFun := fun x => ⟨(γ : MulAut S) (x : S), apply_mem_of_mem_stabilizer γ.2 x.2⟩
      invFun := fun x => ⟨(γ : MulAut S)⁻¹ (x : S), apply_mem_of_mem_stabilizer (inv_mem γ.2) x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self S _ (x : S))
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self S _ (x : S))
      map_mul' := fun x y => Subtype.ext (map_mul (γ : MulAut S) (x : S) (y : S)) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

theorem mem_stabilizer_of_apply_mem {S : Type*} [Group S] [Finite S] {P₀ : Subgroup S}
    {γ : MulAut S} (hγ : ∀ x ∈ P₀, γ x ∈ P₀) : γ ∈ MulAction.stabilizer (MulAut S) P₀ := by
  change γ • P₀ = P₀
  have hle : γ • P₀ ≤ P₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hγ x hx
  refine eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr (Subgroup.equivSMul γ P₀).toEquiv]

theorem exists_conj_eq_of_isSylowOf [Finite H] {p : ℕ} [Fact p.Prime] {X P P' : Subgroup H}
    (hP : IsSylowOf p P X) (hP' : IsSylowOf p P' X) :
    ∃ x ∈ X, P.map (MulAut.conj x).toMonoidHom = P' := by
  obtain ⟨S₁, hS₁⟩ := hP
  obtain ⟨S₂, hS₂⟩ := hP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₁ S₂
  refine ⟨g, g.2, ?_⟩
  rw [← hS₁, ← hS₂, ← hg]
  ext y
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨g * s * g⁻¹, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, ⟨s, hs, rfl⟩, rfl⟩

theorem original_local_sylow_prime_action_is_quotient_of_common_normalizer_restriction
    [Finite H] {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) {D : Subgroup H} (Q : Sylow 2 H)
    (hQD : (Q : Subgroup H) ≤ D) {K : Subgroup H} [K.Normal] {X : Subgroup H} (hXD : X ≤ D)
    (hXn : (X.subgroupOf D).Normal) (hXK : X ≤ K) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    {N : Subgroup K} [N.Characteristic] (hN : ¬ p ∣ Nat.card N) {P : Subgroup H}
    (hP : IsSylowOf p P X) :
    let σ := QuotientGroup.mk' N
    let θ : H →* MulAut (K ⧸ N) :=
      (CFSG.SectionRank.Ccomm.autQuotient N).comp MulAut.conjNormal
    let P₀ := (P.subgroupOf K).map σ
    let U₀ := ((Q : Subgroup H).subgroupOf K).map σ
    let Γ := MulAction.stabilizer (MulAut (K ⧸ N)) P₀ ⊓
      MulAction.stabilizer (MulAut (K ⧸ N)) U₀
    let B := ((Q : Subgroup H) ⊓ normalizer (P : Set H)).map θ
    let QW := ((Q : Subgroup H).subgroupOf (normalizer (X : Set H))).map
      (normalizerFrattiniConj X)
    Function.Injective (σ.comp (P.subgroupOf K).subtype) ∧
      (∃ U : Sylow 2 (K ⧸ N), (U : Subgroup (K ⧸ N)) = U₀) ∧
      ((P₀ : Set (K ⧸ N)) * U₀ = U₀ * P₀) ∧ IsPGroup 2 B ∧ B ≤ Γ ∧
      ∃ (gres : Γ →* MulAut P₀)
        (bres : ((Q : Subgroup H) ⊓ normalizer (P : Set H) : Subgroup H) →* MulAut P₀),
        (∀ γ x, (gres γ x : K ⧸ N) = (γ : MulAut (K ⧸ N)) x) ∧
        (∀ n x, (bres n x : K ⧸ N) = θ n x) ∧ bres.range ≤ gres.range ∧
        (∃ f : bres.range →* QW, Function.Surjective f ∧
          ∀ (n : ((Q : Subgroup H) ⊓ normalizer (P : Set H) : Subgroup H))
            (hn : (n : H) ∈ normalizer (X : Set H)),
            (f (bres.rangeRestrict n) : MulAut _) = normalizerFrattiniConj X ⟨n, hn⟩) ∧
        Nat.card QW ∣ Nat.card bres.range ∧ Nat.card QW ∣ Nat.card gres.range ∧
        ∀ d : ℕ, 1 ≤ d → IsCyclic gres.range → Nat.card gres.range ∣ d →
          IsCyclic QW ∧ Nat.card QW ∣ d := by
  intro σ θ P₀ U₀ Γ B QW
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPX, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hPK : P ≤ K := hPX.trans hXK
  have hDN : D ≤ normalizer (X : Set H) := (normal_subgroupOf_iff_le_normalizer hXD).mp hXn
  have hQN : (Q : Subgroup H) ≤ normalizer (X : Set H) := hQD.trans hDN
  set A := (CFSG.pCore 2 X).map X.subtype with hAdef
  have hA2 : IsPGroup 2 A := CFSG.pCore_isPGroup.map _
  have hmemA : ∀ x : X, (x : H) ∈ A ↔ x ∈ CFSG.pCore 2 X := fun x =>
    mem_map_iff_mem (subtype_injective X)
  have hNA : ∀ g ∈ normalizer (X : Set H), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    rintro g hg _ ⟨a, ha, rfl⟩
    have h1 := characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore 2 X).Characteristic) (X.normalizerMonoidHom ⟨g, hg⟩)
    refine ⟨X.normalizerMonoidHom ⟨g, hg⟩ a, ?_, rfl⟩
    rw [← h1]
    exact mem_map_of_mem _ ha
  have hAQ : A ≤ Q := by
    have h := Q.is_maximal' (Q.isPGroup'.to_sup_of_normal_right' hA2
      (le_normalizer_of_conj_mem fun g hg a ha => hNA g (hQN hg) a ha)) le_sup_left
    rw [← h]
    exact le_sup_right
  have hπP : (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ := by
    obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
    have h := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
      (hXA.to_subgroup ⊤) le_top
    rw [h, Sylow.coe_mapSurjective, hS₁]
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ A := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩ ∈
        (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := hπP ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    exact ⟨y, mem_subgroupOf.mp hy, (hmemA _).mpr (QuotientGroup.eq.mp hyx)⟩
  have hσinj : Function.Injective (σ.comp (P.subgroupOf K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyN : (y : K) ∈ N := (QuotientGroup.eq_one_iff _).mp hy
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨((y : K) : H), mem_subgroupOf.mp y.2⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hk
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact Subtype.ext hk
    · exact absurd ((dvd_pow_self p k.succ_ne_zero).trans
        (hk ▸ Subgroup.orderOf_dvd_natCard N hyN)) hN
  have hnorm : ∀ g : H, (∀ z ∈ P, g * z * g⁻¹ ∈ P) → (∀ z, g * z * g⁻¹ ∈ P → z ∈ P) →
      g ∈ normalizer (P : Set H) := fun g h1 h2 =>
    mem_normalizer_iff.mpr fun z => ⟨h1 z, h2 z⟩
  have hQdec : ∀ q ∈ (Q : Subgroup H), ∃ a ∈ A,
      a⁻¹ * q ∈ (Q : Subgroup H) ⊓ normalizer (P : Set H) := by
    intro q hq
    have hqP : IsSylowOf p (P.map (MulAut.conj q).toMonoidHom) X := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (hQN hq) y).mp (hPX hy)
      · rw [card_map_of_injective (MulAut.conj q).injective, hP.card_eq]
    obtain ⟨x, hx, hxP⟩ := exists_conj_eq_of_isSylowOf hP hqP
    obtain ⟨y, hy, hya⟩ := hXPA x hx
    have haA : x * y⁻¹ ∈ A := by
      have h1 := hNA y (le_normalizer (hPX hy)) _ hya
      rwa [show y * (y⁻¹ * x) * y⁻¹ = x * y⁻¹ by group] at h1
    refine ⟨x * y⁻¹, haA, mem_inf.mpr ⟨mul_mem (inv_mem (hAQ haA)) hq, hnorm _ ?_ ?_⟩⟩
    · intro z hz
      have h1 : q * z * q⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom := by
        rw [hxP]
        exact ⟨z, hz, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : x * z' * x⁻¹ = q * z * q⁻¹ := hzz'
      have e : (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ = y * z' * y⁻¹ := by
        rw [show (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ =
          y * x⁻¹ * (q * z * q⁻¹) * x * y⁻¹ by group, ← hzz']
        group
      rw [e]
      exact mul_mem (mul_mem hy hz') (inv_mem hy)
    · intro z hz
      have hu : y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y ∈ P :=
        mul_mem (mul_mem (inv_mem hy) hz) hy
      have h1 : x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ ∈
          P.map (MulAut.conj q).toMonoidHom := by
        rw [← hxP]
        exact ⟨_, hu, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : q * z' * q⁻¹ =
          x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ := hzz'
      have e : z = z' := by
        have h2 : q * z' * q⁻¹ = q * z * q⁻¹ := by rw [hzz']; group
        exact (mul_left_cancel (mul_right_cancel h2)).symm
      rw [e]
      exact hz'
  have hconjmk : ∀ (g : H) (hg : g ∈ normalizer (X : Set H)) (x : X),
      normalizerFrattiniConj X ⟨g, hg⟩
        (QuotientGroup.mk' _ (QuotientGroup.mk' (CFSG.pCore 2 X) x)) =
      QuotientGroup.mk' _ (QuotientGroup.mk' (CFSG.pCore 2 X) (X.normalizerMonoidHom ⟨g, hg⟩ x)) :=
    fun _ _ _ => rfl
  have hAtriv : ∀ (a : H) (ha : a ∈ A) (haN : a ∈ normalizer (X : Set H)),
      normalizerFrattiniConj X ⟨a, haN⟩ = 1 := by
    intro a ha haN
    ext w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    rw [hconjmk, MulAut.one_apply]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply (hmemA _).mp
    change (a * x * a⁻¹)⁻¹ * x ∈ A
    have h1 := hNA (x : H)⁻¹ (le_normalizer (inv_mem x.2)) a⁻¹ (inv_mem ha)
    rw [inv_inv] at h1
    rw [show (a * (x : H) * a⁻¹)⁻¹ * x = a * ((x : H)⁻¹ * a⁻¹ * x) by group]
    exact mul_mem ha h1
  have hcentriv : ∀ (g : H) (hg : g ∈ normalizer (X : Set H)), (∀ z ∈ P, g * z * g⁻¹ = z) →
      normalizerFrattiniConj X ⟨g, hg⟩ = 1 := by
    intro g hg hgP
    ext w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    obtain ⟨y, hy, hya⟩ := hXPA x x.2
    have hxy : QuotientGroup.mk' (CFSG.pCore 2 X) x =
        QuotientGroup.mk' (CFSG.pCore 2 X) ⟨y, hPX hy⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have h1 := inv_mem hya
      rw [mul_inv_rev, inv_inv] at h1
      exact (hmemA _).mp h1
    rw [hxy, hconjmk, MulAut.one_apply]
    congr 2
    exact Subtype.ext (hgP y hy)
  have hθP : ∀ n ∈ normalizer (P : Set H), θ n ∈ MulAction.stabilizer (MulAut (K ⧸ N)) P₀ := by
    intro n hn
    apply mem_stabilizer_of_apply_mem
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨MulAut.conjNormal n k, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply]
    exact (mem_normalizer_iff.mp hn k).mp (mem_subgroupOf.mp hk)
  have hθU : ∀ n ∈ (Q : Subgroup H), θ n ∈ MulAction.stabilizer (MulAut (K ⧸ N)) U₀ := by
    intro n hn
    apply mem_stabilizer_of_apply_mem
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨MulAut.conjNormal n k, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply]
    exact mul_mem (mul_mem hn (mem_subgroupOf.mp hk)) (inv_mem hn)
  have hBΓ : B ≤ Γ := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_inf.mpr ⟨hθP n (mem_inf.mp hn).2, hθU n (mem_inf.mp hn).1⟩
  have hB2 : IsPGroup 2 B := (Q.isPGroup'.to_le inf_le_left).map θ
  have hU₀ : ∃ U : Sylow 2 (K ⧸ N), (U : Subgroup (K ⧸ N)) = U₀ := by
    have hQtop : IsSylowOf 2 (Q : Subgroup H) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
      exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩
    obtain ⟨S₁, hS₁⟩ := (hQtop.inf_of_le_normalizer (N := K) le_top
      (by rw [normalizer_eq_top])).exists_sylow_eq_subgroupOf
    refine ⟨S₁.mapSurjective (QuotientGroup.mk'_surjective N), ?_⟩
    rw [Sylow.coe_mapSurjective, hS₁, inf_subgroupOf_right]
  have hPQ : ∀ y ∈ P, ∀ q ∈ (Q : Subgroup H),
      ∃ q' ∈ (Q : Subgroup H), ∃ y' ∈ P, y * q = q' * y' := by
    intro y hy q hq
    have hx : q⁻¹ * y * q⁻¹⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hQN (inv_mem hq)) y).mp (hPX hy)
    rw [inv_inv] at hx
    obtain ⟨y', hy', hya⟩ := hXPA _ hx
    refine ⟨q * (y' * (y'⁻¹ * (q⁻¹ * y * q)) * y'⁻¹),
      mul_mem hq (hAQ (hNA y' (le_normalizer (hPX hy')) _ hya)), y', hy', by group⟩
  have hQP : ∀ q ∈ (Q : Subgroup H), ∀ y ∈ P,
      ∃ y' ∈ P, ∃ q' ∈ (Q : Subgroup H), q * y = y' * q' := by
    intro q hq y hy
    obtain ⟨y', hy', hya⟩ := hXPA _ ((mem_normalizer_iff.mp (hQN hq) y).mp (hPX hy))
    exact ⟨y', hy', y'⁻¹ * (q * y * q⁻¹) * q, mul_mem (hAQ hya) hq, by group⟩
  have hPU : (P₀ : Set (K ⧸ N)) * U₀ = U₀ * P₀ := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨q', hq', y', hy', he⟩ :=
        hPQ _ (mem_subgroupOf.mp hy) _ (mem_subgroupOf.mp hu)
      have hq'K : q' ∈ K := by
        rw [show q' = (y : H) * u * y'⁻¹ by rw [he]; group]
        exact mul_mem (mul_mem y.2 u.2) (inv_mem (hPK hy'))
      refine ⟨σ ⟨q', hq'K⟩, ⟨⟨q', hq'K⟩, mem_subgroupOf.mpr hq', rfl⟩, σ ⟨y', hPK hy'⟩,
        ⟨⟨y', hPK hy'⟩, mem_subgroupOf.mpr hy', rfl⟩, ?_⟩
      change σ ⟨q', hq'K⟩ * σ ⟨y', hPK hy'⟩ = σ y * σ u
      rw [← map_mul, ← map_mul]
      exact congrArg σ (Subtype.ext he.symm)
    · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨y', hy', q', hq', he⟩ :=
        hQP _ (mem_subgroupOf.mp hu) _ (mem_subgroupOf.mp hy)
      have hq'K : q' ∈ K := by
        rw [show q' = y'⁻¹ * ((u : H) * y) by rw [he]; group]
        exact mul_mem (inv_mem (hPK hy')) (mul_mem u.2 y.2)
      refine ⟨σ ⟨y', hPK hy'⟩, ⟨⟨y', hPK hy'⟩, mem_subgroupOf.mpr hy', rfl⟩, σ ⟨q', hq'K⟩,
        ⟨⟨q', hq'K⟩, mem_subgroupOf.mpr hq', rfl⟩, ?_⟩
      change σ ⟨y', hPK hy'⟩ * σ ⟨q', hq'K⟩ = σ u * σ y
      rw [← map_mul, ← map_mul]
      exact congrArg σ (Subtype.ext he.symm)
  let gres : Γ →* MulAut P₀ := (stabilizerRestrict P₀).comp (inclusion inf_le_left)
  let bres : ((Q : Subgroup H) ⊓ normalizer (P : Set H) : Subgroup H) →* MulAut P₀ :=
    (stabilizerRestrict P₀).comp
      ((θ.comp ((Q : Subgroup H) ⊓ normalizer (P : Set H)).subtype).codRestrict _
        fun n => hθP n (mem_inf.mp n.2).2)
  have hbg : bres.range ≤ gres.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨θ n, hBΓ ⟨n, n.2, rfl⟩⟩, MulEquiv.ext fun _ => rfl⟩
  have hmemQW : ∀ n : ((Q : Subgroup H) ⊓ normalizer (P : Set H) : Subgroup H),
      normalizerFrattiniConj X ⟨n, hQN (mem_inf.mp n.2).1⟩ ∈ QW := fun n =>
    ⟨⟨n, hQN (mem_inf.mp n.2).1⟩, mem_subgroupOf.mpr (mem_inf.mp n.2).1, rfl⟩
  let hW : ((Q : Subgroup H) ⊓ normalizer (P : Set H) : Subgroup H) →* QW :=
    ((normalizerFrattiniConj X).comp (inclusion (inf_le_left.trans hQN))).codRestrict QW
      hmemQW
  have hWsurj : Function.Surjective hW := by
    rintro ⟨_, ⟨q, hq, rfl⟩⟩
    obtain ⟨a, ha, han⟩ := hQdec q (mem_subgroupOf.mp hq)
    have haN : a ∈ normalizer (X : Set H) := hQN (hAQ ha)
    refine ⟨⟨a⁻¹ * q, han⟩, Subtype.ext ?_⟩
    change normalizerFrattiniConj X (⟨a, haN⟩⁻¹ * q) = normalizerFrattiniConj X q
    rw [map_mul, map_inv, hAtriv a ha haN, inv_one, one_mul]
  have hker : bres.rangeRestrict.ker ≤ hW.ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    have hn' : bres n = 1 := congrArg Subtype.val hn
    have hcent : ∀ z ∈ P, (n : H) * z * (n : H)⁻¹ = z := by
      intro z hz
      have hk : (⟨z, hPK hz⟩ : K) ∈ P.subgroupOf K := mem_subgroupOf.mpr hz
      have hc : MulAut.conjNormal (n : H) ⟨z, hPK hz⟩ ∈ P.subgroupOf K := by
        rw [mem_subgroupOf, MulAut.conjNormal_apply]
        exact (mem_normalizer_iff.mp (mem_inf.mp n.2).2 z).mp hz
      have h1 := congrArg (fun φ : MulAut P₀ =>
        ((φ ⟨σ ⟨z, hPK hz⟩, ⟨_, hk, rfl⟩⟩ : P₀) : K ⧸ N)) hn'
      change σ (MulAut.conjNormal (n : H) ⟨z, hPK hz⟩) = σ ⟨z, hPK hz⟩ at h1
      have h2 : (⟨_, hc⟩ : P.subgroupOf K) = ⟨_, hk⟩ := hσinj h1
      have h3 := congrArg (fun w : P.subgroupOf K => ((w : K) : H)) h2
      simpa [MulAut.conjNormal_apply] using h3
    exact Subtype.ext (hcentriv n (hQN (mem_inf.mp n.2).1) hcent)
  let f := (MonoidHom.liftOfSurjective bres.rangeRestrict bres.rangeRestrict_surjective)
    ⟨hW, hker⟩
  have hf : ∀ n, f (bres.rangeRestrict n) = hW n := fun n =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hfsurj : Function.Surjective f := fun w => by
    obtain ⟨n, rfl⟩ := hWsurj w
    exact ⟨_, hf n⟩
  have hcard : Nat.card QW ∣ Nat.card bres.range := card_dvd_of_surjective f hfsurj
  refine ⟨hσinj, hU₀, hPU, hB2, hBΓ, gres, bres, fun _ _ => rfl, fun _ _ => rfl, hbg,
    ⟨f, hfsurj, fun n hn => by rw [hf]; rfl⟩, hcard, hcard.trans (card_dvd_of_le hbg), ?_⟩
  intro d _ hcyc hd
  have : IsCyclic bres.range := Subgroup.isCyclic_of_le hbg
  exact ⟨isCyclic_of_surjective f hfsurj, (hcard.trans (card_dvd_of_le hbg)).trans hd⟩

end CFSG.Quasithin.SteinbergCC
