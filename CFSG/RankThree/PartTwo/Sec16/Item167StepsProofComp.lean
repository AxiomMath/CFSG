module

public import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Core
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.Transfer.Yoshida
import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec16.Item167ProofGL2
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec16.Comp167

open CFSG CFSG.Open CFSG.SectionRank CFSG.SectionRank.Ccomm Subgroup
open CFSG.RankThree.PartTwo.Sec16.Crit167
open scoped commutatorElement

section Criterion

variable {X : Type*} [Group X] [Finite X]

theorem le_fittingSubgroup_of_forall_coprime' {N : Subgroup X} [hN : N.Normal]
    (hF : ∀ y ∈ N, y ∈ Subgroup.centralizer (fittingSubgroup X : Set X) →
      y ∈ fittingSubgroup X)
    (hcop : ∀ r : ℕ, r.Prime → ∀ y ∈ N, Nat.Coprime (orderOf y) r →
      ∀ x ∈ pCore r X, y * x = x * y) :
    N ≤ fittingSubgroup X := by
  have stepA : ∀ r : ℕ, r.Prime → ∀ y ∈ N, (∃ k : ℕ, y ^ (r ^ k) = 1) →
      y ∈ fittingSubgroup X := by
    intro r hr y hyN hyr
    have : Fact r.Prime := ⟨hr⟩
    set Sr : Set X := {g | g ∈ N ∧ ∃ k : ℕ, g ^ (r ^ k) = 1} with hSr
    set R := Subgroup.normalClosure Sr with hRdef
    have hRN : R ≤ N := Subgroup.normalClosure_le_normal fun g hg => hg.1
    have hRq : ∀ q : ℕ, q.Prime → q ≠ r → ∀ g ∈ R, ∀ x ∈ pCore q X, g * x = x * g := by
      intro q hq hqr g hg x hx
      have : Fact q.Prime := ⟨hq⟩
      have : (pCore q X).Normal := pCore_normal
      have hle : R ≤ Subgroup.centralizer (pCore q X : Set X) := by
        refine Subgroup.normalClosure_le_normal fun g' hg' => ?_
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro x' hx'
        obtain ⟨k, hk⟩ := hg'.2
        have hco : Nat.Coprime (orderOf g') q :=
          Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)
            (Nat.Coprime.pow_left k ((Nat.coprime_primes hr hq).mpr hqr.symm))
        exact (hcop q hq g' hg'.1 hco x' hx').symm
      exact (Subgroup.mem_centralizer_iff.mp (hle hg) x hx).symm
    have hRcop : ∀ g ∈ R, Nat.Coprime (orderOf g) r →
        g ∈ Subgroup.centralizer (fittingSubgroup X : Set X) := by
      intro g hg hgr
      refine Sec4.Census.mem_centralizer_fittingSubgroup fun p hp x hx => ?_
      by_cases hpr : p = r
      · subst hpr
        exact hcop p hp g (hRN hg) hgr x hx
      · exact hRq p hp hpr g hg x hx
    have hcen : ∀ a ∈ R, Nat.Coprime (orderOf a) r → ∀ g ∈ R, g * a = a * g := by
      intro a ha har g hg
      have haC := hRcop a ha har
      set H := Subgroup.normalClosure ({a} : Set X) with hHdef
      have hHZ : H ≤ Subgroup.centralizer (fittingSubgroup X : Set X) ⊓ fittingSubgroup X :=
        Subgroup.normalClosure_le_normal
          (Set.singleton_subset_iff.mpr ⟨haC, hF a (hRN ha) haC⟩)
      have hHcomm : ∀ b ∈ H, ∀ c ∈ H, Commute b c := fun b hb c hc =>
        (Subgroup.mem_centralizer_iff.mp (hHZ hb).1 c (hHZ hc).2).symm
      have hconj : ∀ b ∈ Group.conjugatesOfSet ({a} : Set X), Nat.Coprime (orderOf b) r := by
        intro b hb
        rw [Group.mem_conjugatesOfSet_iff] at hb
        obtain ⟨a', ha', hab⟩ := hb
        rw [Set.mem_singleton_iff] at ha'
        subst ha'
        obtain ⟨c, rfl⟩ := isConj_iff.mp hab
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a'
        rw [show (MulAut.conj c).toMonoidHom a' = c * a' * c⁻¹ from rfl] at this
        rw [this]
        exact har
      have hHcop : ∀ b ∈ H, Nat.Coprime (orderOf b) r := fun b hb =>
        Sec4.Census.coprime_orderOf_of_mem_closure
          (fun b₁ hb₁ b₂ hb₂ _ => hHcomm b₁ (Subgroup.conjugatesOfSet_subset_normalClosure hb₁)
            b₂ (Subgroup.conjugatesOfSet_subset_normalClosure hb₂)) hconj hb
      have hcard : Nat.Coprime (Nat.card H) r := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hr]
        intro hdvd
        obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := H) r hdvd
        have := hHcop b b.2
        rw [Subgroup.orderOf_coe, hb, Nat.coprime_self] at this
        exact hr.one_lt.ne' this
      have hHnil : Group.IsNilpotent H := by
        have : Subgroup.center H = ⊤ := by
          rw [eq_top_iff]
          intro b _
          rw [Subgroup.mem_center_iff]
          intro c
          exact Subtype.ext (hHcomm c c.2 b b.2)
        exact Subgroup.isNilpotent_of_ker_le_center (1 : H →* Unit)
          (by rw [this]; exact le_top)
      exact Sec4.Census.commute_of_coprime_card inferInstance hcard
        (fun q hq hqr x hx => hRq q hq hqr g hg x hx) a (Subgroup.subset_normalClosure rfl)
    let Z : Subgroup R := Subgroup.closure {g : R | Nat.Coprime (orderOf g) r}
    have hZcen : Z ≤ Subgroup.center R := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      have hg' : Nat.Coprime (orderOf (g : X)) r := by rwa [Subgroup.orderOf_coe]
      exact hcen g g.2 hg' h h.2
    have : Z.Normal := Subgroup.normal_of_le_center hZcen
    have hRZ : IsPGroup r (R ⧸ Z) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨a, b, hab, ⟨k, hk⟩, hb, -, -⟩ := Sec4.Census.exists_mul_eq_isPGroup_coprime g hr
        refine ⟨k, ?_⟩
        have hbZ : b ∈ Z := Subgroup.subset_closure hb
        rw [← hab, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).mpr hbZ, mul_one,
          ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    have : Group.IsNilpotent (R ⧸ Z) := hRZ.isNilpotent
    have hRnil : Group.IsNilpotent R := Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Z)
      (by rw [QuotientGroup.ker_mk']; exact hZcen)
    have hRF : R ≤ fittingSubgroup X := le_sSup ⟨inferInstance, hRnil⟩
    exact hRF (Subgroup.subset_normalClosure ⟨hyN, hyr⟩)
  set H := (fittingSubgroup X).subgroupOf N
  have hidx : H.index = 1 := by
    by_contra hne
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨P⟩ : Nonempty (Sylow r N) := inferInstance
    have hPH : (P : Subgroup N) ≤ H := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      apply stepA r hr g g.2
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val (congrArg Subtype.val hk)
      simpa using this
    exact P.not_dvd_index (hrd.trans (Subgroup.index_dvd_of_le hPH))
  rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hidx
  exact hidx

end Criterion

section Residual

variable {H : Type*} [Group H] [Finite H]

theorem commute_of_mem_oResidual (hgl : KS167GL2)
    (h2 : CFSG.pCore 2 H = ⊥) (h3 : ¬ 3 ∣ Nat.card H)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup H) ≤ 2)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup 3 A) (β : A →* MulAut H)
    (hgen : Subgroup.closure {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹} = ⊤)
    {r : ℕ} (hr : r.Prime) {y : H} (hy : y ∈ CFSG.GH74.GLS.oResidual 2 H)
    (hcop : Nat.Coprime (orderOf y) r) {x : H} (hx : x ∈ CFSG.pCore r H) : y * x = x * y := by
  have : Fact r.Prime := ⟨hr⟩
  have hx1 : ∀ q : ℕ, q = 2 ∨ q = 3 → q = r → x = 1 := by
    rintro q hq rfl
    rcases hq with rfl | rfl
    · rwa [h2, mem_bot] at hx
    · have hP1 : CFSG.pCore 3 H = ⊥ := by
        rcases (CFSG.pCore_isPGroup (p := 3) (G := H)).card_eq_or_dvd with h1 | h1
        · exact Subgroup.card_eq_one.mp h1
        · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) h3
      rwa [hP1, mem_bot] at hx
  by_cases hr23 : r = 2 ∨ r = 3
  · rw [hx1 r hr23 rfl, one_mul, mul_one]
  have hr2 : r ≠ 2 := fun h => hr23 (Or.inl h)
  have hr5 : 5 ≤ r := by
    rcases Nat.lt_or_ge r 5 with h | h
    · have h2le := hr.two_le
      interval_cases r
      · exact absurd (Or.inl rfl) hr23
      · exact absurd (Or.inr rfl) hr23
      · exact absurd hr (by decide)
    · exact h
  have : Finite (H ⋊[β] A) :=
    Finite.of_injective (fun x : H ⋊[β] A => (x.left, x.right)) fun x y hxy =>
      SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have hιinj : Function.Injective (SemidirectProduct.inl : H →* H ⋊[β] A) :=
    SemidirectProduct.inl_injective
  have hconj : ∀ (a : A) (n : H), (SemidirectProduct.inl (β a n) : H ⋊[β] A) =
      SemidirectProduct.inr a * SemidirectProduct.inl n * (SemidirectProduct.inr a)⁻¹ :=
    fun a n => by
      have h := SemidirectProduct.inl_aut (φ := β) a n
      rw [map_inv] at h
      exact h
  set P := CFSG.pCore r H with hPdef
  set Q := P.map (SemidirectProduct.inl : H →* H ⋊[β] A) with hQdef
  have hPchar : ∀ (σ : MulAut H), ∀ p ∈ P, σ p ∈ P := fun σ p hp => by
    rw [hPdef, ← CFSG.pCore_map_iso r σ]
    exact ⟨p, hp, rfl⟩
  have hQn : Q.Normal := by
    refine ⟨fun q hq g => ?_⟩
    obtain ⟨p, hp, rfl⟩ := hq
    rw [← SemidirectProduct.inl_left_mul_inr_right g]
    have h1 : SemidirectProduct.inl g.left * SemidirectProduct.inr g.right *
        (SemidirectProduct.inl p : H ⋊[β] A) *
        (SemidirectProduct.inl g.left * SemidirectProduct.inr g.right)⁻¹ =
        SemidirectProduct.inl (g.left * β g.right p * g.left⁻¹) := by
      rw [map_mul, map_mul, map_inv, hconj]
      group
    rw [h1]
    exact ⟨_, (CFSG.pCore_normal (p := r) (G := H)).conj_mem _ (hPchar _ p hp) g.left, rfl⟩
  have hQ : IsPGroup r Q := CFSG.pCore_isPGroup.map _
  have hQrank : CFSG.Open.pRank r Q ≤ 2 := by
    rw [hQdef, pRank_map_eq_of_injective hr _ hιinj]
    exact (pRank_mono hr.one_lt le_top).trans (hrank r hr (by omega))
  obtain ⟨k, hk, φ, hφ⟩ := exists_rep hr2 Q hQ hQrank
  set φι : H →* GL (Fin k) (ZMod r) := φ.comp SemidirectProduct.inl with hφι
  set φκ : A →* GL (Fin k) (ZMod r) := φ.comp SemidirectProduct.inr with hφκ
  have hφconj : ∀ (a : A) (n : H), φι (β a n) = φκ a * φι n * (φκ a)⁻¹ := fun a n => by
    simp only [hφι, hφκ, MonoidHom.comp_apply, hconj, map_mul, map_inv]
  set T := φι.range with hTdef
  set B := φκ.range with hBdef
  have hconjT : ∀ a : A, ∀ t ∈ T, φκ a * t * (φκ a)⁻¹ ∈ T := by
    rintro a _ ⟨n, rfl⟩
    exact ⟨β a n, hφconj a n⟩
  have hBN : B ≤ normalizer (T : Set (GL (Fin k) (ZMod r))) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_normalizer_iff]
    intro t
    constructor
    · exact hconjT a t
    · intro ht
      have h1 := hconjT a⁻¹ _ ht
      rw [map_inv, inv_inv] at h1
      simpa [mul_assoc] using h1
  have hTB : ⁅T, B⁆ = T := by
    refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hBN) ?_
    have hTcl : T = Subgroup.closure (φι '' {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹}) := by
      rw [hTdef, MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
    rw [hTcl, Subgroup.closure_le]
    rintro _ ⟨_, ⟨x', a, rfl⟩, rfl⟩
    have h1 : φι (x' * (β a x')⁻¹) = ⁅φι x', φκ a⁆ := by
      rw [map_mul, map_inv, hφconj, commutatorElement_def]
      group
    rw [SetLike.mem_coe, h1, ← hTcl]
    exact Subgroup.commutator_mem_commutator (MonoidHom.mem_range.mpr ⟨x', rfl⟩)
      (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hT3 : ¬ 3 ∣ Nat.card T := fun h => h3 (h.trans (Subgroup.card_dvd_of_surjective
    (f := φι.rangeRestrict) φι.rangeRestrict_surjective))
  have hB3 : IsPGroup 3 B := hA.of_surjective _ φκ.rangeRestrict_surjective
  have hφy : φι y = 1 := by
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · have hT1 : T = ⊥ := by
        rw [← hTB, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro t _
        rw [mem_centralizer_iff]
        intro b _
        exact GL_comm_of_le_one (by omega) b t
      have : φι y ∈ T := ⟨y, rfl⟩
      rw [hT1, mem_bot] at this
      exact this
    · obtain rfl : k = 2 := by omega
      have hres := hgl r hr hr5 T B hT3 hB3 hBN hTB
      have hmem := rangeRestrict_mem_oResidual φι hy
      obtain ⟨n, hn⟩ := hres ⟨_, hmem⟩
      have hn' : (φι.rangeRestrict y) ^ r ^ n = 1 := by
        simpa using congrArg Subtype.val hn
      have hdvd : orderOf (φι.rangeRestrict y) ∣ orderOf y := orderOf_map_dvd _ y
      have h1 : orderOf (φι.rangeRestrict y) ∣ Nat.gcd (r ^ n) (orderOf y) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn') hdvd
      rw [(Nat.Coprime.pow_left n hcop.symm).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
      simpa using congrArg Subtype.val h1
  have hyc := hφ (SemidirectProduct.inl y) (by rwa [orderOf_injective _ hιinj]) hφy
  have h1 := mem_centralizer_iff.mp hyc (SemidirectProduct.inl x) ⟨x, hx, rfl⟩
  apply hιinj
  rw [map_mul, map_mul]
  exact h1.symm

end Residual

section Components

variable {H : Type*} [Group H] [Finite H]

theorem commute_of_isComponent {K L : Subgroup H} (hK : IsComponent K) (hL : IsComponent L)
    (hKL : K ≠ L) {x y : H} (hx : x ∈ K) (hy : y ∈ L) : Commute x y := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hKL
  · exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm

omit [Finite H] in
theorem eq_one_of_commute_of_center_eq_bot {K : Subgroup H} (hZ : Subgroup.center K = ⊥)
    {y : H} (hy : y ∈ K) (hc : ∀ k ∈ K, y * k = k * y) : y = 1 := by
  have hmem : (⟨y, hy⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hc k k.2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

omit [Finite H] in
theorem map_pow_eq_of_map_eq {τ : MulAut H} {K : Subgroup H}
    (h : K.map τ.toMonoidHom = K) (j : ℕ) : K.map (τ ^ j).toMonoidHom = K := by
  induction j with
  | zero =>
    have h1 : (τ ^ 0).toMonoidHom = MonoidHom.id H := MonoidHom.ext fun _ => rfl
    rw [h1, Subgroup.map_id]
  | succ j ih =>
    have h1 : (τ ^ (j + 1)).toMonoidHom = (τ ^ j).toMonoidHom.comp τ.toMonoidHom := by
      rw [pow_succ]
      exact MonoidHom.ext fun _ => rfl
    rw [h1, ← Subgroup.map_map, h, ih]

omit [Finite H] in
theorem zpowers_mul_comm (g : H) (a b : Subgroup.zpowers g) : a * b = b * a := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
  exact zpow_mul_comm g i j

omit [Finite H] in
theorem zpowers_pow_eq_one {g : H} {p : ℕ} (hg : g ^ p = 1) (a : Subgroup.zpowers g) :
    a ^ p = 1 := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hg, one_zpow]

theorem map_eq_of_isComponent (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup H) ≤ 2)
    (hcomp : ∀ K : Subgroup H, IsComponent K → Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K)
    {σ : MulAut H} {n : ℕ} (hσ : σ ^ (3 ^ n) = 1) {K : Subgroup H} (hK : IsComponent K) :
    K.map σ.toMonoidHom = K := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_contra hne
  set K₁ := K.map σ.toMonoidHom with hK₁
  set K₂ := K₁.map σ.toMonoidHom with hK₂
  have hc₁ : IsComponent K₁ := CFSG.LocalCores.isComponent_map_mulEquiv σ hK
  have hc₂ : IsComponent K₂ := CFSG.LocalCores.isComponent_map_mulEquiv σ hc₁
  have h01 : K ≠ K₁ := fun h => hne h.symm
  have h12 : K₁ ≠ K₂ := by
    intro h
    apply hne
    have e1 : K₁.map σ.symm.toMonoidHom = K := CFSG.LocalCores.map_map_symm σ K
    have e2 : K₂.map σ.symm.toMonoidHom = K₁ := CFSG.LocalCores.map_map_symm σ K₁
    rw [← h] at e2
    exact e2.symm.trans e1
  have h02 : K ≠ K₂ := by
    intro h
    have h2 : K.map (σ ^ 2).toMonoidHom = K := by
      have h1 : (σ ^ 2).toMonoidHom = σ.toMonoidHom.comp σ.toMonoidHom := by
        rw [sq]
        exact MonoidHom.ext fun _ => rfl
      rw [h1, ← Subgroup.map_map]
      exact h.symm
    obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
    have hσm : σ = (σ ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 3 ^ n + 1 by omega, pow_succ, hσ, one_mul]
    apply hne
    have := map_pow_eq_of_map_eq h2 (m + 1)
    rwa [← hσm] at this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 (hcomp K hK).2
  set x₀ : H := (x : H) with hx₀def
  have hx₀K : x₀ ∈ K := x.2
  have hx₀ : orderOf x₀ = 5 := by rw [hx₀def, Subgroup.orderOf_coe, hx]
  set x₁ : H := σ x₀ with hx₁def
  set x₂ : H := σ x₁ with hx₂def
  have hx₁K : x₁ ∈ K₁ := ⟨x₀, hx₀K, rfl⟩
  have hx₂K : x₂ ∈ K₂ := ⟨x₁, hx₁K, rfl⟩
  have hx₁ : orderOf x₁ = 5 := by
    rw [hx₁def, ← hx₀]
    exact orderOf_injective σ.toMonoidHom σ.injective x₀
  have hx₂ : orderOf x₂ = 5 := by
    rw [hx₂def, ← hx₁]
    exact orderOf_injective σ.toMonoidHom σ.injective x₁
  set P₀ := Subgroup.zpowers x₀ with hP₀
  set P₁ := Subgroup.zpowers x₁ with hP₁
  set P₂ := Subgroup.zpowers x₂ with hP₂
  have hP₀K : P₀ ≤ K := Subgroup.zpowers_le.mpr hx₀K
  have hP₁K : P₁ ≤ K₁ := Subgroup.zpowers_le.mpr hx₁K
  have hP₂K : P₂ ≤ K₂ := Subgroup.zpowers_le.mpr hx₂K
  have c12 : ∀ (u : P₁) (v : P₂), Commute (P₁.subtype u) (P₂.subtype v) := fun u v =>
    commute_of_isComponent hc₁ hc₂ h12 (hP₁K u.2) (hP₂K v.2)
  set f₁₂ : P₁ × P₂ →* H := P₁.subtype.noncommCoprod P₂.subtype c12 with hf₁₂
  have c0 : ∀ (u : P₀) (v : P₁ × P₂), Commute (P₀.subtype u) (f₁₂ v) := fun u v => by
    rw [hf₁₂, MonoidHom.noncommCoprod_apply]
    exact Commute.mul_right (commute_of_isComponent hK hc₁ h01 (hP₀K u.2) (hP₁K v.1.2))
      (commute_of_isComponent hK hc₂ h02 (hP₀K u.2) (hP₂K v.2.2))
  set f : P₀ × (P₁ × P₂) →* H := P₀.subtype.noncommCoprod f₁₂ c0 with hf
  have hfapp : ∀ w : P₀ × (P₁ × P₂), f w = (w.1 : H) * ((w.2.1 : H) * (w.2.2 : H)) := by
    intro w
    rw [hf, MonoidHom.noncommCoprod_apply, hf₁₂, MonoidHom.noncommCoprod_apply]
    rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v, w⟩ h1
    rw [hfapp] at h1
    have hu' : (u : H) = ((v : H) * w)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hu : (u : H) = 1 := by
      refine eq_one_of_commute_of_center_eq_bot (hcomp K hK).1 (hP₀K u.2) fun k hk => ?_
      rw [hu']
      have hv : Commute ((v : H) * w) k := Commute.mul_left
        (commute_of_isComponent hc₁ hK h01.symm (hP₁K v.2) hk)
        (commute_of_isComponent hc₂ hK h02.symm (hP₂K w.2) hk)
      exact hv.inv_left.eq
    rw [hu, one_mul] at h1
    have hv' : (v : H) = (w : H)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hv : (v : H) = 1 := by
      refine eq_one_of_commute_of_center_eq_bot (hcomp K₁ hc₁).1 (hP₁K v.2) fun k hk => ?_
      rw [hv']
      exact (commute_of_isComponent hc₂ hc₁ h12.symm (hP₂K w.2) hk).inv_left.eq
    rw [hv, one_mul] at h1
    have hu1 : u = 1 := Subtype.ext hu
    have hv1 : v = 1 := Subtype.ext hv
    have hw1 : w = 1 := Subtype.ext h1
    rw [hu1, hv1, hw1]
    rfl
  have hcard : Nat.card (P₀ × (P₁ × P₂)) = 5 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, hP₀, hP₁, hP₂, Nat.card_zpowers, Nat.card_zpowers,
      Nat.card_zpowers, hx₀, hx₁, hx₂]
    norm_num
  have hcomm : ∀ a b : P₀ × (P₁ × P₂), a * b = b * a := fun a b =>
    Prod.ext (zpowers_mul_comm _ _ _) (Prod.ext (zpowers_mul_comm _ _ _)
      (zpowers_mul_comm _ _ _))
  have h5pow : ∀ g : H, orderOf g = 5 → g ^ 5 = 1 := fun g hg => by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hpow : ∀ a : P₀ × (P₁ × P₂), a ^ 5 = 1 := fun a =>
    Prod.ext (zpowers_pow_eq_one (h5pow _ hx₀) _)
      (Prod.ext (zpowers_pow_eq_one (h5pow _ hx₁) _) (zpowers_pow_eq_one (h5pow _ hx₂) _))
  have h3 := le_pRank_of_injective (p := 5) (by norm_num) hcomm hpow hcard f hfinj
    (H := (⊤ : Subgroup H)) le_top
  omega

omit [Finite H] in
theorem mem_normalizer_of_forall_conj_mem [Finite H] {K : Subgroup H} {z : H}
    (hle : ∀ k ∈ K, z * k * z⁻¹ ∈ K) : z ∈ Subgroup.normalizer (K : Set H) := by
  have hmap : K.map (MulAut.conj z).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact hle k hk
  have heq : K.map (MulAut.conj z).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj z).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => hle k hk, fun hk => ?_⟩
  rw [← heq] at hk
  obtain ⟨k', hk', hkk'⟩ := hk
  have h1 : z * k' * z⁻¹ = z * k * z⁻¹ := hkk'
  rwa [mul_left_cancel (mul_right_cancel h1)] at hk'

theorem normal_of_isComponent {A : Type*} [Group A] (β : A →* MulAut H)
    (hgen : Subgroup.closure {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹} = ⊤)
    (hfix : ∀ a : A, ∀ K : Subgroup H, IsComponent K → K.map (β a).toMonoidHom = K)
    {K : Subgroup H} (hK : IsComponent K) : K.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨x, a, rfl⟩
  refine mem_normalizer_of_forall_conj_mem fun k hk => ?_
  have hk' : k ∈ K.map (β a).toMonoidHom := by rw [hfix a K hK]; exact hk
  obtain ⟨k', hk'K, rfl⟩ := hk'
  set L := K.map (MulAut.conj x⁻¹).toMonoidHom with hL
  have hLc : IsComponent L := CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hmem : x⁻¹ * k' * x ∈ L := ⟨k', hk'K, by simp⟩
  have hmem' : β a (x⁻¹ * k' * x) ∈ L := by
    rw [← hfix a L hLc]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨k'', hk''K, hk''⟩ := hmem'
  have h2 : x⁻¹ * k'' * x = β a (x⁻¹ * k' * x) := by
    rw [← hk'']
    simp
  have h1 : (β a x)⁻¹ * β a k' * β a x = β a (x⁻¹ * k' * x) := by
    simp [map_mul, map_inv]
  have key : x * (β a x)⁻¹ * (β a).toMonoidHom k' * (x * (β a x)⁻¹)⁻¹ = k'' := by
    calc x * (β a x)⁻¹ * (β a).toMonoidHom k' * (x * (β a x)⁻¹)⁻¹ =
        x * ((β a x)⁻¹ * β a k' * β a x) * x⁻¹ := by
          rw [MulEquiv.coe_toMonoidHom]
          group
      _ = x * (x⁻¹ * k'' * x) * x⁻¹ := by rw [h1, h2]
      _ = k'' := by group
  rw [key]
  exact hk''K

omit [Finite H] in
theorem exists_conj_eq_of_isComponent {A : Type*} [Group A] (β : A →* MulAut H)
    (hgen : Subgroup.closure {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹} = ⊤)
    {K : Subgroup H} [K.Normal] (hfix : ∀ a : A, K.map (β a).toMonoidHom = K)
    (hout : commutator (MulAut K) ≤ (MulAut.conj : K →* MulAut K).range) (h : H) :
    ∃ k ∈ K, ∀ y ∈ K, h * y * h⁻¹ = k * y * k⁻¹ := by
  set φ : H →* MulAut K := MulAut.conjNormal with hφ
  have hα : ∀ a : A, ∃ α : MulAut K, ∀ k : K, (α k : H) = β a k := fun a =>
    ⟨((β a).subgroupMap K).trans (MulEquiv.subgroupCongr (hfix a)), fun k => rfl⟩
  have hgenφ : {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹} ⊆
      ((MulAut.conj : K →* MulAut K).range.comap φ : Set H) := by
    rintro _ ⟨x, a, rfl⟩
    obtain ⟨α, hα⟩ := hα a
    have hcomm : φ (β a x) * α = α * φ x := by
      ext k
      simp only [MulAut.mul_apply, hφ, MulAut.conjNormal_apply, hα, map_mul, map_inv]
    have h1 : φ (β a x) = α * φ x * α⁻¹ := eq_mul_inv_of_mul_eq hcomm
    have h2 : φ (x * (β a x)⁻¹) = ⁅φ x, α⁆ := by
      rw [map_mul, map_inv, h1, commutatorElement_def]
      group
    show φ (x * (β a x)⁻¹) ∈ (MulAut.conj : K →* MulAut K).range
    rw [h2]
    exact hout (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hall : φ h ∈ (MulAut.conj : K →* MulAut K).range := by
    have hle := (Subgroup.closure_le _).mpr hgenφ
    rw [hgen] at hle
    exact hle (Subgroup.mem_top h)
  obtain ⟨k, hk⟩ := hall
  refine ⟨k, k.2, fun y hy => ?_⟩
  have := congrArg (fun σ : MulAut K => ((σ ⟨y, hy⟩ : K) : H)) hk
  simp only [MulAut.conj_apply, hφ, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at this
  exact this.symm

theorem exists_mem_layer_mul_mem_centralizer
    (hinner : ∀ K : Subgroup H, IsComponent K → ∀ h : H, ∃ k ∈ K, ∀ y ∈ K,
      h * y * h⁻¹ = k * y * k⁻¹) (h : H) :
    ∃ e ∈ layer H, e⁻¹ * h ∈ Subgroup.centralizer (layer H : Set H) := by
  classical
  choose k hkK hk using fun K : CFSG.LocalCores.ComponentIndex H => hinner K.1 K.2 h
  set x : ∀ K : CFSG.LocalCores.ComponentIndex H, K.1 := fun K => ⟨k K, hkK K⟩ with hx
  set e := CFSG.LocalCores.layerMul H x with he
  have heE : e ∈ layer H := by
    rw [← CFSG.LocalCores.layerMul_range]
    exact ⟨x, rfl⟩
  refine ⟨e, heE, ?_⟩
  have hK : ∀ K : CFSG.LocalCores.ComponentIndex H, ∀ y ∈ K.1,
      y * (e⁻¹ * h) = (e⁻¹ * h) * y := by
    intro K y hy
    have hu : Commute y (CFSG.LocalCores.layerMul H (Function.update x K 1)) :=
      CFSG.LocalCores.commute_layerMul_update x K hy
    have hdecomp := CFSG.LocalCores.layerMul_eq_mul_update x K
    set u := CFSG.LocalCores.layerMul H (Function.update x K 1) with hudef
    have hxK : ((x K : K.1) : H) = k K := rfl
    rw [hxK] at hdecomp
    have hkey : h * y * h⁻¹ = k K * y * (k K)⁻¹ := hk K y hy
    have hu' : y * u⁻¹ = u⁻¹ * y := hu.inv_right.eq
    calc y * (e⁻¹ * h) = y * u⁻¹ * (k K)⁻¹ * h := by rw [he, hdecomp]; group
      _ = u⁻¹ * y * (k K)⁻¹ * h := by rw [hu']
      _ = (k K * u)⁻¹ * (k K * y * (k K)⁻¹) * h := by group
      _ = (k K * u)⁻¹ * (h * y * h⁻¹) * h := by rw [hkey]
      _ = (e⁻¹ * h) * y := by rw [he, hdecomp]; group
  have hle : layer H ≤ Subgroup.centralizer {e⁻¹ * h} :=
    sSup_le fun K hKc y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hK ⟨K, hKc⟩ y hy)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

end Components

section Main

variable {H : Type*} [Group H] [Finite H]

theorem fittingSubgroup_le_oResidual (h2 : CFSG.pCore 2 H = ⊥) :
    fittingSubgroup H ≤ CFSG.GH74.GLS.oResidual 2 H := by
  intro f hf
  apply Subgroup.subset_closure
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos f).ne'
  have hfm : (f ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hfm1 := eq_one_of_mem_fittingSubgroup h2 (Subgroup.pow_mem _ hf m) hfm
  have hdvd : orderOf f ∣ m := orderOf_dvd_of_pow_eq_one hfm1
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr hm)

theorem layer_le_oResidual : layer H ≤ CFSG.GH74.GLS.oResidual 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine sSup_le fun K hK => ?_
  set N := CFSG.GH74.GLS.oResidual 2 H with hN
  have : N.Normal := oResidual_two_normal
  have hq : IsPGroup 2 (H ⧸ N) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le N le_rfl
  set φ : K →* H ⧸ N := (QuotientGroup.mk' N).comp K.subtype with hφ
  have : Group.IsPerfect K := hK.1.1
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have h2r : IsPGroup 2 φ.range := hq.to_subgroup φ.range
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsNilpotent φ.range := h2r.isNilpotent
    exact Group.IsPerfect.not_isNilpotent φ.range ‹_›
  intro k hk
  have hmem : φ ⟨k, hk⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff k).mp hmem

theorem mem_fittingSubgroup_of_mem_centralizer {y : H}
    (hyF : y ∈ Subgroup.centralizer (fittingSubgroup H : Set H))
    (hyE : y ∈ Subgroup.centralizer (layer H : Set H)) : y ∈ fittingSubgroup H := by
  set Fs := generalizedFitting H with hFs
  have hyFs : y ∈ Subgroup.centralizer (Fs : Set H) := by
    have hle : Fs ≤ Subgroup.centralizer {y} := sup_le
      (fun f hf => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hyF f hf))
      (fun f hf => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hyE f hf))
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hyFs' : y ∈ Fs := centralizer_generalizedFitting_le H hyFs
  have hFsn : Fs.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  set Zs := Fs ⊓ Subgroup.centralizer (Fs : Set H) with hZs
  have hZn : Zs.Normal := inferInstance
  have hZnil : Group.IsNilpotent Zs := by
    have : Subgroup.center Zs = ⊤ := by
      rw [eq_top_iff]
      intro b _
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp b.2.2 c c.2.1)
    exact Subgroup.isNilpotent_of_ker_le_center (1 : Zs →* Unit) (by rw [this]; exact le_top)
  have hZF : Zs ≤ fittingSubgroup H := le_sSup ⟨hZn, hZnil⟩
  exact hZF ⟨hyFs', hyFs⟩

theorem generalizedFitting_eq_oResidual
    (h2 : CFSG.pCore 2 H = ⊥) (h3 : ¬ 3 ∣ Nat.card H)
    (hrank : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup H) ≤ 2)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup 3 A) (β : A →* MulAut H)
    (hgen : Subgroup.closure {z | ∃ x : H, ∃ a : A, z = x * (β a x)⁻¹} = ⊤)
    (hcomp : ∀ K : Subgroup H, IsComponent K → Subgroup.center K = ⊥ ∧ 5 ∣ Nat.card K ∧
      commutator (MulAut K) ≤ (MulAut.conj : K →* MulAut K).range) :
    generalizedFitting H = CFSG.GH74.GLS.oResidual 2 H := by
  have hfix : ∀ a : A, ∀ K : Subgroup H, IsComponent K → K.map (β a).toMonoidHom = K := by
    intro a K hK
    obtain ⟨n, hn⟩ := hA a
    have hσ : β a ^ (3 ^ n) = 1 := by rw [← map_pow, hn, map_one]
    exact map_eq_of_isComponent (hrank 5 (by norm_num) (by norm_num))
      (fun K hK => ⟨(hcomp K hK).1, (hcomp K hK).2.1⟩) hσ hK
  have hinner : ∀ K : Subgroup H, IsComponent K → ∀ h : H, ∃ k ∈ K, ∀ y ∈ K,
      h * y * h⁻¹ = k * y * k⁻¹ := by
    intro K hK h
    have : K.Normal := normal_of_isComponent β hgen hfix hK
    exact exists_conj_eq_of_isComponent β hgen (fun a => hfix a K hK) (hcomp K hK).2.2 h
  have hF := fittingSubgroup_le_oResidual h2
  have hE : layer H ≤ CFSG.GH74.GLS.oResidual 2 H := layer_le_oResidual
  refine le_antisymm (sup_le hF hE) fun u hu => ?_
  obtain ⟨e, he, hec⟩ := exists_mem_layer_mul_mem_centralizer hinner u
  have : (layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (CFSG.GH74.GLS.oResidual 2 H).Normal := oResidual_two_normal
  set N := CFSG.GH74.GLS.oResidual 2 H ⊓ Subgroup.centralizer (layer H : Set H) with hNdef
  have hNF : N ≤ fittingSubgroup H := by
    refine le_fittingSubgroup_of_forall_coprime' (N := N)
      (fun y hy hyF => mem_fittingSubgroup_of_mem_centralizer hyF hy.2)
      fun r hr y hy hc x hx => ?_
    exact commute_of_mem_oResidual ks167GL2 h2 h3 hrank hA β hgen hr hy.1 hc hx
  have hmem : e⁻¹ * u ∈ N :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hE he)) hu, hec⟩
  have heq : u = e * (e⁻¹ * u) := by group
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_right he) (Subgroup.mem_sup_left (hNF hmem))

end Main

end CFSG.RankThree.PartTwo.Sec16.Comp167
