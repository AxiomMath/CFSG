module

public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofLF
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.KFacts.KS116Proof (uu uu_add uu_zero uu_injective)
open scoped MatrixGroups

@[expose] def L2EvenSolvableMinDegree : Prop :=
  ∀ (f : ℕ), 6 ≤ f → ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      ∀ (N : Subgroup X) [N.Normal], Group.IsSolvable N → ¬ 3 ∣ Nat.card N →
        Nonempty (X ⧸ N ≃* projSL 2 (GaloisField 2 f)) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
        (ρ : X →* (V →ₗ[ZMod p] V)), (∃ x, ρ x ≠ 1) → 7 ≤ Module.finrank (ZMod p) V

namespace LSSolvableProof

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem ker_sup_ker_sup_ker_eq_top (h2 : (2 : K) ≠ 0) {a b : Module.End K V}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) ⊔ LinearMap.ker (a * b - 1) = ⊤ := by
  have haa : ∀ v, a (a v) = v := fun v => by
    rw [← Module.End.mul_apply, ha, Module.End.one_apply]
  have hbb : ∀ v, b (b v) = v := fun v => by
    rw [← Module.End.mul_apply, hb, Module.End.one_apply]
  have hba : ∀ v, a (b v) = b (a v) := fun v => by
    rw [← Module.End.mul_apply, hab, Module.End.mul_apply]
  rw [eq_top_iff]
  intro v _
  set w := v - a v with hw
  have haw : a w = -w := by rw [hw, map_sub, haa, neg_sub]
  have h1 : v + a v ∈ LinearMap.ker (a - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_add, haa]
    abel
  have h2' : w + b w ∈ LinearMap.ker (b - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_add, hbb]
    abel
  have h3 : w - b w ∈ LinearMap.ker (a * b - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply,
      map_sub, hbb, map_sub, hba, haw, map_neg]
    abel
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hsum : (4 : K) • v = (2 : K) • (v + a v) + ((w + b w) + (w - b w)) := by
    rw [hw]
    module
  have hv : v = (4 : K)⁻¹ • ((2 : K) • (v + a v) + ((w + b w) + (w - b w))) := by
    rw [← hsum, inv_smul_smul₀ h4]
  rw [hv]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ (Submodule.add_mem _ ?_ ?_))
  · exact Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.mem_sup_left h1))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right h2')
  · exact Submodule.mem_sup_right h3

theorem finrank_le_add_ker [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {a b : Module.End K V}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Module.finrank K V ≤ Module.finrank K (LinearMap.ker (a - 1)) +
      Module.finrank K (LinearMap.ker (b - 1)) +
        Module.finrank K (LinearMap.ker (a * b - 1)) := by
  have htop := ker_sup_ker_sup_ker_eq_top h2 ha hb hab
  calc Module.finrank K V = Module.finrank K (⊤ : Submodule K V) := finrank_top K V |>.symm
    _ = Module.finrank K ↥(LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) ⊔
          LinearMap.ker (a * b - 1)) := by rw [htop]
    _ ≤ Module.finrank K ↥(LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1)) +
          Module.finrank K (LinearMap.ker (a * b - 1)) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ _ := by
          have := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.ker (a - 1))
            (LinearMap.ker (b - 1))
          omega

end Linear

section Klein

open CFSG.BenderSuzuki.PFchapter1section1 (TwoRankAtLeastTwo)

theorem mul_comm_of_mul_self {G : Type*} [Group G] (h : ∀ x : G, x * x = 1) (a b : G) :
    a * b = b * a := by
  have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h x)
  rw [← hinv (a * b), mul_inv_rev, hinv, hinv]

theorem exists_klein_of_twoRank {Y : Type*} [Group Y] (hY : TwoRankAtLeastTwo Y) :
    ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  obtain ⟨E, hcard, hsq⟩ := hY
  have hE : ∀ x : E, x * x = 1 := fun x => by rw [← sq]; exact hsq x
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have := Fintype.ofFinite E
  have hcard' : (Finset.univ : Finset E).card = 4 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset E)) (t := Finset.univ) (by rw [hcard']; simp)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset E)) (t := Finset.univ)
    (by
      rw [hcard']
      exact lt_of_le_of_lt (Finset.card_le_two : ({1, a} : Finset E).card ≤ 2) (by norm_num))
  simp only [Finset.mem_singleton] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  refine ⟨a, b, congrArg Subtype.val (hE a), congrArg Subtype.val (hE b),
    congrArg Subtype.val (mul_comm_of_mul_self hE a b), fun h => ha (Subtype.ext h),
    fun h => hb.1 (Subtype.ext h), fun h => hb.2 (Subtype.ext h).symm⟩

theorem natCard_le_four_of_mem {G : Type*} [Group G] [Finite G] {α β : G}
    (h : ∀ x : G, x = 1 ∨ x = α ∨ x = β ∨ x = β * α) : Nat.card G ≤ 4 := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  calc Finset.univ.card ≤ ({1, α, β, β * α} : Finset G).card := by
        apply Finset.card_le_card
        intro x _
        rcases h x with h | h | h | h <;> simp [h]
    _ ≤ 4 := Finset.card_le_four

theorem natCard_le_four_of_quaternion {U : Type*} [Group U] [Finite U] {n : ℕ} [NeZero n]
    (θ : QuaternionGroup n →* U) (hθ : Function.Surjective θ) (hU : ∀ x : U, x * x = 1) :
    Nat.card U ≤ 4 := by
  set α := θ (QuaternionGroup.a 1) with hα
  set β := θ (QuaternionGroup.xa 0) with hβ
  have hpow : ∀ k : ℕ, α ^ k = 1 ∨ α ^ k = α := by
    intro k
    induction k with
    | zero => exact Or.inl (pow_zero α)
    | succ k ih =>
      rcases ih with h | h
      · right; rw [pow_succ, h, one_mul]
      · left; rw [pow_succ, h, hU]
  have : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  have ha : ∀ i : ZMod (2 * n), θ (QuaternionGroup.a i) = 1 ∨ θ (QuaternionGroup.a i) = α := by
    intro i
    have : (QuaternionGroup.a i : QuaternionGroup n) = QuaternionGroup.a 1 ^ i.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow]
    exact hpow _
  apply natCard_le_four_of_mem (α := α) (β := β)
  intro x
  obtain ⟨q, rfl⟩ := hθ x
  cases q with
  | a i =>
    rcases ha i with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | xa i =>
    have : (QuaternionGroup.xa i : QuaternionGroup n) =
        QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [this, map_mul]
    rcases ha i with h | h
    · rw [h, mul_one]; exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h]; exact Or.inr (Or.inr (Or.inr rfl))

@[expose] noncomputable def uuHom (F : Type) [Field F] : Multiplicative F →* SL(2, F) where
  toFun a := uu (Multiplicative.toAdd a)
  map_one' := uu_zero
  map_mul' _ _ := uu_add _ _

theorem exists_klein_four {Y : Type*} [Group Y] [Finite Y] {f : ℕ} (hf : 3 ≤ f)
    (π : Y →* projSL 2 (GaloisField 2 f)) (hπ : Function.Surjective π) :
    ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  by_cases hY : TwoRankAtLeastTwo Y
  · exact exists_klein_of_twoRank hY
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  set E := CFSG.RankThree.PartTwo.KFacts.KS116Proof.projSLEquiv F
  set φ : Multiplicative F →* projSL 2 F := E.toMonoidHom.comp (uuHom F) with hφ
  have hφinj : Function.Injective φ :=
    E.injective.comp (fun a b h => Multiplicative.toAdd.injective (uu_injective h))
  set U : Subgroup (projSL 2 F) := φ.range with hU
  have hUcard : Nat.card U = 2 ^ f := by
    rw [hU, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_congr
      Multiplicative.toAdd, GaloisField.card 2 f (by omega)]
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hUcard]; positivity)
  have hUexp : ∀ x : U, x * x = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul, ← map_one φ]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    exact CharTwo.add_self_eq_zero _
  set Ut : Subgroup Y := U.comap π with hUt
  let πU : Ut →* U := (π.comp Ut.subtype).codRestrict U (fun x => x.2)
  have hπU : Function.Surjective πU := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := hπ u
    exact ⟨⟨y, hu⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Ut) := inferInstance
  have hUp : IsPGroup 2 U := IsPGroup.of_card hUcard
  have hPU : (P : Subgroup Ut).map πU = ⊤ := by
    have h := (P.mapSurjective hπU).is_maximal' (Q := ⊤) (hUp.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hPY : ¬ TwoRankAtLeastTwo P := fun h => hY
    (CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective (Ut.subtype.comp (P : Subgroup Ut).subtype)
      (Subtype.val_injective.comp Subtype.val_injective) h)
  obtain ⟨S⟩ : Nonempty (Sylow 2 P) := inferInstance
  have hS : (S : Subgroup P) = ⊤ := by
    have h := S.is_maximal' (Q := ⊤) (P.isPGroup'.to_subgroup ⊤) le_top
    exact h.symm
  set θ : (S : Subgroup P) →* U :=
    (πU.comp (P : Subgroup Ut).subtype).comp (S : Subgroup P).subtype with hθ
  have hθ : Function.Surjective θ := by
    intro u
    have hu : u ∈ (P : Subgroup Ut).map πU := by rw [hPU]; exact Subgroup.mem_top u
    obtain ⟨x, hx, rfl⟩ := hu
    refine ⟨⟨⟨x, hx⟩, ?_⟩, rfl⟩
    rw [hS]
    exact Subgroup.mem_top _
  have hU4 : Nat.card U ≤ 4 := by
    rcases CFSG.BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hPY S with hcyc | hq
    ·
      have : IsCyclic U := isCyclic_of_surjective θ hθ
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := U)
      have hcard := Nat.card_zpowers g
      have hzp : Subgroup.zpowers g = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact hg x
      rw [hzp, Subgroup.card_top] at hcard
      have hord : orderOf g ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact hUexp g)
      omega
    · obtain ⟨r, -, ⟨ϕ⟩⟩ := hq
      exact natCard_le_four_of_quaternion (θ.comp ϕ.symm.toMonoidHom)
        (hθ.comp ϕ.symm.surjective) hUexp
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

end Klein

theorem ker_le_of_perfect {X : Type*} [Group X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) (hsimple : IsSimpleGroup (X ⧸ N)) {M : Type*} [Monoid M]
    (ρ : X →* M) (hρ : ∃ x, ρ x ≠ 1) : ρ.ker ≤ N := by
  by_contra hK
  set K := ρ.ker with hKdef
  have hmap : K.map (QuotientGroup.mk' N) = ⊤ := by
    have : (K.map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' N)) with h | h
    · exfalso
      apply hK
      intro k hk
      have : (QuotientGroup.mk' N k) ∈ K.map (QuotientGroup.mk' N) := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exact h
  let g : N →* X ⧸ K := (QuotientGroup.mk' K).comp N.subtype
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    have hx : QuotientGroup.mk' N x ∈ K.map (QuotientGroup.mk' N) := by
      rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
    refine ⟨⟨k⁻¹ * x, hkx⟩, ?_⟩
    change QuotientGroup.mk' K (k⁻¹ * x) = QuotientGroup.mk' K x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (k⁻¹ * x)⁻¹ * x = x⁻¹ * k * x⁻¹⁻¹ := by group
    rw [this]
    exact (inferInstance : K.Normal).conj_mem k hk x⁻¹
  have : Group.IsSolvable N := hN
  have hsolv : Group.IsSolvable (X ⧸ K) := Group.isSolvable_of_surjective hg
  have hnt : Nontrivial (X ⧸ K) := by
    obtain ⟨x, hx⟩ := hρ
    refine ⟨⟨QuotientGroup.mk' K x, 1, fun h => hx ?_⟩⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_ker] at h
    exact h
  exact Group.IsPerfect.not_isSolvable (X ⧸ K) hsolv

theorem isSimpleGroup_projSL {f : ℕ} (hf : 2 ≤ f) :
    IsSimpleGroup (projSL 2 (GaloisField 2 f)) :=
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ le_rfl (Or.inr (by omega)) (Or.inr (by omega))

theorem liftKer_injective {X M : Type*} [Group X] [Monoid M] (ρ : X →* M) :
    Function.Injective (QuotientGroup.lift ρ.ker ρ (fun _ hx => hx)) := by
  intro q₁ q₂ h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker q₁
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker q₂
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
    QuotientGroup.lift_mk] at h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, MonoidHom.mem_ker,
    map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]

theorem landazuriSeitzL2EvenSolvable_of_minDegree (h : L2EvenSolvableMinDegree) :
    LandazuriSeitzL2EvenSolvable := by
  intro f hf p _ hp5 X _ _ hperf N _ hN hN3 hiso V _ _ _ ρ hρN
  obtain ⟨e⟩ := hiso
  have hρ : ∃ x, ρ x ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hρN fun x _ => hall x
  have hdim := h f hf p hp5 X hperf N hN hN3 ⟨e⟩ V ρ hρ
  have : IsSimpleGroup (projSL 2 (GaloisField 2 f)) := isSimpleGroup_projSL (by omega)
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  have hKN : ρ.ker ≤ N := @ker_le_of_perfect X _ hperf N _ hN hsimple _ _ ρ hρ
  let ρbar : X ⧸ ρ.ker →* (V →ₗ[ZMod p] V) := QuotientGroup.lift ρ.ker ρ (fun _ hx => hx)
  have hinj : Function.Injective ρbar := liftKer_injective ρ
  let π : X ⧸ ρ.ker →* projSL 2 (GaloisField 2 f) :=
    e.toMonoidHom.comp
      (QuotientGroup.map ρ.ker N (MonoidHom.id X) (by rw [Subgroup.comap_id]; exact hKN))
  have hπs : Function.Surjective π := by
    refine e.surjective.comp ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    refine ⟨QuotientGroup.mk' ρ.ker x, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.map_mk, MonoidHom.id_apply, QuotientGroup.mk'_apply]
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := exists_klein_four (by omega) π hπs
  have hK2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have hρa : ρbar a * ρbar a = 1 := by rw [← map_mul, ha, map_one]
  have hρb : ρbar b * ρbar b = 1 := by rw [← map_mul, hb, map_one]
  have hρab : ρbar a * ρbar b = ρbar b * ρbar a := by rw [← map_mul, ← map_mul, hab]
  have hsum := finrank_le_add_ker hK2 hρa hρb hρab
  obtain ⟨g, hg2, hg1, hgdim⟩ : ∃ g : X ⧸ ρ.ker, g * g = 1 ∧ g ≠ 1 ∧
      3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρbar g - 1)) := by
    by_cases h1 : 3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρbar a - 1))
    · exact ⟨a, ha, ha1, h1⟩
    by_cases h2 : 3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρbar b - 1))
    · exact ⟨b, hb, hb1, h2⟩
    refine ⟨a * b, ?_, ?_, ?_⟩
    · calc a * b * (a * b) = a * b * (b * a) := by rw [hab]
        _ = 1 := by rw [mul_assoc, ← mul_assoc b b a, hb, one_mul, ha]
    · intro h1'
      apply hne
      calc a = a * (a * b) := by rw [h1', mul_one]
        _ = b := by rw [← mul_assoc, ha, one_mul]
    · rw [map_mul]
      omega
  obtain ⟨t, htg, k, htk⟩ := TwoStarProof.exists_two_element_lift (QuotientGroup.mk' ρ.ker)
    (QuotientGroup.mk'_surjective ρ.ker) hg2
  have hρt : ρ t = ρbar g := by
    rw [← htg, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  refine ⟨t, ?_, ⟨k, htk⟩, ?_⟩
  · rw [hρt]
    intro h1
    exact hg1 (hinj (h1.trans (map_one ρbar).symm))
  · rw [hρt]
    exact hgdim

end LSSolvableProof

end CFSG.RankThree.PartTwo.Sec11
