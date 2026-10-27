module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofCases
public import CFSG.CGT.T75N.L29Kernel
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

@[expose] def Step208CaseOneL32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M} →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 1)) →
    ¬ kTwenty M c ≤ N →
    Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))) →
    kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T →
    CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) →
    CFSG.Open.pCoreOf 2 (kTwenty M c) = CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)

variable {G : Type} [Group G] [Finite G]

theorem transvection_mulVec_sub {F : Type} [Field F] {i j : Fin 3} (hij : i ≠ j) (a : F)
    (w : Fin 3 → F) :
    (Matrix.SpecialLinearGroup.transvection hij a : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w =
      Pi.single i (a * w j) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext k
  simp [Matrix.add_mulVec, Matrix.single_mulVec, Pi.single_apply, Function.update_apply]

theorem forall_of_sl3_invariant {F : Type} [Field F] {P : (Fin 3 → F) → Prop}
    (hsub : ∀ x y, P x → P y → P (x - y))
    (hinv : ∀ (g : SpecialLinearGroup (Fin 3) F) x, P x →
      P ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x))
    {v : Fin 3 → F} (hv : P v) (hv0 : v ≠ 0) (x : Fin 3 → F) : P x := by
  have h0 : P 0 := by simpa using hsub v v hv hv
  have hadd : ∀ x y, P x → P y → P (x + y) := fun x y hx hy => by
    simpa using hsub x (0 - y) hx (hsub 0 y h0 hy)
  have step : ∀ w, P w → ∀ i j : Fin 3, i ≠ j → ∀ a : F, P (Pi.single i (a * w j)) := by
    intro w hw i j hij a
    rw [← transvection_mulVec_sub hij a w]
    exact hsub _ _ (hinv _ w hw) hw
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hj' : ∀ i, i ≠ j → ∀ b : F, P (Pi.single i b) := by
    intro i hij b
    have := step v hv i j hij (b / v j)
    rwa [div_mul_cancel₀ b hj] at this
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 3, i₀ ≠ j := by fin_cases j <;> decide
  have hall : ∀ (k : Fin 3) (b : F), P (Pi.single k b) := by
    intro k b
    by_cases hk : k = j
    · subst hk
      have := step _ (hj' i₀ hi₀ 1) k i₀ (Ne.symm hi₀) b
      simpa using this
    · exact hj' k hk b
  have hx : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) + Pi.single 2 (x 2) := by
    ext k
    fin_cases k <;> simp
  rw [hx]
  exact hadd _ _ (hadd _ _ (hall 0 _) (hall 1 _)) (hall 2 _)

omit [Finite G] in
theorem eq_of_le_of_natural {K Q V : Subgroup G} {F : Type} [Field F]
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (β : ↥Q →* Multiplicative (Fin 3 → F))
    (hβinj : Function.Injective β)
    (hβ : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * (a : G)⁻¹ →
      Multiplicative.toAdd (β v) =
        (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    (hVQ : V ≤ Q) (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hV0 : V ≠ ⊥) : V = Q := by
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV0
  have hsub : ∀ x y : Fin 3 → F,
      (∃ q : ↥Q, (q : G) ∈ V ∧ Multiplicative.toAdd (β q) = x) →
      (∃ q : ↥Q, (q : G) ∈ V ∧ Multiplicative.toAdd (β q) = y) →
      ∃ q : ↥Q, (q : G) ∈ V ∧ Multiplicative.toAdd (β q) = x - y := by
    rintro x y ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
    refine ⟨q₁ * q₂⁻¹, V.mul_mem hq₁ (V.inv_mem hq₂), ?_⟩
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hinv : ∀ (g : SpecialLinearGroup (Fin 3) F) (x : Fin 3 → F),
      (∃ q : ↥Q, (q : G) ∈ V ∧ Multiplicative.toAdd (β q) = x) →
      ∃ q : ↥Q, (q : G) ∈ V ∧
        Multiplicative.toAdd (β q) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
    rintro g x ⟨q, hq, rfl⟩
    obtain ⟨a, rfl⟩ := hαs g
    have hq' : (a : G) * q * (a : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hKQ a.2) q).mp q.2
    exact ⟨⟨_, hq'⟩, (Subgroup.mem_normalizer_iff.mp (hKV a.2) q).mp hq, hβ a q ⟨_, hq'⟩ rfl⟩
  have hwQ : (w : G) ∈ Q := hVQ w.2
  have hv0 : Multiplicative.toAdd (β ⟨w, hwQ⟩) ≠ 0 := by
    intro h
    apply hw
    have h1 : β ⟨w, hwQ⟩ = β 1 := by
      rw [map_one]
      exact toAdd_eq_zero.mp h
    have h2 := congrArg Subtype.val (hβinj h1)
    exact Subtype.ext (by simpa using h2)
  have hall := forall_of_sl3_invariant hsub hinv ⟨⟨w, hwQ⟩, w.2, rfl⟩ hv0
  refine le_antisymm hVQ fun q hq => ?_
  obtain ⟨q', hq'V, hq'⟩ := hall (Multiplicative.toAdd (β ⟨q, hq⟩))
  have hqq : (q' : G) = q := congrArg Subtype.val (hβinj (Multiplicative.toAdd.injective hq'))
  rw [← hqq]
  exact hq'V

omit [Finite G] in
theorem le_normalizer_commutator_right (H K : Subgroup G) :
    K ≤ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ k ∈ K, ∀ y ∈ ⁅H, K⁆, k * y * k⁻¹ ∈ ⁅H, K⁆ := by
    intro k hk y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨h, hh, a, ha, rfl⟩ := hz
      have e : k * ⁅h, a⁆ * k⁻¹ = ⁅h, k⁆⁻¹ * ⁅h, k * a⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (inv_mem (Subgroup.commutator_mem_commutator hh hk))
        (Subgroup.commutator_mem_commutator hh (mul_mem hk ha))
    | one => simp
    | mul y z _ _ hy hz =>
      rw [show k * (y * z) * k⁻¹ = (k * y * k⁻¹) * (k * z * k⁻¹) by group]
      exact mul_mem hy hz
    | inv y _ hy =>
      rw [show k * y⁻¹ * k⁻¹ = (k * y * k⁻¹)⁻¹ by group]
      exact inv_mem hy
  intro k hk
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨key k hk y, fun h => ?_⟩
  have := key k⁻¹ (inv_mem hk) _ h
  rwa [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at this

theorem vTwenty_eq_c134Q_of_natural_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N) {F : Type} [Field F]
    (α : ↥(kTwenty M c) →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hKQ : kTwenty M c ≤ Subgroup.normalizer
      ((CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) : Subgroup G) : Set G))
    (β : ↥(CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)) →* Multiplicative (Fin 3 → F))
    (hβinj : Function.Injective β)
    (hβ : ∀ (a : ↥(kTwenty M c)) (u v : ↥(CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c))),
      (v : G) = a * u * (a : G)⁻¹ →
        Multiplicative.toAdd (β v) =
          (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u)) :
    vTwenty M c T = CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) :=
  eq_of_le_of_natural α hαs hKQ β hβinj hβ
    (Subgroup.commutator_mono (fun _ hz => (mem_center_pCoreOf_of_mem_zTwenty_core hT hz).1)
      le_rfl)
    (le_normalizer_commutator_right _ _)
    (fun h => hKN ((le_inf le_rfl (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h))).trans h207))

theorem isPerfect_of_sl3 {K : Subgroup G} {F : Type} [Field F]
    (hres : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → N = ⊤)
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K) : Group.IsPerfect ↥K := by
  have hSL : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl
  refine ⟨hres (commutator ↥K) fun y => ?_⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (commutator ↥K) y
  have hmap : (commutator ↥K).map α = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hαs]
    exact hSL.commutator_eq_top
  have hmem : α k ∈ (commutator ↥K).map α := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp hmem
  have hO : ((k'⁻¹ * k : ↥K) : G) ∈ CFSG.Open.pCoreOf 2 K := by
    rw [← hαk, map_mul, map_inv, hkk', inv_mul_cancel]
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨_, hO⟩
  refine ⟨m, ?_⟩
  have hk'1 : QuotientGroup.mk' (commutator ↥K) k' = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk'
  have hkk : QuotientGroup.mk' (commutator ↥K) k =
      QuotientGroup.mk' (commutator ↥K) (k'⁻¹ * k) := by
    rw [map_mul, map_inv, hk'1, inv_one, one_mul]
  have hpow : (k'⁻¹ * k) ^ 2 ^ m = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hm
    simpa using this
  rw [hkk, ← map_pow, hpow, map_one]

omit [Finite G] in
theorem pCoreOf_le_of_schur
    {K Q : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
    (h8 : 8 ≤ Nat.card F) [Group.IsPerfect ↥K]
    (α : ↥K →* SpecialLinearGroup (Fin 3) F) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hQK : Q ≤ K) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQO : Q ≤ CFSG.Open.pCoreOf 2 K) (hcomm : ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ Q) :
    CFSG.Open.pCoreOf 2 K ≤ Q := by
  have : (Q.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hKQ
  have hle : Q.subgroupOf K ≤ α.ker := fun x hx =>
    MonoidHom.mem_ker.mpr ((hαk x).mpr (hQO (Subgroup.mem_subgroupOf.mp hx)))
  set π : (↥K ⧸ Q.subgroupOf K) →* SpecialLinearGroup (Fin 3) F :=
    QuotientGroup.lift (Q.subgroupOf K) α hle with hπ
  have hπmk : ∀ k : ↥K, π (k : ↥K ⧸ Q.subgroupOf K) = α k := fun k => by
    rw [hπ, QuotientGroup.lift_mk]
  have hπs : Function.Surjective π := by
    intro g
    obtain ⟨k, rfl⟩ := hαs g
    exact ⟨(k : ↥K ⧸ Q.subgroupOf K), hπmk k⟩
  have : Group.IsPerfect (↥K ⧸ Q.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Q.subgroupOf K))
      (QuotientGroup.mk'_surjective _)
  have hcen : π.ker ≤ Subgroup.center (↥K ⧸ Q.subgroupOf K) := by
    intro y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    have hk : (k : G) ∈ CFSG.Open.pCoreOf 2 K := by
      rw [← hαk, ← hπmk]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := Subgroup.commutator_mem_commutator (inv_mem hk) (inv_mem k'.2)
    have e : (((k' * k)⁻¹ * (k * k') : ↥K) : G) = ⁅(k : G)⁻¹, (k' : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact hcomm h
  have hker := ker_eq_bot_of_generic (m := 1) (Or.inr (Or.inl ⟨rfl, h8⟩)) π hπs hcen
  intro x hx
  have hxK : x ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hx
  have h1 : ((⟨x, hxK⟩ : ↥K) : ↥K ⧸ Q.subgroupOf K) ∈ π.ker := by
    rw [MonoidHom.mem_ker, hπmk]
    exact (hαk ⟨x, hxK⟩).mpr hx
  rw [hker, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem eq_of_card_sl3_eq {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F'] {a b : ℕ}
    (hF : Nat.card F = 2 ^ a) (hF' : Nat.card F' = 2 ^ b)
    (h : Nat.card (SpecialLinearGroup (Fin 3) F) = Nat.card (SpecialLinearGroup (Fin 3) F')) :
    a = b := by
  have ha : a ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    rw [hF] at this
    norm_num at this
  have hb : b ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F')
    rw [hF'] at this
    norm_num at this
  have hodd : ∀ k : ℕ, k ≠ 0 → Odd (2 ^ k - 1) := fun k hk =>
    Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' hk).mpr even_two) odd_one
  have e : ∀ {K : Type} [Field K] [Finite K] {k : ℕ}, Nat.card K = 2 ^ k →
      Nat.card (SpecialLinearGroup (Fin 3) K) =
        2 ^ (k * 3) * ((2 ^ (k * 2) - 1) * (2 ^ (k * 3) - 1)) := by
    intro K _ _ k hK
    rw [LinearFlag.card_SL_eq (by norm_num), hK, show (3 * (3 - 1) / 2 : ℕ) = 3 by norm_num,
      show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num), ← pow_mul, ← pow_mul]
  rw [e hF, e hF'] at h
  have := eq_of_two_pow_mul_eq ((hodd _ (by omega)).mul (hodd _ (by omega)))
    ((hodd _ (by omega)).mul (hodd _ (by omega))) h
  omega

theorem conclusion_of_isC134Case_one_core
    {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hone : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 1)) →
      CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) →
      CFSG.Open.pCoreOf 2 (kTwenty M c) = CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c))
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n)))
    (hKN : ¬ kTwenty M c ≤ N)
    (hpar : Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))))
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := h3
  have hi' := hi
  obtain ⟨⟨hshort, -⟩, n', F, _, _, hF, hKQ, α, hαs, hαk, β, hβs, hβk, hβ⟩ := hi'
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hβinj := injective_of_ker_eq β hβk
  have hα'k := toSL_eq_one_iff_mem hαk
  have hVQ : vTwenty M c T = CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) :=
    vTwenty_eq_c134Q_of_natural_core hT h207 hKN (toSL α) (toSL_surjective hαs) hKQ β hβinj
      (fun a u v huv => by rw [hβ a u v huv, coe_toSL])
  have hKTK : kTwenty M c ⊔ T ≤ Subgroup.normalizer (kTwenty M c : Set G) :=
    sup_le Subgroup.le_normalizer (hT.sylow.le.trans hMK)
  have hQK : CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤ kTwenty M c := by
    rw [CFSG.Quasithin.c134Q, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTK)
  have hQO : CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) ≤
      CFSG.Open.pCoreOf 2 (kTwenty M c) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQK hKQ
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le c134Q_le)
  have hOO : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      (hKTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hn'n : n' = n := by
    have hker : (toSL α).ker = CFSG.pCore 2 ↥(kTwenty M c) := by
      ext k
      rw [MonoidHom.mem_ker, toSL_eq_one_iff, ← MonoidHom.mem_ker, hαk]
    have h1 : Nat.card (SpecialLinearGroup (Fin 3) F) =
        Nat.card (↥(kTwenty M c) ⧸ CFSG.pCore 2 ↥(kTwenty M c)) := by
      rw [← hker]
      exact (Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective _ (toSL_surjective hαs)).toEquiv).symm
    have h2 : Nat.card (↥(kTwenty M c) ⧸ CFSG.pCore 2 ↥(kTwenty M c)) =
        Nat.card (SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :=
      Nat.card_congr ((e.trans (projSLEquivStatedSL hn)).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 _).symm).toEquiv
    exact eq_of_card_sl3_eq (by rw [Nat.card_eq_fintype_card, hF])
      (GaloisField.card 2 n hn.pos.ne') (h1.trans h2)
  have hn'odd : Odd n' := hn'n ▸ hn
  have hOQ : CFSG.Open.pCoreOf 2 (kTwenty M c) =
      CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) := by
    rcases Nat.lt_or_ge n' 3 with h1 | h3'
    · have hn1 : n = 1 := by
        obtain ⟨k, hk⟩ := hn'odd
        omega
      subst hn1
      exact hone ⟨e⟩ hi
    · have : Group.IsPerfect ↥(kTwenty M c) :=
        isPerfect_of_sl3 hshort.1 (toSL α) (toSL_surjective hαs) hα'k
      have h8 : 8 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card, hF]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) h3'
      exact le_antisymm (pCoreOf_le_of_schur h8 (toSL α) (toSL_surjective hαs) hα'k hQK hKQ hQO
        (Subgroup.commutator_mono hOO le_rfl)) hQO
  refine ⟨⟨IsShort2.isShort (L := kTwenty M c) hshort, hKM,
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK).isSubnormal⟩,
    hVQ.trans hOQ.symm, n', hn'odd, hVQ ▸ hQK, F, inferInstance, inferInstance, hF, toSL α,
    toSL_surjective hαs, ?_, (MulEquiv.subgroupCongr hVQ).trans
      (MulEquiv.ofBijective β ⟨hβinj, hβs⟩), fun k v w hvw => ?_⟩
  · ext k
    rw [MonoidHom.mem_ker, hα'k, Subgroup.mem_subgroupOf, hVQ, ← hOQ]
  · show Multiplicative.toAdd (β (MulEquiv.subgroupCongr hVQ w)) =
      (toSL α k : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β (MulEquiv.subgroupCongr hVQ v))
    rw [coe_toSL]
    exact hβ k _ _ hvw

theorem conclusion_of_isC134Case_one
    (hone : Step208CaseOneL32)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (hTN : T ≤ N)
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (h3 : ∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n)))
    (hKN : ¬ kTwenty M c ≤ N)
    (hpar : Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))))
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.IsC134Case 1 (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n :=
  conclusion_of_isC134Case_one_core
    (fun e hi => hone G A M L N c T hT hTN h204 h207 e hKN hpar hLQ hi) hT.toCtx20 hTN h204 h207
    h3 hKN hpar hLQ hi

theorem step208CasesCtxFour_of
    (hone : Step208CaseOneL32) : Step208CasesCtxFour := by
  intro G _ _ A M L N c T hT hTN h204 h207 h3 hKN hpar hLQ i hi1 hi4 hi
  interval_cases i
  · exact conclusion_of_isC134Case_one hone hT hTN h204 h207 h3 hKN hpar hLQ hi
  · exact (false_of_isC134Case_two hT hTN h207 hKN hLQ hi).elim
  · exact (false_of_isC134Case_three hT hTN h207 hKN hLQ hi).elim
  · exact (false_of_isC134Case_four hT hTN h207 hKN hLQ hi).elim

end CFSG.RankThree.PartTwo.Sec20
