module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTriD4Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTriD4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTriD4SchurHolds
public import CFSG.LocalAnalysis.StandardType.GGTorusFieldTransferSh

public section

namespace CFSG.StandardType.TriD4TwoRow

open CFSG CFSG.Assembly CFSG.StandardType

theorem center_eq_bot_of_simple {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem ggTorusNoLineComp_of_inn_rank {R : Type} [Group R] {I : Set (MulAut R)} (r : ℕ)
    (hZ : Subgroup.center R = ⊥) (hI : I = Set.range (MulAut.conj : R →* MulAut R))
    (hrk : ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) :
    GGTorusNoLineComp 3 r R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 _
  exfalso
  set Λ : R →* MulAut L' := ReflInner.liftConj ψ hψ hker
  have hΛinj : Function.Injective Λ := ReflInner.liftConj_injective hψ hker hZ
  have hΛmap : ∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹ := ReflInner.map_liftConj_apply hψ hker
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    rw [hI] at hφI
    obtain ⟨e, rfl⟩ := hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hle := hrk E hEab
  rw [hcardE] at hle
  norm_num at h3 hle
  omega

theorem ggTorusLiftFix_zero_of_fixedInv {R : Type} [Group R] {I F : Set (MulAut R)}
    (hker2 : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → IsPGroup 2 ψ.ker)
    (hinv : ∀ φ ∈ Subgroup.closure (I ∪ F), φ ∉ I → φ ^ 3 = 1 →
      ∃ t : R, t ≠ 1 ∧ t ^ 2 = 1 ∧ φ t = t) :
    GGTorusLiftFix 3 0 R I F := by
  classical
  intro L' _ _ ψ hψ hker hperf f hf3 hind hnot
  obtain ⟨φ, hφ, hφψ⟩ := hind
  have hφI : φ ∉ I := fun h => hnot ⟨φ, h, hφψ⟩
  have hφ3 : φ ^ 3 = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    rw [ggInduced_pow ψ hφψ 3 l, hf3]
    rfl
  obtain ⟨t, ht1, ht2, htφ⟩ := hinv φ hφ hφI hφ3
  have hfix := Line63.H5.map_ggFix_eq_of_lift ψ hψ hker (hker2 L' ψ hψ hker hperf) hf3 hφψ
  have ht : t ∈ ggFix φ := mem_ggFix.mpr htφ
  rw [hfix] at ht
  obtain ⟨l, hl, hlt⟩ := ht
  have hfl : f l = l := mem_ggFix.mp hl
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  set l₂ := l ^ m with hl₂
  have hl₂pow : l₂ ^ 2 ^ k = 1 := by
    rw [hl₂, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hψl₂ : ψ l₂ = t := by
    obtain ⟨j, rfl⟩ := hm
    rw [hl₂, map_pow, hlt, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hl₂1 : l₂ ≠ 1 := fun h => ht1 (by rw [← hψl₂, h, map_one])
  have hfl₂ : ∀ j : ℤ, f (l₂ ^ j) = l₂ ^ j := by
    intro j
    rw [map_zpow, hl₂, map_pow, hfl]
  refine ⟨Subgroup.zpowers l₂, ⊥, ?_, ?_, bot_le, CFSG.Open.isElemAbelian_bot 3, ?_, bot_inf_eq _,
    ?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact hl₂1
  · rintro ⟨_, j, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hl₂pow, one_zpow]
  · rw [Subgroup.card_bot, pow_zero]
  · rintro _ ⟨j, rfl⟩
    exact hfl₂ j
  · intro x hx
    rw [Subgroup.mem_bot] at hx
    rw [hx, map_one]

theorem ggTorusLift_zero_of_inv {R : Type} [Group R] {t : R} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    GGTorusLift 3 0 R := by
  classical
  intro L' _ _ ψ hψ _ _
  obtain ⟨l, hlt⟩ := hψ t
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  set l₂ := l ^ m with hl₂
  have hl₂pow : l₂ ^ 2 ^ k = 1 := by
    rw [hl₂, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hψl₂ : ψ l₂ = t := by
    obtain ⟨j, rfl⟩ := hm
    rw [hl₂, map_pow, hlt, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hl₂1 : l₂ ≠ 1 := fun h => ht1 (by rw [← hψl₂, h, map_one])
  refine ⟨Subgroup.zpowers l₂, ⊥, ?_, ?_, bot_le, CFSG.Open.isElemAbelian_bot 3, ?_, bot_inf_eq _⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact hl₂1
  · rintro ⟨_, j, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hl₂pow, one_zpow]
  · rw [Subgroup.card_bot, pow_zero]

theorem ker_eq_bot_triD4
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (hs : IsSimpleGroup (GGTriD4R n K))
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥) {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* GGTriD4R n K) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : ψ.ker = ⊥ := by
  have hkc : ψ.ker = Subgroup.center L' := TableBUR.ker_eq_center_of_surjective hψ hker hZ
  let θ : L' ⧸ Subgroup.center L' ≃* GGTriD4R n K :=
    (QuotientGroup.quotientMulEquivOfEq hkc.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  rw [hkc]
  exact ggTriD4SchurInput_holds n hn K hK hs L' hperf θ

theorem ggTorusNoLineFieldComp_of_self {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)}
    (hker : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ψ.ker = ⊥)
    (h : ∀ A : Subgroup (MulAut R), IsElemAbelian p A →
      (∀ a ∈ A, a ∈ Subgroup.closure (I ∪ F)) →
      p ^ (r + 1) ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set R,
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          ∀ a₀ ∈ A, a₀ ≠ 1 → a₀ ∈ I → GGFixCompCyclic p a₀ →
            ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)) :
    GGTorusNoLineFieldComp p r R I F := by
  classical
  intro L' _ _ ψ hψ hker' hperf A hA hAI hr h3 hsc
  have hinj : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp (hker L' ψ hψ hker' hperf)
  let e : L' ≃* R := MulEquiv.ofBijective ψ ⟨hinj, hψ⟩
  have he : ∀ l, e l = ψ l := fun _ => rfl
  let c : MulAut L' ≃* MulAut R := MulAut.congr e
  have hc : ∀ (a : MulAut L') (l : L'), c a (ψ l) = ψ (a l) := by
    intro a l
    rw [← he, ← he]
    simp [c, MulAut.congr_apply]
  have hcφ : ∀ (a : MulAut L') (φ : MulAut R), (∀ l, φ (ψ l) = ψ (a l)) → φ = c a := by
    intro a φ hφ
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [hφ l, hc]
  have hconj : ∀ n : L', c (MulAut.conj n) = MulAut.conj (ψ n) := by
    intro n
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [hc, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set A' : Subgroup (MulAut R) := A.map c.toMonoidHom with hA'
  have hA'ab : IsElemAbelian p A' := TableB.isElemAbelian_map hA c.toMonoidHom
  have hAI' : ∀ a ∈ A', a ∈ Subgroup.closure (I ∪ F) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    have he' := hcφ a φ hφa
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← he']
    exact hφ
  have hcard : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective c.injective
  have hsc' : GGTorusSelfCent p A' := by
    intro n hn hnp
    obtain ⟨m, rfl⟩ := hψ n
    have hm : ∀ a ∈ A, a m = m := by
      intro a ha
      apply hinj
      rw [← hc]
      exact hn _ ⟨a, ha, rfl⟩
    have hmp : m ^ p = 1 := hinj (by rw [map_pow, hnp, map_one])
    exact ⟨MulAut.conj m, hsc m hm hmp, hconj m⟩
  obtain ⟨W', hW'1, hW'2⟩ :=
    h A' hA'ab hAI' (by rw [hcard]; exact hr) (by rw [hcard]; exact h3) hsc'
  have hdiff : ∀ (a : MulAut L') (n : L'), ψ (n * (a n)⁻¹) = ψ n * ((c a) (ψ n))⁻¹ := by
    intro a n
    rw [map_mul, map_inv, hc]
  refine ⟨{l | ψ l ∈ W'}, ?_, ?_⟩
  · intro n hn a ha
    obtain ⟨h1, h2⟩ := hW'1 (ψ n) hn (c a) ⟨a, ha, rfl⟩
    refine ⟨hinj ?_, fun a' ha' => hinj ?_⟩
    · rw [map_pow, hdiff, h1, map_one]
    · rw [← hc, hdiff]
      exact h2 (c a') ⟨a', ha', rfl⟩
  · intro hN a₀ ha₀ ha₀1 hI hcyc
    have hN' : ∀ n ∈ W', ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
      intro n hn a ha
      obtain ⟨m, rfl⟩ := hψ n
      obtain ⟨b, hb, rfl⟩ := ha
      refine ⟨MulAut.conj m * b * (MulAut.conj m)⁻¹, hN m hn b hb, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hconj]
    obtain ⟨φ, hφI, hφa⟩ := hI
    have hca₀I : c a₀ ∈ I := by rw [← hcφ a₀ φ hφa]; exact hφI
    have hca₀1 : c a₀ ≠ 1 := fun h1 => ha₀1 (c.injective (by rw [h1, map_one]))
    have hcyc' : GGFixCompCyclic p (c a₀) := ggFixCompCyclic_map_prime hp hψ hker' (hc a₀) hcyc
    obtain ⟨n', hn', hnot⟩ := hW'2 hN' (c a₀) ⟨a₀, ha₀, rfl⟩ hca₀1 hca₀I hcyc'
    obtain ⟨n, rfl⟩ := hψ n'
    refine ⟨n, hn', fun hmem => hnot ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow, hk, map_mul, map_mul, map_inv, hconj]

theorem fieldCompSelf_of_lines {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hZ : Subgroup.center R = ⊥)
    (hlines : ∀ A : Subgroup (MulAut R), IsElemAbelian p A →
      (∀ a ∈ A, a ∈ Subgroup.closure (I ∪ F)) → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∀ a₀ ∈ A, a₀ ≠ 1 → a₀ ∈ I → GGFixCompCyclic p a₀ →
        ∃ n : R, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut R)) ∧
          MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)
    (A : Subgroup (MulAut R)) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ Subgroup.closure (I ∪ F)) (h3 : p ^ 3 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ W : Set R,
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
        ∀ a₀ ∈ A, a₀ ≠ 1 → a₀ ∈ I → GGFixCompCyclic p a₀ →
          ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀) := by
  classical
  have hconj_inj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    intro x y hxy
    have hz : x⁻¹ * y ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut R => φ g) hxy
      simp only [MulAut.conj_apply] at h1
      calc g * (x⁻¹ * y) = x⁻¹ * (x * g * x⁻¹) * y := by group
        _ = x⁻¹ * (y * g * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz
  have hca : ∀ (a : MulAut R) (n : R), MulAut.conj (a n) = a * MulAut.conj n * a⁻¹ := by
    intro a n
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hdiff : ∀ n ∈ {n : R | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut R))},
      ∀ a ∈ A, MulAut.conj (n * (a n)⁻¹) ∈ A := by
    intro n hn a ha
    rw [map_mul, map_inv, hca]
    have h1 : MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hn a).mp ha
    have : MulAut.conj n * (a * MulAut.conj n * a⁻¹)⁻¹ =
        (MulAut.conj n * a * (MulAut.conj n)⁻¹) * a⁻¹ := by group
    rw [this]
    exact A.mul_mem h1 (A.inv_mem ha)
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut R))}, ?_, ?_⟩
  · intro n hn a ha
    have hm := hdiff n hn a ha
    refine ⟨hconj_inj ?_, fun a' ha' => hconj_inj ?_⟩
    · rw [map_pow, map_one]
      exact hA.2 _ hm
    · rw [hca]
      have hcomm := TableB.IsElemAbelian.comm hA ha' hm
      rw [hcomm, mul_inv_cancel_right]
  · intro _ a₀ ha₀ ha₀1 hI hcyc
    obtain ⟨n, hn, hnot⟩ := hlines A hA hAI h3 hsc a₀ ha₀ ha₀1 hI hcyc
    exact ⟨n, hn, hnot⟩

abbrev GGTriD4F (n : ℕ) (K : Type) [Field K] : Set (MulAut (GGTriD4R n K)) :=
  LargeEvenChevFieldImage LargeEvenCartanD4 K
    (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)

@[expose] def GGTriD4TwoModelFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 3 → IsSimpleGroup (GGTriD4R 1 K) →
    (∃ a b : GGTriD4R 1 K, a * b ≠ b * a) →
    (∃ t : GGTriD4R 1 K, t ≠ 1 ∧ t ^ 2 = 1) ∧
    (∀ φ ∈ Subgroup.closure (GGTriD4ID 1 K ∪ GGTriD4F 1 K), φ ∉ GGTriD4ID 1 K → φ ^ 3 = 1 →
      ∃ t : GGTriD4R 1 K, t ≠ 1 ∧ t ^ 2 = 1 ∧ φ t = t) ∧
    (∀ A : Subgroup (MulAut (GGTriD4R 1 K)), IsElemAbelian 3 A →
      (∀ a ∈ A, a ∈ Subgroup.closure (GGTriD4ID 1 K ∪ GGTriD4F 1 K)) → 3 ^ 3 ≤ Nat.card A →
      GGTorusSelfCent 3 A →
      ∀ a₀ ∈ A, a₀ ≠ 1 → a₀ ∈ GGTriD4ID 1 K → GGFixCompCyclic 3 a₀ →
        ∃ n : GGTriD4R 1 K, MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut (GGTriD4R 1 K))) ∧
          MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)

theorem ggNbrKGFieldTriD4Two_of_model
    (h : GGTriD4TwoModelFacts) : GGNbrKGFieldTriD4Two := by
  intro lab hlab ht hn1
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht hn1
  subst ht
  subst hn1
  intro Q hQ
  refine recipeTwisted_and (P := GGNbrWeylFieldKLevelComp 3) (fun K _ _ hK hs hna => ?_) hQ
  obtain ⟨⟨t, ht1, ht2⟩, hinv, hlines⟩ := h K hK hs hna
  have hZ := center_eq_bot_of_simple hs hna
  have hI : GGTriD4ID 1 K = Set.range (MulAut.conj : GGTriD4R 1 K →* MulAut (GGTriD4R 1 K)) :=
    ggTriD4InnDiagInput_holds 1 le_rfl K hK hs
  have hrk := ggTriD4_card_le_of_isElemAbelian 1 le_rfl K hK hs
  have hkerb : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* GGTriD4R 1 K),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ψ.ker = ⊥ :=
    fun L' _ _ ψ hψ hker hperf => ker_eq_bot_triD4 le_rfl hK hs hZ ψ hψ hker hperf
  refine ⟨fun g => by change MulAut.conj g ∈ GGTriD4ID 1 K; rw [hI]; exact ⟨g, rfl⟩, 0,
    ggTorusLift_zero_of_inv ht1 ht2,
    ggTorusLiftFix_zero_of_fixedInv (fun L' _ _ ψ hψ hker hperf => by
      rw [hkerb L' ψ hψ hker hperf]; exact IsPGroup.of_bot) hinv,
    ggTorusNoLineComp_of_inn_rank 0 hZ hI hrk,
    ggTorusNoLineFieldComp_of_self Nat.prime_three hkerb
      (fun A hA hAI _ h3 hsc => fieldCompSelf_of_lines hZ hlines A hA hAI h3 hsc)⟩

end CFSG.StandardType.TriD4TwoRow

