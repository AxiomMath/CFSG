module

public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofLNormal
import CFSG.RankThree.PartTwo.Sec18.Item181b
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSL3
public import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofCount

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec20
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2

theorem card_comap_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup H) :
    Nat.card ↥(N.comap f) = Nat.card ↥f.ker * Nat.card ↥N := by
  have : Finite H := Finite.of_surjective f hf
  have h1 := (N.comap f).card_mul_index
  have h2 := N.card_mul_index
  have h3 : (N.comap f).index = N.index := Subgroup.index_comap_of_surjective N hf
  have h4 : Nat.card G = Nat.card H * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [h3] at h1
  have h5 : Nat.card ↥(N.comap f) * N.index = Nat.card ↥f.ker * Nat.card ↥N * N.index := by
    rw [h1, h4, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h5

section Urad

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def uradConj {v : SpecialLinearGroup (Fin 3) F} (hv : v ∈ lstab F) :
    MulAut ↥(urad F) :=
  ((MulAut.conj v).subgroupMap (urad F)).trans (MulEquiv.subgroupCongr (by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact conj_mem_urad hv hu
    · intro u hu
      refine ⟨v⁻¹ * u * v, ?_, by simp [mul_assoc]⟩
      have := conj_mem_urad ((lstab F).inv_mem hv) hu
      simpa using this))

omit [Finite F] in
theorem uradConj_apply {v : SpecialLinearGroup (Fin 3) F} (hv : v ∈ lstab F) (u : ↥(urad F)) :
    ((uradConj hv u : ↥(urad F)) : SpecialLinearGroup (Fin 3) F) = v * u * v⁻¹ := rfl

theorem eq_one_of_mem_urad_of_commute (hF : Nat.card F = 2) {v : SpecialLinearGroup (Fin 3) F}
    (hv : v ∈ vstab F) (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ urad F) (huv : u * v = v * u) : u = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hφ3 : (uradConj (vstab_le_lstab hv)) ^ 3 = 1 := by
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [MulAut.one_apply, pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply, uradConj_apply,
      uradConj_apply, uradConj_apply]
    have hv3' : v * v * v = 1 := by rw [← hv3, pow_succ, pow_two]
    calc v * (v * (v * (w : SpecialLinearGroup (Fin 3) F) * v⁻¹) * v⁻¹) * v⁻¹ =
        (v * v * v) * w * (v * v * v)⁻¹ := by group
      _ = w := by rw [hv3']; group
  set φ := uradConj (vstab_le_lstab hv) with hφ
  have hP := isPGroup_zpowers_of_pow_eq_one (p := 3) hφ3
  have hmod := hP.card_modEq_card_fixedPoints ↥(urad F)
  set H := fixSubgroup φ with hH
  have he : MulAction.fixedPoints (Subgroup.zpowers φ) ↥(urad F) = (H : Set ↥(urad F)) := by
    ext w
    exact forall_zpowers_fix_iff
  rw [he] at hmod
  have hmod' : Nat.card ↥(urad F) ≡ Nat.card H [MOD 3] := hmod
  have hcard : Nat.card ↥(urad F) = 4 := by rw [card_urad, hF]; norm_num
  have hdvd : Nat.card H ∣ 4 := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have hH1 : Nat.card H = 1 := by
    have h4 : Nat.card H ≠ 4 := by
      intro h4
      have htop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [h4, hcard])
      obtain ⟨u', hu', hne⟩ := exists_commutator_ne_one hv (not_mem_urad_of_pow_three hv3 hv1)
      apply hne
      have hmem : (⟨u', hu'⟩ : ↥(urad F)) ∈ H := htop ▸ Subgroup.mem_top _
      have h1 : (φ ⟨u', hu'⟩ : SpecialLinearGroup (Fin 3) F) = u' :=
        congrArg Subtype.val hmem
      rw [uradConj_apply] at h1
      have h2 : u' * v = v * u' := by
        calc u' * v = (v * u' * v⁻¹) * v := by rw [h1]
          _ = v * u' := by group
      rw [h2]
      group
    have h2 : Nat.card H ≠ 2 := by
      intro h2
      rw [hcard, h2] at hmod'
      exact absurd hmod' (by decide)
    have : Nat.card H ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card H <;> simp_all
  have hbot := Subgroup.eq_bot_of_card_eq H hH1
  have hmem : (⟨u, hu⟩ : ↥(urad F)) ∈ H := by
    show φ ⟨u, hu⟩ = ⟨u, hu⟩
    apply Subtype.ext
    rw [uradConj_apply]
    calc v * u * v⁻¹ = (u * v) * v⁻¹ := by rw [huv]
      _ = u := by group
  rw [hbot] at hmem
  exact congrArg Subtype.val ((Subgroup.mem_bot).mp hmem)

end Urad

section X

variable {G : Type} [Group G] [Finite G]
variable {K N : Subgroup G} {c : G} {F : Type} [Field F] [Finite F]
  {α : ↥K →* SpecialLinearGroup (Fin 3) F}

omit [Finite G] [Finite F] in
theorem normalClosureIn_le_inf (hcK : c ∈ K) (hcN : c ∈ N) :
    normalClosureIn (K ⊓ N) c ≤ K ⊓ N :=
  normalClosureIn_le ⟨hcK, hcN⟩

omit [Finite G] [Finite F] in
theorem map_X_le_vstab (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) (hcK : c ∈ K)
    (hcN : c ∈ N) : ((normalClosureIn (K ⊓ N) c).subgroupOf K).map α ≤ vstab F := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hN x).mp ((normalClosureIn_le_inf hcK hcN (Subgroup.mem_subgroupOf.mp hx)).2)

omit [Finite F] in
theorem alpha_c_props (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) (hcK : c ∈ K) (hcN : c ∈ N)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    α ⟨c, hcK⟩ ∈ vstab F ∧ α ⟨c, hcK⟩ ^ 3 = 1 ∧ α ⟨c, hcK⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(hN ⟨c, hcK⟩).mp hcN, ?_, fun h => ?_⟩
  · rw [← map_pow]
    have : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  · have hcO := (hαk ⟨c, hcK⟩).mp h
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨c, hcO⟩
    have hj' : c ^ (2 ^ j) = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    exact hc1 (Sec18.eq_one_of_pow_three_of_pow_two_pow hc3 hj')

omit [Finite G] [Finite F] in
theorem mem_normalizer_X (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) {k : ↥K}
    (hk : α k ∈ vstab F) :
    (k : G) ∈ Subgroup.normalizer (normalClosureIn (K ⊓ N) c : Set G) :=
  le_normalizer_normalClosureIn (K ⊓ N) c ⟨k.2, (hN k).mpr hk⟩

omit [Finite G] [Finite F] in
theorem vstab_le_normalizer_map_X (hαs : Function.Surjective α)
    (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) :
    vstab F ≤ Subgroup.normalizer
      ((((normalClosureIn (K ⊓ N) c).subgroupOf K).map α : Subgroup _) :
        Set (SpecialLinearGroup (Fin 3) F)) := by
  intro h hh
  obtain ⟨k, rfl⟩ := hαs h
  have hkX := mem_normalizer_X (c := c) hN hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨k * y * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hkX _).mp (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨y, hy, hyx⟩
    refine ⟨k⁻¹ * y * k, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer _).inv_mem hkX) _).mp (Subgroup.mem_subgroupOf.mp hy)
      simpa using this
    · have : α y = α k * x * (α k)⁻¹ := hyx
      rw [map_mul, map_mul, map_inv, this]
      group

theorem urad_le_map_X (hF : Nat.card F = 2) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) (hcK : c ∈ K) (hcN : c ∈ N)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    urad F ≤ ((normalClosureIn (K ⊓ N) c).subgroupOf K).map α := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  set Xb := ((normalClosureIn (K ⊓ N) c).subgroupOf K).map α with hXb
  obtain ⟨hcv, hc3', hc1'⟩ := alpha_c_props hαk hN hcK hcN hc3 hc1
  set cb := α ⟨c, hcK⟩ with hcb
  have hcX : c ∈ normalClosureIn (K ⊓ N) c := self_mem_normalClosureIn _ c
  have hcXb : cb ∈ Xb := ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr hcX, rfl⟩
  have hR := eq_urad_of_le (R := Xb ⊓ urad F) inf_le_right ?_ ?_
  · rw [← hR]
    exact inf_le_left
  · intro h hh
    exact mem_normalizer_inf_of_mem (vstab_le_normalizer_map_X hαs hN hh)
      (by
        rw [Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · intro hu
          exact conj_mem_urad (vstab_le_lstab hh) hu
        · intro hu
          have := conj_mem_urad ((lstab F).inv_mem (vstab_le_lstab hh)) hu
          simpa [mul_assoc] using this)
  · obtain ⟨u, hu, hne⟩ := exists_commutator_ne_one hcv (not_mem_urad_of_pow_three hc3' hc1')
    intro hbot
    apply hne
    obtain ⟨k, rfl⟩ := hαs u
    have hkN : (k : G) ∈ N := (hN k).mpr (urad_le_vstab hu)
    have hkc : (k : G) * c * (k : G)⁻¹ * c⁻¹ ∈ normalClosureIn (K ⊓ N) c :=
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, ⟨k.2, hkN⟩, rfl⟩) (Subgroup.inv_mem _ hcX)
    have hmemK : (k : G) * c * (k : G)⁻¹ * c⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem k.2 hcK) (K.inv_mem k.2)) (K.inv_mem hcK)
    have hval : α ⟨_, hmemK⟩ = α k * cb * (α k)⁻¹ * cb⁻¹ := by
      rw [hcb, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    have hmem : α k * cb * (α k)⁻¹ * cb⁻¹ ∈ Xb ⊓ urad F := by
      refine ⟨⟨⟨_, hmemK⟩, Subgroup.mem_subgroupOf.mpr hkc, hval⟩, ?_⟩
      have h1 : cb * (α k)⁻¹ * cb⁻¹ ∈ urad F :=
        conj_mem_urad (vstab_le_lstab hcv) ((urad F).inv_mem hu)
      have : α k * cb * (α k)⁻¹ * cb⁻¹ = α k * (cb * (α k)⁻¹ * cb⁻¹) := by group
      rw [this]
      exact (urad F).mul_mem hu h1
    rw [hbot] at hmem
    exact hmem

theorem irredModE0_map_X (hF : Nat.card F = 2) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) (hcK : c ∈ K) (hcN : c ∈ N)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    IrredModE0 F (((normalClosureIn (K ⊓ N) c).subgroupOf K).map α) := by
  obtain ⟨-, hc3', hc1'⟩ := alpha_c_props hαk hN hcK hcN hc3 hc1
  exact irredModE0_of_card_two hF (map_X_le_vstab hN hcK hcN)
    (urad_le_map_X hF hαs hαk hN hcK hcN hc3 hc1)
    ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.mpr (self_mem_normalClosureIn _ c), rfl⟩ hc3' hc1'

theorem le_X_of_natural (hF : Nat.card F = 2) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) (hcK : c ∈ K) (hcN : c ∈ N)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {Q : Subgroup G} (hQK : Q ≤ K) (hQN : Q ≤ N)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (β : ↥Q →* Multiplicative (Fin 3 → F)) (hβinj : Function.Injective β)
    (hβs : Function.Surjective β)
    (hβ : ∀ (a : ↥K) (u v : ↥Q), (v : G) = a * u * (a : G)⁻¹ →
      Multiplicative.toAdd (β v) = (α a : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u)) :
    Q ≤ normalClosureIn (K ⊓ N) c := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  set X := normalClosureIn (K ⊓ N) c with hX
  obtain ⟨hcv, hc3', hc1'⟩ := alpha_c_props hαk hN hcK hcN hc3 hc1
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {x | ∃ q : ↥Q, (q : G) ∈ X ∧ Multiplicative.toAdd (β q) = x}
      zero_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
      add_mem' := by
        rintro _ _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
        exact ⟨q₁ * q₂, X.mul_mem hq₁ hq₂, by rw [map_mul, toAdd_mul]⟩
      neg_mem' := by
        rintro _ ⟨q, hq, rfl⟩
        exact ⟨q⁻¹, X.inv_mem hq, by rw [map_inv, toAdd_inv]⟩ }
  have hSinv : ∀ k ∈ vstab F, ∀ w ∈ S, (k : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ S := by
    intro h hh w hw
    obtain ⟨q, hq, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := hαs h
    have hkX := mem_normalizer_X (c := c) hN hh
    have hkq : (k : G) * q * (k : G)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ k.2) q).mp q.2
    exact ⟨⟨_, hkq⟩, (Subgroup.mem_normalizer_iff.mp hkX q).mp hq, hβ k q ⟨_, hkq⟩ rfl⟩
  obtain ⟨q₁, hq₁⟩ := hβs (Multiplicative.ofAdd (Pi.single 1 1))
  have hq₁N : (q₁ : G) ∈ N := hQN q₁.2
  have hcq : c * (q₁ : G)⁻¹ * c⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hKQ hcK) _).mp (Q.inv_mem q₁.2)
  have hcomm : (q₁ : G) * c * (q₁ : G)⁻¹ * c⁻¹ ∈ X :=
    X.mul_mem (Subgroup.subset_closure ⟨q₁, ⟨hQK q₁.2, hq₁N⟩, rfl⟩)
      (X.inv_mem (self_mem_normalClosureIn _ c))
  have hcommQ : (q₁ : G) * c * (q₁ : G)⁻¹ * c⁻¹ ∈ Q := by
    have : (q₁ : G) * c * (q₁ : G)⁻¹ * c⁻¹ = q₁ * (c * (q₁ : G)⁻¹ * c⁻¹) := by group
    rw [this]
    exact Q.mul_mem q₁.2 hcq
  have hvec : Multiplicative.toAdd (β ⟨_, hcommQ⟩) =
      Pi.single 1 1 - (α ⟨c, hcK⟩ : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 := by
    have he : (⟨_, hcommQ⟩ : ↥Q) = q₁ * ⟨_, hcq⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul]
      group)
    have h2 := hβ ⟨c, hcK⟩ q₁⁻¹ ⟨_, hcq⟩ (by simp)
    rw [he, map_mul, toAdd_mul, h2, map_inv, toAdd_inv, hq₁, toAdd_ofAdd, mulVec_neg,
      sub_eq_add_neg]
  set u₀ : Fin 3 → F :=
    (Pi.single 1 1 : Fin 3 → F) - (α ⟨c, hcK⟩ : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1
    with hu₀
  have hoff : u₀ 1 ≠ 0 ∨ u₀ 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hcu := not_mem_urad_of_pow_three hc3' hc1'
    obtain ⟨e1, e2⟩ := mulVec_one_two_of_mem_vstab hcv (Pi.single 1 1)
    simp only [hu₀, Pi.sub_apply, Pi.single_eq_same, e1, e2] at h1 h2
    simp only [Pi.single_apply, show (2 : Fin 3) ≠ 1 by decide, ite_false, mul_one,
      mul_zero, add_zero] at h1 h2
    have hk11 : (α ⟨c, hcK⟩ : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := by linear_combination -h1
    have hk21 : (α ⟨c, hcK⟩ : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by linear_combination -h2
    apply blkSL_ne_one_of_not_mem_urad hcv hcu
    refine sl2_eq_one_of_fix (blkSL_pow_three hcv hc3') (x := ![1, 0]) (by
      intro h
      have := congrFun h 0
      simp at this) ?_
    show blkMat (α ⟨c, hcK⟩ : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0] = ![1, 0]
    ext i
    fin_cases i <;> simp [blkMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hk11, hk21]
  have hStop : S = ⊤ := irredModE0_vstab S hSinv _ ⟨⟨_, hcommQ⟩, hcomm, hvec⟩ hoff
  intro q hq
  have hmem : Multiplicative.toAdd (β ⟨q, hq⟩) ∈ S := hStop ▸ AddSubgroup.mem_top _
  obtain ⟨q', hq'X, hq'⟩ := hmem
  have : q' = ⟨q, hq⟩ := hβinj (Multiplicative.toAdd.injective hq')
  have hval : (q' : G) = q := congrArg Subtype.val this
  rw [← hval]
  exact hq'X

theorem map_pCoreOf_X_le_urad (hF : Nat.card F = 2) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) (hcK : c ∈ K) (hcN : c ∈ N)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ((CFSG.Open.pCoreOf 2 (normalClosureIn (K ⊓ N) c)).subgroupOf K).map α ≤ urad F := by
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalClosureIn (K ⊓ N) c with hX
  set Y := CFSG.Open.pCoreOf 2 X with hY
  have hYK : Y ≤ K := (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans
    ((normalClosureIn_le_inf hcK hcN).trans inf_le_left)
  have hY2 : IsPGroup 2 Y := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  refine le_urad_of_isPGroup (map_X_le_vstab hN hcK hcN)
    (irredModE0_map_X hF hαs hαk hN hcK hcN hc3 hc1)
    ((hY2.comap_subtype (K := K)).map _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  have hxY : (x : G) ∈ Subgroup.normalizer (Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hxX
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨x * y * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp hxY _).mp (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨y, hy, hyw⟩
    refine ⟨x⁻¹ * y * x, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer _).inv_mem hxY) _).mp (Subgroup.mem_subgroupOf.mp hy)
      simpa using this
    · have : α y = α x * w * (α x)⁻¹ := hyw
      rw [map_mul, map_mul, map_inv, this]
      group

theorem card_pCoreOf_X_le (hF : Nat.card F = 2) (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K)
    (hN : ∀ k : ↥K, (k : G) ∈ N ↔ α k ∈ vstab F) (hcK : c ∈ K) (hcN : c ∈ N)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    Nat.card (CFSG.Open.pCoreOf 2 (normalClosureIn (K ⊓ N) c)) ≤
      4 * Nat.card (CFSG.Open.pCoreOf 2 K) := by
  set X := normalClosureIn (K ⊓ N) c with hX
  set Y := CFSG.Open.pCoreOf 2 X with hY
  have hYK : Y ≤ K := (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans
    ((normalClosureIn_le_inf hcK hcN).trans inf_le_left)
  have hle : Y.subgroupOf K ≤ (urad F).comap α := fun x hx =>
    map_pCoreOf_X_le_urad hF hαs hαk hN hcK hcN hc3 hc1 ⟨x, hx, rfl⟩
  have h1 : Nat.card Y = Nat.card (Y.subgroupOf K) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv).symm
  have h2 := Subgroup.card_le_of_le hle
  have h3 := card_comap_of_surjective α hαs (urad F)
  have hker : Nat.card α.ker = Nat.card (CFSG.Open.pCoreOf 2 K) := by
    have : α.ker = (CFSG.Open.pCoreOf 2 K).subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).toEquiv
  have hurad : Nat.card (urad F) = 4 := by rw [card_urad, hF]; norm_num
  rw [h1]
  calc Nat.card (Y.subgroupOf K) ≤ Nat.card ((urad F).comap α) := h2
    _ = 4 * Nat.card (CFSG.Open.pCoreOf 2 K) := by rw [h3, hker, hurad, mul_comm]

end X

section Normal

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_X_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M)
    (hTN : T ≤ N) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F % 3 = 2) (α : ↥(kTwenty M c) →* SpecialLinearGroup (Fin 3) F)
    {V : Subgroup G} (hαk : α.ker = V.subgroupOf (kTwenty M c)) (hV2 : IsPGroup 2 V) :
    L ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hc1 : c = 1
  · have hX : normalClosureIn (kTwenty M c ⊓ N) c = ⊥ := by
      rw [eq_bot_iff, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m, -, rfl⟩
      rw [hc1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    intro l _
    rw [hX]
    exact mem_normalizer_of_map_conj_le (le_of_eq (Subgroup.map_bot _))
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL hcA
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hkey : ∀ y ∈ kTwenty M c ⊓ N, y ^ 3 = 1 → y ∈ normalClosureIn (kTwenty M c ⊓ N) c := by
    intro y hy hy3
    obtain ⟨k, hk, hyk⟩ := exists_mem_zpowers_conj hq α hαk hV2 inf_le_left ⟨hcK, hcN⟩ hy hc3
      hy3 hc1
    have hkc : k * c * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c :=
      Subgroup.subset_closure ⟨k, hk, rfl⟩
    exact (Subgroup.zpowers_le.mpr hkc) hyk
  have hcKN : c ∈ kTwenty M c ⊓ N := ⟨hcK, hcN⟩
  have hTX : T ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) := by
    intro t ht
    have htKN : t ∈ Subgroup.normalizer ((kTwenty M c ⊓ N : Subgroup G) : Set G) :=
      mem_normalizer_inf_of_mem (hMK (hT.sylow.le ht)) (Subgroup.le_normalizer (hTN ht))
    apply mem_normalizer_of_map_conj_le
    rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hkcKN : k * c * k⁻¹ ∈ kTwenty M c ⊓ N :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hcKN) (Subgroup.inv_mem _ hk)
    show t * (k * c * k⁻¹) * t⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c
    refine hkey _ ((Subgroup.mem_normalizer_iff.mp htKN _).mp hkcKN) ?_
    rw [conj_pow, conj_pow, hc3]
    group
  have hOX : CFSG.Open.pCoreOf 2 L ≤
      Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) :=
    (pCoreOf_le_core hT hN hO2L hTN).trans hTX
  have hLXO := le_normalizer_normalClosureIn_sup_pCoreOf_core hT hN hAL
  intro l hl
  apply mem_normalizer_of_map_conj_le
  rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hmem : k * c * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c ⊔ CFSG.Open.pCoreOf 2 L :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, hk, rfl⟩)
  show l * (k * c * k⁻¹) * l⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c
  refine mem_of_pow_three_eq_one hOX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    ((Subgroup.mem_normalizer_iff.mp (hLXO hl) _).mp hmem) ?_
  rw [conj_pow, conj_pow, hc3]
  group

end Normal

end CFSG.RankThree.PartTwo.Sec20.Res3
