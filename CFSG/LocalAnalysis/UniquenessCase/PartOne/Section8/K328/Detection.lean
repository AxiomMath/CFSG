module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Leaves
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetAssembly
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open
open scoped commutatorElement

@[expose] def K328ProperComponentLieModel (K : Type) [Group K] : Prop :=
  LieModel K .PSL 4 2 2 ∨
  LieModel K .PSp 3 2 2 ∨
  LieModel K .POmegaMinus 4 2 2 ∨
  LieModel K .PSL 6 2 1 ∨
  LieModel K .PSL 7 2 1 ∨
  LieModel K .G2 0 2 2 ∨
  LieModel K .trialityD4 0 2 2 ∨
  LieModel K .PSU 4 2 3 ∨
  LieModel K .PSp 3 2 3 ∨
  LieModel K .POmegaMinus 4 2 3 ∨
  LieModel K .G2 0 2 3 ∨
  LieModel K .trialityD4 0 2 3 ∨
  LieModel K .twistedF4 0 2 3

theorem K328ProperComponentLieModel.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : K328ProperComponentLieModel A) : K328ProperComponentLieModel B := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · left; exact LieModel.of_mulEquiv e h
  · right; left; exact LieModel.of_mulEquiv e h
  · right; right; left; exact LieModel.of_mulEquiv e h
  · right; right; right; left; exact LieModel.of_mulEquiv e h
  · right; right; right; right; left; exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; left; exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; right; left; exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; right; right; left; exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; right; right; right; left; exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; right; right; right; right; left
    exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; right; right; right; right; right; left
    exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; right; right; right; right; right; right; left
    exact LieModel.of_mulEquiv e h
  · right; right; right; right; right; right; right; right; right; right; right; right
    exact LieModel.of_mulEquiv e h

private def k328rc_centerPart (K : Type) [Group K] (m : ℕ) : Subgroup K where
  carrier := {c : K | c ∈ Subgroup.center K ∧ c ^ m = 1}
  mul_mem' := by
    intro a b ha hb
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
    have hcomm : Commute a b := (Subgroup.mem_center_iff.1 ha.1 b).symm
    rw [hcomm.mul_pow, ha.2, hb.2, mul_one]
  one_mem' := ⟨Subgroup.one_mem _, one_pow m⟩
  inv_mem' := by
    intro a ha
    exact ⟨Subgroup.inv_mem _ ha.1, by rw [inv_pow, ha.2, inv_one]⟩

private theorem k328rc_A_le_center (K : Type) [Group K] (m : ℕ) :
    k328rc_centerPart K m ≤ Subgroup.center K := fun _ h => h.1

private theorem k328rc_A_pow_three_eq_one (K : Type) [Group K] (m : ℕ) (hm : ¬ 3 ∣ m)
    {c : K} (hc : c ∈ k328rc_centerPart K m) (h3 : c ^ 3 = 1) : c = 1 := by
  have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hc.2
  have h2 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm
  have h4 : orderOf c ∣ Nat.gcd 3 m := Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one hcop] at h4
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

private theorem k328rc_centerPart_pow (K : Type) [Group K] [Finite K] (a m : ℕ)
    (hcard : Nat.card (Subgroup.center K) = 3 ^ a * m) {c : K}
    (hc : c ∈ Subgroup.center K) : c ^ (3 ^ a) ∈ k328rc_centerPart K m := by
  refine ⟨Subgroup.pow_mem _ hc _, ?_⟩
  have h2 : c ^ Nat.card (Subgroup.center K) = 1 := by
    have h1 : (⟨c, hc⟩ : Subgroup.center K) ^ Nat.card (Subgroup.center K) = 1 :=
      pow_card_eq_one'
    exact congrArg Subtype.val h1
  rw [← pow_mul, ← hcard, h2]

private theorem k328rc_commute_of_commute_mk {K : Type} [Group K] [Finite K]
    (A : Subgroup K) [A.Normal] (hAc : A ≤ Subgroup.center K)
    (hA3 : ∀ c ∈ A, c ^ 3 = 1 → c = 1) {x f : K} (hf : f ^ 3 = 1)
    (h : (QuotientGroup.mk' A) x * (QuotientGroup.mk' A) f =
      (QuotientGroup.mk' A) f * (QuotientGroup.mk' A) x) :
    x * f = f * x := by
  set c : K := x * f * x⁻¹ * f⁻¹ with hc
  have hcA : c ∈ A := by
    rw [← QuotientGroup.eq_one_iff]
    have : (QuotientGroup.mk' A) c = 1 := by
      simp only [hc, map_mul, map_inv]
      rw [h]
      group
    simpa using this
  have hxf : x * f * x⁻¹ = c * f := by rw [hc]; group
  have hcf : Commute c f := (Subgroup.mem_center_iff.1 (hAc hcA) f).symm
  have h3c : c ^ 3 = 1 := by
    have h1 : (x * f * x⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hf]
      simp
    rw [hxf, hcf.mul_pow, hf, mul_one] at h1
    exact h1
  have hc1 : c = 1 := hA3 c hcA h3c
  rw [hc1] at hxf
  calc x * f = x * f * x⁻¹ * x := by group
    _ = 1 * f * x := by rw [hxf]
    _ = f * x := by group

private theorem k328rc_eq_one_of_mk_eq_one_of_card_center {K : Type} [Group K] [Finite K]
    (A : Subgroup K) [A.Normal] (hAc : A ≤ Subgroup.center K)
    (hA3 : ∀ c ∈ A, c ^ 3 = 1 → c = 1) {X : Subgroup K}
    (hcen : Nat.card (Subgroup.center ↥X) = 3) :
    ∀ x ∈ X, (QuotientGroup.mk' A) x = 1 → x = 1 := by
  intro x hx hx1
  have hxA : x ∈ A := (QuotientGroup.eq_one_iff x).1 hx1
  have hxX : (⟨x, hx⟩ : X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hAc hxA) y)
  have h1 : (⟨⟨x, hx⟩, hxX⟩ : Subgroup.center ↥X) ^ Nat.card (Subgroup.center ↥X) = 1 :=
    pow_card_eq_one'
  rw [hcen] at h1
  have h2 : x ^ 3 = 1 := by
    have := congrArg (fun y : Subgroup.center ↥X => ((y : X) : K)) h1
    simpa using this
  exact hA3 x hxA h2

private theorem k328rc_pos_map {K : Type} [Group K] [Finite K]
    (A : Subgroup K) [A.Normal] (hAc : A ≤ Subgroup.center K)
    (hA3 : ∀ c ∈ A, c ^ 3 = 1 → c = 1) {Z X : Subgroup K} (h : Pos K Z X) :
    Pos (K ⧸ A) (Z.map (QuotientGroup.mk' A)) (X.map (QuotientGroup.mk' A)) := by
  obtain ⟨hZ, hZX, hXC, hsub, hqs, hcen, hlie⟩ := h
  set π := QuotientGroup.mk' A with hπ
  have hinjX : ∀ x ∈ X, π x = 1 → x = 1 :=
    k328rc_eq_one_of_mk_eq_one_of_card_center A hAc hA3 hcen
  obtain ⟨eX, -⟩ := exists_mulEquiv_map π hinjX
  obtain ⟨eZ, -⟩ := exists_mulEquiv_map π (X := Z) fun z hz => hinjX z (hZX hz)
  set C : Subgroup K := Subgroup.centralizer (Z : Set K) with hC
  set C' : Subgroup (K ⧸ A) :=
    Subgroup.centralizer ((Z.map π : Subgroup (K ⧸ A)) : Set _) with hC'
  have hmapC : ∀ c ∈ C, π c ∈ C' := by
    intro c hc
    rw [hC', Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc z hz]
  let π' : ↥C →* ↥C' := (π.comp C.subtype).codRestrict C' fun c => hmapC c c.2
  have hsurj : Function.Surjective π' := by
    rintro ⟨y', hy'⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [hC, Subgroup.mem_centralizer_iff]
    intro z hz
    have hz3 : z ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
      rw [hZ] at this
      simpa using congrArg Subtype.val this
    have hcomm := Subgroup.mem_centralizer_iff.1 hy' (π z) (Subgroup.mem_map_of_mem π hz)
    exact (k328rc_commute_of_commute_mk A hAc hA3 hz3 hcomm.symm).symm
  have hmapX : (X.subgroupOf C).map π' = (X.map π).subgroupOf C' := by
    ext ⟨y', hy'⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨c, hc⟩, hcX, hcy⟩
      have : π c = y' := congrArg Subtype.val hcy
      exact ⟨c, hcX, this⟩
    · rintro ⟨x, hxX, rfl⟩
      exact ⟨⟨x, hXC hxX⟩, hxX, rfl⟩
  refine ⟨?_, Subgroup.map_mono hZX, ?_, ?_, isQuasisimple_of_mulEquiv' eX hqs, ?_, ?_⟩
  · rw [← hZ]
    exact (Nat.card_congr eZ.toEquiv).symm
  · rintro _ ⟨x, hxX, rfl⟩
    exact hmapC x (hXC hxX)
  · have := Subgroup.IsSubnormal.map (f := π') hsurj hsub
    rwa [hmapX] at this
  · rw [← hcen]
    exact (Nat.card_congr (Subgroup.centerCongr eX).toEquiv).symm
  · let f := QuotientGroup.congr (Subgroup.center X) (Subgroup.center (X.map π)) eX
      (Subgroup.map_center_eq eX)
    rcases hlie with hl | hl
    · exact Or.inl (LieModel.of_mulEquiv f hl)
    · exact Or.inr (LieModel.of_mulEquiv f hl)

private theorem k328rc_center_quotient {K : Type} [Group K] [Finite K]
    (A : Subgroup K) [A.Normal] (hAc : A ≤ Subgroup.center K)
    (hperf : commutator K = ⊤) :
    Subgroup.center (K ⧸ A) = (Subgroup.center K).map (QuotientGroup.mk' A) := by
  refine le_antisymm ?_ (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective A))
  intro z hz
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  refine Subgroup.mem_map_of_mem _ ?_
  rw [Subgroup.mem_center_iff]
  intro y
  have hmem : ∀ y : K, ⁅k, y⁆ ∈ A := by
    intro y
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' A) ⁅k, y⁆ = 1
    rw [map_commutatorElement (QuotientGroup.mk' A)]
    exact Commute.commutator_eq ((Subgroup.mem_center_iff.1 hz (QuotientGroup.mk' A y)).symm)
  let φ : K →* Subgroup.center K :=
    { toFun := fun y => ⟨⁅k, y⁆, hAc (hmem y)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y z₁ => Subtype.ext (by
        have hc : ⁅k, z₁⁆ ∈ Subgroup.center K := hAc (hmem z₁)
        have hcz : y * ⁅k, z₁⁆ * y⁻¹ = ⁅k, z₁⁆ := by
          rw [Subgroup.mem_center_iff.1 hc y, mul_assoc, mul_inv_cancel, mul_one]
        calc ⁅k, y * z₁⁆ = ⁅k, y⁆ * y * ⁅k, z₁⁆ * y⁻¹ :=
              commutatorElement_mul_right_eq_mul_conj k y z₁
          _ = ⁅k, y⁆ * (y * ⁅k, z₁⁆ * y⁻¹) := by group
          _ = ⁅k, y⁆ * ⁅k, z₁⁆ := by rw [hcz]) }
  have hker : φ.ker = ⊤ := by
    have := Abelianization.commutator_subset_ker φ
    rw [hperf] at this
    exact top_le_iff.mp this
  have hphi : ⁅k, y⁆ = 1 := by
    have hy : φ y = 1 := by
      have : y ∈ φ.ker := by rw [hker]; trivial
      simpa [MonoidHom.mem_ker] using this
    exact congrArg Subtype.val hy
  exact (commutatorElement_eq_one_iff_mul_comm.mp hphi).symm

private theorem k328rc_center_isPGroup {K : Type} [Group K] [Finite K]
    (A : Subgroup K) [A.Normal] (hAc : A ≤ Subgroup.center K) (hperf : commutator K = ⊤)
    (a : ℕ) (hpowA : ∀ c ∈ Subgroup.center K, c ^ (3 ^ a) ∈ A) :
    IsPGroup 3 (Subgroup.center (K ⧸ A)) := by
  intro g
  refine ⟨a, ?_⟩
  have hcenter := k328rc_center_quotient A hAc hperf
  have hg : (g : K ⧸ A) ∈ (Subgroup.center K).map (QuotientGroup.mk' A) := by
    rw [← hcenter]; exact g.2
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.1 hg
  have hpow : (QuotientGroup.mk' A) (c ^ (3 ^ a)) = 1 := by
    rw [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    exact hpowA c hc
  refine Subtype.ext ?_
  push_cast
  rw [← hcg, ← map_pow, hpow]

private theorem k328rc_A_not_dvd {K : Type} [Group K] [Finite K]
    (A : Subgroup K) (hA3 : ∀ c ∈ A, c ^ 3 = 1 → c = 1) :
    ¬ 3 ∣ Nat.card A := by
  intro h
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 (G := A) h
  have hc3 : (c : K) ^ 3 = 1 := by
    have h1 : (c : A) ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    exact congrArg Subtype.val h1
  have hc1 : (c : K) = 1 := hA3 (c : K) c.2 hc3
  have hord : orderOf (c : K) = 3 := by rw [Subgroup.orderOf_coe, hc]
  rw [hc1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem k328_reduce_center {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hK : CFSG.Open.IsKGroup (K ⧸ Subgroup.center K))
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    {Z X : Subgroup K} (hpos : Pos K Z X) (hX : X ≠ ⊤) :
    ∃ (K' : Type) (_ : Group K') (_ : Finite K'), CFSG.Open.IsQuasisimple K' ∧
      IsPGroup 3 (Subgroup.center K') ∧ CFSG.Open.IsKGroup (K' ⧸ Subgroup.center K') ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup K') ≤ 3 ∧ (∃ Z' X' : Subgroup K', Pos K' Z' X' ∧ X' ≠ ⊤) ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (K' ⧸ Subgroup.center K')) := by
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := Subgroup.center K)).ne' 3 (by norm_num)
  let A : Subgroup K := k328rc_centerPart K m
  have hAc : A ≤ Subgroup.center K := k328rc_A_le_center K m
  have hAn : A.Normal := Subgroup.normal_of_le_center hAc
  have hA3 : ∀ c ∈ A, c ^ 3 = 1 → c = 1 :=
    fun c hc h => k328rc_A_pow_three_eq_one K m hm hc h
  have hpowA : ∀ c ∈ Subgroup.center K, c ^ (3 ^ a) ∈ A :=
    fun c hc => k328rc_centerPart_pow K a m hcard hc
  have hperf : commutator K = ⊤ := hq.1
  have hAnotdvd : ¬ 3 ∣ Nat.card A := k328rc_A_not_dvd A hA3
  have hcomm' : commutator (K ⧸ A) = ⊤ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup K) (⊤ : Subgroup K) (QuotientGroup.mk' A)
    have htop : (⊤ : Subgroup K).map (QuotientGroup.mk' A) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective A)
    rw [htop] at h1
    unfold commutator at hperf ⊢
    rw [← h1, hperf, htop]
  have hcenter : Subgroup.center (K ⧸ A) = (Subgroup.center K).map (QuotientGroup.mk' A) :=
    k328rc_center_quotient A hAc hperf
  have hc' : IsPGroup 3 (Subgroup.center (K ⧸ A)) :=
    k328rc_center_isPGroup A hAc hperf a hpowA
  have hmapn : ((Subgroup.center K).map (QuotientGroup.mk' A)).Normal :=
    Subgroup.Normal.map (inferInstance : (Subgroup.center K).Normal) _
      (QuotientGroup.mk'_surjective A)
  let e1 : (K ⧸ A) ⧸ (Subgroup.center K).map (QuotientGroup.mk' A) ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientQuotientEquivQuotient A (Subgroup.center K) hAc
  let e2 : (K ⧸ A) ⧸ Subgroup.center (K ⧸ A) ≃*
      (K ⧸ A) ⧸ (Subgroup.center K).map (QuotientGroup.mk' A) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  let e : (K ⧸ A) ⧸ Subgroup.center (K ⧸ A) ≃* K ⧸ Subgroup.center K := e2.trans e1
  have hsimp : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hq' : CFSG.Open.IsQuasisimple (K ⧸ A) := ⟨hcomm', e.isSimpleGroup⟩
  have hK' : CFSG.Open.IsKGroup ((K ⧸ A) ⧸ Subgroup.center (K ⧸ A)) :=
    CFSG.KCore.KGroupNonab.of_mulEquiv CFSG.Open.isCatalogGroup_isoInvariant hK e
  have h3' : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ A)) ≤ 3 := by
    have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [CFSG.SectionRank.pRank_quotient_eq (p := 3) A hAnotdvd]
    exact h3
  have hpos' : Pos (K ⧸ A) (Z.map (QuotientGroup.mk' A)) (X.map (QuotientGroup.mk' A)) :=
    k328rc_pos_map A hAc hA3 hpos
  have hX' : X.map (QuotientGroup.mk' A) ≠ ⊤ := by
    intro htop
    refine hX (eq_top_of_perfect_of_sup_center hperf ?_)
    intro k
    have hk : (QuotientGroup.mk' A) k ∈ X.map (QuotientGroup.mk' A) := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x, hxX, hxk⟩ := Subgroup.mem_map.1 hk
    refine ⟨x, hxX, x⁻¹ * k, hAc ?_, by group⟩
    refine (QuotientGroup.eq_one_iff (x⁻¹ * k)).1 ?_
    rw [← QuotientGroup.mk'_apply, map_mul, map_inv, hxk, inv_mul_cancel]
  exact ⟨K ⧸ A, inferInstance, inferInstance, hq', hc', hK', h3',
    ⟨Z.map (QuotientGroup.mk' A), X.map (QuotientGroup.mk' A), hpos', hX'⟩, ⟨e.symm⟩⟩

theorem k328_detection_of_three_center
    {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hc : IsPGroup 3 (Subgroup.center K))
    (hK : CFSG.Open.IsKGroup (K ⧸ Subgroup.center K))
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    {Z X : Subgroup K} (hpos : Pos K Z X) (hX : X ≠ ⊤)
    (h33 : CFSG.LocalAnalysis.UniquenessCase.UCK.K33)
    (h34 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K34odd) :
    K328ProperComponentLieModel (K ⧸ Subgroup.center K) :=
  k328det_detection_of_lists h33 h34 hq hc hK h3 hpos hX

theorem k328_detection
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hK : CFSG.Open.IsKGroup (K ⧸ Subgroup.center K))
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    {Z X : Subgroup K} (hpos : Pos K Z X) (hX : X ≠ ⊤)
    (h33 : CFSG.LocalAnalysis.UniquenessCase.UCK.K33)
    (h34 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K34odd) :
    K328ProperComponentLieModel (K ⧸ Subgroup.center K) := by
  obtain ⟨K', _, _, hq', hc', hK', h3', ⟨Z', X', hpos', hX'⟩, ⟨e⟩⟩ :=
    k328_reduce_center hq hK h3 hpos hX
  exact (k328_detection_of_three_center hq' hc' hK' h3' hpos' hX' h33 h34).of_mulEquiv e.symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
