module

public import CFSG.LocalAnalysis.WeakClosure81.NineTwoB
import CFSG.Goldschmidt.Steps.Sec82PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

theorem nineTwoF_exists_elemAbelian_sq (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsPGroup p X)
    (hnc : ¬ IsCyclic ↥X) :
    ∃ F : Subgroup G, F ≤ X ∧ IsElemAbelian p F ∧ Nat.card ↥F = p ^ 2 := by
  obtain ⟨F, hFX, -, hcard, hexp, hcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hp hp2 hX le_rfl
      Subgroup.le_normalizer hnc
  exact ⟨F, hFX, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩, hcard⟩

private theorem nineTwoF_mem_sup {R F : Subgroup G} (hF : F ≤ normalizer (R : Set G)) {y : G}
    (hy : y ∈ R ⊔ F) : ∃ r ∈ R, ∃ f ∈ F, y = r * f := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left R F hF
  have hy' : y ∈ ((R ⊔ F : Subgroup G) : Set G) := hy
  rw [h] at hy'
  obtain ⟨r, hr, f, hf, rfl⟩ := Set.mem_mul.mp hy'
  exact ⟨r, hr, f, hf, rfl⟩

theorem nineTwoF_le_normalizer (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A F : Subgroup G} (hA : A ∈ nineOmegaIn V K S) (hFX : F ≤ X) :
    A ≤ normalizer ((pCoreOf 2 K ⊔ F : Subgroup G) : Set G) := by
  have hAK : A ≤ K := hA.2.trans h.base.sylowTwo.le
  have hKN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hFK : F ≤ K := hFX.trans h.base.sylowP.le
  have key : ∀ a ∈ A, ∀ f ∈ F, a * f * a⁻¹ ∈ pCoreOf 2 K ⊔ F := by
    intro a ha f hf
    by_cases haR : a ∈ pCoreOf 2 K
    · have h1 : f * a⁻¹ * f⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp (hKN (hFK hf)) a⁻¹).mp ((pCoreOf 2 K).inv_mem haR)
      have h2 : a * f * a⁻¹ = (a * (f * a⁻¹ * f⁻¹)) * f := by group
      rw [h2]
      exact Subgroup.mul_mem_sup ((pCoreOf 2 K).mul_mem haR h1) hf
    · have hu : a * f * a⁻¹ * f ∈ pCoreOf 2 K := nine_two_inv hV hm h hA ha haR (hFX hf)
      have h2 : a * f * a⁻¹ = (a * f * a⁻¹ * f) * f⁻¹ := by group
      rw [h2]
      exact Subgroup.mul_mem_sup hu (F.inv_mem hf)
  have fwd : ∀ a ∈ A, ∀ y ∈ pCoreOf 2 K ⊔ F, a * y * a⁻¹ ∈ pCoreOf 2 K ⊔ F := by
    intro a ha y hy
    obtain ⟨r, hr, f, hf, rfl⟩ := nineTwoF_mem_sup (hFK.trans hKN) hy
    have h1 : a * r * a⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (hKN (hAK ha)) r).mp hr
    have h2 : a * (r * f) * a⁻¹ = (a * r * a⁻¹) * (a * f * a⁻¹) := by group
    rw [h2]
    exact (pCoreOf 2 K ⊔ F).mul_mem (Subgroup.mem_sup_left h1) (key a ha f hf)
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => fwd a ha y hy, fun hy => ?_⟩
  have := fwd a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

theorem nineTwoF_le_commutator_sup (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A F : Subgroup G} (hA : A ∈ nineOmegaIn V K S) (hFX : F ≤ X) (hFp : ∀ x ∈ F, x ^ p = 1) :
    pCoreOf 2 K ⊔ F ≤ ⁅pCoreOf 2 K ⊔ F, A⁆ ⊔ pCoreOf 2 K := by
  have hKN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hFK : F ≤ K := hFX.trans h.base.sylowP.le
  obtain ⟨g, -, -, hAnot⟩ := mem_omegaSet.mp hA.1
  obtain ⟨a, haA, haR⟩ := SetLike.not_le_iff_exists.mp hAnot
  have hodd : Odd p := h.base.prime.odd_of_ne_two h.base.odd
  obtain ⟨m, hm'⟩ := hodd
  have hfin : ∀ f ∈ F, f ∈ ⁅pCoreOf 2 K ⊔ F, A⁆ ⊔ pCoreOf 2 K := by
    intro f hf
    have hu : a * f * a⁻¹ * f ∈ pCoreOf 2 K := nine_two_inv hV hm h hA haA haR (hFX hf)
    have hc : ⁅f, a⁆ ∈ ⁅pCoreOf 2 K ⊔ F, A⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right hf) haA
    have hf2 : f ^ 2 ∈ ⁅pCoreOf 2 K ⊔ F, A⁆ ⊔ pCoreOf 2 K := by
      have : f ^ 2 = ⁅f, a⁆ * (a * f * a⁻¹ * f) := by
        rw [commutatorElement_def, pow_two]; group
      rw [this]
      exact Subgroup.mul_mem_sup hc hu
    have hpf : f = (f ^ 2) ^ (m + 1) := by
      have h1 : f ^ (2 * m + 1) = 1 := hm' ▸ hFp f hf
      calc f = f ^ (2 * m + 1) * f := by rw [h1, one_mul]
        _ = (f ^ 2) ^ (m + 1) := by rw [← pow_succ, ← pow_mul]; ring_nf
    rw [hpf]
    exact Subgroup.pow_mem _ hf2 _
  refine sup_le (fun r hr => Subgroup.mem_sup_right hr) ?_
  intro f hf
  exact hfin f hf

theorem nineTwoF_faithful (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p)
    {A F : Subgroup G} (hA : A ∈ nineOmegaIn V K S) (hFX : F ≤ X) (hF1 : F ≠ ⊥) :
    ∀ a ∈ A, (∀ y ∈ pCoreOf 2 K ⊔ F, ⁅a, y⁆ ∈ pCoreOf 2 K) → a ∈ pCoreOf 2 K := by
  intro a ha hc
  by_contra haR
  obtain ⟨⟨f, hfF⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
  have hf1' : f ≠ 1 := fun h' => hf1 (Subtype.ext h')
  have hu : a * f * a⁻¹ * f ∈ pCoreOf 2 K := nine_two_inv hV hm h hA ha haR (hFX hfF)
  have hv : ⁅a, f⁆ ∈ pCoreOf 2 K := hc f (Subgroup.mem_sup_right hfF)
  have hf2R : f ^ 2 ∈ pCoreOf 2 K := by
    have : f ^ 2 = (⁅a, f⁆)⁻¹ * (a * f * a⁻¹ * f) := by
      rw [commutatorElement_def, pow_two]; group
    rw [this]
    exact (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).inv_mem hv) hu
  have hf2X : f ^ 2 ∈ X := X.pow_mem (hFX hfF) 2
  have hbase : TwoPTwo K S X p := h.base.toTwoPTwoIrred.toTwoPTwo
  have hbot : f ^ 2 ∈ X ⊓ pCoreOf 2 K := ⟨hf2X, hf2R⟩
  rw [TwoPTwo.sylowP_inf_pCoreOf hbase, Subgroup.mem_bot] at hbot
  haveI : Fact p.Prime := ⟨h.base.prime⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.base.sylowP.isPGroup) ⟨f, hFX hfF⟩
  have hdvd : orderOf (⟨f, hFX hfF⟩ : ↥X) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hbot))
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have : p ∣ 2 := (dvd_pow_self p hk0).trans hdvd
    exact h.base.odd ((Nat.prime_dvd_prime_iff_eq h.base.prime Nat.prime_two).mp this)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact hf1' (congrArg Subtype.val hk)

theorem nineTwoF_pow_mem (h : Nine2Hyp V K S X p) {F : Subgroup G} (hFX : F ≤ X)
    (hFp : ∀ x ∈ F, x ^ p = 1) : ∀ y ∈ pCoreOf 2 K ⊔ F, y ^ p ∈ pCoreOf 2 K := by
  have hKN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hFK : F ≤ K := hFX.trans h.base.sylowP.le
  intro y hy
  obtain ⟨r, hr, f, hf, rfl⟩ := nineTwoF_mem_sup (hFK.trans hKN) hy
  have claim : ∀ n : ℕ, ∃ r' ∈ pCoreOf 2 K, (r * f) ^ n = r' * f ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, (pCoreOf 2 K).one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨r', hr', hn⟩ := ih
      have hfn : f ^ n ∈ normalizer (pCoreOf 2 K : Set G) :=
        (normalizer (pCoreOf 2 K : Set G)).pow_mem (hKN (hFK hf)) n
      have h1 : f ^ n * r * (f ^ n)⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp hfn r).mp hr
      refine ⟨r' * (f ^ n * r * (f ^ n)⁻¹), (pCoreOf 2 K).mul_mem hr' h1, ?_⟩
      rw [pow_succ, hn]
      group
  obtain ⟨r', hr', hn⟩ := claim p
  rw [hn, hFp f hf, mul_one]
  exact hr'

theorem nineTwoF_commutator_mem (h : Nine2Hyp V K S X p) {F : Subgroup G} (hFX : F ≤ X)
    (hFc : IsMulCommutative F) :
    ∀ y ∈ pCoreOf 2 K ⊔ F, ∀ z ∈ pCoreOf 2 K ⊔ F, ⁅y, z⁆ ∈ pCoreOf 2 K := by
  have hKN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hRK := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hFK : F ≤ K := hFX.trans h.base.sylowP.le
  intro y hy z hz
  obtain ⟨r, hr, f, hf, rfl⟩ := nineTwoF_mem_sup (hFK.trans hKN) hy
  obtain ⟨r', hr', f', hf', rfl⟩ := nineTwoF_mem_sup (hFK.trans hKN) hz
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  let π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' _
  let rq : ↥K := ⟨r, hRK hr⟩
  let rq' : ↥K := ⟨r', hRK hr'⟩
  let fq : ↥K := ⟨f, hFK hf⟩
  let fq' : ↥K := ⟨f', hFK hf'⟩
  have hrq : π rq = 1 := (QuotientGroup.eq_one_iff rq).mpr ((CFSG.mem_openPCoreOf_iff rq).mp hr)
  have hrq' : π rq' = 1 :=
    (QuotientGroup.eq_one_iff rq').mpr ((CFSG.mem_openPCoreOf_iff rq').mp hr')
  have hcomm : f * f' = f' * f :=
    congrArg Subtype.val (hFc.is_comm.comm (⟨f, hf⟩ : ↥F) ⟨f', hf'⟩)
  have hfq : ⁅fq, fq'⁆ = 1 := Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr hcomm)
  have hπ : π ⁅rq * fq, rq' * fq'⁆ = 1 := by
    rw [map_commutatorElement, map_mul, map_mul, hrq, hrq', one_mul, one_mul,
      ← map_commutatorElement, hfq, map_one]
  have hmem : ⁅rq * fq, rq' * fq'⁆ ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp hπ
  exact (CFSG.mem_openPCoreOf_iff _).mpr hmem

theorem nineTwoF_relIndex (h : Nine2Hyp V K S X p) {F : Subgroup G} (hFX : F ≤ X) :
    (pCoreOf 2 K).relIndex (pCoreOf 2 K ⊔ F) = Nat.card ↥F := by
  have hbase : TwoPTwo K S X p := h.base.toTwoPTwoIrred.toTwoPTwo
  have hFK : F ≤ K := hFX.trans h.base.sylowP.le
  have hRK := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hsupK : pCoreOf 2 K ⊔ F ≤ K := sup_le hRK hFK
  have hinf : pCoreOf 2 K ⊓ F = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← TwoPTwo.sylowP_inf_pCoreOf hbase, inf_comm]
    exact inf_le_inf_right _ hFX
  have hrelF : (pCoreOf 2 K).relIndex F = Nat.card F := by
    have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 K) (K := F)
    rw [hinf, Subgroup.card_bot, mul_one] at h1
    exact h1
  have hsub := Subgroup.relIndex_subgroupOf (H := pCoreOf 2 K) (K := pCoreOf 2 K ⊔ F)
    (L := K) hsupK
  rw [← hsub]
  have hsup' : (pCoreOf 2 K ⊔ F).subgroupOf K = (pCoreOf 2 K).subgroupOf K ⊔ F.subgroupOf K :=
    Subgroup.subgroupOf_sup hRK hFK
  rw [hsup']
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  have hRq : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K
  rw [hRq, Subgroup.relIndex_sup_left]
  have hsub2 := Subgroup.relIndex_subgroupOf (H := pCoreOf 2 K) (K := F) (L := K) hFK
  rw [hRq] at hsub2
  rw [hsub2, hrelF]

theorem nine_two_four (h763 : SevenSixThreeAbelian V) (hV : Hyp7 V) (hm : 2 < rk ↥V)
    (h : Nine2Hyp V K S X p) : IsCyclic ↥X := by
  by_contra hnc
  have hp : p.Prime := h.base.prime
  have hp2 : p ≠ 2 := h.base.odd
  obtain ⟨F, hFX, hFe, hFcard⟩ :=
    nineTwoF_exists_elemAbelian_sq hp hp2 h.base.sylowP.isPGroup hnc
  obtain ⟨A, hA⟩ := exists_mem_nineOmegaIn hV hm h
  have hAK : A ≤ K := hA.2.trans h.base.sylowTwo.le
  have hFK : F ≤ K := hFX.trans h.base.sylowP.le
  have hF1 : F ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hFcard
    have h2 : 2 ≤ p := hp.two_le
    nlinarith
  have hJnorm : ((pCoreOf 2 K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hrel : (pCoreOf 2 K).relIndex (pCoreOf 2 K ⊔ F) = p :=
    h763 hV K (nineE V K) (pCoreOf 2 K) A (pCoreOf 2 K ⊔ F) p hp hp2
      ((nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
      (nineE_subgroupOf_normal V K) (isElemAbelian_nineE V K).1
      (iSup₂_le fun _ _ => inf_le_right) le_rfl hJnorm hA.1 hAK
      (nine_two_relIndex hV hm h hA) le_sup_left
      (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hFK)
      (nineTwoF_le_normalizer hV hm h hA hFX)
      (nineTwoF_le_commutator_sup hV hm h hA hFX hFe.2)
      (nineTwoF_faithful hV hm h hA hFX hF1)
      (nineTwoF_pow_mem h hFX hFe.2)
      (nineTwoF_commutator_mem h hFX hFe.1)
  have hrel2 := nineTwoF_relIndex h hFX
  rw [hrel, hFcard] at hrel2
  have h2 : 2 ≤ p := hp.two_le
  nlinarith

end CFSG.LocalAnalysis.WeakClosure81
