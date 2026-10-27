module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
public import CFSG.RankThree.PartTwo.Sec19.Item1923Rank
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem kmTwo_isElemAbelian_map {H H' : Type} [Group H] [Group H'] {p : ℕ}
    (f : H →* H') {E : Subgroup H} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    have hxy : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 y hy, map_one]

private theorem kmTwo_commute {H : Subgroup G} {p : ℕ} (hH : CFSG.Open.IsElemAbelian p H)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a :=
  congrArg Subtype.val (hH.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem kmTwo_comm_of_mem {H : Subgroup G} [IsMulCommutative H] {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : a * b = b * a :=
  congrArg Subtype.val ((inferInstance : IsMulCommutative H).is_comm.comm (⟨a, ha⟩ : H) ⟨b, hb⟩)

private noncomputable def kmTwoBar {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) :
    K ⧸ CFSG.pCore 2 K →* M ⧸ CFSG.pCore 2 M :=
  QuotientGroup.lift (CFSG.pCore 2 K)
    ((QuotientGroup.mk' (CFSG.pCore 2 M)).comp
      (Subgroup.inclusion (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn hK)))
    (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, CFSG.RankThree.PartTwo.Sec19.Step1911EndProof.mem_pCore_iff]
      exact CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK
        ((CFSG.RankThree.PartTwo.Sec19.Step1911EndProof.mem_pCore_iff x).mp hx))

private theorem kmTwoBar_mk {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) (k : K) :
    kmTwoBar hK (QuotientGroup.mk k) =
      QuotientGroup.mk
        (Subgroup.inclusion (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn hK) k) :=
  rfl

private theorem kmTwoBar_injective {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) :
    Function.Injective (kmTwoBar hK) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : ((Subgroup.inclusion (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn hK) x :
      M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
    rw [kmTwoBar_mk, QuotientGroup.eq_one_iff,
      CFSG.RankThree.PartTwo.Sec19.Step1911EndProof.mem_pCore_iff] at hq
    exact hq
  rw [QuotientGroup.eq_one_iff, CFSG.RankThree.PartTwo.Sec19.Step1911EndProof.mem_pCore_iff]
  exact CFSG.RankThree.PartTwo.Sec19.Step1910Proof.inf_pCoreOf_le hK
    (Subgroup.mem_inf.mpr ⟨x.2, hq'⟩)

private theorem kmTwo_exists_pair {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) {m : G}
    (hm : m ∈ M) (hne : K.map (MulAut.conj m).toMonoidHom ≠ K) {p : ℕ} (hp : p.Prime)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)))
    {E : Subgroup (K ⧸ CFSG.pCore 2 K)} (hE : CFSG.Open.IsElemAbelian p E) :
    ∃ V : Subgroup (M ⧸ CFSG.pCore 2 M), CFSG.Open.IsElemAbelian p V ∧
      Nat.card V = Nat.card E * Nat.card E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hKM : K ≤ M := CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn hK
  have hJ : K.map (MulAut.conj m).toMonoidHom ∈ oTwoComponentsIn M :=
    CFSG.RankThree.PartTwo.Sec18.map_conj_mem_oTwoComponentsIn hK hm
  have hcomm_KJ : ∀ g : M, (g : G) ∈ K.map (MulAut.conj m).toMonoidHom → ∀ k : M, (k : G) ∈ K →
      QuotientGroup.mk' (CFSG.pCore 2 M) g * QuotientGroup.mk' (CFSG.pCore 2 M) k =
        QuotientGroup.mk' (CFSG.pCore 2 M) k * QuotientGroup.mk' (CFSG.pCore 2 M) g :=
    fun g hg k hk => CFSG.RankThree.PartTwo.Sec19.Step1910Proof.mk_mul_comm_of_ne hJ hK hne hg hk
  set μ : M ⧸ CFSG.pCore 2 M := QuotientGroup.mk' (CFSG.pCore 2 M) ⟨m, hm⟩ with hμ
  set E' : Subgroup (M ⧸ CFSG.pCore 2 M) := E.map (kmTwoBar hK) with hE'def
  set W : Subgroup (M ⧸ CFSG.pCore 2 M) := E'.map (MulAut.conj μ).toMonoidHom with hWdef
  have hE' : CFSG.Open.IsElemAbelian p E' := kmTwo_isElemAbelian_map (kmTwoBar hK) hE
  have hW : CFSG.Open.IsElemAbelian p W :=
    kmTwo_isElemAbelian_map (MulAut.conj μ).toMonoidHom hE'
  have hEel : ∀ x ∈ E', ∃ k : M, (k : G) ∈ K ∧ x = QuotientGroup.mk' (CFSG.pCore 2 M) k := by
    intro x hx
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective e
    exact ⟨Subgroup.inclusion hKM k, k.2, kmTwoBar_mk hK k⟩
  have hWel : ∀ y ∈ W, ∃ g : M, (g : G) ∈ K.map (MulAut.conj m).toMonoidHom ∧
      y = QuotientGroup.mk' (CFSG.pCore 2 M) g := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk, rfl⟩ := hEel z hz
    refine ⟨⟨m, hm⟩ * k * ⟨m, hm⟩⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(k : G), hk, by simp [MulAut.conj_apply]⟩
    · simp [hμ, MulAut.conj_apply, map_mul, map_inv]
  have hcomm : ∀ x ∈ E', ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := hEel x hx
    obtain ⟨g, hg, rfl⟩ := hWel y hy
    exact (hcomm_KJ g hg k hk).symm
  have hint : E' ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxW⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨g, hg, hxg⟩ := hWel x hxW
    obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp hxE
    have hcen : e ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective c
      apply kmTwoBar_injective hK
      rw [map_mul, map_mul, hex, hxg, kmTwoBar_mk]
      exact (hcomm_KJ g hg (Subgroup.inclusion hKM k₀) k₀.2).symm
    have he1 : e = 1 := by
      by_contra hne1
      have hord : orderOf e = p := orderOf_eq_prime (hE.2 e he) hne1
      have hdvd : orderOf e ∣ Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)) := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcen)
      exact hpZ (hord ▸ hdvd)
    rw [Subgroup.mem_bot, ← hex, he1, map_one]
  have hpair : ((E' : Set (M ⧸ CFSG.pCore 2 M)) ∪ (W : Set (M ⧸ CFSG.pCore 2 M))).Pairwise
      Commute := by
    intro a ha b hb _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact kmTwo_commute hE' ha hb
    · exact hcomm a ha b hb
    · exact (hcomm b hb a ha).symm
    · exact kmTwo_commute hW ha hb
  have hVcl : E' ⊔ W =
      Subgroup.closure ((E' : Set (M ⧸ CFSG.pCore 2 M)) ∪ (W : Set (M ⧸ CFSG.pCore 2 M))) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hXN : E' ≤ Subgroup.normalizer (W : Set (M ⧸ CFSG.pCore 2 M)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hw
      have e2 := hcomm x hx _ hw
      have e3 : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
        have h' : x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        rw [h', ← e2, inv_mul_cancel_left]
      have e4 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [e4, e3]
      exact hw
  have hinjW : Function.Injective (MulAut.conj μ).toMonoidHom :=
    fun a b h => (MulAut.conj μ).injective h
  have hcardE' : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective (kmTwoBar_injective hK)
  have hcardW : Nat.card W = Nat.card E' := Subgroup.card_map_of_injective hinjW
  refine ⟨E' ⊔ W, ?_, ?_⟩
  · rw [hVcl]
    refine ⟨Subgroup.isMulCommutative_closure hpair, ?_⟩
    intro x hx
    haveI := Subgroup.isMulCommutative_closure hpair
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ha | ha
      · exact hE'.2 a ha
      · exact hW.2 a ha
    | one => exact one_pow p
    | mul a b ha hb iha ihb =>
      rw [(show Commute a b from kmTwo_comm_of_mem ha hb).mul_pow p, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  · have hc := CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf hXN
    rw [hint, Subgroup.card_bot, mul_one, hcardW, hcardE'] at hc
    exact hc

private theorem kmTwo_exists_pow_four {M K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) {m : G}
    (hm : m ∈ M) (hne : K.map (MulAut.conj m).toMonoidHom ≠ K) {p : ℕ} (hp : p.Prime)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)))
    (hpr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K))) :
    ∃ V : Subgroup (M ⧸ CFSG.pCore 2 M), CFSG.Open.IsElemAbelian p V ∧ p ^ 4 ≤ Nat.card V := by
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K))
  have hpE : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos hpr
  obtain ⟨V, hV, hVc⟩ := kmTwo_exists_pair hK hm hne hp hpZ hE
  refine ⟨V, hV, ?_⟩
  rw [hVc, show p ^ 4 = p ^ 2 * p ^ 2 by ring]
  exact Nat.mul_le_mul hpE hpE

theorem step1923_KM2 (h : Hyp1921 G A M N L) (hK : K ∈ scriptJ M N)
    (h194 : Item194UsedWide3) (kf2 : KF2) (kf3a : KF3a) (kfbig : KFBigPrime)
    (hKM : {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard = 2) :
    IsL3OddType (K ⧸ CFSG.pCore 2 K) ∨ IsTripleA6 (K ⧸ CFSG.pCore 2 K) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  obtain ⟨hKq, -⟩ := step1923_list h194 h hK
  have hKc : K ∈ oTwoComponentsIn M := hK.1
  obtain ⟨m, hm, hne⟩ : ∃ m ∈ M, K.map (MulAut.conj m).toMonoidHom ≠ K := by
    obtain ⟨x, y, hxy, hs⟩ := Set.ncard_eq_two.mp hKM
    have hmem : ∀ z ∈ ({x, y} : Set (Subgroup G)),
        ∃ g ∈ M, z = K.map (MulAut.conj g).toMonoidHom := by
      intro z hz
      rw [← hs] at hz
      exact hz
    have hK1 : K ∈ ({x, y} : Set (Subgroup G)) := by
      rw [← hs]
      exact ⟨1, M.one_mem, by ext x; simp [MulAut.conj_apply]⟩
    rcases Set.mem_insert_iff.mp hK1 with hKx | hKy
    · obtain ⟨g, hg, hyg⟩ := hmem y (Set.mem_insert_of_mem _ (Set.mem_singleton y))
      refine ⟨g, hg, fun h' => hxy ?_⟩
      rw [hyg, h', hKx]
    · have hKy' : K = y := Set.mem_singleton_iff.mp hKy
      obtain ⟨g, hg, hxg⟩ := hmem x (Set.mem_insert x _)
      refine ⟨g, hg, fun h' => hxy ?_⟩
      rw [hxg, h', hKy']
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K))
  · rcases (kf2 (K ⧸ CFSG.pCore 2 K) hKq).2 h3 with ⟨n, hn, hn1, ⟨e⟩⟩ | hA6
    · obtain ⟨k, rfl⟩ := hn
      by_cases hk1 : k = 1
      · subst hk1
        exact Or.inr (Or.inr ⟨e⟩)
      · exfalso
        have hk2 : 2 ≤ k := by omega
        rw [← two_mul] at e
        obtain ⟨p, hp, hp5, hpr⟩ := kfbig (K ⧸ CFSG.pCore 2 K) k hk2 ⟨e⟩
        have hpZ : ¬ p ∣ Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)) := by
          intro hd
          have h3p := Nat.le_of_dvd (by norm_num) (hd.trans (kf2 (K ⧸ CFSG.pCore 2 K) hKq).1)
          omega
        obtain ⟨V, hV, hVp⟩ := kmTwo_exists_pow_four hKc hm hne hp hpZ hpr
        have hbound := h.card_le_of_isElemAbelian_quotient_of_five_le hp hp5 hV
        have h4 : p ^ 2 < p ^ 4 := by
          have := Nat.pow_lt_pow_right (show 1 < p by have := hp.two_le; omega)
            (show 2 < 4 by norm_num)
          exact this
        exact absurd (hVp.trans hbound) (not_le.mpr h4)
    · exact Or.inr (Or.inl hA6)
  · by_cases hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K)
    · exact Or.inl hL3
    · exfalso
      have hpr := kf3a (K ⧸ CFSG.pCore 2 K) hKq hL3
      obtain ⟨V, hV, hVp⟩ := kmTwo_exists_pow_four hKc hm hne Nat.prime_three h3 hpr
      have hbound := h.card_le_of_isElemAbelian_quotient hV
      have hcontra := hVp.trans hbound
      norm_num at hcontra

end CFSG.RankThree.PartTwo.Late
