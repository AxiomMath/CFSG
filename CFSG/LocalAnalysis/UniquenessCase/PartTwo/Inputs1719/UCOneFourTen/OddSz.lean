module

public import CFSG.Blueprint.Catalog
import CFSG.RankThree.PartTwo.Sec16.Item166Proof
import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
import CFSG.Monster.B.TwoA.Census.PermClasses
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup

@[expose] def NoSzOverTwo (M : Type) [Group M] : Prop :=
  ∀ (H : Subgroup M) (N : Subgroup H) [N.Normal], IsPGroup 2 N → ∀ p f : ℕ,
    ¬ CFSG.Blueprint.SuzukiModel (H ⧸ N) p f

theorem noSzOverTwo_of_injective {M M' : Type} [Group M] [Group M'] (φ : M →* M')
    (hφ : Function.Injective φ) (h : NoSzOverTwo M') : NoSzOverTwo M := by
  intro H N hNnormal hN p f hSz
  let e : H ≃* H.map φ := H.equivMapOfInjective φ hφ
  have hN'normal : (N.map e.toMonoidHom).Normal := hNnormal.map e.toMonoidHom e.surjective
  have hN'p : IsPGroup 2 (N.map e.toMonoidHom) := hN.map e.toMonoidHom
  have e' : H ⧸ N ≃* H.map φ ⧸ N.map e.toMonoidHom := QuotientGroup.congr N _ e rfl
  exact h (H.map φ) (N.map e.toMonoidHom) hN'p p f
    (CFSG.RankThree.PartTwo.Sec16.suzukiModel_of_mulEquiv e'.symm hSz)

theorem noSzOverTwo_of_surjective {M M' : Type} [Group M] [Group M'] (φ : M →* M')
    (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker) (h : NoSzOverTwo M) :
    NoSzOverTwo M' := by
  intro H' N' hN'normal hN' p f hSz
  set H : Subgroup M := H'.comap φ with hH
  set ψ : H →* H' ⧸ N' := (QuotientGroup.mk' N').comp (φ.subgroupComap H') with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N' y
    obtain ⟨g, hg⟩ := hφ (x : H')
    exact ⟨⟨g, show φ g ∈ H' by rw [hg]; exact x.2⟩, by
      simp only [ψ, MonoidHom.subgroupComap]
      exact congrArg (QuotientGroup.mk' N') (Subtype.ext hg)⟩
  have hϕker : IsPGroup 2 (φ.subgroupComap H').ker := by
    have h1 : (φ.subgroupComap H').ker = Subgroup.comap H.subtype φ.ker := by
      ext x
      exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
    rw [h1]
    exact hker.comap_subtype
  have hkerψ : IsPGroup 2 ψ.ker := by
    have h1 : ψ.ker = Subgroup.comap (φ.subgroupComap H') N' := by
      rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact hN'.comap_of_ker_isPGroup (φ.subgroupComap H') hϕker
  exact h H ψ.ker hkerψ p f
    (CFSG.RankThree.PartTwo.Sec16.suzukiModel_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) hSz)

theorem NoSzOverTwo.not_suzukiModel_quotient {M : Type} [Group M] (h : NoSzOverTwo M)
    (N : Subgroup M) [N.Normal] (hN : IsPGroup 2 N) (p f : ℕ) :
    ¬ CFSG.Blueprint.SuzukiModel (M ⧸ N) p f := by
  intro hSz
  have htop : (⊤ : Subgroup M).subtype = (Subgroup.topEquiv (G := M)).toMonoidHom := by
    ext x
    rfl
  have hNsub : IsPGroup 2 (N.subgroupOf ⊤) :=
    hN.of_equiv (Subgroup.subgroupOfEquivOfLe (le_top : N ≤ ⊤)).symm
  have hmap : Subgroup.map (Subgroup.topEquiv (G := M)).toMonoidHom (N.subgroupOf ⊤) = N := by
    rw [← htop, Subgroup.map_subgroupOf_eq_of_le le_top]
  have e' : (⊤ : Subgroup M) ⧸ (N.subgroupOf ⊤) ≃* M ⧸ N :=
    QuotientGroup.congr (N.subgroupOf ⊤) N Subgroup.topEquiv hmap
  exact h ⊤ (N.subgroupOf ⊤) hNsub p f
    (CFSG.RankThree.PartTwo.Sec16.suzukiModel_of_mulEquiv e' hSz)

private lemma orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  refine (orderOf_eq_iff (by norm_num : 0 < 2)).2 ⟨by decide, ?_⟩
  intro m hm hmn
  interval_cases m
  decide

private lemma orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  refine (orderOf_eq_iff (by norm_num : 0 < 4)).2 ⟨by decide, ?_⟩
  intro m hm hmn
  interval_cases m <;> decide

private lemma orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 10 := by
  refine (orderOf_eq_iff (by norm_num : 0 < 10)).2 ⟨by decide, ?_⟩
  intro m hm hmn
  interval_cases m <;> decide

private lemma orderOf_two_zmod_thirteen : orderOf (2 : ZMod 13) = 12 := by
  refine (orderOf_eq_iff (by norm_num : 0 < 12)).2 ⟨by decide, ?_⟩
  intro m hm hmn
  interval_cases m <;> decide

private lemma false_of_two_pow_eq_one {r f : ℕ} (h2 : (2 : ZMod r) ^ f = 1) (hf : Odd f)
    (hm : 2 ∣ orderOf (2 : ZMod r)) : False :=
  Nat.not_even_iff_odd.mpr hf (even_iff_two_dvd.mpr (hm.trans (orderOf_dvd_of_pow_eq_one h2)))

theorem seven_or_seventeen_le_of_dvd {f r : ℕ} (hf : Odd f) (hr : r.Prime)
    (hrf : r ∣ 2 ^ f - 1) : r = 7 ∨ 17 ≤ r := by
  have h2 : (2 : ZMod r) ^ f = 1 := by
    have hle : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hmod : (1 : ℕ) ≡ 2 ^ f [MOD r] := (Nat.modEq_iff_dvd' hle).2 hrf
    have h1 : ((2 ^ f : ℕ) : ZMod r) = 1 := by
      rw [← (ZMod.natCast_eq_natCast_iff 1 (2 ^ f) r).2 hmod]
      norm_num
    simpa [Nat.cast_pow] using h1
  have hrne2 : r ≠ 2 := by
    intro h
    subst h
    rw [show (2 : ZMod 2) = 0 from by decide, zero_pow hf.pos.ne'] at h2
    exact zero_ne_one h2
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hrne7, hrlt⟩ := hcon
  have hr2 : 2 ≤ r := hr.two_le
  interval_cases r <;>
    first
      | exact hrne2 rfl
      | exact hrne7 rfl
      | (refine false_of_two_pow_eq_one h2 hf ?_
         simp [orderOf_two_zmod_three, orderOf_two_zmod_five, orderOf_two_zmod_eleven,
           orderOf_two_zmod_thirteen])
      | (norm_num at hr)

theorem exists_torus_of_suzukiModel {S : Type} [Group S]
    {p f : ℕ} (h : CFSG.Blueprint.SuzukiModel S p f) :
    ∃ (U : Subgroup S) (t : S), IsPGroup 2 U ∧ (∃ u ∈ U, ∃ v ∈ U, u * v ≠ v * u) ∧
      t ∈ normalizer (U : Set S) ∧ (orderOf t).Prime ∧ (orderOf t = 7 ∨ 17 ≤ orderOf t) ∧
      ∃ x ∈ U, t * x ≠ x * t := by
  obtain ⟨-, a, ha, K, hKfld, hKfin, hf, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcard, hf]
  have hex : ∃ c : K, c ^ 2 ^ (a + 1) ≠ c := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hgord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    have hq : g ^ 2 ^ (a + 1) = g := by
      refine Units.ext ?_
      simpa using hcon (g : K)
    have h1 : g ^ (2 ^ (a + 1) - 1) = 1 := by
      have h2 : g ^ (2 ^ (a + 1) - 1) * g = 1 * g := by
        rw [← pow_succ, Nat.sub_one_add_one (pow_ne_zero _ two_ne_zero), hq, one_mul]
      exact mul_right_cancel h2
    have hdvd : orderOf g ∣ 2 ^ (a + 1) - 1 := orderOf_dvd_of_pow_eq_one h1
    rw [hgord, Nat.card_units, hK] at hdvd
    have hlt : 2 ^ (a + 1) - 1 < 2 ^ (2 * a + 1) - 1 := by
      have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
      have h2 := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : a + 1 < 2 * a + 1)
      omega
    have hpos : 0 < 2 ^ (a + 1) - 1 := by
      have h1 : 2 ≤ 2 ^ (a + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  obtain ⟨c, hc⟩ := hex
  have hUcard : Nat.card (CFSG.LieType.Ree.suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 :=
    (CFSG.LieType.Ree.suzuki_unipotent_structure hK).2.1
  have hU2 : IsPGroup 2 (CFSG.LieType.Ree.suzukiU a K) :=
    IsPGroup.of_card (n := 2 * (2 * a + 1)) (by rw [hUcard, ← pow_mul]; ring_nf)
  have hnab : ∃ u ∈ CFSG.LieType.Ree.suzukiU a K, ∃ v ∈ CFSG.LieType.Ree.suzukiU a K,
      u * v ≠ v * u := by
    refine ⟨CFSG.LieType.Ree.suzukiSElt a K 1 0,
      CFSG.LieType.Ree.suzukiSElt_mem_suzukiU a K 1 0,
      CFSG.LieType.Ree.suzukiSElt a K c 0,
      CFSG.LieType.Ree.suzukiSElt_mem_suzukiU a K c 0, ?_⟩
    intro heq
    have hL : CFSG.LieType.Ree.suzukiSElt a K 1 0 * CFSG.LieType.Ree.suzukiSElt a K c 0 =
        CFSG.LieType.Ree.suzukiSElt a K (1 + c) (0 + 0 + 1 ^ 2 ^ (a + 1) * c) :=
      CFSG.LieType.Ree.suzukiSElt_mul (a := a) (K := K) hK 1 0 c 0
    have hR : CFSG.LieType.Ree.suzukiSElt a K c 0 * CFSG.LieType.Ree.suzukiSElt a K 1 0 =
        CFSG.LieType.Ree.suzukiSElt a K (c + 1) (0 + 0 + c ^ 2 ^ (a + 1) * 1) :=
      CFSG.LieType.Ree.suzukiSElt_mul (a := a) (K := K) hK c 0 1 0
    rw [hL, hR] at heq
    exact hc (by simpa using (CFSG.LieType.Ree.suzukiSElt_inj.1 heq).2.symm)
  have hcardU : Nat.card Kˣ = 2 ^ (2 * a + 1) - 1 := by rw [Nat.card_units, hK]
  have hUbig : 7 ≤ Nat.card Kˣ := by
    rw [hcardU]
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) :=
      Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 3 ≤ 2 * a + 1)
    norm_num at h8 ⊢
    omega
  obtain ⟨r, hr, hrvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card Kˣ) (by omega)
  have hrf : Fact r.Prime := ⟨hr⟩
  have hr7 : r = 7 ∨ 17 ≤ r :=
    seven_or_seventeen_le_of_dvd (f := 2 * a + 1) ⟨a, by ring⟩ hr (by rwa [hcardU] at hrvd)
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hrvd
  let D : Kˣ →* CFSG.Blueprint.suzukiGroup a K :=
    { toFun := CFSG.LieType.Ree.suzukiDElt a K
      map_one' := CFSG.LieType.Ree.suzukiDElt_one
      map_mul' := fun x y => (CFSG.LieType.Ree.suzukiDElt_mul x y).symm }
  have hDord : orderOf (CFSG.LieType.Ree.suzukiDElt a K l) = r := by
    have h : orderOf (CFSG.LieType.Ree.suzukiDElt a K l) = orderOf l :=
      orderOf_injective D (CFSG.LieType.Ree.suzukiDElt_injective hK) l
    rw [h, hl]
  have htnorm : CFSG.LieType.Ree.suzukiDElt a K l ∈
      normalizer (CFSG.LieType.Ree.suzukiU a K :
        Set (CFSG.Blueprint.suzukiGroup a K)) :=
    CFSG.LieType.Ree.suzukiT_le_normalizer hK (CFSG.LieType.Ree.suzukiDElt_mem_suzukiT a K l)
  have hnc : ∃ x ∈ CFSG.LieType.Ree.suzukiU a K,
      CFSG.LieType.Ree.suzukiDElt a K l * x ≠ x * CFSG.LieType.Ree.suzukiDElt a K l := by
    refine ⟨CFSG.LieType.Ree.suzukiSElt a K 1 0,
      CFSG.LieType.Ree.suzukiSElt_mem_suzukiU a K 1 0, ?_⟩
    intro heq
    have hconj : (CFSG.LieType.Ree.suzukiDElt a K l)⁻¹ *
        CFSG.LieType.Ree.suzukiSElt a K 1 0 * CFSG.LieType.Ree.suzukiDElt a K l =
        CFSG.LieType.Ree.suzukiSElt a K 1 0 := by
      calc (CFSG.LieType.Ree.suzukiDElt a K l)⁻¹ * CFSG.LieType.Ree.suzukiSElt a K 1 0 *
            CFSG.LieType.Ree.suzukiDElt a K l
          = (CFSG.LieType.Ree.suzukiDElt a K l)⁻¹ *
            (CFSG.LieType.Ree.suzukiSElt a K 1 0 * CFSG.LieType.Ree.suzukiDElt a K l) := by
            group
        _ = (CFSG.LieType.Ree.suzukiDElt a K l)⁻¹ *
            (CFSG.LieType.Ree.suzukiDElt a K l * CFSG.LieType.Ree.suzukiSElt a K 1 0) := by
            rw [← heq]
        _ = CFSG.LieType.Ree.suzukiSElt a K 1 0 := by group
    rw [CFSG.LieType.Ree.suzukiDElt_conj hK] at hconj
    have h2 := CFSG.LieType.Ree.suzukiSElt_inj.1 hconj
    have hl1 : l = 1 := by
      refine Units.ext ?_
      simpa using h2.1
    rw [hl1, orderOf_one] at hl
    omega
  refine ⟨(CFSG.LieType.Ree.suzukiU a K).map e.symm.toMonoidHom,
    e.symm (CFSG.LieType.Ree.suzukiDElt a K l), hU2.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := hnab
    refine ⟨e.symm u, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, e.symm v,
      Subgroup.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    intro heq
    exact huv (by simpa using congrArg e heq)
  · rw [Subgroup.mem_normalizer_iff']
    intro x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_symm, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff'.mp htnorm (e x)
  · rw [MulEquiv.orderOf_eq, hDord]
    exact hr
  · rw [MulEquiv.orderOf_eq, hDord]
    exact hr7
  · obtain ⟨x, hx, hxne⟩ := hnc
    refine ⟨e.symm x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    intro heq
    exact hxne (by simpa using congrArg e heq)


theorem exists_twoSubgroup_of_suzukiModel_quotient {H : Type}
    [Group H] (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N) {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel (H ⧸ N) p f) :
    ∃ (P : Subgroup H) (y : H), IsPGroup 2 P ∧ (∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧
      y ∈ normalizer (P : Set H) ∧ (orderOf y).Prime ∧ (orderOf y = 7 ∨ 17 ≤ orderOf y) ∧
      ∃ x ∈ P, y * x ≠ x * y := by
  obtain ⟨U, t, hU2, ⟨u₀, hu₀, v₀, hv₀, huv₀⟩, htnorm, htprime, ht7, x₀, hx₀U, hx₀⟩ :=
    exists_torus_of_suzukiModel h
  let π : H →* (H ⧸ N) := QuotientGroup.mk' N
  have hπker : IsPGroup 2 π.ker := by
    rw [show π.ker = N from by rw [show π = QuotientGroup.mk' N from rfl, QuotientGroup.ker_mk']]
    exact hN
  have hP2 : IsPGroup 2 (U.comap π) := hU2.comap_of_ker_isPGroup π hπker
  have hPnab : ∃ u ∈ U.comap π, ∃ v ∈ U.comap π, u * v ≠ v * u := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N u₀
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective N v₀
    refine ⟨u, Subgroup.mem_comap.mpr hu₀, v, Subgroup.mem_comap.mpr hv₀, ?_⟩
    intro heq
    exact huv₀ (by simpa [π, QuotientGroup.mk'_apply] using congrArg π heq)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N t
  have hxr : x ^ orderOf t ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    show π (x ^ orderOf t) = 1
    rw [map_pow, hx, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := hN ⟨x ^ orderOf t, hxr⟩
  have hj' : x ^ (orderOf t * 2 ^ j) = 1 := by
    have h := congrArg Subtype.val hj
    simpa [pow_mul] using h
  have hπy : π (x ^ 2 ^ j) = t ^ 2 ^ j := by rw [map_pow, hx]
  have hyr : (x ^ 2 ^ j) ^ orderOf t = 1 := by
    rw [← pow_mul, Nat.mul_comm (2 ^ j) (orderOf t), hj']
  have hodd : Odd (orderOf t) := by
    refine htprime.odd_of_ne_two ?_
    rcases ht7 with h | h
    · rw [h]; norm_num
    · omega
  have hcop : (2 ^ j).Coprime (orderOf t) :=
    ((Nat.coprime_two_right.mpr hodd).pow_right j).symm
  have hne : x ^ 2 ^ j ≠ 1 := by
    intro hone
    have h1 : t ^ 2 ^ j = 1 := by rw [← hπy, hone, map_one]
    have h2 : orderOf (t ^ 2 ^ j) = orderOf t := hcop.symm.orderOf_pow
    rw [orderOf_eq_one_iff.mpr h1] at h2
    exact htprime.ne_one h2.symm
  have hyord : orderOf (x ^ 2 ^ j) = orderOf t := by
    have hdvd : orderOf (x ^ 2 ^ j) ∣ orderOf t := orderOf_dvd_of_pow_eq_one hyr
    rcases (Nat.dvd_prime htprime).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  have htnorm' : t ^ 2 ^ j ∈ normalizer (U : Set (H ⧸ N)) := Subgroup.pow_mem _ htnorm _
  have hynorm : x ^ 2 ^ j ∈ normalizer (U.comap π : Set H) := by
    rw [Subgroup.mem_normalizer_iff']
    intro w
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, hπy]
    exact Subgroup.mem_normalizer_iff'.mp htnorm' (π w)
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk'_surjective N x₀
  have hx₁P : x₁ ∈ U.comap π := by
    rw [Subgroup.mem_comap]
    change (x₁ : H ⧸ N) ∈ U
    rw [show (x₁ : H ⧸ N) = x₀ from by rw [← QuotientGroup.mk'_apply]; exact hx₁]
    exact hx₀U
  refine ⟨U.comap π, x ^ 2 ^ j, hP2, hPnab, hynorm, ?_, ?_, x₁, hx₁P, ?_⟩
  · rw [hyord]; exact htprime
  · rw [hyord]; exact ht7
  · intro heq
    have hcommq : (t ^ 2 ^ j) * x₀ = x₀ * (t ^ 2 ^ j) := by
      have h1 := congrArg π heq
      simpa [π, QuotientGroup.mk'_apply, map_mul, hπy, hx₁] using h1
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hc : Commute (t ^ 2 ^ j) x₀ := hcommq
    have htcomm := hc.pow_left m
    rw [hm] at htcomm
    exact hx₀ htcomm


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
