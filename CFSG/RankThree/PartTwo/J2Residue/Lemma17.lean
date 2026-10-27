module

public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import CFSG.RankThree.PartTwo.J2Residue.Config
import CFSG.GroupTheory.PCoreSurjective
import CFSG.GroupTheory.CoprimeSectionStability
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Generic

variable {L : Type} [Group L]

private theorem le_center_of_card_eq_two' (N : Subgroup L) [N.Normal]
    (hN : Nat.card N = 2) : N ≤ Subgroup.center L := by
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  by_cases hxone : x = 1
  · simp [hxone]
  have hxne : (⟨x, hx⟩ : N) ≠ 1 := by
    intro h
    exact hxone (congrArg Subtype.val h)
  let y : N := ⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x hx g⟩
  have hyne : y ≠ 1 := by
    intro h
    have hconj : g * x * g⁻¹ = 1 := congrArg Subtype.val h
    have hmul : g * x = g := by
      simpa using (mul_inv_eq_iff_eq_mul.mp hconj)
    exact hxone (mul_left_cancel (hmul.trans (mul_one g).symm))
  have hyx : y = (⟨x, hx⟩ : N) := (huniq y hyne).trans (huniq _ hxne).symm
  have hval : g * x * g⁻¹ = x := congrArg Subtype.val hyx
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [hval]

private theorem zpowers_le_comap_centralizer (N : Subgroup L) [N.Normal] {d : L}
    {y : L ⧸ N} (hy : (d : L ⧸ N) * y = y * (d : L ⧸ N)) :
    Subgroup.zpowers d ≤
      (Subgroup.centralizer ({y} : Set (L ⧸ N))).comap (QuotientGroup.mk' N) := by
  rw [Subgroup.zpowers_le]
  show (QuotientGroup.mk' N d) ∈ Subgroup.centralizer ({y} : Set (L ⧸ N))
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hy

private theorem le_normalizer_of_normal' (N : Subgroup L) [N.Normal] (H : Subgroup L) :
    H ≤ Subgroup.normalizer (N : Set L) := by
  rw [Subgroup.normalizer_eq_top]
  exact le_top

private theorem isPerfect_inSubgroup_perfectResidual' [Finite L] (H : Subgroup L) :
    Group.IsPerfect ↥(inSubgroup perfectResidual H) := by
  have h := (perfect_residual_characterization (G := ↥H)).2.2.1
  haveI := h
  exact Group.IsPerfect.ofSurjective
    (f := ((perfectResidual ↥H).equivMapOfInjective _ H.subtype_injective).toMonoidHom)
    (MulEquiv.surjective _)

private theorem isPerfect_subgroupOf' {K X : Subgroup L} (hKX : K ≤ X)
    (hK : Group.IsPerfect ↥K) : Group.IsPerfect ↥(K.subgroupOf X) := by
  haveI := hK
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKX).symm.toMonoidHom)
    (MulEquiv.surjective _)

variable [Finite L]

private theorem pCore_quot_inf_centralizer_eq (N : Subgroup L) [N.Normal]
    (hN : N ≤ CFSG.pCore 2 L) {d : L} (hd : orderOf d = 3) :
    CFSG.pCore 2 (L ⧸ N) ⊓ Subgroup.centralizer ({(d : L ⧸ N)} : Set (L ⧸ N)) =
      (CFSG.pCore 2 L ⊓ Subgroup.centralizer ({d} : Set L)).map (QuotientGroup.mk' N) := by
  classical
  set R := CFSG.pCore 2 L with hRdef
  haveI hRn : R.Normal := CFSG.pCore_normal
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup
  have hN2 : IsPGroup 2 N := hR2.to_le hN
  have hmap : R.map (QuotientGroup.mk' N) = CFSG.pCore 2 (L ⧸ N) :=
    CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk']; exact hN2)
  apply le_antisymm
  · intro y hy
    obtain ⟨hyR, hyc⟩ := Subgroup.mem_inf.mp hy
    rw [← hmap] at hyR
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hyR
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    have hD : ∀ g ∈ Subgroup.zpowers d, g * r * g⁻¹ * r⁻¹ ∈ N := by
      intro g hg
      have hg' := zpowers_le_comap_centralizer N hyc.symm hg
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hg'
      have h1 : (QuotientGroup.mk' N (g * r * g⁻¹ * r⁻¹) : L ⧸ N) = 1 := by
        simp only [map_mul, map_inv]
        rw [hg']
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥R) := by
      rw [Nat.card_zpowers, hd]
      obtain ⟨k, hk⟩ := hR2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    have hRs : Group.IsSolvable ↥R := by
      haveI := hR2.isNilpotent
      infer_instance
    have hmem := (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff hN
      (le_normalizer_of_normal' N R) (le_normalizer_of_normal' R _)
      (le_normalizer_of_normal' N _) hcop hRs hr).mp hD
    have hCN : R ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set L) ≤
        Subgroup.normalizer (N : Set L) := le_normalizer_of_normal' N _
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ N hCN] at hmem
    obtain ⟨w, hw, n, hn, rfl⟩ := Set.mem_mul.mp hmem
    have hw' := Subgroup.mem_inf.mp hw
    refine Subgroup.mem_map.mpr ⟨w, Subgroup.mem_inf.mpr ⟨hw'.1, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hw'.2 d (Subgroup.mem_zpowers d)).symm
    · have hn1 : (QuotientGroup.mk' N n : L ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, hn1, mul_one]
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hxR
    · rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
      show (QuotientGroup.mk' N x) * (QuotientGroup.mk' N d) =
        (QuotientGroup.mk' N d) * (QuotientGroup.mk' N x)
      rw [← map_mul, ← map_mul, hxc]

private theorem mem_of_odd_orderOf {L₁ R : Subgroup L} (hR2 : IsPGroup 2 R)
    (hdec : ∀ x ∈ L₁, ∃ y ∈ inSubgroup perfectResidual L₁, ∃ r ∈ R, x = y * r)
    {x : L} (hxL₁ : x ∈ L₁) (hodd : Odd (orderOf x)) :
    x ∈ inSubgroup perfectResidual L₁ := by
  classical
  set P := perfectResidual ↥L₁
  haveI : P.Normal := inferInstance
  obtain ⟨y, hy, r, hr, hxyr⟩ := hdec x hxL₁
  have hyL₁ : y ∈ L₁ := (Subgroup.map_subtype_le _) hy
  have hrL₁ : r ∈ L₁ := by
    have : r = y⁻¹ * x := by rw [hxyr]; group
    rw [this]
    exact L₁.mul_mem (L₁.inv_mem hyL₁) hxL₁
  obtain ⟨y', hy'P, hy'⟩ := Subgroup.mem_map.mp hy
  set q := QuotientGroup.mk' P
  have hqy : q y' = 1 := (QuotientGroup.eq_one_iff y').mpr hy'P
  have hy'' : (y' : L) = y := hy'
  have hxe : (⟨x, hxL₁⟩ : ↥L₁) = y' * ⟨r, hrL₁⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hy'']
    exact hxyr
  have hqx : q ⟨x, hxL₁⟩ = q ⟨r, hrL₁⟩ := by
    rw [hxe, map_mul, hqy, one_mul]
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hr2 : (⟨r, hrL₁⟩ : ↥L₁) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf (q ⟨x, hxL₁⟩) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hqx, ← map_pow, hr2, map_one]
  have h2 : orderOf (q ⟨x, hxL₁⟩) ∣ orderOf x := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨x, hxL₁⟩ : ↥L₁) ^ orderOf x = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hone : orderOf (q ⟨x, hxL₁⟩) = 1 := by
    have hg := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    exact Nat.dvd_one.mp hg
  have hmemP : (⟨x, hxL₁⟩ : ↥L₁) ∈ P :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hone)
  exact Subgroup.mem_map.mpr ⟨_, hmemP, rfl⟩

end Generic


private theorem four_le_aux (hfix : KJFix) (hsplit : KJSplit) (hcover : KJCover) :
    ∀ (n : ℕ) (L : Type) [Group L] [Finite L], Nat.card L = n → Group.IsPerfect L →
      Nonempty (L ⧸ CFSG.pCore 2 L ≃* J2) → ∀ d : L, orderOf d = 3 →
      (∃ S : Sylow 3 L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d}) →
      CFSG.pCore 2 L ⊓ inSubgroup perfectResidual (Subgroup.centralizer ({d} : Set L)) ≠ ⊥ →
      4 ≤ Nat.card ↥(CFSG.pCore 2 L ⊓ Subgroup.centralizer ({d} : Set L)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L _ _ hn hperf hJ d hd hd3 hK
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect L := hperf
  by_contra hlt
  push Not at hlt
  set R := CFSG.pCore 2 L with hRdef
  haveI hRn : R.Normal := CFSG.pCore_normal
  have hR2 : IsPGroup 2 ↥R := CFSG.pCore_isPGroup
  set W := R ⊓ Subgroup.centralizer ({d} : Set L) with hWdef
  set K := inSubgroup perfectResidual (Subgroup.centralizer ({d} : Set L)) with hKdef
  have hKC : K ≤ Subgroup.centralizer ({d} : Set L) := Subgroup.map_subtype_le _
  have hKperf : Group.IsPerfect ↥K := isPerfect_inSubgroup_perfectResidual' _
  obtain ⟨z, hzRK, hz1⟩ : ∃ z ∈ R ⊓ K, z ≠ 1 :=
    (Subgroup.bot_or_exists_ne_one (R ⊓ K)).resolve_left hK
  have hzR : z ∈ R := (Subgroup.mem_inf.mp hzRK).1
  have hzK : z ∈ K := (Subgroup.mem_inf.mp hzRK).2
  have hzW : z ∈ W := Subgroup.mem_inf.mpr ⟨hzR, hKC hzK⟩
  have hW2 : IsPGroup 2 ↥W := hR2.to_le inf_le_left
  have hWcard : Nat.card ↥W = 2 := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    have hne : Nat.card ↥W ≠ 1 := by
      intro h1
      have hWb : W = ⊥ := Subgroup.eq_bot_of_card_eq W h1
      exact hz1 (Subgroup.mem_bot.mp (hWb ▸ hzW))
    rw [hk] at hlt hne ⊢
    have hk2 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      norm_num at h4
      omega
    interval_cases k
    · simp at hne
    · rfl
  have hWz : W = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzW)
    rw [hWcard, Nat.card_zpowers]
    have h1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
    have h0 : 0 < orderOf z := orderOf_pos z
    omega
  have hdR : d ∉ R := by
    intro h
    obtain ⟨k, hk⟩ := hR2 ⟨d, h⟩
    have hdvd : orderOf d ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    rw [hd] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hquot : ∀ (N : Subgroup L) [N.Normal], N ≤ R →
      Group.IsPerfect (L ⧸ N) ∧ Nonempty ((L ⧸ N) ⧸ CFSG.pCore 2 (L ⧸ N) ≃* J2) ∧
      orderOf (QuotientGroup.mk' N d) = 3 ∧
      (∃ S : Sylow 3 (L ⧸ N), QuotientGroup.mk' N d ∈ (S : Subgroup (L ⧸ N)) ∧
        (S : Subgroup (L ⧸ N)) ≤ Subgroup.centralizer {QuotientGroup.mk' N d}) := by
    intro N _ hNR
    have hπs : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
    have hker : IsPGroup 2 ↥(QuotientGroup.mk' N).ker := by
      rw [QuotientGroup.ker_mk']
      exact hR2.to_le hNR
    refine ⟨Group.IsPerfect.ofSurjective hπs, ?_, ?_, ?_⟩
    · obtain ⟨e⟩ := hJ
      obtain ⟨e'⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
        (QuotientGroup.mk' N) hπs hker
      exact ⟨e'.symm.trans e⟩
    · apply orderOf_eq_prime
      · rw [← map_pow, ← hd, pow_orderOf_eq_one, map_one]
      · intro h
        exact hdR (hNR ((QuotientGroup.eq_one_iff d).mp h))
    · obtain ⟨S, hdS, hSC⟩ := hd3
      refine ⟨S.mapSurjective hπs, ?_, ?_⟩
      · rw [Sylow.coe_mapSurjective]
        exact Subgroup.mem_map_of_mem _ hdS
      · rw [Sylow.coe_mapSurjective]
        rintro _ ⟨s, hs, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
        rw [← map_mul, ← map_mul, this]
  by_cases h1 : ∃ N : Subgroup L, N.Normal ∧ N ≤ R ∧ N ≠ ⊥ ∧ z ∉ N
  · obtain ⟨N, hNn, hNR, hN1, hzN⟩ := h1
    haveI := hNn
    obtain ⟨hperf', hJ', hd', hd3'⟩ := hquot N hNR
    have hπs : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
    have hker : IsPGroup 2 ↥(QuotientGroup.mk' N).ker := by
      rw [QuotientGroup.ker_mk']
      exact hR2.to_le hNR
    have hcard : Nat.card (L ⧸ N) < n := by
      rw [← hn]
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have hN1' : Nat.card ↥N ≠ 1 := fun h' => hN1 (Subgroup.eq_bot_of_card_eq N h')
      have hNpos : 0 < Nat.card ↥N := Nat.card_pos
      have hQpos : 0 < Nat.card (L ⧸ N) := Nat.card_pos
      have hN2' : 2 ≤ Nat.card ↥N := by omega
      nlinarith
    have hK' : CFSG.pCore 2 (L ⧸ N) ⊓ inSubgroup perfectResidual
        (Subgroup.centralizer ({QuotientGroup.mk' N d} : Set (L ⧸ N))) ≠ ⊥ := by
      intro hbot
      have hKπC : K.map (QuotientGroup.mk' N) ≤
          Subgroup.centralizer ({QuotientGroup.mk' N d} : Set (L ⧸ N)) := by
        rintro _ ⟨k, hk, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
        rw [← map_mul, ← map_mul, this]
      have hKπp : Group.IsPerfect ↥(K.map (QuotientGroup.mk' N)) := by
        haveI := hKperf
        exact Group.IsPerfect.map (QuotientGroup.mk' N)
      have hzmem : QuotientGroup.mk' N z ∈ CFSG.pCore 2 (L ⧸ N) ⊓ inSubgroup perfectResidual
          (Subgroup.centralizer ({QuotientGroup.mk' N d} : Set (L ⧸ N))) := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · rw [← CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker (QuotientGroup.mk' N) hπs hker]
          exact Subgroup.mem_map_of_mem _ hzR
        · exact Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKπp hKπC
            (Subgroup.mem_map_of_mem _ hzK)
      rw [hbot] at hzmem
      exact hzN ((QuotientGroup.eq_one_iff z).mp (Subgroup.mem_bot.mp hzmem))
    have key := ih (Nat.card (L ⧸ N)) hcard (L ⧸ N) rfl hperf' hJ' (QuotientGroup.mk' N d) hd'
      hd3' hK'
    have heq := pCore_quot_inf_centralizer_eq N hNR hd
    have heq' : CFSG.pCore 2 (L ⧸ N) ⊓
        Subgroup.centralizer ({QuotientGroup.mk' N d} : Set (L ⧸ N)) =
        W.map (QuotientGroup.mk' N) := heq
    rw [heq'] at key
    have hle : Nat.card ↥(W.map (QuotientGroup.mk' N)) ≤ Nat.card ↥W :=
      Nat.card_le_card_of_surjective _ ((QuotientGroup.mk' N).subgroupMap_surjective W)
    omega
  push Not at h1
  have hR1 : R ≠ ⊥ := fun h => hz1 (Subgroup.mem_bot.mp (h ▸ hzR))
  obtain ⟨R₁, hR₁n, hR₁lt, hR₁max⟩ := CFSG.exists_maximal_normal_lt R hR1
  haveI := hR₁n
  have hR₁R : R₁ ≤ R := hR₁lt.le
  by_cases hzR₁ : z ∉ R₁
  ·
    have hR₁bot : R₁ = ⊥ := by
      by_contra h
      exact hzR₁ (h1 R₁ hR₁n hR₁R h)
    have hmin : ∀ K' : Subgroup L, K'.Normal → K' ≤ R → K' = ⊥ ∨ K' = R := by
      intro K' hK'n hK'R
      by_cases hK'b : K' = ⊥
      · exact Or.inl hK'b
      · right
        exact hR₁max K' hK'n (hR₁bot ▸ bot_lt_iff_ne_bot.mpr hK'b) hK'R
    have hRcard : Nat.card ↥R = 2 := hfix L hJ R hRn le_rfl hR1 hmin d hd hd3 hWcard
    have hRc : R ≤ Subgroup.center L := le_center_of_card_eq_two' R hRcard
    have hcov := hcover L hperf R hRc hRcard hJ d hd hd3
    exact hz1 (Subgroup.mem_bot.mp (hcov ▸ hzRK))
  push Not at hzR₁
  set π := QuotientGroup.mk' R₁ with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective R₁
  have hR₁2 : IsPGroup 2 ↥R₁ := hR2.to_le hR₁R
  have hker : IsPGroup 2 ↥π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact hR₁2
  set M := R.map π with hMdef
  haveI hMn : M.Normal := hRn.map π hπs
  have hMeq : M = CFSG.pCore 2 (L ⧸ R₁) :=
    CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker π hπs hker
  have hM2 : IsPGroup 2 ↥M := hR2.map π
  have hπR : ∀ x : L, π x ∈ M → ∃ r ∈ R, x = r := by
    intro x hx
    obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp hx
    have hmem : r⁻¹ * x ∈ R₁ := by
      rw [← QuotientGroup.eq_one_iff (r⁻¹ * x)]
      show π (r⁻¹ * x) = 1
      rw [map_mul, map_inv, hrx, inv_mul_cancel]
    exact ⟨r * (r⁻¹ * x), R.mul_mem hr (hR₁R hmem), by group⟩
  have hM1 : M ≠ ⊥ := by
    intro h
    apply hR₁lt.2
    intro r hr
    have : π r ∈ M := Subgroup.mem_map_of_mem π hr
    rw [h] at this
    exact (QuotientGroup.eq_one_iff r).mp (Subgroup.mem_bot.mp this)
  have hMmin : ∀ K' : Subgroup (L ⧸ R₁), K'.Normal → K' ≤ M → K' = ⊥ ∨ K' = M := by
    intro K' hK'n hK'M
    have hK''n : (K'.comap π).Normal := hK'n.comap π
    have hR₁K'' : R₁ ≤ K'.comap π := by
      intro x hx
      show π x ∈ K'
      rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact K'.one_mem
    have hK''R : K'.comap π ≤ R := by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := hπR x (hK'M hx)
      exact hr
    have hK'eq : K' = (K'.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs K').symm
    rcases eq_or_lt_of_le hR₁K'' with h | h
    · left
      rw [hK'eq, ← h, Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    · right
      rw [hK'eq, hR₁max _ hK''n h hK''R]
  have hLM : Nonempty ((L ⧸ R₁) ⧸ M ≃* J2) := by
    obtain ⟨e⟩ := hJ
    exact ⟨(QuotientGroup.quotientQuotientEquivQuotient R₁ R hR₁R).trans e⟩
  obtain ⟨-, -, hd', hd3'⟩ := hquot R₁ hR₁R
  have hMC : M ⊓ Subgroup.centralizer ({π d} : Set (L ⧸ R₁)) = ⊥ := by
    have heq := pCore_quot_inf_centralizer_eq R₁ hR₁R hd
    have heq' : CFSG.pCore 2 (L ⧸ R₁) ⊓ Subgroup.centralizer ({π d} : Set (L ⧸ R₁)) =
        W.map π := heq
    rw [hMeq, heq', Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk', hWz]
    exact Subgroup.zpowers_le.mpr hzR₁
  obtain ⟨H', hH'⟩ := hsplit (L ⧸ R₁) M hM2 hM1 hMmin hLM (π d) hd' hd3' hMC
  have hH'M : H' ⊓ M = ⊥ := hH'.disjoint.eq_bot
  have hH'dec : ∀ w : L ⧸ R₁, ∃ h ∈ H', ∃ m ∈ M, w = h * m := by
    intro w
    have hw : w ∈ ((H' ⊔ M : Subgroup (L ⧸ R₁)) : Set (L ⧸ R₁)) := by
      rw [hH'.sup_eq_top]
      exact Subgroup.mem_top w
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H' M
      (le_normalizer_of_normal' M H')] at hw
    obtain ⟨h, hh, m, hm, rfl⟩ := Set.mem_mul.mp hw
    exact ⟨h, hh, m, hm, rfl⟩
  have hnd : ¬ 3 ∣ Nat.card ((L ⧸ R₁) ⧸ H') := by
    rw [← Subgroup.index, hH'.symm.index_eq_card]
    obtain ⟨k, hk⟩ := hM2.exists_card_eq
    rw [hk]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have h3grp : IsPGroup 3 ↥(Subgroup.zpowers (π d)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hd', pow_one]
  obtain ⟨q, hq⟩ := h3grp.nonempty_fixed_point_of_prime_not_dvd_card ((L ⧸ R₁) ⧸ H') hnd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hgd : g⁻¹ * π d * g ∈ H' := by
    have hfix' := hq ⟨π d, Subgroup.mem_zpowers _⟩
    have hfix'' : ((π d * g : L ⧸ R₁) : (L ⧸ R₁) ⧸ H') = (g : (L ⧸ R₁) ⧸ H') := hfix'
    have := QuotientGroup.eq.mp hfix''
    have h2 : g⁻¹ * π d * g = ((π d * g)⁻¹ * g)⁻¹ := by group
    rw [h2]
    exact H'.inv_mem this
  set H'' := H'.map (MulAut.conj g).toMonoidHom with hH''def
  have hdH'' : π d ∈ H'' := by
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * π d * g, hgd, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hH''M : H'' ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwH, hwM⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hwH
    have hhM : h ∈ M := by
      have := hMn.conj_mem _ hwM g⁻¹
      simpa [MulAut.conj_apply, mul_assoc] using this
    have : h ∈ H' ⊓ M := Subgroup.mem_inf.mpr ⟨hh, hhM⟩
    rw [hH'M] at this
    rw [Subgroup.mem_bot.mp this, map_one]
    exact Subgroup.one_mem _
  have hH''dec : ∀ w : L ⧸ R₁, ∃ h ∈ H'', ∃ m ∈ M, w = h * m := by
    intro w
    obtain ⟨h, hh, m, hm, hw⟩ := hH'dec (g⁻¹ * w * g)
    refine ⟨g * h * g⁻¹, Subgroup.mem_map.mpr ⟨h, hh, by simp [MulAut.conj_apply]⟩,
      g * m * g⁻¹, hMn.conj_mem m hm g, ?_⟩
    have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rw [this, hw]
    group
  set L₁ := H''.comap π with hL₁def
  have hR₁L₁ : R₁ ≤ L₁ := by
    intro x hx
    show π x ∈ H''
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact H''.one_mem
  have hdL₁ : d ∈ L₁ := hdH''
  have hL₁R : ∀ x ∈ L₁, x ∈ R → x ∈ R₁ := by
    intro x hxL hxR
    have : π x ∈ H'' ⊓ M := Subgroup.mem_inf.mpr ⟨hxL, Subgroup.mem_map_of_mem π hxR⟩
    rw [hH''M] at this
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  have hL₁dec : ∀ x : L, ∃ y ∈ L₁, ∃ r ∈ R, x = y * r := by
    intro x
    obtain ⟨h, hh, m, hm, hxe⟩ := hH''dec (π x)
    obtain ⟨y, rfl⟩ := hπs h
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hm
    have hmem : (y * r)⁻¹ * x ∈ R₁ := by
      rw [← QuotientGroup.eq_one_iff ((y * r)⁻¹ * x)]
      show π ((y * r)⁻¹ * x) = 1
      rw [map_mul, map_inv, map_mul, hxe]
      group
    exact ⟨y, hh, r * ((y * r)⁻¹ * x), R.mul_mem hr (hR₁R hmem), by group⟩
  have hCL₁ : Subgroup.centralizer ({d} : Set L) ≤ L₁ := by
    intro x hx
    have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    obtain ⟨h, hh, m, hm, hxe⟩ := hH''dec (π x)
    have hcomm : Commute (π d) (π x) := by
      show π d * π x = π x * π d
      rw [← map_mul, ← map_mul, hxd]
    have hX : π x * (π d)⁻¹ * (π x)⁻¹ = (π d)⁻¹ := by
      have := hcomm.inv_left.eq
      calc π x * (π d)⁻¹ * (π x)⁻¹ = (π d)⁻¹ * π x * (π x)⁻¹ := by rw [this]
        _ = (π d)⁻¹ := by group
    have hm' : m = h⁻¹ * π x := by rw [hxe]; group
    have hc2 : π d * m * (π d)⁻¹ * m⁻¹ ∈ H'' := by
      have hcalc : π d * m * (π d)⁻¹ * m⁻¹ = π d * h⁻¹ * (π x * (π d)⁻¹ * (π x)⁻¹) * h := by
        rw [hm']
        group
      rw [hcalc, hX]
      exact H''.mul_mem (H''.mul_mem (H''.mul_mem hdH'' (H''.inv_mem hh)) (H''.inv_mem hdH'')) hh
    have hc1 : π d * m * (π d)⁻¹ * m⁻¹ ∈ M := M.mul_mem (hMn.conj_mem m hm (π d)) (M.inv_mem hm)
    have hc : π d * m * (π d)⁻¹ * m⁻¹ = 1 := by
      have : π d * m * (π d)⁻¹ * m⁻¹ ∈ H'' ⊓ M := Subgroup.mem_inf.mpr ⟨hc2, hc1⟩
      rw [hH''M] at this
      exact Subgroup.mem_bot.mp this
    have hmC : m ∈ M ⊓ Subgroup.centralizer ({π d} : Set (L ⧸ R₁)) := by
      refine Subgroup.mem_inf.mpr ⟨hm, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' : π d * m * (π d)⁻¹ = m := by
        calc π d * m * (π d)⁻¹ = π d * m * (π d)⁻¹ * m⁻¹ * m := by group
          _ = m := by rw [hc, one_mul]
      calc m * π d = π d * m * (π d)⁻¹ * π d := by rw [h']
        _ = π d * m := by group
    rw [hMC] at hmC
    show π x ∈ H''
    rw [hxe, Subgroup.mem_bot.mp hmC, mul_one]
    exact hh
  have hL₁top : L₁ ≠ ⊤ := by
    intro h
    apply hR₁lt.2
    intro r hr
    exact hL₁R r (h ▸ Subgroup.mem_top r) hr
  set L₀ := inSubgroup perfectResidual L₁ with hL₀def
  have hL₀L₁ : L₀ ≤ L₁ := Subgroup.map_subtype_le _
  have hL₀perf : Group.IsPerfect ↥L₀ := isPerfect_inSubgroup_perfectResidual' L₁
  have hLRperf : Group.IsPerfect (L ⧸ R) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective R)
  have hL₀dec : ∀ x : L, ∃ y ∈ L₀, ∃ r ∈ R, x = y * r := by
    set φ : ↥L₁ →* L ⧸ R := (QuotientGroup.mk' R).comp L₁.subtype with hφdef
    have hφs : Function.Surjective φ := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
      obtain ⟨y, hy, r, hr, rfl⟩ := hL₁dec x
      refine ⟨⟨y, hy⟩, ?_⟩
      show QuotientGroup.mk' R y = QuotientGroup.mk' R (y * r)
      rw [map_mul, show QuotientGroup.mk' R r = 1 from (QuotientGroup.eq_one_iff r).mpr hr,
        mul_one]
    obtain ⟨m, hm, -⟩ := (perfect_residual_characterization (G := ↥L₁)).1
    have hmapP : (perfectResidual ↥L₁).map φ = ⊤ := by
      haveI := hLRperf
      rw [hm, map_derivedSeries_eq hφs, Group.IsPerfect.derivedSeries_eq_top]
    intro x
    have hx : QuotientGroup.mk' R x ∈ (perfectResidual ↥L₁).map φ := by
      rw [hmapP]
      exact Subgroup.mem_top _
    obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hx
    refine ⟨y, Subgroup.mem_map_of_mem L₁.subtype hyP, (y : L)⁻¹ * x, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff ((y : L)⁻¹ * x)]
    show QuotientGroup.mk' R ((y : L)⁻¹ * x) = 1
    have hyx' : QuotientGroup.mk' R (y : L) = QuotientGroup.mk' R x := hyx
    rw [map_mul, map_inv, hyx', inv_mul_cancel]
  have hL₀decL₁ : ∀ x ∈ L₁, ∃ y ∈ inSubgroup perfectResidual L₁, ∃ r ∈ R, x = y * r :=
    fun x _ => hL₀dec x
  have hdL₀ : d ∈ L₀ := mem_of_odd_orderOf hR2 hL₀decL₁ hdL₁ (by rw [hd]; decide)
  obtain ⟨S, hdS, hSC⟩ := hd3
  have hSL₀ : (S : Subgroup L) ≤ L₀ := by
    intro s hs
    apply mem_of_odd_orderOf hR2 hL₀decL₁ (hCL₁ (hSC hs))
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have hdvd : orderOf s ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hj]
    exact Odd.pow (by decide)
  have hKL₀ : K ≤ L₀ := Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKperf (hKC.trans hCL₁)
  have hzL₀ : z ∈ L₀ := hKL₀ hzK
  have hcardL₀ : Nat.card ↥L₀ < n := by
    rw [← hn]
    calc Nat.card ↥L₀ ≤ Nat.card ↥L₁ := Subgroup.card_le_of_le hL₀L₁
      _ < Nat.card L := lt_of_le_of_ne (Subgroup.card_le_card_group L₁)
          (fun h => hL₁top ((Subgroup.card_eq_iff_eq_top L₁).mp h))
  set ψ : ↥L₀ →* L ⧸ R := (QuotientGroup.mk' R).comp L₀.subtype with hψdef
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    obtain ⟨y, hy, r, hr, rfl⟩ := hL₀dec x
    refine ⟨⟨y, hy⟩, ?_⟩
    show QuotientGroup.mk' R y = QuotientGroup.mk' R (y * r)
    rw [map_mul, show QuotientGroup.mk' R r = 1 from (QuotientGroup.eq_one_iff r).mpr hr,
      mul_one]
  have hψker : ψ.ker = R.subgroupOf L₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' R (x : L) = 1 ↔ (x : L) ∈ R
    exact QuotientGroup.eq_one_iff _
  have hψker2 : IsPGroup 2 ↥ψ.ker := by
    rw [hψker]
    exact hR2.comap_subtype
  have hO₂R : ∀ x ∈ CFSG.pCore 2 ↥L₀, (x : L) ∈ R := by
    intro x hx
    have hmap := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker ψ hψs hψker2
    have hbot : CFSG.pCore 2 (L ⧸ R) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
    have : ψ x ∈ CFSG.pCore 2 (L ⧸ R) := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem ψ hx
    rw [hbot] at this
    have hx' : x ∈ ψ.ker := Subgroup.mem_bot.mp this
    rw [hψker] at hx'
    exact Subgroup.mem_subgroupOf.mp hx'
  have hJ₀ : Nonempty (↥L₀ ⧸ CFSG.pCore 2 ↥L₀ ≃* J2) := by
    obtain ⟨e₁⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker ψ hψs hψker2
    obtain ⟨e⟩ := hJ
    have hbot : CFSG.pCore 2 (L ⧸ R) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
    exact ⟨e₁.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot.trans e))⟩
  set d₀ : ↥L₀ := ⟨d, hdL₀⟩ with hd₀def
  have hd₀ : orderOf d₀ = 3 := by
    rw [hd₀def, Subgroup.orderOf_mk]
    exact hd
  have hd3₀ : ∃ S₀ : Sylow 3 ↥L₀, d₀ ∈ (S₀ : Subgroup ↥L₀) ∧
      (S₀ : Subgroup ↥L₀) ≤ Subgroup.centralizer {d₀} := by
    refine ⟨S.subtype hSL₀, ?_, ?_⟩
    · rw [Sylow.coe_subtype]
      exact Subgroup.mem_subgroupOf.mpr hdS
    · rw [Sylow.coe_subtype]
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (hSC (Subgroup.mem_subgroupOf.mp hs))
      simpa using this
  have hK₀ : CFSG.pCore 2 ↥L₀ ⊓ inSubgroup perfectResidual
      (Subgroup.centralizer ({d₀} : Set ↥L₀)) ≠ ⊥ := by
    intro hbot
    set z₀ : ↥L₀ := ⟨z, hzL₀⟩ with hz₀def
    have hz₀O : z₀ ∈ CFSG.pCore 2 ↥L₀ := by
      have hn' : (R₁.subgroupOf L₀).Normal := hR₁n.subgroupOf L₀
      have h2 : IsPGroup 2 ↥(R₁.subgroupOf L₀) := hR₁2.comap_subtype
      exact le_sSup (s := {K' : Subgroup ↥L₀ | K'.Normal ∧ IsPGroup 2 K'}) ⟨hn', h2⟩
        (Subgroup.mem_subgroupOf.mpr hzR₁)
    have hz₀K : z₀ ∈ inSubgroup perfectResidual (Subgroup.centralizer ({d₀} : Set ↥L₀)) := by
      have hKsub : Group.IsPerfect ↥(K.subgroupOf L₀) := isPerfect_subgroupOf' hKL₀ hKperf
      have hKsubC : K.subgroupOf L₀ ≤ Subgroup.centralizer ({d₀} : Set ↥L₀) := by
        intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        have := Subgroup.mem_centralizer_singleton_iff.mp (hKC (Subgroup.mem_subgroupOf.mp hk))
        simpa using this
      exact Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKsub hKsubC
        (Subgroup.mem_subgroupOf.mpr hzK)
    have hmem : z₀ ∈ (⊥ : Subgroup ↥L₀) := hbot ▸ Subgroup.mem_inf.mpr ⟨hz₀O, hz₀K⟩
    exact hz1 (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
  have key := ih (Nat.card ↥L₀) hcardL₀ ↥L₀ rfl hL₀perf hJ₀ d₀ hd₀ hd3₀ hK₀
  have hle : Nat.card ↥(CFSG.pCore 2 ↥L₀ ⊓ Subgroup.centralizer ({d₀} : Set ↥L₀)) ≤
      Nat.card ↥W := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥L₀) : L), Subgroup.mem_inf.mpr ⟨hO₂R _ (Subgroup.mem_inf.mp x.2).1, ?_⟩⟩)
      ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
      have := congrArg Subtype.val this
      simpa using this
    · intro x y hxy
      have h' := congrArg Subtype.val hxy
      simp only at h'
      exact Subtype.ext (Subtype.ext h')
  omega

theorem four_le_card_pCore_inf_centralizer (hfix : KJFix) (hsplit : KJSplit)
    (hcover : KJCover) {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hJ : Nonempty (L ⧸ CFSG.pCore 2 L ≃* J2)) {d : L} (hd : orderOf d = 3)
    (hd3 : ∃ S : Sylow 3 L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d})
    (hK : CFSG.pCore 2 L ⊓ inSubgroup perfectResidual (Subgroup.centralizer ({d} : Set L)) ≠ ⊥) :
    4 ≤ Nat.card ↥(CFSG.pCore 2 L ⊓ Subgroup.centralizer ({d} : Set L)) :=
  four_le_aux hfix hsplit hcover (Nat.card L) L rfl hperf hJ d hd hd3 hK

theorem J2Config.four_le_card (hfix : KJFix) (hsplit : KJSplit) (hcover : KJCover)
    {G : Type} [Group G] [Finite G] {L LB : Subgroup G} {d : G} (h : J2Config L d LB)
    (hU : CFSG.Open.pCoreOf 2 LB ≠ ⊥) :
    4 ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  classical
  set d' : ↥L := ⟨d, h.mem_d⟩ with hd'def
  have hd' : orderOf d' = 3 := by
    rw [hd'def, Subgroup.orderOf_mk]
    exact h.orderOf_d
  have hLBL : LB ≤ L := by
    rw [h.lB_eq]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hLBC : LB ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [h.lB_eq]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hLBperf : Group.IsPerfect ↥LB := by
    rw [h.lB_eq]
    exact isPerfect_inSubgroup_perfectResidual' _
  have hK : CFSG.pCore 2 ↥L ⊓ inSubgroup perfectResidual
      (Subgroup.centralizer ({d'} : Set ↥L)) ≠ ⊥ := by
    obtain ⟨u, hu, hu1⟩ := (Subgroup.bot_or_exists_ne_one (CFSG.Open.pCoreOf 2 LB)).resolve_left hU
    have huL : u ∈ CFSG.Open.pCoreOf 2 L := h.pCoreOf_le hu
    obtain ⟨u', hu'P, hu'u⟩ := Subgroup.mem_map.mp huL
    have huLB : u ∈ LB := (Subgroup.map_subtype_le _) hu
    have hsub : Group.IsPerfect ↥(LB.subgroupOf L) := isPerfect_subgroupOf' hLBL hLBperf
    have hsubC : LB.subgroupOf L ≤ Subgroup.centralizer ({d'} : Set ↥L) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLBC (Subgroup.mem_subgroupOf.mp hx))
      simpa using this
    have hu'LB : u' ∈ LB.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      have : (u' : G) = u := hu'u
      rw [this]
      exact huLB
    have hu'K := Sec6.le_inSubgroup_perfectResidual_of_isPerfect hsub hsubC hu'LB
    intro hbot
    have hmem : u' ∈ (⊥ : Subgroup ↥L) := hbot ▸ Subgroup.mem_inf.mpr ⟨hu'P, hu'K⟩
    apply hu1
    have : (u' : G) = u := hu'u
    rw [← this, Subgroup.mem_bot.mp hmem]
    rfl
  have key := four_le_card_pCore_inf_centralizer hfix hsplit hcover h.perfect h.j2 hd'
    h.threeCentral hK
  refine key.trans (Nat.card_le_card_of_injective
    (fun x => ⟨((x : ↥L) : G), Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_map_of_mem L.subtype (Subgroup.mem_inf.mp x.2).1, ?_⟩⟩) ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
    have := congrArg Subtype.val this
    simpa using this
  · intro x y hxy
    have h' := congrArg Subtype.val hxy
    simp only at h'
    exact Subtype.ext (Subtype.ext h')

end CFSG.RankThree.PartTwo.J2Residue
