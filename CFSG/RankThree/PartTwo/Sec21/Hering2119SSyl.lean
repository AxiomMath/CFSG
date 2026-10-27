module

public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJCases
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SVec
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SRank4
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

section Rank

variable {G : Type} [Group G] [Finite G]

theorem card_le_27_of_normalizes (hloc : localRank 3 G = 3) {T E : Subgroup G} (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) : Nat.card E ≤ 27 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have h := CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ.pRank_le_localRank_of_le_normalizer hp hT hT2
    (le_refl (Subgroup.normalizer (T : Set G)))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    at h
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hEp
  have hk3 : k ≤ 3 := by
    have := CFSG.SectionRank.le_pRank hp.one_lt hET hE hk
    rw [hloc] at h
    omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num


omit [Finite G] in
theorem IsElem3.toIsElemAbelian {D : Subgroup G} (h : IsElem3 D) : CFSG.Open.IsElemAbelian 3 D :=
  ⟨⟨⟨fun a b => Subtype.ext (h.comm a a.2 b b.2)⟩⟩, h.pow3⟩

theorem mem_normalizer_zpowers_of_mul_eq {x τ : G} (h : x * τ = τ * x) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers τ : Set G) := by
  have hxτ : Commute x τ := h
  have hx' : ∀ k : ℤ, x * τ ^ k * x⁻¹ = τ ^ k := fun k => by
    rw [(Commute.zpow_right hxτ k).eq]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [hx']
    exact Subgroup.zpow_mem_zpowers _ k
  · intro hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : g = τ ^ k := by
      have h1 : x * g * x⁻¹ = τ ^ k := hk.symm
      calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
        _ = x⁻¹ * τ ^ k * x := by rw [h1]
        _ = τ ^ k := by
          have := hx' k
          calc x⁻¹ * τ ^ k * x = x⁻¹ * (x * τ ^ k * x⁻¹) * x := by rw [this]
            _ = τ ^ k := by group
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ k


theorem odd_card_centralizer (hloc : localRank 3 G = 3) {D : Subgroup G} (hD : IsElem3 D)
    (hD81 : Nat.card D = 81) : Odd (Nat.card (Subgroup.centralizer (D : Set G))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (D : Set G)) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.centralizer (D : Set G))) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hτK : (τ : G) ∈ Subgroup.centralizer (D : Set G) := τ.2
  have hτ2 : (τ : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one τ
    rw [hτ] at this
    simpa using congrArg Subtype.val this
  have hτ1 : (τ : G) ≠ 1 := by
    intro h
    have : τ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hτ
    omega
  have hT2 : IsPGroup 2 (Subgroup.zpowers (τ : G)) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hτ2, one_zpow]
    rfl
  have hT0 : Subgroup.zpowers (τ : G) ≠ ⊥ := by
    intro h
    exact hτ1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (τ : G)))
  have hDN : D ≤ Subgroup.normalizer (Subgroup.zpowers (τ : G) : Set G) := fun x hx =>
    mem_normalizer_zpowers_of_mul_eq (Subgroup.mem_centralizer_iff.mp hτK x hx)
  have := card_le_27_of_normalizes hloc hT0 hT2 hD.toIsElemAbelian hDN
  omega


@[expose] def conjOn {S B : Subgroup G} (h : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B) :
    S →* MulAut B where
  toFun s :=
    { toFun := fun b => ⟨(s : G) * b * (s : G)⁻¹, h s s.2 b b.2⟩
      invFun := fun b => ⟨(s : G)⁻¹ * b * s, by
        have := h _ (S.inv_mem s.2) b b.2
        rwa [inv_inv] at this⟩
      left_inv := fun b => Subtype.ext (by dsimp only; group)
      right_inv := fun b => Subtype.ext (by dsimp only; group)
      map_mul' := fun b b' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  map_one' := MulEquiv.ext fun b => Subtype.ext (by
    show ((1 : S) : G) * b * ((1 : S) : G)⁻¹ = b
    rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
  map_mul' s s' := MulEquiv.ext fun b => Subtype.ext (by
    show ((s * s' : S) : G) * b * ((s * s' : S) : G)⁻¹ = s * (s' * b * (s' : G)⁻¹) * (s : G)⁻¹
    rw [Subgroup.coe_mul]
    group)

theorem exists_invariant_sylow {S R : Subgroup G} (hS : IsPGroup 2 S) (hR : Odd (Nat.card R))
    (hSR : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) :
    ∃ P : Subgroup G, P ≤ R ∧ IsPGroup 3 P ∧
      Nat.card P = 3 ^ (Nat.card R).factorization 3 ∧ ∀ s ∈ S, ∀ x ∈ P, s * x * s⁻¹ ∈ P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulAction S (Sylow 3 R) := MulAction.compHom _ (conjOn hSR)
  have h2 : ¬ 2 ∣ Nat.card (Sylow 3 R) := by
    obtain ⟨P⟩ : Nonempty (Sylow 3 R) := inferInstance
    intro h
    have h1 := (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card (P : Subgroup R))
    exact (Nat.not_even_iff_odd.2 hR) (even_iff_two_dvd.2 (h.trans h1))
  obtain ⟨P, hP⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 R) h2
  refine ⟨(P : Subgroup R).map R.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map R.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective R.subtype_injective, Sylow.card_eq_multiplicity]
  · rintro s hs _ ⟨y, hy, rfl⟩
    have hfix : (⟨s, hs⟩ : S) • P = P := hP ⟨s, hs⟩
    have hmem : conjOn hSR ⟨s, hs⟩ y ∈ (((⟨s, hs⟩ : S) • P : Sylow 3 R) : Subgroup R) := by
      show conjOn hSR ⟨s, hs⟩ y ∈ conjOn hSR ⟨s, hs⟩ • (P : Subgroup R)
      exact Subgroup.smul_mem_pointwise_smul y _ _ hy
    rw [hfix] at hmem
    exact ⟨_, hmem, rfl⟩


theorem inverts_of_fixedPointFree {S : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S) (hfix : ∀ s ∈ S, t * s * t⁻¹ = s → s = 1) :
    ∀ s ∈ S, t * s * t⁻¹ = s⁻¹ := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let f : S → S := fun s => ⟨(s : G)⁻¹ * (t * s * t⁻¹), S.mul_mem (S.inv_mem s.2) (htS s s.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (a : G)⁻¹ * (t * a * t⁻¹) = (b : G)⁻¹ * (t * b * t⁻¹) := congrArg Subtype.val hab
    have h2 : t * ((b : G) * (a : G)⁻¹) * t⁻¹ = (b : G) * (a : G)⁻¹ := by
      calc t * ((b : G) * (a : G)⁻¹) * t⁻¹
          = (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ := by group
        _ = (b : G) * (a : G)⁻¹ := by
          have : (t * b * t⁻¹) = (b : G) * ((a : G)⁻¹ * (t * a * t⁻¹)) := by
            rw [h1]; group
          rw [this]; group
    have h3 := hfix _ (S.mul_mem b.2 (S.inv_mem a.2)) h2
    exact Subtype.ext (by
      have : (b : G) * (a : G)⁻¹ = 1 := h3
      exact (mul_inv_eq_one.mp this).symm)
  have hs : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  intro s hsS
  obtain ⟨a, ha⟩ := hs ⟨s, hsS⟩
  have h1 : (a : G)⁻¹ * (t * a * t⁻¹) = s := congrArg Subtype.val ha
  rw [← h1, hti]
  have hL : t * ((a : G)⁻¹ * (t * a * t)) * t = t * (a : G)⁻¹ * t * a * (t * t) := by group
  have hR : ((a : G)⁻¹ * (t * a * t))⁻¹ = t⁻¹ * (a : G)⁻¹ * t⁻¹ * a := by group
  rw [hL, hR, hti, ht2, mul_one]


theorem inf_centralizer_eq_bot (hloc : localRank 3 G = 3) {D T : Subgroup G} (hD : IsElem3 D)
    (hD81 : Nat.card D = 81) (hT2 : IsPGroup 2 T) :
    T ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
  have hodd := odd_card_centralizer hloc hD hD81
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)

theorem eq_of_same_action (hloc : localRank 3 G = 3) {D T : Subgroup G} (hD : IsElem3 D)
    (hD81 : Nat.card D = 81) (hT2 : IsPGroup 2 T) {g h : G} (hg : g ∈ T) (hh : h ∈ T)
    (hgh : ∀ x ∈ D, g * x * g⁻¹ = h * x * h⁻¹) : g = h := by
  have hmem : g⁻¹ * h ∈ T ⊓ Subgroup.centralizer (D : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem hg) hh, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have h1 := hgh x hx
    calc x * (g⁻¹ * h) = g⁻¹ * (g * x * g⁻¹) * h := by group
      _ = g⁻¹ * (h * x * h⁻¹) * h := by rw [h1]
      _ = (g⁻¹ * h) * x := by group
  rw [inf_centralizer_eq_bot hloc hD hD81 hT2, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem


theorem isPGroup_zpowers_of_pow_three' {T : Type*} [Group T] {t : T} (ht : t ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers t) := by
  intro g
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, ht, one_zpow]
  rfl

theorem exists_conj_mem_sylow {K S : Subgroup G} (hSK : S ≤ K)
    (hS : Nat.card S = 3 ^ (Nat.card K).factorization 3) {y : G} (hyK : y ∈ K) (hy3 : y ^ 3 = 1) :
    ∃ k ∈ K, k * y * k⁻¹ ∈ S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS' : Nat.card (S.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]; exact hS
  let P : Sylow 3 K := Sylow.ofCard (S.subgroupOf K) hS'
  let yK : K := ⟨y, hyK⟩
  have hyK3 : yK ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  obtain ⟨P₂, hP₂⟩ := (isPGroup_zpowers_of_pow_three' hyK3).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P P₂
  have hmem : yK ∈ (P₂ : Subgroup K) := hP₂ (Subgroup.mem_zpowers yK)
  have hmem' : yK ∈ (MulAut.conj g • (P : Subgroup K) : Subgroup K) := by
    rw [← Sylow.coe_subgroup_smul, hg]; exact hmem
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem'
  refine ⟨(g⁻¹ : K), (g⁻¹ : K).2, ?_⟩
  have h1 : (MulAut.conj g)⁻¹ • yK ∈ (P : Subgroup K) := hmem'
  have h2 : (MulAut.conj g)⁻¹ • yK = g⁻¹ * yK * g := by
    rw [MulAut.smul_def, ← MulAut.conj_symm_apply]; simp
  rw [h2] at h1
  have h3 : g⁻¹ * yK * g ∈ S.subgroupOf K := h1
  rw [Subgroup.mem_subgroupOf] at h3
  simpa using h3


theorem exists_pow_order_three {z : G} (hz : IsPGroup 3 (Subgroup.zpowers z)) (hz1 : z ≠ 1) :
    ∃ w ∈ Subgroup.zpowers z, w ≠ 1 ∧ w ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Nat.card (Subgroup.zpowers z) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hz
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : Nat.card (Subgroup.zpowers z) = 1 := by simpa using hn
      rw [Subgroup.card_eq_one] at this
      exact hz1 (Subgroup.mem_bot.mp (this ▸ Subgroup.mem_zpowers z))
    rw [hn]
    exact dvd_pow_self 3 hn0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  refine ⟨(w : G), w.2, ?_, ?_⟩
  · intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at hw
    omega
  · have := pow_orderOf_eq_one w
    rw [hw] at this
    simpa using congrArg Subtype.val this


theorem exists_abelian_invariant_sylow (hloc : localRank 3 G = 3) {D T : Subgroup G}
    (hD : IsElem3 D) (hD81 : Nat.card D = 81) (hT2 : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (D : Set G)) {t : G} (htT : t ∈ T)
    (ht : ∀ x ∈ D, t * x * t⁻¹ = x⁻¹)
    (hCt : ∀ z ∈ Subgroup.centralizer (D : Set G), t * z * t⁻¹ = z → z ^ 3 = 1 → z = 1) :
    ∃ S : Subgroup G, S ≤ Subgroup.centralizer (D : Set G) ∧ IsPGroup 3 S ∧
      Nat.card S = 3 ^ (Nat.card (Subgroup.centralizer (D : Set G))).factorization 3 ∧
      (∀ s ∈ T, ∀ x ∈ S, s * x * s⁻¹ ∈ S) ∧ (∀ x ∈ S, t * x * t⁻¹ = x⁻¹) ∧
      (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧ D ≤ S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.centralizer (D : Set G) with hKdef
  have hKodd : Odd (Nat.card K) := odd_card_centralizer hloc hD hD81
  have hDK : D ≤ K := fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz => hD.comm z hz x hx
  have hTK : ∀ s ∈ T, ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
    intro s hs k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hsx : s⁻¹ * x * s ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem hs)) x).mp hx
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hk _ hsx
    calc x * (s * k * s⁻¹) = s * ((s⁻¹ * x * s) * k) * s⁻¹ := by group
      _ = s * (k * (s⁻¹ * x * s)) * s⁻¹ := by rw [this]
      _ = (s * k * s⁻¹) * x := by group
  obtain ⟨S, hSK, hS3, hScard, hSinv⟩ := exists_invariant_sylow hT2 hKodd hTK
  have htt : t * t = 1 := by
    refine eq_of_same_action hloc hD hD81 hT2 (T.mul_mem htT htT) T.one_mem (fun x hx => ?_)
    have h1 : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [ht x hx, ht _ (D.inv_mem hx), inv_inv]
    calc t * t * x * (t * t)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ := by group
      _ = x := h1
      _ = 1 * x * 1⁻¹ := by group
  have hfix : ∀ s ∈ S, t * s * t⁻¹ = s → s = 1 := by
    intro z hz hzfix
    by_contra hz1
    obtain ⟨w, hw, hw1, hw3⟩ := exists_pow_order_three (hS3.to_le (Subgroup.zpowers_le.mpr hz)) hz1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hwS : z ^ k ∈ S := S.zpow_mem hz k
    apply hw1
    refine hCt _ (hSK hwS) ?_ hw3
    rw [← conj_zpow, hzfix]
  have hSinvert : ∀ s ∈ S, t * s * t⁻¹ = s⁻¹ :=
    inverts_of_fixedPointFree htt (fun s hs => hSinv t htT s hs) hfix
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    have h1 := hSinvert (x * y) (S.mul_mem hx hy)
    have h2 : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [h2, hSinvert x hx, hSinvert y hy, mul_inv_rev] at h1
    have h3 := congrArg (fun z => z⁻¹) h1
    simpa [mul_inv_rev] using h3.symm
  have hDS : D ≤ S := by
    have hD3 : IsPGroup 3 D := fun g => ⟨1, Subtype.ext (by simpa using hD.pow3 g g.2)⟩
    have hxc : ∀ x ∈ D, ∀ g' ∈ K, x * g' * x⁻¹ = g' := fun x hx g' hg' => by
      have := Subgroup.mem_centralizer_iff.mp hg' x hx
      calc x * g' * x⁻¹ = (g' * x) * x⁻¹ := by rw [this]
        _ = g' := by group
    have hDN : D ≤ Subgroup.normalizer (S : Set G) := fun x hx => by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg; rw [hxc x hx g (hSK hg)]; exact hg
      · intro hg
        have h1 : x * g * x⁻¹ ∈ K := hSK hg
        have h2 : x⁻¹ * (x * g * x⁻¹) * x = x * g * x⁻¹ := by
          have := hxc x⁻¹ (D.inv_mem hx) _ h1
          simpa using this
        have h3 : g = x * g * x⁻¹ := by
          calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
            _ = x * g * x⁻¹ := h2
        rw [h3]; exact hg
    have hR3 : IsPGroup 3 (S ⊔ D : Subgroup G) := IsPGroup.to_sup_of_normal_left' hS3 hD3 hDN
    have hle : Nat.card (S ⊔ D : Subgroup G) ≤ 3 ^ (Nat.card K).factorization 3 :=
      Item2119End6Proof.card_le_three_pow_of_isPGroup (sup_le hSK hDK) hR3
    have heq : S ⊔ D = S :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hScard]; exact hle)).symm
    exact heq ▸ le_sup_right
  exact ⟨S, hSK, hS3, hScard, hSinv, hSinvert, hSc, hDS⟩



theorem false_of_omega (hloc : localRank 3 G = 3) {T Ω : Subgroup G} (hΩ : IsElem3 Ω)
    (hT2 : IsPGroup 2 T) (hTΩ : ∀ s ∈ T, ∀ x ∈ Ω, s * x * s⁻¹ ∈ Ω)
    (hΩcard : 243 ≤ Nat.card Ω) {a b c t : G} (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T)
    (htT : t ∈ T) (hinv : ∀ x ∈ Ω, t * x * t⁻¹ = x⁻¹)
    (hat : a * a = t) (hbt : b * b = t) (hct : c * c = t)
    (hab : a * b = t * (b * a)) (hac : a * c = c * a) (hbc : b * c = c * b) : False := by
  classical
  haveI : Fact (IsElem3 Ω) := ⟨hΩ⟩
  haveI : Finite (Vec Ω) := inferInstanceAs (Finite (Additive Ω))
  haveI : Module.Finite F3 (Vec Ω) := Module.Finite.of_finite
  have hTN : T ≤ Subgroup.normalizer (Ω : Set G) := fun s hs => by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hTΩ s hs g hg, fun hg => ?_⟩
    have h1 := hTΩ s⁻¹ (T.inv_mem hs) _ hg
    have h2 : s⁻¹ * (s * g * s⁻¹) * s⁻¹⁻¹ = g := by group
    rwa [h2] at h1
  let ρ : T →* Module.End F3 (Vec Ω) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp
      ((conjLinHom Ω).comp (Subgroup.inclusion hTN))
  have hρ : ∀ (g : T) (v : Vec Ω), ((Vec.toD (ρ g v) : Ω) : G) =
      (g : G) * (Vec.toD v : Ω) * (g : G)⁻¹ := fun g v => rfl
  let a' : T := ⟨a, haT⟩
  let b' : T := ⟨b, hbT⟩
  let c' : T := ⟨c, hcT⟩
  let t' : T := ⟨t, htT⟩
  have hρt : ρ t' = -1 := by
    apply LinearMap.ext
    intro v
    apply Vec.toD_injective
    apply Subtype.ext
    rw [hρ, LinearMap.neg_apply, Module.End.one_apply, Vec.toD_neg, Subgroup.coe_inv]
    exact hinv _ (Vec.toD v).2
  have hA : ρ a' * ρ a' = -1 := by
    rw [← map_mul, show a' * a' = t' from Subtype.ext hat, hρt]
  have hB : ρ b' * ρ b' = -1 := by
    rw [← map_mul, show b' * b' = t' from Subtype.ext hbt, hρt]
  have hC : ρ c' * ρ c' = -1 := by
    rw [← map_mul, show c' * c' = t' from Subtype.ext hct, hρt]
  have hAB : ρ a' * ρ b' = -(ρ b' * ρ a') := by
    rw [← map_mul, ← map_mul, show a' * b' = t' * (b' * a') from Subtype.ext hab, map_mul, hρt,
      neg_one_mul]
  have hAC : ρ a' * ρ c' = ρ c' * ρ a' := by
    rw [← map_mul, ← map_mul, show a' * c' = c' * a' from Subtype.ext hac]
  have hBC : ρ b' * ρ c' = ρ c' * ρ b' := by
    rw [← map_mul, ← map_mul, show b' * c' = c' * b' from Subtype.ext hbc]
  obtain ⟨h4, h2k⟩ := rank_four (ρ a') (ρ b') (ρ c') hA hB hC hAB hAC hBC
  set k := Module.finrank F3 (LinearMap.ker (ρ a' * ρ c' - 1)) with hk
  set r := Module.finrank F3 (Vec Ω) with hr
  have hcardV : Nat.card Ω = 3 ^ r := by
    have h := Module.natCard_eq_pow_finrank (K := F3) (V := Vec Ω)
    rw [Nat.card_zmod] at h
    rw [← h]
    exact Nat.card_congr (Additive.ofMul)
  have hr5 : 5 ≤ r := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ r ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk4 : 4 ≤ k := by omega
  let E : Subgroup G := Ω ⊓ Subgroup.centralizer ({a * c} : Set G)
  have hEΩ : IsElem3 E := ⟨fun x hx y hy => hΩ.comm x hx.1 y hy.1, fun x hx => hΩ.pow3 x hx.1⟩
  have hkerE : ∀ v : Vec Ω, v ∈ LinearMap.ker (ρ a' * ρ c' - 1) ↔
      ((Vec.toD v : Ω) : G) ∈ Subgroup.centralizer ({a * c} : Set G) := by
    intro v
    rw [LinearMap.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg (fun w => ((Vec.toD w : Ω) : G)) h
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, sub_eq_add_neg,
        Vec.toD_add, Vec.toD_neg, Subgroup.coe_mul, Subgroup.coe_inv, Vec.toD_zero,
        OneMemClass.coe_one] at h1
      change a * (c * (Vec.toD v : Ω) * c⁻¹) * a⁻¹ * ((Vec.toD v : Ω) : G)⁻¹ = 1 at h1
      have h2 := mul_inv_eq_one.mp h1
      calc ((Vec.toD v : Ω) : G) * (a * c)
          = (a * (c * (Vec.toD v : Ω) * c⁻¹) * a⁻¹) * (a * c) := by rw [h2]
        _ = (a * c) * (Vec.toD v : Ω) := by group
    · intro h
      apply Vec.toD_injective
      apply Subtype.ext
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, sub_eq_add_neg,
        Vec.toD_add, Vec.toD_neg, Subgroup.coe_mul, Subgroup.coe_inv, Vec.toD_zero,
        OneMemClass.coe_one]
      change a * (c * (Vec.toD v : Ω) * c⁻¹) * a⁻¹ * ((Vec.toD v : Ω) : G)⁻¹ = 1
      have h2 : a * (c * (Vec.toD v : Ω) * c⁻¹) * a⁻¹ = (Vec.toD v : Ω) := by
        calc a * (c * (Vec.toD v : Ω) * c⁻¹) * a⁻¹
            = ((a * c) * (Vec.toD v : Ω)) * (a * c)⁻¹ := by group
          _ = (((Vec.toD v : Ω) : G) * (a * c)) * (a * c)⁻¹ := by rw [h]
          _ = (Vec.toD v : Ω) := by group
      rw [h2]
      group
  have hEcard : Nat.card E = 3 ^ k := by
    have h1 : Nat.card E = Nat.card (LinearMap.ker (ρ a' * ρ c' - 1)) := Nat.card_congr
      { toFun := fun x => ⟨Vec.ofD ⟨x.1, x.2.1⟩, (hkerE _).mpr x.2.2⟩
        invFun := fun v => ⟨((Vec.toD v.1 : Ω) : G), (Vec.toD v.1).2, (hkerE _).mp v.2⟩
        left_inv := fun x => rfl
        right_inv := fun v => rfl }
    rw [h1, Module.natCard_eq_pow_finrank (K := F3), Nat.card_zmod]
  have hac1 : a * c ≠ 1 := by
    intro h1
    have htop : LinearMap.ker (ρ a' * ρ c' - 1) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [hkerE, h1, Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul]
    have : k = r := by rw [hk, htop, finrank_top]
    omega
  have hT0 : Subgroup.zpowers (a * c) ≠ ⊥ := fun h => hac1 (Subgroup.zpowers_eq_bot.mp h)
  have hT2' : IsPGroup 2 (Subgroup.zpowers (a * c)) :=
    hT2.to_le (Subgroup.zpowers_le.mpr (T.mul_mem haT hcT))
  have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers (a * c) : Set G) := fun x hx =>
    mem_normalizer_zpowers_of_mul_eq (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
  have h27 := card_le_27_of_normalizes hloc hT0 hT2' hEΩ.toIsElemAbelian hEN
  rw [hEcard] at h27
  have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
  omega


theorem false_of_triple (hloc : localRank 3 G = 3) {D T : Subgroup G} (hD : IsElem3 D)
    (hD81 : Nat.card D = 81) (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (D : Set G))
    {a b c t y : G} (haT : a ∈ T) (hbT : b ∈ T) (hcT : c ∈ T) (htT : t ∈ T)
    (ht : ∀ x ∈ D, t * x * t⁻¹ = x⁻¹)
    (ha : ∀ x ∈ D, a * (a * x * a⁻¹) * a⁻¹ = x⁻¹)
    (hb : ∀ x ∈ D, b * (b * x * b⁻¹) * b⁻¹ = x⁻¹)
    (hc : ∀ x ∈ D, c * (c * x * c⁻¹) * c⁻¹ = x⁻¹)
    (hab : ∀ x ∈ D, a * (b * x * b⁻¹) * a⁻¹ = (b * (a * x * a⁻¹) * b⁻¹)⁻¹)
    (hac : ∀ x ∈ D, a * (c * x * c⁻¹) * a⁻¹ = c * (a * x * a⁻¹) * c⁻¹)
    (hbc : ∀ x ∈ D, b * (c * x * c⁻¹) * b⁻¹ = c * (b * x * b⁻¹) * c⁻¹)
    (hCt : ∀ z ∈ Subgroup.centralizer (D : Set G), t * z * t⁻¹ = z → z ^ 3 = 1 → z = 1)
    (hyK : y ∈ Subgroup.centralizer (D : Set G)) (hyD : y ∉ D) (hy3 : y ^ 3 = 1) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSK, hS3, hScard, hSinv, hSinvert, hSc, hDS⟩ :=
    exists_abelian_invariant_sylow hloc hD hD81 hT2 hTN htT ht hCt
  obtain ⟨k, hkK, hkS⟩ := exists_conj_mem_sylow hSK hScard hyK hy3
  have hy'D : k * y * k⁻¹ ∉ D := by
    intro h
    apply hyD
    have h1 : (k * y * k⁻¹) * k = k * (k * y * k⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hkK _ h
    have h2 : k * y = k * (k * y * k⁻¹) := by
      calc k * y = (k * y * k⁻¹) * k := by group
        _ = k * (k * y * k⁻¹) := h1
    have : y = k * y * k⁻¹ := mul_left_cancel h2
    rw [this]; exact h
  have hy'3 : (k * y * k⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3]; group
  obtain ⟨Ω, hΩmem⟩ : ∃ Ω : Subgroup G, ∀ x, x ∈ Ω ↔ x ∈ S ∧ x ^ 3 = 1 :=
    ⟨{ carrier := {x | x ∈ S ∧ x ^ 3 = 1}
       mul_mem' := fun {x z} hx hz => ⟨S.mul_mem hx.1 hz.1, by
         rw [(show Commute x z from hSc x hx.1 z hz.1).mul_pow, hx.2, hz.2, mul_one]⟩
       one_mem' := ⟨S.one_mem, one_pow 3⟩
       inv_mem' := fun {x} hx => ⟨S.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ },
     fun x => Iff.rfl⟩
  have hΩ : IsElem3 Ω := ⟨fun x hx z hz => hSc x ((hΩmem x).mp hx).1 z ((hΩmem z).mp hz).1,
    fun x hx => ((hΩmem x).mp hx).2⟩
  have hDΩ : D ≤ Ω := fun x hx => (hΩmem x).mpr ⟨hDS hx, hD.pow3 x hx⟩
  have hy'Ω : k * y * k⁻¹ ∈ Ω := (hΩmem _).mpr ⟨hkS, hy'3⟩
  have hTΩ : ∀ s ∈ T, ∀ x ∈ Ω, s * x * s⁻¹ ∈ Ω := fun s hs x hx =>
    (hΩmem _).mpr ⟨hSinv s hs x ((hΩmem x).mp hx).1, by
      rw [conj_pow, ((hΩmem x).mp hx).2]; group⟩
  have hΩcard : 243 ≤ Nat.card Ω := by
    have hlt : D < Ω := lt_of_le_of_ne hDΩ (fun h => hy'D (h ▸ hy'Ω))
    have h1 := Subgroup.card_lt_of_lt hlt
    obtain ⟨r, hr⟩ := (IsPGroup.iff_card).mp (show IsPGroup 3 Ω from
      fun g => ⟨1, Subtype.ext (by simpa using hΩ.pow3 g g.2)⟩)
    rw [hD81, hr] at h1
    have hr5 : 5 ≤ r := by
      by_contra hlt5
      push Not at hlt5
      have : 3 ^ r ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hr]
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr5
  have hTD : ∀ s ∈ T, ∀ x ∈ D, s * x * s⁻¹ ∈ D := fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTN hs) x).mp hx
  have hinvΩ : ∀ x ∈ Ω, t * x * t⁻¹ = x⁻¹ := fun x hx => hSinvert x ((hΩmem x).mp hx).1
  have hat : a * a = t := eq_of_same_action hloc hD hD81 hT2 (T.mul_mem haT haT) htT
    (fun x hx => by
      calc a * a * x * (a * a)⁻¹ = a * (a * x * a⁻¹) * a⁻¹ := by group
        _ = x⁻¹ := ha x hx
        _ = t * x * t⁻¹ := (ht x hx).symm)
  have hbt : b * b = t := eq_of_same_action hloc hD hD81 hT2 (T.mul_mem hbT hbT) htT
    (fun x hx => by
      calc b * b * x * (b * b)⁻¹ = b * (b * x * b⁻¹) * b⁻¹ := by group
        _ = x⁻¹ := hb x hx
        _ = t * x * t⁻¹ := (ht x hx).symm)
  have hct : c * c = t := eq_of_same_action hloc hD hD81 hT2 (T.mul_mem hcT hcT) htT
    (fun x hx => by
      calc c * c * x * (c * c)⁻¹ = c * (c * x * c⁻¹) * c⁻¹ := by group
        _ = x⁻¹ := hc x hx
        _ = t * x * t⁻¹ := (ht x hx).symm)
  have hab' : a * b = t * (b * a) := eq_of_same_action hloc hD hD81 hT2 (T.mul_mem haT hbT)
    (T.mul_mem htT (T.mul_mem hbT haT)) (fun x hx => by
      have hz : b * (a * x * a⁻¹) * b⁻¹ ∈ D := hTD b hbT _ (hTD a haT x hx)
      calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
        _ = (b * (a * x * a⁻¹) * b⁻¹)⁻¹ := hab x hx
        _ = t * (b * (a * x * a⁻¹) * b⁻¹) * t⁻¹ := (ht _ hz).symm
        _ = t * (b * a) * x * (t * (b * a))⁻¹ := by group)
  have hac' : a * c = c * a := eq_of_same_action hloc hD hD81 hT2 (T.mul_mem haT hcT)
    (T.mul_mem hcT haT) (fun x hx => by
      calc a * c * x * (a * c)⁻¹ = a * (c * x * c⁻¹) * a⁻¹ := by group
        _ = c * (a * x * a⁻¹) * c⁻¹ := hac x hx
        _ = c * a * x * (c * a)⁻¹ := by group)
  have hbc' : b * c = c * b := eq_of_same_action hloc hD hD81 hT2 (T.mul_mem hbT hcT)
    (T.mul_mem hcT hbT) (fun x hx => by
      calc b * c * x * (b * c)⁻¹ = b * (c * x * c⁻¹) * b⁻¹ := by group
        _ = c * (b * x * b⁻¹) * c⁻¹ := hbc x hx
        _ = c * b * x * (c * b)⁻¹ := by group)
  exact false_of_omega hloc hΩ hT2 hTΩ hΩcard haT hbT hcT htT hinvΩ hat hbt hct hab' hac' hbc'

end Rank

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
