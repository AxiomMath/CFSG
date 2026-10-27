module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoFixedPointFree
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.StandardType.USixTwo

open scoped Pointwise

open CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.PCoreSection
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {K : Type} [Field K]

theorem exists_conj_eq_pow_of_index_eq_prime {M : Type*} [Group M] [Finite M]
    {N : Subgroup M} [N.Normal] {p : ℕ} [Fact p.Prime] (hN : N.index = p)
    (hcop : ¬ p ∣ Nat.card N) {x y : M} (hxN : x ∉ N) (hyN : y ∉ N)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) :
    ∃ (m : M) (k : ℕ), ¬ p ∣ k ∧ m * x ^ k * m⁻¹ = y := by
  have hx1 : x ≠ 1 := fun h => hxN (h ▸ N.one_mem)
  have hy1 : y ≠ 1 := fun h => hyN (h ▸ N.one_mem)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hMcard : Nat.card M = p * Nat.card N := by
    rw [← Subgroup.card_mul_index N, hN, mul_comm]
  have hXcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
  have hYcard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyord]
  have hXp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hYp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [hYcard, pow_one])
  have hXindex : (Subgroup.zpowers x).index = Nat.card N := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hXcard, hMcard] at h
    exact Nat.mul_left_cancel (Nat.Prime.pos (Fact.out : p.Prime)) h
  have hYindex : (Subgroup.zpowers y).index = Nat.card N := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers y)
    rw [hYcard, hMcard] at h
    exact Nat.mul_left_cancel (Nat.Prime.pos (Fact.out : p.Prime)) h
  have hindX : ¬ p ∣ (Subgroup.zpowers x).index := by rw [hXindex]; exact hcop
  have hindY : ¬ p ∣ (Subgroup.zpowers y).index := by rw [hYindex]; exact hcop
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M := M)
    (hXp.toSylow hindX) (hYp.toSylow hindY)
  have hset : MulAut.conj m • (Subgroup.zpowers x) = Subgroup.zpowers y := by
    have h1 : ((m • hXp.toSylow hindX : Sylow p M) : Subgroup M) =
        ((hYp.toSylow hindY : Sylow p M) : Subgroup M) := congrArg _ hm
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h1
    exact h1
  have hmem : (MulAut.conj m)⁻¹ • y ∈ Subgroup.zpowers x :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp (hset ▸ Subgroup.mem_zpowers y)
  have hmem' : (MulAut.conj m)⁻¹ • y ∈ Submonoid.powers x :=
    mem_powers_iff_mem_zpowers.mpr hmem
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff ((MulAut.conj m)⁻¹ • y) x).mp hmem'
  have hinv : (MulAut.conj m)⁻¹ = MulAut.conj m⁻¹ := (map_inv MulAut.conj m).symm
  have hsm : (MulAut.conj m)⁻¹ • y = m⁻¹ * y * m := by
    rw [MulAut.smul_def, hinv, MulAut.conj_apply]
    simp
  have hyx : m * x ^ k * m⁻¹ = y := by
    rw [hk, hsm]
    group
  refine ⟨m, k, ?_, hyx⟩
  intro hdvd
  obtain ⟨t, rfl⟩ := hdvd
  rw [pow_mul, hxp, one_pow, mul_one] at hyx
  exact hy1 (by simpa using hyx.symm)

theorem exists_conj_eq_or_inv_of_relIndex_eq_three {L : Type*} [Group L] [Finite L]
    {N Q : Subgroup L} [N.Normal] (hNQ : N ≤ Q) (hQ : N.relIndex Q = 3)
    (hcop : ¬ 3 ∣ Nat.card N) {x y : L} (hxQ : x ∈ Q) (hyQ : y ∈ Q) (hxN : x ∉ N)
    (hyN : y ∉ N) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) :
    ∃ m ∈ Q, m * x * m⁻¹ = y ∨ m * x⁻¹ * m⁻¹ = y := by
  have hN'card : Nat.card ↥(N.subgroupOf Q) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNQ).toEquiv
  have hcop' : ¬ 3 ∣ Nat.card ↥(N.subgroupOf Q) := by rw [hN'card]; exact hcop
  have hQ' : (N.subgroupOf Q).index = 3 := hQ
  obtain ⟨m', k, hk, hm⟩ := exists_conj_eq_pow_of_index_eq_prime (M := ↥Q)
    (N := N.subgroupOf Q) (p := 3) hQ' hcop'
    (x := ⟨x, hxQ⟩) (y := ⟨y, hyQ⟩)
    (fun h => hxN (Subgroup.mem_subgroupOf.mp h))
    (fun h => hyN (Subgroup.mem_subgroupOf.mp h))
    (by apply Subtype.ext; simpa using hx3) (by apply Subtype.ext; simpa using hy3)
  have hmL : (m' : L) * x ^ k * (m' : L)⁻¹ = y := by
    have h := congrArg (fun z : ↥Q => (z : L)) hm
    simpa using h
  have h3 : k % 3 = 1 ∨ k % 3 = 2 := by
    have hlt := Nat.mod_lt k (by norm_num : 0 < 3)
    have hne : k % 3 ≠ 0 := fun h => hk (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have hxkr : x ^ k = x ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3]
    rw [pow_add, pow_mul, hx3, one_pow, one_mul]
  have hmain : (m' : L) * x * (m' : L)⁻¹ = y ∨ (m' : L) * x⁻¹ * (m' : L)⁻¹ = y := by
    rw [hxkr] at hmL
    rcases h3 with h | h
    · left
      rw [h, pow_one] at hmL
      exact hmL
    · right
      have hx2 : x ^ 2 = x⁻¹ := by
        have h2 : x ^ 2 * x = 1 := by rw [← pow_succ]; exact hx3
        exact mul_eq_one_iff_eq_inv.mp h2
      rw [h, hx2] at hmL
      exact hmL
  exact ⟨(m' : L), m'.2, hmain⟩

theorem exists_conj_eq_or_inv_of_mem_normal_of_not_dvd_three {L : Type*} [Group L] [Finite L]
    {N : Subgroup L} [N.Normal] (hcop : ¬ 3 ∣ Nat.card N) {a g : L}
    (ha3 : a ^ 3 = 1) (hg3 : g ^ 3 = 1) (haN : a ∉ N) (hgN : g ∉ N)
    (hsame : a * g⁻¹ ∈ N) :
    ∃ m : L, m * a * m⁻¹ = g ∨ m * a⁻¹ * m⁻¹ = g := by
  have haord : orderOf a = 3 :=
    orderOf_eq_prime ha3 (fun h => haN (h ▸ N.one_mem))
  have hcard3 : Nat.card ↥(Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, haord]
  have hdisj : Subgroup.zpowers a ⊓ N = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ N) ∣ 3 := by
      rw [← hcard3]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h1
    · rwa [Subgroup.card_eq_one] at h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ N = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hcard3])
      have hmem : a ∈ Subgroup.zpowers a ⊓ N := by
        rw [heq]; exact Subgroup.mem_zpowers a
      exact haN (Subgroup.mem_inf.mp hmem).2
  have hrel : N.relIndex (N ⊔ Subgroup.zpowers a) = 3 := by
    have h1 : N.relIndex (Subgroup.zpowers a) = 3 := by
      have h := Subgroup.relIndex_mul_card (H := N) (K := Subgroup.zpowers a)
      rw [inf_comm, hdisj, Subgroup.card_bot, mul_one, hcard3] at h
      exact h
    rw [Subgroup.relIndex_sup_left]
    exact h1
  have hgQ : g ∈ N ⊔ Subgroup.zpowers a := by
    have hg1 : g = (a * g⁻¹)⁻¹ * a := by group
    rw [hg1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (N.inv_mem hsame))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have haQ : a ∈ N ⊔ Subgroup.zpowers a :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  obtain ⟨m, -, hm⟩ := exists_conj_eq_or_inv_of_relIndex_eq_three (N := N)
    (Q := N ⊔ Subgroup.zpowers a) le_sup_left hrel hcop haQ hgQ haN hgN ha3 hg3
  exact ⟨m, hm⟩

theorem le_of_centralizer_le_of_threeA_of_surjective {G : Type*} [Group G] [Finite G] [Finite K]
    (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {L X Y : Subgroup G}
    (φ : L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (hφ : Function.Surjective φ)
    (hker : ¬ 3 ∣ Nat.card φ.ker) {e : G} (he3 : orderOf e = 3) (heL : e ∈ L)
    (he : ∃ u, u * φ ⟨e, heL⟩ * u⁻¹ = threeA hω)
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) (hY : ¬ 3 ∣ Nat.card Y)
    (hfix : Y ⊓ Subgroup.centralizer {e} ≤ X) : Y ≤ X := by
  classical
  obtain ⟨P, z, hPcard, hPexp, hzP, hzcent, hPconj⟩ := exists_extraspecial_conj_threeA hK hω
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf (G := L) 3 (P.comap φ)
  have hSQ : S ≤ P.comap φ := hS.le
  have hS3 : IsPGroup 3 S := hS.isPGroup
  have hSP : S.map φ = P := by
    have hmapP : (P.comap φ).map φ = P := Subgroup.map_comap_eq_self_of_surjective hφ P
    have hle : S.map φ ≤ P := by
      rw [← hmapP]
      exact Subgroup.map_mono hSQ
    have hrelmap : (S.map φ).relIndex P = (S ⊔ φ.ker).relIndex (P.comap φ) := by
      have h1 := Subgroup.relIndex_map_map (f := φ) S (P.comap φ)
      rw [hmapP, sup_eq_left.mpr (MonoidHom.ker_le_comap φ P)] at h1
      exact h1
    have hSrel : ¬ 3 ∣ S.relIndex (P.comap φ) :=
      ((CFSG.ABGLocalTools.isSylowOf_iff (p := 3) (P := S) (K := P.comap φ)).mp hS).2.2
    have hnd : ¬ 3 ∣ (S.map φ).relIndex P := by
      rw [hrelmap]
      exact fun h => hSrel (h.trans (Subgroup.relIndex_dvd_of_le_left
        (H := S) (K := S ⊔ φ.ker) (L := P.comap φ) le_sup_left))
    haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPcard]; norm_num)
    have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hPcard]; norm_num)
    have hrel : (S.map φ).relIndex P = 1 := by
      obtain ⟨n, hn⟩ := hP3.index ((S.map φ).subgroupOf P)
      have hn' : (S.map φ).relIndex P = 3 ^ n := hn
      rcases n with - | n
      · rw [hn', pow_zero]
      · exfalso
        apply hnd
        rw [hn', pow_succ']
        exact ⟨3 ^ n, rfl⟩
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hrel)
  have hSdisj : S ⊓ φ.ker = ⊥ := by
    have hcard1 : Nat.card ↥(S ⊓ φ.ker) = 1 := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hS3.to_inf_left (K := φ.ker))
      have hm' : Nat.card ↥(S ⊓ φ.ker) = 3 ^ m := hm
      rcases m with - | m
      · rw [hm', pow_zero]
      · exfalso
        apply hker
        have hdvd : Nat.card ↥(S ⊓ φ.ker) ∣ Nat.card ↥φ.ker :=
          Subgroup.card_dvd_of_le inf_le_right
        rw [hm', pow_succ'] at hdvd
        exact dvd_trans ⟨3 ^ m, rfl⟩ hdvd
    exact Subgroup.card_eq_one.mp hcard1
  have hinj : ∀ a ∈ S, ∀ b ∈ S, φ a = φ b → a = b := by
    intro a ha b hb hab
    have hmem : a * b⁻¹ ∈ S ⊓ φ.ker := by
      refine Subgroup.mem_inf.mpr ⟨S.mul_mem ha (S.inv_mem hb), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    rw [hSdisj] at hmem
    have h1 : a * b⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    rwa [mul_inv_eq_one] at h1
  have hSexp : ∀ g ∈ S, g ^ 3 = 1 := by
    intro g hg
    have h1 : φ (g ^ 3) = 1 := by
      rw [map_pow]
      have hgP : φ g ∈ P := Subgroup.mem_comap.mp (hSQ hg)
      rw [hPexp (φ g) hgP]
    have h2 : g ^ 3 ∈ S ⊓ φ.ker :=
      Subgroup.mem_inf.mpr ⟨S.pow_mem hg 3, by rw [MonoidHom.mem_ker]; exact h1⟩
    rw [hSdisj] at h2
    exact Subgroup.mem_bot.mp h2
  have hzP' : z ∈ S.map φ := by rw [hSP]; exact hzP
  obtain ⟨zL, hzLS, hzLφ⟩ := Subgroup.mem_map.mp hzP'
  have hzL3 : zL ^ 3 = 1 := hSexp zL hzLS
  have hzLcent : ∀ g ∈ S, g * zL = zL * g := by
    intro g hg
    have h1 : φ (g * zL * g⁻¹ * zL⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_mul, map_inv, hzLφ]
      have hgP : φ g ∈ P := Subgroup.mem_comap.mp (hSQ hg)
      have hcomm : φ g * z = z * φ g := hzcent (φ g) hgP
      calc φ g * z * (φ g)⁻¹ * z⁻¹ = (z * φ g) * (φ g)⁻¹ * z⁻¹ := by rw [hcomm]
        _ = z * z⁻¹ := by group
        _ = 1 := by group
    have h2 : g * zL * g⁻¹ * zL⁻¹ ∈ S ⊓ φ.ker :=
      Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem (S.mul_mem hg hzLS) (S.inv_mem hg))
        (S.inv_mem hzLS), by rw [MonoidHom.mem_ker]; exact h1⟩
    rw [hSdisj] at h2
    have h3 : g * zL * g⁻¹ * zL⁻¹ = 1 := Subgroup.mem_bot.mp h2
    calc g * zL = (g * zL * g⁻¹ * zL⁻¹) * (zL * g) := by group
      _ = 1 * (zL * g) := by rw [h3]
      _ = zL * g := one_mul _
  have hnotmem : ∀ g ∈ S, g ∉ Subgroup.zpowers zL → φ g ∉ Subgroup.zpowers z := by
    intro g hg hgz hmem
    apply hgz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : g * zL ^ (-k) ∈ S ⊓ φ.ker := by
      refine Subgroup.mem_inf.mpr ⟨S.mul_mem hg (S.zpow_mem hzLS (-k)), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hzLφ, ← hk, ← zpow_add]
      simp
    rw [hSdisj] at h1
    have h4 : g * zL ^ (-k) = 1 := Subgroup.mem_bot.mp h1
    have h5 : g = zL ^ k := by
      have h6 : g = (zL ^ (-k))⁻¹ := mul_eq_one_iff_eq_inv.mp h4
      rw [h6, zpow_neg, inv_inv]
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, h5.symm⟩
  have hφg1 : ∀ g ∈ S, g ∉ Subgroup.zpowers zL → φ g ≠ 1 := by
    intro g hg hgz h1
    refine hnotmem g hg hgz ?_
    rw [h1]
    exact Subgroup.one_mem _
  have he1 : (⟨e, heL⟩ : ↥L) ≠ 1 := by
    intro h
    have h' : e = 1 := congrArg Subtype.val h
    rw [h'] at he3
    simp at he3
  have hconj : ∀ g ∈ S, g ∉ Subgroup.zpowers zL → ∃ c : ↥L,
      g = c * ⟨e, heL⟩ * c⁻¹ ∨ g = c * ⟨e, heL⟩⁻¹ * c⁻¹ := by
    intro g hg hgz
    have hφgP : φ g ∈ P := Subgroup.mem_comap.mp (hSQ hg)
    have hφgz : φ g ∉ Subgroup.zpowers z := hnotmem g hg hgz
    have hg3 : g ^ 3 = 1 := hSexp g hg
    have hgN : g ∉ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hφg1 g hg hgz
    obtain ⟨u, hu⟩ := hPconj (φ g) hφgP hφgz
    obtain ⟨u₀, hu₀⟩ := he
    obtain ⟨l, hl⟩ := hφ u
    obtain ⟨l₀, hl₀⟩ := hφ u₀
    set c₀ : ↥L := l * l₀ with hc₀
    have hφc₀ : φ c₀ = u * u₀ := by rw [hc₀, map_mul, hl, hl₀]
    have key : ∀ w : ↥L, w ^ 3 = 1 → φ (c₀ * w * c₀⁻¹) = φ g →
        ∃ c : ↥L, g = c * w * c⁻¹ ∨ g = c * w⁻¹ * c⁻¹ := by
      intro w hw3 hwφ
      have ha3 : (c₀ * w * c₀⁻¹) ^ 3 = 1 := by
        have h : c₀ * w * c₀⁻¹ = MulAut.conj c₀ w := (MulAut.conj_apply c₀ w).symm
        rw [h, ← map_pow, hw3, map_one]
      have haN : c₀ * w * c₀⁻¹ ∉ φ.ker := by
        rw [MonoidHom.mem_ker, hwφ]
        exact hφg1 g hg hgz
      have hsame : (c₀ * w * c₀⁻¹) * g⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwφ, mul_inv_cancel]
      obtain ⟨m, hm | hm⟩ := exists_conj_eq_or_inv_of_mem_normal_of_not_dvd_three
        (N := φ.ker) hker ha3 hg3 haN hgN hsame
      · exact ⟨m * c₀, Or.inl (by rw [← hm]; group)⟩
      · exact ⟨m * c₀, Or.inr (by rw [← hm]; group)⟩
    have hφe : φ (⟨e, heL⟩ : ↥L) = u₀⁻¹ * threeA hω * u₀ := by
      calc φ ⟨e, heL⟩ = u₀⁻¹ * (u₀ * φ ⟨e, heL⟩ * u₀⁻¹) * u₀ := by group
        _ = u₀⁻¹ * threeA hω * u₀ := by rw [hu₀]
    have he3' : (⟨e, heL⟩ : ↥L) ^ 3 = 1 := by
      have h : orderOf (⟨e, heL⟩ : ↥L) = 3 := (Subgroup.orderOf_mk e heL).trans he3
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h])
    rcases hu with hu | hu
    · refine key ⟨e, heL⟩ he3' ?_
      · simp only [map_mul, map_inv, hφc₀, hφe]
        calc (u * u₀) * (u₀⁻¹ * threeA hω * u₀) * (u * u₀)⁻¹ = u * threeA hω * u⁻¹ := by
              group
          _ = φ g := hu
    · have hw3 : ((⟨e, heL⟩ : ↥L)⁻¹) ^ 3 = 1 := by
        rw [inv_pow, he3', inv_one]
      have hwφ : φ (c₀ * (⟨e, heL⟩ : ↥L)⁻¹ * c₀⁻¹) = φ g := by
        simp only [map_mul, map_inv, hφc₀, hφe]
        calc (u * u₀) * (u₀⁻¹ * threeA hω * u₀)⁻¹ * (u * u₀)⁻¹ = u * (threeA hω)⁻¹ * u⁻¹ := by
              group
          _ = φ g := hu
      obtain ⟨c, hc⟩ := key (⟨e, heL⟩ : ↥L)⁻¹ hw3 hwφ
      refine ⟨c, ?_⟩
      rcases hc with hc | hc
      · exact Or.inr hc
      · exact Or.inl (by rwa [inv_inv] at hc)
  have hfixS : ∀ g ∈ S.map L.subtype, g ∉ Subgroup.zpowers (zL : G) →
      Y ⊓ Subgroup.centralizer {g} ≤ X := by
    intro g hg hgz y hy
    obtain ⟨g', hg'S, hg'eq⟩ := Subgroup.mem_map.mp hg
    rw [← hg'eq] at hy hgz
    obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy
    have hg'z : g' ∉ Subgroup.zpowers zL := by
      intro h
      apply hgz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact ⟨k, by rw [← hk]; simp⟩
    obtain ⟨c, hc | hc⟩ := hconj g' hg'S hg'z
    · have hyG : y * ((c : G) * e * (c : G)⁻¹) = ((c : G) * e * (c : G)⁻¹) * y := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [hc] at h
        simpa using h
      have hyY' : (c : G)⁻¹ * y * c ∈ Y := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hLY (L.inv_mem c.2)) y).mp hyY
      have hyC' : (c : G)⁻¹ * y * c ∈ Subgroup.centralizer {e} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := congrArg (fun z : G => (c : G)⁻¹ * z * (c : G)) hyG
        simpa [mul_assoc] using h2
      have hyX' : (c : G)⁻¹ * y * c ∈ X := hfix (Subgroup.mem_inf.mpr ⟨hyY', hyC'⟩)
      have h3 : (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hLX c.2) ((c : G)⁻¹ * y * c)).mp hyX'
      rwa [show (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ = y from by group] at h3
    · have hyG : y * ((c : G) * e⁻¹ * (c : G)⁻¹) = ((c : G) * e⁻¹ * (c : G)⁻¹) * y := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [hc] at h
        simpa using h
      have hyY' : (c : G)⁻¹ * y * c ∈ Y := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hLY (L.inv_mem c.2)) y).mp hyY
      have hyC' : (c : G)⁻¹ * y * c ∈ Subgroup.centralizer {e} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := congrArg (fun z : G => (c : G)⁻¹ * z * (c : G)) hyG
        have h3 : ((c : G)⁻¹ * y * c) * e⁻¹ = e⁻¹ * ((c : G)⁻¹ * y * c) := by
          simpa [mul_assoc] using h2
        have h5 : ((c : G)⁻¹ * y * c) = e⁻¹ * ((c : G)⁻¹ * y * c) * e := by
          calc ((c : G)⁻¹ * y * c) = (((c : G)⁻¹ * y * c) * e⁻¹) * e := by group
            _ = (e⁻¹ * ((c : G)⁻¹ * y * c)) * e := by rw [h3]
        have h4 : e * ((c : G)⁻¹ * y * c) = ((c : G)⁻¹ * y * c) * e := by
          conv_lhs => rw [h5]
          group
        exact h4.symm
      have hyX' : (c : G)⁻¹ * y * c ∈ X := hfix (Subgroup.mem_inf.mpr ⟨hyY', hyC'⟩)
      have h3 : (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hLX c.2) ((c : G)⁻¹ * y * c)).mp hyX'
      rwa [show (c : G) * ((c : G)⁻¹ * y * c) * (c : G)⁻¹ = y from by group] at h3
  have hPX : S.map L.subtype ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.map_subtype_le S).trans hLX
  have hPY : S.map L.subtype ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.map_subtype_le S).trans hLY
  have hexp : ∀ g ∈ S.map L.subtype, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨g', hg', hg'eq⟩ := Subgroup.mem_map.mp hg
    rw [← hg'eq]
    simpa using congrArg (fun x : ↥L => (x : G)) (hSexp g' hg')
  have hcardS : 3 ^ 3 ≤ Nat.card (S.map L.subtype) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    have hdvd : 27 ∣ Nat.card S := by
      have h1 : Nat.card (S.map φ) ∣ Nat.card S := Subgroup.card_map_dvd S φ
      rwa [hSP, hPcard] at h1
    have h2 : 27 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos hdvd
    simpa using h2
  have hzPsub : (zL : G) ∈ S.map L.subtype := Subgroup.mem_map_of_mem _ hzLS
  have hzsub : ∀ g ∈ S.map L.subtype, g * (zL : G) = (zL : G) * g := by
    intro g hg
    obtain ⟨g', hg', hg'eq⟩ := Subgroup.mem_map.mp hg
    rw [← hg'eq]
    simpa using congrArg (fun x : ↥L => (x : G)) (hzLcent g' hg')
  exact CFSG.le_of_centralizer_le_outside_zpowers (p := 3) hYX hPX hPY hY hexp hcardS
    hzPsub hzsub hfixS

theorem normal_sup_of_le_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K X Q : Subgroup G} [K.Normal]
    (hX : CFSG.ABGLocalTools.IsSylowOf p X K)
    (hQN : Q ≤ Subgroup.normalizer (X : Set G))
    (hQn : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    (K ⊔ Q).Normal := by
  classical
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN
  have hfratt : K ⊔ N = ⊤ := by
    obtain ⟨S, hS⟩ := hX.exists_sylow_eq_subgroupOf
    have hXeq : (S : Subgroup ↥K).map K.subtype = X := by
      rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX.le]
    have h := Sylow.normalizer_sup_eq_top (p := p) (N := K) S
    rw [hXeq] at h
    rw [sup_comm]
    exact h
  set π : G →* G ⧸ K := QuotientGroup.mk' K with hπ
  have hKbot : K.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hNtop : N.map π = ⊤ := by
    have h1 : (⊤ : Subgroup G).map π = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective π
        (QuotientGroup.mk'_surjective K)]
    rw [← hfratt, Subgroup.map_sup, hKbot, bot_sup_eq] at h1
    exact h1
  have hQsub : (Q.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr hQn
  set ψ : ↥N →* G ⧸ K := π.comp N.subtype with hψ
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ N.map π := by rw [hNtop]; exact Subgroup.mem_top y
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨n, hn⟩, rfl⟩
  have hmap : ((Q.subgroupOf N).map ψ).Normal := hQsub.map ψ hψsurj
  have hQm : (Q.map π).Normal := by
    have h1 : (Q.subgroupOf N).map ψ = Q.map π := by
      rw [hψ, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQN]
    rwa [← h1]
  have hfinal : ((Q.map π).comap π).Normal := hQm.comap π
  rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_comm] at hfinal
  exact hfinal

theorem mul_conj_commute {G : Type*} [Group G] {x y e : G}
    (hx : x * e = e * x) (hy : y * e = e * y) :
    (x * y * x⁻¹) * e = e * (x * y * x⁻¹) := by
  have hx' : x⁻¹ * e = e * x⁻¹ := by
    have h := congrArg (fun z => x⁻¹ * z * x⁻¹) hx
    simpa [mul_assoc] using h.symm
  calc x * y * x⁻¹ * e = x * y * (x⁻¹ * e) := by group
    _ = x * y * (e * x⁻¹) := by rw [hx']
    _ = x * (y * e) * x⁻¹ := by group
    _ = x * (e * y) * x⁻¹ := by rw [hy]
    _ = x * e * y * x⁻¹ := by group
    _ = e * x * y * x⁻¹ := by rw [hx]
    _ = e * (x * y * x⁻¹) := by group

theorem odd_card_of_le_centralizer_threeA {G : Type*} [Group G] [Finite G]
    (hG : IsCharTwoType G) [Finite K] (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {L : Subgroup G} (φ : L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hφ : Function.Surjective φ) (hker : ¬ 3 ∣ Nat.card φ.ker)
    {e : G} (he3 : orderOf e = 3) (heL : e ∈ L) (he : ∃ u, u * φ ⟨e, heL⟩ * u⁻¹ = threeA hω)
    (hO2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {e} →
      ((Q ⊔ relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf
        (Subgroup.centralizer {e})).Normal →
      Q ≤ relPPrimeCore 3 (Subgroup.centralizer {e}))
    {C R : Subgroup G} (hCe : C ≤ Subgroup.centralizer {e})
    (hKC : relPPrimeCore 3 (Subgroup.centralizer {e}) ≤ C)
    (hKodd : ¬ 2 ∣ ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf C).index)
    (hRC : R ≤ C) (hRodd : ¬ 2 ∣ (R.subgroupOf C).index)
    (hRL : R ≤ Subgroup.centralizer (L : Set G)) :
    Odd (Nat.card R) := by
  classical
  obtain ⟨X, hX⟩ := CFSG.ABGLocalTools.exists_isSylowOf (G := G) 2 R
  have hXR : X ≤ R := hX.le
  have hX2 : IsPGroup 2 X := hX.isPGroup
  have hXndR : ¬ 2 ∣ X.relIndex R :=
    ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := X) (K := R)).mp hX).2.2
  have hXC : CFSG.ABGLocalTools.IsSylowOf 2 X C := by
    refine (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := X) (K := C)).mpr
      ⟨hXR.trans hRC, hX2, ?_⟩
    intro h2
    have hprod : 2 ∣ X.relIndex R * R.relIndex C := by
      rw [Subgroup.relIndex_mul_relIndex X R C hXR hRC]
      exact h2
    rcases Nat.prime_two.dvd_mul.mp hprod with h3 | h3
    · exact hXndR h3
    · exact hRodd h3
  have hXCnd : ¬ 2 ∣ X.relIndex C :=
    ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := X) (K := C)).mp hXC).2.2
  have hXleCe : X ≤ Subgroup.centralizer {e} := (hXR.trans hRC).trans hCe
  have hKeLe : relPPrimeCore 3 (Subgroup.centralizer {e}) ≤ Subgroup.centralizer {e} :=
    relPPrimeCore_le _
  have hKenCe : Subgroup.centralizer {e} ≤
      Subgroup.normalizer (relPPrimeCore 3 (Subgroup.centralizer {e}) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKeLe).mp
      (relPPrimeCore_normal (p := 3) (by norm_num) _)
  have hKen : ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr (hCe.trans hKenCe)
  have hXleKe : X ≤ relPPrimeCore 3 (Subgroup.centralizer {e}) := by
    haveI := hKen
    have hXmap : (X.subgroupOf C).map C.subtype = X := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hXR.trans hRC)]
    have hKemap : ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf C).map C.subtype
        = relPPrimeCore 3 (Subgroup.centralizer {e}) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKC]
    set π : ↥C →* (↥C ⧸ ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf C)) :=
      QuotientGroup.mk' _ with hπ
    have hXsub2 : IsPGroup 2 (X.subgroupOf C) := hX2.comap_subtype
    have hmap2 : IsPGroup 2 ((X.subgroupOf C).map π) := hXsub2.map π
    have hcard_dvd : Nat.card ((X.subgroupOf C).map π) ∣
        Nat.card (↥C ⧸ ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf C)) :=
      Subgroup.card_subgroup_dvd_card _
    have hoddquot : ¬ 2 ∣ Nat.card (↥C ⧸
        ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf C)) := hKodd
    have hmapbot : (X.subgroupOf C).map π = ⊥ := by
      have h1 : Nat.card ((X.subgroupOf C).map π) = 1 := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hmap2
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · rw [h0, pow_zero] at hn
          exact hn
        · exfalso
          apply hoddquot
          have h2 : 2 ∣ Nat.card ((X.subgroupOf C).map π) := by
            rw [hn]
            exact dvd_pow_self 2 h0.ne'
          exact h2.trans hcard_dvd
      exact Subgroup.card_eq_one.mp h1
    have hle : X.subgroupOf C ≤ (relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf C := by
      rw [Subgroup.map_eq_bot_iff] at hmapbot
      rwa [hπ, QuotientGroup.ker_mk'] at hmapbot
    rw [← hXmap, ← hKemap]
    exact Subgroup.map_mono hle
  have hXKe : CFSG.ABGLocalTools.IsSylowOf 2 X (relPPrimeCore 3 (Subgroup.centralizer {e})) := by
    refine (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := X)
      (K := relPPrimeCore 3 (Subgroup.centralizer {e}))).mpr ⟨hXleKe, hX2, ?_⟩
    intro h2
    apply hXCnd
    rw [← Subgroup.relIndex_mul_relIndex X (relPPrimeCore 3 (Subgroup.centralizer {e})) C
      hXleKe hKC]
    exact dvd_mul_of_dvd_left h2 _
  have hQ2 : IsPGroup 2 (pCoreOf 2 (Subgroup.centralizer {e} ⊓
      Subgroup.normalizer (X : Set G))) := isPGroup_pCoreOf 2 _
  have hQleCe : pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ≤
      Subgroup.centralizer {e} := (pCoreOf_le 2 _).trans inf_le_left
  have hQN : pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ≤
      Subgroup.normalizer (X : Set G) := (pCoreOf_le 2 _).trans inf_le_right
  have hN0Q : Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer {e} ⊓
        Subgroup.normalizer (X : Set G)) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hn hq
    · intro hq
      have h1 := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf
        (Subgroup.mem_inf.mpr ⟨(Subgroup.centralizer {e}).inv_mem hn.1,
          (Subgroup.normalizer (X : Set G)).inv_mem hn.2⟩) hq
      simpa [mul_assoc] using h1
  have hQN' : (pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G))).subgroupOf
      (Subgroup.centralizer {e}) ≤ Subgroup.normalizer
        (X.subgroupOf (Subgroup.centralizer {e}) : Set ↥(Subgroup.centralizer {e})) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hXleCe]
    exact Subgroup.subgroupOf_mono _ hQN
  have hN'Q' : Subgroup.normalizer (X.subgroupOf (Subgroup.centralizer {e}) :
        Set ↥(Subgroup.centralizer {e})) ≤
      Subgroup.normalizer ((pCoreOf 2 (Subgroup.centralizer {e} ⊓
        Subgroup.normalizer (X : Set G))).subgroupOf (Subgroup.centralizer {e}) :
        Set ↥(Subgroup.centralizer {e})) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hXleCe,
      ← Subgroup.subgroupOf_normalizer_eq hQleCe]
    intro x hx
    have hx' : (x : G) ∈ Subgroup.normalizer (X : Set G) := hx
    have h : (x : G) ∈ Subgroup.normalizer (pCoreOf 2 (Subgroup.centralizer {e} ⊓
        Subgroup.normalizer (X : Set G)) : Set G) :=
      hN0Q (Subgroup.mem_inf.mpr ⟨x.2, hx'⟩)
    exact h
  have hQNormal : ((pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ⊔
      relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf
        (Subgroup.centralizer {e})).Normal := by
    haveI : ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf
        (Subgroup.centralizer {e})).Normal := relPPrimeCore_normal (p := 3) (by norm_num) _
    have hX' : CFSG.ABGLocalTools.IsSylowOf 2 (X.subgroupOf (Subgroup.centralizer {e}))
        ((relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf
          (Subgroup.centralizer {e})) := by
      refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (Subgroup.centralizer {e})
        (A := X.subgroupOf (Subgroup.centralizer {e}))
        (B := (relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf
          (Subgroup.centralizer {e}))).mp ?_
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXleCe,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKeLe]
    have h := normal_sup_of_le_normalizer hX' hQN' hN'Q'
    have hsup : ((pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ⊔
        relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf (Subgroup.centralizer {e}))
        = (pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G))).subgroupOf
            (Subgroup.centralizer {e}) ⊔
          (relPPrimeCore 3 (Subgroup.centralizer {e})).subgroupOf (Subgroup.centralizer {e}) :=
      Subgroup.subgroupOf_sup hQleCe hKeLe
    rw [hsup]
    rw [sup_comm] at h
    exact h
  have hQleKe : pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ≤
      relPPrimeCore 3 (Subgroup.centralizer {e}) :=
    hO2 _ hQ2 hQleCe hQNormal
  have hN0le : Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer
        (pCoreOf 2 (Subgroup.normalizer (X : Set G)) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hn.2 hq
    · intro hq
      have h1 := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf
        ((Subgroup.normalizer (X : Set G)).inv_mem hn.2) hq
      simpa [mul_assoc] using h1
  have hNgY : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (X : Set G)) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hn hq
    · intro hq
      have h1 := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf
        ((Subgroup.normalizer (X : Set G)).inv_mem hn) hq
      simpa [mul_assoc] using h1
  have hQX2 : IsPGroup 2
      ((pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ⊔ X :
        Subgroup G)) :=
    (isPGroup_pCoreOf 2 _).to_sup_of_normal_right' hX2 hQN
  have hQleX : pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ≤ X := by
    have heq : pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) ⊔ X = X :=
      CFSG.ABGLocalTools.IsSylowOf.eq_of_le hXKe le_sup_right
        (by rw [sup_le_iff]; exact ⟨hQleKe, hXleKe⟩) hQX2
    exact le_sup_left.trans (le_of_eq heq)
  have hYQ : pCoreOf 2 (Subgroup.normalizer (X : Set G)) ⊓ Subgroup.centralizer {e} ≤
      pCoreOf 2 (Subgroup.centralizer {e} ⊓ Subgroup.normalizer (X : Set G)) := by
    refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf ?_ ?_ ?_
    · intro y hy
      exact Subgroup.mem_inf.mpr ⟨hy.2, pCoreOf_le 2 _ hy.1⟩
    · intro x hx y hy
      obtain ⟨hyY, hyCe⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hNgY hx.2) y).mp hyY
      · rw [Subgroup.mem_centralizer_singleton_iff] at hyCe ⊢
        exact mul_conj_commute (Subgroup.mem_centralizer_singleton_iff.mp hx.1) hyCe
    · exact (isPGroup_pCoreOf 2 (Subgroup.normalizer (X : Set G))).of_injective
        (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  have hYCeX : pCoreOf 2 (Subgroup.normalizer (X : Set G)) ⊓ Subgroup.centralizer {e} ≤ X :=
    hYQ.trans hQleX
  have hcommXL : ∀ l ∈ L, ∀ x ∈ X, l * x = x * l := by
    intro l hl x hx
    have h1 : x ∈ Subgroup.centralizer (L : Set G) := hRL (hXR hx)
    exact (Subgroup.mem_centralizer_iff.mp h1) l hl
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [show l * x * l⁻¹ = x from by rw [hcommXL l hl x hx]; group]
      exact hx
    · intro hx
      have hcomm' : l⁻¹ * (l * x * l⁻¹) = (l * x * l⁻¹) * l⁻¹ :=
        hcommXL l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
      have h2 : x = l * x * l⁻¹ := by
        calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
          _ = (l * x * l⁻¹) * l⁻¹ * l := by rw [hcomm']
          _ = l * x * l⁻¹ := by group
      rw [h2]
      exact hx
  have hLY : L ≤ Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (X : Set G)) : Set G) :=
    hLX.trans hNgY
  have hYX : pCoreOf 2 (Subgroup.normalizer (X : Set G)) ≤ Subgroup.normalizer (X : Set G) :=
    pCoreOf_le 2 _
  have hY3 : ¬ 3 ∣ Nat.card (pCoreOf 2 (Subgroup.normalizer (X : Set G))) := by
    intro h3
    obtain ⟨n, hn⟩ : ∃ n, Nat.card (pCoreOf 2 (Subgroup.normalizer (X : Set G))) = 2 ^ n :=
      IsPGroup.iff_card.mp (isPGroup_pCoreOf 2 (Subgroup.normalizer (X : Set G)))
    rw [hn] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hYXle : pCoreOf 2 (Subgroup.normalizer (X : Set G)) ≤ X :=
    le_of_centralizer_le_of_threeA_of_surjective hK hω φ hφ hker he3 heL he hLX hLY hYX hY3 hYCeX
  have hXleY : X ≤ pCoreOf 2 (Subgroup.normalizer (X : Set G)) := by
    refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf ?_ ?_ hX2
    · exact Subgroup.le_normalizer
    · intro x hx y hy
      exact (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  have hYXeq : pCoreOf 2 (Subgroup.normalizer (X : Set G)) = X := le_antisymm hYXle hXleY
  have hXbot : X = ⊥ := by
    by_contra hXne
    have h2loc : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hXne, hX2, rfl⟩
    have hchar := hG _ h2loc
    have hLle : L ≤ Subgroup.normalizer (X : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (X : Set G)) : Set G) := by
      intro l hl
      refine Subgroup.mem_inf.mpr ⟨hLX hl, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyX : y ∈ X := by rw [← hYXeq]; exact hy
      exact (hcommXL l hl y hyX).symm
    have hLleX : L ≤ X := hLle.trans (hchar.trans (le_of_eq hYXeq))
    have heX : e ∈ X := hLleX heL
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hX2 ⟨e, heX⟩
    have hk3 : orderOf (⟨e, heX⟩ : ↥X) = 3 := (Subgroup.orderOf_mk e heX).trans he3
    rw [hk3] at hk
    have h2dvd : 2 ∣ 2 ^ k := by
      rcases k with - | k
      · rw [pow_zero] at hk
        omega
      · rw [pow_succ']
        exact dvd_mul_right 2 _
    rw [← hk] at h2dvd
    exact absurd h2dvd (by norm_num)
  have hcardR : Nat.card R = Nat.card (X.subgroupOf R) * (X.subgroupOf R).index :=
    (Subgroup.card_mul_index _).symm
  have hXsub1 : Nat.card (X.subgroupOf R) = 1 := by
    rw [hXbot]
    simp
  rw [hXsub1, one_mul] at hcardR
  have hoddR : ¬ 2 ∣ Nat.card R := by
    rw [hcardR]
    exact hXndR
  rcases Nat.even_or_odd (Nat.card R) with hev | hodd
  · exact absurd (even_iff_two_dvd.mp hev) hoddR
  · exact hodd

end CFSG.StandardType.USixTwo

end
