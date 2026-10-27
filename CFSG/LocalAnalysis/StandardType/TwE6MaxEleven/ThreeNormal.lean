module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Local
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.StandardType.TwE6MaxEleven

open Subgroup

open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X]

private theorem maxElevenB_exists_zpow_of_mem_normalizer {G : Type*} [Group G]
    {C : Subgroup G} [IsCyclic C] {k : G} (hk : k ∈ Subgroup.normalizer (C : Set G)) :
    ∃ m : ℤ, ∀ c ∈ C, k * c * k⁻¹ = c ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (C.normalizerMonoidHom ⟨k, hk⟩).toMonoidHom
  exact ⟨m, fun c hc => by simpa using congrArg Subtype.val (hm ⟨c, hc⟩)⟩

private theorem maxElevenB_commutator_le_centralizer_of_isCyclic {G : Type*} [Group G]
    {C K : Subgroup G} [IsCyclic C] (hK : K ≤ Subgroup.normalizer (C : Set G)) :
    ⁅K, K⁆ ≤ Subgroup.centralizer (C : Set G) := by
  rw [Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨m₁, h₁⟩ := maxElevenB_exists_zpow_of_mem_normalizer (hK hk₁)
  obtain ⟨m₂, h₂⟩ := maxElevenB_exists_zpow_of_mem_normalizer (hK hk₂)
  obtain ⟨n₁, h₁'⟩ := maxElevenB_exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ (hK hk₁))
  obtain ⟨n₂, h₂'⟩ := maxElevenB_exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ (hK hk₂))
  have e₁ : ∀ c ∈ C, (c ^ n₁) ^ m₁ = c := fun c hc => by
    rw [← h₁ _ (C.zpow_mem hc n₁), ← h₁' c hc]
    group
  have e₂ : ∀ c ∈ C, (c ^ n₂) ^ m₂ = c := fun c hc => by
    rw [← h₂ _ (C.zpow_mem hc n₂), ← h₂' c hc]
    group
  refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
  have hc₂ := C.zpow_mem hc n₂
  have hc₂₁ := C.zpow_mem hc₂ n₁
  have hc₂₁₂ := C.zpow_mem hc₂₁ m₂
  have key : ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹ = c := by
    calc ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹
        = k₁ * (k₂ * (k₁⁻¹ * (k₂⁻¹ * c * k₂⁻¹⁻¹) * k₁⁻¹⁻¹) * k₂⁻¹) * k₁⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (((c ^ n₂) ^ n₁) ^ m₂) ^ m₁ := by rw [h₂' c hc, h₁' _ hc₂, h₂ _ hc₂₁, h₁ _ hc₂₁₂]
      _ = c := by
          rw [← zpow_mul (c ^ n₂) n₁ m₂, mul_comm n₁ m₂, zpow_mul (c ^ n₂) m₂ n₁, e₂ c hc,
            e₁ c hc]
  calc c * ⁅k₁, k₂⁆ = ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹ * ⁅k₁, k₂⁆ := by rw [key]
    _ = ⁅k₁, k₂⁆ * c := by group

private theorem maxElevenB_factorization_eleven :
    (2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19).factorization 11 = 1 := by
  have hnum : 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 =
      76532479683774853939200 := by norm_num
  rw [hnum]
  have h1 : 11 ^ 1 ∣ 76532479683774853939200 := by norm_num
  have h2 : ¬ 11 ^ 2 ∣ 76532479683774853939200 := by norm_num
  have hle1 : 1 ≤ (76532479683774853939200).factorization 11 :=
    (Nat.prime_eleven.pow_dvd_iff_le_factorization (by norm_num)).mp h1
  have hle2 : ¬ 2 ≤ (76532479683774853939200).factorization 11 := fun h =>
    h2 ((Nat.prime_eleven.pow_dvd_iff_le_factorization (by norm_num)).mpr h)
  omega

theorem maxElevenB_of_elemAbelian_three (hX : LocalFacts X) {M E : Subgroup X} (hM : IsCoatom M)
    {t : X} (htM : t ∈ M) (ht : orderOf t = 11) (hE1 : E ≠ ⊥) (hEM : E ≤ M)
    (hME : M ≤ normalizer (E : Set X)) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∃ N : Subgroup X, N ≤ M ∧ Nat.card N = 9196830720 ∧
      ∀ P : Subgroup X, P ≤ M → ⁅P, P⁆ = P → P ≤ N := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  have hE3p : IsPGroup 3 E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro e
    exact ⟨1, Subtype.ext (by simpa using hE3 e.1 e.2)⟩
  obtain ⟨n, hEn⟩ := IsPGroup.iff_card.mp hE3p
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      exact hE1 (Subgroup.eq_bot_of_card_eq (H := E) (by rw [hEn, h, pow_zero]))
    · exact h
  have hrank := hX.rank3 E hE3 hEc
  rw [hEn] at hrank
  have hn5 : n ≤ 5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hrank
  have htE : t ∈ normalizer (E : Set X) := hME htM
  let A : Subgroup X := zpowers t
  have hAE : A ≤ normalizer (E : Set X) := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact Subgroup.zpow_mem _ htE k
  have hAcard : Nat.card A = 11 := by
    change Nat.card (zpowers t) = 11
    rw [Nat.card_zpowers, ht]
  have hA11 : IsPGroup 11 A := IsPGroup.of_card (n := 1) (by rw [hAcard, pow_one])
  letI : Subgroup.Normalizes A E := ⟨hAE⟩
  let C : Subgroup X := E ⊓ centralizer ({t} : Set X)
  have hCeq : MulAction.fixedPoints A E = (fixedPointSubgroup A E : Set E) := rfl
  have hCsub : fixedPointSubgroup A E = C.subgroupOf E := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hx ⟨t, Subgroup.mem_zpowers t⟩
      have h' : t * (x : X) * t⁻¹ = (x : X) := by
        simpa using congrArg Subtype.val h
      calc (x : X) * t = (t * (x : X) * t⁻¹) * t := by rw [h']
        _ = t * (x : X) := by group
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_inf] at hx
      intro a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      apply Subtype.ext
      have hxt : (x : X) * t = t * (x : X) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.2
      change (a : X) * (x : X) * (a : X)⁻¹ = (x : X)
      rw [← hk]
      have hcomm : Commute (t ^ k) (x : X) :=
        (show Commute t (x : X) from hxt.symm).zpow_left k
      calc t ^ k * (x : X) * (t ^ k)⁻¹ = ((x : X) * t ^ k) * (t ^ k)⁻¹ := by rw [hcomm]
        _ = (x : X) := by group
  have hcardC : Nat.card (MulAction.fixedPoints A E) = Nat.card C := by
    rw [hCeq]
    change Nat.card (fixedPointSubgroup A E) = Nat.card C
    rw [hCsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ E)).toEquiv
  have hmod := hA11.card_modEq_card_fixedPoints E
  rw [hcardC, hEn] at hmod
  have hC66 : Nat.card C ∣ 66 :=
    (Subgroup.card_dvd_of_le (inf_le_right : C ≤ centralizer ({t} : Set X))).trans (hX.c11 t ht)
  have hC3n : Nat.card C ∣ 3 ^ n := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : C ≤ E)
    rwa [hEn] at h
  obtain ⟨k, hk_le, hCk⟩ := (Nat.dvd_prime_pow (p := 3) Nat.prime_three).mp hC3n
  have hk5 : k ≤ 5 := hk_le.trans hn5
  have hCk66 : 3 ^ k ∣ 66 := hCk ▸ hC66
  have hk01 : k = 0 ∨ k = 1 := by
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
    all_goals norm_num at hCk66
  have hCcases : Nat.card C = 1 ∨ Nat.card C = 3 := by
    rcases hk01 with rfl | rfl
    · exact Or.inl (by rw [hCk]; norm_num)
    · exact Or.inr (by rw [hCk]; norm_num)
  rcases hCcases with hC1 | hC3
  ·
    exfalso
    rw [hC1] at hmod
    have hn : n = 5 := by
      interval_cases n <;> norm_num at hmod
      rfl
    exact (hX.elem11 E hE3 hEc (by rw [hEn, hn]) t (hME htM)) ht
  rw [hC3] at hmod
  have hn : n = 1 := by
    interval_cases n <;> norm_num at hmod
    rfl
  have hEcard3 : Nat.card E = 3 := by rw [hEn, hn, pow_one]
  have hCE : C = E := by
    refine Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ E) ?_
    rw [hC3, hEcard3]
  have hEcent : E ≤ centralizer ({t} : Set X) := hCE ▸ inf_le_right
  have h3dvd : 3 ∣ Nat.card E := by rw [hEcard3]
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 h3dvd
  have hzX : orderOf (z : X) = 3 := by rw [orderOf_coe]; exact hzord
  have hzE : (z : X) ∈ E := z.2
  have hzEeq : E = zpowers (z : X) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzE) ?_).symm
    rw [Nat.card_zpowers, hzX, hEcard3]
  have hzcomm : Commute (z : X) t :=
    Subgroup.mem_centralizer_singleton_iff.mp (hEcent hzE)
  have hMle : M ≤ normalizer (zpowers (z : X) : Set X) := by
    rw [← hzEeq]
    exact hME
  have hNne : normalizer (zpowers (z : X) : Set X) ≠ ⊤ := by
    intro htop
    haveI : (zpowers (z : X)).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hX.simple.eq_bot_or_eq_top_of_normal (zpowers (z : X)) with hbot | htop'
    · have h3 : Nat.card (zpowers (z : X)) = 3 := by rw [Nat.card_zpowers, hzX]
      rw [hbot, Subgroup.card_bot] at h3
      norm_num at h3
    · have h3 : Nat.card X = 3 := by
        rw [← Subgroup.card_top (G := X), ← htop', Nat.card_zpowers, hzX]
      rw [hX.card] at h3
      norm_num at h3
  have hMeq : M = normalizer (zpowers (z : X) : Set X) := by
    refine le_antisymm hMle ?_
    exact (isCoatom_iff_ge_of_le.mp hM).2 _ hNne hMle
  obtain ⟨y₀, hy₀, L, hLcent, hLcard, hLperf⟩ := hX.levi
  have hL11 : 11 ∣ Nat.card L := by rw [hLcard]; norm_num
  obtain ⟨t₀, ht₀ord⟩ := exists_prime_orderOf_dvd_card' (G := L) 11 hL11
  have ht₀X : orderOf (t₀ : X) = 11 := by rw [orderOf_coe]; exact ht₀ord
  have hfac : (Nat.card X).factorization 11 = 1 := by
    rw [hX.card]
    exact maxElevenB_factorization_eleven
  have hcardt : Nat.card (zpowers t : Subgroup X) =
      11 ^ (Nat.card X).factorization 11 := by
    rw [Nat.card_zpowers, ht, hfac, pow_one]
  have hcardt₀ : Nat.card (zpowers (t₀ : X) : Subgroup X) =
      11 ^ (Nat.card X).factorization 11 := by
    rw [Nat.card_zpowers, ht₀X, hfac, pow_one]
  let P₁ : Sylow 11 X := Sylow.ofCard (zpowers t) hcardt
  let P₀ : Sylow 11 X := Sylow.ofCard (zpowers (t₀ : X)) hcardt₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := X) P₀ P₁
  have hg' : MulAut.conj g • (zpowers (t₀ : X) : Subgroup X) = zpowers t := by
    have h := congrArg (fun S : Sylow 11 X => (S : Subgroup X)) hg
    rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Sylow.coe_ofCard] at h
    exact h
  have hmem : t ∈ MulAut.conj g • (zpowers (t₀ : X) : Subgroup X) := by
    rw [hg']
    exact Subgroup.mem_zpowers t
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at hmem
  set h : X := g⁻¹ * t * g with hh_def
  have hh : h ∈ zpowers (t₀ : X) := by rw [hh_def]; exact hmem
  have hgh' : t = g * h * g⁻¹ := by rw [hh_def]; group
  have hhL : h ∈ L := (Subgroup.zpowers_le.mpr t₀.2) hh
  have hhcomm : Commute y₀ h :=
    ((Subgroup.mem_centralizer_singleton_iff (g := y₀) (k := h)).mp (hLcent hhL)).symm
  have hy3 : orderOf (g * y₀ * g⁻¹) = 3 := by
    have h := (MulAut.conj g).orderOf_eq y₀
    rw [hy₀] at h
    simpa [MulAut.conj_apply] using h
  have hcommY : Commute (g * y₀ * g⁻¹) t := by
    rw [hgh']
    exact hhcomm.conj g
  have hzy : zpowers (z : X) = zpowers (g * y₀ * g⁻¹) := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact mem_zpowers_of_commute_eleven hX ht hy3 hcommY hzX hzcomm
    · rw [Subgroup.zpowers_le]
      exact mem_zpowers_of_commute_eleven hX ht hzX hzcomm hy3 hcommY
  let N : Subgroup X := L.map (MulAut.conj g).toMonoidHom
  have hNcard : Nat.card N = 9196830720 := by
    change Nat.card (L.map (MulAut.conj g).toMonoidHom) = 9196830720
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hLcard]
  have hNleC : N ≤ centralizer ({g * y₀ * g⁻¹} : Set X) := by
    intro n hn
    rw [Subgroup.mem_map] at hn
    obtain ⟨l, hlL, rfl⟩ := hn
    have hlcomm : Commute l y₀ := Subgroup.mem_centralizer_singleton_iff.mp (hLcent hlL)
    have h := hlcomm.conj g
    rw [Subgroup.mem_centralizer_singleton_iff]
    change (g * l * g⁻¹) * (g * y₀ * g⁻¹) = (g * y₀ * g⁻¹) * (g * l * g⁻¹)
    exact h
  have hNleM : N ≤ M := by
    rw [hMeq]
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hnc : Commute n (g * y₀ * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hNleC hn)
    have hfix : MulAut.conj n (g * y₀ * g⁻¹) = g * y₀ * g⁻¹ := by
      calc n * (g * y₀ * g⁻¹) * n⁻¹ = (g * y₀ * g⁻¹) * n * n⁻¹ := by
            rw [show n * (g * y₀ * g⁻¹) = (g * y₀ * g⁻¹) * n from hnc]
        _ = g * y₀ * g⁻¹ := by group
    calc
      (zpowers (z : X)).map (MulAut.conj n)
          = (zpowers (g * y₀ * g⁻¹)).map (MulAut.conj n) := by rw [hzy]
      _ = zpowers (MulAut.conj n (g * y₀ * g⁻¹)) := MonoidHom.map_zpowers _ _
      _ = zpowers (g * y₀ * g⁻¹) := by rw [hfix]
      _ = zpowers (z : X) := hzy.symm
  refine ⟨N, hNleM, hNcard, ?_⟩
  intro P hPM hPperf
  have hPn : P ≤ normalizer (zpowers (z : X) : Set X) := by
    rw [hMeq] at hPM
    exact hPM
  have hPcent : P ≤ centralizer (zpowers (z : X) : Set X) := by
    have h := maxElevenB_commutator_le_centralizer_of_isCyclic (C := zpowers (z : X))
      (K := P) hPn
    rwa [hPperf] at h
  let P' : Subgroup X := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hP'cent : P' ≤ centralizer ({y₀} : Set X) := by
    intro p' hp'
    rw [Subgroup.mem_map] at hp'
    obtain ⟨p, hpP, rfl⟩ := hp'
    have hpC : p ∈ centralizer (zpowers (z : X) : Set X) := hPcent hpP
    have hpC' : p ∈ centralizer (zpowers (g * y₀ * g⁻¹) : Set X) := by
      rwa [hzy] at hpC
    have hpconj : Commute p (g * y₀ * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hpC' _ (Subgroup.mem_zpowers _)).symm
    have hconj : Commute (g⁻¹ * p * g) y₀ := by
      have h := hpconj.conj g⁻¹
      have h2 : g⁻¹ * (g * y₀ * g⁻¹) * (g⁻¹)⁻¹ = y₀ := by group
      rw [h2] at h
      simpa using h
    have hconj' : (g⁻¹ * p * g) * y₀ = y₀ * (g⁻¹ * p * g) := hconj
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [MulAut.conj_apply] using hconj'
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [← Subgroup.map_commutator (f := (MulAut.conj g⁻¹).toMonoidHom), hPperf]
  have hP'L : P' ≤ L := hLperf P' hP'cent hP'perf
  intro p hp
  have hmem' : (MulAut.conj g⁻¹) p ∈ P' := Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
  have hmemN : (MulAut.conj g) ((MulAut.conj g⁻¹) p) ∈ N :=
    Subgroup.mem_map.mpr ⟨(MulAut.conj g⁻¹) p, hP'L hmem', rfl⟩
  have hconjgp : (MulAut.conj g) ((MulAut.conj g⁻¹) p) = p := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rwa [hconjgp] at hmemN

end CFSG.StandardType.TwE6MaxEleven
