module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Fin
public import CFSG.Open.StatedZModTwo
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_gl3_centralizer_seven
    {P : Subgroup (GL (Fin 3) (ZMod 2))} (hP : Nat.card P = 7) :
    Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2))) = P := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hN := CFSG.ComponentClassification.GMS78.card_normalizer_eq_of_card_eq_seven_GL32 hP
  have hle : P ≤ Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2))) := by
    haveI : IsCyclic P := isCyclic_of_prime_card (p := 7) hP
    exact Subgroup.le_centralizer (H := P)
  have hCN : Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2))) ≤
      Subgroup.normalizer (P : Set (GL (Fin 3) (ZMod 2))) :=
    Subgroup.centralizer_le_normalizer _
  have hdvd : Nat.card (Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2)))) ∣ 21 :=
    (Subgroup.card_dvd_of_le hCN).trans (by rw [hN])
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2)))) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hP] at this
  have hc : Nat.card (Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2)))) = 7 ∨
      Nat.card (Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2)))) = 21 := by
    obtain ⟨m, hm⟩ := h7
    have hm3 : m ∣ 3 := by
      have h : 7 * m ∣ 7 * 3 := by
        rw [← show (21 : ℕ) = 7 * 3 by norm_num]
        rwa [hm] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h1 | h3
    · left; rw [hm, h1, mul_one]
    · right; rw [hm, h3]
  rcases hc with hcard7 | hcard21
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard7, hP])).symm
  · exfalso
    have hNC : Subgroup.normalizer (P : Set (GL (Fin 3) (ZMod 2))) ≤
        Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2))) := by
      have heq : Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2))) =
          Subgroup.normalizer (P : Set (GL (Fin 3) (ZMod 2))) :=
        Subgroup.eq_of_le_of_card_ge hCN (by rw [hN, hcard21])
      exact heq.ge
    let S : Sylow 7 (GL (Fin 3) (ZMod 2)) := Sylow.ofCard P (by
      rw [hP, show (Nat.card (GL (Fin 3) (ZMod 2))).factorization 7 = 1 by
        rw [CFSG.ComponentClassification.GHarris.card_GL32_gh]; decide +kernel]
      norm_num)
    have hS : (S : Subgroup (GL (Fin 3) (ZMod 2))) = P := Sylow.coe_ofCard _ _
    have hburn : Subgroup.normalizer (S : Set (GL (Fin 3) (ZMod 2))) ≤
        Subgroup.centralizer (S : Set (GL (Fin 3) (ZMod 2))) := by
      have heqS : (S : Set (GL (Fin 3) (ZMod 2))) = (P : Set (GL (Fin 3) (ZMod 2))) :=
        congrArg (fun H : Subgroup (GL (Fin 3) (ZMod 2)) =>
          (H : Set (GL (Fin 3) (ZMod 2)))) hS
      rw [heqS]
      exact hNC
    let K := (MonoidHom.transferSylow S hburn).ker
    have hKcard : Nat.card K = 24 := by
      have hcK := (MonoidHom.ker_transferSylow_isComplement' S hburn).card_mul_card
      rw [CFSG.ComponentClassification.GHarris.card_GL32_gh] at hcK
      have hScard : Nat.card (S : Subgroup (GL (Fin 3) (ZMod 2))) = 7 := by rw [hS, hP]
      rw [hScard, show (168 : ℕ) = 24 * 7 by norm_num] at hcK
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) hcK
    rcases CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh.eq_bot_or_eq_top_of_normal K
      with hbot | htop
    · rw [hbot, Subgroup.card_bot] at hKcard; omega
    · rw [htop, Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh] at hKcard
      omega

private theorem s16h_e3_gl3_normal_coprime_bot
    {R P N : Subgroup (GL (Fin 3) (ZMod 2))}
    (hRcard : Nat.card R = 7 ∨ Nat.card R = 21)
    (hPle : P ≤ R) (hPcard : Nat.card P = 7)
    (hPnorm : ∀ x ∈ R, P.map (MulAut.conj x).toMonoidHom = P)
    (hNle : N ≤ R)
    (hNnorm : ∀ x ∈ R, N.map (MulAut.conj x).toMonoidHom = N)
    (h7N : ¬ 7 ∣ Nat.card N) : N = ⊥ := by
  have hdisj : N ⊓ P = ⊥ := by
    have hdvd : Nat.card ↥(N ⊓ P) ∣ 7 := by
      simpa [hPcard] using Subgroup.card_dvd_of_le (inf_le_right : N ⊓ P ≤ P)
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (h7 ▸ Subgroup.card_dvd_of_le (inf_le_left : N ⊓ P ≤ N)) h7N
  have hcent : N ≤ Subgroup.centralizer (P : Set (GL (Fin 3) (ZMod 2))) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hnR : n ∈ R := hNle hn
    have hpR : p ∈ R := hPle hp
    have hconjP : n * p * n⁻¹ ∈ P := by
      have hmem : (MulAut.conj n) p ∈ P.map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
      rwa [hPnorm n hnR] at hmem
    have hconjN : p * n⁻¹ * p⁻¹ ∈ N := by
      have hmem : (MulAut.conj p) n⁻¹ ∈ N.map (MulAut.conj p).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨n⁻¹, N.inv_mem hn, rfl⟩
      rwa [hNnorm p hpR] at hmem
    have hcomm : n * p * n⁻¹ * p⁻¹ ∈ N ⊓ P := by
      rw [Subgroup.mem_inf]
      refine ⟨?_, P.mul_mem hconjP (P.inv_mem hp)⟩
      have hNmem := N.mul_mem hn hconjN
      simpa only [← mul_assoc] using hNmem
    rw [hdisj] at hcomm
    have h1 : n * p * n⁻¹ * p⁻¹ = 1 := Subgroup.mem_bot.mp hcomm
    have h3 : n * p = p * n := by
      have h4 : n * p * n⁻¹ = p := by
        calc n * p * n⁻¹ = (n * p * n⁻¹ * p⁻¹) * p := by group
          _ = 1 * p := by rw [h1]
          _ = p := by rw [one_mul]
      calc n * p = (n * p * n⁻¹) * n := by group
        _ = p * n := by rw [h4]
    exact h3.symm
  have hcentP : N ≤ P := by
    rwa [s16h_e3_gl3_centralizer_seven hPcard] at hcent
  have hle : N ≤ N ⊓ P := le_inf le_rfl hcentP
  rw [hdisj] at hle
  exact le_bot_iff.mp hle

theorem s16h_e3_gl3_K_structure {K : Type} [Group K] [Finite K]
    (π₁ π₂ : K →* GL (Fin 3) (ZMod 2))
    (hinj : ∀ x : K, π₁ x = 1 → π₂ x = 1 → x = 1)
    (hno : ∀ x : K, orderOf x = 7 → π₁ x ≠ 1 ∧ π₂ x ≠ 1)
    {d : K} (hd : orderOf d = 7) :
    IsL3 K 1 ∨
      ∃ Z : Subgroup K, Nat.card ↥Z = 7 ∧ (∀ Z' : Subgroup K, Nat.card ↥Z' = 7 → Z' = Z) ∧
        Group.IsSolvable K ∧
        ∀ N : Subgroup K, N.Normal → Group.IsNilpotent ↥N → N ≤ Z := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let K1 : Subgroup K := π₁.ker
  let R : Subgroup (GL (Fin 3) (ZMod 2)) := π₂.range
  have hK1normal : K1.Normal := MonoidHom.normal_ker π₁
  have hK1no7 : ∀ x ∈ K1, orderOf x ≠ 7 := by
    intro x hx hx7
    exact (hno x hx7).1 (MonoidHom.mem_ker.mp (by simpa [K1] using hx))
  have h7K1 : ¬ 7 ∣ Nat.card ↥K1 := by
    intro h7
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K1) 7 h7
    rw [← Subgroup.orderOf_coe] at hx
    exact hK1no7 (x : K) x.2 hx
  have hφinj : Function.Injective (π₂.comp K1.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    refine hinj (x : K) ?_ ?_
    · exact MonoidHom.mem_ker.mp (by simpa [K1] using x.2)
    · simpa using hx
  have hNcard : Nat.card ↥(K1.map π₂) = Nat.card ↥K1 := by
    have hmap : K1.map π₂ = (π₂.comp K1.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hmap]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have h7N : ¬ 7 ∣ Nat.card ↥(K1.map π₂) := by
    rw [hNcard]; exact h7K1
  have hNle : K1.map π₂ ≤ R := Subgroup.map_le_range π₂ K1
  have hRy : 7 ∣ Nat.card ↥R := by
    have hmem : π₂ d ∈ R := MonoidHom.mem_range.mpr ⟨d, rfl⟩
    have hord : orderOf (⟨π₂ d, hmem⟩ : R) = 7 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [← map_pow, ← hd, pow_orderOf_eq_one, map_one]) (hno d hd).2
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hK1bot : K1 = ⊥ := by
    rcases s16h_gl3_subgroup_seven_dvd hRy with hR168 | ⟨hRcard, P, hPle, hPcard, hPnorm⟩
    ·
      have hRtop : R = ⊤ :=
        Subgroup.eq_top_of_card_eq R
          (by rw [hR168, CFSG.ComponentClassification.GHarris.card_GL32_gh])
      have hNnormal : (K1.map π₂).Normal := by
        refine ⟨fun n hn g => ?_⟩
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn
        have hg : g ∈ R := by rw [hRtop]; exact Subgroup.mem_top g
        obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
        exact Subgroup.mem_map.mpr
          ⟨y * k * y⁻¹, hK1normal.conj_mem k hk y, by simp [map_mul]⟩
      have hNbot : K1.map π₂ = ⊥ := by
        rcases CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
          |>.eq_bot_or_eq_top_of_normal (K1.map π₂) with hbot | htop
        · exact hbot
        · exfalso
          have h168 : Nat.card ↥(K1.map π₂) = 168 := by
            rw [htop, Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh]
          exact h7N (h168 ▸ by norm_num)
      have hcard1 : Nat.card ↥K1 = 1 := by rw [← hNcard, hNbot, Subgroup.card_bot]
      exact Subgroup.eq_bot_of_card_eq _ hcard1
    ·
      have hNnorm : ∀ x ∈ R, (K1.map π₂).map (MulAut.conj x).toMonoidHom = K1.map π₂ := by
        intro x hx
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · intro n hn
          obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
          obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
          obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
          exact Subgroup.mem_map.mpr
            ⟨y * k * y⁻¹, hK1normal.conj_mem k hk y,
              by simp [map_mul, MulAut.conj_apply]⟩
        · exact (Subgroup.card_map_of_injective
            (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).ge
      have hNbot : K1.map π₂ = ⊥ :=
        s16h_e3_gl3_normal_coprime_bot hRcard hPle hPcard hPnorm hNle hNnorm h7N
      have hcard1 : Nat.card ↥K1 = 1 := by rw [← hNcard, hNbot, Subgroup.card_bot]
      exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hπ₁inj : Function.Injective π₁ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    simpa [K1] using hK1bot
  let R1 : Subgroup (GL (Fin 3) (ZMod 2)) := π₁.range
  have hR1cardK : Nat.card ↥R1 = Nat.card K := by
    change Nat.card ↥π₁.range = Nat.card K
    exact (Nat.card_congr (MonoidHom.ofInjective hπ₁inj).toEquiv).symm
  have hdR1 : 7 ∣ Nat.card ↥R1 := by
    have hmem : π₁ d ∈ R1 := MonoidHom.mem_range.mpr ⟨d, rfl⟩
    have hord : orderOf (⟨π₁ d, hmem⟩ : R1) = 7 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [← map_pow, ← hd, pow_orderOf_eq_one, map_one]) (hno d hd).1
    rw [← hord]
    exact orderOf_dvd_natCard _
  rcases s16h_gl3_subgroup_seven_dvd hdR1 with hR1_168 | ⟨hR1card, P, hPle, hPcard, hPnorm⟩
  ·
    left
    have hR1top : R1 = ⊤ :=
      Subgroup.eq_top_of_card_eq R1
        (by rw [hR1_168, CFSG.ComponentClassification.GHarris.card_GL32_gh])
    have hsurj : Function.Surjective π₁ :=
      MonoidHom.range_eq_top.mp (by simpa [R1] using hR1top)
    let e : K ≃* GL (Fin 3) (ZMod 2) := MulEquiv.ofBijective π₁ ⟨hπ₁inj, hsurj⟩
    have hGL : IsL3 (GL (Fin 3) (ZMod 2)) 1 := by
      refine Or.inl ⟨by decide, ?_⟩
      refine CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two
        (n := 3) (by norm_num) ?_
      have h : CFSG.Open.StatedSL 3 (ZMod 2) = ⊤ :=
        CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two (by simp) 3
      exact Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hGL
  ·
    right
    let Z : Subgroup K := P.comap π₁
    have hZmap : Z.map π₁ = P := by
      change (P.comap π₁).map π₁ = P
      exact Subgroup.map_comap_eq_self hPle
    have hZcard : Nat.card ↥Z = 7 := by
      calc Nat.card ↥Z = Nat.card ↥(Z.map π₁) :=
            (Subgroup.card_map_of_injective (K := Z) hπ₁inj).symm
        _ = Nat.card ↥P := by rw [hZmap]
        _ = 7 := hPcard
    have hKcard : Nat.card K = 7 ∨ Nat.card K = 21 := by
      rw [← hR1cardK]; exact hR1card
    have hZnormal : Z.Normal := by
      refine ⟨fun z hz k => ?_⟩
      have hzP : π₁ z ∈ P := hz
      have hkR : π₁ k ∈ R1 := MonoidHom.mem_range.mpr ⟨k, rfl⟩
      have hmem : (MulAut.conj (π₁ k)) (π₁ z) ∈
          P.map (MulAut.conj (π₁ k)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨π₁ z, hzP, rfl⟩
      rw [hPnorm (π₁ k) hkR] at hmem
      simpa [map_mul, Z] using hmem
    haveI : Z.Normal := hZnormal
    refine ⟨Z, hZcard, ?_, ?_, ?_⟩
    ·
      intro Z' hZ'
      have hZ'card : Nat.card ↥(Z'.map π₁) = 7 := by
        rw [Subgroup.card_map_of_injective (K := Z') hπ₁inj, hZ']
      have hZ'le : Z'.map π₁ ≤ R1 := Subgroup.map_le_range π₁ Z'
      have hEq : Z'.map π₁ = P := by
        rcases hR1card with h7 | h21
        · have hZ'eq : Z'.map π₁ = R1 :=
            Subgroup.eq_of_le_of_card_ge hZ'le (by rw [hZ'card, h7])
          have hPeq : P = R1 :=
            Subgroup.eq_of_le_of_card_ge hPle (by rw [hPcard, h7])
          rw [hZ'eq, hPeq]
        · exact CFSG.Quasithin.Asc81c.eq_of_card_seven h21 hZ'le hPle hZ'card hPcard
      have h1 : (Z'.map π₁).comap π₁ = Z' :=
        Subgroup.comap_map_eq_self_of_injective hπ₁inj Z'
      have h2 : (Z.map π₁).comap π₁ = Z :=
        Subgroup.comap_map_eq_self_of_injective hπ₁inj Z
      rw [hEq] at h1
      rw [hZmap] at h2
      exact h1.symm.trans h2
    ·
      have hquot : Nat.card (K ⧸ Z) ∣ 3 := by
        rw [← Subgroup.index_eq_card]
        have h := Z.index_mul_card
        rw [hZcard] at h
        rcases hKcard with hk | hk <;> rw [hk] at h
        · have h1 : Z.index = 1 := by omega
          rw [h1]; norm_num
        · have h1 : Z.index = 3 := by omega
          rw [h1]
      haveI hZsol : Group.IsSolvable ↥Z := by
        haveI : IsCyclic ↥Z := isCyclic_of_card_dvd_prime (p := 7) (by rw [hZcard])
        infer_instance
      haveI hQsol : Group.IsSolvable (K ⧸ Z) := by
        haveI : IsCyclic (K ⧸ Z) := isCyclic_of_card_dvd_prime (p := 3) hquot
        infer_instance
      exact Group.isSolvable_of_subgroup_quotient Z
    ·
      intro N hNnormal hNnil
      by_cases h3 : 3 ∣ Nat.card ↥N
      ·
        have hNcard321 : Nat.card ↥N = 3 ∨ Nat.card ↥N = 21 := by
          have h1 : Nat.card ↥N ∣ Nat.card ↥R1 := by
            rw [hR1cardK]
            exact Subgroup.card_subgroup_dvd_card N
          rcases hR1card with h7 | h21
          · rw [h7] at h1
            exact absurd (h3.trans h1) (by norm_num)
          · rw [h21] at h1
            obtain ⟨t, ht⟩ := h3
            rw [ht] at h1
            have h2 : 3 * t ∣ 3 * 7 := by
              simpa [show (21 : ℕ) = 3 * 7 by norm_num] using h1
            have ht7 : t ∣ 7 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
            rcases (Nat.dvd_prime Nat.prime_seven).mp ht7 with h1' | h7'
            · left; rw [ht, h1', mul_one]
            · right; rw [ht, h7']
        rcases hNcard321 with hN3 | hN21
        ·
          have hMNcard : Nat.card ↥(N.map π₁) = 3 := by
            rw [Subgroup.card_map_of_injective (K := N) hπ₁inj, hN3]
          have hMle : N.map π₁ ≤ R1 := Subgroup.map_le_range π₁ N
          have hMnorm : ∀ x ∈ R1,
              (N.map π₁).map (MulAut.conj x).toMonoidHom = N.map π₁ := by
            intro x hx
            refine Subgroup.eq_of_le_of_card_ge ?_ ?_
            · intro m hm
              obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.mp hm
              obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm'
              obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
              exact Subgroup.mem_map.mpr
                ⟨y * k * y⁻¹, hNnormal.conj_mem k hk y,
                  by simp [map_mul, MulAut.conj_apply]⟩
            · exact (Subgroup.card_map_of_injective
                (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).ge
          have hbot := s16h_e3_gl3_normal_coprime_bot hR1card hPle hPcard hPnorm hMle hMnorm
            (by rw [hMNcard]; norm_num)
          rw [hbot, Subgroup.card_bot] at hMNcard
          omega
        ·
          have hK21 : Nat.card K = 21 := by
            have h1 : 21 ∣ Nat.card ↥R1 := by
              rw [← hN21]
              exact (Subgroup.card_subgroup_dvd_card N).trans (by rw [hR1cardK])
            rcases hR1card with h7 | h21
            · rw [h7] at h1; norm_num at h1
            · rw [← hR1cardK, h21]
          have hNK : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [hN21, hK21])
          haveI : Group.IsNilpotent ↥(⊤ : Subgroup K) := hNK ▸ hNnil
          haveI : Group.IsNilpotent K := Group.nilpotent_of_mulEquiv Subgroup.topEquiv
          obtain ⟨Q, hQcard, hQnormK⟩ :=
            Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (G := K) (n := 3)
              (by rw [hK21]; norm_num)
          let Q' : Subgroup (GL (Fin 3) (ZMod 2)) := Q.map π₁
          have hQ'card : Nat.card ↥Q' = 3 := by
            rw [Subgroup.card_map_of_injective (K := Q) hπ₁inj, hQcard]
          have hQ'le : Q' ≤ R1 := Subgroup.map_le_range π₁ Q
          have hQ'norm : ∀ x ∈ R1, Q'.map (MulAut.conj x).toMonoidHom = Q' := by
            intro x hx
            refine Subgroup.eq_of_le_of_card_ge ?_ ?_
            · intro q hq
              obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
              obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hq'
              obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
              exact Subgroup.mem_map.mpr
                ⟨y * k * y⁻¹, hQnormK.conj_mem k hk y,
                  by simp [map_mul, MulAut.conj_apply]⟩
            · exact (Subgroup.card_map_of_injective
                (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).ge
          have hbot := s16h_e3_gl3_normal_coprime_bot hR1card hPle hPcard hPnorm hQ'le hQ'norm
            (by rw [hQ'card]; norm_num)
          rw [hbot, Subgroup.card_bot] at hQ'card
          omega
      ·
        have hMNcard : Nat.card ↥(N.map π₁) = Nat.card ↥N :=
          Subgroup.card_map_of_injective (K := N) hπ₁inj
        have hMdiv7 : Nat.card ↥(N.map π₁) ∣ 7 := by
          have h1 : Nat.card ↥(N.map π₁) ∣ Nat.card ↥R1 := by
            rw [hMNcard, hR1cardK]
            exact Subgroup.card_subgroup_dvd_card N
          rcases hR1card with h7 | h21
          · rw [h7] at h1; exact h1
          · rw [h21] at h1
            have h3M : ¬ 3 ∣ Nat.card ↥(N.map π₁) := by rwa [hMNcard]
            have hcop : Nat.Coprime (Nat.card ↥(N.map π₁)) 3 :=
              ((Nat.prime_three.coprime_iff_not_dvd).2 h3M).symm
            exact (hcop.dvd_mul_right).mp
              (by simpa [show (21 : ℕ) = 7 * 3 by norm_num] using h1)
        have hMleP : N.map π₁ ≤ P := by
          rcases (Nat.dvd_prime Nat.prime_seven).mp hMdiv7 with h1 | h7
          · have hbot : N.map π₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
            rw [hbot]; exact bot_le
          · rcases hR1card with hR7 | hR21
            · have hPeq : P = R1 :=
                Subgroup.eq_of_le_of_card_ge hPle (by rw [hPcard, hR7])
              rw [hPeq]; exact Subgroup.map_le_range π₁ N
            · exact le_of_eq (CFSG.Quasithin.Asc81c.eq_of_card_seven hR21
                (Subgroup.map_le_range π₁ N) hPle h7 hPcard)
        intro n hn
        show π₁ n ∈ P
        exact hMleP (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
