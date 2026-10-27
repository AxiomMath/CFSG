module

public import CFSG.Monster.B.Mathieu.M11Sylow
public import CFSG.Monster.B.Mathieu.M22Sylow
public import CFSG.Monster.B.Mathieu.M23Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical

public section

namespace CFSG.RankThree.ThinCatalog

open CFSG.Blueprint CFSG.Monster.B.Mathieu

theorem eq_two_of_pow_dvd {N p k : ℕ} (hk : p ^ k ∣ N) (hk1 : ¬ p ^ (k + 1) ∣ N)
    (h2 : p ^ 2 ∣ N) (h3 : ¬ p ^ 3 ∣ N) : k = 2 := by
  rcases lt_trichotomy k 2 with hlt | heq | hgt
  · exact absurd ((Nat.pow_dvd_pow p (by omega : k + 1 ≤ 2)).trans h2) hk1
  · exact heq
  · exact absurd ((Nat.pow_dvd_pow p (by omega : 3 ≤ k)).trans hk) h3

theorem two_le_pRank_of_sylowFacts {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {N : ℕ}
    {gs : List (Equiv.Perm (Fin n))} {s : SylowRecord} (h : SylowFacts G N gs s)
    (hk : N.factorization s.prime = 2) (hlen : 2 ≤ s.normalGeneration.length) :
    2 ≤ CFSG.Open.pRank s.prime (⊤ : Subgroup G) := by
  obtain ⟨hp, -, hPG, hcard, -, -, hnd, hreps, huniq, -, -⟩ := h
  have : Fact s.prime.Prime := ⟨hp⟩
  have hlen' : 2 ≤ (s.reps n).length := by
    rw [SylowRecord.reps, List.length_map]
    exact hlen
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y, x ∈ s.reps n ∧ y ∈ s.reps n ∧ x ≠ y := by
    obtain ⟨x, y, l, hl⟩ : ∃ x y l, s.reps n = x :: y :: l := by
      rcases hr : s.reps n with _ | ⟨x, _ | ⟨y, l⟩⟩
      · rw [hr] at hlen'
        simp at hlen'
      · rw [hr] at hlen'
        simp at hlen'
      · exact ⟨x, y, l, rfl⟩
    rw [hl] at hnd
    refine ⟨x, y, by simp [hl], by simp [hl], fun hxy => ?_⟩
    rw [List.nodup_cons] at hnd
    exact hnd.1 (by simp [hxy])
  obtain ⟨hxP, hxo, -⟩ := hreps x hx
  obtain ⟨hyP, hyo, -⟩ := hreps y hy
  have hyx : ∀ m : ℕ, x ^ m ≠ y := by
    intro m hm
    have hQ : Subgroup.zpowers x ≤ s.subgroup n := (Subgroup.zpowers_le).2 hxP
    have hQc : Nat.card (Subgroup.zpowers x) = s.prime := by rw [Nat.card_zpowers, hxo]
    obtain ⟨z, -, hzu⟩ := huniq _ hQ hQc
    have hyQ : y ∈ Subgroup.zpowers x := by
      rw [← hm]
      exact Subgroup.npow_mem_zpowers x m
    have h1 := hzu x ⟨hx, Subgroup.mem_zpowers x⟩
    have h2 := hzu y ⟨hy, hyQ⟩
    exact hxy (h1.trans h2.symm)
  have hPc : Nat.card (s.subgroup n) = s.prime ^ 2 := by rw [hcard, hk]
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hPc
  have hcomm : x * y = y * x := by
    have h := congrArg Subtype.val (mul_comm' (⟨x, hxP⟩ : s.subgroup n) ⟨y, hyP⟩)
    simpa using h
  let x' : G := ⟨x, hPG hxP⟩
  let y' : G := ⟨y, hPG hyP⟩
  have hxp : x ^ s.prime = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one x
  have hyp : y ^ s.prime = 1 := by
    rw [← hyo]
    exact pow_orderOf_eq_one y
  have hx' : x' ^ s.prime = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hxp)
  have hy' : y' ^ s.prime = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hyp)
  have hxy' : Commute x' y' := Subtype.ext hcomm
  have hx1 : x' ≠ 1 := by
    intro h1
    have h1' : x = 1 := congrArg Subtype.val h1
    rw [h1', orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx' hy' hxy' hx1
    fun m hm => ?_
  exact hyx m (by
    have := congrArg Subtype.val hm
    rwa [SubgroupClass.coe_pow] at this)

theorem two_le_pRank_three_of_record {S : Type} [Group S] [Finite S] {n N : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))} {gs : List (Equiv.Perm (Fin n))} {r : GroupRecord}
    (hfacts : ∀ s ∈ r.sylows, SylowFacts G N gs s)
    (hmem : (3, 4) ∈ r.sylows.map (fun s => (s.prime, s.normalGeneration.length)))
    (h9 : 3 ^ 2 ∣ N) (h27 : ¬ 3 ^ 3 ∣ N) (e : S ≃* G) : 2 ≤ CFSG.pRank 3 S := by
  obtain ⟨s, hs, hs3⟩ := List.mem_map.1 hmem
  simp only [Prod.mk.injEq] at hs3
  obtain ⟨hp3, hl4⟩ := hs3
  have hf := hfacts s hs
  have hk : N.factorization s.prime = 2 := by
    rw [hp3]
    have hdvd := hf.2.2.2.2.1
    have hndvd := hf.2.2.2.2.2.1
    rw [hp3] at hdvd hndvd
    exact eq_two_of_pow_dvd hdvd hndvd h9 h27
  have h := two_le_pRank_of_sylowFacts hf hk (by omega)
  rw [hp3] at h
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
  exact h

theorem two_le_pRank_three_M11_sylow {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.M11) : 2 ≤ CFSG.pRank 3 S := by
  obtain ⟨r, -, -, -, hcounts, -, hfacts⟩ := fam_M11_sylow_normal_generation
  exact two_le_pRank_three_of_record hfacts (by rw [hcounts]; simp) (by norm_num)
    (by norm_num) e

theorem two_le_pRank_three_M22_sylow {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.M22) : 2 ≤ CFSG.pRank 3 S := by
  obtain ⟨r, -, -, -, hcounts, -, hfacts⟩ := fam_M22_sylow_normal_generation
  exact two_le_pRank_three_of_record hfacts (by rw [hcounts]; simp) (by norm_num)
    (by norm_num) e

theorem two_le_pRank_three_M23_sylow {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.M23) : 2 ≤ CFSG.pRank 3 S := by
  obtain ⟨r, -, -, -, hcounts, -, hfacts⟩ := fam_M23_sylow_normal_generation
  exact two_le_pRank_three_of_record hfacts (by rw [hcounts]; simp) (by norm_num)
    (by norm_num) e

end CFSG.RankThree.ThinCatalog
