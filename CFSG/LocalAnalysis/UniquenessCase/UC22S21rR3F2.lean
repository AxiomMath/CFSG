module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3PA
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace R3Pair

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem false_of_not_inner (u : R3Pair D L K n p) {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D)
    (he : CFSG.Open.evenRank G = 3) (h1930 : H1930 D) (c : Ctx21 D Ch) {q : ℕ} (hq : q.Prime)
    (hq7 : 7 ≤ q) (hqn : q ∣ 2 ^ n - 1) {b : G} (hb : b ∈ c.B0) (hbo : orderOf b = q)
    (hninn : ¬ ∃ x ∈ barImage D.M L, ∀ f ∈ barImage D.M L, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x * f * x⁻¹) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  obtain ⟨hcomm, hinf, -, -, -, -, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have hβL := uc22ine229_mk_mem_normalizer (M := D.M) (x := ⟨b, c.hBM hb⟩)
    (uc22p2214_mem_normalizer_of_odd u.hc2 (c.hBM hb) hodd)
  have hβK := uc22ine229_mk_mem_normalizer (M := D.M) (x := ⟨b, c.hBM hb⟩)
    (uc22p2214_mem_normalizer_of_odd u.symm.hc2 (c.hBM hb) hodd)
  have hβq : uc22p21cPi D.M ⟨b, c.hBM hb⟩ ^ q = 1 := by
    rw [← map_pow, show (⟨b, c.hBM hb⟩ : ↥D.M) ^ q = 1 from
      Subtype.ext (by simpa [← hbo] using pow_orderOf_eq_one b), map_one]
  obtain ⟨β, hβ⟩ : ∃ β, uc22p21cPi D.M ⟨b, c.hBM hb⟩ = β := ⟨_, rfl⟩
  rw [hβ] at hβL hβK hβq hninn
  have hβ1 : β ≠ 1 := fun h => hninn ⟨1, one_mem _, fun f _ => by rw [h]⟩
  have hβo : orderOf β = q := orderOf_eq_prime hβq hβ1
  have hβX : β ∉ barImage D.M L ⊔ barImage D.M K := by
    intro h
    obtain ⟨a, ha, a', ha', hx⟩ := u4x_mem_sup hcomm h
    refine hninn ⟨a, ha, fun f hf => ?_⟩
    rw [← hx]
    have e : a' * f = f * a' := (hcomm f hf a' ha').symm
    calc a * a' * f * (a * a')⁻¹ = a * (a' * f) * a'⁻¹ * a⁻¹ := by group
      _ = a * (f * a') * a'⁻¹ * a⁻¹ := by rw [e]
      _ = a * f * a⁻¹ := by group
  obtain ⟨e₀, -⟩ := uc22p22l_barImage_equiv u.hL
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv u.hK
  obtain ⟨eK⟩ := u4x_bar2_equiv u.mem_K
  have hqL : q ∣ Nat.card ↥(barImage D.M L) := by
    rw [← Nat.card_congr e₀.toEquiv]
    exact hqn.trans u.dvd_card_bar2
  have hqK : q ∣ Nat.card ↥(barImage D.M K) := by
    rw [← Nat.card_congr (eK.trans e₁).toEquiv]
    exact hqn.trans u.dvd_card_bar2
  obtain ⟨u₀, hu₀, hu₀o, hβu₀⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L122A.exists_fixed_elt hq hqL hβo hβL
  obtain ⟨u₁, hu₁, hu₁o, hβu₁⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L122A.exists_fixed_elt hq hqK hβo hβK
  have hne1 : ∀ {x : Bar2 D.M}, orderOf x = q → x ≠ 1 := fun hx h => by
    rw [h, orderOf_one] at hx
    exact hq.one_lt.ne hx
  obtain ⟨hE₁, hc₁⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers
    (CFSG.Open.isElemAbelian_bot (G := Bar2 D.M) q) hu₀o
    (fun e he => by rw [Subgroup.mem_bot.1 he]; exact Commute.one_left _)
    (fun h => hne1 hu₀o (Subgroup.mem_bot.1 h))
  have hE₁L : (⊥ ⊔ zpowers u₀ : Subgroup (Bar2 D.M)) ≤ barImage D.M L :=
    sup_le bot_le (zpowers_le.2 hu₀)
  obtain ⟨hE₂, hc₂⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE₁ hu₁o
    (fun e he => hcomm e (hE₁L he) u₁ hu₁) fun h => hne1 hu₁o (by
      have h' : u₁ ∈ barImage D.M L ⊓ barImage D.M K := ⟨hE₁L h, hu₁⟩
      rwa [hinf, Subgroup.mem_bot] at h')
  have hE₂X : (⊥ ⊔ zpowers u₀ ⊔ zpowers u₁ : Subgroup (Bar2 D.M)) ≤
      barImage D.M L ⊔ barImage D.M K :=
    sup_le (hE₁L.trans le_sup_left) (zpowers_le.2 (mem_sup_right hu₁))
  have hE₂C : (⊥ ⊔ zpowers u₀ ⊔ zpowers u₁ : Subgroup (Bar2 D.M)) ≤ centralizer {β} :=
    sup_le (sup_le bot_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hβu₀.symm)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hβu₁.symm))
  obtain ⟨hE₃, hc₃⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE₂ hβo
    (fun e he => mem_centralizer_singleton_iff.1 (hE₂C he)) fun h => hβX (hE₂X h)
  have h3 : 3 ≤ CFSG.Open.pRank q (barImage D.M D.M) := by
    refine CFSG.Quasithin.le_pRank hq (fun x _ => ?_) hE₃
      (by rw [hc₃, hc₂, hc₁, Subgroup.card_bot]; ring)
    obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective D.M x
    exact uc22p21c_mem_barImage.2 ⟨m, m.2, rfl⟩
  rw [PartTwo.s13_pRank_barImage hq hq2 le_rfl] at h3
  obtain ⟨r, hr⟩ := hSg.nonempty
  have hqσ := h13 ⟨r, hr, uc22s2121e3_pRank_eq_three hSg he hr⟩ q hq hq7 h3
  exact uc22s217v_not_sp D Ch h1930 c hb hq hbo
    (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC u.hL) hqσ)

end R3Pair

theorem uc22r3f_false_of_isPowTwo {D : Data G} {Ch : Choice2011 G}
    (h869P : F08.R869NPair D) (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hn : 2 < n)
    (hpow : IsPowTwo n) (hL2 : IsL2 (Bar2 L) n) {q m : ℕ} (hq : q.Prime) (hm : Odd m)
    (hqm : q ∣ 2 ^ m - 1) {b : G} (hb : b ∈ c.B0) (hbo : orderOf b = q) : False := by
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hq2 : q ≠ 2 := by have := PartTwo.s13_seven_le_of_dvd hm hq hqm; omega
  have hqn : ¬ q ∣ n := by
    obtain ⟨j, rfl⟩ := hpow
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  have hqL : ¬ q ∣ Nat.card (Bar2 L) := by
    intro h
    rw [uc22p22r_L2_card hL2] at h
    rcases (Nat.Prime.dvd_mul hq).1 h with h1 | h1
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h1))
    · rw [← pow_mul] at h1
      have h2 : q ∣ Nat.gcd (2 ^ m - 1) (2 ^ (n * 2) - 1) := Nat.dvd_gcd hqm h1
      rw [Nat.pow_sub_one_gcd_pow_sub_one] at h2
      have hg : Nat.gcd m (n * 2) = 1 := by
        obtain ⟨j, rfl⟩ := hpow
        rw [← pow_succ]
        exact Nat.Coprime.pow_right _ hm.coprime_two_right
      rw [hg, pow_one] at h2
      exact hq.not_dvd_one (by simpa using h2)
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hb
  have hmemK : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hcK : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hmemK]; exact hc2
  have hbq : b ^ q = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  obtain ⟨x₀, hx₀, x₁, hx₁, hx₀q, hx₁q, -, -, hc⟩ :=
    u4x_bar_decomp hL hK hne hset (Or.inl hL2) hq hqn (b := ⟨b, c.hBM hb⟩)
      (uc22p2214_mem_normalizer_of_odd hc2 (c.hBM hb) hodd)
      (uc22p2214_mem_normalizer_of_odd hcK (c.hBM hb) hodd) (Subtype.ext (by simpa using hbq))
  obtain ⟨e₀, -⟩ := uc22p22l_barImage_equiv hL
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eK⟩ := u4x_bar2_equiv hmemK
  have h0 : x₀ = 1 := u4x_eq_one_of_pow hx₀ hq (by rwa [← Nat.card_congr e₀.toEquiv]) hx₀q
  have h1 : x₁ = 1 :=
    u4x_eq_one_of_pow hx₁ hq (by rwa [← Nat.card_congr (eK.trans e₁).toEquiv]) hx₁q
  subst h0 h1
  obtain ⟨-, -, -, -, hX, -, -⟩ := u4x_bar_structure hL hK hne hset (Or.inl hL2)
  have hw : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩ ∈
      centralizer ((barImage D.M (conjClosure D.M L) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) := by
    rw [hX]
    simpa using hc
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hcard : Nat.card (zpowers b) = q := by rw [Nat.card_zpowers, hbo]
  refine u4x_false_of_normalizer_le h1930 c hb (h869P L hL hc2 n hn hpow hL2 q hq hq2
    (zpowers b) (zpowers_le.2 (c.hBM hb)) hcard
    (uc22p21d_sup_pCore_eq hq hq2 hcard fun a ha => ?_))
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  refine u4x_centralizesBar hXM hMX (D.M.zpow_mem (c.hBM hb) k) ?_
  have he : (⟨b ^ k, D.M.zpow_mem (c.hBM hb) k⟩ : ↥D.M) = ⟨b, c.hBM hb⟩ ^ k :=
    Subtype.ext (by simp)
  rw [he, map_zpow]
  exact Subgroup.zpow_mem _ hw k

end CFSG.LocalAnalysis.UniquenessCase.UC22
