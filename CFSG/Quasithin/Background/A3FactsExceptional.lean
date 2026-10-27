module

public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.RootConj
public import CFSG.LieType.Chevalley.OrbitGroups
public import CFSG.LieType.Steinberg.Adjoint.Unipotent
public import CFSG.LieType.Steinberg.TwistedD4.Unipotent
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus
public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate123
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint (torusHom)

theorem exists_odd_prime_dvd_pred {n : ℕ} (h4 : 4 ≤ n) (hev : 2 ∣ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ n - 1 := by
  refine ⟨(n - 1).minFac, Nat.minFac_prime (by omega), ?_, Nat.minFac_dvd _⟩
  intro h2
  have h := Nat.minFac_dvd (n - 1)
  rw [h2] at h
  omega

theorem exists_unit_of_prime_dvd_pred {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    (hr : r ∣ Nat.card K - 1) : ∃ u : Kˣ, orderOf u = r := by
  have h : r ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hr
  exact exists_prime_orderOf_dvd_card' (G := Kˣ) r h

theorem simpleChar_one_adjoint {τ : Tag} {K : Type} [Field K] [Finite K] (i : Fin τ.rank) :
    CFSG.SectionRank.LargeRee.simpleChar (1 : adjointGroup τ K) i = 1 := by
  simp [CFSG.SectionRank.LargeRee.simpleChar]

section Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem zpow_cartan_eq_of_torusElement_eq
    {i j : Fin τ.rank} {t s : Kˣ}
    (h : torusElement τ K i t = torusElement τ K j s) (k : Fin τ.rank) :
    t ^ τ.cartan i k = s ^ τ.cartan j k := by
  have e1 := torusElement_conj_xElement (K := K) i k t 1
  have e2 := torusElement_conj_xElement (K := K) j k s 1
  rw [h, e2] at e1
  have h3 := xElement_injective k e1
  rw [mul_one, mul_one] at h3
  exact Units.ext h3.symm

theorem two_le_pRank_adjoint_torus
    [Finite K] {r : ℕ} [hr : Fact r.Prime] {u : Kˣ}
    (hu : orderOf u = r) {i j : Fin τ.rank}
    (hdet : ¬ (r : ℤ) ∣ τ.cartan i i * τ.cartan j j - τ.cartan i j * τ.cartan j i) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (adjointGroup τ K)) := by
  have hur : u ^ r = 1 := hu ▸ pow_orderOf_eq_one u
  have hord : ∀ m : ℤ, u ^ m = 1 → (r : ℤ) ∣ m := fun m hm => by
    have := (orderOf_dvd_iff_zpow_eq_one (x := u) (i := m)).2 hm
    rwa [hu] at this
  refine two_le_pRank_of_gens (x := torusHom K i u) (y := torusHom K j u) ?_ ?_
    (torusElement_commute i j u u) ?_ ?_
  · rw [← map_pow, hur, map_one]
  · rw [← map_pow, hur, map_one]
  · intro hx
    have h1 : torusElement τ K i u = torusElement τ K j 1 := by
      rw [show torusElement τ K j 1 = 1 from (torusHom K j).map_one]
      exact hx
    have hi := hord (τ.cartan i i) (by simpa using zpow_cartan_eq_of_torusElement_eq h1 i)
    have hj := hord (τ.cartan i j) (by simpa using zpow_cartan_eq_of_torusElement_eq h1 j)
    exact hdet (dvd_sub (Dvd.dvd.mul_right hi _) (Dvd.dvd.mul_right hj _))
  · intro n hn
    have h1 : torusElement τ K i (u ^ n) = torusElement τ K j u := by
      have : torusHom K i (u ^ n) = torusHom K j u := by rw [map_pow]; exact hn
      exact this
    have key : ∀ k : Fin τ.rank, (r : ℤ) ∣ (n : ℤ) * τ.cartan i k - τ.cartan j k := fun k => by
      have hk := zpow_cartan_eq_of_torusElement_eq h1 k
      apply hord
      rw [zpow_sub, mul_inv_eq_one, zpow_mul, zpow_natCast]
      exact hk
    apply hdet
    have h2 := dvd_sub (Dvd.dvd.mul_left (key i) (τ.cartan i j))
      (Dvd.dvd.mul_left (key j) (τ.cartan i i))
    convert h2 using 1
    ring

end Adjoint

theorem cartan_G2_det :
    Tag.G2.cartan ⟨0, by decide⟩ ⟨0, by decide⟩ * Tag.G2.cartan ⟨1, by decide⟩ ⟨1, by decide⟩ -
      Tag.G2.cartan ⟨0, by decide⟩ ⟨1, by decide⟩ * Tag.G2.cartan ⟨1, by decide⟩ ⟨0, by decide⟩ =
      1 := by
  decide

theorem not_dvd_cartan_G2_det {r : ℕ} (hr : r.Prime) :
    ¬ (r : ℤ) ∣ Tag.G2.cartan ⟨0, by decide⟩ ⟨0, by decide⟩ *
      Tag.G2.cartan ⟨1, by decide⟩ ⟨1, by decide⟩ -
      Tag.G2.cartan ⟨0, by decide⟩ ⟨1, by decide⟩ *
        Tag.G2.cartan ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  rw [cartan_G2_det]
  intro hd
  have h := Int.eq_one_of_dvd_one (Int.natCast_nonneg r) hd
  exact hr.one_lt.ne' (by exact_mod_cast h)

theorem oddRankTwo_G2
    {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : OddRankTwo S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨r, hr, hr2, hrdvd⟩ := exists_odd_prime_dvd_pred h4 h2f
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ := exists_unit_of_prime_dvd_pred (K := K) (r := r) (by rw [hK]; exact hrdvd)
  have hT : OddRankTwo (adjointGroup .G2 K) :=
    ⟨r, hr, hr2, two_le_pRank_adjoint_torus hu (not_dvd_cartan_G2_det hr)⟩
  let eQ : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot
  exact OddRankTwo.of_mulEquiv (e.trans eQ) hT

section Ree

open CFSG.SectionRank.LargeRee CFSG.LieType.Ree

theorem oddRankTwo_twistedF4
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : OddRankTwo S := by
  obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model h
  have hp2 : ReeTag.F4.prime = 2 := rfl
  have hKg : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hp2]
  have h2 : 2 ∣ Nat.card K := by rw [hKg]; exact dvd_pow_self 2 (by omega)
  have h4 : 4 ≤ Nat.card K := by
    rw [hKg]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨r, hr, hr2, hrdvd⟩ := exists_odd_prime_dvd_pred h4 h2
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ := exists_unit_of_prime_dvd_pred (K := K) hrdvd
  have hur : u ^ r = 1 := hu ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu
    exact hr.one_lt.ne hu
  obtain ⟨x, hx⟩ : ∃ x : reeFixed ReeTag.F4 K a, x = reeTorusHom a hK fi_zero_mem_longSet u :=
    ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : reeFixed ReeTag.F4 K a, y = reeTorusHom a hK fi_one_mem_longSet u :=
    ⟨_, rfl⟩
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 := congrArg (fun g : reeFixed ReeTag.F4 K a =>
      simpleChar (g : adjointGroup ReeTag.F4.tag K) (fi 1)) h1
    simp only [hx, coe_reeTorusHom, simpleChar_reeTorus, reeExp_zero_one, Subgroup.coe_one,
      simpleChar_one_adjoint] at h2
    have h3 : u ^ (-1 : ℤ) = 1 := Units.ext h2
    exact hu1 (by simpa using h3)
  have hy1 : y ≠ 1 := by
    intro h1
    have h2 := congrArg (fun g : reeFixed ReeTag.F4 K a =>
      simpleChar (g : adjointGroup ReeTag.F4.tag K) (fi 0)) h1
    simp only [hy, coe_reeTorusHom, simpleChar_reeTorus, reeExp_one_zero, Subgroup.coe_one,
      simpleChar_one_adjoint] at h2
    have h3 : u ^ (-1 : ℤ) = 1 := Units.ext h2
    exact hu1 (by simpa using h3)
  have hT : OddRankTwo (reeFixed ReeTag.F4 K a) := by
    refine ⟨r, hr, hr2, two_le_pRank_of_gens (x := x) (y := y) ?_ ?_ ?_ hx1 ?_⟩
    · rw [hx, ← map_pow, hur, map_one]
    · rw [hy, ← map_pow, hur, map_one]
    · rw [hx, hy]
      exact commute_of_mem_reeTorusPart
        (reeTorusSub_le_reeTorusPart hK fi_zero_mem_longSet ⟨u, rfl⟩)
        (reeTorusSub_le_reeTorusPart hK fi_one_mem_longSet ⟨u, rfl⟩)
    · intro n hn
      have hy0 : y ∈ reeTorusSub a hK fi_zero_mem_longSet :=
        ⟨u ^ n, by rw [map_pow, ← hx]; exact hn⟩
      have hy1' : y ∈ reeTorusSub a hK fi_one_mem_longSet := ⟨u, hy.symm⟩
      have hbot : y ∈ (⊥ : Subgroup (reeFixed ReeTag.F4 K a)) := by
        rw [← reeTorusSub_inf hK]
        exact ⟨hy0, hy1'⟩
      exact hy1 (Subgroup.mem_bot.mp hbot)
  exact OddRankTwo.of_mulEquiv e hT

end Ree

section Triality

open CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K] {σ : K →+* K}

theorem two_le_pRank_twistedGroup
    [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) {r : ℕ}
    [hr : Fact r.Prime] {u : Kˣ} (hu : orderOf u = r) (hσu : σ u = u) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (twistedGroup σ)) := by
  have hur : u ^ r = 1 := hu ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu
    exact hr.out.one_lt.ne hu
  obtain ⟨X, hXH, hXv⟩ := exists_hLongElt (σ := σ) hσu
  have hYmem : hShortHom σ u ∈ hHatE σ (ng 1 (by decide)) := ⟨u, rfl⟩
  have hYE : hShortHom σ u ∈ twistedGroup σ := hHatE_le_twistedGroup hσ (ng 1 (by decide)) hYmem
  obtain ⟨Y, hYv⟩ : ∃ Y : twistedGroup σ, (Y : adjointGroup d4 K) = hShortHom σ u :=
    ⟨⟨_, hYE⟩, rfl⟩
  have hYH : Y ∈ hHat σ (ng 1 (by decide)) := by
    rw [hHat, Subgroup.mem_subgroupOf, hYv]
    exact hYmem
  have hXpow : ∀ n : ℕ, ((X ^ n : twistedGroup σ) : adjointGroup d4 K) =
      torusElement d4 K (nd 2) (u ^ n) := fun n => by
    rw [Subgroup.coe_pow, hXv]
    exact (map_pow (torusHom (τ := d4) K (nd 2)) u n).symm
  have hY1 : Y ≠ 1 := fun h1 =>
    hu1 (eq_one_of_hShortHom_eq_one (σ := σ) (by simpa [hYv] using congrArg Subtype.val h1))
  refine two_le_pRank_of_gens (x := X) (y := Y) ?_ ?_ (hHat_commute σ hXH hYH) ?_ ?_
  · refine Subtype.ext ?_
    rw [hXpow, hur, Subgroup.coe_one]
    exact (torusHom (τ := d4) K (nd 2)).map_one
  · refine Subtype.ext ?_
    have h1 : hShortHom σ u ^ r = 1 := by rw [← map_pow, hur, map_one]
    rw [Subgroup.coe_pow, hYv, h1, Subgroup.coe_one]
  · intro hX1
    have h0 : ((X ^ 1 : twistedGroup σ) : adjointGroup d4 K) = 1 := by simp [hX1]
    have h1 : torusElement d4 K (nd 2) (u ^ 1) = hShortHom σ 1 := by
      rw [← hXpow, h0, map_one]
    exact hu1 (by simpa using eq_one_of_torusElement_eq_hShortHom hσ h1)
  · intro n hn
    have h1 : torusElement d4 K (nd 2) (u ^ n) = hShortHom σ u := by
      rw [← hXpow, hn, hYv]
    have hun : u ^ n = 1 := eq_one_of_torusElement_eq_hShortHom hσ h1
    apply hY1
    refine Subtype.ext ?_
    rw [hYv, ← h1, hun, Subgroup.coe_one]
    exact (torusHom (τ := d4) K (nd 2)).map_one

end Triality

theorem oddRankTwo_trialityD4
    {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (hS : ChevalleyExceptionalModel S .trialityD4 2 f) : OddRankTwo S := by
  obtain ⟨hadm, K, _, _, hK, σ, hσq, ⟨e⟩⟩ := hS
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 :=
    CFSG.SectionRank.charP_two_of_card (f := f * 3) (by rw [hK', ← pow_mul])
  have hσ3 := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hK' hσq
  let eD := CFSG.LieType.Steinberg.TwistedD4.twistedGroupEquivDerived σ hq hK' hσq
  have hZ := CFSG.SectionRank.center_eq_bot_of_mulEquiv' eD
    (CFSG.SectionRank.twistedGroup_center_eq_bot hσ3)
  let eS : DerivedCentralQuotient (twistedFixedGroup .D4 K σ) ≃*
      CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eD.symm)
  have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨r, hr, hr2, hrdvd⟩ := exists_odd_prime_dvd_pred h4 h2f
  have : Fact r.Prime := ⟨hr⟩
  have hdvd3 : 2 ^ f - 1 ∣ (2 ^ f) ^ 3 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 3
    rwa [one_pow] at this
  obtain ⟨u, hu⟩ := exists_unit_of_prime_dvd_pred (K := K) (r := r)
    (by rw [hK']; exact hrdvd.trans hdvd3)
  have hu1 : u ^ (2 ^ f - 1) = 1 := by
    have hdvd' : orderOf u ∣ 2 ^ f - 1 := by rw [hu]; exact hrdvd
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd'
  have hσu : σ (u : K) = u := by
    rw [hσq]
    have h1 : u ^ (2 ^ f) = u := by
      rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := f)), pow_succ, hu1, one_mul]
    have h2 := congrArg (fun v : Kˣ => (v : K)) h1
    simpa using h2
  exact OddRankTwo.of_mulEquiv (e.trans eS)
    ⟨r, hr, hr2, two_le_pRank_twistedGroup hσ3 hu hσu⟩

@[expose] def TrialityTwoOddRankTwo : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ChevalleyExceptionalModel S .trialityD4 2 1 → OddRankTwo S

end A3Facts

end CFSG.Quasithin
