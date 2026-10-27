module

public import CFSG.Quasithin.EmptyFaithful.S151cOne
public import CFSG.Quasithin.EmptyFaithful.S151cCases

public section

namespace CFSG.Quasithin

open CFSG.Open

section ShapeD10Aux151c

variable {V : Type} [CommGroup V] [Finite V]

theorem conj_mem_fittingOf_of_normalIn151c {X J : Subgroup (MulAut V)} (hn : NormalIn X J)
    {x f : MulAut V} (hx : x ∈ X) (hf : f ∈ fittingOf J) : x * f * x⁻¹ ∈ fittingOf J := by
  have hle : conjBy x (fittingOf J) ≤ fittingOf J := by
    refine le_fittingOf_of_normal_nilpotent ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hn x hx y (fittingOf_le J hy)
    · intro j hj n hn'
      rw [mem_conjBy_iff] at hn' ⊢
      have hj' : x⁻¹ * j * x ∈ J := by simpa using hn x⁻¹ (X.inv_mem hx) j hj
      have e : x⁻¹ * (j * n * j⁻¹) * x = (x⁻¹ * j * x) * (x⁻¹ * n * x) * (x⁻¹ * j * x)⁻¹ := by
        group
      rw [e]
      exact conj_mem_fittingOf hj' hn'
    · have := fittingOf_nilpotent J
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.equivMapOfInjective (fittingOf J) (MulAut.conj x).toMonoidHom
          (MulAut.conj x).injective)
  exact hle (mem_conjBy_of_mem hf)

private theorem d10_noFixed_of_commute (hcard : Nat.card V = 16) {a c : MulAut V}
    (ha5 : orderOf a = 5) (hfix : fixV (Subgroup.zpowers a) = ⊥) (hac : a * c = c * a)
    (hc1 : c ≠ 1) {v : V} (hv : c v = v) : v = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP : IsPGroup 5 (Subgroup.zpowers a) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha5]
    norm_num
  have hDinv : ∀ g ∈ Subgroup.zpowers a, ∀ b ∈ fixV (Subgroup.zpowers c),
      g b ∈ fixV (Subgroup.zpowers c) := by
    intro g hg b hb
    have hgc : g * c = c * g := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact ((show Commute a c from hac).zpow_left n).eq
    rw [mem_fixV_zpowers_iff] at hb ⊢
    calc c (g b) = (c * g) b := rfl
      _ = (g * c) b := by rw [hgc]
      _ = g (c b) := rfl
      _ = g b := by rw [hb]
  have hmod := card_invariant_modEq hP hfix hDinv
  have hdvd : Nat.card (fixV (Subgroup.zpowers c)) ∣ 16 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card (fixV (Subgroup.zpowers c))
  have hD1 : Nat.card (fixV (Subgroup.zpowers c)) = 1 := by
    have hne : Nat.card (fixV (Subgroup.zpowers c)) ≠ 16 := by
      intro h16
      have htop : fixV (Subgroup.zpowers c) = ⊤ :=
        (Subgroup.card_eq_iff_eq_top _).mp (by rw [h16, hcard])
      apply hc1
      refine MulEquiv.ext fun u => ?_
      have : u ∈ fixV (Subgroup.zpowers c) := by rw [htop]; exact Subgroup.mem_top u
      exact mem_fixV_zpowers_iff.mp this
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos := Nat.card_pos (α := fixV (Subgroup.zpowers c))
    unfold Nat.ModEq at hmod
    generalize Nat.card (fixV (Subgroup.zpowers c)) = n at *
    interval_cases n <;> omega
  have hDbot : fixV (Subgroup.zpowers c) = ⊥ := Subgroup.card_eq_one.mp hD1
  have : v ∈ fixV (Subgroup.zpowers c) := mem_fixV_zpowers_iff.mpr hv
  rw [hDbot, Subgroup.mem_bot] at this
  exact this

private theorem d10_card_centralizer_dvd (hcard : Nat.card V = 16) {F : Subgroup (MulAut V)}
    (hF5 : Nat.card F = 5) (hfix : fixV F = ⊥) :
    Nat.card (Subgroup.centralizer (F : Set (MulAut V))) ∣ 15 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨a, haF, -, hFa, ha5⟩ := exists_generator_of_prime_card hF5
  rw [← hFa] at hfix
  let Ω : Set V := {c | c ∈ (⊤ : Subgroup V) ∧ c ≠ 1}
  have hΩ : ∀ g ∈ Subgroup.centralizer (F : Set (MulAut V)), ∀ v ∈ Ω, g v ∈ Ω := by
    rintro g - v ⟨-, hv1⟩
    exact ⟨Subgroup.mem_top _, fun h => hv1 (g.injective (by rw [h, map_one]))⟩
  have hfree : ∀ g ∈ Subgroup.centralizer (F : Set (MulAut V)), ∀ v ∈ Ω, g v = v → g = 1 := by
    rintro g hg v ⟨-, hv1⟩ hgv
    by_contra hg1
    have hac : a * g = g * a := Subgroup.mem_centralizer_iff.mp hg a haF
    exact hv1 (d10_noFixed_of_commute hcard ha5 hfix hac hg1 hgv)
  have hdvd := card_dvd_card_of_free hΩ hfree
  have hΩcard : Nat.card ↥Ω + 1 = 16 := by
    have h := card_ne_one_add_one (⊤ : Subgroup V)
    rw [Subgroup.card_top, hcard] at h
    exact h
  have h15 : Nat.card ↥Ω = 15 := by omega
  rwa [h15] at hdvd

private theorem d10_centralizes_of_odd_order {F : Subgroup (MulAut V)} (hF5 : Nat.card F = 5)
    {y : MulAut V} (hy : y ∈ Subgroup.normalizer (F : Set (MulAut V))) (hodd : Odd (orderOf y)) :
    ∀ f ∈ F, y * f = f * y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcyc : IsCyclic F := isCyclic_of_prime_card hF5
  have h1 : orderOf (F.normalizerMonoidHom ⟨y, hy⟩) ∣ orderOf y := by
    have := orderOf_map_dvd F.normalizerMonoidHom
      (⟨y, hy⟩ : Subgroup.normalizer (F : Set (MulAut V)))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (F.normalizerMonoidHom ⟨y, hy⟩) ∣ 4 := by
    have := orderOf_dvd_natCard (F.normalizerMonoidHom ⟨y, hy⟩)
    rwa [IsCyclic.card_mulAut, hF5, Nat.totient_prime Nat.prime_five] at this
  have h3 : orderOf (F.normalizerMonoidHom ⟨y, hy⟩) = 1 := by
    have hcop : Nat.Coprime (orderOf y) 4 := by
      have := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)
      simpa using this
    have := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have hψ1 : F.normalizerMonoidHom ⟨y, hy⟩ = 1 := orderOf_eq_one_iff.mp h3
  intro f hf
  have := congrArg (fun φ : MulAut F => ((φ ⟨f, hf⟩ : F) : MulAut V)) hψ1
  simp only [MulAut.one_apply] at this
  have h4 : y * f * y⁻¹ = f := this
  rwa [mul_inv_eq_iff_eq_mul] at h4

private theorem d10_pow_four_centralizes {F : Subgroup (MulAut V)} (hF5 : Nat.card F = 5)
    {y : MulAut V} (hy : y ∈ Subgroup.normalizer (F : Set (MulAut V))) :
    ∀ f ∈ F, y ^ 4 * f = f * y ^ 4 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcyc : IsCyclic F := isCyclic_of_prime_card hF5
  have h4 : F.normalizerMonoidHom ⟨y, hy⟩ ^ 4 = 1 := by
    have h := pow_card_eq_one' (G := MulAut F) (x := F.normalizerMonoidHom ⟨y, hy⟩)
    rwa [IsCyclic.card_mulAut, hF5, Nat.totient_prime Nat.prime_five] at h
  intro f hf
  have h5 : F.normalizerMonoidHom
      ((⟨y, hy⟩ : Subgroup.normalizer (F : Set (MulAut V))) ^ 4) = 1 := by
    rw [map_pow]
    exact h4
  have := congrArg (fun φ : MulAut F => ((φ ⟨f, hf⟩ : F) : MulAut V)) h5
  simp only [MulAut.one_apply] at this
  have h6 : y ^ 4 * f * (y ^ 4)⁻¹ = f := this
  rwa [mul_inv_eq_iff_eq_mul] at h6

private theorem d10_eq_one_of_pow_two_pow {G : Type*} [Group G] {g : G} {m k : ℕ} (hm : Odd m)
    (hg : g ^ 2 ^ k = 1) (hd : orderOf g ∣ m) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
  have := Nat.dvd_gcd hd h1
  rw [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

private theorem d10_isCyclic_of_card {Q : Type*} [Group Q] [Finite Q] {a : Q} (ha : orderOf a = 5)
    (hc : ∀ q : Q, Commute a q) (h : Nat.card Q = 5 ∨ Nat.card Q = 15) : IsCyclic Q := by
  rcases h with h | h
  · exact isCyclic_of_orderOf_eq_card a (by rw [ha, h])
  · have h3 : 3 ∣ Nat.card Q := by rw [h]; norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine isCyclic_of_orderOf_eq_card (a * b) ?_
    rw [(hc b).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; norm_num), ha, hb, h]

private theorem d10_nonempty_zmod_of_cyclic {G : Type*} [Group G] (hG : IsCyclic G) {n : ℕ}
    (h : Nat.card G = n) : Nonempty (G ≃* Multiplicative (ZMod n)) := by
  subst h
  exact ⟨(zmodCyclicMulEquiv hG).symm⟩

private theorem d10_fittingOf_structure (hcard : Nat.card V = 16) {X F : Subgroup (MulAut V)}
    (hF5 : Nat.card F = 5) (hfix : fixV F = ⊥) (hFX : F ≤ X) (hn : NormalIn X F)
    (hodd : Odd (Nat.card (fittingOf X))) :
    fittingOf X = X ⊓ Subgroup.centralizer (F : Set (MulAut V)) ∧ F ≤ fittingOf X ∧
      IsCyclic (fittingOf X) ∧ (Nat.card (fittingOf X) = 5 ∨ Nat.card (fittingOf X) = 15) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hFcyc : IsCyclic F := isCyclic_of_prime_card hF5
  obtain ⟨a, haF, -, -, ha5⟩ := exists_generator_of_prime_card hF5
  have hCdvd := d10_card_centralizer_dvd hcard hF5 hfix
  have hXN := NormalIn.le_normalizer hn
  have hFC : F ≤ Subgroup.centralizer (F : Set (MulAut V)) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hFQ : F ≤ X ⊓ Subgroup.centralizer (F : Set (MulAut V)) := le_inf hFX hFC
  have hQcard : Nat.card ↥(X ⊓ Subgroup.centralizer (F : Set (MulAut V))) = 5 ∨
      Nat.card ↥(X ⊓ Subgroup.centralizer (F : Set (MulAut V))) = 15 := by
    have h1 := Subgroup.card_dvd_of_le hFQ
    have h2 := Subgroup.card_dvd_of_le
      (inf_le_right : X ⊓ Subgroup.centralizer (F : Set (MulAut V)) ≤ _)
    rw [hF5] at h1
    have h3 := h2.trans hCdvd
    have h4 := Nat.le_of_dvd (by norm_num) h3
    generalize Nat.card ↥(X ⊓ Subgroup.centralizer (F : Set (MulAut V))) = m at *
    interval_cases m <;> omega
  have hQcyc : IsCyclic ↥(X ⊓ Subgroup.centralizer (F : Set (MulAut V))) := by
    refine d10_isCyclic_of_card (a := ⟨a, hFQ haF⟩) ?_ ?_ hQcard
    · rw [Subgroup.orderOf_mk]
      exact ha5
    · intro q
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp q.2.2 a haF)
  have hNQ : fittingOf X ≤ X ⊓ Subgroup.centralizer (F : Set (MulAut V)) := by
    intro n hn'
    have hnX : n ∈ X := fittingOf_le X hn'
    refine ⟨hnX, ?_⟩
    have hoddn : Odd (orderOf n) := by
      have : orderOf n ∣ Nat.card (fittingOf X) := by
        have := orderOf_dvd_natCard (⟨n, hn'⟩ : fittingOf X)
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hodd this
    exact Subgroup.mem_centralizer_iff.mpr fun f hf =>
      (d10_centralizes_of_odd_order hF5 (hXN hnX) hoddn f hf).symm
  have hQN : X ⊓ Subgroup.centralizer (F : Set (MulAut V)) ≤ fittingOf X := by
    refine le_fittingOf_of_normal_nilpotent inf_le_left ?_ ?_
    · intro x hx q hq
      refine ⟨X.mul_mem (X.mul_mem hx hq.1) (X.inv_mem hx), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
      have hf' : x⁻¹ * f * x ∈ F := by simpa using hn x⁻¹ (X.inv_mem hx) f hf
      have := Subgroup.mem_centralizer_iff.mp hq.2 _ hf'
      calc f * (x * q * x⁻¹) = x * ((x⁻¹ * f * x) * q) * x⁻¹ := by group
        _ = x * (q * (x⁻¹ * f * x)) * x⁻¹ := by rw [this]
        _ = x * q * x⁻¹ * f := by group
    · have := hQcyc
      infer_instance
  have hEq : fittingOf X = X ⊓ Subgroup.centralizer (F : Set (MulAut V)) := le_antisymm hNQ hQN
  refine ⟨hEq, ?_, ?_, ?_⟩
  · rw [hEq]
    exact hFQ
  · rw [hEq]
    exact hQcyc
  · rw [hEq]
    exact hQcard

private theorem d10_sylow_structure (hcard : Nat.card V = 16) {X Tb F : Subgroup (MulAut V)}
    (hF5 : Nat.card F = 5) (hfix : fixV F = ⊥) (hn : NormalIn X F) (hTb : Tb ∈ sylow2Of X)
    (h2X : 2 ∣ Nat.card X) : IsCyclic Tb ∧ Nat.card Tb ∣ 4 ∧ 2 ∣ Nat.card Tb := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hCdvd := d10_card_centralizer_dvd hcard hF5 hfix
  have hCodd : Odd (Nat.card (Subgroup.centralizer (F : Set (MulAut V)))) :=
    Odd.of_dvd_nat (by decide) hCdvd
  obtain ⟨hTX, hTp, hTidx⟩ := hTb
  have hTN : Tb ≤ Subgroup.normalizer (F : Set (MulAut V)) :=
    hTX.trans (NormalIn.le_normalizer hn)
  let ρ : ↥Tb →* MulAut ↥F := F.normalizerMonoidHom.comp (Subgroup.inclusion hTN)
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcent : ∀ f ∈ F, (g : MulAut V) * f = f * (g : MulAut V) := by
      intro f hf
      have := congrArg (fun φ : MulAut ↥F => ((φ ⟨f, hf⟩ : ↥F) : MulAut V)) hg
      simp only [MulAut.one_apply] at this
      have h4 : (g : MulAut V) * f * (g : MulAut V)⁻¹ = f := this
      rwa [mul_inv_eq_iff_eq_mul] at h4
    have hgC : (g : MulAut V) ∈ Subgroup.centralizer (F : Set (MulAut V)) :=
      Subgroup.mem_centralizer_iff.mpr fun f hf => (hcent f hf).symm
    obtain ⟨k, hk⟩ := hTp g
    have hgk : (g : MulAut V) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf (g : MulAut V) ∣
        Nat.card (Subgroup.centralizer (F : Set (MulAut V))) := by
      have := orderOf_dvd_natCard
        (⟨(g : MulAut V), hgC⟩ : Subgroup.centralizer (F : Set (MulAut V)))
      rwa [Subgroup.orderOf_mk] at this
    exact Subtype.ext (d10_eq_one_of_pow_two_pow hCodd hgk hdvd)
  have hFcyc : IsCyclic F := isCyclic_of_prime_card hF5
  have hAutcyc : IsCyclic (MulAut ↥F) :=
    (IsCyclic.mulAutMulEquiv ↥F).isCyclic.mpr
      (ZMod.isCyclic_units_prime (by rw [hF5]; exact Nat.prime_five))
  have hTcyc : IsCyclic Tb := isCyclic_of_injective ρ hρinj
  have hTdvd : Nat.card Tb ∣ 4 := by
    have := Subgroup.card_dvd_of_injective ρ hρinj
    rwa [IsCyclic.card_mulAut, hF5, Nat.totient_prime Nat.prime_five] at this
  have hTeven : 2 ∣ Nat.card Tb := by
    have hmul := Subgroup.card_mul_index (Tb.subgroupOf X)
    have hcardT : Nat.card (Tb.subgroupOf X) = Nat.card Tb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv
    rw [hcardT] at hmul
    have h2 : 2 ∣ Nat.card Tb * (Tb.subgroupOf X).index := by
      rw [hmul]
      exact h2X
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact h
    · exact absurd h hTidx
  exact ⟨hTcyc, hTdvd, hTeven⟩

end ShapeD10Aux151c

section ShapeD10151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

theorem shape_D10 (B : OneBlock151c X Tb Xc J r) (e : Nonempty (↥J ≃* DihedralGroup 5))
    (_hr : r = 2) (hrk : rk V = 4) : ACase5 X Tb J ∧ TwoNilpAut X := by
  have hcard : Nat.card V = 16 := by rw [card_eq_two_pow_rk B.sq, hrk]; norm_num
  have hJ10 : Nat.card J = 10 := by rw [card_of_dihedral e]
  have hodd := odd_card_fittingOf B.hyp.o2
  have hfix : fixV (fittingOf J) = ⊥ := fixV_fittingOf_eq_bot B.sq B.hyp.o2 B.hyp.comm_fitting
  have hF5 : Nat.card (fittingOf J) = 5 := by
    have hdvd : Nat.card (fittingOf J) ∣ 10 := hJ10 ▸ Subgroup.card_dvd_of_le (fittingOf_le J)
    have hbotfix : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      refine eq_top_iff.mpr fun v _ x hx => ?_
      rw [Subgroup.mem_bot] at hx
      simp [hx]
    have hne : Nat.card (fittingOf J) ≠ 1 := by
      intro h1
      have hbot : fittingOf J = ⊥ := Subgroup.card_eq_one.mp h1
      have htop : (⊤ : Subgroup V) = ⊥ := by
        rw [← hbotfix, ← hbot, hfix]
      have : Nat.card V = 1 := by rw [← Subgroup.card_top, htop, Subgroup.card_bot]
      omega
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hodd
    generalize Nat.card (fittingOf J) = n at *
    interval_cases n <;> omega
  have hFX : fittingOf J ≤ X := (fittingOf_le J).trans B.le
  have hn : NormalIn X (fittingOf J) := fun x hx f hf =>
    conj_mem_fittingOf_of_normalIn151c B.normal hx hf
  have hoddX := odd_card_fittingOf B.setting.o2
  have h2X : 2 ∣ Nat.card X := by
    have h1 : Nat.card J ∣ Nat.card X := Subgroup.card_dvd_of_le B.le
    rw [hJ10] at h1
    exact (show 2 ∣ 10 by norm_num).trans h1
  obtain ⟨hNeq, hFN, hNcyc, hNcard⟩ := d10_fittingOf_structure hcard hF5 hfix hFX hn hoddX
  obtain ⟨hTcyc, hTdvd, hTeven⟩ := d10_sylow_structure hcard hF5 hfix hn B.syl h2X
  refine ⟨⟨hcard, e, ?_, ?_⟩, ?_⟩
  · have hT24 : Nat.card Tb = 2 ∨ Nat.card Tb = 4 := by
      have h1 := Nat.le_of_dvd (by norm_num) hTdvd
      generalize Nat.card Tb = m at *
      interval_cases m <;> omega
    rcases hT24 with h | h
    · exact Or.inl (d10_nonempty_zmod_of_cyclic hTcyc h)
    · exact Or.inr (d10_nonempty_zmod_of_cyclic hTcyc h)
  · rcases hNcard with h | h
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hFN (by rw [hF5, h])).symm
    · exact Or.inr (d10_nonempty_zmod_of_cyclic hNcyc h)
  · refine ⟨fittingOf X, fittingOf_le X, fun g hg y hy => conj_mem_fittingOf hg hy, hoddX,
      fun x hx => ⟨2, ?_⟩⟩
    have hx4 : x ^ 4 ∈ X ⊓ Subgroup.centralizer (fittingOf J : Set (MulAut V)) :=
      ⟨X.pow_mem hx 4, Subgroup.mem_centralizer_iff.mpr fun f hf =>
        (d10_pow_four_centralizes hF5 (NormalIn.le_normalizer hn hx) f hf).symm⟩
    rw [hNeq]
    exact hx4

end ShapeD10151c

end CFSG.Quasithin
