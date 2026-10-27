module

public import CFSG.Quasithin.Background.RonanF13Defs
public import CFSG.Quasithin.Background.RonanF13Section
public import CFSG.Quasithin.Background.RonanF13Finish
public import CFSG.GH74.Uniqueness.Bender.Sylow2Special
public import CFSG.Quasithin.H13.NQCatLieOverRank1
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.RonanF13

open CFSG.GH74.Uniqueness.Bender

section Aux

variable {K : Type*} [Group K]

theorem card_normalizer_eq_mul (T D : Subgroup K)
    (hTD : T ⊔ D = Subgroup.normalizer (T : Set K)) (hI : T ⊓ D = ⊥) :
    Nat.card (Subgroup.normalizer (T : Set K)) = Nat.card T * Nat.card D := by
  have hDN : D ≤ Subgroup.normalizer (T : Set K) := hTD ▸ le_sup_right
  let f : T × D → Subgroup.normalizer (T : Set K) := fun p =>
    ⟨(p.1 : K) * p.2, by
      rw [← hTD]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, d⟩ ⟨u', d'⟩ h
      have h1 : (u : K) * d = u' * d' := congrArg Subtype.val h
      have h2 : ((u' : K)⁻¹ * u) ∈ T ⊓ D := by
        refine ⟨T.mul_mem (T.inv_mem u'.2) u.2, ?_⟩
        have : ((u' : K)⁻¹ * u) = d' * (d : K)⁻¹ := by
          calc ((u' : K)⁻¹ * u) = (u' : K)⁻¹ * (u * d) * (d : K)⁻¹ := by group
            _ = (u' : K)⁻¹ * (u' * d') * (d : K)⁻¹ := by rw [h1]
            _ = d' * (d : K)⁻¹ := by group
        rw [this]
        exact D.mul_mem d'.2 (D.inv_mem d.2)
      rw [hI, Subgroup.mem_bot] at h2
      have hu : (u : K) = u' := by
        have := mul_eq_one_iff_eq_inv.mp h2
        simpa using this.symm
      have hd : (d : K) = d' := by
        have := h1
        rw [hu] at this
        exact mul_left_cancel this
      exact Prod.ext (Subtype.ext hu) (Subtype.ext hd)
    · rintro ⟨n, hn⟩
      rw [← hTD] at hn
      obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hDN).mp hn
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem mem_normalizer_rootCenter {T : Subgroup K} {d : K} (hd : d ∈ Subgroup.normalizer (T : Set K)) :
    d ∈ Subgroup.normalizer ((rootCenter T : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact conj_mem_rootCenter hd hz
  · intro hz
    have hd' : d⁻¹ ∈ borel T := Subgroup.inv_mem _ hd
    have := conj_mem_rootCenter hd' hz
    simpa [mul_assoc] using this

theorem alpha_rootCenter {T : Subgroup K} (α : MulAut K) (hαT : ∀ x, α x ∈ T ↔ x ∈ T) (x : K) :
    α x ∈ rootCenter T ↔ x ∈ rootCenter T := by
  rw [mem_rootCenter_iff, mem_rootCenter_iff, hαT]
  refine and_congr_right fun hx => ?_
  constructor
  · intro h p hp
    have := h (α p) ((hαT p).mpr hp)
    rw [← map_mul, ← map_mul] at this
    exact α.injective this
  · intro h p hp
    obtain ⟨q, rfl⟩ : ∃ q, α q = p := ⟨α⁻¹ p, by simp⟩
    rw [← map_mul, ← map_mul, h q ((hαT q).mp hp)]

theorem exists_mul_of_sup {T D : Subgroup K} (hTD : T ⊔ D = Subgroup.normalizer (T : Set K))
    {n : K} (hn : n ∈ Subgroup.normalizer (T : Set K)) : ∃ u ∈ T, ∃ δ ∈ D, n = u * δ := by
  have hDN : D ≤ Subgroup.normalizer (T : Set K) := hTD ▸ le_sup_right
  rw [← hTD] at hn
  exact (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hDN).mp hn

end Aux

section Main

variable {K : Type*} [Group K] [Finite K] {n i e : ℕ}

theorem bender_twist (h : BenderType K n i e) : RankOneTwist K := by
  intro T D α hT hodd hTD hDodd hαT hαD hαodd hcomm
  classical
  have hDN : D ≤ Subgroup.normalizer (T : Set K) := hTD ▸ le_sup_right
  have hTN : T ≤ Subgroup.normalizer (T : Set K) := hTD ▸ le_sup_left
  have hI : T ⊓ D = ⊥ := inf_eq_bot_of_odd hT hDodd
  let Q : Sylow 2 K := hT.toSylow hodd
  have hQ : (Q : Subgroup K) = T := IsPGroup.toSylow_coe hT hodd
  obtain ⟨t, hc0⟩ := h.exists_benderCore Q
  have hL0 := h.lemma_3_2 Q hc0.sq_eq_one hc0.not_mem
  have hrank := CFSG.Quasithin.H13.NQCat.isRankOneSylow_of_benderType h T hT hodd
  rw [hQ] at hc0 hL0
  set C : Subgroup K := cartan T t with hCdef
  have hCsup : T ⊔ C = Subgroup.normalizer (T : Set K) := hc0.sup_eq
  have hCinf : T ⊓ C = ⊥ := hc0.inf_eq
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hDC : Nat.card D = Nat.card C := by
    have h1 := card_normalizer_eq_mul T D hTD hI
    have h2 := card_normalizer_eq_mul T C hCsup hCinf
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_left hTpos h2
  have hcard : Nat.card D = (2 ^ n - 1) * e := by rw [hDC]; exact hc0.card_cartan
  have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    obtain ⟨-, -, hab⟩ := hrank
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ T ⊓ D :=
      ⟨hab x (hDN hx) y (hDN hy), D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)⟩
    rw [hI, Subgroup.mem_bot] at h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hαTD : ∀ x, α x ∈ D ↔ x ∈ D := hαD
  have hcases := h.cases'
  by_cases hi3 : i = 3
  ·
    subst hi3
    obtain ⟨he3, hn2⟩ : e = (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) ∧ 2 ≤ n := by
      rcases hcases with ⟨hi, -, -⟩ | ⟨hi, -, -⟩ | ⟨-, he, hn⟩
      · omega
      · omega
      · exact ⟨he, hn⟩
    have hspec := h.lemma_3_5_a_unitary Q
    have hsqQ : ∀ x ∈ (Q : Subgroup K), x * x ∈ rootCenter (Q : Subgroup K) :=
      fun x hx => h.sq_mem_rootCenter_unitary Q hx
    rw [hQ] at hspec hsqQ
    have hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ rootCenter T := by
      intro x hx y hy
      have := Subgroup.commutator_mem_commutator hx hy
      rw [hspec.1] at this
      simpa [commutatorElement_def] using this
    have hZcard : Nat.card (rootCenter T) = 2 ^ n := hL0.card_center
    have h2n : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hZne : rootCenter T ≠ T := by
      intro h0
      have h1 : Nat.card T = 2 ^ n := by rw [← h0]; exact hZcard
      have h3 := hc0.card_eq
      rw [h1] at h3
      have : (2 ^ n) ^ 3 = 2 ^ n * ((2 ^ n) * (2 ^ n)) := by ring
      nlinarith
    have hDA : D ≤ Subgroup.normalizer (T : Set K) := hDN
    have hDB : D ≤ Subgroup.normalizer ((rootCenter T : Subgroup K) : Set K) :=
      fun d hd => mem_normalizer_rootCenter (hDN hd)
    have hirr : ∀ W : Subgroup K, rootCenter T ≤ W → W ≤ T →
        (∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W) → W = rootCenter T ∨ W = T := by
      intro W hZW hWT hWinv
      have hWT' : ∀ u ∈ T, ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
        intro u hu w hw
        have h1 : u * w * u⁻¹ * w⁻¹ ∈ rootCenter T := hcommT u hu w (hWT hw)
        have : u * w * u⁻¹ = (u * w * u⁻¹ * w⁻¹) * w := by group
        rw [this]
        exact W.mul_mem (hZW h1) hw
      have hWC : ∀ c ∈ cartan T t, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
        intro c hcC w hw
        obtain ⟨u, huT, δ, hδD, hcu⟩ := exists_mul_of_sup hTD (cartan_le_borel T t hcC)
        have h1 : δ * w * δ⁻¹ ∈ W := hWinv δ hδD w hw
        have h2 := hWT' u huT _ h1
        rw [hcu]
        have : u * δ * w * (u * δ)⁻¹ = u * (δ * w * δ⁻¹) * u⁻¹ := by group
        rw [this]
        exact h2
      have := h.irreducible_unitary Q hc0.sq_eq_one (by rw [hQ]; exact hc0.not_mem) W
        (by rw [hQ]; exact hZW) (by rw [hQ]; exact hWT) (by rw [hQ]; exact hWC)
      rwa [hQ] at this
    have hfaith : ∀ d ∈ D, (∀ x ∈ T, d * x * d⁻¹ * x⁻¹ ∈ rootCenter T) → d = 1 := by
      intro d hdD hdz
      obtain ⟨u, huT, c', hc'C, hdu⟩ := exists_mul_of_sup hCsup (hDN hdD)
      have hc'd : c' = u⁻¹ * d := by rw [hdu]; group
      have hc'triv : ∀ x ∈ T, c' * x * c'⁻¹ * x⁻¹ ∈ rootCenter T := by
        intro x hx
        have ha := hdz x hx
        have hu1 := hcommT u⁻¹ (T.inv_mem huT) x hx
        have hu2 : u⁻¹ * (d * x * d⁻¹ * x⁻¹) * u = d * x * d⁻¹ * x⁻¹ := by
          have := (mem_rootCenter_iff.mp ha).2 u⁻¹ (T.inv_mem huT)
          calc u⁻¹ * (d * x * d⁻¹ * x⁻¹) * u = (u⁻¹ * (d * x * d⁻¹ * x⁻¹)) * u := rfl
            _ = ((d * x * d⁻¹ * x⁻¹) * u⁻¹) * u := by rw [this]
            _ = d * x * d⁻¹ * x⁻¹ := by group
        have key : c' * x * c'⁻¹ * x⁻¹ =
            (u⁻¹ * (d * x * d⁻¹ * x⁻¹) * u) * (u⁻¹ * x * u⁻¹⁻¹ * x⁻¹) := by
          rw [hc'd]; group
        rw [key, hu2]
        exact (rootCenter T).mul_mem ha hu1
      have hc'1 : c' = 1 := by
        by_contra hne
        apply hZne
        apply le_antisymm (rootCenter_le T)
        intro x hx
        have := h.fixedPointFree_unitary Q hc0.sq_eq_one (by rw [hQ]; exact hc0.not_mem)
          (by rw [hQ]; exact hc'C) hne (by rw [hQ]; exact hx)
          (by rw [hQ]; exact hc'triv x hx)
        rwa [hQ] at this
      have hdT : d ∈ T ⊓ D := ⟨by rw [hdu, hc'1, mul_one]; exact huT, hdD⟩
      rw [hI, Subgroup.mem_bot] at hdT
      exact hdT
    obtain ⟨hcyc, k, hk⟩ := singer_sections T (rootCenter T) D (rootCenter_le T) hZne hcommT
      hsqQ hDA hDB hDab hirr hfaith α hαT (alpha_rootCenter α hαT) hαTD
    have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 ∨ Nat.gcd 3 (2 ^ n + 1) = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left _ _)
    refine twist_finish D α hcyc hk hαodd hcomm (M := 2 * n) (c := Nat.gcd 3 (2 ^ n + 1))
      (by omega) hgcd (by omega) ?_
    rw [hcard, he3]
    have hdvd : Nat.gcd 3 (2 ^ n + 1) ∣ 2 ^ n + 1 := Nat.gcd_dvd_right _ _
    have h1 : Nat.gcd 3 (2 ^ n + 1) * ((2 ^ n - 1) * ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1))) =
        (2 ^ n - 1) * (2 ^ n + 1) := by
      rw [mul_left_comm, Nat.mul_div_cancel' hdvd]
    rw [h1, two_mul, pow_add]
    obtain ⟨b, hb⟩ : ∃ b, 2 ^ n = b + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hb]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  ·
    obtain ⟨he1, hn2⟩ : e = 1 ∧ 2 ≤ n := by
      rcases hcases with ⟨-, he, hn⟩ | ⟨-, he, a, ha, hn⟩ | ⟨hi, -, -⟩
      · exact ⟨he, hn⟩
      · exact ⟨he, by omega⟩
      · exact absurd hi hi3
    have hZcard : Nat.card (rootCenter T) = 2 ^ n := hL0.card_center
    have h2n : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hZne : (⊥ : Subgroup K) ≠ rootCenter T := by
      intro h0
      have h1 : Nat.card (rootCenter T) = 1 := by rw [← h0]; exact Subgroup.card_bot
      omega
    have hZcomm : ∀ x ∈ rootCenter T, ∀ y ∈ rootCenter T, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup K) := by
      intro x hx y hy
      rw [Subgroup.mem_bot]
      have h1 := (mem_rootCenter_iff.mp hx).2 y (rootCenter_le T hy)
      calc x * y * x⁻¹ * y⁻¹ = (x * y) * x⁻¹ * y⁻¹ := rfl
        _ = (y * x) * x⁻¹ * y⁻¹ := by rw [h1]
        _ = 1 := by group
    have hsq : ∀ x ∈ rootCenter T, x * x ∈ (⊥ : Subgroup K) := fun x hx =>
      Subgroup.mem_bot.mpr (hc0.center_sq x hx)
    have hDA : D ≤ Subgroup.normalizer ((rootCenter T : Subgroup K) : Set K) :=
      fun d hd => mem_normalizer_rootCenter (hDN hd)
    have hDB : D ≤ Subgroup.normalizer ((⊥ : Subgroup K) : Set K) := by
      intro d _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp [Subgroup.mem_bot]
    have hirr : ∀ W : Subgroup K, (⊥ : Subgroup K) ≤ W → W ≤ rootCenter T →
        (∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W) → W = ⊥ ∨ W = rootCenter T := by
      intro W _ hWZ hWinv
      by_cases hW : W = ⊥
      · exact Or.inl hW
      · right
        obtain ⟨⟨z0, hz0W'⟩, hz01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
        have hz01' : (z0 : K) ≠ 1 := fun h1 => hz01 (Subtype.ext h1)
        apply le_antisymm hWZ
        intro z hz
        by_cases hz1 : z = 1
        · rw [hz1]; exact W.one_mem
        obtain ⟨c, hcC, hczz⟩ := hL0.involutions_conj z0 (hWZ hz0W') hz01' z hz hz1
        obtain ⟨u, huT, δ, hδD, hcu⟩ := exists_mul_of_sup hTD (cartan_le_borel T t hcC)
        have hu : (u : K)⁻¹ * z0 * u = z0 := by
          have := (mem_rootCenter_iff.mp (hWZ hz0W')).2 u huT
          calc (u : K)⁻¹ * z0 * u = u⁻¹ * (z0 * u) := by group
            _ = u⁻¹ * (u * z0) := by rw [this]
            _ = z0 := by group
        have hzz : z = δ⁻¹ * z0 * δ := by
          rw [hczz, hcu]
          calc (u * δ)⁻¹ * z0 * (u * δ) = δ⁻¹ * (u⁻¹ * z0 * u) * δ := by group
            _ = δ⁻¹ * z0 * δ := by rw [hu]
        rw [hzz]
        have := hWinv δ⁻¹ (D.inv_mem hδD) z0 hz0W'
        simpa using this
    have hfaith : ∀ d ∈ D, (∀ x ∈ rootCenter T, d * x * d⁻¹ * x⁻¹ ∈ (⊥ : Subgroup K)) → d = 1 := by
      intro d hdD hdz
      obtain ⟨u, huT, c', hc'C, hdu⟩ := exists_mul_of_sup hCsup (hDN hdD)
      obtain ⟨⟨z, hzZ'⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hZne.symm)
      have hz1' : (z : K) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
      have hdzz := hdz z hzZ'
      rw [Subgroup.mem_bot] at hdzz
      have hdz' : d * z * d⁻¹ = z := by
        calc d * z * d⁻¹ = (d * z * d⁻¹ * z⁻¹) * z := by group
          _ = z := by rw [hdzz, one_mul]
      have hc'N : c' ∈ Subgroup.normalizer (T : Set K) := cartan_le_borel T t hc'C
      have hczmem : c' * z * c'⁻¹ ∈ rootCenter T := conj_mem_rootCenter hc'N hzZ'
      have hucomm : u * (c' * z * c'⁻¹) * u⁻¹ = c' * z * c'⁻¹ := by
        have := (mem_rootCenter_iff.mp hczmem).2 u huT
        calc u * (c' * z * c'⁻¹) * u⁻¹ = (u * (c' * z * c'⁻¹)) * u⁻¹ := rfl
          _ = ((c' * z * c'⁻¹) * u) * u⁻¹ := by rw [this]
          _ = c' * z * c'⁻¹ := by group
      have hc'z : c' * z * c'⁻¹ = z := by
        calc c' * z * c'⁻¹ = u * (c' * z * c'⁻¹) * u⁻¹ := hucomm.symm
          _ = (u * c') * z * (u * c')⁻¹ := by group
          _ = d * z * d⁻¹ := by rw [← hdu]
          _ = z := hdz'
      have hCeq : C = ⁅C, Subgroup.zpowers t⁆ := hL0.cartan_eq_commutator hi3
      have hex := hL0.regular z hzZ' hz1' z hzZ' hz1'
      have hone : (1 : K) ∈ ⁅C, Subgroup.zpowers t⁆ ∧ (z : K) = 1⁻¹ * z * 1 :=
        ⟨Subgroup.one_mem _, by simp⟩
      have hinv : c'⁻¹ ∈ ⁅C, Subgroup.zpowers t⁆ ∧ (z : K) = (c'⁻¹)⁻¹ * z * c'⁻¹ :=
        ⟨by rw [← hCeq]; exact C.inv_mem hc'C, by
          have : (c'⁻¹)⁻¹ * z * c'⁻¹ = c' * z * c'⁻¹ := by rw [inv_inv]
          rw [this, hc'z]⟩
      have : c'⁻¹ = 1 := hex.unique hinv hone
      have hc'1 : c' = 1 := inv_eq_one.mp this
      have hdT : d ∈ T ⊓ D := ⟨by rw [hdu, hc'1, mul_one]; exact huT, hdD⟩
      rw [hI, Subgroup.mem_bot] at hdT
      exact hdT
    obtain ⟨hcyc, k, hk⟩ := singer_sections (rootCenter T) ⊥ D bot_le hZne hZcomm hsq hDA hDB hDab
      hirr hfaith α (alpha_rootCenter α hαT) (fun x => by simp) hαTD
    exact twist_finish D α hcyc hk hαodd hcomm (M := n) (c := 1) (by omega) (Or.inl rfl)
      (by intro h3; omega) (by rw [hcard, he1]; simp)

end Main

section Card

variable {K : Type*} [Group K] [Finite K] {n i e : ℕ}

theorem bender_card_hall (h : BenderType K n i e) {T D : Subgroup K} (hT : IsPGroup 2 T)
    (hodd : ¬ 2 ∣ T.index) (hTD : T ⊔ D = Subgroup.normalizer (T : Set K))
    (hDodd : Odd (Nat.card D)) : Nat.card D = (2 ^ n - 1) * e := by
  have hI : T ⊓ D = ⊥ := inf_eq_bot_of_odd hT hDodd
  let Q : Sylow 2 K := hT.toSylow hodd
  have hQ : (Q : Subgroup K) = T := IsPGroup.toSylow_coe hT hodd
  obtain ⟨t, hc0⟩ := h.exists_benderCore Q
  rw [hQ] at hc0
  have hCsup : T ⊔ cartan T t = Subgroup.normalizer (T : Set K) := hc0.sup_eq
  have hCinf : T ⊓ cartan T t = ⊥ := hc0.inf_eq
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hDC : Nat.card D = Nat.card (cartan T t) := by
    have h1 := card_normalizer_eq_mul T D hTD hI
    have h2 := card_normalizer_eq_mul T (cartan T t) hCsup hCinf
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_left hTpos h2
  rw [hDC]
  exact hc0.card_cartan

end Card

section Complement

variable {K : Type*} [Group K]

noncomputable def complementEquiv {T D : Subgroup K}
    (hTD : T ⊔ D = Subgroup.normalizer (T : Set K)) (hI : T ⊓ D = ⊥) :
    ↥D ≃* (↥(Subgroup.normalizer (T : Set K)) ⧸
      T.subgroupOf (Subgroup.normalizer (T : Set K))) := by
  have hDN : D ≤ Subgroup.normalizer (T : Set K) := hTD ▸ le_sup_right
  refine MulEquiv.ofBijective
    ((QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set K)))).comp
      (Subgroup.inclusion hDN)) ⟨?_, ?_⟩
  · intro a b hab
    have h1 := QuotientGroup.eq.mp hab
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((Subgroup.inclusion hDN a)⁻¹ * Subgroup.inclusion hDN b : ↥(Subgroup.normalizer
        (T : Set K))) = ((a⁻¹ * b : ↥D) : K) := rfl
    have h3 : ((a⁻¹ * b : ↥D) : K) ∈ T ⊓ D := ⟨by rw [← h2]; exact h1, (a⁻¹ * b).2⟩
    rw [hI, Subgroup.mem_bot] at h3
    have h4 : a⁻¹ * b = 1 := Subtype.ext h3
    exact inv_mul_eq_one.mp h4
  · intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : K) ∈ T ⊔ D := by rw [hTD]; exact x.2
      obtain ⟨u, hu, d, hd, hxe⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hDN).mp hx
      refine ⟨⟨d, hd⟩, ?_⟩
      show (QuotientGroup.mk (Subgroup.inclusion hDN ⟨d, hd⟩) : _) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((Subgroup.inclusion hDN ⟨d, hd⟩)⁻¹ * x : ↥(Subgroup.normalizer (T : Set K))) : K) =
          d⁻¹ * (u * d) := by
        simp [hxe]
      rw [this]
      have hdN : d⁻¹ ∈ Subgroup.normalizer (T : Set K) := Subgroup.inv_mem _ (hDN hd)
      have := (Subgroup.mem_normalizer_iff.mp hdN u).mp hu
      simpa [mul_assoc] using this

end Complement

section CardCyclic

variable {K : Type*} [Group K] [Finite K] {n i e : ℕ}

theorem bender_hall_cyclic (h : BenderType K n i e) {T D : Subgroup K} (hT : IsPGroup 2 T)
    (hodd : ¬ 2 ∣ T.index) (hTD : T ⊔ D = Subgroup.normalizer (T : Set K))
    (hDodd : Odd (Nat.card D)) : IsCyclic ↥D := by
  have hI : T ⊓ D = ⊥ := inf_eq_bot_of_odd hT hDodd
  let Q : Sylow 2 K := hT.toSylow hodd
  have hQ : (Q : Subgroup K) = T := IsPGroup.toSylow_coe hT hodd
  obtain ⟨t, hc0⟩ := h.exists_benderCore Q
  rw [hQ] at hc0
  have hCsup : T ⊔ cartan T t = Subgroup.normalizer (T : Set K) := hc0.sup_eq
  have hCinf : T ⊓ cartan T t = ⊥ := hc0.inf_eq
  have e1 := complementEquiv hTD hI
  have e2 := complementEquiv hCsup hCinf
  exact (MulEquiv.isCyclic (e1.trans e2.symm)).mpr hc0.isCyclic

end CardCyclic


end CFSG.Quasithin.RonanF13
