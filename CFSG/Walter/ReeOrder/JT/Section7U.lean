module

public import CFSG.Walter.ReeOrder.JT.Section7T
public import CFSG.Walter.ReeOrder.JT.Section7S

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_card_le_two {R : Subgroup X} (hR : Nat.card R ≤ 2) {x : X}
    (hxR : x ∈ Subgroup.normalizer (R : Set X)) : ∀ y ∈ R, x * y = y * x := by
  classical
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, one_mul]
  have hxy : x * y * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxR y).mp hy
  have hxy1 : x * y * x⁻¹ ≠ 1 := fun h0 => hy1 (by
    have := congrArg (fun z => x⁻¹ * z * x) h0
    simpa [mul_assoc] using this)
  have hyo : orderOf y = 2 := by
    have hd : orderOf y ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hy
    have hle := Nat.le_of_dvd Nat.card_pos hd
    have h1 : orderOf y ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
    have h0 : 0 < orderOf y := orderOf_pos y
    omega
  have hRz : R = Subgroup.zpowers y :=
    (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hy)
      (by rw [Nat.card_zpowers, hyo]; exact hR)).symm
  rw [hRz] at hxy
  rcases (mem_zpowers_of_orderOf_eq_two hyo).mp hxy with h1 | h1
  · exact absurd h1 hxy1
  · calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h1]

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem commute_of_isPGroup_pi
    (c : TorusConf h) {R : Subgroup G} (hRF : R ≤ h.F)
    (hRq : Nat.card R = h.q) {H : Subgroup G} (hH : IsPGroup 3 H) (hRH : R ≤ H)
    {M : Subgroup G} (hMs : Group.IsSolvable M) (hHM : H ≤ M)
    (hMH : M ≤ Subgroup.normalizer (H : Set G)) (htM : h.t ∈ M) (hM4 : ¬ 4 ∣ Nat.card M)
    {r : ℕ} [hr : Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2) {K : Subgroup G} (hK : IsPGroup r K)
    (hKM : K ≤ M) (hMKH : M ≤ Subgroup.normalizer ((K ⊔ H : Subgroup G) : Set G)) {x : G}
    (hxM : x ∈ M) (hx : IsPGroup 3 (Subgroup.zpowers x))
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) :
    ∀ y ∈ K, x * y = y * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr7 := h.seven_le_of_pi hp3 hrq
  have hcop3 : ∀ {A B : Subgroup G}, IsPGroup r A → IsPGroup 3 B → Disjoint A B := by
    intro A B hA hB
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨a, ha⟩ := hA.exists_card_eq
    obtain ⟨b, hb⟩ := hB.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hr.out Nat.prime_three).mpr (by omega))
  have hcentH : ∀ {u : G}, u ∈ M → orderOf u = 2 → ∀ {S : Subgroup G}, IsPGroup 3 S → S ≤ M →
      S ≤ Subgroup.centralizer ({u} : Set G) → S ≤ H := by
    intro u huM hu S hS hSM hSu
    obtain ⟨m, hm⟩ := exists_conj_of_not_four_dvd hM4 (a := ⟨h.t, htM⟩) (b := ⟨u, huM⟩)
      (by rw [Subgroup.orderOf_mk]; exact h.orderOf_t) (by rw [Subgroup.orderOf_mk]; exact hu)
    have hm' : (m : G) * h.t * (m : G)⁻¹ = u := by simpa using congrArg Subtype.val hm
    have hS' : S.map (MulAut.conj (m : G)⁻¹).toMonoidHom ≤ R := by
      refine h.le_of_le_centralizer_t hp3 hRF hRq hH hRH (hS.map _) ?_ ?_
      · rintro _ ⟨s, hs, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hsu := Subgroup.mem_centralizer_singleton_iff.mp (hSu hs)
        rw [← hm'] at hsu
        change (m : G)⁻¹ * s * (m : G)⁻¹⁻¹ * h.t = h.t * ((m : G)⁻¹ * s * (m : G)⁻¹⁻¹)
        calc (m : G)⁻¹ * s * (m : G)⁻¹⁻¹ * h.t
            = (m : G)⁻¹ * (s * ((m : G) * h.t * (m : G)⁻¹)) * m := by group
          _ = (m : G)⁻¹ * (((m : G) * h.t * (m : G)⁻¹) * s) * m := by rw [hsu]
          _ = h.t * ((m : G)⁻¹ * s * (m : G)⁻¹⁻¹) := by group
      · rintro _ ⟨s, hs, rfl⟩
        change (m : G)⁻¹ * s * (m : G)⁻¹⁻¹ ∈ Subgroup.normalizer (H : Set G)
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMH m.2))
          (hMH (hSM hs))) (Subgroup.inv_mem _ (Subgroup.inv_mem _ (hMH m.2)))
    intro s hs
    have h1 : (m : G)⁻¹ * s * (m : G)⁻¹⁻¹ ∈ H := hRH (hS' ⟨s, hs, rfl⟩)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hMH m.2) _).mp h1
    have : (m : G) * ((m : G)⁻¹ * s * (m : G)⁻¹⁻¹) * (m : G)⁻¹ = s := by group
    rwa [this] at h2
  set L := K ⊔ H with hLdef
  have hKH : K ≤ Subgroup.normalizer (H : Set G) := hKM.trans hMH
  have hLcard : Nat.card L = Nat.card K * Nat.card H :=
    card_sup_eq_mul_of_disjoint hKH (hcop3 hK hH)
  obtain ⟨a, ha⟩ := hK.exists_card_eq
  obtain ⟨b, hb⟩ := hH.exists_card_eq
  have hLodd : ¬ 2 ∣ Nat.card L := by
    rw [hLcard, ha, hb]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr.out).mp
        (Nat.prime_two.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
        (Nat.prime_two.dvd_of_dvd_pow h2)
      omega
  have htL : Subgroup.zpowers h.t ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.zpowers_le).mpr (hMKH htM)
  have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  obtain ⟨R₁, hR₁⟩ := exists_sylow_normalized_of_coprime ht2 htL hLodd r
  have hKL : K ≤ L := le_sup_left
  have hKcard : Nat.card (K.subgroupOf L) = r ^ (Nat.card L).factorization r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hLcard, ha, hb,
      Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow hr.out, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => by
        have := (Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_three).mp (hr.out.dvd_of_dvd_pow hd)
        omega), add_zero]
  let KS : Sylow r L := Sylow.ofCard _ hKcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L KS R₁
  have hR₁map : (R₁ : Subgroup L).map L.subtype = K.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    ext z
    simp only [Subgroup.mem_map, MulDistribMulAction.toMonoidEnd_apply,
      MulDistribMulAction.toMonoidHom_apply, MulAut.smul_def, MulAut.conj_apply,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨g * ⟨k, hKL hk⟩ * g⁻¹, ⟨⟨k, hKL hk⟩, hk, rfl⟩, by simp⟩
  set u := (g : G)⁻¹ * h.t * (g : G) with hudef
  have huK : u ∈ Subgroup.normalizer (K : Set G) := by
    have h1 : h.t ∈ Subgroup.normalizer
        ((K.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G) :=
      hR₁map ▸ hR₁ (Subgroup.mem_zpowers h.t)
    have h2 := conj_mem_normalizer_map h1 ((g : G)⁻¹)
    rw [Subgroup.map_map] at h2
    have h3 : (MulAut.conj (g : G)⁻¹).toMonoidHom.comp (MulAut.conj (g : G)).toMonoidHom =
        MonoidHom.id G := by
      ext z
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, MonoidHom.id_apply]
      group
    rw [h3, Subgroup.map_id, inv_inv] at h2
    exact h2
  have hgM : (g : G) ∈ M := sup_le hKM hHM g.2
  have huM : u ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) htM) hgM
  have huo : orderOf u = 2 := by
    rw [hudef, show (g : G)⁻¹ * h.t * (g : G) = MulAut.conj (g : G)⁻¹ h.t by simp,
      MulEquiv.orderOf_eq, h.orderOf_t]
  have huu : u * u = 1 := by rw [← pow_two, ← huo, pow_orderOf_eq_one]
  set Y := Subgroup.normalizer (K : Set G) ⊓ M with hYdef
  have hYs : Group.IsSolvable Y := isSolvable_of_le inf_le_right hMs
  have huY : u ∈ Y := ⟨huK, huM⟩
  set π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩}
  have huπ : IsPiSubgroup π ((Subgroup.zpowers u).subgroupOf Y) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).mpr huY)).toEquiv,
      Nat.card_zpowers, huo] at hq
    left
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp hq)
  obtain ⟨Z, hZ, huZ⟩ := SolvableHall.solvable_hall_containment hYs π _ huπ
  set ZG := Z.map Y.subtype with hZGdef
  have hZGY : ZG ≤ Y := Subgroup.map_subtype_le Z
  have hZGcard : Nat.card ZG = Nat.card Z := Subgroup.card_map_of_injective Y.subtype_injective
  have huZG : u ∈ ZG := ⟨⟨u, huY⟩, huZ (by
    rw [Subgroup.mem_subgroupOf]; exact Subgroup.mem_zpowers u), rfl⟩
  have hZG4 : ¬ 4 ∣ Nat.card ZG := fun h4 =>
    hM4 (h4.trans (Subgroup.card_dvd_of_le (hZGY.trans inf_le_right)))
  have hZGπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card ZG → q = 2 ∨ q = 3 := by
    intro q hq hqd
    rw [hZGcard] at hqd
    rcases hZ.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqd with h1 | h1
    · left; exact congrArg Subtype.val h1
    · right; exact congrArg Subtype.val h1
  let S₃ : Sylow 3 ZG := default
  have hS₃idx : (S₃ : Subgroup ZG).index = 2 := by
    have hcm := (S₃ : Subgroup ZG).card_mul_index
    have hidx2 : ∀ q : ℕ, q.Prime → q ∣ (S₃ : Subgroup ZG).index → q = 2 := by
      intro q hq hqd
      rcases hZGπ q hq (hqd.trans (Subgroup.index_dvd_card _)) with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hqd) S₃.not_dvd_index
    have hidx0 : (S₃ : Subgroup ZG).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hidx0 (fun {d} hd hdd => hidx2 d hd hdd)
    set k := (S₃ : Subgroup ZG).index.primeFactorsList.length
    have hk1 : k ≤ 1 := by
      by_contra hk
      apply hZG4
      rw [← hcm]
      exact Dvd.dvd.mul_left (hpow ▸ (pow_dvd_pow 2 (by omega : 2 ≤ k))) _
    have hk0 : k ≠ 0 := by
      intro hk
      rw [hk, pow_zero] at hpow
      have h2 : 2 ∣ Nat.card ZG := by
        have := Subgroup.orderOf_dvd_natCard ZG huZG
        rwa [huo] at this
      rw [← hcm, hpow, mul_one, S₃.card_eq_multiplicity] at h2
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
        (Nat.prime_two.dvd_of_dvd_pow h2)) (by norm_num)
    have : k = 1 := by omega
    rw [hpow, this, pow_one]
  have hS₃n : (S₃ : Subgroup ZG).Normal := Subgroup.normal_of_index_eq_two hS₃idx
  set P := (S₃ : Subgroup ZG).map ZG.subtype with hPdef
  have hP3 : IsPGroup 3 P := S₃.isPGroup'.map _
  have hPY : P ≤ Y := (Subgroup.map_subtype_le _).trans hZGY
  have hPM : P ≤ M := hPY.trans inf_le_right
  have hPK : P ≤ Subgroup.normalizer (K : Set G) := hPY.trans inf_le_left
  have huP : u ∈ Subgroup.normalizer (P : Set G) := by
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨⟨u, huZG⟩ * z' * ⟨u, huZG⟩⁻¹, hS₃n.conj_mem z' hz' _, rfl⟩
  have hPcard : Nat.card P = 3 ^ (Nat.card Y).factorization 3 := by
    rw [hPdef, Subgroup.card_map_of_injective ZG.subtype_injective, S₃.card_eq_multiplicity,
      hZGcard]
    congr 1
    have hc := Z.card_mul_index
    rw [← hc, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (fun hd =>
        hZ.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ hd (Or.inr rfl)), add_zero]
  have h710 := h.lemma_7_10 hp3 c hrq hK hP3 hPK huo huK huP
  have hdecomp : ∀ y ∈ P, ∃ a ∈ H, ∃ n ∈ Subgroup.centralizer (K : Set G), y = a * n := by
    intro y hy
    set P₂ := P ⊓ Subgroup.centralizer (K : Set G)
    have hP₂odd : Odd (Nat.card P₂) := by
      obtain ⟨n, hn⟩ := (hP3.to_le (inf_le_left : P₂ ≤ P)).exists_card_eq
      rw [hn]
      exact Nat.odd_iff.mpr (by rw [Nat.pow_mod]; norm_num)
    have huP₂ : u ∈ Subgroup.normalizer (P₂ : Set G) :=
      Walter.Transitivity.le_normalizer_inf (A := Subgroup.zpowers u)
        ((Subgroup.zpowers_le).mpr huP)
        ((Subgroup.zpowers_le).mpr (mem_normalizer_of_conj_mem fun z hz => by
          rw [Subgroup.mem_centralizer_iff] at hz ⊢
          intro k hk
          have hk' : u⁻¹ * k * u ∈ K := by
            have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huK) k).mp hk
            simpa using this
          have := hz _ hk'
          calc k * (u * z * u⁻¹) = u * ((u⁻¹ * k * u) * z) * u⁻¹ := by group
            _ = u * (z * (u⁻¹ * k * u)) * u⁻¹ := by rw [this]
            _ = u * z * u⁻¹ * k := by group))
        (Subgroup.mem_zpowers u)
    have hyc : y⁻¹ * u * y * u⁻¹ ∈ P₂ := by
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp huP y).mp hy
        have h2 := P.mul_mem (P.inv_mem hy) this
        have e : y⁻¹ * u * y * u⁻¹ = y⁻¹ * (u * y * u⁻¹) := by group
        show y⁻¹ * u * y * u⁻¹ ∈ P
        rw [e]
        exact h2
      · have := h710 y⁻¹ (P.inv_mem hy)
        rwa [inv_inv] at this
    obtain ⟨n, hnP₂, hn⟩ := exists_mem_centralizer_coset hP₂odd huu huP₂ hyc
    have hcP : y * n⁻¹ ∈ P := P.mul_mem hy (P.inv_mem hnP₂.1)
    have hcH : y * n⁻¹ ∈ H := by
      have hz : Subgroup.zpowers (y * n⁻¹) ≤ H := hcentH huM huo
        (hP3.to_le ((Subgroup.zpowers_le).mpr hcP)) ((Subgroup.zpowers_le).mpr (hPM hcP))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr hn))
      exact hz (Subgroup.mem_zpowers _)
    exact ⟨y * n⁻¹, hcH, n, hnP₂.2, by group⟩
  have hxY : x ∈ Y := ⟨hxK, hxM⟩
  have hPYle : P.subgroupOf Y ≤ ⊤ := le_top
  let PS : Sylow 3 Y := Sylow.ofCard (P.subgroupOf Y) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv, hPcard])
  obtain ⟨S', hS'⟩ := (hx.comap_subtype (K := Y)).exists_le_sylow
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq Y S' PS
  have hwx : (w : G) * x * (w : G)⁻¹ ∈ P := by
    have hmem : w * ⟨x, hxY⟩ * w⁻¹ ∈ ((w • S' : Sylow 3 Y) : Subgroup Y) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨⟨x, hxY⟩, hS' (by rw [Subgroup.mem_comap]; exact Subgroup.mem_zpowers x), rfl⟩
    rw [hw] at hmem
    exact hmem
  obtain ⟨a₀, ha₀H, n₀, hn₀K, hxeq⟩ := hdecomp _ hwx
  have hwM : (w : G) ∈ M := (w : Y).2.2 |> fun h' => h'
  have hwK : (w : G) ∈ Subgroup.normalizer (K : Set G) := w.2.1
  set a₁ := (w : G)⁻¹ * a₀ * (w : G) with ha₁def
  set n₁ := (w : G)⁻¹ * n₀ * (w : G) with hn₁def
  have hxan : x = a₁ * n₁ := by
    have : x = (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * (w : G) := by group
    rw [this, hxeq, ha₁def, hn₁def]
    group
  have ha₁H : a₁ ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hMH hwM)) a₀).mp ha₀H
    simpa [ha₁def] using this
  have hn₁K : n₁ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hn₀K ⊢
    intro k hk
    have hk' : (w : G) * k * (w : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hwK k).mp hk
    have := hn₀K _ hk'
    calc k * n₁ = (w : G)⁻¹ * (((w : G) * k * (w : G)⁻¹) * n₀) * w := by rw [hn₁def]; group
      _ = (w : G)⁻¹ * (n₀ * ((w : G) * k * (w : G)⁻¹)) * w := by rw [this]
      _ = n₁ * k := by rw [hn₁def]; group
  intro y hy
  have hny : n₁ * y = y * n₁ := (Subgroup.mem_centralizer_iff.mp hn₁K y hy).symm
  have hcomm : x * y * x⁻¹ * y⁻¹ ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp hxK y).mp hy
    exact K.mul_mem this (K.inv_mem hy)
  have hcommH : x * y * x⁻¹ * y⁻¹ ∈ H := by
    have e : x * y * x⁻¹ * y⁻¹ = a₁ * (y * a₁⁻¹ * y⁻¹) := by
      rw [hxan]
      calc a₁ * n₁ * y * (a₁ * n₁)⁻¹ * y⁻¹ = a₁ * (n₁ * y) * n₁⁻¹ * a₁⁻¹ * y⁻¹ := by group
        _ = a₁ * (y * n₁) * n₁⁻¹ * a₁⁻¹ * y⁻¹ := by rw [hny]
        _ = a₁ * (y * a₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact H.mul_mem ha₁H ((Subgroup.mem_normalizer_iff.mp (hMH (hKM hy)) _).mp (H.inv_mem ha₁H))
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 :=
    Subgroup.disjoint_def.mp (hcop3 hK hH) hcomm hcommH
  calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
    _ = y * x := by rw [h1, one_mul]


theorem lemma_7_11_a
    (c : TorusConf h) :
    ∃ P : Sylow 3 G, c.C ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
      h.t ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
      ∃ R : Subgroup G, R ≤ P ∧ R ≤ h.F ∧ Nat.card R = h.q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hRF, hRq, hCR⟩ := h.exists_R hp3 c
  have hqpow : h.q = 3 ^ h.f := by rw [JTHyp.q_eq, hp3]
  have hR3 : IsPGroup 3 R := IsPGroup.of_card (n := h.f) (by rw [hRq, hqpow])
  have hf2 : 2 ≤ h.f := by
    have := h.five_lt
    rw [hp3] at this
    by_contra hf
    interval_cases hf' : h.f <;> norm_num at this
  have htN : h.t ∈ Subgroup.normalizer (R : Set G) :=
    mem_normalizer_of_conj_mem fun x hx => by
      rw [← h.commute_of_mem_F (hRF hx), mul_inv_cancel_right]
      exact hx
  set T := c.C ⊔ Subgroup.zpowers h.t with hTdef
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := sup_le hCR ((Subgroup.zpowers_le).mpr htN)
  set 𝒮 : Set (Subgroup G) :=
    {H | IsPGroup 3 H ∧ R ≤ H ∧ T ≤ Subgroup.normalizer (H : Set G)} with h𝒮
  obtain ⟨H, ⟨hH3, hRH, hTH⟩, hHmax⟩ := (Set.toFinite 𝒮).exists_maximal ⟨R, hR3, le_rfl, hTR⟩
  have hR1 : R ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hRq
    have := h.five_lt
    rw [← JTHyp.q_eq] at this
    omega
  have hH1 : H ≠ ⊥ := fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRH))
  set N := Subgroup.normalizer (H : Set G) with hNdef
  have hNs : Group.IsSolvable N := h.isSolvable_normalizer_of_isPGroup_three hp3 hH3 hH1
  set σ₀ : Set Nat.Primes := {r | r.val = 2 ∨ r.val = 3 ∨ r.val ∣ (h.q - 1) / 2} with hσ₀
  have hTσ : IsPiSubgroup σ₀ (T.subgroupOf N) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv] at hr
    have hTcard : Nat.card T = Nat.card c.C * 2 := by
      have hN : Subgroup.zpowers h.t ≤ Subgroup.normalizer (c.C : Set G) :=
        (Subgroup.zpowers_le).mpr (c.T₀_le_normalizer_C c.t_mem_T₀)
      have hdisj : Disjoint (Subgroup.zpowers h.t) c.C := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [Nat.card_zpowers, h.orderOf_t]
        have := c.card_C
        have hq8 := h.q_mod_eight_of_eq_three hp3
        exact Nat.Coprime.symm (Nat.odd_iff.mpr (by omega) |>.coprime_two_right)
      rw [hTdef, sup_comm, card_sup_eq_mul_of_disjoint hN hdisj, Nat.card_zpowers, h.orderOf_t,
        mul_comm]
    rw [hTcard] at hr
    rcases (Nat.Prime.dvd_mul r.2).mp hr with h1 | h1
    · right; right
      have := c.card_C
      have hq : (h.q - 1) / 2 = Nat.card c.C := by omega
      rw [hq]
      exact h1
    · left
      exact (Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_two).mp h1
  obtain ⟨M', hM', hTM'⟩ := SolvableHall.solvable_hall_containment hNs σ₀ _ hTσ
  set M := M'.map N.subtype with hMdef
  have hMN : M ≤ N := Subgroup.map_subtype_le M'
  have hMs : Group.IsSolvable M := isSolvable_of_le hMN hNs
  have hMcard : Nat.card M = Nat.card M' := Subgroup.card_map_of_injective N.subtype_injective
  have hTM : T ≤ M := fun x hx => ⟨⟨x, hTH hx⟩, hTM' (by rw [Subgroup.mem_subgroupOf]; exact hx),
    rfl⟩
  have htM : h.t ∈ M := hTM (Subgroup.mem_sup_right (Subgroup.mem_zpowers h.t))
  have hfac3 : (Nat.card M').factorization 3 = (Nat.card N).factorization 3 := by
    have hidx : ¬ 3 ∣ M'.index := fun hd =>
      hM'.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ hd (Or.inr (Or.inl rfl))
    rw [← M'.card_mul_index, Nat.factorization_mul Nat.card_pos.ne'
      Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  have hHM : H ≤ M := by
    obtain ⟨SM⟩ : Nonempty (Sylow 3 M') := inferInstance
    let SN : Sylow 3 N := Sylow.ofCard ((SM : Subgroup M').map M'.subtype) (by
      rw [Subgroup.card_map_of_injective M'.subtype_injective, SM.card_eq_multiplicity, hfac3])
    have hHN : (H.subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hHS : H.subgroupOf N ≤ SN :=
      IsPGroup.le_sylow_of_normal (N := H.subgroupOf N) (hH3.comap_subtype (K := N)) SN
    intro x hx
    have hxN : x ∈ N := Subgroup.le_normalizer hx
    obtain ⟨y, -, hy⟩ := hHS (show (⟨x, hxN⟩ : N) ∈ H.subgroupOf N from hx)
    exact ⟨⟨x, hxN⟩, hy ▸ y.2, rfl⟩
  have hMH : M ≤ Subgroup.normalizer (H : Set G) := hMN
  have hM9 : 9 ∣ Nat.card M := by
    have := Subgroup.card_dvd_of_le (hRH.trans hHM)
    rw [hRq, hqpow] at this
    exact (pow_dvd_pow 3 hf2).trans this
  have hM4 : ¬ 4 ∣ Nat.card M := fun h4 => h.not_nine_dvd_card hp3 hMs h4 hM9
  set O := (pCore 3 M).map M.subtype with hOdef
  have hOp : IsPGroup 3 O := pCore_isPGroup.map _
  have hHO : H ≤ O := by
    have hHn : (H.subgroupOf M).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hMH g.2) x).mp hx
    have hle : H.subgroupOf M ≤ pCore 3 M :=
      le_sSup ⟨hHn, hH3.comap_subtype (K := M)⟩
    intro x hx
    exact ⟨⟨x, hHM hx⟩, hle hx, rfl⟩
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := by
    intro x hx
    have hmem : (⟨x, hx⟩ : M) ∈ Subgroup.normalizer (pCore 3 M : Set M) := by
      have := pCore_normal (p := 3) (G := M)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map M.subtype ⟨_, hmem, rfl⟩
  have hOH : O = H := le_antisymm (hHmax ⟨hOp, hRH.trans hHO, hTM.trans hMO⟩ hHO) hHO
  have hcomm : ∀ x : M, IsPGroup 3 (Subgroup.zpowers x) → ∀ q : ℕ, q.Prime → q ≠ 3 →
      ∀ R' : Subgroup M, IsPGroup q R' → (R' ⊔ pCore 3 M).Normal →
        x ∈ Subgroup.normalizer (R' : Set M) → ∀ y ∈ R', x * y = y * x := by
    intro x hx q hq hq3 R' hR' hR'n hxR'
    have : Fact q.Prime := ⟨hq⟩
    by_cases hq2 : q = 2
    · subst hq2
      refine commute_of_card_le_two ?_ hxR'
      obtain ⟨k, hk⟩ := hR'.exists_card_eq
      have hk1 : k ≤ 1 := by
        by_contra hk1
        apply hM4
        have := Subgroup.card_dvd_of_le (le_top : R' ≤ ⊤)
        rw [Subgroup.card_top, hk] at this
        exact (pow_dvd_pow 2 (by omega : 2 ≤ k)).trans this
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    by_cases hqπ : q ∣ (h.q - 1) / 2
    ·
      set K := R'.map M.subtype with hKdef
      have hKM : K ≤ M := Subgroup.map_subtype_le R'
      have hKH : (R' ⊔ pCore 3 M).map M.subtype = K ⊔ H := by
        rw [Subgroup.map_sup, ← hOdef, hOH]
      have hMKH : M ≤ Subgroup.normalizer ((K ⊔ H : Subgroup G) : Set G) := by
        intro g hg
        have hmem : (⟨g, hg⟩ : M) ∈ Subgroup.normalizer ((R' ⊔ pCore 3 M : Subgroup M) : Set M) := by
          rw [Subgroup.normalizer_eq_top]
          exact Subgroup.mem_top _
        rw [← hKH]
        exact Subgroup.le_normalizer_map M.subtype ⟨_, hmem, rfl⟩
      have hxK : (x : G) ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.le_normalizer_map M.subtype ⟨x, hxR', rfl⟩
      have hxG : IsPGroup 3 (Subgroup.zpowers (x : G)) := by
        have := hx.map M.subtype
        rwa [MonoidHom.map_zpowers] at this
      have key := h.commute_of_isPGroup_pi hp3 c hRF hRq hH3 hRH hMs hHM hMH htM hM4 hqπ
        (hR'.map M.subtype) hKM hMKH x.2 hxG hxK
      intro y hy
      exact Subtype.ext (key y ⟨y, hy, rfl⟩)
    ·
      have hR'1 : R' = ⊥ := by
        obtain ⟨k, hk⟩ := hR'.exists_card_eq
        rcases k with _ | k
        · rw [pow_zero] at hk
          exact Subgroup.card_eq_one.mp hk
        · exfalso
          have hqM : q ∣ Nat.card M' := by
            rw [← hMcard]
            have := Subgroup.card_dvd_of_le (le_top : R' ≤ ⊤)
            rw [Subgroup.card_top, hk] at this
            exact (dvd_pow_self q (by omega)).trans this
          rcases hM'.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqM with h1 | h1 | h1
          · exact hq2 h1
          · exact hq3 h1
          · exact hqπ h1
      intro y hy
      rw [hR'1, Subgroup.mem_bot] at hy
      rw [hy, mul_one, one_mul]
  obtain ⟨SM⟩ : Nonempty (Sylow 3 M) := inferInstance
  have hSM := sylow_le_pCore_of_centralize_normal hMs hcomm SM
  have hHcard : Nat.card H = 3 ^ (Nat.card N).factorization 3 := by
    apply le_antisymm
    · obtain ⟨SN, hSN⟩ := (hH3.comap_subtype (K := N)).exists_le_sylow
      have := Subgroup.card_le_of_le hSN
      rwa [SN.card_eq_multiplicity, ← Subgroup.card_map_of_injective N.subtype_injective,
        Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact Subgroup.le_normalizer)]
        at this
    · have h1 := Subgroup.card_le_of_le hSM
      rw [SM.card_eq_multiplicity, hMcard, hfac3, ← Subgroup.card_map_of_injective M.subtype_injective,
        ← hOdef, hOH] at h1
      exact h1
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_maximal hH3 fun Q hQ3 hHQ hQN => by
    refine (Subgroup.eq_of_le_of_card_ge hHQ ?_).symm
    rw [hHcard]
    obtain ⟨SN, hSN⟩ := (hQ3.comap_subtype (K := N)).exists_le_sylow
    have := Subgroup.card_le_of_le hSN
    rwa [SN.card_eq_multiplicity, ← Subgroup.card_map_of_injective N.subtype_injective,
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hQN)] at this
  refine ⟨P, ?_, ?_, R, ?_, hRF, hRq⟩
  · rw [hP]
    exact le_sup_left.trans hTH
  · rw [hP]
    exact hTH (Subgroup.mem_sup_right (Subgroup.mem_zpowers h.t))
  · rw [hP]
    exact hRH

end JTHyp

end CFSG.Walter.JT
