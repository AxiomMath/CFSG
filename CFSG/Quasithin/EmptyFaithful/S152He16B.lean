module

public import CFSG.Quasithin.EmptyFaithful.S152He16A
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.He16

open CFSG.Quasithin

variable {X : Type*} [Group X] [Finite X]

theorem odd_centralizes_five {Y : Subgroup X} (hY5 : Nat.card Y = 5) {g : X}
    (hg : g ∈ Subgroup.normalizer (Y : Set X)) (hodd : Odd (orderOf g)) :
    ∀ y ∈ Y, g * y * g⁻¹ = y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hYne : Y ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hY5; omega
  obtain ⟨⟨a, haY⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord : orderOf a = 5 := by
    have hd : orderOf a ∣ Nat.card Y := by
      have := orderOf_dvd_natCard (⟨a, haY⟩ : ↥Y)
      rwa [← Subgroup.orderOf_coe] at this
    rw [hY5] at hd
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1'
    · exact h
  have hYz : Y = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haY)
      (by rw [Nat.card_zpowers, hord, hY5])).symm
  have hga : g * a * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hg a).mp haY
  rw [hYz] at hga
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hga
  have hgk : g * a * g⁻¹ = a ^ k := hk.symm
  have hpow : ∀ n : ℕ, g ^ n * a * (g ^ n)⁻¹ = a ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc g ^ (n + 1) * a * (g ^ (n + 1))⁻¹ = g * (g ^ n * a * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * a ^ (k ^ n) * g⁻¹ := by rw [ih]
        _ = (g * a * g⁻¹) ^ (k ^ n) := (conj_zpow).symm
        _ = a ^ (k ^ (n + 1)) := by rw [hgk, ← zpow_mul, pow_succ']
  have h1 : a ^ (1 : ℤ) = a ^ (k ^ orderOf g) := by
    have := hpow (orderOf g)
    rw [pow_orderOf_eq_one] at this
    simpa using this
  rw [zpow_eq_zpow_iff_modEq, hord] at h1
  have h2 : (1 : ZMod 5) = (k : ZMod 5) ^ orderOf g := by
    have := (ZMod.intCast_eq_intCast_iff (1 : ℤ) (k ^ orderOf g) 5).mpr (by exact_mod_cast h1)
    simpa using this
  have hk0 : (k : ZMod 5) ≠ 0 := by
    intro h0
    have h5 : (5 : ℤ) ∣ k := (ZMod.intCast_zmod_eq_zero_iff_dvd k 5).mp h0
    have : a ^ k = 1 := by
      rw [zpow_eq_one_iff_modEq, hord]
      exact (Int.modEq_zero_iff_dvd).mpr (by exact_mod_cast h5)
    rw [← hgk] at this
    exact ha1' (by simpa using this)
  have h4 : (k : ZMod 5) ^ 4 = 1 := by
    have := ZMod.pow_card_sub_one_eq_one hk0
    simpa using this
  have hcop : Nat.Coprime (orderOf g) (2 ^ 2) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have h5 : (k : ZMod 5) ^ Nat.gcd (orderOf g) 4 = 1 := pow_gcd_eq_one.mpr ⟨h2.symm, h4⟩
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, hcop.gcd_eq_one, pow_one] at h5
  have h6 : (k : ℤ) ≡ 1 [ZMOD 5] := by
    have := (ZMod.intCast_eq_intCast_iff k 1 5).mp (by simpa using h5)
    exact this
  have hak : a ^ k = a := by
    have : a ^ k = a ^ (1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hord]
      exact h6
    simpa using this
  intro y hy
  rw [hYz] at hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, hgk, hak]


theorem exists_gen_five {Y : Subgroup X} (hY5 : Nat.card Y = 5) :
    ∃ a ∈ Y, orderOf a = 5 ∧ Y = Subgroup.zpowers a := by
  have hYne : Y ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hY5; omega
  obtain ⟨⟨a, haY⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord : orderOf a = 5 := by
    have hd : orderOf a ∣ Nat.card Y := by
      have := orderOf_dvd_natCard (⟨a, haY⟩ : ↥Y)
      rwa [← Subgroup.orderOf_coe] at this
    rw [hY5] at hd
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1'
    · exact h
  exact ⟨a, haY, hord, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haY)
    (by rw [Nat.card_zpowers, hord, hY5])).symm⟩

theorem comm_mem_centralizer_five {Y : Subgroup X} [hYn : Y.Normal] (hY5 : Nat.card Y = 5) (x x' : X) :
    (x' * x)⁻¹ * (x * x') ∈ Subgroup.centralizer (Y : Set X) := by
  obtain ⟨a, haY, -, hYz⟩ := exists_gen_five hY5
  have hconj : ∀ z : X, ∃ i : ℤ, z * a * z⁻¹ = a ^ i := fun z => by
    have : z * a * z⁻¹ ∈ Y := hYn.conj_mem a haY z
    rw [hYz] at this
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp this
    exact ⟨i, hi.symm⟩
  obtain ⟨i, hi⟩ := hconj x
  obtain ⟨j, hj⟩ := hconj x'
  have e1 : (x * x') * a * (x * x')⁻¹ = a ^ (i * j) := by
    calc (x * x') * a * (x * x')⁻¹ = x * (x' * a * x'⁻¹) * x⁻¹ := by group
      _ = x * a ^ j * x⁻¹ := by rw [hj]
      _ = (x * a * x⁻¹) ^ j := conj_zpow.symm
      _ = a ^ (i * j) := by rw [hi, ← zpow_mul]
  have e2 : (x' * x) * a * (x' * x)⁻¹ = a ^ (i * j) := by
    calc (x' * x) * a * (x' * x)⁻¹ = x' * (x * a * x⁻¹) * x'⁻¹ := by group
      _ = x' * a ^ i * x'⁻¹ := by rw [hi]
      _ = (x' * a * x'⁻¹) ^ i := conj_zpow.symm
      _ = a ^ (i * j) := by rw [hj, ← zpow_mul, mul_comm]
  have hc : ((x' * x)⁻¹ * (x * x')) * a = a * ((x' * x)⁻¹ * (x * x')) := by
    calc ((x' * x)⁻¹ * (x * x')) * a = (x' * x)⁻¹ * ((x * x') * a * (x * x')⁻¹) * (x * x') := by group
      _ = (x' * x)⁻¹ * ((x' * x) * a * (x' * x)⁻¹) * (x * x') := by rw [e1, e2]
      _ = a * ((x' * x)⁻¹ * (x * x')) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [hYz] at hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((Commute.zpow_left (show Commute a ((x' * x)⁻¹ * (x * x')) from hc.symm) m)).eq

theorem central_of_normal_five {Y F : Subgroup X} [hYn : Y.Normal] [hFn : F.Normal] (hY5 : Nat.card Y = 5)
    (hF : ∀ x ∈ F, Odd (orderOf x)) (hperf : Group.IsPerfect (X ⧸ F)) : Y ≤ Subgroup.center X := by
  set N : Subgroup X := Subgroup.centralizer (Y : Set X) with hN
  have hFN : F ≤ N := fun f hf => by
    rw [hN, Subgroup.mem_centralizer_iff]
    intro y hy
    have := odd_centralizes_five hY5 (Subgroup.le_normalizer_of_normal (H := Y) (K := ⊤)
      (Subgroup.mem_top f)) (hF f hf) y hy
    calc y * f = (f * y * f⁻¹) * f := by rw [this]
      _ = f * y := by group
  have hperfN : Group.IsPerfect (X ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.map F N (MonoidHom.id X) hFN) (fun u => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨x, rfl⟩)
  have hcommq : ∀ u v : X ⧸ N, u * v = v * u := by
    intro u v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := N.inv_mem (comm_mem_centralizer_five hY5 x x')
    simpa [mul_assoc] using this
  have hbot : commutator (X ⧸ N) ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcommq a b)
  have hN' : N = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (x : X ⧸ N) ∈ commutator (X ⧸ N) := by
      rw [hperfN.commutator_eq_top]; exact Subgroup.mem_top _
    have h2 := hbot h1
    rw [Subgroup.mem_bot] at h2
    exact (QuotientGroup.eq_one_iff x).mp h2
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro g
  have : g ∈ N := hN' ▸ Subgroup.mem_top g
  exact ((Subgroup.mem_centralizer_iff.mp this) y hy).symm


theorem card_isElemAbelianOfRank {V : Type*} [Group V] {p n : ℕ}
    (h : IsElemAbelianOfRank p n V) : Nat.card V = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin n →
    ZMod p) ≃ (Fin n → ZMod p)), Nat.card_pi]
  simp [Nat.card_zmod]

theorem mem_pCore_of_mem_normal_nilpotent {p : ℕ} (hp : p.Prime) {N : Subgroup X}
    (hN : N.Normal) (hNnil : Group.IsNilpotent N) {x : X} (hxN : x ∈ N) {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ∈ CFSG.pCore p X := by
  have : Fact p.Prime := ⟨hp⟩
  have hxp : IsPGroup p (Subgroup.zpowers (⟨x, hxN⟩ : N)) := by
    have hdvd : Nat.card (Subgroup.zpowers (⟨x, hxN⟩ : N)) ∣ p ^ k := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact IsPGroup.of_card hj
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  have h1 : (⟨x, hxN⟩ : N) ∈ (S : Subgroup N) := hS (Subgroup.mem_zpowers _)
  exact Sylow.map_le_pCore hN hNnil p S ⟨⟨x, hxN⟩, h1, rfl⟩

theorem nq_core {X : Type} [Group X] [Finite X]
    (hcase : A36Case3 X ∨ A36Case4 X) (hex : A36Extra X)
    (hodd : ∀ x ∈ CFSG.fittingSubgroup X, Odd (orderOf x))
    (hperf : Group.IsPerfect (X ⧸ CFSG.fittingSubgroup X))
    {Y Q : Subgroup X} (hY5 : Nat.card Y = 5) (hYF : Y ≤ CFSG.fittingSubgroup X)
    (hFY : CFSG.fittingSubgroup X ≤ Subgroup.normalizer (Y : Set X))
    (hQY : Q ≤ Subgroup.normalizer (Y : Set X)) (hQ2 : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) :
    Y ≤ Subgroup.center X := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5F : 5 ∣ Nat.card (CFSG.fittingSubgroup X) := hY5 ▸ Subgroup.card_dvd_of_le hYF
  have hFC : ∀ f ∈ CFSG.fittingSubgroup X, ∀ y ∈ Y, f * y * f⁻¹ = y := fun f hf =>
    odd_centralizes_five hY5 (hFY hf) (hodd f hf)
  have hRF : CFSG.pCore 5 X ≤ CFSG.fittingSubgroup X := CFSG.pCore_le_fitting X 5
  have hYR : Y ≤ CFSG.pCore 5 X := by
    intro y hy
    refine mem_pCore_of_mem_normal_nilpotent Nat.prime_five inferInstance inferInstance (hYF hy)
      (k := 1) ?_
    have := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
    rw [hY5] at this
    simpa using congrArg Subtype.val this
  have hφex : ∃ φ : X →* SL25, Function.Surjective φ ∧ φ.ker = CFSG.fittingSubgroup X := by
    rcases hcase with ⟨p, hp, -, -, hFel, hnat⟩ | ⟨-, -, ⟨e⟩, -⟩
    · have hp5 : 5 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp (by
        have := card_isElemAbelianOfRank hFel
        rw [this] at h5F
        exact Nat.prime_five.dvd_of_dvd_pow h5F)
      subst hp5
      obtain ⟨-, ψ, hψs, hψk, -⟩ := hnat
      exact ⟨ψ, hψs, hψk⟩
    · refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup X)),
        e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  obtain ⟨φ, hφs, hφk⟩ := hφex
  have hXcard : Nat.card (CFSG.fittingSubgroup X) * 120 = Nat.card X := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hφk, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, sl2_five_card] at h1
    exact h1
  have hFodd : ¬ 2 ∣ Nat.card (CFSG.fittingSubgroup X) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have := hodd x x.2
    rw [Subgroup.orderOf_coe, hx] at this
    exact absurd this (by decide)
  have hQ8 : Nat.card Q = 8 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ2
    have h1 := Subgroup.card_mul_index Q
    rw [hn, ← hXcard] at h1
    rcases Nat.lt_trichotomy n 3 with hlt | heq | hgt
    · exfalso
      interval_cases n <;> omega
    · rw [hn, heq]; norm_num
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h2 : 2 ^ (m + 4) * Q.index = 16 * (2 ^ m * Q.index) := by ring
      omega
  let ψ : ↥Q →* SL25 := φ.comp Q.subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haF : (a : X) ∈ CFSG.fittingSubgroup X := by rw [← hφk]; exact ha
    obtain ⟨k, hk⟩ := hQ2 a
    have hk' : (a : X) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime (orderOf (a : X)) (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (hodd _ haF))
    exact Subtype.ext (orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk')))
  have key_ab : (∀ a ∈ CFSG.pCore 5 X, ∀ b ∈ CFSG.pCore 5 X, a * b = b * a) →
      Y ≤ Subgroup.center X := by
    intro hab
    exfalso
    obtain ⟨P, hsc, -, hP, hact⟩ := hex 5 Nat.prime_five h5F
    have hPab : ∀ a b : ↥P, a * b = b * a := fun a b =>
      Subtype.ext (Subtype.ext (hab _ a.1.2 _ b.1.2))
    have hPe : IsElemAbelianOfRank 5 2 ↥P := by
      rcases hP with h | ⟨hext, -, -⟩
      · exact h
      · exfalso
        have : CFSG.IsExtraspecial 5 ↥P := hext
        have hnt := CFSG.IsExtraspecial.quotient_nontrivial 5 ↥P
        obtain ⟨u, hu⟩ := exists_ne (1 : ↥P ⧸ Subgroup.center ↥P)
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
        exact hu ((QuotientGroup.eq_one_iff g).mpr
          (Subgroup.mem_center_iff.mpr fun h => hPab h g))
    obtain ⟨eP⟩ := hPe
    have : P.Characteristic := hsc.characteristic
    have hP'n : (P.map (CFSG.pCore 5 X).subtype).Normal := inferInstance
    let e : ↥(P.map (CFSG.pCore 5 X).subtype) ≃* Multiplicative (Fin 2 → ZMod 5) :=
      ((P.equivMapOfInjective (CFSG.pCore 5 X).subtype (CFSG.pCore 5 X).subtype_injective).symm).trans eP
    have hYP : Y ≤ P.map (CFSG.pCore 5 X).subtype := by
      intro y hy
      have hyR : y ∈ CFSG.pCore 5 X := hYR hy
      have hy5 : y ^ 5 = 1 := by
        have := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
        rw [hY5] at this
        simpa using congrArg Subtype.val this
      by_cases hy1 : y = 1
      · rw [hy1]; exact Subgroup.one_mem _
      · have hord : orderOf (⟨y, hyR⟩ : ↥(CFSG.pCore 5 X)) = 5 := by
          have hd : orderOf y ∣ 5 := orderOf_dvd_of_pow_eq_one hy5
          rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hy1
          · rw [Subgroup.orderOf_mk]; exact h
        have hcent : (⟨y, hyR⟩ : ↥(CFSG.pCore 5 X)) ∈ Subgroup.centralizer (P : Set ↥(CFSG.pCore 5 X)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro d _
          exact Subtype.ext (hab _ d.2 _ hyR)
        exact ⟨⟨y, hyR⟩, hsc.mem_of_orderOf_eq _ hcent hord, rfl⟩
    have hker : ∀ q ∈ Q, (∀ d ∈ P.map (CFSG.pCore 5 X).subtype, q * d * q⁻¹ = d) → q = 1 := by
      intro q hq hqd
      have hqF : q ∈ CFSG.fittingSubgroup X := (hact q).mp (fun d hd => by
        rw [hqd d hd, inv_mul_cancel]
        exact Subgroup.one_mem _)
      have h1 : φ q = 1 := by rw [← MonoidHom.mem_ker, hφk]; exact hqF
      have h2 : ψ ⟨q, hq⟩ = 1 := h1
      exact congrArg Subtype.val (hψinj (h2.trans (map_one ψ).symm))
    exact no_invariant_line e (fun q _ d hd => hP'n.conj_mem d hd q) hker hY5 hYP
      (fun q hq y hy => (Subgroup.mem_normalizer_iff.mp (hQY hq) y).mp hy) hQ8 ψ hψinj
  have key_ex : IsPOnePlusTwo 5 ↥(CFSG.pCore 5 X) → Y ≤ Subgroup.center X := by
    intro hext
    obtain ⟨hE, -, -⟩ := hext
    have : CFSG.IsExtraspecial 5 ↥(CFSG.pCore 5 X) := hE
    have hZ5 : Nat.card (Subgroup.center ↥(CFSG.pCore 5 X)) = 5 :=
      CFSG.IsExtraspecial.center_order_p 5 ↥(CFSG.pCore 5 X)
    have hZcard : Nat.card ((Subgroup.center ↥(CFSG.pCore 5 X)).map (CFSG.pCore 5 X).subtype) = 5 := by
      rw [Subgroup.card_map_of_injective (CFSG.pCore 5 X).subtype_injective, hZ5]
    have hYZ : Y ≤ (Subgroup.center ↥(CFSG.pCore 5 X)).map (CFSG.pCore 5 X).subtype := by
      intro y hy
      refine ⟨⟨y, hYR hy⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
      have h1 := hFC g (hRF g.2) y hy
      have h2 : (g : X) * y = y * (g : X) := by
        calc (g : X) * y = ((g : X) * y * (g : X)⁻¹) * (g : X) := by group
          _ = y * (g : X) := by rw [h1]
      exact Subtype.ext h2
    have hYeq : Y = (Subgroup.center ↥(CFSG.pCore 5 X)).map (CFSG.pCore 5 X).subtype :=
      Subgroup.eq_of_le_of_card_ge hYZ (by rw [hZcard, hY5])
    have hYn : Y.Normal := by
      rw [hYeq]
      infer_instance
    exact central_of_normal_five hY5 hodd hperf
  rcases hcase with h3 | h4
  · obtain ⟨p, hp, -, -, hFel, -⟩ := h3
    refine key_ab fun a ha b hb => ?_
    obtain ⟨e⟩ := hFel
    have hab : (⟨a, hRF ha⟩ : ↥(CFSG.fittingSubgroup X)) * ⟨b, hRF hb⟩ =
        ⟨b, hRF hb⟩ * ⟨a, hRF ha⟩ := by
      apply e.injective
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val hab
  · obtain ⟨-, -, -, hprime⟩ := h4
    rcases (hprime 5 Nat.prime_five h5F).2 with hext | ⟨n, -, ⟨e⟩⟩
    · exact key_ex hext
    · refine key_ab fun a ha b hb => ?_
      have hab : (⟨a, ha⟩ : ↥(CFSG.pCore 5 X)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
        apply e.injective
        rw [map_mul, map_mul, mul_comm]
      exact congrArg Subtype.val hab


theorem nq_core' {Γ : Type} [Group Γ] [Finite Γ] {L Y S : Subgroup Γ}
    (hcase : A36Case3 ↥L ∨ A36Case4 ↥L) (hex : A36Extra ↥L)
    (hodd : ∀ x ∈ CFSG.fittingSubgroup ↥L, Odd (orderOf x))
    (hperf : Group.IsPerfect (↥L ⧸ CFSG.fittingSubgroup ↥L))
    (hY5 : Nat.card Y = 5) (hYL : Y ≤ L)
    (hYF : Y ≤ (CFSG.fittingSubgroup ↥L).map L.subtype)
    (hFY : (CFSG.fittingSubgroup ↥L).map L.subtype ≤ Subgroup.normalizer (Y : Set Γ))
    (hSY : S ≤ Subgroup.normalizer (Y : Set Γ)) (hSL : QuasithinUnique.IsSylowTwoOf (S ⊓ L) L) :
    ∀ y ∈ Y, ∀ l ∈ L, y * l = l * y := by
  have hY₀5 : Nat.card (Y.subgroupOf L) = 5 := by
    rw [← hY5]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
  have hY₀F : Y.subgroupOf L ≤ CFSG.fittingSubgroup ↥L := by
    intro y hy
    obtain ⟨f, hf, hfy⟩ := hYF (Subgroup.mem_subgroupOf.mp hy)
    have : f = y := Subtype.ext hfy
    rwa [← this]
  have hFY₀ : CFSG.fittingSubgroup ↥L ≤ Subgroup.normalizer ((Y.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    fun f hf => Subgroup.le_normalizer_comap L.subtype (hFY ⟨f, hf, rfl⟩)
  have hQ₀Y : (S ⊓ L).subgroupOf L ≤ Subgroup.normalizer ((Y.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    fun q hq => Subgroup.le_normalizer_comap L.subtype (hSY (Subgroup.mem_inf.mp hq).1)
  have hcent := nq_core hcase hex hodd hperf hY₀5 hY₀F hFY₀ hQ₀Y
    (hSL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL.1).symm) hSL.2.2
  intro y hy l hl
  have hy' : (⟨y, hYL hy⟩ : ↥L) ∈ Y.subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
  have := Subgroup.mem_center_iff.mp (hcent hy') ⟨l, hl⟩
  exact (congrArg Subtype.val this).symm

end CFSG.Quasithin.He16
