module

public import CFSG.Walter.W67.Section6.JRSylow
public import CFSG.Walter.W67.JR.Ree
public import CFSG.Walter.W67.W1Prop24C

public section

namespace CFSG.Walter.W67

namespace Sec6

open scoped MatrixGroups

variable {L : Type} [Group L] [Finite L]

theorem card_modEq_card_inf_centralizer {ℓ : ℕ} [Fact ℓ.Prime] {S : Subgroup L} {g : L}
    (hg : g ∈ Subgroup.normalizer (S : Set L)) {k : ℕ} (hgk : g ^ ℓ ^ k = 1) :
    Nat.card S ≡ Nat.card ↥(S ⊓ Subgroup.centralizer ({g} : Set L)) [MOD ℓ] := by
  have hmem : ∀ s ∈ S, g * s * g⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.mp hg s).mp hs
  have hmem' : ∀ s ∈ S, g⁻¹ * s * g ∈ S := fun s hs => by
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * s * g)).mpr (by simpa [mul_assoc] using hs)
    exact this
  let σ : MulAut S :=
    { toFun := fun s => ⟨g * s * g⁻¹, hmem s s.2⟩
      invFun := fun s => ⟨g⁻¹ * s * g, hmem' s s.2⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
  have hσn : ∀ (n : ℕ) (s : S), ((σ ^ n) s : L) = g ^ n * s * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [pow_succ', MulAut.mul_apply]
      change g * ((σ ^ n) s : L) * g⁻¹ = _
      rw [ih, pow_succ']
      group
  have hσk : σ ^ ℓ ^ k = 1 := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [hσn, hgk, one_mul, inv_one, mul_one]
    rfl
  have h := Huppert.card_fixedSubgroup_modEq (p := ℓ) hσk
  have hcard : Nat.card (Huppert.fixedSubgroup σ) =
      Nat.card ↥(S ⊓ Subgroup.centralizer ({g} : Set L)) := by
    have heq : (Huppert.fixedSubgroup σ).map S.subtype =
        S ⊓ Subgroup.centralizer ({g} : Set L) := by
      ext x
      simp only [Subgroup.mem_map, Huppert.mem_fixedSubgroup, Subgroup.coe_subtype,
        Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨s, hs, rfl⟩
        refine ⟨s.2, ?_⟩
        have h1 := congrArg Subtype.val hs
        change g * (s : L) * g⁻¹ = s at h1
        calc (s : L) * g = (g * s * g⁻¹) * g := by rw [h1]
          _ = g * s := by group
      · rintro ⟨hxS, hx⟩
        refine ⟨⟨x, hxS⟩, Subtype.ext ?_, rfl⟩
        change g * x * g⁻¹ = x
        rw [← hx]
        group
    rw [← heq, Subgroup.card_map_of_injective S.subtype_injective]
  rwa [hcard] at h

theorem card_eq_1512 (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3)
    (hns : ¬ Group.IsSolvable L) : Nat.card L = 1512 := by
  have h := (hR L hL (by rw [hq]; norm_num)).1.2.1 hns
  rw [h, hq]
  norm_num

theorem pPrimeCore_eq_bot_of_R3
    (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3) :
    CFSG.pPrimeCore 2 L = ⊥ := by
  obtain ⟨-, ⟨hR2a, -⟩, -⟩ := hR L hL (by rw [hq]; norm_num)
  obtain ⟨fr⟩ := Frame.nonempty L hL.toHyp
  have hle := fr.pPrimeCore_le_E_of_three hq (fun N hN => hL.index_ne_two N hN)
  have hCS : fr.CS = fr.S := (hR2a fr.S).1
  have hE : fr.E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ (fr.S : Subgroup L) := hCS ▸ fr.E_le_CS hx
    exact eq_one_of_odd_of_isPGroup fr.S.isPGroup' hxS (odd_orderOf_of_mem_oddPart hx)
  rw [eq_bot_iff, ← hE]
  exact hle

theorem eq_bot_of_normal_odd
    (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3) (N : Subgroup L)
    (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rw [eq_bot_iff, ← pPrimeCore_eq_bot_of_R3 hR hL hq]
  exact le_sSup ⟨hN, Nat.coprime_two_left.mpr hodd⟩

theorem card_centralizer_of_orderOf_two (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3) {t : L}
    (ht : orderOf t = 2) : Nat.card (Subgroup.centralizer ({t} : Set L)) = 24 := by
  obtain ⟨-, ⟨-, hR2b⟩, -⟩ := hR L hL (by rw [hq]; norm_num)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hR2b hL.J t hL.orderOf_J ht)
  rw [← hc, ← cj_centralizer_singleton, card_cj, hL.centralizer_eq]
  have hK : Nat.card hL.K = 12 := by
    have := hL.toHyp.card_K_of_three hq
    exact this
  have hJN : Subgroup.zpowers hL.J ≤ Subgroup.normalizer (hL.K : Set L) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hL.le_centralizer hk))
  have h := Sec52.card_sup_mul_card_inf hJN
  have hinf : hL.K ⊓ Subgroup.zpowers hL.J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxJ⟩ := Subgroup.mem_inf.mp hx
    rcases eq_one_or_eq_of_mem_zpowers hL.orderOf_J hxJ with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxK) hL.J_not_mem
  rw [hinf, Subgroup.card_bot, mul_one, hK, Nat.card_zpowers, hL.orderOf_J] at h
  rw [h]

theorem not_mem_centralizer_of_seven (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3) {x t : L}
    (hx : orderOf x = 7) (ht : orderOf t = 2) : x ∉ Subgroup.centralizer ({t} : Set L) := by
  intro hxt
  have h1 := Subgroup.orderOf_dvd_natCard _ hxt
  rw [card_centralizer_of_orderOf_two hR hL hq ht, hx] at h1
  norm_num at h1

theorem card_normalizer_seven
    (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3)
    (hns : ¬ Group.IsSolvable L) {P : Subgroup L} (hPc : Nat.card P = 7) :
    Nat.card (Subgroup.normalizer (P : Set L)) = 42 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hL1512 := card_eq_1512 hR hL hq hns
  have hfac : (Nat.card L).factorization 7 = 1 := by
    rw [hL1512, show (1512 : ℕ) = 7 ^ 1 * 216 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7)]
    simp only [Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  set S : Sylow 7 L := Sylow.ofCard P (by rw [hPc, hfac, pow_one]) with hSdef
  have hSP : (S : Subgroup L) = P := rfl
  have hn := Sylow.card_eq_index_normalizer S
  have hmod := card_sylow_modEq_one 7 L
  have hidx : (Subgroup.normalizer (P : Set L)).index = Nat.card (Sylow 7 L) := by
    rw [hn, ← hSP]
    rfl
  have hmul := Subgroup.card_mul_index (Subgroup.normalizer (P : Set L))
  rw [hidx, hL1512] at hmul
  have h7 : 7 ∣ Nat.card (Subgroup.normalizer (P : Set L)) :=
    hPc ▸ Subgroup.card_dvd_of_le Subgroup.le_normalizer
  obtain ⟨m, hm⟩ := h7
  set n := Nat.card (Sylow 7 L) with hndef
  have hn216 : n ∣ 216 := by
    refine ⟨m, ?_⟩
    rw [hm] at hmul
    have h7 : 7 * (n * m) = 7 * 216 := by linarith [hmul]
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h7).symm
  have hn7 : n % 7 = 1 := hmod
  have hn3 : n = 1 ∨ n = 8 ∨ n = 36 := by
    have hmem : n ∈ (Nat.divisors 216).filter (fun k => k % 7 = 1) :=
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hn216, by norm_num⟩, hn7⟩
    have heq : (Nat.divisors 216).filter (fun k => k % 7 = 1) = {1, 8, 36} := by decide
    rw [heq] at hmem
    simpa using hmem
  rcases hn3 with h1 | h8 | h36
  ·
    exfalso
    have htop : Subgroup.normalizer (P : Set L) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hL1512]
      rw [h1] at hmul
      omega
    have hnorm : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hbot := eq_bot_of_normal_odd hR hL hq P hnorm (by rw [hPc]; decide)
    rw [hbot, Subgroup.card_bot] at hPc
    exact absurd hPc (by norm_num)
  ·
    exfalso
    set φ := MulAction.toPermHom L (Sylow 7 L)
    have hker : φ.ker ≤ Subgroup.normalizer (P : Set L) := by
      intro g hg
      have : g • S = S := by
        have := congrArg (fun σ : Equiv.Perm (Sylow 7 L) => σ S) (MonoidHom.mem_ker.mp hg)
        exact this
      rw [← hSP]
      exact Sylow.smul_eq_iff_mem_normalizer.mp this
    have hNodd : Odd (Nat.card (Subgroup.normalizer (P : Set L))) := by
      have : Nat.card (Subgroup.normalizer (P : Set L)) = 189 := by
        rw [h8] at hmul; omega
      rw [this]; decide
    have hkodd : Odd (Nat.card φ.ker) :=
      Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hker)
    have hkbot := eq_bot_of_normal_odd hR hL hq φ.ker inferInstance hkodd
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkbot
    have hdvd : Nat.card L ∣ Nat.card (Equiv.Perm (Sylow 7 L)) := by
      have h1 := Subgroup.card_subgroup_dvd_card φ.range
      rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h1
    rw [Nat.card_perm, ← hndef, h8, hL1512] at hdvd
    exact absurd hdvd (by decide)
  · rw [h36] at hmul
    omega

theorem exists_three_seven (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3) :
    ∃ x d : L, orderOf x = 7 ∧ orderOf d = 3 ∧
      d ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup L) : Set L) ∧ d * x ≠ x * d := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, ⟨hR2a, -⟩, -⟩ := hR L hL (by rw [hq]; norm_num)
  obtain ⟨S₂⟩ := (inferInstance : Nonempty (Sylow 2 L))
  obtain ⟨hCS, hNS⟩ := hR2a S₂
  have hS8 : Nat.card (S₂ : Subgroup L) = 8 := hL.card_sylow S₂
  set N := Subgroup.normalizer ((S₂ : Subgroup L) : Set L) with hNdef
  have hSN : (S₂ : Subgroup L) ≤ N := Subgroup.le_normalizer
  have hrel : (S₂ : Subgroup L).relIndex N = 21 := by
    have h := Subgroup.relIndex_mul_card (H := (S₂ : Subgroup L)) (K := N)
    rw [inf_eq_left.mpr hSN, hS8, hNS] at h
    omega
  obtain ⟨F, hFN, -, -, hcard⟩ := exists_complement_in hSN le_rfl (by rw [hrel, hS8]; decide)
  have hF21 : Nat.card F = 21 := by rw [hS8, hNS] at hcard; omega
  obtain ⟨P₇, hP₇n, hP₇c⟩ := exists_normal_card_seven hF21
  have hP₇cyc : IsCyclic P₇ := isCyclic_of_prime_card hP₇c
  obtain ⟨x₀, hgen⟩ := hP₇cyc.exists_generator
  have hox₀ : orderOf x₀ = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hP₇c]
  obtain ⟨d', hod'⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 (by rw [hF21]; norm_num)
  set x : L := ((x₀ : F) : L) with hxdef
  set d : L := (d' : L) with hddef
  have hox : orderOf x = 7 := by rw [hxdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hox₀]
  have hod : orderOf d = 3 := by rw [hddef, Subgroup.orderOf_coe, hod']
  have hzx : Subgroup.zpowers x = P₇.map F.subtype := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      exact ⟨(x₀ : F), x₀.2, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨w, hw⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h1 := congrArg (fun z : P₇ => ((z : F) : L)) hk
      simpa [hxdef] using h1
  have hdN : d ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup L) : Set L) := by
    rw [hzx, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨d' * w * d'⁻¹, hP₇n.conj_mem w hw d', by simp [hddef]⟩
    · rintro ⟨w, hw, hwz⟩
      refine ⟨d'⁻¹ * w * d', ?_, ?_⟩
      · have := hP₇n.conj_mem w hw d'⁻¹
        simpa using this
      · have h1 : d * z * d⁻¹ = (w : L) := hwz.symm
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hddef, ← h1]
        group
  refine ⟨x, d, hox, hod, hdN, fun hdx => ?_⟩
  have hxN : x ∈ N := hFN (x₀ : F).2
  have hdN' : d ∈ N := hFN d'.2
  have hmodd := card_modEq_card_inf_centralizer (ℓ := 3) (k := 1) hdN'
    (by rw [pow_one, ← hod, pow_orderOf_eq_one])
  have hmodx := card_modEq_card_inf_centralizer (ℓ := 7) (k := 1) hxN
    (by rw [pow_one, ← hox, pow_orderOf_eq_one])
  rw [hS8] at hmodd hmodx
  have hnot : ∀ g : L, Odd (orderOf g) → orderOf g ≠ 1 →
      ¬ (S₂ : Subgroup L) ≤ Subgroup.centralizer ({g} : Set L) := by
    intro g hgodd hg1 hle
    have hgC : g ∈ Subgroup.centralizer ((S₂ : Subgroup L) : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)
    rw [hCS] at hgC
    have := eq_one_of_odd_of_isPGroup S₂.isPGroup' hgC hgodd
    rw [this, orderOf_one] at hg1
    exact hg1 rfl
  have hcard8 : ∀ g : L, Odd (orderOf g) → orderOf g ≠ 1 →
      Nat.card ↥((S₂ : Subgroup L) ⊓ Subgroup.centralizer ({g} : Set L)) ∈
        ({1, 2, 4} : Finset ℕ) := by
    intro g hgodd hg1
    have hdvd : Nat.card ↥((S₂ : Subgroup L) ⊓ Subgroup.centralizer ({g} : Set L)) ∣ 8 :=
      hS8 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne8 : Nat.card ↥((S₂ : Subgroup L) ⊓ Subgroup.centralizer ({g} : Set L)) ≠ 8 := by
      intro h8
      apply hnot g hgodd hg1
      have : (S₂ : Subgroup L) ⊓ Subgroup.centralizer ({g} : Set L) = (S₂ : Subgroup L) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hS8])
      rw [← this]
      exact inf_le_right
    have hmem : Nat.card ↥((S₂ : Subgroup L) ⊓ Subgroup.centralizer ({g} : Set L)) ∈
        Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    omega
  have hCd2 : Nat.card ↥((S₂ : Subgroup L) ⊓ Subgroup.centralizer ({d} : Set L)) = 2 := by
    have h1 := hcard8 d (by rw [hod]; decide) (by rw [hod]; norm_num)
    unfold Nat.ModEq at hmodd
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hCx1 : Nat.card ↥((S₂ : Subgroup L) ⊓ Subgroup.centralizer ({x} : Set L)) = 1 := by
    have h1 := hcard8 x (by rw [hox]; decide) (by rw [hox]; norm_num)
    unfold Nat.ModEq at hmodx
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  set Cd := (S₂ : Subgroup L) ⊓ Subgroup.centralizer ({d} : Set L) with hCddef
  set Cx := (S₂ : Subgroup L) ⊓ Subgroup.centralizer ({x} : Set L) with hCxdef
  obtain ⟨y, hyCd, hy1⟩ := (Subgroup.bot_or_exists_ne_one Cd).resolve_left (by
    intro h
    rw [h, Subgroup.card_bot] at hCd2
    exact absurd hCd2 (by norm_num))
  have hdx' : x⁻¹ * d = d * x⁻¹ := by
    calc x⁻¹ * d = x⁻¹ * (d * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * d) * x⁻¹ := by rw [hdx]
      _ = d * x⁻¹ := by group
  have hxy : x * y * x⁻¹ ∈ Cd := by
    obtain ⟨hyS, hyd⟩ := Subgroup.mem_inf.mp hyCd
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hxN y).mp hyS, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyd ⊢
    calc x * y * x⁻¹ * d = x * y * (x⁻¹ * d) := by group
      _ = x * y * (d * x⁻¹) := by rw [hdx']
      _ = x * (y * d) * x⁻¹ := by group
      _ = x * (d * y) * x⁻¹ := by rw [hyd]
      _ = (x * d) * y * x⁻¹ := by group
      _ = (d * x) * y * x⁻¹ := by rw [hdx]
      _ = d * (x * y * x⁻¹) := by group
  have hxy' : x * y * x⁻¹ = y := by
    have hCdy : Cd = Subgroup.zpowers y := by
      have hoy : orderOf y = 2 := by
        have h1 : orderOf y ∣ 2 := hCd2 ▸ Subgroup.orderOf_dvd_natCard Cd hyCd
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hy1
        · exact h
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyCd)
      rw [hCd2, Nat.card_zpowers, hoy]
    rw [hCdy] at hxy
    have hoy2 : y * y = 1 := by
      have h1 : orderOf y ∣ 2 := hCd2 ▸ Subgroup.orderOf_dvd_natCard Cd hyCd
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    rcases eq_one_or_eq_of_mem_zpowers (by
      have h1 : orderOf y ∣ 2 := hCd2 ▸ Subgroup.orderOf_dvd_natCard Cd hyCd
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1
      · exact h) hxy with h | h
    · exfalso
      apply hy1
      have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [this, h]
      group
    · exact h
  have hyCx : y ∈ Cx := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hyCd).1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * x = x * y * x⁻¹ * x := by rw [hxy']
      _ = x * y := by group
  rw [Subgroup.card_eq_one] at hCx1
  rw [hCx1, Subgroup.mem_bot] at hyCx
  exact hy1 hyCx

omit [Finite L] in
theorem commutator_mem_centralizer_of_normalizer_zpowers {y w₁ w₂ : L}
    (h₁ : w₁ ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup L) : Set L))
    (h₂ : w₂ ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup L) : Set L)) :
    w₁ * w₂ * w₁⁻¹ * w₂⁻¹ ∈ Subgroup.centralizer ({y} : Set L) := by
  have key : ∀ u v : L, u ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup L) : Set L) →
      v ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup L) : Set L) →
      u * v * y * (u * v)⁻¹ = v * u * y * (v * u)⁻¹ := by
    intro u v hu hv
    obtain ⟨ku, hku⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hu y).mp (Subgroup.mem_zpowers y))
    obtain ⟨kv, hkv⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hv y).mp (Subgroup.mem_zpowers y))
    have hcu : ∀ k : ℤ, u * y ^ k * u⁻¹ = y ^ (ku * k) := by
      intro k
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hku, ← zpow_mul]
    have hcv : ∀ k : ℤ, v * y ^ k * v⁻¹ = y ^ (kv * k) := by
      intro k
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hkv, ← zpow_mul]
    have e1 : u * v * y * (u * v)⁻¹ = u * (v * y ^ (1 : ℤ) * v⁻¹) * u⁻¹ := by
      rw [zpow_one]; group
    have e2 : v * u * y * (v * u)⁻¹ = v * (u * y ^ (1 : ℤ) * u⁻¹) * v⁻¹ := by
      rw [zpow_one]; group
    rw [e1, e2, hcv, hcu, hcu, hcv]
    congr 1
    ring
  have h := key w₁⁻¹ w₂⁻¹ (Subgroup.inv_mem _ h₁) (Subgroup.inv_mem _ h₂)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc w₁ * w₂ * w₁⁻¹ * w₂⁻¹ * y
      = w₁ * w₂ * (w₁⁻¹ * w₂⁻¹ * y * (w₁⁻¹ * w₂⁻¹)⁻¹) * w₁⁻¹ * w₂⁻¹ := by group
    _ = w₁ * w₂ * (w₂⁻¹ * w₁⁻¹ * y * (w₂⁻¹ * w₁⁻¹)⁻¹) * w₁⁻¹ * w₂⁻¹ := by rw [h]
    _ = y * (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) := by group

theorem exists_sylowData_of_R3
    (hR : RFacts) (hL : JRGroup L) (hq : hL.q = 3)
    (hns : ¬ Group.IsSolvable L) {r : ℕ} [Fact r.Prime] (hr : ¬ r ∣ hL.q * (hL.q ^ 2 - 1))
    {P : Subgroup L} (hPc : Nat.card P = r ^ (Nat.card L).factorization r) (hP : P ≠ ⊥) :
    ∃ C W : Subgroup L, SylowData hL r P C W := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hL1512 := card_eq_1512 hR hL hq hns
  have hrp : r.Prime := Fact.out
  have hrL := dvd_card_of_ne_bot hPc hP
  rw [hq] at hr
  have hr7 : r = 7 := by
    rw [hL1512, show (1512 : ℕ) = 3 * (3 ^ 2 - 1) * 7 * 9 by norm_num] at hrL
    rcases (hrp.dvd_mul).mp hrL with h | h
    · rcases (hrp.dvd_mul).mp h with h | h
      · exact absurd h hr
      · exact (Nat.prime_dvd_prime_iff_eq hrp (by norm_num)).mp h
    · have h3 : r ∣ 3 := hrp.dvd_of_dvd_pow (show r ∣ 3 ^ 2 by norm_num at h ⊢; exact h)
      exact absurd (h3.mul_right _) hr
  subst hr7
  have hfac : (Nat.card L).factorization 7 = 1 := by
    rw [hL1512, show (1512 : ℕ) = 7 ^ 1 * 216 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7)]
    simp only [Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hP7 : Nat.card P = 7 := by rw [hPc, hfac, pow_one]
  have hN42 := card_normalizer_seven hR hL hq hns hP7
  obtain ⟨x, d, hox, hod, hdN, hdx⟩ := exists_three_seven hR hL hq
  have hx7 : Nat.card (Subgroup.zpowers x) = 7 := by rw [Nat.card_zpowers, hox]
  obtain ⟨g, -, hgP⟩ := exists_conj_of_sylowIn (G := L) (L := ⊤) (P := Subgroup.zpowers x)
    (Q := P) le_top le_top (by rw [Subgroup.card_top, hx7, hfac, pow_one])
    (by rw [Subgroup.card_top, hP7, hfac, pow_one])
  set d' := g * d * g⁻¹ with hd'def
  have hPy : P = Subgroup.zpowers (g * x * g⁻¹) := by rw [hgP, cj_zpowers]
  have hd'N : d' ∈ Subgroup.normalizer (P : Set L) := by
    rw [hgP, ← cj_normalizer]
    exact conj_mem_cj hdN
  have hod' : orderOf d' = 3 := by rw [hd'def, orderOf_conj_mul, hod]
  have hd'C : d' ∉ Subgroup.centralizer (P : Set L) := by
    intro hC
    apply hdx
    have h1 := Subgroup.mem_centralizer_iff.mp hC (g * x * g⁻¹) (by
      rw [hPy]; exact Subgroup.mem_zpowers _)
    have h2 : g * (x * d) * g⁻¹ = g * (d * x) * g⁻¹ := by
      calc g * (x * d) * g⁻¹ = g * x * g⁻¹ * d' := by rw [hd'def]; group
        _ = d' * (g * x * g⁻¹) := h1
        _ = g * (d * x) * g⁻¹ := by rw [hd'def]; group
    have := mul_left_cancel (mul_right_cancel h2)
    exact this.symm
  have hPcyc : IsCyclic P := isCyclic_of_prime_card hP7
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup P := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : P) ⟨b, hb⟩)
  have hPC : P ≤ Subgroup.centralizer (P : Set L) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hPcomm b hb a ha
  have hCN : Subgroup.centralizer (P : Set L) ≤ Subgroup.normalizer (P : Set L) :=
    Subgroup.centralizer_le_normalizer _
  have hCP : Subgroup.centralizer (P : Set L) = P := by
    have hdvd : Nat.card (Subgroup.centralizer (P : Set L)) ∣ 42 :=
      hN42 ▸ Subgroup.card_dvd_of_le hCN
    have h7 : 7 ∣ Nat.card (Subgroup.centralizer (P : Set L)) :=
      hP7 ▸ Subgroup.card_dvd_of_le hPC
    have h2 : ¬ 2 ∣ Nat.card (Subgroup.centralizer (P : Set L)) := by
      intro h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨⟨t, ht⟩, hot⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer
        (P : Set L)) 2 h2
      rw [Subgroup.orderOf_mk] at hot
      apply not_mem_centralizer_of_seven hR hL hq (x := g * x * g⁻¹)
        (by rw [orderOf_conj_mul, hox]) hot
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp ht _ (by rw [hPy]; exact Subgroup.mem_zpowers _))
    have h3 : ¬ 3 ∣ Nat.card (Subgroup.centralizer (P : Set L)) := by
      intro h3
      have hC21 : Nat.card (Subgroup.centralizer (P : Set L)) = 21 := by
        obtain ⟨a, ha⟩ := hdvd
        have h21 : 21 ∣ Nat.card (Subgroup.centralizer (P : Set L)) :=
          Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h7
        obtain ⟨b, hb⟩ := h21
        rw [hb] at ha h2 ⊢
        have hba : b * a = 2 := by rw [mul_assoc] at ha; omega
        have hb2 : b ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨a, hba.symm⟩
        interval_cases b
        · omega
        · rfl
        · exact absurd (dvd_mul_left 2 21) h2
      have hd'NC : Subgroup.zpowers d' ≤ Subgroup.normalizer
          ((Subgroup.centralizer (P : Set L) : Subgroup L) : Set L) :=
        Subgroup.zpowers_le.mpr (Huppert.normalizer_le_normalizer_centralizer P hd'N)
      have hcard := Sec52.card_sup_mul_card_inf hd'NC
      have hinf : Subgroup.centralizer (P : Set L) ⊓ Subgroup.zpowers d' = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨hzC, hzd⟩ := Subgroup.mem_inf.mp hz
        by_contra hz1
        have hzz : Subgroup.zpowers z = Subgroup.zpowers d' := by
          apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzd)
          rw [Nat.card_zpowers, Nat.card_zpowers, hod']
          have hdv : orderOf z ∣ 3 := hod' ▸ orderOf_dvd_of_mem_zpowers hzd
          rcases (Nat.dvd_prime Nat.prime_three).mp hdv with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hz1
          · exact h.ge
        apply hd'C
        have : d' ∈ Subgroup.zpowers z := hzz ▸ Subgroup.mem_zpowers d'
        exact Subgroup.zpowers_le.mpr hzC this
      rw [hinf, Subgroup.card_bot, mul_one, hC21, Nat.card_zpowers, hod'] at hcard
      have hle : Subgroup.zpowers d' ⊔ Subgroup.centralizer (P : Set L) ≤
          Subgroup.normalizer (P : Set L) := sup_le (Subgroup.zpowers_le.mpr hd'N) hCN
      have := Subgroup.card_le_of_le hle
      rw [hcard, hN42] at this
      omega
    have hC7 : Nat.card (Subgroup.centralizer (P : Set L)) = 7 := by
      obtain ⟨a, ha⟩ := hdvd
      obtain ⟨b, hb⟩ := h7
      rw [hb] at ha h2 h3 ⊢
      have hba : b * a = 6 := by rw [mul_assoc] at ha; omega
      have hb6 : b ≤ 6 := Nat.le_of_dvd (by norm_num) ⟨a, hba.symm⟩
      interval_cases b
      · omega
      · rfl
      · exact absurd (dvd_mul_left 2 7) h2
      · exact absurd (dvd_mul_left 3 7) h3
      · exact absurd (Dvd.dvd.mul_left (by norm_num : 2 ∣ 4) 7) h2
      · omega
      · exact absurd (Dvd.dvd.mul_left (by norm_num : 2 ∣ 6) 7) h2
    exact (Subgroup.eq_of_le_of_card_ge hPC (by rw [hC7, hP7])).symm
  have hrel : P.relIndex (Subgroup.normalizer (P : Set L)) = 6 := by
    have h := Subgroup.relIndex_mul_card (H := P) (K := Subgroup.normalizer (P : Set L))
    rw [inf_eq_left.mpr Subgroup.le_normalizer, hP7, hN42] at h
    omega
  obtain ⟨W, hWN, hi, hs, hWcard⟩ := exists_complement_in (C := P)
    (N := Subgroup.normalizer (P : Set L)) Subgroup.le_normalizer le_rfl
    (by rw [hrel, hP7]; decide)
  have hW6 : Nat.card W = 6 := by rw [hP7, hN42] at hWcard; omega
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have hy : P = Subgroup.zpowers (g * x * g⁻¹) := hPy
    have hc := commutator_mem_centralizer_of_normalizer_zpowers (y := g * x * g⁻¹)
      (hy ▸ hWN ha) (hy ▸ hWN hb)
    have hc' : a * b * a⁻¹ * b⁻¹ ∈ P := by
      rw [← hCP, hy, Sec52.centralizer_zpowers_eq]
      exact hc
    have hcW : a * b * a⁻¹ * b⁻¹ ∈ W :=
      W.mul_mem (W.mul_mem (W.mul_mem ha hb) (W.inv_mem ha)) (W.inv_mem hb)
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hc', hcW⟩
      rwa [hi, Subgroup.mem_bot] at this
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hWcyc : IsCyclic W := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hou⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 (by rw [hW6]; norm_num)
    obtain ⟨v, hov⟩ := exists_prime_orderOf_dvd_card' (G := W) 3 (by rw [hW6]; norm_num)
    have hcomm : Commute u v := Subtype.ext (hWcomm _ u.2 _ v.2)
    have huv : orderOf (u * v) = 6 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hou, hov]; norm_num), hou, hov]
    exact isCyclic_of_orderOf_eq_card (u * v) (by rw [huv, hW6])
  have hPcent : ∀ c ∈ P, c ≠ 1 → Subgroup.centralizer ({c} : Set L) = P := by
    intro c hc hc1
    have hz : Subgroup.zpowers c = P := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc) ?_
      rw [hP7, Nat.card_zpowers]
      have hdvd : orderOf c ∣ 7 := hP7 ▸ Subgroup.orderOf_dvd_natCard P hc
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hc1
      · exact h.ge
    rw [← Sec52.centralizer_zpowers_eq, hz, hCP]
  have hPhall : Nat.Coprime (Nat.card P) P.index := by
    have h1 := Subgroup.card_mul_index P
    rw [hP7, hL1512] at h1
    have : P.index = 216 := by omega
    rw [hP7, this]
    decide
  exact ⟨P, W, ⟨le_rfl, hPcomm, hPhall, hPcent, hi, hs, le_rfl, hWcyc, Or.inl hW6⟩⟩

end Sec6

end CFSG.Walter.W67
