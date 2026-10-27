module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc

public section

namespace CFSG.StandardType.TwE6DD2

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule

section Abstract

variable {G R : Type} [Group G] [Group R]

theorem finite_of_card_dvd_three {Z : Subgroup G} (hZ : Nat.card Z ∣ 3) : Finite Z :=
  Nat.finite_of_card_ne_zero fun h => by
    rw [h] at hZ
    exact absurd hZ (by norm_num)

theorem eq_one_or_eq_or_eq_inv {Z : Subgroup G} (hZ : Nat.card Z ∣ 3) {c d : G} (hc : c ∈ Z)
    (hd : d ∈ Z) (hc1 : c ≠ 1) : d = 1 ∨ d = c ∨ d = c⁻¹ := by
  have := finite_of_card_dvd_three hZ
  have hoc : orderOf c ∣ 3 := (Subgroup.orderOf_dvd_natCard Z hc).trans hZ
  have ho3 : orderOf c = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hoc with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hc1
    · exact h
  have hc3 : c ^ 3 = 1 := by
    rw [← ho3]
    exact pow_orderOf_eq_one c
  have hle : Subgroup.zpowers c ≤ Z := (Subgroup.zpowers_le).2 hc
  have hcard : Nat.card Z ≤ Nat.card (Subgroup.zpowers c) := by
    rw [Nat.card_zpowers, ho3]
    exact Nat.le_of_dvd (by norm_num) hZ
  have hdz : d ∈ Subgroup.zpowers c := (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ hd
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hdz
  have hk : c ^ k = c ^ (k % 3) := by
    have h := zpow_mod_orderOf c k
    rw [ho3] at h
    exact_mod_cast h.symm
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  rw [hk]
  generalize k % 3 = m at h0 h3
  interval_cases m
  · exact Or.inl (zpow_zero c)
  · exact Or.inr (Or.inl (zpow_one c))
  · refine Or.inr (Or.inr ?_)
    rw [zpow_two]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_assoc, ← pow_three, hc3])

theorem commute_of_cube_lift {q : G →* R} (hq : Function.Surjective q)
    (hqZ : q.ker = Subgroup.center G) (hperf : commutator G = ⊤)
    (h3 : Nat.card (Subgroup.center G) ∣ 3) {w : MulAut R} {φ : MulAut G}
    (hφ : ∀ g, q (φ g) = w (q g)) {g₁ g₂ : G} (h₁ : w ^ 3 = MulAut.conj (q g₁))
    (h₂ : w (q g₂) = q g₂) : g₁ * g₂ = g₂ * g₁ := by
  have := finite_of_card_dvd_three h3
  have hinj := BstarDesc.descAut_injective hq hqZ hperf
  have hd : BstarDesc.descAut hq hqZ φ = w := by
    refine MulEquiv.ext fun r => ?_
    obtain ⟨g, rfl⟩ := hq r
    rw [BstarDesc.descAut_apply, hφ]
  have hdc : BstarDesc.descAut hq hqZ (MulAut.conj g₁) = MulAut.conj (q g₁) := by
    refine MulEquiv.ext fun r => ?_
    obtain ⟨g, rfl⟩ := hq r
    rw [BstarDesc.descAut_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hφ3 : φ ^ 3 = MulAut.conj g₁ := hinj (by rw [map_pow, hd, h₁, hdc])
  set c := g₂⁻¹ * φ g₂ with hcdef
  have hcZ : c ∈ Subgroup.center G := by
    rw [← hqZ, MonoidHom.mem_ker, map_mul, map_inv, hφ, h₂, inv_mul_cancel]
  have hφg : φ g₂ = g₂ * c := by rw [hcdef, mul_inv_cancel_left]
  have hc3 : c ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard _ hcZ).trans h3)
  have hφ3c : (φ ^ 3) c = c := by
    rw [hφ3, MulAut.conj_apply, Subgroup.mem_center_iff.1 hcZ g₁, mul_inv_cancel_right]
  have hfix : φ c = c := by
    by_cases hc1 : c = 1
    · rw [hc1, map_one]
    rcases eq_one_or_eq_or_eq_inv h3 hcZ (BstarDesc.mulAut_mem_center φ hcZ) hc1 with h | h | h
    · exact absurd ((map_eq_one_iff φ φ.injective).1 h) hc1
    · exact h
    · exfalso
      have h2 : (φ ^ 3) c = c⁻¹ := by
        rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, h, map_inv, h, inv_inv, h]
      have hinv : c⁻¹ = c := h2.symm.trans hφ3c
      have hcc : c * c = 1 := by
        calc c * c = c * c⁻¹ := by rw [hinv]
          _ = 1 := mul_inv_cancel c
      apply hc1
      calc c = c * (c * c) := by rw [hcc, mul_one]
        _ = c ^ 3 := (pow_three c).symm
        _ = 1 := hc3
  have hφk : ∀ k : ℕ, (φ ^ k) g₂ = g₂ * c ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, MulAut.one_apply, mul_one]
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, hφg, map_pow, hfix, pow_succ', mul_assoc]
  have h3g : (φ ^ 3) g₂ = g₂ := by rw [hφk, hc3, mul_one]
  rw [hφ3, MulAut.conj_apply] at h3g
  calc g₁ * g₂ = g₁ * g₂ * g₁⁻¹ * g₁ := by group
    _ = g₂ * g₁ := by rw [h3g]

theorem eq_one_of_pow_two_pow_of_pow_three {x : G} {M : ℕ} (h2 : x ^ 2 ^ M = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have hcop : Nat.Coprime (orderOf x) (2 ^ M) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3)
      (Nat.Coprime.pow_right M (by norm_num))
  exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h2))

end Abstract

section SC


theorem finite_twistedE6Group (n : ℕ) : Finite (twistedE6Group 2 n) := by
  have : Finite (Module.End (GaloisField 2 (2 * n)) (Fin e6Data.d →₀ GaloisField 2 (2 * n))) :=
    Module.finite_of_finite (GaloisField 2 (2 * n))
  infer_instance

theorem card_center_dvd_three {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (Subgroup.center (twistedE6Group 2 n)) ∣ 3 := by
  have h := (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n))
    (θ := frobQ 2 n) (q := 2 ^ n) (card_galoisField_two_mul 2 n hn)
    (fun c => by rw [frobQ_apply])).1
  rw [h]
  exact Nat.gcd_dvd_left 3 _

theorem exists_section_sc {n : ℕ} (hn : 1 ≤ n) (E : Type) [Group E] [Finite E]
    (π : E →* twistedE6Group 2 n) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hcop : Nat.Coprime 2 (Nat.card π.ker)) :
    ∃ s : twistedE6Group 2 n →* E, ∀ h, π (s h) = h :=
  TwistedE6Closed.twistedE6_exists_section_of_coprime (k := GaloisField 2 (2 * n))
    (θ := frobQ 2 n) (frobQ_frobQ 2 n hn) (p := 2) hπ hc hcop

theorem exists_lift_sc {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    {q : twistedE6Group 2 n →* TwE6Delta.RecipeR K n} (hq : Function.Surjective q)
    (hqk : q.ker ≤ Subgroup.center (twistedE6Group 2 n)) (w : MulAut (TwE6Delta.RecipeR K n)) :
    ∃ φ : MulAut (twistedE6Group 2 n), ∀ u, q (φ u) = w (q u) := by
  have := finite_twistedE6Group n
  set ψ' : twistedE6Group 2 n →* TwE6Delta.RecipeR K n := w.symm.toMonoidHom.comp q with hψ'
  have hψ's : Function.Surjective ψ' := w.symm.surjective.comp hq
  have hker' : ψ'.ker = q.ker := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    exact map_eq_one_iff w.symm w.symm.injective
  have hodd : ∀ y ∈ ψ'.ker, y ^ 2 = 1 → y = 1 := by
    intro y hy hy2
    rw [hker'] at hy
    have h1 : orderOf y ∣ 3 :=
      (Subgroup.orderOf_dvd_natCard _ (hqk hy)).trans (card_center_dvd_three hn)
    have hcop : Nat.Coprime (orderOf y) 2 :=
      Nat.Coprime.coprime_dvd_left h1 (by norm_num)
    exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hy2))
  obtain ⟨α, hα, hαs⟩ := StdSubRestU.exists_surjective_of_oddKernel hq (exists_section_sc hn)
    hψ's (by rw [hker']; exact hqk) (MpStdTwE6.commutator_twistedE6Group hn) hodd
  have hαi : Function.Injective α := Finite.injective_iff_surjective.2 hαs
  refine ⟨MulEquiv.ofBijective α ⟨hαi, hαs⟩, fun u => ?_⟩
  have h : w.symm (q (α u)) = q u := hα u
  change q (α u) = w (q u)
  rw [← h, MulEquiv.apply_symm_apply]

end SC

section Cover


variable {n : ℕ} {K : Type} [Field K] [Finite K] {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n}

theorem exists_sc_quot (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) :
    ∃ (q : twistedE6Group 2 n →* TwE6Delta.RecipeR K n)
      (α : twistedE6Group 2 n →* L' ⧸ TableBU.twoPartOf ψ.ker hker (Nat.card L')),
      Function.Surjective q ∧ q.ker ≤ Subgroup.center (twistedE6Group 2 n) ∧
      Function.Surjective α ∧
      ∀ u, QuotientGroup.lift _ ψ (TableBU.twoPartOf_le _ hker _) (α u) = q u := by
  obtain ⟨q, hq, hqk⟩ := TwE6Delta.exists_sc_surjection hn hK
  have := finite_twistedE6Group n
  set N := TableBU.twoPartOf ψ.ker hker (Nat.card L') with hNdef
  have hNk : N ≤ ψ.ker := TableBU.twoPartOf_le _ hker _
  set π : L' →* L' ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set ψb : L' ⧸ N →* TwE6Delta.RecipeR K n := QuotientGroup.lift N ψ hNk with hψb
  have hψbπ : ∀ l, ψb (π l) = ψ l := fun l => QuotientGroup.lift_mk N hNk l
  have hψbs : Function.Surjective ψb := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨π l, hψbπ l⟩
  have hψbc : ψb.ker ≤ Subgroup.center (L' ⧸ N) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hπs y
    have hz' : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψbπ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hπs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz') v]
  have hψbodd : ∀ y ∈ ψb.ker, y ^ 2 = 1 → y = 1 := fun y hy hy2 =>
    TableBU.sq_eq_one_ker_lift hker y hy hy2
  have hperfb : commutator (L' ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := hπs y
    have hl : l ∈ commutator L' := by rw [hperf]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem π hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs, ← commutator_def] at h1
  obtain ⟨α, hα, hαs⟩ :=
    StdSubRestU.exists_surjective_of_oddKernel hq (exists_section_sc hn) hψbs hψbc hperfb hψbodd
  exact ⟨q, α, hq, hqk, hαs, hα⟩

theorem center_facts (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) :
    (∀ z ∈ Subgroup.center L', (z ^ 4 ^ Nat.card L') ^ 3 = 1) ∧
    ∀ z₀ ∈ Subgroup.center L', ∀ z ∈ Subgroup.center L', orderOf z₀ = 3 → z ^ 3 = 1 →
      z ∈ Subgroup.zpowers z₀ := by
  obtain ⟨q, α, hq, hqk, hαs, hα⟩ := exists_sc_quot hn hK hψ hker hperf
  have := finite_twistedE6Group n
  set N := TableBU.twoPartOf ψ.ker hker (Nat.card L') with hNdef
  have hkc : ψ.ker = Subgroup.center L' :=
    BstarDesc.ker_eq_center hψ hker (TwE6Delta.center_recipeR_eq_bot hn hK)
  have hZ3 := card_center_dvd_three hn
  have hpre : ∀ z ∈ Subgroup.center L', ∃ u ∈ q.ker, α u = (z : L' ⧸ N) := by
    intro z hz
    obtain ⟨u, hu⟩ := hαs (z : L' ⧸ N)
    refine ⟨u, ?_, hu⟩
    rw [MonoidHom.mem_ker, ← hα, hu, QuotientGroup.lift_mk]
    have hz' : z ∈ ψ.ker := by rw [hkc]; exact hz
    exact hz'
  have hcube : ∀ u ∈ q.ker, u ^ 3 = 1 := fun u hu =>
    orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard _ (hqk hu)).trans hZ3)
  have hN3 : ∀ x : L', (x : L' ⧸ N) = 1 → x ^ 3 = 1 → x = 1 := by
    intro x hx hx3
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 hx
    exact eq_one_of_pow_two_pow_of_pow_three hxN.2 hx3
  refine ⟨fun z hz => ?_, fun z₀ hz₀ z hz ho hz3 => ?_⟩
  · obtain ⟨u, hu, hαu⟩ := hpre z hz
    have h1 : ((z ^ 3 : L') : L' ⧸ N) = 1 := by
      rw [QuotientGroup.mk_pow, ← hαu, ← map_pow, hcube u hu, map_one]
    have h2 : (z ^ 3) ^ 2 ^ Nat.card L' = 1 := ((QuotientGroup.eq_one_iff _).1 h1).2
    rw [← pow_mul, mul_comm, pow_mul, show 4 ^ Nat.card L' = 2 ^ Nat.card L' * 2 ^ Nat.card L' by
      rw [← mul_pow]; norm_num, pow_mul, h2, one_pow]
  · have hz₀3 : z₀ ^ 3 = 1 := by
      rw [← ho]
      exact pow_orderOf_eq_one z₀
    obtain ⟨u₀, hu₀, hαu₀⟩ := hpre z₀ hz₀
    obtain ⟨u, hu, hαu⟩ := hpre z hz
    have hu₀1 : u₀ ≠ 1 := by
      intro h1
      have h := hN3 z₀ (by rw [← hαu₀, h1, map_one]) hz₀3
      rw [h, orderOf_one] at ho
      exact absurd ho (by norm_num)
    have hcomm : ∀ x : L', Commute x z := fun x => Subgroup.mem_center_iff.1 hz x
    rcases eq_one_or_eq_or_eq_inv hZ3 (hqk hu₀) (hqk hu) hu₀1 with h | h | h
    · rw [hN3 z (by rw [← hαu, h, map_one]) hz3]
      exact one_mem _
    · have h1 : ((z₀⁻¹ * z : L') : L' ⧸ N) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hαu₀, ← hαu, h, inv_mul_cancel]
      have h3 : (z₀⁻¹ * z) ^ 3 = 1 := by
        rw [(hcomm z₀⁻¹).mul_pow, inv_pow, hz₀3, hz3, inv_one, one_mul]
      rw [← inv_mul_eq_one.1 (hN3 _ h1 h3)]
      exact Subgroup.mem_zpowers z₀
    · have h1 : ((z₀ * z : L') : L' ⧸ N) = 1 := by
        rw [QuotientGroup.mk_mul, ← hαu₀, ← hαu, h, map_inv, mul_inv_cancel]
      have h3 : (z₀ * z) ^ 3 = 1 := by
        rw [(hcomm z₀).mul_pow, hz₀3, hz3, one_mul]
      have hz' : z = z₀⁻¹ := eq_inv_of_mul_eq_one_right (hN3 _ h1 h3)
      rw [hz']
      exact inv_mem (Subgroup.mem_zpowers z₀)

theorem commute_of_cube_mem (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {Y W : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hW : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) (hW9 : ∀ w ∈ W, w ^ 9 = 1)
    (hYW : ∀ y ∈ Y, ∃ w ∈ W, w ^ 3 = y) {l₁ l₂ : L'}
    (h₁ : MulAut.conj (ψ l₁) ∈ Y) (h₂ : MulAut.conj (ψ l₂) ∈ Y) : l₁ * l₂ = l₂ * l₁ := by
  have hZR := TwE6Delta.center_recipeR_eq_bot hn hK
  have hconjinj : Function.Injective
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hrZ : r ∈ Subgroup.center (TwE6Delta.RecipeR K n) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut (TwE6Delta.RecipeR K n) => f g) hr
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * r = r * g * r⁻¹ * r := by rw [h]
        _ = r * g := by group
    rw [hZR] at hrZ
    exact hrZ
  obtain ⟨w₁, hw₁, hw₁3⟩ := hYW _ h₁
  obtain ⟨w₂, hw₂, hw₂3⟩ := hYW _ h₂
  have hfix : w₁ (ψ l₂) = ψ l₂ := by
    apply hconjinj
    have hc : MulAut.conj (w₁ (ψ l₂)) = w₁ * MulAut.conj (ψ l₂) * w₁⁻¹ := by
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
        map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    have hcomm : Commute w₁ w₂ := hW w₁ hw₁ w₂ hw₂
    rw [hc, ← hw₂3, (hcomm.pow_right 3).eq, mul_inv_cancel_right]
  obtain ⟨q, α, hq, hqk, hαs, hα⟩ := exists_sc_quot hn hK hψ hker hperf
  set N := TableBU.twoPartOf ψ.ker hker (Nat.card L') with hNdef
  obtain ⟨φ, hφ⟩ := exists_lift_sc hn hq hqk w₁
  obtain ⟨u₁, hu₁⟩ := hαs (l₁ : L' ⧸ N)
  obtain ⟨u₂, hu₂⟩ := hαs (l₂ : L' ⧸ N)
  have hqu : ∀ (u : twistedE6Group 2 n) (l : L'), α u = (l : L' ⧸ N) → q u = ψ l := by
    intro u l h
    rw [← hα, h, QuotientGroup.lift_mk]
  have hqZ : q.ker = Subgroup.center (twistedE6Group 2 n) := BstarDesc.ker_eq_center hq hqk hZR
  have hu : u₁ * u₂ = u₂ * u₁ :=
    commute_of_cube_lift hq hqZ (MpStdTwE6.commutator_twistedE6Group hn)
      (card_center_dvd_three hn) hφ (by rw [hw₁3, hqu u₁ l₁ hu₁])
      (by rw [hqu u₂ l₂ hu₂]; exact hfix)
  have hq12 : ((l₂ * l₁ : L') : L' ⧸ N) = ((l₁ * l₂ : L') : L' ⧸ N) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hu₁, ← hu₂, ← map_mul α u₂ u₁,
      ← map_mul α u₁ u₂, hu]
  have hcN : (l₂ * l₁)⁻¹ * (l₁ * l₂) ∈ N := QuotientGroup.eq.1 hq12
  set c := (l₂ * l₁)⁻¹ * (l₁ * l₂) with hcdef
  have hcZ : c ∈ Subgroup.center L' := hker hcN.1
  have hl₁3 : l₁ ^ 3 ∈ Subgroup.center L' := by
    apply hker
    rw [MonoidHom.mem_ker, map_pow]
    apply hconjinj
    rw [map_pow, map_one, ← hw₁3, ← pow_mul]
    exact hW9 w₁ hw₁
  have hl₁c : l₂⁻¹ * l₁ * l₂ = l₁ * c := by
    rw [hcdef]
    group
  have hc3 : c ^ 3 = 1 := by
    have h1 : (l₂⁻¹ * l₁ * l₂⁻¹⁻¹) ^ 3 = l₂⁻¹ * l₁ ^ 3 * l₂⁻¹⁻¹ := conj_pow
    rw [inv_inv, hl₁c,
      (show Commute l₁ c from Subgroup.mem_center_iff.1 hcZ l₁).mul_pow] at h1
    have h2 : l₂⁻¹ * l₁ ^ 3 * l₂ = l₁ ^ 3 := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 hl₁3 l₂, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h2] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  have hc1 : c = 1 := eq_one_of_pow_two_pow_of_pow_three hcN.2 hc3
  rw [hcdef, inv_mul_eq_one] at hc1
  exact hc1.symm

end Cover

end CFSG.StandardType.TwE6DD2
