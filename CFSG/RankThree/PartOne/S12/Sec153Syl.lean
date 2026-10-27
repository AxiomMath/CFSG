module

public import CFSG.RankThree.PartOne.S12.Sec153Weyl
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec153

variable {G : Type} [Group G] [Finite G]

theorem trans5 : ∀ π : Equiv.Perm (Fin 5), π ^ 5 = 1 → π ≠ 1 → ∀ i j : Fin 5,
    ∃ k : Fin 5, (π ^ (k : ℕ)) i = j := by
  decide +kernel

theorem not_dvd_120 {p : ℕ} (hp : p.Prime) (h3 : 3 < p) (h5 : p ≠ 5) : ¬ p ∣ 120 := by
  intro hd
  have h120 : (120 : ℕ) = 2 ^ 3 * 3 * 5 := by norm_num
  rw [h120] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow hp h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)

theorem card_perm5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem mem_E_of_centralizes {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) {x : G} (hxp : x ^ p = 1) (hx : ∀ e ∈ E, x * e = e * x) :
    x ∈ E := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hEel := h.E_elem
  have hz : IsElementaryAbelian p (Subgroup.zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hcent : Subgroup.zpowers x ≤ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro e he
    exact (hx e he).symm
  have hsup := IsElementaryAbelian.sup_of_le_centralizer (p := p) hcent
  have hF : E ⊔ Subgroup.zpowers x = E := by
    refine h.E_max _ hsup ?_ le_sup_left
    refine sup_le h.E_le ?_
    exact hcent.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 h.A_le_E))
  have hmem : x ∈ E ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [hF] at hmem

theorem mem_E_of_conjAut_eq_one {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) {x : G} (hxN : x ∈ Subgroup.normalizer (E : Set G)) (hxp : x ^ p = 1)
    (h1 : conjAut E x hxN = 1) : x ∈ E := by
  refine mem_E_of_centralizes h hxp (fun e he => ?_)
  have h2 := Equivariance.coe_conjAut hxN ⟨e, he⟩
  rw [h1] at h2
  have h3 : e = x * e * x⁻¹ := h2
  rw [eq_mul_inv_iff_mul_eq] at h3
  exact h3.symm

theorem E_le_of_sylow {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) {P : Subgroup G} (hP : IsSylowOf p P (torusNormalizer E)) :
    E ≤ P := by
  obtain ⟨hPW, hPp, hidx⟩ := hP
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hEel := h.E_elem
  have hEW : E ≤ torusNormalizer E := Subgroup.le_normalizer
  have hPp' : IsPGroup p (P.subgroupOf (torusNormalizer E)) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm
  have hidx' : ¬ p ∣ (P.subgroupOf (torusNormalizer E)).index := hidx
  have hEp : IsPGroup p (E.subgroupOf (torusNormalizer E)) :=
    (IsElementaryAbelian.isPGroup p E).of_equiv (Subgroup.subgroupOfEquivOfLe hEW).symm
  have hnorm : (E.subgroupOf (torusNormalizer E)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 g.2 n).1 hn⟩
  have hle := hEp.le_sylow_of_normal (hPp'.toSylow hidx')
  intro e he
  have h1 : (⟨e, hEW he⟩ : ↥(torusNormalizer E)) ∈ E.subgroupOf (torusNormalizer E) := he
  have h2 := (IsPGroup.mem_toSylow hPp' hidx').1 (hle h1)
  exact Subgroup.mem_subgroupOf.1 h2

theorem omegaOne_eq_of_le {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hX : ¬ p ∣ Nat.card ↥(reflectionGroup p E)) {P : Subgroup G}
    (hP : IsSylowOf p P (torusNormalizer E)) : omegaOne p P = E := by
  have hEP := E_le_of_sylow h hP
  obtain ⟨hPW, hPp, hidx⟩ := hP
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hEel := h.E_elem
  have hE : ∀ e : E, e ^ p = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p E) e
  have hptriv := Sec155.pElement_trivial hp hE hW (Sec1322.reflectionGroup_le E) hX
  have hPcent : ∀ x ∈ P, ∀ e ∈ E, x * e = e * x := by
    intro x hx e he
    have hxN : x ∈ Subgroup.normalizer (E : Set G) := hPW hx
    obtain ⟨a, ha⟩ := hPp ⟨x, hx⟩
    have hxa : x ^ (p ^ a) = 1 := congrArg Subtype.val ha
    have hg : conjAut E x hxN ∈ torusWeyl E := ⟨⟨x, hxN⟩, rfl⟩
    have h1 : (conjAut E x hxN) ^ (p ^ a) = 1 := by
      unfold conjAut
      rw [← map_pow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (p ^ a) = 1 := Subtype.ext hxa
      rw [this, map_one]
    have h2 := hptriv _ hg a h1
    have h3 := Equivariance.coe_conjAut hxN ⟨e, he⟩
    rw [h2] at h3
    have h4 : e = x * e * x⁻¹ := h3
    rw [eq_mul_inv_iff_mul_eq] at h4
    exact h4.symm
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxP, hxp⟩
    exact mem_E_of_centralizes h hxp (hPcent x hxP)
  · intro e he
    exact Subgroup.subset_closure ⟨hEP he, elemPow_eq_one_of_isElementaryAbelian e he⟩

omit [Finite G] in
theorem isElementaryAbelian_of_le {p : ℕ} {A K : Subgroup G} (hA : IsElementaryAbelian p ↥A)
    (hKA : K ≤ A) : IsElementaryAbelian p ↥K := CFSG.IsElementaryAbelian.of_le hA hKA

theorem outer_facts {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G 5 A c L E)
    (M : ModData 5 E) {y : G} (hyN : y ∈ Subgroup.normalizer (E : Set G)) (hy : y ^ 5 = 1)
    (hyE : y ∉ E) :
    conjAut E y hyN ∈ reflectionGroup 5 E ∧ conjAut E y hyN ≠ 1 ∧
      Nat.card {u : ↥E // conjAut E y hyN u = u} ≤ 5 := by
  classical
  have hp := h.prime
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hE : ∀ e : ↥E, e ^ 5 = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 5 ↥E) e
  have hW : conjAut E y hyN ∈ torusWeyl E := ⟨⟨y, hyN⟩, rfl⟩
  have hpow : conjAut E y hyN ^ (5 ^ 1) = 1 := by
    unfold conjAut
    rw [pow_one, ← map_pow]
    have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ 5 = 1 :=
      Subtype.ext (by simpa using hy)
    rw [this, map_one]
  have hI := M.mem_of_pPower hp hEc hE hW hpow
  have hne : conjAut E y hyN ≠ 1 := fun h1 => hyE (mem_E_of_conjAut_eq_one h hyN hy h1)
  refine ⟨hI, hne, ?_⟩
  let _ : CommGroup ↥E := commE hEc
  have hrel' : ∀ a : Fin 5 → ℤ, ∏ i, M.v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, ((5 : ℕ) : ℤ) ∣ a i - m :=
    fun a => by rw [Fin.prod_univ_five]; exact M.rel a
  have hgen' : ∀ x : ↥E, ∃ a : Fin 5 → ℤ, x = ∏ i, M.v i ^ a i := fun x => by
    obtain ⟨a, ha⟩ := M.gen x
    exact ⟨a, by rw [Fin.prod_univ_five]; exact ha⟩
  have hπ5 : (M.θ ⟨conjAut E y hyN, hI⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨conjAut E y hyN, hI⟩ : ↥(reflectionGroup 5 E)) ^ 5 = 1 :=
      Subtype.ext (by simpa [pow_one] using hpow)
    rw [this, map_one]
  have hπ1 : M.θ ⟨conjAut E y hyN, hI⟩ ≠ 1 := by
    intro h1
    apply hne
    have := M.θ.injective (h1.trans (map_one M.θ).symm)
    exact congrArg Subtype.val this
  have htrans : ∀ i j : Fin 5, ∃ k : ℕ, (M.θ ⟨conjAut E y hyN, hI⟩ ^ k) i = j := fun i j => by
    obtain ⟨k, hk⟩ := trans5 _ hπ5 hπ1 i j
    exact ⟨k, hk⟩
  exact card_fixed_le M.v hrel' hgen' _ htrans (conjAut E y hyN)
    (fun k => M.perm ⟨conjAut E y hyN, hI⟩ k)

theorem le_E_of_card_gt {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G 5 A c L E)
    (M : ModData 5 E) {F : Subgroup G} (hFN : F ≤ torusNormalizer E)
    (hFe : IsElementaryAbelian 5 ↥F) (hcard : 25 < Nat.card ↥F) : F ≤ E := by
  classical
  by_contra hFE
  obtain ⟨y, hyF, hyE⟩ : ∃ y ∈ F, y ∉ E := by
    by_contra hcon
    exact hFE fun x hx => by_contra fun hxE => hcon ⟨x, hx, hxE⟩
  have hp := h.prime
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hE : ∀ e : ↥E, e ^ 5 = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 5 ↥E) e
  have hFN' : F ≤ Subgroup.normalizer (E : Set G) := hFN
  have hFexp : ∀ x ∈ F, x ^ 5 = 1 := fun x hx => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 5 ↥F)
      ⟨x, hx⟩
    simpa using congrArg Subtype.val this
  obtain ⟨hyI, hyne, hyfix⟩ := outer_facts h M (hFN' hyF) (hFexp y hyF) hyE
  let φ : ↥F →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hFN')
  have hφ : ∀ x : ↥F, φ x = conjAut E x (hFN' x.2) := fun x => rfl
  have hker : ∀ x : ↥F, φ x = 1 → (x : G) ∈ E := fun x hx =>
    mem_E_of_conjAut_eq_one h (hFN' x.2) (hFexp x x.2) (by rw [← hφ]; exact hx)
  have hyx : ∀ x : ↥φ.ker, (y : G) * (x.1 : G) = (x.1 : G) * y := fun x =>
    congrArg Subtype.val (hFe.is_comm.comm ⟨y, hyF⟩ x.1)
  have hfixk : ∀ x : ↥φ.ker, conjAut E y (hFN' hyF) ⟨x.1.1, hker x.1 x.2⟩ =
      ⟨x.1.1, hker x.1 x.2⟩ := by
    intro x
    apply Subtype.ext
    rw [Equivariance.coe_conjAut]
    show (y : G) * (x.1.1 : G) * y⁻¹ = x.1.1
    rw [hyx x]
    group
  have hkerle : Nat.card ↥φ.ker ≤ 5 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : ↥φ.ker => (⟨⟨x.1.1, hker x.1 x.2⟩, hfixk x⟩ :
        {u : ↥E // conjAut E y (hFN' hyF) u = u})) ?_) hyfix
    intro x x' hxx'
    have := congrArg (fun z : {u : ↥E // conjAut E y (hFN' hyF) u = u} => (z.1 : G)) hxx'
    exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card ↥φ.range ≤ 5 := by
    have hle : φ.range ≤ reflectionGroup 5 E := by
      rintro _ ⟨x, rfl⟩
      have hxW : φ x ∈ torusWeyl E := ⟨⟨x.1, hFN' x.2⟩, rfl⟩
      refine M.mem_of_pPower hp hEc hE hxW (a := 1) ?_
      rw [pow_one, ← map_pow]
      have : x ^ 5 = 1 := Subtype.ext (by simpa using hFexp x x.2)
      rw [this, map_one]
    have hd1 : Nat.card ↥φ.range ∣ 120 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_congr M.θ.toEquiv, card_perm5] at this
    have hd2 : Nat.card ↥φ.range ∣ Nat.card ↥F := Subgroup.card_range_dvd φ
    have : Fact (Nat.Prime 5) := ⟨hp⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (IsElementaryAbelian.isPGroup 5 ↥F)
    rw [hn] at hd2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd2
    rw [hk] at hd1 ⊢
    by_cases hk2 : 2 ≤ k
    · exfalso
      have h25 : 25 ∣ 120 := (pow_dvd_pow 5 hk2 : 5 ^ 2 ∣ 5 ^ k).trans hd1
      omega
    · interval_cases k <;> norm_num
  have hmul := Subgroup.card_ker_mul_card_range φ
  have := Nat.mul_le_mul hkerle hrange
  omega

theorem thompson_le_E {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G 5 A c L E)
    (M : ModData 5 E) (hcardE : Nat.card ↥E = 5 ^ 4) {P : Subgroup G} (hPN : P ≤ torusNormalizer E)
    (hEP : E ≤ P) {X : Subgroup G} (hXP : X ≤ P) (hXn : (X.subgroupOf P).Normal) :
    thompsonElem 5 X ≤ E := by
  classical
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨F, hFX, hFe, hFmax, hxF⟩
  have hFN : F ≤ torusNormalizer E := hFX.trans (hXP.trans hPN)
  have hFE : F ≤ E := by
    by_contra hFE
    obtain ⟨y, hyF, hyE⟩ : ∃ y ∈ F, y ∉ E := by
      by_contra hcon
      exact hFE fun x hx => by_contra fun hxE => hcon ⟨x, hx, hxE⟩
    have hp := h.prime
    have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
    have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
    have hFN' : F ≤ Subgroup.normalizer (E : Set G) := hFN
    have hFexp : ∀ x ∈ F, x ^ 5 = 1 := fun x hx => by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
        (IsElementaryAbelian.exponent_dvd_p 5 ↥F) ⟨x, hx⟩
      simpa using congrArg Subtype.val this
    obtain ⟨hyI, hyne, hyfix⟩ := outer_facts h M (hFN' hyF) (hFexp y hyF) hyE
    let _ : CommGroup ↥E := commE hEc
    set s : MulAut ↥E := conjAut E y (hFN' hyF) with hs
    let ψ : ↥E →* ↥E := MonoidHom.id ↥E * (s.toMonoidHom)⁻¹
    have hψ : ∀ e : ↥E, ψ e = e * (s e)⁻¹ := fun e => rfl
    have hkerle : Nat.card ↥ψ.ker ≤ 5 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : ↥ψ.ker => (⟨x.1, ?_⟩ : {u : ↥E // s u = u})) ?_) hyfix
      · have h1 : ψ x.1 = 1 := x.2
        rw [hψ] at h1
        exact (mul_inv_eq_one.1 h1).symm
      · intro x x' hxx'
        exact Subtype.ext (congrArg (fun z : {u : ↥E // s u = u} => z.1) hxx')
    have hmul := Subgroup.card_ker_mul_card_range ψ
    rw [hcardE] at hmul
    have hrange : 125 ≤ Nat.card ↥ψ.range := by
      by_contra hlt
      have := Nat.mul_le_mul hkerle (Nat.le_of_lt_succ (not_le.1 hlt))
      omega
    set Q : Subgroup G := ψ.range.map E.subtype with hQ
    have hQcard : Nat.card ↥Q = Nat.card ↥ψ.range :=
      Subgroup.card_map_of_injective E.subtype_injective
    have hQE : Q ≤ E := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have hQX : Q ≤ X := by
      rintro _ ⟨q, ⟨e, rfl⟩, rfl⟩
      have hyX : y ∈ X := hFX hyF
      have heP : (e : G) ∈ P := hEP e.2
      have hconj : (e : G) * y * (e : G)⁻¹ ∈ X := by
        have := Subgroup.Normal.conj_mem hXn ⟨y, hXP hyX⟩ (Subgroup.mem_subgroupOf.2 hyX)
          ⟨e, heP⟩
        exact Subgroup.mem_subgroupOf.1 this
      have hval : ((ψ e : ↥E) : G) = ((e : G) * y * (e : G)⁻¹) * y⁻¹ := by
        rw [hψ]
        have h1 : ((s e : ↥E) : G) = y * (e : G) * y⁻¹ := Equivariance.coe_conjAut _ e
        show ((e * (s e)⁻¹ : ↥E) : G) = _
        rw [Subgroup.coe_mul, Subgroup.coe_inv, h1]
        group
      show ((ψ e : ↥E) : G) ∈ X
      rw [hval]
      exact X.mul_mem hconj (X.inv_mem hyX)
    have hQe : IsElementaryAbelian 5 ↥Q := isElementaryAbelian_of_le hEel hQE
    have hFQ := hFmax Q hQX hQe
    have hFcard : 25 < Nat.card ↥F := by omega
    exact hyE (le_E_of_card_gt h M hFN hFe hFcard hyF)
  exact hFE hxF

theorem kf155Five_of_mod (hMod : KFU5Mod) : KF155Five := by
  intro G _ _ p A c L E h15 hF hout P hP
  classical
  have h := h15.h12
  have hp := h.prime
  have h3 := h.three_lt
  obtain ⟨M⟩ := nonempty_modData hMod h15 hF hout
  by_cases h5 : p = 5
  · subst h5
    have hcardE : Nat.card ↥E = 5 ^ 4 := by
      obtain ⟨-, -, -, -, -, hc, -, -⟩ := hout
      exact hc
    have hEP := E_le_of_sylow h hP
    have hPN : P ≤ torusNormalizer E := hP.1
    refine Or.inr ⟨hout, rfl, ?_, ?_⟩
    · intro F hFP hFe hF3
      refine le_E_of_card_gt h M (hFP.trans hPN) hFe ?_
      rw [hF3]
      norm_num
    · intro X hXP hXn
      exact thompson_le_E h M hcardE hPN hEP hXP hXn
  · left
    obtain ⟨W₀, hW⟩ := kf154Five_of_mod hMod G p A c L E h15 hF hout
    refine omegaOne_eq_of_le h hW ?_ hP
    rw [Nat.card_congr M.θ.toEquiv, card_perm5]
    exact not_dvd_120 hp h3 h5

end Sec153

end CFSG.RankThree.PartOne
