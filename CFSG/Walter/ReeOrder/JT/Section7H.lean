module

public import CFSG.Walter.ReeOrder.JT.Section7G
public import CFSG.Walter.ReeOrder.JT.AuxElemRep
public import CFSG.Walter.ReeOrder.JT.AuxGW
public import CFSG.Walter.ReeOrder.JT.AuxPSL2Borel
public import CFSG.Walter.Cited.Suzuki
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Walter.ReeOrder.JT.Section7E

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups


section Helpers

theorem factorization_two_eq_two {n : ℕ} (h4 : 4 ∣ n) (h8 : ¬ 8 ∣ n) :
    n.factorization 2 = 2 := by
  have hn : n ≠ 0 := by rintro rfl; exact h8 (dvd_zero 8)
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn (k := 2)).mp
    (by norm_num; exact h4)
  have h2 : ¬ 3 ≤ n.factorization 2 := fun h3 =>
    h8 (by have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn (k := 3)).mpr h3
           norm_num at this; exact this)
  omega

theorem charP_of_card_eq_pow {K : Type*} [Field K] [Finite K] {s n : ℕ} (hs : s.Prime)
    (hn : 1 ≤ n) (hK : Nat.card K = s ^ n) : CharP K s := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨c, hc, m, hcp, hcm⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcm
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', hm'⟩ : ∃ m', (m : ℕ) = m' + 1 := ⟨(m : ℕ) - 1, by have := m.pos; omega⟩
  rw [hm'] at hcm
  have := (Nat.Prime.pow_inj hs hcp hcm).1
  rw [this]
  exact hc

theorem isInvolved_of_range {Y N M : Type*} [Group Y] [Group N] [Group M] (φ : N →* M)
    (hY : IsInvolved Y φ.range) : IsInvolved Y N :=
  isInvolved_of_glauberman (Glauberman.involved_of_involved_quotient φ.ker
    (glauberman_of_isInvolved (isInvolved_of_mulEquiv_right hY
      (QuotientGroup.quotientKerEquivRange φ).symm)))

theorem isInvolved_of_subgroup
    {Y G : Type*} [Group Y] [Group G] {H : Subgroup G}
    (hY : IsInvolved Y H) : IsInvolved Y G :=
  isInvolved_of_glauberman (Glauberman.involved_of_involved_subgroup
    (glauberman_of_isInvolved hY))

theorem isInvolved_of_quotient {Y X : Type*} [Group Y] [Group X] (N : Subgroup X) [N.Normal]
    (hY : IsInvolved Y (X ⧸ N)) : IsInvolved Y X :=
  isInvolved_of_glauberman (Glauberman.involved_of_involved_quotient N
    (glauberman_of_isInvolved hY))

theorem card_comap_of_surjective {X Y : Type*} [Group X] [Group Y] [Finite X] {f : X →* Y}
    (hf : Function.Surjective f) (H : Subgroup Y) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  have hkerle : f.ker ≤ H.comap f := fun x hx => by
    change f x ∈ H
    rw [MonoidHom.mem_ker.mp hx]
    exact H.one_mem
  let ψ : H.comap f →* H := (f.comp (H.comap f).subtype).codRestrict _ fun x => x.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hψker : ψ.ker = f.ker.subgroupOf (H.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← OneMemClass.coe_eq_one]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hψker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv] at h1
  exact h1

theorem prime_eq_three_five_seven {s : ℕ} (hs : s.Prime) (h3 : 3 ≤ s) (h7 : s ≤ 7) :
    s = 3 ∨ s = 5 ∨ s = 7 := by
  interval_cases s
  · exact Or.inl rfl
  · exact absurd hs (by norm_num)
  · exact Or.inr (Or.inl rfl)
  · exact absurd hs (by norm_num)
  · exact Or.inr (Or.inr rfl)

end Helpers

section A5

theorem nonempty_psl2_equiv_psl24
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nonempty (PSL(2, K) ≃* PSL(2, GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr hK)
  have h4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 two_ne_zero]
    norm_num
  obtain ⟨e₂⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl h4)
  exact ⟨((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).trans
    e₁).trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 2)).trans e₂).symm⟩

end A5

section Conj

variable {G : Type*} [Group G]

@[expose] noncomputable def conjHom (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) →* MulAut A :=
  @MulDistribMulAction.toMulAut _ _ _ _ (conjAct (Subgroup.normalizer (A : Set G)) A le_rfl)

theorem conjHom_apply_coe (A : Subgroup G) (n : Subgroup.normalizer (A : Set G)) (a : A) :
    ((conjHom A n a : A) : G) = n * a * (n : G)⁻¹ := rfl

theorem conjHom_eq_one_iff (A : Subgroup G) (n : Subgroup.normalizer (A : Set G)) :
    conjHom A n = 1 ↔ (n : G) ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 a ha
    have := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h1
    simp only [conjHom_apply_coe, MulAut.one_apply] at this
    calc a * n = (n * a * (n : G)⁻¹) * n := by rw [this]
      _ = n * a := by group
  · intro h1
    ext a
    rw [conjHom_apply_coe, MulAut.one_apply, ← h1 a a.2, mul_inv_cancel_right]

end Conj

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem isSolvable_normalizer_of_elementary_pi
    {r : ℕ} [hr : Fact r.Prime]
    (hrq : r ∣ (h.q - 1) / 2) {A : Subgroup G} (hAr : IsPGroup r A)
    (hAexp : ∀ x ∈ A, x ^ r = 1) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA1 : A ≠ ⊥) :
    Group.IsSolvable (Subgroup.normalizer (A : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr7 := h.seven_le_of_pi hp3 hrq
  by_contra hns
  set N := Subgroup.normalizer (A : Set G) with hNdef
  have h8 := h.not_eight_dvd_card_normalizer_of_pi hp3 hrq hAr hA1
  have h4 : 4 ∣ Nat.card N := by
    by_contra h4
    exact hns (isSolvable_of_not_four_dvd h4)
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := N) 2 (n := 2)
    (by norm_num; exact h4)
  set T₀ : Subgroup G := W.map N.subtype with hT₀def
  have hT₀N : T₀ ≤ N := Subgroup.map_subtype_le _
  have hT₀card : Nat.card T₀ = 4 := by
    rw [hT₀def, Subgroup.card_map_of_injective N.subtype_injective, hW]
    norm_num
  have hT₀2 : IsPGroup 2 T₀ := IsPGroup.of_card (n := 2) (by rw [hT₀card]; norm_num)
  have hT₀ : IsKleinFour T₀ := isKleinFour_of_card_four hT₀card fun x =>
    Subtype.ext (h.mul_self_of_isPGroup_two hp3 hT₀2 x.2)
  have hAcard := h.card_le_cube hp3 hrq hAr hAexp hT₀ hT₀N
  have : IsElementaryAbelian r A :=
    { is_comm := ⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hAexp a a.2) }
  set φ := conjHom A with hφ
  set X := φ.range with hX
  set φ' := φ.rangeRestrict
  have hφ' : Function.Surjective φ' := φ.rangeRestrict_surjective
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha1' : a ≠ 1 := fun h0 => ha1 (Subtype.ext h0)
  have ha2 : a ^ 2 ≠ 1 := by
    intro h2
    have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h3 : orderOf a ∣ r := orderOf_dvd_of_pow_eq_one (hAexp a haA)
    have : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_primes Nat.prime_two hr.out).mpr (by omega)) h1 h3
    exact ha1' (orderOf_eq_one_iff.mp this)
  have hCa := h.lemma_7_7_a hp3 CFSG.Walter.suzukiFourGroupTheorem ha2
  have hkersolv : Group.IsSolvable φ.ker := by
    let f : φ.ker →* Subgroup.centralizer ({a} : Set G) :=
      { toFun := fun n => ⟨((n : N) : G), by
          have := (conjHom_eq_one_iff A n).mp n.2
          rw [Subgroup.mem_centralizer_iff] at this
          exact Subgroup.mem_centralizer_singleton_iff.mpr (this a haA).symm⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun x y hxy => by
      have h1 := congrArg (fun z : Subgroup.centralizer ({a} : Set G) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Group.isSolvable_of_isSolvable_injective hf
  have hXns : ¬ Group.IsSolvable X := by
    intro hXs
    apply hns
    have : Group.IsSolvable (N ⧸ φ.ker) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientKerEquivRange φ).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange φ).injective
    exact Group.isSolvable_of_subgroup_quotient φ.ker
  have hcardN : Nat.card N = Nat.card X * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have h8X : ¬ 8 ∣ Nat.card X := fun h8' => h8 (h8'.trans ⟨_, hcardN⟩)
  have h4X : 4 ∣ Nat.card X := by
    by_contra h4X
    exact hXns (isSolvable_of_not_four_dvd h4X)
  have hkerodd : ¬ 2 ∣ Nat.card φ.ker := by
    intro hev
    apply h8
    rw [hcardN, show (8 : ℕ) = 4 * 2 by norm_num]
    exact Nat.mul_dvd_mul h4X hev
  have hX2 : ∀ S : Sylow 2 X, IsKleinFour (S : Subgroup X) := by
    intro S
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hφ' 2 S
    have hScard : Nat.card (P.mapSurjective hφ' : Subgroup X) = 4 := by
      rw [Sylow.card_eq_multiplicity, factorization_two_eq_two h4X h8X]
      norm_num
    refine isKleinFour_of_card_four hScard fun x => ?_
    obtain ⟨_, ⟨n, hn, rfl⟩⟩ := x
    have hn2 : IsPGroup 2 ((P : Subgroup N).map N.subtype) := P.isPGroup'.map _
    have hnn := h.mul_self_of_isPGroup_two hp3 hn2 ⟨n, hn, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← map_mul]
    have : n * n = 1 := Subtype.ext hnn
    rw [this, map_one]
  have hO3 : ¬ 3 ∣ Nat.card (pPrimeCore 2 X) := by
    set Ot : Subgroup N := (pPrimeCore 2 X).comap φ'
    set OG : Subgroup G := Ot.map N.subtype
    have hOtn : Ot.Normal := Subgroup.Normal.comap inferInstance φ'
    have hOcard : Nat.card OG = Nat.card (pPrimeCore 2 X) * Nat.card φ.ker := by
      rw [Subgroup.card_map_of_injective N.subtype_injective, card_comap_of_surjective hφ',
        MonoidHom.ker_rangeRestrict]
    have hOodd : ¬ 2 ∣ Nat.card OG := by
      rw [hOcard]
      intro h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h2 | h2
      · exact Nat.not_even_iff_odd.mpr Suzuki.odd_card_pPrimeCore (even_iff_two_dvd.mpr h2)
      · exact hkerodd h2
    have hT₀OG : T₀ ≤ Subgroup.normalizer (OG : Set G) := by
      rintro _ ⟨t, ht, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨t * y * t⁻¹, hOtn.conj_mem y hy t, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hx : x = ((t⁻¹ * y * t : N) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [Subgroup.coe_subtype] at hyx
          rw [hyx]
          group
        rw [hx]
        refine ⟨t⁻¹ * y * t, ?_, rfl⟩
        simpa using hOtn.conj_mem y hy t⁻¹
    obtain ⟨P₃, hP₃⟩ := exists_sylow_normalized_of_coprime hT₀2 hT₀OG hOodd 3
    have hP₃bot := h.eq_bot_of_isPGroup_three_of_le_normalizer hp3
      (P₃.isPGroup'.map OG.subtype) hT₀2 (by rw [hT₀card]) hP₃
    intro h3
    have h3G : 3 ∣ Nat.card OG := hOcard ▸ dvd_mul_of_dvd_left h3 _
    have := P₃.pow_dvd_card_of_pow_dvd_card (n := 1) (by simpa using h3G)
    rw [pow_one, ← Subgroup.card_map_of_injective OG.subtype_injective, hP₃bot,
      Subgroup.card_bot] at this
    norm_num at this
  refine exists_psl2_of_isKleinFour_sylow hX2 hXns ?_
  intro K _ _ hK L hLn hLi ⟨e⟩
  obtain ⟨s, n, hs, hsodd, hn, hKcard⟩ := hK
  have : Fact s.Prime := ⟨hs⟩
  have hchar : CharP K s := charP_of_card_eq_pow hs hn hKcard
  set Y := X ⧸ pPrimeCore 2 X
  set π : X →* Y := QuotientGroup.mk' (pPrimeCore 2 X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let f : PSL(2, K) →* Y := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hinv : ∀ (Z : Type) [Group Z] (g : Z →* PSL(2, K)), Function.Injective g →
      IsInvolved Z G := by
    intro Z _ g hg
    have h1 : IsInvolved Z Y := isInvolved_of_injective (f.comp g) (hf.comp hg)
    have h2 : IsInvolved Z X := isInvolved_of_quotient (pPrimeCore 2 X) h1
    exact isInvolved_of_subgroup (isInvolved_of_range φ h2)
  have hLcard : Nat.card L = s ^ n * ((s ^ n) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, Suzuki.card_psl2_of_card K ⟨s, n, hs, hsodd, hn, hKcard⟩
      hKcard]
  have hLdvdX : Nat.card L ∣ Nat.card X :=
    (Subgroup.card_subgroup_dvd_card L).trans card_quotient_pPrimeCore_dvd
  by_cases hsr : s = r
  ·
    subst hsr
    let g₀ : GaloisField s 1 →+* K :=
      (ZMod.castHom (dvd_refl s) K).comp (GaloisField.equivZmodP s).toRingEquiv.toRingHom
    obtain ⟨g, hg⟩ := exists_injective_psl2_map g₀
    exact h.lemma_7_5 hp3 hrq (hinv _ g hg)
  by_cases hK7 : Nat.card K ≤ 7
  · have hs3 : 3 ≤ s := by
      rcases hsodd with ⟨k, rfl⟩
      have := hs.two_le
      omega
    have hn1 : n = 1 := by
      by_contra hn1
      have : s ^ 2 ≤ s ^ n := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    subst hn1
    rw [pow_one] at hKcard hLcard
    have hs357 : s = 3 ∨ s = 5 ∨ s = 7 := prime_eq_three_five_seven hs hs3 (hKcard ▸ hK7)
    rcases hs357 with rfl | rfl | rfl
    ·
      apply hXns
      have hLs : Group.IsSolvable L := by
        refine isSolvable_of_card_eq_two_pow_mul_three_pow (a := 2) (b := 1) ?_
        rw [hLcard]
        norm_num
      have hQs : Group.IsSolvable (Y ⧸ L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by
        rw [← Subgroup.index]
        exact hLi)
      have hYs : Group.IsSolvable Y := isSolvable_of_normal L hLs hQs
      have hOs : Group.IsSolvable (pPrimeCore 2 X) :=
        CFSG.FeitThompson.isSolvable_of_odd_natCard _ Suzuki.odd_card_pPrimeCore
      exact isSolvable_of_normal (pPrimeCore 2 X) hOs hYs
    ·
      obtain ⟨e₅⟩ := nonempty_psl2_equiv_psl24 K hKcard
      exact h.lemma_7_6 hp3 (hinv _ e₅.symm.toMonoidHom e₅.symm.injective)
    ·
      apply h8X
      refine Dvd.dvd.trans ?_ hLdvdX
      rw [hLcard]
      norm_num
  push Not at hK7
  obtain ⟨E, hEs, hEc, d, hdE, x, hxE, h2, h3⟩ := exists_unipotent_of_seven_lt (r := s) hK7
  have hE's : IsPGroup s (E.map f) := hEs.map f
  have hE'c : ∀ y ∈ E.map f, ∀ z ∈ E.map f, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hEc y hy z hz]
  have hdE' : f d ∈ Subgroup.normalizer ((E.map f : Subgroup Y) : Set Y) :=
    Subgroup.le_normalizer_map f ⟨d, hdE, rfl⟩
  have h2' : f d ^ 2 * f x * (f d ^ 2)⁻¹ ≠ f x := by
    rw [← map_pow, ← map_mul, ← map_inv, ← map_mul]
    exact fun h0 => h2 (hf h0)
  have h3' : f d ^ 3 * f x * (f d ^ 3)⁻¹ ≠ f x := by
    rw [← map_pow, ← map_mul, ← map_inv, ← map_mul]
    exact fun h0 => h3 (hf h0)
  obtain ⟨R, hRs, hRE, b₁, hb₁, b₂, hb₂, hb⟩ := exists_nonabelian_of_sq_cube hAcard π
    (s := s) hsr hE's hE'c (fun y _ => hπ y) (hπ (f d)) hdE' ⟨x, hxE, rfl⟩ h2' h3'
  apply hb
  by_cases hs3 : s = 3
  ·
    subst hs3
    have hdisj : R ⊓ π.ker = ⊥ := by
      rw [QuotientGroup.ker_mk']
      rw [eq_bot_iff]
      intro y hy
      have h1 : orderOf y ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hy.1
      have h2 : orderOf y ∣ Nat.card (pPrimeCore 2 X) := Subgroup.orderOf_dvd_natCard _ hy.2
      obtain ⟨k, hk⟩ := hRs.exists_card_eq
      rw [hk] at h1
      have hcop : Nat.Coprime (3 ^ k) (Nat.card (pPrimeCore 2 X)) :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hO3)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    have hinj : ∀ y ∈ R, ∀ z ∈ R, π y = π z → y = z := by
      intro y hy z hz hyz
      have hk : y * z⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyz, mul_inv_cancel]
      have : y * z⁻¹ ∈ R ⊓ π.ker := ⟨R.mul_mem hy (R.inv_mem hz), hk⟩
      rw [hdisj, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    refine hinj _ (R.mul_mem hb₁ hb₂) _ (R.mul_mem hb₂ hb₁) ?_
    rw [map_mul, map_mul]
    exact hE'c _ (hRE hb₁) _ (hRE hb₂)
  ·
    have hs5 : 3 < s := by
      rcases hsodd with ⟨k, rfl⟩
      have := hs.two_le
      omega
    have hR' : IsPGroup s (R.map X.subtype) := hRs.map _
    have := mul_comm_of_isPGroup hAcard (r := s) hs5 hsr hR' (b₁ : MulAut A) ⟨b₁, hb₁, rfl⟩
      (b₂ : MulAut A) ⟨b₂, hb₂, rfl⟩
    exact Subtype.ext this

theorem isSolvable_normalizer_of_isPGroup_pi
    {r : ℕ} [hr : Fact r.Prime]
    (hrq : r ∣ (h.q - 1) / 2) {H : Subgroup G} (hH : IsPGroup r H) (hH1 : H ≠ ⊥) :
    Group.IsSolvable (Subgroup.normalizer (H : Set G)) := by
  have hA := h.isSolvable_normalizer_of_elementary_pi hp3 hrq (A := omegaZ H r)
    (hH.to_le omegaZ_le) (fun x hx => pow_eq_one_of_mem_omegaZ hx)
    (fun x hx y hy => mul_comm_of_mem_omegaZ hx hy) (omegaZ_ne_bot hH hH1)
  exact isSolvable_of_le normalizer_le_normalizer_omegaZ hA

end JTHyp

end CFSG.Walter.JT
