module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndX
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndPairs
public import CFSG.LinearAlgebra.SteinbergBQAutomizerPermutation
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.LocalAnalysis.SignalizerFunctor.SurjectiveSylowLifting
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Subgroup
open scoped Matrix

variable {G : Type*} [Group G] [Finite G]

theorem odd_card_of_forall_odd_orderOf {H : Type*} [Group H] [Finite H]
    (h : ∀ x : H, Odd (orderOf x)) : Odd (Nat.card H) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have := h x
  rw [hx] at this
  exact (Nat.not_odd_iff_even.mpr even_two) this

theorem coprime_two_card_ker_mk' :
    Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (oddCore G)).ker) := by
  rw [QuotientGroup.ker_mk']
  exact Nat.coprime_two_left.mpr (CFSG.ABGDGroups.odd_card_oddCore G)

theorem odd_orderOf_of_mem_oddCore' {o : G} (ho : o ∈ oddCore G) : Odd (orderOf o) := by
  have h := orderOf_dvd_natCard (⟨o, ho⟩ : oddCore G)
  rw [Subgroup.orderOf_mk] at h
  exact (CFSG.ABGDGroups.odd_card_oddCore G).of_dvd_nat h

theorem exists_lift_two (Q : Subgroup (G ⧸ oddCore G)) (hQ : IsPGroup 2 Q) :
    ∃ R : Subgroup G, R.map (QuotientGroup.mk' (oddCore G)) = Q ∧
      Function.Injective ((QuotientGroup.mk' (oddCore G)).comp R.subtype) ∧ IsPGroup 2 R ∧
      (Q.Normal → (normalizer (R : Set G)).map (QuotientGroup.mk' (oddCore G)) = ⊤) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (oddCore G) with hπ
  set N := Q.comap π with hN
  let πN : N →* Q := (π.comp N.subtype).codRestrict Q (fun x => x.2)
  have hπN : Function.Surjective πN := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (oddCore G) y
    exact ⟨⟨x, by change π x ∈ Q; rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  obtain ⟨P, hP⟩ :=
    CFSG.SignalizerFunctor.Helpers.surjective_pgroup_sylow_lift 2 Nat.prime_two πN hπN hQ
  set R := (P : Subgroup N).map N.subtype with hR
  have hR2 : IsPGroup 2 R := P.isPGroup'.map N.subtype
  have hRQ : R.map π = Q := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact x.2
    · intro y hy
      have : (⟨y, hy⟩ : Q) ∈ (P : Subgroup N).map πN := by rw [hP]; exact mem_top _
      obtain ⟨x, hx, hxy⟩ := this
      exact ⟨x, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩
  refine ⟨R, hRQ, CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_injective_on_pGroup 2
    Nat.prime_two π coprime_two_card_ker_mk' R hR2, hR2, fun hQn => ?_⟩
  have : N.Normal := hQn.comap π
  have hsup := Sylow.normalizer_sup_eq_top P
  have hmap := congrArg (Subgroup.map π) hsup
  have hNmap : N.map π = Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Q
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _),
    hNmap] at hmap
  rw [← hmap]
  refine le_antisymm le_sup_left (sup_le le_rfl ?_)
  rw [← hRQ]
  exact Subgroup.map_mono (Subgroup.le_normalizer)

omit [Finite G] in
theorem eq_of_mk_eq {R : Subgroup G}
    (hR : Function.Injective ((QuotientGroup.mk' (oddCore G)).comp R.subtype)) {r r' : G}
    (hr : r ∈ R) (hr' : r' ∈ R) (h : (r : G ⧸ oddCore G) = r') : r = r' :=
  congrArg Subtype.val (hR (show (QuotientGroup.mk' (oddCore G)).comp R.subtype ⟨r, hr⟩ =
    (QuotientGroup.mk' (oddCore G)).comp R.subtype ⟨r', hr'⟩ from h))

omit [Finite G] in
theorem mk_eq_one_of_map_eq_one {H : Type*} [Group H] {ρ : G →* H}
    (hρ : ∀ y, ρ y = 1 → y ∈ oddCore G) {y : G} (hy : ρ y = 1) :
    (y : G ⧸ oddCore G) = 1 :=
  (QuotientGroup.eq_one_iff y).mpr (hρ y hy)

variable [Group.IsPerfect G] {p : ℕ} [Fact p.Prime]

theorem le_center_of_normal_abelian (hp2 : p ≠ 2) {ρ : G →* GL (Fin 4) (ZMod p)}
    (hρ : ∀ y, ρ y = 1 → y ∈ oddCore G) (A : Subgroup (G ⧸ oddCore G)) (hA : A.Normal)
    (hA2 : IsPGroup 2 A) (hAc : IsMulCommutative A) : A ≤ center (G ⧸ oddCore G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (oddCore G) with hπ
  obtain ⟨R, hRA, hRinj, hR2, hRN⟩ := exists_lift_two A hA2
  have hRN' := hRN hA
  have hRc : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := by
    intro r hr r' hr'
    have h1 : π r ∈ A := hRA ▸ mem_map_of_mem π hr
    have h2 : π r' ∈ A := hRA ▸ mem_map_of_mem π hr'
    refine eq_of_mk_eq hRinj (mul_mem hr hr') (mul_mem hr' hr) ?_
    have := hAc.is_comm.comm ⟨_, h1⟩ ⟨_, h2⟩
    exact congrArg Subtype.val this
  set ρ' : G →* LinearMap.GeneralLinearGroup (ZMod p) (Fin 4 → ZMod p) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ with hρ'
  let GLp := LinearMap.GeneralLinearGroup (ZMod p) (Fin 4 → ZMod p)
  have hρ'inj : ∀ y, ρ' y = 1 → ρ y = 1 := fun y hy =>
    Matrix.GeneralLinearGroup.toLin.injective (by rw [map_one]; exact hy)
  set A' := R.map ρ' with hA'
  have : Finite A' := Finite.of_surjective (ρ'.subgroupMap R) (ρ'.subgroupMap_surjective R)
  have hA'comm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    rw [← map_mul, ← map_mul, hRc r hr r' hr']
  have hA'2 : IsPGroup 2 A' := hR2.map ρ'
  have hA'cop : Nat.Coprime (Nat.card A') p := by
    obtain ⟨k, hk⟩ := hA'2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two (Fact.out)).mpr
      (Ne.symm hp2))
  have hfin : Module.finrank (ZMod p) (Fin 4 → ZMod p) = 4 := Module.finrank_fin_fun _
  obtain ⟨-, -, -, -, -, hsol⟩ :=
    CFSG.LinearAlgebra.abelian_coprime_matrix_automizer_permutation_embedding (p := p)
      (by rw [hfin]; norm_num) A' hA'comm hA'cop
  have hQsol := hsol (by rw [hfin])
  set NR := normalizer (R : Set G) with hNR
  have hnorm : ∀ n : NR, ρ' n ∈ normalizer (A' : Set GLp) := by
    intro n
    refine mem_normalizer_fintype fun a ha => ?_
    obtain ⟨r, hr, rfl⟩ := ha
    refine ⟨(n : G) * r * (n : G)⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (mem_normalizer_iff.mp n.2 r).mp hr
  let φ : NR →* normalizer (A' : Set GLp) := (ρ'.comp NR.subtype).codRestrict _ hnorm
  let ψ : NR →* normalizer (A' : Set GLp) ⧸
      (centralizer (A' : Set GLp)).subgroupOf (normalizer (A' : Set GLp)) :=
    (QuotientGroup.mk' _).comp φ
  obtain ⟨k, hk⟩ := hQsol.solvable
  have hder : derivedSeries NR k ≤ ψ.ker := by
    intro n hn
    have := map_derivedSeries_le_derivedSeries ψ k ⟨n, hn, rfl⟩
    rw [hk, mem_bot] at this
    exact this
  have hcen : ∀ n ∈ ψ.ker, ∀ r ∈ R, (n : G) * r = r * n := by
    intro n hn r hr
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf] at hn
    have h1 : ρ' r * ρ' n = ρ' n * ρ' r := mem_centralizer_iff.mp hn _ ⟨r, hr, rfl⟩
    have hmem : (n : G) * r * (n : G)⁻¹ ∈ R := (mem_normalizer_iff.mp n.2 r).mp hr
    have h2 : ρ ((n : G) * r * (n : G)⁻¹ * r⁻¹) = 1 := by
      apply hρ'inj
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    have h3 := mk_eq_one_of_map_eq_one hρ h2
    have h4 : (n : G) * r * (n : G)⁻¹ = r := by
      refine eq_of_mk_eq hRinj hmem hr ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h3
      calc ((n * r * (n : G)⁻¹ : G) : G ⧸ oddCore G)
          = ((n * r * (n : G)⁻¹ : G) : G ⧸ oddCore G) * (r : G ⧸ oddCore G)⁻¹ * r := by group
        _ = r := by rw [h3, one_mul]
    calc (n : G) * r = (n : G) * r * (n : G)⁻¹ * n := by group
      _ = r * n := by rw [h4]
  have hsurj : Function.Surjective (π.comp NR.subtype) := by
    intro x
    have : x ∈ NR.map π := by rw [hRN']; exact mem_top x
    obtain ⟨n, hn, rfl⟩ := this
    exact ⟨⟨n, hn⟩, rfl⟩
  intro a ha
  rw [mem_center_iff]
  intro x
  have hx : x ∈ (derivedSeries NR k).map (π.comp NR.subtype) := by
    rw [map_derivedSeries_eq hsurj, Group.IsPerfect.derivedSeries_eq_top]
    exact mem_top x
  obtain ⟨n, hn, rfl⟩ := hx
  have hra : a ∈ R.map π := hRA ▸ ha
  obtain ⟨r, hr, rfl⟩ := hra
  have := hcen n (hder hn) r hr
  change π n * π r = π r * π n
  rw [← map_mul, ← map_mul, this]

omit [Group.IsPerfect G] in
theorem le_center_of_perfect_lift {H : Type*} [Group H] {ρ : G →* H}
    (hρ : ∀ y, ρ y = 1 → y ∈ oddCore G) {M : Subgroup G}
    (hM : M.map (QuotientGroup.mk' (oddCore G)) = ⊤)
    (h2 : ∀ N : Subgroup (M.map ρ), N.Normal → IsPGroup 2 N → N ≤ center (M.map ρ))
    (hodd : ∀ N : Subgroup (M.map ρ), N.Normal → Odd (Nat.card N) → N = ⊥)
    (N : Subgroup (G ⧸ oddCore G)) (hN : N.Normal) (hN2 : IsPGroup 2 N) :
    N ≤ center (G ⧸ oddCore G) := by
  set π := QuotientGroup.mk' (oddCore G) with hπ
  set ρM : M →* M.map ρ := ρ.subgroupMap M with hρM
  have hρMs : Function.Surjective ρM := ρ.subgroupMap_surjective M
  have : Finite (M.map ρ) := Finite.of_surjective ρM hρMs
  have hkill : ∀ m ∈ M, m ∈ oddCore G → ρ m = 1 := by
    set N₁ := ((oddCore G).subgroupOf M).map ρM with hN₁
    have hN₁n : N₁.Normal := (Subgroup.normal_subgroupOf).map ρM hρMs
    have hN₁odd : Odd (Nat.card N₁) := by
      refine odd_card_of_forall_odd_orderOf ?_
      rintro ⟨_, m, hm, rfl⟩
      have h1 : orderOf (ρM m) ∣ orderOf m := orderOf_map_dvd ρM m
      have h2 : Odd (orderOf m) := by
        rw [← Subgroup.orderOf_coe]
        exact odd_orderOf_of_mem_oddCore' hm
      rw [← Subgroup.orderOf_coe]
      exact h2.of_dvd_nat h1
    have hbot := hodd N₁ hN₁n hN₁odd
    intro m hm hmO
    have : ρM ⟨m, hm⟩ ∈ N₁ := ⟨⟨m, hm⟩, hmO, rfl⟩
    rw [hbot, mem_bot] at this
    exact congrArg Subtype.val this
  set N₂ := (N.comap (π.comp M.subtype)).map ρM with hN₂
  have hN₂n : N₂.Normal := (hN.comap _).map ρM hρMs
  have hN₂2 : IsPGroup 2 N₂ := by
    rintro ⟨_, m, hm, rfl⟩
    obtain ⟨k, hk⟩ := hN2 ⟨π m, hm⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : π (m : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hmk : ((m : G) ^ 2 ^ k) ∈ oddCore G := by
      rw [← map_pow] at hk'
      rwa [← QuotientGroup.ker_mk' (oddCore G), MonoidHom.mem_ker]
    have := hkill _ (pow_mem m.2 _) hmk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    exact Subtype.ext this
  have hN₂c := h2 N₂ hN₂n hN₂2
  intro n hn
  rw [mem_center_iff]
  intro x
  obtain ⟨m, hm, hmn⟩ : n ∈ M.map π := by rw [hM]; exact mem_top n
  obtain ⟨m', hm', hmx⟩ : x ∈ M.map π := by rw [hM]; exact mem_top x
  subst hmn hmx
  have hρm : ρM ⟨m, hm⟩ ∈ N₂ := ⟨⟨m, hm⟩, hn, rfl⟩
  have hc := mem_center_iff.mp (hN₂c hρm) (ρM ⟨m', hm'⟩)
  have hc' : ρ (m' * m * (m * m')⁻¹) = 1 := by
    have h1 : ρ m' * ρ m = ρ m * ρ m' := congrArg Subtype.val hc
    rw [map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel]
  have := mk_eq_one_of_map_eq_one hρ hc'
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at this
  change π m' * π m = π m * π m'
  exact this

theorem normal_two_le_center_of_involution (hp5 : 5 ≤ p) {ρ : G →* GL (Fin 4) (ZMod p)}
    (hρ : ∀ y, ρ y = 1 → y ∈ oddCore G)
    (hdet : ∀ y, (ρ y : Matrix (Fin 4) (Fin 4) (ZMod p)).det = 1) {a₀ : G} (ha₀ : ρ a₀ = -1)
    {t : G ⧸ oddCore G} (ht : t ∈ center (G ⧸ oddCore G)) (htt : t * t = 1) (ht1 : t ≠ 1)
    (hta : t ≠ (a₀ : G ⧸ oddCore G)) (N : Subgroup (G ⧸ oddCore G)) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N ≤ center (G ⧸ oddCore G) := by
  set π := QuotientGroup.mk' (oddCore G) with hπ
  have hQn : (zpowers t).Normal := normal_of_le_center (zpowers_le.mpr ht)
  have hQ2 : IsPGroup 2 (zpowers t) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, htt, one_zpow]
  obtain ⟨R, hRQ, hRinj, -, hRN⟩ := exists_lift_two (zpowers t) hQ2
  have hRN' := hRN hQn
  obtain ⟨s, hs, hst⟩ : t ∈ R.map π := by rw [hRQ]; exact mem_zpowers t
  have hss : s * s = 1 := eq_of_mk_eq hRinj (mul_mem hs hs) (one_mem R) (by
    change π (s * s) = π 1
    rw [map_mul, hst, htt, map_one])
  have hS1 : ρ s ≠ 1 := fun h => ht1 (by rw [← hst]; exact mk_eq_one_of_map_eq_one hρ h)
  have hSm : ρ s ≠ -1 := fun h => hta (by
    rw [← hst]
    have h1 : ρ (s * a₀⁻¹) = 1 := by rw [map_mul, map_inv, h, ha₀, mul_inv_cancel]
    have h2 := mk_eq_one_of_map_eq_one hρ h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h2
    exact h2)
  have hcomm : ∀ n ∈ normalizer (R : Set G), n * s = s * n := by
    intro n hn
    have hmem : n * s * n⁻¹ ∈ R := (mem_normalizer_iff.mp hn s).mp hs
    have h1 : n * s * n⁻¹ = s := eq_of_mk_eq hRinj hmem hs (by
      change π (n * s * n⁻¹) = π s
      rw [map_mul, map_mul, map_inv, hst, mem_center_iff.mp ht (π n), mul_inv_cancel_right])
    calc n * s = n * s * n⁻¹ * n := by group
      _ = s * n := by rw [h1]
  set M := CFSG.Quasithin.perfectCore (normalizer (R : Set G)) with hMdef
  have hMp : Group.IsPerfect M :=
    Subgroup.isPerfect_iff.mpr (CFSG.Quasithin.perfectCore_perfect _)
  have hMmap : M.map π = ⊤ := by
    rw [hMdef, CFSG.Quasithin.map_perfectCore, hRN']
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect Subgroup.commutator_eq_self
  have hMle : M ≤ normalizer (R : Set G) := CFSG.Quasithin.perfectCore_le _
  have hHp : Group.IsPerfect (M.map ρ) := Group.IsPerfect.map ρ
  obtain ⟨h2, hodd⟩ := normal_of_commute_involution hp5 hHp
    (by rw [← map_mul, hss, map_one]) hS1 hSm (hdet s) (by
      rintro _ ⟨m, hm, rfl⟩
      rw [← map_mul, ← map_mul, hcomm m (hMle hm)])
  exact le_center_of_perfect_lift hρ hMmap h2 hodd N hN hN2

theorem det_scalar_four {R : Type*} [CommRing R] (μ : R) :
    (Matrix.scalar (Fin 4) μ).det = μ ^ 4 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

omit [Group.IsPerfect G] in
theorem pairBound (hp5 : 5 ≤ p) {ρ : G →* GL (Fin 4) (ZMod p)}
    (hρ : ∀ y, ρ y = 1 → y ∈ oddCore G)
    (hdet : ∀ y, (ρ y : Matrix (Fin 4) (Fin 4) (ZMod p)).det = 1) {a₀ : G} (ha₀2 : a₀ * a₀ = 1)
    (ha₀ : ρ a₀ = -1) : PairBound (G ⧸ oddCore G) (a₀ : G ⧸ oddCore G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (oddCore G) with hπ
  intro u₁ v₁ u₂ v₂ c c' hu₁ hv₁ hu₂ hv₂ hc hc' hpd₀ hcx hc'x
  set z₀ : G ⧸ oddCore G := π a₀ with hz₀
  have hpd : PairData z₀ u₁ v₁ u₂ v₂ := hpd₀
  set P := closure ({u₁, v₁, u₂, v₂, c, c'} : Set (G ⧸ oddCore G)) with hP
  have hPS : P ≤ pCore 2 (G ⧸ oddCore G) := by
    rw [hP, closure_le]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  have hP2 : IsPGroup 2 P := (pCore_isPGroup : IsPGroup 2 (pCore 2 _)).to_le hPS
  obtain ⟨R, hRP, hRinj, -, -⟩ := exists_lift_two P hP2
  have hlift : ∀ g ∈ P, ∃ r ∈ R, π r = g := fun g hg => by
    rw [← hRP] at hg
    obtain ⟨r, hr, rfl⟩ := hg
    exact ⟨r, hr, rfl⟩
  have hmem : ∀ g ∈ ({u₁, v₁, u₂, v₂, c, c'} : Set (G ⧸ oddCore G)), g ∈ P :=
    fun g hg => subset_closure hg
  obtain ⟨uL₁, huL₁, hπu₁⟩ := hlift u₁ (hmem _ (by simp))
  obtain ⟨vL₁, hvL₁, hπv₁⟩ := hlift v₁ (hmem _ (by simp))
  obtain ⟨uL₂, huL₂, hπu₂⟩ := hlift u₂ (hmem _ (by simp))
  obtain ⟨vL₂, hvL₂, hπv₂⟩ := hlift v₂ (hmem _ (by simp))
  obtain ⟨cL, hcL, hπc⟩ := hlift c (hmem _ (by simp))
  obtain ⟨cL', hcL', hπc'⟩ := hlift c' (hmem _ (by simp))
  have hz₀P : z₀ ∈ P := by
    have : z₀ = u₁ * v₁ * (v₁ * u₁)⁻¹ := by rw [hpd.comm₁]; group
    rw [this]
    exact mul_mem (mul_mem (hmem _ (by simp)) (hmem _ (by simp)))
      (inv_mem (mul_mem (hmem _ (by simp)) (hmem _ (by simp))))
  obtain ⟨zL, hzL, hπz⟩ := hlift z₀ hz₀P
  have hlift_eq : ∀ r ∈ R, ∀ r' ∈ R, π r = π r' → r = r' := fun r hr r' hr' h =>
    eq_of_mk_eq hRinj hr hr' h
  have hzLzL : zL * zL = 1 := hlift_eq _ (mul_mem hzL hzL) _ (one_mem R) (by
    rw [map_mul, hπz, map_one, hz₀, ← map_mul, ha₀2, map_one])
  have hρz : ρ zL = -1 := by
    set o := zL * a₀⁻¹ with ho
    have hoO : o ∈ oddCore G := by
      rw [← QuotientGroup.ker_mk' (oddCore G), MonoidHom.mem_ker, map_mul, map_inv, hπz,
        mul_inv_cancel]
    have hzo : ρ zL = ρ o * (-1) := by rw [ho, map_mul, map_inv, ha₀, mul_assoc, inv_mul_cancel,
      mul_one]
    have hoo : ρ o * ρ o = 1 := by
      have h1 : ρ zL * ρ zL = 1 := by rw [← map_mul, hzLzL, map_one]
      rwa [hzo, mul_neg_one, neg_mul_neg] at h1
    have h1 : orderOf (ρ o) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hoo])
    have h2 : orderOf (ρ o) ∣ orderOf o := orderOf_map_dvd ρ o
    have h3 : orderOf (ρ o) = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_left.mpr (odd_orderOf_of_mem_oddCore' hoO)) h1 h2
    rw [hzo, orderOf_eq_one_iff.mp h3, one_mul]
  have hsq : ∀ {x : G ⧸ oddCore G} {r : G}, r ∈ R → π r = x → (x * x = 1 ∨ x * x = z₀) →
      ((ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) * (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) = 1 ∨
        (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) * (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) =
          -1) := by
    intro x r hr hrx hx
    rcases hx with hx | hx
    · left
      have : r * r = 1 := hlift_eq _ (mul_mem hr hr) _ (one_mem R) (by
        rw [map_mul, hrx, hx, map_one])
      rw [← Units.val_mul, ← map_mul, this, map_one, Units.val_one]
    · right
      have : r * r = zL := hlift_eq _ (mul_mem hr hr) _ hzL (by rw [map_mul, hrx, hx, hπz])
      rw [← Units.val_mul, ← map_mul, this, hρz, Units.val_neg, Units.val_one]
  have hanti : ∀ {x y : G ⧸ oddCore G} {r s : G}, r ∈ R → s ∈ R → π r = x → π s = y →
      x * y = z₀ * (y * x) →
      (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) * (ρ s : Matrix (Fin 4) (Fin 4) (ZMod p)) =
        -((ρ s : Matrix (Fin 4) (Fin 4) (ZMod p)) * (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p))) :=
      by
    intro x y r s hr hs hrx hsy hxy
    have : r * s = zL * (s * r) := hlift_eq _ (mul_mem hr hs) _ (mul_mem hzL (mul_mem hs hr)) (by
      rw [map_mul, map_mul, map_mul, hrx, hsy, hπz, hxy])
    rw [← Units.val_mul, ← map_mul, this, map_mul, hρz, ← Units.val_mul, neg_one_mul,
      Units.val_neg, map_mul, Units.val_mul]
  have hcm : ∀ {x y : G ⧸ oddCore G} {r s : G}, r ∈ R → s ∈ R → π r = x → π s = y →
      x * y = y * x →
      (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) * (ρ s : Matrix (Fin 4) (Fin 4) (ZMod p)) =
        (ρ s : Matrix (Fin 4) (Fin 4) (ZMod p)) * (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) := by
    intro x y r s hr hs hrx hsy hxy
    have : r * s = s * r := hlift_eq _ (mul_mem hr hs) _ (mul_mem hs hr) (by
      rw [map_mul, map_mul, hrx, hsy, hxy])
    rw [← Units.val_mul, ← map_mul, this, map_mul, Units.val_mul]
  have hscal : ∀ {d : G ⧸ oddCore G} {r : G}, r ∈ R → π r = d →
      (∀ x ∈ ({u₁, v₁, u₂, v₂} : Set (G ⧸ oddCore G)), d * x = x * d) →
      ∃ μ : ZMod p, (ρ r : Matrix (Fin 4) (Fin 4) (ZMod p)) = Matrix.scalar (Fin 4) μ := by
    intro d r hr hrd hd
    exact eq_scalar_of_commute_pairs hp5 (hsq huL₁ hπu₁ hpd.sq_u₁) (hsq hvL₁ hπv₁ hpd.sq_v₁)
      (hsq huL₂ hπu₂ hpd.sq_u₂) (hsq hvL₂ hπv₂ hpd.sq_v₂) (hanti huL₁ hvL₁ hπu₁ hπv₁ hpd.comm₁)
      (hanti huL₂ hvL₂ hπu₂ hπv₂ hpd.comm₂) (hcm huL₁ huL₂ hπu₁ hπu₂ hpd.uu)
      (hcm huL₁ hvL₂ hπu₁ hπv₂ hpd.uv) (hcm hvL₁ huL₂ hπv₁ hπu₂ hpd.vu)
      (hcm hvL₁ hvL₂ hπv₁ hπv₂ hpd.vv) (hcm hr huL₁ hrd hπu₁ (hd _ (by simp)))
      (hcm hr hvL₁ hrd hπv₁ (hd _ (by simp))) (hcm hr huL₂ hrd hπu₂ (hd _ (by simp)))
      (hcm hr hvL₂ hrd hπv₂ (hd _ (by simp)))
  obtain ⟨μ, hμ⟩ := hscal hcL hπc hcx
  obtain ⟨μ', hμ'⟩ := hscal hcL' hπc' hc'x
  constructor
  ·
    have h4 : ρ (cL ^ 4) = 1 := by
      apply Units.ext
      rw [map_pow, Units.val_pow_eq_pow_val, hμ, ← map_pow, Units.val_one]
      have hd := hdet cL
      rw [hμ, det_scalar_four] at hd
      rw [hd, map_one]
    have := mk_eq_one_of_map_eq_one hρ h4
    rw [QuotientGroup.mk_pow] at this
    rw [← hπc]
    exact this
  ·
    have h1 : ρ (cL * cL' * (cL' * cL)⁻¹) = 1 := by
      have hc : ρ cL * ρ cL' = ρ cL' * ρ cL :=
        Units.ext (by rw [Units.val_mul, Units.val_mul, hμ, hμ', ← map_mul, ← map_mul, mul_comm])
      rw [map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one]
      exact hc
    have := mk_eq_one_of_map_eq_one hρ h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at this
    rw [← hπc, ← hπc']
    exact this

end CFSG.RankThree.PartTwo.Sec4.Census
