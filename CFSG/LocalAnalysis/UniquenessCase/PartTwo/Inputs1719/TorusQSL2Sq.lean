module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1919Torus
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

section Bridge

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)
open scoped commutatorElement

private theorem le_pCore_of_normal {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N ≤ CFSG.pCore 2 G :=
  le_sSup ⟨hN, hp⟩

section BarMap

variable {X : Type} [Group X]

noncomputable abbrev barMap {I J : Subgroup X} (hJI : J ≤ I) : ↥J →* Bar2 I :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion hJI)

private theorem ker_barMap {I J : Subgroup X} (hJI : J ≤ I) :
    (barMap hJI).ker = (CFSG.pCore 2 ↥I).comap (Subgroup.inclusion hJI) := by
  rw [barMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

theorem ker_barMap_le {I J : Subgroup X} (hJI : J ≤ I) :
    (barMap hJI).ker ≤ CFSG.pCore 2 ↥J := by
  refine le_pCore_of_normal (MonoidHom.normal_ker _) ?_
  rw [ker_barMap]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).comap_of_injective _
    (Subgroup.inclusion_injective hJI)

theorem barMap_injective_of_odd [Finite X] {I A : Subgroup X} (hAI : A ≤ I)
    (hA : Odd (Nat.card A)) : Function.Injective (barMap hAI) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 ↥A) := CFSG.pCore_isPGroup (p := 2) (G := ↥A)
  have hmem := ker_barMap_le hAI ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card ↥(CFSG.pCore 2 ↥A) ∣ Nat.card A := Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have : 2 ∣ Nat.card A := (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr this)
  rw [hk0, pow_zero] at hk
  have hbot : CFSG.pCore 2 ↥A = ⊥ := Subgroup.eq_bot_of_card_eq _ hk
  rw [hbot] at hmem
  exact hmem

theorem commutator_eq_self_of_oUpperTwo [Finite X] {J : Subgroup X}
    (hO : S17.oUpperTwo J = J)
    (hq : commutator (Bar2 J) = ⊤) : ⁅J, J⁆ = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (Subgroup.commutator_le_self J) ?_
  set C : Subgroup ↥J := commutator ↥J with hCdef
  have hCJ : C.map J.subtype = ⁅J, J⁆ := by
    rw [hCdef, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hCJ]
  conv_lhs => rw [← hO]
  rw [S17.oUpperTwo_eq_closure, Subgroup.closure_le]
  rintro x ⟨hxJ, hxodd⟩
  have hx' : (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) ⟨x, hxJ⟩ ∈ commutator (Bar2 J) := by
    rw [hq]; exact Subgroup.mem_top _
  rw [commutator_def, ← Subgroup.map_top_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
      (QuotientGroup.mk'_surjective _), ← Subgroup.map_commutator] at hx'
  obtain ⟨y, hyC, hyx⟩ := Subgroup.mem_map.mp hx'
  have hz : y⁻¹ * ⟨x, hxJ⟩ ∈ CFSG.pCore 2 ↥J := QuotientGroup.eq.mp hyx
  set ψ := QuotientGroup.mk' C with hψ
  have hψy : ψ y = 1 := (QuotientGroup.eq_one_iff y).mpr hyC
  have hψx : ψ ⟨x, hxJ⟩ = ψ (y⁻¹ * ⟨x, hxJ⟩) := by
    rw [map_mul, map_inv, hψy, inv_one, one_mul]
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥J) ⟨_, hz⟩
  have h2 : ψ ⟨x, hxJ⟩ ^ 2 ^ k = 1 := by
    rw [hψx, ← map_pow]
    have : (y⁻¹ * ⟨x, hxJ⟩) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    rw [this, map_one]
  have hodd : ψ ⟨x, hxJ⟩ ^ orderOf x = 1 := by
    rw [← map_pow]
    have : (⟨x, hxJ⟩ : ↥J) ^ orderOf x = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    rw [this, map_one]
  have hord1 : orderOf (ψ ⟨x, hxJ⟩) = 1 := by
    have hd1 : orderOf (ψ ⟨x, hxJ⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    have hd2 : orderOf (ψ ⟨x, hxJ⟩) ∣ orderOf x := orderOf_dvd_of_pow_eq_one hodd
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hxodd)
    have hg : orderOf (ψ ⟨x, hxJ⟩) ∣ Nat.gcd (2 ^ k) (orderOf x) := Nat.dvd_gcd hd1 hd2
    rw [hcop] at hg
    exact Nat.dvd_one.mp hg
  exact ⟨⟨x, hxJ⟩, (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hord1), rfl⟩

end BarMap

private theorem ker_eq_pCore_of_range {G Y : Type*} [Group G] [Group Y] (f : G →* Y)
    (hk : IsPGroup 2 f.ker)
    (hO : ∀ P : Subgroup ↥f.range, P.Normal → IsPGroup 2 P → P = ⊥) :
    f.ker = CFSG.pCore 2 G := by
  refine le_antisymm (le_pCore_of_normal (MonoidHom.normal_ker _) hk) ?_
  have hmap := hO ((CFSG.pCore 2 G).map f.rangeRestrict)
    ((CFSG.pCore_normal (p := 2) (G := G)).map _ (MonoidHom.rangeRestrict_surjective _))
    ((CFSG.pCore_isPGroup (p := 2) (G := G)).map _)
  rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict] at hmap
  exact hmap

private theorem nonempty_quot_pCore_equiv_range {G Y : Type*} [Group G] [Group Y] (f : G →* Y)
    (hk : IsPGroup 2 f.ker)
    (hO : ∀ P : Subgroup ↥f.range, P.Normal → IsPGroup 2 P → P = ⊥) :
    Nonempty (G ⧸ CFSG.pCore 2 G ≃* ↥f.range) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_eq_pCore_of_range f hk hO).symm).trans
    (QuotientGroup.quotientKerEquivRange f)⟩

private theorem nontrivial_of_isQuasisimple {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    Nontrivial G := by
  have := h.2.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center G)).nontrivial

private theorem eq_bot_of_normal_isPGroup_of_mulEquiv {G Y : Type*} [Group G] [Group Y] (e : G ≃* Y)
    (hY : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥) {P : Subgroup G} (hP : P.Normal)
    (h2 : IsPGroup 2 P) : P = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp
    (hY (P.map e.toMonoidHom) (hP.map e.toMonoidHom e.surjective) (h2.map e.toMonoidHom))

private theorem commutator_eq_top_of_commutator_eq_self {G : Type*} [Group G] {H : Subgroup G}
    (h : ⁅H, H⁆ = H) : commutator ↥H = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    h]

private theorem commutator_range_eq_self {G Y : Type*} [Group G] [Group Y] (hG : commutator G = ⊤)
    (f : G →* Y) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hG]

private theorem injective_of_isPGroup_ker_of_odd {G Y : Type*} [Group G] [Group Y] [Finite G]
    (f : G →* Y) (hk : IsPGroup 2 f.ker) (hG : Odd (Nat.card G)) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk'⟩ := hk.exists_card_eq
  have hdvd : Nat.card f.ker ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  rw [hk'] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hG) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
  rw [hk0, pow_zero] at hk'
  exact Subgroup.eq_bot_of_card_eq _ hk'

private theorem odd_card_of_isZModSq {X : Type} [Group X] [Finite X] {A : Subgroup X} {n : ℕ}
    (hn : 1 ≤ n)
    (hA : IsZModSq A n) : Odd (Nat.card A) := by
  rw [S19.card_eq_of_isZModSq hA]
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact ⟨m - 1, by omega⟩
  exact hodd.mul hodd

section Restr

variable {X Y : Type} [Group X] [Group Y] {I : Subgroup X} (φ : ↥I →* Y)

abbrev restr {H : Subgroup X} (hHI : H ≤ I) : ↥H →* Y := φ.comp (Subgroup.inclusion hHI)

theorem range_restr {H : Subgroup X} (hHI : H ≤ I) :
    (restr φ hHI).range = (H.subgroupOf I).map φ := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem isPGroup_ker_restr (hk : IsPGroup 2 φ.ker) {H : Subgroup X} (hHI : H ≤ I) :
    IsPGroup 2 (restr φ hHI).ker := by
  rw [← MonoidHom.comap_ker]
  exact hk.comap_of_injective _ (Subgroup.inclusion_injective hHI)

theorem nonempty_bar2_equiv_of_map_eq (hk : IsPGroup 2 φ.ker) {H : Subgroup X} (hHI : H ≤ I)
    {R : Subgroup Y} (hHR : (H.subgroupOf I).map φ = R)
    (hO : ∀ P : Subgroup ↥R, P.Normal → IsPGroup 2 P → P = ⊥) :
    Nonempty (Bar2 H ≃* ↥R) := by
  have e := MulEquiv.subgroupCongr ((range_restr φ hHI).trans hHR)
  obtain ⟨e'⟩ := nonempty_quot_pCore_equiv_range (restr φ hHI) (isPGroup_ker_restr φ hk hHI)
    fun P hP h2 => eq_bot_of_normal_isPGroup_of_mulEquiv e hO hP h2
  exact ⟨e'.trans e⟩

theorem ker_restr_eq_pCore_of_map_eq (hk : IsPGroup 2 φ.ker) {H : Subgroup X} (hHI : H ≤ I)
    {R : Subgroup Y} (hHR : (H.subgroupOf I).map φ = R)
    (hO : ∀ P : Subgroup ↥R, P.Normal → IsPGroup 2 P → P = ⊥) :
    (restr φ hHI).ker = CFSG.pCore 2 ↥H :=
  ker_eq_pCore_of_range _ (isPGroup_ker_restr φ hk hHI) fun _ hP h2 =>
    eq_bot_of_normal_isPGroup_of_mulEquiv
      (MulEquiv.subgroupCongr ((range_restr φ hHI).trans hHR)) hO hP h2

end Restr

theorem conclusion_of_normal_image {X Y : Type} [Group X] [Group Y] {I J : Subgroup X}
    (hJI : J ≤ I) (φ : ↥I →* Y) (hφ : Function.Surjective φ) (hk : IsPGroup 2 φ.ker)
    (hJ : commutator ↥J = ⊤) {n : ℕ} (hn : 2 ≤ n) {R : Subgroup Y}
    (hR : (J.subgroupOf I).map φ = R) [R.Normal] (hL : IsL2 ↥R n) :
    IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
      CFSG.Open.IsQuasisimple (Bar2 K) ∧ J ≤ K ∧ J ⊔ CFSG.Open.pCoreOf 2 K = K := by
  have := isSimpleGroup_of_isL2 hn hL
  have hOR : ∀ P : Subgroup ↥R, P.Normal → IsPGroup 2 P → P = ⊥ :=
    fun P hP h2 => eq_bot_of_normal_isPGroup_of_simple (not_isPGroup_two_of_isL2 hn hL) hP h2
  obtain ⟨eJ⟩ := nonempty_bar2_equiv_of_map_eq φ hk hJI hR hOR
  refine ⟨CFSG.Blueprint.LieModel.of_mulEquiv eJ.symm hL, ?_⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup ↥I,
      N = Subgroup.normalClosure ((J.subgroupOf I : Subgroup ↥I) : Set ↥I) := ⟨_, rfl⟩
  have hNn : N.Normal := by rw [hNdef]; exact Subgroup.normalClosure_normal
  have hJN : J.subgroupOf I ≤ N := by rw [hNdef]; exact Subgroup.le_normalClosure
  have hKI : N.map I.subtype ≤ I := Subgroup.map_subtype_le N
  have hKN : (N.map I.subtype).subgroupOf I = N :=
    Subgroup.comap_map_eq_self_of_injective I.subtype_injective N
  have hJK : J ≤ N.map I.subtype := fun x hx =>
    ⟨⟨x, hJI hx⟩, hJN (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have hJ'J' : ⁅J.subgroupOf I, J.subgroupOf I⁆ = J.subgroupOf I := by
    rw [← Subgroup.inclusion_range hJI]; exact commutator_range_eq_self hJ _
  have hNN : ⁅N, N⁆ = N := by
    refine le_antisymm (Subgroup.commutator_le_self N) ?_
    have h : Subgroup.normalClosure ((J.subgroupOf I : Subgroup ↥I) : Set ↥I) ≤ ⁅N, N⁆ :=
      Subgroup.normalClosure_le_normal fun x hx => by
        have hx' : x ∈ ⁅J.subgroupOf I, J.subgroupOf I⁆ := by rw [hJ'J']; exact hx
        exact Subgroup.commutator_mono hJN hJN hx'
    rwa [← hNdef] at h
  have hImK : ((N.map I.subtype).subgroupOf I).map φ = R := by
    rw [hKN, hNdef, Subgroup.map_normalClosure _ _ hφ, ← Subgroup.coe_map, hR]
    exact Subgroup.normalClosure_eq_self R
  obtain ⟨eK⟩ := nonempty_bar2_equiv_of_map_eq φ hk hKI hImK hOR
  have hkerK := ker_restr_eq_pCore_of_map_eq φ hk hKI hImK hOR
  refine ⟨N.map I.subtype, hKI, by rw [hKN]; exact hNn, by rw [← Subgroup.map_commutator, hNN],
    CFSG.Open.IsQuasisimple.of_mulEquiv eK (isQuasisimple_of_simple (center_eq_bot_of_isL2 hL)),
    hJK, ?_⟩
  refine le_antisymm (sup_le hJK (Subgroup.map_subtype_le _)) ?_
  intro k hk'
  have hmem : restr φ hKI ⟨k, hk'⟩ ∈ (restr φ hJI).range := by
    rw [range_restr, hR, ← hImK, ← range_restr φ hKI]
    exact ⟨_, rfl⟩
  obtain ⟨j, hj⟩ := hmem
  have hjk : (⟨(j : X)⁻¹ * k, (N.map I.subtype).mul_mem ((N.map I.subtype).inv_mem (hJK j.2)) hk'⟩ :
      ↥(N.map I.subtype)) ∈ CFSG.pCore 2 ↥(N.map I.subtype) := by
    rw [← hkerK, MonoidHom.mem_ker]
    have h1 : (⟨(j : X)⁻¹ * k,
        (N.map I.subtype).mul_mem ((N.map I.subtype).inv_mem (hJK j.2)) hk'⟩ :
        ↥(N.map I.subtype)) = (⟨j, hJK j.2⟩ : ↥(N.map I.subtype))⁻¹ * ⟨k, hk'⟩ := rfl
    have h2 : restr φ hKI ⟨j, hJK j.2⟩ = restr φ hJI j := rfl
    rw [h1, map_mul, map_inv, h2, hj, inv_mul_cancel]
  have hkj : k = (j : X) * ((j : X)⁻¹ * k) := by group
  rw [hkj]
  exact Subgroup.mul_mem_sup j.2 (Subgroup.mem_map.mpr ⟨_, hjk, rfl⟩)

theorem torusQS_l2sq_qs {X : Type} [Group X] [Finite X]
    (I A J : Subgroup X) (n : ℕ) (hn : 2 ≤ n) (hsq : IsL2Square (Bar2 I) n)
    (hAI : A ≤ I) (hA : IsZModSq A n) (hJI : J ≤ I)
    (hAJ : A ≤ Subgroup.normalizer (J : Set X)) (hO : S17.oUpperTwo J = J)
    (hq : CFSG.Open.IsQuasisimple (Bar2 J)) :
    IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
      CFSG.Open.IsQuasisimple (Bar2 K) ∧ J ≤ K ∧ J ⊔ CFSG.Open.pCoreOf 2 K = K := by
  obtain ⟨P₁, P₂, _, _, ⟨eI⟩, h₁, h₂⟩ := hsq
  have : Finite (Bar2 I) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I))
  have : Finite (P₁ × P₂) := Finite.of_equiv _ eI.toEquiv
  have : Finite P₁ := Finite.of_injective (fun a : P₁ => ((a, 1) : P₁ × P₂))
    (fun a b h => congrArg Prod.fst h)
  have : Finite P₂ := Finite.of_injective (fun b : P₂ => ((1, b) : P₁ × P₂))
    (fun a b h => congrArg Prod.snd h)
  have := isSimpleGroup_of_isL2 hn h₁
  have := isSimpleGroup_of_isL2 hn h₂
  have hJ : commutator ↥J = ⊤ :=
    commutator_eq_top_of_commutator_eq_self (commutator_eq_self_of_oUpperTwo hO hq.1)
  let φ : ↥I →* P₁ × P₂ := eI.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥I))
  have hφ : Function.Surjective φ := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 φ.ker := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).to_le fun x hx => by
    have h0 : eI (QuotientGroup.mk' (CFSG.pCore 2 ↥I) x) = 1 := hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I) x = 1 := (MulEquiv.map_eq_one_iff eI).mp h0
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hginj : Function.Injective (restr φ hAI) :=
    injective_of_isPGroup_ker_of_odd _ (isPGroup_ker_restr φ hk hAI)
      (odd_card_of_isZModSq (by omega) hA)
  have hT : IsZModSq ↥((A.subgroupOf I).map φ) n := by
    obtain ⟨e⟩ := hA
    exact ⟨(MulEquiv.subgroupCongr (range_restr φ hAI)).symm.trans
      ((MonoidHom.ofInjective hginj).symm.trans e)⟩
  have hTR : (A.subgroupOf I).map φ ≤
      Subgroup.normalizer (((J.subgroupOf I).map φ : Subgroup (P₁ × P₂)) : Set (P₁ × P₂)) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map φ)
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_normalizer_iff]
    intro j
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hAJ ha) (j : X)
  have hRR : ⁅(J.subgroupOf I).map φ, (J.subgroupOf I).map φ⁆ = (J.subgroupOf I).map φ := by
    rw [← range_restr φ hJI]; exact commutator_range_eq_self hJ _
  rcases perfect_of_l2sq hn h₁ h₂ hT hRR hTR with hR | hR | hR | hR
  ·
    exfalso
    have := nontrivial_of_isQuasisimple hq
    have hker : (restr φ hJI).ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : restr φ hJI x ∈ (restr φ hJI).range := ⟨x, rfl⟩
      rw [range_restr, hR, Subgroup.mem_bot] at hx
      exact hx
    have htop : CFSG.pCore 2 ↥J = ⊤ := by
      rw [eq_top_iff, ← hker]
      exact le_pCore_of_normal (MonoidHom.normal_ker _) (isPGroup_ker_restr φ hk hJI)
    obtain ⟨u, v, huv⟩ := exists_pair_ne (Bar2 J)
    induction u using QuotientGroup.induction_on
    induction v using QuotientGroup.induction_on
    apply huv
    rw [QuotientGroup.eq, htop]
    exact Subgroup.mem_top _
  ·
    have : ((⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂)).Normal := by
      rw [← MonoidHom.ker_snd]; exact MonoidHom.normal_ker _
    exact conclusion_of_normal_image hJI φ hφ hk hJ hn hR
      (CFSG.Blueprint.LieModel.of_mulEquiv prodTopBotEquiv.symm h₁)
  ·
    have : ((⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂)).Normal := by
      rw [← MonoidHom.ker_fst]; exact MonoidHom.normal_ker _
    exact conclusion_of_normal_image hJI φ hφ hk hJ hn hR
      (CFSG.Blueprint.LieModel.of_mulEquiv prodBotTopEquiv.symm h₂)
  ·
    exfalso
    have e : ↥((J.subgroupOf I).map φ) ≃* P₁ × P₂ :=
      (MulEquiv.subgroupCongr hR).trans Subgroup.topEquiv
    have hOR : ∀ P : Subgroup ↥((J.subgroupOf I).map φ), P.Normal → IsPGroup 2 P → P = ⊥ :=
      fun P hP h2 => eq_bot_of_normal_isPGroup_of_mulEquiv e
        (fun Q hQ hQ2 => eq_bot_of_normal_isPGroup_prod (not_isPGroup_two_of_isL2 hn h₁)
          (not_isPGroup_two_of_isL2 hn h₂) hQ hQ2) hP h2
    obtain ⟨eJ⟩ := nonempty_bar2_equiv_of_map_eq φ hk hJI rfl hOR
    exact not_isQuasisimple_prod (center_eq_bot_of_isL2 h₁) (center_eq_bot_of_isL2 h₂)
      (CFSG.Open.IsQuasisimple.of_mulEquiv (eJ.trans e).symm hq)

end Bridge

section L2Sq

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open scoped Pointwise commutatorElement

private theorem exists_prime_dvd_two_pow_sub_one_ne_three {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ r ≠ 3 := by
  by_contra h
  push Not at h
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos : 2 ^ n - 1 ≠ 0 := by omega
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun hd hdvd => h _ hd hdvd)
  set k := (2 ^ n - 1).primeFactorsList.length
  have h3k : ∀ m : ℕ, 3 ^ m % 8 = 1 ∨ 3 ^ m % 8 = 3 := by
    intro m
    induction m with
    | zero => left; rfl
    | succ m ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h' | h' <;> rw [h'] <;> norm_num
  have h2n : 2 ^ n % 8 = 0 := by
    have : 2 ^ n = 2 ^ (n - 3) * 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
    rw [this, Nat.mul_mod_left]
  have h7 : (2 ^ n - 1) % 8 = 7 := by omega
  rw [heq] at h7
  rcases h3k k with h' | h' <;> omega

theorem torusQS_l2sq_three {X : Type} [Group X] [Finite X]
    (I A J : Subgroup X) (n : ℕ) (hn : 3 ≤ n) (hsq : IsL2Square (Bar2 I) n)
    (hAI : A ≤ I) (hA : IsZModSq A n) (hJI : J ≤ I)
    (hAJ : A ≤ Subgroup.normalizer (J : Set X))
    (hgroup : IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) (h3 : 3 ∣ Nat.card (Bar2 J)) :
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) := by
  classical
  obtain ⟨P₁, P₂, _, _, ⟨eI⟩, h₁, h₂⟩ := hsq
  have : Finite (Bar2 I) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I))
  have : Finite (P₁ × P₂) := Finite.of_equiv _ eI.toEquiv
  have hAodd : Odd (Nat.card A) := odd_card_of_isZModSq (by omega) hA
  have hAcomm := S19.isMulCommutative_of_isZModSq hA
  have hinj : Function.Injective (barMap hAI) := barMap_injective_of_odd hAI hAodd
  set ψ : ↥A →* P₁ × P₂ := eI.toMonoidHom.comp (barMap hAI) with hψdef
  have hψinj : Function.Injective ψ := eI.injective.comp hinj
  have hT : IsZModSq ↥ψ.range n := by
    obtain ⟨e⟩ := hA
    exact ⟨(MonoidHom.ofInjective hψinj).symm.trans e⟩
  set S₁ : Subgroup (P₁ × P₂) := (⊤ : Subgroup P₁).prod (⊥ : Subgroup P₂) with hS₁def
  set S₂ : Subgroup (P₁ × P₂) := (⊥ : Subgroup P₁).prod (⊤ : Subgroup P₂) with hS₂def
  have hS₁n : S₁.Normal := by rw [hS₁def, ← MonoidHom.ker_snd]; exact MonoidHom.normal_ker _
  have hS₂n : S₂.Normal := by rw [hS₂def, ← MonoidHom.ker_fst]; exact MonoidHom.normal_ker _
  have hL₁ : IsL2 S₁ n := CFSG.Blueprint.LieModel.of_mulEquiv prodTopBotEquiv.symm h₁
  have hL₂ : IsL2 S₂ n := CFSG.Blueprint.LieModel.of_mulEquiv prodBotTopEquiv.symm h₂
  have hS : (IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n) := Or.inl ⟨hL₁, hL₂⟩
  obtain ⟨hc₁, hc₂, -⟩ := S19.torus_eq_sup_inf_of_prod (by omega) hT S₁ S₂ hS₁n hS₂n
    prod_top_bot_inf_bot_top prod_top_bot_sup_bot_top hS
  obtain ⟨r, hpr, hrd, hr3⟩ := exists_prime_dvd_two_pow_sub_one_ne_three hn
  have : Fact (Nat.Prime r) := ⟨hpr⟩
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hodd : Odd (2 ^ n - 1) := by
      obtain ⟨m, hm⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact ⟨m - 1, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)
  obtain ⟨y₁, hy₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ψ.range ⊓ S₁)) r
    (by rw [hc₁]; exact hrd)
  obtain ⟨y₂, hy₂⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ψ.range ⊓ S₂)) r
    (by rw [hc₂]; exact hrd)
  have hy₁' : orderOf (y₁ : P₁ × P₂) = r := by rw [Subgroup.orderOf_coe]; exact hy₁
  have hy₂' : orderOf (y₂ : P₁ × P₂) = r := by rw [Subgroup.orderOf_coe]; exact hy₂
  have hy₁1 : (y₁ : P₁ × P₂) ≠ 1 := by
    intro h
    have h1 : orderOf (y₁ : P₁ × P₂) = 1 := by rw [h, orderOf_one]
    rw [hy₁'] at h1
    exact hpr.one_lt.ne' h1
  have hy₂1 : (y₂ : P₁ × P₂) ≠ 1 := by
    intro h
    have h1 : orderOf (y₂ : P₁ × P₂) = 1 := by rw [h, orderOf_one]
    rw [hy₂'] at h1
    exact hpr.one_lt.ne' h1
  set z : P₁ × P₂ := (y₁ : P₁ × P₂) * (y₂ : P₁ × P₂) with hzdef
  have hzT : z ∈ ψ.range := ψ.range.mul_mem y₁.2.1 y₂.2.1
  have hzS₁ : z ∉ S₁ := by
    intro hz
    have hmem : (y₂ : P₁ × P₂) ∈ S₁ ⊓ S₂ := ⟨by
        have h := S₁.mul_mem (S₁.inv_mem y₁.2.2) hz
        simpa [hzdef] using h, y₂.2.2⟩
    rw [prod_top_bot_inf_bot_top, Subgroup.mem_bot] at hmem
    exact hy₂1 hmem
  have hzS₂ : z ∉ S₂ := by
    intro hz
    have hmem : (y₁ : P₁ × P₂) ∈ S₁ ⊓ S₂ := ⟨y₁.2.2, by
        have h := S₂.mul_mem hz (S₂.inv_mem y₂.2.2)
        simpa [hzdef] using h⟩
    rw [prod_top_bot_inf_bot_top, Subgroup.mem_bot] at hmem
    exact hy₁1 hmem
  have hCz : Subgroup.centralizer ({z} : Set (P₁ × P₂)) = ψ.range := by
    rcases S19.k_19_25_torusCent_prod hT hzT S₁ S₂ hS₁n hS₂n prod_top_bot_inf_bot_top
      prod_top_bot_sup_bot_top hS with h | h | h
    · exact absurd h hzS₁
    · exact absurd h hzS₂
    · exact h
  have hcomm : Commute (y₁ : P₁ × P₂) (y₂ : P₁ × P₂) :=
    congrArg Subtype.val
      ((S19.isMulCommutative_of_isZModSq hT).is_comm.comm ⟨_, y₁.2.1⟩ ⟨_, y₂.2.1⟩)
  have hzord : orderOf z = r := by
    apply orderOf_eq_prime
    · have e1 : (y₁ : P₁ × P₂) ^ r = 1 := by rw [← hy₁']; exact pow_orderOf_eq_one _
      have e2 : (y₂ : P₁ × P₂) ^ r = 1 := by rw [← hy₂']; exact pow_orderOf_eq_one _
      rw [hzdef, hcomm.mul_pow, e1, e2, one_mul]
    · intro h1
      exact hzS₁ (h1 ▸ S₁.one_mem)
  obtain ⟨x, hx⟩ := hzT
  have hxord : orderOf ((x : ↥A) : X) = r := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective ψ hψinj x, hx, hzord]
  have hCzI : Subgroup.centralizer ({barMap hAI x} : Set (Bar2 I)) = (barMap hAI).range := by
    apply Subgroup.map_injective (f := eI.toMonoidHom) eI.injective
    rw [← CFSG.GroupTheory.CoprimeTransport.centralizer_image_mulEquiv, Set.image_singleton]
    have h1 : eI (barMap hAI x) = z := hx
    rw [h1, hCz, hψdef, MonoidHom.range_comp]
  exact subset_pCore_mul_of_regular_three hAI hAcomm hAodd hJI hAJ hgroup h3 hpr hr2 hr3 x
    hxord hCzI

private theorem isQuasisimple_iff_open (G : Type*) [Group G] :
    CFSG.IsQuasisimple G ↔ CFSG.Open.IsQuasisimple G :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
    G).symm.trans
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open G)

theorem torusQS_l2sq {X : Type} [Group X] [Finite X]
    (I A J : Subgroup X) (n : ℕ) (hn : 3 ≤ n) (hsq : IsL2Square (Bar2 I) n)
    (hAI : A ≤ I) (hA : IsZModSq A n) (hJI : J ≤ I) (hAJ : A ≤ normalizer (J : Set X))
    (hO : S17.oUpperTwo J = J)
    (hcase : (IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) ∨ CFSG.IsQuasisimple (Bar2 J))
    (h3 : 3 ∣ Nat.card (Bar2 J)) :
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) ∨
      (IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
        CFSG.IsQuasisimple (Bar2 K) ∧ J ≤ K ∧
        (J ⊔ pCoreOf 2 K = K ∨ IsSp4 (Bar2 K) n ∨ IsU3 (Bar2 K) n)) := by
  rcases hcase with hg | hq
  · exact Or.inl (torusQS_l2sq_three I A J n hn hsq hAI hA hJI hAJ hg h3)
  · obtain ⟨hL, K, hKI, hKn, hKK, hKq, hJK, hJO⟩ :=
      torusQS_l2sq_qs I A J n (by omega) hsq hAI hA hJI hAJ hO
        ((isQuasisimple_iff_open (Bar2 J)).mp hq)
    exact Or.inr ⟨hL, K, hKI, hKn, hKK, (isQuasisimple_iff_open (Bar2 K)).mpr hKq, hJK,
      Or.inl hJO⟩

end L2Sq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
