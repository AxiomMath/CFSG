module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallComm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallE4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallL225
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GroupTheory.ThreeTranspositions.StrongSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup

structure Loc67 (Hh : Type) [Group Hh] [Finite Hh] (V₀ V H₀ : Subgroup Hh) : Prop where
  elemAbelian : IsElemAbelian 2 V
  le : V₀ ≤ V
  card_eq : Nat.card V = 16 * Nat.card V₀
  card₀_le : Nat.card V₀ ≤ 4
  le_normalizer : H₀ ≤ normalizer (V : Set Hh)
  le_normalizer₀ : H₀ ≤ normalizer (V₀ : Set Hh)
  pCore_le : CFSG.pCore 2 Hh ≤ H₀
  strong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 H₀
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup Hh) ≤ 1
  not_le_sup : ¬ V ≤ V₀ ⊔ CFSG.pPrimeCore 3 Hh
  not_sup : ¬ ⊤ ≤ H₀ ⊔ CFSG.pPrimeCore 3 Hh
  charTwo : centralizer (CFSG.pCore 2 Hh : Set Hh) ≤ CFSG.pCore 2 Hh
  kGroup : CFSG.Open.IsKGroup Hh
  exists_c : ∃ c ∈ H₀, orderOf c = 3 ∧ ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀

structure IsSocle67 {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) : Prop where
  normal : J.Normal
  isKGroup : CFSG.Open.IsKGroup ↥J
  simple : IsSimpleGroup ↥J
  nonab : ∃ a b : ↥J, a * b ≠ b * a
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) = 1
  centralizer_eq : centralizer (J : Set Q) = ⊥
  not_dvd_index : ¬ 3 ∣ J.index

section Basic

variable {Hh : Type} [Group Hh] [Finite Hh] {V₀ V H₀ : Subgroup Hh}

theorem isElemAbelian_map {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    (hA : IsElemAbelian 2 A) (f : X →* Y) : IsElemAbelian 2 (A.map f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    show (x : Y) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul, comm_of_isElemAbelian hA ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]

theorem Loc67.card_le (hL : Loc67 Hh V₀ V H₀) : Nat.card V ≤ 64 := by
  have := hL.card_eq
  have := hL.card₀_le
  omega

theorem not_three_dvd_card_pPrimeCore : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 Hh) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card

theorem exists_socle67 (hL : Loc67 Hh V₀ V H₀) (hTI : K67ThreeIndex) :
    ∃ J : Subgroup (Hh ⧸ CFSG.pPrimeCore 3 Hh), IsSocle67 J := by
  have hK := not_three_dvd_card_pPrimeCore (Hh := Hh)
  have hQO := CFSG.pPrimeCore_quotient_eq_bot (G := Hh) Nat.prime_three
  have hQr : CFSG.Open.pRank 3 (⊤ : Subgroup (Hh ⧸ CFSG.pPrimeCore 3 Hh)) ≤ 1 :=
    (pRank_quotient_le (CFSG.pPrimeCore 3 Hh) hK).trans hL.rank
  have hne : H₀ ⊔ CFSG.pPrimeCore 3 Hh ≠ ⊤ := fun h => hL.not_sup (le_of_eq h.symm)
  have hY := CFSG.GroupTheory.ThreeTranspositions.isStronglyPEmbedded_map_mk_of_sup_ne_top
    Nat.prime_three hL.strong hK hne
  obtain ⟨J, hJn, hJs, hJnab, hJr, hJc⟩ :=
    exists_simple_normal_of_stronglyPEmbedded _ hQO hQr hY
  haveI := hJn
  have hJK : CFSG.Open.IsKGroup ↥J :=
    ((hL.kGroup.quotient (CFSG.pPrimeCore 3 Hh)).subgroup J)
  exact ⟨J, ⟨hJn, hJK, hJs, hJnab, hJr, hJc,
    hTI _ J hJn hJK hJs hJnab hJr hJc hQr⟩⟩

theorem card_le_two_or_four_le {A : Subgroup Hh} (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ∨ 4 ≤ Nat.card A := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hA.isPGroup
  rw [hn]
  rcases n with _ | _ | n
  · left
    simp
  · left
    simp
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem pCore_two_le_pPrimeCore_three : CFSG.pCore 2 Hh ≤ CFSG.pPrimeCore 3 Hh := by
  refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := Hh))
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem le_pCore_two_of_normal {W : Subgroup Hh} (hW : W.Normal) (hp : IsPGroup 2 W) :
    W ≤ CFSG.pCore 2 Hh :=
  le_sSup ⟨hW, hp⟩

theorem mem_normalizer_map {X Y : Type} [Group X] [Group Y] (f : X →* Y) {A : Subgroup X} {h : X}
    (hh : h ∈ normalizer (A : Set X)) : f h ∈ normalizer ((A.map f : Subgroup Y) : Set Y) := by
  have hh1 := Subgroup.mem_normalizer_iff.1 hh
  have hh2 := Subgroup.mem_normalizer_iff''.1 hh
  refine Subgroup.mem_normalizer_iff.2 fun n => ?_
  constructor
  · intro hn
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hn
    exact ⟨h * a * h⁻¹, (hh1 a).1 ha, by simp⟩
  · intro hn
    obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.1 hn
    refine ⟨h⁻¹ * a * h, (hh2 a).1 ha, ?_⟩
    rw [map_mul, map_mul, map_inv, hfa]
    group

theorem mem_normalizer_inf {A B : Subgroup Hh} {n : Hh} (hA : n ∈ normalizer (A : Set Hh))
    (hB : n ∈ normalizer (B : Set Hh)) : n ∈ normalizer ((A ⊓ B : Subgroup Hh) : Set Hh) := by
  have hA1 := Subgroup.mem_normalizer_iff.1 hA
  have hB1 := Subgroup.mem_normalizer_iff.1 hB
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at hA1 hB1 ⊢
  exact and_congr (hA1 x) (hB1 x)

theorem mem_normalizer_centralizer_singleton {c h : Hh}
    (hh : h ∈ normalizer ((Subgroup.zpowers c : Subgroup Hh) : Set Hh)) :
    h ∈ normalizer ((centralizer ({c} : Set Hh) : Subgroup Hh) : Set Hh) := by
  have h1 : h * c * h⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.1 hh c).1 (Subgroup.mem_zpowers c)
  have h2 : h⁻¹ * c * h ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff''.1 hh c).1 (Subgroup.mem_zpowers c)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h2
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have hxm : x * c ^ m = c ^ m * x := (show Commute x c from hx).zpow_right m
    have hc' : h * c ^ m * h⁻¹ = c := by rw [hm]; group
    calc h * x * h⁻¹ * c = h * x * h⁻¹ * (h * c ^ m * h⁻¹) := by rw [hc']
      _ = h * (x * c ^ m) * h⁻¹ := by group
      _ = h * (c ^ m * x) * h⁻¹ := by rw [hxm]
      _ = (h * c ^ m * h⁻¹) * (h * x * h⁻¹) := by group
      _ = c * (h * x * h⁻¹) := by rw [hc']
  · intro hy
    have hym : (h * x * h⁻¹) * c ^ k = c ^ k * (h * x * h⁻¹) :=
      (show Commute (h * x * h⁻¹) c from hy).zpow_right k
    have hc' : h⁻¹ * c ^ k * h = c := by rw [hk]; group
    calc x * c = h⁻¹ * ((h * x * h⁻¹) * c ^ k) * h := by rw [hk]; group
      _ = h⁻¹ * (c ^ k * (h * x * h⁻¹)) * h := by rw [hym]
      _ = (h⁻¹ * c ^ k * h) * x := by group
      _ = c * x := by rw [hc']

theorem comm_of_commutator_eq_one {X : Type} [Group X] {a b : X} (h : a * b * a⁻¹ * b⁻¹ = 1) :
    b * a = a * b := by
  have h1 : a * b * a⁻¹ = b := mul_inv_eq_one.1 h
  have h2 : a * b = b * a := (mul_inv_eq_iff_eq_mul.1 h1)
  exact h2.symm

theorem no_small_commutator_13 (hL : Loc67 Hh V₀ V H₀)
    {J : Subgroup (Hh ⧸ CFSG.pPrimeCore 3 Hh)} (hLie : CFSG.Blueprint.LieModel ↥J .PSL 2 5 2)
    {u : Hh} (hu : u ∈ V)
    (hu2 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) u) = 2)
    (huJ : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) u ∈ J) : False := by
  classical
  obtain ⟨g, hg⟩ := psl225_exists_conj_product hLie
    (i := (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) u, huJ⟩ : ↥J))
    (by rw [← Subgroup.orderOf_coe]; exact hu2)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 Hh)
    (g : Hh ⧸ CFSG.pPrimeCore 3 Hh)
  have hab : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) (u * (x * u * x⁻¹))) = 13 := by
    have e : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) (u * (x * u * x⁻¹)) =
        (((⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) u, huJ⟩ : ↥J) *
          (g * (⟨QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) u, huJ⟩ : ↥J) * g⁻¹) : ↥J) :
          Hh ⧸ CFSG.pPrimeCore 3 Hh) := by
      rw [map_mul, map_mul, map_mul, map_inv, hx]
      rfl
    rw [e, Subgroup.orderOf_coe, hg]
  obtain ⟨y, hyx, hy13, hyK⟩ := exists_pow_isPGroup_thirteen (CFSG.pPrimeCore 3 Hh) hab
  haveI hRn : (CFSG.pCore 2 Hh).Normal := CFSG.pCore_normal
  have hRp : IsPGroup 2 (CFSG.pCore 2 Hh) := CFSG.pCore_isPGroup
  have hRK : CFSG.pCore 2 Hh ≤ CFSG.pPrimeCore 3 Hh := pCore_two_le_pPrimeCore_three
  have hRV : ∀ r ∈ CFSG.pCore 2 Hh, ∀ v ∈ V, r * v * r⁻¹ ∈ V := fun r hr v hv =>
    (Subgroup.mem_normalizer_iff.1 (hL.le_normalizer (hL.pCore_le hr)) v).1 hv
  have hcomm : ∀ r ∈ CFSG.pCore 2 Hh, r⁻¹ * (u * r * u⁻¹) ∈ V ⊓ CFSG.pCore 2 Hh := by
    intro r hr
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : r⁻¹ * u * r ∈ V := by
        simpa using hRV r⁻¹ ((CFSG.pCore 2 Hh).inv_mem hr) u hu
      have h2 : r⁻¹ * (u * r * u⁻¹) = (r⁻¹ * u * r) * u⁻¹ := by group
      rw [h2]
      exact V.mul_mem h1 (V.inv_mem hu)
    · exact (CFSG.pCore 2 Hh).mul_mem ((CFSG.pCore 2 Hh).inv_mem hr) (hRn.conj_mem r hr u)
  have hne : V ⊓ CFSG.pCore 2 Hh ≠ V := by
    intro h
    exact hL.not_le_sup (le_sup_of_le_right ((inf_eq_left.1 h).trans hRK))
  have hEa5 : Nat.card (V ⊓ CFSG.pCore 2 Hh : Subgroup Hh) ≤ 2 ^ 5 := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ CFSG.pCore 2 Hh ≤ V)
    have hpos : 0 < Nat.card V := Nat.card_pos
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · rw [mul_zero] at hk
        omega
      · rw [mul_one] at hk
        exact hne (Subgroup.eq_of_le_of_card_ge (inf_le_left : V ⊓ CFSG.pCore 2 Hh ≤ V)
          (by omega))
    have h64 := hL.card_le
    have h2k : Nat.card (V ⊓ CFSG.pCore 2 Hh : Subgroup Hh) * 2 ≤ Nat.card V := by
      rw [hk]
      exact Nat.mul_le_mul_left _ hk2
    omega
  let Eb : Subgroup Hh := (V ⊓ CFSG.pCore 2 Hh).map (MulAut.conj x).toMonoidHom
  have hEb5 : Nat.card Eb ≤ 2 ^ 5 := by
    have : Nat.card Eb = Nat.card (V ⊓ CFSG.pCore 2 Hh : Subgroup Hh) :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    omega
  have hEbR : Eb ≤ CFSG.pCore 2 Hh := by
    rintro _ ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply] using hRn.conj_mem e (Subgroup.mem_inf.1 he).2 x
  have hEbc : ∀ r ∈ CFSG.pCore 2 Hh, r⁻¹ * ((x * u * x⁻¹) * r * (x * u * x⁻¹)⁻¹) ∈ Eb := by
    intro r hr
    have hr' : x⁻¹ * r * x ∈ CFSG.pCore 2 Hh := by
      simpa using hRn.conj_mem r hr x⁻¹
    refine ⟨(x⁻¹ * r * x)⁻¹ * (u * (x⁻¹ * r * x) * u⁻¹), hcomm _ hr', ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hy : y ∈ Subgroup.closure ({u, x * u * x⁻¹} : Set Hh) := by
    have hab_mem : u * (x * u * x⁻¹) ∈ Subgroup.closure ({u, x * u * x⁻¹} : Set Hh) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    exact (Subgroup.zpowers_le.2 hab_mem) hyx
  have hyR : y ∈ CFSG.pCore 2 Hh :=
    mem_of_small_commutator_13 (CFSG.pCore 2 Hh) hRp hL.charTwo
      (fun W hW hp => le_pCore_two_of_normal hW hp) u (x * u * x⁻¹) (V ⊓ CFSG.pCore 2 Hh) Eb
      inf_le_right hEbR hEa5 hEb5 hcomm hEbc y hy hy13
  exact hyK (hRK hyR)

theorem coreA (hL : Loc67 Hh V₀ V H₀) (hBP : K67BPrimeOne) (hTI : K67ThreeIndex) {c : Hh}
    (hcH : c ∈ H₀) (hc3 : orderOf c = 3)
    (hcK : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ CFSG.pPrimeCore 3 Hh) :
    (CFSG.pPrimeCore 3 Hh).relIndex V ≤ 2 := by
  classical
  obtain ⟨J, hJ⟩ := exists_socle67 hL hTI
  haveI := hJ.normal
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hx3 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c) = 3 :=
    orderOf_mk_pPrimeCore hc3
  have hxJ : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c ∈ J :=
    mem_of_pow_eq_one_of_not_dvd_index J hJ.not_dvd_index (by rw [← map_pow, hc3', map_one])
  have hAe : IsElemAbelian 2 (V.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh))) :=
    isElemAbelian_map hL.elemAbelian _
  have hAx : V.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) ≤
      centralizer
        ({QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c} : Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) (c * v * c⁻¹ * v⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hcK v hv)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact comm_of_commutator_eq_one h1
  have hAN : ∀ t ∈ J ⊓ centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c} :
      Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)),
      t ∈ normalizer ((V.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) : Subgroup _) :
        Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) := by
    intro t ht
    have htz : t ∈ normalizer ((Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c) :
        Subgroup (Hh ⧸ CFSG.pPrimeCore 3 Hh)) : Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) := by
      have h0 : centralizer ((Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c) :
          Subgroup (Hh ⧸ CFSG.pPrimeCore 3 Hh)) : Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) =
          centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c} :
            Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact Subgroup.centralizer_le_normalizer _ (by rw [h0]; exact (Subgroup.mem_inf.1 ht).2)
    obtain ⟨h, hhH, -, rfl⟩ := exists_lift_normalizer_zpowers hL.strong hcH hc3 htz
    exact mem_normalizer_map _ (hL.le_normalizer hhH)
  rw [relIndex_eq_card_map]
  rcases card_le_two_or_four_le hAe with h2 | h4
  · exact h2
  · exfalso
    obtain ⟨hLie, hAJ⟩ := hBP _ J hJ.normal hJ.isKGroup hJ.simple hJ.nonab hJ.rank
      hJ.centralizer_eq hJ.not_dvd_index _ hxJ hx3 _ hAe hAx hAN h4
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAJ
    obtain ⟨hA', hJ'⟩ := Subgroup.mem_inf.1 ha
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hA'
    have hne1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) u ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hsq : (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) u) ^ 2 = 1 := hAe.2 _ hA'
    exact no_small_commutator_13 hL hLie hu (orderOf_eq_prime hsq hne1) hJ'

theorem coreB (hL : Loc67 Hh V₀ V H₀) (hIII : K67CaseIII) (hTI : K67ThreeIndex) {c : Hh}
    (hcH : c ∈ H₀) (hc3 : orderOf c = 3) (hcV : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀)
    (hV₀K : ¬ V₀ ≤ CFSG.pPrimeCore 3 Hh) (hV₀c : ¬ ∀ w ∈ V₀, c * w = w * c) : False := by
  classical
  obtain ⟨J, hJ⟩ := exists_socle67 hL hTI
  haveI := hJ.normal
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hx3 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c) = 3 :=
    orderOf_mk_pPrimeCore hc3
  have hxJ : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c ∈ J :=
    mem_of_pow_eq_one_of_not_dvd_index J hJ.not_dvd_index (by rw [← map_pow, hc3', map_one])
  have hV₀e : IsElemAbelian 2 V₀ := isElemAbelian_of_le hL.elemAbelian hL.le
  have hn : c ∈ normalizer (V₀ : Set Hh) := hL.le_normalizer₀ hcH
  obtain ⟨h4, hfix⟩ : Nat.card V₀ = 4 ∧ V₀ ⊓ centralizer ({c} : Set Hh) = ⊥ := by
    rcases centralizes_or_fixedPointFree hV₀e hL.card₀_le hc3 hn with hcen | h
    · exact absurd hcen hV₀c
    · exact h
  have hV₀K' : V₀ ⊓ CFSG.pPrimeCore 3 Hh = ⊥ := by
    refine eq_bot_of_invariant_of_fixedPointFree hV₀e h4 hfix inf_le_left ?_ ?_
    · intro w hw
      exact Subgroup.mem_inf.2
        ⟨(Subgroup.mem_normalizer_iff.1 hn w).1 hw.1,
          (CFSG.pPrimeCore_normal (p := 3) (G := Hh)).conj_mem w hw.2 c⟩
    · intro h
      exact hV₀K (inf_eq_left.1 h)
  have hEcard : Nat.card (V₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh))) = 4 := by
    rw [← relIndex_eq_card_map, ← Subgroup.inf_relIndex_right, inf_comm, hV₀K',
      Subgroup.relIndex_bot_left, h4]
  have hE : IsElemAbelian 2 (V₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh))) :=
    isElemAbelian_map hV₀e _
  have hEJ : V₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) ≤ J := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 he
    obtain ⟨e', he', hw'⟩ := exists_commutator_eq hV₀e hn hfix w hw
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) w =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c *
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) e' *
            (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c)⁻¹ *
              (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) e')⁻¹) := by
      rw [← hw', map_mul, map_mul, map_mul, map_inv, map_inv]
      group
    rw [h1]
    exact J.mul_mem hxJ (hJ.normal.conj_mem _ (J.inv_mem hxJ) _)
  have hEfix : V₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) ⊓
      centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c} :
        Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨he1, he2⟩ := Subgroup.mem_inf.1 he
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 he1
    rw [Subgroup.mem_centralizer_singleton_iff] at he2
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) (c * w * c⁻¹ * w⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← he2]
      group
    have h2 : c * w * c⁻¹ * w⁻¹ ∈ V₀ ⊓ CFSG.pPrimeCore 3 Hh :=
      Subgroup.mem_inf.2
        ⟨V₀.mul_mem ((Subgroup.mem_normalizer_iff.1 hn w).1 hw) (V₀.inv_mem hw),
          (QuotientGroup.eq_one_iff _).1 h1⟩
    rw [hV₀K', Subgroup.mem_bot] at h2
    have h3 : c * w = w * c := comm_of_commutator_eq_one (a := c) (b := w) h2 |>.symm
    have h4' : w ∈ V₀ ⊓ centralizer ({c} : Set Hh) :=
      Subgroup.mem_inf.2 ⟨hw, Subgroup.mem_centralizer_singleton_iff.2 h3.symm⟩
    rw [hfix, Subgroup.mem_bot] at h4'
    rw [h4', map_one]
    exact Subgroup.one_mem _
  have hWe : IsElemAbelian 2 ((V ⊓ centralizer ({c} : Set Hh)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh))) :=
    isElemAbelian_map (isElemAbelian_of_le hL.elemAbelian inf_le_left) _
  have hWne : (V ⊓ centralizer ({c} : Set Hh)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) ≠
      ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hle := le_sup_centralizer_of_commutator_mem hL.elemAbelian hL.le hc3' hcV
    exact hL.not_le_sup (hle.trans (sup_le_sup_right h V₀ |>.trans (sup_comm _ _).le))
  have hWx : (V ⊓ centralizer ({c} : Set Hh)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) ≤
      centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh) c} :
        Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hv).2)
    rw [← map_mul, ← map_mul, this]
  have hWE : (V ⊓ centralizer ({c} : Set Hh)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) ≤
      centralizer ((V₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Hh)) : Subgroup _) :
        Set (Hh ⧸ CFSG.pPrimeCore 3 Hh)) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 he
    rw [← map_mul, ← map_mul, comm_of_isElemAbelian hL.elemAbelian (hL.le hw)
      (Subgroup.mem_inf.1 hv).1]
  refine hIII _ J hJ.normal hJ.isKGroup hJ.simple hJ.nonab hJ.rank hJ.centralizer_eq
    hJ.not_dvd_index _ hxJ hx3 _ hE hEcard hEJ hEfix _ hWe hWne hWx hWE ?_
  intro n hn'
  obtain ⟨h, hhH, hhN, rfl⟩ := exists_lift_normalizer_zpowers hL.strong hcH hc3 hn'
  exact ⟨mem_normalizer_map _ (hL.le_normalizer₀ hhH),
    mem_normalizer_map _ (mem_normalizer_inf (hL.le_normalizer hhH)
      (mem_normalizer_centralizer_singleton hhN))⟩

theorem coreBot (hL : Loc67 Hh V₀ V H₀) (h0 : V₀ = ⊥) (hBP : K67BPrimeOne)
    (hTI : K67ThreeIndex) : (CFSG.pPrimeCore 3 Hh).relIndex V ≤ 2 := by
  obtain ⟨c, hcH, hc3, hcV⟩ := hL.exists_c
  refine coreA hL hBP hTI hcH hc3 fun v hv => ?_
  have h1 := hcV v hv
  rw [h0, Subgroup.mem_bot] at h1
  rw [h1]
  exact Subgroup.one_mem _

theorem coreC (hL : Loc67 Hh V₀ V H₀) (hBP : K67BPrimeOne) (hIII : K67CaseIII)
    (hTI : K67ThreeIndex) : (CFSG.pPrimeCore 3 Hh).relIndex V ≤ 2 := by
  obtain ⟨c, hcH, hc3, hcV⟩ := hL.exists_c
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  by_cases hcen : ∀ w ∈ V₀, c * w = w * c
  · refine coreA hL hBP hTI hcH hc3 fun v hv => ?_
    have := commute_of_commutator_mem hL.elemAbelian hL.le hc3' hcV hcen v hv
    rw [this]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  · by_cases hV₀K : V₀ ≤ CFSG.pPrimeCore 3 Hh
    · exact coreA hL hBP hTI hcH hc3 fun v hv => hV₀K (hcV v hv)
    · exact (coreB hL hIII hTI hcH hc3 hcV hV₀K hcen).elim

end Basic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
