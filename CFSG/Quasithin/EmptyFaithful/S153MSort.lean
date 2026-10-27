module

public import CFSG.Quasithin.EmptyFaithful.S153MDef
public import CFSG.Quasithin.EmptyFaithful.S153LKsDef
import CFSG.Quasithin.EmptyFaithful.S153LKsA
import CFSG.Quasithin.EmptyFaithful.LRed3FourA
import CFSG.Quasithin.EmptyFaithful.A38c4G2Center
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two
import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
import CFSG.Quasithin.Background.FFC4Real
import CFSG.Quasithin.Vol2.KGNatG2Order

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

section Orders

private theorem srt_ord_of_cq {L S : Type} [Group L] [Finite L]
    [Group S] (hK : S153L.KsCover L) (e : L ⧸ Subgroup.center L ≃* S) :
    S153L.KsOrd (Nat.card S) := by
  obtain ⟨N, hN, hcard⟩ := hK.card_data_eq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)
  have hpos : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
  rw [Nat.card_congr e.toEquiv] at h1
  have h2 : N * Nat.card (Subgroup.center L) = Nat.card S * Nat.card (Subgroup.center L) := by
    rw [← hcard, h1]
  rwa [Nat.eq_of_mul_eq_mul_right hpos h2] at hN

private theorem srt_not_ord {N : ℕ}
    (hN : N = 60 ∨ N = 360 ∨ N = 2520 ∨ N = 6048 ∨ N = 20160 ∨ N = 9999360) :
    ¬ S153L.KsOrd N := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := S153L.ksOrd_ne_fixed h
  have := S153L.ksOrd_ge h
  omega

private theorem srt_ord_of_simple_surj {L Γ : Type} [Group L]
    [Finite L] [Group Γ] (hq : CFSG.IsQuasisimple L) (hK : S153L.KsCover L) (hΓ : IsSimpleGroup Γ)
    (π : Γ →* L) (hπ : Function.Surjective π) : S153L.KsOrd (Nat.card Γ) := by
  obtain ⟨e⟩ := lred3_cq_simple hq hΓ π hπ
  exact srt_ord_of_cq hK e

private theorem srt_ord_of_isHat {L Γ₀ S : Type} [Group L]
    [Finite L] [Group Γ₀] [Group S] (hq : CFSG.IsQuasisimple L) (hK : S153L.KsCover L)
    (hhat : IsHat Γ₀ S) (π : Γ₀ →* L) (hπ : Function.Surjective π) : S153L.KsOrd (Nat.card S) := by
  obtain ⟨e⟩ := lred3_cq_of_quasisimple hhat.1 hq π hπ
  obtain ⟨f⟩ := hhat.2.2
  exact srt_ord_of_cq hK (e.symm.trans f)

end Orders

section Bad

variable {L : Type} [Group L] [Finite L]

private theorem srt_false_alt (hq : CFSG.IsQuasisimple L)
    (hK : S153L.KsCover L) {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≤ 8)
    (π : ↥(alternatingGroup (Fin m)) →* L) (hπ : Function.Surjective π) : False := by
  have h := srt_ord_of_simple_surj hq hK
    (CFSG.Quasithin.Vol2.Ch10.SecA.isSimpleGroup_alt hm5) π hπ
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_alt m (by omega)] at h
  have hm : m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
  rcases hm with rfl | rfl | rfl | rfl
  · exact srt_not_ord (by decide) h
  · exact srt_not_ord (by decide) h
  · exact srt_not_ord (by decide) h
  · exact srt_not_ord (by decide) h

private theorem srt_false_sl_zmod (hq : CFSG.IsQuasisimple L)
    (hK : S153L.KsCover L) {n : ℕ} (hn : n = 4 ∨ n = 5) (π : ↥(StatedSL n (ZMod 2)) →* L)
    (hπ : Function.Surjective π) : False := by
  have hs : IsSimpleGroup ↥(StatedSL n (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch10.SecA.isSimpleGroup_statedSL_two (by omega)
  have h := srt_ord_of_simple_surj hq hK hs π hπ
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rcases hn with rfl | rfl
  · rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
      CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_four_of_two h2] at h
    exact srt_not_ord (by norm_num) h
  · rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
      CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_five_of_two h2] at h
    exact srt_not_ord (by norm_num) h

private theorem srt_false_g2 (hK : S153L.KsCover L) {K : Type}
    [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n)
    (e : ↥(CFSG.Open.quasithinG2 K) ≃* L) : False := by
  have hcp : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hcard
  have h4 : 2 < Nat.card K := by
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := K) h4
  have hZ : Subgroup.center ↥(CFSG.Open.quasithinG2 K) = ⊥ := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
    exact CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1
  have hZ1 : Nat.card (Subgroup.center L) = 1 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hZ, Subgroup.card_bot]
  obtain ⟨N, hN, hcardL⟩ := hK.card_data_eq
  rw [hZ1, mul_one] at hcardL
  have h : S153L.KsOrd (Nat.card L) := by rw [hcardL]; exact hN
  rw [← Nat.card_congr e.toEquiv] at h
  have hc : Nat.card ↥(CFSG.Open.quasithinG2 K) =
      2 ^ (6 * n) * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, hcard, ← pow_mul, ← pow_mul, mul_comm n 6,
      mul_comm n 2]
  rw [hc] at h
  exact S153L.ksOrd_ne_g2 hn h

private theorem srt_false_g2derived
    (hq : CFSG.IsQuasisimple L) (hK : S153L.KsCover L) {K : Type}
    [Field K] [Finite K] (hK2 : Nat.card K = 2)
    (π : ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ →* L)
    (hπ : Function.Surjective π) : False := by
  have hs := CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK2
  have h := srt_ord_of_simple_surj hq hK hs π hπ
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.C10P01.card_g2Two_commutator hK2] at h
  exact srt_not_ord (by norm_num) h

private theorem srt_equiv_g2derived
    {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (N : Subgroup ↥(CFSG.Open.quasithinG2 K)) [N.Normal]
    (e : Y ≃* ↥N) :
    Nonempty (Y ≃* ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆) := by
  have hs : IsSimpleGroup ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK
  have hD : (commutator ↥(CFSG.Open.quasithinG2 K)).map (CFSG.Open.quasithinG2 K).subtype =
      ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eD : ↥(commutator ↥(CFSG.Open.quasithinG2 K)) ≃*
      ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    ((commutator ↥(CFSG.Open.quasithinG2 K)).equivMapOfInjective
      (CFSG.Open.quasithinG2 K).subtype (CFSG.Open.quasithinG2 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hD)
  have hDs : IsSimpleGroup ↥(commutator ↥(CFSG.Open.quasithinG2 K)) := eD.isSimpleGroup
  have hYp : Group.IsPerfect Y := hY.1
  have : Group.IsPerfect ↥N := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hY1 : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY
  have hN0 : N ≠ ⊥ := by
    rintro rfl
    obtain ⟨y, hy⟩ := exists_ne (1 : Y)
    apply hy
    have h1 : ((e y : ↥(⊥ : Subgroup ↥(CFSG.Open.quasithinG2 K))) :
        ↥(CFSG.Open.quasithinG2 K)) = 1 := Subgroup.mem_bot.1 (e y).2
    exact e.injective (Subtype.ext (by rw [h1]; simp))
  have heq : N = commutator ↥(CFSG.Open.quasithinG2 K) :=
    CFSG.Quasithin.Vol2.Ch10.SecA.C10P01.eq_commutator_of_isPerfect N hN0 hDs
  exact ⟨(e.trans (MulEquiv.subgroupCongr heq)).trans eD⟩

end Bad

section Pair

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}

private theorem srt_false_g2natural
    (hq : CFSG.IsQuasisimple ↥L) (hK : S153L.KsCover ↥L) {m : ℕ}
    (h : G2Natural L U Z m) : False := by
  obtain ⟨K, _, _, hcard, π, hπ⟩ := h
  have : CharP K 2 := SzN15.charP_two_of_card hcard
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
  let e : ↥(CFSG.Open.quasithinG2 K) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hcard, pow_zero] at h1
      omega
    · exact h
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · have h1 : m = 1 := by omega
    subst h1
    have hK2 : Nat.card K = 2 := by simpa using hcard
    let eN : ↥L ≃* ↥(⊤ : Subgroup ↥(CFSG.Open.quasithinG2 K)) :=
      e.symm.trans Subgroup.topEquiv.symm
    obtain ⟨e'⟩ := srt_equiv_g2derived hq hK2 ⊤ eN
    exact srt_false_g2derived hq hK hK2 e'.symm.toMonoidHom e'.symm.surjective
  · exact srt_false_g2 hK hge hcard e

private theorem srt_shape_of_pair
    (hq : CFSG.IsQuasisimple ↥L) (hK : S153L.KsCover ↥L)
    (hB : B42ModulePair L U Z) :
    (∃ n, BinaryNaturalSL L U Z 2 n) ∨ (∃ n, BinaryNaturalSL L U Z 3 n) ∨
      (∃ n, BinaryNaturalSp4 L U Z n) := by
  rcases hB with h | h | h | ⟨_, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (srt_false_g2natural hq hK h).elim
  · obtain ⟨_, _, _, hc, π, hπ⟩ := h
    exact (srt_false_g2derived hq hK (by simpa using hc) π hπ.1).elim
  · obtain ⟨π, hπ⟩ := h
    exact (srt_false_alt hq hK (m := 5) (by norm_num) (by norm_num) π hπ.1).elim
  · obtain ⟨π, hπ⟩ := h
    exact (srt_false_alt hq hK (m := 6) (by norm_num) (by norm_num) π hπ.1).elim
  · obtain ⟨π, hπ⟩ := h
    exact (srt_false_alt hq hK (m := 7) (by norm_num) (by norm_num) π hπ.1).elim
  · obtain ⟨_, π, hπ⟩ := h
    exact (srt_false_alt hq hK (m := 7) (by norm_num) (by norm_num) π hπ.1).elim
  · obtain ⟨_, _, _, Γ₀, _, _, hhat, _, π, hπ⟩ := h
    have h6 := srt_ord_of_isHat hq hK hhat π hπ.1
    rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 6 (by norm_num)] at h6
    exact (srt_not_ord (by decide) h6).elim
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact (srt_false_sl_zmod hq hK (Or.inl rfl) π hπ.1).elim
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact (srt_false_sl_zmod hq hK (Or.inr rfl) π hπ.1).elim
  · obtain ⟨π, hπ⟩ := h
    exact (srt_false_sl_zmod hq hK (Or.inl rfl) π hπ.1).elim
  · obtain ⟨π, hπ⟩ := h
    exact (srt_false_sl_zmod hq hK (Or.inr rfl) π hπ.1).elim

end Pair

section Main

variable {V : Type} [CommGroup V] [Finite V] {J L : Subgroup (MulAut V)}

private theorem srt_false_overgroup
    (hLJ : L ≤ J) (hn : ∀ x ∈ J, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hq : CFSG.IsQuasisimple ↥L) (hK : S153L.KsCover ↥L) {U Z : Subgroup V}
    (h : (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural J U Z n) ∨ G2Natural J U Z 1) : False := by
  have hnorm : (L.subgroupOf J).Normal :=
    ⟨fun l hl g => by
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      exact hn g g.2 l hl⟩
  have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLJ).symm hq
  rcases h with ⟨n, hn5, hn8, π, hπ⟩ | ⟨K, _, _, hc, π, hπ⟩
  · obtain ⟨f⟩ := Bridge.TypeList.perm_perfect_normal_equiv hn5 π hπ.1 _ hnorm
      hq'.1.commutator_eq_top (Bridge.TypeList.exists_noncomm_of_quasisimple hq')
    let e : ↥(alternatingGroup (Fin n)) ≃* ↥L := f.trans (Subgroup.subgroupOfEquivOfLe hLJ)
    exact srt_false_alt hq hK hn5 hn8 e.toMonoidHom e.surjective
  · have hcp : CharP K 2 := SzN15.charP_two_of_card hc
    have hK2 : Nat.card K = 2 := by simpa using hc
    have hinj : Function.Injective π :=
      FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ
    let e : ↥(CFSG.Open.quasithinG2 K) ≃* ↥J := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    have hN : ((L.subgroupOf J).map e.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map hnorm e.symm.toMonoidHom e.symm.surjective
    let eN : ↥L ≃* ↥((L.subgroupOf J).map e.symm.toMonoidHom) :=
      (Subgroup.subgroupOfEquivOfLe hLJ).symm.trans (e.symm.subgroupMap (L.subgroupOf J))
    obtain ⟨e'⟩ := srt_equiv_g2derived hq hK2 _ eN
    exact srt_false_g2derived hq hK hK2 e'.symm.toMonoidHom e'.symm.surjective

theorem ffNatShape_of_part1
    (_hLJ : L ≤ J) (_hn : ∀ x ∈ J, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (_h2 : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L)
    (h1 : B51Part1 J L) (hq : CFSG.IsQuasisimple ↥L) (hK : S153L.KsCover ↥L) :
    FFNatShape L := by
  obtain ⟨-, hc⟩ := h1
  rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨-, hpair, -⟩ := hi
    rcases srt_shape_of_pair hq hK hpair with ⟨m, K, hF, hFin, hK2, hreal⟩ |
        ⟨m, K, hF, hFin, hK3, hreal⟩ | ⟨m, K, hF, hFin, hK4, hreal⟩
    · exact Or.inl ⟨K, hF, hFin, m, hK2, hreal⟩
    · exact Or.inr (Or.inl ⟨K, hF, hFin, m, hK3, hreal⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨K, hF, hFin, m, hK4, hreal⟩))
  · obtain ⟨-, n, K, hF, hFin, hK3, I, π, hind, hI, hreal, -⟩ := hii
    exact Or.inr (Or.inr (Or.inr ⟨K, hF, hFin, n, I, π, hK3, hind, hI, hreal⟩))
  · obtain ⟨-, hn, π, U₁, U₂, -, hr1, -⟩ := hiii
    exact (srt_false_sl_zmod hq hK hn π hr1.1).elim
  · obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
    exact (srt_false_sl_zmod hq hK hn π (hreal ⟨0, hk1⟩).1).elim

theorem eq_of_part1
    (hLJ : L ≤ J) (hn : ∀ x ∈ J, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (_h2 : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L)
    (h1 : B51Part1 J L) (hq : CFSG.IsQuasisimple ↥L) (hK : S153L.KsCover ↥L) : J = L := by
  obtain ⟨-, hc⟩ := h1
  rcases hc with hi | hii | ⟨_, hiii⟩ | hiv
  · obtain ⟨-, -, hT⟩ := hi
    obtain ⟨T, hT', -⟩ := EscapingLocal.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup (MulAut V)) ≤ J)
      (by simp [IsPGroup])
    rcases hT T hT' with h | ⟨-, hs⟩
    · exact h
    · exact (srt_false_overgroup hLJ hn hq hK hs).elim
  · exact hii.1
  · exact hiii.1
  · exact hiv.1

end Main

end S153M

end CFSG.Quasithin
