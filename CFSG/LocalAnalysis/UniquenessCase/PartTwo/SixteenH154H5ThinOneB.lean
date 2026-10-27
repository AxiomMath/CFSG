module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Open.StatedZModTwo
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SymmetricGroup
public import CFSG.Quasithin.Background.A3FactsRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SectionRank.ClassicalEven
open Matrix

variable {W : Type} [CommGroup W]

private theorem s16h_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  haveI : Nontrivial (X ⧸ Subgroup.center X) := h.2.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial

private theorem s16h_isSolvable_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    [Group.IsSolvable H] : Group.IsSolvable G :=
  Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16h_H5_false_of_oddRankTwo [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) (h : CFSG.Quasithin.A3Facts.OddRankTwo ↥L) :
    False := by
  obtain ⟨q, hq, hq2, h2⟩ := h
  have h3 : CFSG.Open.pRank q (⊤ : Subgroup ↥L) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hc.thin q hq hq2
  omega

private theorem s16h_H5_two_le_pRank_three_of_rotGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {H : Subgroup (GL ι K)} {e : Fin 2 ⊕ Fin 2 → ι}
    (he : Function.Injective e) (hH : ∀ k, rotGL (e (.inl k)) (e (.inr k)) ∈ H) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ∀ a b : Fin 2 ⊕ Fin 2, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  refine CFSG.Quasithin.A3Facts.two_le_pRank_of_gens (x := ⟨_, hH 0⟩) (y := ⟨_, hH 1⟩) ?_ ?_
    ?_ ?_ ?_
  · exact Subtype.ext (rotGL_pow_three _ _)
  · exact Subtype.ext (rotGL_pow_three _ _)
  · apply Subtype.ext
    exact (rotGL_commute (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide))).eq
  · intro h
    have h1 : rotGL (e (.inl 0)) (e (.inr 0)) = 1 := congrArg Subtype.val h
    exact (mul_scalar_ne (g := 1) (c := 1) (h := rotGL (e (.inl 0)) (e (.inr 0)))
      (a := e (.inl 0)) (b := e (.inr 0)) (hne _ _ (by decide)) (Matrix.one_mulVec _)
      (rotMatrix_mulVec_left _ _) (Subgroup.one_mem _)) (by rw [h1, mul_one])
  · intro m h
    have h1 : (rotGL (e (.inl 0)) (e (.inr 0))) ^ m = rotGL (e (.inl 1)) (e (.inr 1)) :=
      congrArg Subtype.val h
    exact (mul_scalar_ne (g := (rotGL (e (.inl 0)) (e (.inr 0))) ^ m) (c := 1)
      (h := rotGL (e (.inl 1)) (e (.inr 1))) (a := e (.inl 1)) (b := e (.inr 1))
      (hne _ _ (by decide))
      (rotGL_pow_mulVec_of_ne (hne _ _ (by decide)) (hne _ _ (by decide)) m)
      (rotMatrix_mulVec_left _ _) (Subgroup.one_mem _)) (by rw [h1, mul_one])

private theorem s16h_oddRankTwo_statedSp {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K] :
    CFSG.Quasithin.A3Facts.OddRankTwo ↥(StatedSp m K) := by
  refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
  refine s16h_H5_two_le_pRank_three_of_rotGL
    (e := Sum.map (Fin.castLE hm) (Fin.castLE hm))
    ((Fin.castLE_injective hm).sumMap (Fin.castLE_injective hm)) fun k => ?_
  show rotGL (Sum.inl (Fin.castLE hm k)) (Sum.inr (Fin.castLE hm k)) ∈ StatedSp m K
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  exact rotMatrix_inl_inr_symplectic (K := K) (Fin.castLE hm k)

private theorem s16h_subsingleton_statedSp_zero (K : Type) [Field K] :
    Subsingleton ↥(StatedSp 0 K) := by
  haveI : IsEmpty (Fin 0 ⊕ Fin 0) := inferInstance
  haveI : Subsingleton (GL (Fin 0 ⊕ Fin 0) K) := inferInstance
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim (a : GL (Fin 0 ⊕ Fin 0) K) b)⟩

private theorem s16h_subsingleton_statedSL_le_one {n : ℕ} (hn : n ≤ 1) (K : Type) [Field K] :
    Subsingleton ↥(StatedSL n K) := by
  haveI : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
  rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
  exact Subtype.ext (by rw [← hx, ← hy, Subsingleton.elim x y])

private theorem s16h_isSolvable_GL_two_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Group.IsSolvable (GL (Fin 2) K) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨e⟩ := TauCeti.nonempty_mulEquiv_permFinThree hcard
  haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16h_isSolvable_statedSp_one_of_card_two {K : Type} [Field K]
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(StatedSp 1 K) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Group.IsSolvable (GL (Fin 2) K) := s16h_isSolvable_GL_two_of_card_two hK
  have htop : (SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range = ⊤ := by
    rw [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL,
      CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK]
  have hsurj : Function.Surjective
      (SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K) :=
    MonoidHom.range_eq_top.mp htop
  let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* GL (Fin 2) K :=
    MulEquiv.ofBijective _ ⟨SpecialLinearGroup.toGL_injective, hsurj⟩
  haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_surjective (f := e1.symm.toMonoidHom) e1.symm.surjective
  exact Group.isSolvable_of_surjective
    (f := (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).toMonoidHom)
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).surjective

theorem s16h_H5_oddRankTwo_statedSL_three {a : ℕ} (ha : 2 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ a) : CFSG.Quasithin.A3Facts.OddRankTwo ↥(StatedSL 3 K) := by
  have hlt : 2 ^ a - 1 ≠ 1 := by
    have : 4 ≤ 2 ^ a := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hlt
  have hq2 : q ≠ 2 := by
    have hodd : Odd (2 ^ a - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow a 2 (by norm_num))
        (even_two.pow_of_ne_zero (by omega)) odd_one
    intro h2
    rw [h2] at hqdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hqdvd)
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) q
    (by rw [Nat.card_units, hK]; exact hqdvd)
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    exact hq.one_lt.ne hω
  let x : ↥(StatedSL 3 K) :=
    ⟨torusDiag (torusVec ω 0 2), torusDiag_mem_SL (prod_torusVec ω 0 2)⟩
  let y : ↥(StatedSL 3 K) :=
    ⟨torusDiag (torusVec ω 1 2), torusDiag_mem_SL (prod_torusVec ω 1 2)⟩
  refine ⟨q, hq, hq2, ?_⟩
  refine CFSG.Quasithin.A3Facts.two_le_pRank_of_gens (x := x) (y := y) ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, torusVec_pow, ← hω,
      pow_orderOf_eq_one, torusVec_one, map_one]
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, torusVec_pow, ← hω,
      pow_orderOf_eq_one, torusVec_one, map_one]
  · apply Subtype.ext
    exact ((Commute.all (torusVec ω 0 2) (torusVec ω 1 2)).map torusDiag).eq
  · intro h
    have h1 : torusDiag (torusVec ω (0 : Fin 3) (2 : Fin 3)) = 1 := by
      have h2 := congrArg Subtype.val h
      change torusDiag (torusVec ω (0 : Fin 3) (2 : Fin 3)) = 1 at h2
      exact h2
    have h2 : torusVec ω (0 : Fin 3) (2 : Fin 3) = 1 :=
      torusDiag_injective (by rw [h1, map_one])
    have h3 := congrFun h2 0
    rw [torusVec_apply_left ω (by decide : (0 : Fin 3) ≠ 2)] at h3
    exact hω1 (by simpa using h3)
  · intro n h
    have h1 : torusDiag (torusVec (ω ^ n) (0 : Fin 3) (2 : Fin 3)) =
        torusDiag (torusVec ω (1 : Fin 3) (2 : Fin 3)) := by
      have h2 := congrArg Subtype.val h
      change (torusDiag (torusVec ω (0 : Fin 3) (2 : Fin 3))) ^ n =
        torusDiag (torusVec ω (1 : Fin 3) (2 : Fin 3)) at h2
      rwa [← map_pow, torusVec_pow] at h2
    have h2 : torusVec (ω ^ n) (0 : Fin 3) (2 : Fin 3) =
        torusVec ω (1 : Fin 3) (2 : Fin 3) := torusDiag_injective h1
    have hL : torusVec (ω ^ n) (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) = 1 :=
      torusVec_apply_of_ne (ω ^ n) (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)
    have hR : torusVec ω (1 : Fin 3) (2 : Fin 3) (1 : Fin 3) = ω :=
      torusVec_apply_left ω (by decide : (1 : Fin 3) ≠ 2)
    have h3 := congrFun h2 1
    rw [hL, hR] at h3
    exact hω1 h3.symm

theorem s16h_H5_not_quasisimple_of_isSLn_small [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) {n a : ℕ} (hn : n ≤ 1) (h : IsSLn ↥L n a) : False := by
  obtain ⟨K, hF, hFin, -, ⟨e⟩⟩ := h
  letI := hF
  letI := hFin
  haveI hN : Nontrivial ↥L := s16h_nontrivial_of_isQuasisimple hc.comp.2.2
  haveI : Subsingleton ↥(StatedSL n K) := s16h_subsingleton_statedSL_le_one hn K
  haveI : Subsingleton ↥L :=
    ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
  obtain ⟨a, b, hab⟩ := hN
  exact hab (Subsingleton.elim a b)

theorem s16h_H5_not_quasisimple_of_isSLn_two_one [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) (h : IsSLn ↥L 2 1) : False := by
  obtain ⟨K, hF, hFin, hKcard, ⟨e⟩⟩ := h
  letI := hF
  letI := hFin
  have hK : Nat.card K = 2 := by rw [hKcard]; norm_num
  haveI hN : Nontrivial ↥L := s16h_nontrivial_of_isQuasisimple hc.comp.2.2
  haveI : Group.IsPerfect ↥L := ⟨hc.comp.2.2.1⟩
  haveI : Group.IsSolvable (GL (Fin 2) K) := s16h_isSolvable_GL_two_of_card_two hK
  have htop : StatedSL 2 K = ⊤ := CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK 2
  let e2 : ↥(StatedSL 2 K) ≃* GL (Fin 2) K :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  haveI : Group.IsSolvable ↥(StatedSL 2 K) :=
    Group.isSolvable_of_surjective (f := e2.symm.toMonoidHom) e2.symm.surjective
  haveI : Group.IsSolvable ↥L := s16h_isSolvable_of_mulEquiv e
  exact (Group.IsPerfect.not_isSolvable ↥L) inferInstance

theorem s16h_H5_isSpn_class [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {n a : ℕ} (ha : a ≤ 3) (h : IsSpn ↥L n a) :
    (n = 2 ∧ a = 2) ∨ (n = 2 ∧ a = 3) := by
  obtain ⟨hEven, K, hF, hFin, hKcard, ⟨e⟩⟩ := h
  letI := hF
  letI := hFin
  rcases Nat.lt_or_ge n 4 with hn | hn
  · have hn' : n = 0 ∨ n = 2 := by
      obtain ⟨k, hk⟩ := hEven
      omega
    rcases hn' with rfl | rfl
    · haveI hN : Nontrivial ↥L := s16h_nontrivial_of_isQuasisimple hc.comp.2.2
      haveI : Subsingleton ↥(StatedSp (0 / 2) K) := s16h_subsingleton_statedSp_zero K
      haveI : Subsingleton ↥L :=
        ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
      obtain ⟨a, b, hab⟩ := hN
      exact (hab (Subsingleton.elim a b)).elim
    · have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases ha' with rfl | rfl | rfl | rfl
      · exfalso
        have h1 : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
        rw [hKcard] at h1
        norm_num at h1
      · exfalso
        haveI hN : Nontrivial ↥L := s16h_nontrivial_of_isQuasisimple hc.comp.2.2
        haveI : Group.IsPerfect ↥L := ⟨hc.comp.2.2.1⟩
        haveI : Group.IsSolvable ↥(StatedSp (2 / 2) K) :=
          s16h_isSolvable_statedSp_one_of_card_two (by rw [hKcard]; norm_num)
        haveI : Group.IsSolvable ↥L := s16h_isSolvable_of_mulEquiv e
        exact (Group.IsPerfect.not_isSolvable ↥L) inferInstance
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  · exact (s16h_H5_false_of_oddRankTwo hc
      (CFSG.Quasithin.A3Facts.OddRankTwo.of_mulEquiv e
        (s16h_oddRankTwo_statedSp (by omega : 2 ≤ n / 2)))).elim

theorem s16h_H5_not_quasisimple_of_isAlt_le_four [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) {n : ℕ} (h : UC22.IsAlt ↥L n) (hn : n ≤ 4) :
    False := by
  obtain ⟨e⟩ := h
  haveI hN : Nontrivial ↥L := s16h_nontrivial_of_isQuasisimple hc.comp.2.2
  haveI : Group.IsPerfect ↥L := ⟨hc.comp.2.2.1⟩
  haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by rwa [Nat.card_fin])
  haveI : Group.IsSolvable ↥L := s16h_isSolvable_of_mulEquiv e
  exact (Group.IsPerfect.not_isSolvable ↥L) inferInstance

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
