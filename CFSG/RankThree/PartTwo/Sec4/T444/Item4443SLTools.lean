module

public import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.KFacts.KS14SL34

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine (qSub qElt)

section Exponent

theorem factorization_card_SL :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))).factorization 3 = 3 := by
  rw [KFacts.KS14.card_SL_three_four]
  exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (show 60480 = 3 ^ 3 * 2240 by norm_num) (by norm_num)

theorem pow_three_eq_one_of_SL {x : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)}
    (hx : IsPGroup 3 (Subgroup.zpowers x)) : x ^ 3 = 1 := by
  have hk := KFacts.L34.card_galoisField_two_two
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.KS14.card_SL_three_four]; norm_num)
  have hQ : Nat.card (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) =
      3 ^ (Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))).factorization 3 := by
    rw [factorization_card_SL, LinearThreeFourFixedNine.card_qSub hk]
    norm_num
  obtain ⟨S, hS⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_sylow_eq_map hQ S
  have hxS : x ∈ (S : Subgroup _) := hS (Subgroup.mem_zpowers x)
  rw [hg] at hxS
  obtain ⟨y, hy, rfl⟩ := hxS
  have hy' : y ∈ ((qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) :
      Set (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) := hy
  rw [LinearThreeFourFixedNine.coe_qSub] at hy'
  obtain ⟨t, rfl⟩ := hy'
  rw [← map_pow, LinearThreeFourFixedNine.qElt_pow_three hk, map_one]

theorem pow_three_eq_one_of_projSL {x : projSL 3 (GaloisField 2 2)}
    (hx : IsPGroup 3 (Subgroup.zpowers x)) : x ^ 3 = 1 := by
  have hk := KFacts.L34.card_galoisField_two_two
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)
  have : Finite (projectiveSL 3 (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.L34.card_projectiveSL hk]; norm_num)
  have hx' : IsPGroup 3 (Subgroup.zpowers (e x)) := by
    have h := MonoidHom.map_zpowers e.toMonoidHom x
    rw [MulEquiv.coe_toMonoidHom] at h
    rw [← h]
    exact hx.map _
  obtain ⟨S, hS⟩ := hx'.exists_le_sylow
  have hS9 : Nat.card (S : Subgroup (projectiveSL 3 (GaloisField 2 2))) = 9 := by
    rw [Sylow.card_eq_multiplicity, KFacts.L34.factorization_card hk]
    norm_num
  have := KFacts.L34.isElementaryAbelian_of_card_eq_nine hk hS9
  have h1 : e x ^ 3 = 1 := by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := (S : Subgroup _)) (e x)
      (hS (Subgroup.mem_zpowers _))
    simpa using this
  apply e.injective
  rw [map_pow, h1, map_one]

theorem pow_three_eq_one_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (hK : ∀ y : K, IsPGroup 3 (Subgroup.zpowers y) → y ^ 3 = 1) {x : H}
    (hx : IsPGroup 3 (Subgroup.zpowers x)) : x ^ 3 = 1 := by
  have hy : IsPGroup 3 (Subgroup.zpowers (e x)) := by
    have h := MonoidHom.map_zpowers e.toMonoidHom x
    rw [MulEquiv.coe_toMonoidHom] at h
    rw [← h]
    exact hx.map _
  apply e.injective
  rw [map_pow, hK _ hy, map_one]

theorem isQuasisimple_SL :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL
  refine ⟨hperf, specialLinearQuotientCenterEquiv.isSimpleGroup, ?_⟩
  by_contra hab
  push Not at hab
  have hperf' : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hab)
  have hcard := Nat.card_congr specialLinearQuotientCenterEquiv.toEquiv
  rw [Nat.card_unique, KFacts.L34.card_projSL] at hcard
  norm_num at hcard

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {x : G} {n : ℕ}
    (hx : x ^ (3 ^ n) = 1) : IsPGroup 3 (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

end Exponent

section Quasisimple

variable {X : Type*} [Group X]

theorem mem_centralizer_of_commutator_mem {L : Subgroup X} (hL : CFSG.IsQuasisimple L) {m : X}
    (hm : m ∈ L) (h : ∀ y ∈ L, m * y * m⁻¹ * y⁻¹ ∈ Subgroup.centralizer (L : Set X)) :
    m ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨-, hsimple, hnab⟩ := hL
  set Z := Subgroup.center L with hZ
  have hcen : (QuotientGroup.mk' Z ⟨m, hm⟩ : L ⧸ Z) ∈ Subgroup.center (L ⧸ Z) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hmy : (⟨m, hm⟩ : L) * y * (⟨m, hm⟩ : L)⁻¹ * y⁻¹ ∈ Z := by
      rw [hZ, Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_iff.mp (h y y.2) w w.2
      simpa [mul_assoc] using h1
    have h2 : QuotientGroup.mk' Z ((⟨m, hm⟩ : L) * y * (⟨m, hm⟩ : L)⁻¹ * y⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmy
    simp only [map_mul, map_inv] at h2
    calc QuotientGroup.mk' Z y * QuotientGroup.mk' Z ⟨m, hm⟩
        = (QuotientGroup.mk' Z ⟨m, hm⟩ * QuotientGroup.mk' Z y *
            (QuotientGroup.mk' Z ⟨m, hm⟩)⁻¹ * (QuotientGroup.mk' Z y)⁻¹)⁻¹ *
            (QuotientGroup.mk' Z ⟨m, hm⟩ * QuotientGroup.mk' Z y) := by group
      _ = QuotientGroup.mk' Z ⟨m, hm⟩ * QuotientGroup.mk' Z y := by rw [h2, inv_one, one_mul]
  have hbot : Subgroup.center (L ⧸ Z) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (L ⧸ Z)) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hb : b ∈ Subgroup.center (L ⧸ Z) := by
        rw [h0]
        exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨y, hy⟩)

theorem conj_mem_centralizer {L : Subgroup X} {g c : X}
    (hg : g ∈ Subgroup.normalizer (L : Set X)) (hc : c ∈ Subgroup.centralizer (L : Set X)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ L := (Subgroup.mem_normalizer_iff''.mp hg y).mp hy
  have h := Subgroup.mem_centralizer_iff.mp hc _ hy'
  calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * y := by group

theorem mem_centralizer_of_inner_of_mem_centralizer {L I : Subgroup X} (hL : CFSG.IsQuasisimple L)
    (hIL : I ≤ Subgroup.normalizer (L : Set X))
    (hLI : L ≤ I ⊔ Subgroup.centralizer (L : Set X)) {g : X}
    (hgL : g ∈ Subgroup.normalizer (L : Set X))
    (hg : ∃ m ∈ L, ∀ y ∈ L, g * y * g⁻¹ = m * y * m⁻¹)
    (hgI : g ∈ Subgroup.centralizer (I : Set X)) : g ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨m, hmL, hm⟩ := hg
  have hIC : I ≤ Subgroup.normalizer ((Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) :=
    fun i hi => Subgroup.mem_normalizer_iff.mpr fun c =>
      ⟨fun hc => conj_mem_centralizer (hIL hi) hc, fun hc => by
        have := conj_mem_centralizer (Subgroup.inv_mem _ (hIL hi)) hc
        simpa [mul_assoc] using this⟩
  have hdec : ∀ y ∈ L, ∃ i ∈ I, ∃ c ∈ Subgroup.centralizer (L : Set X), y = i * c := by
    intro y hy
    have hy' : y ∈ ((I ⊔ Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) := hLI hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right I _ hIC] at hy'
    obtain ⟨i, hi, c, hc, rfl⟩ := hy'
    exact ⟨i, hi, c, hc, rfl⟩
  have hcomm : ∀ y ∈ L, m * y * m⁻¹ * y⁻¹ ∈ Subgroup.centralizer (L : Set X) := by
    intro y hy
    obtain ⟨i, hi, c, hc, rfl⟩ := hdec y hy
    have hgi : g * i * g⁻¹ = i := by
      rw [(Subgroup.mem_centralizer_iff.mp hgI i hi).symm, mul_inv_cancel_right]
    have hgc := conj_mem_centralizer hgL hc
    have h1 : m * (i * c) * m⁻¹ * (i * c)⁻¹ = i * ((g * c * g⁻¹) * c⁻¹) * i⁻¹ := by
      rw [← hm (i * c) hy]
      calc g * (i * c) * g⁻¹ * (i * c)⁻¹ = (g * i * g⁻¹) * (g * c * g⁻¹) * c⁻¹ * i⁻¹ := by group
        _ = i * ((g * c * g⁻¹) * c⁻¹) * i⁻¹ := by rw [hgi]; group
    rw [h1]
    have hin : (g * c * g⁻¹) * c⁻¹ ∈ Subgroup.centralizer (L : Set X) :=
      Subgroup.mul_mem _ hgc (Subgroup.inv_mem _ hc)
    have := (Subgroup.mem_normalizer_iff.mp (hIC hi) _).mp hin
    exact this
  have hmC := mem_centralizer_of_commutator_mem hL hmL hcomm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hm y hy
  rw [(Subgroup.mem_centralizer_iff.mp hmC y hy).symm, mul_inv_cancel_right] at h1
  calc y * g = (g * y * g⁻¹) * g := by rw [h1]
    _ = g * y := by group

end Quasisimple

section Counting

variable {X : Type*} [Group X] [Finite X]

noncomputable def commHom {D Z : Subgroup X} (hZD : Z ≤ Subgroup.centralizer (D : Set X))
    (hDD : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Z) {x : X} (hx : x ∈ D) : D →* Z where
  toFun d := ⟨(d : X) * x * (d : X)⁻¹ * x⁻¹, hDD _ d.2 _ hx⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' d e := by
    apply Subtype.ext
    set c := (e : X) * x * (e : X)⁻¹ * x⁻¹ with hcdef
    have hcC : c ∈ Subgroup.centralizer (D : Set X) := hZD (hDD _ e.2 _ hx)
    have hcd : (d : X) * c = c * d := Subgroup.mem_centralizer_iff.mp hcC (d : X) d.2
    have hdxD : (d : X) * x * (d : X)⁻¹ * x⁻¹ ∈ D :=
      D.mul_mem (D.mul_mem (D.mul_mem d.2 hx) (D.inv_mem d.2)) (D.inv_mem hx)
    have hcdx := Subgroup.mem_centralizer_iff.mp hcC _ hdxD
    change (d : X) * e * x * ((d : X) * e)⁻¹ * x⁻¹ =
      ((d : X) * x * (d : X)⁻¹ * x⁻¹) * c
    calc (d : X) * e * x * ((d : X) * e)⁻¹ * x⁻¹ = (d : X) * c * x * (d : X)⁻¹ * x⁻¹ := by
          rw [hcdef]; group
      _ = c * ((d : X) * x * (d : X)⁻¹ * x⁻¹) := by rw [hcd]; group
      _ = ((d : X) * x * (d : X)⁻¹ * x⁻¹) * c := hcdx.symm

omit [Finite X] in
theorem mem_ker_commHom_iff {D Z : Subgroup X} (hZD : Z ≤ Subgroup.centralizer (D : Set X))
    (hDD : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Z) {x : X} (hx : x ∈ D) (d : D) :
    d ∈ (commHom hZD hDD hx).ker ↔ (d : X) * x = x * d := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (d : X) * x * (d : X)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h
    calc (d : X) * x = (d : X) * x * (d : X)⁻¹ * x⁻¹ * (x * d) := by group
      _ = x * d := by rw [h1, one_mul]
  · intro h
    apply Subtype.ext
    change (d : X) * x * (d : X)⁻¹ * x⁻¹ = 1
    rw [h]
    group

theorem card_le_nine_mul_card_inf {D Z : Subgroup X} (hZ : Nat.card Z ≤ 3)
    (hZD : Z ≤ Subgroup.centralizer (D : Set X))
    (hDD : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Z) {x y : X} (hx : x ∈ D) (hy : y ∈ D) :
    Nat.card D ≤ 9 * Nat.card (D ⊓ Subgroup.centralizer ({x} : Set X) ⊓
      Subgroup.centralizer ({y} : Set X) : Subgroup X) := by
  set φ := commHom hZD hDD hx
  set ψ := commHom hZD hDD hy
  have hφ : φ.ker.index ≤ 3 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans hZ
  have hψ : ψ.ker.index ≤ 3 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans hZ
  have hinf : (φ.ker ⊓ ψ.ker).index ≤ 9 :=
    (Subgroup.index_inf_le (H := φ.ker) (K := ψ.ker)).trans (by nlinarith)
  have hmap : (φ.ker ⊓ ψ.ker).map D.subtype =
      D ⊓ Subgroup.centralizer ({x} : Set X) ⊓ Subgroup.centralizer ({y} : Set X) := by
    ext g
    constructor
    · rintro ⟨d, ⟨hd1, hd2⟩, rfl⟩
      refine ⟨⟨d.2, ?_⟩, ?_⟩
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((mem_ker_commHom_iff hZD hDD hx d).mp hd1)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((mem_ker_commHom_iff hZD hDD hy d).mp hd2)
    · rintro ⟨⟨hgD, hgx⟩, hgy⟩
      refine ⟨⟨g, hgD⟩, ⟨?_, ?_⟩, rfl⟩
      · exact (mem_ker_commHom_iff hZD hDD hx _).mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hgx)
      · exact (mem_ker_commHom_iff hZD hDD hy _).mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hgy)
  rw [← hmap, Subgroup.card_map_of_injective D.subtype_injective,
    ← Subgroup.card_mul_index (φ.ker ⊓ ψ.ker)]
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ hinf

end Counting

section Shape

variable {W : Type} [Group W] [Finite W]

theorem shape_of_isZ3L34OrHeisSL34 (hW : IsZ3L34OrHeisSL34 W) {N E : Subgroup W} [N.Normal]
    [Group.IsPerfect N] (hs : Group.IsSolvable (W ⧸ N)) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEN : E ⊔ N = ⊤) :
    (Nonempty (N ≃* projSL 3 (GaloisField 2 2)) ∨
      Nonempty (N ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) ∧
      Nat.card (E ⊓ Subgroup.centralizer (N : Set W) : Subgroup W) ≤ 3 := by
  rcases hW with he | ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩
  ·
    obtain ⟨e⟩ := he
    set P := projSL 3 (GaloisField 2 2)
    have : Group.IsPerfect P := isPerfect_projSL
    set φ : W →* Multiplicative (ZMod 3) := (MonoidHom.fst _ _).comp e.toMonoidHom with hφ
    set Pw : Subgroup W := ((MonoidHom.inr (Multiplicative (ZMod 3)) P).range).comap
      e.toMonoidHom with hPw
    have hPwe : Pw.map e.toMonoidHom = (MonoidHom.inr (Multiplicative (ZMod 3)) P).range :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective _
    set ePw : Pw ≃* P := (Pw.equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hPwe).trans
        ((MonoidHom.inr (Multiplicative (ZMod 3)) P).ofInjective
          (fun a b h => congrArg Prod.snd h)).symm) with hePw
    have : Group.IsPerfect Pw :=
      Group.IsPerfect.ofSurjective (f := ePw.symm.toMonoidHom) ePw.symm.surjective
    have hPwN : Pw ≤ N := le_of_isPerfect_of_isSolvable_quotient hs
    have hNPw : N ≤ Pw := by
      have hNφ : N ≤ φ.ker := by
        have : Group.IsPerfect (N.map φ) := Group.IsPerfect.map φ
        have hcomm' : ∀ a b : N.map φ, a * b = b * a := fun a b => Subtype.ext (mul_comm _ _)
        have hsub : Subsingleton (N.map φ) := by
          by_contra hnt
          rw [not_subsingleton_iff_nontrivial] at hnt
          exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hcomm')
        intro x hx
        have h1 := congrArg Subtype.val
          (Subsingleton.elim (⟨φ x, x, hx, rfl⟩ : N.map φ) 1)
        exact h1
      intro x hx
      have hx1 : (e x).1 = 1 := hNφ hx
      refine ⟨(e x).2, ?_⟩
      ext
      · exact hx1.symm
      · rfl
    have hNeq : N = Pw := le_antisymm hNPw hPwN
    refine ⟨Or.inl ⟨(MulEquiv.subgroupCongr hNeq).trans ePw⟩, ?_⟩
    have hcen : ∀ x ∈ Subgroup.centralizer (N : Set W), (e x).2 = 1 := by
      intro x hx
      have hc : (e x).2 ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro p
        have hpN : e.symm (1, p) ∈ N := by
          rw [hNeq]
          refine ⟨p, ?_⟩
          change (1, p) = e (e.symm (1, p))
          rw [MulEquiv.apply_symm_apply]
        have h1 := Subgroup.mem_centralizer_iff.mp hx _ hpN
        have h2 := congrArg (fun w => (e w).2) h1
        simpa using h2
      rw [center_projSL_eq_bot] at hc
      exact hc
    have hinj : Function.Injective
        (fun x : (E ⊓ Subgroup.centralizer (N : Set W) : Subgroup W) => (e x).1) := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact Prod.ext hxy ((hcen x x.2.2).trans (hcen y y.2.2).symm)
    calc Nat.card (E ⊓ Subgroup.centralizer (N : Set W) : Subgroup W)
        ≤ Nat.card (Multiplicative (ZMod 3)) := Nat.card_le_card_of_injective _ hinj
      _ = 3 := by rw [Nat.card_eq_fintype_card]; rfl
  ·
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have : Group.IsPerfect V :=
      Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
    have hVN : V ≤ N := le_of_isPerfect_of_isSolvable_quotient hs
    have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 3) hU.2.1
    have hkey : ∀ u ∈ U, ∀ x ∈ V, u * x * u⁻¹ = x := fun u hu x hx => by
      rw [hcomm u hu x hx, mul_inv_cancel_right]
    have hVn : V.Normal := by
      refine ⟨fun v hv w => ?_⟩
      obtain ⟨u, hu, v', hv', rfl⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hUV hcomm w
      have hx : v' * v * v'⁻¹ ∈ V := V.mul_mem (V.mul_mem hv' hv) (V.inv_mem hv')
      have h1 : u * v' * v * (u * v')⁻¹ = u * (v' * v * v'⁻¹) * u⁻¹ := by group
      rw [h1, hkey u hu _ hx]
      exact hx
    have hsV : Group.IsSolvable (W ⧸ V) := by
      have : Group.IsNilpotent U := hUp.isNilpotent
      refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' V).comp U.subtype) ?_
      intro q
      induction q using QuotientGroup.induction_on with
      | H w =>
        obtain ⟨u, hu, v, hv, rfl⟩ := KFacts.L34.exists_mul_eq_of_sup_eq_top hUV hcomm w
        refine ⟨⟨u, hu⟩, ?_⟩
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        change u⁻¹ * (u * v) ∈ V
        rwa [inv_mul_cancel_left]
    have hNV : N ≤ V := le_of_isPerfect_of_isSolvable_quotient hsV
    have hNeq : N = V := le_antisymm hNV hVN
    refine ⟨Or.inr ⟨(MulEquiv.subgroupCongr hNeq).trans eV⟩, ?_⟩
    have hCU : Subgroup.centralizer (N : Set W) = U := by
      rw [hNeq]
      exact KFacts.L34.centralizer_eq_of_isHeisSL hUV hcomm ⟨eV⟩ hcard
    have hle : E ⊓ Subgroup.centralizer (N : Set W) ≤ (Subgroup.center U).map U.subtype := by
      rintro c ⟨hcE, hcC⟩
      have hcU : c ∈ U := hCU ▸ hcC
      refine ⟨⟨c, hcU⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
      have hu : (u : W) ∈ ((E ⊔ N : Subgroup W) : Set W) := by rw [hEN]; trivial
      rw [Subgroup.coe_mul_of_left_le_normalizer_right E N
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)] at hu
      obtain ⟨a, ha, n, hn, hun⟩ := hu
      change (u : W) * c = c * u
      rw [← hun]
      have h1 : a * c = c * a := hE a ha c hcE
      have h2 : n * c = c * n := Subgroup.mem_centralizer_iff.mp hcC n hn
      calc a * n * c = a * (n * c) := by group
        _ = a * (c * n) := by rw [h2]
        _ = (a * c) * n := by group
        _ = c * (a * n) := by rw [h1]; group
    calc Nat.card (E ⊓ Subgroup.centralizer (N : Set W) : Subgroup W)
        ≤ Nat.card ((Subgroup.center U).map U.subtype) := Subgroup.card_le_of_le hle
      _ = 3 := by
        rw [Subgroup.card_map_of_injective U.subtype_injective]
        exact hU.1.2.2.2.le.antisymm hU.1.2.2.2.ge

end Shape

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
