module

public import CFSG.RankThree.PartTwo.Sec21.Item229Gen
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
public import CFSG.RankThree.PartTwo.Sec21.Item227
public import CFSG.RankThree.PartTwo.Sec21.Item229Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item22Sec7
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open Matrix

variable {G : Type} [Group G]


theorem mem_of_mem_centralizer_of_orderOf_eq_three' {A : Subgroup G} (hA : A ∈ partTwoF G)
    {x : G} (hx : x ∈ Subgroup.centralizer (A : Set G)) (hx3 : orderOf x = 3) : x ∈ A :=
  Sec4.mem_of_maximal_of_commute ⟨hA.1, fun B hB hAB => (hA.2.1 B hB hAB).le⟩
    (by rw [← hx3]; exact pow_orderOf_eq_one x) fun a ha => Subgroup.mem_centralizer_iff.mp hx a ha

theorem exists_coord_image_dStar [Finite G] (h2131 : Item2131One) (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) :
    ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A, (wStar A).map (coordGL f) ≤ monomial ∧
      (coordGL f '' dStar A = swapRefl ∨ coordGL f '' dStar A = monoRefl) := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : IsMulCommutative A := hAe.1
  obtain ⟨f, hWf, G₀, hG₀W, ⟨eG₀⟩⟩ := h2131 G A E U c L hpair hA27
  obtain ⟨-, ⟨φ0, hφ0L, hφ0D⟩, hcase⟩ := h222 G A E U c L hpair
  have hDW := dStar_subset_wStar A
  have hinj := coordGL_injective f
  have hG₀m : G₀.map (coordGL f) ≤ monomial := (Subgroup.map_mono hG₀W).trans hWf
  let eG₀' : G₀.map (coordGL f) ≃* alternatingGroup (Fin 4) :=
    (G₀.equivMapOfInjective _ hinj).symm.trans eG₀
  have hDm : ∀ d ∈ dStar A, coordGL f d ∈ monomial := fun d hd => hWf ⟨d, hDW hd, rfl⟩
  have hDr : ∀ d ∈ dStar A, IsReflectionOn d := fun d hd => hd.1
  have hinv : ∀ g ∈ G₀, ∀ d ∈ dStar A, g * d * g⁻¹ ∈ dStar A :=
    fun g hg d hd => conj_mem_dStar_of_mem_wStar (hG₀W hg) hd
  have hcase0 := hcase φ0 hφ0L hφ0D
  obtain ⟨s, hsL, hsD, t, htL, htD, hst⟩ : ∃ s ∈ starOf A L, s ∈ dStar A ∧
      ∃ t ∈ starOf A L, t ∈ dStar A ∧ s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    have hcomm : ((starOf A L : Set (MulAut A)) ∩ dStar A).Pairwise Commute :=
      fun x hx y hy _ => hcon x hx.1 hx.2 y hy.1 hy.2
    have hab : IsMulCommutative (starOf A L) := by
      have h1 := Subgroup.isMulCommutative_closure hcomm
      have hgen := (h222 G A E U c L hpair).1
      rw [← hgen] at h1
      exact h1
    rcases hcase0 with ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, n, -, -, -, -, ⟨e⟩⟩ |
        ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, -, -, ⟨e⟩⟩ | ⟨h81, -⟩
    · exact not_isMulCommutative_perm_three (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · rw [hA27] at h81
      norm_num at h81
  exact ⟨f, hWf, image_eq_swapRefl_or_eq_monoRefl hAc f hG₀m eG₀' hDm hDr hinv
    ⟨s, hsD, t, htD, hst⟩⟩

theorem nonempty_kOf_conj_mulEquiv [Finite G] {A : Subgroup G} (hK : KOfWellDefined A)
    (w : Subgroup.normalizer (A : Set G)) {φ : MulAut A} (hφ : φ ∈ dStar A) :
    Nonempty (kOf A (wConj A w * φ * (wConj A w)⁻¹) ≃* kOf A φ) := by
  rw [kOf_conj_of_unique hK w hφ]
  exact ⟨((kOf A φ).equivMapOfInjective _ (MulAut.conj (w : G)).injective).symm⟩

theorem nonempty_kOf_mulEquiv_of_conj [Finite G] {A : Subgroup G} (hK : KOfWellDefined A)
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) {g : MulAut A} (hg : g ∈ wStar A)
    (h : g * φ * g⁻¹ = ψ) : Nonempty (kOf A ψ ≃* kOf A φ) := by
  obtain ⟨w, rfl⟩ := hg
  rw [← h]
  exact nonempty_kOf_conj_mulEquiv hK w hφ

theorem mul_self_of_mem_dStar {A : Subgroup G} {φ : MulAut A} (hφ : φ ∈ dStar A) : φ * φ = 1 :=
  Sec7.mul_self_eq_one_of_orderOf_eq_two hφ.1.1

theorem nonempty_kOf_mulEquiv_of_orderOf_eq_three [Finite G] {A : Subgroup G}
    (hK : KOfWellDefined A) {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A)
    (h3 : orderOf (φ * ψ) = 3) : Nonempty (kOf A ψ ≃* kOf A φ) := by
  have hc := Sec7.conj_eq_of_orderOf_mul_eq_three (mul_self_of_mem_dStar hφ)
    (mul_self_of_mem_dStar hψ) (by rw [← h3]; exact pow_orderOf_eq_one _)
  exact nonempty_kOf_mulEquiv_of_conj hK hφ ((wStar A).mul_mem (dStar_subset_wStar A hφ)
    (dStar_subset_wStar A hψ)) hc

theorem mem_starOf_sup [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) :
    φ ∈ starOf A (kOf A φ ⊔ kOf A ψ) ∧ ψ ∈ starOf A (kOf A φ ⊔ kOf A ψ) :=
  ⟨starOf_mono A le_sup_left (mem_starOf_kOf h222 hpair hK hφ),
    starOf_mono A le_sup_right (mem_starOf_kOf h222 hpair hK hψ)⟩

theorem dvd_card_starOf {A X : Subgroup G} {g : MulAut A} (hg : g ∈ starOf A X) :
    orderOf g ∣ Nat.card (starOf A X) := by
  have := orderOf_dvd_natCard (⟨g, hg⟩ : starOf A X)
  rwa [Subgroup.orderOf_mk] at this

theorem starOf_dihedral_of_mem_lThreeStar [Finite G] (h222 : Item222) {A : Subgroup G}
    (hA : Sec21Std G A) (hA27 : Nat.card A = 3 ^ 3) {X : Subgroup G} (hX : X ∈ lThreeStar A)
    {S : Type} [Group S] [IsSimpleGroup S] (e : X ≃* S) :
    starOf A X = Subgroup.closure ((starOf A X : Set (MulAut A)) ∩ dStar A) ∧
      Nonempty (starOf A X ≃* DihedralGroup 4) := by
  obtain ⟨-, E', hE', U', hU', c', hp⟩ := hX
  obtain ⟨hgen, ⟨χ, hχX, hχD⟩, hcase⟩ := h222 G A E' U' c' X ⟨hA, hE', hU', hp⟩
  refine ⟨hgen, ?_⟩
  have hXc : X ∈ thetaComponentsAt 3 c' := (lZeroStarAt_subset A c') hp.2.2.1
  have hperf : Group.IsPerfect X := isPerfect_of_mem_thetaComponentsIn hXc
  rcases hcase χ hχX hχD with ⟨-, n, hn0, hne, ⟨eL⟩, -, -⟩ | ⟨-, -, -, -, -, -, he⟩ |
      ⟨-, -, -, -, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨h81, -⟩
  · have : IsSimpleGroup X := e.isSimpleGroup
    have hθ := inSubgroup_theta_eq_bot_of_isSimpleGroup hperf
    have : IsSimpleGroup (SL3 n) :=
      (((mulEquiv_lBar_of_theta_eq_bot hθ).trans eL).symm.trans e).isSimpleGroup
    exact absurd this (not_isSimpleGroup_SL3 hn0 hne)
  · exact he
  · exact he
  · exact he
  · rw [hA27] at h81
    norm_num at h81

theorem not_dihedral_of_image_eq_swapRefl {A : Subgroup G}
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (hD : coordGL f '' dStar A = swapRefl)
    {Z : Subgroup (MulAut A)} (hZ : Z = Subgroup.closure ((Z : Set (MulAut A)) ∩ dStar A))
    (e : Z ≃* DihedralGroup 4) : False := by
  have hinj := coordGL_injective f
  have hsw : ∀ d ∈ dStar A, coordGL f d ∈ swapRefl := fun d hd => hD ▸ ⟨d, hd, rfl⟩
  have hcard : Nat.card Z = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  by_cases hcomm : ((Z : Set (MulAut A)) ∩ dStar A).Pairwise Commute
  · have hab := Subgroup.isMulCommutative_closure hcomm
    rw [← hZ] at hab
    exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
  · simp only [Set.Pairwise, not_forall] at hcomm
    obtain ⟨x, hx, y, hy, -, hxy⟩ := hcomm
    rcases swapRefl_commute_or_cube (hsw x hx.2) (hsw y hy.2) with hc | h3
    · exact hxy (hinj (by rw [map_mul, map_mul]; exact hc))
    · have h3' : (x * y) ^ 3 = 1 := hinj (by rw [map_pow, map_mul, h3, map_one])
      have hne : x * y ≠ 1 := by
        intro h1
        apply hxy
        have hx2 : x * x = 1 := mul_self_of_mem_dStar hx.2
        have : y = x := by
          calc y = x * x * y := by rw [hx2, one_mul]
            _ = x * (x * y) := by rw [mul_assoc]
            _ = x := by rw [h1, mul_one]
        rw [this]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hord : orderOf (x * y) = 3 := orderOf_eq_prime h3' hne
      have hxyZ : x * y ∈ Z := Z.mul_mem hx.1 hy.1
      have hdvd := orderOf_dvd_natCard (⟨x * y, hxyZ⟩ : Z)
      rw [Subgroup.orderOf_mk, hord, hcard] at hdvd
      norm_num at hdvd

theorem isSimpleGroup_projSL_two {m : ℕ} (hm : 2 ≤ m) :
    IsSimpleGroup (projSL 2 (GaloisField 2 m)) :=
  have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [GaloisField.card 2 m (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ le_rfl (Or.inr (by omega)) (Or.inr (by omega))

theorem exists_not_commute_of_mulEquiv_projSL {X : Type*} [Group X] {m : ℕ}
    (e : X ≃* projSL 2 (GaloisField 2 m)) : ∃ a b : X, a * b ≠ b * a := by
  let e' := e.trans (projSLTwoEquivSL (GaloisField 2 m))
  have hz : orderOf (e'.symm sl2OrderThree) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_sl2OrderThree
  obtain ⟨j, -, hjz⟩ := exists_inv_conj_of_mulEquiv_projSL e hz
  refine ⟨j, e'.symm sl2OrderThree, fun h => ?_⟩
  rw [h, mul_inv_cancel_right] at hjz
  have h2 : (e'.symm sl2OrderThree) ^ 2 = 1 := by
    rw [sq]
    calc e'.symm sl2OrderThree * e'.symm sl2OrderThree =
        e'.symm sl2OrderThree * (e'.symm sl2OrderThree)⁻¹ := by rw [← hjz]
      _ = 1 := mul_inv_cancel _
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hz] at this
  norm_num at this

theorem isPerfect_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : Group.IsPerfect X := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    exact hab (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top a)) b
      (Subgroup.mem_top b)).symm
  · exact ht

theorem isPerfect_of_mulEquiv_projSL {X : Type*} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (e : X ≃* projSL 2 (GaloisField 2 m)) : Group.IsPerfect X := by
  have := isSimpleGroup_projSL_two hm
  have : IsSimpleGroup X := e.isSimpleGroup
  exact isPerfect_of_isSimpleGroup (exists_not_commute_of_mulEquiv_projSL e)

theorem isPerfect_sup {X Y : Subgroup G} (hX : Group.IsPerfect X) (hY : Group.IsPerfect Y) :
    Group.IsPerfect (X ⊔ Y : Subgroup G) := by
  rw [Subgroup.isPerfect_iff] at hX hY ⊢
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact (X ⊔ Y).mul_mem ((X ⊔ Y).mul_mem ((X ⊔ Y).mul_mem ha hb) ((X ⊔ Y).inv_mem ha))
      ((X ⊔ Y).inv_mem hb)
  · calc X = ⁅X, X⁆ := hX.symm
      _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc Y = ⁅Y, Y⁆ := hY.symm
      _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem not_lBar_SL3_of_simple [Finite G] {Y : Subgroup G} (hY : Group.IsPerfect Y)
    {S : Type} [Group S] [IsSimpleGroup S] (e : Y ≃* S) {n : ℕ} (hn : 0 < n) (he : Even n)
    (eL : lBar Y ≃* SL3 n) : False := by
  have : IsSimpleGroup Y := e.isSimpleGroup
  have hθ := inSubgroup_theta_eq_bot_of_isSimpleGroup hY
  have : IsSimpleGroup (SL3 n) :=
    (((mulEquiv_lBar_of_theta_eq_bot hθ).trans eL).symm.trans e).isSimpleGroup
  exact not_isSimpleGroup_SL3 hn he this

theorem card_of_mulEquiv_dihedral {X : Type*} [Group X] (e : X ≃* DihedralGroup 4) :
    Nat.card X = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]

theorem card_of_mulEquiv_perm_three {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) :
    Nat.card X = 6 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_kOf_sup_SL3 [Finite G] (h222 : Item222) (h228 : Item228)
    (hL3 : Item228LThree) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA27 : Nat.card A = 3 ^ 3) (hK : KOfWellDefined A) {φ ψ : MulAut A} (hφ : φ ∈ dStar A)
    (hψ : ψ ∈ dStar A) (h3 : orderOf (φ * ψ) = 3) :
    ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* SL3 m) := by
  have hφ2 := mul_self_of_mem_dStar hφ
  have hψ2 := mul_self_of_mem_dStar hψ
  have hnc : ψ * φ ≠ φ * ψ := by
    intro hc
    have h2 : (φ * ψ) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc ψ, hc, mul_assoc, hψ2, mul_one, hφ2]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h3] at this
    norm_num at this
  have hne : ψ ≠ φ := by
    intro h
    apply hnc
    rw [h]
  have h3Y : 3 ∣ Nat.card (starOf A (kOf A φ ⊔ kOf A ψ)) := by
    obtain ⟨h1, h2⟩ := mem_starOf_sup h222 hpair hK hφ hψ
    have := dvd_card_starOf ((starOf A _).mul_mem h1 h2)
    rwa [h3] at this
  obtain ⟨hX1, -, hX3⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  rcases hX3 hnc with ⟨hYL, hcase, -⟩ | ⟨-, X, hX, hYX, ⟨eX⟩⟩
  · have hYperf : Group.IsPerfect (kOf A φ ⊔ kOf A ψ : Subgroup G) :=
      isPerfect_of_mem_thetaComponentFamily (lStar_subset A hYL)
    rcases hcase with ⟨-, n, hn0, hne', ⟨eL⟩, ⟨eK⟩, -⟩ | ⟨-, -, -, -, -, -, ⟨e8⟩⟩ |
        ⟨-, -, -, -, -, -, ⟨e8⟩⟩ | ⟨-, -, -, ⟨e8⟩⟩ | ⟨h81, -⟩
    · obtain ⟨m', hm'0, hm'e, ⟨eK'⟩, hX'⟩ := hX1 _ hYL le_sup_left
      have hm : m' = n := eq_of_mulEquiv_projSL_two (by omega) (by omega) (eK'.symm.trans eK)
      subst hm
      obtain ⟨eψ⟩ := nonempty_kOf_mulEquiv_of_orderOf_eq_three hK hφ hψ h3
      refine ⟨m', hm'0, hm'e, ⟨eK⟩, ⟨eψ.trans eK⟩, ?_⟩
      have hm2 : 2 ≤ m' := by obtain ⟨k, hk⟩ := hm'e; omega
      rcases hX' with hSL | hS | hS | ⟨hm4, hS⟩ | ⟨-, hS⟩
      · exact hSL
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSp_two hm2
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSU (m := 4) (n := m') le_rfl (by omega)
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSU (m := 4) (n := m' / 2) le_rfl (by omega)
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
      · obtain ⟨eS⟩ := hS
        have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
        exact (not_lBar_SL3_of_simple hYperf eS hm'0 hm'e eL).elim
    · rw [card_of_mulEquiv_dihedral e8] at h3Y
      norm_num at h3Y
    · rw [card_of_mulEquiv_dihedral e8] at h3Y
      norm_num at h3Y
    · rw [card_of_mulEquiv_dihedral e8] at h3Y
      norm_num at h3Y
    · rw [hA27] at h81
      norm_num at h81
  · have hX3' := hL3 G A E U c L hpair hA27 φ hφ ψ hψ hne.symm X hX hYX (Or.inr ⟨eX⟩)
    have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
    obtain ⟨-, ⟨e8⟩⟩ := starOf_dihedral_of_mem_lThreeStar h222 hpair.toSec21Std hA27 hX3' eX
    have hdvd := h3Y.trans (Subgroup.card_dvd_of_le (starOf_mono A hYX))
    rw [card_of_mulEquiv_dihedral e8] at hdvd
    norm_num at hdvd

theorem commute_kOf_of_not_conj [Finite G] (h228 : Item228) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) (hc : ψ * φ = φ * ψ)
    (hnconj : ∀ w ∈ wStar A, w * φ * w⁻¹ ≠ ψ) :
    ∀ x ∈ kOf A φ, ∀ y ∈ kOf A ψ, x * y = y * x := by
  obtain ⟨-, hX2, -⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  rcases hX2 hc with hb | ⟨-, -, -, -, -, -, -, w, hw, hwφ⟩ | ⟨-, -, -, -, w, hw, hwφ⟩
  · intro x hx y hy
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  · exact (hnconj w hw hwφ).elim
  · exact (hnconj w hw hwφ).elim

theorem commute_kOf_of_swapRefl [Finite G] (h222 : Item222) (h228 : Item228)
    (hL3 : Item228LThree) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA27 : Nat.card A = 3 ^ 3) (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    (hD : coordGL f '' dStar A = swapRefl) {φ ψ : MulAut A} (hφ : φ ∈ dStar A)
    (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) (hc : ψ * φ = φ * ψ) :
    ∀ x ∈ kOf A φ, ∀ y ∈ kOf A ψ, x * y = y * x := by
  obtain ⟨-, hX2, -⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  rcases hX2 hc with hb | ⟨hYL, m, hm0, hm4, -, -, ⟨eY⟩, -⟩ | ⟨-, -, -, ⟨X, hX, hYX, ⟨eX⟩⟩, -⟩
  · intro x hx y hy
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
  · have hY3 := hL3 G A E U c L hpair hA27 φ hφ ψ hψ hne.symm _ hYL le_rfl
      (Or.inl ⟨m / 2, ⟨eY⟩⟩)
    have := isSimpleGroup_projSU (m := 4) (n := m / 2) le_rfl (by omega)
    obtain ⟨hgen, ⟨e8⟩⟩ := starOf_dihedral_of_mem_lThreeStar h222 hpair.toSec21Std hA27 hY3 eY
    exact (not_dihedral_of_image_eq_swapRefl f hD hgen e8).elim
  · have hX3 := hL3 G A E U c L hpair hA27 φ hφ ψ hψ hne.symm X hX hYX (Or.inr ⟨eX⟩)
    have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
    obtain ⟨hgen, ⟨e8⟩⟩ := starOf_dihedral_of_mem_lThreeStar h222 hpair.toSec21Std hA27 hX3 eX
    exact (not_dihedral_of_image_eq_swapRefl f hD hgen e8).elim

theorem inf_eq_bot_of_commute {X Y : Subgroup G} {m : ℕ}
    (e : X ≃* projSL 2 (GaloisField 2 m)) (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    X ⊓ Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, hz.1⟩ : X) = 1 := eq_one_of_forall_commute_of_mulEquiv_projSL e fun x =>
    Subtype.ext (h x x.2 z hz.2)
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)

theorem fixed_p01_p12_m01 : ∀ v : Fin 3 → ZMod 3,
    (p01 : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v →
    (p12 : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v →
    (m01 : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v → v = 0 := by
  decide +kernel

theorem fixed_p01_p12_d2 : ∀ v : Fin 3 → ZMod 3,
    (p01 : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v →
    (p12 : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v →
    (d2 : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v → v = 0 := by
  decide +kernel

theorem eq_one_of_fixed_coord {A : Subgroup G} (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    {φ₁ φ₂ φ₃ : MulAut A} {M₁ M₂ M₃ : GL (Fin 3) (ZMod 3)} (h₁ : coordGL f φ₁ = M₁)
    (h₂ : coordGL f φ₂ = M₂) (h₃ : coordGL f φ₃ = M₃)
    (hfix : ∀ v : Fin 3 → ZMod 3, (M₁ : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v →
      (M₂ : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v →
      (M₃ : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v → v = 0)
    {a : A} (ha₁ : φ₁ a = a) (ha₂ : φ₂ a = a) (ha₃ : φ₃ a = a) : a = 1 := by
  set v : Fin 3 → ZMod 3 := Multiplicative.toAdd (f.symm a)
  have hv : ∀ {φ : MulAut A} {M : GL (Fin 3) (ZMod 3)}, coordGL f φ = M → φ a = a →
      (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v := by
    intro φ M hM hφ
    rw [← hM, coordGL_mulVec, coordLin3_apply]
    simp only [v, ofAdd_toAdd, MulEquiv.apply_symm_apply, hφ]
  have h0 := hfix v (hv h₁ ha₁) (hv h₂ ha₂) (hv h₃ ha₃)
  have : f.symm a = 1 := by
    simpa [v] using congrArg Multiplicative.ofAdd h0
  simpa using congrArg f this

theorem coprime_card_center_six [Finite G] (h224 : Item224) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {I : Subgroup G} (hAI : A ≤ I)
    (hfix : ∀ a ∈ A, (∀ x ∈ I, a * x = x * a) → a = 1) :
    Nat.Coprime (Nat.card (Subgroup.center I)) 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : (Subgroup.center I).map I.subtype ≤ Subgroup.centralizer (A : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨a, hAI ha⟩)
  have hodd : Odd (Nat.card (Subgroup.center I)) := by
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective I.subtype_injective] at hdvd
    exact (h224 G A E U c L hpair).of_dvd_nat hdvd
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center I) := by
    intro h3
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hzC : ((z : I) : G) ∈ Subgroup.centralizer (A : Set G) := hle ⟨z, z.2, rfl⟩
    have hz3 : orderOf ((z : I) : G) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hzA := mem_of_mem_centralizer_of_orderOf_eq_three' hpair.mem_S.1 hzC hz3
    have h1 := hfix _ hzA fun x hx =>
      (congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨x, hx⟩)).symm
    rw [h1, orderOf_one] at hz3
    norm_num at hz3
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm

theorem iSup_fin_three (K : Fin 3 → Subgroup G) : (⨆ i, K i) = K 0 ⊔ K 1 ⊔ K 2 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · exact sup_le (sup_le (le_iSup K 0) (le_iSup K 1)) (le_iSup K 2)

theorem iGroup_eq_sup_three [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {t₁ t₂ t₃ : MulAut A}
    (h₁ : t₁ ∈ dStar A) (h₂ : t₂ ∈ dStar A) (h₃ : t₃ ∈ dStar A)
    (hfuse : ∀ φ ∈ dStar A, ∃ g ∈ Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A)),
      ∃ τ ∈ ({t₁, t₂, t₃} : Set (MulAut A)), g * τ * g⁻¹ = φ) :
    iGroup A = kOf A t₁ ⊔ kOf A t₂ ⊔ kOf A t₃ := by
  have hT : ({t₁, t₂, t₃} : Set (MulAut A)) ⊆ dStar A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  rw [iGroup_eq_iSup_of_fuse h222 hpair hK hT hfuse, iSup_insert, iSup_insert, iSup_singleton,
    sup_assoc]

theorem isChainSystem_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {t₁ t₂ t₃ : MulAut A}
    (h₁ : t₁ ∈ dStar A) (h₂ : t₂ ∈ dStar A) (h₃ : t₃ ∈ dStar A) (h12 : t₁ ≠ t₂)
    (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) (hAI : A ≤ kOf A t₁ ⊔ kOf A t₂ ⊔ kOf A t₃)
    (hc : ∀ x ∈ kOf A t₁, ∀ y ∈ kOf A t₃, x * y = y * x) (hinf : kOf A t₁ ⊓ kOf A t₃ = ⊥) :
    IsChainSystem 3 A ![kOf A t₁, kOf A t₂, kOf A t₃] where
  commute i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact hc
  inf_eq_bot i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact hinf
  elem := hpair.mem_S.1.1
  le := by
    rw [iSup_fin_three]
    simpa using hAI
  split i := by
    fin_cases i
    · exact eq_sup_inf_centralizer_kOf h222 hpair hK h₁
    · exact eq_sup_inf_centralizer_kOf h222 hpair hK h₂
    · exact eq_sup_inf_centralizer_kOf h222 hpair hK h₃
  index i := by
    fin_cases i
    · exact card_eq_three_mul_inf_centralizer_kOf h222 hpair hK h₁
    · exact card_eq_three_mul_inf_centralizer_kOf h222 hpair hK h₂
    · exact card_eq_three_mul_inf_centralizer_kOf h222 hpair hK h₃
  index₂ i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₁ h₂ h12
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₁ h₃ h13
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₂ h₁ h12.symm
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₂ h₃ h23
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₃ h₁ h13.symm
    · exact card_eq_nine_mul_inf_centralizer_kOf h222 hpair hK h₃ h₂ h23.symm

theorem eq_of_le_of_mem_lStar [Finite G] {A L Y : Subgroup G} (hL : L ∈ lStar A)
    (hY : Y ∈ lStar A) (hYL : Y ≤ L) (hθ : inSubgroup (aschbacherSolvableCore 3) L = ⊥) :
    L = Y := by
  have hYperf := isPerfect_of_mem_thetaComponentFamily (lStar_subset A hY)
  have hYL' : llRel Y L := by
    rw [llRel, inf_eq_left.mpr hYL, inSubgroup_perfectResidual_of_isPerfect hYperf]
    exact (sup_eq_left.mpr (Subgroup.map_subtype_le _)).symm
  have h := hY.2 L (lStar_subset A hL) hYL'
  rwa [llRel, inf_eq_right.mpr hYL, inSubgroup_perfectResidual_of_isPerfect hYperf, hθ,
    sup_bot_eq] at h

theorem dihedral_involutions : ∀ x y : DihedralGroup 4, x * x = 1 → y * y = 1 →
    x * y ≠ y * x → (x * y) ^ 4 = 1 ∧ (x * y) ^ 2 ≠ 1 := by
  decide

theorem exists_orderOf_mul_eq_four {X : Type*} [Group X] {Z : Subgroup X} {S : Set X}
    (hS : ∀ s ∈ S, s * s = 1) (hZ : Z = Subgroup.closure (S ∩ (Z : Set X)))
    (e : Z ≃* DihedralGroup 4) : ∃ s ∈ S ∩ (Z : Set X), ∃ t ∈ S ∩ (Z : Set X),
      orderOf (s * t) = 4 := by
  by_cases hcomm : (S ∩ (Z : Set X)).Pairwise Commute
  · have hab := Subgroup.isMulCommutative_closure hcomm
    rw [← hZ] at hab
    exact (not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)).elim
  · simp only [Set.Pairwise, not_forall] at hcomm
    obtain ⟨x, hx, y, hy, -, hxy⟩ := hcomm
    refine ⟨x, hx, y, hy, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hx' : e ⟨x, hx.2⟩ * e ⟨x, hx.2⟩ = 1 := by
      rw [← map_mul, ← map_one e]
      exact congrArg e (Subtype.ext (hS x hx.1))
    have hy' : e ⟨y, hy.2⟩ * e ⟨y, hy.2⟩ = 1 := by
      rw [← map_mul, ← map_one e]
      exact congrArg e (Subtype.ext (hS y hy.1))
    have hxy' : e ⟨x, hx.2⟩ * e ⟨y, hy.2⟩ ≠ e ⟨y, hy.2⟩ * e ⟨x, hx.2⟩ := by
      intro h
      apply hxy
      have h' : (⟨x, hx.2⟩ * ⟨y, hy.2⟩ : Z) = ⟨y, hy.2⟩ * ⟨x, hx.2⟩ :=
        e.injective (by rw [map_mul, map_mul]; exact h)
      exact congrArg Subtype.val h'
    obtain ⟨h4, h2⟩ := dihedral_involutions _ _ hx' hy' hxy'
    have hord : orderOf (e ⟨x, hx.2⟩ * e ⟨y, hy.2⟩) = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (by simpa using h2) (by simpa using h4)
    rw [← map_mul, MulEquiv.orderOf_eq] at hord
    have : orderOf (⟨x, hx.2⟩ * ⟨y, hy.2⟩ : Z) = orderOf (x * y) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [this] at hord
    simpa using hord

end CFSG.RankThree.PartTwo.Sec21
