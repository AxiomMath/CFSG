module

public import CFSG.OddTranspositions.PartFour.FixedFreeCount
public import CFSG.OddTranspositions.PartFour.LineVmem
public import CFSG.OddTranspositions.PartFour.OrbitPower

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def rootLiftSubgroup (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    Subgroup (Halpha D hC.alpha) :=
  Subgroup.closure
    {d | d ∈ DstarH hC ∧ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ∈ S₀}

@[expose] def rootLiftClass (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    Set ↥(rootLiftSubgroup hC S₀) :=
  {d | (d : Halpha D hC.alpha) ∈ DstarH hC ∧
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (d : Halpha D hC.alpha) ∈ S₀}

private theorem rootLift_mem_subgroup (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {d : Halpha D hC.alpha} (hd : d ∈ DstarH hC)
    (hm : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ∈ S₀) :
    d ∈ rootLiftSubgroup hC S₀ :=
  Subgroup.subset_closure ⟨hd, hm⟩

private theorem rootLift_mk_mem (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {d : Halpha D hC.alpha} (hd : d ∈ rootLiftSubgroup hC S₀) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ∈ Subgroup.closure S₀ := by
  let R := CFSG.solvableRadical (Halpha D hC.alpha)
  let mk := QuotientGroup.mk' R
  have hle : rootLiftSubgroup hC S₀ ≤ (Subgroup.closure S₀).comap mk :=
    (Subgroup.closure_le _).mpr (fun z hz =>
      Subgroup.mem_comap.mpr (Subgroup.subset_closure hz.2))
  exact Subgroup.mem_comap.mp (hle hd)

private theorem rootLift_exists_lift (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {x : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hS₀ : S₀ ⊆ imageClass hC) (hx : x ∈ S₀) :
    ∃ d : ↥(rootLiftSubgroup hC S₀), d ∈ rootLiftClass hC S₀ ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) = x := by
  obtain ⟨d, hd, rfl⟩ := hS₀ hx
  exact ⟨⟨d, rootLift_mem_subgroup hC hd hx⟩, ⟨hd, hx⟩, rfl⟩

private theorem rootLift_isOddTransp (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    IsOddTransp (rootLiftClass hC S₀) :=
  (IsOddTransp.preimage (DstarH_isOddTransp hC) (rootLiftSubgroup hC S₀)).mono
    (fun _ hd => hd.1)

private theorem rootLift_imageClass_mul_self (hC : HypothesisC D)
    {x : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hx : x ∈ imageClass hC) : x * x = 1 := by
  obtain ⟨d, hd, rfl⟩ := hx
  rw [← map_mul, (DstarH_isOddTransp hC).mul_self_eq_one hd, map_one]

private theorem rootLift_not_commute_of_order (hC : HypothesisC D) {n : ℕ} (hn : 0 < n)
    {x y : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hx : x ∈ imageClass hC) (hy : y ∈ imageClass hC)
    (hxy : orderOf (x * y) = 2 ^ n + 1) : ¬ Commute x y := by
  intro hcomm
  have hx2 : x * x = 1 := rootLift_imageClass_mul_self hC hx
  have hy2 : y * y = 1 := rootLift_imageClass_mul_self hC hy
  have h2 : (x * y) ^ 2 = 1 := by
    rw [hcomm.mul_pow 2, pow_two, pow_two, hx2, hy2, mul_one]
  have hdvd : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hxy] at hdvd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have hge : 3 ≤ 2 ^ n + 1 := by
    have h2n : 2 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right Nat.two_pos (show 1 ≤ n from hn)
      simpa using this
    omega
  omega

private theorem rootLift_closure_conj_mem (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    {g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hg : g ∈ Subgroup.closure S₀)
    {x : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hx : x ∈ S₀) :
    g * x * g⁻¹ ∈ S₀ := by
  have key : ∀ g ∈ Subgroup.closure S₀, ∀ x ∈ S₀,
      g * x * g⁻¹ ∈ S₀ ∧ g⁻¹ * x * g ∈ S₀ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      intro x hx
      have hy2 : y * y = 1 := rootLift_imageClass_mul_self hC (hS₀ hy)
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      exact ⟨by simpa [hyinv] using hinv x hx y hy,
        by simpa [hyinv] using hinv x hx y hy⟩
    | one =>
      intro x hx
      exact ⟨by simpa using hx, by simpa using hx⟩
    | mul a b _ _ iha ihb =>
      intro x hx
      obtain ⟨hb1, -⟩ := ihb x hx
      obtain ⟨ha1, -⟩ := iha (b * x * b⁻¹) hb1
      obtain ⟨-, ha2⟩ := iha x hx
      refine ⟨?_, ?_⟩
      · rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group]
        exact ha1
      · rw [show (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b by group]
        exact (ihb (a⁻¹ * x * a) ha2).2
    | inv a _ iha =>
      intro x hx
      exact ⟨by simpa using (iha x hx).2, by simpa using (iha x hx).1⟩
  exact (key g hg x hx).1

private theorem rootLift_isNormalSet (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀) :
    IsNormalSet (rootLiftClass hC S₀) := by
  intro g x hx
  refine ⟨?_, ?_⟩
  · show (g : Halpha D hC.alpha) * (x : Halpha D hC.alpha) *
      (g : Halpha D hC.alpha)⁻¹ ∈ DstarH hC
    exact isNormalSet_DstarH hC (g : Halpha D hC.alpha) (x : Halpha D hC.alpha) hx.1
  · have hgk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (g : Halpha D hC.alpha) ∈ Subgroup.closure S₀ := rootLift_mk_mem hC g.2
    have hxk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (x : Halpha D hC.alpha) ∈ S₀ := hx.2
    change QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      ((g : Halpha D hC.alpha) * (x : Halpha D hC.alpha) *
        (g : Halpha D hC.alpha)⁻¹) ∈ S₀
    rw [map_mul, map_mul, map_inv]
    exact rootLift_closure_conj_mem hC hS₀ hinv hgk hxk

private theorem rootLift_pCore_normal (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
  (CFSG.pCore_normal (G := Halpha D hC.alpha) (p := 2)).subgroupOf (rootLiftSubgroup hC S₀)

private theorem rootLift_pCore_isPGroup (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    IsPGroup 2 ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)) :=
  (CFSG.pCore_isPGroup (G := Halpha D hC.alpha) (p := 2)).comap_subtype

private theorem rootLift_imageClass_isNormalSet (hC : HypothesisC D) :
    IsNormalSet (imageClass hC) := by
  intro g x hx
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨h, rfl⟩ :=
    QuotientGroup.mk'_surjective (CFSG.solvableRadical (Halpha D hC.alpha)) g
  exact ⟨h * d * h⁻¹, isNormalSet_DstarH hC h d hd,
    by rw [map_mul, map_mul, map_inv]⟩

private theorem rootLift_closure_eq_top (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    Subgroup.closure (rootLiftClass hC S₀) = ⊤ := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  have hset : rootLiftClass hC S₀ =
      ((↑) : K → H) ⁻¹' {d : H | d ∈ DstarH hC ∧ mk d ∈ S₀} := by
    ext d
    change ((d : H) ∈ DstarH hC ∧ mk (d : H) ∈ S₀) ↔
      ((d : H) ∈ DstarH hC ∧ mk (d : H) ∈ S₀)
    exact Iff.rfl
  rw [hset]
  exact Subgroup.closure_closure_coe_preimage

private theorem rootLift_exists_not_commute (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} {n : ℕ}
    (hn : 0 < n)
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {x : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hx : x ∈ S₀) :
    ∃ y ∈ S₀, ¬ Commute x y := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hord₀⟩ := hord
  obtain ⟨g, hg, hgx⟩ := hconj x₀ hx₀ x hx
  refine ⟨g * y₀ * g⁻¹, rootLift_closure_conj_mem hC hS₀ hinv hg hy₀, ?_⟩
  intro hcomm
  have hcomm' : Commute (g * x₀ * g⁻¹) (g * y₀ * g⁻¹) := by
    rw [hgx]
    exact hcomm
  have hcomm₀ : Commute x₀ y₀ := by
    have h1 := hcomm'.map (MulAut.conj g⁻¹).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    have e1 : g⁻¹ * (g * x₀ * g⁻¹) * g = x₀ := by group
    have e2 : g⁻¹ * (g * y₀ * g⁻¹) * g = y₀ := by group
    rwa [e1, e2] at h1
  exact rootLift_not_commute_of_order hC hn (hS₀ hx₀) (hS₀ hy₀) hord₀ hcomm₀

private theorem rootLift_surj_on_closure (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    {g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hg : g ∈ Subgroup.closure S₀) :
    ∃ k : ↥(rootLiftSubgroup hC S₀),
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (k : Halpha D hC.alpha) = g := by
  let R := CFSG.solvableRadical (Halpha D hC.alpha)
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  have hle : Subgroup.closure S₀ ≤ (mk.comp K.subtype).range :=
    (Subgroup.closure_le _).mpr (fun z hz => by
      obtain ⟨k, -, hk⟩ := rootLift_exists_lift hC hS₀ hz
      exact ⟨k, hk⟩)
  obtain ⟨k, hk⟩ := hle hg
  exact ⟨k, hk⟩

private theorem rootLift_commuting_lift_of_mem_class (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    {a : ↥(rootLiftSubgroup hC S₀)} (ha : a ∈ rootLiftClass hC S₀)
    {z : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hz : z ∈ S₀)
    (hza : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (a : Halpha D hC.alpha)) z) :
    ∃ f : ↥(rootLiftSubgroup hC S₀), f ∈ rootLiftClass hC S₀ ∧ Commute f a ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (f : Halpha D hC.alpha) = z := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  obtain ⟨f, hfDK, hmkf⟩ := rootLift_exists_lift hC hS₀ hz
  have hza' : Commute (mk (f : H)) (mk (a : H)) := by
    rw [hmkf]
    exact hza.symm
  have hcommH : Commute (f : H) (a : H) :=
    commute_of_commute_mk h113 hC hrad hn3 hfDK.1 ha.1 hza'
  refine ⟨f, hfDK, ?_, hmkf⟩
  apply Subtype.ext
  simpa using hcommH.eq

private theorem rootLift_closure_le_image_closure (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    {a c : ↥(rootLiftSubgroup hC S₀)} (ha : a ∈ rootLiftClass hC S₀)
    (hc : c ∈ rootLiftClass hC S₀) (hac : ¬ Commute a c) :
    Subgroup.closure S₀ ≤ (Subgroup.closure
      (insert c {f | f ∈ rootLiftClass hC S₀ ∧ Commute f a})).map
        ((QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))).comp
          (rootLiftSubgroup hC S₀).subtype) := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let DK := rootLiftClass hC S₀
  let X := Subgroup.closure (insert c {f | f ∈ DK ∧ Commute f a})
  change Subgroup.closure S₀ ≤ X.map (mk.comp K.subtype)
  have hxa : mk (a : H) ∈ imageClass hC := ⟨(a : H), ha.1, rfl⟩
  have hxc : mk (c : H) ∈ imageClass hC := ⟨(c : H), hc.1, rfl⟩
  have hnc : ¬ Commute (mk (a : H)) (mk (c : H)) := by
    intro h
    apply hac
    apply Subtype.ext
    simpa using (commute_of_commute_mk h113 hC hrad hn3 ha.1 hc.1 h).eq
  have hcl : Subgroup.closure
      (insert (mk (c : H)) {z | z ∈ S₀ ∧ Commute z (mk (a : H))}) =
        Subgroup.closure S₀ :=
    hgen (mk (a : H)) ha.2 (mk (c : H)) hc.2 hnc
  rw [← hcl]
  refine (Subgroup.closure_le _).mpr ?_
  intro z hz
  rcases hz with rfl | hzS
  · exact Subgroup.mem_map.mpr
      ⟨c, Subgroup.subset_closure (Set.mem_insert c _), rfl⟩
  · obtain ⟨f, hfDK, hcommK, hmkf⟩ :=
      rootLift_commuting_lift_of_mem_class h113 hC hrad hn3 hS₀ ha hzS.1 hzS.2.symm
    exact Subgroup.mem_map.mpr
      ⟨f, Subgroup.subset_closure (Set.mem_insert_of_mem c ⟨hfDK, hcommK⟩), hmkf⟩

private theorem rootLift_pCore_conj_commuting (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {a : ↥(rootLiftSubgroup hC S₀)} (ha : a ∈ rootLiftClass hC S₀)
    {y' : Halpha D hC.alpha} (hy'Q : y' ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    ∃ a' : ↥(rootLiftSubgroup hC S₀), a' ∈ rootLiftClass hC S₀ ∧ Commute a' a ∧
      (a' : Halpha D hC.alpha) = y' * (a : Halpha D hC.alpha) * y'⁻¹ := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let Q := CFSG.pCore 2 H
  letI : Q.Normal := CFSG.pCore_normal (G := H) (p := 2)
  let a'H : H := y' * (a : H) * y'⁻¹
  have ha'Star : a'H ∈ DstarH hC := by
    have := isNormalSet_DstarH hC y' (a : H) ha.1
    simpa [a'H] using this
  have ha'mk : mk a'H = mk (a : H) := by
    have hy'1 : mk y' = 1 :=
      (QuotientGroup.eq_one_iff y').mpr (CFSG.pCore_le_solvableRadical 2 H hy'Q)
    simp [a'H, map_mul, hy'1]
  have ha'K : a'H ∈ K :=
    rootLift_mem_subgroup hC ha'Star (by rw [ha'mk]; exact ha.2)
  let a' : K := ⟨a'H, ha'K⟩
  have ha'DK : a' ∈ rootLiftClass hC S₀ := by
    refine ⟨by simpa [a'] using ha'Star, ?_⟩
    change mk a'H ∈ S₀
    rw [ha'mk]
    exact ha.2
  have ha'Q : a'H * (a : H)⁻¹ ∈ Q := by
    have hconjQ : (a : H) * y'⁻¹ * (a : H)⁻¹ ∈ Q :=
      (CFSG.pCore_normal (G := H) (p := 2)).conj_mem y'⁻¹ (Q.inv_mem hy'Q) (a : H)
    have e : a'H * (a : H)⁻¹ = y' * ((a : H) * y'⁻¹ * (a : H)⁻¹) := by
      show y' * (a : H) * y'⁻¹ * (a : H)⁻¹ = y' * ((a : H) * y'⁻¹ * (a : H)⁻¹)
      group
    rw [e]
    exact Q.mul_mem hy'Q hconjQ
  have hcommH : Commute a'H (a : H) :=
    CFSG.Timmesfeld.Bridge.OddTransp.commute_of_mul_inv_mem
      (D := DstarH hC) (Q := Q) (DstarH_isOddTransp hC)
      (CFSG.pCore_isPGroup (G := H) (p := 2)) ha'Star ha.1 ha'Q
  have hcommK : Commute a' a := by
    apply Subtype.ext
    simpa [a'] using hcommH.eq
  exact ⟨a', ha'DK, hcommK, rfl⟩

private theorem rootLift_exists_conj_commuting (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {a d : ↥(rootLiftSubgroup hC S₀)} (ha : a ∈ rootLiftClass hC S₀)
    (hd : d ∈ rootLiftClass hC S₀) {h : ↥(rootLiftSubgroup hC S₀)}
    (hg : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (h : Halpha D hC.alpha) *
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
          (a : Halpha D hC.alpha) *
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
          (h : Halpha D hC.alpha))⁻¹ =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha)) :
    ∃ a' ∈ rootLiftClass hC S₀, Commute a' a ∧ d = h * a' * h⁻¹ := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let Q := CFSG.pCore 2 H
  letI : Q.Normal := CFSG.pCore_normal (G := H) (p := 2)
  let b : K := h * a * h⁻¹
  have hbStar : (b : H) ∈ DstarH hC := by
    have := isNormalSet_DstarH hC (h : H) (a : H) ha.1
    simpa [b] using this
  have hbmk : mk (b : H) = mk (d : H) := by
    calc mk (b : H) = mk (h : H) * mk (a : H) * (mk (h : H))⁻¹ := by
          simp [b, map_mul]
      _ = mk (d : H) := hg
  have hbc : (b : H)⁻¹ * (d : H) ∈ R := by
    have h1 : mk ((b : H)⁻¹ * (d : H)) = 1 := by
      rw [map_mul, map_inv, hbmk, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨y, hyQ, hye⟩ :=
    exists_pCore_conj_eq_of_inv_mul_mem h113 hC hrad hn3 hHns hbStar hd.1 hbc
  let y' : H := (h : H)⁻¹ * y * (h : H)
  have hy'Q : y' ∈ Q := by
    have := (CFSG.pCore_normal (G := H) (p := 2)).conj_mem y hyQ (h : H)⁻¹
    simpa [y'] using this
  obtain ⟨a', ha'DK, hcommK, ha'eq⟩ :=
    rootLift_pCore_conj_commuting hC ha hy'Q
  refine ⟨a', ha'DK, hcommK, ?_⟩
  apply Subtype.ext
  have e : ((h * a' * h⁻¹ : K) : H) = (d : H) := by
    calc ((h * a' * h⁻¹ : K) : H)
        = (h : H) * (a' : H) * (h : H)⁻¹ := by simp
      _ = (h : H) * (y' * (a : H) * y'⁻¹) * (h : H)⁻¹ := by rw [ha'eq]
      _ = y * ((h : H) * (a : H) * (h : H)⁻¹) * y⁻¹ := by
            simp only [y']
            group
      _ = y * (b : H) * y⁻¹ := rfl
      _ = (d : H) := hye
  simpa using e.symm

private theorem rootLift_class_subset_closure (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    {a c : ↥(rootLiftSubgroup hC S₀)} (ha : a ∈ rootLiftClass hC S₀)
    (hc : c ∈ rootLiftClass hC S₀) (hac : ¬ Commute a c) :
    rootLiftClass hC S₀ ⊆ Subgroup.closure
      (insert c {f | f ∈ rootLiftClass hC S₀ ∧ Commute f a}) := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let DK := rootLiftClass hC S₀
  let X := Subgroup.closure (insert c {f | f ∈ DK ∧ Commute f a})
  change DK ⊆ X
  have hXmap : Subgroup.closure S₀ ≤ X.map (mk.comp K.subtype) :=
    rootLift_closure_le_image_closure h113 hC hrad hn3 hS₀ hgen ha hc hac
  intro d hd
  have hda : mk (a : H) ∈ imageClass hC := ⟨(a : H), ha.1, rfl⟩
  have hdd : mk (d : H) ∈ imageClass hC := ⟨(d : H), hd.1, rfl⟩
  obtain ⟨g, hgmem, hgeq⟩ := hconj (mk (a : H)) ha.2 (mk (d : H)) hd.2
  obtain ⟨h, hhX, hhmk⟩ := Subgroup.mem_map.mp (hXmap hgmem)
  have hhmk' : mk (h : H) = g := hhmk
  have hg' : mk (h : H) * mk (a : H) * (mk (h : H))⁻¹ = mk (d : H) := by
    rw [hhmk']
    exact hgeq
  obtain ⟨a', ha'DK, hcomm, hd_eq⟩ :=
    rootLift_exists_conj_commuting h113 hC hrad hn3 hHns ha hd hg'
  rw [hd_eq]
  exact X.mul_mem (X.mul_mem hhX
    (Subgroup.subset_closure (Set.mem_insert_of_mem c ⟨ha'DK, hcomm⟩))) (X.inv_mem hhX)

private theorem rootLift_mk_eq_of_mul_inv_mem_pCore (hC : HypothesisC D)
    {d e : Halpha D hC.alpha}
    (hde : e * d⁻¹ ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) e =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  have h1 : mk (e * d⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (CFSG.pCore_le_solvableRadical 2 H hde)
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem exists_conj_eq_of_mem_rootLiftClass (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} {n : ℕ}
    (hn : 0 < n)
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {d e : ↥(rootLiftSubgroup hC S₀)} (hd : d ∈ rootLiftClass hC S₀)
    (he : e ∈ rootLiftClass hC S₀)
    (hde : (e : Halpha D hC.alpha) * (d : Halpha D hC.alpha)⁻¹ ∈
      CFSG.pCore 2 (Halpha D hC.alpha)) :
    ∃ x : ↥(rootLiftSubgroup hC S₀), (x : Halpha D hC.alpha) ∈ CFSG.pCore 2 (Halpha D hC.alpha) ∧
      x * d * x⁻¹ = e := by
  classical
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let Q := CFSG.pCore 2 H
  let K := rootLiftSubgroup hC S₀
  let Q' := Q.subgroupOf K
  obtain ⟨y, hyS, hnc⟩ :=
    rootLift_exists_not_commute hC hn hS₀ hinv hconj hord hd.2
  obtain ⟨w, hwDK, hmkw⟩ := rootLift_exists_lift hC hS₀ hyS
  have hmke := rootLift_mk_eq_of_mul_inv_mem_pCore hC hde
  have hmkw' : (mk.comp K.subtype) w = y := hmkw
  have hdwc : ¬ Commute d w := by
    intro h
    apply hnc
    have h' := h.map (mk.comp K.subtype)
    rwa [hmkw'] at h'
  have hcec : ¬ Commute e w := by
    intro h
    apply hnc
    have h' := h.map (mk.comp K.subtype)
    rw [hmkw', MonoidHom.comp_apply] at h'
    change Commute (mk (e : H)) y at h'
    rw [hmke] at h'
    exact h'
  have hdeQ : ((e : K) * (d : K)⁻¹ : K) ∈ Q' := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    show (e : H) * (d : H)⁻¹ ∈ Q
    exact hde
  haveI : Q'.Normal := rootLift_pCore_normal hC S₀
  obtain ⟨x, hx, hxe⟩ :=
    CFSG.Timmesfeld.Bridge.OddTransp.exists_conj_of_mul_inv_mem
      (G := K) (D := rootLiftClass hC S₀) (Q := Q')
      (rootLift_isOddTransp hC S₀) (rootLift_isNormalSet hC hS₀ hinv)
      (rootLift_pCore_isPGroup hC S₀)
      hd hwDK hdwc he hdeQ hcec
  exact ⟨x, Subgroup.mem_subgroupOf.mp (Subgroup.commutator_le_left Q' _ hx), hxe⟩

theorem closure_insert_rootLiftClass_eq_top (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    {a c : ↥(rootLiftSubgroup hC S₀)} (ha : a ∈ rootLiftClass hC S₀)
    (hc : c ∈ rootLiftClass hC S₀) (hac : ¬ Commute a c) :
    Subgroup.closure (insert c {f | f ∈ rootLiftClass hC S₀ ∧ Commute f a}) = ⊤ := by
  let DK := rootLiftClass hC S₀
  have hsub : DK ⊆ Subgroup.closure (insert c {f | f ∈ DK ∧ Commute f a}) :=
    rootLift_class_subset_closure h113 hC hrad hn3 hHns hS₀ hgen hconj ha hc hac
  rw [eq_top_iff, ← rootLift_closure_eq_top hC S₀]
  exact (Subgroup.closure_le _).mpr hsub

private theorem rootLift_isConj_of_mem_class (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} {n : ℕ}
    (hn : 0 < n)
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {d₀ : ↥(rootLiftSubgroup hC S₀)} (hd₀ : d₀ ∈ rootLiftClass hC S₀)
    {g : ↥(rootLiftSubgroup hC S₀)} (hg : g ∈ rootLiftClass hC S₀) :
    IsConj d₀ g := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let Q := CFSG.pCore 2 H
  obtain ⟨h, hh, hhEq⟩ := hconj (mk (d₀ : H)) hd₀.2 (mk (g : H)) hg.2
  obtain ⟨k, hk⟩ := rootLift_surj_on_closure hC hS₀ hh
  let b : K := k * d₀ * k⁻¹
  have hbStar : (b : H) ∈ DstarH hC := by
    have := isNormalSet_DstarH hC (k : H) (d₀ : H) hd₀.1
    simpa [b] using this
  have hbmk : mk (b : H) = mk (g : H) := by
    calc mk (b : H) = mk (k : H) * mk (d₀ : H) * (mk (k : H))⁻¹ := by
          simp [b, map_mul]
      _ = h * mk (d₀ : H) * h⁻¹ := by rw [hk]
      _ = mk (g : H) := hhEq
  have hb : b ∈ rootLiftClass hC S₀ := by
    refine ⟨hbStar, ?_⟩
    change mk (b : H) ∈ S₀
    rw [hbmk]
    exact hg.2
  have hbc : (b : H)⁻¹ * (g : H) ∈ R := by
    have h1 : mk ((b : H)⁻¹ * (g : H)) = 1 := by
      rw [map_mul, map_inv, hbmk, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hQ : (g : H) * (b : H)⁻¹ ∈ Q :=
    mul_inv_mem_pCore_of_inv_mul_mem h113 hC hrad hn3 hbStar hg.1 hbc
  obtain ⟨x', -, hx'e⟩ :=
    exists_conj_eq_of_mem_rootLiftClass hC hn hS₀ hinv hconj hord hb hg hQ
  refine isConj_iff.mpr ⟨x' * k, ?_⟩
  calc (x' * k) * d₀ * (x' * k)⁻¹ = x' * b * x'⁻¹ := by
        rw [show b = k * d₀ * k⁻¹ from rfl]
        group
    _ = g := hx'e

theorem setup_rootLiftClass (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} {n : ℕ}
    (hn : 0 < n)
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1) :
    Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀) := by
  classical
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  refine ⟨?_, rootLift_isOddTransp hC S₀, rootLift_closure_eq_top hC S₀⟩
  have hord' := hord
  obtain ⟨x, hx, _⟩ := hord
  obtain ⟨d₀, hd₀DK, -⟩ := rootLift_exists_lift hC hS₀ hx
  refine ⟨d₀, ?_⟩
  ext g
  constructor
  · intro hgDK
    exact rootLift_isConj_of_mem_class h113 hC hrad hn3 hn hS₀ hinv hconj hord' hd₀DK hgDK
  · intro hg
    obtain ⟨k, hk⟩ := isConj_iff.mp hg
    have hmem : k * d₀ * k⁻¹ ∈ rootLiftClass hC S₀ := by
      refine ⟨?_, ?_⟩
      · have := isNormalSet_DstarH hC (k : H) (d₀ : H) hd₀DK.1
        simpa using this
      · change mk ((k : H) * (d₀ : H) * (k : H)⁻¹) ∈ S₀
        rw [map_mul, map_mul, map_inv]
        exact rootLift_closure_conj_mem hC hS₀ hinv (rootLift_mk_mem hC k.2) hd₀DK.2
    rw [← hk]
    exact hmem

private theorem rootLift_image_conj_eq (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} {n : ℕ}
    (hn : 0 < n)
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {d : ↥(rootLiftSubgroup hC S₀)} (hd : d ∈ rootLiftClass hC S₀) :
    ((↑) : ↥(rootLiftSubgroup hC S₀) → Halpha D hC.alpha) ''
        ((fun y => y * d * y⁻¹) ''
          ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf
            (rootLiftSubgroup hC S₀) : Set ↥(rootLiftSubgroup hC S₀))) =
      (fun y : Halpha D hC.alpha => y * (d : Halpha D hC.alpha) * y⁻¹) ''
        (CFSG.pCore 2 (Halpha D hC.alpha) : Set (Halpha D hC.alpha)) := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let Q := CFSG.pCore 2 H
  let Q' := Q.subgroupOf K
  ext e
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(z : H), Subgroup.mem_subgroupOf.mp hz, by simp [Subgroup.coe_mul]⟩
  · rintro ⟨y, hyQ, rfl⟩
    have hy1 : mk y = 1 :=
      (QuotientGroup.eq_one_iff y).mpr (CFSG.pCore_le_solvableRadical 2 H hyQ)
    have heStar : y * (d : H) * y⁻¹ ∈ DstarH hC := isNormalSet_DstarH hC y (d : H) hd.1
    have hmke : mk (y * (d : H) * y⁻¹) = mk (d : H) := by
      rw [map_mul, map_mul, map_inv, hy1, one_mul, inv_one, mul_one]
    have heK : y * (d : H) * y⁻¹ ∈ K :=
      rootLift_mem_subgroup hC heStar (by rw [hmke]; exact hd.2)
    let eK : K := ⟨y * (d : H) * y⁻¹, heK⟩
    have heDK : eK ∈ rootLiftClass hC S₀ := by
      refine ⟨by simpa [eK] using heStar, ?_⟩
      change mk (y * (d : H) * y⁻¹) ∈ S₀
      rw [hmke]
      exact hd.2
    have hde : (eK : H) * (d : H)⁻¹ ∈ Q := by
      have hconjQ : (d : H) * y⁻¹ * (d : H)⁻¹ ∈ Q :=
        (CFSG.pCore_normal (G := H) (p := 2)).conj_mem y⁻¹ (Q.inv_mem hyQ) (d : H)
      have e : (eK : H) * (d : H)⁻¹ = y * ((d : H) * y⁻¹ * (d : H)⁻¹) := by
        show (y * (d : H) * y⁻¹) * (d : H)⁻¹ = y * ((d : H) * y⁻¹ * (d : H)⁻¹)
        group
      rw [e]
      exact Q.mul_mem hyQ hconjQ
    obtain ⟨x, hxQ, hxe⟩ :=
      exists_conj_eq_of_mem_rootLiftClass hC hn hS₀ hinv hconj hord hd heDK hde
    refine ⟨x * d * x⁻¹, ⟨x, Subgroup.mem_subgroupOf.mpr hxQ, rfl⟩, ?_⟩
    simpa [eK] using congrArg ((↑) : K → H) hxe

theorem ncard_conj_rootLiftClass_eq (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} {n : ℕ}
    (hn : 0 < n)
    (hS₀ : S₀ ⊆ imageClass hC)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {d : ↥(rootLiftSubgroup hC S₀)} (hd : d ∈ rootLiftClass hC S₀)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ((fun y => y * d * y⁻¹) ''
        ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀) :
          Set ↥(rootLiftSubgroup hC S₀))).ncard =
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
  classical
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let Q := CFSG.pCore 2 H
  let Q' := Q.subgroupOf K
  let imgK : Set K := (fun y : K => y * d * y⁻¹) '' (Q' : Set K)
  let imgH : Set H := (fun y : H => y * (d : H) * y⁻¹) '' (Q : Set H)
  have hset : ((↑) : K → H) '' imgK = imgH :=
    rootLift_image_conj_eq hC hn hS₀ hinv hconj hord hd
  have hA : imgK.ncard = imgH.ncard := by
    have h1 : (((↑) : K → H) '' imgK).ncard = imgK.ncard :=
      Set.ncard_image_of_injective imgK K.subtype_injective
    rw [hset] at h1
    exact h1.symm
  have hB : imgH.ncard = ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
    obtain ⟨δ, hδ, hdδ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hd.1)
    have h1 := ncard_orbit_Malpha_eq_ncard_conj h89 h113 hC hrad hW hn3 hHns hδ hdδ
    have h2 := ncard_orbit_Malpha_eq hC hβ hδ
    exact h1.symm.trans h2
  exact hA.trans hB

theorem orderOf_mul_dvd_ncard_orbit_sq_sub_one_of_class (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (hS₀ : S₀ ⊆ imageClass hC) {n : ℕ} (hn : 0 < n)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {x y : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hx : x ∈ S₀)
    (hy : y ∈ S₀) (hxy : ¬ Commute x y) :
    orderOf (x * y) ∣ ((fun g => cimg g β) '' (Malpha D hC.alpha : Set G)).ncard ^ 2 - 1 := by
  classical
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let DK := rootLiftClass hC S₀
  let Q := CFSG.pCore 2 H
  let Q' := Q.subgroupOf K
  let m : ℕ := ((fun g => cimg g β) '' (Malpha D hC.alpha : Set G)).ncard
  haveI : Q'.Normal := rootLift_pCore_normal hC S₀
  have hS : Setup K DK := setup_rootLiftClass h113 hC hrad hn3 hn hS₀ hinv hconj hord
  have hm : ∀ d ∈ DK, ((fun y : K => y * d * y⁻¹) '' (Q' : Set K)).ncard = m := by
    intro d hd
    have h := ncard_conj_rootLiftClass_eq h89 h113 hC hrad hW hn3 hHns hn hS₀ hinv
      hconj hord hd (β := β) hβ
    simpa [m, Q'] using h
  have hgenK : ∀ a ∈ DK, ∀ c ∈ DK, ¬ Commute a c →
      Subgroup.closure (insert a {f | f ∈ DK ∧ Commute f c}) = ⊤ := by
    intro a ha c hc hac
    exact closure_insert_rootLiftClass_eq_top h113 hC hrad hn3 hHns hS₀ hgen hconj hc ha
      (fun h => hac h.symm)
  obtain ⟨a, haDK, hma⟩ := rootLift_exists_lift hC hS₀ hx
  obtain ⟨b, hbDK, hmb⟩ := rootLift_exists_lift hC hS₀ hy
  have hab : ¬ Commute a b := by
    intro hcomm
    apply hxy
    have h' := hcomm.map (mk.comp K.subtype)
    rwa [show (mk.comp K.subtype) a = x from hma,
      show (mk.comp K.subtype) b = y from hmb] at h'
  have hdvd := orderOf_mul_dvd_sq_sub_one (X := K) (D := DK) hS
    (Q := Q') (rootLift_pCore_isPGroup hC S₀) (m := m) hm hgenK haDK hbDK hab
  have hmkab : (mk.comp K.subtype) (a * b) = x * y := by
    show mk ((a : H) * (b : H)) = x * y
    rw [map_mul, hma, hmb]
  have hmapord : orderOf (x * y) ∣ orderOf (a * b) := by
    have h := orderOf_map_dvd (mk.comp K.subtype) (a * b)
    rwa [hmkab] at h
  exact hmapord.trans hdvd

theorem exists_ncard_orbit_Malpha_eq_two_pow_mul_of_class (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (hS₀ : S₀ ⊆ imageClass hC) {n : ℕ} (hn : 0 < n)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ j : ℕ, 0 < j ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (n * j) := by
  classical
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  let K := rootLiftSubgroup hC S₀
  let DK := rootLiftClass hC S₀
  let Q := CFSG.pCore 2 H
  let Q' := Q.subgroupOf K
  let m : ℕ := ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard
  have hm1 : 1 < m := by
    simpa [m] using one_lt_ncard_orbit_Malpha h89 h113 hC hrad hW hn3 hMZ hHns hβ
  obtain ⟨s, hs⟩ : ∃ s : ℕ, m = 2 ^ s := by
    obtain ⟨s, h⟩ := exists_ncard_orbit_Malpha_eq_two_pow h89 h113 hC hrad hW hn3 hHns hβ
    exact ⟨s, by simpa [m] using h⟩
  have hs_pos : 0 < s := by
    by_contra h
    have h0 : s = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_lt h)
    rw [hs, h0, pow_zero] at hm1
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := hord
  have hdiv : 2 ^ n + 1 ∣ m ^ 2 - 1 := by
    have h := orderOf_mul_dvd_ncard_orbit_sq_sub_one_of_class h89 h113 hC hrad hW hn3 hHns S₀
      hS₀ hn hinv hgen hconj ⟨x, hx, y, hy, hxy⟩ hβ hx hy
      (rootLift_not_commute_of_order hC hn (hS₀ hx) (hS₀ hy) hxy)
    rw [hxy] at h
    exact h
  have hdiv2 : 2 ^ n + 1 ∣ 2 ^ (2 * s) - 1 := by
    rw [hs] at hdiv
    rwa [show (2 ^ s) ^ 2 = 2 ^ (2 * s) by rw [← pow_mul, Nat.mul_comm s 2]] at hdiv
  obtain ⟨j, rfl⟩ : n ∣ s := dvd_of_two_pow_add_one_dvd hn hdiv2
  exact ⟨j, Nat.pos_of_ne_zero (by rintro rfl; simp at hs_pos), hs⟩

private theorem rootLift_old_closure_eq (hC : HypothesisC D)
    {K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} {n : ℕ}
    (hn : 0 < n)
    (hgen : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = K0)
    (hord : ∃ x ∈ imageClass hC, x ∈ K0 ∧ ∃ y ∈ imageClass hC, y ∈ K0 ∧
      orderOf (x * y) = 2 ^ n + 1) :
    Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0} = K0 := by
  obtain ⟨x₀, hx₀, hx₀K, y₀, hy₀, hy₀K, hord₀⟩ := hord
  have hnc₀ : ¬ Commute x₀ y₀ := rootLift_not_commute_of_order hC hn hx₀ hy₀ hord₀
  have hcl₀ := hgen x₀ hx₀ hx₀K y₀ hy₀ hy₀K hnc₀
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro z hz
    exact hz.2
  · have hclS : Subgroup.closure (insert y₀ (Vmem (imageClass hC) x₀)) ≤
        Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0} := by
      apply Subgroup.closure_mono
      intro z hz
      rcases hz with rfl | hz
      · exact ⟨hy₀, hy₀K⟩
      · have hzK : z ∈ K0 :=
          hcl₀ ▸ Subgroup.subset_closure (Set.mem_insert_of_mem y₀ hz)
        exact ⟨(mem_Vmem.mp hz).1, hzK⟩
    calc K0 = Subgroup.closure (insert y₀ (Vmem (imageClass hC) x₀)) := hcl₀.symm
      _ ≤ Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0} := hclS

private theorem rootLift_old_hinv (hC : HypothesisC D)
    {K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} :
    ∀ x ∈ {x | x ∈ imageClass hC ∧ x ∈ K0},
      ∀ y ∈ {x | x ∈ imageClass hC ∧ x ∈ K0},
        y * x * y⁻¹ ∈ {x | x ∈ imageClass hC ∧ x ∈ K0} := by
  intro x hx y hy
  exact ⟨rootLift_imageClass_isNormalSet hC y x hx.1,
    K0.mul_mem (K0.mul_mem hy.2 hx.2) (K0.inv_mem hy.2)⟩

private theorem rootLift_old_hgen (hC : HypothesisC D)
    {K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hgen : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = K0)
    (hclosure : Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0} = K0) :
    ∀ x ∈ {x | x ∈ imageClass hC ∧ x ∈ K0},
      ∀ y ∈ {x | x ∈ imageClass hC ∧ x ∈ K0}, ¬ Commute x y →
        Subgroup.closure (insert y
          {z | z ∈ {x | x ∈ imageClass hC ∧ x ∈ K0} ∧ Commute z x}) =
          Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0} := by
  intro x hx y hy hxy
  have hcl := hgen x hx.1 hx.2 y hy.1 hy.2 hxy
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact Subgroup.subset_closure hy
    · exact Subgroup.subset_closure hz.1
  · have hle : Subgroup.closure (insert y (Vmem (imageClass hC) x)) ≤
        Subgroup.closure (insert y
          {z | z ∈ {x | x ∈ imageClass hC ∧ x ∈ K0} ∧ Commute z x}) := by
      apply Subgroup.closure_mono
      intro z hz
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · have hzK : z ∈ K0 :=
          hcl ▸ Subgroup.subset_closure (Set.mem_insert_of_mem y hz)
        have hzx : Commute z x := by
          have hxself : x ∈ perpMem (imageClass hC) x := mem_perpMem_self hx.1
          rw [← (mem_Vmem.mp hz).2] at hxself
          exact hxself.2.symm
        exact Or.inr ⟨⟨(mem_Vmem.mp hz).1, hzK⟩, hzx⟩
    calc Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0} = K0 := hclosure
      _ = Subgroup.closure (insert y (Vmem (imageClass hC) x)) := hcl.symm
      _ ≤ Subgroup.closure (insert y
          {z | z ∈ {x | x ∈ imageClass hC ∧ x ∈ K0} ∧ Commute z x}) := hle

private theorem rootLift_old_hconj {hC : HypothesisC D}
    {K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hconj : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 →
      ∃ g ∈ K0, g * x * g⁻¹ = y)
    (hclosure : Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0} = K0) :
    ∀ x ∈ {x | x ∈ imageClass hC ∧ x ∈ K0},
      ∀ y ∈ {x | x ∈ imageClass hC ∧ x ∈ K0},
        ∃ g ∈ Subgroup.closure {x | x ∈ imageClass hC ∧ x ∈ K0}, g * x * g⁻¹ = y := by
  intro x hx y hy
  obtain ⟨g, hg, hge⟩ := hconj x hx.1 hx.2 y hy.1 hy.2
  exact ⟨g, by rw [hclosure]; exact hg, hge⟩

theorem exists_ncard_orbit_Malpha_eq_two_pow_mul (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) {n : ℕ}
    (hn : 0 < n)
    (hgen : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = K0)
    (hconj : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 →
      ∃ g ∈ K0, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ imageClass hC, x ∈ K0 ∧ ∃ y ∈ imageClass hC, y ∈ K0 ∧
      orderOf (x * y) = 2 ^ n + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ j : ℕ, 0 < j ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ (n * j) := by
  classical
  let S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
    {x | x ∈ imageClass hC ∧ x ∈ K0}
  have hclosure : Subgroup.closure S₀ = K0 :=
    rootLift_old_closure_eq hC hn hgen hord
  obtain ⟨x₀, hx₀, hx₀K, y₀, hy₀, hy₀K, hxy₀⟩ := hord
  refine exists_ncard_orbit_Malpha_eq_two_pow_mul_of_class h89 h113 hC hrad hW hn3 hMZ hHns
    S₀ (fun _ hx => hx.1) hn (rootLift_old_hinv hC) ?_
    (rootLift_old_hconj hconj hclosure) ?_ hβ
  · exact rootLift_old_hgen hC hgen hclosure
  · exact ⟨x₀, ⟨hx₀, hx₀K⟩, y₀, ⟨hy₀, hy₀K⟩, hxy₀⟩

theorem two_pow_le_ncard_orbit_Malpha (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (K0 : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) {n : ℕ}
    (hn : 0 < n)
    (hgen : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem (imageClass hC) x)) = K0)
    (hconj : ∀ x ∈ imageClass hC, x ∈ K0 → ∀ y ∈ imageClass hC, y ∈ K0 →
      ∃ g ∈ K0, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ imageClass hC, x ∈ K0 ∧ ∃ y ∈ imageClass hC, y ∈ K0 ∧
      orderOf (x * y) = 2 ^ n + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    2 ^ n ≤ ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard := by
  obtain ⟨j, hj, h⟩ := exists_ncard_orbit_Malpha_eq_two_pow_mul h89 h113 hC hrad hW hn3 hMZ hHns
    K0 hn hgen hconj hord hβ
  rw [h]
  exact Nat.pow_le_pow_right Nat.two_pos (Nat.le_mul_of_pos_right n hj)

end CFSG.OddTranspositions.PartFour
