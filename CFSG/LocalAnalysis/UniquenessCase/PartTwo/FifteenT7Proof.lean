module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7A5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Aut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_T7_isElemAbelian_biSup {A : Type*} [Group A] (p : ℕ) (S : Set (Subgroup A))
    (hS : ∀ Y ∈ S, IsElemAbelian p Y) (hc : ∀ Y ∈ S, ∀ Z ∈ S, Y ≠ Z → ⁅Y, Z⁆ = ⊥) :
    IsElemAbelian p (⨆ Y ∈ S, Y) := by
  have hcomm : ∀ Y ∈ S, ∀ Z ∈ S, ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y := by
    intro Y hY Z hZ y hy z hz
    by_cases hYZ : Y = Z
    · subst hYZ
      haveI := (hS Y hY).1
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Y) ⟨z, hz⟩)
    · have h1 : ⁅y, z⁆ ∈ ⁅Y, Z⁆ := Subgroup.commutator_mem_commutator hy hz
      rw [hc Y hY Z hZ hYZ, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have h1 : ∀ Y ∈ S, ∀ y ∈ Y, ∀ x ∈ ⨆ Z ∈ S, Z, y * x = x * y := by
    intro Y hY y hy x hx
    have : (⨆ Z ∈ S, Z) ≤ Subgroup.centralizer {y} :=
      iSup₂_le fun Z hZ z hz => Subgroup.mem_centralizer_iff.2 fun w hw => by
        rw [Set.mem_singleton_iff.1 hw]
        exact hcomm Y hY Z hZ y hy z hz
    exact (Subgroup.mem_centralizer_iff.1 (this hx)) y rfl
  have h2 : ∀ x ∈ ⨆ Z ∈ S, Z, ∀ x' ∈ ⨆ Z ∈ S, Z, x * x' = x' * x := by
    intro x hx x' hx'
    have : (⨆ Z ∈ S, Z) ≤ Subgroup.centralizer {x'} :=
      iSup₂_le fun Y hY y hy => Subgroup.mem_centralizer_iff.2 fun w hw => by
        rw [Set.mem_singleton_iff.1 hw]
        exact (h1 Y hY y hy x' hx').symm
    exact ((Subgroup.mem_centralizer_iff.1 (this hx)) x' rfl).symm
  refine ⟨⟨⟨fun a b => Subtype.ext (h2 a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
  have hx' : x ∈ ⨆ Y : ↥S, (Y : Subgroup A) := by
    rwa [iSup_subtype'' S (fun Y => Y)]
  refine Subgroup.iSup_induction' (fun Y : ↥S => (Y : Subgroup A)) (C := fun x _ => x ^ p = 1)
    ?_ ?_ ?_ hx'
  · intro Y y hy
    exact (hS Y Y.2).2 y hy
  · exact one_pow p
  · intro x y hx hy hxp hyp
    rw [iSup_subtype'' S (fun Y => Y)] at hx hy
    have hcm : Commute x y := h2 x hx y hy
    rw [hcm.mul_pow, hxp, hyp, one_mul]

theorem s15_T7_isElemAbelian_of_cyclicOrd {A : Type} [Group A] {K : Subgroup A} {p : ℕ}
    (h : IsCyclicOrd ↥K p) : IsElemAbelian p K := by
  obtain ⟨hc, hcard⟩ := h
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact congrArg Subtype.val (mul_comm' a b)
  · have := pow_card_eq_one' (G := ↥K) (x := ⟨x, hx⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this

theorem s15_T7_isElemAbelian_of_directProd {A : Type*} [Group A] {X K N : Subgroup A} {p : ℕ}
    (hK : IsElemAbelian p K) (h : IsDirectProdOfConj X K N) : IsElemAbelian p X := by
  have hS : ∀ Y ∈ conjSet K N, IsElemAbelian p Y := by
    rintro Y ⟨n, -, rfl⟩
    exact hK.map _
  rw [← h.2.1]
  exact s15_T7_isElemAbelian_biSup p _ hS h.2.2.1

theorem s15_T7_mem_conjSet_self {A : Type*} [Group A] (K N : Subgroup A) : K ∈ conjSet K N :=
  ⟨1, N.one_mem, by ext x; simp [Subgroup.mem_map]⟩

theorem s15_T7_eq_of_ncard_one {A : Type*} [Group A] {X K N : Subgroup A}
    (h : IsDirectProdOfConj X K N) (h1 : (conjSet K N).ncard = 1) : X = K := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
  have hK := s15_T7_mem_conjSet_self K N
  rw [ha, Set.mem_singleton_iff] at hK
  rw [← h.2.1, ha, hK]
  simp

theorem s15_T7_card_eight {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    (h : BinaryNaturalSL H U ⊥ 3 1) : Nat.card ↥U = 8 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.nat (StatedSL 3 K)).ker.subgroupOf (FFModel.nat (StatedSL 3 K)).sec)
  have h2 : Nat.card ↥((FFModel.nat (StatedSL 3 K)).ker.subgroupOf
      (FFModel.nat (StatedSL 3 K)).sec) = 1 := by
    show Nat.card ↥((⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤) = 1
    rw [Subgroup.bot_subgroupOf]
    simp
  have h3 : Nat.card ↥(FFModel.nat (StatedSL 3 K)).sec = 8 := by
    show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) = 8
    have : Nat.card (Multiplicative (Fin 3 → K)) = Nat.card (Fin 3 → K) :=
      Nat.card_congr Multiplicative.toAdd
    rw [Subgroup.card_top, this, Nat.card_fun, hK]
    simp
  rw [h2, mul_one, h3] at h1
  exact h1.symm

theorem s15_T7_rk_binaryNatural {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U : Subgroup V} (h : BinaryNaturalSL H U ⊥ 3 1) : rk ↥U = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [s15_T7_card_eight h, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]

theorem s15_T7_commSub_autSub_top {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {V : Subgroup W} (hLs : L ≤ stabSub V) (hc : commSub V L = V) :
    commSub (⊤ : Subgroup ↥V) (autSub L V) = ⊤ := by
  have h1 := map_commSub_autSub hLs (⊤ : Subgroup ↥V)
  have htop : (⊤ : Subgroup ↥V).map V.subtype = V := by
    rw [← MonoidHom.range_eq_map]
    exact V.range_subtype
  rw [htop, hc] at h1
  apply Subgroup.map_injective V.subtype_injective
  rw [h1, htop]

theorem s15_T7_not_group_of_elemAbelian3 (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL3 : IsElemAbelian 3 (lStar D.M V₀ V h.isElemAbelian L))
    {Q : Subgroup (MulAut (vStar D.M V₀ V h.isElemAbelian L))}
    (hQ : s15T7Group D V₀ V L h.isElemAbelian Q) : False := by
  have hV := h.isElemAbelian
  obtain ⟨-, -, hQN, hrk, A, hAW, hAm, hfix⟩ := hQ
  have hsq : ∀ w : vStar D.M V₀ V hV L, w ^ 2 = 1 := s15_LP_vtil_sq_eq_one _ V hV
  have hsqW : ∀ w : ↥(wStar D.M V₀ V hV L), w ^ 2 = 1 := fun w => Subtype.ext (hsq w.1)
  have hodd : Odd (Nat.card ↥(lStar D.M V₀ V hV L)) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hL3.isPGroup.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have hcomm : commSub (wStar D.M V₀ V hV L) (lStar D.M V₀ V hV L) = wStar D.M V₀ V hV L := by
    rw [s15_T7_wStar_eq_commSub D h]
    exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.commSub_commSub_eq hsq hodd
  have hE := s15_T7_commSub_autSub_top (s15_T7_lStar_le_stabSub D h) hcomm
  have hcard := s15_T7_Z3_card_le_two hsqW (s15_T7_isElemAbelian_autSub 3 _ hL3) hE
    (s15_T7_autSub_le_normalizer hQN)
    (Hy := A.subgroupOf (wStar D.M V₀ V hV L))
    (by rw [s15_T7_mQuot_top_subgroupOf]; exact hAm) (fun q hq u hu => by
      obtain ⟨g, hgQ, rfl⟩ := mem_autSub.1 hq
      apply Subtype.ext
      rw [resHom_apply]
      exact hfix _ hgQ _ (Subgroup.mem_subgroupOf.1 hu))
  have := s15_T7_rk_le_one_of_card_le_two hcard
  omega

theorem s15_T7_case3 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {Q : Subgroup (MulAut (vStar D.M V₀ V h.isElemAbelian L))}
    (hQ : s15T7Group D V₀ V L h.isElemAbelian Q)
    (h3 : Case153_3 D V₀ V h.isElemAbelian L) : False := by
  obtain ⟨⟨K₀, -, hcyc, hdp, -⟩, -⟩ := h3
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hL3 : IsElemAbelian 3 (lBar V₀ V h.isElemAbelian L) :=
    s15_T7_isElemAbelian_of_directProd (s15_T7_isElemAbelian_of_cyclicOrd hcyc) hdp
  exact s15_T7_not_group_of_elemAbelian3 D h
    (s15_T7_isElemAbelian_barSub 3 h.isElemAbelian (s15_Infra_le_v1Sub _ V₀ V _ L) hMs₀
      (s15_T7_le_stabTil_v1Sub h) h.le hL3) hQ

theorem s15_T7_case2_five (D : Data G) {V₀ V L K₀ : Subgroup G} (h : Hyp151 D V₀ V L)
    (hLK : lStar D.M V₀ V h.isElemAbelian L =
      barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀)
    (hnat : AlternatingNatural (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀)) ⊥ 5)
    {Q : Subgroup (MulAut (vStar D.M V₀ V h.isElemAbelian L))}
    (hQ : s15T7Group D V₀ V L h.isElemAbelian Q) : False := by
  obtain ⟨-, hQs, hQN, hrk, A, hAW, hAm, hfix⟩ := hQ
  have hW : wStar D.M V₀ V h.isElemAbelian L =
      commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀) := by
    rw [s15_T7_wStar_eq_commSub D h]
    exact congrArg (commSub ⊤) hLK
  rw [hW] at hQs hAW hAm hrk
  have hQN' : Q ≤ normalizer ((barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀ :
      Subgroup _) : Set _) := hLK ▸ hQN
  have h1 := hrk.trans (s15_T7_rk_le_one_of_card_le_two
    (s15_T7_alt5_card_le_two hnat hQN' hAm hfix))
  omega

theorem s15_T7_case2 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.isElemAbelian L)
    {Q : Subgroup (MulAut (vStar D.M V₀ V h.isElemAbelian L))}
    (hQ : s15T7Group D V₀ V L h.isElemAbelian Q)
    (h2 : Case153_2 D V₀ V h.isElemAbelian L) :
    gamma15 D.M V₀ V h.isElemAbelian L = 3 ∧ s15 D.M V₀ V h.isElemAbelian L = 2 := by
  obtain ⟨K₀, p, hK₀L, hp, hdp, -, -, hrs, -⟩ := h2
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hr : 0 < (conjSet (barSub V₀ V h.isElemAbelian K₀)
      (Mbar D.M V₀ V h.isElemAbelian ⊓
        normalizer ((lBar V₀ V h.isElemAbelian L : Subgroup _) : Set _))).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨_, s15_T7_mem_conjSet_self _ _⟩
  have hr1 : (conjSet (barSub V₀ V h.isElemAbelian K₀)
      (Mbar D.M V₀ V h.isElemAbelian ⊓
        normalizer ((lBar V₀ V h.isElemAbelian L : Subgroup _) : Set _))).ncard = 1 := by
    nlinarith
  have hs2 : s15 D.M V₀ V h.isElemAbelian L = 2 := by
    rw [hr1] at hrs
    omega
  refine ⟨?_, hs2⟩
  have hLK : lStar D.M V₀ V h.isElemAbelian L =
      barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀ :=
    s15_T7_barSub_eq_of_barSub_eq h.isElemAbelian (s15_Infra_le_v1Sub _ V₀ V _ L) hMs₀
      (s15_T7_le_stabTil_v1Sub h) h.le (hK₀L.trans h.le) (s15_T7_eq_of_ncard_one hdp hr1)
  rcases hp with ⟨-, -, hnat⟩ | ⟨-, -, hnat⟩
  · exact (s15_T7_case2_five D h hLK hnat hQ).elim
  · have hW : wStar D.M V₀ V h.isElemAbelian L =
        commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀) := by
      rw [s15_T7_wStar_eq_commSub D h]
      exact congrArg (commSub ⊤) hLK
    unfold gamma15
    rw [hW]
    exact s15_T7_rk_binaryNatural hnat

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
