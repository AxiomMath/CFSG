module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixPerm
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

namespace Six

theorem uvec_moved {σ : Perm (Fin 6)} {x y : Fin 6} (hxy : x ≠ y) (h1 : σ x ≠ x)
    (h2 : σ x ≠ y) : barAct σ (uvec x y) ≠ uvec x y := by
  rw [barAct_uvec]
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := exists_ne_four (by norm_num : 5 ≤ 6) (σ x) (σ y) x y
  have hσxy : σ x ≠ σ y := fun h => hxy (σ.injective h)
  unfold uvec
  refine bar_mk_ne_of_coords (i := σ x) (j := j) ?_ ?_
  · simp only [Pi.add_apply, Pi.single_apply, if_true, hσxy, h1, h2, if_false]
    decide
  · simp only [Pi.add_apply, Pi.single_apply, hj1, hj2, hj3, hj4, if_false]

theorem FourGroup_barAct_uvec_ne {J : Finset (Fin 6)} {N : Subgroup (Perm (Fin 6))}
    (h : FourGroup J N) (hJ : J.card = 4) {σ σ' : Perm (Fin 6)} (hσ : σ ∈ N) (hσ1 : σ ≠ 1)
    (hσ' : σ' ∈ N) (hσ'1 : σ' ≠ 1) (hne : σ ≠ σ') {a : Fin 6} (ha : a ∈ J) :
    barAct σ (uvec a (σ' a)) ≠ uvec a (σ' a) :=
  uvec_moved (fun h' => h.free hJ hσ' hσ'1 a ha h'.symm) (h.free hJ hσ hσ1 a ha)
    (h.apart hJ hσ hσ' hne ha)

theorem card_mul_succ_le {F : Subgroup (Perm (Fin 6))}
    {A Z : Subgroup (Multiplicative (permBar 6))}
    (hA : ∀ u : altHeart 6, Multiplicative.ofAdd (heartToBar u) ∈ A) (hZA : Z ≤ A)
    (hZ : ∀ z ∈ Z, ∀ σ ∈ F, barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z)
    (T : Finset (Fin 6)) (p : Fin 6) (hp : p ∉ T)
    (hP : ∀ x ∈ T, ∃ σ ∈ F, σ x ≠ x ∧ σ x ≠ p)
    (hQ : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∃ σ ∈ F, σ x ≠ x ∧ σ x ≠ y) :
    Nat.card Z * (T.card + 1) ≤ Nat.card A := by
  classical
  let a : Option ↥T → Multiplicative (permBar 6) := fun i =>
    match i with
    | none => 1
    | some x => Multiplicative.ofAdd (uvec (x : Fin 6) p)
  have haA : ∀ i, a i ∈ A := by
    intro i
    cases i with
    | none => exact A.one_mem
    | some x =>
      have := hA (pairEW (x : Fin 6) p : altHeart 6)
      rwa [heartToBar_pairEW_eq_uvec] at this
  have hcard : Nat.card (Option ↥T) = T.card + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe]
  have key := card_mul_le_of_cosets hZA a haA (fun i j hij hmem => by
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some y =>
        obtain ⟨σ, hσ, h1, h2⟩ := hP y y.2
        have hy : (y : Fin 6) ≠ p := fun h => hp (h ▸ y.2)
        have e : Multiplicative.toAdd ((a none)⁻¹ * a (some y)) = uvec (y : Fin 6) p := by
          simp [a]
        have := hZ _ hmem σ hσ
        rw [e] at this
        exact uvec_moved hy h1 h2 this
    | some x =>
      cases j with
      | none =>
        obtain ⟨σ, hσ, h1, h2⟩ := hP x x.2
        have hx : (x : Fin 6) ≠ p := fun h => hp (h ▸ x.2)
        have e : Multiplicative.toAdd ((a (some x))⁻¹ * a none) = -(uvec (x : Fin 6) p) := by
          simp [a]
        have := hZ _ hmem σ hσ
        rw [e, map_neg] at this
        exact uvec_moved hx h1 h2 (neg_inj.1 this)
      | some y =>
        have hxy : (x : Fin 6) ≠ y := fun h => hij (by rw [Subtype.ext h])
        obtain ⟨σ, hσ, h1, h2⟩ := hQ x x.2 y y.2 hxy
        have e : Multiplicative.toAdd ((a (some x))⁻¹ * a (some y)) =
            uvec (x : Fin 6) (y : Fin 6) := by
          simp only [a, toAdd_mul, toAdd_inv, toAdd_ofAdd]
          exact neg_uvec_add_uvec _ _ _
        have := hZ _ hmem σ hσ
        rw [e] at this
        exact uvec_moved hxy h1 h2 this)
  rwa [hcard] at key

theorem card_mul_card_lt {J : Finset (Fin 6)} (hJ : J.card = 4)
    {F : Subgroup (Perm (Fin 6))} (hFle : F ≤ klein4 J) (hF1 : F ≠ ⊥)
    {A Z : Subgroup (Multiplicative (permBar 6))}
    (hA : ∀ u : altHeart 6, Multiplicative.ofAdd (heartToBar u) ∈ A) (hZA : Z ≤ A)
    (hZ : ∀ z ∈ Z, ∀ σ ∈ F, barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z) :
    Nat.card Z * Nat.card F < Nat.card A := by
  classical
  have hN := klein4_fourGroup hJ
  have hFdvd : Nat.card F ∣ 4 := by
    have := Subgroup.card_dvd_of_le hFle
    rwa [card_klein4 hJ] at this
  have hF1' : Nat.card F ≠ 1 := fun h => hF1 (Subgroup.card_eq_one.1 h)
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hdiv : Nat.card F = 2 ∨ Nat.card F = 4 := by
    have hle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hFdvd
    have hpos : 0 < Nat.card F := Nat.card_pos
    interval_cases h : Nat.card F
    · exact absurd rfl hF1'
    · exact Or.inl rfl
    · exact absurd hFdvd (by norm_num)
    · exact Or.inr rfl
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := J) (t := (Finset.univ : Finset (Fin 6))) (by rw [hJ]; simp)
  obtain ⟨σ, hσF, hσ1⟩ : ∃ σ ∈ F, σ ≠ 1 := by
    obtain ⟨⟨σ, hσ⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
    exact ⟨σ, hσ, fun h => hσ1 (Subtype.ext h)⟩
  have hfree : ∀ q ∈ J, σ q ≠ q := hN.free hJ (hFle hσF) hσ1
  have hσJ : ∀ q ∈ J, σ q ∈ J := fun q hq => (mem_setStab.1 (hN.stab (hFle hσF)) q).2 hq
  have hσsq : σ * σ = 1 := ((mem_klein4_iff hJ).1 (hFle hσF)).2
  have hσσ : ∀ q, σ (σ q) = q := fun q => by
    have := congrArg (fun f : Perm (Fin 6) => f q) hσsq
    simpa [Perm.mul_apply] using this
  rcases hdiv with h2 | h4
  ·
    obtain ⟨a, haJ⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨c, hcJ, hc⟩ := exists_fourth hJ {a, σ a} (Finset.card_le_two.trans (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨hca, hcσ⟩ := hc
    have hac : a ≠ c := Ne.symm hca
    have hcard : ({a, c} : Finset (Fin 6)).card = 2 := Finset.card_pair hac
    have hpT : p ∉ ({a, c} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hp (h ▸ haJ), fun h => hp (h ▸ hcJ)⟩
    have key := card_mul_succ_le hA hZA hZ {a, c} p hpT
      (fun x hx => by
        have hxJ : x ∈ J := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        exact ⟨σ, hσF, hfree x hxJ, fun h => hp (h ▸ hσJ x hxJ)⟩)
      (fun x hx y hy hxy => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl
        · rcases hy with rfl | rfl
          · exact absurd rfl hxy
          · exact ⟨σ, hσF, hfree _ haJ, fun h => hcσ h.symm⟩
        · rcases hy with rfl | rfl
          · refine ⟨σ, hσF, hfree _ hcJ, fun h => hcσ ?_⟩
            have := congrArg σ h
            rw [hσσ] at this
            exact this
          · exact absurd rfl hxy)
    rw [hcard] at key
    rw [h2]
    omega
  ·
    have hFN : F = klein4 J := Subgroup.eq_of_le_of_card_ge hFle (by rw [card_klein4 hJ, h4])
    have hN1 : klein4 J ≠ ⊥ := hFN ▸ hF1
    have key := card_mul_succ_le hA hZA hZ J p hp
      (fun x hx => ⟨σ, hσF, hfree x hx, fun h => hp (h ▸ hσJ x hx)⟩)
      (fun x hx y hy hxy => by
        obtain ⟨z, hzJ, hz⟩ := exists_fourth hJ {x, y} (Finset.card_le_two.trans (by norm_num))
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        obtain ⟨τ, hτ, hτx⟩ := hN.transitive hJ hN1 hx hzJ
        exact ⟨τ, hFN ▸ hτ, by rw [hτx]; exact hz.1, by rw [hτx]; exact hz.2⟩)
    rw [hJ] at key
    rw [h4]
    omega

end Six

section Len2

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6}

namespace Cfg.PiData

variable (D : C.PiData)

theorem altOn_le_theta_CMOf_six {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)}
    (hI : 2 * I.card < 6) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I)
    {S : Finset (Fin 6)} (hS : S = I ∨ S = Iᶜ) :
    altOn S ≤ ((CMOf M x).subgroupOf M).map C.θ := by
  refine altOn_le_of_threeCycles S _ fun τ hτ hsupp => ?_
  have hτS : τ ∈ altOn S := mem_altOn.2 ⟨hsupp, hτ.sign⟩
  have hτst : τ ∈ setStab S := altOn_le_setStab S hτS
  have hτI : τ ∈ setStab I := by
    rcases hS with rfl | rfl
    · exact hτst
    · exact setStab_compl_le I hτst
  have hfix : barAct τ (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) =
      Multiplicative.toAdd (D.piQ ⟨x, hx⟩) := by
    rw [hπ]
    exact (barAct_barInd_eq_self_iff hI _).2 hτI
  obtain ⟨y, hyθ, hyc⟩ := D.exists_comm_lift ⟨x, hx⟩ hτ hfix
  have hyM : (y : G) ∈ M := C.S.le y.2
  refine Subgroup.mem_map.2 ⟨⟨(y : G), hyM⟩, ?_, hyθ⟩
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.mem_inf.2 ⟨hyM, mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 hyc)⟩

theorem theta_mem_setStab_of_mem_CMOf_six {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 6)} (hI : 2 * I.card < 6)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {k : ↥M} (hk : (k : G) ∈ CMOf M x) :
    C.θ k ∈ setStab I := by
  have hc : (k : G) * x * (k : G)⁻¹ = x := mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
  have := D.piQ_conj k ⟨x, hx⟩ ⟨x, hx⟩ hc.symm
  rw [hπ] at this
  exact (barAct_barInd_eq_self_iff hI _).1 this.symm

theorem thetaN_le_setStab_six {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)}
    (hI : 2 * I.card < 6) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    C.thetaN x ≤ setStab I := by
  intro σ hσ
  obtain ⟨t, htT, rfl⟩ := C.mem_thetaN.1 hσ
  exact D.theta_mem_setStab_of_mem_CMOf_six hx hI hπ (TOf_le_C M x htT)

theorem thetaN_normalized_six {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)}
    (hI : 2 * I.card < 6) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I)
    {S : Finset (Fin 6)} (hS : S = I ∨ S = Iᶜ) :
    ∀ τ ∈ altOn S, ∀ σ ∈ C.thetaN x, τ * σ * τ⁻¹ ∈ C.thetaN x := by
  intro τ hτ σ hσ
  obtain ⟨c, hcC, hcθ⟩ := Subgroup.mem_map.1 (D.altOn_le_theta_CMOf_six hx hI hπ hS hτ)
  obtain ⟨t, htT, rfl⟩ := C.mem_thetaN.1 hσ
  have hcC' : (c : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hcC
  have hcmT : (c : G) * (t : G) * (c : G)⁻¹ ∈ TOf M x := normalized_TOf M x hcC' htT
  refine C.mem_thetaN.2 ⟨⟨(c : G) * t * (c : G)⁻¹, TOf_le_M M x hcmT⟩, hcmT, ?_⟩
  have : (⟨(c : G) * (t : G) * (c : G)⁻¹, TOf_le_M M x hcmT⟩ : ↥M) = c * t * c⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hcθ]

theorem mem_setStab_compl {I : Finset (Fin 6)} {σ : Perm (Fin 6)} (h : σ ∈ setStab I) :
    σ ∈ setStab Iᶜ := fun y => by
  have := mem_setStab.1 h y
  simp [this]

theorem fourGroup_thetaN_six (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : FourGroup Iᶜ (C.thetaN x) := by
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  refine Six.fourGroup_of_even hIc (C.isPGroup_thetaN x)
    (fun σ hσ => mem_setStab_compl (D.thetaN_le_setStab_six hx (by omega) hπ hσ))
    (D.thetaN_normalized_six hx (by omega) hπ (Or.inr rfl)) fun σ hσ => ?_
  obtain ⟨t, -, rfl⟩ := C.mem_thetaN.1 hσ
  exact Equiv.Perm.mem_alternatingGroup.1 (halt t)

theorem klein4_le_thetaN_six (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : klein4 Iᶜ ≤ C.thetaN x := by
  classical
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  set Lam : Subgroup G := CMOf M x ⊓ ((klein4 Iᶜ).comap C.θ).map M.subtype with hLam
  have hmemLam : ∀ g : G, g ∈ Lam ↔
      g ∈ CMOf M x ∧ ∃ hg : g ∈ M, C.θ ⟨g, hg⟩ ∈ klein4 Iᶜ := by
    intro g
    rw [hLam, Subgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hLamC : Lam ≤ CMOf M x := inf_le_left
  have hnorm : ∀ k ∈ CMOf M x, ∀ u ∈ Lam, k * u * k⁻¹ ∈ Lam := by
    intro k hk u hu
    obtain ⟨huC, huM, huθ⟩ := (hmemLam u).1 hu
    have hkM : k ∈ M := (Subgroup.mem_inf.1 hk).1
    have hkuM : k * u * k⁻¹ ∈ M := M.mul_mem (M.mul_mem hkM huM) (M.inv_mem hkM)
    refine (hmemLam _).2 ⟨(CMOf M x).mul_mem ((CMOf M x).mul_mem hk huC) ((CMOf M x).inv_mem hk),
      hkuM, ?_⟩
    have e : (⟨k * u * k⁻¹, hkuM⟩ : ↥M) = ⟨k, hkM⟩ * ⟨u, huM⟩ * ⟨k, hkM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact klein4_conj_mem hIc (mem_setStab_compl
      (D.theta_mem_setStab_of_mem_CMOf_six hx (by omega) hπ (k := ⟨k, hkM⟩) hk)) huθ
  have hLam2 : IsPGroup 2 Lam := by
    refine isPGroup_two_of_forall fun u hu => ?_
    obtain ⟨huC, huM, huθ⟩ := (hmemLam u).1 hu
    have hsq := ((mem_klein4_iff hIc).1 huθ).2
    have hK : u * u ∈ C.K := by
      refine C.mem_K.2 ⟨M.mul_mem huM huM, ?_⟩
      have e : (⟨u * u, M.mul_mem huM huM⟩ : ↥M) = ⟨u, huM⟩ * ⟨u, huM⟩ := rfl
      rw [e, map_mul, hsq]
    rw [C.K_eq_Q hR] at hK
    obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf M hK
    refine ⟨j + 1, ?_⟩
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact hj
  have hLamT : Lam ≤ TOf M x := le_pCoreOf_of_normalized hLamC hnorm hLam2
  intro σ hσ
  have hσA : σ ∈ altOn Iᶜ := klein4_le_altOn hIc hσ
  obtain ⟨c, hcC, hcθ⟩ :=
    Subgroup.mem_map.1 (D.altOn_le_theta_CMOf_six hx (by omega) hπ (Or.inr rfl) hσA)
  have hcC' : (c : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hcC
  have hcLam : (c : G) ∈ Lam := (hmemLam _).2 ⟨hcC', c.2, by
    show C.θ c ∈ klein4 Iᶜ
    rw [hcθ]
    exact hσ⟩
  exact C.mem_thetaN.2 ⟨c, hLamT hcLam, hcθ⟩

theorem theta_TOf_len_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    C.thetaN x = klein4 Iᶜ := by
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  have hF := D.fourGroup_thetaN_six halt hx hI hπ
  have hle := D.klein4_le_thetaN_six hR hx hI hπ
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_klein4 hIc]; exact hF.card_le_four hIc)).symm

theorem heart_mem_piQ_Q (u : altHeart 6) :
    Multiplicative.ofAdd (heartToBar u) ∈
      ((CFSG.Open.pCoreOf 2 M).subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ := by
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
  have hwQ : (w : G) ∈ CFSG.Open.pCoreOf 2 M := C.S.W_le_Q w.2
  refine Subgroup.mem_map.2 ⟨⟨(w : G), hwQ⟩, Subgroup.mem_subgroupOf.2 hwQ, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [D.piQ_W w ⟨(w : G), hwQ⟩ rfl, hw]
  rfl

include D in
theorem eq_Q_of_theta_le_klein4 (hR : Nat.card ↥(Rc X) ≤ 2) {J : Finset (Fin 6)}
    (hJ : J.card = 4) {A : Subgroup G} (hAM : A ≤ M)
    (hFN : (A.subgroupOf M).map C.θ ≤ klein4 J) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≤ Nat.card ↥A) :
    A = CFSG.Open.pCoreOf 2 M := by
  classical
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  have hcardA := C.card_eq_card_inf_mul hR hAM
  by_cases hbot : (A.subgroupOf M).map C.θ = ⊥
  · rw [hbot, Subgroup.card_bot, mul_one] at hcardA
    have hAQ : A ⊓ Q = A :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ Q ≤ A) hcardA.le
    have hAle : A ≤ Q := hAQ ▸ inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hAle hcard
  · exfalso
    set F : Subgroup (Perm (Fin 6)) := (A.subgroupOf M).map C.θ with hF
    set Ab : Subgroup (Multiplicative (permBar 6)) := (Q.subgroupOf Q).map D.piQ with hAb
    set Zg : Subgroup G := Q ⊓ Subgroup.centralizer (A : Set G) with hZg
    set Zp : Subgroup (Multiplicative (permBar 6)) := (Zg.subgroupOf Q).map D.piQ with hZp
    have hZgQ : Zg ≤ Q := inf_le_left
    have hZpA : Zp ≤ Ab := by
      rintro z ⟨q, -, rfl⟩
      exact ⟨q, Subgroup.mem_subgroupOf.2 q.2, rfl⟩
    have hZpfix : ∀ z ∈ Zp, ∀ σ ∈ F,
        barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z := by
      rintro z ⟨q, hq, rfl⟩ σ ⟨m, hm, rfl⟩
      have hqA : (q : G) ∈ Subgroup.centralizer (A : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).2
      have hmA : (m : G) ∈ A := hm
      have hc : (m : G) * (q : G) = (q : G) * (m : G) :=
        Subgroup.mem_centralizer_iff.1 hqA (m : G) hmA
      have := D.piQ_conj m q q (by rw [Subgroup.coe_inv, hc]; group)
      exact this.symm
    have hlt := Six.card_mul_card_lt hJ hFN hbot D.heart_mem_piQ_Q hZpA hZpfix
    have hcardZ := D.card_eq_card_inf_R_mul hZgQ
    have hcardQ := D.card_eq_card_inf_R_mul (le_refl Q)
    have hRQ : Q ⊓ Rc X = Rc X := inf_eq_right.2 (by
      rw [C.S.R_eq_inf]
      exact inf_le_left)
    rw [hRQ] at hcardQ
    have hZR : Nat.card ↥(Zg ⊓ Rc X) ≤ Nat.card ↥(Rc X) := Subgroup.card_le_of_le inf_le_right
    have hAZ : A ⊓ Q ≤ Zg := by
      intro a ha
      obtain ⟨haA, haQ⟩ := Subgroup.mem_inf.1 ha
      exact Subgroup.mem_inf.2 ⟨haQ, Subgroup.mem_centralizer_iff.2 fun b hb =>
        hAab b hb a haA⟩
    have hAZc : Nat.card ↥(A ⊓ Q) ≤ Nat.card Zg := Subgroup.card_le_of_le hAZ
    have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
    have hlt' : Nat.card ↥A < Nat.card ↥Q := by
      rw [hcardA, hcardQ]
      calc Nat.card ↥(A ⊓ Q) * Nat.card F
          ≤ Nat.card Zg * Nat.card F := Nat.mul_le_mul_right _ hAZc
        _ = (Nat.card ↥(Zg ⊓ Rc X) * Nat.card Zp) * Nat.card F := by rw [hcardZ]
        _ ≤ (Nat.card ↥(Rc X) * Nat.card Zp) * Nat.card F :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hZR)
        _ = Nat.card ↥(Rc X) * (Nat.card Zp * Nat.card F) := by ring
        _ < Nat.card ↥(Rc X) * Nat.card Ab := Nat.mul_lt_mul_of_pos_left hlt hRpos
    omega

theorem eq_Q_of_le_TOf_len_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {A : Subgroup G}
    (hAT : A ≤ TOf M x) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≤ Nat.card ↥A) :
    A = CFSG.Open.pCoreOf 2 M := by
  have hIc : Iᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hI]
  have hFN : (A.subgroupOf M).map C.θ ≤ klein4 Iᶜ := by
    rw [← D.theta_TOf_len_two hR halt hx hI hπ]
    exact Subgroup.map_mono (fun m hm => hAT hm)
  exact D.eq_Q_of_theta_le_klein4 hR hIc (hAT.trans (TOf_le_M M x)) hFN hAab hcard

theorem conj_eq_of_le_TOf_len_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (halt : ∀ m : ↥M, C.θ m ∈ alternatingGroup (Fin 6)) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 6)} (hI : I.card = 2)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {g : G}
    (hg : conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ TOf M x) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  have hQ := C.Q_comm hR
  refine D.eq_Q_of_le_TOf_len_two hR halt hx hI hπ hg (fun a ha b hb => ?_)
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have h1 := hQ _ (mem_conjSubgroup.1 ha) _ (mem_conjSubgroup.1 hb)
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = b * a := by group

end Cfg.PiData

end Len2

end CFSG.RankThree.PartTwo.Sec19.SolEven
