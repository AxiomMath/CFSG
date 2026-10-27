module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSpUCard
import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveAbs
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAct
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

private theorem wc85ex_center_eq_bot_of_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hB : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : e x ∈ Subgroup.center B := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨x, hx, rfl⟩
  rw [hB, Subgroup.mem_bot] at hx'
  exact e.injective (by simpa using hx')

private theorem wc85ex_center_eq_bot_of_isSpGp {L : Type} [Group L] {m n : ℕ}
    (hL : IsSpGp L m n) : Subgroup.center L = ⊥ := by
  obtain ⟨k, -, F, hFld, hFin, hFcard, ⟨e⟩⟩ := hL
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [← Nat.card_eq_fintype_card]; exact hFcard)
  have hcenter : Subgroup.center (↥(StatedSp k F)) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  exact wc85ex_center_eq_bot_of_mulEquiv e hcenter

private theorem wc85ex_center_eq_bot_of_isPSUGp {L : Type} [Group L] {m n : ℕ} (hm : 4 ≤ m)
    (hL : IsPSUGp L m n) : Subgroup.center L = ⊥ := by
  have hadm := CFSG.Blueprint.LieModel.admissible hL
  obtain ⟨-, hn1, hm3, hne⟩ := hadm
  obtain ⟨⟨-, -, -, -⟩, K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm3' : 3 ≤ m := by omega
  have hsimple : IsSimpleGroup (StatedProj (StatedSU m (2 ^ n) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 n hKcard m hm3' hne
  have hntriv : Nontrivial (StatedProj (StatedSU m (2 ^ n) K)) :=
    (CFSG.ClassicalGroups.Unitary.fam_unitary_projective_simple K 2 n hKcard m hm3' hne).2.1
  have hperfSU : Group.IsPerfect (StatedSU m (2 ^ n) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := n) hKcard (n := m) hm3' hne
  have hperf : Group.IsPerfect (StatedProj (StatedSU m (2 ^ n) K)) := by
    haveI := hperfSU
    exact Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' ((StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ n) K)))
      (QuotientGroup.mk'_surjective _)
  haveI := hntriv
  haveI := hperf
  have hcenterP : Subgroup.center (StatedProj (StatedSU m (2 ^ n) K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSU m (2 ^ n) K))) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) (Group.IsPerfect.not_isMulCommutative _)
  exact wc85ex_center_eq_bot_of_mulEquiv e hcenterP

private theorem wc85ex_inf_center_eq_bot_of_isPGroup {X : Type} [Group X] [Finite X]
    {W : Subgroup X} (hW : IsPGroup 2 W) (hodd : Odd (Nat.card (Subgroup.center X))) :
    W ⊓ Subgroup.center X = ⊥ := by
  have h2 : IsPGroup 2 (W ⊓ Subgroup.center X : Subgroup X) := hW.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hdvd : Nat.card ↥(W ⊓ Subgroup.center X) ∣ Nat.card (Subgroup.center X) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hkne
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
    have h2dvd : 2 ∣ 2 ^ (j + 1) := ⟨2 ^ j, by rw [pow_succ]; ring⟩
    exact hodd.not_two_dvd_nat (dvd_trans h2dvd hdvd)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq (H := W ⊓ Subgroup.center X) hk

private theorem wc85ex_exists_action_H {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
    (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {X : Type} [Group X]
    {φ : ↥(kGenIn V H) →* X} (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) :
    ∃ ρX : ↥H →* MulAut X, ∀ (u : ↥H) (k k' : ↥(kGenIn V H)),
      (k' : G) = u * k * u⁻¹ → ρX u (φ k) = φ k' := by
  have hmem : ∀ (u : ↥H) (k : ↥(kGenIn V H)), (u : G) * k * (u : G)⁻¹ ∈ kGenIn V H :=
    fun u k => (Subgroup.mem_normalizer_iff.1
      (h.le_normalizer_kGenIn_of_eq_sup hKT u.2) k).1 k.2
  let cj : ↥H → ↥(kGenIn V H) → ↥(kGenIn V H) := fun u k => ⟨u * k * u⁻¹, hmem u k⟩
  have hcj_one : ∀ k, cj 1 k = k := fun k => Subtype.ext (by simp [cj])
  have hcj_mul : ∀ a b k, cj (a * b) k = cj a (cj b k) := fun a b k =>
    Subtype.ext (by simp [cj, mul_assoc])
  choose ρ₀ hρ₀ using fun u : ↥H => exists_conj_aut h hKT hφ u.2
  have hρcj : ∀ u k, ρ₀ u (φ k) = φ (cj u k) := fun u k => hρ₀ u k (cj u k) rfl
  refine ⟨{ toFun := ρ₀
            map_one' := ?_
            map_mul' := ?_ }, fun u k k' hk => ?_⟩
  · refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := hφ.surjective x
    rw [hρcj, hcj_one]
    rfl
  · intro a b
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := hφ.surjective x
    rw [hρcj, hcj_mul]
    change _ = ρ₀ a (ρ₀ b (φ k))
    rw [hρcj, hρcj]
  · change ρ₀ u (φ k) = φ k'
    rw [hρcj u k]
    exact congrArg φ (Subtype.ext (by rw [hk]))

private theorem wc85ex_isSymplecticRootGroup_quot_center {X : Type} [Group X] [Finite X]
    {m n : ℕ} {W : Subgroup X} (hodd : Odd (Nat.card (Subgroup.center X)))
    (hW : IsSymplecticRootGroup X m n W) :
    IsSymplecticRootGroup (X ⧸ Subgroup.center X) m n
      (W.map (QuotientGroup.mk' (Subgroup.center X))) := by
  obtain ⟨hcard, k, hm, F, hFld, hFin, hFcard, e, he⟩ := hW
  have hSp : IsSpGp (X ⧸ Subgroup.center X) m n :=
    ⟨k, hm, F, hFld, hFin, hFcard, ⟨e⟩⟩
  have hcenter : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    wc85ex_center_eq_bot_of_isSpGp hSp
  have hdisj : W ⊓ Subgroup.center X = ⊥ :=
    wc85ex_inf_center_eq_bot_of_isPGroup (IsPGroup.of_card (n := n) hcard) hodd
  have hinj : Set.InjOn (QuotientGroup.mk' (Subgroup.center X)) (W : Set X) := by
    intro a ha b hb hab
    have h1 : (QuotientGroup.mk' (Subgroup.center X)) (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ Subgroup.center X :=
      (QuotientGroup.eq_one_iff (a⁻¹ * b)).1 (by simpa [QuotientGroup.mk'_apply] using h1)
    have h3 : a⁻¹ * b ∈ W := W.mul_mem (W.inv_mem ha) hb
    have hmem : a⁻¹ * b ∈ W ⊓ Subgroup.center X := Subgroup.mem_inf.mpr ⟨h3, h2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hmem
  have hcardR : Nat.card (W.map (QuotientGroup.mk' (Subgroup.center X))) = 2 ^ n := by
    change Nat.card ((QuotientGroup.mk' (Subgroup.center X)) '' (W : Set X)) = 2 ^ n
    rw [Nat.card_image_of_injOn hinj]
    simpa using hcard
  let e' : (X ⧸ Subgroup.center X) ⧸ Subgroup.center (X ⧸ Subgroup.center X) ≃*
      ↥(StatedSp k F) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans e)
  have hbot : ∀ x : X ⧸ Subgroup.center X,
      QuotientGroup.quotientBot
        (QuotientGroup.mk x : (X ⧸ Subgroup.center X) ⧸ ⊥) = x := by
    intro x
    change (QuotientGroup.kerLift (MonoidHom.id (X ⧸ Subgroup.center X)))
      (QuotientGroup.mk x : (X ⧸ Subgroup.center X) ⧸ (MonoidHom.id _).ker) = x
    rw [QuotientGroup.kerLift_mk]
    rfl
  have he' : ∀ w : X,
      e' (QuotientGroup.mk (QuotientGroup.mk' (Subgroup.center X) w)) =
        e (QuotientGroup.mk' (Subgroup.center X) w) := by
    intro w
    change e (QuotientGroup.quotientBot (QuotientGroup.quotientMulEquivOfEq hcenter
      (QuotientGroup.mk (QuotientGroup.mk' (Subgroup.center X) w)))) =
        e (QuotientGroup.mk' (Subgroup.center X) w)
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    exact congrArg e (hbot _)
  refine ⟨hcardR, k, hm, F, hFld, hFin, hFcard, e', ?_⟩
  rintro r ⟨w, hwW, rfl⟩ hr
  have hw1 : w ≠ 1 := by rintro rfl; exact hr (map_one _)
  rw [he' w]
  simpa only [QuotientGroup.mk'_apply] using he w hwW hw1

private theorem wc85ex_isUnitaryRootGroup_quot_center {X : Type} [Group X] [Finite X]
    {m n : ℕ} (hm : 4 ≤ m) {W : Subgroup X} (hodd : Odd (Nat.card (Subgroup.center X)))
    (hPSU : IsPSUGp (X ⧸ Subgroup.center X) m n) (hW : IsUnitaryRootGroup X m n W) :
    IsUnitaryRootGroup (X ⧸ Subgroup.center X) m n
      (W.map (QuotientGroup.mk' (Subgroup.center X))) := by
  obtain ⟨hcard, F, hFld, hFin, hFcard, e, he⟩ := hW
  have hcenter : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    wc85ex_center_eq_bot_of_isPSUGp hm hPSU
  have hdisj : W ⊓ Subgroup.center X = ⊥ :=
    wc85ex_inf_center_eq_bot_of_isPGroup (IsPGroup.of_card (n := n) hcard) hodd
  have hinj : Set.InjOn (QuotientGroup.mk' (Subgroup.center X)) (W : Set X) := by
    intro a ha b hb hab
    have h1 : (QuotientGroup.mk' (Subgroup.center X)) (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ Subgroup.center X :=
      (QuotientGroup.eq_one_iff (a⁻¹ * b)).1 (by simpa [QuotientGroup.mk'_apply] using h1)
    have h3 : a⁻¹ * b ∈ W := W.mul_mem (W.inv_mem ha) hb
    have hmem : a⁻¹ * b ∈ W ⊓ Subgroup.center X := Subgroup.mem_inf.mpr ⟨h3, h2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hmem
  have hcardR : Nat.card (W.map (QuotientGroup.mk' (Subgroup.center X))) = 2 ^ n := by
    change Nat.card ((QuotientGroup.mk' (Subgroup.center X)) '' (W : Set X)) = 2 ^ n
    rw [Nat.card_image_of_injOn hinj]
    simpa using hcard
  let e' : (X ⧸ Subgroup.center X) ⧸ Subgroup.center (X ⧸ Subgroup.center X) ≃*
      StatedProj (StatedSU m (2 ^ n) F) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans e)
  have hbot : ∀ x : X ⧸ Subgroup.center X,
      QuotientGroup.quotientBot
        (QuotientGroup.mk x : (X ⧸ Subgroup.center X) ⧸ ⊥) = x := by
    intro x
    change (QuotientGroup.kerLift (MonoidHom.id (X ⧸ Subgroup.center X)))
      (QuotientGroup.mk x : (X ⧸ Subgroup.center X) ⧸ (MonoidHom.id _).ker) = x
    rw [QuotientGroup.kerLift_mk]
    rfl
  have he' : ∀ w : X,
      e' (QuotientGroup.mk (QuotientGroup.mk' (Subgroup.center X) w)) =
        e (QuotientGroup.mk' (Subgroup.center X) w) := by
    intro w
    change e (QuotientGroup.quotientBot (QuotientGroup.quotientMulEquivOfEq hcenter
      (QuotientGroup.mk (QuotientGroup.mk' (Subgroup.center X) w)))) =
        e (QuotientGroup.mk' (Subgroup.center X) w)
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    exact congrArg e (hbot _)
  refine ⟨hcardR, F, hFld, hFin, hFcard, e', ?_⟩
  rintro r ⟨w, hwW, rfl⟩ hr
  have hw1 : w ≠ 1 := by rintro rfl; exact hr (map_one _)
  rw [he' w]
  simpa only [QuotientGroup.mk'_apply] using he w hwW hw1

section Certified


theorem exists_rootData (hLie : SpPSULieFacts) (hRU : UnitaryRootCommutatorRank)
    (d : ShapeData V H T φ) {m n : ℕ} (hm : 4 ≤ m)
    (h : (IsSpGp (X ⧸ Subgroup.center X) m n ∧
        IsSymplecticRootGroup X m n (barSub (kGenIn V H) φ V)) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧
        IsUnitaryRootGroup X m n (barSub (kGenIn V H) φ V))) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S) (ψ : ↥(kGenIn V H) →* S) (ρ : ↥H →* MulAut S)
      (R Sy : Subgroup S) (e : ℕ), RootData V H T S ψ ρ R Sy e := by
  haveI : Finite X := d.finite
  obtain ⟨ρX, hρX⟩ := wc85ex_exists_action_H d.hyp83 d.eq_sup d.bar
  have hρXcenter : ∀ (u : ↥H) (x : X),
      (QuotientGroup.mk' (Subgroup.center X)) x = 1 →
        (QuotientGroup.mk' (Subgroup.center X)) (ρX u x) = 1 := by
    intro u x hx
    have hx' : x ∈ Subgroup.center X := by
      rw [QuotientGroup.mk'_apply] at hx
      exact (QuotientGroup.eq_one_iff x).1 hx
    have hmap : Subgroup.map (ρX u).toMonoidHom (Subgroup.center X) = Subgroup.center X :=
      Subgroup.map_center_eq (ρX u)
    have hmem : ρX u x ∈ Subgroup.map (ρX u).toMonoidHom (Subgroup.center X) :=
      Subgroup.mem_map_of_mem _ hx'
    rw [hmap] at hmem
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (ρX u x)).2 hmem
  obtain ⟨ρ, hρ⟩ := gap5_exists_quotAut (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) ρX hρXcenter
  let ψ : ↥(kGenIn V H) →* (X ⧸ Subgroup.center X) :=
    (QuotientGroup.mk' (Subgroup.center X)).comp φ
  let R : Subgroup (X ⧸ Subgroup.center X) := barSub (kGenIn V H) ψ V
  let Sy : Subgroup (X ⧸ Subgroup.center X) := barSub (kGenIn V H) ψ T
  have hsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (Subgroup.center X)).comp d.bar.surjective
  have hact : ∀ (h : ↥H) (k x : ↥(kGenIn V H)), (x : G) = h * k * h⁻¹ →
      ρ h (ψ k) = ψ x := by
    intro h k x hx
    have h1 : ρ h (ψ k) =
        (QuotientGroup.mk' (Subgroup.center X)) (ρX h (φ k)) := hρ h (φ k)
    have h2 : ρX h (φ k) = φ x := hρX h k x hx
    rw [h1, h2]
    rfl
  have hker : ∀ k : ↥(kGenIn V H), ψ k = 1 ↔
      (k : G) ∈ centerPre (kGenIn V H) (eCentSet V H T) := by
    intro k
    have h1 : ψ k = 1 ↔ (k : G) ∈ centerPre (kGenIn V H)
        ((pCoreOf 2 (kGenIn V H) : Subgroup G) : Set G) := by
      change (QuotientGroup.mk' (Subgroup.center X)) (φ k) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      constructor
      · intro hk
        refine ⟨k.2, fun x hx => ?_⟩
        have h2 : φ (k * (⟨x, hx⟩ : ↥(kGenIn V H)) * k⁻¹ *
            (⟨x, hx⟩ : ↥(kGenIn V H))⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hk (φ ⟨x, hx⟩)]
          group
        exact (d.bar.ker_iff _).mp h2
      · rintro ⟨-, hx⟩ g
        obtain ⟨y, rfl⟩ := d.bar.surjective g
        have h2 : φ (k * y * k⁻¹ * y⁻¹) = 1 := by
          refine (d.bar.ker_iff _).mpr ?_
          simpa using hx (y : G) y.2
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
        exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)).symm
    exact h1.trans (by rw [Hyp83.centerPre_eCentSet_eq d.hyp83 d.eq_sup])
  have hRmap : R = (barSub (kGenIn V H) φ V).map (QuotientGroup.mk' (Subgroup.center X)) := by
    show (V.subgroupOf (kGenIn V H)).map
        ((QuotientGroup.mk' (Subgroup.center X)).comp φ) =
      ((V.subgroupOf (kGenIn V H)).map φ).map (QuotientGroup.mk' (Subgroup.center X))
    rw [Subgroup.map_map]
  have hSymap : Sy = (barSub (kGenIn V H) φ T).map (QuotientGroup.mk' (Subgroup.center X)) := by
    show (T.subgroupOf (kGenIn V H)).map
        ((QuotientGroup.mk' (Subgroup.center X)).comp φ) =
      ((T.subgroupOf (kGenIn V H)).map φ).map (QuotientGroup.mk' (Subgroup.center X))
    rw [Subgroup.map_map]
  have hKH : kGenIn V H ≤ H := kGenIn_le_H d.hyp83.le_H
  have hKN : ((kGenIn V H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
      (d.hyp83.le_normalizer_kGenIn_of_eq_sup d.eq_sup)
  have hSylK : IsSylowIn 2 (T ⊓ kGenIn V H) (kGenIn V H) :=
    d.hyp83.sylow_H.inf_normal hKH hKN
  let P₀ : Sylow 2 ↥(kGenIn V H) := hSylK.toSylow
  have hP₀coe : ((P₀.mapSurjective d.bar.surjective : Sylow 2 X) : Subgroup X) =
      barSub (kGenIn V H) φ T := by
    change ((hSylK.toSylow).mapSurjective d.bar.surjective : Subgroup X) =
      (T.subgroupOf (kGenIn V H)).map φ
    rw [Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
    show ((T ⊓ kGenIn V H).subgroupOf (kGenIn V H)).map φ =
      (T.subgroupOf (kGenIn V H)).map φ
    rw [inf_subgroupOf_right]
  have hSySylow : ∃ P : Sylow 2 (X ⧸ Subgroup.center X),
      (P : Subgroup (X ⧸ Subgroup.center X)) = Sy := by
    refine ⟨(P₀.mapSurjective d.bar.surjective).mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center X)), ?_⟩
    rw [Sylow.coe_mapSurjective, hP₀coe]
    exact hSymap.symm
  have hRSy : R ≤ Sy := by
    rw [hRmap, hSymap]
    refine Subgroup.map_mono ?_
    rintro x hx
    obtain ⟨v, hvV, rfl⟩ := mem_barSub.1 hx
    exact mem_barSub.2 ⟨v, d.hyp83.le_T hvV, rfl⟩
  have hkeyW0 : ∀ y ∈ barSub (kGenIn V H) φ T,
      ∀ w ∈ barSub (kGenIn V H) φ V, y * w * y⁻¹ ∈ barSub (kGenIn V H) φ V := by
    intro y hy w hw
    obtain ⟨t, htT, rfl⟩ := mem_barSub.1 hy
    obtain ⟨v, hvV, rfl⟩ := mem_barSub.1 hw
    refine mem_barSub.2 ⟨t * v * t⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (d.hyp83.T_le_normalizer htT) v).1 hvV
    · rw [map_mul, map_mul, map_inv]
  have hSyT_norm : barSub (kGenIn V H) φ T ≤
      Subgroup.normalizer ((barSub (kGenIn V H) φ V : Subgroup X) : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    exact ⟨fun hw => hkeyW0 y hy w hw, fun hw => by
      have := hkeyW0 y⁻¹ ((barSub (kGenIn V H) φ T).inv_mem hy) (y * w * y⁻¹) hw
      simpa [mul_assoc] using this⟩
  have hkeyR : ∀ y ∈ Sy, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨t, htT, rfl⟩ := mem_barSub.1 hy
    obtain ⟨v, hvV, rfl⟩ := mem_barSub.1 hr
    refine mem_barSub.2 ⟨t * v * t⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (d.hyp83.T_le_normalizer htT) v).1 hvV
    · rw [map_mul, map_mul, map_inv]
  have hSy_norm : Sy ≤ Subgroup.normalizer (R : Set (X ⧸ Subgroup.center X)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro r
    exact ⟨fun hr => hkeyR y hy r hr, fun hr => by
      have := hkeyR y⁻¹ (Sy.inv_mem hy) (y * r * y⁻¹) hr
      simpa [mul_assoc] using this⟩
  rcases h with ⟨hSp, hR0⟩ | ⟨hPSU, hR0⟩
  · have hRtrans : IsSymplecticRootGroup (X ⧸ Subgroup.center X) m n R := by
      rw [hRmap]
      exact wc85ex_isSymplecticRootGroup_quot_center d.odd_card_center hR0
    have hlie : RootLieFacts (X ⧸ Subgroup.center X) R Sy 1 :=
      rootLieFacts_sp hLie hm hSp hRtrans hSySylow hSy_norm hRSy
    refine ⟨X ⧸ Subgroup.center X, inferInstance, inferInstance, ψ, ρ, R, Sy, 1, ?_⟩
    refine ⟨d.hyp83, d.eq_sup, hsurj, hker, hact, rfl, rfl,
      ⟨hSySylow, hRSy, hSy_norm⟩, hlie, ?_⟩
    rw [pow_one, hRtrans.1, ← hR0.1]
    exact card_barSub_lt_card_V d
  · have hRtrans : IsUnitaryRootGroup (X ⧸ Subgroup.center X) m n R := by
      rw [hRmap]
      exact wc85ex_isUnitaryRootGroup_quot_center hm d.odd_card_center hPSU hR0
    have hlie : RootLieFacts (X ⧸ Subgroup.center X) R Sy 2 :=
      rootLieFacts_psu hLie hm hPSU hRtrans hSySylow hSy_norm hRSy
    refine ⟨X ⧸ Subgroup.center X, inferInstance, inferInstance, ψ, ρ, R, Sy, 2, ?_⟩
    refine ⟨d.hyp83, d.eq_sup, hsurj, hker, hact, rfl, rfl,
      ⟨hSySylow, hRSy, hSy_norm⟩, hlie, ?_⟩
    rw [hRtrans.1]
    exact card_V_gt_unitary hRU d (by omega) hPSU hR0

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
