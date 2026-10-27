module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSix
public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
public import CFSG.LocalAnalysis.WeakClosure81.ThreeTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem le_sup_zpowers_of_relIndex_eq_two {L K : Subgroup G} (hLK : L ≤ K)
    (h : L.relIndex K = 2) {a : G} (haK : a ∈ K) (haL : a ∉ L) :
    K ≤ L ⊔ Subgroup.zpowers a := by
  intro x hxK
  have hKindex : (L.subgroupOf K).index = 2 := h
  by_cases hxL : x ∈ L
  · exact Subgroup.mem_sup_left hxL
  · have hmul := Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K) hKindex
      (a := (⟨x, hxK⟩ : K)) (b := (⟨a, haK⟩ : K))
    have hxa : x * a ∈ L := by
      have : (⟨x, hxK⟩ : K) * (⟨a, haK⟩ : K) ∈ L.subgroupOf K := by
        rw [hmul]
        exact ⟨fun hx' => absurd (Subgroup.mem_subgroupOf.mp hx') hxL,
          fun ha' => absurd (Subgroup.mem_subgroupOf.mp ha') haL⟩
      exact Subgroup.mem_subgroupOf.mp this
    have hmem : (x * a) * a⁻¹ ∈ L ⊔ Subgroup.zpowers a :=
      (L ⊔ Subgroup.zpowers a).mul_mem (Subgroup.mem_sup_left hxa)
        (Subgroup.mem_sup_right ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)))
    rwa [show (x * a) * a⁻¹ = x by group] at hmem

private theorem mem_normalizer_sup_of_conj_mem {U J : Subgroup G} {u x : G}
    (hJfix : conjSubgroup J x = J) (hUJ2 : (U ⊓ J).relIndex U = 2) (hu : u ∈ U)
    (huJ : u ∉ J) (hxux : x⁻¹ * u * x ∈ U ⊔ J) :
    x ∈ Subgroup.normalizer ((U ⊔ J : Subgroup G) : Set G) := by
  have hUle : U ≤ (U ⊓ J) ⊔ Subgroup.zpowers u :=
    le_sup_zpowers_of_relIndex_eq_two inf_le_left hUJ2 hu
      (fun h => huJ (Subgroup.mem_inf.mp h).2)
  have hconjU : conjSubgroup U x ≤ U ⊔ J := by
    calc conjSubgroup U x ≤ conjSubgroup ((U ⊓ J) ⊔ Subgroup.zpowers u) x :=
          Subgroup.map_mono hUle
      _ = conjSubgroup (U ⊓ J) x ⊔ conjSubgroup (Subgroup.zpowers u) x := by
          simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_sup]
      _ ≤ U ⊔ J := by
          refine sup_le ?_ ?_
          · calc conjSubgroup (U ⊓ J) x ≤ conjSubgroup J x := Subgroup.map_mono inf_le_right
              _ = J := hJfix
              _ ≤ U ⊔ J := le_sup_right
          · rw [CFSG.Quasithin.conjSubgroup, MonoidHom.map_zpowers]
            exact Subgroup.zpowers_le.mpr (by
              show (MulAut.conj x⁻¹) u ∈ U ⊔ J
              rw [MulAut.conj_apply, inv_inv]
              exact hxux)
  have hconj : conjSubgroup (U ⊔ J) x ≤ U ⊔ J := by
    rw [show conjSubgroup (U ⊔ J) x = conjSubgroup U x ⊔ conjSubgroup J x by
      simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_sup]]
    rw [hJfix]
    exact sup_le hconjU le_sup_right
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  exact Subgroup.eq_of_le_of_card_ge hconj (by rw [card_conjSubgroup'])

theorem seven_six_one_hall {V H E J A X Y : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E) (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J)
    (hJX : J ≤ X) (hXH : X ≤ H)
    [(J.subgroupOf X).Normal] (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hXodd : Odd (J.relIndex X))
    (hXnil : Group.IsNilpotent (↥X ⧸ J.subgroupOf X))
    (hfaith : ∀ a ∈ A, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J)
    (hAgen : A = ⨆ U ∈ omegaSet V H E, ⨆ (_ : U ≤ A), U)
    (hIY : iSub V H E ≤ Y) (hYX : Y ≤ X) (hYJ : Y ⊓ J = iSub V H E) (hYJX : Y ⊔ J = X) :
    A ⊔ J = (⨆ U ∈ omegaSet V H E, ⨆ (_ : U ≤ A ⊔ J),
      ⨆ (_ : U ≤ Subgroup.normalizer (Y : Set G)), U) ⊔ J := by
  have hJleH : J ≤ H := hJ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun W => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hInorm : ((iSub V H E).subgroupOf H).Normal := iSub_subgroupOf_normal hEH hEnorm
  set R : Subgroup G :=
    (⨆ U ∈ omegaSet V H E, ⨆ (_ : U ≤ A ⊔ J),
      ⨆ (_ : U ≤ Subgroup.normalizer (Y : Set G)), U) with hR
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ le_sup_right
    rw [hAgen]
    refine iSup_le fun U => iSup_le fun hU => iSup_le fun hUleA => ?_
    have hUbase : U ∈ omegaSet U H E := by rw [omegaSet_eq_of_mem hU]; exact hU
    have hIeq : iSub U H E = iSub V H E := iSub_eq_of_mem hU
    have hfirst := seven_six_one_relIndex_eq_two (V := U) (H := H) (E := E) (J := J)
      (A := A) (X := X) (isElemAbelian_of_mem_omegaSet hV hU) (isTI_of_mem_omegaSet hU hTI)
      hE hEH hEnorm (by rw [omegaSet_eq_of_mem hU]; exact hOmH) hJ hJnorm
      (by rw [iSub_eq_of_mem hU]; exact hIJ) hJX hXH hAX hXodd hfaith U hUbase
      hUleA
    have hUJ2 : (U ⊓ J).relIndex U = 2 := by
      rw [← inf_iSub_eq_inf_J hU hIJ hJ, ← hIeq]
      exact hfirst.2
    have hOmU : ∀ W ∈ omegaSet U H E, W ≤ H := by
      intro W hW
      rw [omegaSet_eq_of_mem hU] at hW
      exact hOmH W hW
    have hN : ∀ W ∈ omegaSet U H E, ⁅W, U⁆ ≠ ⊥ →
        U ⊓ Subgroup.normalizer (W : Set G) = U ⊓ iSub U H E :=
      nVSub_eq_inf_iSub_of_relIndex_eq_two (V := U) (isElemAbelian_of_mem_omegaSet hV hU)
        (isTI_of_mem_omegaSet hU hTI) hE hEH hEnorm hOmU hfirst.2
    obtain ⟨g, hUg, -, hUnotO⟩ := mem_omegaSet.mp hU
    have hUnotJ : ¬ U ≤ J := fun hUJ => hUnotO (hUJ.trans hJ)
    obtain ⟨u, hu, huJ⟩ := Set.not_subset.mp hUnotJ
    have hu2 : u * u = 1 := elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet hV hU) hu
    have hex : ∀ w ∈ U ⊓ iSub U H E, ∃ a ∈ iSub U H E, ⁅a, u⁆ = w :=
      exists_commutator_eq_of_mem_inf_iSub (V := U) (isElemAbelian_of_mem_omegaSet hV hU)
        (isTI_of_mem_omegaSet hU hTI) hEH hEnorm hOmU hUbase hN hu
        (by rw [hIeq]; intro h; exact huJ (hIJ h))
    have hfix : ∀ x ∈ X, x⁻¹ * (u * x * u⁻¹) ∈ J →
        ∃ y ∈ X, u * y = y * u ∧ x⁻¹ * y ∈ J := by
      intro x hxX hxJ
      have hxJ' : x⁻¹ * u * x * u⁻¹ ∈ J := by
        rwa [show x⁻¹ * (u * x * u⁻¹) = x⁻¹ * u * x * u⁻¹ by group] at hxJ
      have hJfix : conjSubgroup J x = J :=
        conjSubgroup_eq_iff_mem_normalizer.mpr
          (le_normalizer_of_subgroupOf_normal hJleH hJnorm (hXH hxX))
      have hxux : x⁻¹ * u * x ∈ U ⊔ J := by
        have h : x⁻¹ * u * x = (x⁻¹ * u * x * u⁻¹) * u := by group
        rw [h]
        exact (U ⊔ J).mul_mem (Subgroup.mem_sup_right hxJ') (Subgroup.mem_sup_left hu)
      have hxN : x ∈ Subgroup.normalizer ((U ⊔ J : Subgroup G) : Set G) :=
        mem_normalizer_sup_of_conj_mem hJfix hUJ2 hu huJ hxux
      obtain ⟨m, hm, j, hj, hxmj⟩ :=
        seven_three_four_normalizer (V := U) (H := H) (E := E) (J := J)
          (isElemAbelian_of_mem_omegaSet hV hU) (isTI_of_mem_omegaSet hU hTI) hE hEH hEnorm
          hUbase hOmU hJ hJnorm (by rw [hIeq]; exact hIJ) (hXH hxX) hxN
      have hmH : m ∈ H := (Subgroup.mem_inf.mp hm).1
      have hmN : m ∈ Subgroup.normalizer (U : Set G) := (Subgroup.mem_inf.mp hm).2
      have hmX : m ∈ X := by
        have h : m = x * j⁻¹ := by rw [hxmj]; group
        rw [h]
        exact X.mul_mem hxX (X.inv_mem (hJX hj))
      have hrU : m⁻¹ * u * m * u⁻¹ ∈ U := by
        have h1 : m⁻¹ * u * m ∈ U := by
          have h2 : m⁻¹ * u * (m⁻¹)⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp
              ((Subgroup.normalizer (U : Set G)).inv_mem hmN) u).mp hu
          rwa [inv_inv] at h2
        exact U.mul_mem h1 (U.inv_mem hu)
      have hjuj : j * u * j⁻¹ * u⁻¹ ∈ J := by
        have hJu : u ∈ Subgroup.normalizer (J : Set G) :=
          le_normalizer_of_subgroupOf_normal hJleH hJnorm (hOmH U hU hu)
        have hmem : u * j⁻¹ * u⁻¹ ∈ J :=
          (Subgroup.mem_normalizer_iff.mp hJu j⁻¹).mp (J.inv_mem hj)
        have := J.mul_mem hj hmem
        rwa [show j * (u * j⁻¹ * u⁻¹) = j * u * j⁻¹ * u⁻¹ by group] at this
      have hJj : j ∈ Subgroup.normalizer (J : Set G) :=
        le_normalizer_of_subgroupOf_normal hJleH hJnorm (hJleH hj)
      have hxmJ : m⁻¹ * u * m * (j * u * j⁻¹)⁻¹ ∈ J := by
        have hconj : j * (x⁻¹ * u * x * u⁻¹) * j⁻¹ ∈ J :=
          (Subgroup.mem_normalizer_iff.mp hJj (x⁻¹ * u * x * u⁻¹)).mp hxJ'
        rw [hxmj] at hconj
        convert hconj using 1 <;> group
      have hrJ : m⁻¹ * u * m * u⁻¹ ∈ J := by
        have := J.mul_mem hxmJ hjuj
        rwa [show (m⁻¹ * u * m * (j * u * j⁻¹)⁻¹) * (j * u * j⁻¹ * u⁻¹) =
          m⁻¹ * u * m * u⁻¹ by group] at this
      have hrI : m⁻¹ * u * m * u⁻¹ ∈ U ⊓ iSub V H E := by
        rw [inf_iSub_eq_inf_J hU hIJ hJ]
        exact ⟨hrU, hrJ⟩
      have hrI' : m⁻¹ * u * m * u⁻¹ ∈ U ⊓ iSub U H E := by
        rw [hIeq]
        exact hrI
      obtain ⟨a, ha, haeq⟩ := hex (m⁻¹ * u * m * u⁻¹) hrI'
      have haI : a ∈ iSub V H E := hIeq ▸ ha
      have haX : a ∈ X := hJX (hIJ haI)
      have haeq' : a * u * a⁻¹ * u⁻¹ = m⁻¹ * u * m * u⁻¹ := by
        rw [← haeq, commutatorElement_def]
      have hcomm : u * (m * a) = (m * a) * u := by
        have h1 : u * m = m * a * u * a⁻¹ := by
          calc u * m = m * (m⁻¹ * u * m * u⁻¹) * u := by group
            _ = m * (a * u * a⁻¹ * u⁻¹) * u := by rw [← haeq']
            _ = m * a * u * a⁻¹ := by group
        calc u * (m * a) = (u * m) * a := by group
          _ = (m * a * u * a⁻¹) * a := by rw [h1]
          _ = (m * a) * u := by group
      refine ⟨m * a, X.mul_mem hmX haX, hcomm, ?_⟩
      have hy : x⁻¹ * (m * a) = j⁻¹ * a := by rw [hxmj]; group
      rw [hy]
      exact J.mul_mem (J.inv_mem hj) (hIJ haI)
    have hJ2 : IsPGroup 2 J := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le hJ
    obtain ⟨S, hSX, hSinf, hSsup, huS⟩ :=
      exists_complement_normalized_of_involution (X := X) (Y := J) (a := u)
        hJX hJ2 hXodd hXnil hu2 (hAX (hUleA hu)) hfix
    have hIrel : (iSub V H E).relIndex Y = J.relIndex X := by
      rw [← hYJ, Subgroup.inf_relIndex_left]
      have h1 : (J.subgroupOf X).relIndex ((Y.subgroupOf X) ⊔ (J.subgroupOf X)) =
          (J.subgroupOf X).relIndex (Y.subgroupOf X) :=
        Subgroup.relIndex_sup_right (H := Y.subgroupOf X) (K := J.subgroupOf X)
      rw [← Subgroup.subgroupOf_sup hYX hJX, hYJX, Subgroup.subgroupOf_self,
        Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hYX] at h1
      exact h1.symm
    have hI2 : IsPGroup 2 (iSub V H E) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le (hIJ.trans hJ)
    obtain ⟨kI, hkI⟩ := IsPGroup.iff_card.mp hI2
    have hcopI : Nat.Coprime (Nat.card (iSub V H E)) ((iSub V H E).relIndex Y) := by
      rw [hIrel, hkI]
      exact (Nat.coprime_two_right.mpr hXodd).symm.pow_left kI
    obtain ⟨S', hS'Y, hS'inf, hS'sup, -⟩ :=
      CFSG.Walter.W67.Sec6.exists_complement_in (C := iSub V H E) (N := Y) hIY
        ((hYX.trans hXH).trans (le_normalizer_of_subgroupOf_normal hIleH hInorm)) hcopI
    have hS'X : S' ≤ X := hS'Y.trans hYX
    have hS'infJ : S' ⊓ J = ⊥ := by
      have hle : S' ⊓ J ≤ iSub V H E := (inf_le_inf hS'Y le_rfl).trans (le_of_eq hYJ)
      have h2 : S' ⊓ J ≤ iSub V H E ⊓ S' := le_inf hle inf_le_left
      rw [hS'inf] at h2
      exact le_bot_iff.mp h2
    have hS'supJ : S' ⊔ J = X := by
      rw [← hYJX, ← hS'sup]
      rw [sup_comm (iSub V H E) S', sup_assoc, sup_eq_right.mpr hIJ]
    obtain ⟨kJ, hkJ⟩ := IsPGroup.iff_card.mp hJ2
    have hcopJ : Nat.Coprime (Nat.card J) (J.relIndex X) := by
      rw [hkJ]
      exact (Nat.coprime_two_right.mpr hXodd).symm.pow_left kJ
    obtain ⟨c, hcJ, hc⟩ := CFSG.Walter.W67.Sec6.exists_conj_complement_in
      (C := J) (N := X) (W₁ := S) (W₂ := S') hJX
      (hXH.trans (le_normalizer_of_subgroupOf_normal hJleH hJnorm)) hcopJ hSX hS'X
      (by rw [inf_comm]; exact hSinf) (by rw [sup_comm]; exact hSsup)
      (by rw [inf_comm]; exact hS'infJ) (by rw [sup_comm]; exact hS'supJ)
    have hcH : c ∈ H := hJleH hcJ
    have hIfix : conjSubgroup (iSub V H E) c⁻¹ = iSub V H E :=
      conjSubgroup_eq_iff_mem_normalizer.mpr
        (le_normalizer_of_subgroupOf_normal hIleH hInorm (hJleH (J.inv_mem hcJ)))
    have hScj : conjSubgroup S c⁻¹ = S' := by
      rw [CFSG.Quasithin.conjSubgroup, inv_inv]
      exact hc.symm
    have hYeq : conjSubgroup (S ⊔ iSub V H E) c⁻¹ = Y := by
      have h1 : conjSubgroup (S ⊔ iSub V H E) c⁻¹ =
          conjSubgroup S c⁻¹ ⊔ conjSubgroup (iSub V H E) c⁻¹ := by
        simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_sup]
      rw [h1, hScj, hIfix, sup_comm S' (iSub V H E), hS'sup]
    have huNSI : u ∈ Subgroup.normalizer ((S ⊔ iSub V H E : Subgroup G) : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer]
      have h1 : conjSubgroup (S ⊔ iSub V H E) u =
          conjSubgroup S u ⊔ conjSubgroup (iSub V H E) u := by
        simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_sup]
      rw [h1, conjSubgroup_eq_iff_mem_normalizer.mpr huS,
        conjSubgroup_eq_iff_mem_normalizer.mpr
          (le_normalizer_of_subgroupOf_normal hIleH hInorm (hOmH U hU hu))]
    have hUnorm : U ≤ Subgroup.normalizer ((S ⊔ iSub V H E : Subgroup G) : Set G) := by
      have hUle : U ≤ (U ⊓ J) ⊔ Subgroup.zpowers u :=
        le_sup_zpowers_of_relIndex_eq_two inf_le_left hUJ2 hu
          (fun h => huJ (Subgroup.mem_inf.mp h).2)
      refine hUle.trans ?_
      refine sup_le ?_ ?_
      · calc U ⊓ J = U ⊓ iSub V H E := (inf_iSub_eq_inf_J hU hIJ hJ).symm
          _ ≤ iSub V H E := inf_le_right
          _ ≤ S ⊔ iSub V H E := le_sup_right
          _ ≤ Subgroup.normalizer ((S ⊔ iSub V H E : Subgroup G) : Set G) :=
              Subgroup.le_normalizer
      · exact Subgroup.zpowers_le.mpr huNSI
    have hU'N : conjSubgroup U c⁻¹ ≤ Subgroup.normalizer (Y : Set G) := by
      calc conjSubgroup U c⁻¹
          ≤ conjSubgroup (Subgroup.normalizer ((S ⊔ iSub V H E : Subgroup G) : Set G)) c⁻¹ :=
            Subgroup.map_mono hUnorm
        _ = Subgroup.normalizer (conjSubgroup (S ⊔ iSub V H E) c⁻¹ : Set G) :=
            conjSubgroup_normalizer (S ⊔ iSub V H E) c⁻¹
        _ = Subgroup.normalizer (Y : Set G) := by rw [hYeq]
    have hU'Om : conjSubgroup U c⁻¹ ∈ omegaSet V H E :=
      conjSubgroup_mem_omegaSet hEH hEnorm hU (H.inv_mem hcH)
    have hU'AJ : conjSubgroup U c⁻¹ ≤ A ⊔ J := by
      calc conjSubgroup U c⁻¹ ≤ conjSubgroup (U ⊔ J) c⁻¹ := Subgroup.map_mono le_sup_left
        _ = U ⊔ J := conjSubgroup_eq_iff_mem_normalizer.mpr
            (Subgroup.le_normalizer (Subgroup.mem_sup_right (J.inv_mem hcJ)))
        _ ≤ A ⊔ J := sup_le (hUleA.trans le_sup_left) le_sup_right
    have hUleU'J : U ≤ conjSubgroup U c⁻¹ ⊔ J := by
      intro u₀ hu₀
      have hcu₀ : c * u₀ * c⁻¹ ∈ conjSubgroup U c⁻¹ :=
        mem_conjSubgroup_iff.mpr (by
          rw [show c⁻¹ * (c * u₀ * c⁻¹) * (c⁻¹)⁻¹ = u₀ by group]
          exact hu₀)
      have hmem : c⁻¹ * (c * u₀ * c⁻¹) * c ∈ conjSubgroup U c⁻¹ ⊔ J :=
        (conjSubgroup U c⁻¹ ⊔ J).mul_mem
          ((conjSubgroup U c⁻¹ ⊔ J).mul_mem (Subgroup.mem_sup_right (J.inv_mem hcJ))
            (Subgroup.mem_sup_left hcu₀))
          (Subgroup.mem_sup_right hcJ)
      rwa [show c⁻¹ * (c * u₀ * c⁻¹) * c = u₀ by group] at hmem
    have hU'R : conjSubgroup U c⁻¹ ≤ R := by
      rw [hR]
      exact le_iSup_of_le (conjSubgroup U c⁻¹)
        (le_iSup_of_le hU'Om (le_iSup_of_le hU'AJ (le_iSup_of_le hU'N le_rfl)))
    exact hUleU'J.trans (sup_le_sup_right hU'R J)
  · rw [hR]
    refine sup_le ?_ le_sup_right
    refine iSup_le fun U => iSup_le fun _ => iSup_le fun hUleAJ => iSup_le fun _ => hUleAJ

end CFSG.LocalAnalysis.WeakClosure81
