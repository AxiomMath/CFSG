module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwo2
public import CFSG.Quasithin.Recognition.Stroth.Str83G4C2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str83G4_c23_sup_left_eq_sup_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
  obtain ⟨hF, hB, ha, ⟨e⟩, -, -⟩ := hfr
  exact sup_eq_of_S_eq (eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨e⟩⟩))

private theorem str83G4_c23_sup_le_centralizer_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  rw [str83G4_c23_sup_left_eq_sup_q1 hfr]
  exact hfr.2.2.2.2.2

private theorem str83G4_c23_isNormalIn_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (Q1 L1 L2 S) := by
  have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S := sup_left_le_p1 L1 L2 S
  exact ⟨le_rfl, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S) (hHleP1 hg)) x).mp hx⟩

private theorem str83G4_c23_isNormalIn_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (Z1 L1 L2 S) := by
  have hZ1Q1 : Z1 L1 L2 S ≤ Q1 L1 L2 S := A4.omegaOneCenterOf_le (Q1 L1 L2 S)
  have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S := sup_left_le_p1 L1 L2 S
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)
  exact ⟨hZ1Q1, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hP1N (hHleP1 hg)) x).mp hx⟩

private theorem str83G4_c23_isNormalIn_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (str83X L1 L2 S) := by
  have hXQ1 : str83X L1 L2 S ≤ Q1 L1 L2 S := str83X_le_q1 hfr
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  exact ⟨hXQ1, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHN hg) x).mp hx⟩

private theorem str83G4_c23_commutator_x_oTwo_le_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hY : twoResidual (L1 ⊔ S) ≤
      centralizerMod (str83Y L1 L2 S) (L1 ⊔ S) (Q1 L1 L2 S)) :
    ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ Z1 L1 L2 S := by
  classical
  set H : Subgroup G := L1 ⊔ S with hH
  set X : Subgroup G := str83X L1 L2 S with hXdef
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  set Z1s : Subgroup G := Z1 L1 L2 S with hZ1def
  set Ys : Subgroup G := str83Y L1 L2 S with hYdef
  have hQH : Q ≤ H := by rw [hQ, hH]; exact (str83G4_q1_le_s hfr).trans le_sup_right
  have hXQ : X ≤ Q := by rw [hXdef, hQ]; exact str83X_le_q1 hfr
  have hYsQ : Ys ≤ Q := by rw [hYdef, hQ]; exact inf_le_left
  have hYsX : Ys ≤ Subgroup.centralizer (X : Set G) := by
    rw [hYdef, hXdef]; exact inf_le_right
  have hQZ1 : Q ≤ Subgroup.centralizer (Z1s : Set G) := by
    rw [hQ, hZ1def]
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)
  have hZ1Q : Z1s ≤ Subgroup.centralizer (Q : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hQZ1 hy) z hz).symm
  have hZ1CX : Z1s ≤ Subgroup.centralizer (X : Set G) := by
    intro z hz
    have hz' : z ∈ Z1 L1 L2 S := by rwa [hZ1def] at hz
    have h := (str83G4_z1_le_center_x hfr hz').2
    show z ∈ Subgroup.centralizer (X : Set G)
    rwa [← hXdef] at h
  have hXCZ1 : X ≤ Subgroup.centralizer (Z1s : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZ1CX hz) v hv).symm
  have hHNX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hH, hXdef]
    exact (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)
  have hHZ1 : H ≤ Subgroup.centralizer (Z1s : Set G) := by
    rw [hH, hZ1def, str83G4_c23_sup_left_eq_sup_q1 hfr]
    exact hfr.2.2.2.2.2
  have hHNY : H ≤ Subgroup.normalizer (Ys : Set G) := by
    rw [hH, hYdef]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (str83G4_isNormalIn_y hfr).2 g hg y hy
    · intro hy
      have h1 := (str83G4_isNormalIn_y hfr).2 g⁻¹ (H.inv_mem hg) (g * y * g⁻¹) hy
      simpa [mul_assoc] using h1
  refine Subgroup.commutator_le.mpr fun x hx g hg => ?_
  rw [← F6.twoResidual_eq_oTwoUpper] at hg
  have hgH : g ∈ H := twoResidual_le H hg
  have hgNX : g ∈ Subgroup.normalizer (X : Set G) := hHNX hgH
  have hgZ1 : g ∈ Subgroup.centralizer (Z1s : Set G) := hHZ1 hgH
  have hxgX : g * x * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hgNX x).mp hx
  have huX : g * x * g⁻¹ * x⁻¹ ∈ X := X.mul_mem hxgX (X.inv_mem hx)
  have hu2 : (g * x * g⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹) = 1 := by
    have h := (B6.isElemAbelian_iff.mp hX).2 _ huX
    simpa [pow_two] using h
  have huCent : ∀ y ∈ Q, y * (g * x * g⁻¹ * x⁻¹) = (g * x * g⁻¹ * x⁻¹) * y := by
    intro y hy
    have hxyZ : x * y * x⁻¹ * y⁻¹ ∈ Z1s :=
      str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx hy)
    have hgfix : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp hgZ1 _ hxyZ
      rw [← h]
      group
    have hcY : g * y * g⁻¹ * y⁻¹ ∈ Ys := (hY hg).2.2 y hy
    have hcX : (g * x * g⁻¹) * (g * y * g⁻¹ * y⁻¹) =
        (g * y * g⁻¹ * y⁻¹) * (g * x * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hYsX hcY) (g * x * g⁻¹) hxgX
    have hcZ : (g * y * g⁻¹ * y⁻¹) * ⁅g * x * g⁻¹, y⁆ *
        (g * y * g⁻¹ * y⁻¹)⁻¹ = ⁅g * x * g⁻¹, y⁆ := by
      have hmem : ⁅g * x * g⁻¹, y⁆ ∈ Z1s :=
        str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hxgX hy)
      have h := Subgroup.mem_centralizer_iff.mp (hQZ1 (hYsQ hcY)) _ hmem
      rw [← h]
      group
    have h1 : (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ *
        (g * y * g⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      rw [← hgfix]
      group
    have h2 : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    have h3 : (g * x * g⁻¹) * ((g * y * g⁻¹ * y⁻¹) * y) * (g * x * g⁻¹)⁻¹ *
        ((g * y * g⁻¹ * y⁻¹) * y)⁻¹ =
        (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ * y⁻¹ := by
      change ⁅g * x * g⁻¹, (g * y * g⁻¹ * y⁻¹) * y⁆ = ⁅g * x * g⁻¹, y⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc1 : ⁅g * x * g⁻¹, g * y * g⁻¹ * y⁻¹⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hcX
      rw [hc1, one_mul]
      exact hcZ
    have heq : (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
        x * y * x⁻¹ * y⁻¹ := by
      rw [← h3, ← h2]
      exact h1
    have hux : (g * x * g⁻¹ * x⁻¹) * x = g * x * g⁻¹ := by group
    have hconj0 : (g * x * g⁻¹ * x⁻¹) * (x * y * x⁻¹ * y⁻¹) *
        (g * x * g⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      have h := Subgroup.mem_centralizer_iff.mp (hXCZ1 huX) _ hxyZ
      rw [← h]
      group
    have hconj : (g * x * g⁻¹ * x⁻¹) * ⁅x, y⁆ * (g * x * g⁻¹ * x⁻¹)⁻¹ = ⁅x, y⁆ := by
      simpa [commutatorElement_def] using hconj0
    have hmul := commutatorElement_mul_left_eq_conj_mul
      (a := g * x * g⁻¹ * x⁻¹) (b := x) (c := y)
    rw [hux, hconj] at hmul
    have heq' : ⁅g * x * g⁻¹, y⁆ = ⁅x, y⁆ := by
      simpa [commutatorElement_def] using heq
    rw [heq'] at hmul
    have huy : ⁅g * x * g⁻¹ * x⁻¹, y⁆ = 1 := by
      have h1 := congrArg (fun t => ⁅x, y⁆⁻¹ * t) hmul
      simpa [mul_assoc] using h1.symm
    exact ((commutatorElement_eq_one_iff_mul_comm).mp huy).symm
  have huMemZ : g * x * g⁻¹ * x⁻¹ ∈ Z1s := by
    have huCentQ : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact huCent
    have huCenter : g * x * g⁻¹ * x⁻¹ ∈ centerOf Q := ⟨hXQ huX, huCentQ⟩
    exact Subgroup.subset_closure ⟨huCenter, by simpa [pow_two] using hu2⟩
  have hcomm : ⁅x, g⁆ = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  exact Z1s.inv_mem huMemZ

theorem str83G4_not_twoResidual_le_centralizerMod_y_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (str83Y L1 L2 S) (L1 ⊔ S) (Q1 L1 L2 S) := by
  classical
  intro hY
  have hXZ : ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ Z1 L1 L2 S :=
    str83G4_c23_commutator_x_oTwo_le_z1 hfr d hX hY
  obtain ⟨L, N, hstep, hZ1L, hnc⟩ := str83G4_exists_chiefStep hfr
  apply hnc
  intro g hg
  refine ⟨twoResidual_le (L1 ⊔ S) hg,
    D14.le_normalizer_of_isNormalIn hstep.2.1 (twoResidual_le (L1 ⊔ S) hg), fun n hn => ?_⟩
  have hmem : ⁅n, g⁆ ∈ ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ :=
    Subgroup.commutator_mem_commutator (hstep.1.1 hn)
      (by rwa [← F6.twoResidual_eq_oTwoUpper])
  have hmemZ : ⁅n, g⁆ ∈ Z1 L1 L2 S := hXZ hmem
  have e : g * n * g⁻¹ * n⁻¹ = ⁅n, g⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hZ1L ((Z1 L1 L2 S).inv_mem hmemZ)

private theorem str83G4_c23_eta_values
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    F112W.eta (L1 ⊔ S) (Q1 L1 L2 S) (Q1 L1 L2 S) = 2 ∧
    F112W.eta (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) = 1 ∧
    F112W.eta (L1 ⊔ S) (Q1 L1 L2 S) (str83X L1 L2 S) = 1 ∧
    F112W.eta (L1 ⊔ S) (Q1 L1 L2 S) (Z1 L1 L2 S) = 0 := by
  classical
  set H : Subgroup G := L1 ⊔ S with hH
  set Q : Subgroup G := Q1 L1 L2 S with hQ
  set X : Subgroup G := str83X L1 L2 S with hXdef
  set Y : Subgroup G := str83Y L1 L2 S with hYdef
  set Z1s : Subgroup G := Z1 L1 L2 S with hZ1def
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hQH : Q ≤ H := by rw [hQ, hH]; exact (str83G4_q1_le_s hfr).trans le_sup_right
  have hpCore : pCoreOf 2 H = Q := by rw [hH, hQ]; exact str83G4_pCoreOf_sup_left hfr
  have hQcore : Q ≤ pCoreOf 2 H := hpCore.ge
  have hQn : IsNormalIn H Q Q := by rw [hH, hQ]; exact str83G4_c23_isNormalIn_q1 hfr
  have hZ1n : IsNormalIn H Q Z1s := by
    rw [hH, hQ, hZ1def]; exact str83G4_c23_isNormalIn_z1 hfr
  have hXn : IsNormalIn H Q X := by
    rw [hH, hQ, hXdef]; exact str83G4_c23_isNormalIn_x hfr
  have hYn : IsNormalIn H Q Y := by
    rw [hH, hQ, hYdef]; exact str83G4_isNormalIn_y hfr
  have hXQ : X ≤ Q := by rw [hXdef, hQ]; exact str83X_le_q1 hfr
  have hYQ : Y ≤ Q := by rw [hYdef, hQ]; exact inf_le_left
  have hZ1Q : Z1s ≤ Q := by
    rw [hZ1def, hQ]; exact A4.omegaOneCenterOf_le (Q1 L1 L2 S)
  have hXY : X ≤ Y := by rw [hXdef, hYdef]; exact str83X_le_str83Y hfr hX
  have hZ1comm : ⁅Z1s, oTwoUpper H⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h := Subgroup.mem_centralizer_iff.mp
      (str83G4_c23_sup_le_centralizer_z1 hfr (oTwoUpper_le H hw)) z hz
    exact h.symm
  have hetaZ : F112W.eta H Q Z1s = 0 :=
    (F112W.eta_eq_zero_iff hQH hQcore hZ1n).mpr hZ1comm
  have hetaX : F112W.eta H Q X = 1 := by
    have h1 : IsChiefSeriesFrom H Q X (F112W.eta H Q X) := F112W.isChiefSeriesFrom_eta hQH hXn
    have h2 : IsChiefSeriesFrom H X X (F112W.eta H Q X) :=
      isChiefSeriesFrom_of_le_module hXQ le_rfl h1
    exact str83G4_chiefSeries_x_eq_one hfr d hX hB h2
  obtain ⟨t, ht, htQ⟩ : ∃ t : G, t ∈ CFSG.conjugate X d.w ∧ t ∉ Q := by
    by_contra h
    apply hB
    intro x hx
    by_contra hxQ
    exact h ⟨x, hx, hxQ⟩
  have hWleS : CFSG.conjugate X d.w ≤ S := by
    rw [hXdef]; exact str83G4_conjugate_x_le_s hfr d hX
  have hWabel : IsElemAbelian 2 (CFSG.conjugate X d.w) := by
    rw [hXdef]; exact str83G4_isElemAbelian_conjugate_x d hX
  have ht2 : t * t = 1 := by
    have h := (B6.isElemAbelian_iff.mp hWabel).2 t ht
    simpa [pow_two] using h
  have htH : t ∈ H := by
    rw [hH]
    exact (le_sup_right : S ≤ L1 ⊔ S) (hWleS ht)
  have hU : IsPGroup 2 Q := by rw [hQ]; exact pCoreOf_isPGroup 2 (P1 L1 L2 S)
  have hserQ : IsChiefSeriesFrom H Q Q (F112W.eta H Q Q) := F112W.isChiefSeriesFrom_eta hQH hQn
  have hM6 := pow_sq_le_relIndex_centralizer (H := H) (U := Q) (q := q)
    (c := F112W.eta H Q Q) (str83G4_isSzU3Quot_sup_left hfr) hU hQH hserQ htH
    (by rw [hpCore, ht2]; exact Q.one_mem)
    (by rw [hpCore]; exact htQ)
  have hCq : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex Q =
      q ^ 4 := by
    have h := str83G4_relIndex_centralizer_q1 hfr d hX ht htQ
    rw [hq]
    exact h
  have hq2gt1 : 1 < q ^ 2 := by
    rw [hq, ← pow_mul]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hetaQle : F112W.eta H Q Q ≤ 2 := by
    have h : (q ^ 2) ^ F112W.eta H Q Q ≤ (q ^ 2) ^ 2 := by
      rw [hCq] at hM6
      rwa [show q ^ 4 = (q ^ 2) ^ 2 by ring] at hM6
    exact (Nat.pow_le_pow_iff_right hq2gt1).mp h
  obtain ⟨cY, hserY⟩ := F112W.exists_isChiefSeriesBetween hYn Q hQn hYQ
  have hcYpos : 1 ≤ cY := by
    rcases Nat.eq_zero_or_pos cY with h0 | hpos
    · exfalso
      have hcomm : ⁅Q, oTwoUpper H⁆ ≤ Y :=
        (F112W.isChiefSeriesBetween_zero_iff hQH hQcore hYn hQn hYQ).mp (h0 ▸ hserY)
      have hYmem : twoResidual H ≤ centralizerMod Y H Q := by
        intro g hg
        have hgO : g ∈ oTwoUpper H := by rwa [F6.twoResidual_eq_oTwoUpper] at hg
        refine ⟨twoResidual_le H hg,
          D14.le_normalizer_of_isNormalIn hYn (twoResidual_le H hg), fun u hu => ?_⟩
        have hmem : ⁅u, g⁆ ∈ Y := Subgroup.commutator_le.mp hcomm u hu g hgO
        have e : g * u * g⁻¹ * u⁻¹ = ⁅u, g⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Y.inv_mem hmem
      exact str83G4_not_twoResidual_le_centralizerMod_y_q1 hfr d hX hYmem
    · exact hpos
  obtain ⟨cXY, hserXY⟩ := F112W.exists_isChiefSeriesBetween hXn Y hYn hXY
  have hetaYX : F112W.eta H Q Y = F112W.eta H Q X + cXY :=
    F112W.eta_eq_add hQH hXn hserXY
  have hetaQY : F112W.eta H Q Q = F112W.eta H Q Y + cY :=
    F112W.eta_eq_add hQH hYn hserY
  have hetaQeq : F112W.eta H Q Q = 1 + cXY + cY := by
    rw [hetaQY, hetaYX, hetaX]
  have hsum : cXY + cY ≤ 1 := by omega
  have hcXY : cXY = 0 := by omega
  have hcY : cY = 1 := by omega
  have hetaY : F112W.eta H Q Y = 1 := by rw [hetaYX, hetaX, hcXY]
  have hetaQ : F112W.eta H Q Q = 2 := by rw [hetaQeq, hcXY, hcY]
  exact ⟨hetaQ, hetaY, hetaX, hetaZ⟩

theorem str83G4_commutator_y_oTwoUpper_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ⁅str83Y L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ str83X L1 L2 S := by
  have hvals := str83G4_c23_eta_values hfr d hX hB
  have hQH : Q1 L1 L2 S ≤ L1 ⊔ S := (str83G4_q1_le_s hfr).trans le_sup_right
  have hQcore : Q1 L1 L2 S ≤ pCoreOf 2 (L1 ⊔ S) :=
    (str83G4_pCoreOf_sup_left hfr).symm.le
  have hXn : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (str83X L1 L2 S) :=
    str83G4_c23_isNormalIn_x hfr
  have hYn : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) :=
    str83G4_isNormalIn_y hfr
  have hXY : str83X L1 L2 S ≤ str83Y L1 L2 S := str83X_le_str83Y hfr hX
  obtain ⟨c, hser⟩ := F112W.exists_isChiefSeriesBetween hXn (str83Y L1 L2 S) hYn hXY
  have h := F112W.eta_eq_add hQH hXn hser
  rw [hvals.2.1, hvals.2.2.1] at h
  have hc : c = 0 := by omega
  exact (F112W.isChiefSeriesBetween_zero_iff hQH hQcore hXn hYn hXY).mp (hc ▸ hser)

theorem str83G4_chiefSeriesBetween_y_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) {c : ℕ}
    (hser : F112W.IsChiefSeriesBetween (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S)
      (Q1 L1 L2 S) c) : c = 1 := by
  have hvals := str83G4_c23_eta_values hfr d hX hB
  have hQH : Q1 L1 L2 S ≤ L1 ⊔ S := (str83G4_q1_le_s hfr).trans le_sup_right
  have hYn : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) :=
    str83G4_isNormalIn_y hfr
  have h := F112W.eta_eq_add hQH hYn hser
  rw [hvals.1, hvals.2.1] at h
  omega

end CFSG.Quasithin.Stroth

end
