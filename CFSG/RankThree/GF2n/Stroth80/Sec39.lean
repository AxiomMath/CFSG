module

public import CFSG.RankThree.GF2n.Stroth80.Sec36

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec39_Vt_le {M L B Z : Subgroup G} {t : G} {S : Subgroup G} (hZ : Z ≤ S)
    (hB : ∀ m ∈ M, t ∈ conjSubgroup m L → conjSubgroup m B ≤ S) : Vt M L B Z t ≤ S := by
  unfold Vt
  exact sup_le hZ (iSup₂_le fun m hm => iSup_le fun hT => hB m hm hT)

theorem sec39_Z_le_Vt {M L B Z : Subgroup G} {t : G} : Z ≤ Vt M L B Z t := by
  unfold Vt
  exact le_sup_left

theorem sec39_conjB_le_Vt {M L B Z : Subgroup G} {t m : G} (hm : m ∈ M)
    (hT : t ∈ conjSubgroup m L) : conjSubgroup m B ≤ Vt M L B Z t := by
  unfold Vt
  exact le_sup_of_le_right (le_iSup₂_of_le m hm (le_iSup_of_le hT le_rfl))

theorem sec39_Q_le_LB {M Q B : Subgroup G} : Q ≤ LB M Q B := by
  unfold LB
  exact le_sup_left

theorem sec39_centralizer_symm {A K : Subgroup G} (h : A ≤ Subgroup.centralizer (K : Set G)) :
    K ≤ Subgroup.centralizer (A : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (h ha) k hk).symm

theorem le_Rt (L : Subgroup G) {t : G} (ht : t ∈ L) : L ≤ Rt M L t := by
  have hT : t ∈ conjSubgroup (1 : G) (L) := by
    rw [conjSubgroup_one]
    exact ht
  have hL : L ≤ conjSubgroup (1 : G) (L) :=
    le_of_eq (conjSubgroup_one _).symm
  unfold Rt
  exact hL.trans (le_iSup₂_of_le (1 : G) M.one_mem (le_iSup_of_le hT le_rfl))

theorem Ctx.Rt_le_M (hc : Ctx M Q Z B) (t : G) : Rt M (LB M Q B) t ≤ M := by
  unfold Rt
  refine iSup₂_le fun m hm => iSup_le fun hT => ?_
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h2 : m * (m⁻¹ * x * m) * m⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hm (hc.LB_le_M hx)) (M.inv_mem hm)
  rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h2

theorem Ctx.Q_le_Rt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Q ≤ Rt M (LB M Q B) t :=
  le_trans sec39_Q_le_LB (le_Rt (LB M Q B) ht)

theorem Ctx.Vt_le_Q (hc : Ctx M Q Z B) (t : G) : Vt M (LB M Q B) B Z t ≤ Q := by
  refine sec39_Vt_le hc.Z_le_Q fun m hm _ => ?_
  calc conjSubgroup m B ≤ conjSubgroup m Q := Subgroup.map_mono hc.le
    _ = Q := hc.conj_Q_eq hm

theorem Ctx.comm_QB_le_B (hc : Ctx M Q Z B) {s s' : G} (hs : s ∈ QB B) (hs' : s' ∈ QB B) :
    ⁅s, s'⁆ ∈ B := by
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have h1 : g⁻¹ * s * g ∈ Q := by
    rw [hQB] at hs
    exact mem_conjSubgroup.mp hs
  have h2 : g⁻¹ * s' * g ∈ Q := by
    rw [hQB] at hs'
    exact mem_conjSubgroup.mp hs'
  have h3 : ⁅g⁻¹ * s * g, g⁻¹ * s' * g⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V h1 h2
  have e : ⁅s, s'⁆ = g * ⁅g⁻¹ * s * g, g⁻¹ * s' * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e2 : g⁻¹ * (g * ⁅g⁻¹ * s * g, g⁻¹ * s' * g⁆ * g⁻¹) * g =
      ⁅g⁻¹ * s * g, g⁻¹ * s' * g⁆ := by
    group
  rw [e, hg, mem_conjSubgroup, e2]
  exact h3

theorem Ctx.commutator_LB_le_Q (hc : Ctx M Q Z B) : ⁅LB M Q B, LB M Q B⁆ ≤ Q := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB ha
  obtain ⟨s', hs', y', hy', rfl⟩ := hc.exists_mul_of_mem_LB hb
  have hsM : s ∈ M := hs.2
  have hs'M : s' ∈ M := hs'.2
  have hconj : ∀ g ∈ M, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) x).mp hx
  have hss : ⁅s, s'⁆ ∈ Q := hc.le (hc.comm_QB_le_B hs.1 hs'.1)
  have hA : ⁅s, y'⁆ ∈ Q := by
    have e : ⁅s, y'⁆ = (s * y' * s⁻¹) * y'⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    exact Q.mul_mem (hconj s hsM y' hy') (Q.inv_mem hy')
  have hE : ⁅y, s'⁆ ∈ Q := by
    have e : ⁅y, s'⁆ = y * (s' * y⁻¹ * s'⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hy (hconj s' hs'M y⁻¹ (Q.inv_mem hy))
  have hD : ⁅y, y'⁆ ∈ Q := by
    have e : ⁅y, y'⁆ = ((y * y') * y⁻¹) * y'⁻¹ := by
      rw [commutatorElement_def]
    rw [e]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hy hy') (Q.inv_mem hy)) (Q.inv_mem hy')
  have F1 : ⁅y, s'⁆ * (s' * ⁅y, y'⁆ * s'⁻¹) ∈ Q := Q.mul_mem hE (hconj s' hs'M _ hD)
  have F2 : ⁅s, s'⁆ * (s' * ⁅s, y'⁆ * s'⁻¹) ∈ Q := Q.mul_mem hss (hconj s' hs'M _ hA)
  have key : ⁅s * y, s' * y'⁆ = s * (⁅y, s'⁆ * (s' * ⁅y, y'⁆ * s'⁻¹)) * s⁻¹ *
      (⁅s, s'⁆ * (s' * ⁅s, y'⁆ * s'⁻¹)) := by
    simp only [commutatorElement_def]
    group
  rw [key]
  exact Q.mul_mem (hconj s hsM _ F1) F2

theorem Ctx.conj_LB_le_M (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    conjSubgroup m (LB M Q B) ≤ M := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h2 : m * (m⁻¹ * x * m) * m⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hm (hc.LB_le_M hx)) (M.inv_mem hm)
  rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h2

theorem Ctx.comm_mem_Q_of_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) {t r : G}
    (ht : t ∈ conjSubgroup m (LB M Q B)) (hr : r ∈ conjSubgroup m (LB M Q B)) :
    ⁅t, r⁆ ∈ Q := by
  rw [mem_conjSubgroup] at ht hr
  have h2 : ⁅m⁻¹ * t * m, m⁻¹ * r * m⁆ ∈ Q :=
    Subgroup.commutator_le.mp hc.commutator_LB_le_Q _ ht _ hr
  have e : ⁅m⁻¹ * t * m, m⁻¹ * r * m⁆ = m⁻¹ * ⁅t, r⁆ * m := by
    simp only [commutatorElement_def]
    group
  rw [e] at h2
  have h3 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm)
    (m⁻¹ * ⁅t, r⁆ * m)).mp h2
  have e2 : m * (m⁻¹ * ⁅t, r⁆ * m) * m⁻¹ = ⁅t, r⁆ := by group
  rw [e2] at h3
  exact h3

theorem Ctx.Rt_normalizes_Vt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
  have hstep : ∀ m' ∈ M, ∀ _ : t ∈ conjSubgroup m' (LB M Q B),
      ∀ r ∈ conjSubgroup m' (LB M Q B),
      Vt M (LB M Q B) B Z t ≤ Subgroup.comap (MulAut.conj r).toMonoidHom
        (Vt M (LB M Q B) B Z t) := by
    intro m' hm' ht' r hr
    have hrM : r ∈ M := hc.conj_LB_le_M hm' hr
    refine sec39_Vt_le ?_ fun m hm hT => ?_
    · intro z hz
      show r * z * r⁻¹ ∈ Vt M (LB M Q B) B Z t
      exact sec39_Z_le_Vt ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrM) z).mp hz)
    · intro x hx
      show r * x * r⁻¹ ∈ Vt M (LB M Q B) B Z t
      have hcommQ : ⁅r⁻¹, t⁆ ∈ Q := hc.comm_mem_Q_of_conj hm' (Subgroup.inv_mem _ hr) ht'
      have hQ' : m⁻¹ * ⁅r⁻¹, t⁆ * m ∈ Q := by
        have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hm))
          ⁅r⁻¹, t⁆).mp hcommQ
        rw [inv_inv] at h
        exact h
      have hTr : t ∈ conjSubgroup (r * m) (LB M Q B) := by
        rw [mem_conjSubgroup] at hT ⊢
        have e : (r * m)⁻¹ * t * (r * m) = (m⁻¹ * ⁅r⁻¹, t⁆ * m) * (m⁻¹ * t * m) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (LB M Q B).mul_mem (sec39_Q_le_LB hQ') hT
      have hmem : r * x * r⁻¹ ∈ conjSubgroup (r * m) B := by
        rw [conjSubgroup_mul, mem_conjSubgroup]
        have e : r⁻¹ * (r * x * r⁻¹) * r = x := by group
        rw [e]
        exact hx
      exact sec39_conjB_le_Vt (M.mul_mem hrM hm) hTr hmem
  unfold Rt
  refine iSup₂_le fun m' hm' => iSup_le fun ht' => ?_
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hstep m' hm' ht' r hr hx
  · intro hx
    have h1 : r⁻¹ * (r * x * r⁻¹) * r⁻¹⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      hstep m' hm' ht' r⁻¹ (Subgroup.inv_mem _ hr) hx
    have e : r⁻¹ * (r * x * r⁻¹) * r⁻¹⁻¹ = x := by group
    rw [e] at h1
    exact h1

theorem Ctx.Vt_comm (hc : Ctx M Q Z B)
    (h352 : ∀ m ∈ M, CQt Q Z (LB M Q (conjSubgroup m B)) =
      ((conjSubgroup m B ⊔ Z : Subgroup G) : Set G))
    {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q) :
    ∀ x ∈ Vt M (LB M Q B) B Z t, ∀ y ∈ Vt M (LB M Q B) B Z t, x * y = y * x := by
  have hBQ : ∀ m ∈ M, conjSubgroup m B ≤ Q := fun m hm => (hc.conj_of_mem hm).le
  have hpair : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) → ∀ m' ∈ M,
      t ∈ conjSubgroup m' (LB M Q B) → ∀ b ∈ conjSubgroup m B, ∀ c ∈ conjSubgroup m' B,
        b * c = c * b := by
    intro m hm hTm m' hm' hTm' b hb c hc'
    have hcm := hc.conj_of_mem hm
    have hne : conjSubgroup (m' * m⁻¹) (LB M Q (conjSubgroup m B)) ⊓
        Subgroup.normalizer (LB M Q (conjSubgroup m B) : Set G) ≠ Q := by
      intro hne'
      have htL : t ∈ conjSubgroup (m' * m⁻¹) (LB M Q (conjSubgroup m B)) ⊓
          Subgroup.normalizer (LB M Q (conjSubgroup m B) : Set G) := by
        refine ⟨?_, ?_⟩
        · rw [hc.LB_conj hm, ← conjSubgroup_mul, inv_mul_cancel_right]
          exact hTm'
        · rw [hc.LB_conj hm]
          exact Subgroup.le_normalizer hTm
      rw [hne'] at htL
      exact htQ htL
    have key := stroth_3_6_of_3_5 hcm (h352 m hm) (M.mul_mem hm' (M.inv_mem hm)) hne
    have e : conjSubgroup (m' * m⁻¹) (conjSubgroup m B) = conjSubgroup m' B := by
      rw [← conjSubgroup_mul, inv_mul_cancel_right]
    exact key b hb c (by rw [e]; exact hc')
  have hcent1 : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) →
      Vt M (LB M Q B) B Z t ≤ Subgroup.centralizer (conjSubgroup m B : Set G) := by
    intro m hm hTm
    refine sec39_Vt_le ?_ fun m' hm' hTm' => ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hc.hyp.toHyp79.V_central hz (hBQ m hm hb)).symm
    · intro c hc'
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hpair m hm hTm m' hm' hTm' b hb c hc'
  have hBV : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) →
      conjSubgroup m B ≤ Subgroup.centralizer (Vt M (LB M Q B) B Z t : Set G) :=
    fun m hm hTm => sec39_centralizer_symm (hcent1 m hm hTm)
  have hVZ : Vt M (LB M Q B) B Z t ≤ Subgroup.centralizer (Z : Set G) := by
    refine sec39_Vt_le ?_ fun m hm _ => ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro z' hz'
      exact (hc.hyp.toHyp79.V_central hz (hc.Z_le_Q hz')).symm
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hc.hyp.toHyp79.V_central hz (hBQ m hm hb)
  have hZV : Z ≤ Subgroup.centralizer (Vt M (LB M Q B) B Z t : Set G) :=
    sec39_centralizer_symm hVZ
  have hVV : Vt M (LB M Q B) B Z t ≤ Subgroup.centralizer (Vt M (LB M Q B) B Z t : Set G) :=
    sec39_Vt_le hZV fun m hm hTm => hBV m hm hTm
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (hVV hy) x hx

end CFSG.RankThree.GF2n.Stroth80
