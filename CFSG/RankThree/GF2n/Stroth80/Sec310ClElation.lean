module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClReprData
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClConj
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClScalar
public import CFSG.RankThree.GF2n.Stroth80.Sec310Count

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem ReprData.mem_QB_iff (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    {m : G} (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B))
    (hnotC : ¬ Vt M (LB M Q B) B Z t ≤ QB (conjSubgroup m B))
    {b : M₀.E} (hbB : ∀ v, v ∈ M₀.img (conjSubgroup m B) ↔ ∃ s : K, v = s • b)
    (hbV : b ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS) {v : G}
    (hv : v ∈ Vt M (LB M Q B) B Z t) :
    v ∈ QB (conjSubgroup m B) ↔
      D.F ⟨b, hbV⟩ ⟨M₀.π v, mem_imgSub.mpr (M₀.pi_mem_img hv (hc.Vt_le_Q t hv))⟩ = 0 := by
  classical
  have hcC := hc.conj_of_mem hm
  have hsC := sec5Hyp_conj hc hm hs ht
  obtain ⟨-, hVC⟩ := rt_vt_conj hc hm t
  have hv' : v ∈ Vt M (LB M Q (conjSubgroup m B)) (conjSubgroup m B) Z t := by
    rw [hVC]
    exact hv
  have hnotC' : ¬ Vt M (LB M Q (conjSubgroup m B)) (conjSubgroup m B) Z t ≤
      QB (conjSubgroup m B) := by
    rw [hVC]
    exact hnotC
  have hP := stroth310Perp_of_34 h34 G M Q Z (conjSubgroup m B) hcC n t hsC hnotC' v hv'
  rw [hP]
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  have htH : t ∈ H0 M Z := hc.LB_le_H0 hs.mem
  have htM : t ∈ M := hc.LB_le_M hs.mem
  set τ : M₀.E ≃ₗ[K] M₀.E := φ₀ ⟨t, htH⟩ with hτ
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨t, htH⟩ x hx
  have hQnorm : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) x).mp hx
  have hπc : ∀ x ∈ Q, M₀.π ⁅x, t⁆ = M₀.π x - τ (M₀.π x) := fun x hx =>
    pi_comm_eq_sub hQnorm hτπ hx
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  set w : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
    ⟨M₀.π v, mem_imgSub.mpr (M₀.pi_mem_img hv hvQ)⟩ with hw
  obtain ⟨x, hx⟩ := D.onto τ hτπ w
  have hcorr : ∀ y ∈ Q, ⁅y, t⁆ * v⁻¹ ∈ Z ↔ τ (M₀.π y) - M₀.π y = M₀.π v := by
    intro y hy
    have hcQ : ⁅y, t⁆ ∈ Q := hc.comm_mem_Q htM hy
    rw [← M₀.π_ker _ (Q.mul_mem hcQ (Q.inv_mem hvQ)), M₀.π_mul _ hcQ _ (Q.inv_mem hvQ),
      M₀.pi_inv hvQ, hπc y hy, Classify.vec_sub_eq_add K, Classify.vec_sub_eq_add K,
      Classify.vec_neg_eq K]
    constructor
    · intro h0
      have h1 : τ (M₀.π y) + M₀.π y = M₀.π v := by
        rw [add_comm]
        exact add_eq_zero_iff_eq_neg.mp h0 |>.trans (Classify.vec_neg_eq K _)
      exact h1
    · intro h0
      rw [add_comm] at h0
      rw [h0]
      exact Classify.vec_add_self K _
  have hb0 : b ∈ M₀.img (conjSubgroup m B) := (hbB b).mpr ⟨1, (one_smul K b).symm⟩
  obtain ⟨b', hb'C, hb'Q, hb'π⟩ := hb0
  constructor
  · intro hPr
    obtain ⟨y₀, hy₀Q, hy₀π⟩ := M₀.π_surj x
    have hz : ⁅y₀, t⁆ * v⁻¹ ∈ Z := (hcorr y₀ hy₀Q).mpr (by rw [hy₀π]; exact hx)
    have h1 := hPr b' hb'C y₀ hy₀Q hz
    have h2 : b' * y₀ = y₀ * b' := commutatorElement_eq_one_iff_mul_comm.mp h1
    have h3 := (M₀.comm_iff_B h.reg hb'Q hy₀Q).mp h2
    rw [hb'π, hy₀π] at h3
    rw [D.form τ hτπ ⟨b, hbV⟩ w x hx]
    exact h3
  · intro hF b'' hb''C y hyQ hyz
    have hxy : τ (M₀.π y) - M₀.π y = M₀.π v := (hcorr y hyQ).mp hyz
    have h1 := D.form τ hτπ ⟨b, hbV⟩ w (M₀.π y) hxy
    rw [hF] at h1
    have hb''Q : b'' ∈ Q := hcC.le hb''C
    obtain ⟨s, hs'⟩ := (hbB _).mp (M₀.pi_mem_img hb''C hb''Q)
    have h2 : M₀.B (M₀.π b'') (M₀.π y) = 0 := by
      rw [hs', map_smul, LinearMap.smul_apply, ← h1, smul_zero]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((M₀.comm_iff_B h.reg hb''Q hyQ).mpr h2)

theorem ReprData.not_Vt_le_QB_conj (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    (hdim : 4 ≤ Module.finrank K ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    {m : G} (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B)) :
    ¬ Vt M (LB M Q B) B Z t ≤ QB (conjSubgroup m B) := by
  classical
  intro hle
  have hcC := hc.conj_of_mem hm
  have hsC := sec5Hyp_conj hc hm hs ht
  have hcard := stroth_3_5 h34 hcC hsC.width hsC.n_gt hsC.noA2 hsC.gen
  obtain ⟨b₂, hb₂Y, hb₂0, -, -, hel4, -⟩ := hcC.elation_package hsC.width hsC.n_gt hsC.noA2
    hcard.2.2.1 hcard.2.2.2 h (Y := Vt M (LB M Q B) B Z t) (sec39_conjB_le_Vt hm ht)
    (le_inf (hc.Vt_le_Q t) hle) hS
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  have hLR : LB M Q (conjSubgroup m B) ≤ Rt M (LB M Q B) t := hc.LB_conj_le_Rt hm ht
  refine Classify.no_elations_of_isom D.nondeg D.alt (by omega)
    (b := (⟨b₂, hb₂Y⟩ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)))
    (fun h0 => hb₂0 (congrArg Subtype.val h0)) (Set.range D.ρ) ?_ ?_
  · rintro _ ⟨r, rfl⟩
    exact D.isom r
  · intro φ hφ
    obtain ⟨l, hl, hlS⟩ := hel4 φ hφ
    have hlR : l ∈ Rt M (LB M Q B) t := hLR hl
    have hrH : l ∈ H0 M Z := hc.Rt_le_H0 t hlR
    obtain ⟨hw, -⟩ := D.ρ_apply ⟨l, hlR⟩ (φ₀ ⟨l, hrH⟩) (fun x hx => hφπ ⟨l, hrH⟩ x hx) 0
    refine ⟨D.ρ ⟨l, hlR⟩, ⟨⟨l, hlR⟩, rfl⟩, fun y => ?_⟩
    obtain ⟨hy, hρy⟩ := D.ρ_apply ⟨l, hlR⟩ (φ₀ ⟨l, hrH⟩) (fun x hx => hφπ ⟨l, hrH⟩ x hx) y
    apply Subtype.ext
    rw [hρy]
    exact hlS (φ₀ ⟨l, hrH⟩) (fun x hx => hφπ ⟨l, hrH⟩ x hx) y

theorem ReprData.elation_data (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    {hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)}
    (D : ReprData (Vt M (LB M Q B) B Z t) (Rt M (LB M Q B) t) (hc.CN t) M₀ hS t)
    (hdim : 4 ≤ Module.finrank K ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    {m : G} (hm : m ∈ M) (ht : t ∈ conjSubgroup m (LB M Q B)) :
    ∃ e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS), e ≠ 0 ∧
      (∀ v : M₀.E, v ∈ M₀.img (conjSubgroup m B) ↔ ∃ s : K, v = s • (e : M₀.E)) ∧
      ((conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ ≤
        Classify.pointRadSubgroup D.F e ∧
      Classify.ElationFull D.F
        ((((conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map D.ρ :
          Subgroup _) : Set _) e := by
  classical
  have hcC := hc.conj_of_mem hm
  have hsC := sec5Hyp_conj hc hm hs ht
  have hnotC := D.not_Vt_le_QB_conj h34 hs h hdim hm ht
  have hcard := stroth_3_5 h34 hcC hsC.width hsC.n_gt hsC.noA2 hsC.gen
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  have hLR : LB M Q (conjSubgroup m B) ≤ Rt M (LB M Q B) t := hc.LB_conj_le_Rt hm ht
  have hLC : LB M Q (conjSubgroup m B) = conjSubgroup m (LB M Q B) := hc.LB_conj hm
  obtain ⟨b, hb0, -, hB, -, -⟩ := hcC.dictB h
  have hbV : b ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS :=
    mem_imgSub.mpr (M₀.img_mono (sec39_conjB_le_Vt hm ht) ((hB b).mpr ⟨1, (one_smul K b).symm⟩))
  have himgY : ∀ {b' : M₀.E}, (∀ v, v ∈ M₀.img (conjSubgroup m B) ↔ ∃ s : K, v = s • b') →
      ∀ (hb'V : b' ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS) (e : M₀.E),
        e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup m B)) ↔
          ∃ he : e ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS, D.F ⟨b', hb'V⟩ ⟨e, he⟩ = 0 := by
    intro b' hb' hb'V e
    constructor
    · rintro ⟨v, ⟨hvV, hvB⟩, hvQ, rfl⟩
      refine ⟨mem_imgSub.mpr (M₀.pi_mem_img hvV hvQ), ?_⟩
      exact (D.mem_QB_iff h34 hs h hm ht hnotC hb' hb'V hvV).mp hvB
    · rintro ⟨he, hF⟩
      obtain ⟨v, hvV, hvQ, hv⟩ := mem_imgSub.mp he
      have hvV' : v ∈ Vt M (LB M Q B) B Z t := hvV
      refine ⟨v, ⟨hvV', ?_⟩, hvQ, hv⟩
      refine (D.mem_QB_iff h34 hs h hm ht hnotC hb' hb'V hvV').mpr ?_
      have : (⟨M₀.π v, mem_imgSub.mpr (M₀.pi_mem_img hvV' hvQ)⟩ :
          ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) = ⟨e, he⟩ := Subtype.ext hv
      rw [this]
      exact hF
  have hY : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup m B)) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup m B)) := by
    intro c e he
    obtain ⟨he', hF⟩ := (himgY hB hbV e).mp he
    refine (himgY hB hbV (c • e)).mpr ⟨(imgSub M₀ (Vt M (LB M Q B) B Z t) hS).smul_mem c he', ?_⟩
    have : (⟨c • e, (imgSub M₀ (Vt M (LB M Q B) B Z t) hS).smul_mem c he'⟩ :
        ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) = c • ⟨e, he'⟩ := rfl
    rw [this, map_smul, hF, smul_zero]
  obtain ⟨b₂, hb₂Y, hb₂0, hb₂B, hel3, hel4, -⟩ := hcC.elation_package hsC.width hsC.n_gt
    hsC.noA2 hcard.2.2.1 hcard.2.2.2 h
    (Y := Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup m B))
    (le_inf (sec39_conjB_le_Vt hm ht) hcC.B_le_QB)
    (inf_le_inf_right _ (hc.Vt_le_Q t)) hY
  have hle : imgSub M₀ (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup m B)) hY ≤
      imgSub M₀ (Vt M (LB M Q B) B Z t) hS := fun e he =>
    mem_imgSub.mpr (M₀.img_mono inf_le_left (mem_imgSub.mp he))
  have hb₂V : b₂ ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS := hle hb₂Y
  have hperp : ∀ v : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS),
      D.F v ⟨b₂, hb₂V⟩ = 0 → (v : M₀.E) ∈ imgSub M₀
        (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup m B)) hY := by
    intro v hv
    refine mem_imgSub.mpr ((himgY hb₂B hb₂V (v : M₀.E)).mpr ⟨v.2, ?_⟩)
    rw [Classify.form_comm D.alt]
    exact hv
  have hmemL : ∀ r : ↥(Rt M (LB M Q B) t),
      r ∈ (conjSubgroup m (LB M Q B)).subgroupOf (Rt M (LB M Q B) t) →
        (r : G) ∈ LB M Q (conjSubgroup m B) := by
    intro r hr
    rw [hLC]
    exact hr
  refine ⟨⟨b₂, hb₂V⟩, fun h0 => hb₂0 (congrArg Subtype.val h0), hb₂B, ?_, ?_⟩
  · rintro g ⟨r, hr, rfl⟩
    have hrH : (r : G) ∈ H0 M Z := hc.Rt_le_H0 t r.2
    have hS' : ∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = (φ₀ ⟨r, hrH⟩) (M₀.π x) :=
      fun x hx => hφπ ⟨r, hrH⟩ x hx
    obtain ⟨hfix, hmove⟩ := hel3 (r : G) (hmemL r hr) (φ₀ ⟨r, hrH⟩) hS'
    refine ⟨D.isom r, ?_, fun v hv => ?_⟩
    · obtain ⟨hw, hρ⟩ := D.ρ_apply r (φ₀ ⟨r, hrH⟩) hS' ⟨b₂, hb₂V⟩
      rw [hρ]
      exact Subtype.ext hfix
    · obtain ⟨hw, hρ⟩ := D.ρ_apply r (φ₀ ⟨r, hrH⟩) hS' v
      obtain ⟨c, hc'⟩ := hmove (v : M₀.E) (hperp v hv)
      refine ⟨c, ?_⟩
      rw [hρ]
      apply Subtype.ext
      show (φ₀ ⟨r, hrH⟩) (v : M₀.E) = (v : M₀.E) + c • b₂
      rw [← hc']
      abel
  · intro φ hφ
    let f : Module.Dual K ↥(imgSub M₀ (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup m B)) hY) :=
      φ.comp (Submodule.inclusion hle)
    have hf0 : f ⟨b₂, hb₂Y⟩ = 0 := hφ
    obtain ⟨l, hl, hlS⟩ := hel4 f hf0
    have hlR : l ∈ Rt M (LB M Q B) t := hLR hl
    have hlH : l ∈ H0 M Z := hc.Rt_le_H0 t hlR
    have hS' : ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = (φ₀ ⟨l, hlH⟩) (M₀.π x) :=
      fun x hx => hφπ ⟨l, hlH⟩ x hx
    refine ⟨D.ρ ⟨l, hlR⟩, ⟨⟨l, hlR⟩, ?_, rfl⟩, fun v hv => ?_⟩
    · show l ∈ conjSubgroup m (LB M Q B)
      rw [← hLC]
      exact hl
    · obtain ⟨hw, hρ⟩ := D.ρ_apply ⟨l, hlR⟩ (φ₀ ⟨l, hlH⟩) hS' v
      have h1 := hlS (φ₀ ⟨l, hlH⟩) hS' ⟨(v : M₀.E), mem_imgSub.mp (hperp v hv) |> mem_imgSub.mpr⟩
      rw [hρ]
      apply Subtype.ext
      exact h1

end CFSG.RankThree.GF2n.Stroth80
