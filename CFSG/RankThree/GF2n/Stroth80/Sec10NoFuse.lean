module

public import CFSG.RankThree.GF2n.Stroth80.Sec10FlagRadical
public import CFSG.RankThree.GF2n.Stroth80.Sec10Sigma
public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU
public import CFSG.RankThree.GF2n.Stroth80.Sec103Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec10Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem StrothHyp.card_le_of_isElemAbelian (H : StrothHyp M Q Z) {w : ℕ} (hw : Width Q Z w)
    {S : Subgroup G} (hSQ : S ≤ Q) (hS : CFSG.Open.IsElemAbelian 2 S) :
    Nat.card S ≤ Nat.card Z ^ (w + 1) := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF H
  have hK : 1 < Nat.card (GaloisField 2 m) := by rw [h.card]; have := H.q4; omega
  have hdim := h.finrank_E hw hK
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hSN : S ≤ Subgroup.normalizer (Z : Set G) := fun s hs =>
    H.Z_normal.2 (H.Q_normal.1 (hSQ hs))
  have hsing : ∀ e ∈ M₀.img (S ⊔ Z), M₀.Qf e = 0 := by
    rintro _ ⟨x, hx, hxQ, rfl⟩
    obtain ⟨s, hs, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hSN hx
    rw [M₀.π_mul s (hSQ hs) z (hZQ hz), (M₀.π_ker z (hZQ hz)).mpr hz, add_zero]
    exact (M₀.isElemAbelian_iff h.reg hSQ).mp hS _ (M₀.pi_mem_img hs (hSQ hs))
  have h1 := M₀.card_eq (sup_le hSQ hZQ) (le_sup_right : Z ≤ S ⊔ Z)
  have h2 := Tim79.QuadModel.card_le_of_totallySingular M₀ (U := M₀.img (S ⊔ Z)) hsing hdim
  rw [h.card] at h2
  calc Nat.card S ≤ Nat.card ↥(S ⊔ Z) := Subgroup.card_le_of_le le_sup_left
    _ = Nat.card Z * Nat.card (M₀.img (S ⊔ Z)) := h1
    _ ≤ Nat.card Z * Nat.card Z ^ w := Nat.mul_le_mul_left _ h2
    _ = Nat.card Z ^ (w + 1) := by ring

theorem Ctx.mul_comm_of_noFuse (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hNF : ∀ y ∈ Q, ∀ z ∈ Z, y * t * y⁻¹ = t * z → z = 1) {x : G} (hxQ : x ∈ Q)
    (hxZ : ⁅t, x⁆ ∈ Z) : x * t = t * x := by
  have hz : ⁅x, t⁆ ∈ Z := by rw [← commutatorElement_inv]; exact Z.inv_mem hxZ
  have hct : t * ⁅x, t⁆ * t⁻¹ = ⁅x, t⁆ := hc.LB_centralizes_Z ht _ hz
  have heq : x * t * x⁻¹ = t * ⁅x, t⁆ := by
    calc x * t * x⁻¹ = ⁅x, t⁆ * t := by simp only [commutatorElement_def]; group
      _ = t * ⁅x, t⁆ * t⁻¹ * t := by rw [hct]
      _ = t * ⁅x, t⁆ := by group
  exact commutatorElement_eq_one_iff_mul_comm.mp (hNF x hxQ _ hz heq)

private theorem img_Vt_le_range (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) (τ : M₀.E ≃ₗ[K] M₀.E)
    (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x)) :
    imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he) ≤
      LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1) := by
  intro e he
  have h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
    (stroth_3_5 h34 hc H.width H.n_gt H.noA2 H.gen).2.1
  have hVt : Vt M (LB M Q B) B Z t ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t :=
    hc.Vt_le_Tt_of_SLNat (H.toSec5 ht.1.mem_LB ht.1.2.2.1) h35 (SLMNat.toSLNat hm (by norm_num))
  have hTU : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Ut Q Z t :=
    sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht.1.mem_LB)
  exact (mem_img_comm_zpowers_sup_iff M₀ hM.reg τ htQ htQ' hτπ e).mp
    (M₀.img_mono (hVt.trans hTU) (mem_imgSub.mp he))

private theorem Qf_eq_zero_of_mem_range (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) (τ : M₀.E ≃ₗ[K] M₀.E)
    (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x)) :
    ∀ u ∈ LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf u = 0 := by
  intro u hu
  have htM : t ∈ M := hc.LB_le_M ht.1.mem_LB
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hEA := Ctx.isElemAbelian_Ut h34 hc (H.toSec5 ht.1.mem_LB ht.1.2.2.1)
    (SLMNat.toSLNat hm (by norm_num))
  exact (M₀.isElemAbelian_iff hM.reg (hc.Ut_le_Q htM)).mp hEA u
    ((mem_img_comm_zpowers_sup_iff M₀ hM.reg τ htQ htQ' hτπ u).mpr hu)

private theorem finrank_range_eq (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) (τ : M₀.E ≃ₗ[K] M₀.E)
    (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x)) :
    Module.finrank K (LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1)) =
      Module.finrank K (imgSub M₀ (Vt M (LB M Q B) B Z t)
        (fun c _ he => hc.smul_mem_img_Vt hM t c he)) + 2 := by
  have hq : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M ht.1.mem_LB)
  have hcard := card_comm_zpowers_sup M₀ hM.reg τ htQ htQ' hτπ
  rw [hM.card] at hcard
  have hUt := Good103.card_Ut_eq h34 h311a hspread H ht hm
  have hU : Nat.card Z ^ (2 * 2 + 1) =
      Nat.card Z ^ (1 + Module.finrank K (LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1))) := by
    rw [← hUt, pow_add, pow_one]
    exact hcard
  have hVcard := M₀.card_eq (hc.Vt_le_Q t)
    (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
  have hpow : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hM t c he)) = Nat.card K ^ Module.finrank K
        (imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he)) :=
    Module.natCard_eq_pow_finrank
  have hV : Nat.card Z ^ (2 + 1) = Nat.card Z ^ (1 + Module.finrank K
      (imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he))) := by
    rw [← SLMNat.card_Vt hm, hVcard, pow_add, pow_one]
    congr 1
    rw [← hM.card]
    exact hpow
  have h1 := Nat.pow_right_injective hq hU
  have h2 := Nat.pow_right_injective hq hV
  omega

private theorem Lx_sub_mem_of_orthogonal (hc : Ctx M Q Z B) {t : G} (ht : Good103 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hNF : ∀ y ∈ Q, ∀ z ∈ Z, y * t * y⁻¹ = t * z → z = 1)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (τ : M₀.E ≃ₗ[K] M₀.E) (hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x))
    (hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f) {d : G} (hd : d ∈ QB Y ⊓ M) {e : M₀.E}
    (he : e ∈ M₀.B.orthogonal (LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1))) :
    φ ⟨d, Lx_le_H0 hs (smith_1_12 hs) hd⟩ e - e ∈
      imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he) := by
  have hrefl : M₀.B.IsRefl := LinearMap.IsAlt.isRefl M₀.alt
  have hnd : M₀.B.Nondegenerate := hrefl.nondegenerate_iff_separatingLeft.mpr M₀.nondeg
  have hker := ker_sub_one_eq_orthogonal_range M₀.B hnd hrefl (τ : M₀.E →ₗ[K] M₀.E)
    (fun u v => hτB u v) τ.surjective
  rw [← hker, LinearMap.mem_ker] at he
  have htM : t ∈ M := hc.LB_le_M ht.1.mem_LB
  obtain ⟨htQ, -⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
  have hfix : τ (M₀.π x) = M₀.π x := by simpa [sub_eq_zero] using he
  have hxZ : ⁅t, x⁆ ∈ Z := (comm_mem_iff_fix htQ hτπ hxQ).mpr hfix
  have hxt := hc.mul_comm_of_noFuse ht.1.mem_LB hNF hxQ hxZ
  have hxK : x ∈ Kx Q Y := by
    rw [Kx_eq hs (smith_1_12 hs)]
    exact ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
  have hA : ⁅x, d⁆ ∈ Q ⊓ QB Y := Subgroup.commutator_le.mp (smith_1_13 hs).1 x hxK d hd
  have hdQ := (hc.conj_mem_Q_of_mem_M hd.2).1
  have hπ := pi_comm_eq_sub (M₀ := M₀) (t := d) (T := φ ⟨d, Lx_le_H0 hs (smith_1_12 hs) hd⟩)
    hdQ (fun y hy => hφπ ⟨d, Lx_le_H0 hs (smith_1_12 hs) hd⟩ y hy) hxQ
  have haV : ⁅x, d⁆ ∈ Vt M (LB M Q B) B Z t := by
    rw [Good103.Vt_eq ht hs]
    exact Subgroup.mem_sup_left hA
  have hmem : M₀.π ⁅x, d⁆ ∈ imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hM t c he) :=
    mem_imgSub.mpr (M₀.pi_mem_img haV (hc.Vt_le_Q t haV))
  have hneg : φ ⟨d, Lx_le_H0 hs (smith_1_12 hs) hd⟩ (M₀.π x) - M₀.π x = -M₀.π ⁅x, d⁆ := by
    rw [hπ]; abel
  rw [hneg]
  exact Submodule.neg_mem _ hmem

private theorem eq_one_of_sub_mem_img_Vt (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {y : G} (hyY : y ∈ Y) (hyH0 : y ∈ H0 M Z)
    (hy : ∀ e, φ ⟨y, hyH0⟩ e - e ∈ M₀.img (Vt M (LB M Q B) B Z t)) : y = 1 := by
  by_contra hy1
  have hy103 : Good103 M Q Z B y := (Good103.iff_of_mem_root h34 hspread H ht.1 hs hyY hy1).mpr ht
  have hym : SLMNat hc y 2 := (SLMNat.iff_of_mem_root h34 hspread H ht.1 hs hyY hy1).mpr hm
  have hU := Good103.card_Ut_eq h34 h311a hspread H hy103 hym
  obtain ⟨hyQ, hyQ'⟩ := hc.conj_mem_Q_of_mem_M hyH0.1
  have hle : Ut Q Z y ≤ Vt M (LB M Q B) B Z t := by
    intro u hu
    have huQ : u ∈ Q := hc.Ut_le_Q hyH0.1 hu
    have hr := (mem_img_comm_zpowers_sup_iff M₀ hM.reg (φ ⟨y, hyH0⟩) hyQ hyQ'
      (fun x hx => hφπ ⟨y, hyH0⟩ x hx) (M₀.π u)).mp (M₀.pi_mem_img hu huQ)
    obtain ⟨e, he⟩ := LinearMap.mem_range.mp hr
    have he' : φ ⟨y, hyH0⟩ e - e = M₀.π u := by simpa using he
    exact (M₀.mem_img_iff sec39_Z_le_Vt huQ).mp (he' ▸ hy e)
  have h1 := Subgroup.card_le_of_le hle
  rw [hU, SLMNat.card_Vt hm] at h1
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have := (Nat.pow_le_pow_iff_right hq).mp h1
  omega

private theorem isElemAbelian_map_ker (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφQf : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e)
    {D₀ : Subgroup ↥(QB Y ⊓ M)}
    (hD₀ : ∀ d ∈ D₀, ∀ w ∈ M₀.B.orthogonal (imgSub M₀ (Vt M (LB M Q B) B Z t)
        (fun c _ he => hc.smul_mem_img_Vt hM t c he)),
      φ (Subgroup.inclusion (Lx_le_H0 hs (smith_1_12 hs)) d) w - w ∈
        imgSub M₀ (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he)) :
    CFSG.Open.IsElemAbelian 2 (D₀.map (QB Y ⊓ M).subtype) := by
  have hDH0 : QB Y ⊓ M ≤ H0 M Z := Lx_le_H0 hs (smith_1_12 hs)
  let ρ : ↥(QB Y ⊓ M) →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hDH0)
  have hρB : ∀ d e f, M₀.B (ρ d e) (ρ d f) = M₀.B e f := fun d e f =>
    quadModel_B_iso M₀ (ρ d) (hφQf _) e f
  have hρV : ∀ d : ↥(QB Y ⊓ M), ∀ v ∈ imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c _ he => hc.smul_mem_img_Vt hM t c he), ρ d v = v := fun d v hv =>
    Good103.actionHom_fixes_img_Vt hc ht hs hDH0 le_rfl hφπ d.2 (mem_imgSub.mp hv)
  have hkey : ∀ d : ↥(QB Y ⊓ M), (d : G) ∈ Y → (∀ e, ρ d e - e ∈ imgSub M₀
      (Vt M (LB M Q B) B Z t) (fun c _ he => hc.smul_mem_img_Vt hM t c he)) → (d : G) = 1 :=
    fun d hdY hd => eq_one_of_sub_mem_img_Vt h34 h311a hspread H ht hm hs hM hφπ hdY
      (hDH0 d.2) (fun e => mem_imgSub.mp (hd e))
  have hcomm : ∀ a ∈ D₀, ∀ b ∈ D₀, (a : G) * b = b * a := by
    intro a ha b hb
    have hρc : ρ ⁅a, b⁆ = ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹ := by
      simp only [commutatorElement_def, map_mul, map_inv]
    refine commutatorElement_eq_one_iff_mul_comm.mp
      (hkey ⁅a, b⁆ (hs.comm_QB_mem_X a.2.1 b.2.1) fun e => ?_)
    rw [hρc]
    exact commutator_apply_sub_mem_of_radical M₀.B M₀.nondeg M₀.alt (hρB a) (hρB b)
      (hρV a) (hρV b) (hD₀ a ha) (hD₀ b hb) e
  have hsq : ∀ a ∈ D₀, (a : G) ^ 2 = 1 := by
    intro a ha
    obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
    have ha' : (a : G) ∈ conjSubgroup g Q := hQB ▸ a.2.1
    have h := hc.hyp.toHyp79.sq_mem_conj g ha'
    rw [sq, ← hg] at h
    rw [sq]
    refine hkey (a * a) h fun e => ?_
    rw [map_mul]
    exact sq_apply_sub_mem_of_radical M₀.B M₀.nondeg M₀.alt (hρB a) (hρV a)
      (hD₀ a ha) e
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby]
    exact hcomm a ha b hb
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact hsq a ha

theorem Good103.card_QB_inf_M_le_of_noFuse (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hNF : ∀ y ∈ Q, ∀ z ∈ Z, y * t * y⁻¹ = t * z → z = 1) :
    Nat.card ↥(QB Y ⊓ M) ≤ Nat.card Z ^ (n + 2) := by
  obtain ⟨n', γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, -, hφQf⟩ := exists_actionHom_H0 hc.hyp hM
  have hDH0 : QB Y ⊓ M ≤ H0 M Z := Lx_le_H0 hs (smith_1_12 hs)
  let ρ : ↥(QB Y ⊓ M) →* (M₀.E ≃ₗ[GaloisField 2 n'] M₀.E) :=
    φ.comp (Subgroup.inclusion hDH0)
  let tH : ↥(H0 M Z) := ⟨t, hc.LB_le_H0 ht.1.mem_LB⟩
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = φ tH (M₀.π x) := fun x hx => hφπ tH x hx
  have hτB : ∀ e f, M₀.B (φ tH e) (φ tH f) = M₀.B e f := fun e f =>
    quadModel_B_iso M₀ (φ tH) (hφQf tH) e f
  obtain ⟨c, hc0⟩ := exists_hom_sub_mem_of_flag M₀.B M₀.Qf M₀.nondeg M₀.Qf_add
    (img_Vt_le_range h34 H ht hm hM (φ tH) hτπ) (Qf_eq_zero_of_mem_range h34 H ht hm hM (φ tH) hτπ)
    (finrank_range_eq h34 h311a hspread H ht hm hM (φ tH) hτπ) ρ (fun d e => hφQf _ e)
    (fun d v hv => Good103.actionHom_fixes_img_Vt hc ht hs hDH0 le_rfl hφπ d.2
      (mem_imgSub.mp hv))
    (fun d e he => Lx_sub_mem_of_orthogonal hc ht hs hNF hM hφπ (φ tH) hτπ hτB d.2 he)
  have hab := isElemAbelian_map_ker h34 h311a hspread H ht hm hs hM hφπ hφQf (D₀ := c.ker)
    (fun d hd w hw => hc0 d (MonoidHom.mem_ker.mp hd) w hw)
  obtain ⟨g, hg⟩ := hs.conj
  have hQBY : QB Y = conjSubgroup g Q := by rw [hg]; exact QB_conj_eq hc.hyp g
  have hD₀Q : c.ker.map (QB Y ⊓ M).subtype ≤ conjSubgroup g Q :=
    (Subgroup.map_subtype_le _).trans (inf_le_left.trans hQBY.le)
  have hb := (StrothHyp.conj hc.hyp g).card_le_of_isElemAbelian (H.width.conjG g) hD₀Q hab
  rw [card_conjSubgroup, Subgroup.card_map_of_injective (QB Y ⊓ M).subtype_injective] at hb
  have hidx := Subgroup.card_mul_index c.ker
  rw [Subgroup.index_ker] at hidx
  have hr : Nat.card ↥c.range ≤ Nat.card Z := by
    rw [← hM.card]
    exact (Subgroup.card_le_card_group c.range).trans (Nat.card_congr Multiplicative.toAdd).le
  calc Nat.card ↥(QB Y ⊓ M) = Nat.card ↥c.ker * Nat.card ↥c.range := hidx.symm
    _ ≤ Nat.card Z ^ (n + 1) * Nat.card Z := Nat.mul_le_mul hb hr
    _ = Nat.card Z ^ (n + 2) := by ring

end CFSG.RankThree.GF2n.Stroth80
