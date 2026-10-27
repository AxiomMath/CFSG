module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep7B
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIEnv

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Helpers

theorem K1_mem_of_L {T L V V₁ V₂ K₁ : Subgroup G} (hLK : lOne L V₁ ≤ K₁)
    (hs : Setting1282One G T L V 4 V₁ V₂) {y : G}
    (hy : y ∈ L ⊓ Subgroup.centralizer (V₂ : Set G)) (hy3 : orderOf y = 3) : y ∈ K₁ :=
  L0_le_K₁ hLK hs.le (Subgroup.subset_closure ⟨hy, by rw [hy3]; decide⟩)

theorem rel_arith (r s : ℕ) (h : r * s = 4) (hs : s ≠ 1) : r = 1 ∨ r = 2 := by
  have hd : s ∣ 4 := ⟨r, by rw [← h, mul_comm]⟩
  have hle : s ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  interval_cases s <;> omega

theorem mem_sup_decomp {I W : Subgroup G} (hc : ∀ i ∈ I, ∀ w ∈ W, i * w = w * i) :
    ∀ x ∈ I ⊔ W, ∃ i ∈ I, ∃ w ∈ W, x = i * w := by
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact ⟨z, hz, 1, W.one_mem, by simp⟩
    · exact ⟨1, I.one_mem, z, hz, by simp⟩
  | one => exact ⟨1, I.one_mem, 1, W.one_mem, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i1, hi1, w1, hw1, rfl⟩ := ha
    obtain ⟨i2, hi2, w2, hw2, rfl⟩ := hb
    refine ⟨i1 * i2, I.mul_mem hi1 hi2, w1 * w2, W.mul_mem hw1 hw2, ?_⟩
    have := hc i2 hi2 w1 hw1
    calc i1 * w1 * (i2 * w2) = i1 * (w1 * i2) * w2 := by group
      _ = i1 * (i2 * w1) * w2 := by rw [this]
      _ = i1 * i2 * (w1 * w2) := by group
  | inv a _ ha =>
    obtain ⟨i, hi, w, hw, rfl⟩ := ha
    refine ⟨i⁻¹, I.inv_mem hi, w⁻¹, W.inv_mem hw, ?_⟩
    have := hc i hi w hw
    calc (i * w)⁻¹ = w⁻¹ * i⁻¹ := by group
      _ = i⁻¹ * w⁻¹ := by
        have h2 : i⁻¹ * w = w * i⁻¹ := by
          calc i⁻¹ * w = i⁻¹ * (w * i) * i⁻¹ := by group
            _ = i⁻¹ * (i * w) * i⁻¹ := by rw [this]
            _ = w * i⁻¹ := by group
        calc w⁻¹ * i⁻¹ = (i * w)⁻¹ := by group
          _ = (w * i)⁻¹ := by rw [this]
          _ = i⁻¹ * w⁻¹ := by group

end Helpers

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

theorem DIEnv.fixD0_iff (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2) (h1289 : Lemma12_8_9W)
    (h12813 : Lemma12_8_13) (i : G) (hi : i ∈ E.I) :
    (∀ γ ∈ kmapOf (D.img K₁) E.kap (D.img (CFSG.conjugate (zU128 V V₁) g)),
        γ (Additive.ofMul ⟨i, hi⟩) = Additive.ofMul ⟨i, hi⟩) ↔
      (∀ d ∈ CFSG.conjugate (zU128 V V₁) g, d * i * d⁻¹ = i) := by
  constructor
  · intro hfix d hd
    have hdN1 := (Dg_mem_normalizers h12813 E.hs E.hgP E.hgN hd).1
    have hdN := (Dg_mem_normalizers h12813 E.hs E.hgP E.hgN hd).2
    have hdT := Dg_le_T h1222 h1289 E.hcx E.hs E.hgP E.hgN hd
    have hdI : d ∈ Subgroup.normalizer (E.I : Set G) := E.hTI hdT
    have hdΩ : D.ρ ⟨d, hdN⟩ ∈ D.img K₁ := E.hTΩ d hdT hdN
    have hmem : E.kap ⟨D.ρ ⟨d, hdN⟩, hdΩ⟩ ∈
        kmapOf (D.img K₁) E.kap (D.img (CFSG.conjugate (zU128 V V₁) g)) := by
      unfold kmapOf
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (L128A.HatU.rho_mem_img D hd hdN))
    have h1 := hfix _ hmem
    have h2 := E.action hdN hdI hdN1 hdΩ (Additive.ofMul ⟨i, hi⟩)
    rw [h1] at h2
    exact h2.symm
  · intro hcomm γ hγ
    unfold kmapOf at hγ
    obtain ⟨x, hx, hxγ⟩ := Subgroup.mem_map.1 hγ
    obtain ⟨d, hd, hdN, hdρ⟩ := (L128A.HatU.mem_img D).1 (Subgroup.mem_subgroupOf.1 hx)
    have hdN1 := (Dg_mem_normalizers h12813 E.hs E.hgP E.hgN hd).1
    have hdT := Dg_le_T h1222 h1289 E.hcx E.hs E.hgP E.hgN hd
    have hdI : d ∈ Subgroup.normalizer (E.I : Set G) := E.hTI hdT
    have hdΩ : D.ρ ⟨d, hdN⟩ ∈ D.img K₁ := E.hTΩ d hdT hdN
    have hxeq : x = ⟨D.ρ ⟨d, hdN⟩, hdΩ⟩ := Subtype.ext hdρ.symm
    have hγeq : γ = E.kap ⟨D.ρ ⟨d, hdN⟩, hdΩ⟩ := by
      rw [← hxγ, hxeq]
      rfl
    rw [hγeq]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [E.action hdN hdI hdN1 hdΩ]
    exact hcomm d hd

theorem DIEnv.fstar (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F3 : FactF3)
    {x : G} (hx : x ∈ zU128 V V₁) (hxW : E.y₀ * x * E.y₀⁻¹ * x⁻¹ ∈ wcSub T L V V₁) :
    x ∈ wcSub T L V V₁ :=
  F_star h1222 h12213 h1289 h12810 h12813 F3 E.hcx E.hs E.hLK E.hK₁H E.hK₁U E.hgP E.hgN D E.hTΩ
    E.hker E.S E.hSV E.hSπ E.haV₂ E.haV₁ E.hM E.kap E.fp E.fl E.fPl E.hp E.hℓ E.hPl E.hpℓ E.hℓPl
    E.hY₁ E.hY₂ E.hD0 E.hy₀ E.hy₀3 hx hxW

theorem DIEnv.natCard_D0 (E : DIEnv T L V V₁ V₂ K₁ g D) (F2 : FactF2) :
    Nat.card ↥(kmapOf (D.img K₁) E.kap (D.img (CFSG.conjugate (zU128 V V₁) g))) = 4 := by
  rw [E.hD0]
  exact card_D0 F2 E.hM E.fp E.fl E.fPl E.hp E.hℓ E.hPl E.hpℓ E.hℓPl _ E.hY₂

theorem DIEnv.exists_not_centralize (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h1289 : Lemma12_8_9W) (h12813 : Lemma12_8_13) (F2 : FactF2) :
    ∃ d ∈ CFSG.conjugate (zU128 V V₁) g, ∃ i : G, ∃ hi : i ∈ E.I, d * i * d⁻¹ ≠ i := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ γ ∈ kmapOf (D.img K₁) E.kap (D.img (CFSG.conjugate (zU128 V V₁) g)), γ = 1 := by
    intro γ hγ
    apply LinearEquiv.ext
    intro m
    have hm : ∃ i : G, ∃ hi : i ∈ E.I, m = Additive.ofMul ⟨i, hi⟩ :=
      ⟨(Additive.toMul m : ↥E.I), (Additive.toMul m : ↥E.I).2, by simp⟩
    obtain ⟨i, hi, rfl⟩ := hm
    have hfix := (E.fixD0_iff h1222 h1289 h12813 i hi).2 (fun d hd => hcon d hd i hi)
    exact hfix γ hγ
  have hbot : kmapOf (D.img K₁) E.kap (D.img (CFSG.conjugate (zU128 V V₁) g)) = ⊥ := by
    apply eq_bot_iff.2
    intro γ hγ
    exact (Subgroup.mem_bot).2 (hall γ hγ)
  have hc := E.natCard_D0 F2
  rw [hbot] at hc
  simp at hc

theorem DIEnv.conj_Dg_of_L (E : DIEnv T L V V₁ V₂ K₁ g D) {y : G}
    (hy : y ∈ L ⊓ Subgroup.centralizer (V₂ : Set G)) (hy3 : orderOf y = 3) :
    ∀ d ∈ CFSG.conjugate (zU128 V V₁) g, y * d * y⁻¹ ∈ CFSG.conjugate (zU128 V V₁) g := by
  intro d hd
  rw [mem_conj'] at hd ⊢
  have hy₂ := (y0_conj_mem E.hcx E.hs E.hgP hy).1
  have hy₂3 : orderOf (g * y * g⁻¹) = 3 := by rw [conj_orderOf]; exact hy3
  have hy₂K := K1_mem_of_L E.hLK E.hs hy₂ hy₂3
  have hN : g * y * g⁻¹ ∈ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) (E.hK₁U hy₂K)
  have e : g * (y * d * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * d * g⁻¹) * (g * y * g⁻¹)⁻¹ := by
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 hN _).1 hd

theorem DIEnv.y0_norm (E : DIEnv T L V V₁ V₂ K₁ g D) (h1289 : Lemma12_8_9W) :
    E.y₀ ∈ K₁ ∧ E.y₀ ∈ Subgroup.normalizer (i128 T L V V₁ : Set G) ∧
      E.y₀ ∈ Subgroup.normalizer (V₁ : Set G) := by
  have hy₀K : E.y₀ ∈ K₁ := K1_mem_of_L E.hLK E.hs E.hy₀ E.hy₀3
  refine ⟨hy₀K, ?_, E.hK₁H hy₀K⟩
  have hV₂ : E.y₀ ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 E.hy₀).2
  exact (h1289 G T L V 4 V₁ V₂ E.hs g E.hgP E.hgN).2.1 hV₂

theorem DIEnv.C_Z_Dg (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F2 : FactF2)
    (F3 : FactF3) {x : G} (hx : x ∈ zU128 V V₁)
    (hc : ∀ d ∈ CFSG.conjugate (zU128 V V₁) g, d * x * d⁻¹ = x) :
    x ∈ wcSub T L V V₁ := by
  classical
  let CC : Subgroup G := zU128 V V₁ ⊓ Subgroup.centralizer ((CFSG.conjugate (zU128 V V₁) g : Subgroup G) : Set G)
  have hCCmem : ∀ y, y ∈ CC ↔ y ∈ zU128 V V₁ ∧ ∀ d ∈ CFSG.conjugate (zU128 V V₁) g, d * y = y * d := by
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hwZ := wcSub_le_zU h1222 h12213 h12810 E.hs E.hgP E.hgN
  have hWC : wcSub T L V V₁ ≤ CC := by
    intro w hw
    rw [hCCmem]
    refine ⟨hwZ hw, fun d hd => ?_⟩
    have h := wc_centralizes_Dg h1289 h12813 E.hs E.hgP E.hgN hd hw
    calc d * w = d * w * d⁻¹ * d := by group
      _ = w * d := by rw [h]
  have hCCle : CC ≤ zU128 V V₁ := inf_le_left
  obtain ⟨d0, hd0, i0, hi0, hne⟩ := E.exists_not_centralize h1222 h1289 h12813 F2
  have hCCne : ¬ zU128 V V₁ ≤ CC := by
    intro h
    have hi0C : i0 ∈ CC := h (E.hIZ hi0)
    rw [hCCmem] at hi0C
    have hcomm := hi0C.2 d0 hd0
    apply hne
    calc d0 * i0 * d0⁻¹ = i0 * d0 * d0⁻¹ := by rw [hcomm]
      _ = i0 := by group
  have hrel : (wcSub T L V V₁).relIndex CC * CC.relIndex (zU128 V V₁) = 4 := by
    rw [Subgroup.relIndex_mul_relIndex (wcSub T L V V₁) CC (zU128 V V₁) hWC hCCle]
    exact relIndex_wc_zU h1222 h12213 h1289 h12810 h12813 E.hs E.hgP E.hgN D E.hDg4
  have hs1 : CC.relIndex (zU128 V V₁) ≠ 1 := fun h => hCCne (Subgroup.relIndex_eq_one.1 h)
  rcases rel_arith _ _ hrel hs1 with hr1 | hr2
  · have hCCle' : CC ≤ wcSub T L V V₁ := Subgroup.relIndex_eq_one.1 hr1
    apply hCCle'
    rw [hCCmem]
    refine ⟨hx, fun d hd => ?_⟩
    have h := hc d hd
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [h]
  · exfalso
    obtain ⟨hy₀K, hy₀I2, hy₀V₁⟩ := E.y0_norm h1289
    have hy₀N : E.y₀ ∈ Subgroup.normalizer (zU128 V V₁ : Set G) :=
      CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) (E.hK₁U hy₀K)
    have hyW : ∀ z ∈ wcSub T L V V₁, E.y₀ * z * E.y₀⁻¹ ∈ wcSub T L V V₁ :=
      wc_normalized (V₂ := V₂) hy₀I2 hy₀V₁
    have hyW' : ∀ z ∈ wcSub T L V V₁, E.y₀⁻¹ * z * E.y₀ ∈ wcSub T L V V₁ := by
      intro z hz
      have := wc_normalized (V₂ := V₂) (Subgroup.inv_mem _ hy₀I2) (Subgroup.inv_mem _ hy₀V₁) z hz
      simpa using this
    have hyCC : ∀ z ∈ CC, E.y₀ * z * E.y₀⁻¹ ∈ CC := by
      intro z hz
      rw [hCCmem] at hz ⊢
      obtain ⟨hzZ, hzc⟩ := hz
      refine ⟨(Subgroup.mem_normalizer_iff.1 hy₀N z).1 hzZ, fun d hd => ?_⟩
      have hd' : E.y₀⁻¹ * d * E.y₀ ∈ CFSG.conjugate (zU128 V V₁) g := by
        have h := E.conj_Dg_of_L (y := E.y₀⁻¹) (Subgroup.inv_mem _ E.hy₀)
          (by rw [orderOf_inv]; exact E.hy₀3) d hd
        simpa using h
      have hc' := hzc _ hd'
      calc d * (E.y₀ * z * E.y₀⁻¹) = E.y₀ * ((E.y₀⁻¹ * d * E.y₀) * z) * E.y₀⁻¹ := by group
        _ = E.y₀ * (z * (E.y₀⁻¹ * d * E.y₀)) * E.y₀⁻¹ := by rw [hc']
        _ = (E.y₀ * z * E.y₀⁻¹) * d := by group
    have hnot : ∃ j ∈ CC, j ∉ wcSub T L V V₁ := by
      by_contra hcon
      push_neg at hcon
      have hle : CC ≤ wcSub T L V V₁ := fun j hj => hcon j hj
      have h1 := Subgroup.relIndex_eq_one.2 hle
      rw [hr2] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨j, hjCC, hjW⟩ := hnot
    have hjzU : j ∈ zU128 V V₁ := ((hCCmem j).1 hjCC).1
    have hcomm := comm_mem_of_relIndex_two hWC hr2 hyCC hyW hyW' hjCC hjW
    exact hjW (E.fstar h1222 h12213 h1289 h12810 h12813 F3 hjzU hcomm)

theorem DIEnv.point_fix (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F2 : FactF2)
    (F3 : FactF3) (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp) (i : G) (hi : i ∈ E.I) :
    i ∈ wcSub T L V V₁ ↔ (Additive.ofMul ⟨i, hi⟩ : Additive ↥E.I) ∈ E.fl := by
  have hD0 : kmapOf (D.img K₁) E.kap (D.img (CFSG.conjugate (zU128 V V₁) g)) =
      pCoreOf 2 (stabS E.fp) ⊓ pCoreOf 2 (stabS E.fl) := by
    rw [E.hD0, hpt]
  have hF2 := (F2 (Additive ↥E.I) E.hM E.fp E.fl E.fPl E.hp E.hℓ E.hPl E.hpℓ E.hℓPl).1.2.2
  constructor
  · intro hw
    have hfixγ := (E.fixD0_iff h1222 h1289 h12813 i hi).2
      (fun d hd => wc_centralizes_Dg h1289 h12813 E.hs E.hgP E.hgN hd hw)
    exact (hF2 _).1 (fun γ hγ => hfixγ γ (by rw [hD0]; exact hγ))
  · intro hv
    have hfix : ∀ d ∈ CFSG.conjugate (zU128 V V₁) g, d * i * d⁻¹ = i :=
      (E.fixD0_iff h1222 h1289 h12813 i hi).1 (fun γ hγ => by
        have hγ' : γ ∈ pCoreOf 2 (stabS E.fp) ⊓ pCoreOf 2 (stabS E.fl) := by
          rw [← hD0]; exact hγ
        exact (hF2 _).2 hv γ hγ')
    exact E.C_Z_Dg h1222 h12213 h1289 h12810 h12813 F2 F3 (E.hIZ hi) hfix

theorem DIEnv.plane_fix (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13) (F2 : FactF2)
    (F3 : FactF3) (hpl : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fPl) (i : G) (hi : i ∈ E.I) :
    i ∈ wcSub T L V V₁ ↔ (Additive.ofMul ⟨i, hi⟩ : Additive ↥E.I) ∈ E.fPl := by
  have hD0 : kmapOf (D.img K₁) E.kap (D.img (CFSG.conjugate (zU128 V V₁) g)) =
      pCoreOf 2 (stabS E.fPl) ⊓ pCoreOf 2 (stabS E.fl) := by
    rw [E.hD0, hpl]
  have hF2 := (F2 (Additive ↥E.I) E.hM E.fp E.fl E.fPl E.hp E.hℓ E.hPl E.hpℓ E.hℓPl).2.2.2
  constructor
  · intro hw
    have hfixγ := (E.fixD0_iff h1222 h1289 h12813 i hi).2
      (fun d hd => wc_centralizes_Dg h1289 h12813 E.hs E.hgP E.hgN hd hw)
    exact (hF2 _).1 (fun γ hγ => hfixγ γ (by rw [hD0]; exact hγ))
  · intro hv
    have hfix : ∀ d ∈ CFSG.conjugate (zU128 V V₁) g, d * i * d⁻¹ = i :=
      (E.fixD0_iff h1222 h1289 h12813 i hi).1 (fun γ hγ => by
        have hγ' : γ ∈ pCoreOf 2 (stabS E.fPl) ⊓ pCoreOf 2 (stabS E.fl) := by
          rw [← hD0]; exact hγ
        exact (hF2 _).2 hv γ hγ')
    exact E.C_Z_Dg h1222 h12213 h1289 h12810 h12813 F2 F3 (E.hIZ hi) hfix

theorem DIEnv.plane_false (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (F2 : FactF2) (F3 : FactF3)
    (hpl : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fPl) : False := by
  have hcard : Nat.card ↥(E.I ⊓ wcSub T L V V₁) = 8 := by
    rw [natCard_inf_eq_submodule E.fPl (fun i hi => E.plane_fix h1222 h12213 h1289 h12810 h12813 F2 F3 hpl i hi),
      natCard_submodule_two, E.hPl]
    norm_num
  have hrel2 : (E.I ⊓ wcSub T L V V₁).relIndex E.I = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := E.I ⊓ wcSub T L V V₁) (K := E.I)
    rw [inf_eq_left.2 (inf_le_left : E.I ⊓ wcSub T L V V₁ ≤ E.I), hcard, E.hI16] at h1
    omega
  obtain ⟨j, hjI, hjW⟩ : ∃ j ∈ E.I, j ∉ wcSub T L V V₁ := by
    by_contra hcon
    push_neg at hcon
    have hle : E.I ≤ E.I ⊓ wcSub T L V V₁ := fun j hj => Subgroup.mem_inf.2 ⟨hj, hcon j hj⟩
    have h1 := Subgroup.relIndex_eq_one.2 hle
    rw [h1] at hrel2
    exact absurd hrel2 (by norm_num)
  obtain ⟨hy₀K, hy₀I2, hy₀V₁⟩ := E.y0_norm h1289
  have hyI : ∀ z ∈ E.I, E.y₀ * z * E.y₀⁻¹ ∈ E.I := fun z hz =>
    (Subgroup.mem_normalizer_iff.1 (E.hKI hy₀K) z).1 hz
  have hyI' : ∀ z ∈ E.I, E.y₀⁻¹ * z * E.y₀ ∈ E.I := by
    intro z hz
    have := (Subgroup.mem_normalizer_iff.1 (E.hKI (Subgroup.inv_mem _ hy₀K)) z).1 hz
    simpa using this
  have hyIW : ∀ z ∈ E.I ⊓ wcSub T L V V₁, E.y₀ * z * E.y₀⁻¹ ∈ E.I ⊓ wcSub T L V V₁ := fun z hz =>
    Subgroup.mem_inf.2 ⟨hyI z (Subgroup.mem_inf.1 hz).1,
      wc_normalized (V₂ := V₂) hy₀I2 hy₀V₁ z (Subgroup.mem_inf.1 hz).2⟩
  have hyIW' : ∀ z ∈ E.I ⊓ wcSub T L V V₁, E.y₀⁻¹ * z * E.y₀ ∈ E.I ⊓ wcSub T L V V₁ := by
    intro z hz
    refine Subgroup.mem_inf.2 ⟨hyI' z (Subgroup.mem_inf.1 hz).1, ?_⟩
    have := wc_normalized (V₂ := V₂) (Subgroup.inv_mem _ hy₀I2) (Subgroup.inv_mem _ hy₀V₁) z
      (Subgroup.mem_inf.1 hz).2
    simpa using this
  have hjH : j ∉ E.I ⊓ wcSub T L V V₁ := fun h => hjW (Subgroup.mem_inf.1 h).2
  have hcomm := comm_mem_of_relIndex_two inf_le_left hrel2 hyI hyIW hyIW' hjI hjH
  exact hjW (E.fstar h1222 h12213 h1289 h12810 h12813 F3 (E.hIZ hjI) (Subgroup.mem_inf.1 hcomm).2)

theorem DIEnv.zU_eq_I_mul (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13)
    (F2 : FactF2) (F3 : FactF3) (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp) :
    ∀ z ∈ zU128 V V₁, ∃ i ∈ E.I, ∃ w ∈ wcSub T L V V₁, z = i * w := by
  have hZc : ∀ x ∈ zU128 V V₁, ∀ y ∈ zU128 V V₁, x * y = y * x := fun x hx y hy =>
    (mem_centerOf_iff'.1 hy).2 x (zU_le_u128 hx)
  have hIW : Nat.card ↥(E.I ⊓ wcSub T L V V₁) = 4 := by
    rw [natCard_inf_eq_submodule E.fl (fun i hi => E.point_fix h1222 h12213 h1289 h12810 h12813 F2
      F3 hpt i hi), natCard_submodule_two, E.hℓ]
    norm_num
  have hsup : E.I ⊔ wcSub T L V V₁ = zU128 V V₁ :=
    sup_eq_of_card (zU128 V V₁) E.I (wcSub T L V V₁) hZc E.hIZ
      (wcSub_le_zU h1222 h12213 h12810 E.hs E.hgP E.hgN)
      (relIndex_wc_zU h1222 h12213 h1289 h12810 h12813 E.hs E.hgP E.hgN D E.hDg4) E.hI16 hIW
  have hcomm : ∀ i ∈ E.I, ∀ w ∈ wcSub T L V V₁, i * w = w * i := fun i hi w hw =>
    hZc i (E.hIZ hi) w (wcSub_le_zU h1222 h12213 h12810 E.hs E.hgP E.hgN hw)
  intro z hz
  have hzs : z ∈ E.I ⊔ wcSub T L V V₁ := by rw [hsup]; exact hz
  exact mem_sup_decomp hcomm z hzs

theorem DIEnv.Dg_comm (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13)
    (F2 : FactF2) (F3 : FactF3) (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    {d : G} (hd : d ∈ CFSG.conjugate (zU128 V V₁) g) {z : G} (hz : z ∈ zU128 V V₁) :
    d * z * d⁻¹ * z⁻¹ ∈ E.I := by
  obtain ⟨i, hi, w, hw, rfl⟩ := E.zU_eq_I_mul h1222 h12213 h1289 h12810 h12813 F2 F3 hpt z hz
  have hdw : d * w * d⁻¹ = w := wc_centralizes_Dg h1289 h12813 E.hs E.hgP E.hgN hd hw
  have hdT := Dg_le_T h1222 h1289 E.hcx E.hs E.hgP E.hgN hd
  have hdi : d * i * d⁻¹ ∈ E.I := (Subgroup.mem_normalizer_iff.1 (E.hTI hdT) i).1 hi
  have e : d * (i * w) * d⁻¹ * (i * w)⁻¹ = (d * i * d⁻¹) * i⁻¹ := by
    calc d * (i * w) * d⁻¹ * (i * w)⁻¹ = (d * i * d⁻¹) * (d * w * d⁻¹) * w⁻¹ * i⁻¹ := by group
      _ = (d * i * d⁻¹) * w * w⁻¹ * i⁻¹ := by rw [hdw]
      _ = (d * i * d⁻¹) * i⁻¹ := by group
  rw [e]
  exact E.I.mul_mem hdi (E.I.inv_mem hi)

end Env

end CFSG.Quasithin.H13.C1294
