module

public import CFSG.Quasithin.EmptyFaithful.S153VRz
public import CFSG.Quasithin.EmptyFaithful.S153VDef

public section

namespace CFSG.Quasithin.ModF

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.LieType.BorelTits
  CFSG.Quasithin.ModV CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem dsub_comm : dsub S K₂ K₁ = dsub S K₁ K₂ := by
  show S ⊓ Subgroup.centralizer ((K₂ ⊔ K₁ : Subgroup G) : Set G) =
    S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)
  rw [sup_comm]

theorem fix_of_mem_klein {p : Fin 5} {w : Perm (Fin 5)} (hw : w ∈ klein p) : w p = p := by
  simp only [klein, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw.2.2

namespace A5Cfg

variable (c : A5Cfg I S Iz K₁ K₂)
include c

theorem zel_central (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p) {y : G}
    (hy : y ∈ S ⊓ K₁) : y * zel P p = zel P p * y := by
  have hyN : y ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer hy.2
  have hpfy : P.toPiData.pf y ∈ klein p := by
    rw [pf_eq_alpha P hy.2, ← toPerm_apply]
    exact (c.memS_iff P hp ⟨y, hy.2⟩).mp hy.1
  refine (P.toPiData.comm_iff hyN (zel_mem P p)).mpr ?_
  rw [bf_zel]
  exact Subtype.ext (pact_zvec p _ (fix_of_mem_klein hpfy))

theorem central_mem_inf_S (P : AppC.A5Pi K₁) {p : Fin 5} (hp : ∀ g ∈ imgS K₁ S P.α, g p = p) {r : G}
    (hr : r ∈ S ⊓ K₁) (hc : ∀ t ∈ S ⊓ K₁, r * t = t * r) :
    r ∈ dsub S K₁ K₂ ⊔ Subgroup.zpowers (zel P p) := by
  refine c.central_mem_of_sub P hp (T := S ⊓ K₁) le_rfl ?_ ?_ hr hc
  · intro v hv
    exact c.exists_mem_inf_pf_eq P hp hv
  · intro v hv hv1
    have hnot : ¬ ∀ w, vact v w = w := fun h => hv1 (vact_faithful h)
    push Not at hnot
    obtain ⟨w, hw⟩ := hnot
    obtain ⟨u, hu, hbu⟩ := P.toPiData.bf_surj w
    refine ⟨u, ?_, hu, ?_⟩
    · exact ⟨(c.pCore_le₁ (C1.blockU_le_blockQ c.blk₁.1 hu)).1, c.U₁_le_K₁ hu⟩
    · rw [hbu]
      exact hw

theorem central_R_of {z : G}
    (hzD : ∀ d ∈ dsub S K₁ K₂, z * d = d * z) (hz₁ : ∀ y ∈ S ⊓ K₁, z * y = y * z)
    (hz₂ : ∀ y ∈ S ⊓ K₂, z * y = y * z) {r : G} (hr : r ∈ pCoreOf 2 Iz) : r * z = z * r := by
  obtain ⟨d, hd, s₁, hs₁, s₂, hs₂, rfl⟩ := c.exists_decomp_R hr
  have h₀ : d * z = z * d := (hzD d hd).symm
  have h₁ : s₁ * z = z * s₁ := (hz₁ s₁ hs₁).symm
  have h₂ : s₂ * z = z * s₂ := (hz₂ s₂ hs₂).symm
  calc d * (s₁ * s₂) * z = d * (s₁ * (s₂ * z)) := by group
    _ = d * (s₁ * (z * s₂)) := by rw [h₂]
    _ = d * ((s₁ * z) * s₂) := by group
    _ = d * ((z * s₁) * s₂) := by rw [h₁]
    _ = (d * z) * (s₁ * s₂) := by group
    _ = (z * d) * (s₁ * s₂) := by rw [h₀]
    _ = z * (d * (s₁ * s₂)) := by group

theorem omegaOneCenter_eq (hD : CFSG.Open.IsElemAbelian 2 (dsub S K₁ K₂)) (hnot₁ : ¬ K₁ ≤ Iz)
    (hnot₂ : ¬ K₂ ≤ Iz) :
    omegaOneCenterOf (pCoreOf 2 Iz) = dsub S K₁ K₂ ⊔ z0Of1469 Iz K₁ K₂ := by
  have hD' := C5.isElemAbelian_two_iff.mp hD
  obtain ⟨α₁, hα₁, hαk₁, -⟩ := c.a5₁
  obtain ⟨P₁, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α₁ hα₁ hαk₁
  obtain ⟨p₁, hp₁⟩ := exists_fixed (α := P₁.α) c.sylow₁
  obtain ⟨α₂, hα₂, hαk₂, -⟩ := c.a5₂
  obtain ⟨P₂, -⟩ := AppC.exists_a5pi c.blk₂.1 c.a5₂ α₂ hα₂ hαk₂
  obtain ⟨p₂, hp₂⟩ := exists_fixed (α := P₂.α) c.symm.sylow₁
  have hz₁U := zel_mem P₁ p₁
  have hz₂U := zel_mem P₂ p₂
  have hz₁K : zel P₁ p₁ ∈ K₁ := c.U₁_le_K₁ hz₁U
  have hz₂K : zel P₂ p₂ ∈ K₂ := c.U₂_le_K₂ hz₂U
  have hz₁S : zel P₁ p₁ ∈ S ⊓ K₁ := ⟨(c.pCore_le₁ (C1.blockU_le_blockQ c.blk₁.1 hz₁U)).1, hz₁K⟩
  have hz₂S : zel P₂ p₂ ∈ S ⊓ K₂ :=
    ⟨(c.symm.pCore_le₁ (C1.blockU_le_blockQ c.blk₂.1 hz₂U)).1, hz₂K⟩
  have hz₁R : zel P₁ p₁ ∈ pCoreOf 2 Iz :=
    c.P_le_pCoreIz hnot₁ hnot₂ (Subgroup.mem_sup_left hz₁S)
  have hz₂R : zel P₂ p₂ ∈ pCoreOf 2 Iz :=
    c.P_le_pCoreIz hnot₁ hnot₂ (Subgroup.mem_sup_right hz₂S)
  have hz₁sq : zel P₁ p₁ ^ 2 = 1 := C1.blockU_sq c.blk₁.1 _ hz₁U
  have hz₂sq : zel P₂ p₂ ^ 2 = 1 := C1.blockU_sq c.blk₂.1 _ hz₂U
  have hDK : ∀ x ∈ K₁ ⊔ K₂, ∀ d ∈ dsub S K₁ K₂, x * d = d * x := fun x hx d hd =>
    K_le_centralizer_dsub x hx d hd
  have hc₁₂ : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := c.comm
  have hz₁c : ∀ r ∈ pCoreOf 2 Iz, r * zel P₁ p₁ = zel P₁ p₁ * r :=
    fun r hr => c.central_R_of
      (fun d hd => hDK _ (Subgroup.mem_sup_left hz₁K) d hd)
      (fun y hy => (c.zel_central P₁ hp₁ hy).symm)
      (fun y hy => hc₁₂ _ hz₁K y hy.2) hr
  have hz₂c : ∀ r ∈ pCoreOf 2 Iz, r * zel P₂ p₂ = zel P₂ p₂ * r :=
    fun r hr => c.central_R_of
      (fun d hd => hDK _ (Subgroup.mem_sup_right hz₂K) d hd)
      (fun y hy => (hc₁₂ y hy.2 _ hz₂K).symm)
      (fun y hy => (c.symm.zel_central P₂ hp₂ hy).symm) hr
  have hDc : ∀ d ∈ dsub S K₁ K₂, ∀ r ∈ pCoreOf 2 Iz, r * d = d * r := fun d hd r hr =>
    c.central_R_of (fun d' hd' => hD'.1 d hd d' hd')
      (fun y hy => (hDK y (Subgroup.mem_sup_left hy.2) d hd).symm)
      (fun y hy => (hDK y (Subgroup.mem_sup_right hy.2) d hd).symm) hr
  have hDR : dsub S K₁ K₂ ≤ pCoreOf 2 Iz := c.dsub_le_pCore.trans c.Q_le_R
  set W : Subgroup G := dsub S K₁ K₂ ⊔ Subgroup.zpowers (zel P₁ p₁) ⊔ Subgroup.zpowers (zel P₂ p₂)
    with hWdef
  have hDW : dsub S K₁ K₂ ≤ W := le_sup_left.trans le_sup_left
  have hz₁W : zel P₁ p₁ ∈ W := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hz₂W : zel P₂ p₂ ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hW1 : W ≤ omegaOneCenterOf (pCoreOf 2 Iz) := by
    unfold omegaOneCenterOf omegaOneOf
    refine sup_le (sup_le ?_ ?_) ?_
    · intro d hd
      exact Subgroup.subset_closure ⟨⟨hDR hd, Subgroup.mem_centralizer_iff.mpr fun r hr => hDc d hd r hr⟩,
        hD'.2 d hd⟩
    · refine (Subgroup.zpowers_le).mpr (Subgroup.subset_closure ⟨⟨hz₁R, ?_⟩, hz₁sq⟩)
      exact Subgroup.mem_centralizer_iff.mpr fun r hr => hz₁c r hr
    · refine (Subgroup.zpowers_le).mpr (Subgroup.subset_closure ⟨⟨hz₂R, ?_⟩, hz₂sq⟩)
      exact Subgroup.mem_centralizer_iff.mpr fun r hr => hz₂c r hr
  have hW2 : ∀ x ∈ centerOf (pCoreOf 2 Iz), x ∈ W := by
    intro x hx
    obtain ⟨d, hd, s₁, hs₁, s₂, hs₂, rfl⟩ := c.exists_decomp_R hx.1
    have hxc : ∀ t ∈ pCoreOf 2 Iz, t * (d * (s₁ * s₂)) = (d * (s₁ * s₂)) * t := fun t ht =>
      Subgroup.mem_centralizer_iff.mp hx.2 t ht
    have hs₁c : ∀ t ∈ S ⊓ K₁, s₁ * t = t * s₁ := by
      intro t ht
      have htR : t ∈ pCoreOf 2 Iz := c.P_le_pCoreIz hnot₁ hnot₂ (Subgroup.mem_sup_left ht)
      have h := hxc t htR
      have e1 : t * d = d * t := hDK t (Subgroup.mem_sup_left ht.2) d hd
      have e2 : s₂ * t = t * s₂ := (hc₁₂ t ht.2 s₂ hs₂.2).symm
      have h2 : d * ((t * s₁) * s₂) = d * ((s₁ * t) * s₂) := by
        calc d * ((t * s₁) * s₂) = (d * t) * (s₁ * s₂) := by group
          _ = (t * d) * (s₁ * s₂) := by rw [e1]
          _ = t * (d * (s₁ * s₂)) := by group
          _ = (d * (s₁ * s₂)) * t := h
          _ = d * (s₁ * (s₂ * t)) := by group
          _ = d * (s₁ * (t * s₂)) := by rw [e2]
          _ = d * ((s₁ * t) * s₂) := by group
      have h3 := mul_left_cancel h2
      exact (mul_right_cancel h3).symm
    have hs₂c : ∀ t ∈ S ⊓ K₂, s₂ * t = t * s₂ := by
      intro t ht
      have htR : t ∈ pCoreOf 2 Iz := c.P_le_pCoreIz hnot₁ hnot₂ (Subgroup.mem_sup_right ht)
      have h := hxc t htR
      have e1 : t * d = d * t := hDK t (Subgroup.mem_sup_right ht.2) d hd
      have e2 : s₁ * t = t * s₁ := hc₁₂ s₁ hs₁.2 t ht.2
      have h2 : d * (s₁ * (t * s₂)) = d * (s₁ * (s₂ * t)) := by
        calc d * (s₁ * (t * s₂)) = (d * s₁) * (t * s₂) := by group
          _ = d * (s₁ * t) * s₂ := by group
          _ = d * (t * s₁) * s₂ := by rw [e2]
          _ = (d * t) * (s₁ * s₂) := by group
          _ = (t * d) * (s₁ * s₂) := by rw [e1]
          _ = t * (d * (s₁ * s₂)) := by group
          _ = (d * (s₁ * s₂)) * t := h
          _ = d * (s₁ * (s₂ * t)) := by group
      have h3 := mul_left_cancel h2
      have h4 := mul_left_cancel h3
      exact h4.symm
    have hs₁W : s₁ ∈ W := by
      have h := c.central_mem_inf_S P₁ hp₁ hs₁ hs₁c
      exact (sup_le hDW (Subgroup.zpowers_le.mpr hz₁W) : _ ≤ W) h
    have hs₂W : s₂ ∈ W := by
      have h := c.symm.central_mem_inf_S P₂ hp₂ hs₂ hs₂c
      rw [dsub_comm] at h
      exact (sup_le hDW (Subgroup.zpowers_le.mpr hz₂W) : _ ≤ W) h
    exact mul_mem (hDW hd) (mul_mem hs₁W hs₂W)
  have hR₁le : ∀ a ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁), a ∈ K₁ := fun a ha => (pCoreOf_le 2 _ ha).2
  have hR₂le : ∀ a ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₂), a ∈ K₂ := fun a ha => (pCoreOf_le 2 _ ha).2
  have hRc : ∀ a ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁), ∀ b ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₂),
      a * b = b * a := fun a ha b hb => hc₁₂ a (hR₁le a ha) b (hR₂le b hb)
  have hZ₀W : z0Of1469 Iz K₁ K₂ ≤ W := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := C5.mem_sup_of_commute hRc hy.1
    have hyc : ∀ t ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁) ⊔ pCoreOf 2 (oTwoUpper Iz ⊓ K₂),
        t * (a * b) = (a * b) * t := fun t ht => Subgroup.mem_centralizer_iff.mp hy.2 t ht
    have haW : a ∈ W := by
      have hac : ∀ t ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₁), a * t = t * a := by
        intro t ht
        have h := hyc t (Subgroup.mem_sup_left ht)
        have e : b * t = t * b := (hRc t ht b hb).symm
        have h2 : (t * a) * b = (a * t) * b := by
          calc (t * a) * b = t * (a * b) := by group
            _ = (a * b) * t := h
            _ = a * (b * t) := by group
            _ = a * (t * b) := by rw [e]
            _ = (a * t) * b := by group
        exact (mul_right_cancel h2).symm
      have := c.central_mem_of_sub P₁ hp₁ (T := pCoreOf 2 (oTwoUpper Iz ⊓ K₁)) c.R_inf_le
        (c.pf_surj_R P₁ hp₁ hnot₁) (c.noFix_R P₁ hp₁ hnot₁) ha hac
      exact (sup_le hDW (Subgroup.zpowers_le.mpr hz₁W) : _ ≤ W) this
    have hbW : b ∈ W := by
      have hbc : ∀ t ∈ pCoreOf 2 (oTwoUpper Iz ⊓ K₂), b * t = t * b := by
        intro t ht
        have h := hyc t (Subgroup.mem_sup_right ht)
        have e : a * t = t * a := hRc a ha t ht
        have h2 : a * (t * b) = a * (b * t) := by
          calc a * (t * b) = (a * t) * b := by group
            _ = (t * a) * b := by rw [e]
            _ = t * (a * b) := by group
            _ = (a * b) * t := h
            _ = a * (b * t) := by group
        exact (mul_left_cancel h2).symm
      have h := c.symm.central_mem_of_sub P₂ hp₂ (T := pCoreOf 2 (oTwoUpper Iz ⊓ K₂)) c.symm.R_inf_le
        (c.symm.pf_surj_R P₂ hp₂ hnot₂) (c.symm.noFix_R P₂ hp₂ hnot₂) hb hbc
      rw [dsub_comm] at h
      exact (sup_le hDW (Subgroup.zpowers_le.mpr hz₂W) : _ ≤ W) h
    exact mul_mem haW hbW
  have hz₁Z : zel P₁ p₁ ∈ z0Of1469 Iz K₁ K₂ := by
    have hz₁R₁ := c.zel_mem_R P₁ hp₁ hnot₁
    refine ⟨Subgroup.mem_sup_left hz₁R₁, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hle : pCoreOf 2 (oTwoUpper Iz ⊓ K₁) ⊔ pCoreOf 2 (oTwoUpper Iz ⊓ K₂) ≤
        Subgroup.centralizer ({zel P₁ p₁} : Set G) := by
      refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
        (fun a ha => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      · rw [Set.mem_singleton_iff.mp hh]
        exact (c.zel_central P₁ hp₁ ⟨c.R_inf_le ha |>.1, hR₁le a ha⟩).symm
      · rw [Set.mem_singleton_iff.mp hh]
        exact hc₁₂ _ hz₁K a (hR₂le a ha)
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) _ rfl).symm
  have hz₂Z : zel P₂ p₂ ∈ z0Of1469 Iz K₁ K₂ := by
    have hz₂R₂ := c.symm.zel_mem_R P₂ hp₂ hnot₂
    refine ⟨Subgroup.mem_sup_right hz₂R₂, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hle : pCoreOf 2 (oTwoUpper Iz ⊓ K₁) ⊔ pCoreOf 2 (oTwoUpper Iz ⊓ K₂) ≤
        Subgroup.centralizer ({zel P₂ p₂} : Set G) := by
      refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
        (fun a ha => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_)
      · rw [Set.mem_singleton_iff.mp hh]
        exact (hc₁₂ a (hR₁le a ha) _ hz₂K).symm
      · rw [Set.mem_singleton_iff.mp hh]
        exact (c.symm.zel_central P₂ hp₂ ⟨c.symm.R_inf_le ha |>.1, hR₂le a ha⟩).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) _ rfl).symm
  have hΩW : omegaOneCenterOf (pCoreOf 2 Iz) ≤ W := by
    unfold omegaOneCenterOf omegaOneOf
    exact (Subgroup.closure_le W).mpr fun x hx => hW2 x hx.1
  have hWDZ : W ≤ dsub S K₁ K₂ ⊔ z0Of1469 Iz K₁ K₂ := by
    refine sup_le (sup_le le_sup_left ?_) ?_
    · exact (Subgroup.zpowers_le.mpr hz₁Z).trans le_sup_right
    · exact (Subgroup.zpowers_le.mpr hz₂Z).trans le_sup_right
  exact le_antisymm (hΩW.trans hWDZ) ((sup_le hDW hZ₀W).trans hW1)

end A5Cfg

end CFSG.Quasithin.ModF

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input1469A5C567_of_res (h : Input1469A5Res) : Input1469A5C567 := by
  intro G _ _ I S Iz K₁ K₂ Λ hsq hchar hmin hblk h5₁ h5₂ hnot hyp hrel hC52
  obtain ⟨hD1, hD2⟩ := h G I S Iz K₁ K₂ Λ hsq hchar hmin hblk h5₁ h5₂ hnot hyp hrel hC52
  have c : ModF.A5Cfg I S Iz K₁ K₂ := ModF.A5Cfg.of_blockProduct hmin hblk h5₁ h5₂
  have hnot₂ : ¬ K₂ ≤ Iz := by
    intro h2
    obtain ⟨t, ht, htK⟩ : ∃ t ∈ S, B6.conjSub t K₁ = K₂ := by
      obtain ⟨-, -, -, -, -, htr, -⟩ := hblk
      simpa using htr 0 1
    apply hnot
    have h1 : B6.conjSub t⁻¹ K₂ ≤ B6.conjSub t⁻¹ Iz := (B6.conjSub t⁻¹).monotone h2
    rw [← htK, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at h1
    rwa [B6.conjSub_eq_self (Subgroup.le_normalizer (c.S_le_Iz (S.inv_mem ht)))] at h1
  exact ⟨hD1, hD2, c.pCoreOf_eq, c.omegaOneCenter_eq hD1 hnot hnot₂⟩

end CFSG.Quasithin
