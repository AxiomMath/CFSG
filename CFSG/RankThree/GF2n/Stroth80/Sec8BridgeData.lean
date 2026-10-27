module

public import CFSG.RankThree.GF2n.Stroth80.Sec8BridgeModel
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj
public import CFSG.RankThree.GF2n.Stroth80.Sec8OuterElt

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_bridge_data (hc : Ctx M Q Z B) {n : ℕ} {t r g l : G} (h : Sec8Outer hc n t r g)
    (hlL : l ∈ LB M Q B) (hm2 : SpMNat hc t 2) (hV : Vt M (LB M Q B) B Z t = Ut Q Z t)
    (h53b : ∀ s ∈ hc.CN t, ∀ y ∈ Sec8W1 M Q Z B t r, ⁅s, y⁆ ∈ Sec8V1 M Q Z B t r)
    (hnormLB : conjSubgroup (g * t * g⁻¹) (LB M Q B) = LB M Q B)
    (htightW : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Sec8W1 M Q Z B t r)
    (htightV : conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8V1 M Q Z B t r = Z)
    (hclaimB : conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓
      conjSubgroup (l * g) (Vt M (LB M Q B) B Z t) = Z)
    (hw : Nat.card Q = Nat.card Z ^ (2 * n + 1))
    (hcard : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (E : Type) (_ : AddCommGroup E)
      (_ : Module K E) (_ : Module.Finite K E) (B' : LinearMap.BilinForm K E)
      (X X' L : E →ₗ[K] E) (S Bpt : AddSubgroup E),
      B'.Nondegenerate ∧ (∀ e, B' e e = 0) ∧
      (∀ u v, B' (X u) (X v) = B' u v) ∧ (∀ u v, B' (X' u) (X' v) = B' u v) ∧
      Function.Surjective X ∧ Function.Surjective X' ∧
      (∀ e ∈ LinearMap.range (X - 1), (X' - 1) e = 0) ∧
      (∀ e, e ∈ LinearMap.range (X' - 1) ↔ ∃ e' ∈ LinearMap.range (X - 1), e = L e') ∧
      (∀ e, e ∈ LinearMap.range (X - 1) → e ∈ LinearMap.range (X' - 1) → e = 0) ∧
      Function.Injective L ∧
      Nat.card ↥(LinearMap.range (X - 1)) = Nat.card K ^ 4 ∧
      (∀ s ∈ S, ∀ s' ∈ S, B' s s' = 0) ∧ Nat.card ↥S * Nat.card ↥S = Nat.card E ∧
      Nat.card ↥Bpt ≤ Nat.card K ∧ (∀ s ∈ S, X' (X s) - s ∈ Bpt) ∧
      (∀ s ∈ S, L s - s ∈ Bpt) := by
  classical
  have hs := h.hs
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hgM := h.hg
  have hlM : l ∈ M := hc.LB_le_M hlL
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hlL
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hx'M : l * (g * t * g⁻¹) * l⁻¹ ∈ M := M.mul_mem (M.mul_mem hlM hxM) (M.inv_mem hlM)
  have hVV₁ : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hZV₁ : Z ≤ Sec8V1 M Q Z B t r := sec8_Z_le_V1 hc t r
  have hVx : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z :=
    fun v hv => h.hvan v (hVV₁ hv)
  obtain ⟨K, iF, iFin, iCh, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI := iCh
  have hxH : g * t * g⁻¹ ∈ H0 M Z := sec8_conj_mem_H0 hc hgM (hc.LB_le_H0 ht)
  have hxcz : ∀ z ∈ Z, (g * t * g⁻¹) * z * (g * t * g⁻¹)⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hxH.2 z hz, mul_inv_cancel_right]
  obtain ⟨Tx, hTx0, -, hTxB⟩ := hD.linear_of_centralizes hxM hxcz
  obtain ⟨Tl, hTl0, -, hTlB⟩ := hD.linear_of_centralizes hlM (hc.LB_centralizes_Z hlL)
  have hTx : Sec8ActsAs M₀ (g * t * g⁻¹) Tx := hTx0
  have hTl : Sec8ActsAs M₀ l Tl := hTl0
  have hx2 : (g * t * g⁻¹) ^ 2 ∈ Q := by
    have e : (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
    rw [e]
    exact hQn g hgM _ (hc.sq_mem_Q_of_mem_LB ht)
  have hTT : Tx * Tx = 1 := by
    have h1 : Sec8ActsAs M₀ ((g * t * g⁻¹) * (g * t * g⁻¹)) (Tx * Tx) := hTx.mul hQn hxM hTx
    have h2 : Sec8ActsAs M₀ ((g * t * g⁻¹) * (g * t * g⁻¹)) 1 :=
      Sec8ActsAs.of_mem_Q (by rwa [← pow_two])
    exact h1.unique h2
  have hTx' : Sec8ActsAs M₀ (l * (g * t * g⁻¹) * l⁻¹) (Tl * Tx * Tl⁻¹) :=
    (hTl.mul hQn hxM hTx).mul hQn (M.inv_mem hlM) (hTl.inv hQn hlM)
  have hx'2 : (l * (g * t * g⁻¹) * l⁻¹) ^ 2 ∈ Q := by
    have e : (l * (g * t * g⁻¹) * l⁻¹) ^ 2 = l * (g * t * g⁻¹) ^ 2 * l⁻¹ := by
      rw [pow_two, pow_two]; group
    rw [e]
    exact hQn l hlM _ hx2
  have hVgUt : conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z (g * t * g⁻¹) :=
    sec8_conj_V_eq_Ut hc hV hgM
  have hUt' : Ut Q Z (l * (g * t * g⁻¹) * l⁻¹) = conjSubgroup l (Ut Q Z (g * t * g⁻¹)) :=
    Ut_conj_of_normalizes (hc.conj_Q_eq hlM) (hc.conj_Z_eq hlM) _
  have hVlg : conjSubgroup (l * g) (Vt M (LB M Q B) B Z t) =
      Ut Q Z (l * (g * t * g⁻¹) * l⁻¹) := by
    rw [hUt', ← hVgUt, conjSubgroup_mul]
  have hinterUt : Ut Q Z (g * t * g⁻¹) ⊓ Ut Q Z (l * (g * t * g⁻¹) * l⁻¹) ≤ Z := by
    rw [← hVgUt, ← hVlg]
    exact hclaimB.le
  have hUtQ : Ut Q Z (g * t * g⁻¹) ≤ Q := by
    rw [← hVgUt]
    have h1 : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ conjSubgroup g Q :=
      Subgroup.map_mono (hc.Vt_le_Q t)
    rwa [hc.conj_Q_eq hgM] at h1
  have hcardUt : Nat.card ↥(Ut Q Z (g * t * g⁻¹)) = Nat.card Z ^ 5 := by
    rw [← hVgUt, card_conjSubgroup, hm2.card_V]
  have hēN : l * (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹ ∈ hc.CN t :=
    sec8_comm_mem_CN hc ht hxM h.hxt hVx hlR
  have hēM : l * (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹ ∈ M :=
    hc.Rt_le_M t (Ctx.mem_CN.mp hēN).1
  have hxe : l * (g * t * g⁻¹) * l⁻¹ =
      (l * (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
  have hinterV₁ : Sec8V1 M Q Z B t r ⊓ Ut Q Z (l * (g * t * g⁻¹) * l⁻¹) ≤ Z := by
    rw [hUt', ← hVgUt]
    have hfix := (sec8InvStatement_holds G M Q Z B hc n t hs r h.hr l hlR).1
    have h1 : conjSubgroup l (Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
        Sec8V1 M Q Z B t r ⊓ conjSubgroup l (conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
      rw [conjSubgroup_inf, hfix]
    rw [← h1, inf_comm, htightV, hc.conj_Z_eq hlM]
  have hSiso := sec8_bridge_S_iso M₀ hc hD
  have hScard := sec8_bridge_S_card M₀ hc hD hw hcard
  have hBcard := sec8_card_img_B_le M₀ hc hD
  have hSsub : ∀ s ∈ M₀.img (Q ⊓ QB B), ∃ a ∈ Q ⊓ QB B, M₀.π a = s := by
    intro s hs'
    obtain ⟨a, haS, -, rfl⟩ := (Tim79.QuadModel.mem_img M₀).mp hs'
    exact ⟨a, haS, rfl⟩
  have hcommB : ∀ m : G, m ∈ LB M Q B → ∀ T : M₀.E ≃ₗ[K] M₀.E, Sec8ActsAs M₀ m T →
      ∀ s ∈ M₀.img (Q ⊓ QB B), T s - s ∈ M₀.img B := by
    intro m hm T hT s hs'
    obtain ⟨a, ha, rfl⟩ := hSsub s hs'
    have haQ : a ∈ Q := (Subgroup.mem_inf.mp ha).1
    have hmM : m ∈ M := hc.LB_le_M hm
    have hmaQ : m * a * m⁻¹ ∈ Q := hQn m hmM a haQ
    have hcQ : ⁅m, a⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hmaQ (Q.inv_mem haQ)
    have hZB : ⁅m, a⁆ ∈ Z ⊔ B := hc.comm_LB_inf_QB_mem_sup hm ha
    have hπ := sec8_pi_comm M₀ haQ hmaQ (hT a haQ)
    rw [← hπ]
    exact sec8_img_sup_le M₀ hc (Tim79.QuadModel.pi_mem_img M₀ hZB hcQ)
  have hēL : l * (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹ ∈ LB M Q B := by
    have e : l * (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹ =
        l * ((g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹) := by group
    rw [e]
    exact (LB M Q B).mul_mem hlL ((mem_iff_conj_mem_of_eq hnormLB l⁻¹).mp ((LB M Q B).inv_mem hlL))
  have hTinv : Tx⁻¹ = Tx := inv_eq_of_mul_eq_one_right hTT
  have hTe : Sec8ActsAs M₀ (l * (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹) ((Tl * Tx * Tl⁻¹) * Tx) := by
    have := (hTx'.mul hQn (M.inv_mem hxM) (hTx.inv hQn hxM))
    rwa [hTinv] at this
  have hTlinvB : ∀ u v, M₀.B (Tl⁻¹ u) (Tl⁻¹ v) = M₀.B u v := fun u v =>
    calc M₀.B (Tl⁻¹ u) (Tl⁻¹ v) = M₀.B (Tl (Tl⁻¹ u)) (Tl (Tl⁻¹ v)) := (hTlB _ _).symm
      _ = M₀.B u v := by simp
  refine ⟨K, iF, iFin, iCh, M₀.E, inferInstance, inferInstance, inferInstance, M₀.B,
    (Tx : M₀.E →ₗ[K] M₀.E), ((Tl * Tx * Tl⁻¹ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E),
    (Tl : M₀.E →ₗ[K] M₀.E), M₀.img (Q ⊓ QB B), M₀.img B, ?_, M₀.alt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hSiso, hScard, hBcard, ?_, ?_⟩
  · exact ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩
  · exact fun u v => hTxB u v
  · intro u v
    show M₀.B (Tl (Tx (Tl⁻¹ u))) (Tl (Tx (Tl⁻¹ v))) = M₀.B u v
    rw [hTlB, hTxB, hTlinvB]
  · exact Tx.surjective
  · exact (Tl * Tx * Tl⁻¹).surjective
  · intro e he
    exact sec8_bridge_aa M₀ hc hD hxM hx2 hx'M hēM hxe hTx hTx' hTT hZV₁
      (fun w hw => htightW (hVgUt ▸ hw)) (h53b _ hēN) hinterV₁ e he
  · intro e
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨(Tx : M₀.E →ₗ[K] M₀.E) (Tl⁻¹ f) - Tl⁻¹ f, ⟨Tl⁻¹ f, by simp⟩, ?_⟩
      simp
    · rintro ⟨e', ⟨f, rfl⟩, rfl⟩
      refine ⟨Tl f, ?_⟩
      simp
  · intro e he he'
    exact sec8_bridge_disj M₀ hc hD hxM hx2 hx'M hx'2 hTx hTx' hinterUt e he he'
  · exact Tl.injective
  · exact sec8_bridge_dim M₀ hc hD hxM hx2 hTx hUtQ hcardUt
  · intro s hs'
    have := hcommB _ hēL _ hTe s hs'
    simpa using this
  · intro s hs'
    have := hcommB _ hlL _ hTl s hs'
    simpa using this

end

end CFSG.RankThree.GF2n.Stroth80
