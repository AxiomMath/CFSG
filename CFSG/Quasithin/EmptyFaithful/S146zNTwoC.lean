module

public import CFSG.Quasithin.EmptyFaithful.S146zNCov
public import CFSG.Quasithin.EmptyFaithful.S146zNTwoB
public import Certificates.Kernel.J4Count.FixCE

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Aux

variable {G : Type} [Group G]

theorem a6c_le_normalizer_of_commutator_le {U₁ K : Subgroup G} (h : ⁅U₁, K⁆ ≤ U₁) :
    K ≤ Subgroup.normalizer (U₁ : Set G) := by
  have key : ∀ k ∈ K, ∀ x ∈ U₁, k * x * k⁻¹ ∈ U₁ := by
    intro k hk x hx
    have h1 : ⁅x⁻¹, k⁆ ∈ U₁ := h (Subgroup.commutator_mem_commutator (U₁.inv_mem hx) hk)
    have e : k * x * k⁻¹ = x * ⁅x⁻¹, k⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact U₁.mul_mem hx h1
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

theorem a6c_Z_le {Z X K : Subgroup G} (hZX : Z ≤ X) (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) :
    Z ≤ centralizerMod Z X K := fun z hz => by
  refine ⟨hZX hz, Subgroup.le_normalizer hz, fun u hu => ?_⟩
  have h1 : u * z⁻¹ * u⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hKZ hu) z⁻¹).mp
    (Subgroup.inv_mem _ hz)
  have e : z * u * z⁻¹ * u⁻¹ = z * (u * z⁻¹ * u⁻¹) := by group
  rw [e]
  exact Z.mul_mem hz h1

theorem a6c_irr_sup {U₁ F K F₁ : Subgroup G} (hcomm : ∀ x ∈ U₁, ∀ y ∈ F, x * y = y * x)
    (hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G)) (hinf : U₁ ⊓ F = F₁)
    (hirr : ∀ W : Subgroup G, F₁ ≤ W → W ≤ U₁ → K ≤ Subgroup.normalizer (W : Set G) →
      W = F₁ ∨ W = U₁) :
    ∀ W : Subgroup G, F ≤ W → W ≤ U₁ ⊔ F → K ≤ Subgroup.normalizer (W : Set G) →
      W = F ∨ W = U₁ ⊔ F := by
  intro W hFW hWU hKW
  have hUF : U₁ ≤ Subgroup.normalizer (F : Set G) := le_normalizer_of_forall_commute hcomm
  have hF₁W : F₁ ≤ W ⊓ U₁ := fun x hx => by
    rw [← hinf] at hx
    exact ⟨hFW hx.2, hx.1⟩
  have hKW₁ : K ≤ Subgroup.normalizer ((W ⊓ U₁ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKW hk, hKU₁ hk⟩
  rcases hirr (W ⊓ U₁) hF₁W inf_le_right hKW₁ with h | h
  · left
    refine le_antisymm (fun w hw => ?_) hFW
    have hw' : w ∈ ((U₁ ⊔ F : Subgroup G) : Set G) := hWU hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUF] at hw'
    obtain ⟨a, ha, f, hf, rfl⟩ := hw'
    have haW : a ∈ W := by
      have := W.mul_mem hw (W.inv_mem (hFW hf))
      simpa using this
    have : a ∈ W ⊓ U₁ := ⟨haW, ha⟩
    rw [h, ← hinf] at this
    exact F.mul_mem this.2 hf
  · right
    refine le_antisymm hWU (sup_le ?_ hFW)
    intro x hx
    have : x ∈ W ⊓ U₁ := by rw [h]; exact hx
    exact this.1

end Aux

section Rank5

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem a6rk_rank5 (hA6 : A6Amt) (hNo : A6NoIrr5) (S : Setting146 G T M) {K U₁ U₂ : Subgroup G}
    {s u : G} (hctx : Ctx24 T M K U₁ U₂ s u) (hKA : KbarIsA6 K) (hKeq : K = perfectCore (mcOf T))
    (h5 : mIdx U₁ Zz = 5 ∧ ⁅U₁, K⁆ ⊔ Zz = U₁) {X : Subgroup G}
    (hX : QCrit Zz (VZ T M) (mcOf T) X) :
    2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) =
        mIdx (conjClosure (VZ T M) (mcOf T))
          (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) X) ∧
      ∃ x ∈ X, mIdx X (X ⊓ pCoreOf 2 (mcOf T)) + 2 ≤
        mIdx (conjClosure (VZ T M) (mcOf T))
          (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) (Subgroup.zpowers x)) := by
  classical
  obtain ⟨c19, -, c23, hKc, -, -, hdec, -⟩ := hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hsimple : IsSimpleGroup (KBar K) := (c19 (mcOf T) hG).2 K hKc
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  have hTH : T ≤ mcOf T := hG.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hHKT : mcOf T = K ⊔ T := by
    rw [hKeq]
    exact c23.1.2
  have hKH : K ≤ mcOf T := le_of_mem_cComp hKc
  have hHZ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := fun x hx => S.normalizer_Z.ge hx
  have hHU : mcOf T ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hZU : Zz ≤ conjClosure (VZ T M) (mcOf T) := Z_le_conjClosure_VZ T M (mcOf T)
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (conjClosure (VZ T M) (mcOf T)) := isPGroup_of_isElemAbelian hUab
  have hUc : ∀ x ∈ conjClosure (VZ T M) (mcOf T), ∀ y ∈ conjClosure (VZ T M) (mcOf T),
      x * y = y * x := fun x hx y hy => isElemAbelian_comm hUab hx hy
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hUKU : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
    S145.commutator_le_of_le_normalizer (hKH.trans hHU)
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G,
      E = ⁅conjClosure (VZ T M) (mcOf T), K⁆ ⊔ Zz := ⟨_, rfl⟩
  have hEU : E ≤ conjClosure (VZ T M) (mcOf T) := hEdef ▸ sup_le hUKU hZU
  have hZE : Zz ≤ E := hEdef ▸ le_sup_right
  have hHE : mcOf T ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEdef]
    exact fun h hh => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨F9.le_normalizer_commutator_of_le hHU hKn hh, hHZ hh⟩
  have hsup : U₁ ⊔ U₂ = E := by
    rw [hEdef]
    exact hdec.sup.symm
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hdec.mem.2
  have hsH : s ∈ mcOf T := hTH hdec.mem.1
  have hU₁E : U₁ ≤ E := hsup ▸ le_sup_left
  have hU₂E : U₂ ≤ E := hsup ▸ le_sup_right
  have hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G) :=
    a6c_le_normalizer_of_commutator_le (calc ⁅U₁, K⁆ ≤ ⁅U₁, K⁆ ⊔ Zz := le_sup_left
      _ = U₁ := h5.2)
  have hKU₂ : K ≤ Subgroup.normalizer (U₂ : Set G) := by
    rw [hdec.conj]
    exact le_normalizer_conjSub hsK hKU₁
  have hf : KbarFusesThrees K s := by
    rcases hdec.dynkin with ⟨hL3, -⟩ | ⟨-, hf⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 hKA).elim
    · exact hf
  have hKZ : K ≤ Subgroup.normalizer (Zz : Set G) := hKH.trans hHZ
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup G, F = centralizerMod Zz E K := ⟨_, rfl⟩
  have hFE : F ≤ E := hFdef ▸ centralizerMod_le_left _ _ _
  have hZF : Zz ≤ F := by rw [hFdef]; exact a6c_Z_le hZE hKZ
  have hHF : mcOf T ≤ Subgroup.normalizer (F : Set G) := by
    rw [hFdef]
    exact le_normalizer_centralizerMod hHZ hHE hKn
  have hKF : K ≤ Subgroup.normalizer (F : Set G) := hKH.trans hHF
  have hEF : E ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_of_forall_commute fun e he f hf => hUc e (hEU he) f (hEU (hFE hf))
  have hUab₁ : IsElemAbelian 2 U₁ := a6c_isElemAbelian_of_le hUab (hU₁E.trans hEU)
  have hQ₁ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Zz := fun p hp w hw =>
    S.comm_mem_Z hG (hEU (hU₁E hw)) (hQK hp)
  have hcov := a6c_cov hNo hKA hUab₁ hdec.Z₁ hKZ hKU₁ h5.1 h5.2 hQ₁
  have hinf : U₁ ⊓ F = centralizerMod Zz U₁ K := by
    ext x
    rw [hFdef]
    constructor
    · rintro ⟨hxU, hxF⟩
      exact ⟨hxU, hxF.2.1, hxF.2.2⟩
    · rintro ⟨hxU, hxN, hx⟩
      exact ⟨hxU, hU₁E hxU, hxN, hx⟩
  have hcommU₁F : ∀ x ∈ U₁, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    hUc x (hEU (hU₁E hx)) y (hEU (hFE hy))
  have hU₁'E : U₁ ⊔ F ≤ E := sup_le hU₁E hFE
  have hU₂'E : U₂ ⊔ F ≤ E := sup_le hU₂E hFE
  have hsup' : (U₁ ⊔ F) ⊔ (U₂ ⊔ F) = E := by
    refine le_antisymm (sup_le hU₁'E hU₂'E) ?_
    rw [← hsup]
    exact sup_le_sup le_sup_left le_sup_left
  have hconj' : U₂ ⊔ F = conjSub s (U₁ ⊔ F) := by
    rw [conjSub_sup, ← hdec.conj, conjSub_eq_of_mem_normalizer (hHF hsH)]
  have hKU₁' : K ≤ Subgroup.normalizer ((U₁ ⊔ F : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hKU₁ hk, hKF hk⟩
  have hKU₂' : K ≤ Subgroup.normalizer ((U₂ ⊔ F : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hKU₂ hk, hKF hk⟩
  have hP : IsPGroup 2 ↥(U₁ ⊔ F) := hUp.to_le (hU₁'E.trans hEU)
  have hcard : mIdx (U₁ ⊔ F) F = 4 := by
    have h1 := ThreeC.mIdx_sup_of_inf_eq hcommU₁F inf_le_left inf_le_right rfl hP
    have h2 := ThreeC.mIdx_add hP (le_sup_right : F ≤ U₁ ⊔ F) (inf_le_right : U₁ ⊓ F ≤ F)
    have h3 := hcov.1
    rw [← hinf] at h3
    omega
  have hirr' := a6c_irr_sup hcommU₁F hKU₁ hinf hcov.2
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := hKH.trans hHE
  have hQE : ∀ p ∈ pCoreOf 2 K, ∀ e ∈ E, p * e * p⁻¹ * e⁻¹ ∈ F := fun p hp e he =>
    hZF (S.comm_mem_Z hG (hEU he) (hQK hp))
  have hnt : ∃ k ∈ K, ∃ e ∈ E, k * e * k⁻¹ * e⁻¹ ∉ F := by
    by_contra hcon
    push Not at hcon
    have hU₁K : ⁅U₁, K⁆ ≤ U₁ := calc ⁅U₁, K⁆ ≤ ⁅U₁, K⁆ ⊔ Zz := le_sup_left
      _ = U₁ := h5.2
    have h1 : ⁅U₁, K⁆ ≤ centralizerMod Zz U₁ K := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      have h2 : ⁅a, k⁆ ∈ U₁ := hU₁K (Subgroup.commutator_mem_commutator ha hk)
      have h3 : ⁅a, k⁆ ∈ F := by
        have e : ⁅a, k⁆ = (k * a * k⁻¹ * a⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        rw [e]
        exact F.inv_mem (hcon k hk a (hU₁E ha))
      rw [← hinf]
      exact ⟨h2, h3⟩
    have h2 : U₁ ≤ centralizerMod Zz U₁ K := calc U₁ = ⁅U₁, K⁆ ⊔ Zz := h5.2.symm
      _ ≤ _ := sup_le h1 (a6c_Z_le hdec.Z₁ hKZ)
    have h3 : (centralizerMod Zz U₁ K).relIndex U₁ = 1 := Subgroup.relIndex_eq_one.mpr h2
    have h4 := hcov.1
    unfold mIdx at h4
    rw [h3] at h4
    simp at h4
  have hker : centralizerMod F K E = pCoreOf 2 K := by
    refine le_antisymm (a6k_centralizerMod_le hKF hKE hsimple hQE hnt) ?_
    intro p hp
    exact ⟨pCoreOf_le 2 K hp, hKF (pCoreOf_le 2 K hp), fun e he => hQE p hp e he⟩
  have hQ : centralizerMod F (mcOf T) E = pCoreOf 2 (mcOf T) := by
    refine le_antisymm (a6k_centralizerMod_H_le hKc hsimple hKn hT2 hHKT hHF hHE
      (by rw [hker]; exact hQK)) ?_
    intro x hx
    rw [← S.lemma_14_5_15_four hG] at hx
    exact ⟨hx.1, hHF hx.1, fun e he => hZF (hx.2.2 e (hEU he))⟩
  obtain ⟨hXH, hXab, hXnt, hquad, hidx⟩ := hX
  have hCU : mIdx (conjClosure (VZ T M) (mcOf T))
      (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) X) ≤
      2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) := by
    have hXp : IsPGroup 2 X := isPGroup_of_isElemAbelian hXab
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp, HypF98.relIndex_eq_two_pow_mIdx hXp, ← pow_mul,
      mul_comm] at hidx
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hidx
  have hmono : ∀ Y : Subgroup G,
      mIdx E (centralizerMod F E Y) ≤ mIdx E (centralizerMod Zz E Y) := fun Y =>
    ThreeC.mIdx_anti_of_le (X := E) fun x hx =>
      ⟨hx.1, hEF hx.1, fun b hb => hZF (hx.2.2 b hb)⟩
  have hr : mIdx E (centralizerMod F E X) ≤ 2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) :=
    (hmono X).trans ((a6k_mIdx_centralizerMod_le hUp hEU).trans hCU)
  obtain ⟨hc1, x, hxX, hc2⟩ := a6amt_group hA6 (Z₀ := F) (U₁ := U₁ ⊔ F) (U₂ := U₂ ⊔ F)
    hUab hFE hEU hHF hHE hKH hXH hKn hsH hQ hker le_sup_right hsup' hconj' hKU₁' hKU₂' hcard
    hirr' hKA hf hXab hXnt
    (fun b₁ hb₁ b₂ hb₂ e he => hZF (hquad b₁ hb₁ b₂ hb₂ e (hEU he))) hr
  have hle : 2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) ≤
      mIdx (conjClosure (VZ T M) (mcOf T))
        (centralizerMod Zz (conjClosure (VZ T M) (mcOf T)) X) := by
    have h1 := hmono X
    have h2 := a6k_mIdx_centralizerMod_le (Z₀ := Zz) (X := X) hUp hEU
    omega
  exact ⟨le_antisymm hle hCU, x, hxX,
    hc2.trans ((hmono _).trans (a6k_mIdx_centralizerMod_le hUp hEU))⟩

end Rank5

end CFSG.Quasithin
