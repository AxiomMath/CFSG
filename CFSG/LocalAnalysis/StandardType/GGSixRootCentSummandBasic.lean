module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailCanon
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFRootCentAutK
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.StandardType.GGSixOddIndexCore
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Pieces

variable {X : Type} [Group X]

@[expose] def GGRCSPiece (p : ℕ) (V S Q : Subgroup X) : Prop :=
  S ≤ V ∧ IsSubnormal S V ∧ ⁅S, S⁆ = S ∧ p ∣ Nat.card S ∧
    S ≤ Subgroup.closure {s : X | s ∈ S ∧ ∃ n : ℕ, s ^ p ^ n = 1} ∧
    Q ≤ S ∧ IsPGroup 2 Q ∧ (Q.subgroupOf V).Normal ∧
    ∀ [(Q.subgroupOf S).Normal], CFSG.IsQuasisimple (↥S ⧸ Q.subgroupOf S)

@[expose] def GGRCSQuasiPiece (p : ℕ) (V S : Subgroup X) : Prop :=
  ∃ Q : Subgroup X, GGRCSPiece p V S Q

@[expose] def GGRCSSThreePiece (V S : Subgroup X) : Prop :=
  ∃ R₀ Q : Subgroup X, S ≤ R₀ ∧ R₀ ≤ V ∧ (R₀.subgroupOf V).Normal ∧ Q ≤ S ∧ IsPGroup 2 Q ∧
    (Q.subgroupOf V).Normal ∧ Nat.card S = 3 * Nat.card Q ∧
    ∀ [(Q.subgroupOf R₀).Normal], Nonempty (↥R₀ ⧸ Q.subgroupOf R₀ ≃* Equiv.Perm (Fin 3))

@[expose] def GGRCSAutKSetting (p : ℕ) (V E K S : Subgroup X) : Prop :=
  CFSG.IsComponent K ∧ ¬ K ≤ V ∧ E ≤ Subgroup.normalizer (K : Set X) ∧ S ≤ K ∧
    GGRCSQuasiPiece p V S

theorem ggRCS_normal_subgroupOf {V S Q : Subgroup X} (hSV : S ≤ V) (hQS : Q ≤ S)
    (hQn : (Q.subgroupOf V).Normal) : (Q.subgroupOf S).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hQS]
  intro q s hq hs
  rw [Subgroup.normal_subgroupOf_iff (hQS.trans hSV)] at hQn
  exact hQn q s hq (hSV hs)

theorem ggRCS_isSubnormal_of_top {H K : Subgroup X} (h : IsSubnormal H K) (hK : K = ⊤) :
    H.IsSubnormal :=
  h.mathlib (by rw [hK]; exact Subgroup.IsSubnormal.top)

theorem ggRCS_isComponent_of_isComponentOf_top {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    CFSG.IsComponent K :=
  ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK.2.2,
    ggRCS_isSubnormal_of_top hK.2.1 rfl⟩

theorem ggRCS_isComponentOf_map_quot {V S Q : Subgroup X} (hSV : S ≤ V) (hsn : IsSubnormal S V)
    [(Q.subgroupOf V).Normal] [(Q.subgroupOf S).Normal]
    (hq : CFSG.IsQuasisimple (↥S ⧸ Q.subgroupOf S)) :
    IsComponentOf ((S.subgroupOf V).map (QuotientGroup.mk' (Q.subgroupOf V))) ⊤ := by
  set π := QuotientGroup.mk' (Q.subgroupOf V) with hπ
  let φ : ↥S →* ↥V ⧸ Q.subgroupOf V := π.comp (Subgroup.inclusion hSV)
  have hrange : φ.range = (S.subgroupOf V).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = Q.subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change π (Subgroup.inclusion hSV s) = 1 ↔ _
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  let e : ↥S ⧸ Q.subgroupOf S ≃* ↥((S.subgroupOf V).map π) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨le_top, ?_, ?_⟩
  · have h1 : IsSubnormal (S.subgroupOf V) ⊤ := by
      have h := ggAssemblyIsSubnormal_subgroupOf hsn V
      rwa [Subgroup.subgroupOf_self] at h
    have h2 := ggIsSubnormal_map π h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)

theorem ggRCS_not_mem_of_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X}
    (hQ2 : IsPGroup 2 Q) {s : X} (hs : orderOf s = p) : s ∉ Q := by
  intro hsQ
  obtain ⟨k, hk⟩ := hQ2 ⟨s, hsQ⟩
  have h1 : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : p ∣ 2 ^ k := hs ▸ orderOf_dvd_of_pow_eq_one h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

end Pieces

section Centralizer

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem ggRCS_inf_pPrimeCore_eq_bot {p : ℕ} (hO2 : CFSG.pCore 2 X = ⊥) {V Q : Subgroup X}
    (hO : LargeEvenPPrimeCore p X ≤ V) (hQV : Q ≤ V) (hQ2 : IsPGroup 2 Q)
    (hQn : (Q.subgroupOf V).Normal) : Q ⊓ LargeEvenPPrimeCore p X = ⊥ := by
  set O := LargeEvenPPrimeCore p X with hOdef
  have hOn : O.Normal := LargeEvenPPrimeCore.normal p X
  set R : Subgroup X := (CFSG.pCore 2 ↥O).map O.subtype with hRdef
  have hRn : R.Normal := ConjAct.normal_of_characteristic_of_normal
  have hR2 : IsPGroup 2 R := (CFSG.pCore_isPGroup (p := 2)).map _
  have hRbot : R = ⊥ := le_bot_iff.mp (hO2 ▸ le_sSup ⟨hRn, hR2⟩)
  have hT : (Q ⊓ O).subgroupOf O ≤ CFSG.pCore 2 ↥O := by
    refine le_sSup ⟨?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro a o ha ho
      rw [Subgroup.normal_subgroupOf_iff hQV] at hQn
      exact ⟨hQn a o ha.1 (hO ho), hOn.conj_mem a ha.2 o⟩
    · intro y
      obtain ⟨k, hk⟩ := hQ2 ⟨((y : ↥O) : X), (Subgroup.mem_subgroupOf.mp y.2).1⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
  rw [eq_bot_iff]
  intro y hy
  have hyR : y ∈ R := ⟨⟨y, hy.2⟩, hT (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  rw [hRbot] at hyR
  exact hyR

theorem ggRCS_le_centralizer_pPrimeCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO2 : CFSG.pCore 2 X = ⊥) {V S : Subgroup X} (hO : LargeEvenPPrimeCore p X ≤ V)
    (hS : GGRCSQuasiPiece p V S) :
    S ≤ Subgroup.centralizer (LargeEvenPPrimeCore p X : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hSV, hsn, -, hpS, -, hQS, hQ2, hQn, hq⟩ := hS
  have hQSn : (Q.subgroupOf S).Normal := ggRCS_normal_subgroupOf hSV hQS hQn
  set O := LargeEvenPPrimeCore p X with hOdef
  have hOn : O.Normal := LargeEvenPPrimeCore.normal p X
  set π := QuotientGroup.mk' (Q.subgroupOf V) with hπ
  have hC := ggRCS_isComponentOf_map_quot hSV hsn (@hq hQSn)
  have hFn : ((O.subgroupOf V).map π).Normal :=
    (hOn.subgroupOf V).map π (QuotientGroup.mk'_surjective _)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) p hpS
  have hs' : orderOf (s : X) = p := (Subgroup.orderOf_coe s).trans hs
  have hsQ : (s : X) ∉ Q := ggRCS_not_mem_of_two hp hp2 hQ2 hs'
  have hc1 : π ⟨s, hSV s.2⟩ ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hsQ h
  have hcp : π ⟨s, hSV s.2⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨s, hSV s.2⟩ : ↥V) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (s : X) ^ p = 1
      rw [← hs']
      exact pow_orderOf_eq_one _
    rw [h1, map_one]
  have hco : orderOf (π ⟨s, hSV s.2⟩) = p := orderOf_eq_prime hcp hc1
  have hCF : ¬ (S.subgroupOf V).map π ≤ (O.subgroupOf V).map π := by
    intro hle
    have hcF := hle ⟨⟨s, hSV s.2⟩, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
    have h1 : p ∣ Nat.card ((O.subgroupOf V).map π) :=
      hco ▸ Subgroup.orderOf_dvd_natCard _ hcF
    have h2 : Nat.card ((O.subgroupOf V).map π) ∣ Nat.card (O.subgroupOf V) :=
      Subgroup.card_map_dvd _ _
    have h3 : Nat.card (O.subgroupOf V) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO).toEquiv
    have hcop : Nat.Coprime p (Nat.card O) := CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop (h3 ▸ h1.trans h2)
  rcases ggComponent_le_or_commute hC (hFn.subgroupOf ⊤).isSubnormal with hle | hcomm
  · exact absurd hle hCF
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have hoV : o ∈ V := hO ho
  have h1 := hcomm (π ⟨x, hSV hx⟩) ⟨⟨x, hSV hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    (π ⟨o, hoV⟩) ⟨Subgroup.mem_top _, ⟨o, hoV⟩, Subgroup.mem_subgroupOf.mpr ho, rfl⟩
  have hk : x * o * x⁻¹ * o⁻¹ ∈ Q := by
    have h2 : π ((⟨x, hSV hx⟩ : ↥V) * ⟨o, hoV⟩ * (⟨x, hSV hx⟩ : ↥V)⁻¹ * (⟨o, hoV⟩ : ↥V)⁻¹) =
        1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hkO : x * o * x⁻¹ * o⁻¹ ∈ O := O.mul_mem (hOn.conj_mem o ho x) (O.inv_mem ho)
  have hQO := ggRCS_inf_pPrimeCore_eq_bot hO2 hO (hQS.trans hSV) hQ2 hQn
  have hk1 : x * o * x⁻¹ * o⁻¹ = 1 := by
    have h3 : x * o * x⁻¹ * o⁻¹ ∈ Q ⊓ O := ⟨hk, hkO⟩
    rw [hQO] at h3
    exact h3
  calc o * x = (x * o * x⁻¹ * o⁻¹)⁻¹ * (x * o) := by group
    _ = x * o := by rw [hk1, inv_one, one_mul]

end Centralizer

section Quotient

variable {X : Type} [Group X]

@[expose] def ggRCSU (V E K : Subgroup X) : Subgroup X :=
  (E ⊔ (K ⊓ V)) ⊓ Subgroup.centralizer (K : Set X)

theorem ggRCSU_normal {V E K : Subgroup X} (hEK : E ≤ Subgroup.normalizer (K : Set X)) :
    ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal := by
  have hVW : ggRCSU V E K ≤ E ⊔ K := fun v hv =>
    (sup_le_sup_left inf_le_left E : E ⊔ (K ⊓ V) ≤ E ⊔ K) (Subgroup.mem_inf.mp hv).1
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVW]
  have fwdE : ∀ e ∈ E, ∀ v ∈ ggRCSU V E K, e * v * e⁻¹ ∈ ggRCSU V E K := by
    intro e he v hv
    obtain ⟨hvH, hvC⟩ := Subgroup.mem_inf.mp hv
    have heH : e ∈ E ⊔ (K ⊓ V) := (le_sup_left : E ≤ E ⊔ (K ⊓ V)) he
    refine Subgroup.mem_inf.mpr ⟨(E ⊔ (K ⊓ V)).mul_mem
      ((E ⊔ (K ⊓ V)).mul_mem heH hvH) ((E ⊔ (K ⊓ V)).inv_mem heH), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : e⁻¹ * k * e ∈ K := by
      have h0 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (K : Set X)).inv_mem (hEK he)) k).mp hk
      simpa using h0
    have h := Subgroup.mem_centralizer_iff.mp hvC (e⁻¹ * k * e) hk'
    calc k * (e * v * e⁻¹) = e * ((e⁻¹ * k * e) * v) * e⁻¹ := by group
      _ = e * (v * (e⁻¹ * k * e)) * e⁻¹ := by rw [h]
      _ = e * v * e⁻¹ * k := by group
  have fwdK : ∀ k ∈ K, ∀ v ∈ ggRCSU V E K, k * v * k⁻¹ ∈ ggRCSU V E K := by
    intro k hk v hv
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 k hk
    rw [h, mul_inv_cancel_right]
    exact hv
  have hnorm : ∀ Y : Subgroup X,
      (∀ g ∈ Y, ∀ v ∈ ggRCSU V E K, g * v * g⁻¹ ∈ ggRCSU V E K) →
      Y ≤ Subgroup.normalizer (ggRCSU V E K : Set X) := by
    intro Y hY g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hY g hg v, fun hv => ?_⟩
    have h0 := hY g⁻¹ (Y.inv_mem hg) _ hv
    simpa [mul_assoc] using h0
  exact sup_le (hnorm E fwdE) (hnorm K fwdK)

theorem ggRCS_hypRestII [Finite X] {p : ℕ} [Fact p.Prime] {V E K : Subgroup X}
    (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hK : CFSG.IsComponent K)
    (hcat : InCatalog (↥K ⧸ Subgroup.center ↥K))
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    GGHypRestII (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)) := by
  have hYV : (E ⊔ K) ⊓ Subgroup.centralizer (K : Set X) ≤ ggRCSU V E K := by
    intro w hw
    have hwV : w ∈ V := ggAKFT_centralizer_le hfus hE hEcard hEK hw
    exact Subgroup.mem_inf.mpr
      ⟨ggAKFT_sup_inf_le hfus.1 hEK (Subgroup.mem_inf.mpr ⟨hw.1, hwV⟩), hw.2⟩
  set W₀ := E ⊔ K with hW₀
  set U := ggRCSU V E K with hU
  set π : ↥W₀ →* ↥W₀ ⧸ U.subgroupOf W₀ := QuotientGroup.mk' (U.subgroupOf W₀) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ1 : ∀ w : ↥W₀, π w = 1 ↔ (w : X) ∈ U := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hUC : U ≤ Subgroup.centralizer (K : Set X) := inf_le_right
  have hKW : K ≤ W₀ := le_sup_right
  have hKn : (K.subgroupOf W₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKW]
    intro h k hh hk
    have hkN : k ∈ Subgroup.normalizer (K : Set X) := (sup_le hEK Subgroup.le_normalizer) hk
    exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
  have hKnat : CFSG.IsQuasisimple ↥K := hK.1
  have hKA : CFSG.Assembly.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hKnat
  have hKcW : IsComponentOf K W₀ := ⟨hKW, ggIsSubnormal_of_normal hKW hKn, hKA⟩
  set Kbar : Subgroup (↥W₀ ⧸ U.subgroupOf W₀) := (K.subgroupOf W₀).map π with hKbar
  let φ : ↥K →* ↥Kbar := (π.comp (Subgroup.inclusion hKW)).codRestrict Kbar
    (fun k => ⟨Subgroup.inclusion hKW k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, w, hw, rfl⟩
    exact ⟨⟨(w : X), Subgroup.mem_subgroupOf.mp hw⟩, Subtype.ext rfl⟩
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hk g
      have h1 : π (Subgroup.inclusion hKW k) = 1 := congrArg Subtype.val hk
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hUC ((hπ1 _).mp h1)) g g.2)
    · intro hk
      apply Subtype.ext
      change π (Subgroup.inclusion hKW k) = 1
      rw [hπ1]
      refine hYV (Subgroup.mem_inf.mpr ⟨hKW k.2, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (hk ⟨g, hg⟩)
  let eK : ↥Kbar ≃* ↥K ⧸ Subgroup.center ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hφker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).symm
  have hKnotker : ¬ K.subgroupOf W₀ ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hKcW fun a ha c hc => ?_
    have haU : a ∈ U := (hπ1 ⟨a, hKW ha⟩).mp (hle (Subgroup.mem_subgroupOf.mpr ha))
    exact (Subgroup.mem_centralizer_iff.mp (hUC haU) c hc).symm
  have hKcomp : CFSG.IsComponent (K.subgroupOf W₀) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKW).mp hKcW
  have hKbarC : CFSG.IsComponent Kbar :=
    ⟨CFSG.LocalCores.isQuasisimple_map hKcomp.1 π hKnotker, (hKn.map π hπs).isSubnormal⟩
  have hCbar : Subgroup.centralizer (Kbar : Set (↥W₀ ⧸ U.subgroupOf W₀)) = ⊥ := by
    rw [eq_bot_iff]
    intro wbar hwbar
    obtain ⟨w, rfl⟩ := hπs wbar
    rw [Subgroup.mem_bot, hπ1]
    refine hYV (Subgroup.mem_inf.mpr ⟨w.2, ?_⟩)
    have hconj : ∀ k : ↥K, (w : X) * k * (w : X)⁻¹ ∈ K := fun k => by
      have h := hKn.conj_mem (Subgroup.inclusion hKW k) (Subgroup.mem_subgroupOf.mpr k.2) w
      exact Subgroup.mem_subgroupOf.mp h
    let α : ↥K →* ↥K := MonoidHom.mk' (fun k => ⟨(w : X) * k * (w : X)⁻¹, hconj k⟩)
      (fun a c => Subtype.ext (by simp [mul_assoc]))
    have hα : ∀ k : ↥K, k⁻¹ * α k ∈ Subgroup.center ↥K := by
      intro k
      have hcomm := Subgroup.mem_centralizer_iff.mp hwbar (π (Subgroup.inclusion hKW k))
        ⟨_, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
      have h1 : π ((Subgroup.inclusion hKW k)⁻¹ * (w * Subgroup.inclusion hKW k * w⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
        group
      have h2 := hUC ((hπ1 _).mp h1)
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h3 := Subgroup.mem_centralizer_iff.mp h2 (g : X) g.2
      simpa [α, mul_assoc] using h3
    have hαid := ggAKF_eq_of_mem_center hKA.1 α hα
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 : (w : X) * k * (w : X)⁻¹ = k := congrArg Subtype.val (hαid ⟨k, hk⟩)
    calc k * (w : X) = ((w : X) * k * (w : X)⁻¹) * w := by rw [h2]
      _ = w * k := by group
  have hF : CFSG.generalizedFitting (↥W₀ ⧸ U.subgroupOf W₀) = Kbar :=
    ggAKFT_generalizedFitting_eq hKbarC hCbar
  unfold GGHypRestII
  rw [hF]
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKnat.2.1
  have : Nontrivial ↥Kbar := eK.toEquiv.nontrivial
  obtain ⟨a, c, hac⟩ := hKnat.2.2
  exact ⟨IsSimpleGroup.isSimpleGroup_of_surjective eK.symm.toMonoidHom eK.symm.surjective,
    ⟨eK.symm a, eK.symm c, fun h => hac (eK.symm.injective (by rw [map_mul, map_mul, h]))⟩,
    inCatalog_of_mulEquiv eK hcat⟩

end Quotient

section Layer

variable {X : Type} [Group X] [Finite X]

theorem ggRCS_layer_ne_bot {p : ℕ} (hp : p.Prime) {V E K S : Subgroup X} (hEV : E ≤ V)
    (hS : GGRCSQuasiPiece p V S) (hSK : S ≤ K)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    LargeEvenLayer (⊤ : Subgroup (GGHypQuot (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map
      (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))))) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hSV, hsn, hperf, hpS, -, hQS, hQ2, hQn, hq⟩ := hS
  have hQSn : (Q.subgroupOf S).Normal := ggRCS_normal_subgroupOf hSV hQS hQn
  have hq' : CFSG.IsQuasisimple (↥S ⧸ Q.subgroupOf S) := @hq hQSn
  set W := E ⊔ K with hW
  set H := E ⊔ (K ⊓ V) with hH
  set U := ggRCSU V E K with hU
  set π : ↥W →* ↥W ⧸ U.subgroupOf W := QuotientGroup.mk' (U.subgroupOf W) with hπ
  set Ht := (H.subgroupOf W).map π with hHt
  have hHW : H ≤ W := sup_le_sup_left inf_le_left E
  have hHV : H ≤ V := sup_le hEV inf_le_right
  have hSH : S ≤ H := (le_inf hSK hSV).trans le_sup_right
  have hQH : Q ≤ H := hQS.trans hSH
  let ι : ↥H →* ↥Ht := (π.comp (Subgroup.inclusion hHW)).codRestrict Ht
    (fun h => ⟨Subgroup.inclusion hHW h, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩)
  have hιs : Function.Surjective ι := by
    rintro ⟨_, w, hw, rfl⟩
    exact ⟨⟨(w : X), Subgroup.mem_subgroupOf.mp hw⟩, Subtype.ext rfl⟩
  have hι1 : ∀ h : ↥H, ι h = 1 → (h : X) ∈ U := by
    intro h h1
    have h2 : π (Subgroup.inclusion hHW h) = 1 := congrArg Subtype.val h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  set O2 := CFSG.pCore 2 ↥Ht with hO2
  let ρ : ↥H →* GGHypQuot Ht := (QuotientGroup.mk' O2).comp ι
  have hρs : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hιs
  set C := (S.subgroupOf H).map ρ with hC
  have hQO2 : (Q.subgroupOf H).map ι ≤ O2 := by
    refine le_sSup ⟨?_, ?_⟩
    · have hQHn : (Q.subgroupOf H).Normal := by
        rw [Subgroup.normal_subgroupOf_iff hQH]
        rw [Subgroup.normal_subgroupOf_iff (hQS.trans hSV)] at hQn
        intro a h ha hh
        exact hQn a h ha (hHV hh)
      exact hQHn.map ι hιs
    · have hQH2 : IsPGroup 2 ↥(Q.subgroupOf H) := by
        intro y
        obtain ⟨k, hk⟩ := hQ2 ⟨((y : ↥H) : X), Subgroup.mem_subgroupOf.mp y.2⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
      exact hQH2.map ι
  have hS'perf : ⁅S.subgroupOf H, S.subgroupOf H⁆ = S.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSH, hperf]
  have hCne : C ≠ ⊥ := by
    intro hCbot
    have h1 : (S.subgroupOf H).map ι ≤ O2 := by
      rintro _ ⟨h, hh, rfl⟩
      have h2 : ρ h ∈ C := ⟨h, hh, rfl⟩
      rw [hCbot, Subgroup.mem_bot] at h2
      rw [← QuotientGroup.ker_mk' O2]
      exact h2
    have hnil : Group.IsNilpotent ↥O2 := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    have h2 : (S.subgroupOf H).map ι = ⊥ :=
      CFSG.SeitzReduction.perfect_eq_bot_of_le inferInstance
        (by rw [← Subgroup.map_commutator, hS'perf]) h1
    have hSU : ∀ s ∈ S, s ∈ U := by
      intro s hs
      have h3 : ι ⟨s, hSH hs⟩ ∈ (S.subgroupOf H).map ι :=
        ⟨⟨s, hSH hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      rw [h2, Subgroup.mem_bot] at h3
      exact hι1 _ h3
    have hSab : ⁅S, S⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hSU b hb)).2 a (hSK ha)).symm
    rw [hperf] at hSab
    rw [hSab, Subgroup.card_bot] at hpS
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpS)
  let σ : ↥S →* ↥C := (ρ.comp (Subgroup.inclusion hSH)).codRestrict C
    (fun s => ⟨Subgroup.inclusion hSH s, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩)
  have hσs : Function.Surjective σ := by
    rintro ⟨_, h, hh, rfl⟩
    exact ⟨⟨(h : X), Subgroup.mem_subgroupOf.mp hh⟩, Subtype.ext rfl⟩
  have hQker : Q.subgroupOf S ≤ σ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change (QuotientGroup.mk' O2) (ι (Subgroup.inclusion hSH q)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hQO2 ⟨Subgroup.inclusion hSH q,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hq), rfl⟩
  let φ : ↥S ⧸ Q.subgroupOf S →* ↥C := QuotientGroup.lift (Q.subgroupOf S) σ hQker
  have hφs : Function.Surjective φ := by
    intro c
    obtain ⟨s, rfl⟩ := hσs c
    exact ⟨QuotientGroup.mk s, rfl⟩
  have hφker : φ.ker ≤ Subgroup.center (↥S ⧸ Q.subgroupOf S) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq' φ.normal_ker with htop | hcen
    · exfalso
      apply hCne
      rw [eq_bot_iff]
      intro c hc
      obtain ⟨y, hy⟩ := hφs ⟨c, hc⟩
      have hy1 : φ y = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top y)
      rw [hy1] at hy
      rw [Subgroup.mem_bot]
      exact (congrArg Subtype.val hy).symm
    · exact hcen
  have hCq : CFSG.IsQuasisimple ↥C := CFSG.LocalCores.isQuasisimple_of_surjective hq' φ hφs hφker
  have hCcomp : IsComponentOf C ⊤ := by
    refine ⟨le_top, ?_,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hCq⟩
    have h1 : IsSubnormal (S.subgroupOf H) ⊤ := by
      have h := ggAssemblyIsSubnormal_subgroupOf hsn H
      rwa [Subgroup.subgroupOf_eq_top.mpr hHV] at h
    have h2 := ggIsSubnormal_map ρ h1
    rwa [Subgroup.map_top_of_surjective _ hρs] at h2
  intro hbot
  have hle : C ≤ LargeEvenLayer (⊤ : Subgroup (GGHypQuot Ht)) := le_sSup hCcomp
  rw [hbot] at hle
  exact hCne (le_bot_iff.mp hle)

@[expose] def GGHypRestIIIae (H E : Subgroup X) : Prop :=
  (∀ C : Subgroup (GGHypQuot H), IsComponentOf C ⊤ →
    ggHypImage H E ≤ Subgroup.normalizer (C : Set (GGHypQuot H)) ∧
      LargeEvenMarking ↥C (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ e ∈ ggHypImage H E, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GGHypQuot H) = e⁻¹ * l * e) φ)) ∧
  (commutator ↥(ggHypLayer H) = ⊤ ∨ LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥) ∧
  (∃ k : ℕ, derivedSeries ↥H k ≤ (ggHypLayer H).subgroupOf H) ∧
  (LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ →
    GGTwoConstrained ↥(ggHypLayer H) ∨
      (CFSG.Assembly.IsQuasisimple ↥(ggHypLayer H) ∧
        Odd (Nat.card (Subgroup.center ↥(ggHypLayer H)))))

theorem ggHypRestIII_of_ae {p : ℕ} {H E : Subgroup X} (h : GGHypRestIIIae H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) : GGHypRestIII p H E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, fun hb => absurd hb hL⟩

@[expose] def GGRCSAutKIII (V E K : Subgroup X) : Prop :=
  ∀ [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal], GGHypRestIIIae
    (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map
      (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))
    ((E.subgroupOf (E ⊔ K)).map (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))

@[expose] def GGRCSAutKIV (p : ℕ) (V E K : Subgroup X) : Prop :=
  ∀ [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal], GGHypRestIV p
    ((E.subgroupOf (E ⊔ K)).map (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))

@[expose] def GGRCSAutKNotExc (p : ℕ) (V E K : Subgroup X) : Prop :=
  ∀ [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal], ¬ GGFusionException p
    (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map
      (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))
    ((E.subgroupOf (E ⊔ K)).map (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))

theorem ggRCS_autKConfig {p : ℕ} (hp : p.Prime) {V E K S : Subgroup X}
    (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hK : CFSG.IsComponent K)
    (hcat : InCatalog (↥K ⧸ Subgroup.center ↥K)) (hS : GGRCSQuasiPiece p V S) (hSK : S ≤ K)
    (h3 : GGRCSAutKIII V E K) (h4 : GGRCSAutKIV p V E K) (hexc : GGRCSAutKNotExc p V E K) :
    GGAutKConfig p V E K := by
  have : Fact p.Prime := ⟨hp⟩
  have hN := ggRCSU_normal (V := V) hEK
  refine ⟨_, inferInstance, inferInstance, QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)),
    QuotientGroup.mk'_surjective _, ?_,
    ggHypThreeSixteenRest_of_parts (ggRCS_hypRestII hfus hE hEcard hEK hK hcat)
      (ggHypRestIII_of_ae (@h3 hN) (ggRCS_layer_ne_bot hp hfus.1 hS hSK)) (@h4 hN),
    ggRCS_layer_ne_bot hp hfus.1 hS hSK, @hexc hN⟩
  intro w hw
  rw [QuotientGroup.ker_mk'] at hw
  exact hw

end Layer

section KProper

theorem ggRCS_inCatalog_of_surjective {G : Type} [Group G] (hKP : KProper InCatalog G)
    {N : Subgroup G} (hN : N ≠ ⊤) (P : Subgroup ↥N) [P.Normal] (K : Subgroup (↥N ⧸ P))
    (T : Type) [Group T] [IsSimpleGroup T] (hnonab : ∃ a b : T, a * b ≠ b * a) (φ : ↥K →* T)
    (hφ : Function.Surjective φ) : InCatalog T :=
  ((CFSG.KCore.KProperNonab.kGroupNonab inCatalog_isoInvariant hKP N hN).quotient
    inCatalog_isoInvariant P).catalogue_of_surjective inCatalog_isoInvariant K hnonab φ hφ

theorem ggRCS_inCatalog_center_quot {G : Type} [Group G] (hKP : KProper InCatalog G)
    {N : Subgroup G} (hN : N ≠ ⊤) (P : Subgroup ↥N) [P.Normal] {K : Subgroup (↥N ⧸ P)}
    (hK : CFSG.IsComponent K) : InCatalog (↥K ⧸ Subgroup.center ↥K) := by
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  exact ggRCS_inCatalog_of_surjective hKP hN P K _ hK.1.2.2 (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _)

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.OuterAutomorphisms in
theorem ggRCS_outer_solvable {G : Type} [Group G] [Finite G] (hKP : KProper InCatalog G)
    (hSch : SchreierFor InCatalog) {N : Subgroup G} (hN : N ≠ ⊤) (P : Subgroup ↥N) [P.Normal]
    {K : Subgroup (↥N ⧸ P)} (hK : CFSG.IsComponent K) : Group.IsSolvable (Outer ↥K) := by
  have hcat := ggRCS_inCatalog_center_quot hKP hN P hK
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  have : Group.IsSolvable (Outer (↥K ⧸ Subgroup.center ↥K)) := hSch _ hK.1.2.2 hcat
  have : Group.IsPerfect ↥K := hK.1.1
  exact solvable_of_centerQuotient ↥K

theorem ggRCS_pCore_two_quot_eq_bot (N : Type) [Group N] [Finite N] :
    CFSG.pCore 2 (N ⧸ CFSG.Assembly.pCore 2 N) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup N := CFSG.Assembly.pCore 2 N with hP
  have hP2 : IsPGroup 2 P := by
    rw [hP]
    exact CFSG.pCore_isPGroup
  set K : Subgroup N := (CFSG.pCore 2 (N ⧸ P)).comap (QuotientGroup.mk' P) with hK
  have hKn : K.Normal := (CFSG.pCore_normal (p := 2) (G := N ⧸ P)).comap _
  have hKp : IsPGroup 2 K := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := N ⧸ P) ⟨_, hx⟩
    have hxa : x ^ (2 ^ a) ∈ P := by
      have h1 := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one, QuotientGroup.mk'_apply] at h1
      rw [← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := hP2 ⟨_, hxa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
    rw [pow_add, pow_mul, h2]
  have hle : K ≤ P := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ K := hy
  exact (QuotientGroup.eq_one_iff x).mpr (hle hx)

end KProper

end CFSG.StandardType
