module

public import CFSG.Quasithin.EmptyFaithful.S152UBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma116
public import CFSG.Quasithin.Background.B2FactorizationOffender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_eq_inf152 {p : ℕ} {X Y : Subgroup G} (h : oPrimeResidualOf p X ≤ Y) :
    oPrimeResidualOf p X = oPrimeResidualOf p (X ⊓ Y) := by
  unfold oPrimeResidualOf at h ⊢
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact Subgroup.subset_closure ⟨⟨hx.1, h (Subgroup.subset_closure hx)⟩, hx.2⟩
  · exact Subgroup.closure_mono fun x hx => ⟨hx.1.1, hx.2⟩

omit [Finite G] in
theorem conjSub_eq_self152 {g : G} {X : Subgroup G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    conjSub g X = X := by
  ext x
  rw [mem_conjSub]
  have hg' : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hg
  have := Subgroup.mem_normalizer_iff.mp hg' x
  rw [inv_inv] at this
  exact this.symm

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq152 {g : G} {X : Subgroup G} (h : conjSub g X = X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := mul_mem_conjSub (g := g) hx
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    have := mem_conjSub.mp hx
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at this

theorem oTwoUpper_conjSub152 (g : G) (X : Subgroup G) :
    oTwoUpper (conjSub g X) = conjSub g (oTwoUpper X) :=
  oTwoUpper_map (MulAut.conj g).toMonoidHom X

omit [Finite G] in
theorem sq_mem_of_sup_zpowers152 {P : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (P : Set G)) (ht2 : t ^ 2 ∈ P) {x : G}
    (hx : x ∈ P ⊔ Subgroup.zpowers t) : x ^ 2 ∈ P := by
  have hzN : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr htN
  obtain ⟨e, he, k, hk, rfl⟩ := (mem_sup_iff_of_le_normalizer hzN).mp hx
  have hkN : k ∈ Subgroup.normalizer (P : Set G) := hzN hk
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hk2 : (t ^ m) ^ 2 ∈ P := by
    have : (t ^ m) ^ 2 = (t ^ 2) ^ m := by group
    rw [this]
    exact P.zpow_mem ht2 m
  have h1 : (t ^ m) * e * (t ^ m)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hkN e).mp he
  have : (e * t ^ m) ^ 2 = e * ((t ^ m) * e * (t ^ m)⁻¹) * (t ^ m) ^ 2 := by
    rw [sq]
    group
  rw [this]
  exact P.mul_mem (P.mul_mem he h1) hk2

section HPair

variable {H V H₁ H₂ : Subgroup G}

omit [Finite G] in
theorem hp152_le_normalizer_two (hP : IsHPair H V H₁ H₂) :
    H₁ ≤ Subgroup.normalizer (H₂ : Set G) := by
  have key : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b * a⁻¹ ∈ H₂ := by
    intro a ha b hb
    have hc := hP.comm a ha b hb
    have : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    rw [this]
    exact H₂.mul_mem (hP.le₂.1 hc) hb
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key a ha b, fun hb => ?_⟩
  have h1 := key a⁻¹ (H₁.inv_mem ha) _ hb
  have e : a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := by group
  rwa [e] at h1

omit [Finite G] in
theorem hp152_le_normalizer_one (hP : IsHPair H V H₁ H₂) :
    H₂ ≤ Subgroup.normalizer (H₁ : Set G) := by
  have key : ∀ b ∈ H₂, ∀ a ∈ H₁, b * a * b⁻¹ ∈ H₁ := by
    intro b hb a ha
    have hc := (pCoreOf 2 H).inv_mem (hP.comm a ha b hb)
    have e1 : (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ := by group
    rw [e1] at hc
    have : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
    rw [this]
    exact H₁.mul_mem (hP.le₁.1 hc) ha
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key b hb a, fun ha => ?_⟩
  have h1 := key b⁻¹ (H₂.inv_mem hb) _ ha
  have e : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
  rwa [e] at h1

omit [Finite G] in
theorem hp152_swap_mem_normalizer (hP : IsHPair H V H₁ H₂) {t : G} (ht2 : t ^ 2 ∈ pCoreOf 2 H)
    (hconj : conjSub t H₁ = H₂) :
    t ∈ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_eq152
  have h2 : conjSub t H₂ = H₁ := by
    rw [← hconj, ← conjSub_mul]
    have : t * t ∈ H₁ := by rw [← sq]; exact hP.le₁.1 ht2
    exact conjSub_eq_self152 (Subgroup.le_normalizer this)
  rw [conjSub_sup, hconj, h2, sup_comm]

omit [Finite G] in
theorem hp152_oTwoUpper_le (hP : IsHPair H V H₁ H₂) : oTwoUpper H ≤ H₁ ⊔ H₂ := by
  obtain ⟨t₀, -, ht₀Q, hconj, hHeq⟩ := hP.swap
  have hN := hp152_swap_mem_normalizer hP ht₀Q hconj
  have ht2 : t₀ ^ 2 ∈ H₁ ⊔ H₂ := Subgroup.mem_sup_left (hP.le₁.1 ht₀Q)
  refine oTwoUpper_le_of_pow_mem fun x hx => ⟨1, ?_⟩
  rw [pow_one]
  rw [hHeq] at hx
  exact sq_mem_of_sup_zpowers152 hN ht2 hx

theorem KS_eq_sup152 (hP : IsHPair H V H₁ H₂) {S : Subgroup G}
    (hSyl : IsSylowTwoOf S (H₁ ⊔ H₂)) : oTwoUpper H ⊔ S = H₁ ⊔ H₂ := by
  apply le_antisymm
  · exact sup_le (hp152_oTwoUpper_le hP) hSyl.1
  · have h := eq_oTwoUpper_sup_of_isSylowTwoOf hSyl
    have hle : oTwoUpper (H₁ ⊔ H₂) ≤ oTwoUpper H :=
      oTwoUpper_mono (sup_le hP.le₁.2 hP.le₂.2)
    calc H₁ ⊔ H₂ = oTwoUpper (H₁ ⊔ H₂) ⊔ S := h
      _ ≤ oTwoUpper H ⊔ S := sup_le_sup_right hle S

theorem conjSub_oTwoUpper_eq152 (hP : IsHPair H V H₁ H₂) {S T : Subgroup G}
    (hSyl : IsSylowTwoOf S (H₁ ⊔ H₂)) (hT2 : IsPGroup 2 T) (hST : S ≤ T) (hTH : T ≤ H) {t : G}
    (ht : t ∈ T) (htS : t ∉ S) : conjSub t (oTwoUpper H₁) = oTwoUpper H₂ := by
  obtain ⟨t₀, -, ht₀Q, hconj, hHeq⟩ := hP.swap
  have hN := hp152_swap_mem_normalizer hP ht₀Q hconj
  have htP : t ∉ H₁ ⊔ H₂ := fun h => htS (by
    rw [← inf_eq_of_isSylowTwoOf_of_le hSyl hT2 hST]
    exact ⟨ht, h⟩)
  have htH : t ∈ (H₁ ⊔ H₂) ⊔ Subgroup.zpowers t₀ := hHeq ▸ hTH ht
  obtain ⟨e, he, k, hk, rfl⟩ := (mem_sup_iff_of_le_normalizer (Subgroup.zpowers_le.mpr hN)).mp htH
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hq1 : t₀ ^ 2 ∈ H₁ ⊔ H₂ := Subgroup.mem_sup_left (hP.le₁.1 ht₀Q)
  have hmodd : Odd m := by
    by_contra hme
    rw [Int.not_odd_iff_even] at hme
    obtain ⟨j, hj⟩ := hme
    apply htP
    have h1 : t₀ ^ m = (t₀ ^ 2) ^ j := by rw [hj]; group
    rw [h1]
    exact (H₁ ⊔ H₂).mul_mem he ((H₁ ⊔ H₂).zpow_mem hq1 j)
  obtain ⟨j, hj⟩ := hmodd
  have he' : e * (t₀ ^ 2) ^ j ∈ H₁ ⊔ H₂ := (H₁ ⊔ H₂).mul_mem he ((H₁ ⊔ H₂).zpow_mem hq1 j)
  have heq : e * t₀ ^ m = (e * (t₀ ^ 2) ^ j) * t₀ := by rw [hj]; group
  have hPN : e * (t₀ ^ 2) ^ j ∈ Subgroup.normalizer (H₂ : Set G) :=
    (sup_le (hp152_le_normalizer_two hP) Subgroup.le_normalizer) he'
  rw [heq, conjSub_mul, ← oTwoUpper_conjSub152, hconj]
  exact conjSub_eq_self152 (normalizer_le_normalizer_oTwoUpper H₂ hPN)

end HPair

section Main

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem pCoreOf_le_normalizer_of_between152 {W : Subgroup G}
    (hW1 : pCoreOf 2 (oTwoUpper H) ≤ W) (hW2 : W ≤ oTwoUpper H) :
    pCoreOf 2 H ≤ Subgroup.normalizer (W : Set G) := by
  have hn : oTwoUpper H ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    intro k hk
    have hkH : k ∈ H := oTwoUpper_le H hk
    have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hkH)
    have h2 := Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hkH)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩,
      fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩
  have hle : pCoreOf 2 H ⊓ oTwoUpper H ≤ pCoreOf 2 (oTwoUpper H) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hn ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have key : ∀ q ∈ pCoreOf 2 H, ∀ w ∈ W, q * w * q⁻¹ ∈ W := by
    intro q hq w hw
    have hwK : w ∈ oTwoUpper H := hW2 hw
    have hwH : w ∈ H := oTwoUpper_le H hwK
    have hqH : q ∈ H := pCoreOf_le 2 H hq
    have hcQ : q * w * q⁻¹ * w⁻¹ ∈ pCoreOf 2 H := by
      have h1 : w * q⁻¹ * w⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hwH) q⁻¹).mp
          (Subgroup.inv_mem _ hq)
      have : q * w * q⁻¹ * w⁻¹ = q * (w * q⁻¹ * w⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hq h1
    have hcK : q * w * q⁻¹ * w⁻¹ ∈ oTwoUpper H := by
      have h1 : q * w * q⁻¹ ∈ oTwoUpper H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hqH) w).mp hwK
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hwK)
    have : q * w * q⁻¹ = (q * w * q⁻¹ * w⁻¹) * w := by group
    rw [this]
    exact W.mul_mem (hW1 (hle ⟨hcQ, hcK⟩)) hw
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key q hq w, fun hw => ?_⟩
  have h1 := key q⁻¹ ((pCoreOf 2 H).inv_mem hq) _ hw
  have e : q⁻¹ * (q * w * q⁻¹) * q⁻¹⁻¹ = w := by group
  rwa [e] at h1

theorem Q_le_S152 (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hD : Inputs152 T Mc M H B₀ I)
    (hIrr : IsIrredOnSection T (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)))
    (hnot : ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))) :
    pCoreOf 2 H ≤ sOf152 T Mc M B₀ := by
  by_contra hQ
  apply hnot
  obtain ⟨Ts, hTs⟩ := hs.qtfe.exists_sylow
  have hQT : pCoreOf 2 H ≤ T := by
    have := pCoreOf_two_le_sylow H Ts (hTs ▸ hH.1.1)
    rwa [hTs] at this
  have hSQ : sOf152 T Mc M B₀ ≤ sOf152 T Mc M B₀ ⊔ pCoreOf 2 H := le_sup_left
  have hSQT : sOf152 T Mc M B₀ ⊔ pCoreOf 2 H ≤ T := sup_le S_le_T152 hQT
  have hTeq : sOf152 T Mc M B₀ ⊔ pCoreOf 2 H = T := by
    rcases eq_or_eq_of_relIndex_two hSQ hSQT hD.h17.2.2 with h | h
    · exact absurd (le_sup_right.trans h.le) hQ
    · exact h
  obtain ⟨h1, h2, h3, h4⟩ := hIrr
  refine ⟨h1, S_le_T152.trans h2, S_le_T152.trans h3, fun W hW1 hW2 hWn => h4 W hW1 hW2 ?_⟩
  have : sOf152 T Mc M B₀ ⊔ pCoreOf 2 H ≤ Subgroup.normalizer (W : Set G) :=
    sup_le hWn (pCoreOf_le_normalizer_of_between152 hW1 hW2)
  rwa [hTeq] at this

theorem J_sup_eq_S152 (hD : Inputs152 T Mc M H B₀ I) (hQS : pCoreOf 2 H ≤ sOf152 T Mc M B₀)
    (hJ : (thompsonJ T ⊔ pCoreOf 2 H).relIndex T = 2) :
    thompsonJ T ⊔ pCoreOf 2 H = sOf152 T Mc M B₀ := by
  have hJS : thompsonJ T ≤ sOf152 T Mc M B₀ := (B2F.thompsonJ_le_baum T).trans hD.h14.baum_le
  have hle : thompsonJ T ⊔ pCoreOf 2 H ≤ sOf152 T Mc M B₀ := sup_le hJS hQS
  have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hle S_le_T152
  rw [hJ, hD.h17.2.2] at h1
  have h2 : (thompsonJ T ⊔ pCoreOf 2 H).relIndex (sOf152 T Mc M B₀) = 1 := by omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)

theorem K_le_centralizer_zS152 (hB₀ : IsB0 T Mc M B₀) (hD : Inputs152 T Mc M H B₀ I) :
    oTwoUpper H ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
  obtain ⟨B, hB⟩ := hD.hN.sigmaPrime_nonempty
  have hZ := commutator_eq_zSOf hD.h13 hB₀ hB
  have := (hD.h11 B hB).centralizes
  rwa [hZ] at this

theorem centralizer_zS_le_inf152 (hD : Inputs152 T Mc M H B₀ I) :
    Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤ Mc ⊓ I := fun x hx => by
  have h := hD.h16.centralizer_eq
  have hx' : x ∈ Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
    rw [← h]
    exact hx
  exact hD.h16.centralizer_le hx'

end Main

@[expose] def Input15209Irr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H →
      IsIrredOnSection T (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))

@[expose] def Input15112J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      IsSylowTwoOf (thompsonJ T ⊔ pCoreOf 2 H) (H₁ ⊔ H₂) ∧
        (thompsonJ T ⊔ pCoreOf 2 H).relIndex T = 2

@[expose] def Input1210Kc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ → ∀ H : Subgroup G, IsHStar T M H →
      conjClosure (oTwoUpper H) Mc ≠ oTwoUpper H →
        pCoreOf 2 (conjClosure (oTwoUpper H) Mc ⊔ T) ≤ sOf152 T Mc M B₀ →
          conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G)

@[expose] def Input15221Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215 T Mc M B₀ I →
          IsLnTwo 4 (OTwoQuot (conjClosure (oTwoUpper H) Mc)) → Concl15218ii T Mc M H B₀ I →
          (∃ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₁ ∧ Y₁ ≤ M ⊓ I ∧
              sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) ∧
              Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) ∧
              ¬ Y₁ ≤ Mc ⊓ I) →
          IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H))

end CFSG.Quasithin
