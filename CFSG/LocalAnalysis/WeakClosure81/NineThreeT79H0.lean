module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Defs
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeS4FrameBase
public import CFSG.LocalAnalysis.ComponentClassification.KleinFourFixedGeneration
public import CFSG.Open.GilmanSolomonDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_V_le_H0 (hc : Nine3Choice V T A K S X p g x) : V ≤ nineH0 V K g := by
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨hc.core.A_mem_nineOmegaIn.1, hc.core.A_mem_nineOmegaIn.2.trans hc.core.S_le_K⟩
  have hA : A ≤ nineH V K := le_iSup₂_of_le A hAΩ le_rfl
  calc V = conjSubgroup A g := hc.A_g.symm
    _ ≤ conjSubgroup (nineH V K) g := E3.conjSubgroup_mono_left g hA
    _ ≤ nineH0 V K g := le_sup_right

theorem nine3_dcal_le_H0 (hc : Nine3Choice V T A K S X p g x) {D : Subgroup G}
    (hD : D ∈ nine3Dcal V (nineH0 V K g)) : D ≤ nineH0 V K g := by
  obtain ⟨h, hh, rfl⟩ := hD
  have hconj : conjSubgroup (nineH0 V K g) h = nineH0 V K g :=
    conjSubgroup_eq_iff_mem_normalizer.mpr ((nineH0 V K g).le_normalizer hh)
  calc conjSubgroup V h ≤ conjSubgroup (nineH0 V K g) h :=
        E3.conjSubgroup_mono_left h (nine3_V_le_H0 hc)
    _ = nineH0 V K g := hconj

private theorem nine3_conjSubgroup_iSup {ι : Sort*} (B : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, B i) g = ⨆ i, conjSubgroup (B i) g := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.map_iSup _ _

private theorem nine3_conjSubgroup_iSup₂ {ι : Sort*} (q : ι → Prop) (B : ι → Subgroup G)
    (g : G) :
    conjSubgroup (⨆ i, ⨆ (_ : q i), B i) g = ⨆ i, ⨆ (_ : q i), conjSubgroup (B i) g := by
  rw [nine3_conjSubgroup_iSup]
  exact iSup_congr fun i => nine3_conjSubgroup_iSup (fun _ : q i => B i) g

private theorem nine3_le_normalizer_nineH {k : G} (hk : k ∈ K) :
    k ∈ Subgroup.normalizer (nineH V K : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hmap : ∀ j : G, conjSubgroup (nineH V K) j =
      ⨆ U ∈ omegaIn V K (nineE V K), conjSubgroup U j := by
    intro j
    unfold nineH
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
  apply le_antisymm
  · rw [hmap k]
    exact iSup₂_le fun U hU =>
      le_iSup₂_of_le (conjSubgroup U k) (conjSubgroup_mem_omegaIn hU hk) le_rfl
  · have hle_inv : conjSubgroup (nineH V K) k⁻¹ ≤ nineH V K := by
      rw [hmap k⁻¹]
      exact iSup₂_le fun U hU =>
        le_iSup₂_of_le (conjSubgroup U k⁻¹) (conjSubgroup_mem_omegaIn hU (K.inv_mem hk)) le_rfl
    calc nineH V K = conjSubgroup (conjSubgroup (nineH V K) k⁻¹) k :=
          (E3.conjSubgroup_inv_conj (nineH V K) k).symm
      _ ≤ conjSubgroup (nineH V K) k := E3.conjSubgroup_mono_left k hle_inv

private theorem nine3_exists_ne_A (h : Nine3T79Setup V T A K S X p g x) :
    ∃ A' ∈ nineOmegaIn V K S, A' ≠ A := by
  obtain ⟨n, hnΩ, hnΔ⟩ := h.hc.core.card_nineOmegaIn
  have h2 : 1 < Nat.card ↥(nineOmegaIn V K S) := by
    rw [hnΩ]
    rcases h.h35 with h3 | h5 <;> omega
  have h2' : 1 < (nineOmegaIn V K S).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact h2
  exact Set.exists_ne_of_one_lt_ncard h2' A

private theorem nine3_conj_omega_mem_dcal (h : Nine3T79Setup V T A K S X p g x)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    conjSubgroup U g ∈ nine3Dcal V (nineH0 V K g) := by
  obtain ⟨k, hk, hUk⟩ := h.hc.nineH_transitive hU
  refine ⟨g⁻¹ * k * g, ?_, ?_⟩
  · refine (le_sup_right : conjSubgroup (nineH V K) g ≤ nineH0 V K g)
      (mem_conjSubgroup_iff.mpr ?_)
    rw [show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
    exact hk
  · rw [hUk]
    calc conjSubgroup (conjSubgroup A k) g = conjSubgroup A (k * g) :=
          CFSG.Quasithin.conjSubgroup_conjSubgroup A k g
      _ = conjSubgroup (conjSubgroup V g⁻¹) (k * g) := by rw [← h.hc'.V_g]
      _ = conjSubgroup V (g⁻¹ * (k * g)) :=
          CFSG.Quasithin.conjSubgroup_conjSubgroup V g⁻¹ (k * g)
      _ = conjSubgroup V (g⁻¹ * k * g) := by rw [mul_assoc]

private theorem nine3_omega_mem_dcal (h : Nine3T79Setup V T A K S X p g x)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    U ∈ nine3Dcal V (nineH0 V K g) := by
  obtain ⟨A', hA', hA'ne⟩ := nine3_exists_ne_A h
  have hA'Ω : A' ∈ omegaIn V K (nineE V K) :=
    ⟨hA'.1, hA'.2.trans h.hc.core.S_le_K⟩
  have hA'Δ : A' ∈ nineDelta V S := h.hc.core.mem_nineDelta_iff.mpr (Or.inr hA')
  have hBΔ : conjSubgroup A' g⁻¹ ∈ nineDelta V S :=
    ((mem_nineDeltaStab.mp ((nineDeltaStab V S).inv_mem h.hc.g_mem)) A').mp hA'Δ
  have hBVne : conjSubgroup A' g⁻¹ ≠ V := by
    intro hBV
    apply hA'ne
    calc A' = conjSubgroup (conjSubgroup A' g⁻¹) g := by
          rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
            CFSG.Quasithin.conjSubgroup_one]
      _ = conjSubgroup V g := by rw [hBV]
      _ = A := h.hc.V_g
  have hB9 : conjSubgroup A' g⁻¹ ∈ nineOmegaIn V K S :=
    (h.hc.core.mem_nineDelta_iff.mp hBΔ).resolve_left hBVne
  have hBΩ : conjSubgroup A' g⁻¹ ∈ omegaIn V K (nineE V K) :=
    ⟨hB9.1, hB9.2.trans h.hc.core.S_le_K⟩
  have hA'dcal : A' ∈ nine3Dcal V (nineH0 V K g) := by
    have hd := nine3_conj_omega_mem_dcal h hBΩ
    rwa [show conjSubgroup (conjSubgroup A' g⁻¹) g = A' by
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
        CFSG.Quasithin.conjSubgroup_one]] at hd
  obtain ⟨d, hd, hDeq⟩ := hA'dcal
  obtain ⟨k', hk', hA'eq⟩ := h.hc.nineH_transitive hA'Ω
  obtain ⟨k, hk, hUeq⟩ := h.hc.nineH_transitive hU
  refine ⟨d * (k'⁻¹ * k), ?_, ?_⟩
  · have hk'H0 : k' ∈ nineH0 V K g :=
      (le_sup_left : nineH V K ≤ nineH0 V K g) hk'
    have hkH0 : k ∈ nineH0 V K g := (le_sup_left : nineH V K ≤ nineH0 V K g) hk
    exact (nineH0 V K g).mul_mem hd ((nineH0 V K g).mul_mem ((nineH0 V K g).inv_mem hk'H0) hkH0)
  · have hAeq : A = conjSubgroup A' k'⁻¹ := by
      rw [hA'eq, CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
        CFSG.Quasithin.conjSubgroup_one]
    calc U = conjSubgroup A k := hUeq
      _ = conjSubgroup (conjSubgroup A' k'⁻¹) k := by rw [hAeq]
      _ = conjSubgroup A' (k'⁻¹ * k) :=
          CFSG.Quasithin.conjSubgroup_conjSubgroup A' k'⁻¹ k
      _ = conjSubgroup (conjSubgroup V d) (k'⁻¹ * k) := by rw [hDeq]
      _ = conjSubgroup V (d * (k'⁻¹ * k)) :=
          CFSG.Quasithin.conjSubgroup_conjSubgroup V d (k'⁻¹ * k)

theorem nine3_omega_le_dcal (h : Nine3T79Setup V T A K S X p g x) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) :
    U ∈ nine3Dcal V (nineH0 V K g) ∧ conjSubgroup U g ∈ nine3Dcal V (nineH0 V K g) :=
  ⟨nine3_omega_mem_dcal h hU, nine3_conj_omega_mem_dcal h hU⟩

theorem nine3_H0_eq_iSup_dcal (h : Nine3T79Setup V T A K S X p g x) :
    nineH0 V K g = ⨆ D ∈ nine3Dcal V (nineH0 V K g), D := by
  apply le_antisymm
  · show nineH V K ⊔ conjSubgroup (nineH V K) g ≤ ⨆ D ∈ nine3Dcal V (nineH0 V K g), D
    refine sup_le ?_ ?_
    · show (⨆ U, ⨆ (_ : U ∈ omegaIn V K (nineE V K)), U) ≤
        ⨆ D ∈ nine3Dcal V (nineH0 V K g), D
      exact iSup₂_le fun U hU => le_iSup₂_of_le U (nine3_omega_le_dcal h hU).1 le_rfl
    · show conjSubgroup (⨆ U, ⨆ (_ : U ∈ omegaIn V K (nineE V K)), U) g ≤
        ⨆ D ∈ nine3Dcal V (nineH0 V K g), D
      rw [nine3_conjSubgroup_iSup₂]
      exact iSup₂_le fun U hU =>
        le_iSup₂_of_le (conjSubgroup U g) (nine3_omega_le_dcal h hU).2 le_rfl
  · exact iSup₂_le fun D hD => nine3_dcal_le_H0 h.hc hD

theorem nine3_dcal_inf_I0 (h : Nine3T79Setup V T A K S X p g x) {D : Subgroup G}
    (hD : D ∈ nine3Dcal V (nineH0 V K g)) :
    D ⊓ nineI0 V K g ≠ ⊥ ∧ nineI0 V K g ≤ normalizer (D : Set G) := by
  obtain ⟨k, hk, rfl⟩ := hD
  have hIab : IsElemAbelian 2 (nineI0 V K g) := h.hc.nineI0_isElemAbelian h.hI h.hN
  have hI0conj : conjSubgroup (nineI0 V K g) k = nineI0 V K g :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (h.hN hk)
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨h.hc.core.A_mem_nineOmegaIn.1, h.hc.core.A_mem_nineOmegaIn.2.trans h.hc.core.S_le_K⟩
  have hA0 : A ⊓ pCoreOf 2 K ≠ ⊥ := by
    intro hbot
    have hrel := nine3_relIndex_of_mem_omegaIn h.hc hAΩ
    rw [hbot, Subgroup.relIndex_bot_left] at hrel
    have hcardA : Nat.card A = Nat.card V := by
      rw [← h.hc.V_g]
      exact card_conjSubgroup' g V
    have h2V : 2 < Nat.card V := h.hc.core.hyp7.2.1
    omega
  have hV1le : nineV1 V K g ≤ V ⊓ nineI0 V K g :=
    le_inf inf_le_left ((le_sup_left : nineV1 V K g ≤ nineW0 V K S g).trans
      h.hc.nineW0_le_nineI0)
  have hV1ne : nineV1 V K g ≠ ⊥ := by
    rw [h.hc.nineV1_eq_conj]
    intro hbot
    apply hA0
    have hc' := congrArg (fun H => conjSubgroup H g⁻¹) hbot
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CFSG.Quasithin.conjSubgroup_one, E3.conjSubgroup_bot] at hc'
    exact hc'
  have hVinf : V ⊓ nineI0 V K g ≠ ⊥ := by
    intro hbot
    exact hV1ne (le_bot_iff.mp (hV1le.trans (le_of_eq hbot)))
  have hDinf : conjSubgroup V k ⊓ nineI0 V K g ≠ ⊥ := by
    intro hbot
    apply hVinf
    have hI0inv : conjSubgroup (nineI0 V K g) k⁻¹ = nineI0 V K g :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (h.hN ((nineH0 V K g).inv_mem hk))
    have hc' := congrArg (fun H => conjSubgroup H k⁻¹) hbot
    rw [E3.conjSubgroup_inf, hI0inv, CFSG.Quasithin.conjSubgroup_conjSubgroup,
      mul_inv_cancel, CFSG.Quasithin.conjSubgroup_one, E3.conjSubgroup_bot] at hc'
    exact hc'
  refine ⟨hDinf, ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDinf
  have hjD : (j : G) ∈ conjSubgroup V k := j.2.1
  have hjI : (j : G) ∈ nineI0 V K g := j.2.2
  have hj1 : (j : G) ≠ 1 := fun hh => hj (Subtype.ext hh)
  have hIleC : nineI0 V K g ≤ Subgroup.centralizer ({(j : G)} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (hIab.comm ha hjI).symm
  exact hIleC.trans (centralizer_le_normalizer_conj h.hc.core.hyp7.2.2 k hjD hj1)

theorem nine3_dcal_not_le_pCore (h : Nine3T79Setup V T A K S X p g x) {D : Subgroup G}
    (hD : D ∈ nine3Dcal V (nineH0 V K g)) :
    ¬ D ≤ pCoreOf 2 (nineH0 V K g) ∧ (pCoreOf 2 (nineH0 V K g)).relIndex D = 2 := by
  obtain ⟨k, hk, rfl⟩ := hD
  set R₀ : Subgroup G := pCoreOf 2 (nineH0 V K g) with hR₀
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨h.hc.core.A_mem_nineOmegaIn.1, h.hc.core.A_mem_nineOmegaIn.2.trans h.hc.core.S_le_K⟩
  have hAnotR : ¬ A ≤ pCoreOf 2 K := by
    obtain ⟨y, -, -, hnot⟩ := mem_omegaSet.mp h.hc.core.A_mem_nineOmegaIn.1
    exact hnot
  have hV1rel : (nineV1 V K g).relIndex V = 2 := by
    have hrel := nine3_relIndex_of_mem_omegaIn h.hc hAΩ
    have hmap := Subgroup.relIndex_map_map_of_injective (H := A ⊓ pCoreOf 2 K) (K := A)
      (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    have hleft : (conjSubgroup (A ⊓ pCoreOf 2 K) g).relIndex (conjSubgroup A g) =
        (A ⊓ pCoreOf 2 K).relIndex A := by
      simpa only [CFSG.Quasithin.conjSubgroup] using hmap
    rw [h.hc.nineV1_eq_conj, ← h.hc.A_g]
    exact hleft.trans hrel
  have hI0leH0 : nineI0 V K g ≤ nineH0 V K g := by
    have hIleH : nineI V K ≤ nineH V K :=
      iSup₂_le fun U hU => le_iSup₂_of_le U hU inf_le_left
    exact sup_le (hIleH.trans le_sup_left) ((E3.conjSubgroup_mono_left g hIleH).trans le_sup_right)
  have hI0p : IsPGroup 2 (nineI0 V K g) :=
    CFSG.Open.IsElemAbelian.isPGroup (h.hc.nineI0_isElemAbelian h.hI h.hN)
  have hI0leR0 : nineI0 V K g ≤ R₀ := by
    rw [hR₀]
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hI0leH0
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hI0leH0).mpr h.hN) hI0p
  have hV1leR0 : nineV1 V K g ≤ R₀ := by
    have hAI : A ⊓ pCoreOf 2 K ≤ nineI V K := h.hc.inf_pCoreOf_le_nineI h.hc.core.A_mem_nineOmegaIn
    rw [h.hc.nineV1_eq_conj]
    exact (E3.conjSubgroup_mono_left g hAI).trans
      ((le_sup_right : conjSubgroup (nineI V K) g ≤ nineI0 V K g).trans hI0leR0)
  have hVleHg : V ≤ conjSubgroup (nineH V K) g := by
    have hA : A ≤ nineH V K := le_iSup₂_of_le A hAΩ le_rfl
    calc V = conjSubgroup A g := h.hc.A_g.symm
      _ ≤ conjSubgroup (nineH V K) g := E3.conjSubgroup_mono_left g hA
  have hH0N : nineH0 V K g ≤ Subgroup.normalizer (R₀ : Set G) := by
    rw [hR₀]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hHK : nineH V K ≤ K := Nine3Choice.nineH_le_K
  have hN_H : K ≤ Subgroup.normalizer (nineH V K : Set G) :=
    fun k hk => nine3_le_normalizer_nineH hk
  have hHgK : conjSubgroup (nineH V K) g ≤ conjSubgroup K g :=
    E3.conjSubgroup_mono_left g hHK
  have hNKg : conjSubgroup K g ≤ Subgroup.normalizer (conjSubgroup (nineH V K) g : Set G) := by
    rw [← E3.conjSubgroup_normalizer]
    exact E3.conjSubgroup_mono_left g hN_H
  have hO2Kg : pCoreOf 2 (conjSubgroup K g) = conjSubgroup (pCoreOf 2 K) g := by
    have hmap := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g⁻¹) K
    simpa only [CFSG.Quasithin.conjSubgroup] using hmap
  have hR0Hg_le : R₀ ⊓ conjSubgroup (nineH V K) g ≤ conjSubgroup (pCoreOf 2 K) g := by
    have hleHg : R₀ ⊓ conjSubgroup (nineH V K) g ≤ conjSubgroup (nineH V K) g := inf_le_right
    have hp : IsPGroup 2 ↥(R₀ ⊓ conjSubgroup (nineH V K) g) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (nineH0 V K g)).to_le inf_le_left
    have hnormHg : conjSubgroup (nineH V K) g ≤
        Subgroup.normalizer (R₀ ⊓ conjSubgroup (nineH V K) g : Set G) :=
      (le_inf (le_sup_right.trans hH0N) (conjSubgroup (nineH V K) g).le_normalizer).trans
        inf_normalizer_le_normalizer_inf
    have hle := CFSG.LieType.BorelTits.le_pCoreOf 2 hleHg
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hleHg).mpr hnormHg) hp
    have hstep : pCoreOf 2 (conjSubgroup (nineH V K) g) ≤ pCoreOf 2 (conjSubgroup K g) := by
      have hNH : pCoreOf 2 (conjSubgroup (nineH V K) g) ≤ conjSubgroup K g :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hHgK
      have hnorm : ((pCoreOf 2 (conjSubgroup (nineH V K) g)).subgroupOf
          (conjSubgroup K g)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr
          (hNKg.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      exact CFSG.LieType.BorelTits.le_pCoreOf 2 hNH hnorm
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact hle.trans (hstep.trans (le_of_eq hO2Kg))
  have hVnotle : ¬ V ≤ R₀ := by
    intro hVle
    have hVRg : V ≤ conjSubgroup (pCoreOf 2 K) g :=
      (le_inf hVle hVleHg).trans hR0Hg_le
    have hAleR : A ≤ pCoreOf 2 K := by
      have hc' := E3.conjSubgroup_mono_left g⁻¹ hVRg
      have hVg : conjSubgroup V g⁻¹ = A := by
        rw [← h.hc.A_g, CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
          CFSG.Quasithin.conjSubgroup_one]
      have hRg : conjSubgroup (conjSubgroup (pCoreOf 2 K) g) g⁻¹ = pCoreOf 2 K :=
        E3.conjSubgroup_conj_inv (pCoreOf 2 K) g
      rwa [hVg, hRg] at hc'
    exact hAnotR hAleR
  have hVrel : R₀.relIndex V = 2 := by
    have hV1le : nineV1 V K g ≤ R₀ ⊓ V := le_inf hV1leR0 inf_le_left
    have hdvd : (R₀ ⊓ V).relIndex V ∣ 2 := by
      have h := Subgroup.relIndex_dvd_of_le_left V hV1le
      rwa [hV1rel] at h
    have hne1 : (R₀ ⊓ V).relIndex V ≠ 1 := by
      intro h1
      exact hVnotle ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_left)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd h1 hne1
    · rw [← Subgroup.inf_relIndex_right (H := R₀) (K := V)]
      exact h2
  refine ⟨?_, ?_⟩
  · intro hDle
    apply hVnotle
    have hc' := E3.conjSubgroup_mono_left k⁻¹ hDle
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CFSG.Quasithin.conjSubgroup_one] at hc'
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (hH0N ((nineH0 V K g).inv_mem hk))] at hc'
  · have hmap := Subgroup.relIndex_map_map_of_injective (H := R₀) (K := V)
      (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective
    have hleft : (conjSubgroup R₀ k).relIndex (conjSubgroup V k) = R₀.relIndex V := by
      simpa only [CFSG.Quasithin.conjSubgroup] using hmap
    have hR0k : conjSubgroup R₀ k = R₀ :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hH0N hk)
    rw [← hR0k, hleft]
    exact hVrel

theorem nine3_fusionOddCoreOf_le_centralizer (h : Nine3T79Setup V T A K S X p g x) :
    fusionOddCoreOf (nineH0 V K g) ≤ centralizer (nineH0 V K g : Set G) := by
  classical
  set Q : Subgroup G := fusionOddCoreOf (nineH0 V K g) with hQ
  have hQnorm : nineH0 V K g ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    exact CFSG.Open.le_normalizer_fusionOddCoreOf (nineH0 V K g)
  have hQodd : Odd (Nat.card Q) := by
    rw [hQ, fusionOddCoreOf, Subgroup.card_map_of_injective (nineH0 V K g).subtype_injective]
    have hpc : fusionOddCore ↥(nineH0 V K g) = CFSG.pPrimeCore 2 ↥(nineH0 V K g) := by
      unfold fusionOddCore CFSG.pPrimeCore
      congr 1
      ext L
      simp [Nat.coprime_two_left]
    rw [hpc]
    exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(nineH0 V K g)))
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) :=
    (nine3_V_le_H0 h.hc).trans hQnorm
  set ρ : ↥V →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hVQ) with hρ
  set qsub : Subgroup ↥Q := (Subgroup.centralizer (V : Set G)).comap Q.subtype with hqsub
  haveI : Fintype ↥V := Fintype.ofFinite _
  have hVcard2 : 2 < Fintype.card ↥V := by
    rw [← Nat.card_eq_fintype_card]
    exact h.hc.core.hyp7.2.1
  have hVcard : 1 < Fintype.card ↥V := by omega
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card hVcard (1 : ↥V)
  have hβcard : 1 < Fintype.card {y : ↥V // y ≠ a} := by
    rw [Fintype.card_subtype_compl (fun y : ↥V => y = a), Fintype.card_subtype_eq a]
    omega
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hβcard (⟨1, ha.symm⟩ : {y : ↥V // y ≠ a})
  let first : ↥V := a
  let second : ↥V := b.1
  have hfirstNe : (first : G) ≠ 1 := fun hh => ha (Subtype.ext hh)
  have hsecondNe : (second : G) ≠ 1 := fun hh => hb (Subtype.ext (Subtype.ext hh))
  have hsecondNea : second ≠ first := b.2
  have hfirstSquare : first * first = 1 := by
    apply Subtype.ext
    change (first : G) * (first : G) = 1
    simpa only [pow_two] using h.hc.core.hyp7.1.2 first.1 first.2
  have hsecondSquare : second * second = 1 := by
    apply Subtype.ext
    change (second : G) * (second : G) = 1
    simpa only [pow_two] using h.hc.core.hyp7.1.2 second.1 second.2
  have hcommutes : Commute first second := by
    apply Subtype.ext
    exact h.hc.core.hyp7.1.comm first.2 second.2
  have hprodNe : first * second ≠ 1 := by
    intro hprod
    apply hsecondNea
    calc second = 1 * second := (one_mul second).symm
      _ = (first * first) * second := by rw [hfirstSquare]
      _ = first * (first * second) := by rw [mul_assoc]
      _ = first * 1 := by rw [hprod]
      _ = first := mul_one first
  have hprodNe' : ((first * second : ↥V) : G) ≠ 1 := fun hh => hprodNe (Subtype.ext hh)
  have hVp : IsPGroup 2 ↥V := CFSG.Open.IsElemAbelian.isPGroup h.hc.core.hyp7.1
  have hgenerated :=
    CFSG.ComponentClassification.KleinFourFixedGeneration.odd_group_generation hVp hQodd ρ first
      second hfirstSquare hsecondSquare hcommutes
  have hbotQV : V ⊓ Q = ⊥ := by
    rw [← Subgroup.card_eq_one]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hVp
    have hcop : Nat.Coprime (Nat.card V) (Nat.card Q) := by
      rw [hm]
      exact (Nat.coprime_two_left.mpr hQodd).pow_left m
    exact Nat.eq_one_of_dvd_coprimes hcop (Subgroup.card_dvd_of_le inf_le_left)
      (Subgroup.card_dvd_of_le inf_le_right)
  have hfix_le : ∀ y : ↥V, (y : G) ≠ 1 →
      CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (ρ y) ≤ qsub := by
    intro y hyne q hq
    rw [hqsub]
    have hfixed : ρ y q = q := by
      simpa [CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup] using hq
    have h1 : (y : G) * (q : G) * (y : G)⁻¹ = (q : G) := by
      have hcoe := congrArg (fun z : ↥Q => (z : G)) hfixed
      rw [hρ] at hcoe
      simpa only [MonoidHom.comp_apply, Subgroup.coe_inclusion,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using hcoe
    have hcomm : (y : G) * (q : G) = (q : G) * (y : G) := by
      have h1' : (y : G) * (q : G) * (y : G)⁻¹ = (q : G) := by
        simpa only [mul_assoc] using h1
      exact mul_inv_eq_iff_eq_mul.mp h1'
    have hqC : (q : G) ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hcomm
    have hNq : (q : G) ∈ Subgroup.normalizer (V : Set G) :=
      centralizer_le_normalizer_of_isTI h.hc.core.hyp7.2.2 y.2 hyne hqC
    have hZp : Subgroup.zpowers (q : G) ≤ Q := Subgroup.zpowers_le.mpr q.2
    have hZV : ⁅Subgroup.zpowers (q : G), V⁆ ≤ V ⊓ Q := by
      rw [Subgroup.commutator_le]
      intro z hz v hv
      have hzQ : z ∈ Q := hZp hz
      have hzN : z ∈ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr hNq hz
      constructor
      · exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN v).mp hv) (V.inv_mem hv)
      · change z * v * z⁻¹ * v⁻¹ ∈ Q
        rw [show z * v * z⁻¹ * v⁻¹ = z * (v * z⁻¹ * v⁻¹) by group]
        exact Q.mul_mem hzQ
          ((Subgroup.mem_normalizer_iff.mp (hQnorm (nine3_V_le_H0 h.hc hv)) (z⁻¹)).mp
            (Q.inv_mem hzQ))
    have hZVbot : ⁅Subgroup.zpowers (q : G), V⁆ = ⊥ :=
      le_bot_iff.mp (hZV.trans (le_of_eq hbotQV))
    have hqCV : (q : G) ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZVbot (Subgroup.mem_zpowers (q : G))
    exact Subgroup.mem_subgroupOf.mpr hqCV
  have htop : (⊤ : Subgroup ↥Q) ≤ qsub := by
    rw [← hgenerated]
    exact sup_le (sup_le (hfix_le first hfirstNe) (hfix_le second hsecondNe)) (hfix_le _ hprodNe')
  have hQleCV : Q ≤ Subgroup.centralizer (V : Set G) :=
    fun q hq => htop (Subgroup.mem_top ⟨q, hq⟩)
  have hQleD : ∀ D ∈ nine3Dcal V (nineH0 V K g), Q ≤ Subgroup.centralizer (D : Set G) := by
    rintro D ⟨k, hk, rfl⟩
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hconjq : k * q * k⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQnorm hk) q).mp hq
    have hv : k * d * k⁻¹ ∈ V := mem_conjSubgroup_iff.mp hd
    have hcomm := Subgroup.mem_centralizer_iff.mp (hQleCV hconjq) (k * d * k⁻¹) hv
    calc d * q = k⁻¹ * ((k * d * k⁻¹) * (k * q * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * q * k⁻¹) * (k * d * k⁻¹)) * k := by rw [hcomm]
      _ = q * d := by group
  have hH0leCQ : nineH0 V K g ≤ Subgroup.centralizer (Q : Set G) := by
    rw [nine3_H0_eq_iSup_dcal h]
    exact iSup₂_le fun D hD => Subgroup.le_centralizer_iff.mpr (hQleD D hD)
  exact Subgroup.le_centralizer_iff.mp hH0leCQ

end CFSG.LocalAnalysis.WeakClosure81
