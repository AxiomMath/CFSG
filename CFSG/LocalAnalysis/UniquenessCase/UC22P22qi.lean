module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qk
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResCore
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.RankThreeCoreUniqueness.Helpers (gamma_le_iff)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qi_mem_map {m x : G} {H : Subgroup G} :
    x ∈ H.map (MulAut.conj m).toMonoidHom ↔ m⁻¹ * x * m ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨m⁻¹ * x * m, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem uc22p22qi_centralizer_map (m : G) (X : Subgroup G) :
    centralizer ((X.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (X : Set G)).map (MulAut.conj m).toMonoidHom := by
  ext y
  rw [Subgroup.mem_centralizer_iff, uc22p22qi_mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := h (m * x * m⁻¹) (uc22p22qi_mem_map.2 (by simpa [mul_assoc] using hx))
    calc x * (m⁻¹ * y * m) = m⁻¹ * ((m * x * m⁻¹) * y) * m := by group
      _ = m⁻¹ * (y * (m * x * m⁻¹)) * m := by rw [h1]
      _ = (m⁻¹ * y * m) * x := by group
  · intro h z hz
    have hz' : m⁻¹ * z * m ∈ X := uc22p22qi_mem_map.1 hz
    have h1 := h (m⁻¹ * z * m) hz'
    calc z * y = m * ((m⁻¹ * z * m) * (m⁻¹ * y * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * y * m) * (m⁻¹ * z * m)) * m⁻¹ := by rw [h1]
      _ = y * z := by group

theorem uc22p22qi_inftyOf_map (m : G) (H : Subgroup G) :
    UC6.inftyOf (H.map (MulAut.conj m).toMonoidHom) =
      (UC6.inftyOf H).map (MulAut.conj m).toMonoidHom := by
  unfold UC6.inftyOf
  set φ : G →* G := (MulAut.conj m).toMonoidHom with hφ
  have hcard : Nat.card (H.map φ) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  rw [hcard, ← map_derivedSeries_eq (φ.subgroupMap_surjective H) (Nat.card H), Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem uc22p22qi_map_eq_of_conj_mem {M K : Subgroup G} (hK : ∀ k ∈ M, ∀ x ∈ K, k * x * k⁻¹ ∈ K) {m : G}
    (hm : m ∈ M) : K.map (MulAut.conj m).toMonoidHom = K := by
  ext x
  rw [uc22p22qi_mem_map]
  constructor
  · intro h
    have := hK m hm _ h
    simpa [mul_assoc] using this
  · intro h
    simpa using hK m⁻¹ (M.inv_mem hm) x h

theorem uc22p22qi_frobenius_map (m : G) {X K V : Subgroup G}
    (h : CFSG.Open.uniqueFourIsFrobenius X K V) :
    CFSG.Open.uniqueFourIsFrobenius (X.map (MulAut.conj m).toMonoidHom) (K.map (MulAut.conj m).toMonoidHom)
      (V.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨hK, hV, hKX, hKn, hVX, hXKV, hKV, hfpf⟩ := h
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  refine ⟨?_, ?_, Subgroup.map_mono hKX, ?_, Subgroup.map_mono hVX, ?_, ?_, ?_⟩
  · exact fun h => hK ((Subgroup.map_eq_bot_iff_of_injective K hinj).1 h)
  · exact fun h => hV ((Subgroup.map_eq_bot_iff_of_injective V hinj).1 h)
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hKX)).2 ?_
    have hXN : X ≤ normalizer (K : Set G) := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hKn
    exact (Subgroup.map_mono hXN).trans (Subgroup.le_normalizer_map _)
  · rw [hXKV, Subgroup.map_sup]
  · rw [← Subgroup.map_inf K V _ hinj, hKV, Subgroup.map_bot]
  · rintro _ ⟨v, hv, rfl⟩ hv1 _ ⟨k, hk, rfl⟩ hkv
    have hv1' : v ≠ 1 := fun h => hv1 (by rw [h, map_one])
    have hkv' : k * v = v * k := hinj (by simpa using hkv)
    have := hfpf v hv hv1' k hk hkv'
    rw [this, map_one]

theorem uc22p22qi_weak_map {m : G} {P₀ P : Subgroup G} (h : IsWeaklyClosedIn P₀ P) :
    IsWeaklyClosedIn (P₀.map (MulAut.conj m).toMonoidHom) (P.map (MulAut.conj m).toMonoidHom) := by
  have hwe := uc22p22q_weak_elem h
  intro g hg
  have hle : CFSG.conjugate (P₀.map (MulAut.conj m).toMonoidHom) g ≤ P₀.map (MulAut.conj m).toMonoidHom := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ P₀.map (MulAut.conj m).toMonoidHom := hx
    rw [uc22p22qi_mem_map] at hx'
    rw [uc22p22qi_mem_map]
    have h1 : ∀ y ∈ P₀, (m⁻¹ * g * m)⁻¹ * y * (m⁻¹ * g * m) ∈ P := by
      intro y hy
      have hmem : m * y * m⁻¹ ∈ P₀.map (MulAut.conj m).toMonoidHom :=
        uc22p22qi_mem_map.2 (by simpa [mul_assoc] using hy)
      have h2 := hg (show (MulAut.conj g⁻¹).toMonoidHom (m * y * m⁻¹) ∈
        CFSG.conjugate (P₀.map (MulAut.conj m).toMonoidHom) g from ⟨m * y * m⁻¹, hmem, rfl⟩)
      rw [uc22p22qi_mem_map] at h2
      have e : (m⁻¹ * g * m)⁻¹ * y * (m⁻¹ * g * m) =
          m⁻¹ * ((MulAut.conj g⁻¹).toMonoidHom (m * y * m⁻¹)) * m := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact h2
    have h3 := hwe (m⁻¹ * g * m) h1 _ hx'
    have e : m⁻¹ * ((MulAut.conj g⁻¹).toMonoidHom x) * m =
        (m⁻¹ * g * m)⁻¹ * (m⁻¹ * x * m) * (m⁻¹ * g * m) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact h3
  have hc : Nat.card (CFSG.conjugate (P₀.map (MulAut.conj m).toMonoidHom) g) =
      Nat.card (P₀.map (MulAut.conj m).toMonoidHom) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  exact Subgroup.eq_of_le_of_card_ge hle hc.ge

theorem uc22p22qi_normalizer_map {M P₁ : Subgroup G} {m : G} (hm : m ∈ M)
    (h : ∀ Y : Subgroup G, Y ≤ P₁ → Y ≠ ⊥ → normalizer (Y : Set G) ≤ M) :
    ∀ Y : Subgroup G, Y ≤ P₁.map (MulAut.conj m).toMonoidHom → Y ≠ ⊥ → normalizer (Y : Set G) ≤ M := by
  intro Y hY hY1 g hg
  set Y₀ : Subgroup G := Y.map (MulAut.conj m⁻¹).toMonoidHom with hY₀
  have hY₀P : Y₀ ≤ P₁ := by
    rintro _ ⟨y, hy, rfl⟩
    have := uc22p22qi_mem_map.1 (hY hy)
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hY₀1 : Y₀ ≠ ⊥ := fun h0 =>
    hY1 ((Subgroup.map_eq_bot_iff_of_injective Y (MulAut.conj m⁻¹).injective).1 h0)
  have hg' : m⁻¹ * g * m ∈ normalizer (Y₀ : Set G) := by
    refine uc22p22qk_mem_normalizer fun w hw => ?_
    obtain ⟨y, hy, rfl⟩ := hw
    refine ⟨g * y * g⁻¹, (mem_normalizer_iff.1 hg y).1 hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have h1 := h Y₀ hY₀P hY₀1 hg'
  have hgM : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [hgM]
  exact M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)

theorem uc22p22qi_r613defAt_map (D : Data G) {p : ℕ} (hpP : p.Prime) {P P₀ : Subgroup G} {m : G}
    (hm : m ∈ D.M) (hP : IsPGroup p P) (hd : UC6.R613DefAt D p P P₀) :
    UC6.R613DefAt D p (P.map (MulAut.conj m).toMonoidHom) (P₀.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨⟨hp3, hsolv, hwc, hΓ, hL, hfrob⟩, hcent⟩ := hd
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  have hC : centralizer ((P₀.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (P₀ : Set G)).map (MulAut.conj m).toMonoidHom := uc22p22qi_centralizer_map m P₀
  have hL' : UC6.inftyOf (centralizer ((P₀.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) =
      (UC6.inftyOf (centralizer (P₀ : Set G))).map (MulAut.conj m).toMonoidHom := by
    rw [hC]
    exact uc22p22qi_inftyOf_map m _
  have hP₁ : P.map (MulAut.conj m).toMonoidHom ⊓
      UC6.inftyOf (centralizer ((P₀.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) =
      (P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))).map (MulAut.conj m).toMonoidHom := by
    rw [hL', Subgroup.map_inf _ _ _ hinj]
  have hD' : centralizer ((UC6.inftyOf (centralizer ((P₀.map (MulAut.conj m).toMonoidHom : Subgroup G) :
      Set G)) : Subgroup G) : Set G) =
      (centralizer ((UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G)).map
        (MulAut.conj m).toMonoidHom := by
    rw [hL']
    exact uc22p22qi_centralizer_map m _
  refine ⟨⟨hp3, hsolv, uc22p22qi_weak_map hwc, ?_, ?_, ?_⟩, ?_⟩
  · rw [hP₁]
    have hΓ' := (gamma_le_iff 1 p _ D.M).1 hΓ
    refine (gamma_le_iff 1 p _ D.M).2 fun Y' hY' hr' => ?_
    refine uc22p22qi_normalizer_map hm (fun Y hY hY1 => hΓ' Y hY
      (UC6.one_le_pRank_of_ne_bot hpP (hP.to_le (hY.trans inf_le_left)) hY1)) Y' hY'
      (uc22p22qv_ne_bot_of_pRank hpP hr')
  · obtain ⟨n, hn, hmodel⟩ := hL
    refine ⟨n, hn, ?_⟩
    rw [hL']
    exact CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.equivMapOfInjective _ _ hinj) hmodel
  · have h1 := uc22p22qi_frobenius_map m hfrob
    have e1 : (uniqueFourPrimeCore p D.M).map (MulAut.conj m).toMonoidHom = uniqueFourPrimeCore p D.M :=
      uc22p22qi_map_eq_of_conj_mem (M := D.M) (K := uniqueFourPrimeCore p D.M) (fun k hk x hx =>
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_conj_mem hx hk) hm
    have e2 : (pCoreOf 2 D.M).map (MulAut.conj m).toMonoidHom = pCoreOf 2 D.M :=
      uc22p22qi_map_eq_of_conj_mem (M := D.M) (K := pCoreOf 2 D.M)
        (fun k hk x hx => uc22p22qh_conj_mem_pCoreOf hk hx) hm
    rw [Subgroup.map_sup, e1, e2] at h1
    rw [hD']
    exact h1
  · rw [hP₁, uc22p22qi_centralizer_map m]
    exact Subgroup.map_mono hcent

theorem uc22p22qi_pair_conj (D : Data G) {p : ℕ} {P P₀ P' P₀' : Subgroup G} (hH : UC6.Hyp612 D p P P₀)
    (hH' : UC6.Hyp612 D p P' P₀')
    (hN : ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = p → Y ≠ P₀ → normalizer (Y : Set G) ≤ D.M) :
    ∃ m ∈ D.M, P' = P.map (MulAut.conj m).toMonoidHom ∧ P₀' = P₀.map (MulAut.conj m).toMonoidHom := by
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  haveI : Fact p.Prime := ⟨(D.sig_prime p hpσ).1⟩
  obtain ⟨k, hkM, hk⟩ := hH.sylow.exists_mem_conj hH'.sylow
  have hPP : P' = P.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [hk x, uc22p22qi_mem_map]
  set Y : Subgroup G := P₀'.map (MulAut.conj k⁻¹).toMonoidHom with hY
  have hYP : Y ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    have := (hk z).1 (hH'.le hz)
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hYcard : Nat.card Y = p := by
    rw [hY, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
    exact hH'.card
  have hYeq : Y = P₀ := by
    by_contra hne
    apply hH'.not_le
    intro g hg
    have hg' : k⁻¹ * g * k ∈ centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      have hzg := (Subgroup.mem_centralizer_iff.1 hg) z hz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc k⁻¹ * z * k * (k⁻¹ * g * k) = k⁻¹ * (z * g) * k := by group
        _ = k⁻¹ * (g * z) * k := by rw [hzg]
        _ = k⁻¹ * g * k * (k⁻¹ * z * k) := by group
    have h1 := hN Y hYP hYcard hne (Subgroup.centralizer_le_normalizer _ hg')
    have hgM : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
    rw [hgM]
    exact D.M.mul_mem (D.M.mul_mem hkM h1) (D.M.inv_mem hkM)
  refine ⟨k, hkM, hPP, ?_⟩
  ext x
  rw [uc22p22qi_mem_map, ← hYeq, hY, uc22p22qi_mem_map]
  simp only [inv_inv]
  rw [show k * (k⁻¹ * x * k) * k⁻¹ = x by group]

theorem uc22p22q_r613defAt_all (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) (hsp : Sigma2Print D)
    (hid : UC6.R613Ident D) (hcent : UC6.R613Cent D) :
    ∀ (p : ℕ) (P P₀ : Subgroup G), UC6.Hyp612 D p P P₀ → UC6.R613DefAt D p P P₀ := by
  intro p P' P₀' hH'
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH'.mem_sig2)
  obtain ⟨P, P₀, hH, hc2⟩ := hsp p hH'.mem_sig2
  have hd := uc22p22q_r613defAt_of D hstd h61 hH hc2 (hid p P P₀ hH) (hcent p P P₀ hH)
  obtain ⟨m, hm, rfl, rfl⟩ := uc22p22qi_pair_conj D hH hH' hc2.2.2.2.2.2.2
  exact uc22p22qi_r613defAt_map D (D.sig_prime p hpσ).1 hm hH.sylow.isPGroup hd

theorem sigma2Std_of_print {D : Data G} (hsp : Sigma2Print D) : Sigma2Std D :=
  ⟨fun p hp => by
    obtain ⟨P, P₀, hH, -⟩ := hsp p hp
    exact ⟨P, P₀, hH⟩⟩

theorem uc22p22q_r6_13_of_print (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) (hsp : Sigma2Print D)
    (hid : UC6.R613Ident D) (hcent : UC6.R613Cent D) (h4 : UC6.R613Aut D) : UC6.R6_13 D := by
  have h613 : UC6.R613Def D := uc22p22q_r613defAt_all D hstd h61 hsp hid hcent
  exact uc22p22q_r6_13_of D hstd h613 h4 (uc22p22q_r613irr_of D hstd h613)

theorem uc22p22q_r6_38_23_of_print (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D)
    (h611 : UC6.R6_11Used D) (hsp : Sigma2Print D) (hid : UC6.R613Ident D) (hcent : UC6.R613Cent D) :
    UC6.R6_38Sigma23 D :=
  uc22p22q_r6_38_23_of D hstd (sigma2Std_of_print hsp) h611 (uc22p22q_r613defAt_all D hstd h61 hsp hid hcent)

end CFSG.LocalAnalysis.UniquenessCase.UC22
