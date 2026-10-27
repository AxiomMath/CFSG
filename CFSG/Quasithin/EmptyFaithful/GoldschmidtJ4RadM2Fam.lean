module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4RadM3Blk

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.J4Loc

@[expose] noncomputable def u5 : J := pathElt (repPaths.getD 5 [])

theorem u5_not_mem_Hj
    (hM : MatFacts) : u5 ∉ Hj := by
  intro h
  have h1 : u5 * eta uJ 11 1 * u5⁻¹ ∈ Eg uJ 11 :=
    Hj_normalizes_Eg hM u5 h _ (eta_mem_Eg 11 le_rfl 1)
  exact not_mem_Eg_conj hM (by norm_num : 1 ≤ 5) (by norm_num : 5 ≤ 6)
    (x := eta uJ 11 1) ⟨1, one_mem_tMasks, rfl⟩ h1

theorem u5_conj_mem
    (hM : MatFacts) :
    ∀ c ∈ i5Masks, u5 * eta uJ 11 c * u5⁻¹ ∈ Eg uJ 11 := by
  intro c hc
  unfold i5Masks at hc
  rw [mem_srt] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [eta_zero]
    simp only [mul_one, mul_inv_cancel]
    exact (Eg uJ 11).one_mem
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    unfold u5
    rw [conj_i5Pairs hM p hp]
    exact eta_mem_Eg 11 le_rfl _

theorem exists_BV
    (hM : MatFacts) :
    ∃ g : J, g ∉ Hj ∧ ∀ x ∈ V0, g⁻¹ * x * g ∈ Eg uJ 11 := by
  obtain ⟨h5, hh5, h5W⟩ := trio_orbit hM i5Masks i5_prop.2
  refine ⟨h5⁻¹ * u5⁻¹, ?_, ?_⟩
  · intro h
    apply u5_not_mem_Hj hM
    have : h5 * (h5⁻¹ * u5⁻¹) ∈ Hj := Hj.mul_mem hh5 h
    have h' : u5⁻¹ ∈ Hj := by simpa using this
    simpa using Hj.inv_mem h'
  · intro x hx
    have hx' : h5 * x * h5⁻¹ ∈ maskSub i5Masks := by
      rw [h5W]
      have e : h5⁻¹ * (h5 * x * h5⁻¹) * h5 = x := by group
      refine mem_conjSub.mpr ?_
      rw [e]
      exact hx
    obtain ⟨c, hc, hxc⟩ := (mem_maskSub_iff hM (trio_xor _ i5_prop.2).1
      (trio_xor _ i5_prop.2).2).1 hx'
    have := u5_conj_mem hM c hc
    have e : (h5⁻¹ * u5⁻¹)⁻¹ * x * (h5⁻¹ * u5⁻¹) = u5 * (h5 * x * h5⁻¹) * u5⁻¹ := by group
    rw [e, hxc]
    exact this

theorem Ig_eq_conjSub
    (hF : J4Facts) {k g : J} (hk : k ∈ Hj) (hg0 : g ∉ Hj)
    (hg : ∀ x ∈ V0, g⁻¹ * x * g ∈ Eg uJ 11) :
    Ig (k * g) = ((conjSub k V0 : Subgroup J) : Set J) := by
  have hM := hF.mat
  have hkg : k * g ∉ Hj := fun h => hg0 (by
    have := Hj.mul_mem (Hj.inv_mem hk) h
    simpa using this)
  have hsub := conjSub_V0_subset_Ig hM hk hg
  have hc8 : (Ig (k * g)).ncard ≤ 8 := card_inter_le hF hkg
  have hn : ((conjSub k V0 : Subgroup J) : Set J).ncard = 8 := by
    rw [ncard_conjSub, ← Nat.card_coe_set_eq]
    exact card_V0 hM
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hn]; exact hc8) (Set.toFinite _)).symm

theorem conj_mem_Ig (hM : MatFacts) {G r : J} (hr : r ∈ Hj)
    (hrG : G⁻¹ * r * G ∈ Hj) {x : J} (hx : x ∈ Ig G) : r * x * r⁻¹ ∈ Ig G := by
  obtain ⟨hxE, hxG⟩ := hx
  refine ⟨Hj_normalizes_Eg hM r hr x hxE, ?_⟩
  have := Hj_normalizes_Eg hM _ hrG _ hxG
  have e : (G⁻¹ * r * G) * (G⁻¹ * x * G) * (G⁻¹ * r * G)⁻¹ = G⁻¹ * (r * x * r⁻¹) * G := by group
  rwa [e] at this

theorem conjSub_eq_of_maps {Γ : Type*} [Group Γ] {A : Subgroup Γ} {r : Γ}
    (h1 : ∀ x ∈ A, r * x * r⁻¹ ∈ A) (h2 : ∀ x ∈ A, r⁻¹ * x * r ∈ A) : conjSub r A = A := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have := h1 _ hx
    have e : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
    rwa [e] at this
  · intro hx
    exact h2 x hx

theorem normalizes_maskSub
    (hF : J4Facts)
    {R : Subgroup J} (hRH : R ≤ Hj)
    (hN : Subgroup.centralizer ({z0} : Set J) ≤ Subgroup.normalizer (R : Set J))
    {W : List ℕ} (hW : W ∈ w15L) {r : J} (hr : r ∈ R) : conjSub r (maskSub W) = maskSub W := by
  have hM := hF.mat
  obtain ⟨g₀, hg₀H, hg₀⟩ := exists_BV hM
  have hz0 : z0 ∈ Zl := z0_mem_Zl
  have hWt := w15_subset_trio W hW
  obtain ⟨k, hkH, hkW⟩ := trio_orbit hM W hWt
  set G : J := k * g₀ with hG
  have hGOpt : ((G : J) : J ⧸ Hj) ∈ Opt z0 := by
    refine ⟨G, rfl, ?_⟩
    have h1131 : 1131 ∈ W := one_mem_of_mem_w15 hW
    have hz : z0 ∈ maskSub W :=
      (mem_maskSub_iff hM (trio_xor _ hWt).1 (trio_xor _ hWt).2).2 ⟨1131, h1131, rfl⟩
    rw [hkW] at hz
    have hv : k⁻¹ * z0 * k ∈ V0 := mem_conjSub.mp hz
    have := hg₀ _ hv
    have e : g₀⁻¹ * (k⁻¹ * z0 * k) * g₀ = G⁻¹ * z0 * G := by rw [hG]; group
    rwa [e] at this
  have hfix : ∀ r ∈ R, r • ((G : J) : J ⧸ Hj) = ((G : J) : J ⧸ Hj) := by
    intro r hr
    obtain ⟨m, hm, hmw⟩ := exists_mem_centralizer_of_mem_Opt hF hz0 hGOpt
    have hmrm : m⁻¹ * r * m ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp
        (hN ((Subgroup.centralizer ({z0} : Set J)).inv_mem hm)) r).mp hr
      simpa using this
    rw [← hmw]
    have e : r * m = m * (m⁻¹ * r * m) := by group
    rw [smul_smul, e, mul_smul]
    have : (m⁻¹ * r * m) • basePt = basePt := smul_basePt_eq_self_iff.mpr (hRH hmrm)
    rw [this]
  have hIg : Ig G = ((maskSub W : Subgroup J) : Set J) := by
    rw [hG, hkW]
    exact Ig_eq_conjSub hF hkH hg₀H hg₀
  have hmaps : ∀ r ∈ R, ∀ x ∈ maskSub W, r * x * r⁻¹ ∈ maskSub W := by
    intro r hr x hx
    have hrG : G⁻¹ * r * G ∈ Hj := by
      have := QuotientGroup.eq.mp (hfix r hr).symm
      simpa [smul_mk, mul_assoc] using this
    have hx' : x ∈ Ig G := by rw [hIg]; exact hx
    have := conj_mem_Ig hM (hRH hr) hrG hx'
    rw [hIg] at this
    exact this
  exact conjSub_eq_of_maps (hmaps r hr) (fun x hx => by
    simpa using hmaps r⁻¹ (R.inv_mem hr) x hx)

@[expose] def X15 : Set (Subgroup J) := {A | ∃ W ∈ w15L, A = maskSub W}

theorem X15_closed
    (hM : MatFacts) :
    ∀ c ∈ Subgroup.centralizer ({z0} : Set J) ⊓ Hj, ∀ A ∈ X15, conjSub c A ∈ X15 := by
  intro c hc A hA
  have hcz : c ∈ Subgroup.centralizer ({z0} : Set J) := (Subgroup.mem_inf.mp hc).1
  have hcH : c ∈ Hj := (Subgroup.mem_inf.mp hc).2
  obtain ⟨W, hW, rfl⟩ := hA
  have hWt := w15_subset_trio W hW
  obtain ⟨W', hW't, himg⟩ := (trio_conj hM hcH).1 W hWt
  have h1131 : 1131 ∈ W := one_mem_of_mem_w15 hW
  obtain ⟨c', hc', ec⟩ := himg.1 1131 h1131
  have hcz' : c * z0 = z0 * c := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hcz
    exact hcz
  have hz : c * eta uJ 11 1131 * c⁻¹ = eta uJ 11 1131 := by
    have : c * z0 * c⁻¹ = z0 := by rw [hcz']; group
    exact this
  have hc'eq : c' = 1131 :=
    eta_inj' hM ((trio_prop.2 W' hW't).2.1 c' hc') (by norm_num) (ec.symm.trans hz)
  refine ⟨W', ?_, ?_⟩
  · refine ⟨hW't, ?_⟩
    rw [← hc'eq]
    exact hc'
  · exact (conjSub_maskSub hM himg (trio_xor W hWt).1 (trio_xor W hWt).2 (trio_xor W' hW't).1
      (trio_xor W' hW't).2)

theorem conjSub_wordElt_maskSub
    (hM : MatFacts) {w : List Int} (hw : ∀ ℓ ∈ w, ℓ ∈ letters)
    {W : List ℕ} (hW : W ∈ trioL) (hW' : imgW w W ∈ trioL) :
    conjSub (wordElt w) (maskSub W) = maskSub (imgW w W) := by
  ext x
  rw [mem_conjSub, mem_maskSub_iff hM (trio_xor _ hW).1 (trio_xor _ hW).2,
    mem_maskSub_iff hM (trio_xor _ hW').1 (trio_xor _ hW').2]
  constructor
  · rintro ⟨c, hc, e⟩
    refine ⟨actW w c, ?_, ?_⟩
    · unfold imgW
      rw [mem_srt]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    · rw [← wordElt_conj hM hw c, ← e]
      group
  · rintro ⟨c', hc', e⟩
    unfold imgW at hc'
    rw [mem_srt] at hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    refine ⟨c, hc, ?_⟩
    rw [e, ← wordElt_conj hM hw c]
    group

theorem maskSub_ne_of_toFinset_ne
    (hM : MatFacts) {A B : List ℕ} (hA : A ∈ trioL) (hB : B ∈ trioL)
    (h : A.toFinset ≠ B.toFinset) : maskSub A ≠ maskSub B := fun h' =>
  h (toFinset_eq_of_maskSub_eq hM hA hB h')

theorem wordElt_mem_C (hM : MatFacts) {w : List Int}
    (hw : ∀ ℓ ∈ w, ℓ ∈ letters) (hfix : actW w 1131 = 1131) :
    wordElt w ∈ Subgroup.centralizer ({z0} : Set J) ⊓ Hj := by
  refine Subgroup.mem_inf.mpr ⟨?_, wordElt_mem hw⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := wordElt_conj hM hw 1131
  rw [hfix] at h
  have : wordElt w * z0 * (wordElt w)⁻¹ = z0 := h
  calc wordElt w * z0 = (wordElt w * z0 * (wordElt w)⁻¹) * wordElt w := by group
    _ = z0 * wordElt w := by rw [this]

end CFSG.Quasithin.J4Rad
