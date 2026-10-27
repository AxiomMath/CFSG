module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreSymType
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08k8_swap_conj {α : Type*} [DecidableEq α] {x y z : α} (hzx : z ≠ x)
    (hzy : z ≠ y) :
    Equiv.swap x y * Equiv.swap x z * Equiv.swap x y = Equiv.swap y z := by
  rw [Equiv.swap_comm x z,
    Equiv.swap_mul_swap_mul_swap (x := z) (y := x) (z := y) hzx hzy]

theorem ggQ2s08core_sym2 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ℓ : ℕ} (hℓ : 9 ≤ ℓ)
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (hWR : W ≤ R) (e : R ≃* Equiv.Perm (Fin (ℓ + 3)))
    (he : ∀ r : R, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    (s : Fin ℓ → (V ≃ₗ[ZMod 3] V)) (M : CoxeterMatrix (Fin ℓ))
    (hM : M = CoxeterMatrix.A ℓ ∨ M = CoxeterMatrix.B ℓ ∨ M = ggCoxeterMatrixD ℓ)
    (hsR : ∀ i, s i ∈ R) (hsrefl : ∀ i, GGLinRefl (s i))
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ M i j = 1) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hncomm : ∀ i j, i ≠ j → M i j ≠ 2 → s i * s j ≠ s j * s i)
    (hWs : W = Subgroup.closure (Set.range s)) (xv : V)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hr : GGLinRefl r) (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv) :
    GGQ2S08M0 R W r xv = R := by
  let τ : Fin ℓ → Equiv.Perm (Fin (ℓ + 3)) := fun k => e ⟨s k, hsR k⟩
  have hsw : ∀ k, (τ k).IsSwap := fun k => he ⟨s k, hsR k⟩ (hsrefl k)
  have hne : ∀ k l, k ≠ l → τ k ≠ τ l := by
    intro k l hkl h
    exact hdist k l hkl
      (congrArg (Subtype.val) (e.injective (by simpa only [τ] using h)))
  have hrelτ : ∀ k l, k ≠ l → (τ k * τ l) ^ M k l = 1 := by
    intro k l hkl
    have hcast : ((⟨s k, hsR k⟩ * ⟨s l, hsR l⟩ : R) ^ M k l) = 1 := by
      apply Subtype.ext
      simpa using hrel k l hkl
    calc (τ k * τ l) ^ M k l
        = e ((⟨s k, hsR k⟩ * ⟨s l, hsR l⟩ : R) ^ M k l) := by
          change (e ⟨s k, hsR k⟩ * e ⟨s l, hsR l⟩) ^ M k l =
            e ((⟨s k, hsR k⟩ * ⟨s l, hsR l⟩ : R) ^ M k l)
          rw [← map_mul, ← map_pow]
      _ = 1 := by rw [hcast, map_one]
  have hncommτ : ∀ k l, k ≠ l → M k l ≠ 2 → τ k * τ l ≠ τ l * τ k := by
    intro k l hkl h2 h
    apply hncomm k l hkl h2
    have hboth : e (⟨s k, hsR k⟩ * ⟨s l, hsR l⟩ : R) =
        e (⟨s l, hsR l⟩ * ⟨s k, hsR k⟩ : R) := by
      rw [map_mul, map_mul]
      exact h
    exact congrArg (Subtype.val) (e.injective hboth)
  obtain ⟨hMA, a, ha_inj, ha_eq⟩ :=
    ggQ2s08core_swap_coxeter hℓ τ hsw hne M hM hrelτ hncommτ
  let T : Finset (Fin (ℓ + 3)) := Finset.univ.image a
  have hTcard : T.card = ℓ + 1 := by
    change (Finset.univ.image a).card = ℓ + 1
    rw [Finset.card_image_of_injective Finset.univ ha_inj]
    simp
  have hTcompl : Tᶜ.card = 2 := by
    change (Finset.univ.image a)ᶜ.card = 2
    rw [Finset.card_compl, Finset.card_image_of_injective Finset.univ ha_inj]
    simp only [Fintype.card_fin, Finset.card_univ]
    omega
  obtain ⟨i, j, hij, hTij⟩ := Finset.card_eq_two.mp hTcompl
  have hmem_T_range : ∀ x : Fin (ℓ + 3), x ∈ T ↔ x ∈ Set.range a := by
    intro x
    change x ∈ Finset.univ.image a ↔ x ∈ Set.range a
    simp
  have hcompl_set : ∀ x : Fin (ℓ + 3), x ∉ Set.range a ↔ x = i ∨ x = j := by
    intro x
    rw [← hmem_T_range x, ← Finset.mem_compl, hTij]
    simp [Finset.mem_insert, Finset.mem_singleton]
  have hrange_iff : ∀ x : Fin (ℓ + 3), x ∈ Set.range a ↔ x ≠ i ∧ x ≠ j := by
    intro x
    constructor
    · intro h
      exact ⟨fun h1 => (hcompl_set x).mpr (Or.inl h1) h,
        fun h2 => (hcompl_set x).mpr (Or.inr h2) h⟩
    · rintro ⟨h1, h2⟩
      by_contra h
      rcases (hcompl_set x).mp h with h' | h' <;> contradiction
  have ha_mem_T : ∀ k, a k ∈ T := fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have hi_notin_T : i ∉ T := by
    rw [← Finset.mem_compl, hTij]; simp
  have hj_notin_T : j ∉ T := by
    rw [← Finset.mem_compl, hTij]; simp
  have ha_ne_i : ∀ k : Fin (ℓ + 1), a k ≠ i := fun k h => hi_notin_T (h ▸ ha_mem_T k)
  have ha_ne_j : ∀ k : Fin (ℓ + 1), a k ≠ j := fun k h => hj_notin_T (h ▸ ha_mem_T k)
  let sR : Fin ℓ → R := fun k => ⟨s k, hsR k⟩
  let H0 : Subgroup (Equiv.Perm (Fin (ℓ + 3))) := Subgroup.closure (Set.range τ)
  let FixH : Subgroup (Equiv.Perm (Fin (ℓ + 3))) :=
    fixingSubgroup (Equiv.Perm (Fin (ℓ + 3))) ({i, j} : Set (Fin (ℓ + 3)))
  have hH0_le_fix : H0 ≤ FixH := by
    change Subgroup.closure (Set.range τ) ≤ FixH
    rw [Subgroup.closure_le]
    rintro p ⟨k, rfl⟩
    change τ k ∈ fixingSubgroup (Equiv.Perm (Fin (ℓ + 3))) ({i, j} : Set (Fin (ℓ + 3)))
    rw [mem_fixingSubgroup_iff (Equiv.Perm (Fin (ℓ + 3)))]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [Equiv.Perm.smul_def, ha_eq k]
      exact Equiv.swap_apply_of_ne_of_ne (ha_ne_i k.castSucc).symm (ha_ne_i k.succ).symm
    · rw [Equiv.Perm.smul_def, ha_eq k]
      exact Equiv.swap_apply_of_ne_of_ne (ha_ne_j k.castSucc).symm (ha_ne_j k.succ).symm
  have hW' : Subgroup.comap R.subtype W = Subgroup.closure (Set.range sR) := by
    have hmapR : (Subgroup.closure (Set.range sR)).map R.subtype = W := by
      rw [MonoidHom.map_closure, hWs]
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨k, rfl⟩, hyx⟩
        exact ⟨k, hyx⟩
      · rintro ⟨k, rfl⟩
        exact ⟨sR k, ⟨k, rfl⟩, rfl⟩
    rw [← hmapR, Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
  have he_map : (Subgroup.closure (Set.range sR)).map e.toMonoidHom = H0 := by
    change (Subgroup.closure (Set.range sR)).map e.toMonoidHom = Subgroup.closure (Set.range τ)
    rw [MonoidHom.map_closure]
    congr 1
    ext p
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, hyx⟩
      exact ⟨k, hyx⟩
    · rintro ⟨k, rfl⟩
      exact ⟨sR k, ⟨k, rfl⟩, rfl⟩
  have hmem_closure_of_W : ∀ x : R, (x : V ≃ₗ[ZMod 3] V) ∈ W → e x ∈ H0 := by
    intro x hx
    have hx' : x ∈ Subgroup.comap R.subtype W := hx
    rw [hW'] at hx'
    have hx'' : e x ∈ (Subgroup.closure (Set.range sR)).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx', rfl⟩
    rwa [he_map] at hx''
  have hmem_W_of_closure : ∀ x : R, e x ∈ H0 → (x : V ≃ₗ[ZMod 3] V) ∈ W := by
    intro x hx
    have hx' : e x ∈ (Subgroup.closure (Set.range sR)).map e.toMonoidHom := by rwa [← he_map] at hx
    rw [Subgroup.mem_map] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [e.injective hyx] at hy
    have : x ∈ Subgroup.comap R.subtype W := by rwa [← hW'] at hy
    exact this
  have hSswaps0 : ∀ m n : Fin (ℓ + 1), Equiv.swap (a m) (a n) ∈ H0 := by
    have hpath0 : ∀ n : Fin (ℓ + 1), Equiv.swap (a 0) (a n) ∈ H0 := by
      intro n
      induction n using Fin.induction with
      | zero => rw [Equiv.swap_self]; exact H0.one_mem
      | succ k ih =>
          refine SubmonoidClass.swap_mem_trans H0 ih ?_
          rw [← ha_eq k]
          exact Subgroup.subset_closure ⟨k, rfl⟩
    intro m n
    by_cases hzx : a n = a 0
    · rw [hzx, Equiv.swap_comm]; exact hpath0 m
    by_cases hzy : a n = a m
    · rw [hzy, Equiv.swap_self]; exact H0.one_mem
    rw [← ggQ2s08k8_swap_conj hzx hzy]
    exact H0.mul_mem (H0.mul_mem (hpath0 m) (hpath0 n)) (hpath0 m)
  let gR : R := e.symm (Equiv.swap i j)
  let gem : V ≃ₗ[ZMod 3] V := (gR : V ≃ₗ[ZMod 3] V)
  have hg_eq : e gR = Equiv.swap i j := e.apply_symm_apply _
  have hgem_linstab : gem ∈ GGQ2S08LineStab R xv := by
    have hcomm : ∀ w : R, (w : V ≃ₗ[ZMod 3] V) ∈ W →
        (w : V ≃ₗ[ZMod 3] V) * (gR : V ≃ₗ[ZMod 3] V) =
          (gR : V ≃ₗ[ZMod 3] V) * (w : V ≃ₗ[ZMod 3] V) := by
      intro w hw
      have hwfix : e w ∈ FixH := hH0_le_fix (hmem_closure_of_W w hw)
      have hwi : e w i = i := by
        have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin (ℓ + 3)))).mp hwfix i (by simp)
        simpa [Equiv.Perm.smul_def] using this
      have hwj : e w j = j := by
        have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin (ℓ + 3)))).mp hwfix j (by simp)
        simpa [Equiv.Perm.smul_def] using this
      have hcomm_perm : e w * Equiv.swap i j = Equiv.swap i j * e w := by
        rw [Equiv.mul_swap_eq_swap_mul, hwi, hwj]
      have hboth : e (w * gR) = e (gR * w) := by
        rw [map_mul, map_mul, hg_eq, hcomm_perm]
      exact congrArg (Subtype.val) (e.injective hboth)
    have hgem_fix : ∀ v : V, (∀ w ∈ W, w v = v) → (∀ w ∈ W, w (gem v) = gem v) := by
      intro v hv w hw
      have hcw : w * (gR : V ≃ₗ[ZMod 3] V) = (gR : V ≃ₗ[ZMod 3] V) * w := hcomm ⟨w, hWR hw⟩ hw
      calc w (gem v) = (w * (gR : V ≃ₗ[ZMod 3] V)) v := rfl
        _ = ((gR : V ≃ₗ[ZMod 3] V) * w) v := by rw [hcw]
        _ = gem (w v) := rfl
        _ = gem v := by rw [hv w hw]
    have hxv_fix : ∀ w ∈ W, w xv = xv :=
      (hWfix xv).mpr (Submodule.subset_span (Set.mem_singleton xv))
    have hgem_span : gem xv ∈ Submodule.span (ZMod 3) {xv} :=
      (hWfix (gem xv)).mp (hgem_fix xv hxv_fix)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgem_span
    have hxv_ne : xv ≠ 0 := by
      intro h0
      apply hrx
      exact ⟨1, by rw [h0, map_zero, one_smul]⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      apply hxv_ne
      have h1 : gem xv = gem 0 := by rw [hc.symm, hc0, zero_smul, map_zero]
      exact gem.injective h1
    exact ⟨gR.2, c, hc_ne, hc.symm⟩
  have hr_notin_linstab : r ∉ GGQ2S08LineStab R xv := fun h =>
    hrx ⟨h.2.choose, h.2.choose_spec.2⟩
  have hrW : r ∉ W := by
    intro hrw
    apply hrx
    have hrv : r xv = xv := (hWfix xv).mpr (Submodule.subset_span (Set.mem_singleton xv)) r hrw
    exact ⟨1, by rw [hrv, one_smul]⟩
  let er : Equiv.Perm (Fin (ℓ + 3)) := e ⟨r, hrR⟩
  obtain ⟨c0, d0, hc0d0, her0⟩ := he ⟨r, hrR⟩ hr
  have her : er = Equiv.swap c0 d0 := her0
  have her_notin_H0 : er ∉ H0 := by
    intro h
    exact hrW (hmem_W_of_closure ⟨r, hrR⟩ h)
  have hnotboth_S : ¬ (c0 ∈ Set.range a ∧ d0 ∈ Set.range a) := by
    rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    apply her_notin_H0
    rw [her]
    exact hSswaps0 m n
  have hnotboth_ij : ¬ (c0 ∈ ({i, j} : Set (Fin (ℓ + 3))) ∧
      d0 ∈ ({i, j} : Set (Fin (ℓ + 3)))) := by
    rintro ⟨hc0, hd0⟩
    have hswap_eq : Equiv.swap c0 d0 = Equiv.swap i j := by
      rcases hc0 with rfl | rfl <;> rcases hd0 with rfl | rfl
      · exact absurd rfl hc0d0
      · rfl
      · rw [Equiv.swap_comm]
      · exact absurd rfl hc0d0
    have hrg : (⟨r, hrR⟩ : R) = gR := by
      apply e.injective
      have h1 : e ⟨r, hrR⟩ = Equiv.swap c0 d0 := her
      rw [h1, hswap_eq, hg_eq]
    have hrgem : r = gem := congrArg (Subtype.val) hrg
    exact hr_notin_linstab (hrgem.symm ▸ hgem_linstab)
  have hc_or_d_in_ij : c0 = i ∨ c0 = j ∨ d0 = i ∨ d0 = j := by
    by_contra h
    simp only [not_or] at h
    obtain ⟨hc0i, hc0j, hd0i, hd0j⟩ := h
    apply hnotboth_S
    refine ⟨?_, ?_⟩
    · by_contra hc
      rcases (hcompl_set c0).mp hc with h' | h' <;> contradiction
    · by_contra hd
      rcases (hcompl_set d0).mp hd with h' | h' <;> contradiction
  let Tgen : Set (Equiv.Perm (Fin (ℓ + 3))) := Set.range τ ∪ {er} ∪ {Equiv.swap i j}
  let H : Subgroup (Equiv.Perm (Fin (ℓ + 3))) := Subgroup.closure Tgen
  have hH0_le_H : H0 ≤ H := by
    change Subgroup.closure (Set.range τ) ≤ Subgroup.closure Tgen
    exact Subgroup.closure_mono (by rintro p hp; exact Or.inl (Or.inl hp))
  have h_ijH : Equiv.swap i j ∈ H := Subgroup.subset_closure (by simp [Tgen])
  have hErH : er ∈ H := Subgroup.subset_closure (by simp [Tgen])
  have h_conn : ∃ q : Fin (ℓ + 3), q ∈ Set.range a ∧ Equiv.swap i q ∈ H := by
    rcases hc_or_d_in_ij with hci | hcj | hdi | hdj
    · rw [hci] at her
      have hd0i : d0 ≠ i := fun h => hc0d0 (by rw [hci, h])
      have hd0j : d0 ≠ j := by
        intro h
        exact hnotboth_ij ⟨by rw [hci]; simp, by rw [h]; simp⟩
      exact ⟨d0, (hrange_iff d0).mpr ⟨hd0i, hd0j⟩, her ▸ hErH⟩
    · rw [hcj] at her
      have hd0i : d0 ≠ i := by
        intro h
        exact hnotboth_ij ⟨by rw [hcj]; simp, by rw [h]; simp⟩
      have hd0j : d0 ≠ j := fun h => hc0d0 (by rw [hcj, h])
      refine ⟨d0, (hrange_iff d0).mpr ⟨hd0i, hd0j⟩, ?_⟩
      exact SubmonoidClass.swap_mem_trans H h_ijH (her ▸ hErH)
    · rw [hdi] at her
      have hc0i : c0 ≠ i := fun h => hc0d0 (by rw [h, hdi])
      have hc0j : c0 ≠ j := by
        intro h
        exact hnotboth_ij ⟨by rw [h]; simp, by rw [hdi]; simp⟩
      exact ⟨c0, (hrange_iff c0).mpr ⟨hc0i, hc0j⟩, by rw [Equiv.swap_comm]; exact her ▸ hErH⟩
    · rw [hdj] at her
      have hc0i : c0 ≠ i := by
        intro h
        exact hnotboth_ij ⟨by rw [h]; simp, by rw [hdj]; simp⟩
      have hc0j : c0 ≠ j := fun h => hc0d0 (by rw [h, hdj])
      have hjc0 : Equiv.swap j c0 ∈ H := by rw [Equiv.swap_comm]; exact her ▸ hErH
      exact ⟨c0, (hrange_iff c0).mpr ⟨hc0i, hc0j⟩,
        SubmonoidClass.swap_mem_trans H h_ijH hjc0⟩
  have hswap : ∀ x : Fin (ℓ + 3), Equiv.swap i x ∈ H := by
    intro x
    by_cases hx : x ∈ Set.range a
    · obtain ⟨n, rfl⟩ := hx
      obtain ⟨q, hqS, hq⟩ := h_conn
      obtain ⟨m, rfl⟩ := hqS
      exact SubmonoidClass.swap_mem_trans H hq (hH0_le_H (hSswaps0 m n))
    · rcases (hcompl_set x).mp hx with rfl | rfl
      · rw [Equiv.swap_self]; exact H.one_mem
      · exact h_ijH
  haveI : MulAction.IsPretransitive H (Fin (ℓ + 3)) :=
    MulAction.IsPretransitive.of_orbit (x₀ := i) (fun x =>
      ⟨⟨Equiv.swap i x, hswap x⟩, by simp [Equiv.Perm.smul_def]⟩)
  have hTswap : ∀ σ ∈ Tgen, σ.IsSwap := by
    intro σ hσ
    rcases hσ with (⟨k, rfl⟩ | hσ) | hσ
    · exact hsw k
    · rw [Set.mem_singleton_iff] at hσ
      rw [hσ]
      exact he ⟨r, hrR⟩ hr
    · rw [Set.mem_singleton_iff] at hσ
      exact ⟨i, j, hij, hσ⟩
  have hHtop : H = ⊤ := by
    change Subgroup.closure Tgen = ⊤
    exact closure_of_isSwap_of_isPretransitive hTswap
  let SsetR : Set R := Set.range sR ∪ {⟨r, hrR⟩} ∪ {gR}
  let Sset : Set (V ≃ₗ[ZMod 3] V) := Set.range s ∪ {r} ∪ {gem}
  have he_image : e.toMonoidHom '' SsetR = Tgen := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with (hy | hy) | hy
      · rcases hy with ⟨k, rfl⟩; exact Or.inl (Or.inl ⟨k, rfl⟩)
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact Or.inl (Or.inr rfl)
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact Or.inr hg_eq
    · intro hp
      rcases hp with (hp | hp) | hp
      · rcases hp with ⟨k, rfl⟩; exact ⟨sR k, Or.inl (Or.inl ⟨k, rfl⟩), rfl⟩
      · rw [Set.mem_singleton_iff] at hp; subst hp
        exact ⟨⟨r, hrR⟩, Or.inl (Or.inr rfl), rfl⟩
      · rw [Set.mem_singleton_iff] at hp; subst hp
        exact ⟨gR, Or.inr rfl, hg_eq⟩
  have hmap_e : (Subgroup.closure SsetR).map e.toMonoidHom = ⊤ := by
    rw [MonoidHom.map_closure, he_image]
    exact hHtop
  have hclosureR : Subgroup.closure SsetR = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ (Subgroup.closure SsetR).map e.toMonoidHom := by
      rw [hmap_e]; exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact (e.injective hyx) ▸ hy
  have hmap_subtype : (Subgroup.closure SsetR).map R.subtype = Subgroup.closure Sset := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with (hy | hy) | hy
      · rcases hy with ⟨k, rfl⟩; exact Or.inl (Or.inl ⟨k, rfl⟩)
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact Or.inl (Or.inr rfl)
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact Or.inr rfl
    · intro hx
      rcases hx with (hx | hx) | hx
      · rcases hx with ⟨k, rfl⟩
        exact ⟨sR k, Or.inl (Or.inl ⟨k, rfl⟩), rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨⟨r, hrR⟩, Or.inl (Or.inr rfl), hx.symm⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨gR, Or.inr rfl, hx.symm⟩
  have hclosure_le_R : Subgroup.closure Sset ≤ R :=
    (Subgroup.closure_le R).mpr (by
      intro x hx
      rcases hx with (h1 | h2) | h3
      · rcases h1 with ⟨k, rfl⟩; exact hsR k
      · rw [Set.mem_singleton_iff] at h2; rw [h2]; exact hrR
      · rw [Set.mem_singleton_iff] at h3; rw [h3]; exact gR.2)
  have hR_le_closure : R ≤ Subgroup.closure Sset := by
    intro x hx
    have hx' : e ⟨x, hx⟩ ∈ (Subgroup.closure SsetR).map e.toMonoidHom := by
      rw [hmap_e]; exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyG : (y : V ≃ₗ[ZMod 3] V) ∈ Subgroup.closure Sset := by
      rw [← hmap_subtype]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rw [congrArg (Subtype.val) (e.injective hyx)] at hyG
    exact hyG
  have hclosure_Sset : Subgroup.closure Sset = R := le_antisymm hclosure_le_R hR_le_closure
  have hM0_le_R : GGQ2S08M0 R W r xv ≤ R := by
    rw [GGQ2S08M0]
    exact (Subgroup.closure_le R).mpr (by
      intro x hx
      rcases hx with (h1 | h2) | h3
      · exact hWR h1
      · rw [Set.mem_singleton_iff] at h2; rw [h2]; exact hrR
      · exact h3.1)
  have hSset_le_M0 : Sset ⊆ GGQ2S08M0 R W r xv := by
    intro x hx
    rcases hx with (h1 | h2) | h3
    · rcases h1 with ⟨k, rfl⟩
      apply Subgroup.subset_closure
      exact Or.inl (Or.inl (by rw [hWs]; exact Subgroup.subset_closure ⟨k, rfl⟩))
    · rw [Set.mem_singleton_iff] at h2
      rw [h2]
      apply Subgroup.subset_closure
      exact Or.inl (Or.inr rfl)
    · rw [Set.mem_singleton_iff] at h3
      rw [h3]
      apply Subgroup.subset_closure
      exact Or.inr hgem_linstab
  have hR_le_M0 : R ≤ GGQ2S08M0 R W r xv := by
    have hle : Subgroup.closure Sset ≤ GGQ2S08M0 R W r xv :=
      (Subgroup.closure_le (GGQ2S08M0 R W r xv)).mpr hSset_le_M0
    rwa [hclosure_Sset] at hle
  exact le_antisymm hM0_le_R hR_le_M0

end CFSG.StandardType

end
