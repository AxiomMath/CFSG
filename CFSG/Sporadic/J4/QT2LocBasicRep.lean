module

public import CFSG.Sporadic.J4.QT2LocBasic
public import CFSG.Sporadic.J4.QT2LocZProof
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Check
public import CFSG.Sporadic.J4.QT2LocFixMainBase
public import CFSG.Sporadic.J4.QT2LocUniqBase
public import CFSG.Sporadic.J4.QT2LocUniqCheck
public import Certificates.Certificate4008

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix
open scoped Classical

theorem stab_w₀_b (hF : J4Basic) {x : J} (h : x • w₀ = w₀) : x ∈ Hj := hF.stab x h

theorem Rel_smul_w₀_b (hF : J4Basic) {ℓ : ℕ} {g : J} {q : Row} :
    Rel ℓ (g • w₀) q ↔ g⁻¹ • q ∈ Dlt ℓ := by
  constructor
  · rintro ⟨g', hg', hmem⟩
    have h1 : (g⁻¹ * g') • w₀ = w₀ := by rw [mul_smul, hg', inv_smul_smul]
    have hH : g⁻¹ * g' ∈ Hj := stab_w₀_b hF h1
    have := Dlt_smul_mem hH hmem
    rwa [← mul_smul, mul_assoc, mul_inv_cancel, mul_one] at this
  · exact fun h => ⟨g, rfl, h⟩

theorem rep_zero_b : rep 0 = w₀ := by
  rw [rep_eq]
  simp [uElt, pathElt, repPaths]

theorem smul_rep_form_b (hM : MatFacts) {ℓ : ℕ} {h h' : J} (hh' : h' ∈ Hj) :
    (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') • w₀ = h • rep ℓ := by
  rw [mul_smul, mul_smul, smul_root_of_mem_Hj hM hh', rep_eq]
  rfl

theorem fix2B_facts_b : ∀ l ∈ List.range' 1 4, ∀ c ∈ tMasks,
    differs (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 c))
      (pathVec (repPaths.getD l []))) (pathVec (repPaths.getD l [])) = true := by
  have h := chkFix2B_true
  unfold chkFix2B at h
  simp only [List.all_eq_true] at h
  exact h

theorem fix2B_subset_b
    (hF : J4Basic) {c : ℕ} (hc : c ∈ tMasks) {g : J}
    (hfix : eta uJ 11 c • (g • w₀) = g • w₀) :
    g • w₀ = w₀ ∨ g • w₀ ∈ Dlt 5 ∨ g • w₀ ∈ Dlt 6 := by
  have hM := hF.mat
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := Certificates.certificate4008.1 g
  rw [smul_rep_form_b hM hh'] at hfix ⊢
  have h1 : (h⁻¹ * eta uJ 11 c * h) • rep ℓ = rep ℓ := by
    rw [mul_smul, mul_smul, hfix, inv_smul_smul]
  obtain ⟨c', hc', hc'e⟩ := (tSet_conj hM h hh).2 _ (⟨c, hc, rfl⟩ : eta uJ 11 c ∈ tSet)
  rw [hc'e] at h1
  interval_cases ℓ
  · left
    rw [rep_zero_b]
    exact smul_root_of_mem_Hj hM hh
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts_b _ (by decide) c' hc'))
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts_b _ (by decide) c' hc'))
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts_b _ (by decide) c' hc'))
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts_b _ (by decide) c' hc'))
  · exact Or.inr (Or.inl ⟨h, hh, rfl⟩)
  · exact Or.inr (Or.inr ⟨h, hh, rfl⟩)

theorem fix2B_rel_b
    (hF : J4Basic) {c : ℕ} (hc : c ∈ tMasks) {g k : J}
    (hfix : (g * eta uJ 11 c * g⁻¹) • (k • w₀) = k • w₀) :
    k • w₀ = g • w₀ ∨ Rel 5 (g • w₀) (k • w₀) ∨ Rel 6 (g • w₀) (k • w₀) := by
  rcases fix2B_subset_b hF hc (conj_fix_transfer hfix) with h | h | h
  · exact Or.inl (eq_of_inv_smul_eq h)
  · exact Or.inr (Or.inl (Rel_smul_w₀_b hF |>.2 (by rwa [mul_smul] at h)))
  · exact Or.inr (Or.inr (Rel_smul_w₀_b hF |>.2 (by rwa [mul_smul] at h)))

theorem card_inter_le_b
    (hF : J4Basic) {g : J} (hg : g ∉ Hj) :
    {x : J | x ∈ Eg uJ 11 ∧ g⁻¹ * x * g ∈ Eg uJ 11}.ncard ≤ 8 := by
  have hM := hF.mat
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := Certificates.certificate4008.1 g
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    apply hg
    have : pathElt (repPaths.getD 0 []) = 1 := by simp [repPaths, pathElt]
    rw [this]
    simpa using Hj.mul_mem hh hh'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cands_parts
  have hcz : (candZ (locMats ()) (locInvs ()) ℓ).length ≤ 7 := by
    interval_cases ℓ <;> simp_all
  have hZE : (ZE' ℓ).card ≤ 7 := ZE'_card_le hM hℓ (pathInv_get hℓ) hcz
  set u := pathElt (repPaths.getD ℓ []) with hu
  have hmap : ∀ x ∈ {x : J | x ∈ Eg uJ 11 ∧ (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') ∈ Eg uJ 11},
      h⁻¹ * x * h ∈ insert (1 : J) (↑(ZE' ℓ) : Set J) := by
    rintro x ⟨hxE, hxg⟩
    have hx' : h⁻¹ * x * h ∈ Eg uJ 11 := by
      have := Hj_normalizes_Eg hM h⁻¹ (Hj.inv_mem hh) x hxE
      simpa using this
    have hx'' : u * (h⁻¹ * x * h) * u⁻¹ ∈ Eg uJ 11 := by
      have e : u * (h⁻¹ * x * h) * u⁻¹ = h' * ((h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h')) * h'⁻¹ := by
        group
      rw [e]
      exact Hj_normalizes_Eg hM h' hh' _ hxg
    by_cases h1 : h⁻¹ * x * h = 1
    · exact Or.inl h1
    · right
      obtain ⟨c, hcl, hc⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx'
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact h1 (by rw [hc, eta_zero])
      rcases mask_cover c hcl with h0 | hT | hZ
      · exact absurd h0 hc0
      · exfalso
        have hxT : h⁻¹ * x * h ∈ tSet := ⟨c, hT, hc⟩
        exact not_mem_Eg_conj hM (by omega) (by omega) hxT hx''
      · have hxZ : h⁻¹ * x * h ∈ Zl := mem_Zl.2 ⟨c, hZ, hc.symm⟩
        rw [Finset.mem_coe, ZE', Finset.mem_filter]
        exact ⟨hxZ, hx''⟩
  have hinj : Set.InjOn (fun x : J => h⁻¹ * x * h)
      {x : J | x ∈ Eg uJ 11 ∧ (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') ∈ Eg uJ 11} := by
    intro a _ b _ e
    simpa using e
  have hfin : (insert (1 : J) (↑(ZE' ℓ) : Set J)).Finite :=
    Set.Finite.insert _ (Finset.finite_toSet _)
  calc {x : J | x ∈ Eg uJ 11 ∧ (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') ∈ Eg uJ 11}.ncard
      ≤ (insert (1 : J) (↑(ZE' ℓ) : Set J)).ncard :=
        Set.ncard_le_ncard_of_injOn (fun x : J => h⁻¹ * x * h) hmap hinj hfin
    _ ≤ (↑(ZE' ℓ) : Set J).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ 8 := by
      rw [Set.ncard_coe_finset]
      omega

theorem mem_Hj_of_big_inter_b
    (hF : J4Basic) {g : J} {V : Subgroup J} (hVE : V ≤ Eg uJ 11)
    (hVg : ∀ v ∈ V, g⁻¹ * v * g ∈ Eg uJ 11) (hcard : 8 < Nat.card V) : g ∈ Hj := by
  by_contra hg
  have hsub : (V : Set J) ⊆ {x : J | x ∈ Eg uJ 11 ∧ g⁻¹ * x * g ∈ Eg uJ 11} :=
    fun v hv => ⟨hVE hv, hVg v hv⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := card_inter_le_b hF hg
  have h3 : Nat.card V = (V : Set J).ncard := Nat.card_coe_set_eq (V : Set J)
  omega

theorem normalizer_le_Hj_of_le_E_b
    (hF : J4Basic) {V : Subgroup J} (hVE : V ≤ Eg uJ 11)
    (hcard : Nat.card V = 16) : Subgroup.normalizer (V : Set J) ≤ Hj := by
  intro n hn
  refine mem_Hj_of_big_inter_b hF (V := V) hVE (fun v hv => ?_) (by rw [hcard]; norm_num)
  have h := (Subgroup.mem_normalizer_iff''.1 hn) v
  exact hVE (h.1 hv)

theorem mem_Hj_of_conj_mem_b
    (hF : J4Basic) {g x : J} (hx : x ∈ tSet) (hg : g⁻¹ * x * g ∈ Eg uJ 11) : g ∈ Hj := by
  have hM := hF.mat
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := Certificates.certificate4008.1 g
  set u := pathElt (repPaths.getD ℓ []) with hu
  have hx' : h⁻¹ * x * h ∈ tSet := (tSet_conj hM h hh).2 x hx
  have e : (h * u⁻¹ * h')⁻¹ * x * (h * u⁻¹ * h') = h'⁻¹ * (u * (h⁻¹ * x * h) * u⁻¹) * h' := by
    group
  rw [e] at hg
  have hg2 : u * (h⁻¹ * x * h) * u⁻¹ ∈ Eg uJ 11 := by
    have := Hj_normalizes_Eg hM h' hh' _ hg
    simpa [mul_assoc] using this
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have : u = 1 := by simp [hu, repPaths, pathElt]
    rw [this]
    simpa using Hj.mul_mem hh hh'
  · exact absurd hg2 (not_mem_Eg_conj hM (by omega) (by omega) hx')

theorem centralizer_le_Hj_of_T_b
    (hF : J4Basic) {c : ℕ} (hc : c ∈ tMasks) {x : J}
    (hx : x * eta uJ 11 c = eta uJ 11 c * x) : x ∈ Hj := by
  refine mem_Hj_of_conj_mem_b hF (x := eta uJ 11 c) ⟨c, hc, rfl⟩ ?_
  have : x⁻¹ * eta uJ 11 c * x = eta uJ 11 c := by
    rw [mul_assoc, ← hx, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [this]
  exact eta_mem_Eg 11 le_rfl c

theorem centralizer_eta_one_le_Hj_b
    (hF : J4Basic) {x : J} (hx : x * eta uJ 11 1 = eta uJ 11 1 * x) : x ∈ Hj :=
  centralizer_le_Hj_of_T_b hF one_mem_tMasks hx

theorem Dlt_five_card_b (hM : MatFacts) : (Dlt 5).ncard ≤ 15180 :=
  Dlt_card_le_of_vorb hM B7.orb5_ok (rep_toVec hM (by norm_num))

theorem dlt_filter_bound_b
    (hF : J4Basic) (ℓ : ℕ) {m dl : ℕ}
    (hm : (ZE' ℓ).card ≤ m) (hD : (Dlt ℓ).ncard ≤ dl) {z : J} (hz : z ∈ Zl) :
    1771 * {v | v ∈ Dlt ℓ ∧ RIn v z}.ncard ≤ dl * m := by
  have hM := hF.mat
  have hc := card_Zl hM
  have hm' : ∀ v ∈ Dlt ℓ, {x | x ∈ (↑Zl : Set J) ∧ RIn v x}.ncard ≤ m := by
    rintro v ⟨h, hh, rfl⟩
    have hmap : ∀ x ∈ {x | x ∈ (↑Zl : Set J) ∧ RIn (h • rep ℓ) x},
        (fun x => h⁻¹ * x * h) x ∈ (↑(ZE' ℓ) : Set J) := by
      rintro x ⟨hxZ, hxR⟩
      rw [Finset.mem_coe] at hxZ ⊢
      refine Finset.mem_filter.2 ⟨(Zl_conj hM h hh).2 x hxZ, ?_⟩
      have h1 : RIn (rep ℓ) (h⁻¹ * x * h) := by
        have := (RIn_conj h (rep ℓ) (h⁻¹ * x * h)).1
        rw [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this
        exact this hxR
      exact (RIn_rep_b hM hF.stab (rep_eq ℓ) _).1 h1
    have hinj : Set.InjOn (fun x => h⁻¹ * x * h) {x | x ∈ (↑Zl : Set J) ∧ RIn (h • rep ℓ) x} := by
      intro x _ y _ hxy
      simpa using hxy
    refine (Set.ncard_le_ncard_of_injOn _ hmap hinj (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact hm
  have hY : ∀ x ∈ (↑Zl : Set J), {p | p ∈ Dlt ℓ ∧ RIn p z}.ncard ≤
      {p | p ∈ Dlt ℓ ∧ RIn p x}.ncard := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := Zl_trans hM z hz x (Finset.mem_coe.1 hx)
    refine Set.ncard_le_ncard_of_injOn (fun v => k • v) ?_ ?_ (Set.toFinite _)
    · rintro v ⟨⟨h, hh, rfl⟩, hvR⟩
      refine ⟨⟨k * h, Hj.mul_mem hk hh, by rw [mul_smul]⟩, ?_⟩
      have := (RIn_conj k (h • rep ℓ) z).2 hvR
      rwa [hkx] at this
    · intro v _ v' _ hvv
      exact MulAction.injective k hvv
  have key := incidence_le_ncard (Dlt ℓ) (↑Zl : Set J) RIn m hm' z hY
  rw [Set.ncard_coe_finset, hc] at key
  exact key.trans (Nat.mul_le_mul_right _ hD)

theorem Omega_subset_b (hF : J4Basic) {z : J} :
    Omega z ⊆ {v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪ {v | v ∈ Dlt 2 ∧ RIn v z} ∪
      {v | v ∈ Dlt 3 ∧ RIn v z} ∪ {v | v ∈ Dlt 4 ∧ RIn v z} ∪ {v | v ∈ Dlt 5 ∧ RIn v z} ∪
      {v | v ∈ Dlt 6 ∧ RIn v z} := by
  have hM := hF.mat
  intro v hv
  obtain ⟨g, hg, hE⟩ := hv
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := Certificates.certificate4008.1 g
  have hvD : v ∈ Dlt ℓ := by
    refine ⟨h, hh, ?_⟩
    rw [← hg, mul_smul, mul_smul, smul_root_of_mem_Hj hM hh']
    rfl
  have hR : RIn v z := ⟨_, hg, hE⟩
  interval_cases ℓ
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hvD, hR⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨hvD, hR⟩))
  · exact Or.inl (Or.inr ⟨hvD, hR⟩)
  · exact Or.inr ⟨hvD, hR⟩

theorem card_Omega_le_b
    (hF : J4Basic) {z : J} (hz : z ∈ Zl) :
    (Omega z).ncard ≤ 77 := by
  have hM := hF.mat
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := cands_parts
  have hZ := card_Zl hM
  have b0 : {v | v ∈ Dlt 0 ∧ RIn v z}.ncard ≤ 1 := by
    have := dlt_filter_bound_b hF 0 (m := 1771) (dl := 1) (by
      rw [← hZ]; exact Finset.card_le_card (by unfold ZE'; exact Finset.filter_subset _ _))
      (Dlt_zero_card hM) hz
    omega
  have bz : ∀ ℓ, ℓ < 7 → (candZ (locMats ()) (locInvs ()) ℓ).length ≤ 0 →
      {v | v ∈ Dlt ℓ ∧ RIn v z}.ncard = 0 := by
    intro ℓ hℓ hc
    have := dlt_filter_bound_b hF ℓ (m := 0) (dl := (Dlt ℓ).ncard)
      (ZE'_card_le hM hℓ (pathInv_get hℓ) hc) le_rfl hz
    omega
  have b1 := bz 1 (by norm_num) c1.le
  have b2 := bz 2 (by norm_num) c2.le
  have b3 := bz 3 (by norm_num) c3.le
  have b4 := bz 4 (by norm_num) c4.le
  have b5 : {v | v ∈ Dlt 5 ∧ RIn v z}.ncard ≤ 60 := by
    have := dlt_filter_bound_b hF 5 (m := 7) (dl := 15180)
      (ZE'_card_le hM (by norm_num) (pathInv_get (by norm_num)) c5.le) (Dlt_five_card_b hM) hz
    omega
  have b6 : {v | v ∈ Dlt 6 ∧ RIn v z}.ncard ≤ 16 := by
    have := dlt_filter_bound_b hF 6 (m := 1) (dl := 28336)
      (ZE'_card_le hM (by norm_num) (pathInv_get (by norm_num)) c6.le)
      (Dlt_card_le_of_vorb hM orb6_ok (rep_toVec hM (by norm_num))) hz
    omega
  refine (Set.ncard_le_ncard (Omega_subset_b hF) (Set.toFinite _)).trans ?_
  refine (Set.ncard_union_le _ _).trans ?_
  have u1 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪
    {v | v ∈ Dlt 2 ∧ RIn v z} ∪ {v | v ∈ Dlt 3 ∧ RIn v z} ∪ {v | v ∈ Dlt 4 ∧ RIn v z})
    {v | v ∈ Dlt 5 ∧ RIn v z}
  have u2 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪
    {v | v ∈ Dlt 2 ∧ RIn v z} ∪ {v | v ∈ Dlt 3 ∧ RIn v z}) {v | v ∈ Dlt 4 ∧ RIn v z}
  have u3 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z} ∪
    {v | v ∈ Dlt 2 ∧ RIn v z}) {v | v ∈ Dlt 3 ∧ RIn v z}
  have u4 := Set.ncard_union_le ({v | v ∈ Dlt 0 ∧ RIn v z} ∪ {v | v ∈ Dlt 1 ∧ RIn v z})
    {v | v ∈ Dlt 2 ∧ RIn v z}
  have u5 := Set.ncard_union_le {v | v ∈ Dlt 0 ∧ RIn v z} {v | v ∈ Dlt 1 ∧ RIn v z}
  omega

theorem card_centralizer_Zl_b
    (hF : J4Basic) {z : J} (hz : z ∈ Zl)
    (h7 : 7 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set J)))
    (h11 : 11 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set J))) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set J)) = 21799895040 := by
  have hM := hF.mat
  have hKM := card_eq_orbit_mul_inf (Subgroup.centralizer ({z} : Set J)) Hj w₀
    (fun g => ⟨hF.stab g, smul_root_of_mem_Hj hM⟩)
  have hHM := card_eq_card_mul_centralizer Hj z Zl hz (fun h hh x hx => (Zl_conj hM h hh).1 x hx)
    (fun x hx => Zl_trans hM z hz x hx)
  rw [hF.cardHj, card_Zl hM] at hHM
  have hMval : Nat.card ↥(Subgroup.centralizer ({z} : Set J) ⊓ Hj) = 283115520 := by omega
  have hm77 : Nat.card ↥(MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀) ≤ 77 := by
    have hsub : MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀ ⊆ Omega z := by
      refine orbit_subset_of _ w₀ _ fun q hq => ?_
      refine ⟨q, rfl, ?_⟩
      have hc := comm_of_mem_centralizer hq
      have : q⁻¹ * z * q = z := by
        rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact mem_Eg_of_mem_Zl hz
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (card_Omega_le_b hF hz)
  have hmpos : 0 < Nat.card ↥(MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀) := by
    rw [Nat.card_coe_set_eq, Set.ncard_pos (Set.toFinite _)]
    exact ⟨w₀, MulAction.mem_orbit_self w₀⟩
  have hfin := final_arith _ hm77 hmpos (by rw [← hMval, ← hKM]; exact h7)
    (by rw [← hMval, ← hKM]; exact h11)
  rw [hKM, hMval, hfin]

theorem dvd_card_centralizer_of_b (hM : MatFacts) (w : List ℤ) {p : ℕ} (hp : p.Prime)
    (h : chkOrder (locMats ()) (locInvs ()) w p = true) :
    p ∣ Nat.card ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)) := by
  have h1 : chkCommRoot (locMats ()) (locInvs ()) w = true := by
    unfold chkOrder at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have hmem : mixElt w ∈ Subgroup.centralizer ({eta uJ 11 1131} : Set J) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mixElt_comm_notin hM w h1).1
  have := orderOf_dvd_natCard
    (⟨mixElt w, hmem⟩ : ↥(Subgroup.centralizer ({eta uJ 11 1131} : Set J)))
  rwa [Subgroup.orderOf_mk, orderOf_mixElt hM w hp h] at this

theorem card_centralizer_of_mem_Zl_b
    (hF : J4Basic) {x : J}
    (hx : x ∈ Zl) : Nat.card ↥(Subgroup.centralizer ({x} : Set J)) = 21799895040 := by
  have hM := hF.mat
  obtain ⟨h, -, e⟩ := Zl_trans hM _ z0_mem_Zl x hx
  rw [← e, card_centralizer_singleton_conj]
  exact card_centralizer_Zl_b hF z0_mem_Zl
    (dvd_card_centralizer_of_b hM y7Word (by norm_num) y7Word_check)
    (dvd_card_centralizer_of_b hM y11Word (by norm_num) y11Word_check)

end CFSG.Sporadic.J4.QT2

end
