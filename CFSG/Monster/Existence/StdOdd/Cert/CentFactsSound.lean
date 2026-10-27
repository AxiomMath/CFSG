module

public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts
public import CFSG.Monster.Existence.StdOdd.Cert.OrbitChain
public import CFSG.Monster.Existence.StdOdd.Cert.Orbit
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open Matrix CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint Subgroup


theorem smul_eq_rgrpMat (g : Rgrp)
    (v : Pt) : g • v = rgrpMat g *ᵥ v := rfl

theorem rhoC_eq (u w : Pt) :
    rhoC u w = if u = w then 0 else if formPt u w ≠ 0 then 4 else if brPt u w ≠ 0 then 3 else 5 := by
  rw [rhoC, formPt_eq, brPt_eq]
  rfl

theorem exists_of_monL {Ms : List M78} {S : Subgroup Rgrp}
    (hMs : ∀ M ∈ Ms, ∃ g ∈ S, rgrpMat g = M) {M : M78} (h : M ∈ monL Ms) :
    ∃ g ∈ S, rgrpMat g = M := by
  induction h using Submonoid.closure_induction with
  | mem M hM => exact hMs M hM
  | one => exact ⟨1, S.one_mem, map_one _⟩
  | mul M N _ _ hM hN =>
    obtain ⟨g, hg, rfl⟩ := hM
    obtain ⟨h, hh, rfl⟩ := hN
    exact ⟨g * h, S.mul_mem hg hh, map_mul _ _ _⟩

theorem rgrpMat_pow' (g : Rgrp) (n : ℕ) : rgrpMat (g ^ n) = rgrpMat g ^ n := map_pow _ _ _


theorem rhoC_smul (g : Rgrp)
    (u w : Pt) : rhoC (g • u) (g • w) = rhoC u w := by
  rw [rhoC_eq, rhoC_eq]
  simp only [(MulAction.injective g).eq_iff, formPt_smul, brPt_smul, ne_eq, smul_eq_zero_iff_eq]

theorem exists_of_monAB {M : M78} (h : M ∈ monAB) : ∃ g : Rgrp, rgrpMat g = M := by
  induction h using Submonoid.closure_induction with
  | mem M hM =>
    rcases hM with rfl | rfl
    · exact ⟨stdA, glMat_stdA⟩
    · exact ⟨stdB, glMat_stdB⟩
  | one => exact ⟨1, map_one _⟩
  | mul M N _ _ hM hN =>
    obtain ⟨g, rfl⟩ := hM
    obtain ⟨h, rfl⟩ := hN
    exact ⟨g * h, map_mul _ _ _⟩

open Classical in
theorem card_centralizer_of_centFacts
    {p N : ℕ} {xw d0 : List (ℕ × Bool)} {e : ℕ → ℕ} {K1 Kall : List (ℕ × ℕ)}
    (hx : orderOf (repOf xw) = p) (h : CentFacts p N xw d0 e K1 Kall) :
    Nat.card (centralizer ({repOf xw} : Set Rgrp)) = N := by
  obtain ⟨he0, helt, hcov, hfacts⟩ := h
  obtain ⟨reg, B, L, opts, H, sl, st, s, m₀, hregAB, hregFix, hB, hL, hLnd, hLcop, hprod,
    hroot, hcA, hcB, hb1, hball, hoinj, ⟨dep, hdep0, hdeps⟩, hPcard, hslprof, hslO, hslinj, hH, hHst,
    hm₀, hN, hrest⟩ := hfacts
  have hfin : Finite Rgrp := rgrp_finite
  set x : Rgrp := repOf xw with hxdef
  set b : Pt := repOf d0 • e7 with hbdef
  have hXm : rgrpMat x = wM xw := rgrpMat_repOf xw
  have hbv : b = wM d0 *ᵥ Pi.single 7 1 := by
    rw [hbdef, smul_eq_rgrpMat, rgrpMat_repOf]
    rfl
  have hxk : ∀ (k : ℕ) (v : Pt), x ^ k • v = wM xw ^ k *ᵥ v := by
    intro k v
    rw [smul_eq_rgrpMat, rgrpMat_pow', hXm]
  set β : ℕ → Pt := orbitBase x b e with hβ
  have hβv : ∀ i, β i = wM xw ^ e i *ᵥ (wM d0 *ᵥ Pi.single 7 1) := by
    intro i
    rw [hβ, orbitBase_apply, hxk, hbv]
  have hO : ∀ u ∈ rootOrbit, ∃ i < 3968055, opts i = u := by
    have hS : ∀ g : Rgrp, ∀ v ∈ {v : Pt | ∃ i < 3968055, opts i = v}, g • v ∈ {v | ∃ i < 3968055, opts i = v} :=
      smul_mem_of_gens closure_stdA_stdB
        (fun v ⟨i, hi, hv⟩ => by
          obtain ⟨j, hj, e⟩ := hcA i hi
          exact ⟨j, hj, by rw [e, ← hv, smul_eq_rgrpMat]; exact congrArg (· *ᵥ opts i) glMat_stdA.symm⟩)
        (fun v ⟨i, hi, hv⟩ => by
          obtain ⟨j, hj, e⟩ := hcB i hi
          exact ⟨j, hj, by rw [e, ← hv, smul_eq_rgrpMat]; exact congrArg (· *ᵥ opts i) glMat_stdB.symm⟩)
    rintro u ⟨g, rfl⟩
    obtain ⟨r, hr, hre⟩ := hroot
    exact hS g _ ⟨r, hr, hre⟩
  have hbO : b ∈ rootOrbit := ⟨repOf d0, rfl⟩
  have hoO : ∀ i < 3968055, opts i ∈ rootOrbit := by
    have sA : ∀ v, stdA • v = toMat nativeAB.1 *ᵥ v := fun v => by rw [smul_def, glMat_stdA]
    have sB : ∀ v, stdB • v = toMat nativeAB.2 *ᵥ v := fun v => by rw [smul_def, glMat_stdB]
    have key : ∀ m, ∀ i < 3968055, dep i = m → opts i ∈ rootOrbit := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i hi hd
        rcases Nat.eq_zero_or_pos (dep i) with h | h
        · rw [hdep0 i hi h]
          exact MulAction.mem_orbit_self _
        · obtain ⟨j, hj, hlt, e⟩ := hdeps i hi h
          have hjm := ih (dep j) (hd ▸ hlt) j hj rfl
          rcases e with e | e | e
          · rw [e, ← sA]
            exact (smul_mem_rootOrbit_iff stdA _).2 hjm
          · rw [e, ← sB]
            exact (smul_mem_rootOrbit_iff stdB _).2 hjm
          · rw [e, ← sB] at hjm
            exact (smul_mem_rootOrbit_iff stdB _).1 hjm
    exact fun i hi => key _ i hi rfl
  have hcompl : ∀ i < 3968055, (∀ q ∈ K1, rhoC (opts i) (wM xw ^ q.1 *ᵥ opts i) = q.2) →
      ∃ j < s, sl j = opts i := by
    set P := (Finset.range 3968055).filter fun i => ∀ q ∈ K1, rhoC (opts i) (wM xw ^ q.1 *ᵥ opts i) = q.2
    have hPinj : Set.InjOn opts P := fun a ha c hc e => by
      simp only [P, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hc
      exact hoinj a ha.1 c hc.1 e
    have hslinj' : Set.InjOn sl (Finset.range s) := fun a ha c hc e => by
      simp only [Finset.coe_range, Set.mem_Iio] at ha hc
      exact hslinj a ha c hc e
    have hsub : (Finset.range s).image sl ⊆ P.image opts := by
      intro u hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
      rw [Finset.mem_range] at hj
      obtain ⟨g, hg, hgs⟩ := hslO j hj
      obtain ⟨γ, rfl⟩ := exists_of_monAB hg
      have hγ : sl j = γ⁻¹ • b := by rw [eq_inv_smul_iff, smul_eq_rgrpMat, hgs, hbv]
      obtain ⟨i, hi, hie⟩ := hO (sl j) (by rw [hγ]; exact (smul_mem_rootOrbit_iff _ b).2 hbO)
      refine Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, ?_⟩, hie⟩
      rw [hie]
      exact hslprof j hj
    have heq : (Finset.range s).image sl = P.image opts :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hPinj, Finset.card_image_of_injOn hslinj',
          Finset.card_range, hPcard])
    intro i hi hq
    have : opts i ∈ P.image opts :=
      Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hq⟩, rfl⟩
    rw [← heq] at this
    obtain ⟨j, hj, e⟩ := Finset.mem_image.1 this
    exact ⟨j, Finset.mem_range.1 hj, e⟩
  set B' : ℕ → Finset Pt := fun i => if i = 0 then rootFinset else B i with hB'
  have hreg : ∀ i < p, ∀ M ∈ reg i, ∃ g ∈ baseStab (G := Rgrp) β i, rgrpMat g = M := by
    intro i hi M hM
    obtain ⟨g, rfl⟩ := exists_of_monAB (hregAB i M hM)
    refine ⟨g, mem_baseStab.2 fun j hj => ?_, rfl⟩
    rw [smul_eq_rgrpMat, hβv]
    exact hregFix i hi _ hM j hj
  choose! Lg hLg using fun M (hM : M ∈ L) => exists_of_monAB (hL M hM).1
  set L' : Finset Rgrp := (L.map Lg).toFinset with hL'
  have hLinj : (L.map Lg).Nodup := by
    refine (List.nodup_map_iff_inj_on hLnd).2 fun a ha c hc hac => ?_
    rw [← hLg a ha, ← hLg c hc, hac]
  have hL'card : L'.card = L.length := by
    rw [hL', List.toFinset_card_of_nodup hLinj, List.length_map]
  have hL'mem : ∀ k ∈ L', ∃ M ∈ L, Lg M = k := by
    intro k hk
    rw [hL', List.mem_toFinset, List.mem_map] at hk
    exact hk
  have hcR : Nat.card Rgrp = 76532479683774853939200 := card_stdGroup
  have hnc : rootOrbit.ncard = 3968055 :=
    ncard_of_facts (n := 3968055) glMat_stdA glMat_stdB closure_stdA_stdB hoinj hroot hcA hcB hdep0
      hdeps
  have hroots : rootFinset.card = 3968055 := by
    have hset : (↑rootFinset : Set Pt) = rootOrbit := by
      ext u
      simp [mem_rootFinset]
    exact (Set.ncard_coe_finset rootFinset).symm.trans ((congrArg Set.ncard hset).trans hnc)
  have hchain : IsStabChain β p B' (choiceT β) L' := by
    refine IsStabChain.of_exists (fun i hi y hy => ?_) (fun k hk => ?_) ?_
    · by_cases h0 : i = 0
      · subst h0
        simp only [hB', ite_true, mem_rootFinset] at hy
        obtain ⟨g, rfl⟩ := hy
        refine ⟨g * (repOf d0)⁻¹, by rw [baseStab_zero]; exact Subgroup.mem_top _, ?_⟩
        rw [hβ, orbitBase_apply, he0, pow_zero, one_smul, hbdef, ← mul_smul, inv_mul_cancel_right]
      · simp only [hB', h0, ite_false] at hy
        obtain ⟨g, hg, hgy⟩ := hB i (by omega) hi y hy
        obtain ⟨k, hk, rfl⟩ := exists_of_monL (hreg i hi) hg
        refine ⟨k⁻¹, (baseStab β i).inv_mem hk, ?_⟩
        rw [inv_smul_eq_iff, smul_eq_rgrpMat, hgy, hβv]
    · obtain ⟨M, hM, rfl⟩ := hL'mem k hk
      refine mem_baseStab.2 fun j hj => ?_
      rw [smul_eq_rgrpMat, hLg M hM, hβv]
      exact (hL M hM).2.2 j hj
    · have hp0 : 0 < p := by
        rw [← hx]
        exact orderOf_pos _
      have hsplit : Finset.range p = insert 0 (Finset.Ico 1 p) := by
        ext i
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
        omega
      have h0 : (B' 0).card = 3968055 := by simp only [hB', ite_true]; exact hroots
      have hI : ∏ i ∈ Finset.Ico 1 p, (B' i).card = ∏ i ∈ Finset.Ico 1 p, (B i).card :=
        Finset.prod_congr rfl fun i hi => by
          rw [Finset.mem_Ico] at hi
          simp only [hB', show i ≠ 0 by omega, ite_false]
      rw [hsplit, Finset.prod_insert (by simp), hL'card, hcR, h0, hI, ← hprod, Nat.mul_assoc]
  have hcover : ∀ j < orderOf x, ∃ i < p, x ^ e i = x ^ j := by
    intro j hj
    rw [hx] at hj
    obtain ⟨i, hi, hij⟩ := hcov j hj
    exact ⟨i, hi, by rw [hij]⟩
  have hcomm : ∀ κ ∈ L', κ * x = x * κ := by
    intro κ hκ
    obtain ⟨M, hM, rfl⟩ := hL'mem κ hκ
    apply rgrpMat_injective
    rw [map_mul, map_mul, hLg M hM, hXm]
    exact (hL M hM).2.1
  have hcop : Nat.Coprime L'.card (orderOf x) := by
    rw [hL'card, hx]
    exact hLcop
  have hprof : ∀ c ∈ centralizer ({x} : Set Rgrp), ∀ q : ℕ × ℕ,
      rhoC (c • b) (wM xw ^ q.1 *ᵥ (c • b)) = rhoC b (wM xw ^ q.1 *ᵥ b) := by
    intro c hc q
    rw [← hxk, ← smul_pow_smul_of_mem_centralizer hc, rhoC_smul, hxk]
  have hHC : ∀ M ∈ H, ∃ g ∈ centralizer ({x} : Set Rgrp), rgrpMat g = M := by
    intro M hM
    obtain ⟨g, rfl⟩ := exists_of_monAB (hH M hM).1
    refine ⟨g, mem_centralizer_singleton_iff.2 ?_, rfl⟩
    apply rgrpMat_injective
    rw [map_mul, map_mul, hXm]
    exact (hH _ hM).2
  set S : Finset Pt := (Finset.range s).image sl with hSdef
  set Ob : Finset Pt := ((Finset.range s).filter fun j => st j = b).image sl with hObdef
  have hS : ∀ c ∈ centralizer ({x} : Set Rgrp), c • b ∈ S := by
    intro c hc
    have hcb : c • b ∈ rootOrbit := (smul_mem_rootOrbit_iff c b).2 hbO
    obtain ⟨i, hi, hie⟩ := hO _ hcb
    obtain ⟨j, hj, hje⟩ := hcompl i hi (fun q hq => by
      rw [hie, hprof c hc q, hbv]
      exact hb1 q hq)
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, by rw [hje, hie]⟩
  have hOb : ∀ u ∈ Ob, ∃ c ∈ centralizer ({x} : Set Rgrp), c • b = u := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨g, hg, hgs⟩ := hHst j hj.1
    obtain ⟨c, hc, rfl⟩ := exists_of_monL hHC hg
    refine ⟨c⁻¹, (centralizer _).inv_mem hc, ?_⟩
    rw [inv_smul_eq_iff, ← hj.2, smul_eq_rgrpMat, hgs]
  have hrest' : ∀ u ∈ S, u ∉ Ob → ¬ ∃ c ∈ centralizer ({x} : Set Rgrp), c • b = u := by
    intro u hu hnu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
    rw [Finset.mem_range] at hj
    have hstj : st j ≠ b := fun e => hnu (Finset.mem_image.2
      ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, e⟩, rfl⟩)
    rintro ⟨c, hc, hcb⟩
    rcases hrest j hj (by rw [← hbv]; exact hstj) with ⟨q, hq, hne⟩ | ⟨g, hg, hgb, m, t, f, hm1, hmp,
      ht1, ht0, hf, hfail⟩
    · apply hne
      rw [← hcb, hprof c hc q, hbv]
      exact hball q hq
    · obtain ⟨γ, rfl⟩ := exists_of_monAB hg
      have hγ : γ⁻¹ • b = st j := by
        rw [inv_smul_eq_iff, smul_eq_rgrpMat, hbv, hgb]
      obtain ⟨h', hh', hh's⟩ := hHst j hj
      obtain ⟨ch, hch, rfl⟩ := exists_of_monL hHC hh'
      apply not_mem_orbit_of_fail (x := x) (e := e) (n := p) γ⁻¹ hγ
      · refine fun hk => not_exists_of_fail hchain hm1 hmp t (fun j => ?_) ?_ (fun j hj1 hjm => ?_)
          (fun j hj1 hjm i hi => ?_) ?_ (hk.imp fun k hk i hi => ?_)
        · exact if h : ∃ φ ∈ baseStab (G := Rgrp) β j, rgrpMat φ = f j then h.choose⁻¹ else 1
        · rw [ht0, hβv]
        · obtain ⟨hfm, -, -⟩ := hf j hj1 hjm
          have hex := exists_of_monL (hreg j (by omega)) hfm
          simp only [dite_eq_left hex]
          refine ⟨(baseStab β j).inv_mem hex.choose_spec.1, ?_⟩
          rw [inv_smul_eq_iff, smul_eq_rgrpMat, hex.choose_spec.2, (hf j hj1 hjm).2.1, hβv]
        · obtain ⟨hfm, -, hft⟩ := hf j hj1 hjm
          have hex := exists_of_monL (hreg j (by omega)) hfm
          simp only [dite_eq_left hex, inv_inv]
          rw [hft i hi, smul_eq_rgrpMat, hex.choose_spec.2]
        · simpa [hB', show m ≠ 0 by omega] using hfail
        · rw [hk i hi, ht1 i hi, inv_inv, hxk, smul_eq_rgrpMat]
      · refine ⟨ch * c, (centralizer _).mul_mem hch hc, ?_⟩
        rw [mul_smul, hcb, smul_eq_rgrpMat, hh's]
  have hmain := card_centralizer_of_orbits hchain hcover hcomm hcop S Ob hS hOb hrest'
  rw [hmain, hL'card, hN, ← hm₀, hObdef, Finset.card_image_of_injOn (fun a ha c hc hac => by
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hc
    exact hslinj a ha.1 c hc.1 hac), hbv]

end CFSG.Monster.Existence.StdOdd.Cert

end
