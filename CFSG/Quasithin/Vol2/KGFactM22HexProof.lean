module

public import CFSG.Quasithin.Vol2.KGFactM22Hex
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22
public import CFSG.Quasithin.Vol2.KGFact1262

public section

namespace CFSG.Quasithin.H13.S126M22

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  PermLat CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Certificates
  CFSG.ComponentClassification.OuterAutomorphisms

theorem l6_le_M : Subgroup.closure {g | g ∈ l6Gens} ≤ Mgrp := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, l6Gens_eq, List.mem_pair] at hg
  rcases hg with rfl | rfl
  · rw [Equiv.ext g0_eq]; exact evalW_mem_closure _ _
  · rw [Equiv.ext g1_eq]; exact evalW_mem_closure _ _

abbrev L6 : Subgroup ↥Mgrp := (Subgroup.closure {g | g ∈ l6Gens}).subgroupOf Mgrp

theorem exists_conj_eq_l6 (B : Subgroup ↥Mgrp)
    (hB : Nat.card ↥B = 5760) : ∃ g : ↥Mgrp, B.map (MulAut.conj g).toMonoidHom = L6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hMc : Nat.card ↥Mgrp = 443520 := cert.card_m (rawIsEnc 22) hcl hsz
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf Ugrp ⊤ :=
    cert.isSylowTwoOf_top (rawIsEnc 22) hck (k := 7) (m := 3465) (by decide) (by decide)
      (by omega)
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := ↥B) (n := 7)
    (by rw [hB]; norm_num)
  have hPc : Nat.card ↥(P₀.map B.subtype) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hP₀]
  have hPs : CFSG.QuasithinUnique.IsSylowTwoOf (P₀.map B.subtype) ⊤ :=
    isSylowTwoOf_top_of_card hPc (m := 3465) (by rw [hMc]; norm_num) (by decide)
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hPs hU
  refine ⟨g, ?_⟩
  have hcgi : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hUB : Ugrp ≤ B.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.map_mono (Subgroup.map_subtype_le P₀)
  have hB₁ : Nat.card ↥(B.map (MulAut.conj g).toMonoidHom) = 5760 := by
    rw [Subgroup.card_map_of_injective hcgi, hB]
  obtain ⟨j, hj, hLM, hBL, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck _ hUB
  have hs : cert.sizes = [128, 384, 1920, 5760, 443520, 384] := rfl
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  have hj6 : j < 6 := hlen ▸ hj
  have hcj : cert.sizes.getD j 0 = 5760 := by
    rw [← hcardj, ← hB₁, hBL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
  rw [hs] at hcj
  have hj3 : j = 3 := by
    interval_cases j <;> first | rfl | exact absurd hcj (by decide)
  subst hj3
  have ha := List.all_eq_true.mp incl6 3 (by simp)
  have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
  simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
  have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
  have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
  have hAL : Subgroup.closure {g | g ∈ l6Gens} ≤
      Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} := by
    rw [Subgroup.closure_le]
    intro x hx
    have := List.all_eq_true.mp ha x hx
    rw [List.getD_eq_getElem _ _ hlen3] at this
    exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
      (cert.members_closed hcl _ hmem) x).mpr (Std.HashSet.contains_iff_mem.mp this)
  obtain ⟨hAcard, -⟩ := ext6
  have hLA := Subgroup.eq_of_le_of_card_ge hAL (by rw [hcardj, hAcard]; exact h5760.le)
  rw [hBL, ← hLA]

theorem E0_le_of_normal (E : Subgroup ↥Mgrp)
    (hE : Nat.card ↥E = 16) (hEL : E ≤ L6)
    (hLN : L6 ≤ Subgroup.normalizer (E : Set ↥Mgrp)) :
    ∀ a ∈ E0, ∀ haM : a ∈ Mgrp, (⟨a, haM⟩ : ↥Mgrp) ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, V, hVn, -, -, hVcard, ⟨e6⟩⟩ := ext6
  have hEY : E.map Mgrp.subtype ≤ Subgroup.closure {g | g ∈ l6Gens} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hEL hx
  set EY : Subgroup ↥(Subgroup.closure {g | g ∈ l6Gens}) :=
    (E.map Mgrp.subtype).subgroupOf (Subgroup.closure {g | g ∈ l6Gens}) with hEYdef
  have hEYc : Nat.card ↥EY = 2 ^ 4 := by
    rw [hEYdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv,
      Subgroup.card_map_of_injective Mgrp.subtype_injective, hE]
    norm_num
  have hEYn : EY.Normal := by
    refine ⟨fun z hz y => ?_⟩
    obtain ⟨x, hx, hxz⟩ := hz
    have hyM : (y : Perm (Fin 22)) ∈ Mgrp := l6_le_M y.2
    have hyB : (⟨y, hyM⟩ : ↥Mgrp) ∈ L6 := y.2
    have h1 := (Subgroup.mem_normalizer_iff.1 (hLN hyB) x).1 hx
    refine ⟨_, h1, ?_⟩
    have hxz' : ((x : ↥Mgrp) : Perm (Fin 22)) = ((z : ↥(Subgroup.closure {g | g ∈ l6Gens})) :
      Perm (Fin 22)) := hxz
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hxz']
  have hEV : EY ≤ V := le_of_normal_of_quot e6 hEYn (Or.inl (IsPGroup.of_card hEYc))
  have hEV' : EY = V := Subgroup.eq_of_le_of_card_ge hEV (by rw [hVcard, hEYc])
  set E₀Y : Subgroup ↥(Subgroup.closure {g | g ∈ l6Gens}) :=
    E0.subgroupOf (Subgroup.closure {g | g ∈ l6Gens}) with hE₀Ydef
  have hE₀Yn : E₀Y.Normal :=
    ⟨fun z hz y => (Subgroup.mem_normalizer_iff.1 (l6_le_normalizer y.2) z).1 hz⟩
  have hE₀V : E₀Y ≤ V := le_of_normal_of_quot e6 hE₀Yn
    (Or.inr fun a ha b hb => Subtype.ext (E0_comm _ ha _ hb))
  intro a ha haM
  have h1 : (⟨a, E0_le ha⟩ : ↥(Subgroup.closure {g | g ∈ l6Gens})) ∈ V := hE₀V ha
  rw [← hEV'] at h1
  obtain ⟨x, hx, hxa⟩ := h1
  rwa [show x = ⟨a, haM⟩ from Subtype.ext hxa] at hx

theorem exists_eq_conj_E0 (δ : Perm (Fin 22))
    (hδ : ∀ h ∈ Mgrp, δ * h * δ⁻¹ ∈ Mgrp) (hδ2 : δ * δ ∈ Mgrp)
    (hcenter : Subgroup.center ↥Mgrp = ⊥)
    (houter : ∀ g ∈ Mgrp, ¬∀ h ∈ Mgrp, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut ↥Mgrp) ≤ 2 * Nat.card ↥Mgrp) (reps : List (Perm (Fin 22)))
    (hcov : ∀ u, δ⁻¹ * u ∈ Mgrp → orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ Mgrp, u = c * r * c⁻¹)
    (hreps : ∀ r ∈ reps, (Finset.univ.filter fun x => r x = x).card < 16)
    (hbase : ∀ g ∈ Mgrp, (∀ x : Fin 22, x.val < 5 → g x = x) → g = 1) (hA : m22gA ∈ Mgrp)
    (α : MulAut ↥Mgrp) (hα : ∀ a ∈ E0, ∀ haM : a ∈ Mgrp, α ⟨a, haM⟩ = ⟨a, haM⟩) :
    ∃ s ∈ E0, ∀ h : ↥Mgrp, ((α h : ↥Mgrp) : Perm (Fin 22)) = s * h * s⁻¹ := by
  have hbase' : ∀ g ∈ Mgrp, (∀ x : Fin 22, x ∉ hexL → g x = x) → g = 1 := by
    intro g hg hfix
    have h1 : m22gA * g * m22gA⁻¹ = 1 :=
      hbase _ (Mgrp.mul_mem (Mgrp.mul_mem hA hg) (Mgrp.inv_mem hA)) fun x hx => by
        rw [Perm.mul_apply, Perm.mul_apply, hfix _ (base_out x hx)]
        simp
    calc g = m22gA⁻¹ * (m22gA * g * m22gA⁻¹) * m22gA := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨k, hkM, hkα⟩ : ∃ k : Perm (Fin 22), (k ∈ Mgrp ∨ δ⁻¹ * k ∈ Mgrp) ∧
      ∀ h : ↥Mgrp, ((α h : ↥Mgrp) : Perm (Fin 22)) = k * h * k⁻¹ := by
    by_cases hin : α ∈ inner ↥Mgrp
    · obtain ⟨n, hn⟩ := hin
      exact ⟨n, Or.inl n.2, fun h => by rw [← hn]; rfl⟩
    · obtain ⟨g', hg', hα'⟩ := exists_eq_conj_of_outer Mgrp δ hδ hδ2 hcenter houter hcard α hin
      refine ⟨g' * δ, Or.inr ?_, hα'⟩
      rw [← mul_assoc]
      exact inv_conj_mem Mgrp hδ hδ2 _ hg'
  have hk : ∀ a ∈ eL, k * a = a * k := by
    intro a ha
    have haE : a ∈ E0 := Subgroup.subset_closure ha
    have haM : a ∈ Mgrp := l6_le_M (E0_le haE)
    have h1 := hkα ⟨a, haM⟩
    rw [hα a haE haM] at h1
    calc k * a = k * a * k⁻¹ * k := by group
      _ = a * k := by rw [← h1]
  obtain ⟨s, hs, hsk⟩ := exists_span_fix hk
  have hsE : s ∈ E0 := spanOf_mem_E0 s hs
  have hsM : s ∈ Mgrp := l6_le_M (E0_le hsE)
  rcases hkM with hkM | hkM
  · have hm1 : s⁻¹ * k = 1 := hbase' _ (Mgrp.mul_mem (Mgrp.inv_mem hsM) hkM) hsk
    have hks : k = s := by
      calc k = s * (s⁻¹ * k) := by group
        _ = s := by rw [hm1, mul_one]
    exact ⟨s, hsE, fun h => by rw [hkα h, hks]⟩
  · exfalso
    set m := s⁻¹ * k with hmdef
    have hm' : δ⁻¹ * m ∈ Mgrp := by
      have e : δ⁻¹ * m = (δ⁻¹ * s⁻¹ * δ) * (δ⁻¹ * k) := by rw [hmdef]; group
      rw [e]
      exact Mgrp.mul_mem (inv_conj_mem Mgrp hδ hδ2 _ (Mgrp.inv_mem hsM)) hkM
    have hmm : m * m ∈ Mgrp := by
      have e : m * m = (δ * (δ⁻¹ * m) * δ⁻¹) * (δ * δ) * (δ⁻¹ * m) := by group
      rw [e]
      exact Mgrp.mul_mem (Mgrp.mul_mem (hδ _ hm') hδ2) hm'
    have hmm1 : m * m = 1 := hbase' _ hmm fun x hx => by
      rw [Perm.mul_apply, hsk x hx, hsk x hx]
    have hm1 : m ≠ 1 := by
      intro h
      rw [h, mul_one] at hm'
      exact houter _ hm' fun h _ => by group
    have hord : orderOf m = 2 := orderOf_eq_prime (by rw [sq]; exact hmm1) hm1
    obtain ⟨r, hr, c, -, hmr⟩ := hcov m hm' hord
    have hfix : ∀ x : Fin 22, x ∉ hexL → r (c⁻¹ x) = c⁻¹ x := by
      intro x hx
      have h1 : m x = x := hsk x hx
      rw [hmr, Perm.mul_apply, Perm.mul_apply] at h1
      calc r (c⁻¹ x) = c⁻¹ (c (r (c⁻¹ x))) := by simp
        _ = c⁻¹ x := by rw [h1]
    have h16 : 16 ≤ (Finset.univ.filter fun x => r x = x).card := by
      rw [← card_compl_hexL]
      refine Finset.card_le_card_of_injOn (fun x => c⁻¹ x) (fun x hx => ?_)
        (fun x _ y _ h => c⁻¹.injective h)
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      exact hfix x hx
    have := hreps r hr
    omega

theorem core (N : Subgroup (Perm (Fin 22)))
    (hN : Subgroup.closure {g | g ∈ cert.mGens} = N) (δ : Perm (Fin 22))
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center ↥N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut ↥N) ≤ 2 * Nat.card ↥N) (reps : List (Perm (Fin 22)))
    (hcov : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ N, u = c * r * c⁻¹)
    (hreps : ∀ r ∈ reps, (Finset.univ.filter fun x => r x = x).card < 16)
    (hbase : ∀ g ∈ N, (∀ x : Fin 22, x.val < 5 → g x = x) → g = 1) (hA : m22gA ∈ N)
    (B E : Subgroup ↥N) (hB : Nat.card ↥B = 5760) (hEB : E ≤ B)
    (hBN : B ≤ Subgroup.normalizer (E : Set ↥N)) (hE : Nat.card ↥E = 16) (α : MulAut ↥N)
    (hα : ∀ e ∈ E, α e = e) : ∃ e ∈ E, α = MulAut.conj e := by
  subst hN
  obtain ⟨g, hg⟩ := exists_conj_eq_l6 B hB
  set cg := MulAut.conj g with hcg
  have hcgi : Function.Injective cg.toMonoidHom := cg.injective
  have hE₁ : Nat.card ↥(E.map cg.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective hcgi, hE]
  have hE₁L : E.map cg.toMonoidHom ≤ L6 := hg ▸ Subgroup.map_mono hEB
  have hLN : L6 ≤ Subgroup.normalizer ((E.map cg.toMonoidHom : Subgroup ↥Mgrp) : Set ↥Mgrp) :=
    hg ▸ (Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map _)
  have hE0E₁ := E0_le_of_normal _ hE₁ hE₁L hLN
  set α₁ : MulAut ↥Mgrp := cg * α * cg⁻¹ with hα₁def
  have hcc : ∀ h : ↥Mgrp, cg⁻¹ (cg h) = h := fun h => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hα₁ : ∀ a ∈ E0, ∀ haM : a ∈ Mgrp, α₁ ⟨a, haM⟩ = ⟨a, haM⟩ := by
    intro a ha haM
    obtain ⟨e, he, hea⟩ := hE0E₁ a ha haM
    rw [← hea]
    simp only [hα₁def, MulAut.mul_apply, MulEquiv.coe_toMonoidHom]
    rw [hcc, hα e he]
  obtain ⟨s, hsE, hsα⟩ := exists_eq_conj_E0 δ hδ hδ2 hcenter houter hcard reps hcov hreps hbase hA
    α₁ hα₁
  have hsM : s ∈ Mgrp := l6_le_M (E0_le hsE)
  obtain ⟨e₀, he₀, he₀s⟩ := hE0E₁ s hsE hsM
  refine ⟨e₀, he₀, MulEquiv.ext fun h => ?_⟩
  have h1 := hsα (cg h)
  have h2 : α₁ (cg h) = cg (α h) := by
    simp only [hα₁def, MulAut.mul_apply]
    rw [hcc]
  rw [h2] at h1
  have hs' : s = (g : Perm (Fin 22)) * e₀ * (g : Perm (Fin 22))⁻¹ := by
    have := congrArg Subtype.val he₀s
    simp only [MulEquiv.coe_toMonoidHom, hcg, MulAut.conj_apply, Subgroup.coe_mul,
      InvMemClass.coe_inv] at this
    exact this.symm
  simp only [hcg, MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at h1
  apply Subtype.ext
  simp only [MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [hs'] at h1
  calc ((α h : ↥Mgrp) : Perm (Fin 22)) =
      (g : Perm (Fin 22))⁻¹ * ((g : Perm (Fin 22)) * (α h : ↥Mgrp) * (g : Perm (Fin 22))⁻¹) *
        (g : Perm (Fin 22)) := by group
    _ = (g : Perm (Fin 22))⁻¹ * ((g : Perm (Fin 22)) * e₀ * (g : Perm (Fin 22))⁻¹ *
        ((g : Perm (Fin 22)) * h * (g : Perm (Fin 22))⁻¹) *
        ((g : Perm (Fin 22)) * e₀ * (g : Perm (Fin 22))⁻¹)⁻¹) * (g : Perm (Fin 22)) := by
      rw [h1]
    _ = (e₀ : Perm (Fin 22)) * h * (e₀ : Perm (Fin 22))⁻¹ := by group

theorem factM22HexadAut_holds :
    FactM22HexadAut := by
  intro X _ _ ⟨eX⟩ B E hB hEB hBN hE α hα
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  have hcov : ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
      ∃ r ∈ [m22OutRep1, m22OutRep2], ∃ c ∈ NativeSporadic.M22, u = c * r * c⁻¹ := by
    obtain ⟨hok, -, -⟩ := m22_outer_cover
    rw [m22OutReps_eq] at hok
    obtain ⟨hr1, hro1, -⟩ := m22_out_rep_data1
    obtain ⟨hr2, hro2, -⟩ := m22_out_rep_data2
    have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
    have hB' : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
    have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
        m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
      rw [m22Certificate_originalSubgroup]
      exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
    obtain ⟨h, -⟩ := exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB')
      m22Delta hg₀ (m := 2) (by norm_num) [m22OutRep1, m22OutRep2] (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨hr1, hro1⟩
        · exact ⟨hr2, hro2⟩) 2000 hok
    rw [m22Certificate_originalSubgroup] at h
    exact h
  have hbase : ∀ g ∈ NativeSporadic.M22, (∀ x : Fin 22, x.val < 5 → g x = x) → g = 1 := by
    intro g hg hfix
    obtain ⟨hlev, hbot, -⟩ := m22Certificate.schreier_chain_order hQ
    have hmem : g ∈ m22Certificate.levelSubgroup m22Certificate.baseCount := by
      rw [hlev _ le_rfl, Subgroup.mem_inf, m22Certificate_originalSubgroup]
      refine ⟨hg, ?_⟩
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have h5 : ∀ y ∈ m22Certificate.base.toList.take m22Certificate.baseCount, y.val < 5 := by
        decide
      exact hfix y (h5 y hy)
    rw [hbot] at hmem
    exact hmem
  have hreps : ∀ r ∈ [m22OutRep1, m22OutRep2],
      (Finset.univ.filter fun x => r x = x).card < 16 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fix_outRep1
    · exact fix_outRep2
  have key := core NativeSporadic.M22 mGens_closure m22Delta m22_delta_normalizes m22_delta_sq
    m22_center_eq_bot' m22_delta_outer m22_mulAut_card _ hcov hreps hbase m22a.2
  set α' : MulAut ↥NativeSporadic.M22 := (eX.symm.trans α).trans eX with hα'
  have hinj : Function.Injective eX.toMonoidHom := eX.injective
  obtain ⟨e', he', hαe⟩ := key (B.map eX.toMonoidHom) (E.map eX.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective hinj, hB]) (Subgroup.map_mono hEB)
    ((Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map _))
    (by rw [Subgroup.card_map_of_injective hinj, hE]) α' (by
      rintro _ ⟨e, he, rfl⟩
      simp only [hα', MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hα e he])
  obtain ⟨e₀, he₀, rfl⟩ := he'
  refine ⟨e₀, he₀, MulEquiv.ext fun x => eX.injective ?_⟩
  have h1 := congrArg (fun f : MulAut ↥NativeSporadic.M22 => f (eX x)) hαe
  simp only [hα', MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply,
    MulEquiv.coe_toMonoidHom] at h1
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.Quasithin.H13.S126M22
