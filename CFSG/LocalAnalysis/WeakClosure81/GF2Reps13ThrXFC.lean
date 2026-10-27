module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXFB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX.isPGroup
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem w16g_stableUnder_zpowers {t : MulAut W} {U : Subgroup W} (htt : t * t = 1)
    (hUt : ∀ u ∈ U, t u ∈ U) : StableUnder (Subgroup.zpowers t) U := by
  have ht_stab : t ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun htu => by
      have h := hUt (t u) htu
      rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h,
      hUt u⟩
  intro x hx u hu
  exact (mem_stabSub.1 (Subgroup.zpowers_le.2 ht_stab hx) u).2 hu

private theorem w16g_disjoint_sup_sdiff (hW : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) {S : Set (Subgroup W)} (hS : S ⊆ s13IsoComps X) :
    Disjoint (⨆ U ∈ S, U) (⨆ U ∈ s13IsoComps X \ S, U) := by
  classical
  have hind : sSupIndep (s13IsoComps X) := s13IsoComps_sSupIndep hW hX
  rw [sSupIndep_iff] at hind
  let s₁ : Set (s13IsoComps X) := {V | (V : Subgroup W) ∈ S}
  let t₁ : Set (s13IsoComps X) := {V | (V : Subgroup W) ∈ s13IsoComps X \ S}
  have hdisj : Disjoint s₁ t₁ := by
    rw [Set.disjoint_left]
    intro V hV1 hV2
    exact hV2.2 hV1
  have h := hind.disjoint_biSup_biSup' hdisj (Set.toFinite s₁)
  have hA : (⨆ V ∈ s₁, (V : Subgroup W)) = ⨆ U ∈ S, U := by
    apply le_antisymm
    · refine iSup_le fun V => iSup_le fun hV => ?_
      exact le_iSup₂ (f := fun U (_ : U ∈ S) => U) (V : Subgroup W) hV
    · refine iSup_le fun U => iSup_le fun hU => ?_
      exact le_iSup₂ (f := fun V (_ : V ∈ s₁) => (V : Subgroup W)) ⟨U, hS hU⟩ hU
  have hB : (⨆ V ∈ t₁, (V : Subgroup W)) = ⨆ U ∈ s13IsoComps X \ S, U := by
    apply le_antisymm
    · refine iSup_le fun V => iSup_le fun hV => ?_
      exact le_iSup₂ (f := fun U (_ : U ∈ s13IsoComps X \ S) => U) (V : Subgroup W) hV
    · refine iSup_le fun U => iSup_le fun hU => ?_
      exact le_iSup₂ (f := fun V (_ : V ∈ t₁) => (V : Subgroup W)) ⟨U, hU.1⟩ hU
  simpa only [hA, hB] using h

private theorem w16g_two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : p ∣ 2 := by
    have h' : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact h
    rwa [ZMod.natCast_eq_zero_iff] at h'
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have h2p : 2 ≤ p := hp.two_le
  omega

private theorem w16g_ncard_one_disjoint_or_eq {α : Type*} {s t : Set α}
    (hs : s.ncard = 1) (ht : t.ncard = 1) : s = t ∨ Disjoint s t := by
  obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp hs
  obtain ⟨b, rfl⟩ := Set.ncard_eq_one.mp ht
  by_cases hab : a = b
  · exact Or.inl (by rw [hab])
  · right
    rwa [Set.disjoint_singleton]

theorem saturation (h : HAb A X Q t p) {a : MulAut W} (ha : a ∈ A)
    (hcost : rk ↥(commSub (commSub ⊤ (Q.map (MulAut.conj a).toMonoidHom))
      (Subgroup.zpowers (a * t * a⁻¹))) = 3) :
    (∀ U ∈ s13IsoComps X, U ∉ s13Supp X (Q.map (MulAut.conj a).toMonoidHom) →
      commSub U (Subgroup.zpowers (a * t * a⁻¹)) = ⊥) ∧
      commSub (fixV X) (Subgroup.zpowers (a * t * a⁻¹)) = ⊥ := by
  classical
  set s : MulAut W := a * t * a⁻¹ with hs
  set Q' : Subgroup (MulAut W) := Q.map (MulAut.conj a).toMonoidHom with hQ'
  have hcost' : rk ↥(commSub (commSub ⊤ Q') (Subgroup.zpowers s)) = 3 := by
    rw [hQ', hs]; exact hcost
  have h' : HAb A X Q' s p := by rw [hQ', hs]; exact h.conj ha
  have hp : p.Prime := by
    rcases h.hp with h3 | h7
    · rw [h3]; norm_num
    · rw [h7]; norm_num
  have hp2 : p ≠ 2 := by
    rcases h.hp with h3 | h7
    · rw [h3]; norm_num
    · rw [h7]; norm_num
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 h.hXe
  have hs2 : s * s = 1 := by have := h'.ht2; rwa [pow_two] at this
  have hsA : s ∈ A := by rw [hs]; exact A.mul_mem (A.mul_mem ha h.htA) (A.inv_mem ha)
  have hgs : ∀ x ∈ X, s * x * s⁻¹ ∈ X := fun x hx => h.hXA s hsA x hx
  have hgs' : ∀ x ∈ X, s⁻¹ * x * s ∈ X := by
    intro x hx
    simpa using h.hXA s⁻¹ (A.inv_mem hsA) x hx
  have hQ'stab : Q'.map (MulAut.conj s).toMonoidHom = Q' := by
    apply le_antisymm
    · intro x hx
      rw [hQ'] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨q⁻¹, Q.inv_mem hq, ?_⟩
      show MulAut.conj a q⁻¹ = s * (a * q * a⁻¹) * s⁻¹
      rw [show s * (a * q * a⁻¹) * s⁻¹ = a * (t * q * t⁻¹) * a⁻¹ by rw [hs]; group,
        h.hQinv q hq]
      simp [MulAut.conj_apply]
    · intro x hx
      rw [hQ'] at hx ⊢
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_map.mpr ⟨a * q⁻¹ * a⁻¹, Subgroup.mem_map.mpr
        ⟨q⁻¹, Q.inv_mem hq, rfl⟩, ?_⟩
      show MulAut.conj s (a * q⁻¹ * a⁻¹) = MulAut.conj a q
      rw [MulAut.conj_apply, MulAut.conj_apply,
        show s * (a * q⁻¹ * a⁻¹) * s⁻¹ = a * (t * q⁻¹ * t⁻¹) * a⁻¹ by rw [hs]; group,
        h.hQinv q⁻¹ (Q.inv_mem hq), inv_inv]
  have hfixcomm : fixV X ⊓ commSub ⊤ X = ⊥ := by
    have hc := (isCompl_fixV_commV_of_odd X hodd
      (fun w => by rw [pow_two]; exact h.hW w)).inf_eq_bot
    rwa [commV_eq_commSub] at hc
  set B : Subgroup W := commSub ⊤ Q' with hBdef
  have hBs : ∀ u ∈ B, s u ∈ B := by
    rw [hBdef]
    have hmap : (commSub ⊤ Q').map s.toMonoidHom = commSub ⊤ Q' := by
      have hcomm := commSub_map_conj s (⊤ : Subgroup W) Q'
      rw [Subgroup.map_top_of_surjective s.toMonoidHom s.surjective, hQ'stab] at hcomm
      exact hcomm.symm
    intro u hu
    have : s u ∈ (commSub ⊤ Q').map s.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rwa [hmap] at this
  have hBstab : StableUnder (Subgroup.zpowers s) B := w16g_stableUnder_zpowers h'.ht2 hBs
  have hBsup : B = ⨆ U ∈ s13Supp X Q', U := by
    rw [hBdef]
    exact commSub_top_eq_iSup_s13Supp h.hW hp hp2 h.hXe h'.hQX
  set C : Subgroup W := ⨆ U ∈ s13IsoComps X \ s13Supp X Q', U with hCdef
  have hSmap : ∀ U : Subgroup W,
      U.map s.toMonoidHom ∈ s13Supp X Q' ↔ U ∈ s13Supp X Q' := by
    intro U
    have hconj := s13Supp_conj (X := X) (L := Q') (g := s) hgs hgs'
    rw [hQ'stab] at hconj
    constructor
    · intro hU
      rw [hconj] at hU
      obtain ⟨V, hV, hVU⟩ := hU
      have hVU' : V = U := Subgroup.map_injective s.injective hVU
      rwa [hVU'] at hV
    · intro hU
      rw [hconj]
      exact ⟨U, hU, rfl⟩
  have hCmap_le : C.map s.toMonoidHom ≤ C := by
    rw [hCdef]
    simp_rw [Subgroup.map_iSup]
    refine iSup_le fun U => iSup_le fun hU => ?_
    have hUmap : U.map s.toMonoidHom ∈ s13IsoComps X \ s13Supp X Q' :=
      ⟨map_mem_s13IsoComps hgs hgs' hU.1, fun hcon => hU.2 ((hSmap U).mp hcon)⟩
    exact le_iSup₂ (f := fun V (_ : V ∈ s13IsoComps X \ s13Supp X Q') => V)
      (U.map s.toMonoidHom) hUmap
  have hCmap : C.map s.toMonoidHom = C :=
    Subgroup.eq_of_le_of_card_ge hCmap_le (by
      rw [Subgroup.card_map_of_injective s.injective])
  have hCs : ∀ c ∈ C, s c ∈ C := by
    intro c hc
    have : s c ∈ C.map s.toMonoidHom := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    rwa [hCmap] at this
  have hfixs : ∀ u ∈ fixV X, s u ∈ fixV X := by
    intro u hu
    rw [mem_fixV] at hu ⊢
    intro x hx
    have hxu : (s⁻¹ * x * s) u = u := hu (s⁻¹ * x * s) (by
      simpa using h.hXA s⁻¹ (A.inv_mem hsA) x hx)
    calc x (s u) = s ((s⁻¹ * x * s) u) := by simp [MulAut.mul_apply]
      _ = s u := by rw [hxu]
  set B' : Subgroup W := fixV X ⊔ C with hB'def
  have hB'stab : StableUnder (Subgroup.zpowers s) B' := by
    rw [hB'def]
    exact stableUnder_sup (w16g_stableUnder_zpowers h'.ht2 hfixs)
      (w16g_stableUnder_zpowers h'.ht2 hCs)
  have hBle : B ≤ commSub ⊤ X := by
    rw [hBdef]; exact commSub_mono le_top h'.hQX
  have hCle : C ≤ commSub ⊤ X := by
    rw [hCdef]
    refine iSup_le fun U => iSup_le fun hU => ?_
    exact (s13IsoComps_le_commSub h.hW hodd hU.1).2
  have hBC : B ⊓ C = ⊥ := by
    rw [hBsup, hCdef]
    exact (w16g_disjoint_sup_sdiff h.hW hodd (S := s13Supp X Q') (fun _ hU => hU.1)).eq_bot
  have hB'disj : B ⊓ B' = ⊥ := by
    rw [hB'def]
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨hxB, hxB'⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨f, hf, c, hc, rfl⟩ := Subgroup.mem_sup.mp hxB'
    have hfcomm : f ∈ commSub ⊤ X := by
      have hfeq : f = (f * c) * c⁻¹ := by group
      rw [hfeq]
      exact (commSub ⊤ X).mul_mem (hBle hxB) ((commSub ⊤ X).inv_mem (hCle hc))
    have hf1 : f = 1 := by
      have : f ∈ fixV X ⊓ commSub ⊤ X := ⟨hf, hfcomm⟩
      rw [hfixcomm] at this
      exact Subgroup.mem_bot.mp this
    have hc1 : c = 1 := by
      rw [hf1, one_mul] at hxB
      have : c ∈ B ⊓ C := ⟨hxB, hc⟩
      rw [hBC] at this
      exact Subgroup.mem_bot.mp this
    rw [Subgroup.mem_bot, hf1, hc1, mul_one]
  have heq : commSub B (Subgroup.zpowers s) = commSub ⊤ (Subgroup.zpowers s) := by
    refine eq_of_le_of_rk_le (fun w => by rw [pow_two]; exact h.hW w) ?_ ?_
    · rw [hBdef]; exact commSub_mono le_top le_rfl
    · rw [hcost']; exact h'.hrk
  have hB'bot : commSub B' (Subgroup.zpowers s) = ⊥ := by
    have h1 : commSub B' (Subgroup.zpowers s) ≤ B := by
      calc commSub B' (Subgroup.zpowers s) ≤ commSub ⊤ (Subgroup.zpowers s) :=
            commSub_mono le_top le_rfl
        _ = commSub B (Subgroup.zpowers s) := heq.symm
        _ ≤ B := commSub_le_of_invariant hBstab
    have h2 : commSub B' (Subgroup.zpowers s) ≤ B' := commSub_le_of_invariant hB'stab
    have : commSub B' (Subgroup.zpowers s) ≤ B ⊓ B' := le_inf h1 h2
    rw [hB'disj] at this
    exact le_bot_iff.mp this
  refine ⟨?_, ?_⟩
  · intro U hU hUnot
    have hUleB' : U ≤ B' := by
      rw [hB'def]
      exact le_trans
        (le_iSup₂ (f := fun U (_ : U ∈ s13IsoComps X \ s13Supp X Q') => U) U
          ⟨hU, hUnot⟩) le_sup_right
    exact le_bot_iff.mp
      (calc commSub U (Subgroup.zpowers s) ≤ commSub B' (Subgroup.zpowers s) :=
            commSub_mono hUleB' le_rfl
        _ = ⊥ := hB'bot)
  · have hfixleB' : fixV X ≤ B' := by rw [hB'def]; exact le_sup_left
    exact le_bot_iff.mp
      (calc commSub (fixV X) (Subgroup.zpowers s) ≤ commSub B' (Subgroup.zpowers s) :=
            commSub_mono hfixleB' le_rfl
        _ = ⊥ := hB'bot)

theorem exists_of_singleton_supp (h : HAb A X Q t p) {y : MulAut W} (hy : y ∈ X) (hy1 : y ≠ 1)
    (hs : (s13Supp X (Subgroup.zpowers y)).ncard = 1) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ ∧
      sSupIndep (conjSubs A (commSub ⊤ L)) ∧ (s13Supp X L).ncard = 1 ∧
      ((p = 3 ∧ Nat.card ↥L = 3 ∧
          (rk ↥(commSub ⊤ L) = 2 ∨ rk ↥(commSub ⊤ L) = 4 ∨ rk ↥(commSub ⊤ L) = 6)) ∨
        (p = 7 ∧ Nat.card ↥L = 7 ∧ rk ↥(commSub ⊤ L) = 3)) := by
  classical
  have hp : p.Prime := by
    rcases h.hp with h3 | h7
    · rw [h3]; norm_num
    · rw [h7]; norm_num
  have hp2 : p ≠ 2 := by
    rcases h.hp with h3 | h7
    · rw [h3]; norm_num
    · rw [h7]; norm_num
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 h.hXe
  set L₀ : Subgroup (MulAut W) := Subgroup.zpowers y with hL₀
  have hL₀X : L₀ ≤ X := by rw [hL₀]; exact Subgroup.zpowers_le.mpr hy
  have hs' : (s13Supp X L₀).ncard = 1 := by rw [hL₀]; exact hs
  obtain ⟨U, hUeq⟩ := Set.ncard_eq_one.mp hs'
  have hsupp_eq : s13Supp X (Subgroup.zpowers y) = {U} := by rw [← hL₀, hUeq]
  have hUsupp : U ∈ s13Supp X L₀ := by rw [hUeq]; exact Set.mem_singleton U
  have hUcomp : U ∈ s13IsoComps X := hUsupp.1
  have hUnotbot : commSub U L₀ ≠ ⊥ := hUsupp.2
  have hyorder : orderOf y = p := by
    have hdvd : orderOf y ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (h.hXe.2 y hy)
    rcases hp.eq_one_or_self_of_dvd (orderOf y) hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact hp'
  have hL₀card : Nat.card L₀ = p := by rw [hL₀, Nat.card_zpowers, hyorder]
  obtain ⟨lam, hlam⟩ := exists_coord h.hW hp hp2 h.hXe
  have hlamUy : lam ⟨U, hUcomp⟩ (Additive.ofMul (⟨y, hy⟩ : ↥X)) ≠ 0 :=
    (coord_ne_zero_iff hlam ⟨y, hy⟩ ⟨U, hUcomp⟩).mpr (by simpa [hL₀] using hUnotbot)
  obtain ⟨a, haA, hUsupp'⟩ := exists_conj_supp h hUcomp
  set sm : MulAut W := a * t * a⁻¹ with hsm
  have hsmA : sm ∈ A := by rw [hsm]; exact A.mul_mem (A.mul_mem haA h.htA) (A.inv_mem haA)
  have hsmX : ∀ x ∈ X, sm * x * sm⁻¹ ∈ X := fun x hx => h.hXA sm hsmA x hx
  have hsmX' : ∀ x ∈ X, sm⁻¹ * x * sm ∈ X := by
    intro x hx; simpa using h.hXA sm⁻¹ (A.inv_mem hsmA) x hx
  have hne : sm * y * sm⁻¹ ≠ y := by
    by_cases hfix : U.map sm.toMonoidHom = U
    · rcases h.hp with h3 | h7
      · have hfix' : U.map (a * t * a⁻¹).toMonoidHom = U := by rw [← hsm]; exact hfix
        have hker := fixed_comp_inverted (h3 ▸ h) haA hUsupp' hfix'
        have hkery : sm * y * sm⁻¹ * y ∈ s13KerOn X U := by simpa [hsm] using hker y hy
        intro hyeq
        have hy2 : y * y ∈ s13KerOn X U := by
          have h := hkery
          rw [hyeq] at h
          exact h
        have hmemXy : y * y ∈ X := X.mul_mem hy hy
        have hzero : lam ⟨U, hUcomp⟩ (Additive.ofMul (⟨y * y, hmemXy⟩ : ↥X)) = 0 :=
          ((hlam ⟨U, hUcomp⟩).2 ⟨y * y, hmemXy⟩).mpr hy2
        have hadd : Additive.ofMul (⟨y * y, hmemXy⟩ : ↥X) =
            Additive.ofMul (⟨y, hy⟩ : ↥X) + Additive.ofMul (⟨y, hy⟩ : ↥X) := by
          rw [← ofMul_mul]; congr 1
        have h2 : (2 : ZMod p) * lam ⟨U, hUcomp⟩ (Additive.ofMul (⟨y, hy⟩ : ↥X)) = 0 := by
          rw [two_mul]
          rw [hadd, map_add] at hzero
          exact hzero
        exact hlamUy ((mul_eq_zero.mp h2).resolve_left (w16g_two_ne_zero_zmod hp hp2))
      · have hfix' : U.map (a * t * a⁻¹).toMonoidHom = U := by rw [← hsm]; exact hfix
        exact absurd hfix' (not_fixed_comp (h7 ▸ h) haA hUsupp')
    · obtain ⟨σ, c, hσ, hc⟩ := exists_monomial h.hW hp hp2 h.hXe hlam hsmX hsmX'
      have hσU : (σ ⟨U, hUcomp⟩ : Subgroup W) = U.map sm.toMonoidHom := hσ ⟨U, hUcomp⟩
      have hσU_ne : (σ ⟨U, hUcomp⟩ : Subgroup W) ≠ U := by rw [hσU]; exact hfix
      have hnotmem : (σ ⟨U, hUcomp⟩ : Subgroup W) ∉ s13Supp X (Subgroup.zpowers y) := by
        rw [hsupp_eq, Set.mem_singleton_iff]; exact hσU_ne
      have hσzero : lam (σ ⟨U, hUcomp⟩) (Additive.ofMul (⟨y, hy⟩ : ↥X)) = 0 := by
        by_contra hcon
        exact hnotmem ⟨(σ ⟨U, hUcomp⟩).2,
          (coord_ne_zero_iff hlam ⟨y, hy⟩ (σ ⟨U, hUcomp⟩)).mp hcon⟩
      have hnonzero : lam (σ ⟨U, hUcomp⟩) (Additive.ofMul
          (⟨sm * y * sm⁻¹, hsmX y hy⟩ : ↥X)) ≠ 0 := by
        rw [hc ⟨U, hUcomp⟩ ⟨y, hy⟩ (hsmX y hy)]
        exact mul_ne_zero (Units.ne_zero _) hlamUy
      intro hyeq
      have h1 : (⟨sm * y * sm⁻¹, hsmX y hy⟩ : ↥X) = ⟨y, hy⟩ := Subtype.ext hyeq
      rw [h1] at hnonzero
      exact hnonzero hσzero
  set L : Subgroup (MulAut W) := L₀.map (MulAut.conj a⁻¹).toMonoidHom with hL
  have hga : ∀ x ∈ X, a⁻¹ * x * (a⁻¹)⁻¹ ∈ X := fun x hx => h.hXA a⁻¹ (A.inv_mem haA) x hx
  have hga' : ∀ x ∈ X, (a⁻¹)⁻¹ * x * a⁻¹ ∈ X := by
    intro x hx; simpa using h.hXA a haA x hx
  have hLsupp_eq : s13Supp X L = {U.map a⁻¹.toMonoidHom} := by
    have hconj := s13Supp_conj (X := X) (L := L₀) (g := a⁻¹) hga hga'
    rw [← hL] at hconj
    rw [hconj, hUeq, Set.image_singleton]
  have hLX : L ≤ X := by
    intro u hu
    rw [hL] at hu
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hu
    change MulAut.conj a⁻¹ l ∈ X
    rw [MulAut.conj_apply, inv_inv]
    exact h.hXA a⁻¹ (A.inv_mem haA) l (hL₀X hl)
  have hLsupp_ncard : (s13Supp X L).ncard = 1 := by rw [hLsupp_eq]; simp
  have hLcomm : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    have hxL : a⁻¹ * y * a ∈ L := by
      rw [hL]
      refine Subgroup.mem_map.mpr ⟨y, ?_, ?_⟩
      · rw [hL₀]; exact Subgroup.mem_zpowers y
      · change MulAut.conj a⁻¹ y = a⁻¹ * y * a
        rw [MulAut.conj_apply, inv_inv]
    have hxne : t * (a⁻¹ * y * a) * t⁻¹ ≠ a⁻¹ * y * a := by
      intro heq
      apply hne
      have h1 : sm * y * sm⁻¹ = a * (t * (a⁻¹ * y * a) * t⁻¹) * a⁻¹ := by
        rw [hsm]; group
      rw [h1, heq]; group
    have hmem : ⁅a⁻¹ * y * a, t⁆ ∈ ⁅L, Subgroup.zpowers t⁆ :=
      Subgroup.commutator_mem_commutator hxL (Subgroup.mem_zpowers t)
    rw [hbot] at hmem
    have h1 : ⁅a⁻¹ * y * a, t⁆ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : t * (a⁻¹ * y * a) * t⁻¹ = a⁻¹ * y * a := by
      have hcomm : (a⁻¹ * y * a) * t = t * (a⁻¹ * y * a) :=
        commutatorElement_eq_one_iff_mul_comm.mp h1
      rw [← hcomm]; group
    exact hxne h2
  have hSupIndep : sSupIndep (conjSubs A (commSub ⊤ L)) := by
    refine sSupIndep_conjSubs_of_s13Supp h.hW hp hp2 h.hXe h.hXA hLX ?_
    intro g hg
    have h2 : (s13Supp X (L.map (MulAut.conj g).toMonoidHom)).ncard = 1 := by
      have hconj := s13Supp_conj (X := X) (L := L) (g := g)
        (fun x hx => h.hXA g hg x hx)
        (fun x hx => by simpa using h.hXA g⁻¹ (A.inv_mem hg) x hx)
      rw [hconj]
      rw [Set.ncard_image_of_injective _ (Subgroup.map_injective g.injective)]
      exact hLsupp_ncard
    exact w16g_ncard_one_disjoint_or_eq h2 hLsupp_ncard
  have hcommL : commSub ⊤ L = U.map a⁻¹.toMonoidHom := by
    rw [commSub_top_eq_iSup_s13Supp h.hW hp hp2 h.hXe hLX, hLsupp_eq]
    simp
  have hrkL : rk ↥(commSub ⊤ L) = rk ↥U := by
    rw [hcommL]
    unfold rk
    rw [Subgroup.card_map_of_injective (f := (a⁻¹).toMonoidHom) (a⁻¹).injective]
  refine ⟨L, hLX, hLcomm, hSupIndep, hLsupp_ncard, ?_⟩
  rcases h.hp with h3 | h7
  · left
    have hd3 : dParam p = 2 := by
      rw [h3, dParam]
      exact (orderOf_eq_iff (by norm_num : 0 < 2)).2
        ⟨by decide, by intro m hm _; interval_cases m <;> decide⟩
    obtain ⟨s, hs0, hsrk⟩ := rk_s13IsoComps_eq h.hW hp hp2 h.hXe hUcomp
    have hle6 := rk_s13IsoComps_le_six h hUcomp
    have hcard : Nat.card ↥L = 3 := by
      rw [hL, Subgroup.card_map_of_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
        (MulAut.conj a⁻¹).injective, hL₀card, h3]
    refine ⟨h3, hcard, ?_⟩
    rw [hrkL, hsrk, hd3]
    rw [hsrk, hd3] at hle6
    omega
  · right
    have hcard : Nat.card ↥L = 7 := by
      rw [hL, Subgroup.card_map_of_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
        (MulAut.conj a⁻¹).injective, hL₀card, h7]
    refine ⟨h7, hcard, ?_⟩
    rw [hrkL]
    exact rk_s13IsoComps_eq_three (h7 ▸ h) hUcomp

end CFSG.LocalAnalysis.WeakClosure81
