module

public import CFSG.Quasithin.Background.F918Z8Kb

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

section PartB

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

omit [Finite Y] in
theorem d321k_realizesVia_of_iso {D : FFModel} {π : D.Gam →* ↥Λ} {J J' : Subgroup Y}
    (h : D.RealizesVia Λ J' ⊥ π) (hJ : XMod.IsInv ↥Λ J) (hiso : XMod.Iso ↥Λ J J') :
    D.RealizesVia Λ J ⊥ π := by
  obtain ⟨hπs, -, hks, hinv', hinvZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  obtain ⟨φ, hφ⟩ := hiso
  refine ⟨hπs, bot_le, hks, fun a u hu => hJ a u hu, hinvZ, hsec, hker,
    β.comp φ.toMonoidHom, hβs.comp φ.surjective, fun u => ?_, ?_⟩
  · show β (φ u) = 1 ↔ (u : Y) ∈ (⊥ : Subgroup Y)
    rw [hβk, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h1
      have h2 : φ u = 1 := Subtype.ext h1
      have h3 : u = 1 := φ.injective (h2.trans (map_one φ).symm)
      rw [h3]
      rfl
    · intro h1
      have h2 : u = 1 := Subtype.ext h1
      rw [h2, map_one]
      rfl
  · intro γ u m hu hm hum
    have hφu : φ ⟨((π γ : ↥Λ) : MulAut Y) u, hu⟩ =
        ⟨((π γ : ↥Λ) : MulAut Y) (φ u), hinv' (π γ) (φ u) (φ u).2⟩ :=
      Subtype.ext (hφ (π γ) u ⟨_, hu⟩ rfl).symm
    show β (φ ⟨_, hu⟩) = _
    rw [hφu]
    exact hβe γ (φ u) m (hinv' (π γ) (φ u) (φ u).2) hm hum

theorem loc_directSum {D : FFModel} {π : D.Gam →* ↥Λ} (hexp : ∀ y : Y, y ^ 2 = 1)
    (hVirr : XMod.IsIrr ↥Λ V) (hπ : D.RealizesVia Λ V ⊥ π)
    (hΓ : Γ ≤ Subgroup.normalizer (Λ : Set (MulAut Y)))
    (hsum : (⨆ g ∈ Γ, V.map g.toMonoidHom) = ⊤)
    (hiso : ∀ g ∈ Γ, XMod.Iso ↥Λ (V.map g.toMonoidHom) V) :
    ∃ k : ℕ, DirectSumOfCopies Λ ⊤ ⊥ D k ∧ rk Y = k * rk ↥V := by
  classical
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (hΓ ha) y).1 hy
  have hN : XMod.Normalizes ↥Λ ↥Γ Y := Z3A1.normalizes_of_conj hgn
  have hirr : ∀ g ∈ Γ, XMod.IsIrr ↥Λ (V.map g.toMonoidHom) := fun g hg =>
    Z3A1.isIrr_smul hN ⟨g, hg⟩ hVirr
  have hrkJ : ∀ g : MulAut Y, rk ↥(V.map g.toMonoidHom) = rk ↥V := fun g => by
    unfold rk
    rw [Subgroup.card_map_of_injective g.injective]
  have hV0 : V ≠ ⊥ := bot_lt_iff_ne_bot.1 hVirr.2.1
  have hVpos : 0 < rk ↥V := Nat.pos_of_ne_zero fun h0 => hV0 ((rk_eq_zero_iff hexp).1 h0)
  have hrkY : ∀ P : Subgroup Y, rk ↥P ≤ rk Y := fun P => by
    have := rk_mono (le_top : P ≤ ⊤)
    rwa [rk_top] at this
  have step : ∀ n : ℕ, ∀ s : Finset (Subgroup Y),
      ((∀ J ∈ s, ∃ g ∈ Γ, J = V.map g.toMonoidHom) ∧ s.SupIndep id ∧
        rk ↥(s.sup id) = s.card * rk ↥V) → rk Y - rk ↥(s.sup id) = n →
      ∃ s' : Finset (Subgroup Y), ((∀ J ∈ s', ∃ g ∈ Γ, J = V.map g.toMonoidHom) ∧ s'.SupIndep id ∧
        rk ↥(s'.sup id) = s'.card * rk ↥V) ∧ s'.sup id = ⊤ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs hn
      by_cases htop : s.sup id = ⊤
      · exact ⟨s, hs, htop⟩
      · obtain ⟨hsT, hsI, hsrk⟩ := hs
        obtain ⟨g, hgΓ, hgP⟩ : ∃ g ∈ Γ, ¬ V.map g.toMonoidHom ≤ s.sup id := by
          by_contra hcon
          push Not at hcon
          apply htop
          rw [eq_top_iff, ← hsum]
          exact iSup₂_le hcon
        have hPinv : XMod.IsInv ↥Λ (s.sup id) := by
          refine Finset.sup_induction ?_ (fun a ha b hb => ha.sup hb) (fun J hJ => ?_)
          · intro a x hx
            rw [Subgroup.mem_bot] at hx ⊢
            rw [hx]
            exact smul_one a
          · obtain ⟨g', hg', rfl⟩ := hsT J hJ
            exact (hirr g' hg').1
        have hdisj : V.map g.toMonoidHom ⊓ s.sup id = ⊥ := by
          rcases (hirr g hgΓ).2.2 (V.map g.toMonoidHom ⊓ s.sup id)
              ((hirr g hgΓ).1.inf hPinv) bot_le inf_le_left with h0 | h0
          · exact h0
          · exact absurd (h0 ▸ inf_le_right) hgP
        have hJs : V.map g.toMonoidHom ∉ s := fun hJs => hgP (Finset.le_sup (f := id) hJs)
        have hsup : (insert (V.map g.toMonoidHom) s).sup id = V.map g.toMonoidHom ⊔ s.sup id :=
          Finset.sup_insert
        have hrk1 := rk_sup_add_rk_inf (V.map g.toMonoidHom) (s.sup id)
        rw [hdisj, rk_bot, hrkJ g] at hrk1
        have hrk2 : rk ↥((insert (V.map g.toMonoidHom) s).sup id) = rk ↥V + s.card * rk ↥V := by
          rw [hsup]
          omega
        have hle := hrkY ((insert (V.map g.toMonoidHom) s).sup id)
        refine ih (rk Y - rk ↥((insert (V.map g.toMonoidHom) s).sup id)) (by omega)
          (insert (V.map g.toMonoidHom) s) ⟨?_, ?_, ?_⟩ rfl
        · intro J hJ
          rcases Finset.mem_insert.1 hJ with rfl | hJ'
          · exact ⟨g, hgΓ, rfl⟩
          · exact hsT J hJ'
        · exact Finset.SupIndep.insert hsI (disjoint_iff.2 hdisj)
        · rw [hrk2, Finset.card_insert_of_notMem hJs]
          ring
  obtain ⟨s', ⟨hsT, hsI, hsrk⟩, hstop⟩ :=
    step _ ∅ ⟨by simp, Finset.supIndep_empty _,
      by rw [Finset.sup_empty, rk_bot, Finset.card_empty, zero_mul]⟩ rfl
  refine ⟨s'.card, ?_, ?_⟩
  · let e : Fin s'.card ≃ s' := s'.equivFin.symm
    let I : Fin s'.card → Subgroup Y := fun i => ((e i : s') : Subgroup Y)
    have hIind : iSupIndep I := by
      have h1 := Finset.SupIndep.independent hsI
      exact h1.comp e.injective
    have hIsum : ⨆ i, I i = ⊤ := by
      have h1 : ⨆ i, I i = ⨆ x : s', (x : Subgroup Y) :=
        Equiv.iSup_comp (g := fun x : s' => (x : Subgroup Y)) e
      have h2 : s'.sup id = ⨆ x : s', (x : Subgroup Y) := by
        rw [Finset.sup_eq_iSup, iSup_subtype']
        rfl
      rw [h1, ← h2, hstop]
    refine ⟨I, π, fun i => bot_le, fun i => ?_, ?_, fun i => ?_⟩
    · rw [bot_sup_eq]
      exact disjoint_iff.1 (hIind i)
    · rw [bot_sup_eq]
      exact hIsum
    · obtain ⟨g, hg, hgeq⟩ := hsT (I i) (e i).2
      rw [hgeq]
      exact d321k_realizesVia_of_iso hπ (hirr g hg).1 (hiso g hg)
  · have h1 := hsrk
    rw [hstop, rk_top] at h1
    exact h1


theorem loc_hhom (h : LocCfg Γ Λ S V)
    (hiso : ∀ g ∈ Γ, XMod.Iso ↥Λ (V.map g.toMonoidHom) V)
    {H : Subgroup (MulAut Y)} (hΛH : Λ ≤ H) (hVinv : ∀ g : ↥H, ∀ v ∈ V, g • v ∈ V)
    (P : Subgroup Y) (hP : ∀ g : ↥H, ∀ x ∈ P, g • x ∈ P) (hPtop : P ≠ ⊤) :
    ∃ ψ : ↥V →* Z391.QuotMod P hP,
      (∀ l ∈ Λ.subgroupOf H, ∀ v : ↥V, ψ ⟨l • (v : Y), hVinv l v v.2⟩ = l • ψ v) ∧ ψ ≠ 1 := by
  classical
  obtain ⟨g, hgΓ, hgP⟩ : ∃ g ∈ Γ, ¬ V.map g.toMonoidHom ≤ P := by
    by_contra hcon
    push Not at hcon
    apply hPtop
    rw [eq_top_iff, ← h.std.hyp.gen]
    exact iSup₂_le hcon
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  have hN : XMod.Normalizes ↥Λ ↥Γ Y := Z3A1.normalizes_of_conj hgn
  have hirr : XMod.IsIrr ↥Λ ((⟨g, hgΓ⟩ : ↥Γ) • V) :=
    Z3A1.isIrr_smul hN ⟨g, hgΓ⟩ (loc_isIrr h)
  have hsm : ((⟨g, hgΓ⟩ : ↥Γ) • V) = V.map g.toMonoidHom := rfl
  rw [hsm] at hirr
  set S₀ : Subgroup Y := V.map g.toMonoidHom with hS₀
  have hS₀inv : XMod.IsInv ↥Λ S₀ := hirr.1
  have hPΛ : XMod.IsInv ↥Λ P := fun a x hx => hP ⟨a, hΛH a.2⟩ x hx
  have hdisj : S₀ ⊓ P = ⊥ := by
    rcases hirr.2.2 (S₀ ⊓ P) (XMod.IsInv.inf hS₀inv hPΛ) bot_le inf_le_left with h0 | h0
    · exact h0
    · exact absurd (h0 ▸ inf_le_right) hgP
  obtain ⟨φ, hφ⟩ := hiso g hgΓ
  let ψ₀ : ↥V →* Z391.QuotMod P hP :=
    (Z391.QuotMod.mk P hP).comp (S₀.subtype.comp φ.symm.toMonoidHom)
  refine ⟨ψ₀, ?_, ?_⟩
  · intro l hl v
    have hlΛ : ((l : ↥H) : MulAut Y) ∈ Λ := hl
    set x : ↥S₀ := φ.symm v with hx
    set a : ↥Λ := ⟨((l : ↥H) : MulAut Y), hlΛ⟩ with ha
    have hlx : l • (x : Y) ∈ S₀ := hS₀inv a x x.2
    have h1 := hφ a x ⟨l • (x : Y), hlx⟩ rfl
    have hφx : φ x = v := φ.apply_symm_apply v
    rw [hφx] at h1
    have h2 : φ ⟨l • (x : Y), hlx⟩ = ⟨l • (v : Y), hVinv l v v.2⟩ := Subtype.ext h1.symm
    have h3 : φ.symm ⟨l • (v : Y), hVinv l v v.2⟩ = ⟨l • (x : Y), hlx⟩ := by
      rw [← h2, φ.symm_apply_apply]
    show Z391.QuotMod.mk P hP ((φ.symm ⟨l • (v : Y), hVinv l v v.2⟩ : ↥S₀) : Y) =
      l • Z391.QuotMod.mk P hP ((x : ↥S₀) : Y)
    rw [h3, Z391.quotMod_smul_mk]
  · obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v ∈ V, v ≠ 1 := by
      by_contra hcon
      apply (loc_irr_data h).2.1
      refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
      by_contra hne
      exact hcon ⟨v, hv, hne⟩
    intro h0
    have h1 : ψ₀ ⟨v₀, hv₀⟩ = 1 := by rw [h0]; rfl
    have h2 : ((φ.symm ⟨v₀, hv₀⟩ : ↥S₀) : Y) ∈ (Z391.QuotMod.mk P hP).ker := h1
    rw [Z391.QuotMod.ker_mk] at h2
    have h3 : ((φ.symm ⟨v₀, hv₀⟩ : ↥S₀) : Y) ∈ S₀ ⊓ P := ⟨(φ.symm ⟨v₀, hv₀⟩).2, h2⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have h4 : φ.symm ⟨v₀, hv₀⟩ = 1 := Subtype.ext h3
    have h5 : (⟨v₀, hv₀⟩ : ↥V) = 1 := by
      have := congrArg φ h4
      rwa [φ.apply_symm_apply, map_one] at this
    exact hv₀1 (congrArg Subtype.val h5)

theorem loc_count (h : LocCfg Γ Λ S V) {A : Subgroup (MulAut Y)}
    (hA : A ∈ QhatStar Γ) (hAS : A ≤ S)
    (hiso : ∀ g ∈ Γ, XMod.Iso ↥Λ (V.map g.toMonoidHom) V) {k : ℕ} (hk : rk Y = k * rk ↥V) :
    k * rkIdx (fixV (autSub A V)) ≤ 2 * rk ↥A := by
  classical
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec hA
  have hrA : 0 < rk ↥A := hA2.rk_pos
  have hAΓ : A ≤ Γ := hA2.1
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  have hLs : Λ ≤ stabSub V := le_stabSub_of_forall_mem (loc_irr_data h).1
  have hAs : A ≤ stabSub V := le_stabSub_of_forall_mem fun a ha => loc_S_inv h a (hAS ha)
  set H : Subgroup (MulAut Y) := Λ ⊔ A with hH
  have hΛH : Λ ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hHs : H ≤ stabSub V := sup_le hLs hAs
  have hVinv : ∀ g : ↥H, ∀ v ∈ V, g • v ∈ V := fun g v hv => (hHs g.2 v).2 hv
  have hVirr : XMod.IsIrr ↥(Λ.subgroupOf H) V := Z391.isIrr_subgroupOf hΛH (loc_isIrr h)
  have hQ : ∀ q : Y, q ^ 2 = 1 := h.std.hyp.exp
  have hAp : IsPGroup 2 ↥(A.subgroupOf H) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hA2.2.2.2 ((x : ↥H) : MulAut Y) x.2))⟩
  have hAΛ : ∀ a ∈ A.subgroupOf H, ∀ l ∈ Λ.subgroupOf H, a * l * a⁻¹ ∈ Λ.subgroupOf H :=
    fun a ha l hl => hgn (a : MulAut Y) (hAΓ ha) (l : MulAut Y) hl
  have hgen : Λ.subgroupOf H ⊔ A.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hΛH hAH]
    exact Subgroup.subgroupOf_self H
  have hmc := Z391.d321k_multi_count (Γ := ↥H) (Q := Y) hQ hAp hAΛ hgen hVinv hVirr
    (fun P hP hPtop => loc_hhom h hiso hΛH hVinv P hP hPtop)
  have hA₀A : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
  have hn1 : Z391.nB (A.subgroupOf H) (⊤ : Subgroup Y) ≤ rkIdx (fixV A) := by
    have := Z391.nB_top_le_rkIdx_fixV (M := H) (MonoidHom.id Y) Function.surjective_id
      (fun g w => rfl) (A.subgroupOf H)
    rwa [hA₀A] at this
  have hn2 : Z391.nB (A.subgroupOf H) V = rkIdx (fixV (autSub A V)) := by
    rw [Z391.nB_subgroupOf hAH V]
    have e1 : XMod.fixed ↥A (⊤ : Subgroup Y) = fixV A :=
      (fixed_eq_inf_fixV A ⊤).trans (top_inf_eq _)
    have e2 := rk_add_rkIdx (fixV (autSub A V))
    have e3 := rk_fixV_autSub hAs
    have e4 : Z391.nB A V = rk ↥V - rk ↥(V ⊓ fixV A) := by
      unfold Z391.nB
      rw [e1]
    rw [e4]
    have e5 : rk ↥(⊤ : Subgroup ↥V) = rk ↥V := rk_top
    omega
  have hN2 : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h1 : rAV A ≤ 2 := by rw [hAr]; exact_mod_cast hr2
    unfold rAV at h1
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    rw [div_le_iff₀ hpos] at h1
    exact_mod_cast h1
  have hV0 : V ≠ ⊥ := (loc_irr_data h).2.1
  have hVpos : 0 < rk ↥V := Nat.pos_of_ne_zero fun h0 => hV0 ((rk_eq_zero_iff hQ).1 h0)
  rw [hk, hn2] at hmc
  have h5 : rk ↥V * (k * rkIdx (fixV (autSub A V))) ≤ rk ↥V * (2 * rk ↥A) := by
    calc rk ↥V * (k * rkIdx (fixV (autSub A V))) = k * rk ↥V * rkIdx (fixV (autSub A V)) := by ring
      _ ≤ rk ↥V * Z391.nB (A.subgroupOf H) ⊤ := hmc
      _ ≤ rk ↥V * (2 * rk ↥A) := Nat.mul_le_mul_left _ (hn1.trans hN2)
  exact Nat.le_of_mul_le_mul_left h5 hVpos

end PartB

end CFSG.Quasithin
