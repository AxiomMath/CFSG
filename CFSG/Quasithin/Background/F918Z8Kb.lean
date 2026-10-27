module

public import CFSG.Quasithin.Background.F918Z8Ka
public import CFSG.Quasithin.Background.F918Z3A1Aux
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

namespace Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem d321k_add_copy [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ A : Subgroup Γ} (hA : IsPGroup 2 A)
    (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) (hgen : Λ ⊔ A = ⊤) {V : Subgroup Q}
    (hVinv : ∀ g : Γ, ∀ v ∈ V, g • v ∈ V) (hV : XMod.IsIrr ↥Λ V)
    {P : Subgroup Q} (hP : ∀ g : Γ, ∀ x ∈ P, g • x ∈ P) (ψ₀ : ↥V →* QuotMod P hP)
    (hψ₀ : ∀ l ∈ Λ, ∀ v : ↥V, ψ₀ ⟨l • (v : Q), hVinv l v v.2⟩ = l • ψ₀ v) (hne : ψ₀ ≠ 1) :
    ∃ P' : Subgroup Q, P ≤ P' ∧ (∀ g : Γ, ∀ x ∈ P', g • x ∈ P') ∧
      rk ↥P' = rk ↥P + rk ↥V ∧ nB A P + nB A V ≤ nB A P' := by
  classical
  let _ : MulDistribMulAction Γ ↥V := subAct V hVinv
  have hq2 : ∀ p : QuotMod P hP, p ^ 2 = 1 := by
    intro p
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective P hP p
    rw [← map_pow, hQ x, map_one]
  obtain ⟨φ, hφne, hφΛ, hφA⟩ :=
    exists_fixed_hom hq2 Λ A hA hAΛ ψ₀ (fun l hl p => hψ₀ l hl p) hne
  have hker : φ.ker = ⊥ := by
    set K : Subgroup Q := (φ.ker).map V.subtype with hK
    have hKΛ : XMod.IsInv ↥Λ K := by
      rintro ⟨l, hl⟩ k hk
      obtain ⟨k', hk', rfl⟩ := hk
      refine ⟨l • k', ?_, rfl⟩
      have hk'' : φ k' = 1 := hk'
      show φ (l • k') = 1
      rw [hφΛ l hl k', hk'', smul_one]
    rcases hV.2.2 K hKΛ bot_le (Subgroup.map_subtype_le _) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
      have hk' : (k : Q) ∈ K := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at hk'
      exact Subtype.ext hk'
    · exfalso
      apply hφne
      refine MonoidHom.ext fun v => ?_
      have hv : (v : Q) ∈ K := by rw [h]; exact v.2
      obtain ⟨v', hv', hvv'⟩ := hv
      have : v' = v := Subtype.ext hvv'
      rw [← this]
      exact hv'
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  set S : Subgroup (QuotMod P hP) := φ.range with hS
  have hSinv : ∀ g : Γ, ∀ s ∈ S, g • s ∈ S := by
    have hg_mem : ∀ g : Γ, g ∈ Subgroup.closure ((Λ : Set Γ) ∪ (A : Set Γ)) := by
      intro g
      rw [← Subgroup.sup_eq_closure, hgen]
      exact Subgroup.mem_top g
    have key : ∀ g : Γ, ∀ s ∈ S, g • s ∈ S ∧ g⁻¹ • s ∈ S := by
      intro g
      have hg := hg_mem g
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        rintro _ ⟨v, rfl⟩
        rcases hx with hx | hx
        · exact ⟨⟨_, hφΛ x hx v⟩, ⟨_, hφΛ x⁻¹ (Λ.inv_mem hx) v⟩⟩
        · exact ⟨⟨_, hφA x hx v⟩, ⟨_, hφA x⁻¹ (A.inv_mem hx) v⟩⟩
      | one =>
        intro s hs
        simp only [one_smul, inv_one]
        exact ⟨hs, hs⟩
      | mul x y _ _ hx hy =>
        intro s hs
        refine ⟨?_, ?_⟩
        · rw [mul_smul]
          exact (hx _ (hy s hs).1).1
        · rw [mul_inv_rev, mul_smul]
          exact (hy _ (hx s hs).2).2
      | inv x _ hx =>
        intro s hs
        rw [inv_inv]
        exact ⟨(hx s hs).2, (hx s hs).1⟩
    exact fun g s hs => (key g s hs).1
  set P' : Subgroup Q := S.comap (QuotMod.mk P hP) with hP'
  have hPP' : P ≤ P' := by
    intro x hx
    show QuotMod.mk P hP x ∈ S
    have : QuotMod.mk P hP x = 1 := by
      rw [← MonoidHom.mem_ker, QuotMod.ker_mk]; exact hx
    rw [this]; exact S.one_mem
  have hP'inv : ∀ g : Γ, ∀ x ∈ P', g • x ∈ P' := by
    intro g x hx
    show QuotMod.mk P hP (g • x) ∈ S
    rw [← quotMod_smul_mk]
    exact hSinv g _ hx
  set F : Subgroup Q := XMod.fixed ↥A (⊤ : Subgroup Q) with hF
  set F' : Subgroup (QuotMod P hP) := XMod.fixed ↥A (⊤ : Subgroup (QuotMod P hP)) with hF'
  have hrk1 : rk ↥S = rk ↥V := by
    unfold rk
    exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm)
  have key : ∀ (a : Γ) (v : ↥V), a • v = v ↔ a • (v : Q) = (v : Q) :=
    fun a v => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hmap : S ⊓ F' = ((V ⊓ F).subgroupOf V).map φ := by
    ext y
    constructor
    · rintro ⟨⟨v, rfl⟩, hy⟩
      refine ⟨v, ?_, rfl⟩
      refine ⟨v.2, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩⟩
      have h1 := (XMod.mem_fixed.1 hy).2 a
      change (a : Γ) • φ v = φ v at h1
      rw [← hφA (a : Γ) a.2 v] at h1
      exact (key a v).1 (hinj h1)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨v, rfl⟩, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩⟩
      have h1 := (XMod.mem_fixed.1 hv.2).2 a
      change (a : Γ) • (v : Q) = v at h1
      change (a : Γ) • φ v = φ v
      rw [← hφA (a : Γ) a.2 v, (key a v).2 h1]
  have hrk2 : rk ↥(S ⊓ F') = rk ↥(V ⊓ F) := by
    rw [hmap]
    unfold rk
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ φ hinj).toEquiv.symm]
    exact congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv)
  have hmapP' : P'.map (QuotMod.mk P hP) = S := by
    rw [hP', Subgroup.map_comap_eq_self_of_surjective (QuotMod.mk_surjective P hP)]
  have h1 := B1More.card_map_mul_card_inf_ker P' (QuotMod.mk P hP)
  rw [QuotMod.ker_mk, hmapP', inf_eq_right.2 hPP'] at h1
  have hrkP' : rk ↥P' = rk ↥P + rk ↥V := by
    unfold rk at hrk1 ⊢
    rw [← h1, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hrk1, add_comm]
  refine ⟨P', hPP', hP'inv, hrkP', ?_⟩
  have himg : (P' ⊓ F).map (QuotMod.mk P hP) ≤ S ⊓ F' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hx.1, XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩⟩
    have hb := (XMod.mem_fixed.1 hx.2).2 b
    change (b : Γ) • x = x at hb
    change (b : Γ) • (QuotMod.mk P hP x) = QuotMod.mk P hP x
    rw [quotMod_smul_mk, hb]
  have h2 := B1More.card_map_mul_card_inf_ker (P' ⊓ F) (QuotMod.mk P hP)
  rw [QuotMod.ker_mk] at h2
  have hPF : (P' ⊓ F) ⊓ P = P ⊓ F := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hFx⟩, hx⟩
      exact ⟨hx, hFx⟩
    · rintro ⟨hx, hFx⟩
      exact ⟨⟨hPP' hx, hFx⟩, hx⟩
  rw [hPF] at h2
  have h2' : rk ↥((P' ⊓ F).map (QuotMod.mk P hP)) + rk ↥(P ⊓ F) = rk ↥(P' ⊓ F) := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h2]
  have h3 : rk ↥((P' ⊓ F).map (QuotMod.mk P hP)) ≤ rk ↥(S ⊓ F') := rk_mono himg
  have h4 : rk ↥(P ⊓ F) ≤ rk ↥P := rk_mono inf_le_left
  have h5 : rk ↥(V ⊓ F) ≤ rk ↥V := rk_mono inf_le_left
  have e1 : nB A P = rk ↥P - rk ↥(P ⊓ F) := rfl
  have e2 : nB A V = rk ↥V - rk ↥(V ⊓ F) := rfl
  have e3 : nB A P' = rk ↥P' - rk ↥(P' ⊓ F) := rfl
  rw [e1, e2, e3]
  omega

theorem d321k_multi_count [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ A : Subgroup Γ}
    (hA : IsPGroup 2 A) (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) (hgen : Λ ⊔ A = ⊤)
    {V : Subgroup Q}
    (hVinv : ∀ g : Γ, ∀ v ∈ V, g • v ∈ V) (hV : XMod.IsIrr ↥Λ V)
    (hhom : ∀ (P : Subgroup Q) (hP : ∀ g : Γ, ∀ x ∈ P, g • x ∈ P), P ≠ ⊤ →
      ∃ ψ : ↥V →* QuotMod P hP,
        (∀ l ∈ Λ, ∀ v : ↥V, ψ ⟨l • (v : Q), hVinv l v v.2⟩ = l • ψ v) ∧ ψ ≠ 1) :
    rk Q * nB A V ≤ rk ↥V * nB A (⊤ : Subgroup Q) := by
  have hV0 : V ≠ ⊥ := bot_lt_iff_ne_bot.1 hV.2.1
  have hVpos : 0 < rk ↥V := Nat.pos_of_ne_zero fun h0 => hV0 ((rk_eq_zero_iff hQ).1 h0)
  have key : ∀ d : ℕ, ∀ (j : ℕ) (P : Subgroup Q) (hP : ∀ g : Γ, ∀ x ∈ P, g • x ∈ P),
      rk Q - rk ↥P = d → rk ↥P = j * rk ↥V → j * nB A V ≤ nB A P →
      rk Q * nB A V ≤ rk ↥V * nB A (⊤ : Subgroup Q) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j P hP hd hrk hnB
      by_cases hPtop : P = ⊤
      · subst hPtop
        rw [rk_top] at hrk
        have h1 := nB_mono A (le_top : (⊤ : Subgroup Q) ≤ ⊤)
        rw [hrk]
        calc j * rk ↥V * nB A V = rk ↥V * (j * nB A V) := by ring
          _ ≤ rk ↥V * nB A (⊤ : Subgroup Q) := Nat.mul_le_mul_left _ hnB
      · obtain ⟨ψ, hψ, hψne⟩ := hhom P hP hPtop
        obtain ⟨P', hPP', hP', hrk', hnB'⟩ :=
          d321k_add_copy hQ hA hAΛ hgen hVinv hV hP ψ hψ hψne
        have hle : rk ↥P' ≤ rk Q := by
          have := rk_mono (le_top : P' ≤ ⊤)
          rwa [rk_top] at this
        refine ih (rk Q - rk ↥P') (by omega) (j + 1) P' hP' rfl (by rw [hrk', hrk]; ring) ?_
        calc (j + 1) * nB A V = j * nB A V + nB A V := by ring
          _ ≤ nB A P + nB A V := by omega
          _ ≤ nB A P' := hnB'
  have := key (rk Q - rk ↥(⊥ : Subgroup Q)) 0 ⊥ (fun g x hx => by
    rw [Subgroup.mem_bot] at hx ⊢; rw [hx]; exact smul_one g) rfl (by simp [rk_bot]) (by simp)
  exact this

end Z391

theorem d321k_sylow_mul_cent {G : Type*} [Group G] [Finite G] (N S : Subgroup G) [hN : N.Normal]
    (hZ : ∀ z : ↥N, (∀ g : ↥N, g * z = z * g) → z = 1)
    (hAut : Nat.card (MulAut ↥N) ≤ 2 * Nat.card ↥N) (hS : ¬ 2 ∣ S.index) :
    ∀ g : G, ∃ c ∈ Subgroup.centralizer (N : Set G), ∃ x ∈ N ⊔ S, g = c * x := by
  classical
  set φ : G →* MulAut ↥N := MulAut.conjNormal with hφ
  have hker : φ.ker = Subgroup.centralizer (N : Set G) := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h n hn
      have := congrArg (fun f : MulAut ↥N => (f ⟨n, hn⟩ : G)) h
      simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc n * g = (g * n * g⁻¹) * g := by rw [this]
        _ = g * n := by group
    · intro h
      ext ⟨n, hn⟩
      simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply]
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [h n hn]
        _ = n := by group
  have hinj : Function.Injective (φ.comp N.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (Subgroup.eq_bot_iff_forall _).2 fun n hn => ?_
    have h1 : φ (n : G) = 1 := hn
    have h2 : (n : G) ∈ φ.ker := h1
    rw [hker, Subgroup.mem_centralizer_iff] at h2
    exact hZ n fun g => Subtype.ext (h2 g g.2)
  have hrange : (φ.comp N.subtype).range = N.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardI : Nat.card ↥(N.map φ) = Nat.card ↥N := by
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  set P : Subgroup G := N ⊔ φ.ker with hP
  have hPidx : P.index ≤ 2 := by
    have h1 := Subgroup.index_map N φ
    have h2 := Subgroup.index_mul_card (N.map φ)
    rw [hcardI] at h2
    have h3 : P.index * φ.range.index * Nat.card ↥N ≤ 2 * Nat.card ↥N := by
      calc P.index * φ.range.index * Nat.card ↥N = (N.map φ).index * Nat.card ↥N := by
            rw [h1]
        _ = Nat.card (MulAut ↥N) := h2
        _ ≤ 2 * Nat.card ↥N := hAut
    have h4 : P.index * φ.range.index ≤ 2 := Nat.le_of_mul_le_mul_right h3 Nat.card_pos
    have h5 : 0 < φ.range.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    calc P.index = P.index * 1 := (mul_one _).symm
      _ ≤ P.index * φ.range.index := Nat.mul_le_mul_left _ h5
      _ ≤ 2 := h4
  have hPne : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hX : (P ⊔ S).index = 1 := by
    have d1 : (P ⊔ S).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_right
    have d2 : (P ⊔ S).index ∣ P.index := Subgroup.index_dvd_of_le le_sup_left
    have hcases : P.index = 1 ∨ P.index = 2 := by omega
    rcases hcases with h1 | h1
    · rw [h1] at d2
      exact Nat.dvd_one.1 d2
    · rw [h1] at d2
      rcases (Nat.dvd_prime Nat.prime_two).1 d2 with h2 | h2
      · exact h2
      · exact absurd (h2 ▸ d1) hS
  have hXtop : P ⊔ S = ⊤ := Subgroup.index_eq_one.1 hX
  intro g
  have hg : g ∈ P ⊔ S := by rw [hXtop]; trivial
  have : φ.ker.Normal := MonoidHom.normal_ker φ
  have : P.Normal := by rw [hP]; infer_instance
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
  obtain ⟨p, hp, s, hs, rfl⟩ := hg
  have hp' : p ∈ φ.ker ⊔ N := by rw [sup_comm]; exact hp
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hp'
  obtain ⟨k, hk, n, hn, rfl⟩ := hp'
  refine ⟨k, ?_, n * s, Subgroup.mul_mem_sup hn hs, by group⟩
  rw [← hker]
  exact hk


section PartB

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem loc_two_le (h : LocCfg Γ Λ S V) {k : ℕ} (hk : rk Y = k * rk ↥V) : 2 ≤ k := by
  by_contra hk2
  push Not at hk2
  have hle : rk Y ≤ rk ↥V := by
    rw [hk]
    interval_cases k <;> simp
  apply h.ne
  refine eq_of_le_of_rk_le h.std.hyp.exp le_top ?_
  rw [rk_top]
  exact hle

theorem loc_A_data (h : LocCfg Γ Λ S V) {A : Subgroup (MulAut Y)}
    (hA : A ∈ QhatStar Γ) (hAS : A ≤ S) (hAf : ∀ a ∈ A, (∀ x ∈ Λ, a * x = x * a) → a = 1) :
    0 < rk ↥A ∧ A ≤ stabSub V ∧ A ⊓ centSub V = ⊥ ∧ IsElemAbelian2 (autSub A V) ∧
      rk ↥(autSub A V) = rk ↥A ∧
      autSub A V ≤ Subgroup.normalizer ((autSub Λ V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hA3⟩, -⟩ := QhatStar_spec hA
  have hAΓ : A ≤ Γ := hA2.1
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  have hLs : Λ ≤ stabSub V := le_stabSub_of_forall_mem (loc_irr_data h).1
  have hAs : A ≤ stabSub V := le_stabSub_of_forall_mem fun a ha => loc_S_inv h a (hAS ha)
  have hfaith := loc_faithful h
  have hAc : A ⊓ centSub V = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun a ha => ?_
    obtain ⟨haA, haC⟩ := ha
    refine hAf a haA fun x hx => ?_
    have hax : a * x * a⁻¹ ∈ Λ := hgn a (hAΓ haA) x hx
    have hcomm : a * x * a⁻¹ * x⁻¹ ∈ Λ ⊓ centSub V := by
      refine ⟨Λ.mul_mem hax (Λ.inv_mem hx), fun v hv => ?_⟩
      have hw : x⁻¹ v ∈ V := (loc_irr_data h).1 x⁻¹ (Λ.inv_mem hx) v hv
      have h1 : a (x⁻¹ v) = x⁻¹ v := haC _ hw
      have h2 : a⁻¹ (x⁻¹ v) = x⁻¹ v := by
        calc a⁻¹ (x⁻¹ v) = a⁻¹ (a (x⁻¹ v)) := by rw [h1]
          _ = x⁻¹ v := by simp
      have h3 : x (x⁻¹ v) = v := by simp
      show a (x (a⁻¹ (x⁻¹ v))) = v
      rw [h2, h3]
      exact haC v hv
    rw [hfaith, Subgroup.mem_bot] at hcomm
    have : a * x * a⁻¹ = x := by
      have := congrArg (· * x) hcomm
      simpa using this
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [this]
  have hEl : IsElemAbelian2 (autSub A V) := by
    refine ⟨fun φ hφ ψ hψ => ?_, fun φ hφ => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
      obtain ⟨g', hg', rfl⟩ := mem_autSub.1 hψ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA2.2.2.1 _ hg _ hg')
    · obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using hA2.2.2.2 _ hg)
      rw [this, map_one]
  have hcard := card_autSub_mul hAs
  rw [hAc, Subgroup.card_bot, mul_one] at hcard
  have hrk : rk ↥(autSub A V) = rk ↥A := by
    unfold rk
    rw [hcard]
  have key : ∀ φ ∈ autSub A V, ∀ ψ ∈ autSub Λ V, φ * ψ * φ⁻¹ ∈ autSub Λ V := by
    intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    obtain ⟨l, hl, rfl⟩ := mem_autSub.1 hψ
    refine mem_autSub.2 ⟨⟨g.1 * l.1 * g.1⁻¹, ?_⟩, hgn _ (hAΓ hg) _ hl, ?_⟩
    · exact (stabSub V).mul_mem ((stabSub V).mul_mem g.2 l.2) ((stabSub V).inv_mem g.2)
    · have e : (⟨g.1 * l.1 * g.1⁻¹, (stabSub V).mul_mem ((stabSub V).mul_mem g.2 l.2)
          ((stabSub V).inv_mem g.2)⟩ : stabSub V) = g * l * g⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
  refine ⟨hA2.rk_pos, hAs, hAc, hEl, hrk, ?_⟩
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    exact key φ hφ ψ hψ
  · intro hψ
    have := key φ⁻¹ ((autSub A V).inv_mem hφ) _ hψ
    have e : φ⁻¹ * (φ * ψ * φ⁻¹) * φ⁻¹⁻¹ = ψ := by group
    rwa [e] at this


theorem loc_mul_cent (h : LocCfg Γ Λ S V) (hZ : Subgroup.center ↥Λ = ⊥)
    (hAut : Nat.card (MulAut ↥Λ) ≤ 2 * Nat.card ↥Λ) :
    ∀ g ∈ Γ, ∃ c ∈ Γ, (∀ l ∈ Λ, c * l = l * c) ∧ ∃ x ∈ Λ ⊔ S, g = c * x := by
  classical
  have hΛΓ : Λ ≤ Γ := le_of_mem_cComp h.std.hyp.comp
  have hSΓ : S ≤ Γ := h.std.hyp.sylow.1
  have hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal ha) y).1 hy
  have : (Λ.subgroupOf Γ).Normal :=
    ⟨fun n hn g => hgn (g : MulAut Y) g.2 (n : MulAut Y) hn⟩
  let e : ↥(Λ.subgroupOf Γ) ≃* ↥Λ := Subgroup.subgroupOfEquivOfLe hΛΓ
  have hZ' : ∀ z : ↥(Λ.subgroupOf Γ), (∀ g : ↥(Λ.subgroupOf Γ), g * z = z * g) → z = 1 := by
    intro z hz
    have hmem : e z ∈ Subgroup.center ↥Λ := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg e (hz (e.symm y))
      simpa using h1
    rw [hZ, Subgroup.mem_bot] at hmem
    exact e.injective (by simpa using hmem)
  have hAut' : Nat.card (MulAut ↥(Λ.subgroupOf Γ)) ≤ 2 * Nat.card ↥(Λ.subgroupOf Γ) := by
    have h1 : Nat.card (MulAut ↥(Λ.subgroupOf Γ)) = Nat.card (MulAut ↥Λ) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    have h2 : Nat.card ↥(Λ.subgroupOf Γ) = Nat.card ↥Λ := Nat.card_congr e.toEquiv
    rw [h1, h2]
    exact hAut
  intro g hg
  obtain ⟨c, hc, x, hx, hgx⟩ :=
    d321k_sylow_mul_cent (Λ.subgroupOf Γ) (S.subgroupOf Γ) hZ' hAut' h.std.hyp.sylow.2.2 ⟨g, hg⟩
  refine ⟨(c : MulAut Y), c.2, fun l hl => ?_, (x : MulAut Y), ?_, congrArg Subtype.val hgx⟩
  · have h1 := (Subgroup.mem_centralizer_iff.1 hc) ⟨l, hΛΓ hl⟩ hl
    exact (congrArg Subtype.val h1).symm
  · have hx' : (x : MulAut Y) ∈ (Λ.subgroupOf Γ ⊔ S.subgroupOf Γ).map Γ.subtype := ⟨x, hx, rfl⟩
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hΛΓ,
      Subgroup.map_subgroupOf_eq_of_le hSΓ] at hx'

theorem d321k_iso_conj_of_out_two (h : LocCfg Γ Λ S V) (hZ : Subgroup.center ↥Λ = ⊥)
    (hAut : Nat.card (MulAut ↥Λ) ≤ 2 * Nat.card ↥Λ) :
    ∀ g ∈ Γ, XMod.Iso ↥Λ (V.map g.toMonoidHom) V := by
  intro g hg
  obtain ⟨c, hcΓ, hcc, x, hx, rfl⟩ := loc_mul_cent h hZ hAut g hg
  have hLs : Λ ≤ stabSub V := le_stabSub_of_forall_mem (loc_irr_data h).1
  have hSs : S ≤ stabSub V := le_stabSub_of_forall_mem (loc_S_inv h)
  have hxs : x ∈ stabSub V := (sup_le hLs hSs) hx
  have hmap : V.map (c * x).toMonoidHom = V.map c.toMonoidHom := by
    have h1 : (c * x).toMonoidHom = c.toMonoidHom.comp x.toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, map_eq_of_mem_stabSub hxs]
  rw [hmap]
  have hX : ∀ y ∈ Λ, ∀ z ∈ Subgroup.centralizer (Λ : Set (MulAut Y)), y * z = z * y :=
    fun y hy z hz => Subgroup.mem_centralizer_iff.1 hz y hy
  have hcmem : c ∈ Subgroup.centralizer (Λ : Set (MulAut Y)) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => (hcc l hl).symm
  have h2 := Z3A1.iso_smul_of_comm hX ⟨c, hcmem⟩ V
  exact XMod.Iso.symm (loc_isIrr h).1 h2


end PartB

end CFSG.Quasithin
