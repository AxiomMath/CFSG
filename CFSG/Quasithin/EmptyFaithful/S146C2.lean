module

public import CFSG.Quasithin.EmptyFaithful.S146B0
public import CFSG.Quasithin.EmptyFaithful.S146R5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section TwoCoset

@[expose] def twoCoset (Z : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Z : Set G))
    (ha2 : a ^ 2 ∈ Z) : Subgroup G where
  carrier := {x | x ∈ Z ∨ x * a ∈ Z}
  one_mem' := Or.inl Z.one_mem
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (Z.mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact Z.mul_mem hx hy)
    · refine Or.inr ?_
      have h1 : a⁻¹ * y * a ∈ Z := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) y).mp hy
        |> fun h => by simpa using h
      have e : x * y * a = (x * a) * (a⁻¹ * y * a) := by group
      rw [e]
      exact Z.mul_mem hx h1
    · refine Or.inl ?_
      have h1 : a⁻¹ * (y * a) * a ∈ Z := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) (y * a)).mp hy
        simpa using this
      have h2 : (a ^ 2)⁻¹ ∈ Z := Z.inv_mem ha2
      have e : x * y = (x * a) * (a⁻¹ * (y * a) * a) * (a ^ 2)⁻¹ := by group
      rw [e]
      exact Z.mul_mem (Z.mul_mem hx h1) h2
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (Z.inv_mem hx)
    · refine Or.inr ?_
      have h1 : a * (x * a)⁻¹ * a⁻¹ ∈ Z := by
        have := (Subgroup.mem_normalizer_iff.mp ha _).mp (Z.inv_mem hx)
        simpa using this
      have e : x⁻¹ * a = (a * (x * a)⁻¹ * a⁻¹) * a ^ 2 := by group
      rw [e]
      exact Z.mul_mem h1 ha2

theorem mem_twoCoset {Z : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (Z : Set G))
    (ha2 : a ^ 2 ∈ Z) {x : G} : x ∈ twoCoset Z a ha ha2 ↔ x ∈ Z ∨ x * a ∈ Z := Iff.rfl

theorem le_twoCoset {Z : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (Z : Set G))
    (ha2 : a ^ 2 ∈ Z) : Z ≤ twoCoset Z a ha ha2 := fun _ hx => Or.inl hx

theorem mem_twoCoset_self {Z : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (Z : Set G))
    (ha2 : a ^ 2 ∈ Z) : a ∈ twoCoset Z a ha ha2 :=
  Or.inr (by
    have e : a * a = a ^ 2 := (pow_two a).symm
    rw [e]; exact ha2)

end TwoCoset

section Sec8

structure Sec8 (K Z U₁ : Subgroup G) : Prop where
  le : Z ≤ U₁
  norm : U₁ ≤ Subgroup.normalizer (Z : Set G)
  sq : ∀ a ∈ U₁, a ^ 2 ∈ Z
  comm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ Z
  card : Z.relIndex U₁ = 8
  KZ : K ≤ Subgroup.normalizer (Z : Set G)
  KU : K ≤ Subgroup.normalizer (U₁ : Set G)
  irr : ∀ W : Subgroup G, Z ≤ W → W ≤ U₁ → K ≤ Subgroup.normalizer (W : Set G) → W = Z ∨ W = U₁

variable {K Z U₁ : Subgroup G}

theorem Sec8.exists_nc (h : Sec8 K Z U₁) : ∃ k ∈ K, ∃ u ∈ U₁, k * u * k⁻¹ * u⁻¹ ∉ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haU, haZ⟩ : ∃ a ∈ U₁, a ∉ Z := by
    by_contra hh
    push Not at hh
    have h1 : Z.relIndex U₁ = 1 := Subgroup.relIndex_eq_one.mpr hh
    have h8 := h.card
    omega
  have haN := h.norm haU
  have ha2 := h.sq a haU
  have hWU : twoCoset Z a haN ha2 ≤ U₁ := by
    rintro x (hx | hx)
    · exact h.le hx
    · have e : x = (x * a) * a⁻¹ := by group
      rw [e]
      exact U₁.mul_mem (h.le hx) (U₁.inv_mem haU)
  have key : ∀ k ∈ K, ∀ x ∈ twoCoset Z a haN ha2, k * x * k⁻¹ ∈ twoCoset Z a haN ha2 := by
    intro k hk x hx
    have hxU := hWU hx
    have hc := hcon k hk x hxU
    rcases hx with hx | hx
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (h.KZ hk) x).mp hx)
    · refine Or.inr ?_
      have e : k * x * k⁻¹ * a = (k * x * k⁻¹ * x⁻¹) * (x * a) := by group
      rw [e]
      exact Z.mul_mem hc hx
  have hKW : K ≤ Subgroup.normalizer (twoCoset Z a haN ha2 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
    have h1 := key k⁻¹ (K.inv_mem hk) _ hx
    have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rwa [e] at h1
  rcases h.irr _ (le_twoCoset haN ha2) hWU hKW with hW | hW
  · exact haZ (by
      have := mem_twoCoset_self haN ha2
      rwa [hW] at this)
  · have hd : Z.relIndex U₁ ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨a, haU, fun b hb => ?_⟩
      rw [← hW] at hb
      exact hb.symm
    rw [h.card] at hd
    omega

theorem Sec8.centralizerMod_le (h : Sec8 K Z U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ u ∈ U₁, p * u * p⁻¹ * u⁻¹ ∈ Z) :
    centralizerMod Z K U₁ ≤ pCoreOf 2 K := by
  classical
  have hC₁K : centralizerMod Z K U₁ ≤ K := centralizerMod_le_left _ _ _
  have key : ∀ k ∈ K, ∀ c ∈ centralizerMod Z K U₁, k * c * k⁻¹ ∈ centralizerMod Z K U₁ := by
    intro k hk c hc
    obtain ⟨hcK, hcN, hcu⟩ := mem_centralizerMod.mp hc
    refine mem_centralizerMod.mpr ⟨K.mul_mem (K.mul_mem hk hcK) (K.inv_mem hk),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.KZ hk) hcN) (Subgroup.inv_mem _ (h.KZ hk)),
      fun u hu => ?_⟩
    have hu' : k⁻¹ * u * k ∈ U₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (h.KU (K.inv_mem hk)) u).mp hu
      simpa using this
    have hc' := hcu _ hu'
    have e : k * c * k⁻¹ * u * (k * c * k⁻¹)⁻¹ * u⁻¹ =
        k * (c * (k⁻¹ * u * k) * c⁻¹ * (k⁻¹ * u * k)⁻¹) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (h.KZ hk) _).mp hc'
  have hnormC : K ≤ Subgroup.normalizer ((centralizerMod Z K U₁ : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => key k hk c hc, fun hc => ?_⟩
    have h1 := key k⁻¹ (K.inv_mem hk) _ hc
    have e : k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c := by group
    rwa [e] at h1
  have hCn : ((centralizerMod Z K U₁).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC₁K).mpr hnormC
  set π : ↥K →* KBar K := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNn : (((centralizerMod Z K U₁).subgroupOf K).map π).Normal := Subgroup.Normal.map hCn π hπs
  have := hNn
  rcases hsimple.eq_bot_or_eq_top_of_normal (((centralizerMod Z K U₁).subgroupOf K).map π) with hbot | htop
  · intro x hx
    have hxK : x ∈ K := hC₁K hx
    have h1 : π ⟨x, hxK⟩ ∈ ((centralizerMod Z K U₁).subgroupOf K).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  · exfalso
    obtain ⟨k, hk, u, hu, hnc⟩ := h.exists_nc
    apply hnc
    have h1 : π ⟨k, hk⟩ ∈ ((centralizerMod Z K U₁).subgroupOf K).map π := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hck⟩ := h1
    have hp : (c : G)⁻¹ * k ∈ pCoreOf 2 K :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hck)
    have hcC : (c : G) ∈ centralizerMod Z K U₁ := Subgroup.mem_subgroupOf.mp hc
    obtain ⟨-, hcN, hcu⟩ := mem_centralizerMod.mp hcC
    have hz1 := hQ _ hp u hu
    have e : k * u * k⁻¹ * u⁻¹ =
        ((c : G) * ((c : G)⁻¹ * k * u * ((c : G)⁻¹ * k)⁻¹ * u⁻¹) * (c : G)⁻¹) *
          ((c : G) * u * (c : G)⁻¹ * u⁻¹) := by group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN _).mp hz1) (hcu u hu)

end Sec8

section Aut

theorem card_mulAut_of_card_eight {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (h8 : Nat.card W = 8) :
    Nat.card (MulAut W) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq
    (n := 3) (by rw [h8]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp [Fin.prod_univ_succ]

variable [Finite G] {K Z U₁ : Subgroup G}

omit [Finite G] in
theorem Sec8.isElemAbelian_tilde (h : Sec8 K Z U₁) : IsElemAbelian 2 (tildeOf Z U₁) :=
  isElemAbelian_secImg_normalizer h.comm h.sq

omit [Finite G] in
theorem Sec8.card_tilde (h : Sec8 K Z U₁) : Nat.card (tildeOf Z U₁) = 8 := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (le_refl Z) h.le h.norm
  have h2 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left, h.card] at h1
  exact h1

theorem Sec8.autOn_eq_top (h : Sec8 K Z U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ u ∈ U₁, p * u * p⁻¹ * u⁻¹ ∈ Z)
    (h168 : (pCoreOf 2 K).relIndex K = 168) :
    autOn (tildeOf Z K) (tildeOf Z U₁) = ⊤ := by
  have hC₁ := h.centralizerMod_le hsimple hQ
  have hcard := card_autOn_secImg (K := Z) (E := U₁) (X := K) h.KZ h.norm h.KU
  have hge : 168 ≤ (centralizerMod Z K U₁).relIndex K := by
    have hd := Subgroup.relIndex_dvd_of_le_left K hC₁
    rw [h168] at hd
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)) hd
  have hel := h.isElemAbelian_tilde
  have hAut : Nat.card (MulAut ↥(tildeOf Z U₁)) = 168 :=
    card_mulAut_of_card_eight (fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2))
      (fun a => Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2))
      h.card_tilde
  refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
  rw [hAut]
  exact hcard ▸ hge

@[expose] noncomputable def Sec8.rho (h : Sec8 K Z U₁) : ↥K →* MulAut ↥(tildeOf Z U₁) :=
  (conjAct (tildeOf Z U₁)).comp
    (((secMk (Subgroup.normalizer (Z : Set G)) Z).comp (Subgroup.inclusion h.KZ)).codRestrict
      (Subgroup.normalizer (tildeOf Z U₁ : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)))
      (fun k => secMk_mem_normalizer_secImg (a := Subgroup.inclusion h.KZ k) (h.KU k.2)))

omit [Finite G] in
theorem Sec8.rho_coe (h : Sec8 K Z U₁) (k : ↥K) (w : ↥(tildeOf Z U₁)) :
    ((h.rho k w : ↥(tildeOf Z U₁)) :
        SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion h.KZ k) * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion h.KZ k))⁻¹ :=
  conjAct_apply_coe' (tildeOf Z U₁) _ w

omit [Finite G] in
theorem Sec8.mem_centralizerMod_of_rho_eq_one (h : Sec8 K Z U₁) {k : ↥K} (hk : h.rho k = 1) :
    (k : G) ∈ centralizerMod Z K U₁ := by
  refine mem_centralizerMod.mpr ⟨k.2, h.KZ k.2, fun u hu => ?_⟩
  have hw : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, h.norm hu⟩ ∈ tildeOf Z U₁ :=
    secMk_mem_secImg (x := ⟨u, h.norm hu⟩) hu
  have h1 := congrArg (fun a : MulAut ↥(tildeOf Z U₁) =>
    ((a ⟨_, hw⟩ : ↥(tildeOf Z U₁)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z)) hk
  simp only [h.rho_coe, MulAut.one_apply] at h1
  have h2 : secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion h.KZ k) *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, h.norm hu⟩ =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, h.norm hu⟩ *
        secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion h.KZ k) :=
    mul_inv_eq_iff_eq_mul.mp h1
  exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (Z : Set G)) (B := Z)
    (x := Subgroup.inclusion h.KZ k) (y := ⟨u, h.norm hu⟩) h2

theorem Sec8.exists_rho_eq (h : Sec8 K Z U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ u ∈ U₁, p * u * p⁻¹ * u⁻¹ ∈ Z)
    (h168 : (pCoreOf 2 K).relIndex K = 168) (ψ : MulAut ↥(tildeOf Z U₁)) :
    ∃ k : ↥K, h.rho k = ψ := by
  have htop := h.autOn_eq_top hsimple hQ h168
  have hψ : ψ ∈ autOn (tildeOf Z K) (tildeOf Z U₁) := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨g, hgK, hg⟩ := mem_autOn_iff.mp hψ
  obtain ⟨x, hxK, hx⟩ := mem_secImg.mp hgK
  refine ⟨⟨(x : G), hxK⟩, ?_⟩
  rw [← hg]
  have hxg : (⟨secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion h.KZ ⟨(x : G), hxK⟩),
      secMk_mem_normalizer_secImg (a := Subgroup.inclusion h.KZ ⟨(x : G), hxK⟩) (h.KU hxK)⟩ :
      ↥(Subgroup.normalizer (tildeOf Z U₁ : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)))) =
        g := Subtype.ext hx
  exact congrArg (conjAct (tildeOf Z U₁)) hxg

theorem Sec8.false_of_twisted (h : Sec8 K Z U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ u ∈ U₁, p * u * p⁻¹ * u⁻¹ ∈ Z)
    (h168 : (pCoreOf 2 K).relIndex K = 168) {s : G} (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hout : KbarInducesOuter K s) (ψ : MulAut ↥(tildeOf Z U₁))
    (hψ : ∀ k : ↥K, ψ * h.rho k * ψ⁻¹ = h.rho (conjAct K ⟨s, hsK⟩ k)) : False := by
  obtain ⟨k₀, hk₀⟩ := h.exists_rho_eq hsimple hQ h168 ψ
  have hC := h.centralizerMod_le hsimple hQ
  have hr : ∀ x : ↥K, (k₀ : G) * x * (k₀ : G)⁻¹ * (s * (x : G) * s⁻¹)⁻¹ ∈ pCoreOf 2 K := by
    intro x
    have h1 := hψ x
    rw [← hk₀] at h1
    have h2 : h.rho (k₀ * x * k₀⁻¹ * (conjAct K ⟨s, hsK⟩ x)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      exact mul_inv_cancel _
    have h4 := hC (h.mem_centralizerMod_of_rho_eq_one h2)
    simpa [conjAct_apply_coe'] using h4
  have hk' : s⁻¹ * (k₀ : G) * s ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsK) (k₀ : G)).mp k₀.2
    simpa using this
  obtain ⟨x, hxK, hx⟩ := hout _ hk'
  apply hx
  have hP := hr ⟨x, hxK⟩
  have hPn := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K (K.inv_mem k₀.2)) _).mp hP
  have e : ⁅s * (s⁻¹ * (k₀ : G) * s)⁻¹, x⁆ =
      ((k₀ : G)⁻¹ * ((k₀ : G) * x * (k₀ : G)⁻¹ * (s * x * s⁻¹)⁻¹) * (k₀ : G)⁻¹⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (pCoreOf 2 K).inv_mem hPn

end Aut

section Twisted

variable {Γ : Type*} [Group Γ] [Finite Γ] {W E : Subgroup Γ} {c : Γ}

omit [Finite Γ] in
theorem eq_of_mul_eq_of_inf_eq_bot (hWE : W ⊓ E = ⊥) {w w' : Γ} (hw : w ∈ W) (hw' : w' ∈ W)
    {e e' : Γ} (he : e ∈ E) (he' : e' ∈ E) (h : w * e = w' * e') : w = w' := by
  have h1 : w'⁻¹ * w = e' * e⁻¹ := by
    calc w'⁻¹ * w = w'⁻¹ * (w * e) * e⁻¹ := by group
      _ = w'⁻¹ * (w' * e') * e⁻¹ := by rw [h]
      _ = e' * e⁻¹ := by group
  have h2 : w'⁻¹ * w ∈ W ⊓ E := ⟨W.mul_mem (W.inv_mem hw') hw, h1 ▸ E.mul_mem he' (E.inv_mem he)⟩
  rw [hWE, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2.symm

theorem exists_twisted_mulAut (hWE : W ⊓ E = ⊥) (hW2E : conjSub c W ⊓ E = ⊥)
    (hle : conjSub c W ≤ W ⊔ E) (hcomm : ∀ x ∈ W ⊔ E, ∀ y ∈ W ⊔ E, x * y = y * x) :
    ∃ ψ : MulAut ↥W, ∀ w : ↥W, ∃ e ∈ E, c * (w : Γ) * c⁻¹ = (ψ w : Γ) * e := by
  classical
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W E
    (fun x hx y hy => hcomm x (Subgroup.mem_sup_left hx) y (Subgroup.mem_sup_right hy))
  have hmemc : ∀ w : ↥W, c * (w : Γ) * c⁻¹ ∈ conjSub c W := fun w => by
    refine mem_conjSub.mpr ?_
    have e : c⁻¹ * (c * (w : Γ) * c⁻¹) * c = (w : Γ) := by group
    rw [e]
    exact w.2
  have hconj : ∀ w : ↥W, c * (w : Γ) * c⁻¹ ∈ W ⊔ E := fun w => hle (hmemc w)
  have hex : ∀ w : ↥W, ∃ w' : ↥W, ∃ e ∈ E, c * (w : Γ) * c⁻¹ = (w' : Γ) * e := by
    intro w
    have h1 : c * (w : Γ) * c⁻¹ ∈ (W : Set Γ) * (E : Set Γ) := by
      rw [← hset]; exact hconj w
    obtain ⟨w', hw', e, he, hwe⟩ := Set.mem_mul.mp h1
    exact ⟨⟨w', hw'⟩, e, he, hwe.symm⟩
  choose ψ₀ e he hψ₀ using hex
  have hmul : ∀ w₁ w₂ : ↥W, ψ₀ (w₁ * w₂) = ψ₀ w₁ * ψ₀ w₂ := by
    intro w₁ w₂
    apply Subtype.ext
    refine eq_of_mul_eq_of_inf_eq_bot hWE (ψ₀ (w₁ * w₂)).2 (W.mul_mem (ψ₀ w₁).2 (ψ₀ w₂).2)
      (he (w₁ * w₂)) (E.mul_mem (he w₁) (he w₂)) ?_
    have h1 : c * ((w₁ * w₂ : ↥W) : Γ) * c⁻¹ = (c * (w₁ : Γ) * c⁻¹) * (c * (w₂ : Γ) * c⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    have hc2 : (e w₁ : Γ) * (ψ₀ w₂ : Γ) = (ψ₀ w₂ : Γ) * e w₁ :=
      hcomm _ (Subgroup.mem_sup_right (he w₁)) _ (Subgroup.mem_sup_left (ψ₀ w₂).2)
    calc ((ψ₀ (w₁ * w₂) : ↥W) : Γ) * e (w₁ * w₂) = c * ((w₁ * w₂ : ↥W) : Γ) * c⁻¹ :=
          (hψ₀ (w₁ * w₂)).symm
      _ = (c * (w₁ : Γ) * c⁻¹) * (c * (w₂ : Γ) * c⁻¹) := h1
      _ = ((ψ₀ w₁ : Γ) * e w₁) * ((ψ₀ w₂ : Γ) * e w₂) := by rw [hψ₀ w₁, hψ₀ w₂]
      _ = (ψ₀ w₁ : Γ) * ((e w₁ : Γ) * (ψ₀ w₂ : Γ)) * e w₂ := by group
      _ = (ψ₀ w₁ : Γ) * ((ψ₀ w₂ : Γ) * e w₁) * e w₂ := by rw [hc2]
      _ = (((ψ₀ w₁ * ψ₀ w₂ : ↥W)) : Γ) * ((e w₁ : Γ) * e w₂) := by
        simp only [Subgroup.coe_mul]; group
  let ψh : ↥W →* ↥W := MonoidHom.mk' ψ₀ hmul
  have hinj : Function.Injective ψh := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hw' : ψ₀ w = 1 := hw
    have h1 : c * (w : Γ) * c⁻¹ = (e w : Γ) := by
      have := hψ₀ w
      rw [hw'] at this
      simpa using this
    have h2 : (e w : Γ) ∈ conjSub c W ⊓ E := ⟨h1 ▸ hmemc w, he w⟩
    rw [hW2E, Subgroup.mem_bot] at h2
    have h3 : c * (w : Γ) * c⁻¹ = 1 := h1.trans h2
    apply Subtype.ext
    simpa using h3
  have hbij : Function.Bijective ψh := ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  exact ⟨MulEquiv.ofBijective ψh hbij, fun w => ⟨e w, he w, hψ₀ w⟩⟩

omit [Finite Γ] in
theorem twisted_conj (hWE : W ⊓ E = ⊥) (ψ : MulAut ↥W)
    (hψ : ∀ w : ↥W, ∃ e ∈ E, c * (w : Γ) * c⁻¹ = (ψ w : Γ) * e) {g : Γ}
    (hgW : g ∈ Subgroup.normalizer (W : Set Γ)) (hg'W : c * g * c⁻¹ ∈ Subgroup.normalizer (W : Set Γ))
    (hg'E : c * g * c⁻¹ ∈ Subgroup.normalizer (E : Set Γ)) :
    ψ * conjAct W ⟨g, hgW⟩ * ψ⁻¹ = conjAct W ⟨c * g * c⁻¹, hg'W⟩ := by
  ext w
  have hw₀ : ψ (ψ⁻¹ w) = w := ψ.apply_symm_apply w
  set w₀ : ↥W := ψ⁻¹ w with hw₀def
  obtain ⟨e, he, hce⟩ := hψ w₀
  obtain ⟨e', he', hce'⟩ := hψ (conjAct W ⟨g, hgW⟩ w₀)
  have h1 : c * ((conjAct W ⟨g, hgW⟩ w₀ : ↥W) : Γ) * c⁻¹ =
      (c * g * c⁻¹) * (c * (w₀ : Γ) * c⁻¹) * (c * g * c⁻¹)⁻¹ := by
    rw [conjAct_apply_coe']
    group
  have h2 : (c * g * c⁻¹) * (c * (w₀ : Γ) * c⁻¹) * (c * g * c⁻¹)⁻¹ =
      ((c * g * c⁻¹) * (ψ w₀ : Γ) * (c * g * c⁻¹)⁻¹) * ((c * g * c⁻¹) * e * (c * g * c⁻¹)⁻¹) := by
    rw [hce]
    group
  have hmemW : (c * g * c⁻¹) * (ψ w₀ : Γ) * (c * g * c⁻¹)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp hg'W _).mp (ψ w₀).2
  have hmemE : (c * g * c⁻¹) * e * (c * g * c⁻¹)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp hg'E _).mp he
  have h3 := eq_of_mul_eq_of_inf_eq_bot hWE (ψ (conjAct W ⟨g, hgW⟩ w₀)).2 hmemW he' hmemE
    (by rw [← hce', h1, h2])
  show ((ψ (conjAct W ⟨g, hgW⟩ w₀) : ↥W) : Γ) = ((conjAct W ⟨c * g * c⁻¹, hg'W⟩ w : ↥W) : Γ)
  rw [h3, hw₀, conjAct_apply_coe']

end Twisted

end CFSG.Quasithin
