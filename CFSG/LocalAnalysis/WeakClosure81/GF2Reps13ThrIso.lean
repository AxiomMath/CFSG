module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsSec
public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_stableUnder_bot {X : Subgroup (MulAut W)} :
    StableUnder X (⊥ : Subgroup W) := by
  intro x hx u hu
  rw [Subgroup.mem_bot] at hu ⊢
  rw [hu, map_one]

private theorem w16g_map_mul (U : Subgroup W) (g h : MulAut W) :
    (U.map g.toMonoidHom).map h.toMonoidHom = U.map (h * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem w16g_map_map_inv (U : Subgroup W) (g : MulAut W) :
    (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U := by
  rw [w16g_map_mul, inv_mul_cancel]
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext x; rfl
  rw [hone, Subgroup.map_id]

private theorem w16g_map_map_inv' (U : Subgroup W) (g : MulAut W) :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [w16g_map_mul, mul_inv_cancel]
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext x; rfl
  rw [hone, Subgroup.map_id]

private theorem w16g_isIrrOn_map_of_normalizes {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X)
    {U : Subgroup W} (hU : IsIrrOn X U ⊥) : IsIrrOn X (U.map g.toMonoidHom) ⊥ := by
  obtain ⟨hlt, hUstab, -, hirr⟩ := hU
  have hstab : StableUnder X (U.map g.toMonoidHom) :=
    stableUnder_map_of_normalizes hg' hUstab
  have hlt' : ⊥ < U.map g.toMonoidHom := by
    have h := (Subgroup.map_lt_map_iff_of_injective (f := g.toMonoidHom) g.injective
      (H := (⊥ : Subgroup W)) (K := U)).mpr hlt
    rwa [Subgroup.map_bot] at h
  refine ⟨hlt', hstab, w16g_stableUnder_bot, ?_⟩
  intro J hJstab hbotJ hJle
  have hJ'stab : StableUnder X (J.map (g⁻¹).toMonoidHom) :=
    stableUnder_map_of_normalizes (g := g⁻¹) (by simpa using hg) hJstab
  have hJ'le : J.map (g⁻¹).toMonoidHom ≤ U := by
    have h := Subgroup.map_mono (f := (g⁻¹).toMonoidHom) hJle
    rwa [w16g_map_map_inv] at h
  rcases hirr (J.map (g⁻¹).toMonoidHom) hJ'stab bot_le hJ'le with h | h
  · left
    have h' : (J.map (g⁻¹).toMonoidHom).map g.toMonoidHom = (⊥ : Subgroup W) := by
      rw [h, Subgroup.map_bot]
    rwa [w16g_map_map_inv'] at h'
  · right
    have h' : (J.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U.map g.toMonoidHom := by
      rw [h]
    rwa [w16g_map_map_inv'] at h'

private theorem w16g_secIsoOn_of_le {L N : Subgroup (MulAut W)} (hLN : L ≤ N)
    {A A₀ B B₀ : Subgroup W} (h : SecIsoOn N A A₀ B B₀) : SecIsoOn L A A₀ B B₀ := by
  obtain ⟨hA, hB, hSA, hSA₀, hSB, hSB₀, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  exact ⟨hA, hB, fun x hx => hSA x (hLN hx), fun x hx => hSA₀ x (hLN hx),
    fun x hx => hSB x (hLN hx), fun x hx => hSB₀ x (hLN hx), β, hβB, hβiff, hβsurj,
    fun x hx => hβeq x (hLN hx)⟩

private theorem w16g_exists_isIrrOn_le {X : Subgroup (MulAut W)} {C A : Subgroup W}
    (hCA : C < A) (hA : StableUnder X A) (hC : StableUnder X C) :
    ∃ J : Subgroup W, J ≤ A ∧ IsIrrOn X J C := by
  classical
  have hex : ∃ n, ∃ J : Subgroup W, J ≤ A ∧ C < J ∧ StableUnder X J ∧ Nat.card J = n :=
    ⟨_, A, le_rfl, hCA, hA, rfl⟩
  obtain ⟨J, hJA, hCJ, hJs, hJn⟩ := Nat.find_spec hex
  refine ⟨J, hJA, hCJ, hJs, hC, fun J' hJ's hCJ' hJ'J => ?_⟩
  by_cases h : J' = C
  · exact Or.inl h
  · right
    have hlt : C < J' := lt_of_le_of_ne hCJ' (Ne.symm h)
    have hmin := Nat.find_min' hex ⟨J', hJ'J.trans hJA, hlt, hJ's, rfl⟩
    rw [← hJn] at hmin
    exact Subgroup.eq_of_le_of_card_ge hJ'J hmin

private theorem w16g_secIsoOn_symm {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) : SecIsoOn X B ⊥ A ⊥ := by
  classical
  obtain ⟨-, -, hSA, -, hSB, -, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  have hβone : ∀ a : ↥A, β a = 1 ↔ (a : W) = 1 := fun a => by simpa using hβiff a
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥A) : W) = 1 := (hβone (a * b⁻¹)).mp h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have haux : ∀ b : ↥B, ∃ a : ↥A, β a = (b : W) := by
    intro b
    obtain ⟨a, ha⟩ := hβsurj (b : W) b.2
    exact ⟨a, mul_inv_eq_one.mp (by simpa using ha)⟩
  let aOf : ↥B → ↥A := fun b => Classical.choose (haux b)
  have haOf : ∀ b : ↥B, β (aOf b) = (b : W) := fun b => Classical.choose_spec (haux b)
  let γ : ↥B →* W :=
    { toFun := fun b => ((aOf b : ↥A) : W)
      map_one' := by
        have h1 : aOf 1 = 1 := by
          apply hβinj
          rw [haOf, map_one]
          rfl
        rw [h1]
        rfl
      map_mul' := by
        intro b b'
        have h1 : aOf (b * b') = aOf b * aOf b' := by
          apply hβinj
          rw [map_mul, haOf, haOf, haOf]
          rfl
        rw [h1]
        rfl }
  have hγ : ∀ b : ↥B, γ b = ((aOf b : ↥A) : W) := fun b => rfl
  refine ⟨bot_le, bot_le, hSB, w16g_stableUnder_bot, hSA, w16g_stableUnder_bot, γ, ?_, ?_,
    ?_, ?_⟩
  · intro b
    exact (aOf b).2
  · intro b
    rw [Subgroup.mem_bot, Subgroup.mem_bot, hγ]
    exact (hβone (aOf b)).symm.trans (by rw [haOf])
  · intro a ha
    refine ⟨⟨β ⟨a, ha⟩, hβB ⟨a, ha⟩⟩, ?_⟩
    have h1 : aOf ⟨β ⟨a, ha⟩, hβB ⟨a, ha⟩⟩ = ⟨a, ha⟩ := by
      apply hβinj
      rw [haOf]
    rw [hγ, h1, mul_inv_cancel]
    simp
  · intro x hx b b' hb'
    let a : ↥A := aOf b
    let a' : ↥A := aOf b'
    let a'' : ↥A := ⟨x (a : W), hSA x hx (a : W) a.2⟩
    have ha'' : (a'' : W) = x (a : W) := rfl
    have h1 : β a'' * (x (β a))⁻¹ ∈ ⊥ := hβeq x hx a a'' ha''
    have h2 : β a'' = x (β a) := mul_inv_eq_one.mp (by simpa using h1)
    have h3 : a'' = a' := by
      apply hβinj
      rw [h2, haOf b, haOf b']
      exact hb'.symm
    have h4 : ((aOf b' : ↥A) : W) = x ((aOf b : ↥A) : W) := by
      have h5 : (aOf b' : ↥A) = a'' := h3.symm
      rw [h5]
    have hgoal : γ b' * (x (γ b))⁻¹ = 1 := by
      rw [hγ b', hγ b, h4, mul_inv_cancel]
    simpa using hgoal

private theorem w16g_exists_image_of_secIsoOn {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) {V : Subgroup W} (hVA : V ≤ A) (hV : IsIrrOn X V ⊥) :
    ∃ V₀ : Subgroup W, V₀ ≤ B ∧ IsIrrOn X V₀ ⊥ ∧ SecIsoOn X V ⊥ V₀ ⊥ := by
  classical
  obtain ⟨-, -, hSA, -, hSB, -, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  have hβone : ∀ a : ↥A, β a = 1 ↔ (a : W) = 1 := fun a => by simpa using hβiff a
  let βV : ↥V →* W := β.comp (Subgroup.inclusion hVA)
  have hβVone : ∀ a : ↥V, βV a = 1 ↔ (a : W) = 1 := by
    intro a
    simpa [βV] using hβone (Subgroup.inclusion hVA a)
  have hβVbot : ∀ a : ↥V, βV a ∈ (⊥ : Subgroup W) ↔ (a : W) ∈ (⊥ : Subgroup W) := by
    intro a
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    exact hβVone a
  have hβVmem : ∀ (x : MulAut W) (hx : x ∈ X) (v : ↥V),
      βV ⟨x (v : W), hV.2.1 x hx (v : W) v.2⟩ = x (βV v) := by
    intro x hx v
    have h1 := hβeq x hx (Subgroup.inclusion hVA v)
      (Subgroup.inclusion hVA ⟨x (v : W), hV.2.1 x hx (v : W) v.2⟩) rfl
    exact mul_inv_eq_one.mp (by simpa [βV] using h1)
  have hV₀B : βV.range ≤ B := by
    rintro _ ⟨v, rfl⟩
    exact hβB _
  have hV₀ne : βV.range ≠ ⊥ := by
    intro hbot
    apply hV.1.ne'
    apply le_bot_iff.mp
    intro v hv
    have h1 : βV ⟨v, hv⟩ ∈ βV.range := ⟨_, rfl⟩
    rw [hbot] at h1
    have h2 : βV ⟨v, hv⟩ = 1 := Subgroup.mem_bot.mp h1
    have h3 : ((⟨v, hv⟩ : ↥V) : W) = 1 := (hβVone ⟨v, hv⟩).mp h2
    simpa using h3
  have hV₀stab : StableUnder X βV.range := by
    intro x hx w hw
    rcases hw with ⟨v, rfl⟩
    rw [← hβVmem x hx v]
    exact ⟨_, rfl⟩
  have hirrV₀ : IsIrrOn X βV.range ⊥ := by
    refine ⟨bot_lt_iff_ne_bot.mpr hV₀ne, hV₀stab, w16g_stableUnder_bot, ?_⟩
    intro J hJstab hbotJ hJle
    let K : Subgroup ↥V := J.comap βV
    have hJK : J = K.map βV := (Subgroup.map_comap_eq_self hJle).symm
    have hK'le : K.map (Subgroup.subtype V) ≤ V := by
      rintro _ ⟨k, -, rfl⟩
      exact k.2
    have hK'stab : StableUnder X (K.map (Subgroup.subtype V)) := by
      intro x hx w hw
      rcases Subgroup.mem_map.mp hw with ⟨k, hk, rfl⟩
      refine Subgroup.mem_map.mpr
        ⟨⟨x (k : W), hV.2.1 x hx (k : W) k.2⟩, ?_, rfl⟩
      change βV ⟨x (k : W), hV.2.1 x hx (k : W) k.2⟩ ∈ J
      rw [hβVmem x hx k]
      exact hJstab x hx (βV k) hk
    rcases hV.2.2.2 (K.map (Subgroup.subtype V)) hK'stab bot_le hK'le with hK' | hK'
    · left
      have hKbot : K = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective K (f := Subgroup.subtype V)
          (fun _ _ h => Subtype.ext h)).mp hK'
      rw [hJK, hKbot, Subgroup.map_bot]
    · right
      have hKtop : K = ⊤ := by
        ext k
        constructor
        · intro _; exact Subgroup.mem_top _
        · intro _
          have h1 : ((k : ↥V) : W) ∈ K.map (Subgroup.subtype V) := by
            rw [hK']
            exact k.2
          rcases Subgroup.mem_map.mp h1 with ⟨k₀, hk₀, hkeq⟩
          rw [← Subtype.ext hkeq]
          exact hk₀
      rw [hJK, hKtop, Subgroup.map_top]
  refine ⟨βV.range, hV₀B, hirrV₀, ?_⟩
  refine ⟨bot_le, bot_le, hV.2.1, w16g_stableUnder_bot, hV₀stab, w16g_stableUnder_bot,
    βV, ?_, hβVbot, ?_, ?_⟩
  · intro v
    exact ⟨v, rfl⟩
  · intro b hb
    rcases hb with ⟨v, rfl⟩
    exact ⟨v, by rw [mul_inv_cancel]; exact Subgroup.one_mem _⟩
  · intro x hx a a' ha'
    have h1 := hβeq x hx (Subgroup.inclusion hVA a) (Subgroup.inclusion hVA a')
      (by simpa using ha')
    simpa [βV] using h1

private theorem w16g_fixV_inf_commSub_eq_bot (hW : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} (hY : Odd (Nat.card Y)) : fixV Y ⊓ commSub ⊤ Y = ⊥ := by
  have h := (CFSG.Quasithin.B1.coprime_decomp hW hY (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _)).2
  rwa [top_inf_eq] at h

theorem s13_sSupIndep_of_pairwise_not_iso (hW : ∀ w : W, w * w = 1) (N : Subgroup (MulAut W))
    (𝒮 : Set (Subgroup W)) (hirr : ∀ U ∈ 𝒮, IsIrrOn N U ⊥)
    (hniso : ∀ U ∈ 𝒮, ∀ U' ∈ 𝒮, U ≠ U' → ¬ SecIsoOn N U ⊥ U' ⊥) : sSupIndep 𝒮 := by
  classical
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  rw [sSupIndep_iff]
  intro U
  rw [disjoint_iff]
  by_contra hne
  have hUirr : IsIrrOn N U.1 ⊥ := hirr U.1 U.2
  have hEq : (⨆ j, ⨆ (_ : j ≠ U), (j : Subgroup W))
      = ⨆ k : {j : ↥𝒮 // j ≠ U}, (k.1.1 : Subgroup W) := iSup_subtype'
  have hstabS : StableUnder N (⨆ j, ⨆ (_ : j ≠ U), (j : Subgroup W)) := by
    rw [hEq]
    exact stableUnder_iSup (fun k => (hirr k.1.1 k.1.2).2.1)
  have hsi : StableUnder N (U.1 ⊓ ⨆ j, ⨆ (_ : j ≠ U), (j : Subgroup W)) :=
    stableUnder_inf hUirr.2.1 hstabS
  have hle : U.1 ≤ ⨆ j, ⨆ (_ : j ≠ U), (j : Subgroup W) := by
    rcases hUirr.2.2.2 (U.1 ⊓ ⨆ j, ⨆ (_ : j ≠ U), (j : Subgroup W)) hsi bot_le
      inf_le_left with h | h
    · exact absurd h hne
    · exact h.ge.trans inf_le_right
  have hle' : U.1 ≤ ⊥ ⊔ ⨆ k : {j : ↥𝒮 // j ≠ U}, (k.1.1 : Subgroup W) := by
    rw [bot_sup_eq, ← hEq]
    exact hle
  obtain ⟨k, hiso, -⟩ := exists_secIsoOn_of_le_iSup (hW := fun w => by rw [pow_two]; exact hW w)
    hUirr (fun k : {j : ↥𝒮 // j ≠ U} => hirr k.1.1 k.1.2) hle'
  exact hniso U.1 U.2 k.1.1 k.1.2 (fun h => k.2 (Subtype.ext h.symm)) hiso

theorem sSupIndep_conjSubs_of_isotypic (hW : ∀ w : W, w * w = 1) (A N L : Subgroup (MulAut W))
    (hNA : N ≤ A) (hNn : ∀ g ∈ A, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hLN : L ≤ N) (U : Subgroup W)
    (hirr : IsIrrOn N U ⊥) (hiso : IsEntireIsotypic L U) : sSupIndep (conjSubs A U) := by
  classical
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  have hNinv : ∀ g ∈ A, ∀ x ∈ N, g⁻¹ * x * g ∈ N := by
    intro g hg x hx
    have h := hNn g⁻¹ (A.inv_mem hg) x hx
    simpa using h
  refine s13_sSupIndep_of_pairwise_not_iso hW N (conjSubs A U) ?_ ?_
  · rintro V ⟨g, hgA, rfl⟩
    exact w16g_isIrrOn_map_of_normalizes (hNn g hgA) (hNinv g hgA) hirr
  · rintro V ⟨g, hgA, rfl⟩ V' ⟨h, hhA, rfl⟩ hne hsec
    have hk : g⁻¹ * h ∈ A := A.mul_mem (A.inv_mem hgA) hhA
    have hsec' : SecIsoOn N U ⊥ (U.map (g⁻¹ * h).toMonoidHom) ⊥ := by
      have h' := secIsoOn_map (X := N) (g := g⁻¹) (by simpa using hNinv g hgA)
        (by simpa using hNn g hgA) hsec
      have e1 : (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U :=
        w16g_map_map_inv U g
      have e2 : (U.map h.toMonoidHom).map (g⁻¹).toMonoidHom
          = U.map (g⁻¹ * h).toMonoidHom := w16g_map_mul U h g⁻¹
      have e3 : (⊥ : Subgroup W).map (g⁻¹).toMonoidHom = ⊥ := Subgroup.map_bot _
      rw [e1, e2, e3] at h'
      exact h'
    have hUL : StableUnder L U := fun x hx => hirr.2.1 x (hLN hx)
    obtain ⟨V₀, hV₀U, hirrV₀⟩ :=
      w16g_exists_isIrrOn_le (X := L) hirr.1 hUL w16g_stableUnder_bot
    have hsecL : SecIsoOn L U ⊥ (U.map (g⁻¹ * h).toMonoidHom) ⊥ :=
      w16g_secIsoOn_of_le hLN hsec'
    obtain ⟨V₁, hV₁le, hirrV₁, hsecV⟩ :=
      w16g_exists_image_of_secIsoOn hsecL hV₀U hirrV₀
    have hsecV' : SecIsoOn L V₁ ⊥ V₀ ⊥ := w16g_secIsoOn_symm hsecV
    have hV₁U : V₁ ≤ U := hiso V₁ V₀ hV₀U hirrV₀ hirrV₁ hsecV'
    have hUk_irr : IsIrrOn N (U.map (g⁻¹ * h).toMonoidHom) ⊥ :=
      w16g_isIrrOn_map_of_normalizes (hNn (g⁻¹ * h) hk) (hNinv (g⁻¹ * h) hk) hirr
    have hinfstab : StableUnder N (U ⊓ U.map (g⁻¹ * h).toMonoidHom) :=
      stableUnder_inf hirr.2.1 hUk_irr.2.1
    have hinfne : U ⊓ U.map (g⁻¹ * h).toMonoidHom ≠ ⊥ := by
      intro hbot
      have hle : V₁ ≤ U ⊓ U.map (g⁻¹ * h).toMonoidHom := le_inf hV₁U hV₁le
      exact hirrV₁.1.ne' (le_bot_iff.mp (hbot ▸ hle))
    have hUle : U ≤ U.map (g⁻¹ * h).toMonoidHom := by
      rcases hirr.2.2.2 (U ⊓ U.map (g⁻¹ * h).toMonoidHom) hinfstab bot_le inf_le_left with h | h
      · exact absurd h hinfne
      · exact h.ge.trans inf_le_right
    have hmapU : U.map (g⁻¹ * h).toMonoidHom = U := by
      rcases hUk_irr.2.2.2 U hirr.2.1 bot_le hUle with h | h
      · exact absurd h hirr.1.ne'
      · exact h.symm
    have hgoal : U.map g.toMonoidHom = U.map h.toMonoidHom := by
      have hgh : g * (g⁻¹ * h) = h := by group
      have h1 : (U.map (g⁻¹ * h).toMonoidHom).map g.toMonoidHom = U.map h.toMonoidHom :=
        (w16g_map_mul U (g⁻¹ * h) g).trans
          (congrArg (fun k : MulAut W => U.map k.toMonoidHom) hgh)
      rwa [hmapU] at h1
    exact hne hgoal

theorem s13_isotypic_commSub (hW : ∀ w : W, w * w = 1) {Z : Subgroup (MulAut W)}
    (hZodd : Odd (Nat.card Z)) : IsEntireIsotypic Z (commSub ⊤ Z) := by
  intro V₁ V₀ hV₀ hIrr₀ hIrr₁ hsec
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hW w
  have hbot : fixV Z ⊓ commSub ⊤ Z = ⊥ := w16g_fixV_inf_commSub_eq_bot hW2 hZodd
  have hV₀bot : V₀ ⊓ fixV Z = ⊥ := by
    apply le_bot_iff.mp
    calc V₀ ⊓ fixV Z ≤ commSub ⊤ Z ⊓ fixV Z := inf_le_inf hV₀ le_rfl
      _ = fixV Z ⊓ commSub ⊤ Z := inf_comm _ _
      _ = ⊥ := hbot
  obtain ⟨-, -, -, -, -, -, β, hβV₀, hβiff, -, hβeq⟩ := hsec
  have hβone : ∀ a : ↥V₁, β a = 1 ↔ (a : W) = 1 := fun a => by simpa using hβiff a
  have hV₁bot : V₁ ⊓ fixV Z = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hβfix : β ⟨v, hv.1⟩ ∈ fixV Z := by
      rw [mem_fixV]
      intro z hz
      have h1 : β ⟨v, hv.1⟩ * (z (β ⟨v, hv.1⟩))⁻¹ ∈ (⊥ : Subgroup W) := by
        refine hβeq z hz ⟨v, hv.1⟩ ⟨v, hv.1⟩ ?_
        exact (mem_fixV.mp hv.2 z hz).symm
      exact (mul_inv_eq_one.mp (by simpa using h1)).symm
    have hmem : β ⟨v, hv.1⟩ ∈ V₀ ⊓ fixV Z := ⟨hβV₀ _, hβfix⟩
    rw [hV₀bot] at hmem
    have hβv1 : β ⟨v, hv.1⟩ = 1 := Subgroup.mem_bot.mp hmem
    have h1 : ((⟨v, hv.1⟩ : ↥V₁) : W) = 1 := (hβone _).mp hβv1
    simpa using h1
  have hdecomp := CFSG.Quasithin.B1.coprime_decomp hW2 hZodd (M := V₁) hIrr₁.2.1
  have hV₁eq : commSub V₁ Z = V₁ := by
    rw [hV₁bot, bot_sup_eq] at hdecomp
    exact hdecomp.1
  rw [← hV₁eq]
  exact commSub_mono le_top le_rfl

end CFSG.LocalAnalysis.WeakClosure81
