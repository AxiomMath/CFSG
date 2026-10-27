module

public import CFSG.Milestones.ASVolI.F45.Two
public import CFSG.Milestones.ASVolI.F4Conjugacy
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots

section Generic

variable {S G : Type} [Group S] [Group G] (f : S →* G) (hf : Function.Injective f)

noncomputable def burnsideF45_conjOn (hR : f.range.Normal) : G →* MulAut S :=
  (MulAut.congr (MonoidHom.ofInjective hf).symm).toMonoidHom.comp
    (@MulAut.conjNormal G _ f.range hR)

theorem burnsideF45_conjOn_apply (hR : f.range.Normal) (g : G) (s : S) :
    f (burnsideF45_conjOn f hf hR g s) = g * f s * g⁻¹ := by
  show f ((MonoidHom.ofInjective hf).symm
    (@MulAut.conjNormal G _ f.range hR g (MonoidHom.ofInjective hf s))) = _
  rw [MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

theorem burnsideF45_conjOn_injective (hR : f.range.index = 2)
    (hS : Subgroup.center S = ⊥) (hG : Subgroup.center G = ⊥) :
    Function.Injective (burnsideF45_conjOn f hf (Subgroup.normal_of_index_eq_two hR)) := by
  have hN : f.range.Normal := Subgroup.normal_of_index_eq_two hR
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hcent : ∀ s : S, g * f s = f s * g := by
    intro s
    have h1 := burnsideF45_conjOn_apply f hf hN g s
    rw [hg, MulAut.one_apply] at h1
    calc g * f s = (g * f s * g⁻¹) * g := by group
      _ = f s * g := by rw [← h1]
  have hZ : ∀ s : S, (∀ t : S, f s * f t = f t * f s) → s = 1 := by
    intro s hs
    have hsc : s ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun t =>
      hf (by rw [map_mul, map_mul]; exact (hs t).symm)
    rw [hS, Subgroup.mem_bot] at hsc
    exact hsc
  have hgc : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hcR : x * g * x⁻¹ * g⁻¹ ∈ f.range := by
      have e : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
      rw [e, Subgroup.mul_mem_iff_of_index_two hR]
      constructor
      · intro hx
        exact hN.conj_mem _ (f.range.inv_mem hx) g
      · intro hx
        have := hN.conj_mem _ hx g⁻¹
        simpa [mul_assoc] using f.range.inv_mem this
    obtain ⟨s, hs⟩ := hcR
    have hcomm : ∀ t : S, f s * f t = f t * f s := by
      intro t
      rw [hs]
      obtain ⟨t', ht'⟩ : x⁻¹ * f t * x ∈ f.range := by
        have := hN.conj_mem _ ⟨t, rfl⟩ x⁻¹
        simpa using this
      have h1 : g * (x⁻¹ * f t * x) = (x⁻¹ * f t * x) * g := by
        rw [← ht']; exact hcent t'
      have h2 : g⁻¹ * f t = f t * g⁻¹ := by
        have := hcent t
        calc g⁻¹ * f t = g⁻¹ * (f t * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * f t) * g⁻¹ := by rw [this]
          _ = f t * g⁻¹ := by group
      have h3 : x * g * x⁻¹ * f t = f t * (x * g * x⁻¹) := by
        calc x * g * x⁻¹ * f t = x * (g * (x⁻¹ * f t * x)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * f t * x) * g) * x⁻¹ := by rw [h1]
          _ = f t * (x * g * x⁻¹) := by group
      calc x * g * x⁻¹ * g⁻¹ * f t = x * g * x⁻¹ * (g⁻¹ * f t) := by group
        _ = x * g * x⁻¹ * (f t * g⁻¹) := by rw [h2]
        _ = (x * g * x⁻¹ * f t) * g⁻¹ := by group
        _ = (f t * (x * g * x⁻¹)) * g⁻¹ := by rw [h3]
        _ = f t * (x * g * x⁻¹ * g⁻¹) := by group
    have hs1 := hZ s hcomm
    rw [hs1, map_one] at hs
    have : x * g * x⁻¹ = g := by
      have := congrArg (fun z => z * g) hs
      simpa [mul_assoc] using this.symm
    calc x * g = (x * g * x⁻¹) * x := by group
      _ = g * x := by rw [this]
  rw [hG, Subgroup.mem_bot] at hgc
  rw [Subgroup.mem_bot]
  exact hgc

theorem burnsideF45_card_of_index_two [Finite G] (hf : Function.Injective f)
    (hR : f.range.index = 2) :
    Nat.card G = 2 * Nat.card S := by
  have h := Subgroup.card_mul_index f.range
  rw [hR, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at h
  omega

end Generic

section ExtEquiv

theorem burnsideF45_normalizer_inf_eq {G : Type} [Group G] [Finite G] {R P B : Subgroup G}
    (hR : R.index = 2) (hRs : IsSimpleGroup ↥R) (hPtop : P ≠ ⊤)
    (hPmax : ∀ X : Subgroup G, P < X → X = ⊤) (hBP : B < P) (hB : B ≠ ⊥) (hPR : ¬ P ≤ R) :
    Subgroup.normalizer ((R ⊓ P : Subgroup G) : Set G) = P := by
  haveI hRN : R.Normal := Subgroup.normal_of_index_eq_two hR
  have hle : P ≤ Subgroup.normalizer ((R ⊓ P : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxR, hxP⟩
      exact ⟨hRN.conj_mem x hxR g, P.mul_mem (P.mul_mem hg hxP) (P.inv_mem hg)⟩
    · rintro ⟨hxR, hxP⟩
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      refine ⟨?_, ?_⟩
      · rw [e]
        have := hRN.conj_mem _ hxR g⁻¹
        simpa [mul_assoc] using this
      · rw [e]
        exact P.mul_mem (P.mul_mem (P.inv_mem hg) hxP) hg
  have hne : Subgroup.normalizer ((R ⊓ P : Subgroup G) : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : ((R ⊓ P).subgroupOf R).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hg : (g : G) ∈ Subgroup.normalizer ((R ⊓ P : Subgroup G) : Set G) := by
        rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
    haveI := hRs
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ P).subgroupOf R) with h | h
    ·
      have hbot : R ⊓ P = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hx.1⟩ : ↥R) ∈ (R ⊓ P).subgroupOf R := hx
        rw [h, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this
      have h2 : R.relIndex P = 2 := burnsideF4h_g2_relIndex_eq_two hR hPR
      rw [← Subgroup.inf_relIndex_right, inf_comm, ← inf_comm, hbot, Subgroup.relIndex_bot_left] at h2
      have hBc : Nat.card B < Nat.card P := Subgroup.card_lt_of_lt hBP
      have hBd : Nat.card B ∣ Nat.card P := Subgroup.card_dvd_of_le hBP.le
      rw [h2] at hBc hBd
      have hB1 : Nat.card B = 1 := by
        have : Nat.card B ≠ 0 := Nat.card_pos.ne'
        rcases (Nat.dvd_prime Nat.prime_two).1 hBd with h1 | h1
        · exact h1
        · omega
      exact hB (Subgroup.eq_bot_of_card_eq B hB1)
    ·
      have hRP : R ≤ P := fun x hx => by
        have : (⟨x, hx⟩ : ↥R) ∈ (R ⊓ P).subgroupOf R := by rw [h]; exact Subgroup.mem_top _
        exact this.2
      have hlt : R < P := lt_of_le_of_ne hRP (fun h' => hPR (h' ▸ le_rfl))
      have hRmax : ∀ X : Subgroup G, R < X → X = ⊤ := by
        intro X hX
        obtain ⟨x, hxX, hxR⟩ := SetLike.exists_of_lt hX
        rw [eq_top_iff]
        intro g _
        by_cases hg : g ∈ R
        · exact hX.le hg
        · have : g * x⁻¹ ∈ R := by
            rw [Subgroup.mul_mem_iff_of_index_two hR]
            exact iff_of_false hg (fun h => hxR (by simpa using R.inv_mem h))
          have := X.mul_mem (hX.le this) hxX
          simpa using this
      exact hPtop (hRmax P hlt)
  rcases lt_or_eq_of_le hle with h | h
  · exact absurd (hPmax _ h) hne
  · exact h.symm

theorem burnsideF45_sylow_ne_bot {G : Type} [Group G] [Finite G] {R S : Subgroup G}
    (hR : R.index = 2) (hS : ChF.IsSylowOf 2 S ⊤) : S ≠ ⊥ := by
  intro h
  apply hS.2.2
  rw [h, Subgroup.relIndex_top_right, Subgroup.index_bot]
  have := Subgroup.card_mul_index R
  rw [hR] at this
  exact ⟨Nat.card R, by omega⟩

theorem burnsideF45_ext_equiv {S Gs E : Type} [Group S] [Group Gs] [Group E] [Finite Gs]
    [Finite E] (ι : S →* Gs) (hιinj : Function.Injective ι) (hιidx : ι.range.index = 2)
    (hS : Subgroup.center S = ⊥) (hGs : Subgroup.center Gs = ⊥) (hsimple : IsSimpleGroup S)
    (hcard : Nat.card (MulAut S) ≤ Nat.card Gs)
    {B₀ P₁ P₂ : Subgroup Gs} (hlie : IsLieParabolics 2 ⊤ B₀ P₁ P₂) (hB₀ : ¬ B₀ ≤ ι.range)
    {Gp M₁ M₂ : Subgroup E} (marking : S ≃* ↥Gp) [hN : Gp.Normal]
    (hcent : Subgroup.centralizer (Gp : Set E) = ⊥) (hGp : Gp ≠ ⊤)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (h1 : ∀ s : S, ((marking s : ↥Gp) : E) ∈ M₁ ↔ ι s ∈ P₁)
    (h2 : ∀ s : S, ((marking s : ↥Gp) : E) ∈ M₂ ↔ ι s ∈ P₂) :
    ∃ φ : E ≃* Gs, M₁.map φ.toMonoidHom = P₁ ∧ M₂.map φ.toMonoidHom = P₂ ∧
      (∀ s : S, φ (marking s) = ι s) ∧
      ∀ g : E, g ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) → g ∈ M₁ := by
  classical
  haveI hRN : ι.range.Normal := Subgroup.normal_of_index_eq_two hιidx
  haveI : Finite S := Finite.of_injective ι hιinj
  haveI : Finite (MulAut S) := Finite.of_injective (fun α : MulAut S => (α : S → S))
    fun _ _ h => MulEquiv.ext fun x => congrFun h x
  haveI := hsimple
  have hcinj := burnsideF45_conjOn_injective ι hιinj hιidx hS hGs
  let c : Gs ≃* MulAut S := MulEquiv.ofBijective _ (hcinj.bijective_of_nat_card_le hcard)
  have hc : ∀ (g : Gs) (x : S), ι (c g x) = g * ι x * g⁻¹ := fun g x =>
    burnsideF45_conjOn_apply ι hιinj _ g x
  let φ₀ : E →* MulAut S :=
    (MulAut.congr marking.symm).toMonoidHom.comp (@MulAut.conjNormal E _ Gp hN)
  have hφ₀ : ∀ (g : E) (x : S), ((marking (φ₀ g x) : ↥Gp) : E) = g * marking x * g⁻¹ := by
    intro g x
    show ((marking (marking.symm (@MulAut.conjNormal E _ Gp hN g (marking.symm.symm x))) :
      ↥Gp) : E) = _
    rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
    rfl
  let φm : E →* Gs := c.symm.toMonoidHom.comp φ₀
  have hext : ∀ s : S, φm (marking s) = ι s := by
    intro s
    show c.symm (φ₀ (marking s)) = ι s
    rw [MulEquiv.symm_apply_eq]
    ext x
    apply marking.injective
    apply Subtype.ext
    rw [hφ₀]
    have hx : ι (c (ι s) x) = ι (s * x * s⁻¹) := by rw [hc, map_mul, map_mul, map_inv]
    rw [hιinj hx, map_mul, map_mul, map_inv]
    rfl
  have hφinj : Function.Injective φm := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hg0 : φ₀ g = 1 := by
      have : c.symm (φ₀ g) = 1 := hg
      rw [MulEquiv.symm_apply_eq, map_one] at this
      exact this
    have hgc : g ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨x, hx⟩ := marking.surjective ⟨h, hh⟩
      have hxe : ((marking x : ↥Gp) : E) = h := by rw [hx]
      have e := hφ₀ g x
      rw [hg0, MulAut.one_apply, hxe] at e
      calc h * g = (g * h * g⁻¹) * g := by rw [← e]
        _ = g * h := by group
    rw [hcent] at hgc
    exact hgc
  have hcardGs : Nat.card Gs = 2 * Nat.card S := burnsideF45_card_of_index_two ι hιinj hιidx
  have hcardGp : Nat.card Gp = Nat.card S := (Nat.card_congr marking.toEquiv).symm
  have hidxGp : Gp.index = 2 := by
    have hle : Nat.card E ≤ Nat.card Gs := Nat.card_le_card_of_injective φm hφinj
    have hmul := Subgroup.card_mul_index Gp
    have hidx1 : Gp.index ≠ 1 := fun h => hGp (Subgroup.index_eq_one.1 h)
    have hpos : 0 < Nat.card S := Nat.card_pos
    have hidx0 : Gp.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hcardGp] at hmul
    rw [hcardGs, ← hmul] at hle
    have : Gp.index ≤ 2 := by
      by_contra hc'
      push Not at hc'
      have : Nat.card S * 3 ≤ Nat.card S * Gp.index := Nat.mul_le_mul_left _ hc'
      omega
    omega
  have hcardE : Nat.card E = Nat.card Gs := by
    have hmul := Subgroup.card_mul_index Gp
    rw [hidxGp, hcardGp] at hmul
    omega
  have hφbij : Function.Bijective φm := (Function.Injective.bijective_of_nat_card_le hφinj
    hcardE.ge)
  let φ : E ≃* Gs := MulEquiv.ofBijective φm hφbij
  have hφ : ∀ g, φ g = φm g := fun _ => rfl
  have hBP₁ : B₀ ≤ P₁ := hlie.2.2.1 ▸ inf_le_left
  have hBP₂ : B₀ ≤ P₂ := hlie.2.2.1 ▸ inf_le_right
  have hmax₁ := (hlie.2.2.2 P₁).2 (Or.inl rfl)
  have hmax₂ := (hlie.2.2.2 P₂).2 (Or.inr rfl)
  obtain ⟨Syl, hSyl, hBeq⟩ := hlie.1
  have hSB : Syl ≤ B₀ := by rw [hBeq]; exact le_inf hSyl.1 Subgroup.le_normalizer
  have hB0 : B₀ ≠ ⊥ := fun h => burnsideF45_sylow_ne_bot hιidx hSyl
    (eq_bot_iff.2 (h ▸ hSB))
  haveI : IsSimpleGroup ↥ι.range := (MonoidHom.ofInjective hιinj).symm.isSimpleGroup
  have hnorm : ∀ {P : Subgroup Gs}, (B₀ ≤ P ∧ P ≤ ⊤ ∧ P ≠ ⊤ ∧
      ∀ R : Subgroup Gs, P < R → R ≤ ⊤ → R = ⊤) → P ≠ B₀ →
      Subgroup.normalizer ((ι.range ⊓ P : Subgroup Gs) : Set Gs) = P := by
    intro P hP hPB
    exact burnsideF45_normalizer_inf_eq hιidx inferInstance hP.2.2.1
      (fun X hX => hP.2.2.2 X hX le_top) (lt_of_le_of_ne hP.1 (Ne.symm hPB)) hB0
      (fun h => hB₀ (hP.1.trans h))
  have hP₁B : P₁ ≠ B₀ := by
    intro h
    apply hlie.2.1
    have : P₁ ≤ P₂ := h ▸ hBP₂
    have hmx := hmax₁.2.2.2 P₂ (lt_of_le_of_ne this hlie.2.1) le_top
    exact absurd hmx hmax₂.2.2.1
  have hP₂B : P₂ ≠ B₀ := by
    intro h
    apply hlie.2.1
    have : P₂ ≤ P₁ := h ▸ hBP₁
    have hmx := hmax₂.2.2.2 P₁ (lt_of_le_of_ne this hlie.2.1.symm) le_top
    exact absurd hmx hmax₁.2.2.1
  have hmapGp : ∀ {M : Subgroup E} {P : Subgroup Gs},
      (∀ s : S, ((marking s : ↥Gp) : E) ∈ M ↔ ι s ∈ P) →
      (Gp ⊓ M).map φ.toMonoidHom = ι.range ⊓ P := by
    intro M P hMP
    ext y
    constructor
    · rintro ⟨g, ⟨hgGp, hgM⟩, rfl⟩
      obtain ⟨s, hs⟩ := marking.surjective ⟨g, hgGp⟩
      have hg : g = ((marking s : ↥Gp) : E) := by rw [hs]
      subst hg
      refine ⟨⟨s, (hext s).symm⟩, ?_⟩
      show φm (marking s) ∈ P
      rw [hext]
      exact (hMP s).1 hgM
    · rintro ⟨⟨s, rfl⟩, hsP⟩
      exact ⟨marking s, ⟨(marking s).2, (hMP s).2 hsP⟩, hext s⟩
  have hMnot : ∀ {M : Subgroup E}, M₁ ⊓ M₂ ≤ M → ¬ M ≤ Gp := by
    intro M hM hle
    apply hGp
    rw [eq_top_iff]
    intro e _
    obtain ⟨n, hn, h, hh, rfl⟩ := hsplit e
    exact Gp.mul_mem hn (hle (hM hh))
  have hmapM : ∀ {M : Subgroup E} {P : Subgroup Gs},
      (∀ s : S, ((marking s : ↥Gp) : E) ∈ M ↔ ι s ∈ P) → M₁ ⊓ M₂ ≤ M →
      Subgroup.normalizer ((ι.range ⊓ P : Subgroup Gs) : Set Gs) = P → B₀ ≤ P →
      M.map φ.toMonoidHom = P ∧
        ∀ g : E, g ∈ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) → g ∈ M := by
    intro M P hMP hM hNP hBP
    have hmap := hmapGp hMP
    have hNle : ∀ g : E, g ∈ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) → φ g ∈ P := by
      intro g hg
      rw [← hNP, Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_inv, ← map_mul, ← hmap, Subgroup.mem_map_equiv,
        Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      exact (Subgroup.mem_normalizer_iff.1 hg x)
    have hMN : M ≤ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxGp, hxM⟩
        exact ⟨hN.conj_mem x hxGp m, M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm)⟩
      · rintro ⟨hxGp, hxM⟩
        have e : x = m⁻¹ * (m * x * m⁻¹) * m := by group
        refine ⟨?_, ?_⟩
        · rw [e]
          have := hN.conj_mem _ hxGp m⁻¹
          simpa [mul_assoc] using this
        · rw [e]
          exact M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm
    have hle : M.map φ.toMonoidHom ≤ P := by
      rintro _ ⟨m, hm, rfl⟩
      exact hNle m (hMN hm)
    have hcM : Nat.card M = 2 * Nat.card ↥(Gp ⊓ M) := by
      have h2 := burnsideF4h_g2_relIndex_eq_two hidxGp (hMnot hM)
      have := Subgroup.relIndex_mul_card (H := Gp) (K := M)
      rw [h2] at this
      omega
    have hcP : Nat.card P = 2 * Nat.card ↥(ι.range ⊓ P) := by
      have h2 := burnsideF4h_g2_relIndex_eq_two hιidx (fun h => hB₀ (hBP.trans h))
      have := Subgroup.relIndex_mul_card (H := ι.range) (K := P)
      rw [h2] at this
      omega
    have hcmap : Nat.card ↥((Gp ⊓ M).map φ.toMonoidHom) = Nat.card ↥(Gp ⊓ M) :=
      Nat.card_congr ((Gp ⊓ M).equivMapOfInjective _ φ.injective).symm.toEquiv
    have hcMm : Nat.card ↥(M.map φ.toMonoidHom) = Nat.card M :=
      Nat.card_congr (M.equivMapOfInjective _ φ.injective).symm.toEquiv
    refine ⟨Subgroup.eq_of_le_of_card_ge hle ?_, fun g hg => ?_⟩
    · rw [hcMm, hcM, hcP, ← hmap, hcmap]
    · have hgP := hNle g hg
      have hMP' : M.map φ.toMonoidHom = P := Subgroup.eq_of_le_of_card_ge hle
        (by rw [hcMm, hcM, hcP, ← hmap, hcmap])
      rw [← hMP', Subgroup.mem_map_equiv] at hgP
      simpa using hgP
  obtain ⟨hM₁, hN₁⟩ := hmapM h1 inf_le_left (hnorm hmax₁ hP₁B) hBP₁
  obtain ⟨hM₂, -⟩ := hmapM h2 inf_le_right (hnorm hmax₂ hP₂B) hBP₂
  exact ⟨φ, hM₁, hM₂, hext, hN₁⟩

theorem burnsideF45_map_top_subtype {E X : Type} [Group E] [Group X] (e : E ≃* X)
    (H : Subgroup X) :
    (H.map (e.symm.trans (Subgroup.topEquiv : ↥(⊤ : Subgroup E) ≃* E).symm).toMonoidHom).map
      (⊤ : Subgroup E).subtype = H.map e.symm.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem burnsideF45_centralizer_top_eq_bot {E : Type} [Group E] {Gp : Subgroup E}
    (h : Subgroup.centralizer (Gp : Set E) = ⊥) :
    Subgroup.centralizer ((⊤ : Subgroup E) : Set E) = ⊥ := by
  rw [eq_bot_iff, ← h]
  exact Subgroup.centralizer_le (fun x _ => Subgroup.mem_top x)

theorem burnsideF45_dynkin_top {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} [hN : Gp.Normal]
    (hd : ∀ g : E, g ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) →
      g ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E))
    (hN₁ : ∀ g : E, g ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) → g ∈ M₁) :
    ∀ g : E, g ∈ Subgroup.normalizer (((⊤ : Subgroup E) ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) →
      g ∈ Subgroup.normalizer (((⊤ : Subgroup E) ⊓ M₁ : Subgroup E) : Set E) := by
  intro g hg
  rw [top_inf_eq] at hg ⊢
  have hg' : g ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro x
    constructor
    · rintro ⟨hxGp, hxM⟩
      exact ⟨hN.conj_mem x hxGp g, (hg x).1 hxM⟩
    · rintro ⟨hxGp, hxM⟩
      refine ⟨?_, (hg x).2 hxM⟩
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [e]
      have := hN.conj_mem _ hxGp g⁻¹
      simpa [mul_assoc] using this
  have hgM := hN₁ g (hd g hg')
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact M₁.mul_mem (M₁.mul_mem hgM hx) (M₁.inv_mem hgM)
  · intro hx
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e]
    exact M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hgM) hx) hgM

end ExtEquiv

section G2dCenter

open CFSG.Blueprint CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K]

theorem burnsideF45_g2_center_full : Subgroup.center (G2Native.FullModel K) = ⊥ :=
  burnsideF45_center_quotient_eq_bot CFSG.LieType.Chevalley.center_adjointGroup_eq_bot


theorem burnsideF45_g2_center_small (hK : Nat.card K = 2) :
    Subgroup.center (G2Native.SmallModel K) = ⊥ :=
  burnsideF45_center_quotient_eq_bot (burnsideF4h_g2_center_derived hK)

end G2dCenter

section G2d

open CFSG.Blueprint CFSG.Blueprint.Chevalley


variable {K : Type} [Field K] [Finite K]

theorem burnsideF45_g2_conj_bijective (hK : Nat.card K = 2) :
    Function.Bijective (burnsideF45_conjOn (burnsideF4h_g2_incl K hK)
      (burnsideF4h_g2_incl_injective hK)
      (Subgroup.normal_of_index_eq_two (burnsideF4h_g2_incl_index hK))) := by
  have hinj := burnsideF45_conjOn_injective (burnsideF4h_g2_incl K hK)
    (burnsideF4h_g2_incl_injective hK) (burnsideF4h_g2_incl_index hK)
    (burnsideF45_g2_center_small hK) burnsideF45_g2_center_full
  refine hinj.bijective_of_nat_card_le ?_
  rw [burnsideF45_card_of_index_two _ (burnsideF4h_g2_incl_injective hK)
    (burnsideF4h_g2_incl_index hK), burnsideF4h_g2_card_small hK,
    ← Nat.card_congr (MulAut.congr (burnsideF4h_g2_psi K hK)).toEquiv]
  exact card_mulAut_u33Pres_le

theorem burnsideF45_F43_G2d {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .G2d p f Gp M₁ M₂) : IsGenLie (MulAut ↥Gp) .G2 2 1 := by
  obtain ⟨hp, hf, -⟩ := hyp.model
  subst hp hf
  obtain ⟨K, fK, finK, hK, marking, -, -⟩ := burnsideF4gG2Two_chart_G2d hyp
  letI := fK
  haveI := finK
  refine ⟨Nat.prime_two, le_rfl, K, fK, finK, by rw [hK, pow_one], ⟨?_⟩⟩
  exact (MulAut.congr marking.symm).trans
    (MulEquiv.ofBijective _ (burnsideF45_g2_conj_bijective hK)).symm

end G2d

section G2dExt

open CFSG.Blueprint CFSG.Blueprint.Chevalley


theorem burnsideF45_F43_ext_G2d {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .G2d p f Gp M₁ M₂) (hGp : Gp ≠ ⊤) : HypF_4_4 .G2 2 1 ⊤ M₁ M₂ := by
  obtain ⟨hp, hf, -⟩ := hyp.model
  subst hp hf
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, fK, finK, hK, marking, hM1, hM2⟩ := burnsideF4gG2Two_chart_G2d hyp
  letI := fK
  haveI := finK
  have hfull := burnsideF4h_g2_full K 2 1 Nat.prime_two le_rfl (by rw [hK, pow_one])
  have hmem : ∀ (L : Subgroup (G2Native.Parent K)) (M : Subgroup E),
      M.subgroupOf Gp = G2Native.smallImage K marking L →
      ∀ s, ((marking s : ↥Gp) : E) ∈ M ↔
        burnsideF4h_g2_incl K hK s ∈ G2Native.fullLocal K L := by
    intro L M hML s
    rw [burnsideF4h_g2_incl_mem hK L s]
    have h0 : ((marking s : ↥Gp) : E) ∈ M ↔ marking s ∈ M.subgroupOf Gp := Iff.rfl
    rw [h0, hML]
    unfold G2Native.smallImage
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  haveI := CFSG.Quasithin.isSimpleGroup_u33Pres
  have hsimple : IsSimpleGroup (G2Native.SmallModel K) := (burnsideF4h_g2_psi K hK).symm.isSimpleGroup
  have hcard : Nat.card (MulAut (G2Native.SmallModel K)) ≤ Nat.card (G2Native.FullModel K) := by
    rw [burnsideF45_card_of_index_two _ (burnsideF4h_g2_incl_injective hK)
      (burnsideF4h_g2_incl_index hK), burnsideF4h_g2_card_small hK,
      ← Nat.card_congr (MulAut.congr (burnsideF4h_g2_psi K hK)).toEquiv]
    exact card_mulAut_u33Pres_le
  obtain ⟨φ, hφ1, hφ2, -, hφN⟩ := burnsideF45_ext_equiv (burnsideF4h_g2_incl K hK)
    (burnsideF4h_g2_incl_injective hK) (burnsideF4h_g2_incl_index hK)
    (burnsideF45_g2_center_small hK) burnsideF45_g2_center_full hsimple hcard hfull.1
    (burnsideF4h_g2_borel_not_le_range hK) marking hyp.centralizer_trivial hGp hyp.split
    (hmem _ M₁ hM1) (hmem _ M₂ hM2)
  have hM₁ : M₁ = (G2Native.fullLocal K (G2Native.pointParabolic K)).map φ.symm.toMonoidHom := by
    rw [← hφ1, Subgroup.map_map]
    simp
  have hM₂ : M₂ = (G2Native.fullLocal K (G2Native.lineParabolic K)).map φ.symm.toMonoidHom := by
    rw [← hφ2, Subgroup.map_map]
    simp
  have hB : M₁ ⊓ M₂ =
      (G2Native.fullLocal K (G2Native.positiveBorel K)).map φ.symm.toMonoidHom := by
    rw [hM₁, hM₂, ← Subgroup.map_inf_eq _ _ φ.symm.toMonoidHom φ.symm.injective, hfull.1.2.2.1]
  let mk : G2Native.FullModel K ≃* ↥(⊤ : Subgroup E) :=
    φ.symm.trans (Subgroup.topEquiv : ↥(⊤ : Subgroup E) ≃* E).symm
  let chart : NativeChart .G2 2 1 (⊤ : Subgroup E) :=
    { borel := (G2Native.fullImage K mk (G2Native.positiveBorel K)).map (⊤ : Subgroup E).subtype
      points := (G2Native.fullImage K mk (G2Native.pointParabolic K)).map
        (⊤ : Subgroup E).subtype
      lines := (G2Native.fullImage K mk (G2Native.lineParabolic K)).map (⊤ : Subgroup E).subtype
      longRoot := (G2Native.fullImage K mk (G2Native.longRoot K)).map (⊤ : Subgroup E).subtype
      shortRoot := (G2Native.fullImage K mk (G2Native.shortRoot K)).map
        (⊤ : Subgroup E).subtype
      coordinates := Or.inr (Or.inl ⟨rfl, Nat.prime_two, le_rfl, K, fK, finK,
        by rw [hK, pow_one], mk, rfl, rfl, rfl, rfl, rfl⟩) }
  have hmatch : chart.Matches M₁ M₂ := by
    refine ⟨?_, ?_, ?_⟩
    · show (⊤ : Subgroup E) ⊓ (M₁ ⊓ M₂) = ((G2Native.fullLocal K (G2Native.positiveBorel K)).map
        mk.toMonoidHom).map (⊤ : Subgroup E).subtype
      rw [burnsideF45_map_top_subtype, top_inf_eq, hB]
    · show (⊤ : Subgroup E) ⊓ M₁ = ((G2Native.fullLocal K (G2Native.pointParabolic K)).map
        mk.toMonoidHom).map (⊤ : Subgroup E).subtype
      rw [burnsideF45_map_top_subtype, top_inf_eq, hM₁]
    · show (⊤ : Subgroup E) ⊓ M₂ = ((G2Native.fullLocal K (G2Native.lineParabolic K)).map
        mk.toMonoidHom).map (⊤ : Subgroup E).subtype
      rw [burnsideF45_map_top_subtype, top_inf_eq, hM₂]
  exact ⟨⟨hyp.finite,
    ⟨Nat.prime_two, le_rfl, K, fK, finK, by rw [hK, pow_one], ⟨Subgroup.topEquiv.trans φ⟩⟩,
    Subgroup.normal_of_characteristic ⊤, burnsideF45_centralizer_top_eq_bot hyp.centralizer_trivial,
    hyp.gen, ⟨chart, hmatch⟩,
    fun e => ⟨e, Subgroup.mem_top e, 1, (M₁ ⊓ M₂).one_mem, (mul_one e).symm⟩,
    burnsideF45_dynkin_top hyp.dynkin hφN⟩, fun _ => rfl⟩

end G2dExt

section Tits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.Schreier.Tits


theorem burnsideF45_F43_Tits {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .Tits p f Gp M₁ M₂) : IsGenLie (MulAut ↥Gp) .F4tw 2 1 := by
  obtain ⟨hp, hf, -⟩ := hyp.model
  subst hp hf
  obtain ⟨K, fK, finK, charK, hscope, marking, -, -⟩ := burnsideF4gF4Two_chart_tits hyp
  letI := fK
  haveI := finK
  haveI := charK
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := hscope
  have hK : Nat.card K = 2 := by simpa using hK'
  obtain ⟨-, -, -, ι, hιinj, hιidx, -⟩ := burnsideF4h_titsParentAssembly K hscope
  have hZfull : Subgroup.center (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0)) = ⊥ :=
    burnsideF45_center_quotient_eq_bot (burnsideF4h_ree_center_trivial hK')
  obtain ⟨Φ, -⟩ := burnsideF4h_tits_gammaEquiv hK
  obtain ⟨Θ, -⟩ := burnsideF4h_tits_commutator_equiv (reeGroup K 0) Φ
  have hZ : Subgroup.center ↥⁅reeGroup K 0, reeGroup K 0⁆ = ⊥ :=
    burnsideF4h_tits_center_eq_bot_of_equiv Θ burnsideF4h_tits_center_titsD
  have hZsmall : Subgroup.center (DerivedCentralQuotient (reeGroup K 0)) = ⊥ :=
    burnsideF45_center_quotient_eq_bot hZ
  obtain ⟨eC, -⟩ := burnsideF4h_tits_exists_derivedEquiv (reeGroup K 0) _ rfl hZ
  have hinj := burnsideF45_conjOn_injective ι hιinj hιidx hZsmall hZfull
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [burnsideF45_card_of_index_two ι hιinj hιidx,
      Nat.card_congr (MulAut.congr (eC.trans Θ)).toEquiv, Nat.card_congr (eC.trans Θ).toEquiv]
    exact card_mulAut_titsD_le titsOuter_card_le_two)
  exact ⟨rfl, odd_one, Or.inl ⟨rfl, K, fK, finK, hK,
    ⟨(MulAut.congr marking.symm).trans (MulEquiv.ofBijective _ hbij).symm⟩⟩⟩


theorem burnsideF45_F43_ext_Tits {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .Tits p f Gp M₁ M₂) (hGp : Gp ≠ ⊤) : HypF_4_4 .F4tw 2 1 ⊤ M₁ M₂ := by
  obtain ⟨hp, hf, -⟩ := hyp.model
  subst hp hf
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, fK, finK, charK, hscope, marking, hM1, hM2⟩ := burnsideF4gF4Two_chart_tits hyp
  letI := fK
  haveI := finK
  haveI := charK
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := hscope
  have hK : Nat.card K = 2 := by simpa using hK'
  obtain ⟨-, -, -, ι, hιinj, hιidx, -, hB, hP1, hP2, -, -, hBi, -, -⟩ :=
    burnsideF4h_titsParentAssembly K hscope
  have hloc := burnsideF4h_reeOrderedLocals_core K 0 hscope
  have hZfull : Subgroup.center (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0)) = ⊥ :=
    burnsideF45_center_quotient_eq_bot (burnsideF4h_ree_center_trivial hK')
  obtain ⟨Φ, -⟩ := burnsideF4h_tits_gammaEquiv hK
  obtain ⟨Θ, -⟩ := burnsideF4h_tits_commutator_equiv (reeGroup K 0) Φ
  have hZ : Subgroup.center ↥⁅reeGroup K 0, reeGroup K 0⁆ = ⊥ :=
    burnsideF4h_tits_center_eq_bot_of_equiv Θ burnsideF4h_tits_center_titsD
  have hZsmall : Subgroup.center (DerivedCentralQuotient (reeGroup K 0)) = ⊥ :=
    burnsideF45_center_quotient_eq_bot hZ
  obtain ⟨eC, -⟩ := burnsideF4h_tits_exists_derivedEquiv (reeGroup K 0) _ rfl hZ
  haveI : IsSimpleGroup ↥titsD := titsD_simple
  have hsimple : IsSimpleGroup (DerivedCentralQuotient (reeGroup K 0)) := (eC.trans Θ).isSimpleGroup
  have hcard : Nat.card (MulAut (DerivedCentralQuotient (reeGroup K 0))) ≤
      Nat.card (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0)) := by
    rw [burnsideF45_card_of_index_two ι hιinj hιidx,
      Nat.card_congr (MulAut.congr (eC.trans Θ)).toEquiv, Nat.card_congr (eC.trans Θ).toEquiv]
    exact card_mulAut_titsD_le titsOuter_card_le_two
  have hι : ∀ {S' : Subgroup (DerivedCentralQuotient (reeGroup K 0))}
      {F : Subgroup (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0))},
      S'.map ι = ι.range ⊓ F → ∀ s, s ∈ S' ↔ ι s ∈ F := by
    intro S' F h s
    rw [← Subgroup.mem_map_iff_mem hιinj, h]
    exact ⟨fun h' => h'.2, fun h' => ⟨⟨s, rfl⟩, h'⟩⟩
  have hmem : ∀ (R : Subgroup (CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.F4 K))
      (M : Subgroup E)
      {F : Subgroup (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0))},
      M.subgroupOf Gp = (derivedImage (reeGroup K 0) R).map marking.toMonoidHom →
      (derivedImage (reeGroup K 0) R).map ι = ι.range ⊓ F →
      ∀ s, ((marking s : ↥Gp) : E) ∈ M ↔ ι s ∈ F := by
    intro R M F hMR hRF s
    have h0 : ((marking s : ↥Gp) : E) ∈ M ↔ marking s ∈ M.subgroupOf Gp := Iff.rfl
    rw [h0, hMR, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact hι hRF s
  have hB₀ : ¬ (NativeFrame.ree K 0).borel ≤ ι.range := by
    intro hle
    have h1 := hBi
    rw [hB, Subgroup.inf_relIndex_right, Subgroup.relIndex_eq_one.2 hle] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨φ, hφ1, hφ2, -, hφN⟩ := burnsideF45_ext_equiv ι hιinj hιidx hZsmall hZfull hsimple
    hcard hloc.1 hB₀ marking hyp.centralizer_trivial hGp hyp.split (hmem _ M₁ hM1 hP1)
    (hmem _ M₂ hM2 hP2)
  have hM₁ : M₁ = (NativeFrame.ree K 0).pointParabolic.map φ.symm.toMonoidHom := by
    rw [← hφ1, Subgroup.map_map]
    simp
  have hM₂ : M₂ = (NativeFrame.ree K 0).lineParabolic.map φ.symm.toMonoidHom := by
    rw [← hφ2, Subgroup.map_map]
    simp
  have hBB : M₁ ⊓ M₂ = (NativeFrame.ree K 0).borel.map φ.symm.toMonoidHom := by
    rw [hM₁, hM₂, ← Subgroup.map_inf_eq _ _ φ.symm.toMonoidHom φ.symm.injective, hloc.1.2.2.1]
  let mk : (↥(reeGroup K 0) ⧸ Subgroup.center ↥(reeGroup K 0)) ≃* ↥(⊤ : Subgroup E) :=
    φ.symm.trans (Subgroup.topEquiv : ↥(⊤ : Subgroup E) ≃* E).symm
  let chart : NativeChart .F4tw 2 1 (⊤ : Subgroup E) :=
    { borel := ((centralImage (reeGroup K 0) (reeBorel K 0)).map mk.toMonoidHom).map
        (⊤ : Subgroup E).subtype
      points := ((centralImage (reeGroup K 0) (reeParabolic K 0 1)).map mk.toMonoidHom).map
        (⊤ : Subgroup E).subtype
      lines := ((centralImage (reeGroup K 0) (reeParabolic K 0 0)).map mk.toMonoidHom).map
        (⊤ : Subgroup E).subtype
      longRoot := ((centralImage (reeGroup K 0) (reeLongRoot K 0)).map mk.toMonoidHom).map
        (⊤ : Subgroup E).subtype
      shortRoot := ((centralImage (reeGroup K 0) (reeShortRoot K 0)).map mk.toMonoidHom).map
        (⊤ : Subgroup E).subtype
      coordinates := Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, 0, K, fK, finK, charK, hscope,
        Or.inl ⟨rfl, rfl, mk, rfl, rfl, rfl, rfl, rfl⟩⟩))) }
  have hmatch : chart.Matches M₁ M₂ := by
    refine ⟨?_, ?_, ?_⟩
    · show (⊤ : Subgroup E) ⊓ (M₁ ⊓ M₂) = ((NativeFrame.ree K 0).borel.map
        mk.toMonoidHom).map (⊤ : Subgroup E).subtype
      rw [burnsideF45_map_top_subtype, top_inf_eq, hBB]
    · show (⊤ : Subgroup E) ⊓ M₁ = ((NativeFrame.ree K 0).pointParabolic.map
        mk.toMonoidHom).map (⊤ : Subgroup E).subtype
      rw [burnsideF45_map_top_subtype, top_inf_eq, hM₁]
    · show (⊤ : Subgroup E) ⊓ M₂ = ((NativeFrame.ree K 0).lineParabolic.map
        mk.toMonoidHom).map (⊤ : Subgroup E).subtype
      rw [burnsideF45_map_top_subtype, top_inf_eq, hM₂]
  exact ⟨⟨hyp.finite,
    ⟨rfl, odd_one, Or.inl ⟨rfl, K, fK, finK, hK, ⟨Subgroup.topEquiv.trans φ⟩⟩⟩,
    Subgroup.normal_of_characteristic ⊤, burnsideF45_centralizer_top_eq_bot hyp.centralizer_trivial,
    hyp.gen, ⟨chart, hmatch⟩,
    fun e => ⟨e, Subgroup.mem_top e, 1, (M₁ ⊓ M₂).one_mem, (mul_one e).symm⟩,
    burnsideF45_dynkin_top hyp.dynkin hφN⟩, fun _ => rfl⟩

end Tits

section Main


theorem as_F_4_3 : F_4_3 := by
  intro κ p f E _ Gp M₁ M₂ hyp
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · subst h
    exact burnsideF45_F43_G2d hyp
  · subst h
    exact burnsideF45_F43_Tits hyp
  · by_cases hκ : κ.IsLie
    · exact Or.inl ⟨κ, p, f, Gp, hκ, ⟨hyp, fun h => h.elim (fun h' => absurd h' hκ.1)
        (fun h' => absurd h' hκ.2)⟩⟩
    · have hκ' : κ = .G2d ∨ κ = .Tits := by
        cases κ <;> simp_all [GLKind.IsLie]
      by_cases hGp : Gp = ⊤
      · exact Or.inr ⟨hGp, hκ'⟩
      · left
        rcases hκ' with rfl | rfl
        · exact ⟨.G2, 2, 1, ⊤, by simp [GLKind.IsLie], burnsideF45_F43_ext_G2d hyp hGp⟩
        · exact ⟨.F4tw, 2, 1, ⊤, by simp [GLKind.IsLie], burnsideF45_F43_ext_Tits hyp hGp⟩

end Main

end CFSG.ASVolI
