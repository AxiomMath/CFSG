module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Transport
public import CFSG.RankThree.GF2n.Stroth80.Sec93OmPfLinAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem propAGroup_strong {G : Type} [Group G] [Finite G]
    (Q Z V W SB SC Bp P : Subgroup G) (lam : ↥Z →* Multiplicative (ZMod 2)) (X Y : Set G)
    (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ a ∈ Q, Commute z a)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z) (hsq : ∀ a ∈ Q, a ^ 2 ∈ Z)
    (hnd : ∀ a ∈ Q, (∀ b ∈ Q, LamOrth Z lam a b) → a ∈ Z)
    (hZV : Z ≤ V) (hVQ : V ≤ Q) (hWQ : W ≤ Q) (hVab : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ = 1)
    (hWdef : ∀ a ∈ Q, a ∈ W ↔ ∀ v ∈ V, LamOrth Z lam a v) (hWsum : W = SB ⊔ SC ⊔ V)
    (hSBab : ∀ a ∈ SB, ∀ b ∈ SB, ⁅a, b⁆ = 1) (hSCab : ∀ a ∈ SC, ∀ b ∈ SC, ⁅a, b⁆ = 1)
    (hZBp : Z ≤ Bp) (hZP : Z ≤ P) (hBpQ : Bp ≤ Q) (hPQ : P ≤ Q) (hBpP : Bp ⊓ P = Z)
    (hnorm : ∀ g ∈ X ∪ Y, ∀ a ∈ Q, g * a * g⁻¹ ∈ Q)
    (hfix : ∀ g ∈ X ∪ Y, ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hQW : ∀ g ∈ X ∪ Y, ∀ a ∈ Q, ⁅g, a⁆ ∈ W) (hWV : ∀ g ∈ X ∪ Y, ∀ a ∈ W, ⁅g, a⁆ ∈ V)
    (hVZ : ∀ g ∈ X ∪ Y, ∀ a ∈ V, ⁅g, a⁆ ∈ Z)
    (hXB : ∀ x ∈ X, ∀ a ∈ SB, ⁅x, a⁆ ∈ Bp) (hXC : ∀ x ∈ X, ∀ a ∈ SC, ⁅x, a⁆ ∈ P)
    (hYP : ∀ y ∈ Y, ∀ a ∈ W, ⁅y, a⁆ ∈ P)
    (hXf : ∀ a ∈ SB, (∀ x ∈ X, ⁅x, a⁆ ∈ Z) → a ∈ V)
    (hYf : ∀ a ∈ SC, (∀ y ∈ Y, ⁅y, a⁆ ∈ Z) → a ∈ V) :
    (∀ x ∈ X, (∃ a ∈ SB, ⁅x, a⁆ ∉ Z) → ∃ y ∈ Y, ⁅x, y⁆ ∉ Q) ∧
    (∀ x ∈ X, (∀ a ∈ SB, ⁅x, a⁆ ∈ Z) → (∀ x' ∈ X, ⁅x, x'⁆ ∈ Q) → ∀ a ∈ Q, ⁅x, a⁆ ∈ V) := by
  classical
  let R₀ : Subgroup G := Subgroup.normalizer (Q : Set G) ⊓ Subgroup.centralizer (Z : Set G)
  have hmemR₀ : ∀ g : G, (∀ a ∈ Q, g * a * g⁻¹ ∈ Q) → (∀ z ∈ Z, g * z * g⁻¹ = z) → g ∈ R₀ := by
    intro g h1 h2
    refine ⟨Subgroup.mem_normalizer_fintype fun a ha => h1 a ha,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro z hz
    calc z * g = (g * z * g⁻¹) * g := by rw [h2 z hz]
      _ = g * z := by group
  have hnormR : ∀ r ∈ R₀, ∀ a ∈ Q, r * a * r⁻¹ ∈ Q := fun r hr a ha =>
    (Subgroup.mem_normalizer_iff.mp hr.1 a).mp ha
  have hfixR : ∀ r ∈ R₀, ∀ z ∈ Z, r * z * r⁻¹ = z := by
    intro r hr z hz
    have := Subgroup.mem_centralizer_iff.mp hr.2 z hz
    calc r * z * r⁻¹ = (z * r) * r⁻¹ := by rw [this]
      _ = z := by group
  have hQR : Q ≤ R₀ := fun c hc =>
    ⟨Subgroup.le_normalizer hc, Subgroup.mem_centralizer_iff.mpr fun z hz => (hZc z hz c hc).eq⟩
  have hsec : SecHyp R₀ Q Z :=
    ⟨hZQ, hcomm, hsq, fun r hr x hx => hnormR r hr x hx,
      fun r hr x hx => by rw [hfixR r hr x hx]; exact hx⟩
  obtain ⟨M, iM, iA, κ, hκ⟩ := exists_sectionModule hsec
  haveI : Finite M := hκ.finite
  letI : Module (ZMod 2) M := AddCommGroup.zmodModule (fun a => by
    rw [two_nsmul]; exact hκ.two a)
  haveI : FiniteDimensional (ZMod 2) M := Module.Finite.of_finite
  obtain ⟨f, hfnd, hfalt, hfκ⟩ := exists_lamForm lam hcomm hZc hκ hnd
  let Sub : Subgroup G → Submodule (ZMod 2) M := fun U =>
    AddSubgroup.toZModSubmodule 2 (secSub κ U)
  have hrep : ∀ x : M, ∃ a : ↥Q, Multiplicative.toAdd (κ a) = x := by
    intro x
    obtain ⟨a, ha⟩ := hκ.surj (Multiplicative.ofAdd x)
    exact ⟨a, by rw [ha]; rfl⟩
  have hmemU : ∀ U : Subgroup G, Z ≤ U → ∀ a : ↥Q,
      Multiplicative.toAdd (κ a) ∈ Sub U ↔ (a : G) ∈ U :=
    fun U hU a => toAdd_mem_secSub_iff hκ hU a
  have hmemS : ∀ (U : Subgroup G) (s : ↥Q), (s : G) ∈ U → Multiplicative.toAdd (κ s) ∈ Sub U :=
    fun U s hs => mem_secSub.2 ⟨s, hs, by rw [ofAdd_toAdd]⟩
  let lin : ↥R₀ → (M →ₗ[ZMod 2] M) := fun r =>
    AddMonoidHom.toZModLinearMap 2 (DistribSMul.toAddMonoidHom M r)
  have hlin : ∀ (r : ↥R₀) (x : M), lin r x = r • x := fun r x => rfl
  have hact : ∀ (r : ↥R₀) (a : ↥Q), lin r (Multiplicative.toAdd (κ a)) =
      Multiplicative.toAdd (κ ⟨(r : G) * a * (r : G)⁻¹, hnormR r r.2 a a.2⟩) := by
    intro r a
    have := hκ.act r a ⟨(r : G) * a * (r : G)⁻¹, hnormR r r.2 a a.2⟩ rfl
    rw [hlin, this, toAdd_ofAdd]
  have hcQ : ∀ r ∈ R₀, ∀ a ∈ Q, ⁅r, a⁆ ∈ Q := by
    intro r hr a ha
    rw [commutatorElement_def]
    exact Q.mul_mem (hnormR r hr a ha) (Q.inv_mem ha)
  have hsub : ∀ (r : ↥R₀) (a : ↥Q), lin r (Multiplicative.toAdd (κ a)) -
      Multiplicative.toAdd (κ a) = Multiplicative.toAdd (κ ⟨⁅(r : G), (a : G)⁆,
        hcQ r r.2 a a.2⟩) := by
    intro r a
    have e : (⟨⁅(r : G), (a : G)⁆, hcQ r r.2 a a.2⟩ : ↥Q) =
        ⟨(r : G) * a * (r : G)⁻¹, hnormR r r.2 a a.2⟩ * a⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [hact, e, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hZW : Z ≤ W := hZV.trans (by rw [hWsum]; exact le_sup_right)
  have hVW : V ≤ W := by rw [hWsum]; exact le_sup_right
  have hSBQ : SB ≤ Q := (show SB ≤ W by rw [hWsum]; exact le_sup_left.trans le_sup_left).trans hWQ
  have hSCQ : SC ≤ Q := (show SC ≤ W by rw [hWsum]; exact le_sup_right.trans le_sup_left).trans hWQ
  have horth : f.orthogonal (Sub V) = Sub W := by
    ext x
    obtain ⟨a, rfl⟩ := hrep x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    have h1 : (∀ n ∈ Sub V, f n (Multiplicative.toAdd (κ a)) = 0) ↔
        ∀ v : ↥Q, (v : G) ∈ V → comm2 lam hcomm v a = 0 := by
      constructor
      · intro h v hv
        rw [← hfκ]
        exact h _ ((hmemU V hZV v).2 hv)
      · intro h n hn
        obtain ⟨v, rfl⟩ := hrep n
        rw [hfκ]
        exact h v ((hmemU V hZV v).1 hn)
    refine (h1.trans ?_).trans (hmemU W hZW a).symm
    rw [hWdef a a.2]
    constructor
    · intro h v hv
      have := h ⟨v, hVQ hv⟩ hv
      rw [comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm] at this
      exact this
    · intro h v hv
      rw [comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm]
      exact h v hv
  have hsubW : Sub W = Sub SB ⊔ Sub SC ⊔ Sub V := by
    have : secSub κ W = secSub κ SB ⊔ secSub κ SC ⊔ secSub κ V := by
      rw [hWsum, secSub_sup (sup_le hSBQ hSCQ) hVQ, secSub_sup hSBQ hSCQ]
    show AddSubgroup.toZModSubmodule 2 (secSub κ W) = _
    rw [this, OrderIso.map_sup, OrderIso.map_sup]
  have hVW' : Sub V ≤ f.orthogonal (Sub V) := by
    rw [horth]
    exact (AddSubgroup.toZModSubmodule 2).monotone (secSub_mono hVW)
  have hBP : Sub Bp ⊓ Sub P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := hrep x
    have h1 := (hmemU Bp hZBp a).1 hx.1
    have h2 := (hmemU P hZP a).1 hx.2
    have h3 : (a : G) ∈ Z := by rw [← hBpP]; exact ⟨h1, h2⟩
    have h4 : κ a = 1 := (hκ.ker a).2 h3
    rw [h4, toAdd_one]
    exact Submodule.zero_mem _
  have hmemR : ∀ g ∈ X ∪ Y, g ∈ R₀ := fun g hg => hmemR₀ g (hnorm g hg) (hfix g hg)
  let X' : Set (M →ₗ[ZMod 2] M) := {T | ∃ g ∈ X, ∃ hg : g ∈ R₀, T = lin ⟨g, hg⟩}
  let Y' : Set (M →ₗ[ZMod 2] M) := {T | ∃ g ∈ Y, ∃ hg : g ∈ R₀, T = lin ⟨g, hg⟩}
  have hXY : ∀ T ∈ X' ∪ Y', ∃ g ∈ X ∪ Y, ∃ hg : g ∈ R₀, T = lin ⟨g, hg⟩ := by
    rintro T (⟨g, hg, hR, rfl⟩ | ⟨g, hg, hR, rfl⟩)
    · exact ⟨g, Or.inl hg, hR, rfl⟩
    · exact ⟨g, Or.inr hg, hR, rfl⟩
  have hkz : ∀ (r : ↥R₀) (a : ↥Q), ⁅(r : G), (a : G)⁆ ∈ Z →
      lin r (Multiplicative.toAdd (κ a)) = Multiplicative.toAdd (κ a) := by
    intro r a hz
    have h0 := hsub r a
    have h1 : κ ⟨⁅(r : G), (a : G)⁆, hcQ r r.2 a a.2⟩ = 1 := (hκ.ker _).2 hz
    rw [h1, toAdd_one] at h0
    exact sub_eq_zero.1 h0
  have hpres : ∀ g ∈ X' ∪ Y', ∀ a b, f (g a) (g b) = f a b := by
    intro T hT x y
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    obtain ⟨b, rfl⟩ := hrep y
    rw [hact, hact, hfκ, hfκ]
    unfold comm2
    have e : ⁅g * (a : G) * g⁻¹, g * (b : G) * g⁻¹⁆ = g * ⁅(a : G), (b : G)⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    congr 2
    exact Subtype.ext (by
      show ⁅g * (a : G) * g⁻¹, g * (b : G) * g⁻¹⁆ = ⁅(a : G), (b : G)⁆
      rw [e]
      exact hfixR g hR _ (hcomm _ a.2 _ b.2))
  have hQW' : ∀ g ∈ X' ∪ Y', ∀ a, g a - a ∈ f.orthogonal (Sub V) := by
    intro T hT x
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    rw [horth, hsub ⟨g, hR⟩ a]
    exact (hmemU W hZW _).2 (hQW g hg a a.2)
  have hWV' : ∀ g ∈ X' ∪ Y', ∀ a ∈ f.orthogonal (Sub V), g a - a ∈ Sub V := by
    intro T hT x hx
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    rw [horth] at hx
    have haW : (a : G) ∈ W := (hmemU W hZW a).1 hx
    rw [hsub ⟨g, hR⟩ a]
    exact (hmemU V hZV _).2 (hWV g hg a haW)
  have hV' : ∀ g ∈ X' ∪ Y', ∀ a ∈ Sub V, g a = a := by
    intro T hT x hx
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    exact hkz ⟨g, hR⟩ a (hVZ g hg a ((hmemU V hZV a).1 hx))
  have hXB' : ∀ x ∈ X', ∀ a ∈ Sub SB, x a - a ∈ Sub Bp := by
    rintro T ⟨g, hg, hR, rfl⟩ x hx
    obtain ⟨s, hsSB, hs⟩ := mem_secSub.1 hx
    have hsa : Multiplicative.toAdd (κ s) = x := by rw [hs]; rfl
    rw [← hsa, hsub ⟨g, hR⟩ s]
    exact (hmemU Bp hZBp _).2 (hXB g hg s hsSB)
  have hXC' : ∀ x ∈ X', ∀ a ∈ Sub SC, x a - a ∈ Sub P := by
    rintro T ⟨g, hg, hR, rfl⟩ x hx
    obtain ⟨s, hsSC, hs⟩ := mem_secSub.1 hx
    have hsa : Multiplicative.toAdd (κ s) = x := by rw [hs]; rfl
    rw [← hsa, hsub ⟨g, hR⟩ s]
    exact (hmemU P hZP _).2 (hXC g hg s hsSC)
  have hYP' : ∀ y ∈ Y', ∀ a ∈ f.orthogonal (Sub V), y a - a ∈ Sub P := by
    rintro T ⟨g, hg, hR, rfl⟩ x hx
    obtain ⟨a, rfl⟩ := hrep x
    rw [horth] at hx
    rw [hsub ⟨g, hR⟩ a]
    exact (hmemU P hZP _).2 (hYP g hg a ((hmemU W hZW a).1 hx))
  have hXf' : ∀ a ∈ Sub SB, (∀ x ∈ X', x a = a) → a ∈ Sub V := by
    intro a ha hall
    obtain ⟨s, hsSB, hs⟩ := mem_secSub.1 ha
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsV : (s : G) ∈ V := by
      apply hXf s hsSB
      intro g hg
      have h1 := hall (lin ⟨g, hmemR g (Or.inl hg)⟩) ⟨g, hg, hmemR g (Or.inl hg), rfl⟩
      rw [← hsa] at h1
      have h2 := hsub ⟨g, hmemR g (Or.inl hg)⟩ s
      rw [h1, sub_self] at h2
      have h3 : κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inl hg)) s s.2⟩ = 1 := by
        have : Multiplicative.toAdd (κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inl hg)) s s.2⟩) = 0 :=
          h2.symm
        simpa using this
      exact (hκ.ker _).1 h3
    exact mem_secSub.2 ⟨s, hsV, hs⟩
  have hYf' : ∀ a ∈ Sub SC, (∀ y ∈ Y', y a = a) → a ∈ Sub V := by
    intro a ha hall
    obtain ⟨s, hsSC, hs⟩ := mem_secSub.1 ha
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsV : (s : G) ∈ V := by
      apply hYf s hsSC
      intro g hg
      have h1 := hall (lin ⟨g, hmemR g (Or.inr hg)⟩) ⟨g, hg, hmemR g (Or.inr hg), rfl⟩
      rw [← hsa] at h1
      have h2 := hsub ⟨g, hmemR g (Or.inr hg)⟩ s
      rw [h1, sub_self] at h2
      have h3 : κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inr hg)) s s.2⟩ = 1 := by
        have : Multiplicative.toAdd (κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inr hg)) s s.2⟩) = 0 :=
          h2.symm
        simpa using this
      exact (hκ.ker _).1 h3
    exact mem_secSub.2 ⟨s, hsV, hs⟩
  have hSBiso : ∀ a ∈ Sub SB, ∀ b ∈ Sub SB, f a b = 0 := by
    intro a ha b hb
    obtain ⟨s, hsSB, hs⟩ := mem_secSub.1 ha
    obtain ⟨s', hsSB', hs'⟩ := mem_secSub.1 hb
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsa' : Multiplicative.toAdd (κ s') = b := by rw [hs']; rfl
    rw [← hsa, ← hsa', hfκ, comm2_eq_zero_iff lam hcomm]
    refine ⟨hcomm _ s.2 _ s'.2, ?_⟩
    have : (⟨⁅(s : G), (s' : G)⁆, hcomm _ s.2 _ s'.2⟩ : ↥Z) = 1 :=
      Subtype.ext (hSBab _ hsSB _ hsSB')
    rw [this, map_one]
  have hSCiso : ∀ a ∈ Sub SC, ∀ b ∈ Sub SC, f a b = 0 := by
    intro a ha b hb
    obtain ⟨s, hsSC, hs⟩ := mem_secSub.1 ha
    obtain ⟨s', hsSC', hs'⟩ := mem_secSub.1 hb
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsa' : Multiplicative.toAdd (κ s') = b := by rw [hs']; rfl
    rw [← hsa, ← hsa', hfκ, comm2_eq_zero_iff lam hcomm]
    refine ⟨hcomm _ s.2 _ s'.2, ?_⟩
    have : (⟨⁅(s : G), (s' : G)⁆, hcomm _ s.2 _ s'.2⟩ : ↥Z) = 1 :=
      Subtype.ext (hSCab _ hsSC _ hsSC')
    rw [this, map_one]
  have hcommQ : ∀ (g₁ g₂ : G) (hR₁ : g₁ ∈ R₀) (hR₂ : g₂ ∈ R₀), ⁅g₁, g₂⁆ ∈ Q →
      lin ⟨g₁, hR₁⟩ ∘ₗ lin ⟨g₂, hR₂⟩ = lin ⟨g₂, hR₂⟩ ∘ₗ lin ⟨g₁, hR₁⟩ := by
    intro g₁ g₂ hR₁ hR₂ hc
    have hcR : ⁅g₁, g₂⁆ ∈ R₀ := hQR hc
    have hrel : (⟨g₁, hR₁⟩ : ↥R₀) * ⟨g₂, hR₂⟩ = ⟨⁅g₁, g₂⁆, hcR⟩ * (⟨g₂, hR₂⟩ * ⟨g₁, hR₁⟩) := by
      apply Subtype.ext
      show g₁ * g₂ = ⁅g₁, g₂⁆ * (g₂ * g₁)
      simp only [commutatorElement_def]; group
    have htriv : ∀ x : M, (⟨⁅g₁, g₂⁆, hcR⟩ : ↥R₀) • x = x := by
      intro x
      obtain ⟨a, rfl⟩ := hrep x
      have h1 := hact ⟨⁅g₁, g₂⁆, hcR⟩ a
      rw [hlin] at h1
      rw [h1]
      congr 1
      show _ = _
      have h2 : κ ⟨⁅g₁, g₂⁆ * (a : G) * ⁅g₁, g₂⁆⁻¹, hnormR _ hcR a a.2⟩ = κ a := by
        rw [hκ.eq_iff]
        have := hcomm _ hc _ a.2
        simpa [commutatorElement_def, mul_assoc] using this
      rw [h2]
    ext x
    show (⟨g₁, hR₁⟩ : ↥R₀) • ((⟨g₂, hR₂⟩ : ↥R₀) • x) = (⟨g₂, hR₂⟩ : ↥R₀) • ((⟨g₁, hR₁⟩ : ↥R₀) • x)
    calc (⟨g₁, hR₁⟩ : ↥R₀) • ((⟨g₂, hR₂⟩ : ↥R₀) • x)
        = ((⟨g₁, hR₁⟩ : ↥R₀) * ⟨g₂, hR₂⟩) • x := (mul_smul _ _ _).symm
      _ = ((⟨⁅g₁, g₂⁆, hcR⟩ : ↥R₀) * ((⟨g₂, hR₂⟩ : ↥R₀) * ⟨g₁, hR₁⟩)) • x := by rw [hrel]
      _ = (⟨⁅g₁, g₂⁆, hcR⟩ : ↥R₀) • (((⟨g₂, hR₂⟩ : ↥R₀) * ⟨g₁, hR₁⟩) • x) := mul_smul _ _ _
      _ = ((⟨g₂, hR₂⟩ : ↥R₀) * ⟨g₁, hR₁⟩) • x := htriv _
      _ = (⟨g₂, hR₂⟩ : ↥R₀) • ((⟨g₁, hR₁⟩ : ↥R₀) • x) := mul_smul _ _ _

  refine ⟨?_, ?_⟩
  · rintro g₁ hg₁ ⟨a, haSB, haZ⟩
    have hR₁ : g₁ ∈ R₀ := hmemR g₁ (Or.inl hg₁)
    have haQ : a ∈ Q := hSBQ haSB
    have hmove : lin ⟨g₁, hR₁⟩ (Multiplicative.toAdd (κ ⟨a, haQ⟩)) ≠
        Multiplicative.toAdd (κ ⟨a, haQ⟩) := by
      intro h
      apply haZ
      have h0 := hsub ⟨g₁, hR₁⟩ ⟨a, haQ⟩
      rw [h, sub_self] at h0
      have h3 : κ ⟨⁅g₁, a⁆, hcQ g₁ hR₁ a haQ⟩ = 1 := by
        have : Multiplicative.toAdd (κ ⟨⁅g₁, a⁆, hcQ g₁ hR₁ a haQ⟩) = 0 := h0.symm
        simpa using this
      exact (hκ.ker _).1 h3
    obtain ⟨T, hT, hne'⟩ := (n12_strong_noncomm f hfnd hfalt (Sub V) (Sub SB) (Sub SC) (Sub Bp)
      (Sub P) hVW' (horth.trans hsubW) hSBiso hSCiso hBP X' Y' hpres hQW' hWV' hV' hXB' hXC'
      hYP' hXf' hYf').1 (lin ⟨g₁, hR₁⟩) ⟨g₁, hg₁, hR₁, rfl⟩
      ⟨Multiplicative.toAdd (κ ⟨a, haQ⟩), hmemS SB ⟨a, haQ⟩ haSB, hmove⟩
    obtain ⟨g₂, hg₂, hR₂, rfl⟩ := hT
    exact ⟨g₂, hg₂, fun hc => hne' (hcommQ g₁ g₂ hR₁ hR₂ hc)⟩
  · intro g₁ hg₁ hfixSB hcommX a haQ
    have hR₁ : g₁ ∈ R₀ := hmemR g₁ (Or.inl hg₁)
    have hfixT : ∀ b ∈ Sub SB, lin ⟨g₁, hR₁⟩ b = b := by
      intro b hb
      obtain ⟨s, hsSB, hs⟩ := mem_secSub.1 hb
      have hsa : Multiplicative.toAdd (κ s) = b := by rw [hs]; rfl
      rw [← hsa]
      exact hkz ⟨g₁, hR₁⟩ s (hfixSB s hsSB)
    have hcommT : ∀ x' ∈ X', lin ⟨g₁, hR₁⟩ ∘ₗ x' = x' ∘ₗ lin ⟨g₁, hR₁⟩ := by
      rintro T ⟨g', hg', hR', rfl⟩
      exact hcommQ g₁ g' hR₁ hR' (hcommX g' hg')
    have key := (n12_strong_noncomm f hfnd hfalt (Sub V) (Sub SB) (Sub SC) (Sub Bp) (Sub P)
      hVW' (horth.trans hsubW) hSBiso hSCiso hBP X' Y' hpres hQW' hWV' hV' hXB' hXC' hYP' hXf'
      hYf').2 (lin ⟨g₁, hR₁⟩) ⟨g₁, hg₁, hR₁, rfl⟩ hfixT hcommT (Multiplicative.toAdd (κ ⟨a, haQ⟩))
    have h0 := hsub ⟨g₁, hR₁⟩ ⟨a, haQ⟩
    rw [h0] at key
    exact (hmemU V hZV _).1 key

end CFSG.RankThree.GF2n.Stroth80
