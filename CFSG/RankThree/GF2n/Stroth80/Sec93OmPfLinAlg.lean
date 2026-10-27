module

public import CFSG.RankThree.GF2n.Stroth80.Sec711PropA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open LinearMap Submodule

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

theorem n12_strong_noncomm
    (f : LinearMap.BilinForm (ZMod 2) E) (hf : f.Nondegenerate) (halt : f.IsAlt)
    (V SB SC B P : Submodule (ZMod 2) E)
    (hVW : V ≤ f.orthogonal V)
    (hWsum : f.orthogonal V = SB ⊔ SC ⊔ V)
    (hSBiso : ∀ a ∈ SB, ∀ b ∈ SB, f a b = 0) (hSCiso : ∀ a ∈ SC, ∀ b ∈ SC, f a b = 0)
    (hBP : B ⊓ P = ⊥)
    (X Y : Set (E →ₗ[ZMod 2] E))
    (hpres : ∀ g ∈ X ∪ Y, ∀ a b, f (g a) (g b) = f a b)
    (hQW : ∀ g ∈ X ∪ Y, ∀ a, g a - a ∈ f.orthogonal V)
    (hWV : ∀ g ∈ X ∪ Y, ∀ a ∈ f.orthogonal V, g a - a ∈ V)
    (hV : ∀ g ∈ X ∪ Y, ∀ a ∈ V, g a = a)
    (hXB : ∀ x ∈ X, ∀ a ∈ SB, x a - a ∈ B)
    (hXC : ∀ x ∈ X, ∀ a ∈ SC, x a - a ∈ P)
    (hYP : ∀ y ∈ Y, ∀ a ∈ f.orthogonal V, y a - a ∈ P)
    (hXfaith : ∀ a ∈ SB, (∀ x ∈ X, x a = a) → a ∈ V)
    (hYfaith : ∀ a ∈ SC, (∀ y ∈ Y, y a = a) → a ∈ V) :
    (∀ x ∈ X, (∃ a ∈ SB, x a ≠ a) → ∃ y ∈ Y, x ∘ₗ y ≠ y ∘ₗ x) ∧
    (∀ x ∈ X, (∀ a ∈ SB, x a = a) → (∀ x' ∈ X, x ∘ₗ x' = x' ∘ₗ x) → ∀ q, x q - q ∈ V) := by
  classical
  have hrefl : f.IsRefl := halt.isRefl
  have hn2 : ∀ z : ZMod 2, -z = z := by decide
  have h01 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  have hsym : ∀ a b, f a b = f b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    rw [eq_neg_of_add_eq_zero_left h, hn2]
  have hmemW : ∀ w, w ∈ f.orthogonal V ↔ ∀ v ∈ V, f v w = 0 := fun w => by
    simp [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.isOrtho_def]
  have hWW : ∀ z, (∀ a ∈ f.orthogonal V, f a z = 0) → z ∈ V := by
    intro z hz
    have : z ∈ f.orthogonal (f.orthogonal V) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact hz n hn
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hf hrefl] at this
  have hadj : ∀ g ∈ X ∪ Y, ∀ p, ∀ a ∈ f.orthogonal V, f (g p - p) a = f p (g a - a) := by
    intro g hg p a ha
    have h1 := hpres g hg p a
    have h0 : f (g p - p) (g a - a) = 0 := by
      rw [hsym]; exact (hmemW _).1 (hQW g hg p) _ (hWV g hg a ha)
    have hp : g p = p + (g p - p) := by abel
    have ha' : g a = a + (g a - a) := by abel
    rw [hp, ha'] at h1
    simp only [map_add, LinearMap.add_apply] at h1
    rw [h0, add_zero, add_assoc] at h1
    rw [eq_neg_of_add_eq_zero_left (add_eq_left.1 h1), hn2]
  have hSBW : SB ≤ f.orthogonal V := by rw [hWsum]; exact le_sup_left.trans le_sup_left
  have hSCW : SC ≤ f.orthogonal V := by rw [hWsum]; exact le_sup_right.trans le_sup_left
  have lag : ∀ S T : Submodule (ZMod 2) E, f.orthogonal V = S ⊔ T ⊔ V →
      (∀ a ∈ S, ∀ b ∈ S, f a b = 0) → (∀ a ∈ T, ∀ b ∈ T, f a b = 0) →
      ∀ w ∈ f.orthogonal V, (∀ t ∈ T, f t w = 0) → w ∈ T ⊔ V := by
    intro S T hST hS hT w hw hwT
    have hSW : S ≤ f.orthogonal V := by rw [hST]; exact le_sup_left.trans le_sup_left
    have hTW : T ≤ f.orthogonal V := by rw [hST]; exact le_sup_right.trans le_sup_left
    have hw' := hw
    rw [hST] at hw'
    obtain ⟨y, hy, v, hv, rfl⟩ := Submodule.mem_sup.1 hw'
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    have hsV : s ∈ V := by
      apply hWW
      intro a ha
      have ha' := ha
      rw [hST] at ha'
      obtain ⟨y', hy', v', hv', rfl⟩ := Submodule.mem_sup.1 ha'
      obtain ⟨s', hs', t', ht', rfl⟩ := Submodule.mem_sup.1 hy'
      have e1 : f s' s = 0 := hS _ hs' _ hs
      have e2 : f t' s = 0 := by
        have h := hwT t' ht'
        have h2 : f t' t = 0 := hT _ ht' _ ht
        have h3 : f t' v = 0 := by rw [hsym]; exact (hmemW t').1 (hTW ht') v hv
        simp only [map_add] at h
        linear_combination h - h2 - h3
      have e3 : f v' s = 0 := (hmemW s).1 (hSW hs) v' hv'
      simp only [map_add, LinearMap.add_apply, e1, e2, e3, add_zero]
    exact Submodule.mem_sup.2 ⟨t, ht, s + v, add_mem hsV hv, by abel⟩
  refine ⟨?_, ?_⟩
  ·
    rintro x hx ⟨a₀, ha₀, hxa⟩
    have hb₀P : x a₀ - a₀ ∉ P := by
      intro h
      apply hxa
      have hm : x a₀ - a₀ ∈ B ⊓ P := ⟨hXB x hx a₀ ha₀, h⟩
      rw [hBP] at hm
      exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hm)
    obtain ⟨q₁, hq₁P, hq₁b⟩ : ∃ q₁, (∀ p ∈ P, f p q₁ = 0) ∧ f (x a₀ - a₀) q₁ = 1 := by
      by_contra h
      push Not at h
      apply hb₀P
      have hm : x a₀ - a₀ ∈ f.orthogonal (f.orthogonal P) := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        rw [LinearMap.BilinForm.mem_orthogonal_iff] at hn
        by_contra hne0
        exact h n (fun p hp => hn p hp)
          (by rw [hsym]; exact h01 _ hne0)
      rwa [LinearMap.BilinForm.orthogonal_orthogonal hf hrefl] at hm
    have hw₁W : x q₁ - q₁ ∈ f.orthogonal V := hQW x (Or.inl hx) q₁
    have hw₁C : ∀ s ∈ SC, f s (x q₁ - q₁) = 0 := by
      intro s hs
      rw [hsym, hadj x (Or.inl hx) q₁ s (hSCW hs), hsym]
      exact hq₁P _ (hXC x hx s hs)
    have hw₁a₀ : f a₀ (x q₁ - q₁) = 1 := by
      rw [hsym, hadj x (Or.inl hx) q₁ a₀ (hSBW ha₀), hsym]
      exact hq₁b
    obtain ⟨s₁, hs₁, v₁, hv₁, hsv⟩ :=
      Submodule.mem_sup.1 (lag SB SC hWsum hSBiso hSCiso _ hw₁W hw₁C)
    have hs₁V : s₁ ∉ V := by
      intro hs₁V
      have hmV : x q₁ - q₁ ∈ V := hsv ▸ add_mem hs₁V hv₁
      have h0 := (hmemW a₀).1 (hSBW ha₀) _ hmV
      rw [hsym, hw₁a₀] at h0
      exact one_ne_zero h0
    obtain ⟨y, hy, hys⟩ : ∃ y ∈ Y, y s₁ ≠ s₁ := by
      by_contra h
      push Not at h
      exact hs₁V (hYfaith s₁ hs₁ h)
    have hyw₁ : y (x q₁ - q₁) - (x q₁ - q₁) ≠ 0 := by
      rw [← hsv, map_add, hV y (Or.inr hy) v₁ hv₁]
      intro h
      apply hys
      exact sub_eq_zero.1 (by rw [← h]; abel)
    have hyq₁ : y q₁ - q₁ ∈ V := by
      apply hWW
      intro a ha
      rw [hsym, hadj y (Or.inr hy) q₁ a ha, hsym]
      exact hq₁P _ (hYP y hy a ha)
    refine ⟨y, hy, fun hcomm => hyw₁ ?_⟩
    have h1 := LinearMap.congr_fun hcomm q₁
    simp only [LinearMap.comp_apply] at h1
    have hx' : x (y q₁) = x q₁ + (y q₁ - q₁) := by
      have h := hV x (Or.inl hx) _ hyq₁
      rw [map_sub] at h
      exact sub_eq_iff_eq_add'.1 h
    rw [map_sub, ← h1, hx']
    abel
  ·
    intro x hx hfix hcomm q
    have hxW : x q - q ∈ f.orthogonal V := hQW x (Or.inl hx) q
    have hSBorth : ∀ a ∈ SB, f a (x q - q) = 0 := by
      intro a ha
      rw [hsym, hadj x (Or.inl hx) q a (hSBW ha)]
      have : x a - a = 0 := sub_eq_zero.2 (hfix a ha)
      rw [this, map_zero]
    obtain ⟨s, hs, v, hv, hsv⟩ :=
      Submodule.mem_sup.1 (lag SC SB (by rw [hWsum, sup_comm SB SC]) hSCiso hSBiso _ hxW hSBorth)
    by_cases hsV : s ∈ V
    · rw [← hsv]; exact add_mem hsV hv
    · exfalso
      obtain ⟨x', hx', hx's⟩ : ∃ x' ∈ X, x' s ≠ s := by
        by_contra h
        push Not at h
        exact hsV (hXfaith s hs h)
      have hBx : x' s - s ∈ B := hXB x' hx' s hs
      have hcq : x (x' q) = x' (x q) := LinearMap.congr_fun (hcomm x' hx') q
      have hw'W : x' q - q ∈ f.orthogonal V := hQW x' (Or.inl hx') q
      rw [hWsum] at hw'W
      obtain ⟨y, hy, v', hv', hw'⟩ := Submodule.mem_sup.1 hw'W
      obtain ⟨sb, hsb, sc, hsc, hy'⟩ := Submodule.mem_sup.1 hy
      have hxsb : x sb = sb := hfix sb hsb
      have hxv' : x v' = v' := hV x (Or.inl hx) v' hv'
      have hx'v : x' v = v := hV x' (Or.inl hx') v hv
      have hδ : x sc - sc ∈ P := hXC x hx sc hsc
      have hxq : x q = q + (s + v) := by
        rw [hsv]; abel
      have hx'q : x' q = q + (sb + sc + v') := by
        rw [hy', hw']; abel
      have e1 : x' (x q) = x' q + (x' s + v) := by
        rw [hxq, map_add, map_add, hx'v]
      have e2 : x (x' q) = x q + (sb + x sc + v') := by
        rw [hx'q, map_add, map_add, map_add, hxsb, hxv']
      have key : x' s - s = x sc - sc := by
        have h := hcq
        rw [e2, e1, hxq, hx'q] at h
        have h' : x' s - s - (x sc - sc) =
            (q + (sb + sc + v') + (x' s + v)) - (q + (s + v) + (sb + x sc + v')) := by abel
        rw [← h, sub_self] at h'
        exact sub_eq_zero.1 h'
      have hm : x' s - s ∈ B ⊓ P := ⟨hBx, key ▸ hδ⟩
      rw [hBP] at hm
      exact hx's (sub_eq_zero.1 ((Submodule.mem_bot _).1 hm))
