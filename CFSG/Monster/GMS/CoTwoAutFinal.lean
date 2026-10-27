module

public import CFSG.Monster.GMS.CoTwoAutStep
public import CFSG.Monster.GMS.CoTwoAutLin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

namespace CoTwoAutSetup

variable {G : Type} [Group G] {t x : G}

structure AutHyp (x t : G) : Prop where
  perf : ⁅Xsub x t, Xsub x t⁆ = Xsub x t
  cent : ∀ g ∈ Xsub x t, (∀ n ∈ Rsub x t, g * n = n * g) → g = 1 ∨ g = x ∨ g = t ∨ g = x * t
  irr : ∀ N : Subgroup G, x ∈ N → t ∈ N → N ≤ Rsub x t →
    (∀ g ∈ Xsub x t, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      (∀ n ∈ N, n = 1 ∨ n = x ∨ n = t ∨ n = x * t) ∨ N = Rsub x t

theorem eq_of_add_eq_zero' {a b : Fin 24 → ZMod 2} (h : a + b = 0) : a = b :=
  calc a = (a + b) + b := by rw [add_assoc, vec_add_self, add_zero]
    _ = b := by rw [h, zero_add]

theorem card_Rsub
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) : Nat.card ↥(Rsub x t) = 2 ^ 24 := by
  have hind : LinearIndependent (ZMod 2) fun _ : Unit => L.vec x :=
    linearIndependent_unique_iff.2 (L.vec_ne_zero_of_mem_typeSet hx)
  have h := L.card_inf_iInf_centralizer_Q (fun _ : Unit => x) (fun _ => hx.1) hind
  rw [iInf_const] at h
  simpa [Rsub] using h

theorem phiG_Psi_eq (L : LeechSystem t) {Ψ : G → G} {g : G} (hg : g ∈ Xsub x t)
    (hΨg : Ψ g ∈ Xsub x t) (hker : g⁻¹ * Ψ g ∈ Rsub x t) : phiG L (Ψ g) = phiG L g := by
  have h1 : phiG L (g⁻¹ * Ψ g) = 1 := phiG_eq_one_of_mem L hker.1
  have hgC := Xsub_le_C hg
  rw [phiG_mul L (inv_mem hgC) (Xsub_le_C hΨg), phiG_inv L hgC] at h1
  exact (eq_of_inv_mul_eq_one h1).symm

theorem vec_Psi_eq
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) (H : AutHyp x t) {Ψ : G → G}
    (hΨ : AutOn (Xsub x t) Ψ) (hΨx : Ψ x = x) (hΨt : Ψ t = t)
    (hR : ∀ r ∈ Rsub x t, Ψ r ∈ Rsub x t)
    (hcorr : ∀ r ∈ Rsub x t, L.vec (Ψ r) + L.vec r = 0 ∨ L.vec (Ψ r) + L.vec r = L.vec x)
    (hker : ∀ g ∈ Xsub x t, g⁻¹ * Ψ g ∈ Rsub x t) :
    ∀ r ∈ Rsub x t, L.vec (Ψ r) = L.vec r := by
  classical
  have hxR := x_mem_Rsub (t := t) hx.1
  have htR := t_mem_Rsub L hx.1
  have hΨvec : ∀ r ∈ Rsub x t, ∀ s ∈ Rsub x t,
      L.vec (Ψ (r * s)) = L.vec (Ψ r) + L.vec (Ψ s) := fun r hr s hs => by
    rw [hΨ.mul r (Rsub_le_Xsub L hr) s (Rsub_le_Xsub L hs), vec_mul_Rsub L (hR r hr) (hR s hs)]
  let N₁ : Subgroup G :=
    { carrier := {r | r ∈ Rsub x t ∧ L.vec (Ψ r) = L.vec r}
      mul_mem' := by
        rintro r s ⟨hr, hr'⟩ ⟨hs, hs'⟩
        refine ⟨mul_mem hr hs, ?_⟩
        rw [hΨvec r hr s hs, hr', hs', vec_mul_Rsub L hr hs]
      one_mem' := ⟨one_mem _, by rw [hΨ.map_one']⟩
      inv_mem' := by
        rintro r ⟨hr, hr'⟩
        refine ⟨inv_mem hr, ?_⟩
        rw [hΨ.map_inv' (Rsub_le_Xsub L hr), L.vec_inv (hR r hr).1, L.vec_inv hr.1, hr'] }
  have hN₁x : x ∈ N₁ := ⟨hxR, by rw [hΨx]⟩
  have hN₁t : t ∈ N₁ := ⟨htR, by rw [hΨt]⟩
  have hN₁le : N₁ ≤ Rsub x t := fun r hr => hr.1
  have hN₁norm : ∀ g ∈ Xsub x t, ∀ n ∈ N₁, g * n * g⁻¹ ∈ N₁ := by
    rintro g hg n ⟨hn, hn'⟩
    refine ⟨conj_mem_Rsub L hg hn, ?_⟩
    have hphi := phiG_Psi_eq L (Ψ := Ψ) hg (hΨ.mem g hg) (hker g hg)
    rw [hΨ.map_conj hg (Rsub_le_Xsub L hn), vec_conj_phiG L (Xsub_le_C (hΨ.mem g hg)) (hR n hn).1,
      hphi, hn', vec_conj_phiG L (Xsub_le_C hg) hn.1]
  rcases H.irr N₁ hN₁x hN₁t hN₁le hN₁norm with hZ | hN
  ·
    by_contra hcon
    push Not at hcon
    obtain ⟨r₁, hr₁, hr₁'⟩ := hcon
    have hD : ∀ r ∈ Rsub x t, r ∉ N₁ → L.vec (Ψ r) + L.vec r = L.vec x := by
      intro r hr hrN
      rcases hcorr r hr with h | h
      · exact absurd ⟨hr, eq_of_add_eq_zero' h⟩ hrN
      · exact h
    set Zf : Finset G := {1, x, t, x * t} with hZf
    have hZmem : ∀ n, (n = 1 ∨ n = x ∨ n = t ∨ n = x * t) → n ∈ Zf := by
      intro n hn
      simp only [hZf, Finset.mem_insert, Finset.mem_singleton]
      exact hn
    have hcover : ∀ r ∈ Rsub x t, r ∈ Zf ∪ Zf.image (fun z => z * r₁⁻¹) := by
      intro r hr
      by_cases hrN : r ∈ N₁
      · exact Finset.mem_union_left _ (hZmem r (hZ r hrN))
      · have hr₁N : r₁ ∉ N₁ := fun h => hr₁' h.2
        have hrr₁ : r * r₁ ∈ N₁ := by
          refine ⟨mul_mem hr hr₁, ?_⟩
          have h1 := hD r hr hrN
          have h2 := hD r₁ hr₁ hr₁N
          have e : L.vec (Ψ (r * r₁)) + L.vec (r * r₁) = 0 := by
            rw [hΨvec r hr r₁ hr₁, vec_mul_Rsub L hr hr₁, add_add_add_comm, h1, h2,
              vec_add_self]
          exact eq_of_add_eq_zero' e
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨r * r₁, hZmem _ (hZ _ hrr₁), ?_⟩)
        group
    have hle : Nat.card ↥(Rsub x t) ≤ 8 := by
      have h1 : Nat.card ↥(Rsub x t) = (Rsub x t : Set G).ncard := Nat.card_coe_set_eq _
      have h2 : (Rsub x t : Set G) ⊆ ↑(Zf ∪ Zf.image (fun z => z * r₁⁻¹)) := fun r hr =>
        Finset.mem_coe.2 (hcover r hr)
      have h3 := Set.ncard_le_ncard h2 (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at h3
      have h4 : (Zf ∪ Zf.image (fun z => z * r₁⁻¹)).card ≤ 8 :=
        calc (Zf ∪ Zf.image (fun z => z * r₁⁻¹)).card
            ≤ Zf.card + (Zf.image (fun z => z * r₁⁻¹)).card := Finset.card_union_le _ _
          _ ≤ 4 + 4 := Nat.add_le_add Finset.card_le_four
              (Finset.card_image_le.trans Finset.card_le_four)
      omega
    have := card_Rsub L hx
    omega
  · intro r hr
    have : r ∈ N₁ := hN ▸ hr
    exact this.2

theorem exists_r₀
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) {Ψ : G → G}
    (hΨ : AutOn (Xsub x t) Ψ) (hΨx : Ψ x = x) (hΨt : Ψ t = t)
    (hR : ∀ r ∈ Rsub x t, Ψ r ∈ Rsub x t) (hvec : ∀ r ∈ Rsub x t, L.vec (Ψ r) = L.vec r) :
    ∃ r₀ ∈ Rsub x t, ∀ r ∈ Rsub x t, r₀⁻¹ * Ψ r * r₀ = r := by
  classical
  have hxR := x_mem_Rsub (t := t) hx.1
  have htR := t_mem_Rsub L hx.1
  have ht1 : t ≠ 1 := L.z_ne_one
  have htt : t * t = 1 := L.z_mul_self
  have hcase : ∀ r ∈ Rsub x t, Ψ r = r ∨ Ψ r = r * t := fun r hr =>
    L.eq_or_eq_mul_z (hR r hr).1 hr.1 (hvec r hr)
  have hne : ∀ r : G, r * t ≠ r := fun r h => ht1 (mul_eq_left.1 h)
  let Fv : (Fin 24 → ZMod 2) → ZMod 2 := fun w =>
    if h : ∃ r ∈ Rsub x t, L.vec r = w then (if Ψ h.choose = h.choose then 0 else 1) else 0
  have hFv : ∀ r ∈ Rsub x t, Fv (L.vec r) = if Ψ r = r then 0 else 1 := by
    intro r hr
    have h : ∃ r' ∈ Rsub x t, L.vec r' = L.vec r := ⟨r, hr, rfl⟩
    have hf : Fv (L.vec r) = if Ψ h.choose = h.choose then 0 else 1 := by
      show (if h : ∃ r' ∈ Rsub x t, L.vec r' = L.vec r then
        (if Ψ h.choose = h.choose then 0 else 1) else 0) = _
      simp [h]
    rw [hf]
    obtain ⟨hr', hv'⟩ := h.choose_spec
    rcases L.eq_or_eq_mul_z hr'.1 hr.1 hv' with e | e
    · rw [e]
    · rw [e, hΨ.mul r (Rsub_le_Xsub L hr) t (Rsub_le_Xsub L htR), hΨt]
      by_cases h1 : Ψ r = r
      · simp [h1]
      · have : Ψ r * t ≠ r * t := fun h2 => h1 (mul_right_cancel h2)
        simp [h1, this]
  have hFadd : ∀ a b, bil₀ a (L.vec x) = 0 → bil₀ b (L.vec x) = 0 →
      Fv (a + b) = Fv a + Fv b := by
    intro a b ha hb
    obtain ⟨r, hr, rfl⟩ := exists_mem_Rsub_vec L hx.1 ha
    obtain ⟨s, hs, rfl⟩ := exists_mem_Rsub_vec L hx.1 hb
    rw [← vec_mul_Rsub L hr hs, hFv _ (mul_mem hr hs), hFv r hr, hFv s hs,
      hΨ.mul r (Rsub_le_Xsub L hr) s (Rsub_le_Xsub L hs)]
    have hts : s * t = t * s := t_central (Rsub_le_Xsub L hs)
    rcases hcase r hr with e₁ | e₁ <;> rcases hcase s hs with e₂ | e₂ <;> rw [e₁, e₂]
    · simp
    · have h1 : r * (s * t) ≠ r * s := fun h => hne s (mul_left_cancel h)
      simp [h1, hne s]
    · have h1 : r * t * s ≠ r * s := fun h => by
        have : t * s = s := mul_left_cancel (by rw [← mul_assoc]; exact h)
        exact ht1 (mul_eq_right.1 this)
      simp [h1, hne r]
    · have h1 : r * t * (s * t) = r * s := by
        calc r * t * (s * t) = r * (t * s) * t := by group
          _ = r * (s * t) * t := by rw [hts]
          _ = r * s * (t * t) := by group
          _ = r * s := by rw [htt, mul_one]
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [h1, hne r, hne s, h2]
  have hFvv : Fv (L.vec x) = 0 := by
    rw [hFv x hxR, hΨx]
    simp
  obtain ⟨m, hm_perp, hm⟩ :=
    CoTwoAutLin.exists_dual_vec (L.vec_ne_zero_of_mem_typeSet hx) hFadd hFvv
  obtain ⟨r₀, hr₀, hr₀m⟩ := exists_mem_Rsub_vec L hx.1 hm_perp
  refine ⟨r₀, hr₀, fun r hr => ?_⟩
  have hF := hm (L.vec r) (vec_perp_of_mem_Rsub L hx.1 hr)
  rw [hFv r hr, ← hr₀m] at hF
  have hr₀t : r₀ * t = t * r₀ := t_central (Rsub_le_Xsub L hr₀)
  have hrt : r * t = t * r := t_central (Rsub_le_Xsub L hr)
  rcases hcase r hr with e | e
  ·
    rw [e]
    simp only [e, ite_true] at hF
    have hc : ⁅r, r₀⁆ = 1 := (L.comm_eq_one_iff hr.1 hr₀.1).2 hF.symm
    have hcomm : r * r₀ = r₀ * r := commutatorElement_eq_one_iff_mul_comm.1 hc
    calc r₀⁻¹ * r * r₀ = r₀⁻¹ * (r * r₀) := by group
      _ = r₀⁻¹ * (r₀ * r) := by rw [hcomm]
      _ = r := by group
  ·
    rw [e]
    have hne' : ¬ Ψ r = r := by rw [e]; exact hne r
    simp only [hne', ite_false] at hF
    have hc : ⁅r, r₀⁆ = t := (L.comm_eq_z_iff hr.1 hr₀.1).2 hF.symm
    have h1 : r * r₀ = t * (r₀ * r) := by
      calc r * r₀ = (r * r₀ * r⁻¹ * r₀⁻¹) * (r₀ * r) := by group
        _ = t * (r₀ * r) := by rw [show r * r₀ * r⁻¹ * r₀⁻¹ = t from hc]
    calc r₀⁻¹ * (r * t) * r₀ = r₀⁻¹ * r * (t * r₀) := by group
      _ = r₀⁻¹ * r * (r₀ * t) := by rw [hr₀t]
      _ = (r₀⁻¹ * (r * r₀)) * t := by group
      _ = (r₀⁻¹ * (t * (r₀ * r))) * t := by rw [h1]
      _ = (r₀⁻¹ * t * r₀) * r * t := by group
      _ = (r₀⁻¹ * (t * r₀)) * r * t := by group
      _ = (r₀⁻¹ * (r₀ * t)) * r * t := by rw [← hr₀t]
      _ = t * r * t := by group
      _ = r * t * t := by rw [← hrt]
      _ = r := by rw [mul_assoc, htt, mul_one]

theorem central_of_mem_Z (hx : x ∈ leechQ t) (L : LeechSystem t) {a : G}
    (ha : a = 1 ∨ a = x ∨ a = t ∨ a = x * t) {y : G} (hy : y ∈ Xsub x t) : a * y = y * a := by
  have hxy : x * y = y * x := (x_central hy).symm
  have hty : t * y = y * t := (t_central hy).symm
  rcases ha with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hxy
  · exact hty
  · calc x * t * y = x * (t * y) := by rw [mul_assoc]
      _ = x * (y * t) := by rw [hty]
      _ = (x * y) * t := by rw [mul_assoc]
      _ = (y * x) * t := by rw [hxy]
      _ = y * (x * t) := by rw [mul_assoc]

theorem mem_Xsub_of_mem_Z (L : LeechSystem t) (hx : x ∈ leechQ t) {a : G}
    (ha : a = 1 ∨ a = x ∨ a = t ∨ a = x * t) : a ∈ Xsub x t := by
  have hxX := Rsub_le_Xsub L (x_mem_Rsub (t := t) hx)
  have htX := Rsub_le_Xsub L (t_mem_Rsub L hx)
  rcases ha with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hxX
  · exact htX
  · exact mul_mem hxX htX

theorem eq_of_fix_Rsub (L : LeechSystem t) (hx : x ∈ L.typeSet 0) (H : AutHyp x t) {Φ : G → G}
    (hΦ : AutOn (Xsub x t) Φ) (hfix : ∀ r ∈ Rsub x t, Φ r = r) :
    ∀ g ∈ Xsub x t, Φ g = g := by
  have hcentral : ∀ g ∈ Xsub x t, ∃ a, (a = 1 ∨ a = x ∨ a = t ∨ a = x * t) ∧ Φ g = g * a := by
    intro g hg
    refine ⟨g⁻¹ * Φ g, ?_, by group⟩
    refine H.cent _ (mul_mem (inv_mem hg) (hΦ.mem g hg)) fun n hn => ?_
    have h1 : Φ (g * n * g⁻¹) = g * n * g⁻¹ := hfix _ (conj_mem_Rsub L hg hn)
    rw [hΦ.map_conj hg (Rsub_le_Xsub L hn), hfix n hn] at h1
    have h2 : (g⁻¹ * Φ g) * n * (g⁻¹ * Φ g)⁻¹ = n :=
      calc (g⁻¹ * Φ g) * n * (g⁻¹ * Φ g)⁻¹ = g⁻¹ * (Φ g * n * (Φ g)⁻¹) * g := by group
        _ = g⁻¹ * (g * n * g⁻¹) * g := by rw [h1]
        _ = n := by group
    calc (g⁻¹ * Φ g) * n = ((g⁻¹ * Φ g) * n * (g⁻¹ * Φ g)⁻¹) * (g⁻¹ * Φ g) := by group
      _ = n * (g⁻¹ * Φ g) := by rw [h2]
  let K₀ : Subgroup G :=
    { carrier := {g | g ∈ Xsub x t ∧ Φ g = g}
      mul_mem' := by
        rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
        exact ⟨mul_mem hg hh, by rw [hΦ.mul _ hg _ hh, hg', hh']⟩
      one_mem' := ⟨one_mem _, hΦ.map_one'⟩
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        exact ⟨inv_mem hg, by rw [hΦ.map_inv' hg, hg']⟩ }
  have hcomm : ⁅Xsub x t, Xsub x t⁆ ≤ K₀ := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh), ?_⟩
    obtain ⟨a, ha, hΦg⟩ := hcentral g hg
    obtain ⟨b, hb, hΦh⟩ := hcentral h hh
    have hbX := mem_Xsub_of_mem_Z L hx.1 hb
    have hag : a * g = g * a := central_of_mem_Z hx.1 L ha hg
    have hah : a * h = h * a := central_of_mem_Z hx.1 L ha hh
    have hab : a * b = b * a := central_of_mem_Z hx.1 L ha hbX
    have hbg : b * g = g * b := central_of_mem_Z hx.1 L hb hg
    have hbh : b * h = h * b := central_of_mem_Z hx.1 L hb hh
    have hbg' : b * g⁻¹ = g⁻¹ * b :=
      calc b * g⁻¹ = g⁻¹ * (g * b) * g⁻¹ := by group
        _ = g⁻¹ * (b * g) * g⁻¹ := by rw [hbg]
        _ = g⁻¹ * b := by group
    have hΦc : Φ (g * h * g⁻¹ * h⁻¹) = Φ g * Φ h * (Φ g)⁻¹ * (Φ h)⁻¹ := by
      rw [hΦ.mul _ (mul_mem (mul_mem hg hh) (inv_mem hg)) _ (inv_mem hh),
        hΦ.mul _ (mul_mem hg hh) _ (inv_mem hg), hΦ.mul _ hg _ hh, hΦ.map_inv' hg,
        hΦ.map_inv' hh]
    show Φ (g * h * g⁻¹ * h⁻¹) = g * h * g⁻¹ * h⁻¹
    rw [hΦc, hΦg, hΦh]
    calc g * a * (h * b) * (g * a)⁻¹ * (h * b)⁻¹
        = g * a * (h * b) * (a⁻¹ * g⁻¹) * (b⁻¹ * h⁻¹) := by rw [mul_inv_rev, mul_inv_rev]
      _ = g * (a * h) * b * a⁻¹ * g⁻¹ * b⁻¹ * h⁻¹ := by group
      _ = g * (h * a) * b * a⁻¹ * g⁻¹ * b⁻¹ * h⁻¹ := by rw [hah]
      _ = g * h * (a * b) * a⁻¹ * g⁻¹ * b⁻¹ * h⁻¹ := by group
      _ = g * h * (b * a) * a⁻¹ * g⁻¹ * b⁻¹ * h⁻¹ := by rw [hab]
      _ = g * h * (b * g⁻¹) * b⁻¹ * h⁻¹ := by group
      _ = g * h * (g⁻¹ * b) * b⁻¹ * h⁻¹ := by rw [hbg']
      _ = g * h * g⁻¹ * h⁻¹ := by group
  rw [H.perf] at hcomm
  exact fun g hg => (hcomm hg).2

theorem inv_mul_mem_Rsub
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) {Ψ : G → G}
    (hΨ : AutOn (Xsub x t) Ψ) (hR : ∀ r ∈ Rsub x t, Ψ r ∈ Rsub x t)
    (hcorr : ∀ r ∈ Rsub x t, L.vec (Ψ r) + L.vec r = 0 ∨ L.vec (Ψ r) + L.vec r = L.vec x)
    {g : G} (hg : g ∈ Xsub x t) : g⁻¹ * Ψ g ∈ Rsub x t := by
  have hgC := Xsub_le_C hg
  have hΨgX := hΨ.mem g hg
  have hΨgC := Xsub_le_C hΨgX
  have hdX : g⁻¹ * Ψ g ∈ Xsub x t := mul_mem (inv_mem hg) hΨgX
  have hphid : phiG L (g⁻¹ * Ψ g) = (phiG L g)⁻¹ * phiG L (Ψ g) := by
    rw [phiG_mul L (inv_mem hgC) hΨgC, phiG_inv L hgC]
  have hA := phiG_mem_stab L hx hg
  have hB := phiG_mem_stab L hx hΨgX
  have hkw : ∀ w, bil₀ w (L.vec x) = 0 →
      co1Act (phiG L (g⁻¹ * Ψ g)) w + w = 0 ∨ co1Act (phiG L (g⁻¹ * Ψ g)) w + w = L.vec x := by
    intro w hw
    obtain ⟨r₁, hr₁, rfl⟩ := exists_mem_Rsub_vec L hx.1 hw
    have h1 := hcorr _ (conj_mem_Rsub L hg hr₁)
    have h2 := hcorr r₁ hr₁
    rw [hΨ.map_conj hg (Rsub_le_Xsub L hr₁), vec_conj_phiG L hΨgC (hR r₁ hr₁).1,
      vec_conj_phiG L hgC hr₁.1] at h1
    have h3 := CoTwoAutKer.smul01 hB h2
    have h4 : co1Act (phiG L (Ψ g)) (L.vec r₁) + co1Act (phiG L g) (L.vec r₁) = 0 ∨
        co1Act (phiG L (Ψ g)) (L.vec r₁) + co1Act (phiG L g) (L.vec r₁) = L.vec x := by
      have e : co1Act (phiG L (Ψ g)) (L.vec r₁) + co1Act (phiG L g) (L.vec r₁) =
          (co1Act (phiG L (Ψ g)) (L.vec (Ψ r₁)) + co1Act (phiG L g) (L.vec r₁)) +
            co1Act (phiG L (Ψ g)) (L.vec (Ψ r₁) + L.vec r₁) := by
        rw [map_add, add_add_add_comm, vec_add_self, zero_add, add_comm]
      rw [e]
      exact CoTwoAutKer.add01 h1 h3
    have h5 := CoTwoAutKer.smul01 (inv_mem hA) h4
    rw [map_add, CoTwoModule.co1Act_inv_apply] at h5
    rw [hphid, CoTwoModule.co1Act_mul_apply]
    exact h5
  have hk1 : phiG L (g⁻¹ * Ψ g) = 1 :=
    CoTwoAutKer.eq_one_of_trivial_on_perp hx.2 (phiG_mem_stab L hx hdX) hkw
  exact ⟨(phiG_eq_one_iff L (Xsub_le_C hdX)).1 hk1, hdX.1⟩

theorem inner_of_autOn
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) (H : AutHyp x t)
    (hnorm : Co2NormalizerFact) {Ψ : G → G} (hΨ : AutOn (Xsub x t) Ψ) (hΨx : Ψ x = x)
    (hΨt : Ψ t = t) : ∃ h ∈ Xsub x t, ∀ g ∈ Xsub x t, Ψ g = h * g * h⁻¹ := by
  have hR := fun r (hr : r ∈ Rsub x t) => AutOn.mem_Rsub L hx hΨ hΨt hr
  obtain ⟨c, hcX, hcorr⟩ := exists_inner_correction L hx hnorm hΨ hΨx hΨt
  have hΨ₁ : AutOn (Xsub x t) (fun g => c⁻¹ * Ψ g * c) := by
    have := hΨ.conj (inv_mem hcX)
    simpa only [inv_inv] using this
  have hcx : c⁻¹ * x * c = x := by
    have := x_central (inv_mem hcX)
    calc c⁻¹ * x * c = x * c⁻¹ * c := by rw [this]
      _ = x := by group
  have hct : c⁻¹ * t * c = t := by
    have := t_central (inv_mem hcX)
    calc c⁻¹ * t * c = t * c⁻¹ * c := by rw [this]
      _ = t := by group
  have hΨ₁x : (fun g => c⁻¹ * Ψ g * c) x = x := by
    show c⁻¹ * Ψ x * c = x
    rw [hΨx, hcx]
  have hΨ₁t : (fun g => c⁻¹ * Ψ g * c) t = t := by
    show c⁻¹ * Ψ t * c = t
    rw [hΨt, hct]
  have hR₁ : ∀ r ∈ Rsub x t, (fun g => c⁻¹ * Ψ g * c) r ∈ Rsub x t := by
    intro r hr
    have := conj_mem_Rsub L (inv_mem hcX) (hR r hr)
    rwa [inv_inv] at this
  have hker₁ : ∀ g ∈ Xsub x t, g⁻¹ * (fun g => c⁻¹ * Ψ g * c) g ∈ Rsub x t := fun g hg =>
    inv_mul_mem_Rsub L hx hΨ₁ hR₁ hcorr hg
  have hvec₁ := vec_Psi_eq L hx H hΨ₁ hΨ₁x hΨ₁t hR₁ hcorr hker₁
  obtain ⟨r₀, hr₀, hr₀fix⟩ := exists_r₀ L hx hΨ₁ hΨ₁x hΨ₁t hR₁ hvec₁
  have hΨ₂ : AutOn (Xsub x t) (fun g => r₀⁻¹ * (c⁻¹ * Ψ g * c) * r₀) := by
    have := hΨ₁.conj (inv_mem (Rsub_le_Xsub L hr₀))
    simpa only [inv_inv] using this
  have hfix := eq_of_fix_Rsub L hx H hΨ₂ hr₀fix
  refine ⟨c * r₀, mul_mem hcX (Rsub_le_Xsub L hr₀), fun g hg => ?_⟩
  have h2 : r₀⁻¹ * (c⁻¹ * Ψ g * c) * r₀ = g := hfix g hg
  calc Ψ g = (c * r₀) * (r₀⁻¹ * (c⁻¹ * Ψ g * c) * r₀) * (c * r₀)⁻¹ := by group
    _ = (c * r₀) * g * (c * r₀)⁻¹ := by rw [h2]

end CoTwoAutSetup

end CFSG.Monster.GMS
