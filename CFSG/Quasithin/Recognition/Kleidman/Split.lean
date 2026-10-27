module

public import CFSG.Quasithin.Recognition.Kleidman.SplitQ
public import CFSG.Quasithin.Recognition.Kleidman.SplitCount
public import CFSG.Quasithin.Recognition.J2RecSplit
public import CFSG.Quasithin.Recognition.J2RecInvol

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SzI47J2NoA4

variable {G : Type*} [Group G]

theorem sq_mem_of_mem_closure {C W : Subgroup G} {X : Set G} (hXC : X ⊆ C)
    (hW : ∀ w ∈ W, ∀ c ∈ C, w * c = c * w) (hsq : ∀ x ∈ X, x * x ∈ W)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ W) :
    ∀ r ∈ Subgroup.closure X, r * r ∈ W := by
  have hRC : Subgroup.closure X ≤ C := (Subgroup.closure_le C).mpr hXC
  have hWC : ∀ {w c : G}, w ∈ W → c ∈ C → c * w * c⁻¹ = w := fun hw hc => by
    rw [← hW _ hw _ hc]; group
  have h1 : ∀ r ∈ Subgroup.closure X, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ W := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem r hr => exact fun x hx => hcomm r hr x hx
    | one => intro x _; simp [one_mem]
    | mul a b ha hb iha ihb =>
      intro x hx
      have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
          (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
      rw [e, hWC (ihb x hx) (hRC ha)]
      exact mul_mem (ihb x hx) (iha x hx)
    | inv a ha iha =>
      intro x hx
      have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
      rw [e, hWC (inv_mem (iha x hx)) (inv_mem (hRC ha))]
      exact inv_mem (iha x hx)
  have h2 : ∀ r ∈ Subgroup.closure X, ∀ s ∈ Subgroup.closure X, r * s * r⁻¹ * s⁻¹ ∈ W := by
    intro r hr s hs
    induction hs using Subgroup.closure_induction with
    | mem s hs => exact h1 r hr s hs
    | one => simp [one_mem]
    | mul a b ha hb iha ihb =>
      have e : r * (a * b) * r⁻¹ * (a * b)⁻¹ =
          (r * a * r⁻¹ * a⁻¹) * (a * (r * b * r⁻¹ * b⁻¹) * a⁻¹) := by group
      rw [e, hWC ihb (hRC ha)]
      exact mul_mem iha ihb
    | inv a ha iha =>
      have e : r * a⁻¹ * r⁻¹ * a⁻¹⁻¹ = a⁻¹ * (r * a * r⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
      rw [e, hWC (inv_mem iha) (inv_mem (hRC ha))]
      exact inv_mem iha
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem r hr => exact hsq r hr
  | one => simp [one_mem]
  | mul a b ha hb iha ihb =>
    have hc := h2 b hb a ha
    have e : a * b * (a * b) = (a * (b * a * b⁻¹ * a⁻¹) * a⁻¹) * (a * a) * (b * b) := by group
    rw [e, hWC hc (hRC ha)]
    exact mul_mem (mul_mem hc iha) ihb
  | inv a ha iha =>
    rw [show a⁻¹ * a⁻¹ = (a * a)⁻¹ by group]
    exact inv_mem iha

section QAt

variable (z : G)

@[expose] def qAt (v : G) : Subgroup G where
  carrier := {x | ∀ g : G, g * z * g⁻¹ = v →
    g⁻¹ * x * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))}
  mul_mem' {a b} ha hb g hg := by
    have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
    rw [e]
    exact mul_mem (ha g hg) (hb g hg)
  one_mem' g _ := by simp [one_mem]
  inv_mem' {a} ha g hg := by
    have e : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
    rw [e]
    exact inv_mem (ha g hg)

variable {z}

theorem conj_mem_qAt {v x : G} (hx : x ∈ qAt z v) (k : G) : k * x * k⁻¹ ∈ qAt z (k * v * k⁻¹) := by
  intro g hg
  have hg' : (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ = v := by
    calc (k⁻¹ * g) * z * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * z * g⁻¹) * k := by group
      _ = v := by rw [hg]; group
  have e : g⁻¹ * (k * x * k⁻¹) * g = (k⁻¹ * g)⁻¹ * x * (k⁻¹ * g) := by group
  rw [e]
  exact hx _ hg'

theorem mem_qAt_iff {v g x : G} (hg : g * z * g⁻¹ = v) :
    x ∈ qAt z v ↔ g⁻¹ * x * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  refine ⟨fun hx => hx g hg, fun hx g' hg' => ?_⟩
  set c := g'⁻¹ * g with hc
  have hcH : c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : g * z * g⁻¹ = g' * z * g'⁻¹ := hg.trans hg'.symm
    have hzc : z * c = c * z := by
      calc z * c = g'⁻¹ * (g' * z * g'⁻¹) * g := by rw [hc]; group
        _ = g'⁻¹ * (g * z * g⁻¹) * g := by rw [this]
        _ = c * z := by rw [hc]; group
    exact hzc.symm
  have hN := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hcH) _).mp hx
  have e : c * (g⁻¹ * x * g) * c⁻¹ = g'⁻¹ * x * g' := by rw [hc]; group
  rwa [e] at hN

theorem qAt_self : qAt z z = pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  ext x
  rw [mem_qAt_iff (g := 1) (by group)]
  simp

end QAt

section Klein

theorem klein_mul_mem {z t a b : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : t * z = z * t)
    (ha : a = 1 ∨ a = z ∨ a = t ∨ a = z * t) (hb : b = 1 ∨ b = z ∨ b = t ∨ b = z * t) :
    a * b = 1 ∨ a * b = z ∨ a * b = t ∨ a * b = z * t := by
  have e1 : z * (z * t) = t := by rw [← mul_assoc, hz2, one_mul]
  have e2 : t * (z * t) = z := by rw [← mul_assoc, hzt, mul_assoc, ht2, mul_one]
  have e3 : z * t * z = t := by rw [mul_assoc, hzt, ← mul_assoc, hz2, one_mul]
  have e4 : z * t * t = z := by rw [mul_assoc, ht2, mul_one]
  have e5 : z * t * (z * t) = 1 := by rw [← mul_assoc, e3, ht2]
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, hz2, ht2, e1, e2, e3, e4, e5, hzt, true_or, or_true]

theorem klein_sq {z t a : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : t * z = z * t)
    (ha : a = 1 ∨ a = z ∨ a = t ∨ a = z * t) : a * a = 1 := by
  rcases ha with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact hz2
  · exact ht2
  · rw [mul_assoc, ← mul_assoc t z t, hzt, mul_assoc, ht2, mul_one, hz2]

end Klein

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

variable [Finite G]

theorem exists_involution_not_mem_pCoreOf (h : IsTypeH2 G z) :
    ∃ t ∈ Subgroup.centralizer ({z} : Set G), t * t = 1 ∧
      t ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  classical
  set H := Subgroup.centralizer ({z} : Set G) with hH
  set Q := pCoreOf 2 H with hQ
  by_contra hcon
  push Not at hcon
  have hall : ∀ s ∈ H, s * s = 1 → s ∈ Q := fun s hs hs2 => hcon s hs hs2
  have hQH : Q ≤ H := pCoreOf_le 2 H
  have hzQ : z ∈ Q := h.z_mem_pCoreOf
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.sq
  have hz1 : z ≠ 1 := h.ne_one
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hmemH : ∀ {x : G}, x ∈ H ↔ z * x = x * z := by
    intro x
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hQcomm : ∀ {x : G}, x ∈ Q → x * z = z * x := fun hx => (hmemH.mp (hQH hx)).symm
  have hQnorm : ∀ {c x : G}, c ∈ H → x ∈ Q → c * x * c⁻¹ ∈ Q := fun hc hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hc) _).mp hx
  have hconjQ : ∀ {k v : G}, k * z * k⁻¹ = v → ∀ {s : G}, s * v = v * s → s * s = 1 →
      k⁻¹ * s * k ∈ Q := by
    intro k v hk s hsv hs2
    refine hall _ (hmemH.mpr ?_) ?_
    · have e1 : z = k⁻¹ * v * k := by rw [← hk]; group
      calc z * (k⁻¹ * s * k) = k⁻¹ * (v * s) * k := by rw [e1]; group
        _ = k⁻¹ * (s * v) * k := by rw [hsv]
        _ = k⁻¹ * s * k * z := by rw [e1]; group
    · calc k⁻¹ * s * k * (k⁻¹ * s * k) = k⁻¹ * (s * s) * k := by group
        _ = 1 := by rw [hs2]; group
  have hpre : ∀ {k v : G}, k * z * k⁻¹ = v → v ∈ Q → v ≠ z →
      k⁻¹ * z * k ∈ Q ∧ k⁻¹ * z * k * (k⁻¹ * z * k) = 1 ∧ k⁻¹ * z * k ≠ 1 ∧
        k⁻¹ * z * k ≠ z := by
    intro k v hk hvQ hvz
    refine ⟨hconjQ hk (hQcomm hvQ).symm hz2, ?_, ?_, ?_⟩
    · calc k⁻¹ * z * k * (k⁻¹ * z * k) = k⁻¹ * (z * z) * k := by group
        _ = 1 := by rw [hz2]; group
    · intro h1
      apply hz1
      calc z = k * (k⁻¹ * z * k) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      apply hvz
      rw [← hk]
      calc k * z * k⁻¹ = k * (k⁻¹ * z * k) * k⁻¹ := by rw [h1]
        _ = z := by group
  obtain ⟨g, hgQ, hgz⟩ := h.notWeaklyClosed
  set t := g * z * g⁻¹ with ht
  have htQ : t ∈ Q := hgQ
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [ht]; group
      _ = 1 := by rw [hz2]; group
  have ht1 : t ≠ 1 := fun h1 => hz1 (by
    calc z = g⁻¹ * t * g := by rw [ht]; group
      _ = 1 := by rw [h1]; group)
  have hzt : z ≠ t := fun h1 => hgz h1.symm
  have htz : t * z = z * t := hQcomm htQ
  have hztQ : z * t ∈ Q := mul_mem hzQ htQ
  have hVt : ∀ {a : G}, (a = 1 ∨ a = z ∨ a = t ∨ a = z * t) → a * a = 1 :=
    fun ha => klein_sq hz2 ht2 htz ha
  have hzt2 : z * t * (z * t) = 1 := hVt (Or.inr (Or.inr (Or.inr rfl)))
  have hzt1 : z * t ≠ 1 := fun h1 => hzt (by
    rw [← hzinv]; exact (eq_inv_of_mul_eq_one_right h1).symm)
  have hztz : z * t ≠ z := fun h1 => ht1 (by simpa using h1)
  have hztt : z * t ≠ t := fun h1 => hz1 (by simpa using h1)
  obtain ⟨c1, hc1H, hc1⟩ := h.exists_conj_of_noncentral htQ ht2 ht1 hzt.symm hztQ hzt2 hzt1 hztz
  set g2 := c1 * g with hg2
  have hg2z : g2 * z * g2⁻¹ = z * t := by
    rw [hg2, ← hc1, ht]; group
  have hswap : ∀ {k v : G}, k * z * k⁻¹ = v → v ∈ Q → v * v = 1 → v ≠ 1 → v ≠ z →
      ∃ m : G, m * z * m⁻¹ = v ∧ m * v * m⁻¹ = z := by
    intro k v hk hvQ hv2 hv1 hvz
    obtain ⟨hs, hs2, hs1, hsz⟩ := hpre hk hvQ hvz
    obtain ⟨c, hcH, hc⟩ := h.exists_conj_of_noncentral hvQ hv2 hv1 hvz hs hs2 hs1 hsz
    refine ⟨k * c, ?_, ?_⟩
    · have hcz : c * z = z * c := (hmemH.mp hcH).symm
      calc k * c * z * (k * c)⁻¹ = k * (c * z * c⁻¹) * k⁻¹ := by group
        _ = k * z * k⁻¹ := by rw [hcz]; group
        _ = v := hk
    · calc k * c * v * (k * c)⁻¹ = k * (c * v * c⁻¹) * k⁻¹ := by group
        _ = k * (k⁻¹ * z * k) * k⁻¹ := by rw [hc]
        _ = z := by group
  obtain ⟨m1, hm1z, hm1t⟩ := hswap (k := g) rfl htQ ht2 ht1 hzt.symm
  obtain ⟨m2, hm2z, hm2zt⟩ := hswap hg2z hztQ hzt2 hzt1 hztz
  set ρ := m2 * m1 with hρ
  have hm2t : m2 * t * m2⁻¹ = t := by
    have e : t = z⁻¹ * (z * t) := by group
    calc m2 * t * m2⁻¹ = (m2 * z * m2⁻¹)⁻¹ * (m2 * (z * t) * m2⁻¹) := by
          rw [e]; group
      _ = (z * t)⁻¹ * z := by rw [hm2z, hm2zt]
      _ = t := by rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one,
          inv_eq_of_mul_eq_one_right ht2]
  have hρz : ρ * z * ρ⁻¹ = t := by
    calc ρ * z * ρ⁻¹ = m2 * (m1 * z * m1⁻¹) * m2⁻¹ := by rw [hρ]; group
      _ = t := by rw [hm1z, hm2t]
  have hρt : ρ * t * ρ⁻¹ = z * t := by
    calc ρ * t * ρ⁻¹ = m2 * (m1 * t * m1⁻¹) * m2⁻¹ := by rw [hρ]; group
      _ = z * t := by rw [hm1t, hm2z]
  have hρzt : ρ * (z * t) * ρ⁻¹ = z := by
    have e : ρ * (z * t) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * t * ρ⁻¹) := by group
    rw [e, hρz, hρt, ← mul_assoc, htz, mul_assoc, ht2, mul_one]
  set C := Subgroup.centralizer ({z, t} : Set G) with hC
  have hmemC : ∀ {x : G}, x ∈ C ↔ x * z = z * x ∧ x * t = t * x := by
    intro x
    simp only [hC, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have hCH : ∀ {x : G}, x ∈ C → x ∈ H := fun hx => hmemH.mpr (hmemC.mp hx).1.symm
  have hCzt : ∀ {x : G}, x ∈ C → x * (z * t) = z * t * x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hmemC.mp hx
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  have hCconj : ∀ {x k : G}, x ∈ C → k ∈ C → k * x * k⁻¹ ∈ C := fun hx hk =>
    mul_mem (mul_mem hk hx) (inv_mem hk)
  have hconjV : ∀ {k v : G}, k ∈ C → (v = z ∨ v = t ∨ v = z * t) → k * v * k⁻¹ = v := by
    intro k v hk hv
    obtain ⟨h1, h2⟩ := hmemC.mp hk
    rcases hv with rfl | rfl | rfl
    · rw [h1]; group
    · rw [h2]; group
    · rw [hCzt hk]; group
  set W := Subgroup.closure ({z, t} : Set G) with hW
  have hWV : ∀ w ∈ W, w = 1 ∨ w = z ∨ w = t ∨ w = z * t := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul a b _ _ ha hb => exact klein_mul_mem hz2 ht2 htz ha hb
    | inv a _ ha =>
      have : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hVt ha)
      rw [this]
      exact ha
  have hWC : ∀ w ∈ W, ∀ c ∈ C, w * c = c * w := by
    intro w hw c hc
    have hle : W ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hW, Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨h1, h2⟩ := hmemC.mp hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h1.symm
      · exact h2.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hzW : z ∈ W := Subgroup.subset_closure (by simp)
  have htW : t ∈ W := Subgroup.subset_closure (by simp)
  have hztW : z * t ∈ W := mul_mem hzW htW
  set Az := Q ⊓ C with hAz
  set At := qAt z t ⊓ C with hAt
  set Azt := qAt z (z * t) ⊓ C with hAzt
  have hqt : ∀ {x : G}, x ∈ qAt z t ↔ g⁻¹ * x * g ∈ Q := mem_qAt_iff rfl
  have hqzt : ∀ {x : G}, x ∈ qAt z (z * t) ↔ g2⁻¹ * x * g2 ∈ Q := mem_qAt_iff hg2z
  have hsqConj : ∀ {k v x : G}, k * z * k⁻¹ = v → k⁻¹ * x * k ∈ Q →
      x * x = 1 ∨ x * x = v := by
    intro k v x hk hx
    rcases IsTypeH2.sq_eq_one_or_eq h hx with h1 | h1
    · left
      calc x * x = k * ((k⁻¹ * x * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · right
      calc x * x = k * ((k⁻¹ * x * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
        _ = v := by rw [h1, hk]
  have hcommConj : ∀ {k v x y : G}, k * z * k⁻¹ = v → k⁻¹ * x * k ∈ Q → k⁻¹ * y * k ∈ Q →
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = v := by
    intro k v x y hk hx hy
    have e : x * y * x⁻¹ * y⁻¹ = k * ((k⁻¹ * x * k) * (k⁻¹ * y * k) * (k⁻¹ * x * k)⁻¹ *
        (k⁻¹ * y * k)⁻¹) * k⁻¹ := by group
    rcases IsTypeH2.commutator_eq_one_or_eq h hx hy with h1 | h1
    · left; rw [e, h1]; group
    · right; rw [e, h1, hk]
  have hinvConj : ∀ {k v x : G}, k * z * k⁻¹ = v → v ∈ Q → v ≠ z → k⁻¹ * x * k ∈ Q →
      x * z = z * x → x * x = 1 → x = 1 ∨ x = v ∨ x = z ∨ x = v * z := by
    intro k v x hk hvQ hvz hx hxz hx2
    obtain ⟨hu, hu2, hu1, huz⟩ := hpre hk hvQ hvz
    have hqu : (k⁻¹ * x * k) * (k⁻¹ * z * k) = (k⁻¹ * z * k) * (k⁻¹ * x * k) := by
      calc (k⁻¹ * x * k) * (k⁻¹ * z * k) = k⁻¹ * (x * z) * k := by group
        _ = k⁻¹ * (z * x) * k := by rw [hxz]
        _ = (k⁻¹ * z * k) * (k⁻¹ * x * k) := by group
    have hq2 : (k⁻¹ * x * k) * (k⁻¹ * x * k) = 1 := by
      calc (k⁻¹ * x * k) * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
        _ = 1 := by rw [hx2]; group
    have hback : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rcases IsTypeH2.eq_of_comm_of_sq_eq_one h hu hu2 hu1 huz hx hqu hq2 with h1 | h1 | h1 | h1
    · left; rw [hback, h1]; group
    · right; left; rw [hback, h1, hk]
    · right; right; left; rw [hback, h1]; group
    · right; right; right
      rw [hback, h1]
      calc k * (z * (k⁻¹ * z * k)) * k⁻¹ = (k * z * k⁻¹) * z := by group
        _ = v * z := by rw [hk]
  set V : Set G := {1, z, t, z * t} with hV
  have hmemV : ∀ {a : G}, a ∈ V ↔ a = 1 ∨ a = z ∨ a = t ∨ a = z * t := by
    intro a
    simp only [hV, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hinvAz : ∀ x ∈ Az, x * x = 1 → x ∈ V := by
    intro x hx hx2
    have hxt := (hmemC.mp hx.2).2
    rw [hmemV]
    exact IsTypeH2.eq_of_comm_of_sq_eq_one h htQ ht2 ht1 hzt.symm hx.1 hxt hx2
  have hinvAt : ∀ x ∈ At, x * x = 1 → x ∈ V := by
    intro x hx hx2
    rcases hinvConj rfl htQ hzt.symm (hqt.mp hx.1) (hmemC.mp hx.2).1 hx2 with
      h1 | h1 | h1 | h1 <;> rw [hmemV]
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr (h1.trans htz)))
  have hinvAzt : ∀ x ∈ Azt, x * x = 1 → x ∈ V := by
    intro x hx hx2
    rcases hinvConj hg2z hztQ hztz (hqzt.mp hx.1) (hmemC.mp hx.2).1 hx2 with
      h1 | h1 | h1 | h1 <;> rw [hmemV]
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact Or.inr (Or.inl h1)
    · right; right; left
      rw [h1, mul_assoc, htz, ← mul_assoc, hz2, one_mul]
  have hnormQ : ∀ {k x : G}, k ∈ C → x ∈ Az → k * x * k⁻¹ ∈ Az := by
    intro k x hk hx
    exact ⟨hQnorm (hCH hk) hx.1, hCconj hx.2 hk⟩
  have hnormAt : ∀ {k x : G}, k ∈ C → x ∈ At → k * x * k⁻¹ ∈ At := by
    intro k x hk hx
    refine ⟨?_, hCconj hx.2 hk⟩
    have := conj_mem_qAt hx.1 k
    rwa [hconjV hk (Or.inr (Or.inl rfl))] at this
  have hnormAzt : ∀ {k x : G}, k ∈ C → x ∈ Azt → k * x * k⁻¹ ∈ Azt := by
    intro k x hk hx
    refine ⟨?_, hCconj hx.2 hk⟩
    have := conj_mem_qAt hx.1 k
    rwa [hconjV hk (Or.inr (Or.inr rfl))] at this
  have hcommAB : ∀ {A B : Subgroup G}, (∀ {k x : G}, k ∈ C → x ∈ A → k * x * k⁻¹ ∈ A) →
      (∀ {k x : G}, k ∈ C → x ∈ B → k * x * k⁻¹ ∈ B) → A ≤ C → B ≤ C →
      ∀ {a b : G}, a ∈ A → b ∈ B → a * b * a⁻¹ * b⁻¹ ∈ A ∧ a * b * a⁻¹ * b⁻¹ ∈ B := by
    intro A B hA hB hAC hBC a b ha hb
    refine ⟨?_, ?_⟩
    · have e : a * b * a⁻¹ * b⁻¹ = a * (b * a * b⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem ha (inv_mem (hA (hBC hb) ha))
    · exact mul_mem (hB (hAC ha) hb) (inv_mem hb)
  have hAzC : Az ≤ C := inf_le_right
  have hAtC : At ≤ C := inf_le_right
  have hAztC : Azt ≤ C := inf_le_right
  have hsqAz : ∀ x ∈ Az, x * x = 1 ∨ x * x = z := fun x hx => IsTypeH2.sq_eq_one_or_eq h hx.1
  have hsqAt : ∀ x ∈ At, x * x = 1 ∨ x * x = t := fun x hx => hsqConj rfl (hqt.mp hx.1)
  have hsqAzt : ∀ x ∈ Azt, x * x = 1 ∨ x * x = z * t := fun x hx =>
    hsqConj hg2z (hqzt.mp hx.1)
  have hinter : ∀ {A B : Subgroup G} {v w : G}, (∀ x ∈ A, x * x = 1 ∨ x * x = v) →
      (∀ x ∈ B, x * x = 1 ∨ x * x = w) → v ≠ w → (∀ x ∈ A, x * x = 1 → x ∈ V) →
      ∀ x, x ∈ A → x ∈ B → x ∈ V := by
    intro A B v w hA hB hvw hAinv x hxA hxB
    refine hAinv x hxA ?_
    rcases hA x hxA with h1 | h1
    · exact h1
    rcases hB x hxB with h2 | h2
    · exact h2
    exact absurd (h1.symm.trans h2) hvw
  have hVW : ∀ {a : G}, a ∈ V → a ∈ W := by
    intro a ha
    rcases hmemV.mp ha with rfl | rfl | rfl | rfl
    · exact one_mem W
    · exact hzW
    · exact htW
    · exact hztW
  set X : Set G := (Az : Set G) ∪ At ∪ Azt with hX
  set R := Subgroup.closure X with hR
  have hXC : X ⊆ C := by
    rintro x ((hx | hx) | hx)
    · exact hAzC hx
    · exact hAtC hx
    · exact hAztC hx
  have hRC : R ≤ C := (Subgroup.closure_le C).mpr hXC
  have hsqX : ∀ x ∈ X, x * x ∈ W := by
    rintro x ((hx | hx) | hx)
    · rcases hsqAz x hx with h1 | h1 <;> rw [h1]
      exacts [one_mem W, hzW]
    · rcases hsqAt x hx with h1 | h1 <;> rw [h1]
      exacts [one_mem W, htW]
    · rcases hsqAzt x hx with h1 | h1 <;> rw [h1]
      exacts [one_mem W, hztW]
  have hsame : ∀ {A : Subgroup G} {v : G}, v ∈ W → (∀ x ∈ A, ∀ y ∈ A,
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = v) →
      ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ W := by
    intro A v hv hA x hx y hy
    rcases hA x hx y hy with h1 | h1 <;> rw [h1]
    exacts [one_mem W, hv]
  have hcAz : ∀ x ∈ Az, ∀ y ∈ Az, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z :=
    fun x hx y hy => IsTypeH2.commutator_eq_one_or_eq h hx.1 hy.1
  have hcAt : ∀ x ∈ At, ∀ y ∈ At, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = t :=
    fun x hx y hy => hcommConj rfl (hqt.mp hx.1) (hqt.mp hy.1)
  have hcAzt : ∀ x ∈ Azt, ∀ y ∈ Azt,
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z * t :=
    fun x hx y hy => hcommConj hg2z (hqzt.mp hx.1) (hqzt.mp hy.1)
  have hcross : ∀ {A B : Subgroup G} {v w : G},
      (∀ {k x : G}, k ∈ C → x ∈ A → k * x * k⁻¹ ∈ A) →
      (∀ {k x : G}, k ∈ C → x ∈ B → k * x * k⁻¹ ∈ B) → A ≤ C → B ≤ C →
      (∀ x ∈ A, x * x = 1 ∨ x * x = v) → (∀ x ∈ B, x * x = 1 ∨ x * x = w) → v ≠ w →
      (∀ x ∈ A, x * x = 1 → x ∈ V) →
      ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ W := by
    intro A B v w hA hB hAC hBC hsA hsB hvw hiA a ha b hb
    obtain ⟨h1, h2⟩ := hcommAB hA hB hAC hBC ha hb
    exact hVW (hinter hsA hsB hvw hiA _ h1 h2)
  have hcross' : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ W) →
      ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ * a⁻¹ ∈ W := by
    intro A B hAB b hb a ha
    have e : b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hAB a ha b hb)
  have hzt_ne_t : z * t ≠ t := hztt
  have hc12 := hcross (A := Az) (B := At) hnormQ hnormAt hAzC hAtC hsqAz hsqAt hzt hinvAz
  have hc13 := hcross (A := Az) (B := Azt) hnormQ hnormAzt hAzC hAztC hsqAz hsqAzt
    (fun h1 => hztz h1.symm) hinvAz
  have hc23 := hcross (A := At) (B := Azt) hnormAt hnormAzt hAtC hAztC hsqAt hsqAzt
    (fun h1 => hztt h1.symm) hinvAt
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ W := by
    rintro x ((hx | hx) | hx) y ((hy | hy) | hy)
    · exact hsame hzW hcAz x hx y hy
    · exact hc12 x hx y hy
    · exact hc13 x hx y hy
    · exact hcross' hc12 x hx y hy
    · exact hsame htW hcAt x hx y hy
    · exact hc23 x hx y hy
    · exact hcross' hc13 x hx y hy
    · exact hcross' hc23 x hx y hy
    · exact hsame hztW hcAzt x hx y hy
  have hsqR : ∀ r ∈ R, r * r ∈ W := sq_mem_of_mem_closure hXC hWC hsqX hcommX
  have hnormR : ∀ {k : G}, (∀ x ∈ X, k * x * k⁻¹ ∈ X) → ∀ r ∈ R, k * r * k⁻¹ ∈ R := by
    intro k hk r hr
    induction hr using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hk x hx)
    | one => simp [one_mem]
    | mul a b _ _ ha hb =>
      have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  have hρC : ∀ {x : G}, x ∈ C → ρ * x * ρ⁻¹ ∈ C := by
    intro x hx
    obtain ⟨h1, h2⟩ := hmemC.mp hx
    have h3 := hCzt hx
    refine hmemC.mpr ⟨?_, ?_⟩
    · calc ρ * x * ρ⁻¹ * z = ρ * x * ρ⁻¹ * (ρ * (z * t) * ρ⁻¹) := by rw [hρzt]
        _ = ρ * (x * (z * t)) * ρ⁻¹ := by group
        _ = ρ * (z * t * x) * ρ⁻¹ := by rw [h3]
        _ = ρ * (z * t) * ρ⁻¹ * (ρ * x * ρ⁻¹) := by group
        _ = z * (ρ * x * ρ⁻¹) := by rw [hρzt]
    · calc ρ * x * ρ⁻¹ * t = ρ * x * ρ⁻¹ * (ρ * z * ρ⁻¹) := by rw [hρz]
        _ = ρ * (x * z) * ρ⁻¹ := by group
        _ = ρ * (z * x) * ρ⁻¹ := by rw [h1]
        _ = ρ * z * ρ⁻¹ * (ρ * x * ρ⁻¹) := by group
        _ = t * (ρ * x * ρ⁻¹) := by rw [hρz]
  have hρX : ∀ x ∈ X, ρ * x * ρ⁻¹ ∈ X := by
    rintro x ((hx | hx) | hx)
    · left; right
      refine ⟨?_, hρC hx.2⟩
      have := conj_mem_qAt (show x ∈ qAt z z by rw [qAt_self]; exact hx.1) ρ
      rwa [hρz] at this
    · right
      refine ⟨?_, hρC hx.2⟩
      have := conj_mem_qAt hx.1 ρ
      rwa [hρt] at this
    · left; left
      refine ⟨?_, hρC hx.2⟩
      have := conj_mem_qAt hx.1 ρ
      rwa [hρzt, qAt_self] at this
  have hρR : ∀ r ∈ R, ρ * r * ρ⁻¹ ∈ R := hnormR hρX
  have hinvR : ∀ r ∈ R, r * r = 1 → r = 1 ∨ r = z ∨ r = t ∨ r = z * t := by
    intro r hr hr2
    have hrC := hRC hr
    have hrQ := hall r (hCH hrC) hr2
    exact IsTypeH2.eq_of_comm_of_sq_eq_one h htQ ht2 ht1 hzt.symm hrQ (hmemC.mp hrC).2 hr2
  have hsqR' : ∀ r ∈ R, r * r = 1 ∨ r * r = z ∨ r * r = t ∨ r * r = z * t :=
    fun r hr => hWV _ (hsqR r hr)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2R : IsPGroup 2 R := IsPGroup.iff_orderOf.mpr fun r => by
    have h4 : r ^ 4 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      exact hVt (hsqR' r r.2)
    have hdvd : orderOf r ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨i, hi⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2R
  have hRH : R ≤ H := fun r hr => hCH (hRC hr)
  have hdvdH : Nat.card R ∣ 1920 := h.card_centralizer ▸ Subgroup.card_dvd_of_le hRH
  have hn7 : n ≤ 7 := by
    rw [hn] at hdvdH
    have : 2 ^ n ∣ 2 ^ 7 * 15 := by simpa using hdvdH
    have hcop : Nat.Coprime (2 ^ n) 15 := Nat.Coprime.pow_left n (by norm_num)
    have := (Nat.Coprime.dvd_of_dvd_mul_right hcop this)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have htR : t ∈ R := Subgroup.subset_closure (Or.inl (Or.inl ⟨htQ, hmemC.mpr ⟨htz, rfl⟩⟩))
  have hRle : Nat.card R ≤ 64 := by
    by_contra hgt
    have hn7' : n = 7 := by
      have : 2 ^ 6 < 2 ^ n := by rw [← hn]; omega
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      omega
    have hR128 : Nat.card R = 128 := by rw [hn, hn7']; norm_num
    have hSyl : IsSylowTwoOf R H := by
      refine ⟨hRH, h2R, ?_⟩
      have hidx := Subgroup.index_mul_card (R.subgroupOf H)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv, hR128,
        h.card_centralizer] at hidx
      have : (R.subgroupOf H).index = 15 := by omega
      rw [this]
      decide
    have htc : ∀ s ∈ R, t * s = s * t := fun s hs => ((hmemC.mp (hRC hs)).2).symm
    rcases h.eq_one_or_eq_of_mem_center_sylow hSyl htR htc with h1 | h1
    · exact ht1 h1
    · exact hzt h1.symm
  have h12 : 12 ≤ (sqSet R z).ncard := by
    have hsub : {q : G | q ∈ Q ∧ q * t = t * q ∧ q * q = z} ⊆ sqSet R z := by
      rintro q ⟨hq, hqt, hq2⟩
      refine ⟨Subgroup.subset_closure (Or.inl (Or.inl ⟨hq, hmemC.mpr ⟨hQcomm hq, hqt⟩⟩)), hq2⟩
    have hfin : (sqSet R z).Finite := Set.toFinite _
    exact (IsTypeH2.twelve_le_ncard_sq_eq h htQ ht2 ht1 hzt.symm).trans (Set.ncard_le_ncard hsub hfin)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ₀', hσ₀'⟩ := exists_prime_orderOf_dvd_card' (G := H) 3
    (by rw [h.card_centralizer]; norm_num)
  set σ₀ : G := (σ₀' : G) with hσ₀
  have hσ₀3 : orderOf σ₀ = 3 := by rw [hσ₀, Subgroup.orderOf_coe, hσ₀']
  have hσ₀H : σ₀ ∈ H := σ₀'.2
  set N : Set G := {q : G | q ∈ Q ∧ q * q = 1 ∧ q ≠ 1 ∧ q ≠ z} with hN
  have hP3 : IsPGroup 3 (Subgroup.zpowers σ₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ₀3, pow_one])
  have hPH : Subgroup.zpowers σ₀ ≤ H := Subgroup.zpowers_le.mpr hσ₀H
  have hNstab : ∀ k ∈ Subgroup.zpowers σ₀, ∀ x ∈ N, k * x * k⁻¹ ∈ N := by
    rintro k hk x ⟨hx, hx2, hx1, hxz⟩
    have hkH := hPH hk
    have hkz : k * z * k⁻¹ = z := by rw [← (hmemH.mp hkH)]; group
    refine ⟨hQnorm hkH hx, ?_, ?_, ?_⟩
    · calc k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    · intro h1
      apply hx1
      calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      apply hxz
      calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
        _ = k⁻¹ * (k * z * k⁻¹) * k := by rw [h1, hkz]
        _ = z := by group
  have hNfin : Finite N := Set.toFinite N |>.to_subtype
  have hmod := card_modEq_card_fixed 3 (Subgroup.zpowers σ₀) hP3 N hNstab
  rw [Nat.card_coe_set_eq, IsTypeH2.ncard_noncentral h] at hmod
  have hfixne : {x : G | x ∈ N ∧ ∀ k ∈ Subgroup.zpowers σ₀, k * x = x * k}.Nonempty := by
    rw [Nat.card_coe_set_eq] at hmod
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨u, ⟨huQ, hu2, hu1, huz⟩, hufix⟩ := hfixne
  have hσ₀u : σ₀ * u = u * σ₀ := hufix σ₀ (Subgroup.mem_zpowers σ₀)
  obtain ⟨c3, hc3H, hc3⟩ := h.exists_conj_of_noncentral huQ hu2 hu1 huz htQ ht2 ht1 hzt.symm
  set σ := c3 * σ₀ * c3⁻¹ with hσdef
  have hσH : σ ∈ H := mul_mem (mul_mem hc3H hσ₀H) (inv_mem hc3H)
  have hσz : σ * z = z * σ := (hmemH.mp hσH).symm
  have hσt : σ * t = t * σ := by
    rw [hσdef, ← hc3]
    calc c3 * σ₀ * c3⁻¹ * (c3 * u * c3⁻¹) = c3 * (σ₀ * u) * c3⁻¹ := by group
      _ = c3 * (u * σ₀) * c3⁻¹ := by rw [hσ₀u]
      _ = c3 * u * c3⁻¹ * (c3 * σ₀ * c3⁻¹) := by group
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσdef, conj_pow, ← hσ₀3, pow_orderOf_eq_one]; group
  have hσC : σ ∈ C := hmemC.mpr ⟨hσz, hσt⟩
  have hσX : ∀ x ∈ X, σ * x * σ⁻¹ ∈ X := by
    rintro x ((hx | hx) | hx)
    · exact Or.inl (Or.inl (hnormQ hσC hx))
    · exact Or.inl (Or.inr (hnormAt hσC hx))
    · exact Or.inr (hnormAzt hσC hx)
  have hσR : ∀ r ∈ R, σ * r * σ⁻¹ ∈ R := hnormR hσX
  have hσnot : ∃ r ∈ R, σ * r ≠ r * σ := by
    by_contra hall'
    push Not at hall'
    have hP3' : IsPGroup 3 (Subgroup.zpowers σ) := by
      have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; rfl)
    have hQstab : ∀ k ∈ Subgroup.zpowers σ, ∀ x ∈ (Q : Set G), k * x * k⁻¹ ∈ (Q : Set G) :=
      fun k hk x hx => hQnorm ((Subgroup.zpowers_le.mpr hσH) hk) hx
    have hQfin : Finite (Q : Set G) := Set.toFinite _ |>.to_subtype
    have hmodQ := card_modEq_card_fixed 3 (Subgroup.zpowers σ) hP3' (Q : Set G) hQstab
    set F := Q ⊓ Subgroup.centralizer ({σ} : Set G) with hF
    have hFeq : {x : G | x ∈ (Q : Set G) ∧ ∀ k ∈ Subgroup.zpowers σ, k * x = x * k} =
        (F : Set G) := by
      ext x
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe, hF, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hx, hk⟩
        exact ⟨hx, (hk σ (Subgroup.mem_zpowers σ)).symm⟩
      · rintro ⟨hx, hσx⟩
        refine ⟨hx, fun k hk => ?_⟩
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        exact (Commute.zpow_left (show Commute σ x from hσx.symm) m)
    rw [hFeq, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hmodQ
    have hQ32 : (Q : Set G).ncard = 32 := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.card_pCoreOf]
    have hFn : (F : Set G).ncard = Nat.card F := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    rw [hQ32, hFn] at hmodQ
    have hFdvd : Nat.card F ∣ 32 := h.card_pCoreOf ▸ Subgroup.card_dvd_of_le inf_le_left
    have hF16 : 16 ≤ Nat.card F := by
      have hsub : {q : G | q ∈ Q ∧ q * t = t * q} ⊆ (F : Set G) := by
        rintro q ⟨hq, hqt⟩
        refine ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        exact (hall' q (Subgroup.subset_closure
          (Or.inl (Or.inl ⟨hq, hmemC.mpr ⟨hQcomm hq, hqt⟩⟩)))).symm
      rw [← hFn]
      exact (IsTypeH2.sixteen_le_ncard_comm h htQ ht2 ht1 hzt.symm).trans
        (Set.ncard_le_ncard hsub (Set.toFinite _))
    have hF32 : Nat.card F = 32 := by
      have hmem : Nat.card F ∈ Nat.divisors 32 := Nat.mem_divisors.mpr ⟨hFdvd, by norm_num⟩
      rw [show Nat.divisors 32 = {1, 2, 4, 8, 16, 32} by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      unfold Nat.ModEq at hmodQ
      rcases hmem with h1 | h1 | h1 | h1 | h1 | h1 <;> omega
    have hFQ : F = Q := Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [hF32, h.card_pCoreOf])
    have hσQc : σ ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqF : q ∈ F := hFQ ▸ hq
      exact Subgroup.mem_centralizer_singleton_iff.mp hqF.2
    have hσQ : σ ∈ Q := h.charTwo ⟨hσH, hσQc⟩
    have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 H
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨σ, hσQ⟩
    rw [Subgroup.orderOf_mk] at hj
    have hdvd3 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    rw [hj] at hdvd3
    have hj0 : j = 0 := by
      rcases j with _ | j
      · rfl
      · exfalso
        have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans hdvd3
        omega
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    have : σ₀ = 1 := by
      calc σ₀ = c3⁻¹ * σ * c3 := by rw [hσdef]; group
        _ = 1 := by rw [hj]; group
    rw [this, orderOf_one] at hσ₀3
    omega
  have hzR : z ∈ R := Subgroup.subset_closure (Or.inl (Or.inl ⟨hzQ, hmemC.mpr ⟨rfl, htz.symm⟩⟩))
  exact false_of_klein_squares (R := R) hzR htR hz2 ht2 hz1 ht1 hzt
    (fun r hr => (hmemC.mp (hRC hr)).1) (fun r hr => (hmemC.mp (hRC hr)).2)
    hsqR' hinvR hRle h12 hρR hρz hρt hσ3 hσR hσz hσt hσnot

theorem nonempty_mulEquiv_model_of_typeH2 (h : IsTypeH2 G z) :
    Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* J2Cz.Model) := by
  obtain ⟨t, htC, ht2, htQ⟩ := IsTypeH2.exists_involution_not_mem_pCoreOf h
  obtain ⟨L, hLC, hLQ, hL⟩ := h.exists_complement_of_involution htC ht2 htQ
  exact h.nonempty_mulEquiv_model hLC hLQ hL

end IsTypeH2

end CFSG.Quasithin.Kleidman
