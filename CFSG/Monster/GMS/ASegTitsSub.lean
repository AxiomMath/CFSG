module

public import CFSG.Monster.GMS.ASegTits

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Assembly CFSG.Monster.GMS.S4Family

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Normalizer

variable {G : Type*} [Group G]

theorem mem_normalizer_iff_forall [Finite G] {S : Set G} {g : G} :
    g ∈ Subgroup.normalizer S ↔ ∀ n ∈ S, g * n * g⁻¹ ∈ S := by
  refine ⟨fun h n hn => (Subgroup.mem_set_normalizer_iff.1 h n).1 hn, fun h => ?_⟩
  refine Subgroup.mem_set_normalizer_iff.2 fun n => ⟨h n, fun hn => ?_⟩
  have hmaps : Set.MapsTo (fun x : G => g * x * g⁻¹) S S := fun x hx => h x hx
  have hinj : Set.InjOn (fun x : G => g * x * g⁻¹) S := fun x _ y _ hxy => by simpa using hxy
  obtain ⟨m, hm, hmn⟩ := (((Set.toFinite S).injOn_iff_bijOn_of_mapsTo hmaps).1 hinj).surjOn hn
  have : m = n := by simpa using hmn
  exact this ▸ hm

theorem mem_normalizer_triple [Finite G] {p q r g : G} (hp : g * p * g⁻¹ ∈ ({p, q, r} : Set G))
    (hq : g * q * g⁻¹ ∈ ({p, q, r} : Set G)) (hr : g * r * g⁻¹ ∈ ({p, q, r} : Set G)) :
    g ∈ Subgroup.normalizer ({p, q, r} : Set G) := by
  rw [mem_normalizer_iff_forall]
  intro n hn
  rcases hn with rfl | rfl | rfl <;> assumption

theorem mem_centralizer_conj_iff_of_mem_normalizer {S : Set G} {g : G}
    (hg : g ∈ Subgroup.normalizer S) (x : G) :
    x ∈ Subgroup.centralizer S ↔ g * x * g⁻¹ ∈ Subgroup.centralizer S := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer S → ∀ x : G, x ∈ Subgroup.centralizer S →
      g * x * g⁻¹ ∈ Subgroup.centralizer S := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro c hc
    have hc' : g⁻¹ * c * g ∈ S := (Subgroup.mem_set_normalizer_iff''.1 hg c).1 hc
    have := hx _ hc'
    calc c * (g * x * g⁻¹) = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * c := by group
  refine ⟨key hg x, fun h => ?_⟩
  have := key ((Subgroup.normalizer S).inv_mem hg) _ h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem inv_mul_mem_centralizer_iff {m g x : G} :
    m⁻¹ * g ∈ C[x] ↔ g * x * g⁻¹ = m * x * m⁻¹ := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ = m * (m⁻¹ * g * x) * g⁻¹ := by group
      _ = m * (x * (m⁻¹ * g)) * g⁻¹ := by rw [h]
      _ = m * x * m⁻¹ := by group
  · intro h
    calc m⁻¹ * g * x = m⁻¹ * (g * x * g⁻¹) * g := by group
      _ = m⁻¹ * (m * x * m⁻¹) * g := by rw [h]
      _ = x * (m⁻¹ * g) := by group

theorem inv_mul_mem_K_iff {m g a y : G} :
    m⁻¹ * g ∈ C[a] ⊓ C[y] ↔ g * a * g⁻¹ = m * a * m⁻¹ ∧ g * y * g⁻¹ = m * y * m⁻¹ := by
  rw [Subgroup.mem_inf, inv_mul_mem_centralizer_iff, inv_mul_mem_centralizer_iff]

theorem conj_comp (m₁ m₂ x : G) :
    (m₁ * m₂) * x * (m₁ * m₂)⁻¹ = m₁ * (m₂ * x * m₂⁻¹) * m₁⁻¹ := by group

end Normalizer

section Tri

variable {G : Type*} [Group G]

@[expose] def tri0 (a y : G) : Set G := {a, y, a * y}

@[expose] def tri1 (a y z : G) : Set G := {a, y, a * y * z}

@[expose] def Xt0 (a y : G) : Subgroup G := Subgroup.normalizer (tri0 a y)

@[expose] def Xt1 (a y z : G) : Subgroup G := C[z] ⊓ Subgroup.normalizer (tri1 a y z)

theorem centralizer_tri0 (a y : G) : Subgroup.centralizer (tri0 a y) = C[a] ⊓ C[y] := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h a (Or.inl rfl)).symm, (h y (Or.inr (Or.inl rfl))).symm⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases hc with rfl | rfl | rfl
    · exact h1.symm
    · exact h2.symm
    · calc a * y * x = a * (y * x) := mul_assoc _ _ _
        _ = a * (x * y) := by rw [h2]
        _ = a * x * y := (mul_assoc _ _ _).symm
        _ = x * a * y := by rw [h1]
        _ = x * (a * y) := mul_assoc _ _ _


theorem mem_Xt0_iff [Finite G] {a y g : G} :
    g ∈ Xt0 a y ↔ g * a * g⁻¹ ∈ tri0 a y ∧ g * y * g⁻¹ ∈ tri0 a y ∧
      g * (a * y) * g⁻¹ ∈ tri0 a y :=
  ⟨fun h => ⟨mem_normalizer_iff_forall.1 h a (Or.inl rfl),
    mem_normalizer_iff_forall.1 h y (Or.inr (Or.inl rfl)),
    mem_normalizer_iff_forall.1 h (a * y) (Or.inr (Or.inr rfl))⟩,
  fun h => mem_normalizer_triple h.1 h.2.1 h.2.2⟩

theorem Xt0.cases [Finite G] {a y g : G} (hay : a ≠ y) (hg : g ∈ Xt0 a y) :
    (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨ (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a) ∨
      (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = a * y) ∨ (g * a * g⁻¹ = a * y ∧ g * y * g⁻¹ = a) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a * y) ∨ (g * a * g⁻¹ = a * y ∧ g * y * g⁻¹ = y) := by
  obtain ⟨h1, h2, -⟩ := mem_Xt0_iff.1 hg
  have hne : g * a * g⁻¹ ≠ g * y * g⁻¹ := fun h => hay (by simpa using h)
  rcases h1 with e1 | e1 | e1 <;> rcases h2 with e2 | e2 | e2 <;>
    first | exact absurd (e1.trans e2.symm) hne | tauto

theorem Xt0.mem_K_iff {a y g : G} (hg : g ∈ Xt0 a y) (x : G) :
    x ∈ C[a] ⊓ C[y] ↔ g * x * g⁻¹ ∈ C[a] ⊓ C[y] := by
  rw [← centralizer_tri0]
  exact mem_centralizer_conj_iff_of_mem_normalizer hg x

theorem K_le_Xt0 [Finite G] (a y : G) : C[a] ⊓ C[y] ≤ Xt0 a y := by
  intro k hk
  rw [← centralizer_tri0] at hk
  refine mem_normalizer_iff_forall.2 fun n hn => ?_
  have : k * n * k⁻¹ = n := by
    rw [← Subgroup.mem_centralizer_iff.1 hk n hn]
    group
  rw [this]
  exact hn

section Elements

variable [Finite G] {a y z : G}

theorem mem_Xt0_of_fix_or_swap (h : Comm3 a y z) {g : G}
    (hg : (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨ (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) :
    g ∈ Xt0 a y := by
  rw [Xt0]
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine mem_normalizer_triple ?_ ?_ ?_
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; exact Or.inr (Or.inl rfl)
    · rw [conj_mul_conj, h1, h2]; exact Or.inr (Or.inr rfl)
  · refine mem_normalizer_triple ?_ ?_ ?_
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; exact Or.inl rfl
    · rw [conj_mul_conj, h1, h2, h.ya]; exact Or.inr (Or.inr rfl)

theorem mem_Xt0_of_cycle (h : Comm3 a y z) {g : G} (h1 : g * a * g⁻¹ = y)
    (h2 : g * y * g⁻¹ = a * y) : g ∈ Xt0 a y := by
  rw [Xt0]
  refine mem_normalizer_triple ?_ ?_ ?_
  · rw [h1]; exact Or.inr (Or.inl rfl)
  · rw [h2]; exact Or.inr (Or.inr rfl)
  · rw [conj_mul_conj, h1, h2, show y * (a * y) = a by comm3_simp h]; exact Or.inl rfl

theorem mem_Xt0_of_transposition (h : Comm3 a y z) {g : G} (h1 : g * a * g⁻¹ = a)
    (h2 : g * y * g⁻¹ = a * y) : g ∈ Xt0 a y := by
  rw [Xt0]
  refine mem_normalizer_triple ?_ ?_ ?_
  · rw [h1]; exact Or.inl rfl
  · rw [h2]; exact Or.inr (Or.inr rfl)
  · rw [conj_mul_conj, h1, h2, show a * (a * y) = y by comm3_simp h]; exact Or.inr (Or.inl rfl)

theorem exists_mem_inv_mul_mem_K (h : Comm3 a y z) (hay : a ≠ y) {s t : G}
    (hs1 : s * a * s⁻¹ = y) (hs2 : s * y * s⁻¹ = a) (ht1 : t * a * t⁻¹ = a)
    (ht2 : t * y * t⁻¹ = a * y) (M : Subgroup G) (hsM : s ∈ M) (htM : t ∈ M) {g : G}
    (hg : g ∈ Xt0 a y) : ∃ m ∈ M, m⁻¹ * g ∈ C[a] ⊓ C[y] := by
  rcases Xt0.cases hay hg with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
      ⟨e1, e2⟩
  · exact ⟨1, M.one_mem, inv_mul_mem_K_iff.2 ⟨by simp [e1], by simp [e2]⟩⟩
  · exact ⟨s, hsM, inv_mul_mem_K_iff.2 ⟨e1.trans hs1.symm, e2.trans hs2.symm⟩⟩
  · exact ⟨t, htM, inv_mul_mem_K_iff.2 ⟨e1.trans ht1.symm, e2.trans ht2.symm⟩⟩
  · refine ⟨t * s, M.mul_mem htM hsM, inv_mul_mem_K_iff.2 ⟨?_, ?_⟩⟩
    · rw [e1, conj_comp, hs1, ht2]
    · rw [e2, conj_comp, hs2, ht1]
  · refine ⟨s * t, M.mul_mem hsM htM, inv_mul_mem_K_iff.2 ⟨?_, ?_⟩⟩
    · rw [e1, conj_comp, ht1, hs1]
    · rw [e2, conj_comp, ht2, conj_mul_conj, hs1, hs2, h.ya]
  · refine ⟨s * t * s, M.mul_mem (M.mul_mem hsM htM) hsM, inv_mul_mem_K_iff.2 ⟨?_, ?_⟩⟩
    · rw [e1, conj_comp, conj_comp s t, hs1, ht2, conj_mul_conj, hs1, hs2, h.ya]
    · rw [e2, conj_comp, conj_comp s t, hs2, ht1, hs1]

theorem mem_Xt1_of_swap (h : Comm3 a y z) {g : G} (h1 : g * a * g⁻¹ = y) (h2 : g * y * g⁻¹ = a)
    (h3 : g * z * g⁻¹ = z) : g ∈ Xt1 a y z := by
  refine ⟨mem_centralizer_of_conj_eq h3, ?_⟩
  refine mem_normalizer_triple ?_ ?_ ?_
  · rw [h1]; exact Or.inr (Or.inl rfl)
  · rw [h2]; exact Or.inl rfl
  · rw [show g * (a * y * z) * g⁻¹ = (g * a * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) by group,
      h1, h2, h3, show y * a * z = a * y * z by comm3_simp h]
    exact Or.inr (Or.inr rfl)

theorem mem_Xt1_of_cycle (h : Comm3 a y z) {g : G} (h1 : g * a * g⁻¹ = y)
    (h2 : g * y * g⁻¹ = a * y * z) (h3 : g * z * g⁻¹ = z) : g ∈ Xt1 a y z := by
  refine ⟨mem_centralizer_of_conj_eq h3, ?_⟩
  refine mem_normalizer_triple ?_ ?_ ?_
  · rw [h1]; exact Or.inr (Or.inl rfl)
  · rw [h2]; exact Or.inr (Or.inr rfl)
  · rw [show g * (a * y * z) * g⁻¹ = (g * a * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) by group,
      h1, h2, h3, show y * (a * y * z) * z = a by comm3_simp h]
    exact Or.inl rfl

end Elements

end Tri

section Decomposition

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ y z : G}

omit [Finite G] in
theorem ASegData.a_ne_y (hG : GMSF1Type d₀ a z₀) (D : ASegData a z₀ y z) : a ≠ y := fun h =>
  S365.ne_one_of_isConj_a hG.1.1 D.isConj_ay
    (by rw [← h]; exact mul_self_eq_one_of_orderOf hG.1.1)

theorem ASegData.exists_mul_of_mem_Xt0 (EL : EightGroupLines a z₀) (hG : GMSF1Type d₀ a z₀)
    (D : ASegData a z₀ y z) {g : G} (hg : g ∈ Xt0 a y) :
    ∃ k ∈ C[a] ⊓ C[y], ∃ w ∈ Xt0 a y ⊓ C[z], g = k * w := by
  have h := D.comm3 hG
  obtain ⟨s, hs1, hs2, hs3⟩ := D.exists_s EL hG
  obtain ⟨t, ht1, ht2, ht3⟩ := D.exists_t' EL hG
  have hsW : s ∈ Xt0 a y ⊓ C[z] :=
    ⟨mem_Xt0_of_fix_or_swap h (Or.inr ⟨hs1, hs2⟩), mem_centralizer_of_conj_eq hs3⟩
  have htW : t ∈ Xt0 a y ⊓ C[z] :=
    ⟨mem_Xt0_of_transposition h ht1 ht2, mem_centralizer_of_conj_eq ht3⟩
  obtain ⟨m, hm, hk⟩ := exists_mem_inv_mul_mem_K h (D.a_ne_y hG) hs1 hs2 ht1 ht2
    (Xt0 a y ⊓ C[z]) hsW htW hg
  refine ⟨g * m⁻¹, ?_, m, hm, by group⟩
  have := (Xt0.mem_K_iff hm.1 (m⁻¹ * g)).1 hk
  have e : m * (m⁻¹ * g) * m⁻¹ = g * m⁻¹ := by group
  rwa [e] at this

end Decomposition

section Transport

variable {G G' : Type*} [Group G] [Group G'] {f : G → G'} {H : Subgroup G} {H' : Subgroup G'}

theorem forall_conj_mem_iff_of_isIsoOn (hf : IsIsoOn f H H') {S : Set G} {S' : Set G'}
    (hS : S ⊆ H) (himg : f '' S = S') {g : G} (hg : g ∈ H) :
    (∀ n ∈ S, g * n * g⁻¹ ∈ S) ↔ ∀ n' ∈ S', f g * n' * (f g)⁻¹ ∈ S' := by
  subst himg
  constructor
  · rintro h _ ⟨n, hn, rfl⟩
    rw [← iso_map_conj hf hg (hS hn)]
    exact ⟨g * n * g⁻¹, h n hn, rfl⟩
  · intro h n hn
    obtain ⟨m, hm, hmn⟩ := h (f n) ⟨n, hn, rfl⟩
    rw [← iso_map_conj hf hg (hS hn)] at hmn
    have := hf.injOn (hS hm) (H.mul_mem (H.mul_mem hg (hS hn)) (H.inv_mem hg)) hmn
    rw [← this]
    exact hm

theorem image_tri0 (hf : IsIsoOn f H H') {a y : G} (ha : a ∈ H) (hy : y ∈ H) :
    f '' tri0 a y = tri0 (f a) (f y) := by
  unfold tri0
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hf.map_mul a ha y hy]

theorem image_tri1 (hf : IsIsoOn f H H') {a y z : G} (ha : a ∈ H) (hy : y ∈ H) (hz : z ∈ H) :
    f '' tri1 a y z = tri1 (f a) (f y) (f z) := by
  unfold tri1
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    hf.map_mul (a * y) (H.mul_mem ha hy) z hz, hf.map_mul a ha y hy]

theorem tri0_subset {a y : G} (ha : a ∈ H) (hy : y ∈ H) : tri0 a y ⊆ (H : Set G) := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · exact ha
  · exact hy
  · exact H.mul_mem ha hy

theorem tri1_subset {a y z : G} (ha : a ∈ H) (hy : y ∈ H) (hz : z ∈ H) :
    tri1 a y z ⊆ (H : Set G) := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · exact ha
  · exact hy
  · exact H.mul_mem (H.mul_mem ha hy) hz

theorem mem_Xt0_iff_of_isIsoOn [Finite G] [Finite G'] (hf : IsIsoOn f H H') {a y : G}
    (ha : a ∈ H) (hy : y ∈ H) {g : G} (hg : g ∈ H) :
    f g ∈ Xt0 (f a) (f y) ↔ g ∈ Xt0 a y := by
  rw [Xt0, Xt0, mem_normalizer_iff_forall, mem_normalizer_iff_forall]
  exact (forall_conj_mem_iff_of_isIsoOn hf (tri0_subset ha hy) (image_tri0 hf ha hy) hg).symm

theorem mem_Xt1_iff_of_isIsoOn [Finite G] [Finite G'] (hf : IsIsoOn f H H') {a y z : G}
    (ha : a ∈ H) (hy : y ∈ H) (hz : z ∈ H) {g : G} (hg : g ∈ H) :
    f g ∈ Xt1 (f a) (f y) (f z) ↔ g ∈ Xt1 a y z := by
  rw [Xt1, Xt1, Subgroup.mem_inf, Subgroup.mem_inf, iso_mem_centralizer_iff hf hg hz,
    mem_normalizer_iff_forall, mem_normalizer_iff_forall]
  exact and_congr_right fun _ =>
    (forall_conj_mem_iff_of_isIsoOn hf (tri1_subset ha hy hz) (image_tri1 hf ha hy hz) hg).symm

end Transport

end CFSG.Monster.GMS
