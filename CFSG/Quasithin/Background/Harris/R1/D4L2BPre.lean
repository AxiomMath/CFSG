module

public import CFSG.Quasithin.Background.Harris.R1.D4VertPres

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

variable {G Y : Type*} [Group G] [Group Y] {K : Subgroup G} {H₀ : Subgroup Y}

open Classical in
@[expose] noncomputable def ebar (e : ↥K ≃* ↥H₀) (x : G) : Y :=
  if h : x ∈ K then (e ⟨x, h⟩ : Y) else 1

theorem ebar_of_mem (e : ↥K ≃* ↥H₀) {x : G} (hx : x ∈ K) : ebar e x = (e ⟨x, hx⟩ : Y) := by
  simp [ebar, hx]

theorem ebar_mul (e : ↥K ≃* ↥H₀) {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    ebar e (x * y) = ebar e x * ebar e y := by
  rw [ebar_of_mem e (K.mul_mem hx hy), ebar_of_mem e hx, ebar_of_mem e hy]
  exact congrArg Subtype.val (map_mul e ⟨x, hx⟩ ⟨y, hy⟩)

theorem ebar_one (e : ↥K ≃* ↥H₀) : ebar e 1 = 1 := by
  rw [ebar_of_mem e K.one_mem]
  exact congrArg Subtype.val (map_one e)

theorem ebar_inv (e : ↥K ≃* ↥H₀) {x : G} (hx : x ∈ K) : ebar e x⁻¹ = (ebar e x)⁻¹ := by
  rw [ebar_of_mem e (K.inv_mem hx), ebar_of_mem e hx]
  exact congrArg Subtype.val (map_inv e ⟨x, hx⟩)

theorem ebar_conj (e : ↥K ≃* ↥H₀) {k x : G} (hk : k ∈ K) (hx : x ∈ K) :
    ebar e (k * x * k⁻¹) = ebar e k * ebar e x * (ebar e k)⁻¹ := by
  rw [ebar_mul e (K.mul_mem hk hx) (K.inv_mem hk), ebar_mul e hk hx, ebar_inv e hk]

theorem ebar_pow (e : ↥K ≃* ↥H₀) {x : G} (hx : x ∈ K) (n : ℕ) :
    ebar e (x ^ n) = ebar e x ^ n := by
  induction n with
  | zero => simpa using ebar_one e
  | succ n ih => rw [pow_succ, ebar_mul e (K.pow_mem hx n) hx, ih, pow_succ]

theorem ebar_mem (e : ↥K ≃* ↥H₀) {x : G} (hx : x ∈ K) : ebar e x ∈ H₀ := by
  rw [ebar_of_mem e hx]
  exact (e ⟨x, hx⟩).2

theorem ebar_inj (e : ↥K ≃* ↥H₀) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (h : ebar e x = ebar e y) : x = y := by
  rw [ebar_of_mem e hx, ebar_of_mem e hy] at h
  exact congrArg Subtype.val (e.injective (Subtype.ext h))

theorem ebar_eq_one_iff (e : ↥K ≃* ↥H₀) {x : G} (hx : x ∈ K) : ebar e x = 1 ↔ x = 1 :=
  ⟨fun h => ebar_inj e hx K.one_mem (h.trans (ebar_one e).symm), fun h => by rw [h, ebar_one]⟩

theorem exists_ebar_eq (e : ↥K ≃* ↥H₀) {y : Y} (hy : y ∈ H₀) : ∃ x ∈ K, ebar e x = y := by
  refine ⟨((e.symm ⟨y, hy⟩ : ↥K) : G), (e.symm ⟨y, hy⟩).2, ?_⟩
  rw [ebar_of_mem e (e.symm ⟨y, hy⟩).2]
  simp

theorem exists_equiv_ebar (e : ↥K ≃* ↥H₀) {Q : Subgroup G} {U : Subgroup Y} (hQK : Q ≤ K)
    (hUH : U ≤ H₀) (hQt : ∀ k ∈ K, k ∈ Q ↔ ebar e k ∈ U) :
    ∃ ε : ↥Q ≃* ↥U, ∀ q : ↥Q, (ε q : Y) = ebar e (q : G) := by
  let φ : ↥Q →* ↥U :=
    { toFun := fun q => ⟨ebar e q, (hQt q (hQK q.2)).mp q.2⟩
      map_one' := Subtype.ext (ebar_one e)
      map_mul' := fun a b => Subtype.ext (ebar_mul e (hQK a.2) (hQK b.2)) }
  have hinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (ebar_inj e (hQK a.2) (hQK b.2) (congrArg Subtype.val hab))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hxK, hxy⟩ := exists_ebar_eq e (hUH y.2)
    exact ⟨⟨x, (hQt x hxK).mpr (hxy ▸ y.2)⟩, Subtype.ext hxy⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun q => rfl⟩

theorem mem_normalizer_ebar_iff (e : ↥K ≃* ↥H₀) {S : Subgroup G} {U : Subgroup Y}
    (hUH : U ≤ H₀) (heS : ∀ k ∈ K, k ∈ S ↔ ebar e k ∈ U) (hSK : S ≤ K) {k : G} (hk : k ∈ K) :
    k ∈ Subgroup.normalizer (S : Set G) ↔ ebar e k ∈ Subgroup.normalizer (U : Set Y) := by
  have hek : ebar e k ∈ H₀ := ebar_mem e hk
  constructor
  · intro hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨x, hxK, rfl⟩ := exists_ebar_eq e (hUH hy)
      have hxS : x ∈ S := (heS x hxK).mpr hy
      have h1 : k * x * k⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn x).mp hxS
      have := (heS _ (K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk))).mp h1
      rwa [ebar_conj e hk hxK] at this
    · intro hy
      have hyH : y ∈ H₀ := by
        have := H₀.mul_mem (H₀.mul_mem (H₀.inv_mem hek) (hUH hy)) hek
        simpa [mul_assoc] using this
      obtain ⟨x, hxK, rfl⟩ := exists_ebar_eq e hyH
      rw [← ebar_conj e hk hxK] at hy
      have h1 : k * x * k⁻¹ ∈ S := (heS _ (K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk))).mpr hy
      exact (heS x hxK).mp ((Subgroup.mem_normalizer_iff.mp hn x).mpr h1)
  · intro hn
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgK : g ∈ K := hSK hg
      have h1 := (Subgroup.mem_normalizer_iff.mp hn _).mp ((heS g hgK).mp hg)
      rw [← ebar_conj e hk hgK] at h1
      exact (heS _ (K.mul_mem (K.mul_mem hk hgK) (K.inv_mem hk))).mpr h1
    · intro hg
      have hkgK : k * g * k⁻¹ ∈ K := hSK hg
      have hgK : g ∈ K := by
        have := K.mul_mem (K.mul_mem (K.inv_mem hk) hkgK) hk
        simpa [mul_assoc] using this
      have h1 := (heS _ hkgK).mp hg
      rw [ebar_conj e hk hgK] at h1
      exact (heS g hgK).mpr ((Subgroup.mem_normalizer_iff.mp hn _).mpr h1)

theorem mem_centralizer_ebar_iff (e : ↥K ≃* ↥H₀) {S : Subgroup G} {U : Subgroup Y}
    (hUH : U ≤ H₀) (heS : ∀ k ∈ K, k ∈ S ↔ ebar e k ∈ U) (hSK : S ≤ K) {k : G} (hk : k ∈ K) :
    k ∈ Subgroup.centralizer (S : Set G) ↔ ebar e k ∈ Subgroup.centralizer (U : Set Y) := by
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hxK, rfl⟩ := exists_ebar_eq e (hUH hy)
    have hxS : x ∈ S := (heS x hxK).mpr hy
    have := Subgroup.mem_centralizer_iff.mp hc x hxS
    rw [← ebar_mul e hxK hk, this, ebar_mul e hk hxK]
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgK : g ∈ K := hSK hg
    have := Subgroup.mem_centralizer_iff.mp hc _ ((heS g hgK).mp hg)
    rw [← ebar_mul e hgK hk, ← ebar_mul e hk hgK] at this
    exact ebar_inj e (K.mul_mem hgK hk) (K.mul_mem hk hgK) this

theorem evalWord_ebar (e : ↥K ≃* ↥H₀) {m : ℕ} (g : Fin m → G) (gY : Fin m → Y)
    (r : List (Fin m × Bool)) (hr : ∀ p ∈ r, g p.1 ∈ K ∧ ebar e (g p.1) = gY p.1) :
    evalWord g r ∈ K ∧ ebar e (evalWord g r) = evalWord gY r := by
  induction r with
  | nil => exact ⟨K.one_mem, by simp [evalWord_nil, ebar_one]⟩
  | cons p r ih =>
    obtain ⟨ih1, ih2⟩ := ih fun q hq => hr q (List.mem_cons_of_mem p hq)
    obtain ⟨hp1, hp2⟩ := hr p List.mem_cons_self
    rw [evalWord_cons, evalWord_cons]
    obtain ⟨i, s⟩ := p
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp1 hp2 ⊢
      refine ⟨K.mul_mem (K.inv_mem hp1) ih1, ?_⟩
      rw [ebar_mul e (K.inv_mem hp1) ih1, ebar_inv e hp1, hp2, ih2]
    · simp only [↓reduceIte] at hp1 hp2 ⊢
      exact ⟨K.mul_mem hp1 ih1, by rw [ebar_mul e hp1 ih1, hp2, ih2]⟩

theorem evalWord_eq_one_of_ebar (e : ↥K ≃* ↥H₀) {m : ℕ} (g : Fin m → G) (gY : Fin m → Y)
    (r : List (Fin m × Bool)) (hr : ∀ p ∈ r, g p.1 ∈ K ∧ ebar e (g p.1) = gY p.1)
    (h1 : evalWord gY r = 1) : evalWord g r = 1 := by
  obtain ⟨h2, h3⟩ := evalWord_ebar e g gY r hr
  rw [h1] at h3
  exact (ebar_eq_one_iff e h2).mp h3

end CFSG.Quasithin.Background.Harris.R1.D4Vert
