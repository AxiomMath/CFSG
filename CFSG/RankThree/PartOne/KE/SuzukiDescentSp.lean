module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer

public section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Embedding

variable {K L : Type} [Field K] [Field L]

theorem minorMap_map_hom (f : K →+* L) (g : Matrix (Fin 4) (Fin 4) K) :
    minorMap (g.map f) = (minorMap g).map f := by
  ext A B
  simp only [minorMap_apply, Matrix.map_apply, map_sub, map_mul]

@[expose] def antiSpMap (f : K →+* L) : antiSp K →* antiSp L :=
  ((GeneralLinearGroup.map f).comp (antiSp K).subtype).codRestrict (antiSp L) fun g => by
    rw [mem_antiSp]
    change ((glMat g).map f)ᵀ * minorJ L * (glMat g).map f = minorJ L
    rw [← minorJ_map f, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      mem_antiSp.mp g.2]

theorem glMat_antiSpMap (f : K →+* L) (g : antiSp K) :
    glMat (antiSpMap f g : GL (Fin 4) L) = (glMat (g : GL (Fin 4) K)).map f :=
  rfl

theorem antiSpMap_injective (f : K →+* L) : Function.Injective (antiSpMap f) := by
  intro g h hgh
  have h1 := congrArg (fun x : antiSp L => glMat (x : GL (Fin 4) L)) hgh
  simp only [glMat_antiSpMap] at h1
  exact Subtype.ext (Units.ext (Matrix.ext fun i j => f.injective (congrFun (congrFun h1 i) j)))

@[expose] noncomputable def szEmbed {a : ℕ} [CharP K 2] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : K →+* L) : suzukiGroup a K →* antiSp L :=
  (antiSpMap f).comp (Subgroup.inclusion (suzukiGroup_le_antiSp hK))

theorem glMat_szEmbed {a : ℕ} [CharP K 2] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (f : K →+* L) (g : suzukiGroup a K) :
    glMat (szEmbed hK f g : GL (Fin 4) L) = (glMat (g : GL (Fin 4) K)).map f :=
  rfl

theorem szEmbed_injective {a : ℕ} [CharP K 2] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (f : K →+* L) : Function.Injective (szEmbed hK f) :=
  (antiSpMap_injective f).comp (Subgroup.inclusion_injective _)

theorem exists_glMap_eq_of_entries (f : K →+* L) (g : GL (Fin 4) L)
    (h : ∀ i j, (g : Matrix (Fin 4) (Fin 4) L) i j ∈ Set.range f) :
    ∃ g₀ : GL (Fin 4) K, (GeneralLinearGroup.map f g₀ : GL (Fin 4) L) = g := by
  choose m hm using h
  set m₀ : Matrix (Fin 4) (Fin 4) K := Matrix.of m with hm₀
  have hmap : m₀.map f = (g : Matrix (Fin 4) (Fin 4) L) := by
    ext i j
    exact hm i j
  have hdet : m₀.det ≠ 0 := by
    intro h0
    have h1 : ((g : Matrix (Fin 4) (Fin 4) L)).det = f m₀.det := by
      rw [← hmap]
      exact (RingHom.map_det f m₀).symm
    rw [h0, map_zero] at h1
    exact (Matrix.isUnits_det_units g).ne_zero h1
  refine ⟨Matrix.nonsingInvUnit m₀ (isUnit_iff_ne_zero.2 hdet), Units.ext ?_⟩
  exact hmap

end Embedding

section Powers

variable {L : Type} [Field L] [CharP L 2]

theorem antiFrobPowHom_apply_add (m n : ℕ) (g : antiSp L) :
    antiFrobPowHom L (m + n) g = antiFrobPowHom L m (antiFrobPowHom L n g) := by
  apply antiSp_ext
  simp only [glMat_antiFrobPowHom, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  rw [← pow_mul, ← pow_add, add_comm]

theorem antiFrobPowHom_zero (g : antiSp L) : antiFrobPowHom L 0 g = g := by
  apply antiSp_ext
  rw [glMat_antiFrobPowHom]
  ext i j
  simp

theorem minorHom_antiFrobPowHom (n : ℕ) (g : antiSp L) :
    minorHom L (antiFrobPowHom L n g) = antiFrobPowHom L n (minorHom L g) := by
  apply antiSp_ext
  rw [glMat_minorHom, glMat_antiFrobPowHom, glMat_antiFrobPowHom, glMat_minorHom,
    minorMap_map_pow]

theorem minorHom_minorHom_eq_antiFrobPowHom_one (g : antiSp L) :
    minorHom L (minorHom L g) = antiFrobPowHom L 1 g := by
  rw [minorHom_minorHom]
  apply antiSp_ext
  rw [glMat_frobHom, glMat_antiFrobPowHom]
  simp only [pow_one]

variable {b : ℕ} {S₀ : MulAut (antiSp L)}
  (hS : ∀ g : antiSp L, glMat (S₀ g : GL (Fin 4) L) =
    (minorMap (glMat (g : GL (Fin 4) L))).map (fun x => x ^ 2 ^ b))

include hS in
theorem S0_apply (g : antiSp L) : S₀ g = antiFrobPowHom L b (minorHom L g) := by
  apply antiSp_ext
  rw [hS, glMat_antiFrobPowHom, glMat_minorHom]

include hS in
theorem S0_sq (g : antiSp L) : (S₀ ^ 2) g = antiFrobPowHom L (2 * b + 1) g := by
  rw [sq, MulAut.mul_apply, S0_apply hS, S0_apply hS, minorHom_antiFrobPowHom,
    minorHom_minorHom_eq_antiFrobPowHom_one, ← antiFrobPowHom_apply_add,
    ← antiFrobPowHom_apply_add]
  congr 2
  omega

include hS in
theorem S0_pow_two_mul (j : ℕ) (g : antiSp L) :
    (S₀ ^ (2 * j)) g = antiFrobPowHom L ((2 * b + 1) * j) g := by
  induction j generalizing g with
  | zero => simp [antiFrobPowHom_zero]
  | succ j ih =>
    rw [mul_add, mul_one, pow_add, MulAut.mul_apply, S0_sq hS, ih, ← antiFrobPowHom_apply_add]
    congr 1

include hS in
theorem S0_pow_two_mul_add_one (j : ℕ) (g : antiSp L) :
    (S₀ ^ (2 * j + 1)) g = antiFrobPowHom L ((2 * b + 1) * j + b) (minorHom L g) := by
  rw [pow_succ', MulAut.mul_apply, S0_pow_two_mul hS, S0_apply hS, minorHom_antiFrobPowHom,
    ← antiFrobPowHom_apply_add, Nat.add_comm b ((2 * b + 1) * j)]

include hS in
theorem fixed_of_S0_pow {m a : ℕ} (ha : a = (2 * b + 1) * m + b) {h : antiSp L}
    (hh : (S₀ ^ (2 * m + 1)) h = h) :
    minorHom L h = antiFrobPowHom L (a + 1) h ∧ antiFrobPowHom L (2 * a + 1) h = h := by
  have h1 : antiFrobPowHom L a (minorHom L h) = h := by
    rw [ha]
    rw [S0_pow_two_mul_add_one hS] at hh
    exact hh
  have h2 : minorHom L h = antiFrobPowHom L (a + 1) h := by
    calc minorHom L h = minorHom L (antiFrobPowHom L a (minorHom L h)) := by rw [h1]
      _ = antiFrobPowHom L a (minorHom L (minorHom L h)) := minorHom_antiFrobPowHom _ _
      _ = antiFrobPowHom L a (antiFrobPowHom L 1 h) := by
        rw [minorHom_minorHom_eq_antiFrobPowHom_one]
      _ = antiFrobPowHom L (a + 1) h := by rw [← antiFrobPowHom_apply_add]
  refine ⟨h2, ?_⟩
  have e2 : 2 * a + 1 = a + (a + 1) := by omega
  calc antiFrobPowHom L (2 * a + 1) h
      = antiFrobPowHom L a (antiFrobPowHom L (a + 1) h) := by
        rw [e2, antiFrobPowHom_apply_add]
    _ = antiFrobPowHom L a (minorHom L h) := by rw [h2]
    _ = h := h1

end Powers

section Range

variable {K L : Type} [Field K] [Field L] [CharP K 2] [CharP L 2] [Finite K]

theorem mem_range_szEmbed {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : K →+* L)
    (hf : ∀ x : L, x ^ 2 ^ (2 * a + 1) = x → x ∈ Set.range f) {h : antiSp L}
    (h1 : minorHom L h = antiFrobPowHom L (a + 1) h) (h2 : antiFrobPowHom L (2 * a + 1) h = h) :
    ∃ g : suzukiGroup a K, szEmbed hK f g = h := by
  have hentries : ∀ i j, (glMat (h : GL (Fin 4) L)) i j ∈ Set.range f := by
    intro i j
    apply hf
    have := congrFun (congrFun (congrArg (fun x : antiSp L => glMat (x : GL (Fin 4) L)) h2) i) j
    rw [glMat_antiFrobPowHom] at this
    exact this
  obtain ⟨g₀, hg₀⟩ := exists_glMap_eq_of_entries f (h : GL (Fin 4) L) hentries
  have hmap : (glMat g₀).map f = glMat (h : GL (Fin 4) L) := by
    rw [← hg₀]
    rfl
  have hanti : g₀ ∈ antiSp K := by
    rw [mem_antiSp]
    apply Matrix.map_injective f.injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, minorJ_map, hmap]
    exact mem_antiSp.mp h.2
  have hρ : minorMap (glMat (h : GL (Fin 4) L)) =
      (glMat (h : GL (Fin 4) L)).map (· ^ 2 ^ (a + 1)) := by
    have := congrArg (fun x : antiSp L => glMat (x : GL (Fin 4) L)) h1
    simpa only [glMat_minorHom, glMat_antiFrobPowHom] using this
  have hρK : minorMap (glMat g₀) = (glMat g₀).map (· ^ 2 ^ (a + 1)) := by
    apply Matrix.map_injective f.injective
    dsimp only
    have e1 : (minorMap (glMat g₀)).map f = minorMap (glMat (h : GL (Fin 4) L)) := by
      rw [← minorMap_map_hom, hmap]
    rw [e1, hρ, ← hmap, Matrix.map_map, Matrix.map_map]
    ext i j
    simp only [Function.comp_apply, Matrix.map_apply, map_pow]
  have hsz : g₀ ∈ suzukiGroup a K := (mem_suzukiGroup_iff_minorMap hK ⟨g₀, hanti⟩).2 hρK
  refine ⟨⟨g₀, hsz⟩, antiSp_ext ?_⟩
  rw [glMat_szEmbed]
  exact hmap

end Range

end CFSG.RankThree.PartOne.KE
