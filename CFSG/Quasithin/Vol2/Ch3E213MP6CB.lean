module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ minorJ_apply mem_antiSp antiSp_ext antiUnipotent antiUnipotentCenter uElt
    uMat uElt_mem_antiUnipotent card_antiSp glMat_uElt)
open CFSG.ABGLocalTools (IsSylowOf)

variable {k : Type} [Field k]

theorem minorJ_map {K L : Type} [Field K] [Field L] (f : K →+* L) :
    (minorJ K).map f = minorJ L := by
  ext i j
  simp only [Matrix.map_apply, minorJ_apply]
  split_ifs <;> simp

@[expose] def subAntiSp (F₀ : Subfield k) : antiSp ↥F₀ →* antiSp k :=
  ((Matrix.GeneralLinearGroup.map F₀.subtype).comp (antiSp ↥F₀).subtype).codRestrict (antiSp k)
    fun g => by
      rw [mem_antiSp]
      change ((glMat (g : GL (Fin 4) ↥F₀)).map F₀.subtype).transpose * minorJ k *
        (glMat (g : GL (Fin 4) ↥F₀)).map F₀.subtype = minorJ k
      rw [← minorJ_map F₀.subtype, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        mem_antiSp.mp g.2]

theorem glMat_subAntiSp (F₀ : Subfield k) (g : antiSp ↥F₀) :
    glMat (subAntiSp F₀ g : GL (Fin 4) k) = (glMat (g : GL (Fin 4) ↥F₀)).map F₀.subtype :=
  rfl

theorem subAntiSp_injective (F₀ : Subfield k) : Function.Injective (subAntiSp F₀) := by
  intro g h hgh
  apply antiSp_ext
  have h1 := congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) hgh
  simp only [glMat_subAntiSp] at h1
  exact Matrix.map_injective Subtype.val_injective h1

theorem range_subAntiSp (F₀ : Subfield k) : (subAntiSp F₀).range = subfieldSp F₀ := by
  ext g
  constructor
  · rintro ⟨g₀, rfl⟩ i j
    exact (glMat (g₀ : GL (Fin 4) ↥F₀) i j).2
  · intro hg
    have hgi : g⁻¹ ∈ subfieldSp F₀ := (subfieldSp F₀).inv_mem hg
    let A : Matrix (Fin 4) (Fin 4) ↥F₀ := fun i j => ⟨glMat (g : GL (Fin 4) k) i j, hg i j⟩
    let B : Matrix (Fin 4) (Fin 4) ↥F₀ :=
      fun i j => ⟨glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) i j, hgi i j⟩
    have hA : A.map F₀.subtype = glMat (g : GL (Fin 4) k) := rfl
    have hB : B.map F₀.subtype = glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) := rfl
    have hAB : A * B = 1 := Matrix.map_injective (f := F₀.subtype) Subtype.val_injective
      (show (A * B).map F₀.subtype = (1 : Matrix (Fin 4) (Fin 4) ↥F₀).map F₀.subtype by
        rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
        exact (g : GL (Fin 4) k).mul_inv)
    have hBA : B * A = 1 := Matrix.map_injective (f := F₀.subtype) Subtype.val_injective
      (show (B * A).map F₀.subtype = (1 : Matrix (Fin 4) (Fin 4) ↥F₀).map F₀.subtype by
        rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
        exact (g : GL (Fin 4) k).inv_mul)
    have hmem : (⟨A, B, hAB, hBA⟩ : GL (Fin 4) ↥F₀) ∈ antiSp ↥F₀ := by
      rw [mem_antiSp]
      apply Matrix.map_injective Subtype.val_injective
      change (A.transpose * minorJ ↥F₀ * A).map F₀.subtype = (minorJ ↥F₀).map F₀.subtype
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, minorJ_map, hA]
      exact mem_antiSp.mp g.2
    exact ⟨⟨_, hmem⟩, antiSp_ext hA⟩

@[expose] noncomputable def subfieldSpEquiv (F₀ : Subfield k) : antiSp ↥F₀ ≃* subfieldSp F₀ :=
  (MonoidHom.ofInjective (subAntiSp_injective F₀)).trans
    (MulEquiv.subgroupCongr (range_subAntiSp F₀))

theorem subfieldSp_top : subfieldSp (⊤ : Subfield k) = ⊤ :=
  eq_top_iff.2 fun _ _ _ _ => Subfield.mem_top _

theorem wLong_mem_subfieldSp (F₀ : Subfield k) : (wLong : antiSp k) ∈ subfieldSp F₀ :=
  fun i j => by
    rw [glMat_wLong]
    exact minorJ_apply_mem F₀ i j

theorem card_subfieldSp [Finite k] [CharP k 2] (F₀ : Subfield k) {q : ℕ} (hq : Nat.card F₀ = q) :
    Nat.card (subfieldSp F₀) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  rw [← Nat.card_congr (subfieldSpEquiv F₀).toEquiv, card_antiSp hq]

section CharTwo

variable [CharP k 2]

theorem uElt_mem_subfieldSp {F₀ : Subfield k} {a b c d : k} (ha : a ∈ F₀) (hb : b ∈ F₀)
    (hc : c ∈ F₀) (hd : d ∈ F₀) : uElt a b c d ∈ subfieldSp F₀ := by
  intro i j
  rw [glMat_uElt]
  fin_cases i <;> fin_cases j <;> simp [uMat] <;>
    first | exact F₀.zero_mem | exact F₀.one_mem | assumption |
      exact F₀.add_mem hb (F₀.mul_mem ha hd)

theorem subAntiSp_uElt (F₀ : Subfield k) (a b c d : ↥F₀) :
    subAntiSp F₀ (uElt a b c d) = uElt (a : k) b c d := by
  apply antiSp_ext
  rw [glMat_subAntiSp, glMat_uElt, glMat_uElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem subfieldSp_inf_antiUnipotent (F₀ : Subfield k) :
    subfieldSp F₀ ⊓ antiUnipotent k = (antiUnipotent ↥F₀).map (subAntiSp F₀) := by
  ext g
  constructor
  · rintro ⟨hg, a, b, c, d, rfl⟩
    have ha : a ∈ F₀ := by simpa [glMat_uElt, uMat] using hg 0 1
    have hb : b ∈ F₀ := by simpa [glMat_uElt, uMat] using hg 0 2
    have hc : c ∈ F₀ := by simpa [glMat_uElt, uMat] using hg 0 3
    have hd : d ∈ F₀ := by simpa [glMat_uElt, uMat] using hg 1 2
    exact ⟨uElt ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩, uElt_mem_antiUnipotent _ _ _ _,
      subAntiSp_uElt F₀ _ _ _ _⟩
  · rintro ⟨g₀, ⟨a, b, c, d, rfl⟩, rfl⟩
    refine ⟨range_subAntiSp F₀ ▸ ⟨_, rfl⟩, ?_⟩
    rw [subAntiSp_uElt]
    exact uElt_mem_antiUnipotent _ _ _ _

theorem isSylowOf_subfieldSp_inf [Finite k] (F₀ : Subfield k) :
    IsSylowOf 2 (subfieldSp F₀ ⊓ antiUnipotent k) (subfieldSp F₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.QuasithinUnique.Setup.X7b.card_and_isSylowTwoOf_antiUnipotent (K := ↥F₀)).2
  rw [CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf] at h
  have h2 := CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective (subAntiSp F₀)
    (subAntiSp_injective F₀) h
  rwa [← subfieldSp_inf_antiUnipotent, ← MonoidHom.range_eq_map, range_subAntiSp] at h2

theorem card_subfieldSp_inf_center_le [Finite k] (F₀ : Subfield k) :
    Nat.card ↥(subfieldSp F₀ ⊓ antiUnipotentCenter k) ≤ Nat.card F₀ ^ 2 := by
  let f : ↥(subfieldSp F₀ ⊓ antiUnipotentCenter k) → ↥F₀ × ↥F₀ := fun g =>
    (⟨glMat ((g : antiSp k) : GL (Fin 4) k) 0 2, g.2.1 0 2⟩,
      ⟨glMat ((g : antiSp k) : GL (Fin 4) k) 0 3, g.2.1 0 3⟩)
  have hf : Function.Injective f := by
    rintro ⟨x, hx1, b, c, hx⟩ ⟨y, hy1, b', c', hy⟩ hxy
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    subst hx hy
    rw [glMat_uElt, glMat_uElt] at hxy
    simp only [uMat] at hxy
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    rfl
  calc Nat.card ↥(subfieldSp F₀ ⊓ antiUnipotentCenter k) ≤ Nat.card (↥F₀ × ↥F₀) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card F₀ ^ 2 := by rw [Nat.card_prod, sq]

end CharTwo

end CFSG.Quasithin.Ch3E213M
