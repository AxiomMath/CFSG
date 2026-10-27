module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerPair

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def cliffCoord (Z : Matrix V₄ V₄ K) : K × K × K × K × K :=
  (Z (Sum.inl 0) (Sum.inl 0), Z (Sum.inl 0) (Sum.inl 1), Z (Sum.inl 1) (Sum.inl 0),
    Z (Sum.inl 0) (Sum.inr 1), Z (Sum.inr 0) (Sum.inl 1))

@[expose] def cliffQuad (v : K × K × K × K × K) : K :=
  v.1 ^ 2 + v.2.1 * v.2.2.1 - v.2.2.2.1 * v.2.2.2.2

@[expose] def cliffMatOf (v : K × K × K × K × K) : Matrix V₄ V₄ K :=
  cliffMat v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2

theorem cliffQ_cliffMatOf (v : K × K × K × K × K) : cliffQ (cliffMatOf v) = cliffQuad v := by
  rw [cliffQ, cliffMatOf, cliffMat_mul_self, cliffQuad]
  simp [Matrix.scalar_apply]

variable (h2 : (2 : K) ≠ 0)
include h2

theorem eq_cliffMat_cliffCoord {d : GL V₄ K} (hd : IsNCInv d) :
    (d : Matrix V₄ V₄ K) = cliffMatOf (cliffCoord (d : Matrix V₄ V₄ K)) :=
  eq_cliffMat_of_mem h2 (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1

theorem cliffQuad_cliffCoord {d : GL V₄ K} (hd : IsNCInv d) :
    cliffQuad (cliffCoord (d : Matrix V₄ V₄ K)) = 1 := by
  rw [← cliffQ_cliffMatOf, ← eq_cliffMat_cliffCoord h2 hd]
  exact (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).2

theorem two_mul_card_ncImage_le {G : Subgroup (GL V₄ K)} [Finite G] (hGS : G ≤ StatedSp 2 K)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K)) :
    2 * Nat.card (ncImage G t) ≤ Nat.card {d : G // IsNCInv (d : GL V₄ K)} := by
  classical
  choose g hg using fun ω : ncImage G t => exists_eq_mk_of_mem_ncImage ω.2
  have hN : ∀ ω : ncImage G t, IsNCInv ((g ω * t * (g ω)⁻¹ : G) : GL V₄ K) :=
    fun ω => conj_isNCInv hGS ht (g ω)
  let m1 : G := ⟨-1, hneg⟩
  let f : ncImage G t × Bool → {d : G // IsNCInv (d : GL V₄ K)} := fun p =>
    if p.2 then ⟨g p.1 * t * (g p.1)⁻¹, hN p.1⟩
    else ⟨m1 * (g p.1 * t * (g p.1)⁻¹), by
      have := (hN p.1).neg
      simpa [m1] using this⟩
  have hval : ∀ p : ncImage G t × Bool, ((f p : G) : GL V₄ K) =
      if p.2 then ((g p.1 * t * (g p.1)⁻¹ : G) : GL V₄ K)
      else -((g p.1 * t * (g p.1)⁻¹ : G) : GL V₄ K) := by
    rintro ⟨ω, b⟩
    cases b <;> simp [f, m1]
  have hne : ∀ ω : ncImage G t, ((g ω * t * (g ω)⁻¹ : G) : GL V₄ K) ≠
      -((g ω * t * (g ω)⁻¹ : G) : GL V₄ K) := by
    intro ω h
    have hm := congrArg (fun x : GL V₄ K => (x : Matrix V₄ V₄ K)) h
    simp only [Units.val_neg] at hm
    have h0 : (2 : K) • (((g ω * t * (g ω)⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hm]
      exact neg_add_cancel _
    rw [smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact h2 h0
    · have := Units.ne_zero (g ω * t * (g ω)⁻¹ : G).1
      exact this h0
  have hinj : Function.Injective f := by
    rintro ⟨ω, b⟩ ⟨ω', b'⟩ hf
    have hf' := congrArg (fun x : {d : G // IsNCInv (d : GL V₄ K)} => ((x : G) : GL V₄ K)) hf
    simp only [hval] at hf'
    have hω : (ω : G ⧸ Subgroup.center G) = ω' := by
      rw [hg ω, hg ω', mk_eq_mk_iff hZ hneg]
      cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hf'
      · left; exact (neg_inj.mp hf').symm
      · right; exact hf'.symm
      · right; rw [hf', neg_neg]
      · left; exact hf'.symm
    have hωω : ω = ω' := Subtype.ext hω
    subst hωω
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at hf'
    · rfl
    · exact absurd hf'.symm (hne ω)
    · exact absurd hf' (hne ω)
    · rfl
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm] at this
  exact this

omit h2

theorem card_cliffQuad_eq_one :
    (Finset.univ.filter fun v : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 =>
      cliffQuad v = 1).card = 90 := by
  decide

theorem exists_isNCInv_of_card {G : Subgroup (GL V₄ (ZMod 3))}
    (hcard : 90 ≤ Nat.card {d : G // IsNCInv (d : GL V₄ (ZMod 3))})
    {v : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3} (hv : cliffQuad v = 1) :
    ∃ d : G, IsNCInv (d : GL V₄ (ZMod 3)) ∧
      ((d : GL V₄ (ZMod 3)) : Matrix V₄ V₄ (ZMod 3)) = cliffMatOf v := by
  classical
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  let T := {w : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 // cliffQuad w = 1}
  let f : {d : G // IsNCInv (d : GL V₄ (ZMod 3))} → T := fun d =>
    ⟨cliffCoord (((d : G) : GL V₄ (ZMod 3)) : Matrix V₄ V₄ (ZMod 3)),
      cliffQuad_cliffCoord h2 d.2⟩
  have hinj : Function.Injective f := by
    intro d d' h
    have hc := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [eq_cliffMat_cliffCoord h2 d.2, eq_cliffMat_cliffCoord h2 d'.2]
    exact congrArg cliffMatOf hc
  have hT : Nat.card T = 90 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_cliffQuad_eq_one
  have hbij := hinj.bijective_of_nat_card_le (by rw [hT]; exact hcard)
  obtain ⟨d, hd⟩ := hbij.2 ⟨v, hv⟩
  refine ⟨d, d.2, ?_⟩
  rw [eq_cliffMat_cliffCoord h2 d.2]
  exact congrArg cliffMatOf (congrArg Subtype.val hd)

theorem cliffMat_mul_eq_spTransMat :
    cliffMat (1 : ZMod 3) 1 0 0 0 * cliffMat 1 1 0 0 1 * cliffMat 1 0 0 0 1 * cliffMat 1 0 0 0 0 =
      spTransMat (Pi.single (Sum.inr 1) 1 : V₄ → ZMod 3) 1 := by
  decide

theorem spTrans_mem_of_card {G : Subgroup (GL V₄ (ZMod 3))}
    (hcard : 90 ≤ Nat.card {d : G // IsNCInv (d : GL V₄ (ZMod 3))}) :
    spTrans (Pi.single (Sum.inr 1) 1 : V₄ → ZMod 3) 1 ∈ G := by
  obtain ⟨d₁, -, h₁⟩ := exists_isNCInv_of_card hcard (v := (1, 1, 0, 0, 0)) (by decide)
  obtain ⟨d₂, -, h₂⟩ := exists_isNCInv_of_card hcard (v := (1, 1, 0, 0, 1)) (by decide)
  obtain ⟨d₃, -, h₃⟩ := exists_isNCInv_of_card hcard (v := (1, 0, 0, 0, 1)) (by decide)
  obtain ⟨d₄, -, h₄⟩ := exists_isNCInv_of_card hcard (v := (1, 0, 0, 0, 0)) (by decide)
  have h : spTrans (Pi.single (Sum.inr 1) 1 : V₄ → ZMod 3) 1 =
      ((d₁ * d₂ * d₃ * d₄ : G) : GL V₄ (ZMod 3)) := by
    apply Units.ext
    rw [coe_spTrans, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
      Units.val_mul, Units.val_mul, h₁, h₂, h₃, h₄]
    exact cliffMat_mul_eq_spTransMat.symm
  rw [h]
  exact (d₁ * d₂ * d₃ * d₄).2

end CFSG.RankThree.SubgroupLists
