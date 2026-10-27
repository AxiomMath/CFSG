module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515bLoc

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Blk (Γ : SimpleGraph V) (z : G) (α β δ β' α' αs α's : V) (d zz : G) : Prop where
  cinv : z ∈ Cinv G α
  orb' : ∃ g : G, g • α = α'
  hset1 : Γ.neighborSet β = {α, δ, αs}
  hset2 : Γ.neighborSet β' = {δ, α', α's}
  hαδ : α ≠ δ
  hα'δ : α' ≠ δ
  hzz : zz = Lb z α α'
  Lαs : Lb z α αs = z * d
  Lα's : Lb z α α's = zz * d
  c1 : z * zz = zz * z
  c2 : z * d = d * z
  c3 : zz * d = d * zz
  dd : d * d = 1
  dcin : d ∈ Cinv G δ

theorem conj_in (F : FanTree Γ G) {z : G} {α β δ β' α' αs α's : V} {d zz : G}
    (B : Blk Γ z α β δ β' α' αs α's d zz) {w : G} (hwδ : w • δ = δ)
    (hw : (w • β = β ∧ w • β' = β') ∨ (w • β = β' ∧ w • β' = β)) :
    w * (z * zz) * w⁻¹ = z * zz ∨ w * (z * zz) * w⁻¹ = z * zz * d := by
  have hβα : Γ.Adj β α := by
    have : α ∈ Γ.neighborSet β := by rw [B.hset1]; simp
    exact this
  have hβ'α' : Γ.Adj β' α' := by
    have : α' ∈ Γ.neighborSet β' := by rw [B.hset2]; simp
    exact this
  have e1 : w * z * w⁻¹ = Lb z α (w • α) := by
    have := Lb_conj B.cinv ⟨1, one_smul G α⟩ w
    rwa [Lb_self B.cinv] at this
  have e2 : w * zz * w⁻¹ = Lb z α (w • α') := by
    have := Lb_conj B.cinv B.orb' w
    rwa [← B.hzz] at this
  have hsplit : w * (z * zz) * w⁻¹ = (w * z * w⁻¹) * (w * zz * w⁻¹) := by group
  have hα1 : w • α ≠ δ := fun h => B.hαδ (MulAction.injective w (h.trans hwδ.symm))
  have hα2 : w • α' ≠ δ := fun h => B.hα'δ (MulAction.injective w (h.trans hwδ.symm))
  have adj1 : Γ.Adj (w • β) (w • α) := (F.adj_smul w β α).2 hβα
  have adj2 : Γ.Adj (w • β') (w • α') := (F.adj_smul w β' α').2 hβ'α'
  have labA : ∀ l, Γ.Adj β l → l ≠ δ → Lb z α l = z ∨ Lb z α l = z * d := by
    intro l hl hne
    have : l ∈ Γ.neighborSet β := hl
    rw [B.hset1] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with rfl | rfl | rfl
    · exact Or.inl (Lb_self B.cinv)
    · exact absurd rfl hne
    · exact Or.inr B.Lαs
  have labB : ∀ l, Γ.Adj β' l → l ≠ δ → Lb z α l = zz ∨ Lb z α l = zz * d := by
    intro l hl hne
    have : l ∈ Γ.neighborSet β' := hl
    rw [B.hset2] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl B.hzz.symm
    · exact Or.inr B.Lα's
  rw [hsplit, e1, e2]
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at adj1
    rw [h2] at adj2
    exact (four_prods B.c1 B.c2 B.c3 B.dd (labA _ adj1 hα1) (labB _ adj2 hα2)).1
  · rw [h1] at adj1
    rw [h2] at adj2
    exact (four_prods B.c1 B.c2 B.c3 B.dd (labA _ adj2 hα2) (labB _ adj1 hα1)).2

theorem final (F : FanTree Γ G) {z : G} {α β δ β' α' αs α's : V} {d zz : G}
    (B : Blk Γ z α β δ β' α' αs α's d zz) {x y : G} (hxδ : x • δ = δ) (hyδ : y • δ = δ)
    (hx : (x • β = β ∧ x • β' = β') ∨ (x • β = β' ∧ x • β' = β))
    (hy : (y • β = β ∧ y • β' = β') ∨ (y • β = β' ∧ y • β' = β))
    (hxu : x * (z * zz) ≠ (z * zz) * x) (hyu : y * (z * zz) ≠ (z * zz) * y) :
    (x * y) * (z * zz) = (z * zz) * (x * y) := by
  have hx' : x * (z * zz) * x⁻¹ = z * zz * d := by
    rcases conj_in F B hxδ hx with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h) hxu
    · exact h
  have hy' : y * (z * zz) * y⁻¹ = z * zz * d := by
    rcases conj_in F B hyδ hy with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.1 h) hyu
    · exact h
  have hxd : x * d * x⁻¹ = d := by
    rw [B.dcin.2.2.2 x (MulAction.mem_stabilizer_iff.2 hxδ)]
    group
  have key : (x * y) * (z * zz) * (x * y)⁻¹ = z * zz := by
    calc (x * y) * (z * zz) * (x * y)⁻¹ = x * (y * (z * zz) * y⁻¹) * x⁻¹ := by group
      _ = x * (z * zz * d) * x⁻¹ := by rw [hy']
      _ = (x * (z * zz) * x⁻¹) * (x * d * x⁻¹) := by group
      _ = z * zz * d * d := by rw [hx', hxd]
      _ = z * zz := by rw [mul_assoc, B.dd, mul_one]
  exact mul_inv_eq_iff_eq_mul.1 key

end P515

end CFSG.Quasithin.Fan86
