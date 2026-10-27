module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeRootPts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6Three_datum_of_coords {G : Type} [Group G] {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (cd : ↥Bs →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hrange : cd.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ cd.range ↔ x ∈ NoOffRest.hypE6)
    (φ : Fin Tag.E6.rank → MulAut ↥Bs) (hφ2 : ∀ k, φ k * φ k = 1)
    (hφ : ∀ (k : Fin Tag.E6.rank) (b : ↥Bs), cd (φ k b) =
      Multiplicative.ofAdd (adRefl Tag.E6 3 k (Multiplicative.toAdd (cd b))))
    (hfixZ : ∀ (k : Fin Tag.E6.rank) (z : ↥Bs), cd z = 1 → φ k z = z) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin Tag.E6.rank → V) (α : Fin Tag.E6.rank → Module.Dual (ZMod 3) V),
      (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection 3 (φ i)) ∧
      (∀ i j, α i (h j) = (Tag.cartan .E6 i j : ZMod 3)) ∧
      (∀ (b : ↥Bs) j, α j (ι (Additive.ofMul b)) = Multiplicative.toAdd (cd b) j) := by
  have hcomm : ∀ x y : ↥Bs, x * y = y * x := fun x y => hBs.1.is_comm.comm x y
  have hcube : ∀ x : ↥Bs, x ^ 3 = 1 := fun x => Subtype.ext (hBs.2 x x.2)
  have hsymm : ∀ i j : Fin Tag.E6.rank, Tag.cartan Tag.E6 i j = Tag.cartan Tag.E6 j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdiag : ∀ k : Fin Tag.E6.rank, Tag.cartan Tag.E6 k k = 2 := by
    intro k
    fin_cases k <;> rfl
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  let a : Fin Tag.E6.rank → (V →+ ZMod 3) := fun j =>
    AddMonoidHom.mk' (fun v => (Multiplicative.toAdd (cd (Additive.toMul (ι.symm v)))) j)
      (fun u w => by simp only [map_add, toMul_add, map_mul, toAdd_mul]; try rfl)
  let α : Fin Tag.E6.rank → Module.Dual (ZMod 3) V := fun j => (a j).toZModLinearMap 3
  have hα : ∀ (b : ↥Bs) (j : Fin Tag.E6.rank),
      α j (ι (Additive.ofMul b)) = Multiplicative.toAdd (cd b) j := by
    intro b j
    simp [α, a]
  have hfix : ∀ (k : Fin Tag.E6.rank) (b : ↥Bs), Multiplicative.toAdd (cd b) k = 0 → φ k b = b := by
    intro k b hb
    set δ : ↥Bs := φ k b * b⁻¹ with hδ
    have hcδ : cd δ = 1 := by
      rw [hδ, map_mul, map_inv, hφ]
      have : adRefl Tag.E6 3 k (Multiplicative.toAdd (cd b)) = Multiplicative.toAdd (cd b) := by
        funext j
        simp [adRefl, hb]
      rw [this]
      simp
    have h1 : φ k δ = δ := hfixZ k δ hcδ
    have hδb : δ * b = φ k b := by rw [hδ]; group
    have h2 : φ k (φ k b) = b := by
      have := congrArg (fun f : MulAut ↥Bs => f b) (hφ2 k)
      simpa using this
    have h3 : δ * (δ * b) = b := by
      have e1 : φ k (δ * b) = b := by rw [hδb]; exact h2
      have e2 : φ k (δ * b) = δ * φ k b := by rw [map_mul, h1]
      calc δ * (δ * b) = δ * φ k b := by rw [hδb]
        _ = φ k (δ * b) := e2.symm
        _ = b := e1
    have h4 : δ ^ 2 = 1 := by
      have : δ ^ 2 * b = 1 * b := by rw [pow_two, mul_assoc, h3, one_mul]
      exact mul_right_cancel this
    have h5 : δ = 1 := by
      have : δ = δ ^ 3 * (δ ^ 2)⁻¹ := by group
      rw [this, hcube, h4]
      simp
    rw [← hδb, h5, one_mul]
  have hfixV : ∀ (k : Fin Tag.E6.rank) (v : V), α k v = 0 → ggLin (p := 3) ι (φ k) v = v := by
    intro k v hv
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, v = ι (Additive.ofMul b) :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [hα] at hv
    rw [ggLin_apply_ofMul, hfix k b hv]
  have hex : ∀ k : Fin Tag.E6.rank, ∃ b : ↥Bs, Multiplicative.toAdd (cd b) k = 1 := by
    intro k
    have hxk : (e6ThreeRootPt (Pi.single k 1)) k = 2 := by
      have h1 : (∑ m, Tag.cartan Tag.E6 k m * (Pi.single k (1 : ℤ) : Fin Tag.E6.rank → ℤ) m) =
          2 := by
        rw [Finset.sum_eq_single k]
        · simp [hdiag]
        · intro m _ hm
          simp [Pi.single_apply, hm]
        · intro h
          exact absurd (Finset.mem_univ k) h
      simp only [e6ThreeRootPt, h1]
      norm_num
    rcases hrange with h | h
    · have hm : Multiplicative.ofAdd (Pi.single k (1 : ZMod 3) : Fin Tag.E6.rank → ZMod 3) ∈
          cd.range := by rw [h]; trivial
      obtain ⟨b, hb⟩ := hm
      refine ⟨b, ?_⟩
      rw [hb, toAdd_ofAdd]
      exact Pi.single_eq_same k 1
    · have hm : Multiplicative.ofAdd (-(e6ThreeRootPt (Pi.single k 1))) ∈ cd.range :=
        (h _).2 (neg_mem (e6ThreeRootPt_mem_hypE6 _))
      obtain ⟨b, hb⟩ := hm
      refine ⟨b, ?_⟩
      rw [hb, toAdd_ofAdd]
      have hneg : (-(e6ThreeRootPt (Pi.single k 1))) k = -(e6ThreeRootPt (Pi.single k 1) k) := rfl
      rw [hneg, hxk]
      decide
  choose b0 hb0 using hex
  let v0 : Fin Tag.E6.rank → V := fun k => ι (Additive.ofMul (b0 k))
  let T : Fin Tag.E6.rank → (V ≃ₗ[ZMod 3] V) := fun k => ggLin (p := 3) ι (φ k)
  let hh : Fin Tag.E6.rank → V := fun k => v0 k - T k (v0 k)
  have hαv0 : ∀ k, α k (v0 k) = 1 := fun k => by simp only [v0]; rw [hα]; exact hb0 k
  have hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • hh i := by
    intro i w
    have hw' : α i (w - α i w • v0 i) = 0 := by
      rw [map_sub, map_smul, hαv0, smul_eq_mul, mul_one, sub_self]
    have h1 := hfixV i _ hw'
    have h2 : ggLin (p := 3) ι (φ i) w =
        ggLin (p := 3) ι (φ i) (w - α i w • v0 i) + α i w • T i (v0 i) := by
      have : w = (w - α i w • v0 i) + α i w • v0 i := by abel
      conv_lhs => rw [this]
      rw [map_add, map_smul]
    rw [h2, h1]
    simp only [hh]
    module
  have hpair : ∀ i j, α i (hh j) = (Tag.cartan .E6 i j : ZMod 3) := by
    intro i j
    have hv0 : α i (v0 j) = Multiplicative.toAdd (cd (b0 j)) i := by
      simp only [v0]
      rw [hα]
    have hTv : α i (T j (v0 j)) = Multiplicative.toAdd (cd (φ j (b0 j))) i := by
      simp only [T, v0]
      rw [ggLin_apply_ofMul, hα]
    have hj : Multiplicative.toAdd (cd (b0 j)) j = 1 := hb0 j
    simp only [hh, map_sub]
    rw [hv0, hTv, hφ]
    simp only [adRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toAdd_ofAdd, hj, one_mul]
    rw [sub_sub_cancel, hsymm j i]
  have hrefl : ∀ i, GGIsReflection 3 (φ i) := by
    intro i
    have hfx : α i (hh i) = 2 := by
      rw [hpair, hdiag]
      norm_num
    exact ggIsReflection_of_eq_reflection (by norm_num) ι hfx
      (ggLin_eq_reflection ι hfx (hlin i))
  exact ⟨V, hVadd, hVmod, ι, hh, α, hlin, hrefl, hpair, hα⟩

end CFSG.StandardType

end
