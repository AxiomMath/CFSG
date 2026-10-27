module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

@[expose, instance_reducible] def natVecAct {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {R : Type*} [Group R] (φ : R →* GL ι K) : DistribMulAction R (ι → K) where
  smul ρ a := (φ ρ : Matrix ι ι K) *ᵥ a
  one_smul a := by
    show ((φ 1 : GL ι K) : Matrix ι ι K) *ᵥ a = a
    rw [map_one]
    simp
  mul_smul ρ σ a := by
    show ((φ (ρ * σ) : GL ι K) : Matrix ι ι K) *ᵥ a =
      (φ ρ : Matrix ι ι K) *ᵥ ((φ σ : Matrix ι ι K) *ᵥ a)
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  smul_zero ρ := Matrix.mulVec_zero _
  smul_add ρ a b := Matrix.mulVec_add _ _ _

variable {G : Type} [Group G]

theorem NaturalRep.exists_isSecMod {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [CharP K 2] {X : Subgroup (GL ι K)} {R V Z N : Subgroup G}
    (h : NaturalRep K X R V Z N) :
    ∃ (φ : ↥R →* GL ι K) (_ : φ.range = X) (_ : φ.ker = N.subgroupOf R)
      (κ : ↥V →* Multiplicative (ι → K)),
      @IsSecMod G _ R V Z (ι → K) _ (natVecAct φ) κ := by
  obtain ⟨φ, hφX, hker, -, hN, ψ, hψ⟩ := h
  haveI := hN
  refine ⟨φ, hφX, hker, ψ.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf V)), ?_⟩
  refine @IsSecMod.mk G _ R V Z (ι → K) _ (natVecAct φ) _ ?_ ?_ ?_ ?_
  · intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ψ.symm a)
    exact ⟨x, by simp [hx]⟩
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro ρ x y hxy
    have := hψ ρ x y hxy
    refine Multiplicative.toAdd.injective ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      toAdd_ofAdd]
    exact this
  · intro a
    funext i
    simp [CharTwo.add_self_eq_zero]

theorem NaturalRep.eq_or_eq_of_invariant {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] {X : Subgroup (GL ι K)} (hirr : NatIrred X)
    (hcomm : AddCommutantScalar X) {R V Z N : Subgroup G} (h : NaturalRep K X R V Z N)
    {U : Subgroup G} (hZU : Z ≤ U) (hUV : U ≤ V)
    (hRU : ∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U) : U = Z ∨ U = V := by
  have hRV : ∀ r ∈ R, ∀ x ∈ V, r * x * r⁻¹ ∈ V := by
    obtain ⟨φ, -, -, hact⟩ := h
    intro r hr x hx
    exact (Subgroup.mem_normalizer_iff.mp (hact.1 hr) x).mp hx
  obtain ⟨φ, hφX, hker, κ, hκ⟩ := h.exists_isSecMod
  letI := natVecAct φ
  have hZV : Z ≤ V := hZU.trans hUV
  have hinv : ∀ A ∈ X, ∀ v ∈ secSub κ U, (A : Matrix ι ι K) *ᵥ v ∈ secSub κ U := by
    intro A hA v hv
    rw [← hφX] at hA
    obtain ⟨r, rfl⟩ := hA
    have hle : secSub κ (conjSubgroup (r : G) U) ≤ secSub κ U := by
      refine secSub_mono fun x hx => ?_
      rw [mem_conjSubgroup] at hx
      have := hRU (r : G) r.2 _ hx
      rwa [show (r : G) * ((r : G)⁻¹ * x * r) * (r : G)⁻¹ = x by group] at this
    rw [secSub_conjSubgroup hRV hκ r U] at hle
    exact hle ⟨v, hv, rfl⟩
  by_cases hbot : secSub κ U = ⊥
  · left
    refine le_antisymm (fun u hu => ?_) hZU
    have hu1 : Multiplicative.toAdd (κ ⟨u, hUV hu⟩) ∈ secSub κ U :=
      mem_secSub.mpr ⟨⟨u, hUV hu⟩, hu, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at hu1
    have : κ ⟨u, hUV hu⟩ = 1 := Multiplicative.toAdd.injective hu1
    exact (hκ.ker _).mp this
  · right
    have htop : secSub κ U = ⊤ := eq_top_of_addInvariant hirr hcomm hbot hinv
    refine le_antisymm hUV (fun v hv => ?_)
    have : Multiplicative.toAdd (κ ⟨v, hv⟩) ∈ secSub κ U := by
      rw [htop]
      exact AddSubgroup.mem_top _
    exact (toAdd_mem_secSub_iff hκ hZU ⟨v, hv⟩).mp this

theorem natIrred_statedSp {K : Type} [Field K] {m : ℕ} : NatIrred (StatedSp m K) := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  rw [eq_top_iff]
  intro y _
  by_cases hy : y = 0
  · rw [hy]
    exact S.zero_mem
  obtain ⟨A, hA, hAx⟩ := exists_statedSp_mulVec_eq hx0 hy
  have h := hS A hA x hxS
  rwa [hAx] at h

section Order

variable [Finite G] {M Q Z B : Subgroup G}

theorem SpMNat.card_V {hc : Ctx M Q Z B} {t : G} {m : ℕ} (h : SpMNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) := by
  obtain ⟨K, _, _, hK, hrep⟩ := h
  rw [card_of_naturalRep hrep sec39_Z_le_Vt hK]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

theorem SpMNat.m_unique {hc : Ctx M Q Z B} {t : G} {m m' : ℕ} (h : SpMNat hc t m)
    (h' : SpMNat hc t m') : m = m' := by
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have h1 := h.card_V.symm.trans h'.card_V
  have h2 := Nat.pow_right_injective hq2 h1
  omega

end Order

end CFSG.RankThree.GF2n.Stroth80
