module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.RankThree.SubgroupLists.SL2Perfect

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.SubgroupLists

open Matrix
open scoped MatrixGroups

noncomputable def sl2CongrRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map e.toRingHom)
    (SpecialLinearGroup.map e.symm.toRingHom)
    (by ext A i j; simp) (by ext A i j; simp)

variable {p : ℕ} [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]

theorem perfect_irreducible_not_absolutely (hp2 : p ≠ 2) (hσ : Fintype.card σ = 4)
    {G : Subgroup (GL σ (ZMod p))} [Group.IsPerfect G] (hG : IsIrreducibleOn G)
    (hC : commutant G ≠ ⊥) :
    Nonempty (G ≃* SL(2, ZMod 5)) ∨ Nonempty (G ≃* SL(2, ZMod p)) ∨
      Nonempty (G ≃* SL(2, GaloisField p 2)) := by
  classical
  have : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  have hdvd := finrank_commutant_dvd hG
  rw [hσ] at hdvd
  have hne1 : Module.finrank (ZMod p) (commutant G) ≠ 1 := fun h =>
    hC (Subalgebra.finrank_eq_one_iff.mp h)
  have hd : Module.finrank (ZMod p) (commutant G) = 2 ∨
      Module.finrank (ZMod p) (commutant G) = 4 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4] at hdvd
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases i <;> simp_all
  have hGnt : ∃ g ∈ G, g ≠ 1 := by
    by_contra h
    push Not at h
    exact not_irreducibleOn_of_forall_scalar (by omega) (fun g hg => ⟨1, by
      rw [h g hg]
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]⟩) hG
  rcases hd with h2 | h4
  swap
  ·
    exfalso
    have hGC := mem_commutant_of_finrank_eq hG (by rw [h4, hσ])
    let := commutantField hG
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => Subtype.ext (Units.ext
      (congrArg Subtype.val (mul_comm (⟨((a : GL σ (ZMod p)) : Matrix σ σ (ZMod p)),
        hGC a a.2⟩ : commutant G) ⟨((b : GL σ (ZMod p)) : Matrix σ σ (ZMod p)), hGC b b.2⟩)))
    have : IsMulCommutative G := ⟨⟨hcomm⟩⟩
    have : Subsingleton G := Group.IsPerfect.subsingleton_of_isMulCommutative
    obtain ⟨g, hg, hg1⟩ := hGnt
    exact hg1 (congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : G) 1))
  let := commutantField hG
  have hCcard : Nat.card (commutant G) = p ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), h2, Nat.card_zmod]
  have : Module.Finite (commutant G) (σ → ZMod p) :=
    Module.Finite.of_restrictScalars_finite (ZMod p) (commutant G) (σ → ZMod p)
  have hfinC : Module.finrank (commutant G) (σ → ZMod p) = 2 := by
    have h1 : Nat.card (σ → ZMod p) = p ^ 4 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := σ), hσ]
    have h2' : Nat.card (σ → ZMod p) =
        Nat.card (commutant G) ^ Module.finrank (commutant G) (σ → ZMod p) :=
      Module.natCard_eq_pow_finrank
    rw [h1, hCcard, ← pow_mul] at h2'
    have := Nat.pow_right_injective (Fact.out : p.Prime).two_le h2'
    omega
  let b := Module.finBasisOfFinrankEq (commutant G) (σ → ZMod p) hfinC
  let gC : G →* Module.End (commutant G) (σ → ZMod p) :=
    { toFun := fun g =>
        { toFun := fun v => ((g : GL σ (ZMod p)) : Matrix σ σ (ZMod p)) *ᵥ v
          map_add' := fun v w => Matrix.mulVec_add _ _ _
          map_smul' := fun c v => by
            change _ *ᵥ ((c : Matrix σ σ (ZMod p)) *ᵥ v) =
              (c : Matrix σ σ (ZMod p)) *ᵥ (_ *ᵥ v)
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (mem_commutant.mp c.2) g g.2] }
      map_one' := by
        apply LinearMap.ext
        intro v
        simp
      map_mul' := fun g h => by
        apply LinearMap.ext
        intro v
        simp [Matrix.mulVec_mulVec] }
  have hgC : ∀ g v, gC g v = ((g : GL σ (ZMod p)) : Matrix σ σ (ZMod p)) *ᵥ v := fun _ _ => rfl
  let ρ : G →* GL (Fin 2) (commutant G) :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp gC.toHomUnits
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have h1 : (LinearMap.toMatrixAlgEquiv b) (gC g) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
      simpa [ρ] using this
    have h2 : gC g = 1 := (LinearMap.toMatrixAlgEquiv b).injective (by rw [h1, map_one])
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    have := LinearMap.congr_fun h2 v
    rw [hgC] at this
    rw [this, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
    rfl
  have hdet : ∀ g, ((ρ g : GL (Fin 2) (commutant G)) : Matrix (Fin 2) (Fin 2)
      (commutant G)).det = 1 := by
    intro g
    have h := CFSG.SectionRank.Ccomm.perfect_hom_eq_one (GeneralLinearGroup.det.comp ρ) g
    have := congrArg Units.val h
    simpa using this
  let s : G →* SL(2, commutant G) :=
    { toFun := fun g => ⟨(ρ g : Matrix (Fin 2) (Fin 2) (commutant G)), hdet g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp; rfl) }
  have hsinj : Function.Injective s := fun g h hgh => hρinj (Units.ext (congrArg Subtype.val hgh))
  let e : G ≃* s.range := MonoidHom.ofInjective hsinj
  have : Group.IsPerfect s.range := Group.IsPerfect.range s
  have hne : s.range ≠ ⊥ := by
    intro h
    obtain ⟨g, hg, hg1⟩ := hGnt
    have : s ⟨g, hg⟩ ∈ s.range := ⟨⟨g, hg⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hg1 (congrArg Subtype.val (hsinj (this.trans (map_one s).symm)))
  rcases perfect_sl2_mulEquiv hp2 hCcard s.range hne with h | ⟨m, hm0, hm2, hm⟩
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨f⟩ := hm
    have hm12 : m = 1 ∨ m = 2 := by
      have := Nat.le_of_dvd two_pos hm2
      omega
    rcases hm12 with rfl | rfl
    · exact Or.inr (Or.inl ⟨(e.trans f).trans
        (sl2CongrRingEquiv (GaloisField.equivZmodP p).toRingEquiv)⟩)
    · exact Or.inr (Or.inr ⟨e.trans f⟩)

end CFSG.RankThree.SubgroupLists
