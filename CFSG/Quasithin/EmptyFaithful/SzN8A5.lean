module

public import CFSG.Quasithin.EmptyFaithful.SzN4Local
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Inner

variable {G : Type} [Group G]

theorem szN8_alt5_inner {L : Subgroup G} (hA : IsAltType L 5) {y : G}
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hy : Odd (orderOf y)) :
    ∃ x ∈ L, ∀ l ∈ L, l * (x⁻¹ * y) * l⁻¹ * (x⁻¹ * y)⁻¹ ∈ pCoreOf 2 L := by
  classical
  obtain ⟨α, hαs, hαk, -⟩ := hA
  have hc : ∀ l : ↥L, y * (l : G) * y⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp hyN _).mp l.2
  let c : ↥L →* ↥L :=
    { toFun := fun l => ⟨y * (l : G) * y⁻¹, hc l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcapp : ∀ l : ↥L, ((c l : ↥L) : G) = y * (l : G) * y⁻¹ := fun l => rfl
  let ψ : ↥L →* alternatingGroup (Fin 5) := α.comp c
  have hker : α.ker ≤ ψ.ker := by
    intro l hl
    have h1 : l ∈ CFSG.pCore 2 ↥L := hαk ▸ hl
    have h2 : (l : G) ∈ pCoreOf 2 L := (szN4_mem_pCore_iff l).mp h1
    have h3 : y * (l : G) * y⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 L hyN) _).mp h2
    have h4 : c l ∈ CFSG.pCore 2 ↥L := (szN4_mem_pCore_iff (c l)).mpr h3
    rw [← hαk] at h4
    exact h4
  let φ : alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) :=
    MonoidHom.liftOfRightInverse α (Function.surjInv hαs) (Function.rightInverse_surjInv hαs)
      ⟨ψ, hker⟩
  have hφ : ∀ l : ↥L, φ (α l) = α (c l) := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply α _ _ ⟨ψ, hker⟩ l
  have hφsurj : Function.Surjective φ := by
    intro b
    obtain ⟨l', rfl⟩ := hαs b
    have hinv : y⁻¹ * (l' : G) * y⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem hyN) _).mp l'.2
    refine ⟨α ⟨y⁻¹ * (l' : G) * y⁻¹⁻¹, hinv⟩, ?_⟩
    rw [hφ]
    congr 1
    apply Subtype.ext
    rw [hcapp]
    simp only
    group
  have hφbij : Function.Bijective φ := ⟨Finite.injective_iff_surjective.mpr hφsurj, hφsurj⟩
  let φ' : MulAut (alternatingGroup (Fin 5)) := MulEquiv.ofBijective φ hφbij
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)).2 φ'
  have hπinj := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)).1
  have key : ∀ a : alternatingGroup (Fin 5),
      ((φ a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = π * a * π⁻¹ := by
    intro a
    have h := congrArg (fun f : MulAut (alternatingGroup (Fin 5)) =>
      ((f a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) hπ
    simp only [MulAut.conjNormal_apply] at h
    exact h.symm
  have hpow : ∀ k : ℕ, ∀ l : ↥L, (φ' ^ k) (α l) = α ⟨y ^ k * (l : G) * (y ^ k)⁻¹,
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem hyN k) _).mp l.2⟩ := by
    intro k
    induction k with
    | zero =>
      intro l
      simp only [pow_zero, MulAut.one_apply, inv_one, one_mul, mul_one]
    | succ k ih =>
      intro l
      rw [pow_succ', MulAut.mul_apply, ih l]
      have h1 : φ' (α ⟨y ^ k * (l : G) * (y ^ k)⁻¹, (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer _).pow_mem hyN k) _).mp l.2⟩) = φ (α ⟨y ^ k * (l : G) * (y ^ k)⁻¹,
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem hyN k) _).mp l.2⟩) := rfl
      rw [h1, hφ]
      congr 1
      apply Subtype.ext
      rw [hcapp]
      simp only
      rw [pow_succ']
      group
  have hφm : φ' ^ orderOf y = 1 := by
    ext a
    obtain ⟨l, rfl⟩ := hαs a
    rw [hpow]
    simp only [pow_orderOf_eq_one, one_mul, inv_one, mul_one, MulAut.one_apply]
  have hπm : π ^ orderOf y = 1 := by
    apply hπinj
    rw [map_pow, hπ, hφm, map_one]
  have hsign : Equiv.Perm.sign π = 1 := by
    have h1 : Equiv.Perm.sign π ^ orderOf y = 1 := by
      rw [← map_pow, hπm, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · exact h
    · rw [h, hy.neg_one_pow] at h1
      exact absurd h1 (by decide)
  let a₀ : alternatingGroup (Fin 5) := ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  obtain ⟨x', hx'⟩ := hαs a₀
  have hφa : ∀ a : alternatingGroup (Fin 5), φ a = a₀ * a * a₀⁻¹ := by
    intro a
    apply Subtype.ext
    rw [key a]
    simp [a₀]
  have hconj : ∀ l : ↥L, α (c l) = α x' * α l * (α x')⁻¹ := by
    intro l
    rw [← hφ l, hφa, hx']
  refine ⟨(x' : G), x'.2, fun l hl => ?_⟩
  let l' : ↥L := ⟨l, hl⟩
  let w : ↥L := l' * x'⁻¹ * c l'⁻¹ * x'
  have hw : w ∈ α.ker := by
    rw [MonoidHom.mem_ker]
    show α (l' * x'⁻¹ * c l'⁻¹ * x') = 1
    rw [map_mul, map_mul, map_mul, map_inv, hconj, map_inv]
    group
  have hwG : (w : G) = l * ((x' : G)⁻¹ * y) * l⁻¹ * ((x' : G)⁻¹ * y)⁻¹ := by
    show (l : G) * ((x' : G))⁻¹ * (y * ((l : G))⁻¹ * y⁻¹) * (x' : G) = _
    group
  rw [← hwG]
  exact (szN4_mem_pCore_iff w).mp (hαk ▸ hw)

end Inner

end CFSG.Quasithin
