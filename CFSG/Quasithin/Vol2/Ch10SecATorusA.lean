module

public import CFSG.Quasithin.Vol2.Ch10SecANatCoord
public import CFSG.Quasithin.Vol2.Ch10SecATorus

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_mem_autOn_of_mem_fsuL0 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {y : G} (hy : y ∈ fsuL0 T L) :
    ∃ l ∈ L, ∀ w ∈ fsuUL T L I, y * w * y⁻¹ = l * w * l⁻¹ := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hUt := (ha t ht htn).2.2
  have hloc := hyp.fsu.maximal.1
  have hLtN : CFSG.conjugate L t ≤ Subgroup.normalizer (L : Set G) :=
    (conjugate_le_fsuL0 ht).trans (fsuL0_le_normalizer hloc)
  have hy' : y ∈ ((L ⊔ CFSG.conjugate L t : Subgroup G) : Set G) := by
    rw [← fsuL0_eq_sup h37 h38 hyp ht htn]
    exact hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLtN] at hy'
  obtain ⟨l, hl, l', hl', rfl⟩ := Set.mem_mul.mp hy'
  refine ⟨l, hl, fun w hw => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp (hUt hw) l' hl'
  calc l * l' * w * (l * l')⁻¹ = l * (l' * w) * l'⁻¹ * l⁻¹ := by group
    _ = l * (w * l') * l'⁻¹ * l⁻¹ := by rw [h1]
    _ = l * w * l⁻¹ := by group

omit [Finite G] in
theorem NatCoord.beta_eq [IsMulCommutative ↥(fsuUL T L I)] {F : Type} [Field F]
    (c : NatCoord T L I F) {γ : Matrix.SpecialLinearGroup (Fin 2) F} {w : ↥(fsuUL T L I)}
    (h : ((c.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) w * w⁻¹ ∈
      Ch10.cV1 T L I) :
    (γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c.β w)) =
      Multiplicative.toAdd (c.β w) := by
  have h1 := (c.ker _).mpr h
  rw [map_mul, map_inv, mul_inv_eq_one, c.equivariant] at h1
  exact congrArg Multiplicative.toAdd h1

theorem centralizes_of_case_one (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n) {y : G} (hyL0 : y ∈ fsuL0 T L) (hyodd : Odd (orderOf y))
    (hyN : y ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) {w : G}
    (hwU : w ∈ fsuUL T L I) (hwC : w ∉ fsuCVM T L I)
    (hwS : ∀ s ∈ T ⊓ L, s * w * s⁻¹ * w⁻¹ ∈ fsuCVM T L I)
    (hwy : y * w * y⁻¹ * w⁻¹ ∈ fsuCVM T L I) :
    ∀ u ∈ fsuUL T L I, y * u * y⁻¹ = u := by
  obtain ⟨hUab, F, _, _, _, hn, hF, ⟨c⟩⟩ := exists_natCoord hyp h1
  obtain ⟨l, hlL, hl⟩ := exists_mem_autOn_of_mem_fsuL0 h37 h38 hyp hyL0
  have hloc := hyp.fsu.maximal.1
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hL0U : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (fsuL0_le_normalizer_fsuVM T L I) (fsuL0_le_normalizer hloc)
  set φ := conjAct (fsuUL T L I) ⟨y, hL0U hyL0⟩ with hφdef
  have hφl : φ = conjAct (fsuUL T L I) ⟨l, hLU hlL⟩ := by
    ext u
    rw [coe_conjAct_apply', coe_conjAct_apply']
    exact hl u u.2
  have hφ : φ ∈ autOn L (fsuUL T L I) := mem_autOn_iff'.mpr ⟨_, hlL, hφl.symm⟩
  set h := c.eρ.symm ⟨φ, hφ⟩ with hhdef
  have hhφ : ((c.eρ h : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) = φ := by
    rw [hhdef, MulEquiv.apply_symm_apply]
  have hodd : Odd (orderOf h) := by
    have h2 : orderOf h = orderOf φ := by
      rw [← MulEquiv.orderOf_eq c.eρ h, ← Subgroup.orderOf_coe, hhφ]
    rw [h2]
    refine Odd.of_dvd_nat hyodd ((orderOf_map_dvd (conjAct (fsuUL T L I)) _).trans ?_)
    rw [← Subgroup.orderOf_coe]
  have hmemC : ∀ {a : G} (ha : a ∈ Subgroup.normalizer (fsuUL T L I : Set G)),
      a * w * a⁻¹ * w⁻¹ ∈ fsuCVM T L I →
        conjAct (fsuUL T L I) ⟨a, ha⟩ ⟨w, hwU⟩ * (⟨w, hwU⟩ : ↥(fsuUL T L I))⁻¹ ∈
          Ch10.cV1 T L I := by
    intro a ha h
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAct_apply']
    exact h.2
  have hN : ∀ b : F, ∃ b' : F, h * (c.g⁻¹ * unipSL b * c.g) * h⁻¹ = c.g⁻¹ * unipSL b' * c.g := by
    intro b
    have hp : ((c.eρ (c.g⁻¹ * unipSL b * c.g) : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) ∈ autOn (T ⊓ L) (fsuUL T L I) :=
      (c.unip _).mpr ⟨b, by group⟩
    obtain ⟨s, hsTL, hs⟩ := mem_autOn_iff'.mp hp
    have hconj : ((c.eρ (h * (c.g⁻¹ * unipSL b * c.g) * h⁻¹) : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) ∈ autOn (T ⊓ L) (fsuUL T L I) := by
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hhφ,
        ← hs, hφdef, ← map_inv, ← map_mul, ← map_mul]
      refine mem_autOn_iff'.mpr ⟨_, ?_, rfl⟩
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hyN _).mp hsTL
    obtain ⟨b', hb'⟩ := (c.unip _).mp hconj
    exact ⟨b', by rw [← hb']; group⟩
  set w' : ↥(fsuUL T L I) := ⟨w, hwU⟩ with hw'def
  have hv : Multiplicative.toAdd (c.β w') ≠ 0 := by
    intro h0
    apply hwC
    have h2 : c.β w' = 1 := by rw [← ofAdd_toAdd (c.β w'), h0, ofAdd_zero]
    have h3 := (c.ker w').mp h2
    rw [Subgroup.mem_subgroupOf] at h3
    have hLV' : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
    exact ⟨hLV' hwU, h3⟩
  have hu : (unipSL 1 : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
      ((c.g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c.β w'))) =
      (c.g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c.β w')) := by
    have hp : ((c.eρ (c.g⁻¹ * unipSL 1 * c.g) : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) ∈ autOn (T ⊓ L) (fsuUL T L I) :=
      (c.unip _).mpr ⟨1, by group⟩
    obtain ⟨s, hsTL, hs⟩ := mem_autOn_iff'.mp hp
    have h2 := c.beta_eq (γ := c.g⁻¹ * unipSL 1 * c.g) (w := w')
      (by rw [← hs]; exact hmemC s.2 (hwS s hsTL))
    have h3 := congrArg (fun u => (c.g : Matrix (Fin 2) (Fin 2) F).mulVec u) h2
    simp only [Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
      coe_mul_inv_SL, Matrix.one_mul] at h3
    rw [← Matrix.mulVec_mulVec] at h3
    exact h3
  have hfix : (h : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (c.β w')) =
      Multiplicative.toAdd (c.β w') :=
    c.beta_eq (by rw [hhφ, hφdef]; exact hmemC _ hwy)
  have hh1 := eq_one_of_natural hodd hN hv hu hfix
  intro u hu'
  have h4 : φ = 1 := by
    rw [← hhφ, hh1, map_one]
    rfl
  have h5 := congrArg (fun f : MulAut ↥(fsuUL T L I) => ((f ⟨u, hu'⟩ : ↥(fsuUL T L I)) : G)) h4
  simp only [hφdef, coe_conjAct_apply', MulAut.one_apply] at h5
  exact h5

end CFSG.Quasithin.Vol2.Ch10.SecA
