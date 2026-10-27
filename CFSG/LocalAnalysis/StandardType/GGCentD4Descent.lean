module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Lang.D4Three.DiagSquare
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley


private theorem desc_exists_sq_eq_of_char_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (a : F) : ∃ b : F, b ^ 2 = a := by
  have hinj : Function.Injective fun x : F => x ^ 2 := fun x y hxy =>
    CharTwo.sq_inj.mp hxy
  exact Finite.surjective_of_injective hinj a

private theorem desc_exists_sq_eq_unit {F : Type} [Field F] [Finite F] [CharP F 2]
    (a : Fˣ) : ∃ b : Fˣ, b ^ 2 = a := by
  obtain ⟨u, hu⟩ := desc_exists_sq_eq_of_char_two (F := F) (a : F)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hu.symm)
  exact ⟨Units.mk0 u hu0, Units.ext (by simpa using hu)⟩

theorem ntpD4_descent_untwisted
    {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 : ℕ) ^ f)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra F L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f)) :
    adjointGroup Tag.D4 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (adjointGroup Tag.D4 F).map (baseChangeGL (algebraMap F L)) := by
  classical
  have hFr' : ∀ c : L, Fr c = c ^ Nat.card F := fun c => by rw [hF]; exact hFr c
  have hbij : Function.Bijective Fr :=
    CFSG.LieType.Chevalley.frobenius_bijective (k := F) Fr hFr'
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hbij with hσ
  have hσFr : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hfix' : ∀ c : L, σ c = c → c ∈ Set.range (algebraMap F L) := by
    intro c hc
    refine CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := F) (L := L) ?_
    rw [← hFr', ← hσFr]
    exact hc
  refine le_antisymm ?_ ?_
  ·
    intro g hg
    have hg' : g ∈ entrywiseFixedGroup Tag.D4 σ := ⟨hg.1, by
      change Units.map (entrywiseHom σ.toRingHom) g = g
      rw [hσFr]
      exact hg.2⟩
    obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg'
    refine mul_mem ?_ ?_
    ·
      obtain ⟨hhT, -, hhF⟩ := hh
      obtain ⟨c, rfl⟩ := exists_cartanChar_eq_of_mem_torusGroup hhT
      have h0 : Units.map (entrywiseHom σ.toRingHom)
          (rootDiagUnit Tag.D4 (cartanChar c)) =
          rootDiagUnit Tag.D4
            (fun i => Units.map σ.toRingHom.toMonoidHom (cartanChar c i)) :=
        Units.ext (entrywise_rootDiag σ.toRingHom (cartanChar c))
      have hinj := rootDiagUnit_injective (τ := Tag.D4) (h0.symm.trans hhF)
      have hfixa : ∀ l, σ (cartanChar c l : L) = (cartanChar c l : L) := fun l =>
        congrArg Units.val (congrFun hinj l)
      have hrange : ∀ l, ∃ s : F, algebraMap F L s = (cartanChar c l : L) := fun l =>
        hfix' _ (hfixa l)
      choose s hs using hrange
      have hs0 : ∀ l, s l ≠ 0 := by
        intro l h0'
        have h1 := hs l
        rw [h0', map_zero] at h1
        exact (cartanChar c l).ne_zero h1.symm
      let a'' : Fin Tag.D4.rank → Fˣ := fun l => Units.mk0 (s l) (hs0 l)
      have ha'' : ∀ l, Units.map (algebraMap F L).toMonoidHom (a'' l) = cartanChar c l :=
        fun l => Units.ext (hs l)
      have hcharF : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two hf hF
      have hsq : ∃ b : Fin Tag.D4.rank → Fˣ, (fun l => b l ^ 2) = a'' := by
        choose b hb using fun l => desc_exists_sq_eq_unit (F := F) (a'' l)
        exact ⟨b, funext hb⟩
      obtain ⟨b, hb⟩ := hsq
      have hmem : rootDiagUnit Tag.D4 a'' ∈ adjointGroup Tag.D4 F := by
        rw [← hb]
        exact rootDiagUnit_sq_mem_adjointGroup_D4 b
      refine ⟨rootDiagUnit Tag.D4 a'', hmem, ?_⟩
      rw [CFSG.TauCetiBridge.BigCell.baseChangeGL_rootDiagUnit,
        show (fun k => Units.map (algebraMap F L).toMonoidHom (a'' k)) = cartanChar c from
          funext fun l => ha'' l]
    ·
      rw [fixedFieldImage_eq_closure] at hj
      refine (Subgroup.closure_le _).2 ?_ hj
      rintro _ ⟨i, c, hc, rfl | rfl⟩
      · obtain ⟨c', hc'⟩ := hfix' c hc
        exact ⟨xUnit Tag.D4 F i c', xUnit_mem_adjointGroup i c',
          by rw [baseChangeGL_xUnit, hc']⟩
      · obtain ⟨c', hc'⟩ := hfix' c hc
        exact ⟨yUnit Tag.D4 F i c', yUnit_mem_adjointGroup i c',
          by rw [baseChangeGL_yUnit, hc']⟩
  ·
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨baseChangeGL_mem_adjointGroup (f := algebraMap F L) hg,
      units_map_entrywiseHom_baseChangeGL_algebraMap (k := F) (L := L) Fr hFr' g⟩

end CFSG.StandardType.NTPlane

end
