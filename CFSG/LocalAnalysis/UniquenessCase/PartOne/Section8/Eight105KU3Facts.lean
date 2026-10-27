module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
import CFSG.ClassicalGroups.UnitaryFlag.SU3L2Subgroup
import CFSG.ClassicalGroups.UnitaryFlag.SU3L2Aut
import CFSG.ClassicalGroups.UnitaryFlag.SU3L2Normalizer
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Perfect
import CFSG.Mathlib.Arithmetic.TwoPowModThree
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

theorem eq_bot_of_isPGroup_of_le_normalizer_of_isU3 {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : IsU3 X f) {K : Subgroup X} (hK : ⁅K, K⁆ = K) (hK2 : IsL2 (Bar2 K) f)
    {U : Subgroup X} (hU : IsPGroup 2 U) (hKU : K ≤ normalizer (U : Set X)) : U = ⊥ := by
  have hlt : 1 < Nat.card (Bar2 K) := by
    have hs := CFSG.Blueprint.LieModel.statedClassicalModel hK2 (by decide)
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hs]
    have h1 : 1 ≤ f := hs.1.2.1
    have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1)
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
    calc 1 < 2 * 3 := by norm_num
      _ ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := Nat.mul_le_mul h2 (by omega)
  by_contra hUne
  have hKbot : K = ⊥ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3
      hX hU hUne (Subgroup.isPerfect_iff.mpr hK) hKU
  have hdvd : Nat.card (Bar2 K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  have hKcard : Nat.card ↥K = 1 := by rw [hKbot, Subgroup.card_bot]
  rw [hKcard] at hdvd
  exact absurd hlt (not_lt.mpr (Nat.le_of_dvd (by norm_num) hdvd))

theorem isL2_of_isL2_bar2_of_isU3 {X : Type} [Group X] [Finite X] {f : ℕ} (hX : IsU3 X f)
    {K : Subgroup X} (hK : ⁅K, K⁆ = K) (hK2 : IsL2 (Bar2 K) f) : IsL2 ↥K f := by
  have hcore : CFSG.pCore 2 ↥K = ⊥ := by
    have hKU : K ≤ normalizer (((CFSG.pCore 2 ↥K).map K.subtype) : Set X) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk u hu
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu
      exact Subgroup.mem_map_of_mem K.subtype
        ((CFSG.pCore_normal (G := ↥K)).conj_mem y hy ⟨k, hk⟩)
    have hU : ((CFSG.pCore 2 ↥K).map K.subtype) = ⊥ :=
      eq_bot_of_isPGroup_of_le_normalizer_of_isU3 hX hK hK2
        ((CFSG.pCore_isPGroup (G := ↥K)).map K.subtype) hKU
    exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥K)
      K.subtype_injective).mp hU
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot) hK2

theorem exists_mem_centralizer_orderOf_and_forall_twoGroup {m : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 m F) (hm : 2 ≤ m) {L : Subgroup (unitarySU 2 m F 3)}
    (hL2 : IsL2 L m) :
    ∃ g ∈ centralizer (L : Set (unitarySU 2 m F 3)), orderOf g = 2 ^ m + 1 ∧
      ∀ A : Subgroup (MulAut (unitarySU 2 m F 3)), IsPGroup 2 A →
        (∀ α ∈ A, ∀ x ∈ L, α x = x) →
        Nat.card A ≤ 2 ∧ ∀ α ∈ A, α ≠ 1 → α g = g⁻¹ := by
  obtain ⟨v, hv, hL⟩ := exists_nonisotropic_forall_mem_iff_of_isL2 h hm hL2
  obtain ⟨μ, hμord, g, hg, hgord, hgv, hgw⟩ := exists_mem_centralizer_of_nonisotropic h hv hL
  have hμ : μ ^ (2 ^ m + 1) = 1 := by rw [← hμord]; exact pow_orderOf_eq_one μ
  exact ⟨g, hg, hgord, fun A hA hAL =>
    card_le_two_and_apply_eq_inv_of_forall_mem h hm hv hL hμ hgv hgw hA hAL⟩

theorem exists_unitarySU_model_of_isU3 {X : Type} [Group X] [Finite X] {f : ℕ} (hX : IsU3 X f)
    (hf : 4 ≤ f) (heven : Even f) {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hK2 : IsL2 (Bar2 K) f) :
    ∃ (F : Type) (_ : Field F), ∃ (h : UnitaryFieldData 2 f F) (e : X ≃* unitarySU 2 f F 3)
      (v : Fin 3 → F),
      stdHermForm h 3 v v ≠ 0 ∧
        ∀ g : unitarySU 2 f F 3, g ∈ K.map e.toMonoidHom ↔
          ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = v := by
  obtain ⟨-, F, hFld, hFfin, hF, ⟨e0⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hgcd : Nat.gcd 3 (2 ^ f + 1) = 1 := by
    have hmod : 2 ^ f % 3 = 1 := CFSG.two_pow_mod_three_of_even heven
    have hnot : ¬ 3 ∣ 2 ^ f + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hmod]
      norm_num
    exact Nat.prime_three.coprime_iff_not_dvd.2 hnot
  let h : UnitaryFieldData 2 f F := unitaryFieldDataOfCard hF
  have hbot : unitaryScalars h 3 = ⊥ := by
    rw [Subgroup.eq_bot_iff_card, card_unitaryScalars h (by norm_num : 1 ≤ 3), hgcd]
  have hinj : Function.Injective (unitaryProj h 3) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj]
    exact hbot
  let e : X ≃* unitarySU 2 f F 3 :=
    e0.trans ((unitaryPSUEquivStated hF).symm.trans
      (MulEquiv.ofBijective (unitaryProj h 3) ⟨hinj, unitaryProj_surjective h 3⟩).symm)
  have hK'2 : IsL2 ↥(K.map (e : X →* unitarySU 2 f F 3)) f :=
    CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupMap e K)
      (isL2_of_isL2_bar2_of_isU3 hX hK hK2)
  obtain ⟨v, hv, hL⟩ := exists_nonisotropic_forall_mem_iff_of_isL2 h (by omega) hK'2
  exact ⟨F, hFld, h, e, v, hv, hL⟩

theorem eq_bot_and_exists_inv_of_isU3 {X : Type} [Group X] [Finite X] {f : ℕ} (hX : IsU3 X f)
    (hf : 4 ≤ f) (heven : Even f) {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hK2 : IsL2 (Bar2 K) f) :
    (∀ U : Subgroup X, IsPGroup 2 U → K ≤ normalizer (U : Set X) → U = ⊥) ∧
      ∃ g ∈ centralizer (K : Set X), orderOf g = 2 ^ f + 1 ∧
        ∀ A : Subgroup (MulAut X), IsPGroup 2 A → (∀ α ∈ A, ∀ x ∈ K, α x = x) →
          Nat.card A ≤ 2 ∧ ∀ α ∈ A, α ≠ 1 → α g = g⁻¹ := by
  refine ⟨fun U hU hKU => eq_bot_of_isPGroup_of_le_normalizer_of_isU3 hX hK hK2 hU hKU, ?_⟩
  obtain ⟨F, hFld, h, e, -, -, -⟩ := exists_unitarySU_model_of_isU3 hX hf heven hK hK2
  have hK'2 : IsL2 ↥(K.map (e : X →* unitarySU 2 f F 3)) f :=
    CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupMap e K)
      (isL2_of_isL2_bar2_of_isU3 hX hK hK2)
  obtain ⟨g', hg', hg'ord, hg'A⟩ :=
    exists_mem_centralizer_orderOf_and_forall_twoGroup h (by omega) hK'2
  let g : X := e.symm g'
  have hg : g ∈ centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff] at hg' ⊢
    intro x hx
    have hx' : e x ∈ K.map (e : X →* unitarySU 2 f F 3) :=
      Subgroup.mem_map_of_mem (e : X →* unitarySU 2 f F 3) hx
    have h := congrArg (fun y => e.symm y) (hg' (e x) hx')
    simpa [g] using h
  have hord : orderOf g = 2 ^ f + 1 :=
    calc orderOf g = orderOf (e.symm g') := rfl
      _ = orderOf g' := orderOf_injective (e.symm : unitarySU 2 f F 3 →* X) e.symm.injective g'
      _ = 2 ^ f + 1 := hg'ord
  refine ⟨g, hg, hord, ?_⟩
  intro A hA hAK
  let φ : MulAut X ≃* MulAut (unitarySU 2 f F 3) := MulAut.congr e
  have hφe : ∀ (β : MulAut X) (z : X), (φ β) (e z) = e (β z) := by
    intro β z
    change (e.symm.trans (β.trans e)) (e z) = e (β z)
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
  let A' : Subgroup (MulAut (unitarySU 2 f F 3)) := A.map φ.toMonoidHom
  have hA' : IsPGroup 2 A' := hA.map φ.toMonoidHom
  have hA'L : ∀ α ∈ A', ∀ x ∈ K.map (e : X →* unitarySU 2 f F 3), α x = x := by
    rintro _ ⟨α, hα, rfl⟩ x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    change (φ α) (e y) = e y
    rw [hφe α y, hAK α hα y hy]
  obtain ⟨hcard, hinv⟩ := hg'A A' hA' hA'L
  have hcardA : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective φ.injective
  refine ⟨hcardA ▸ hcard, ?_⟩
  intro α hα hα1
  have hφα1 : φ α ≠ 1 := fun h => hα1 (φ.injective (by rw [h, map_one]))
  have h := hinv (φ α) (Subgroup.mem_map_of_mem φ.toMonoidHom hα) hφα1
  have hg' : g' = e g := (e.apply_symm_apply g').symm
  have hφg : e (α g) = (φ α) (e g) := (hφe α g).symm
  apply e.injective
  calc e (α g) = (φ α) (e g) := hφg
    _ = (φ α) g' := by rw [hg']
    _ = g'⁻¹ := h
    _ = e (g⁻¹) := by rw [hg', map_inv]

theorem not_le_normalizer_of_isU3 {X : Type} [Group X] [Finite X] {f : ℕ} (hX : IsU3 X f)
    (hf : 4 ≤ f) (heven : Even f) {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hK2 : IsL2 (Bar2 K) f) (T₂ : Sylow 2 X) :
    ¬ (T₂ : Subgroup X) ≤ normalizer (K : Set X) := by
  obtain ⟨F, hFld, h, e, v, hv, hL⟩ := exists_unitarySU_model_of_isU3 hX hf heven hK hK2
  intro hTK
  let T' : Sylow 2 (unitarySU 2 f F 3) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T₂
  have hnot := not_le_normalizer_of_nonisotropic h (by omega) hv hL T'
  apply hnot
  have hmap : (T₂ : Subgroup X).map e.toMonoidHom ≤
      (normalizer (K : Set X)).map e.toMonoidHom :=
    Subgroup.map_mono (f := e.toMonoidHom) hTK
  rw [Subgroup.map_equiv_normalizer_eq K e] at hmap
  simpa [T'] using hmap

theorem kU3Facts_holds : KU3Facts := fun _ _ _ _ hX hf heven _ hK hK2 =>
  ⟨(eq_bot_and_exists_inv_of_isU3 hX hf heven hK hK2).1,
    not_le_normalizer_of_isU3 hX hf heven hK hK2,
    (eq_bot_and_exists_inv_of_isU3 hX hf heven hK hK2).2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
