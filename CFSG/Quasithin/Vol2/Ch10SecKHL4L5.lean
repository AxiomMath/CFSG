module

public import CFSG.Quasithin.Vol2.Ch10SecKHNine
public import CFSG.Quasithin.Vol2.Ch10SecBFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Quasithin.H13.VolIAutSLFive

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.LieType.BorelTits Matrix
open scoped Pointwise

namespace C10KH

theorem exists_radical_of_mulEquiv {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (e : Q ≃* SpecialLinearGroup (Fin n) (ZMod 2)) (hn : n = 4 ∨ n = 5) (U : Sylow 2 Q)
    {D : Subgroup Q} (hD : Nat.card D = 9)
    (hDU : (D : Set Q) * ((U : Subgroup Q) : Set Q) = ((U : Subgroup Q) : Set Q) * D) :
    ∃ R : Subgroup Q, R ≤ D ⊔ U ∧ IsPGroup 2 R ∧
      (∀ x ∈ D ⊔ (U : Subgroup Q), ∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧
      ∀ a ∈ (U : Subgroup Q), ∀ b ∈ (U : Subgroup Q), a * b * a⁻¹ * b⁻¹ ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' : Sylow 2 (SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective U with hU'
  have hU'c : (U' : Subgroup _) = (U : Subgroup Q).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ U
  have hD' : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD]
  have hDU' : ((D.map e.toMonoidHom : Subgroup _) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) *
      ((U' : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
        Set (SpecialLinearGroup (Fin n) (ZMod 2))) =
        ((U' : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))) :
        Set (SpecialLinearGroup (Fin n) (ZMod 2))) *
          (D.map e.toMonoidHom : Subgroup _) := by
    rw [hU'c, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul, hDU]
  obtain ⟨R', hR'le, hR'p, hR'n, hR'c⟩ :=
    exists_radical_of_card_nine (K := ZMod 2) (Nat.card_zmod 2) hn U' hD' hDU'
  have hsup : ∀ x : Q, x ∈ D ⊔ (U : Subgroup Q) ↔
      e x ∈ D.map e.toMonoidHom ⊔ (U' : Subgroup _) := by
    intro x
    rw [hU'c, ← Subgroup.map_sup]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  have hU : ∀ x : Q, x ∈ (U : Subgroup Q) → e x ∈ (U' : Subgroup _) := fun x hx => by
    rw [hU'c]
    exact Subgroup.mem_map_of_mem _ hx
  refine ⟨R'.comap e.toMonoidHom, fun x hx => (hsup x).2 (hR'le hx),
    hR'p.comap_of_injective _ e.injective, fun x hx r hr => ?_, fun a ha b hb => ?_⟩
  · rw [Subgroup.mem_comap] at hr ⊢
    simpa using hR'n (e x) ((hsup x).1 hx) (e r) hr
  · rw [Subgroup.mem_comap]
    simpa using hR'c (e a) (hU a ha) (e b) (hU b hb)

theorem commutator_conj_mem_pCoreOf {Q : Type*} [Group Q] [Finite Q] {n : ℕ}
    (e : Q ≃* SpecialLinearGroup (Fin n) (ZMod 2)) (hn : n = 4 ∨ n = 5) (U : Sylow 2 Q)
    {Y : Subgroup Q} (hUY : (U : Subgroup Q) ≤ Subgroup.normalizer (Y : Set Q))
    (h9 : (pCoreOf 2 Y).relIndex Y = 9) {a b y : Q} (ha : a ∈ (U : Subgroup Q))
    (hb : b ∈ (U : Subgroup Q)) (hy : y ∈ Y) :
    (a * b * a⁻¹ * b⁻¹) * (b * a * y * (b * a)⁻¹) * (a * b * a⁻¹ * b⁻¹)⁻¹ *
      (b * a * y * (b * a)⁻¹)⁻¹ ∈ pCoreOf 2 Y := by
  obtain ⟨D, hDY, hD⟩ := exists_le_card_nine h9
  have hdec := fun y hy => exists_inv_mul_mem hDY hD h9 (y := y) hy
  have hPU := pCoreOf_le_of_le_normalizer U hUY
  have hDU := mul_comm_of_le_normalizer hDY hUY hPU hdec
  obtain ⟨R, -, hRp, hRn, hRc⟩ := exists_radical_of_mulEquiv e hn U hD hDU
  have hba : b * a ∈ (U : Subgroup Q) := Subgroup.mul_mem _ hb ha
  have hw : b * a * y * (b * a)⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hUY hba) y).1 hy
  have hcU : a * b * a⁻¹ * b⁻¹ ∈ (U : Subgroup Q) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  exact commutator_mem_pCoreOf (le_sup_of_dec hPU hdec) hRp hRn (hRc a ha b hb) (hUY hcU) hw

end C10KH

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial in
theorem factL4L5 : FactL4L5 := by
  intro Q _ _ k hk hQ A S Y hInn hS _ hSY _ h9 hnab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero k := ⟨by omega⟩
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hQ
  have hF2 : Nat.card F = 2 := by simpa using hF
  set e : Q ≃* SpecialLinearGroup (Fin k) (ZMod 2) :=
    e₀.trans (Setup.Family.statedProjSL_equiv_of_card_two k F hF2)
  set e' := e.trans (Setup.Family.projEquiv k)
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun f : MulAut Q => (f : Q → Q)) DFunLike.coe_injective
  have hinj : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
    refine (injective_iff_map_eq_one _).2 fun q hq => ?_
    have hc : e' q ∈ Subgroup.center (LinearFlag.projectiveSL k (ZMod 2)) := by
      refine Subgroup.mem_center_iff.2 fun z => ?_
      obtain ⟨x, rfl⟩ := e'.surjective z
      have h1 := congrArg (fun φ : MulAut Q => φ x) hq
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      rw [← map_mul, ← map_mul]
      congr 1
      calc x * q = q * x * q⁻¹ * q := by rw [h1]
        _ = q * x := by group
    rw [Setup.Family.center_projectiveSL_zmod_two, Subgroup.mem_bot] at hc
    exact e'.injective (hc.trans (map_one e').symm)
  have hcardQ : Nat.card (MulAut Q) ≤ 2 * Nat.card Q := by
    rw [Nat.card_congr (MulAut.congr e').toEquiv, Nat.card_congr e'.toEquiv]
    calc _ ≤ 2 * Nat.card (GL (Fin k) (ZMod 2)) :=
          H13.VolI.card_mulAut_projectiveSL_two_le (by omega)
      _ = 2 * Nat.card (LinearFlag.projectiveSL k (ZMod 2)) := by
        rw [H13.VolI.card_GL_zmod_two_eq, Nat.card_congr (Setup.Family.projEquiv k).toEquiv]
  set I := (MulAut.conj : Q →* MulAut Q).range with hIdef
  have hIA : I ≤ A := by
    rintro _ ⟨q, rfl⟩
    exact hInn q
  have hcardI : Nat.card I = Nat.card Q :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  by_contra hA
  have hAI : A = I := by
    have h1 := Subgroup.one_lt_index_of_ne_top hA
    have h2 := A.card_mul_index
    have h3 : Nat.card A ≤ Nat.card I := by
      rw [hcardI]
      have : Nat.card A * 2 ≤ Nat.card A * A.index := Nat.mul_le_mul_left _ h1
      omega
    exact (Subgroup.eq_of_le_of_card_ge hIA h3).symm
  have hSI : S ≤ I := hAI ▸ hS.1
  set S0 := S.comap (MulAut.conj : Q →* MulAut Q) with hS0def
  have hS0c : Nat.card S0 = Nat.card S := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hSI]
  have hS0p : IsPGroup 2 S0 := hS.2.1.comap_of_injective _ hinj
  have hidx : ¬ 2 ∣ S0.index := by
    have h1 := S0.index_mul_card
    have h2 := (S.subgroupOf A).index_mul_card
    have h3 : Nat.card (S.subgroupOf A) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
    have h4 : Nat.card A = Nat.card Q := by rw [hAI, hcardI]
    have hpos : 0 < Nat.card S := Nat.card_pos
    have h5 : S0.index = (S.subgroupOf A).index := by
      rw [h3, h4, ← h1, hS0c] at h2
      exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm
    rw [h5]
    exact hS.2.2
  set U : Sylow 2 Q := hS0p.toSylow hidx
  have hconj : ∀ s ∈ S0, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := fun s hs y hy => by
    simpa using hSY _ hs y hy
  have hUY : (U : Subgroup Q) ≤ Subgroup.normalizer (Y : Set Q) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj s hs y, fun h => ?_⟩
    have h' := hconj s⁻¹ (S0.inv_mem hs) _ h
    simpa [mul_assoc] using h'
  obtain ⟨α, hα, β, hβ, y, hy, hne⟩ := hnab
  obtain ⟨a, rfl⟩ := hSI hα
  obtain ⟨b, rfl⟩ := hSI hβ
  apply hne
  have key := C10KH.commutator_conj_mem_pCoreOf e hk U hUY h9 (a := a) (b := b) hα hβ hy
  have heq : (MulAut.conj a * MulAut.conj b) y * ((MulAut.conj b * MulAut.conj a) y)⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (b * a * y * (b * a)⁻¹) * (a * b * a⁻¹ * b⁻¹)⁻¹ *
        (b * a * y * (b * a)⁻¹)⁻¹ := by
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    group
  rw [heq]
  exact key

end CFSG.Quasithin.Vol2.Ch10.SecB
