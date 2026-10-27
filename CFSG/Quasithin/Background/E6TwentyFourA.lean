module

public import CFSG.Quasithin.Background.E6TwentyFour
public import CFSG.Quasithin.Background.E6Three
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.Quasithin.Background.E3OffenderB

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open
open scoped commutatorElement

section Translate

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem map_valHom_commSub_le (X : Subgroup G) :
    (commSub ⊤ (autI hV X)).map (E3.valHom hV) ≤ ⁅V, X⁆ := by
  unfold commSub
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨ξ, hξ, w, -, rfl⟩, rfl⟩
  obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).1 hξ
  have h1 : E3.valHom hV ((convI hV g) w * w⁻¹) = ⁅(g : G), w.val⁆ := by
    rw [map_mul, map_inv, E3.valHom_apply, E3.valHom_apply, convI_apply_val,
      commutatorElement_def]
  rw [SetLike.mem_coe, h1, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hgX w.val_mem

end Translate

section Hyp

variable {G : Type} [Group G] [Finite G] {T M V U X : Subgroup G}

theorem hyp102_autI (hV : IsElemAbelian 2 V) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hU1 : 1 < E3.mQuot V U) (hUm : E3.mQuot V U < E3.mParam (autI hV M))
    (hXMU : X ≤ M ⊓ Subgroup.centralizer (U : Set G)) (hXcyc : IsCyclic (autI hV X))
    (hXcard : Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1)
    (hUX2 : U ⊔ ⁅V, X⁆ = V)
    (hreg : ∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v = v * x →
      x ∈ Subgroup.centralizer (V : Set G))
    (hnorm : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x ∈ X, ∃ y ∈ X, g * x * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    Asc81c.Hyp102 (autI hV M) (autI hV X) ∧ (fixV (autI hV X)).map (E3.valHom hV) = U ∧
      Nat.card (commSub ⊤ (autI hV X)) = 2 ^ E3.mQuot V U := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  set n := E3.mQuot V U with hndef
  have hUV : U ≤ V := hU.1
  have hXN : X ≤ Subgroup.normalizer (V : Set G) :=
    hXMU.trans (inf_centralizer_le_normalizer h hUV hU.2.1)
  have hXU : X ≤ Subgroup.centralizer (U : Set G) := hXMU.trans inf_le_right
  have h2n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hU1
  have hXodd : Odd (Nat.card (autI hV X)) := by
    rw [hXcard]
    have he : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd (by omega) he odd_one
  have hXne : autI hV X ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hXcard
    omega
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV ha hb
  have hVXle : ⁅V, X⁆ ≤ V :=
    calc ⁅V, X⁆ ≤ U ⊔ ⁅V, X⁆ := le_sup_right
      _ = V := hUX2
  have hCVX : ∀ v ∈ V, v ∈ Subgroup.centralizer (X : Set G) → v ∈ U := by
    intro v hv hvC
    have hv' : v ∈ ((U ⊔ ⁅V, X⁆ : Subgroup G) : Set G) := by
      rw [hUX2]
      exact hv
    have hN : ⁅V, X⁆ ≤ Subgroup.normalizer (U : Set G) := fun c hc =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun u hu =>
        hcomm _ (hUV hu) _ (hVXle hc))
    rw [Subgroup.coe_mul_of_right_le_normalizer_left U ⁅V, X⁆ hN] at hv'
    obtain ⟨u, hu, c, hc, rfl⟩ := hv'
    have hu' : u ∈ Subgroup.centralizer (X : Set G) := Subgroup.le_centralizer_iff.1 hXU hu
    have hcC : c ∈ Subgroup.centralizer (X : Set G) := by
      have h1 := (Subgroup.centralizer (X : Set G)).mul_mem
        ((Subgroup.centralizer (X : Set G)).inv_mem hu') hvC
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
    by_cases hc1 : c = 1
    · show u * c ∈ U
      rw [hc1, mul_one]
      exact hu
    · exfalso
      apply hXne
      rw [autI_eq_bot_iff hV hXN]
      intro x hx
      exact hreg c hc hc1 x hx (Subgroup.mem_centralizer_iff.1 hcC x hx)
  have hfix : ∀ v : IntMod V hV, v ∈ fixV (autI hV X) ↔ v.val ∈ U := by
    intro v
    rw [mem_fixV_autI hV hXN v]
    exact ⟨hCVX v.val v.val_mem, fun hv => Subgroup.le_centralizer_iff.1 hXU hv⟩
  have hfixmap : (fixV (autI hV X)).map (E3.valHom hV) = U := by
    ext g
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hfix v).1 hv
    · intro hg
      exact ⟨IntMod.mk hV ⟨g, hUV hg⟩, (hfix _).2 hg, rfl⟩
  have hrkIdx : rkIdx (fixV (autI hV X)) = n := by
    rw [E3.rkIdx_eq_mQuot_map hV, hfixmap]
  have hprod := Asc81c.card_fixV_mul_card_commSub hW hXodd
  have hrk : rk (commSub ⊤ (autI hV X)) = n := by
    have h1 := rk_add_rkIdx (fixV (autI hV X))
    have h2 : rk (fixV (autI hV X)) + rk (commSub ⊤ (autI hV X)) = rk (IntMod V hV) := by
      unfold rk
      rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hprod]
    omega
  have hcardc : Nat.card (commSub ⊤ (autI hV X)) = 2 ^ n := by
    rw [card_eq_two_pow hW, hrk]
  have hsemi : ∀ v ∈ commSub ⊤ (autI hV X), v ≠ 1 → ∀ ξ ∈ autI hV X, ξ v = v → ξ = 1 := by
    intro v hv hv1 ξ hξ hξv
    obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).1 hξ
    rw [convI_eq_one_iff]
    have hvX : v.val ∈ ⁅V, X⁆ := map_valHom_commSub_le hV X ⟨v, hv, rfl⟩
    have hv1' : v.val ≠ 1 := fun h0 => hv1 (IntMod.val_injective (h0.trans IntMod.val_one.symm))
    have hcv : (g : G) * v.val = v.val * g := by
      have h1 := congrArg IntMod.val hξv
      rw [convI_apply_val] at h1
      calc (g : G) * v.val = (g * v.val * (g : G)⁻¹) * g := by group
        _ = v.val * g := by rw [h1]
    exact hreg v.val hvX hv1' g hgX hcv
  have hregular : ∀ v ∈ commSub ⊤ (autI hV X), v ≠ 1 → ∀ w ∈ commSub ⊤ (autI hV X), w ≠ 1 →
      ∃! ξ : autI hV X, (ξ : MulAut (IntMod V hV)) v = w := by
    intro v hv hv1 w hw hw1
    let f : autI hV X → ↥(((commSub ⊤ (autI hV X)) : Set (IntMod V hV)) \ {1}) := fun ξ =>
      ⟨(ξ : MulAut (IntMod V hV)) v, Asc81c.commSub_stable' ξ.2 hv, fun h0 => hv1 (by
        have h1 : (ξ : MulAut (IntMod V hV)) v = (ξ : MulAut (IntMod V hV)) 1 := by
          rw [map_one]
          exact h0
        exact (ξ : MulAut (IntMod V hV)).injective h1)⟩
    have hf : Function.Injective f := by
      intro ξ₁ ξ₂ h12
      have h12' : (ξ₁ : MulAut (IntMod V hV)) v = (ξ₂ : MulAut (IntMod V hV)) v :=
        congrArg Subtype.val h12
      have h2 : ((ξ₂ : MulAut (IntMod V hV))⁻¹ * ξ₁) v = v := by
        rw [MulAut.mul_apply, h12', MulAut.inv_apply_self]
      have h1 := hsemi v hv hv1 _ ((autI hV X).mul_mem ((autI hV X).inv_mem ξ₂.2) ξ₁.2) h2
      apply Subtype.ext
      have h3 := congrArg (fun x => (ξ₂ : MulAut (IntMod V hV)) * x) h1
      simpa using h3
    have hcardf : Nat.card ↥(((commSub ⊤ (autI hV X)) : Set (IntMod V hV)) \ {1}) ≤
        Nat.card (autI hV X) := by
      rw [Asc81c.card_diff_one, hcardc, hXcard]
    have hbij : Function.Bijective f := hf.bijective_of_nat_card_le hcardf
    obtain ⟨ξ, hξ⟩ := hbij.2 ⟨w, hw, hw1⟩
    refine ⟨ξ, congrArg Subtype.val hξ, fun η hη => hf ?_⟩
    rw [hξ]
    exact Subtype.ext hη
  have hnormal : ∀ φ ∈ autI hV M,
      (fixV (autI hV X)).map (φ : MulAut (IntMod V hV)).toMonoidHom = fixV (autI hV X) →
      ∀ ξ ∈ autI hV X, φ * ξ * φ⁻¹ ∈ autI hV X := by
    intro φ hφ hφfix ξ hξ
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨x, hxX, rfl⟩ := (mem_autI hV).1 hξ
    have hgU : (g : G) ∈ Subgroup.normalizer (U : Set G) := by
      have hle : U.map (MulAut.conj (g : G)).toMonoidHom ≤ U := by
        rintro _ ⟨u, hu, rfl⟩
        have hmem : IntMod.mk hV ⟨u, hUV hu⟩ ∈ fixV (autI hV X) := (hfix _).2 hu
        have h1 : convI hV g (IntMod.mk hV ⟨u, hUV hu⟩) ∈ fixV (autI hV X) := by
          rw [← hφfix]
          exact ⟨_, hmem, rfl⟩
        have h2 := (hfix _).1 h1
        rw [convI_apply_val] at h2
        exact h2
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective).ge
    obtain ⟨y, hyX, hyC⟩ := hnorm g ⟨hgM, g.2⟩ hgU x hxX
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hXN hyX
    refine (mem_autI hV).2 ⟨⟨y, hyN⟩, hyX, ?_⟩
    have h1 : convI hV (g * x * g⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
      rw [convI_eq_one_iff]
      exact hyC
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [← h1, map_mul, map_mul, map_inv]
  refine ⟨⟨⟨autI_mono hV (hXMU.trans inf_le_left), hXne, hXcyc, hXodd, hregular, hnormal⟩, ?_⟩,
    hfixmap, hcardc⟩
  rw [hrk]
  exact hUm

end Hyp

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commSub_bot' {W : Type*} [CommGroup W] (A : Subgroup W) :
    commSub A (⊥ : Subgroup (MulAut W)) = ⊥ := by
  rw [eq_bot_iff, commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, -, rfl⟩
  rw [Subgroup.mem_bot] at hx
  rw [hx, MulAut.one_apply, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem e624_of (h104 : Asc81c.Thm104) : E624Stmt := by
  intro G _ _ T M V U X hV h hm hU hr hU1 hUm hXMU hXcyc hXcard hUX1 hUX2 hreg hnorm
  classical
  obtain ⟨hyp, hfixmap, hcardc⟩ :=
    hyp102_autI hV h hU hU1 hUm hXMU hXcyc hXcard hUX2 hreg hnorm
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  set Gb := autI hV M with hGb
  set Xb := autI hV X with hXb
  set Ω : Set (Subgroup (MulAut (IntMod V hV))) :=
    {Y | ∃ φ ∈ Gb, Y = Xb.map (MulAut.conj φ).toMonoidHom} with hΩdef
  have hconj1 : Xb.map (MulAut.conj (1 : MulAut (IntMod V hV))).toMonoidHom = Xb := by
    rw [map_one]
    exact Subgroup.map_id Xb
  have hXΩ : Xb ∈ Ω := ⟨1, Gb.one_mem, hconj1.symm⟩
  have hΩhyp : ∀ Y ∈ Ω, Asc81c.Hyp102 Gb Y := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact Asc81c.hyp102_map_conj hyp hφ
  have hmapmap : ∀ φ ψ : MulAut (IntMod V hV), (Xb.map (MulAut.conj φ).toMonoidHom).map
      (MulAut.conj ψ).toMonoidHom = Xb.map (MulAut.conj (ψ * φ)).toMonoidHom := by
    intro φ ψ
    rw [Subgroup.map_map, map_mul]
    rfl
  have hΩinv : ∀ g ∈ Gb, ∀ Y ∈ Ω, Y.map (MulAut.conj g).toMonoidHom ∈ Ω := by
    rintro g hg _ ⟨φ, hφ, rfl⟩
    exact ⟨g * φ, Gb.mul_mem hg hφ, hmapmap φ g⟩
  obtain ⟨n, L, hsup, hind, hcomm, hperm, hVsup, hVind, hdich⟩ :=
    h104 (IntMod V hV) hW Gb Ω hΩhyp hΩinv
  have hΩcard : ∀ Y ∈ Ω, Nat.card Y = Nat.card Xb := by
    rintro _ ⟨φ, -, rfl⟩
    exact Subgroup.card_map_of_injective (MulAut.conj φ).injective
  have hΩne : ∀ Y ∈ Ω, Y ≠ ⊥ := fun Y hY => (hΩhyp Y hY).1.2.1
  have hXodd : Odd (Nat.card Xb) := hyp.1.2.2.2.1
  have hdich' : ∀ Y ∈ Ω, ∃ j, Y ≤ L j := fun Y hY => by
    rcases hdich Y hY with ⟨j, hj⟩ | ⟨j, hj, -⟩
    · exact ⟨j, hj.le⟩
    · exact ⟨j, hj⟩
  have hLtype : ∀ i, L i ≠ ⊥ → L i ∈ Ω ∨
      (Nat.card (L i) = 21 ∧ ∃ a ∈ L i, ∃ b ∈ L i, a * b ≠ b * a) := by
    intro i hi
    obtain ⟨Y, hYΩ, hYL⟩ := Asc81c.exists_mem_le_of_ne_bot hsup hind hcomm hdich' hi
    rcases hdich Y hYΩ with ⟨j, hj⟩ | ⟨j, hj, h21, hna⟩
    · have hji : j = i := Asc81c.eq_of_le_of_le hind (hΩne Y hYΩ) hj.le hYL
      left
      rw [← hji, ← hj]
      exact hYΩ
    · have hji : j = i := Asc81c.eq_of_le_of_le hind (hΩne Y hYΩ) hj hYL
      right
      rw [← hji]
      exact ⟨h21, hna⟩
  have hLodd : ∀ i, Odd (Nat.card (L i)) := by
    intro i
    by_cases hi : L i = ⊥
    · rw [hi, Subgroup.card_bot]
      exact odd_one
    · rcases hLtype i hi with hΩ | ⟨h21, -⟩
      · rw [hΩcard _ hΩ]
        exact hXodd
      · rw [h21]
        decide
  have hYeq : sSup Ω = e624Y hV M X := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ξ, hξ, rfl⟩
      exact Subgroup.subset_closure ⟨φ, hφ, ξ, hξ, rfl⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨φ, hφ, ξ, hξ, rfl⟩
      exact Subgroup.mem_sSup_of_mem (⟨φ, hφ, rfl⟩ : Xb.map (MulAut.conj φ).toMonoidHom ∈ Ω)
        (Subgroup.mem_map.2 ⟨ξ, hξ, rfl⟩)
  have hYodd : Odd (Nat.card (e624Y hV M X)) := by
    rw [← hYeq, ← hsup]
    exact Asc81c.odd_card_iSup_of_commute hcomm hLodd
  let ι' := {i : Fin n // L i ≠ ⊥}
  let e := Fintype.equivFin ι'
  have hsup' : (⨆ k, L (e.symm k).1) = ⨆ i, L i := by
    rw [Equiv.iSup_comp (g := fun i : ι' => L i.1) e.symm]
    exact iSup_ne_bot_subtype L
  have htrans : ∀ i j, L i ≠ ⊥ → L j ≠ ⊥ →
      ∃ φ ∈ Gb, (L i).map (MulAut.conj φ).toMonoidHom = L j := by
    intro i j hi hj
    obtain ⟨Y₁, ⟨φ₁, hφ₁, rfl⟩, hY₁⟩ := Asc81c.exists_mem_le_of_ne_bot hsup hind hcomm hdich' hi
    obtain ⟨Y₂, ⟨φ₂, hφ₂, rfl⟩, hY₂⟩ := Asc81c.exists_mem_le_of_ne_bot hsup hind hcomm hdich' hj
    have hψ : φ₂ * φ₁⁻¹ ∈ Gb := Gb.mul_mem hφ₂ (Gb.inv_mem hφ₁)
    obtain ⟨k, hk⟩ := hperm _ hψ i
    refine ⟨φ₂ * φ₁⁻¹, hψ, ?_⟩
    have hle : Xb.map (MulAut.conj φ₂).toMonoidHom ≤ L k := by
      rw [← hk]
      have h1 := Subgroup.map_mono (f := (MulAut.conj (φ₂ * φ₁⁻¹)).toMonoidHom) hY₁
      rwa [hmapmap, inv_mul_cancel_right] at h1
    have hkj : k = j := Asc81c.eq_of_le_of_le hind (hΩne _ ⟨φ₂, hφ₂, rfl⟩) hle hY₂
    rw [hk, hkj]
  refine ⟨Fintype.card ι', fun k => L (e.symm k).1, fun k => commSub ⊤ (L (e.symm k).1),
    ⟨?_, ?_, ?_⟩, ⟨Asc81c.fixV_inf_commSub_eq_bot' hW hYodd,
      Asc81c.fixV_sup_commSub_eq_top' hW hYodd⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hsup', hsup, hYeq]
  · exact (iSupIndep_ne_bot.2 hind).comp e.symm.injective
  · intro k k' hkk'
    exact hcomm _ _ fun h0 => hkk' (e.symm.injective (Subtype.ext h0))
  ·
    rw [Equiv.iSup_comp (g := fun i : ι' => commSub ⊤ (L i.1)) e.symm, ← hYeq, ← hVsup]
    apply le_antisymm
    · exact iSup_le fun i => le_iSup_of_le i.1 le_rfl
    · refine iSup_le fun i => ?_
      by_cases hi : L i = ⊥
      · rw [hi, commSub_bot']
        exact bot_le
      · exact le_iSup_of_le (⟨i, hi⟩ : ι') le_rfl
  · exact hVind.comp (Subtype.val_injective.comp e.symm.injective)
  · intro k
    exact ⟨rfl, Asc81c.commSub_commSub_eq' hW (hLodd _)⟩
  ·
    intro φ hφ k
    obtain ⟨j, hj⟩ := hperm φ hφ (e.symm k).1
    have hjne : L j ≠ ⊥ := by
      intro h0
      rw [h0] at hj
      exact (e.symm k).2 ((Subgroup.map_eq_bot_iff_of_injective _
        (MulAut.conj φ).injective).1 hj)
    refine ⟨e ⟨j, hjne⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hj
  · intro k k'
    exact htrans _ _ (e.symm k).2 (e.symm k').2
  ·
    rcases hdich Xb hXΩ with ⟨i, hi⟩ | ⟨i, hi, h21, hna⟩
    · have hine : L i ≠ ⊥ := hi ▸ hΩne Xb hXΩ
      left
      refine ⟨e ⟨i, hine⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      exact hi
    · right
      have hine : L i ≠ ⊥ := fun h0 => hΩne Xb hXΩ (le_bot_iff.1 (h0 ▸ hi))
      have hdvd : Nat.card Xb ∣ 21 := h21 ▸ Subgroup.card_dvd_of_le hi
      have h3 : Nat.card Xb = 3 := by
        have hne21 : Nat.card Xb ≠ 21 := by
          intro h0
          have hXL : Xb = L i := Subgroup.eq_of_le_of_card_ge hi (by rw [h0, h21])
          obtain ⟨a, ha, b, hb, hab⟩ := hna
          apply hab
          rw [← hXL] at ha hb
          have := hyp.1.2.2.1
          let _ : CommGroup Xb := IsCyclic.commGroup
          exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Xb) ⟨b, hb⟩)
        have hne1 : Nat.card Xb ≠ 1 := fun h0 =>
          hΩne Xb hXΩ (Subgroup.eq_bot_of_card_eq _ h0)
        have hne7 : Nat.card Xb ≠ 7 := by
          intro h7
          have hgen := Asc81c.le_sSup_inter hsup hind hcomm hdich' i
          have hall : sSup {Y | Y ∈ Ω ∧ Y ≤ L i} ≤ Xb := sSup_le fun Y hY =>
            (Asc81c.eq_of_card_seven h21 hY.2 hi (by rw [hΩcard Y hY.1, h7]) h7).le
          have := Subgroup.card_le_of_le (hgen.trans hall)
          rw [h21, h7] at this
          omega
        have hd : Nat.card Xb ∈ Nat.divisors 21 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
        have h21d : Nat.divisors 21 = {1, 3, 7, 21} := by decide
        rw [h21d] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with hd | hd | hd | hd
        · exact absurd hd hne1
        · exact hd
        · exact absurd hd hne7
        · exact absurd hd hne21
      have hn2 : 2 ^ E3.mQuot V U = 4 := by
        rw [hXcard] at h3
        omega
      have h8 : Nat.card (commSub ⊤ (L i)) = 8 :=
        Asc81c.card_commSub_frob21 hW h21 hna hi h3 (by rw [hcardc, hn2])
      refine ⟨h3, e ⟨i, hine⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]
        exact hi
      · simp only [Equiv.symm_apply_apply]
        exact (Asc81c.closure_conj_eq_of_frob21 h21 hna hi h3).symm
      · simp only [Equiv.symm_apply_apply]
        exact h21
      · simp only [Equiv.symm_apply_apply]
        exact hna
      · intro j
        obtain ⟨φ, -, hφ⟩ := htrans i (e.symm j).1 hine (e.symm j).2
        show Nat.card (commSub ⊤ (L (e.symm j).1)) = 8
        rw [← hφ, Asc81c.commSub_map_conj,
          Subgroup.card_map_of_injective (φ : MulAut (IntMod V hV)).injective, h8]

end Main


end E6

end CFSG.Quasithin
