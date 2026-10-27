module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinIso
import CFSG.LocalAnalysis.StandardType.SpSimpleOrder
import CFSG.Sporadic.Co2Smith.Timmesfeld

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LieType.SpinGeom CFSG.LieType.Sp6Spin CFSG.LieType.D4Small
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open QuadraticMap
open scoped Matrix

private lemma sixteenC8SpinIrr_zmod_two_add_self (x : ZMod 2) : x + x = 0 :=
  (by decide : ∀ x : ZMod 2, x + x = 0) x

private lemma sixteenC8SpinIrr_zmod_two_eq_one {x : ZMod 2} (hx : x ≠ 0) : x = 1 :=
  (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) x hx

private lemma sixteenC8SpinIrr_zmod_two_eq_zero_or_eq_one (x : ZMod 2) : x = 0 ∨ x = 1 :=
  (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x

private lemma sixteenC8SpinIrr_zmod_two_eq_one_of_one_eq_add (c : ZMod 2)
    (h : (1 : ZMod 2) = 1 + 1 + c) : c = 1 :=
  (by decide : ∀ c : ZMod 2, (1 : ZMod 2) = 1 + 1 + c → c = 1) c h

private lemma sixteenC8SpinIrr_mul_self (w : SpinW) : w * w = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  funext i
  exact sixteenC8SpinIrr_zmod_two_add_self _

private lemma sixteenC8SpinIrr_inv_eq_self (w : SpinW) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (sixteenC8SpinIrr_mul_self w)

private lemma sixteenC8SpinIrr_polarQ_eq_polar (x y : SpinW) :
    polarQ spinQ x y = polar (coordinateQuadPlus 4 (ZMod 2)) x.toAdd y.toAdd :=
  rfl

private lemma sixteenC8SpinIrr_quad_mul (x y : SpinW) :
    spinQ (x * y) = spinQ x + spinQ y + polarQ spinQ x y := by
  simp only [polarQ]
  abel

private lemma sixteenC8SpinIrr_polarQ_add_left (x y z : SpinW) :
    polarQ spinQ (x * y) z = polarQ spinQ x z + polarQ spinQ y z := by
  rw [sixteenC8SpinIrr_polarQ_eq_polar, sixteenC8SpinIrr_polarQ_eq_polar,
    sixteenC8SpinIrr_polarQ_eq_polar, toAdd_mul]
  exact (polar_add_left_iff (f := ⇑(coordinateQuadPlus 4 (ZMod 2)))).mpr
    (QuadraticMap.map_add_add_add_map (coordinateQuadPlus 4 (ZMod 2)) x.toAdd y.toAdd z.toAdd)

private lemma sixteenC8SpinIrr_polarQ_comm (x y : SpinW) :
    polarQ spinQ x y = polarQ spinQ y x := by
  rw [sixteenC8SpinIrr_polarQ_eq_polar, sixteenC8SpinIrr_polarQ_eq_polar, polar_comm]

private lemma sixteenC8SpinIrr_polarQ_add_right (x y z : SpinW) :
    polarQ spinQ x (y * z) = polarQ spinQ x y + polarQ spinQ x z := by
  rw [sixteenC8SpinIrr_polarQ_comm x (y * z), sixteenC8SpinIrr_polarQ_add_left y z x,
    sixteenC8SpinIrr_polarQ_comm y x, sixteenC8SpinIrr_polarQ_comm z x]

private lemma sixteenC8SpinIrr_polarQ_eq_one (J : Subgroup SpinW)
    (hQ : ∀ w ∈ J, w ≠ 1 → spinQ w = 1)
    (p q : SpinW) (hp : p ∈ J) (hq : q ∈ J) (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hpq : p ≠ q) :
    polarQ spinQ p q = 1 := by
  have hpqJ : p * q ∈ J := J.mul_mem hp hq
  have hpq_ne1 : p * q ≠ 1 := by
    intro h
    have hq_eq : q = p⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [sixteenC8SpinIrr_inv_eq_self p] at hq_eq
    exact hpq hq_eq.symm
  have hpqQ : spinQ (p * q) = 1 := hQ (p * q) hpqJ hpq_ne1
  have hpQ : spinQ p = 1 := hQ p hp hp1
  have hqQ : spinQ q = 1 := hQ q hq hq1
  have hquad := sixteenC8SpinIrr_quad_mul p q
  rw [hpqQ, hpQ, hqQ] at hquad
  exact sixteenC8SpinIrr_zmod_two_eq_one_of_one_eq_add _ hquad

private lemma sixteenC8SpinIrr_card_le_four (J : Subgroup SpinW) (hJne : J ≠ ⊥)
    (hQ : ∀ w ∈ J, w ≠ 1 → spinQ w = 1) : Nat.card ↥J ≤ 4 := by
  classical
  obtain ⟨u₀, hu₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJne
  let a : SpinW := u₀
  have haJ : a ∈ J := u₀.2
  have hane : a ≠ 1 := fun h => hu₀ne (Subtype.ext h)
  by_cases htwo : ∃ v ∈ J, v ≠ 1 ∧ v ≠ a
  · obtain ⟨b, hbJ, hbne, hbne'⟩ := htwo
    have hsub : (J : Set SpinW) ⊆ (({1, a, b, a * b} : Finset SpinW) : Set SpinW) := by
      intro z hz
      by_cases hz1 : z = 1
      · simp [hz1]
      by_cases hza : z = a
      · simp [hza]
      by_cases hzb : z = b
      · simp [hzb]
      by_cases hzab : z = a * b
      · simp [hzab]
      · exfalso
        have hab_ne1 : a * b ≠ 1 := by
          intro h
          have hb_eq : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
          rw [sixteenC8SpinIrr_inv_eq_self a] at hb_eq
          exact hbne' hb_eq
        have hzab1 : polarQ spinQ z (a * b) = 1 :=
          sixteenC8SpinIrr_polarQ_eq_one J hQ z (a * b) hz (J.mul_mem haJ hbJ) hz1
            hab_ne1 hzab
        have hza1 : polarQ spinQ z a = 1 :=
          sixteenC8SpinIrr_polarQ_eq_one J hQ z a hz haJ hz1 hane hza
        have hzb1 : polarQ spinQ z b = 1 :=
          sixteenC8SpinIrr_polarQ_eq_one J hQ z b hz hbJ hz1 hbne hzb
        have hadd : polarQ spinQ z (a * b) = polarQ spinQ z a + polarQ spinQ z b :=
          sixteenC8SpinIrr_polarQ_add_right z a b
        rw [hadd, hza1, hzb1] at hzab1
        exact absurd hzab1 (by decide)
    have hle : Nat.card ↥J ≤ ({1, a, b, a * b} : Finset SpinW).card := by
      calc Nat.card ↥J = (J : Set SpinW).ncard := Nat.card_coe_set_eq _
        _ ≤ (({1, a, b, a * b} : Finset SpinW) : Set SpinW).ncard :=
            Set.ncard_le_ncard hsub (by simp)
        _ = ({1, a, b, a * b} : Finset SpinW).card := Set.ncard_coe_finset _
    exact hle.trans Finset.card_le_four
  · have hsub : (J : Set SpinW) ⊆ (({1, a, a, a * a} : Finset SpinW) : Set SpinW) := by
      intro z hz
      by_cases hz1 : z = 1
      · simp [hz1]
      · have hza : z = a := by
          by_contra hzne
          exact htwo ⟨z, hz, hz1, hzne⟩
        simp [hza]
    have hle : Nat.card ↥J ≤ ({1, a, a, a * a} : Finset SpinW).card := by
      calc Nat.card ↥J = (J : Set SpinW).ncard := Nat.card_coe_set_eq _
        _ ≤ (({1, a, a, a * a} : Finset SpinW) : Set SpinW).ncard :=
            Set.ncard_le_ncard hsub (by simp)
        _ = ({1, a, a, a * a} : Finset SpinW).card := Set.ncard_coe_finset _
    exact hle.trans Finset.card_le_four

private lemma sixteenC8SpinIrr_frameE_ne_zero (k : Fin 4) : frameE (ZMod 2) k ≠ 0 := by
  intro h
  have h1 : coordX (ZMod 2) (frameE (ZMod 2) k) k = 1 := by
    rw [coordX_frameE]
    exact if_pos rfl
  rw [h, coordX_zero] at h1
  exact zero_ne_one h1

private lemma sixteenC8SpinIrr_frameF_ne_zero (k : Fin 4) : frameF (ZMod 2) k ≠ 0 := by
  intro h
  have h1 : coordY (ZMod 2) (frameF (ZMod 2) k) k = 1 := by
    rw [coordY_frameF]
    exact if_pos rfl
  rw [h, coordY_zero] at h1
  exact zero_ne_one h1

private noncomputable def sixteenC8SpinIrr_permHom (J : Subgroup SpinW)
    (hJ : StableUnder spinH J) : ↥spinH →* Equiv.Perm ↥J where
  toFun h :=
    { toFun := fun x => ⟨h.1 x.1, hJ h.1 h.2 x.1 x.2⟩
      invFun := fun x => ⟨h.1⁻¹ x.1, hJ h.1⁻¹ (inv_mem h.2) x.1 x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self SpinW h.1 x.1)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self SpinW h.1 x.1) }
  map_one' := Equiv.ext fun x => Subtype.ext (MulAut.one_apply SpinW x.1)
  map_mul' := fun h k => Equiv.ext fun x => Subtype.ext (MulAut.mul_apply SpinW h.1 k.1 x.1)

theorem spinH_irr : IsIrrOn spinH (⊤ : Subgroup SpinW) ⊥ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bot_lt_top
  · intro x _ u _
    exact Subgroup.mem_top u
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu]
    exact x.map_one
  · intro J hJ _ _
    by_cases hJbot : J = ⊥
    · exact Or.inl hJbot
    · right
      obtain ⟨u₀, hu₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJbot
      let a : SpinW := u₀
      have haJ : a ∈ J := u₀.2
      have hane : a ≠ 1 := fun h => hu₀ne (Subtype.ext h)
      by_cases hsing : ∃ w ∈ J, w ≠ 1 ∧ spinQ w = 0
      ·
        obtain ⟨w, hwJ, hwne, hwQ⟩ := hsing
        have hw_ne_zero : Multiplicative.toAdd w ≠ 0 := by
          intro h
          exact hwne (Multiplicative.toAdd.injective (by simpa using h))
        let E : SpinW := Multiplicative.ofAdd (frameE (ZMod 2) 0)
        have hE_mem : E ∈ J := by
          obtain ⟨h, hh, hact⟩ := spinSeven_transitive (ZMod 2) (Multiplicative.toAdd w)
            hw_ne_zero (by simpa [spinQ] using hwQ)
          have hhin : spinHom h ∈ spinH := (mem_spinH_iff (spinHom h)).2 ⟨h, hh, rfl⟩
          have hmap : spinHom h E = w := by
            rw [spinHom_apply, toAdd_ofAdd, hact, ofAdd_toAdd]
          have : (spinHom h)⁻¹ w ∈ J := hJ (spinHom h)⁻¹ (inv_mem hhin) w hwJ
          rwa [← hmap, MulAut.inv_apply_self] at this
        have hsing_mem : ∀ b : Fin (2 * 4) → ZMod 2, b ≠ 0 →
            coordinateQuadPlus 4 (ZMod 2) b = 0 → Multiplicative.ofAdd b ∈ J := by
          intro b hb hbQ
          obtain ⟨h, hh, hact⟩ := spinSeven_transitive (ZMod 2) b hb hbQ
          have hhin : spinHom h ∈ spinH := (mem_spinH_iff (spinHom h)).2 ⟨h, hh, rfl⟩
          have hmap : spinHom h E = Multiplicative.ofAdd b := by
            rw [spinHom_apply, toAdd_ofAdd, hact]
          rw [← hmap]
          exact hJ (spinHom h) hhin E hE_mem
        have hframeE_mem : ∀ k : Fin 4, Multiplicative.ofAdd (frameE (ZMod 2) k) ∈ J :=
          fun k => hsing_mem _ (sixteenC8SpinIrr_frameE_ne_zero k) (quad_frameE k)
        have hframeF_mem : ∀ k : Fin 4, Multiplicative.ofAdd (frameF (ZMod 2) k) ∈ J :=
          fun k => hsing_mem _ (sixteenC8SpinIrr_frameF_ne_zero k) (quad_frameF k)
        let K : Submodule (ZMod 2) (Fin (2 * 4) → ZMod 2) :=
          { carrier := {v | Multiplicative.ofAdd v ∈ J}
            zero_mem' := by
              change Multiplicative.ofAdd (0 : Fin (2 * 4) → ZMod 2) ∈ J
              exact J.one_mem
            add_mem' := fun {x y} hx hy => by
              simp only [Set.mem_setOf_eq, ofAdd_add]
              exact J.mul_mem hx hy
            smul_mem' := fun c {v} hv => by
              rcases sixteenC8SpinIrr_zmod_two_eq_zero_or_eq_one c with rfl | rfl
              · rw [zero_smul]
                change Multiplicative.ofAdd (0 : Fin (2 * 4) → ZMod 2) ∈ J
                exact J.one_mem
              · simpa using hv }
        have hK : K = ⊤ := by
          apply le_antisymm le_top
          intro v _
          rw [vec_eq_sum v]
          exact Submodule.sum_mem K fun k _ =>
            K.add_mem (K.smul_mem _ (hframeE_mem k)) (K.smul_mem _ (hframeF_mem k))
        have hJtop : J = ⊤ := by
          apply le_antisymm le_top
          intro x _
          have hxK : Multiplicative.toAdd x ∈ K := by simp [hK]
          have hxJ : Multiplicative.ofAdd (Multiplicative.toAdd x) ∈ J := hxK
          simpa using hxJ
        exact hJtop
      ·
        have hQ1 : ∀ w ∈ J, w ≠ 1 → spinQ w = 1 := by
          intro w hw hw1
          exact sixteenC8SpinIrr_zmod_two_eq_one (fun h0 => hsing ⟨w, hw, hw1, h0⟩)
        obtain ⟨e⟩ := nonempty_spinSeven_mulEquiv (ZMod 2)
        let eH : ↥spinH ≃* ↥(StatedSp 3 (ZMod 2)) := spinHEquiv.symm.trans e
        haveI : IsSimpleGroup ↥(StatedSp 3 (ZMod 2)) :=
          CFSG.StandardType.SpFixed.isSimpleGroup_statedSp (F := ZMod 2) (m := 3) (by norm_num)
        have hsimple : IsSimpleGroup ↥spinH := eH.isSimpleGroup
        have hcard : Nat.card ↥spinH = 1451520 := by
          rw [Nat.card_congr eH.toEquiv]
          exact CFSG.Sporadic.Co2Smith.natCard_sp62
        have hcard4 : Nat.card ↥J ≤ 4 := sixteenC8SpinIrr_card_le_four J hJbot hQ1
        let ρ : ↥spinH →* Equiv.Perm ↥J := sixteenC8SpinIrr_permHom J hJ
        have hperm : Nat.card (Equiv.Perm ↥J) ≤ 24 := by
          rw [Nat.card_perm]
          calc Nat.factorial (Nat.card ↥J) ≤ Nat.factorial 4 := Nat.factorial_le hcard4
            _ = 24 := by decide
        have hker_ne_bot : ρ.ker ≠ ⊥ := by
          intro hbot
          have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hbot
          have hle : Nat.card ↥spinH ≤ Nat.card (Equiv.Perm ↥J) :=
            Nat.card_le_card_of_injective ρ hinj
          rw [hcard] at hle
          omega
        have hker_top : ρ.ker = ⊤ := by
          rcases hsimple.eq_bot_or_eq_top_of_normal ρ.ker with h | h
          · exact absurd h hker_ne_bot
          · exact h
        have hfix_a : ∀ h : ↥spinH, (h : MulAut SpinW) a = a := by
          intro h
          have hhker : h ∈ ρ.ker := by rw [hker_top]; exact Subgroup.mem_top h
          rw [MonoidHom.mem_ker] at hhker
          have h2 := congrArg (fun f : Equiv.Perm ↥J => (f ⟨a, haJ⟩ : SpinW)) hhker
          simpa [ρ, sixteenC8SpinIrr_permHom] using h2
        have hfixall : ∀ g ∈ spinSeven (ZMod 2),
            ((g : GL (Fin (2 * 4)) (ZMod 2)) :
              Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ Multiplicative.toAdd a =
              Multiplicative.toAdd a := by
          intro g hg
          have hmem : spinHom g ∈ spinH := (mem_spinH_iff (spinHom g)).2 ⟨g, hg, rfl⟩
          have hfix := hfix_a ⟨spinHom g, hmem⟩
          have h2 := congrArg Multiplicative.toAdd hfix
          rw [spinHom_apply] at h2
          simpa using h2
        have hzero : Multiplicative.toAdd a = 0 :=
          CFSG.LieType.Sp6Spin.eq_zero_of_forall_spinSeven (K := ZMod 2) hfixall
        exact absurd (Multiplicative.toAdd.injective (by simpa using hzero)) hane

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
