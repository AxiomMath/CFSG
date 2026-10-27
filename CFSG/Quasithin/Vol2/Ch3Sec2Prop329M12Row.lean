module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329M12
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329Rows
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2M12
public import CFSG.Quasithin.Background.SmithB42L2Base

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Prop329.M12Row

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H13.A5.M12 CFSG.Monster.Code CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

@[expose] def conjOn {X : Type*} [Group X] (G L : Subgroup X)
    (hGL : G ≤ Subgroup.normalizer (L : Set X)) : ↥G →* MulAut ↥L where
  toFun g :=
    { toFun := fun l => ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hGL g.2) l).mp l.2⟩
      invFun := fun l => ⟨g⁻¹ * l * g, by
        have h := (Subgroup.mem_normalizer_iff.mp (hGL (G.inv_mem g.2)) l).mp l.2
        simpa using h⟩
      left_inv := fun l => Subtype.ext (by simp [mul_assoc])
      right_inv := fun l => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun l l' => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext l
    simp
  map_mul' g g' := by
    ext l
    simp [mul_assoc]

theorem conjOn_apply {X : Type*} [Group X] {G L : Subgroup X}
    (hGL : G ≤ Subgroup.normalizer (L : Set X)) (g : ↥G) (l : ↥L) :
    ((conjOn G L hGL g l : ↥L) : X) = g * l * g⁻¹ := rfl

end CFSG.Quasithin.H13.Prop329.M12Row

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H13.A5.M12 CFSG.Monster.Code CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
  Prop329.M12Row

theorem row329M12_holds :
    Row329M12 := by
  intro V _ _ G L hHyp h
  have hLG : IsOver L G := ⟨(FFC.b4hyp_data hHyp).1, B42L2.le_normalizer_of_b4Hyp hHyp⟩
  refine ⟨m12_card h, ?_⟩
  obtain ⟨e, he⟩ := m12_std h
  set ρ := rhoC12 m24Pair le_rfl with hρ
  set ρ₀ := rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair with hρ₀
  have hρ₀ρ : ∀ x : ↥(m24Fix dodecadE), ρ₀ x = ρ ⟨x, m24Fix_le_m24Pair x.2⟩ := fun x =>
    MulEquiv.ext fun w => rfl
  have hρ₀inj : Function.Injective ρ₀ := by
    intro x y hxy
    rw [hρ₀ρ, hρ₀ρ] at hxy
    have h1 := rhoC12_m24Pair_injective hxy
    have h2 : (x : Equiv.Perm (Fin 24)) = y :=
      congrArg (fun z : ↥m24Pair => (z : Equiv.Perm (Fin 24))) h1
    exact Subtype.ext h2
  obtain ⟨⟨eM⟩, hcardM⟩ := m24Fix_dodecadE_props
  let eL : ↥L ≃* NativeSporadic.M12 :=
    (L.equivMapOfInjective _ (congrHom_injective e)).trans
      ((MulEquiv.subgroupCongr he).trans ((MonoidHom.ofInjective hρ₀inj).symm.trans eM))
  have hcardL : Nat.card ↥L = 95040 := by
    rw [Nat.card_congr eL.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  by_cases hGL : G = L
  ·
    right
    subst hGL
    refine Prop329.two_le_qhatOf_m12Ten hLG h fun A hAG hA => ?_
    have hsp : NativeSporadic.IsSporadic ↥G .M12 := ⟨eL⟩
    have h8 := GH74.GLS.C3.Layer1.Bk.M12.m12_rank_le_three hsp (A.subgroupOf G) (by
      intro a ha
      refine ⟨Subtype.ext ?_, fun b hb => Subtype.ext ?_⟩
      · have h2 := hA.2 a ha
        rw [sq] at h2
        exact h2
      · exact hA.1 a ha b hb)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv,
      B45Mat.card_eq_two_pow_rk hA] at h8
    by_contra hlt
    push Not at hlt
    have : 2 ^ 4 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  ·
    left
    have hN : (Subgroup.normalizer (L : Set (MulAut V))).map (congrHom e) = ρ.range := by
      rw [← normalizer_rhoC12, ← he]
      exact Subgroup.map_equiv_normalizer_eq L (MulAut.congr e)
    have hcardN : Nat.card ↥(Subgroup.normalizer (L : Set (MulAut V))) = 190080 := by
      rw [← Subgroup.card_map_of_injective (congrHom_injective e), hN,
        ← Nat.card_congr (MonoidHom.ofInjective (f := ρ) rhoC12_m24Pair_injective).toEquiv]
      exact card_m24Pair
    have hcardG : Nat.card ↥G = 190080 := by
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLG.1
      have hle : Nat.card ↥G ≤ 190080 := hcardN ▸ Subgroup.card_le_of_le hLG.2
      rw [hk, hcardL] at hle ⊢
      have hk1 : k ≠ 1 := by
        rintro rfl
        apply hGL
        exact (Subgroup.eq_of_le_of_card_ge hLG.1 (by rw [hk, hcardL, mul_one])).symm
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        exact (Nat.card_pos (α := ↥G)).ne' hk
      have hk2 : k = 2 := by omega
      rw [hk2]
    have hinj : Function.Injective (conjOn G L hLG.2) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hcent : (g : MulAut V) ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : MulAut V)) hg
        simp only [conjOn_apply, MulAut.one_apply, Subgroup.coe_inv] at h1
        calc l * (g : MulAut V) = (g : MulAut V) * l * (g : MulAut V)⁻¹ * g := by rw [h1]
          _ = g * l := by group
      have hcent' : congrHom e g ∈ Subgroup.centralizer
          ((ρ₀.range : Subgroup (MulAut W10)) : Set (MulAut W10)) := by
        rw [← he, Subgroup.mem_centralizer_iff]
        rintro _ ⟨l, hl, rfl⟩
        rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hcent l hl)]
      rw [centralizer_rhoC12, Subgroup.mem_bot] at hcent'
      exact Subtype.ext ((congrHom_injective e) (hcent'.trans (map_one _).symm))
    have hcardAut : Nat.card (MulAut ↥L) = 190080 := by
      rw [Nat.card_congr (MulAut.congr eL).toEquiv]
      exact CFSG.ComponentClassification.M12Cover.card_mulAut
    have hbij : Function.Bijective (conjOn G L hLG.2) :=
      (Function.Injective.bijective_of_nat_card_le hinj (by rw [hcardG, hcardAut]))
    exact ⟨(MulEquiv.ofBijective _ hbij).trans (MulAut.congr eL)⟩

end CFSG.Quasithin.H13
