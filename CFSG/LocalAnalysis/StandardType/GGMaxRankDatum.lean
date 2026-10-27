module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankSide
public import CFSG.LocalAnalysis.StandardType.GGMaxRankLinear
public import CFSG.LocalAnalysis.StandardType.GGMaxRankPairing
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer
public import CFSG.LocalAnalysis.StandardType.GGResMaxRankDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggMaxRankDatum_mk {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (eJ : (CoxeterMatrix.A 8).Group ≃* ↥(ggAutomizer J Bs))
    (hL : GGMaxRankSideChain p Bs L J eJ) (hK : GGMaxRankSideChain p Bs K J eJ)
    (hcardL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p) :
    GGResMaxRankDatum p Bs L J K ggMaxRankSelAny := by
  obtain ⟨hp3, V, i1, i2, ι, φ, h, α, hlin, hrefl, hchain, hpair, hmarks, hdim9, _hdim7,
    hA, fL, hfL⟩ := hL
  obtain ⟨_hp3', V', i1', i2', ι', φ', h', α', hlin', hrefl', hchain', hpair', _hmarks',
    _hdim9', _hdim7', hA', fK, hfK⟩ := hK
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  let τ : V' ≃ₗ[ZMod p] V := l6tr_iso (p := p) ι' ι
  let H : Fin 8 ⊕ Fin 1 → V := fun o => τ (h' o)
  let A : Fin 8 ⊕ Fin 1 → Module.Dual (ZMod p) V := fun o => (α' o).comp τ.symm.toLinearMap
  have hA_H : ∀ o o', A o (H o') = α' o (h' o') := by
    intro o o'
    show α' o (τ.symm (τ (h' o'))) = α' o (h' o')
    rw [LinearEquiv.symm_apply_apply]
  have hlinT : ∀ o w, ggLin (p := p) ι (φ' o) w = w - A o w • H o := by
    intro o w
    have hconj := l6tr_lin_conj_apply (p := p) (ι := ι') (ι' := ι) (φ' o) (τ.symm w)
    have hτ : l6tr_iso (p := p) ι' ι (τ.symm w) = w := LinearEquiv.apply_symm_apply τ w
    rw [hτ] at hconj
    rw [hconj, hlin' o (τ.symm w)]
    simp only [map_sub, map_smul, hτ]
    rfl
  let r : Fin 8 → (V ≃ₗ[ZMod p] V) := fun i =>
    ggLin (p := p) ι ((eJ ((CoxeterMatrix.A 8).simple i) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs)
  have hr : ∀ i v, r i v = v - α (Sum.inl i) v • h (Sum.inl i) := by
    intro i v
    dsimp only [r]
    rw [← hchain i]
    exact hlin (Sum.inl i) v
  have hr' : ∀ i v, r i v = v - A (Sum.inl i) v • H (Sum.inl i) := by
    intro i v
    dsimp only [r]
    rw [← hchain' i]
    exact hlinT (Sum.inl i) v
  have hp : ∀ i j, α (Sum.inl i) (h (Sum.inl j)) = ((CartanMatrix.A 8 i j : ℤ) : ZMod p) := by
    intro i j
    rw [hpair (Sum.inl i) (Sum.inl j)]
    exact ggMaxRankPairing_chain p 0 0 false i j
  have hp' : ∀ i j, A (Sum.inl i) (H (Sum.inl j)) = ((CartanMatrix.A 8 i j : ℤ) : ZMod p) := by
    intro i j
    rw [hA_H (Sum.inl i) (Sum.inl j), hpair' (Sum.inl i) (Sum.inl j)]
    exact ggMaxRankPairing_chain p 0 0 false i j
  obtain ⟨c, hc, hcH, hcA⟩ := ggMaxRank_chain_gauge (p := p) hp2 r (fun i => h (Sum.inl i))
    (fun i => H (Sum.inl i)) (fun i => α (Sum.inl i)) (fun i => A (Sum.inl i)) hr hr' hp hp'
  let ha : V := c⁻¹ • H (Sum.inr 0)
  let αa : Module.Dual (ZMod p) V := c • A (Sum.inr 0)
  have hlin_a : ∀ w, ggLin (p := p) ι (φ' (Sum.inr 0)) w = w - αa w • ha := by
    intro w
    have h1 : A (Sum.inr 0) w • H (Sum.inr 0) = αa w • ha := by
      simp only [αa, ha, LinearMap.smul_apply, smul_eq_mul]
      rw [smul_smul]
      congr 1
      rw [mul_comm c (A (Sum.inr 0) w), mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [hlinT (Sum.inr 0) w, h1]
  have hh : ∀ j, h (Sum.inl j) = c⁻¹ • H (Sum.inl j) := by
    intro j
    rw [hcH j, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hrow_a : ∀ j, αa (h (Sum.inl j)) =
      ggMaxRankPairing p 0 0 false (Sum.inr 0) (Sum.inl j) := by
    intro j
    calc αa (h (Sum.inl j))
        = c * A (Sum.inr 0) (h (Sum.inl j)) := by
            simp [αa, LinearMap.smul_apply, smul_eq_mul]
      _ = c * A (Sum.inr 0) (c⁻¹ • H (Sum.inl j)) := by rw [hh j]
      _ = c * (c⁻¹ * A (Sum.inr 0) (H (Sum.inl j))) := by rw [map_smul, smul_eq_mul]
      _ = A (Sum.inr 0) (H (Sum.inl j)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      _ = α' (Sum.inr 0) (h' (Sum.inl j)) := hA_H (Sum.inr 0) (Sum.inl j)
      _ = ggMaxRankPairing p 0 0 false (Sum.inr 0) (Sum.inl j) := hpair' (Sum.inr 0) (Sum.inl j)
  have hcol_a : ∀ j, α (Sum.inl j) ha =
      ggMaxRankPairing p 0 0 false (Sum.inl j) (Sum.inr 0) := by
    intro j
    have hαj : α (Sum.inl j) = c • A (Sum.inl j) := by
      rw [hcA j, smul_smul, mul_inv_cancel₀ hc, one_smul]
    calc α (Sum.inl j) ha
        = α (Sum.inl j) (c⁻¹ • H (Sum.inr 0)) := rfl
      _ = c⁻¹ * α (Sum.inl j) (H (Sum.inr 0)) := by rw [map_smul, smul_eq_mul]
      _ = c⁻¹ * (c * A (Sum.inl j) (H (Sum.inr 0))) := by
            rw [hαj, LinearMap.smul_apply, smul_eq_mul]
      _ = A (Sum.inl j) (H (Sum.inr 0)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      _ = α' (Sum.inl j) (h' (Sum.inr 0)) := hA_H (Sum.inl j) (Sum.inr 0)
      _ = ggMaxRankPairing p 0 0 false (Sum.inl j) (Sum.inr 0) := hpair' (Sum.inl j) (Sum.inr 0)
  have hself_a : αa ha = ggMaxRankPairing p 0 0 false (Sum.inr 0) (Sum.inr 0) := by
    have h1 : αa ha = c * (c⁻¹ * A (Sum.inr 0) (H (Sum.inr 0))) := by
      show (c • A (Sum.inr 0)) (c⁻¹ • H (Sum.inr 0)) =
        c * (c⁻¹ * A (Sum.inr 0) (H (Sum.inr 0)))
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, hA_H, hpair']
    rfl
  let Nφ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs := fun o =>
    Sum.elim (fun i : Fin 8 => φ (Sum.inl i))
      (fun k : Fin 2 => if k = 0 then φ (Sum.inr 0) else φ' (Sum.inr 0)) o
  let Nh : Fin 8 ⊕ Fin 2 → V := fun o =>
    Sum.elim (fun i : Fin 8 => h (Sum.inl i))
      (fun k : Fin 2 => if k = 0 then h (Sum.inr 0) else ha) o
  let Nα : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V := fun o =>
    Sum.elim (fun i : Fin 8 => α (Sum.inl i))
      (fun k : Fin 2 => if k = 0 then α (Sum.inr 0) else αa) o
  have hNφ_inl : ∀ i, Nφ (Sum.inl i) = φ (Sum.inl i) := fun i => rfl
  have hNφ_inr0 : Nφ (Sum.inr 0) = φ (Sum.inr 0) := by simp [Nφ]
  have hNφ_inr1 : Nφ (Sum.inr 1) = φ' (Sum.inr 0) := by simp [Nφ]
  have hNh_inl : ∀ i, Nh (Sum.inl i) = h (Sum.inl i) := fun i => rfl
  have hNh_inr0 : Nh (Sum.inr 0) = h (Sum.inr 0) := by simp [Nh]
  have hNh_inr1 : Nh (Sum.inr 1) = ha := by simp [Nh]
  have hNα_inl : ∀ i, Nα (Sum.inl i) = α (Sum.inl i) := fun i => rfl
  have hNα_inr0 : Nα (Sum.inr 0) = α (Sum.inr 0) := by simp [Nα]
  have hNα_inr1 : Nα (Sum.inr 1) = αa := by simp [Nα]
  let u : ZMod p := Nα (Sum.inr 1) (Nh (Sum.inr 0))
  let v : ZMod p := Nα (Sum.inr 0) (Nh (Sum.inr 1))
  have hu : u = αa (h (Sum.inr 0)) := by
    show Nα (Sum.inr 1) (Nh (Sum.inr 0)) = αa (h (Sum.inr 0))
    rw [hNα_inr1, hNh_inr0]
  have hv : v = α (Sum.inr 0) ha := by
    show Nα (Sum.inr 0) (Nh (Sum.inr 1)) = α (Sum.inr 0) ha
    rw [hNα_inr0, hNh_inr1]
  have hcross01 : ggMaxRankPairing p u v false (Sum.inr 0) (Sum.inr 1) = α (Sum.inr 0) ha := by
    rw [(ggMaxRankPairing_cross p u v false).2, hv]
  have hcross10 : ggMaxRankPairing p u v false (Sum.inr 1) (Sum.inr 0) = αa (h (Sum.inr 0)) := by
    rw [(ggMaxRankPairing_cross p u v false).1, hu]
  have hk01 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by intro k; fin_cases k <;> simp
  have hlinN : ∀ o w, ggLin (p := p) ι (Nφ o) w = w - Nα o w • Nh o := by
    intro o w
    rcases o with i | k
    · rw [hNφ_inl, hNα_inl, hNh_inl]
      exact hlin (Sum.inl i) w
    · rcases hk01 k with rfl | rfl
      · rw [hNφ_inr0, hNα_inr0, hNh_inr0]
        exact hlin (Sum.inr 0) w
      · rw [hNφ_inr1, hNα_inr1, hNh_inr1]
        exact hlin_a w
  have hreflN : ∀ o, GGIsReflection p (Nφ o) := by
    intro o
    rcases o with i | k
    · rw [hNφ_inl]
      exact hrefl (Sum.inl i)
    · rcases hk01 k with rfl | rfl
      · rw [hNφ_inr0]
        exact hrefl (Sum.inr 0)
      · rw [hNφ_inr1]
        exact hrefl' (Sum.inr 0)
  have hpairN : ∀ o o', Nα o (Nh o') = ggMaxRankPairing p u v false o o' := by
    intro o o'
    rcases o with i | k
    · rcases o' with j | l
      · rw [hNα_inl, hNh_inl, hpair (Sum.inl i) (Sum.inl j)]
        exact ggMaxRankPairing_chain_left p 0 0 u v false i (Sum.inl j)
      · rcases hk01 l with rfl | rfl
        · rw [hNα_inl, hNh_inr0, hpair (Sum.inl i) (Sum.inr 0)]
          exact ggMaxRankPairing_chain_left p 0 0 u v false i (Sum.inr 0)
        · rw [hNα_inl, hNh_inr1, hcol_a i]
          exact (ggMaxRankPairing_chain_extra p u v i).symm
    · rcases hk01 k with rfl | rfl
      · rcases o' with j | l
        · rw [hNα_inr0, hNh_inl, hpair (Sum.inr 0) (Sum.inl j)]
          exact ggMaxRankPairing_chain_right p 0 0 u v false j (Sum.inr 0)
        · rcases hk01 l with rfl | rfl
          · rw [hNα_inr0, hNh_inr0, hpair (Sum.inr 0) (Sum.inr 0)]
            change ggMaxRankPairing p 0 0 false (Sum.inr 0) (Sum.inr 0) =
              ggMaxRankPairing p u v false (Sum.inr 0) (Sum.inr 0)
            rw [ggMaxRankPairing_extra_self p 0 0 false 0,
              ggMaxRankPairing_extra_self p u v false 0]
          · rw [hNα_inr0, hNh_inr1, hcross01]
      · rcases o' with j | l
        · rw [hNα_inr1, hNh_inl, hrow_a j]
          exact (ggMaxRankPairing_extra_chain p u v j).symm
        · rcases hk01 l with rfl | rfl
          · rw [hNα_inr1, hNh_inr0, hcross10]
          · rw [hNα_inr1, hNh_inr1, hself_a,
              ggMaxRankPairing_extra_self p 0 0 false 0,
              ggMaxRankPairing_extra_self p u v false 1]
  have hmarksN : ∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod p) • Nh (Sum.inl j) = 0 := by
    simpa only [hNh_inl] using hmarks
  have hrange_φ : Set.range φ =
      Set.range (fun j : Fin 8 => φ (Sum.inl j)) ∪ {φ (Sum.inr 0)} := by
    ext x; constructor
    · rintro ⟨o, rfl⟩
      rcases o with i | k
      · exact Or.inl ⟨i, rfl⟩
      · fin_cases k; exact Or.inr rfl
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr 0, rfl⟩
  have hrange_φ' : Set.range φ' =
      Set.range (fun j : Fin 8 => φ' (Sum.inl j)) ∪ {φ' (Sum.inr 0)} := by
    ext x; constructor
    · rintro ⟨o, rfl⟩
      rcases o with i | k
      · exact Or.inl ⟨i, rfl⟩
      · fin_cases k; exact Or.inr rfl
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr 0, rfl⟩
  have hchain'_eq : ∀ j, φ' (Sum.inl j) = Nφ (Sum.inl j) := by
    intro j
    rw [hchain' j, ← hchain j, ← hNφ_inl j]
  have hgenJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : Fin 8 => Nφ (Sum.inl j)) := by
    have hsimple : Subgroup.closure (Set.range ((CoxeterMatrix.A 8).simple)) = ⊤ := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact (CoxeterMatrix.A 8).toCoxeterSystem.subgroup_closure_range_simple
    have hT : Subgroup.closure
        (Set.range fun j : Fin 8 => eJ ((CoxeterMatrix.A 8).simple j)) = ⊤ := by
      have h1 : Subgroup.closure
          (eJ.toMonoidHom '' Set.range ((CoxeterMatrix.A 8).simple)) = ⊤ := by
        rw [← MonoidHom.map_closure, hsimple, Subgroup.map_top_of_surjective _ eJ.surjective]
      rw [← h1]
      congr 1
      rw [← Set.range_comp]
      rfl
    have hmap : Subgroup.map (ggAutomizer J Bs).subtype
        (Subgroup.closure (Set.range fun j : Fin 8 => eJ ((CoxeterMatrix.A 8).simple j)))
        = Subgroup.closure (Set.range fun j : Fin 8 => Nφ (Sum.inl j)) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [← Set.range_comp]
      congr 1
      funext j
      rw [hNφ_inl j, hchain j]
      rfl
    rw [← hmap, hT, Subgroup.map_top, Subgroup.range_subtype]
  have hLgen : ggAutomizer L Bs = Subgroup.closure
      (Set.range (fun j : Fin 8 => Nφ (Sum.inl j)) ∪ {Nφ (Sum.inr 0)}) := by
    rw [hA, hrange_φ]
    simp only [hNφ_inl, hNφ_inr0]
  have hKgen : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : Fin 8 => Nφ (Sum.inl j)) ∪ {Nφ (Sum.inr 1)}) := by
    rw [hA', hrange_φ']
    simp only [hchain'_eq, hNφ_inr1]
  refine ⟨V, i1, i2, ι, Nφ, Nh, Nα, u, v, false, hp3, hdim9 hcardL, hlinN, hreflN, hpairN,
    hmarksN, ⟨eJ, ?_⟩, hgenJ, hLgen, hKgen, ⟨fL, hfL⟩, ⟨fK, hfK⟩, trivial⟩
  intro i
  rw [hNφ_inl i, hchain i]

end CFSG.StandardType

end
