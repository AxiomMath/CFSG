module

public import CFSG.LocalAnalysis.StandardType.StarFour.ItemsDatum
public import CFSG.LocalAnalysis.StandardType.StarFour.BlockDatumNesting
public import CFSG.LocalAnalysis.StandardType.StarFour.BlockNestingEq

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL CFSG.Open CFSG.StandardType

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

private lemma blockIota_coord {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (i : Fin fr.r) (a : Fin (fr.m i)) (t : fr.E i) :
    fr.blockIota i a t = fr.Φ.symm (Pi.single i (Pi.single a t)) := by
  rw [SemiFrame.blockIota, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.single_apply, LinearMap.single_apply]
  rfl

private lemma nesting_index_eq {P P' : Type} [CommGroup P] [CommGroup P']
    {ρ : P →* (V ≃ₗ[F] V)} {ρ' : P' →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (fr' : SemiFrame F ρ') (i : Fin fr.r) (hm : 2 ≤ fr.m i)
    (i' i₁ : Fin fr'.r)
    (h3 : ∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i₁ →
      fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0)
    (hle : fr.slOnBlock i ≤ fr'.slOnBlock i') : i₁ = i' := by
  by_contra hne
  have hne' : i' ≠ i₁ := fun h => hne h.symm
  set g : SpecialLinearGroup F V :=
    datumElt (fr.blockIota i (fr.idx0 i hm)) (fr.blockPi i (fr.idx1 i hm))
      (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm) t) 1 with hgdef
  have hg_root : g ∈ fr.blockRoot i hm := by
    rw [SemiFrame.blockRoot]
    exact Subgroup.subset_closure (Set.mem_range_self 1)
  have hg_sl : g ∈ fr'.slOnBlock i' :=
    hle ((SemiFrame.blockRoot_le_blockJ0 fr i hm).trans
      (SemiFrame.blockJ0_le_slOnBlock fr i hm) hg_root)
  obtain ⟨B, hB⟩ := hg_sl
  set v : V := fr.blockIota i (fr.idx1 i hm) 1 with hvdef
  have hv0 : fr'.Φ v i' = 0 := by
    rw [hvdef, blockIota_coord]
    exact h3 (Pi.single (fr.idx1 i hm) (1 : fr.E i)) i' hne'
  have hgv : g v = v + fr.blockIota i (fr.idx0 i hm) 1 := by
    change (datumElt (fr.blockIota i (fr.idx0 i hm)) (fr.blockPi i (fr.idx1 i hm))
      (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm) t) 1 :
        V ≃ₗ[F] V) v = v + fr.blockIota i (fr.idx0 i hm) 1
    rw [datumElt_apply, hvdef, SemiFrame.blockPi_blockIota_self, one_mul]
  have hgv0 : fr'.Φ (g v) i' = 0 := by
    rw [hgv, map_add, Pi.add_apply, hv0, blockIota_coord]
    rw [h3 (Pi.single (fr.idx0 i hm) (1 : fr.E i)) i' hne', add_zero]
  have heq : fr'.Φ (g v) = fr'.Φ v := by
    funext j
    by_cases hj : j = i'
    · subst hj
      rw [hgv0, hv0]
    · rw [hB v, Function.update_of_ne hj]
  have hgv_eq : g v = v := fr'.Φ.injective heq
  have hzero : fr.blockIota i (fr.idx0 i hm) 1 = 0 := by
    have h : v + fr.blockIota i (fr.idx0 i hm) 1 = v + 0 := by
      rw [add_zero, ← hgv]
      exact hgv_eq
    exact add_left_cancel h
  exact one_ne_zero (fr.blockIota_injective i (fr.idx0 i hm) (by rw [hzero, map_zero]))

theorem items_of_frames {P P' : Type} [CommGroup P] [CommGroup P']
    (η : P →* SpecialLinearGroup F V) (η' : P' →* SpecialLinearGroup F V) {g : P} {g' : P'}
    (hg' : ∀ x : P', x ∈ Subgroup.zpowers g') (hgg : η' g' = η g)
    (fr : SemiFrame F (groupRep η)) (fr' : SemiFrame F (groupRep η')) (i : Fin fr.r)
    (hm : 3 ≤ fr.m i) (hc : 2 ≤ Module.finrank F (fr.E i)) (i' : Fin fr'.r)
    (hle : fr.slOnBlock i ≤ fr'.slOnBlock i') (hne : fr'.slOnBlock i' ≠ fr.slOnBlock i)
    (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ) :
    GGRootInnerAt ((fr'.slOnBlock i').map ψ) ((fr.blockRoot i (by omega)).map ψ) ∧
      GGRootNoCentralAt ((fr'.slOnBlock i').map ψ) ((fr.blockRoot i (by omega)).map ψ) := by
  classical
  have hm2 : 2 ≤ fr.m i := by omega
  have hpos : 0 < fr.m i := by omega
  obtain ⟨i₁, ε, _hmi₁, h3, h1, h4, h2⟩ :=
    exists_nesting η η' hg' hgg fr fr' i hpos
  have hidx : i₁ = i' := nesting_index_eq fr fr' i hm2 i' i₁ h3 hle
  subst i₁
  letI : Algebra (fr'.E i') (fr.E i) := ε.toRingHom.toAlgebra
  obtain ⟨ι, ι₁, π, π₁, h1k, h2k, h3k, h4k, heq1, _heq2⟩ :=
    exists_blockDatum η η' hg' hgg fr fr' i hm2 i' ε h3 h1 h4 h2
  haveI : CharP (fr'.E i') 2 :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap F (fr'.E i'))) 2
  let pφ : SpecialLinearGroup (fr'.E i') (Fin (fr'.m i') → fr'.E i') →*
      SpecialLinearGroup F V :=
    (fr'.slOnBlock i').subtype.comp (SemiFrame.blockMulEquiv fr' i').toMonoidHom
  let ψ' : SpecialLinearGroup (fr'.E i') (Fin (fr'.m i') → fr'.E i') →* X := ψ.comp pφ
  have hpφ_inj : Function.Injective pφ := fun B₁ B₂ h =>
    SemiFrame.blockSpecialLinear_injective fr' i' h
  have hψ' : Function.Injective ψ' := fun a b h => hpφ_inj (hψ h)
  have hpφrange : pφ.range = fr'.slOnBlock i' := by
    apply le_antisymm
    · rintro y ⟨B, rfl⟩
      exact ⟨B, fr'.blockSpecialLinear_apply i' B⟩
    · intro y hy
      refine ⟨(SemiFrame.blockMulEquiv fr' i').symm ⟨y, hy⟩, ?_⟩
      show (fr'.slOnBlock i').subtype ((SemiFrame.blockMulEquiv fr' i')
        ((SemiFrame.blockMulEquiv fr' i').symm ⟨y, hy⟩)) = y
      rw [MulEquiv.apply_symm_apply]
      rfl
  have hψ'range : ψ'.range = (fr'.slOnBlock i').map ψ := by
    rw [show ψ' = ψ.comp pφ from rfl, MonoidHom.range_comp ψ pφ, hpφrange]
  have hset : pφ '' Set.range (datumElt ι π h1k) =
      Set.range (datumElt (fr.blockIota i (fr.idx0 i hm2)) (fr.blockPi i (fr.idx1 i hm2))
        (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm2) t)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (heq1 t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨datumElt ι π h1k t, ⟨t, rfl⟩, heq1 t⟩
  have hstep : (datumRoot ι π h1k).map pφ = fr.blockRoot i hm2 := by
    rw [show fr.blockRoot i hm2 = Subgroup.closure (Set.range (datumElt
        (fr.blockIota i (fr.idx0 i hm2)) (fr.blockPi i (fr.idx1 i hm2))
        (fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm2) t))) from rfl]
    rw [show datumRoot ι π h1k = Subgroup.closure (Set.range (datumElt ι π h1k)) from rfl,
      MonoidHom.map_closure pφ (Set.range (datumElt ι π h1k)), hset]
  have hroot : (datumRoot ι π h1k).map ψ' = (fr.blockRoot i hm2).map ψ := by
    rw [show ψ' = ψ.comp pφ from rfl,
      ← Subgroup.map_map (datumRoot ι π h1k) ψ pφ, hstep]
  have hnum : Module.finrank (fr'.E i') (fr.E i) * fr.m i ≤ fr'.m i' :=
    blockDatum_numerics η η' fr fr' i i' ε h3 h4
  have hV : 3 * Module.finrank (fr'.E i') (fr.E i) ≤
      Module.finrank (fr'.E i') (Fin (fr'.m i') → fr'.E i') := by
    rw [Module.finrank_fin_fun]
    calc 3 * Module.finrank (fr'.E i') (fr.E i)
        = Module.finrank (fr'.E i') (fr.E i) * 3 := by rw [Nat.mul_comm]
      _ ≤ Module.finrank (fr'.E i') (fr.E i) * fr.m i := Nat.mul_le_mul_left _ hm
      _ ≤ fr'.m i' := hnum
  have hstar : 2 ≤ Module.finrank (fr'.E i') (fr.E i) ∨
      (Module.finrank (fr'.E i') (fr.E i) = 1 ∧ 4 ≤ Nat.card (fr'.E i') ∧
        4 ≤ Module.finrank (fr'.E i') (Fin (fr'.m i') → fr'.E i')) := by
    by_cases hd : 2 ≤ Module.finrank (fr'.E i') (fr.E i)
    · exact Or.inl hd
    · right
      have hdpos : 0 < Module.finrank (fr'.E i') (fr.E i) := Module.finrank_pos
      have hd1 : Module.finrank (fr'.E i') (fr.E i) = 1 := by omega
      have hbij : Function.Bijective ε := by
        refine ⟨?_, ?_⟩
        · exact RingHom.injective ε.toRingHom
        · intro y
          obtain ⟨c, hc'⟩ := exists_smul_eq_of_finrank_eq_one (K := fr'.E i') hd1
            (x := (1 : fr.E i)) one_ne_zero y
          exact ⟨c, by rw [← hc', Algebra.smul_def, mul_one]; rfl⟩
      have hcardF : 4 ≤ Nat.card (fr.E i) := by
        have hF2 : 2 ≤ Nat.card F := by
          have h1 := (Finite.one_lt_card : 1 < Nat.card F)
          omega
        have hpow : Nat.card F ^ 2 ≤ Nat.card F ^ Module.finrank F (fr.E i) :=
          Nat.pow_le_pow_right (by omega) hc
        have h4 : 4 ≤ Nat.card F ^ 2 := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hF2 2
        rw [Module.natCard_eq_pow_finrank (K := F)]
        exact h4.trans hpow
      have hcardE' : 4 ≤ Nat.card (fr'.E i') := by
        rw [Nat.card_congr (Equiv.ofBijective ε hbij)]
        exact hcardF
      have hle_m : fr.m i ≤ fr'.m i' := by
        have h := hnum
        rw [hd1, one_mul] at h
        exact h
      have hne_m : fr'.m i' ≠ fr.m i := fun hmm =>
        hne (slOnBlock_eq_of_nesting η η' fr fr' i i' ε hbij hle hmm).symm
      have h4m : 4 ≤ fr'.m i' := by omega
      exact ⟨hd1, hcardE', by rw [Module.finrank_fin_fun]; exact h4m⟩
  have hmain := items_of_datum ι ι₁ π π₁ h1k h2k h3k h4k hV hstar ψ' hψ'
  have hinner : GGRootInnerAt ψ'.range ((datumRoot ι π h1k).map ψ') := hmain.2.1
  have hno : GGRootNoCentralAt ψ'.range ((datumRoot ι π h1k).map ψ') := hmain.2.2.1
  rw [hψ'range, hroot] at hinner hno
  exact ⟨hinner, hno⟩

end CFSG.StandardType.StarFour
