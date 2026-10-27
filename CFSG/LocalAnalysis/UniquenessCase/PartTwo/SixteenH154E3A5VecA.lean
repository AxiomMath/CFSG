module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveA5
public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.RankTwoAltFive

theorem s16h_d5_P0_normalizer_fix :
    ∀ (v : Fin 5 → ZMod 2) (σ : Equiv.Perm (Fin 5)),
      (∑ i, v i = 0) →
      (∀ p : A5, p ∈ P0 → (fun i => v ((p : Equiv.Perm (Fin 5))⁻¹ i)) = v) →
      (∀ p : A5, p ∈ P0 →
        ∃ q : A5, q ∈ P0 ∧ σ * (p : Equiv.Perm (Fin 5)) * σ⁻¹ = (q : Equiv.Perm (Fin 5))) →
      σ ^ 3 = 1 → Equiv.Perm.sign σ = 1 →
      (fun i => v (σ⁻¹ i)) = v := by
  decide +kernel


theorem s16h_nat_fix_of_mem_normalizer
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {J : Subgroup W}
    {P : Subgroup (MulAut W)} (hL : IsAlt ↥L 5) (hJ : AlternatingNatural L J ⊥ 5)
    (hP : P ≤ L) (hPcard : Nat.card P = 4) {a : W} (haJ : a ∈ J) (ha1 : a ≠ 1)
    (hPa : ∀ p ∈ P, p a = a) {y : MulAut W} (hyL : y ∈ L)
    (hyN : y ∈ normalizer (P : Set (MulAut W))) (hy3 : orderOf y = 3) : y a = a := by
  classical
  haveI : Nontrivial (alternatingGroup (Fin 5)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp)
  obtain ⟨π, hπ⟩ := hJ
  obtain ⟨f, hfs, hfk, hfe⟩ :=
    CFSG.Quasithin.FFC.RealizesVia.secMap (D := FFModel.altDn 5)
      CFSG.Quasithin.FFC.altDn_ker_five hπ
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  have hπinj : Function.Injective π := by
    have hs5 : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup (FFModel.altDn 5).Gam := hs5
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff π).mp hk
    · exfalso
      obtain ⟨eL⟩ := hL
      haveI : Nontrivial ↥L := Equiv.nontrivial (eL : ↥L ≃ alternatingGroup (Fin 5))
      obtain ⟨z, hz⟩ := exists_ne (1 : ↥L)
      obtain ⟨σ, hσ⟩ := hπ.1 z
      have hmem : π σ = 1 := by
        rw [← MonoidHom.mem_ker, hk]
        exact Subgroup.mem_top σ
      exact hz (by rw [← hσ]; exact hmem)
  let π' : ↥(alternatingGroup (Fin 5)) →* MulAut W := L.subtype.comp π
  have hπ'inj : Function.Injective π' := L.subtype_injective.comp hπinj
  let V : Subgroup ↥(alternatingGroup (Fin 5)) := P.comap π'
  have hVmap : V.map π' = P := by
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hp
      obtain ⟨v, hv⟩ := hπ.1 ⟨p, hP hp⟩
      refine ⟨v, ?_, ?_⟩
      · show (π' v : MulAut W) ∈ P
        rw [show (π' v : MulAut W) = p from congrArg Subtype.val hv]
        exact hp
      · show (π' v : MulAut W) = p
        exact congrArg Subtype.val hv
  have hVcard : Nat.card ↥V = 4 := by
    rw [← hPcard, ← hVmap]
    exact (Subgroup.card_map_of_injective hπ'inj).symm
  obtain ⟨ψ, hψ⟩ :=
    exists_equiv_map_P0 (H := alternatingGroup (Fin 5)) (MulEquiv.refl A5) hVcard
  obtain ⟨τ, hτ⟩ := CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl) ψ
  obtain ⟨γ, hγ⟩ := hπ.1 ⟨y, hyL⟩
  let γA : ↥(alternatingGroup (Fin 5)) := γ
  have hγA : π γA = ⟨y, hyL⟩ := hγ
  have hπ'γA : (π' γA : MulAut W) = y := by
    show (π γA : MulAut W) = y
    rw [hγA]
  have hy3' : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hγ3 : (γA : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    have h1 : γA ^ 3 = 1 := by
      have h0 : γ ^ 3 = (1 : (FFModel.altDn 5).Gam) := by
        apply hπinj
        rw [map_pow, hγ]
        ext x
        have hx := congrArg (fun z : MulAut W => z x) hy3'
        simpa [pow_three, MulAut.mul_apply] using hx
      exact h0
    simpa using congrArg Subtype.val h1
  have hγsign : Equiv.Perm.sign (γA : Equiv.Perm (Fin 5)) = 1 := γA.2
  have hγV : γA ∈ normalizer (V : Set ↥(alternatingGroup (Fin 5))) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro v
    constructor
    · intro hv
      have hπv : (π' v : MulAut W) ∈ P := hv
      have hmem : (γA * v * γA⁻¹ : ↥(alternatingGroup (Fin 5))) ∈ V := by
        show (π' (γA * v * γA⁻¹) : MulAut W) ∈ P
        rw [map_mul, map_mul, map_inv, hπ'γA]
        exact (Subgroup.mem_set_normalizer_iff.mp hyN (π' v)).mp hπv
      exact hmem
    · intro hv
      have hmem : (γA * v * γA⁻¹ : ↥(alternatingGroup (Fin 5))) ∈ V := hv
      have hπv : (π' v : MulAut W) ∈ P := by
        have h2 : (π' (γA * v * γA⁻¹) : MulAut W) ∈ P := hmem
        rw [map_mul, map_mul, map_inv] at h2
        refine (Subgroup.mem_set_normalizer_iff.mp hyN (π' v)).mpr ?_
        rwa [hπ'γA] at h2
      exact hπv
  have hVeq : P0.map ψ.toMonoidHom = V := hψ
  have hVeq' : P0.map (CFSG.Quasithin.SteinbergCB.conjPerm 5 τ) = V := by
    rw [hτ]; exact hVeq
  let v : G6.coreMod 5 := f ⟨a, haJ⟩
  let fv : G6.PermMod 5 := Subtype.val (f ⟨a, haJ⟩)
  have hv1 : v ≠ 1 := by
    intro h
    have h1 : f ⟨a, haJ⟩ = 1 := h
    have h2 : (⟨a, haJ⟩ : ↥J) = 1 := hfinj (h1.trans (map_one f).symm)
    exact ha1 (congrArg Subtype.val h2)
  have hJinv : ∀ h : ↥L, ∀ u ∈ J, (h : MulAut W) u ∈ J := fun h u hu => hπ.2.2.2.1 h u hu
  have hVfix : ∀ δ : ↥(alternatingGroup (Fin 5)),
      δ ∈ V → G6.coreAct 5 (δ : Equiv.Perm (Fin 5)) v = v := by
    intro δ hδ
    have hπδ : (π' δ : MulAut W) ∈ P := hδ
    have haction : (π' δ : MulAut W) a = a := hPa _ hπδ
    have hfix := hfe δ ⟨a, haJ⟩ (hJinv (π δ) a haJ)
    have hleft : (f ⟨((π δ : ↥L) : MulAut W) a, hJinv (π δ) a haJ⟩ : G6.coreMod 5) = v := by
      apply congrArg f
      apply Subtype.ext
      exact haction
    rw [hleft] at hfix
    exact Subtype.ext hfix.symm
  let v' : G6.coreMod 5 := G6.coreAct 5 τ⁻¹ v
  have hvv' : G6.coreAct 5 τ v' = v := by
    show G6.coreAct 5 τ (G6.coreAct 5 τ⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hP0fix : ∀ p : A5, p ∈ P0 →
      (fun i => Multiplicative.toAdd (v' : G6.PermMod 5) ((p : Equiv.Perm (Fin 5))⁻¹ i)) =
        Multiplicative.toAdd (v' : G6.PermMod 5) := by
    intro p hp
    have hδ : (CFSG.Quasithin.SteinbergCB.conjPerm 5 τ p : ↥(alternatingGroup (Fin 5))) ∈ V := by
      rw [← hVeq']
      exact Subgroup.mem_map_of_mem _ hp
    have hfix := hVfix _ hδ
    have hδeq : ((CFSG.Quasithin.SteinbergCB.conjPerm 5 τ p :
        ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = τ * (p : Equiv.Perm (Fin 5)) * τ⁻¹ :=
      CFSG.Quasithin.SteinbergCB.conjPerm_apply 5 τ p
    rw [hδeq] at hfix
    have hcomp : (p : Equiv.Perm (Fin 5)) * τ⁻¹ =
        τ⁻¹ * (τ * (p : Equiv.Perm (Fin 5)) * τ⁻¹) := by group
    calc (fun i => Multiplicative.toAdd (v' : G6.PermMod 5)
            ((p : Equiv.Perm (Fin 5))⁻¹ i))
        = Multiplicative.toAdd (G6.coreAct 5 ((p : Equiv.Perm (Fin 5)) * τ⁻¹) v :
            G6.PermMod 5) := by
          rw [show v' = G6.coreAct 5 τ⁻¹ v from rfl, map_mul, MulAut.mul_apply]
          rfl
      _ = Multiplicative.toAdd (G6.coreAct 5 (τ⁻¹ * (τ * (p : Equiv.Perm (Fin 5)) * τ⁻¹)) v :
            G6.PermMod 5) := by rw [hcomp]
      _ = Multiplicative.toAdd (G6.coreAct 5 τ⁻¹ (G6.coreAct 5
            (τ * (p : Equiv.Perm (Fin 5)) * τ⁻¹) v) : G6.PermMod 5) := by
          rw [map_mul, MulAut.mul_apply]
      _ = Multiplicative.toAdd (G6.coreAct 5 τ⁻¹ v : G6.PermMod 5) := by rw [hfix]
      _ = Multiplicative.toAdd (v' : G6.PermMod 5) := by
          rw [show v' = G6.coreAct 5 τ⁻¹ v from rfl]
  let σ : Equiv.Perm (Fin 5) := τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ
  have hσ3 : σ ^ 3 = 1 := by
    show (τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ) ^ 3 = 1
    have hconj : (τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ) ^ 3 =
        τ⁻¹ * (γA : Equiv.Perm (Fin 5)) ^ 3 * τ := by
      rw [show τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ =
        τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * (τ⁻¹)⁻¹ from by rw [inv_inv]]
      rw [conj_pow, inv_inv]
    rw [hconj, hγ3, mul_one, inv_mul_cancel]
  have hσsign : Equiv.Perm.sign σ = 1 := by
    show Equiv.Perm.sign (τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ) = 1
    rw [map_mul, map_mul, map_inv, hγsign]
    simp
  have hσnorm : ∀ p : A5, p ∈ P0 →
      ∃ q : A5, q ∈ P0 ∧ σ * (p : Equiv.Perm (Fin 5)) * σ⁻¹ =
        (q : Equiv.Perm (Fin 5)) := by
    intro p hp
    have hδ : (CFSG.Quasithin.SteinbergCB.conjPerm 5 τ p : ↥(alternatingGroup (Fin 5))) ∈ V := by
      rw [← hVeq']
      exact Subgroup.mem_map_of_mem _ hp
    have hγδ : (γA * (CFSG.Quasithin.SteinbergCB.conjPerm 5 τ p) * γA⁻¹ :
        ↥(alternatingGroup (Fin 5))) ∈ V :=
      (Subgroup.mem_set_normalizer_iff.mp hγV _).mp hδ
    rw [← hVeq'] at hγδ
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hγδ
    refine ⟨q, hq, ?_⟩
    have hδeq : ((CFSG.Quasithin.SteinbergCB.conjPerm 5 τ p :
        ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = τ * (p : Equiv.Perm (Fin 5)) * τ⁻¹ :=
      CFSG.Quasithin.SteinbergCB.conjPerm_apply 5 τ p
    have hqeq' : ((CFSG.Quasithin.SteinbergCB.conjPerm 5 τ q :
        ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        (γA : Equiv.Perm (Fin 5)) * ((CFSG.Quasithin.SteinbergCB.conjPerm 5 τ p :
          ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
          (γA : Equiv.Perm (Fin 5))⁻¹ := by
      simpa using congrArg Subtype.val hqeq
    rw [hδeq] at hqeq'
    have hqeq'' : τ * (q : Equiv.Perm (Fin 5)) * τ⁻¹ =
        (γA : Equiv.Perm (Fin 5)) * (τ * (p : Equiv.Perm (Fin 5)) * τ⁻¹) *
          (γA : Equiv.Perm (Fin 5))⁻¹ := hqeq'
    have : (q : Equiv.Perm (Fin 5)) = τ⁻¹ * ((γA : Equiv.Perm (Fin 5)) *
        (τ * (p : Equiv.Perm (Fin 5)) * τ⁻¹) * (γA : Equiv.Perm (Fin 5))⁻¹) * τ := by
      rw [← hqeq'']; group
    rw [this]
    show τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ * (p : Equiv.Perm (Fin 5)) *
        (τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ)⁻¹ = _
    group
  have hσfix_raw := s16h_d5_P0_normalizer_fix
    (Multiplicative.toAdd (v' : G6.PermMod 5)) σ
    (by
      have h := G6.mem_coreMod.mp v'.2
      simpa using h)
    hP0fix hσnorm hσ3 hσsign
  have hσfix : G6.coreAct 5 σ v' = v' := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.coreAct_coe, G6.permAct_apply]
    exact congrFun hσfix_raw i
  have hγfix : G6.coreAct 5 (γA : Equiv.Perm (Fin 5)) v = v := by
    have h1 : G6.coreAct 5 (γA : Equiv.Perm (Fin 5)) v =
        G6.coreAct 5 τ (G6.coreAct 5 σ v') := by
      show G6.coreAct 5 (γA : Equiv.Perm (Fin 5)) v =
        G6.coreAct 5 τ (G6.coreAct 5 σ (G6.coreAct 5 τ⁻¹ v))
      rw [show (γA : Equiv.Perm (Fin 5)) = τ * σ * τ⁻¹ by
        show (γA : Equiv.Perm (Fin 5)) = τ * (τ⁻¹ * (γA : Equiv.Perm (Fin 5)) * τ) * τ⁻¹
        group]
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
    rw [h1, hσfix, hvv']
  have hfa : f ⟨a, haJ⟩ = v := rfl
  have hfixa : f ⟨((π γ : ↥L) : MulAut W) a, hJinv (π γ) a haJ⟩ = f ⟨a, haJ⟩ := by
    apply Subtype.ext
    have hfix := hfe γ ⟨a, haJ⟩ (hJinv (π γ) a haJ)
    rw [hfix]
    have hcast : ((FFModel.altDn 5).act γ fv) =
        (((G6.coreAct 5 (γA : Equiv.Perm (Fin 5))) v : G6.coreMod 5) :
          G6.PermMod 5) := rfl
    rw [hcast, congrArg Subtype.val hγfix]
  have hpa : ((π γ : ↥L) : MulAut W) a = a := by
    have := hfinj hfixa
    exact congrArg Subtype.val this
  have hγa : ((π γ : ↥L) : MulAut W) a = a := hpa
  have hy : (⟨y, hyL⟩ : ↥L) = π γ := hγ.symm
  show ((⟨y, hyL⟩ : ↥L) : MulAut W) a = a
  rw [hy]
  exact hγa

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
