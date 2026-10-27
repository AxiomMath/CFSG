module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusTwoAset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusNatAparamHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoordsRestrict
public import CFSG.Quasithin.Background.HMultNorm
public import CFSG.Quasithin.Background.HMultFix
public import CFSG.Quasithin.Background.HModelTransp
public import CFSG.Quasithin.Background.SmithD321Ext
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.E3
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Quasithin.H.Mult
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped Matrix Kronecker

private abbrev OIdx6 : Type := Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2

private theorem sq_eq_one_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {U : Subgroup W} {n : ℕ}
    (h : NatOmegaMinus X U ⊥ 6 n) : ∀ u : ↥U, u ^ 2 = 1 := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π, hπ⟩ := h
  let _ : Field K := hK
  have _ : Finite K := hKf
  have _ : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
  obtain ⟨β, hβs, hβk, hβe⟩ := (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : W) ∈ (⊥ : Subgroup W) := (hβk _).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  intro u
  apply hβinj
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [pow_two, toAdd_mul, toAdd_one]
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hzero : (2 : K) • Multiplicative.toAdd (β u) i = 0 := by rw [h2, zero_smul]
  rw [two_smul] at hzero
  exact hzero

private theorem pair_isIrr_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {U : Subgroup W} {n : ℕ}
    (h : NatOmegaMinus X U ⊥ 6 n) : H.Pair.IsIrr X U := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π, hπ⟩ := h
  let _ : Field K := hK
  have _ : Finite K := hKf
  obtain ⟨H', π', hH'eq, hπ'coe, hreal'⟩ := exists_realizesVia_restrict hπ
  have hNat' : NatOmegaMinus H' ⊤ ⊥ 6 n :=
    ⟨by norm_num, K, hK, hKf, b, c, hcard, hpoly, π', hreal'⟩
  have hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn H' :=
    k_Omega6Minus_irr (W := ↥U) (H := H') (n := n) hNat'
  obtain ⟨β, hβs, hβk, hβe⟩ := (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hUbot : U ≠ ⊥ := by
    intro hbot
    have hnt : Nontrivial
        (Multiplicative (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2 → K)) := by
      refine ⟨Multiplicative.ofAdd (Pi.single (Sum.inl ⟨0, by norm_num⟩) 1), 1, ?_⟩
      intro h
      have h' := congrArg Multiplicative.toAdd h
      simp [Pi.single_eq_same] at h'
    have _ : Subsingleton ↥U := by rw [hbot]; infer_instance
    exact (not_subsingleton_iff_nontrivial.mpr hnt) hβs.subsingleton
  refine ⟨hUbot, ?_⟩
  intro V hVU hVinv
  let V' : Subgroup ↥U := V.comap U.subtype
  have hV'map : V'.map U.subtype = V :=
    Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  have hV'inv : StableUnder H' V' := by
    intro x hx v hv
    obtain ⟨γ, hγ⟩ := hreal'.1 ⟨x, hx⟩
    have hxeq : (π' γ : MulAut ↥U) = x := congrArg Subtype.val hγ
    rw [← hxeq, hπ'coe γ]
    exact hVinv (π γ) (π γ).2 v hv
  rcases hirr V' hV'inv with hbot | htop
  · left
    rw [← hV'map, hbot, Subgroup.map_bot]
  · right
    rw [← hV'map, htop, Subgroup.map_top, Subgroup.range_subtype]

private theorem eq_one_of_fixes_natOmegaMinus_summand {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} {n : ℕ}
    (h0 : NatOmegaMinus X J₀ ⊥ 6 n) (h1 : NatOmegaMinus X J₁ ⊥ 6 n)
    (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = ⊤)
    (hiso : ¬ H.Pair.IsoMod X J₀ J₁)
    {a : MulAut W} (haX : a ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hac : ∀ x ∈ X, a * x = x * a) (ha2 : a ^ 2 = 1)
    (hafix0 : ∀ v ∈ J₀, a v = v) : a = 1 := by
  classical
  have hIrr0 : H.Pair.IsIrr X J₀ := pair_isIrr_of_natOmegaMinus h0
  have hIrr1 : H.Pair.IsIrr X J₁ := pair_isIrr_of_natOmegaMinus h1
  have hInv0 : H.Pair.IsInv X J₀ := by
    obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π, hπ⟩ := h0
    exact fun x hx u hu => hπ.2.2.2.1 ⟨x, hx⟩ u hu
  have hInv1 : H.Pair.IsInv X J₁ := by
    obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π, hπ⟩ := h1
    exact fun x hx u hu => hπ.2.2.2.1 ⟨x, hx⟩ u hu
  have hJ1map : J₁.map a.toMonoidHom = J₁ := by
    have h1inv : H.Pair.IsInv X (J₁.map a.toMonoidHom) := H.Pair.isInv_map haX hInv1
    have h1irr : H.Pair.IsIrr X (J₁.map a.toMonoidHom) := H.Pair.isIrr_map haX hIrr1
    rcases H.Pair.eq_or_eq_of_isIrr hinf hsup hInv0 hInv1 hIrr0 hIrr1 hiso h1inv h1irr with
      h | h
    · exfalso
      obtain ⟨⟨v, hvJ1⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIrr1.1
      have havJ0 : a v ∈ J₀ := by
        rw [← h]
        exact ⟨v, hvJ1, rfl⟩
      have hfixav : a (a v) = a v := hafix0 (a v) havJ0
      have haa : a (a v) = v := by
        simpa [pow_two, MulAut.mul_apply] using
          congrArg (fun f : MulAut W => f v) ha2
      have hvJ0 : v ∈ J₀ := by
        rw [← haa, hfixav]
        exact havJ0
      have hvbot : v ∈ J₀ ⊓ J₁ := ⟨hvJ0, hvJ1⟩
      rw [hinf] at hvbot
      exact hv1 (Subtype.ext (Subgroup.mem_bot.mp hvbot))
    · exact h
  obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π, hπ⟩ := h1
  let _ : Field K := hK
  have _ : Finite K := hKf
  have _ : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
  have hXJ1 : ∀ x ∈ X, ∀ u ∈ J₁, x u ∈ J₁ :=
    fun x hx u hu => hπ.2.2.2.1 ⟨x, hx⟩ u hu
  obtain ⟨H', π', hH'eq, hπ'coe, hreal'⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.exists_realizesVia_restrict hπ
  obtain ⟨β, hβs, hβk, hβe⟩ := (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hreal').exists_β
  have ha_stab : a ∈ stabSub J₁ := CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mpr hJ1map
  have hAI : ∀ x ∈ Subgroup.zpowers a, ∀ u ∈ J₁, x u ∈ J₁ := by
    intro x hx u hu
    have hxstab : x ∈ stabSub J₁ := Subgroup.zpowers_le.mpr ha_stab hx
    have hxmap : J₁.map x.toMonoidHom = J₁ :=
      CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mp hxstab
    rw [← hxmap]
    exact ⟨u, hu, rfl⟩
  let cJ : MulAut ↥J₁ := actOnSub hAI ⟨a, Subgroup.mem_zpowers a⟩
  have hcJ_apply : ∀ v : ↥J₁, ((cJ v : ↥J₁) : W) = a (v : W) := by
    intro v
    exact actOnSub_apply hAI ⟨a, Subgroup.mem_zpowers a⟩ v
  have hc : ∀ x ∈ H', cJ * x = x * cJ := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hreal'.1 ⟨x, hx⟩
    have hx' : x = (π' γ : MulAut ↥J₁) := (congrArg Subtype.val hγ).symm
    rw [hx', hπ'coe γ]
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    simp only [MulAut.mul_apply, hcJ_apply, actOnSub_apply]
    exact congrArg (fun f : MulAut W => f (u : W)) (hac (π γ) (π γ).2)
  have hc2 : cJ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    rw [pow_two, MulAut.mul_apply, hcJ_apply, hcJ_apply]
    have h := congrArg (fun f : MulAut W => f (v : W)) ha2
    simpa [pow_two, MulAut.mul_apply] using h
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hodd : Odd (Nat.card K - 1) := by
    rw [hcard]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨2 ^ m - 1, ?_⟩
    have hpos : 0 < 2 ^ m := Nat.pow_pos (by norm_num)
    rw [pow_succ]
    omega
  have hcop : Nat.Coprime (orderOf cJ) (Nat.card K - 1) :=
    Nat.Coprime.of_dvd_left (orderOf_dvd_iff_pow_eq_one.mpr hc2)
      (Nat.coprime_two_left.mpr hodd)
  have hHSC : CFSG.Quasithin.H.HasScalarCommutant (StatedOmega (StatedQuadMinus 3 K b c)) :=
    fun f hf => CFSG.LocalAnalysis.RankThreeUC.omega_commutant hpoly f hf
  have hfix1 : ∀ v : ↥J₁, ((cJ v : ↥J₁) : W) = (v : W) := by
    let β' : ↥J₁ →* Multiplicative
        (Fin (6 / 2 - 1) ⊕ Fin (6 / 2 - 1) ⊕ Fin 2 → K) :=
      β.comp (Subgroup.topEquiv.symm.toMonoidHom)
    have hβ's : Function.Surjective β' :=
      hβs.comp Subgroup.topEquiv.symm.surjective
    have hβ'k : ∀ v : ↥J₁, β' v = 1 ↔ v ∈ (⊥ : Subgroup ↥J₁) :=
      fun v => hβk ⟨v, trivial⟩
    have hβ'e : ∀ (γ : ↥(StatedOmega (StatedQuadMinus 3 K b c))) (v : ↥J₁),
        β' (((π' γ : ↥H') : MulAut ↥J₁) v) =
          natAct (StatedOmega (StatedQuadMinus 3 K b c)) γ (β' v) :=
      fun γ v => hβe γ ⟨v, trivial⟩ trivial
    have h := commutant_section_of_matrix (H := H') (Γ := StatedOmega (StatedQuadMinus 3 K b c))
      (π := π') (β := β') hβ's (Z := ⊥) hβ'k hβ'e hHSC
      (c := cJ) (fun z hz => by simpa using hz) hc hcop
    intro v
    have hv := h v
    have h1 : cJ v = v := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hv)
    have h2 : ((cJ v : ↥J₁) : W) = (v : W) := congrArg (fun z : ↥J₁ => (z : W)) h1
    rwa [hcJ_apply v] at h2
  have hay : ∀ v ∈ J₁, a v = v := by
    intro v hv
    have h := hfix1 ⟨v, hv⟩
    rw [hcJ_apply ⟨v, hv⟩] at h
    exact h
  ext w
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp (by rw [hsup]; exact Subgroup.mem_top w)
  simpa [map_mul, hafix0 x hx, hay y hy]

theorem k_Omega6Minus_sumOfTwo_aParam_holds : K_Omega6Minus_sumOfTwo_aParam := by
  classical
  intro W _ _ X N n hSum hN
  by_cases hev : Even (Nat.card N)
  · unfold E3.aParam
    rw [if_pos hev]
    by_cases hne : {k : ℕ | 0 < k ∧ (E3.aSet k N).Nonempty}.Nonempty
    · refine csSup_le hne ?_
      rintro k ⟨hk0, A, hA⟩
      obtain ⟨I, hZI, hind, hsup, hNat⟩ := hSum
      have h01 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
        refine le_antisymm ?_ ?_
        · refine iSup_le fun j => iSup_le fun hj => ?_
          fin_cases j
          · exact (hj rfl).elim
          · exact le_rfl
        · exact le_iSup₂ (f := fun j (_ : j ≠ 0) => I j) 1 (by decide)
      have h10 : (⨆ (j : Fin 2) (_ : j ≠ 1), I j) = I 0 := by
        refine le_antisymm ?_ ?_
        · refine iSup_le fun j => iSup_le fun hj => ?_
          fin_cases j
          · exact le_rfl
          · exact (hj rfl).elim
        · exact le_iSup₂ (f := fun j (_ : j ≠ 1) => I j) 0 (by decide)
      have hJinf : I 0 ⊓ I 1 = ⊥ := by
        have h := hind 0
        rw [bot_sup_eq, h01] at h
        exact le_bot_iff.1 h
      have hJsup : I 0 ⊔ I 1 = ⊤ := by
        have hall : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 := by
          refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right
        rw [hall, bot_sup_eq] at hsup
        exact hsup
      have hNat0 : NatOmegaMinus X (I 0) ⊥ 6 n := hNat 0
      have hNat1 : NatOmegaMinus X (I 1) ⊥ 6 n := hNat 1
      have hn1 : 1 ≤ n := by
        obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π, hπ⟩ := hNat0
        let _ : Field K := hK
        have _ : Finite K := hKf
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · rw [hn0, pow_zero] at hcard
          have h2 : 1 < Nat.card K := Finite.one_lt_card
          omega
        · exact hnpos
      by_cases hk2 : k ≤ 2
      · omega
      have hk3 : 3 ≤ k := by omega
      by_cases hiso : H.Pair.IsoMod X (I 0) (I 1)
      ·
        have hNat0c := hNat0
        obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π0, hπ0⟩ := hNat0
        let _ : Field K := hK
        have _ : Finite K := hKf
        have _ : CharP K 2 :=
          CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
        let Γ := StatedOmega (StatedQuadMinus (6 / 2) K b c)
        have hΓsc : CFSG.Quasithin.H.HasScalarCommutant Γ :=
          fun f hf => CFSG.LocalAnalysis.RankThreeUC.omega_commutant hpoly f hf
        have _ : NeZero 2 := ⟨by norm_num⟩
        have hiso0 : H.Pair.IsoMod X (I 0) (I 0) :=
          ⟨MulEquiv.refl _, fun l hl w h => rfl⟩
        have hiso' : ∀ i : Fin 2, H.Pair.IsoMod X (I 0) (I i) := by
          intro i
          fin_cases i
          · exact hiso0
          · exact hiso
        have hVia : SumOfNatVia (FFModel.nat Γ) X ⊤ ⊥ 2 π0 :=
          sumOfNatVia_of_isoMod (D := FFModel.nat Γ) (X := X) (I := I) hind hsup 0 hπ0 hiso'
        obtain ⟨I', e, hI'real, he, hI'mem⟩ := exists_coords_of_sumOfNatVia Γ hVia
        have hXmap : X.map (congrHom e) = natImage (diagSub 2 Γ) :=
          map_congrHom_eq_natImage_diag Γ hπ0.1 e he
        let X' : Subgroup (MulAut (StdMod (Fin 2 × OIdx6) K)) := X.map (congrHom e)
        let A' : Subgroup (MulAut (StdMod (Fin 2 × OIdx6) K)) := A.map (congrHom e)
        let N' : Subgroup (MulAut (StdMod (Fin 2 × OIdx6) K)) := N.map (congrHom e)
        have hXmap' : X' = natImage (diagSub 2 Γ) := hXmap
        have hA' : A' ∈ E3.aSet k N' := (map_mem_aSet_iff e).mpr hA
        have hN' : N' ≤ Subgroup.normalizer
            (X' : Set (MulAut (StdMod (Fin 2 × OIdx6) K))) :=
          CFSG.Quasithin.H.ZTrans.map_le_normalizer_congrHom e hN
        have hform : ∀ a ∈ A', ∃ (A_a : MulAut (StdMod OIdx6 K)) (σ : K ≃+* K)
            (B : GL (Fin 2) K), IsSemilinear A_a σ ∧
              ∀ (v : Fin 2 × OIdx6 → K) (p : Fin 2 × OIdx6), toAddMap a v p =
                toAddMap A_a
                  (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j * v (j, i)) p.2 := by
          intro a ha
          have haN : a ∈ Subgroup.normalizer
              (natImage (diagSub 2 Γ) : Set (MulAut (StdMod (Fin 2 × OIdx6) K))) := by
            have h := hN' (hA'.1 ha)
            rwa [hXmap'] at h
          obtain ⟨A_a, σ, B, -, hsemiA, -, hformula, -⟩ :=
            exists_of_mem_normalizer_diag (k := 2) hΓsc haN
          exact ⟨A_a, σ, B, hsemiA, hformula⟩
        have hA'p : IsPGroup 2 ↥A' :=
          IsPGroup.map (G := MulAut W) (H := A)
            (E3.isPGroup_of_isElemAbelian2 hA.2.2.1) (congrHom e)
        obtain ⟨u, hu0, hufix⟩ := exists_fixed_lineSub hA'p hform
        have hJ : ∀ a ∈ A', ∀ w ∈ (lineSub (ι := OIdx6) u), a w ∈ (lineSub (ι := OIdx6) u) := by
          intro a ha w hw
          change a w ∈ lineSub u
          have hmap := hufix a ha
          rw [← hmap]
          exact ⟨w, hw, rfl⟩
        have hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
          fun a ha => hN (hA.1 ha)
        have hdiag : ∀ (γ : GL OIdx6 K) (y : StdMod OIdx6 K),
            matAut (diagGL (ι := OIdx6) 2 γ)
                (lineEmb (ι := OIdx6) u y) =
              lineEmb (ι := OIdx6) u (matAut γ y) := by
          intro γ y
          have hformula : ∀ (v : Fin 2 × OIdx6 → K) (p : Fin 2 × OIdx6),
              toAddMap (matAut (diagGL (ι := OIdx6) 2 γ)) v p =
                toAddMap (matAut γ)
                  (fun i => ∑ j, (1 : Matrix (Fin 2) (Fin 2) K) p.1 j * v (j, i)) p.2 := by
            intro v p
            rw [toAddMap_matAut, diagGL_mulVec, toAddMap_matAut]
            simp [Matrix.one_apply]
          simpa using normalForm_lineEmb (hA := isSemilinear_matAut γ) (B := 1)
            (u := u) (x := y) hformula
        have hXJ : ∀ x ∈ X', ∀ w ∈ (lineSub (ι := OIdx6) u), x w ∈ (lineSub (ι := OIdx6) u) := by
          intro x hx w hw
          have hx' : x ∈ natImage (diagSub 2 Γ) := by rwa [← hXmap']
          obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hx'
          obtain ⟨δ, hδ, hδγ⟩ := Subgroup.mem_map.mp γ.2
          have hxmat : x = matAut (diagGL (ι := OIdx6) 2 (δ : GL OIdx6 K)) := by
            rw [← hγ]
            change matAut (γ : GL (Fin 2 × OIdx6) K) =
              matAut (diagGL (ι := OIdx6) 2 (δ : GL OIdx6 K))
            rw [hδγ]
          obtain ⟨y, hy⟩ : ∃ y : StdMod OIdx6 K,
              lineEmb (ι := OIdx6) u y = (w : StdMod (Fin 2 × OIdx6) K) := by
            have hw' : (w : StdMod (Fin 2 × OIdx6) K) ∈ (lineEmb (ι := OIdx6) u).range := by
              rw [range_lineEmb]
              exact hw
            exact MonoidHom.mem_range.mp hw'
          rw [hxmat, ← hy, hdiag]
          exact ⟨Multiplicative.toAdd (matAut (δ : GL OIdx6 K) y), rfl⟩
        obtain ⟨eJ, heJ⟩ := exists_lineSub_equiv (ι := OIdx6) (k := 2) u hu0
        let J_W : Subgroup W := (lineSub (ι := OIdx6) u).map e.symm.toMonoidHom
        have hJW : ∀ a ∈ A, ∀ w ∈ J_W, a w ∈ J_W := by
          intro a ha w hw
          obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw
          have hew : e w = v := by
            rw [← hvw]
            exact e.apply_symm_apply v
          have ha' : congrHom e a ∈ A' := ⟨a, ha, rfl⟩
          have hmem : congrHom e a (e w) ∈ lineSub (ι := OIdx6) u := by
            rw [hew]
            exact hJ (congrHom e a) ha' v hv
          have heq : e (a w) = congrHom e a (e w) := by
            rw [congrHom_apply, e.symm_apply_apply]
          rw [← heq] at hmem
          exact Subgroup.mem_map.mpr ⟨e (a w), hmem, e.symm_apply_apply (a w)⟩
        have hXJW : ∀ x ∈ X, ∀ w ∈ J_W, x w ∈ J_W := by
          intro x hx w hw
          obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw
          have hew : e w = v := by
            rw [← hvw]
            exact e.apply_symm_apply v
          have hx' : congrHom e x ∈ X' := ⟨x, hx, rfl⟩
          have hmem : congrHom e x (e w) ∈ lineSub (ι := OIdx6) u := by
            rw [hew]
            exact hXJ (congrHom e x) hx' v hv
          have heq : e (x w) = congrHom e x (e w) := by
            rw [congrHom_apply, e.symm_apply_apply]
          rw [← heq] at hmem
          exact Subgroup.mem_map.mpr ⟨e (x w), hmem, e.symm_apply_apply (x w)⟩
        obtain ⟨β, hβs, hβk, hβe⟩ :=
          (CFSG.Quasithin.SzN15.NatReal.of_realizesVia (hI'real 0)).exists_β
        have hβinj : Function.Injective β := by
          intro a b hab
          have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
          have h2 : ((a * b⁻¹ : ↥(I' 0)) : W) ∈ (⊥ : Subgroup W) := (hβk _).1 h1
          have h3 : a * b⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.1 h2)
          exact mul_inv_eq_one.1 h3
        let βe : ↥(I' 0) ≃* StdMod OIdx6 K := MulEquiv.ofBijective β ⟨hβinj, hβs⟩
        let eJ' : ↥(lineSub (ι := OIdx6) u) ≃* ↥J_W :=
          Subgroup.equivMapOfInjective (lineSub (ι := OIdx6) u) e.symm.toMonoidHom
            e.symm.injective
        have hcoe : ∀ x : ↥(lineSub (ι := OIdx6) u),
            ((eJ' x : ↥J_W) : W) = e.symm (x : StdMod (Fin 2 × OIdx6) K) :=
          fun x => rfl
        let ψ : ↥(I' 0) ≃* ↥J_W := βe.trans (eJ.symm.trans eJ')
        have hconj : ∀ (γ : ↥Γ) (w : ↥(lineSub (ι := OIdx6) u))
            (hw : matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
              (w : StdMod (Fin 2 × OIdx6) K) ∈ lineSub (ι := OIdx6) u),
            eJ' ⟨matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
                (w : StdMod (Fin 2 × OIdx6) K), hw⟩ =
              ((π0 γ : ↥X) : MulAut W) (eJ' w) := by
          intro γ w hw
          apply e.injective
          calc e (eJ' ⟨matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
                (w : StdMod (Fin 2 × OIdx6) K), hw⟩)
              = e (e.symm (matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
                  (w : StdMod (Fin 2 × OIdx6) K))) := by
                rw [hcoe]
            _ = matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
                  (w : StdMod (Fin 2 × OIdx6) K) := e.apply_symm_apply _
            _ = e (((π0 γ : ↥X) : MulAut W) (eJ' w)) := by
                exact ((he γ (eJ' w)).trans (by
                  congr 1
                  rw [hcoe, e.apply_symm_apply])).symm
        have hψ : ∀ (x : ↥X) (v : ↥(I' 0))
            (h : (x : MulAut W) v ∈ I' 0),
            (ψ ⟨(x : MulAut W) v, h⟩ : W) = (x : MulAut W) (ψ v) := by
          intro x v hv
          obtain ⟨γ, hγ⟩ := hπ0.1 x
          subst x
          have hcanon : β ⟨((π0 γ : ↥X) : MulAut W) v,
              (hI'real 0).2.2.2.1 (π0 γ) v v.2⟩ =
              β ⟨((π0 γ : ↥X) : MulAut W) v, hv⟩ := by
            congr 1
          have hβ := hβe γ v ((hI'real 0).2.2.2.1 (π0 γ) v v.2)
          have hψv : ((ψ v : ↥J_W) : W) = e.symm (eJ.symm (βe v)) := rfl
          have hψlv : ((ψ ⟨((π0 γ : ↥X) : MulAut W) v, hv⟩ : ↥J_W) : W) =
              e.symm (eJ.symm (βe ⟨((π0 γ : ↥X) : MulAut W) v, hv⟩)) := rfl
          rw [hψlv, hψv]
          have hβ' : βe ⟨((π0 γ : ↥X) : MulAut W) v, hv⟩ =
              matAut (γ.1 : GL OIdx6 K) (βe v) := by
            change β ⟨((π0 γ : ↥X) : MulAut W) v, hv⟩ =
              matAut (γ.1 : GL OIdx6 K) (β v)
            rw [← hcanon]
            have hnat : CFSG.Quasithin.natAct Γ γ (β v) =
                matAut (γ.1 : GL OIdx6 K) (β v) := rfl
            rw [hnat] at hβ
            exact hβ
          rw [hβ']
          obtain ⟨y, hy⟩ : ∃ y : StdMod OIdx6 K,
              lineEmb (ι := OIdx6) u y = (eJ.symm (βe v) : StdMod (Fin 2 × OIdx6) K) := by
            have hw : (eJ.symm (βe v) : StdMod (Fin 2 × OIdx6) K) ∈
                (lineEmb (ι := OIdx6) u).range := by
              rw [range_lineEmb]
              exact (eJ.symm (βe v)).2
            exact MonoidHom.mem_range.mp hw
          have hmem : matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
              (eJ.symm (βe v)) ∈ lineSub (ι := OIdx6) u := by
            rw [← hy, hdiag]
            exact ⟨Multiplicative.toAdd (matAut (γ.1 : GL OIdx6 K) y), rfl⟩
          have h1 := heJ (γ := (γ.1 : GL OIdx6 K))
            (w := eJ.symm (βe v)) (h := hmem)
          have hsym : eJ.symm (matAut (γ.1 : GL OIdx6 K) (βe v)) =
              ⟨matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
                (eJ.symm (βe v)), hmem⟩ := by
            have h1' : eJ ⟨matAut (diagGL (ι := OIdx6) 2 (γ.1 : GL OIdx6 K))
                (eJ.symm (βe v)), hmem⟩ =
                matAut (γ.1 : GL OIdx6 K) (βe v) := by
              simpa using h1
            exact eJ.symm_apply_eq.mpr h1'.symm
          rw [hsym]
          exact hconj γ (eJ.symm (βe v)) hmem
        have hψ' : ∀ l ∈ X, ∀ (u : ↥(I' 0)) (h : l u ∈ I' 0),
            (ψ ⟨l u, h⟩ : W) = l (ψ u) := by
          intro l hl u hu
          exact hψ ⟨l, hl⟩ u hu
        let hIsoJW : H.Pair.IsoMod X (I' 0) J_W := ⟨ψ, hψ'⟩
        have hRealJW : (FFModel.nat Γ).RealizesVia X J_W ⊥ π0 :=
          realizesVia_of_isoMod (hI'real 0) hIsoJW
        by_cases htrivJW : ∀ a ∈ A, ∀ w ∈ J_W, a w = w
        ·
          have hfaithJW : ∀ x ∈ X, (∀ w ∈ J_W, x w = w) → x = 1 := by
            intro x hx hfix
            obtain ⟨γ, hγ⟩ := hπ0.1 ⟨x, hx⟩
            have hxeq : ((π0 γ : ↥X) : MulAut W) = x := congrArg Subtype.val hγ
            have hfixγ : ∀ w ∈ J_W, ((π0 γ : ↥X) : MulAut W) w = w := by
              intro w hw
              rw [hxeq]
              exact hfix w hw
            by_contra hx1
            have hγ1 : γ ≠ 1 := by
              intro hγeq
              apply hx1
              rw [← hxeq, hγeq]
              simp
            have hmoved := CFSG.Quasithin.G64.RealizesVia.exists_moved
              (D := FFModel.nat Γ) (FFModel.nat_faithful Γ) hRealJW (γ := γ) hγ1
            obtain ⟨w, hw, hneu⟩ := hmoved
            have hmem : ((π0 γ : ↥X) : MulAut W) w * w⁻¹ ∈ (⊥ : Subgroup W) := by
              rw [hfixγ w hw, mul_inv_cancel]
              exact Subgroup.one_mem _
            exact hneu hmem
          have hAc : A ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
            intro a ha
            rw [Subgroup.mem_centralizer_iff]
            intro x hx
            have haP : ∀ w ∈ J_W, a⁻¹ w ∈ J_W := fun w hw =>
              hJW a⁻¹ (A.inv_mem ha) w hw
            exact (CFSG.Quasithin.SmithD321.comm_of_trivial_on
              (hAX ha) hXJW hfaithJW (htrivJW a ha) haP x hx).symm
          have hAc' : A' ≤ Subgroup.centralizer
              (natImage (diagSub 2 Γ) : Set (MulAut (StdMod (Fin 2 × OIdx6) K))) := by
            intro a' ha'
            have ha'map : a' ∈ A.map (congrHom e) := by
              rwa [show A' = A.map (congrHom e) from rfl] at ha'
            obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp ha'map
            rw [← haeq, Subgroup.mem_centralizer_iff]
            intro x' hx'
            have hx'map : x' ∈ X.map (congrHom e) := by
              rwa [← hXmap'] at hx'
            obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hx'map
            rw [← hxeq, ← map_mul, ← map_mul]
            exact congrArg (congrHom e)
              (Subgroup.mem_centralizer_iff.mp (hAc ha) x hx)
          have hcardA : Nat.card A' ≤ Nat.card K :=
            card_le_of_isElemAbelian_two_centralizer_diag hΓsc
              (H.isElemAbelian2_iff.mp hA'.2.2.1) hAc'
          have hcardA' : Nat.card A' = Nat.card A :=
            Subgroup.card_map_of_injective (congrHom_injective e)
          have hkn : k ≤ n := by
            have hkA : k ≤ E3.mQuot A' ⊥ := E3.le_mQuot_bot_of_mem_aSet hA'
            have hcardA'' : Nat.card A' = 2 ^ E3.mQuot A' ⊥ := by
              have h := E3.card_eq_two_pow_mul (V := A') hA'p (bot_le : ⊥ ≤ A')
              simpa using h
            have hpow : 2 ^ k ≤ 2 ^ n := by
              calc 2 ^ k ≤ 2 ^ E3.mQuot A' ⊥ :=
                    Nat.pow_le_pow_right (by norm_num) hkA
                _ = Nat.card A' := hcardA''.symm
                _ ≤ Nat.card K := hcardA
                _ = 2 ^ n := hcard
            exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
          omega
        ·
          have hAJWne : (actOnSub hJW).range ≠ ⊥ := by
            intro hbot
            apply htrivJW
            intro a ha w hw
            have hmem : actOnSub hJW ⟨a, ha⟩ = 1 := by
              have h1 : actOnSub hJW ⟨a, ha⟩ ∈ (⊥ : Subgroup (MulAut ↥J_W)) := by
                rw [← hbot]
                exact ⟨⟨a, ha⟩, rfl⟩
              simpa using Subgroup.mem_bot.mp h1
            have h2 := congrArg (fun f : MulAut ↥J_W => (f ⟨w, hw⟩ : ↥J_W)) hmem
            have h3 : ((actOnSub hJW ⟨a, ha⟩ ⟨w, hw⟩ : ↥J_W) : W) = a w :=
              actOnSub_apply hJW ⟨a, ha⟩ ⟨w, hw⟩
            have h4 : ((actOnSub hJW ⟨a, ha⟩ ⟨w, hw⟩ : ↥J_W) : W) = w := by
              simpa using congrArg (fun z : ↥J_W => (z : W)) h2
            rw [h3] at h4
            exact h4
          obtain ⟨H_J, πJ, hH_J_eq, hπJ_coe, hrealJ'⟩ :=
            CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.exists_realizesVia_restrict hRealJW
          have hNatH_J : NatOmegaMinus H_J ⊤ ⊥ 6 n :=
            ⟨by norm_num, K, hK, hKf, b, c, hcard, hpoly, πJ, hrealJ'⟩
          have hAJWnorm : (actOnSub hJW).range ≤
              Subgroup.normalizer (H_J : Set (MulAut ↥J_W)) := by
            rw [hH_J_eq]
            exact actOnSub_range_le_normalizer hXJW hJW hAX
          have hA_JW : (actOnSub hJW).range ∈ E3.aSet k
              (Subgroup.normalizer (H_J : Set (MulAut ↥J_W))) := by
            rw [hH_J_eq]
            exact mem_aSet_actOnSub hA hJW
              (actOnSub_range_le_normalizer hXJW hJW hAX) hAJWne
          exact le_two_mul_of_mem_aSet_natOmegaMinus hNatH_J le_rfl hA_JW
      ·
        have hIrr0 : H.Pair.IsIrr X (I 0) := pair_isIrr_of_natOmegaMinus hNat0
        have hIrr1 : H.Pair.IsIrr X (I 1) := pair_isIrr_of_natOmegaMinus hNat1
        have hNat0c := hNat0
        obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π0, hπ0⟩ := hNat0
        let _ : Field K := hK
        have _ : Finite K := hKf
        have _ : CharP K 2 :=
          CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
        let Γ := StatedOmega (StatedQuadMinus (6 / 2) K b c)
        have hInv0 : H.Pair.IsInv X (I 0) :=
          fun x hx u hu => hπ0.2.2.2.1 ⟨x, hx⟩ u hu
        have hInv1 : H.Pair.IsInv X (I 1) := by
          obtain ⟨-, K₁, hK₁, hK₁f, b₁, c₁, hcard₁, hpoly₁, π₁, hπ₁⟩ := hNat1
          exact fun x hx u hu => hπ₁.2.2.2.1 ⟨x, hx⟩ u hu
        have hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
          fun a ha => hN (hA.1 ha)
        let A₁ : Subgroup (MulAut W) := A ⊓ stabSub (I 0)
        have hA₁le : A₁ ≤ A := inf_le_left
        by_cases hA₁eq : A₁ = A
        ·
          have hAJ0 : ∀ a ∈ A, ∀ u ∈ I 0, a u ∈ I 0 := by
            intro a ha u hu
            have hain : a ∈ A₁ := by rwa [hA₁eq]
            have hstab : a ∈ stabSub (I 0) := (Subgroup.mem_inf.mp hain).2
            have hmap : (I 0).map a.toMonoidHom = I 0 :=
              CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mp hstab
            rw [← hmap]
            exact ⟨u, hu, rfl⟩
          have hXJ0 : ∀ x ∈ X, ∀ u ∈ I 0, x u ∈ I 0 :=
            fun x hx u hu => hπ0.2.2.2.1 ⟨x, hx⟩ u hu
          by_cases htriv0 : ∀ a ∈ A, ∀ u ∈ I 0, a u = u
          ·
            exfalso
            have hfaith0 : ∀ x ∈ X, (∀ v ∈ I 0, x v = v) → x = 1 := by
              intro x hx hfix
              obtain ⟨γ, hγ⟩ := hπ0.1 ⟨x, hx⟩
              have hxeq : ((π0 γ : ↥X) : MulAut W) = x := congrArg Subtype.val hγ
              have hfixγ : ∀ v ∈ I 0, ((π0 γ : ↥X) : MulAut W) v = v := by
                intro v hv
                rw [hxeq]
                exact hfix v hv
              by_contra hx1
              have hγ1 : γ ≠ 1 := by
                intro hγeq
                apply hx1
                rw [← hxeq, hγeq]
                simp
              have hmoved := CFSG.Quasithin.G64.RealizesVia.exists_moved
                (D := FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c)))
                (FFModel.nat_faithful (StatedOmega (StatedQuadMinus 3 K b c)))
                hπ0 (γ := γ) hγ1
              obtain ⟨u, hu, hneu⟩ := hmoved
              have hmem : ((π0 γ : ↥X) : MulAut W) u * u⁻¹ ∈ (⊥ : Subgroup W) := by
                rw [hfixγ u hu, mul_inv_cancel]
                exact Subgroup.one_mem _
              exact hneu hmem
            have hAc : A ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
              intro a ha
              rw [Subgroup.mem_centralizer_iff]
              intro x hx
              have haP : ∀ v ∈ I 0, a⁻¹ v ∈ I 0 := fun v hv =>
                hAJ0 a⁻¹ (A.inv_mem ha) v hv
              exact (CFSG.Quasithin.SmithD321.comm_of_trivial_on
                (hAX ha) hXJ0 hfaith0 (htriv0 a ha) haP x hx).symm
            have hAone : A = ⊥ := by
              refine le_bot_iff.1 fun a ha => ?_
              have hcomm : ∀ x ∈ X, a * x = x * a := by
                intro x hx
                exact (Subgroup.mem_centralizer_iff.mp (hAc ha) x hx).symm
              have hone : a = 1 := eq_one_of_fixes_natOmegaMinus_summand hNat0c hNat1 hJinf
                hJsup hiso (hAX ha) hcomm (hA.2.2.1.2 a ha) (htriv0 a ha)
              simpa using hone
            exact hA.2.1 hAone
          ·
            have hAJ0ne : (actOnSub hAJ0).range ≠ ⊥ := by
              intro hbot
              apply htriv0
              intro a ha u hu
              have hmem : actOnSub hAJ0 ⟨a, ha⟩ = 1 := by
                have h1 : actOnSub hAJ0 ⟨a, ha⟩ ∈ (⊥ : Subgroup (MulAut ↥(I 0))) := by
                  rw [← hbot]
                  exact ⟨⟨a, ha⟩, rfl⟩
                simpa using Subgroup.mem_bot.mp h1
              have h2 := congrArg (fun f : MulAut ↥(I 0) => (f ⟨u, hu⟩ : ↥(I 0))) hmem
              have h3 : ((actOnSub hAJ0 ⟨a, ha⟩ ⟨u, hu⟩ : ↥(I 0)) : W) = a u :=
                actOnSub_apply hAJ0 ⟨a, ha⟩ ⟨u, hu⟩
              have h4 : ((actOnSub hAJ0 ⟨a, ha⟩ ⟨u, hu⟩ : ↥(I 0)) : W) = u := by
                simpa using congrArg (fun z : ↥(I 0) => (z : W)) h2
              rwa [h3] at h4
            obtain ⟨H', π', hH'eq, hπ'coe, hreal'⟩ :=
              CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.exists_realizesVia_restrict hπ0
            have hNatH' : NatOmegaMinus H' ⊤ ⊥ 6 n :=
              ⟨by norm_num, K, hK, hKf, b, c, hcard, hpoly, π', hreal'⟩
            have hAimN : (actOnSub hAJ0).range ≤
                Subgroup.normalizer (H' : Set (MulAut ↥(I 0))) := by
              rw [hH'eq]
              exact actOnSub_range_le_normalizer hXJ0 hAJ0 hAX
            have hAim : (actOnSub hAJ0).range ∈ E3.aSet k
                (Subgroup.normalizer (H' : Set (MulAut ↥(I 0)))) := by
              rw [hH'eq]
              exact mem_aSet_actOnSub hA hAJ0
                (Y := Subgroup.normalizer ((actOnSub hXJ0).range : Set (MulAut ↥(I 0))))
                (actOnSub_range_le_normalizer hXJ0 hAJ0 hAX) hAJ0ne
            exact le_two_mul_of_mem_aSet_natOmegaMinus hNatH' le_rfl hAim
        ·
          exfalso
          have hex : ∃ a ∈ A, a ∉ stabSub (I 0) := by
            by_contra hcon
            push Not at hcon
            apply hA₁eq
            ext a
            constructor
            · intro ha
              exact hA₁le ha
            · intro ha
              exact Subgroup.mem_inf.mpr ⟨ha, hcon a ha⟩
          obtain ⟨a₀, ha₀A, ha₀not⟩ := hex
          have hmap₀ : (I 0).map a₀.toMonoidHom = I 1 := by
            rcases H.Pair.map_eq_or_map_eq hJinf hJsup hInv0 hInv1 hIrr0 hIrr1 hiso
              (hAX ha₀A) with h | h
            · exfalso
              exact ha₀not (CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mpr h)
            · exact h
          have hprod_of_swap : ∀ a ∈ A, (I 0).map a.toMonoidHom = I 1 →
              (I 0).map (a * a₀).toMonoidHom = I 0 := by
            intro a ha hamap1
            have ha2 : a ^ 2 = 1 := hA.2.2.1.2 a ha
            have ha1map : (I 1).map a.toMonoidHom = I 0 := by
              have h1 : (I 1).map a.toMonoidHom =
                  ((I 0).map a.toMonoidHom).map a.toMonoidHom := by rw [hamap1]
              rw [h1, Subgroup.map_map]
              have hcomp : (MulEquiv.toMonoidHom a).comp (MulEquiv.toMonoidHom a) =
                  (a * a).toMonoidHom := rfl
              rw [hcomp, ← pow_two, ha2]
              rw [show MulEquiv.toMonoidHom (1 : MulAut W) = MonoidHom.id W from rfl]
              simp
            calc (I 0).map (a * a₀).toMonoidHom
                = ((I 0).map a₀.toMonoidHom).map a.toMonoidHom := by
                  have hcomp : (a * a₀).toMonoidHom =
                      (MulEquiv.toMonoidHom a).comp (MulEquiv.toMonoidHom a₀) := rfl
                  rw [hcomp, Subgroup.map_map]
              _ = (I 1).map a.toMonoidHom := by rw [hmap₀]
              _ = I 0 := ha1map
          have hsupA : A₁ ⊔ Subgroup.zpowers a₀ = A := by
            refine le_antisymm (sup_le hA₁le (Subgroup.zpowers_le.mpr ha₀A)) ?_
            intro a ha
            by_cases hamap : (I 0).map a.toMonoidHom = I 0
            · exact Subgroup.mem_sup_left
                ⟨ha, CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mpr hamap⟩
            · have hamap1 : (I 0).map a.toMonoidHom = I 1 := by
                rcases H.Pair.map_eq_or_map_eq hJinf hJsup hInv0 hInv1 hIrr0 hIrr1 hiso
                  (hAX ha) with h | h
                · exact absurd h hamap
                · exact h
              have hmem : a * a₀ ∈ A₁ :=
                Subgroup.mem_inf.mpr ⟨A.mul_mem ha ha₀A,
                  CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mpr
                    (hprod_of_swap a ha hamap1)⟩
              have haeq : a = (a * a₀) * a₀ := by
                have ha₀2 : a₀ * a₀ = 1 := by
                  simpa [pow_two] using hA.2.2.1.2 a₀ ha₀A
                calc a = a * (a₀ * a₀) := by rw [ha₀2, mul_one]
                  _ = (a * a₀) * a₀ := by group
              rw [haeq]
              exact Subgroup.mul_mem_sup hmem (Subgroup.mem_zpowers a₀)
          have hdisj : A₁ ⊓ Subgroup.zpowers a₀ = ⊥ := by
            rw [eq_bot_iff]
            intro x hx
            have hx1 : x ∈ A₁ := (Subgroup.mem_inf.mp hx).1
            have hx2 : x ∈ Subgroup.zpowers a₀ := (Subgroup.mem_inf.mp hx).2
            have ha₀2 : a₀ * a₀ = 1 := by
              simpa [pow_two] using hA.2.2.1.2 a₀ ha₀A
            rcases CFSG.Quasithin.G64.eq_one_or_eq_of_mem_zpowers'
              (w := a₀) (x := x) (by simpa [pow_two] using ha₀2) hx2 with h | h
            · rw [h]
              exact Subgroup.one_mem _
            · exact absurd (Subgroup.mem_inf.mp (h ▸ hx1)).2 ha₀not
          have hz : Nat.card (Subgroup.zpowers a₀) = 2 := by
            rw [Nat.card_zpowers]
            have ha₀2 : a₀ ^ 2 = 1 := hA.2.2.1.2 a₀ ha₀A
            have ha₀ne : a₀ ≠ 1 := by
              intro h
              exact ha₀not (h ▸ (stabSub (I 0)).one_mem)
            exact orderOf_eq_prime ha₀2 ha₀ne
          have hcard : Nat.card A = Nat.card A₁ * 2 := by
            have hcomm : ∀ x ∈ A₁, ∀ y ∈ Subgroup.zpowers a₀, Commute x y := by
              intro x hx y hy
              exact hA.2.2.1.1 x (hA₁le hx) y (Subgroup.zpowers_le.mpr ha₀A hy)
            have h := CFSG.card_sup_eq_mul_of_commute A₁ (Subgroup.zpowers a₀) hcomm hdisj
            rw [hsupA, hz] at h
            exact h
          have hrel : A₁.relIndex A ≤ 2 := by
            have hrel2 : A₁.relIndex A = 2 := by
              have hmul := Subgroup.relIndex_mul_card A₁ A
              rw [inf_eq_left.mpr hA₁le, hcard] at hmul
              have hmul' : A₁.relIndex A * Nat.card A₁ = 2 * Nat.card A₁ := by
                rw [hmul, Nat.mul_comm]
              have hpos : 0 < Nat.card ↥A₁ := Nat.card_pos
              exact Nat.mul_right_cancel hpos hmul'
            omega
          have hlt : E3.mQuot A A₁ < k := by
            have hAp : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
            have hmq : E3.mQuot A A₁ ≤ 1 := by
              have h := E3.relIndex_eq_two_pow hAp A₁
              have hle2 : 2 ^ E3.mQuot A A₁ ≤ 2 := by rwa [← h]
              have hle2' : 2 ^ E3.mQuot A A₁ ≤ 2 ^ 1 := by simpa using hle2
              have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle2'
              simpa using this
            omega
          have hfixA : fixV A₁ = fixV A := hA.2.2.2 A₁ hA₁le hlt
          have hA₁el : IsElemAbelian2 A₁ :=
            ⟨fun x hx y hy => hA.2.2.1.1 x (hA₁le hx) y (hA₁le hy),
              fun x hx => hA.2.2.1.2 x (hA₁le hx)⟩
          have hA₁p : IsPGroup 2 ↥A₁ := E3.isPGroup_of_isElemAbelian2 hA₁el
          have hAJ0₁ : ∀ a ∈ A₁, ∀ u ∈ I 0, a u ∈ I 0 := by
            intro a ha u hu
            have hstab : a ∈ stabSub (I 0) := (Subgroup.mem_inf.mp ha).2
            have hmap : (I 0).map a.toMonoidHom = I 0 :=
              CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mp hstab
            rw [← hmap]
            exact ⟨u, hu, rfl⟩
          let B : Subgroup (MulAut ↥(I 0)) := (actOnSub hAJ0₁).range
          have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hBp : IsPGroup 2 ↥B := by
            obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hA₁p
            refine IsPGroup.of_card_dvd_pow (n := m) ?_
            rw [← hm]
            have h := Subgroup.card_map_dvd (H := ⊤) (f := actOnSub hAJ0₁)
            simpa [B, Subgroup.map_top] using h
          have hsq : ∀ v : ↥(I 0), v ^ 2 = 1 := sq_eq_one_of_natOmegaMinus hNat0c
          have hI0nt : Nontrivial ↥(I 0) := by
            obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIrr0.1
            exact ⟨⟨v, hv⟩, 1, fun h => hv1 h⟩
          have _ : Nontrivial ↥(I 0) := hI0nt
          obtain ⟨m, -, hm1, hmfix⟩ := CFSG.Quasithin.B1.exists_fixed_ne_one hsq hBp
            (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _) top_ne_bot
          have hmem : ((m : ↥(I 0)) : W) ∈ I 0 ⊓ fixV A₁ := by
            refine Subgroup.mem_inf.mpr ⟨m.2, ?_⟩
            change ∀ a ∈ A₁, a ((m : ↥(I 0)) : W) = ((m : ↥(I 0)) : W)
            intro a ha
            have hb : actOnSub hAJ0₁ ⟨a, ha⟩ ∈ B := ⟨⟨a, ha⟩, rfl⟩
            have hfixm := hmfix (actOnSub hAJ0₁ ⟨a, ha⟩) hb
            have hval : ((actOnSub hAJ0₁ ⟨a, ha⟩) m : W) = (m : W) :=
              congrArg Subtype.val hfixm
            rwa [actOnSub_apply] at hval
          have hfixbot : I 0 ⊓ fixV A₁ ≠ ⊥ := by
            intro hbot
            have hm : ((m : ↥(I 0)) : W) ∈ (⊥ : Subgroup W) := by
              rw [← hbot]
              exact hmem
            exact hm1 (Subtype.ext (Subgroup.mem_bot.mp hm))
          have hleA : fixV A ≤ fixV (Subgroup.zpowers a₀) := by
            intro v hv
            rw [mem_fixV] at hv ⊢
            intro b hb
            exact hv b (Subgroup.zpowers_le.mpr ha₀A hb)
          have hfixa₀ : I 0 ⊓ fixV (Subgroup.zpowers a₀) = ⊥ := by
            refine le_bot_iff.1 fun v hv => ?_
            have hv1 : v ∈ I 0 := (Subgroup.mem_inf.mp hv).1
            have hv2 : v ∈ fixV (Subgroup.zpowers a₀) := (Subgroup.mem_inf.mp hv).2
            have hfix : a₀ v = v := mem_fixV.mp hv2 a₀ (Subgroup.mem_zpowers a₀)
            have hav : a₀ v ∈ I 1 := by
              rw [← hmap₀]
              exact ⟨v, hv1, rfl⟩
            rw [hfix] at hav
            have hvbot : v ∈ I 0 ⊓ I 1 := ⟨hv1, hav⟩
            rw [hJinf] at hvbot
            exact Subgroup.mem_bot.mp hvbot
          have hle : I 0 ⊓ fixV A₁ ≤ ⊥ := by
            rw [hfixA]
            calc I 0 ⊓ fixV A ≤ I 0 ⊓ fixV (Subgroup.zpowers a₀) := inf_le_inf_left _ hleA
              _ = fixV (Subgroup.zpowers a₀) ⊓ I 0 := inf_comm _ _
              _ = ⊥ := by
                rw [inf_comm]
                exact hfixa₀
          exact hfixbot (le_bot_iff.1 hle)
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, csSup_empty]
      exact Nat.zero_le _
  · unfold E3.aParam
    rw [if_neg hev]
    exact Nat.zero_le _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
