module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDichotomy
import CFSG.Goldschmidt75.Sig32
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.SignalizerFunctorTheorem.Solvable.Bender.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

namespace A10Gen

variable {X : Type*} [Group X] [Finite X]

private theorem exists_hyperplane_centralizer_not_le {p : ℕ} (hp : p.Prime)
    {A U D : Subgroup X} (hA : CFSG.Open.IsElemAbelian p A) (hpA : p ≤ Nat.card A)
    (hAU : A ≤ Subgroup.normalizer (U : Set X)) (hU : Nat.Coprime p (Nat.card U))
    (hUD : ¬ U ≤ D) :
    ∃ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p A,
      ¬ U ⊓ Subgroup.centralizer (B : Set X) ≤ D := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
    hp hA hpA hAU hU
  by_contra h
  push Not at h
  apply hUD
  calc U = ⨆ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p A,
      U ⊓ Subgroup.centralizer (B : Set X) := hgen.symm
    _ ≤ D := iSup_le fun B => iSup_le fun hB => h B hB

theorem exists_centralizer_not_le {p : ℕ} (hp : p.Prime) {A U V D : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian p A) (hcard : p ^ 3 ≤ Nat.card A)
    (hUA : A ≤ Subgroup.normalizer (U : Set X)) (hVA : A ≤ Subgroup.normalizer (V : Set X))
    (hU : Nat.Coprime p (Nat.card U)) (hV : Nat.Coprime p (Nat.card V))
    (hUD : ¬ U ≤ D) (hVD : ¬ V ≤ D) :
    ∃ x ∈ A, x ≠ 1 ∧ ¬ U ⊓ Subgroup.centralizer ({x} : Set X) ≤ D ∧
      ¬ V ⊓ Subgroup.centralizer ({x} : Set X) ≤ D := by
  classical
  have hpA : p ≤ Nat.card A := (Nat.le_self_pow (by norm_num) p).trans hcard
  obtain ⟨B, hB, hUB⟩ := exists_hyperplane_centralizer_not_le hp hA hpA hUA hU hUD
  have hBA : B ≤ A := hB.1
  have hBelem : CFSG.Open.IsElemAbelian p B :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hBA
  have hcardB : p ^ 2 ≤ Nat.card B :=
    CFSG.SignalizerFunctorTheorem.Solvable.Bender.le_card_of_mem_hyperplanes
      (k := 2) hp hB (by simpa using hcard)
  have hpB : p ≤ Nat.card B := (Nat.le_self_pow (by norm_num) p).trans hcardB
  obtain ⟨C, hC, hVC⟩ :=
    exists_hyperplane_centralizer_not_le hp hBelem hpB (hBA.trans hVA) hV hVD
  have hCB : C ≤ B := hC.1
  have hcardC : p ≤ Nat.card C := by
    simpa using CFSG.SignalizerFunctorTheorem.Solvable.Bender.le_card_of_mem_hyperplanes
      (k := 1) hp hC (by simpa using hcardB)
  have hCbot : C ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardC
    have := hp.two_le
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCbot
  have hxC : (x : X) ∈ C := x.2
  have hx1' : (x : X) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxA : (x : X) ∈ A := hBA (hCB hxC)
  have hCBx : Subgroup.centralizer (B : Set X) ≤
      Subgroup.centralizer ({(x : X)} : Set X) :=
    Subgroup.centralizer_le fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hCB hxC
  have hCCx : Subgroup.centralizer (C : Set X) ≤
      Subgroup.centralizer ({(x : X)} : Set X) :=
    Subgroup.centralizer_le fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxC
  exact ⟨(x : X), hxA, hx1',
    fun hle => hUB (le_trans (le_inf inf_le_left (inf_le_right.trans hCBx)) hle),
    fun hle => hVC (le_trans (le_inf inf_le_left (inf_le_right.trans hCCx)) hle)⟩

end A10Gen

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem coprime_card_three_of_isPGroup_two {U : Subgroup G} (hU : IsPGroup 2 U) :
    Nat.Coprime (Nat.card U) 3 := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
  exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) hU
    Nat.prime_three (by norm_num)

private theorem le_normalizer_relPPrimeCore_three {A X : Subgroup G} (hAX : A ≤ X) :
    A ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore 3 X : Set G) :=
  hAX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (relPPrimeCore_le X)).mp
    (relPPrimeCore_normal Nat.prime_three X))

private theorem not_dvd_card_relPPrimeCore_three {X : Subgroup G} :
    ¬ 3 ∣ Nat.card ↥(CFSG.Open.relPPrimeCore 3 X) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_relPPrimeCore Nat.prime_three X)

private structure TwoLines (F : A10Frame c) (D₀ U V : Subgroup G) (x : G) : Prop where
  hxA : x ∈ F.A
  hx1 : x ≠ 1
  hUxnot : ¬ U ⊓ Subgroup.centralizer ({x} : Set G) ≤ D₀
  hVxnot : ¬ V ⊓ Subgroup.centralizer ({x} : Set G) ≤ D₀

private theorem exists_twoLines (F : A10Frame c) (hF : A10Facts F) {D₀ U V : Subgroup G}
    (hU2 : IsPGroup 2 U) (hV2 : IsPGroup 2 V)
    (hAU : F.A ≤ Subgroup.normalizer (U : Set G))
    (hAV : F.A ≤ Subgroup.normalizer (V : Set G))
    (hUnot : ¬ U ≤ D₀) (hVnot : ¬ V ≤ D₀) :
    ∃ x : G, TwoLines F D₀ U V x := by
  have hUcop : Nat.Coprime 3 (Nat.card U) :=
    Nat.Coprime.symm (coprime_card_three_of_isPGroup_two hU2)
  have hVcop : Nat.Coprime 3 (Nat.card V) :=
    Nat.Coprime.symm (coprime_card_three_of_isPGroup_two hV2)
  obtain ⟨x, hxA, hx1, hUxnot, hVxnot⟩ :=
    A10Gen.exists_centralizer_not_le (X := G) (p := 3) Nat.prime_three F.elemAbelian
      (by rw [F.card_A]; norm_num) hAU hAV hUcop hVcop hUnot hVnot
  exact ⟨x, ⟨hxA, hx1, hUxnot, hVxnot⟩⟩

private theorem exists_gt_of_not_maximal {F : A10Frame c} {D₀ : Subgroup G}
    (h : ¬ ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → D₀ ≤ S' → S' = D₀) :
    ∃ S : Subgroup G, S ≤ D.M ∧ IsPGroup 2 S ∧
      F.A ≤ Subgroup.normalizer (S : Set G) ∧ D₀ < S := by
  by_contra hcon
  apply h
  intro S' h1 h2 h3 h4
  by_contra hne
  exact hcon ⟨S', h1, h2, h3, lt_of_le_of_ne h4 (Ne.symm hne)⟩

private theorem exists_case_b (F : A10Frame c) (hF : A10Facts F)
    {T₀ D₀ H U : Subgroup G} (hHdef : H = Subgroup.normalizer (D₀ : Set G))
    (hAD₀ : F.A ≤ H) (hU2 : IsPGroup 2 U)
    (hAU : F.A ≤ Subgroup.normalizer (U : Set G))
    (hUH : U ≤ H) (hUT : U ≤ T₀) (hUnot : ¬ U ≤ D₀)
    (hnot : ¬ ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → D₀ ≤ S' → S' = D₀) :
    ∃ (S V : Subgroup G) (x : G), S ≤ D.M ∧ IsPGroup 2 S ∧
      F.A ≤ Subgroup.normalizer (S : Set G) ∧ D₀ < S ∧ V = S ⊓ H ∧
      TwoLines F D₀ U V x := by
  obtain ⟨S, hSM, hS2, hAS, hD₀S⟩ := exists_gt_of_not_maximal hnot
  let V : Subgroup G := S ⊓ H
  have hV2 : IsPGroup 2 V := hS2.to_le inf_le_left
  have hAV : F.A ≤ Subgroup.normalizer (V : Set G) := by
    have h := CFSG.Goldschmidt75.le_normalizer_inf_of_le hAS
      (hAD₀.trans Subgroup.le_normalizer)
    simpa [V] using h
  have hVlt : D₀ < V := by
    have h := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 2) hS2 hD₀S
    rw [← hHdef] at h
    simpa [V] using h
  obtain ⟨x, hx⟩ := exists_twoLines F hF hU2 hV2 hAU hAV hUnot (not_le_of_gt hVlt)
  exact ⟨S, V, x, hSM, hS2, hAS, hD₀S, rfl, hx⟩

private theorem exists_conj_le_invariant_sylow {A Y U V : Subgroup G}
    (hA : IsPGroup 3 A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hY : ¬ 3 ∣ Nat.card Y) (hUY : U ≤ Y) (hVY : V ≤ Y)
    (hU : IsPGroup 2 U) (hV : IsPGroup 2 V)
    (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ n ∈ Y ⊓ Subgroup.centralizer (A : Set G), ∃ W : Subgroup G, W ≤ Y ∧
      A ≤ Subgroup.normalizer (W : Set G) ∧ IsPGroup 2 W ∧
      U.map (MulAut.conj n).toMonoidHom ≤ W ∧ V ≤ W := by
  obtain ⟨S₁, hS₁, hUS₁, hAS₁⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA hY hAY hUY hU hAU
  obtain ⟨S₂, hS₂, hVS₂, hAS₂⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA hY hAY hVY hV hAV
  obtain ⟨n, hn, hnS⟩ :=
    CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows (r := 3) (q := 2)
      Nat.prime_three Nat.prime_two hA hY hAY hS₁ hS₂ hAS₁ hAS₂
  exact ⟨n, hn, S₂, hS₂.1, hAS₂, hS₂.2.1,
    by rw [hnS]; exact Subgroup.map_mono hUS₁, hVS₂⟩

private theorem false_of_invariant_sylow (F : A10Frame c) (hF : A10Facts F)
    {T₀ D₀ S U V W : Subgroup G} {n x : G}
    (hkey : ∀ T' : Subgroup G, IsPGroup 2 T' →
      F.A ≤ Subgroup.normalizer (T' : Set G) →
      Nat.card ↥D₀ < Nat.card ↥(T' ⊓ D.M) → T' ≤ D.M)
    (hD₀eq : D₀ = T₀ ⊓ D.M)
    (hD₀M : D₀ ≤ D.M) (hD₀2 : IsPGroup 2 D₀)
    (hAD₀ : F.A ≤ Subgroup.normalizer (D₀ : Set G))
    (hSM : S ≤ D.M)
    (hUxnot : ¬ U ⊓ Subgroup.centralizer ({x} : Set G) ≤ D₀)
    (hVxnot : ¬ V ⊓ Subgroup.centralizer ({x} : Set G) ≤ D₀)
    (hUxT : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ T₀)
    (hVxS : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ S)
    (hWH : W ≤ Subgroup.normalizer (D₀ : Set G))
    (hW2 : IsPGroup 2 W) (hAW : F.A ≤ Subgroup.normalizer (W : Set G))
    (hn : n ∈ D.M)
    (hUxnW : (U ⊓ Subgroup.centralizer ({x} : Set G)).map
      (MulAut.conj n).toMonoidHom ≤ W)
    (hVxW : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ W) : False := by
  let T' : Subgroup G := D₀ ⊔ W
  have hT'2 : IsPGroup 2 T' := hD₀2.to_sup_of_normal_left' hW2 hWH
  have hAT' : F.A ≤ Subgroup.normalizer (T' : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_sup hAD₀ hAW
  have hVxT' : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ T' :=
    hVxW.trans le_sup_right
  have hVxM : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ D.M := hVxS.trans hSM
  have hD₀Vx : D₀ < D₀ ⊔ (V ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    exact hVxnot (h.symm ▸ le_sup_right)
  have hsup : D₀ ⊔ (V ⊓ Subgroup.centralizer ({x} : Set G)) ≤ T' ⊓ D.M :=
    le_inf (sup_le le_sup_left hVxT') (sup_le hD₀M hVxM)
  have hcard : Nat.card ↥D₀ < Nat.card ↥(T' ⊓ D.M) := by
    have h1 : Nat.card ↥D₀ <
        Nat.card ↥(D₀ ⊔ (V ⊓ Subgroup.centralizer ({x} : Set G))) := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le (le_of_lt hD₀Vx)) ?_
      intro heq
      exact hD₀Vx.ne (Subgroup.eq_of_le_of_card_ge (le_of_lt hD₀Vx)
        (le_of_eq heq.symm))
    exact lt_of_lt_of_le h1 (Subgroup.card_le_of_le hsup)
  have hT'M : T' ≤ D.M := hkey T' hT'2 hAT' hcard
  have hWM : W ≤ D.M := le_sup_right.trans hT'M
  have hUxM : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ D.M := by
    intro u hu
    have h1 : n * u * n⁻¹ ∈ W := by
      have := hUxnW (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
      simpa [MulAut.conj_apply] using this
    have heq : u = n⁻¹ * (n * u * n⁻¹) * n := by group
    rw [heq]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hn) (hWM h1)) hn
  exact hUxnot (by rw [hD₀eq]; exact le_inf hUxT hUxM)

private theorem false_of_core_y (F : A10Frame c) (hF : A10Facts F)
    {T₀ D₀ S U V Y : Subgroup G} {x : G}
    (hkey : ∀ T' : Subgroup G, IsPGroup 2 T' →
      F.A ≤ Subgroup.normalizer (T' : Set G) →
      Nat.card ↥D₀ < Nat.card ↥(T' ⊓ D.M) → T' ≤ D.M)
    (hD₀eq : D₀ = T₀ ⊓ D.M)
    (hD₀M : D₀ ≤ D.M) (hD₀2 : IsPGroup 2 D₀)
    (hAD₀ : F.A ≤ Subgroup.normalizer (D₀ : Set G))
    (hSM : S ≤ D.M)
    (hUxnot : ¬ U ⊓ Subgroup.centralizer ({x} : Set G) ≤ D₀)
    (hVxnot : ¬ V ⊓ Subgroup.centralizer ({x} : Set G) ≤ D₀)
    (hUxT : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ T₀)
    (hVxS : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ S)
    (hUx2 : IsPGroup 2 ↥(U ⊓ Subgroup.centralizer ({x} : Set G)))
    (hVx2 : IsPGroup 2 ↥(V ⊓ Subgroup.centralizer ({x} : Set G)))
    (hAUx : F.A ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G))
    (hAVx : F.A ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G))
    (hUxY : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ Y)
    (hVxY : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ Y)
    (hYH : Y ≤ Subgroup.normalizer (D₀ : Set G))
    (hYnotdvd : ¬ 3 ∣ Nat.card Y)
    (hAY : F.A ≤ Subgroup.normalizer (Y : Set G)) : False := by
  obtain ⟨n, hn, W, hWY, hAW, hW2, hUxnW, hVxW⟩ :=
    exists_conj_le_invariant_sylow F.elemAbelian.isPGroup hAY hYnotdvd hUxY hVxY
      hUx2 hVx2 hAUx hAVx
  have hnM : n ∈ D.M := hF.normalizer_A (Subgroup.centralizer_le_normalizer _ hn.2)
  exact false_of_invariant_sylow F hF hkey hD₀eq hD₀M hD₀2 hAD₀ hSM hUxnot hVxnot hUxT
    hVxS (hWY.trans hYH) hW2 hAW hnM hUxnW hVxW

private structure CoreData (F : A10Frame c) (T₀ D₀ H U V S : Subgroup G) (x : G) : Prop where
  hAxC : F.A ≤ Subgroup.centralizer ({x} : Set G)
  hUx2 : IsPGroup 2 ↥(U ⊓ Subgroup.centralizer ({x} : Set G))
  hVx2 : IsPGroup 2 ↥(V ⊓ Subgroup.centralizer ({x} : Set G))
  hAUx : F.A ≤ Subgroup.normalizer
    ((U ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G)
  hAVx : F.A ≤ Subgroup.normalizer
    ((V ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G)
  hUxX : U ⊓ Subgroup.centralizer ({x} : Set G) ≤
    H ⊓ Subgroup.centralizer ({x} : Set G)
  hVxX : V ⊓ Subgroup.centralizer ({x} : Set G) ≤
    H ⊓ Subgroup.centralizer ({x} : Set G)
  hUxT : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ T₀
  hVxS : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ S
  hUxY : U ⊓ Subgroup.centralizer ({x} : Set G) ≤
    CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G))
  hVxY : V ⊓ Subgroup.centralizer ({x} : Set G) ≤
    CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G))

private theorem exists_coreData (F : A10Frame c) (hF : A10Facts F)
    {T₀ D₀ H U S V : Subgroup G} {x : G} (hx : TwoLines F D₀ U V x)
    (hHdef : H = Subgroup.normalizer (D₀ : Set G)) (hAH : F.A ≤ H)
    (hAD₀ : F.A ≤ Subgroup.normalizer (D₀ : Set G))
    (hS2 : IsPGroup 2 S) (hAS : F.A ≤ Subgroup.normalizer (S : Set G))
    (hVdef : V = S ⊓ H) (hU2 : IsPGroup 2 U)
    (hAU : F.A ≤ Subgroup.normalizer (U : Set G))
    (hUH : U ≤ H) (hUT : U ≤ T₀)
    (hcore : ∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({x} : Set G) →
      F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G))) :
    CoreData F T₀ D₀ H U V S x := by
  have hVS : V ≤ S := by rw [hVdef]; exact inf_le_left
  have hVH : V ≤ H := by rw [hVdef]; exact inf_le_right
  have hV2 : IsPGroup 2 V := hS2.to_le hVS
  have hUx2 : IsPGroup 2 ↥(U ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hU2.to_le inf_le_left
  have hVx2 : IsPGroup 2 ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hV2.to_le inf_le_left
  have hAxC : F.A ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (F.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx.hxA⟩)
  have hUxT : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ T₀ :=
    inf_le_left.trans hUT
  have hVxS : V ⊓ Subgroup.centralizer ({x} : Set G) ≤ S :=
    inf_le_left.trans hVS
  have hUxX : U ⊓ Subgroup.centralizer ({x} : Set G) ≤
      H ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf (inf_le_left.trans hUH) inf_le_right
  have hVxX : V ⊓ Subgroup.centralizer ({x} : Set G) ≤
      H ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf (inf_le_left.trans hVH) inf_le_right
  have hAV : F.A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef, hHdef]
    exact CFSG.Goldschmidt75.le_normalizer_inf_of_le hAS
      (hAD₀.trans Subgroup.le_normalizer)
  have hAUx : F.A ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_inf_of_le hAU
      (hAxC.trans Subgroup.le_normalizer)
  have hAVx : F.A ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_inf_of_le hAV
      (hAxC.trans Subgroup.le_normalizer)
  have hUxY : U ⊓ Subgroup.centralizer ({x} : Set G) ≤
      CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hcore _ hUxX hAUx (coprime_card_three_of_isPGroup_two hUx2)
  have hVxY : V ⊓ Subgroup.centralizer ({x} : Set G) ≤
      CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hcore _ hVxX hAVx (coprime_card_three_of_isPGroup_two hVx2)
  exact ⟨hAxC, hUx2, hVx2, hAUx, hAVx, hUxX, hVxX, hUxT, hVxS, hUxY, hVxY⟩

private theorem false_of_core (F : A10Frame c) (hF : A10Facts F)
    {T₀ D₀ H U S V : Subgroup G} {x : G} (hx : TwoLines F D₀ U V x)
    (hkey : ∀ T' : Subgroup G, IsPGroup 2 T' →
      F.A ≤ Subgroup.normalizer (T' : Set G) →
      Nat.card ↥D₀ < Nat.card ↥(T' ⊓ D.M) → T' ≤ D.M)
    (hD₀eq : D₀ = T₀ ⊓ D.M)
    (hD₀M : D₀ ≤ D.M) (hD₀2 : IsPGroup 2 D₀)
    (hAD₀ : F.A ≤ Subgroup.normalizer (D₀ : Set G))
    (hHdef : H = Subgroup.normalizer (D₀ : Set G))
    (hAH : F.A ≤ H)
    (hSM : S ≤ D.M) (hS2 : IsPGroup 2 S)
    (hAS : F.A ≤ Subgroup.normalizer (S : Set G))
    (hVdef : V = S ⊓ H) (hU2 : IsPGroup 2 U)
    (hAU : F.A ≤ Subgroup.normalizer (U : Set G))
    (hUH : U ≤ H) (hUT : U ≤ T₀)
    (hcore : ∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({x} : Set G) →
      F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G))) :
    False := by
  obtain ⟨hAxC, hUx2, hVx2, hAUx, hAVx, hUxX, hVxX, hUxT, hVxS, hUxY, hVxY⟩ :=
    exists_coreData F hF hx hHdef hAH hAD₀ hS2 hAS hVdef hU2 hAU hUH hUT hcore
  have hYH : CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      Subgroup.normalizer (D₀ : Set G) :=
    (relPPrimeCore_le _).trans (inf_le_left.trans (le_of_eq hHdef))
  have hYnotdvd : ¬ 3 ∣ Nat.card
      ↥(CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G))) :=
    not_dvd_card_relPPrimeCore_three
  have hAY : F.A ≤ Subgroup.normalizer
      (CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) :=
    le_normalizer_relPPrimeCore_three (le_inf hAH hAxC)
  exact false_of_core_y F hF hkey hD₀eq hD₀M hD₀2 hAD₀ hSM hx.hUxnot hx.hVxnot hUxT hVxS
    hUx2 hVx2 hAUx hAVx hUxY hVxY hYH hYnotdvd hAY

private theorem false_of_case_b (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {T₀ D₀ H U : Subgroup G}
    (hkey : ∀ T' : Subgroup G, IsPGroup 2 T' →
      F.A ≤ Subgroup.normalizer (T' : Set G) →
      Nat.card ↥D₀ < Nat.card ↥(T' ⊓ D.M) → T' ≤ D.M)
    (hD₀eq : D₀ = T₀ ⊓ D.M)
    (hD₀M : D₀ ≤ D.M) (hD₀2 : IsPGroup 2 D₀)
    (hAD₀ : F.A ≤ Subgroup.normalizer (D₀ : Set G))
    (hHdef : H = Subgroup.normalizer (D₀ : Set G))
    (hAH : F.A ≤ H) (hU2 : IsPGroup 2 U)
    (hAU : F.A ≤ Subgroup.normalizer (U : Set G))
    (hUH : U ≤ H) (hUT : U ≤ T₀)
    (hex : ∃ (S V : Subgroup G) (x : G), S ≤ D.M ∧ IsPGroup 2 S ∧
      F.A ≤ Subgroup.normalizer (S : Set G) ∧ D₀ < S ∧ V = S ⊓ H ∧
      TwoLines F D₀ U V x) : False := by
  obtain ⟨S, V, x, hSM, hS2, hAS, hD₀S, hVdef, hx⟩ := hex
  rcases F.dichotomy_centralizer hF hC (H := H) hAH hx.hxA hx.hx1 with
    hcore | ⟨-, hXM, -⟩
  · exact false_of_core F hF hx hkey hD₀eq hD₀M hD₀2 hAD₀ hHdef hAH hSM hS2 hAS hVdef
      hU2 hAU hUH hUT hcore
  · have hUxT : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ T₀ :=
      inf_le_left.trans hUT
    have hUxH : U ⊓ Subgroup.centralizer ({x} : Set G) ≤ H :=
      inf_le_left.trans hUH
    exact hx.hUxnot (by
      rw [hD₀eq]
      exact le_inf hUxT ((le_inf hUxH inf_le_right).trans hXM))

private theorem exists_maximal_bad (F : A10Frame c) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hAT : F.A ≤ Subgroup.normalizer (T : Set G)) (hTM : ¬ T ≤ D.M) :
    ∃ T₀ : Subgroup G, IsPGroup 2 T₀ ∧ F.A ≤ Subgroup.normalizer (T₀ : Set G) ∧ ¬ T₀ ≤ D.M ∧
      ∀ T' : Subgroup G, IsPGroup 2 T' → F.A ≤ Subgroup.normalizer (T' : Set G) →
        Nat.card ↥(T₀ ⊓ D.M) < Nat.card ↥(T' ⊓ D.M) → T' ≤ D.M := by
  classical
  let bad : Set (Subgroup G) :=
    {S | IsPGroup 2 S ∧ F.A ≤ Subgroup.normalizer (S : Set G) ∧ ¬ S ≤ D.M}
  have hbadne : bad.Nonempty := ⟨T, hT, hAT, hTM⟩
  have hbadfin : bad.Finite := Set.toFinite bad
  obtain ⟨T₀, hT₀max⟩ := hbadfin.exists_maximalFor
    (fun S : Subgroup G => Nat.card ↥(S ⊓ D.M)) bad hbadne
  have hT₀bad : T₀ ∈ bad := hT₀max.prop
  obtain ⟨hT₀2, hAT₀, hT₀M⟩ := hT₀bad
  refine ⟨T₀, hT₀2, hAT₀, hT₀M, fun T' h2 hN' hlt => ?_⟩
  by_contra hbad'
  exact (not_le_of_gt hlt) (hT₀max.le (show T' ∈ bad from ⟨h2, hN', hbad'⟩))

theorem le_M_of_isPGroup_two_of_normalizer_le (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    (hN : ∀ S : Subgroup G, S ≤ D.M → IsPGroup 2 S → F.A ≤ Subgroup.normalizer (S : Set G) →
      (∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
        F.A ≤ Subgroup.normalizer (S' : Set G) → S ≤ S' → S' = S) →
      Subgroup.normalizer (S : Set G) ≤ D.M)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hAT : F.A ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ D.M := by
  classical
  by_contra hTM
  obtain ⟨T₀, hT₀2, hAT₀, hT₀M, hkey⟩ := exists_maximal_bad F hT hAT hTM
  let D₀ : Subgroup G := T₀ ⊓ D.M
  let H : Subgroup G := Subgroup.normalizer (D₀ : Set G)
  let U : Subgroup G := T₀ ⊓ H
  have hD₀M : D₀ ≤ D.M := inf_le_right
  have hD₀2 : IsPGroup 2 D₀ := hT₀2.to_le inf_le_left
  have hAD₀ : F.A ≤ Subgroup.normalizer (D₀ : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_inf_of_le hAT₀
      (F.A_le_M.trans Subgroup.le_normalizer)
  have hAH : F.A ≤ H := hAD₀
  have hD₀lt : D₀ < T₀ := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    exact hT₀M (h ▸ hD₀M)
  have hU2 : IsPGroup 2 U := hT₀2.to_le inf_le_left
  have hAU : F.A ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_inf_of_le hAT₀
      (hAH.trans Subgroup.le_normalizer)
  have hUlt : D₀ < U :=
    CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 2) hT₀2 hD₀lt
  have hUnot : ¬ U ≤ D₀ := not_le_of_gt hUlt
  by_cases hmaxD₀ : ∀ S' : Subgroup G, S' ≤ D.M → IsPGroup 2 S' →
      F.A ≤ Subgroup.normalizer (S' : Set G) → D₀ ≤ S' → S' = D₀
  · have hHle : H ≤ D.M := hN D₀ hD₀M hD₀2 hAD₀ hmaxD₀
    exact hUnot (le_inf inf_le_left (inf_le_right.trans hHle))
  · exact false_of_case_b F hF hC hkey rfl hD₀M hD₀2 hAD₀ rfl hAH hU2 hAU inf_le_right
      inf_le_left (exists_case_b F hF rfl hAH hU2 hAU inf_le_right inf_le_left hUnot hmaxD₀)

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
