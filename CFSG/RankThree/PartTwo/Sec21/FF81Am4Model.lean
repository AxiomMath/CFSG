module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Defs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
import CFSG.ClassicalInvolution.WeakCT.DLLevis
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42S6
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.ClassicalInvolution.WeakCT.Sides
public import CFSG.ClassicalInvolution.WeakCT.SpPair

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.WeakCT (blk blk_zero_tv01 blk_zero_tv10 blk_one_tv01 blk_one_tv10)
open CFSG.Timmesfeld (tv)
open CFSG.Timmesfeld.LevisExtras (tv01_eq_sl2Upper tv10_eq_sl2Lower)
open scoped MatrixGroups

namespace Am4

abbrev K3 : Type := StatedSp 3 (ZMod 2)

abbrev K4 : Type := StatedSp 4 (ZMod 2)

noncomputable def ι₀ : SL(2, ZMod 2) →* K3 :=
  shortBlock (ZMod 2) (show (0 : Fin 3) ≠ 1 by decide)

noncomputable def ι₁ : SL(2, ZMod 2) →* K3 :=
  shortBlock (ZMod 2) (show (1 : Fin 3) ≠ 2 by decide)

noncomputable def ι₂ : SL(2, ZMod 2) →* K3 := longBlock (ZMod 2) 3 2

theorem ι₀_injective : Function.Injective ι₀ := shortBlock_injective _

theorem ι₁_injective : Function.Injective ι₁ := shortBlock_injective _

theorem ι₂_injective : Function.Injective ι₂ := longBlock_injective 2

theorem iSup_nodes_eq_top : ι₀.range ⊔ ι₁.range ⊔ ι₂.range = ⊤ := by
  have h := CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_eq_top_of_ct
    (D := CFSG.LieType.Universal.Symplectic.rootDatum 3 (ZMod 2))
    (CFSG.LieType.Universal.Symplectic.isCTGroupDatum 3 (ZMod 2)) rfl
  have e0 : ι₀.range = CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Symplectic.rootGroup 3 (ZMod 2)) (0 : Fin 3) :=
    range_shortBlock_eq_rankOne (k := (0 : Fin 3)) (by decide)
  have e1 : ι₁.range = CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Symplectic.rootGroup 3 (ZMod 2)) (1 : Fin 3) :=
    range_shortBlock_eq_rankOne (k := (1 : Fin 3)) (by decide)
  have e2 : ι₂.range = CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Symplectic.rootGroup 3 (ZMod 2)) (2 : Fin 3) :=
    range_longBlock_eq_rankOne (k := (2 : Fin 3)) (by decide)
  rw [e0, e1, e2]
  rw [← h]
  apply le_antisymm
  · exact sup_le (sup_le (le_iSup (fun k => CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Symplectic.rootGroup 3 (ZMod 2)) k) 0)
      (le_iSup (fun k => CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Symplectic.rootGroup 3 (ZMod 2)) k) 1))
      (le_iSup (fun k => CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Universal.Symplectic.rootGroup 3 (ZMod 2)) k) 2)
  · refine iSup_le fun k => ?_
    fin_cases k
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right

open CFSG.ClassicalInvolution.WeakCT in
theorem exists_kappa : ∃ κ : SL(3, ZMod 2) →* K3,
    κ.comp (blk (ZMod 2) 0) = ι₁ ∧ κ.comp (blk (ZMod 2) 1) = ι₀ := by
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (CFSG.LieType.Universal.Symplectic.rootDatum 3 (ZMod 2)).isFiniteType
    (Dv := (CFSG.LieType.Universal.Symplectic.rootDatum 3 (ZMod 2)).divisible) rfl
  have hE := CFSG.LieType.Steinberg.Sp.chevalleyExtras (by omega : 2 ≤ 3) O
    CFSG.LieType.Steinberg.Sp.commC (CFSG.LieType.Steinberg.Sp.commutatorFormula O)
  obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE
    (rfl : (CFSG.LieType.Universal.Symplectic.rootDatum 3 (ZMod 2)).divisible = ∅)
    (i := (⟨1, by decide⟩ : Fin 3)) (j := (⟨0, by decide⟩ : Fin 3))
    (k := (⟨2, by decide⟩ : Fin 3))
    (by intro h; exact absurd (congrArg Fin.val h) (by decide))
    (by simp [CFSG.LieType.Universal.Symplectic.rootDatum,
      CFSG.LieType.Universal.Symplectic.cartanC])
    (by simp [CFSG.LieType.Universal.Symplectic.rootDatum,
      CFSG.LieType.Universal.Symplectic.cartanC])
    (by simp [CFSG.LieType.Universal.Symplectic.rootDatum,
      CFSG.LieType.Universal.Symplectic.cartanC])
  refine ⟨emb, ?_, ?_⟩
  · refine shortBlock_eq_of_eq_x (k := (1 : Fin 3)) (by decide) _ (fun c => ?_) (fun c => ?_)
    · rw [MonoidHom.comp_apply, ← tv01_eq_sl2Upper, blk_zero_tv01]
      exact (hv c).1
    · rw [MonoidHom.comp_apply, ← tv10_eq_sl2Lower, blk_zero_tv10]
      exact (hv c).2.1
  · refine shortBlock_eq_of_eq_x (k := (0 : Fin 3)) (by decide) _ (fun c => ?_) (fun c => ?_)
    · rw [MonoidHom.comp_apply, ← tv01_eq_sl2Upper, blk_one_tv01]
      exact (hv c).2.2.1
    · rw [MonoidHom.comp_apply, ← tv10_eq_sl2Lower, blk_one_tv10]
      exact (hv c).2.2.2

noncomputable def lam : StatedSp 2 (ZMod 2) →* K3 :=
  spEmbed (K := ZMod 2) (pairMap (1 : Fin 3) 2) (pairMap_injective (by decide))

theorem lam_comp_spBlock_zero :
    lam.comp (CFSG.ClassicalInvolution.WeakCT.spBlock (ZMod 2) 0) = ι₁ := by
  rw [CFSG.ClassicalInvolution.WeakCT.spBlock_zero_eq_shortBlock]
  exact spEmbed_comp_shortBlock (K := ZMod 2) (i := (1 : Fin 3)) (j := 2) (by decide)

theorem lam_comp_spBlock_one :
    lam.comp (CFSG.ClassicalInvolution.WeakCT.spBlock (ZMod 2) 1) = ι₂ := by
  rw [CFSG.ClassicalInvolution.WeakCT.spBlock_one_eq_longBlock]
  exact spEmbed_comp_longBlock (K := ZMod 2) (i := (1 : Fin 3)) (j := 2) (by decide)

noncomputable def initEmb : K3 →* K4 :=
  spEmbed (K := ZMod 2) (Fin.castSucc : Fin 3 → Fin 4) (Fin.castSucc_injective 3)

noncomputable def shiftEmb : K3 →* K4 :=
  spEmbed (K := ZMod 2) (Fin.succ : Fin 3 → Fin 4) (Fin.succ_injective 3)

theorem initEmb_injective : Function.Injective initEmb := spEmbed_injective _

theorem range_initEmb : initEmb.range = Svec := by
  rw [initEmb, range_spEmbed]
  change _ = complSp (ZMod 2) 3
  rw [complSp]
  congr 1
  ext x
  rcases x with i | i <;> fin_cases i <;> simp [coords] <;> decide

theorem range_shiftEmb : shiftEmb.range = complSp (ZMod 2) (0 : Fin 4) := by
  rw [shiftEmb, range_spEmbed, complSp]
  congr 1
  ext x
  rcases x with i | i <;> fin_cases i <;> simp [coords] <;> decide

theorem initEmb_longBlock (k : Fin 3) (A : SL(2, ZMod 2)) :
    initEmb (longBlock (ZMod 2) 3 k A) = longBlock (ZMod 2) 4 k.castSucc A :=
  spEmbed_longBlock _ k A

theorem shiftEmb_longBlock (k : Fin 3) (A : SL(2, ZMod 2)) :
    shiftEmb (longBlock (ZMod 2) 3 k A) = longBlock (ZMod 2) 4 k.succ A :=
  spEmbed_longBlock _ k A

theorem initEmb_nsElt (k : Fin 3) : initEmb (nsElt (K := ZMod 2) (n := 3) k) =
    nsElt (K := ZMod 2) (n := 4) k.castSucc :=
  initEmb_longBlock k _

noncomputable def tM : K3 := longBlock (ZMod 2) 3 2 (sl2Upper 1)

theorem shiftEmb_tM : shiftEmb tM = tvec := by
  rw [tM, shiftEmb_longBlock]
  exact longBlock_sl2Upper 3 1

theorem initEmb_mem_Svec (x : K3) : initEmb x ∈ Svec := by
  rw [← range_initEmb]
  exact ⟨x, rfl⟩

theorem Svec_le_Pvec : Svec ≤ Pvec := by
  intro x hx
  have h := complSp_le_centralizer_longRootSp2 (K := ZMod 2) (n := 4) 3 hx
  have hmem : tvec ∈ longRootSp2 (ZMod 2) 4 3 :=
    ⟨sl2Upper 1, longBlock_sl2Upper 3 1⟩
  have := Subgroup.mem_centralizer_iff.mp h tvec hmem
  exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm

theorem initEmb_mem_Pvec (x : K3) : initEmb x ∈ Pvec := Svec_le_Pvec (initEmb_mem_Svec x)

section Compose

open Matrix

theorem spIncl_mul_spIncl {m n p : ℕ} (σ : Fin n → Fin p) (τ : Fin m → Fin n) :
    spIncl (K := ZMod 2) σ * spIncl (K := ZMod 2) τ = spIncl (K := ZMod 2) (σ ∘ τ) := by
  ext a c
  simp only [spIncl_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Sum.map τ τ c)]
  · simp [Sum.map_map]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem spEmbed_spEmbed {m n p : ℕ} {σ : Fin n → Fin p} {τ : Fin m → Fin n}
    (hσ : Function.Injective σ) (hτ : Function.Injective τ) (g : StatedSp m (ZMod 2)) :
    spEmbed σ hσ (spEmbed τ hτ g) = spEmbed (σ ∘ τ) (hσ.comp hτ) g := by
  refine CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective ?_
  rw [mat_spEmbed, mat_spEmbed, mat_spEmbed]
  simp only [spEmbedMat]
  have hPP : (spIncl (K := ZMod 2) σ)ᵀ * spIncl (K := ZMod 2) σ = 1 := spIncl_transpose_mul hσ
  rw [← spIncl_mul_spIncl σ τ, Matrix.transpose_mul]
  have e : (1 + spIncl (K := ZMod 2) τ * (CFSG.LieType.Universal.Symplectic.SpExtras.mat m
      (ZMod 2) g - 1) * (spIncl (K := ZMod 2) τ)ᵀ - 1 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) = spIncl (K := ZMod 2) τ *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat m (ZMod 2) g - 1) *
      (spIncl (K := ZMod 2) τ)ᵀ := by
    abel
  rw [e]
  simp only [Matrix.mul_assoc]

theorem spEmbed_congr {m n : ℕ} {σ σ' : Fin m → Fin n} (h : σ = σ') (hσ : Function.Injective σ)
    (hσ' : Function.Injective σ') (g : StatedSp m (ZMod 2)) :
    spEmbed σ hσ g = spEmbed σ' hσ' g := by
  subst h
  rfl

end Compose

theorem spEmbed_shortBlock {m n : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    {i j : Fin m} (hij : i ≠ j) (A : SL(2, ZMod 2)) :
    spEmbed σ hσ (shortBlock (ZMod 2) hij A) =
      shortBlock (ZMod 2) (fun h => hij (hσ h) : σ i ≠ σ j) A := by
  have hle : Subgroup.closure (Set.range (sl2Upper (k := ZMod 2)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus ((spEmbed σ hσ).comp (shortBlock (ZMod 2) hij))
        (shortBlock (ZMod 2) (fun h => hij (hσ h) : σ i ≠ σ j)) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show spEmbed σ hσ (shortBlock (ZMod 2) hij (sl2Upper c)) =
        shortBlock (ZMod 2) (fun h => hij (hσ h) : σ i ≠ σ j) (sl2Upper c)
      rw [shortBlock_sl2Upper, shortBlock_sl2Upper, spEmbed_elt_difference]
    · show spEmbed σ hσ (shortBlock (ZMod 2) hij (sl2Lower c)) =
        shortBlock (ZMod 2) (fun h => hij (hσ h) : σ i ≠ σ j) (sl2Lower c)
      rw [shortBlock_sl2Lower, shortBlock_sl2Lower, spEmbed_elt_difference]
  exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A)

noncomputable def embS : StatedSp 2 (ZMod 2) →* K3 :=
  spEmbed (K := ZMod 2) (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2)

noncomputable def embS' : StatedSp 2 (ZMod 2) →* K3 :=
  spEmbed (K := ZMod 2) (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)

theorem embS_injective : Function.Injective embS := spEmbed_injective _

theorem embS'_injective : Function.Injective embS' := spEmbed_injective _

theorem shiftEmb_embS (z : StatedSp 2 (ZMod 2)) : shiftEmb (embS z) = initEmb (embS' z) := by
  unfold shiftEmb embS initEmb embS'
  rw [spEmbed_spEmbed, spEmbed_spEmbed]
  exact spEmbed_congr (funext fun i => (Fin.succ_castSucc i)) _ _ _

theorem range_embS : embS.range = complSp (ZMod 2) (2 : Fin 3) := by
  rw [embS, range_spEmbed, complSp]
  congr 1
  ext x
  rcases x with i | i <;> fin_cases i <;> simp [coords] <;> decide

theorem range_embS' : embS'.range = complSp (ZMod 2) (0 : Fin 3) := by
  rw [embS', range_spEmbed, complSp]
  congr 1
  ext x
  rcases x with i | i <;> fin_cases i <;> simp [coords] <;> decide

theorem embS_longBlock (k : Fin 2) (A : SL(2, ZMod 2)) :
    embS (longBlock (ZMod 2) 2 k A) = longBlock (ZMod 2) 3 k.castSucc A :=
  spEmbed_longBlock _ k A

theorem embS'_longBlock (k : Fin 2) (A : SL(2, ZMod 2)) :
    embS' (longBlock (ZMod 2) 2 k A) = longBlock (ZMod 2) 3 k.succ A :=
  spEmbed_longBlock _ k A

theorem embS_nsElt (k : Fin 2) : embS (nsElt (K := ZMod 2) (n := 2) k) =
    nsElt (K := ZMod 2) (n := 3) k.castSucc :=
  embS_longBlock k _

theorem embS'_nsElt (k : Fin 2) : embS' (nsElt (K := ZMod 2) (n := 2) k) =
    nsElt (K := ZMod 2) (n := 3) k.succ :=
  embS'_longBlock k _

theorem embS_shortBlock (A : SL(2, ZMod 2)) :
    embS (shortBlock (ZMod 2) (zero_ne_one : (0 : Fin 2) ≠ 1) A) = ι₀ A :=
  spEmbed_shortBlock _ _ A

theorem embS'_shortBlock (A : SL(2, ZMod 2)) :
    embS' (shortBlock (ZMod 2) (zero_ne_one : (0 : Fin 2) ≠ 1) A) = ι₁ A :=
  spEmbed_shortBlock _ _ A

theorem longBlock_mem_complSp {n : ℕ} {j k : Fin n} (h : j ≠ k) (A : SL(2, ZMod 2)) :
    longBlock (ZMod 2) n j A ∈ complSp (ZMod 2) k := by
  have hsub : coords j ⊆ (coords k)ᶜ := by
    intro a ha hak
    rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 hak with h' | h' <;>
      simp_all
  rw [complSp]
  exact suppGroup_mono hsub (by rw [← longRootSp2_eq_suppGroup]; exact ⟨A, rfl⟩)

theorem commute_longBlock {n : ℕ} {j k : Fin n} (h : j ≠ k) (A B : SL(2, ZMod 2)) :
    Commute (longBlock (ZMod 2) n j A) (longBlock (ZMod 2) n k B) :=
  (commute_of_mem_longRootSp2_of_mem_complSp (k := k) (x := longBlock (ZMod 2) n k B)
    (y := longBlock (ZMod 2) n j A) ⟨B, rfl⟩ (longBlock_mem_complSp h A)).symm

theorem nsElt_mem_complSp {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    nsElt (K := ZMod 2) (n := n) j ∈ complSp (ZMod 2) k :=
  longBlock_mem_complSp h _

theorem card_ZMod_two : Nat.card (ZMod 2) = 2 := by simp

theorem mem_complSp_of_two_pow {n : ℕ} (k : Fin n) {x : StatedSp n (ZMod 2)}
    (hx : x * nsElt k = nsElt k * x) {m : ℕ} (hm : x ^ (2 ^ m) = 1) :
    x ∈ complSp (ZMod 2) k := by
  obtain ⟨a, ha, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt card_ZMod_two hx
  have hya : y * a = a * y := by
    have := Subgroup.mem_centralizer_iff.mp (complSp_le_centralizer_nsTorusSp k hy) a ha
    exact this.symm
  have hc : Commute a y := hya.symm
  have h1 : a ^ (2 ^ m) * y ^ (2 ^ m) = 1 := by rw [← hc.mul_pow]; exact hm
  have h2 : a ^ (2 ^ m) = (y ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : a ^ (2 ^ m) = 1 := by
    have hmem : a ^ (2 ^ m) ∈ nsTorusSp (ZMod 2) k := (nsTorusSp (ZMod 2) k).pow_mem ha _
    have hmem' : a ^ (2 ^ m) ∈ complSp (ZMod 2) k := by
      rw [h2]; exact (complSp (ZMod 2) k).inv_mem ((complSp (ZMod 2) k).pow_mem hy _)
    exact (Subgroup.disjoint_def.mp (disjoint_nsTorusSp_complSp k)) hmem hmem'
  have h4 : orderOf a ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard (nsTorusSp (ZMod 2) k) ha
    rwa [card_nsTorusSp] at this
  have h5 : orderOf a ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h3
  have h6 : orderOf a = 1 := by
    have hco : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left _ (by norm_num)
    exact Nat.eq_one_of_dvd_coprimes hco h5 h4
  rw [orderOf_eq_one_iff.mp h6, one_mul]
  exact hy

theorem range_le_closure_sq {H : Type} [Group H] (φ : SL(2, ZMod 2) →* H) :
    φ.range ≤ Subgroup.closure {w : H | w * w = 1} := by
  rintro _ ⟨A, rfl⟩
  have hA := CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A
  have hle : Subgroup.closure (Set.range (sl2Upper (k := ZMod 2)) ∪ Set.range sl2Lower) ≤
      (Subgroup.closure {w : H | w * w = 1}).comap φ := by
    rw [Subgroup.closure_le]
    have key : ∀ c : ZMod 2, sl2Upper c * sl2Upper c = 1 ∧ sl2Lower c * sl2Lower c = 1 := by
      decide
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.subset_closure (by
        show φ (sl2Upper c) * φ (sl2Upper c) = 1
        rw [← map_mul, (key c).1, map_one])
    · exact Subgroup.subset_closure (by
        show φ (sl2Lower c) * φ (sl2Lower c) = 1
        rw [← map_mul, (key c).2, map_one])
  exact hle hA

theorem closure_sq_eq_top_K3 : Subgroup.closure {w : K3 | w * w = 1} = ⊤ := by
  rw [eq_top_iff, ← iSup_nodes_eq_top]
  exact sup_le (sup_le (range_le_closure_sq _) (range_le_closure_sq _)) (range_le_closure_sq _)

theorem closure_sq_eq_top_Sp4 : Subgroup.closure {w : StatedSp 2 (ZMod 2) | w * w = 1} = ⊤ := by
  rw [eq_top_iff, ← shortBlock_sup_longBlock_eq_top (ZMod 2)]
  exact sup_le (range_le_closure_sq _) (range_le_closure_sq _)

theorem nonempty_sp4_mulEquiv_perm : Nonempty (StatedSp 2 (ZMod 2) ≃* Equiv.Perm (Fin 6)) :=
  CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := ZMod 2)
    (ZMod.card 2)

theorem card_sp4 : Nat.card (StatedSp 2 (ZMod 2)) = 720 := by
  obtain ⟨e⟩ := nonempty_sp4_mulEquiv_perm
  rw [Nat.card_congr e.toEquiv]
  exact S6Aut.card_perm_six

theorem card_complSp (k : Fin 3) : Nat.card (complSp (ZMod 2) k) = 720 := by
  rw [← Nat.card_congr (complSpEquiv (K := ZMod 2) (m := 2) k).toEquiv]
  exact card_sp4

theorem card_nsTorus_pair :
    Nat.card ↥(nsTorusSp (ZMod 2) (0 : Fin 2) ⊔ nsTorusSp (ZMod 2) (1 : Fin 2)) = 9 := by
  have hA : nsTorusSp (ZMod 2) (0 : Fin 2) ≤
      Subgroup.normalizer (nsTorusSp (ZMod 2) (1 : Fin 2) : Set (StatedSp 2 (ZMod 2))) := by
    rw [nsTorusSp, Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨j, rfl⟩ := hx
    have hc : Commute (nsElt (K := ZMod 2) (n := 2) 0) (nsElt (K := ZMod 2) (n := 2) 1) :=
      commute_longBlock (by decide) _ _
    rw [(hc.zpow_right j).eq, mul_inv_cancel_right]
    exact ⟨j, rfl⟩
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hA
  have hdis : nsTorusSp (ZMod 2) (0 : Fin 2) ⊓ nsTorusSp (ZMod 2) (1 : Fin 2) = ⊥ := by
    rw [← disjoint_iff]
    refine (disjoint_nsTorusSp_complSp (K := ZMod 2) (n := 2) (0 : Fin 2)).mono_right ?_
    rw [nsTorusSp, Subgroup.zpowers_le]
    exact nsElt_mem_complSp (by decide)
  rw [hdis, Subgroup.card_bot, card_nsTorusSp, card_nsTorusSp] at h
  omega

theorem commute_tM_of_mem_complSp {y : K3} (hy : y ∈ complSp (ZMod 2) (2 : Fin 3)) :
    Commute tM y :=
  commute_of_mem_longRootSp2_of_mem_complSp (k := 2) ⟨sl2Upper 1, rfl⟩ hy

theorem shiftEmb_mem_Pvec_of_commute (y : K3) (hy : y * tM = tM * y) : shiftEmb y ∈ Pvec := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  rw [← shiftEmb_tM, ← map_mul, ← map_mul, hy]

abbrev P3 : Subgroup K3 := Subgroup.centralizer {tM}

noncomputable def initHom : K3 →* ↥Pvec := initEmb.codRestrict Pvec initEmb_mem_Pvec

noncomputable def shiftHom : ↥P3 →* ↥Pvec :=
  (shiftEmb.comp P3.subtype).codRestrict Pvec fun x =>
    shiftEmb_mem_Pvec_of_commute x.1 (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem coe_initHom (x : K3) : ((initHom x : ↥Pvec) : K4) = initEmb x := rfl

theorem initHom_injective : Function.Injective initHom := fun x y h =>
  initEmb_injective (congrArg Subtype.val h)

end Am4

end CFSG.RankThree.PartTwo.Sec21.FF81
