module

public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticDiag
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactGL
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
import CFSG.Assembly.Subnormal
import CFSG.LieType.Universal.Symplectic
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClass
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp SpCoord Multiplicative
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective elt)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed mat_spEmbed spEmbedMat spIncl
  spIncl_transpose_mul spEmbed_elt_difference)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_normal)
open CFSG.LieType.Steinberg.CentralExt
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped Matrix

namespace SpAvoid

section Coord

variable {p k : ℕ}

private theorem sgnAut_eq_self_iff (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin k)
    (f : Fin k → Multiplicative (ZMod p)) : sgnAut i f = f ↔ f i = 1 := by
  constructor
  · intro h
    have h1 := congrFun h i
    rw [sgnAut_apply, Function.update_self] at h1
    have h2 : toAdd (f i) = -toAdd (f i) := by rw [← toAdd_inv, h1]
    rw [← ofAdd_toAdd (f i), coord_eq_zero_of_eq_neg hp hp2 h2, ofAdd_zero]
  · intro h
    rw [sgnAut_apply, h, inv_one, ← h, Function.update_eq_self]

private theorem permAut_swap_eq_self_iff {a b : Fin k} (f : Fin k → Multiplicative (ZMod p)) :
    permAut (Equiv.swap a b) f = f ↔ f a = f b := by
  constructor
  · intro h
    have h1 := congrFun h a
    rw [permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    funext j
    rw [permAut_apply, Function.comp_apply, Equiv.swap_inv]
    by_cases hja : j = a
    · subst hja
      rw [Equiv.swap_apply_left, h]
    · by_cases hjb : j = b
      · subst hjb
        rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]

end Coord

section Blocks

variable {K : Type} [Field K] {n : ℕ}

private theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ} {E : Subgroup G}
    (f : G →* H) (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  obtain ⟨hc, hp⟩ := hE
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨x, hx, hxu⟩ := u.2
    obtain ⟨y, hy, hyv⟩ := v.2
    apply Subtype.ext
    change (u : H) * v = v * u
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, Subgroup.mul_comm_of_mem_isMulCommutative E hx hy]
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [← map_pow, hp x hx, map_one]

private theorem comp_mulSingle {p : ℕ} (χ : Multiplicative (ZMod p) →* Kˣ) (j : Fin n)
    (x : Multiplicative (ZMod p)) :
    (fun k => χ ((Pi.mulSingle j x : Fin n → Multiplicative (ZMod p)) k)) =
      Pi.mulSingle j (χ x) := by
  funext k
  exact Pi.apply_mulSingle (fun _ => χ) (fun _ => map_one χ) j x k

private theorem spTorusSp_eq_diagSp {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (f : Fin n → Multiplicative (ZMod p)) :
    (spTorusSp hζ f : LargeEvenSpGroup K n) = diagSp K n fun j => zmodPowHom hζ (f j) := by
  refine mat_injective ?_
  rw [mat_diagSp, mat_apply, spTorusSp_coe, spTorusGL_apply, TauCeti.diagGL_coe]
  congr 1
  funext x
  rcases x with j | j <;> rfl

private theorem spSwapSp_conj_spTorusSp [CharP K 2] {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (i : Fin n) (f : Fin n → Multiplicative (ZMod p)) :
    spSwapSp i * spTorusSp hζ f * (spSwapSp i)⁻¹ = spTorusSp hζ (sgnAut i f) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spSwapSp_coe, spTorusSp_coe,
    spTorusSp_coe, spTorusGL_apply, spTorusGL_apply, permutationGL_pairSwap_conj,
    pairedUnits_comp_pairSwap, sgnAut_apply]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

private theorem permSp_conj_spTorusSp {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) (σ : Equiv.Perm (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) :
    permSp K σ * spTorusSp hζ f * (permSp K σ)⁻¹ = spTorusSp hζ (permAut σ f) := by
  rw [spTorusSp_eq_diagSp, spTorusSp_eq_diagSp, conj_permSp_diagSp]
  rfl

private theorem spSwapSp_mem_spBlock [CharP K 2] (i : Fin n) :
    (spSwapSp i : LargeEvenSpGroup K n) ∈ spBlock K {i} := by
  have hmem : ∀ c : Fin n ⊕ Fin n,
      c ∈ planeCoords ({i} : Finset (Fin n)) ↔ c = Sum.inl i ∨ c = Sum.inr i := by
    intro c
    rw [mem_planeCoords, Finset.mem_singleton]
    rcases c with j | j <;> simp
  intro a b hab
  rw [mat_apply, spSwapSp_coe, TauCeti.permutationGL_coe, pairSwap, Equiv.swap_inv,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_eq, Matrix.submatrix_apply]
  change (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Equiv.swap (Sum.inl i) (Sum.inr i) a) b =
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a b
  by_cases ha : a ∈ planeCoords ({i} : Finset (Fin n))
  · have hb : b ∉ planeCoords ({i} : Finset (Fin n)) := fun hb => hab ⟨ha, hb⟩
    have hsa : Equiv.swap (Sum.inl i) (Sum.inr i) a ∈ planeCoords ({i} : Finset (Fin n)) := by
      rcases (hmem a).1 ha with rfl | rfl
      · rw [Equiv.swap_apply_left]
        exact (hmem _).2 (Or.inr rfl)
      · rw [Equiv.swap_apply_right]
        exact (hmem _).2 (Or.inl rfl)
    rw [Matrix.one_apply_ne (show Equiv.swap (Sum.inl i) (Sum.inr i) a ≠ b from fun h => hb (h ▸ hsa)),
      Matrix.one_apply_ne (show a ≠ b from fun h => hb (h ▸ ha))]
  · rw [Equiv.swap_apply_of_ne_of_ne (fun h => ha ((hmem a).2 (Or.inl h)))
      (fun h => ha ((hmem a).2 (Or.inr h)))]

private theorem permSp_swap_mem_siegelBlock [CharP K 2] (a b : Fin n) :
    permSp K (Equiv.swap a b) ∈ siegelBlock K ({a, b} : Finset (Fin n)) :=
  ⟨CFSG.SeitzReduction.OmegaPilot.q2SwapSL a b,
    CFSG.SeitzReduction.OmegaPilot.q2SwapSL_mem_blockSpecialLinear a b,
    (CFSG.SeitzReduction.OmegaPilot.permSp_swap_eq a b).symm⟩

private theorem spBlock_univ : spBlock K (Finset.univ : Finset (Fin n)) = ⊤ :=
  eq_top_iff.mpr fun _ _ a b hab =>
    (hab ⟨Finset.mem_univ (planeOf a), Finset.mem_univ (planeOf b)⟩).elim

private theorem permSp_conj_eq_spEmbed (π : Equiv.Perm (Fin n)) (x : StatedSp n K) :
    permSp K π * x * (permSp K π)⁻¹ = spEmbed (⇑π) π.injective x := by
  refine mat_injective ?_
  have hS : spIncl (K := K) (⇑π) * (spIncl (K := K) (⇑π))ᵀ = 1 :=
    mul_eq_one_comm.mp (spIncl_transpose_mul π.injective)
  rw [map_mul, map_mul, mat_permSp, mat_permSp_inv, mat_spEmbed, spEmbedMat, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, hS]
  abel

private theorem elt_difference_eq_of_eq {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j')
    (hi : i = i') (hj : j = j') (c : K) :
    elt (.difference i j hij) c = elt (.difference i' j' hij') c := by
  subst hi hj
  rfl

private theorem elt_difference_eq_conj {u v k : Fin n} (huv : u ≠ v) (hku : k ≠ u) (hkv : k ≠ v)
    (c : K) :
    elt (.difference u v huv) c =
      permSp K (Equiv.swap k u) * elt (.difference k v hkv) c * (permSp K (Equiv.swap k u))⁻¹ := by
  rw [permSp_conj_eq_spEmbed, spEmbed_elt_difference]
  exact elt_difference_eq_of_eq _ _ (Equiv.swap_apply_left k u).symm
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm hkv) (Ne.symm huv)).symm c

private theorem card_SL2 [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

private theorem isComponentOf_of_perfectCore_eq {G : Type*} [Group G] {C S : Subgroup G}
    (h : perfectCore C = S) (hq : CFSG.Assembly.IsQuasisimple S) :
    CFSG.Assembly.IsComponentOf S C := by
  subst h
  exact ⟨perfectCore_le C, CFSG.Assembly.IsSubnormal.step (perfectCore_le C) (perfectCore_normal C)
    (CFSG.Assembly.IsSubnormal.refl _), hq⟩

private theorem sp_injective_of_cover
    [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hn : 2 ≤ n) (L' : Type) [Group L'] [Finite L'] (ψ : L' →* LargeEvenSpGroup K n)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : Function.Injective ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card hK
  set Z := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars n K
  have hZc : Z ≤ Subgroup.center (StatedSp n K) :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Group.IsPerfect (StatedSp n K) := SpClosed.isPerfect_statedSp' (Or.inl h4)
  obtain ⟨σ, hσ⟩ := CoverAssembly.exists_section_of_cover_and_coprime (p := 2)
    (θ := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hZc)
    (SpClosed.psp_two_cover_trivial hK (by omega) hn fun _ => hf)
    (fun E _ _ π hπ hcen hc => SpClosed.sp_exists_section_of_coprime E π hπ hcen hc) L' ψ hψ hker
  have : Group.IsPerfect L' := ⟨hperf⟩
  exact (MonoidHom.ker_eq_bot_iff ψ).mp (SL2Closed.ker_eq_bot_of_section ψ hker σ hσ)

private theorem exists_conj_eq_map_spTorusSp [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {E : Subgroup (LargeEvenSpGroup K n)} (hE : IsElemAbelian p E) (hcard : p ^ n ≤ Nat.card E) :
    ∃ g : LargeEvenSpGroup K n, E = (spTorusSp hζ).range.map (MulAut.conj g).toMonoidHom := by
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h2).symm
  obtain ⟨P, hP, hPE⟩ := exists_conj_eq_range_spTorusGL hp2 hpK hζo hζ
    (E := E.map (LargeEvenSpGroup K n).subtype) (by rintro _ ⟨x, _, rfl⟩; exact x.2)
    (isElemAbelian_map _ hE)
    (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]; exact hcard)
  refine ⟨⟨P, hP⟩, ?_⟩
  ext x
  constructor
  · intro hx
    have h1 : MulAut.conj P⁻¹ (x : GL (Fin n ⊕ Fin n) K) ∈ (spTorusGL (m := n) hζ).range := by
      rw [← hPE]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨f, hf⟩ := h1
    refine ⟨spTorusSp hζ f, ⟨f, rfl⟩, Subtype.ext ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      spTorusSp_coe]
    rw [hf, MulAut.conj_apply]
    group
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    have h1 : spTorusGL (m := n) hζ f ∈ (E.map (LargeEvenSpGroup K n).subtype).map
        (MulAut.conj P⁻¹).toMonoidHom := by
      rw [hPE]
      exact ⟨f, rfl⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hzf⟩ := h1
    have hzeq : (MulAut.conj (⟨P, hP⟩ : LargeEvenSpGroup K n)).toMonoidHom (spTorusSp hζ f) = z := by
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        spTorusSp_coe]
      rw [← hzf]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      group
    rw [hzeq]
    exact hz

end Blocks

private abbrev SpIdx (n : ℕ) : Type := Fin n ⊕ {σ : Equiv.Perm (Fin n) // σ.IsSwap}

section Main

variable {K : Type} [Field K] {n : ℕ}

theorem ggTorusRootGenAvoidKG_statedSp
    [Finite K] {f p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusRootGenAvoidKG p n (LargeEvenSpGroup K n)
      (Set.range (MulAut.conj : LargeEvenSpGroup K n →* MulAut (LargeEvenSpGroup K n))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have : CharP K 2 := charP_two_of_card hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hκ : ζ * ζ ≠ 1 := by
    intro h
    have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hζo] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hχg : zmodPowHom hζ (ofAdd (1 : ZMod p)) = ζ := by
    have h1 := zmodPowHom_natCast hζ 1
    rwa [Nat.cast_one, pow_one] at h1
  have hτinj : Function.Injective (spTorusSp (m := n) hζ) := fun x y h =>
    spTorus_injective hζ hζo (hp.odd_of_ne_two hp2) (by
      rw [spTorus, MonoidHom.comp_apply, MonoidHom.comp_apply, h])
  have : Nonempty (SpIdx n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hcent : ∀ X : Set (Fin n → Multiplicative (ZMod p)),
      Subgroup.centralizer ((spTorusSp hζ : _ →* LargeEvenSpGroup K n) '' X) =
        spBlock K Finset.univ ⊓
          Subgroup.centralizer (diagSp K n '' ((fun f j => zmodPowHom hζ (f j)) '' X)) := by
    intro X
    rw [spBlock_univ, top_inf_eq, Set.image_image]
    congr 1
    exact Set.image_congr fun f _ => spTorusSp_eq_diagSp hζ f
  refine ggTorusRootGenAvoidKG_of_torusModel (ι := SpIdx n) hp
    (sp_injective_of_cover hK hf (by omega)) (center_statedSp_eq_bot (K := K) n) (fun _ h => h)
    (spTorusSp hζ) hτinj (fun E hE hr _ => by
      obtain ⟨g, hg⟩ := exists_conj_eq_map_spTorusSp hp2 hζo hζ hE hr
      exact ⟨MulAut.conj g, hg⟩)
    (Sum.elim (fun i => spSwapSp i) fun σ => permSp K σ.1)
    (Sum.elim (fun i => sgnAut i) fun σ => permAut σ.1)
    (Sum.elim (fun i => spBlock K {i}) fun σ => siegelBlock K σ.1.support) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rintro (i | ⟨σ, hσ⟩) f
    · exact spSwapSp_conj_spTorusSp hζ i f
    · exact permSp_conj_spTorusSp hζ σ f
  ·
    rintro (i | ⟨σ, a, b, hab, rfl⟩)
    · change sgnAut i * sgnAut i = 1
      rw [← sq]
      exact sgnAut_sq i
    · change permAut (Equiv.swap a b) * permAut (Equiv.swap a b) = 1
      rw [← sq]
      exact permAut_swap_sq a b
  ·
    rintro (i | ⟨σ, a, b, hab, rfl⟩)
    · exact card_fix_sgnAut hp hp2 i
    · exact card_fix_permAut_swap hp hp2 hab
  ·
    have hg1 : (ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ≠ 1 := fun h => by
      have h1 := congrArg toAdd h
      rw [toAdd_ofAdd, toAdd_one] at h1
      exact one_ne_zero h1
    have hginv : (ofAdd (1 : ZMod p))⁻¹ ≠ ofAdd (1 : ZMod p) := fun h => by
      have h1 := congrArg toAdd h
      rw [toAdd_inv, toAdd_ofAdd] at h1
      exact ZMod.neg_one_ne_one h1
    have hsgn : ∀ i c : Fin n, sgnAut i (Pi.mulSingle c (ofAdd (1 : ZMod p))) c =
        if c = i then (ofAdd (1 : ZMod p))⁻¹ else ofAdd (1 : ZMod p) := by
      intro i c
      rw [sgnAut_apply]
      by_cases hci : c = i
      · subst hci
        rw [Function.update_self, Pi.mulSingle_eq_same, if_pos rfl]
        rfl
      · rw [Function.update_of_ne hci, Pi.mulSingle_eq_same, if_neg hci]
    have hsp : ∀ (i : Fin n) (σ : Equiv.Perm (Fin n)), sgnAut i ≠
        (permAut σ : MulAut (Fin n → Multiplicative (ZMod p))) := by
      intro i σ h
      have h1 := congrFun (congrArg (fun φ : MulAut (Fin n → Multiplicative (ZMod p)) =>
        φ (Pi.mulSingle i (ofAdd (1 : ZMod p)))) h) i
      rw [hsgn, if_pos rfl, permAut_mulSingle, Pi.mulSingle_apply] at h1
      split_ifs at h1
      · exact hginv h1
      · exact hg1 (inv_eq_one.mp h1)
    rintro (i | ⟨σ, hσ⟩) (i' | ⟨σ', hσ'⟩) h
    · change sgnAut i = sgnAut i' at h
      have h1 := congrFun (congrArg (fun φ : MulAut (Fin n → Multiplicative (ZMod p)) =>
        φ (Pi.mulSingle i (ofAdd (1 : ZMod p)))) h) i
      rw [hsgn, hsgn, if_pos rfl] at h1
      by_cases hii : i = i'
      · rw [hii]
      · rw [if_neg hii] at h1
        exact absurd h1 hginv
    · exact absurd h (hsp i σ')
    · exact absurd h.symm (hsp i' σ)
    · change permAut σ = permAut σ' at h
      have hσσ : σ = σ' := Equiv.ext fun c => by
        have h1 := congrArg (fun φ : MulAut (Fin n → Multiplicative (ZMod p)) =>
          φ (Pi.mulSingle c (ofAdd (1 : ZMod p)))) h
        simp only [permAut_mulSingle] at h1
        exact (mulSingle_ofAdd_eq_iff one_ne_zero h1).1
      subst hσσ
      rfl
  ·
    rintro (i | ⟨σ, a, b, hab, rfl⟩)
    · exact spSwapSp_mem_spBlock i
    · change permSp K (Equiv.swap a b) ∈ siegelBlock K (Equiv.swap a b).support
      rw [Equiv.Perm.support_swap hab]
      exact permSp_swap_mem_siegelBlock a b
  ·
    rintro (r | ⟨σ, a, b, hab, rfl⟩)
    · change IsComponentOf (spBlock K {r})
        (Subgroup.centralizer ((spTorusSp hζ : _ →* LargeEvenSpGroup K n) ''
          {f | sgnAut r f = f}))
      rw [hcent]
      refine isComponentOf_of_perfectCore_eq (perfectCore_spBlock_inf_centralizer_eq
        (Finset.subset_univ _) _ ?_ ?_ (commutator_spBlock_eq h4 _)) ?_
      · rintro _ ⟨f, hf, rfl⟩ x hx y hy
        have hfr : f r = 1 := (sgnAut_eq_self_iff hp hp2 r f).1 hf
        have ht : (fun j => zmodPowHom hζ (f j)) ∈ planeTorusParam K ({r} : Finset (Fin n)) :=
          fun j hj => show zmodPowHom hζ (f j) = 1 by rw [Finset.mem_singleton.1 hj, hfr, map_one]
        rw [diagSpEntry_eq_one_of_mem_planeTorusParam ht hx,
          diagSpEntry_eq_one_of_mem_planeTorusParam ht hy]
      · rintro x - y - hxy hI
        have key : ∀ j : Fin n, j ≠ r →
            diagSpEntry (Pi.mulSingle j ζ) x ≠ diagSpEntry (Pi.mulSingle j ζ) y →
            ∃ s ∈ (fun f j => zmodPowHom hζ (f j)) '' {f | sgnAut r f = f},
              diagSpEntry s x ≠ diagSpEntry s y := by
          intro j hjr hne
          refine ⟨_, ⟨Pi.mulSingle j (ofAdd (1 : ZMod p)), ?_, rfl⟩, ?_⟩
          · exact (sgnAut_eq_self_iff hp hp2 r _).2 (Pi.mulSingle_eq_of_ne (Ne.symm hjr) _)
          · beta_reduce
            rw [comp_mulSingle, hχg]
            exact hne
        rcases hI with hx | hy
        · exact key (planeOf x) (fun h => hx (by rw [mem_planeCoords, h]; simp))
            (diagSpEntry_mulSingle_ne hκ hxy (Or.inl (mem_coords_planeOf x)))
        · exact key (planeOf y) (fun h => hy (by rw [mem_planeCoords, h]; simp))
            (diagSpEntry_mulSingle_ne hκ hxy (Or.inr (mem_coords_planeOf y)))
      · refine Assembly.IsQuasisimple.of_mulEquiv
          (spBlockEquiv (F := K) ({r} : Finset (Fin n))).symm ?_
        rw [Finset.card_singleton]
        have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 1 K le_rfl (Or.inl (Or.inr h4))
        exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
    · change IsComponentOf (siegelBlock K (Equiv.swap a b).support)
        (Subgroup.centralizer ((spTorusSp hζ : _ →* LargeEvenSpGroup K n) ''
          {f | permAut (Equiv.swap a b) f = f}))
      rw [Equiv.Perm.support_swap hab, hcent]
      refine isComponentOf_of_perfectCore_eq (perfectCore_spBlock_inf_centralizer_eq_siegelBlock
        (Finset.subset_univ _) _ ?_ ?_
        (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
          (by rw [Finset.card_pair hab]) h4)) ?_
      · rintro _ ⟨f, hf, rfl⟩ i hi j hj
        have hfab : f a = f b := (permAut_swap_eq_self_iff f).1 hf
        have hc : ∀ k ∈ ({a, b} : Finset (Fin n)), f k = f a := fun k hk => by
          rcases Finset.mem_insert.1 hk with rfl | hk
          · rfl
          · rw [Finset.mem_singleton.1 hk, hfab]
        show zmodPowHom hζ (f i) = zmodPowHom hζ (f j)
        rw [hc i hi, hc j hj]
      · rintro x - y - hxy hB
        have key : ∀ j : Fin n, j ≠ a → j ≠ b →
            diagSpEntry (Pi.mulSingle j ζ) x ≠ diagSpEntry (Pi.mulSingle j ζ) y →
            ∃ s ∈ (fun f j => zmodPowHom hζ (f j)) '' {f | permAut (Equiv.swap a b) f = f},
              diagSpEntry s x ≠ diagSpEntry s y := by
          intro j hja hjb hne
          refine ⟨_, ⟨Pi.mulSingle j (ofAdd (1 : ZMod p)), ?_, rfl⟩, ?_⟩
          · exact (permAut_swap_eq_self_iff _).2 (by
              rw [Pi.mulSingle_eq_of_ne (Ne.symm hja), Pi.mulSingle_eq_of_ne (Ne.symm hjb)])
          · beta_reduce
            rw [comp_mulSingle, hχg]
            exact hne
        have hnot : ∀ c : Fin n ⊕ Fin n, c ∉ planeCoords ({a, b} : Finset (Fin n)) →
            planeOf c ≠ a ∧ planeOf c ≠ b := by
          intro c hc
          refine ⟨fun h => hc ?_, fun h => hc ?_⟩ <;> rw [mem_planeCoords, h] <;> simp
        by_cases hx : x ∈ planeCoords ({a, b} : Finset (Fin n))
        · by_cases hy : y ∈ planeCoords ({a, b} : Finset (Fin n))
          ·
            set f₀ : Fin n → Multiplicative (ZMod p) :=
              fun k => if k ∈ ({a, b} : Finset (Fin n)) then ofAdd (1 : ZMod p) else 1 with hf₀
            refine ⟨_, ⟨f₀, (permAut_swap_eq_self_iff f₀).2 (by simp [hf₀]), rfl⟩, ?_⟩
            have h3 : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := fun e =>
              units_ne_inv_of_mul_self_ne_one hκ (Units.ext e)
            rw [mem_planeCoords] at hx hy
            rcases x with i | i <;> rcases y with j | j
            · exact absurd ⟨hx, hy⟩ hB
            · have hfi : f₀ i = ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hx
              have hfj : f₀ j = ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hy
              show diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inl i) ≠
                diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inr j)
              rw [diagSpEntry_inl, diagSpEntry_inr, hfi, hfj, hχg]
              exact h3
            · have hfi : f₀ i = ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hx
              have hfj : f₀ j = ofAdd (1 : ZMod p) := by rw [hf₀]; exact if_pos hy
              show diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inr i) ≠
                diagSpEntry (fun k => zmodPowHom hζ (f₀ k)) (Sum.inl j)
              rw [diagSpEntry_inr, diagSpEntry_inl, hfi, hfj, hχg]
              exact h3.symm
            · exact absurd ⟨hx, hy⟩ hB
          · obtain ⟨h1, h2⟩ := hnot y hy
            exact key _ h1 h2 (diagSpEntry_mulSingle_ne hκ hxy (Or.inr (mem_coords_planeOf y)))
        · obtain ⟨h1, h2⟩ := hnot x hx
          exact key _ h1 h2 (diagSpEntry_mulSingle_ne hκ hxy (Or.inl (mem_coords_planeOf x)))
      · refine Assembly.IsQuasisimple.of_mulEquiv
          (siegelBlockEquiv (F := K) ({a, b} : Finset (Fin n))).symm ?_
        rw [Finset.card_pair hab]
        have hq := CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2
          K le_rfl (Or.inr (by omega)) (Or.inr (by omega))
        exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  ·
    rintro (r | ⟨σ, a, b, hab, rfl⟩)
    · change p ∣ Nat.card (spBlock K {r})
      have hx : spTorusSp hζ (Pi.mulSingle r (ofAdd (1 : ZMod p))) ∈ spBlock K {r} := by
        rw [spTorusSp_eq_diagSp, comp_mulSingle, hχg, spBlock_singleton]
        exact rootTorusSp_le_longRootSp2 (K := K) r (rootTorusHom_mem_rootTorusSp (K := K) r ζ)
      have hord : orderOf (spTorusSp hζ (Pi.mulSingle r (ofAdd (1 : ZMod p)))) = p := by
        rw [orderOf_injective _ hτinj, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf,
          ZMod.addOrderOf_one]
      have h1 := orderOf_dvd_natCard (⟨_, hx⟩ : spBlock K {r})
      rwa [Subgroup.orderOf_mk, hord] at h1
    · change p ∣ Nat.card (siegelBlock K (Equiv.swap a b).support)
      rw [Equiv.Perm.support_swap hab,
        Nat.card_congr (siegelBlockEquiv (F := K) ({a, b} : Finset (Fin n))).toEquiv.symm,
        Finset.card_pair hab, card_SL2]
      have h1 := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2
      rw [one_pow] at h1
      exact Dvd.dvd.mul_left (hpq.trans h1) _
  ·
    have hmem : ∀ (j i : SpIdx n), i ≠ j → ∀ x ∈ (Sum.elim (fun i => spBlock K {i})
        fun σ => siegelBlock K σ.1.support : SpIdx n → Subgroup (LargeEvenSpGroup K n)) i,
        x ∈ ⨆ (i : SpIdx n) (_ : i ≠ j), (Sum.elim (fun i => spBlock K {i})
          fun σ => siegelBlock K σ.1.support : SpIdx n → Subgroup (LargeEvenSpGroup K n)) i :=
      fun j i hij x hx => Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hij hx)
    have hsw : ∀ (j : SpIdx n) (u v : Fin n) (huv : u ≠ v),
        (Sum.inr ⟨Equiv.swap u v, u, v, huv, rfl⟩ : SpIdx n) ≠ j →
        ∀ x ∈ siegelBlock K ({u, v} : Finset (Fin n)),
        x ∈ ⨆ (i : SpIdx n) (_ : i ≠ j), (Sum.elim (fun i => spBlock K {i})
          fun σ => siegelBlock K σ.1.support : SpIdx n → Subgroup (LargeEvenSpGroup K n)) i := by
      intro j u v huv hne x hx
      refine hmem j _ hne x ?_
      change x ∈ siegelBlock K (Equiv.swap u v).support
      rw [Equiv.Perm.support_swap huv]
      exact hx
    rintro (r | ⟨σ₀, a, b, hab, rfl⟩)
    · obtain ⟨r', hr', -⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_ne_ne_of_three_le hn r r
      refine eq_top_of_adjacent_of_long_statedSp _ r' (fun u v huv c _ => ?_) (fun c => ?_)
        (fun c => ?_)
      · exact hsw _ u v huv Sum.inr_ne_inl _
          (elt_difference_mem_siegelBlock huv (by simp) (by simp) c)
      · exact hmem _ (Sum.inl r') (fun h => hr' (Sum.inl_injective h)) _
          (elt_positiveLong_mem_spBlock (Finset.mem_singleton_self r') c)
      · exact hmem _ (Sum.inl r') (fun h => hr' (Sum.inl_injective h)) _
          (elt_negativeLong_mem_spBlock (Finset.mem_singleton_self r') c)
    · refine eq_top_of_adjacent_of_long_statedSp _ ⟨0, by omega⟩ (fun u v huv c _ => ?_)
        (fun c => ?_) (fun c => ?_)
      · by_cases h : Equiv.swap u v = Equiv.swap a b
        · obtain ⟨k, hku, hkv⟩ :=
            CFSG.SeitzReduction.SymplecticPilot.exists_ne_ne_of_three_le hn u v
          rw [elt_difference_eq_conj huv hku hkv c]
          have hne1 : (Sum.inr ⟨Equiv.swap k u, k, u, hku, rfl⟩ : SpIdx n) ≠
              Sum.inr ⟨Equiv.swap a b, a, b, hab, rfl⟩ := by
            intro e
            have e' : Equiv.swap k u = Equiv.swap a b := congrArg Subtype.val (Sum.inr_injective e)
            rw [← h] at e'
            have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => σ k) e'
            simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hku hkv] at h1
            exact hku h1.symm
          have hne2 : (Sum.inr ⟨Equiv.swap k v, k, v, hkv, rfl⟩ : SpIdx n) ≠
              Sum.inr ⟨Equiv.swap a b, a, b, hab, rfl⟩ := by
            intro e
            have e' : Equiv.swap k v = Equiv.swap a b := congrArg Subtype.val (Sum.inr_injective e)
            rw [← h] at e'
            have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => σ k) e'
            simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hku hkv] at h1
            exact hkv h1.symm
          have hp1 := hsw _ k u hku hne1 _ (permSp_swap_mem_siegelBlock k u)
          have hp2' := hsw _ k v hkv hne2 _
            (elt_difference_mem_siegelBlock hkv (by simp) (by simp) c)
          exact mul_mem (mul_mem hp1 hp2') (inv_mem hp1)
        · exact hsw _ u v huv (fun e => h (congrArg Subtype.val (Sum.inr_injective e))) _
            (elt_difference_mem_siegelBlock huv (by simp) (by simp) c)
      · exact hmem _ (Sum.inl ⟨0, by omega⟩) Sum.inl_ne_inr _
          (elt_positiveLong_mem_spBlock (Finset.mem_singleton_self _) c)
      · exact hmem _ (Sum.inl ⟨0, by omega⟩) Sum.inl_ne_inr _
          (elt_negativeLong_mem_spBlock (Finset.mem_singleton_self _) c)

theorem ggTorusRootGenAvoidKG_symplectic
    [Finite K] {f p : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusRootGenAvoidKG p n (LargeEvenProj (LargeEvenSpGroup K n))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K n)) (LargeEvenGSpSet K n)) := by
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero n := ⟨by omega⟩
  refine ggTorusRootGenAvoidKG_of_mulEquiv spProjEquivSp (fun φ hφ => ?_)
    (ggTorusRootGenAvoidKG_statedSp hK hf hn hp hp2 hpq)
  obtain ⟨x, rfl⟩ := sp_I_subset_inn hφ
  refine ⟨spProjEquivSp x, MulEquiv.ext fun y => ?_⟩
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

end Main

theorem recipeSymplectic_rootGenAvoidKG
    {l n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) (hn : 2 ≤ n) (hl : 3 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    ggTorusLift_symplectic hp hp2 hpq (by omega),
    ggTorusRootGenAvoidKG_symplectic hK hn hl hp hp2 hpq⟩

theorem largeEvenLabelAll_rootGenAvoidKG_symplectic
    {p l n : ℕ}
    {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hn : 2 ≤ n) (hl : 3 ≤ l) :
    LargeEvenLabelAll ⟨t, l, n⟩ fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  intro Q hQ
  rcases ht with rfl | rfl <;> exact recipeSymplectic_rootGenAvoidKG hp hp2 hpn hn hl hQ

end SpAvoid

end CFSG.StandardType

end
