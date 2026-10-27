module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Conj

private theorem g5_latChar_latPerm_fixed {N p : ℕ} {π : Equiv.Perm (Fin N)}
    {z : Fin N → ZMod p} (hz : ∀ i, z (π i) = z i) (γ : Fin N → ℤ) :
    latChar p z (latPerm π γ) = latChar p z γ := by
  simp only [latChar, latPerm]
  have h : (∑ i, (γ (π.symm i) : ZMod p) * z i) = ∑ i, (γ i : ZMod p) * z (π i) := by
    rw [← Equiv.sum_comp π (fun i => (γ (π.symm i) : ZMod p) * z i)]
    simp
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by rw [hz i]

private theorem g5_ggLangReidx_symm {R N : ℕ} (h : R = N) (w : Fin N → ℤ) :
    ggLangReidx h (ggLangReidx h.symm w) = w := by
  subst h
  rfl

private theorem g5_ggLangReidx_injective {R N : ℕ} (h : R = N) :
    Function.Injective (ggLangReidx h) := by
  intro a b hab
  have := congrArg (ggLangReidx h.symm) hab
  rwa [g5_ggLangReidx_symm, g5_ggLangReidx_symm] at this

private theorem g5_ggLangReidx_single {R N : ℕ} (h : R = N) (k : Fin R) :
    ggLangReidx h (Pi.single k 1 : Fin R → ℤ) = Pi.single (Fin.cast h k) 1 := by
  subst h
  ext j
  simp [ggLangReidx, Pi.single_apply]

private theorem g5_ggLangReidx_add {R N : ℕ} (h : R = N) (a b : Fin R → ℤ) :
    ggLangReidx h (a + b) = ggLangReidx h a + ggLangReidx h b := by
  subst h
  rfl

private theorem g5_ggLangReidx_zsmul {R N : ℕ} (h : R = N) (c : ℤ) (a : Fin R → ℤ) :
    ggLangReidx h (c • a) = c • ggLangReidx h a := by
  subst h
  rfl

private theorem g5_latChar_ggLangReidx_symm {R N p : ℕ} (h : R = N) (z : Fin R → ZMod p)
    (w : Fin N → ℤ) :
    latChar p z (ggLangReidx h.symm w) =
      ∑ j : Fin N, (w j : ZMod p) * z (Fin.cast h.symm j) := by
  simp only [latChar, ggLangReidx]
  exact Fintype.sum_equiv (finCongr h) _ _ fun j => by simp

private theorem g5_rootChar_ggParam {τ : Tag} {R p : ℕ} [NeZero p] (hR : R = τ.rank)
    (ζ : GGLˣ) (z : Fin R → ZMod p) (v : Fin R → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (ggParam hR ζ z)
        (ggLangReidx hR v) =
      ζ ^ (∑ j, (ZMod.val (z j) : ℤ) * v j) := by
  show ∏ i, (ggParam hR ζ z) i ^ (ggLangReidx hR v) i = _
  have h1 : ∀ i : Fin τ.rank,
      (ggParam hR ζ z) i ^ (ggLangReidx hR v) i =
        ζ ^ ((ZMod.val (z (Fin.cast hR.symm i)) : ℤ) * v (Fin.cast hR.symm i)) := by
    intro i
    rw [ggParam, ggLangReidx]
    rw [← zpow_natCast ζ (ZMod.val (z (Fin.cast hR.symm i)))]
    rw [zpow_mul]
  rw [show (∏ i, (ggParam hR ζ z) i ^ (ggLangReidx hR v) i) =
      ∏ i, ζ ^ ((ZMod.val (z (Fin.cast hR.symm i)) : ℤ) * v (Fin.cast hR.symm i)) from
    Finset.prod_congr rfl (fun i _ => h1 i)]
  have hprod : (∏ i, ζ ^ ((ZMod.val (z (Fin.cast hR.symm i)) : ℤ) * v (Fin.cast hR.symm i))) =
      ζ ^ (∑ i, (ZMod.val (z (Fin.cast hR.symm i)) : ℤ) * v (Fin.cast hR.symm i)) :=
    Finset.prod_zpow_eq_zpow_sum Finset.univ ζ _
  rw [hprod]
  congr 1
  exact Fintype.sum_equiv (finCongr hR.symm) _ _ fun j => by simp

private theorem g5_sum_reindex {R N p : ℕ} (h : R = N) (z : Fin R → ZMod p) (w : Fin N → ℤ) :
    (∑ j : Fin R, (ZMod.val (z j) : ℤ) * ggLangReidx h.symm w j) =
      ∑ j : Fin N, (ZMod.val (z (Fin.cast h.symm j)) : ℤ) * w j := by
  simp only [ggLangReidx]
  exact Fintype.sum_equiv (finCongr h) _ _ fun j => by simp

private theorem g5_zeta_zpow_eq_of_dvd {p : ℕ} {ζ : GGLˣ} (hζ : orderOf ζ = p) {a b : ℤ}
    (h : (p : ℤ) ∣ b - a) : ζ ^ b = ζ ^ a := by
  have h1 : ζ ^ (b - a) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hζ]
    exact h
  calc ζ ^ b = ζ ^ (a + (b - a)) := by ring_nf
    _ = ζ ^ a * ζ ^ (b - a) := by rw [zpow_add]
    _ = ζ ^ a := by rw [h1, mul_one]

theorem ggG5_Y_conj_uMap
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t} {C : Type}
    [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ} (F : GGLangFrame t p f ht)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D ι₀ ζ)
    (u : WeylGroup (langTag t)) (hu : GGCommPi t p f ht u)
    (z : Multiplicative (ggFixAdd p (piB t p f))) :
    ∃ z' : Multiplicative (ggFixAdd p (piB t p f)),
      (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u * F.M.D.g0⁻¹)⁻¹ * hT.uMap z *
          (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u * F.M.D.g0⁻¹) =
        hT.uMap z' ∧
      ∀ γ γ' : Fin (ggU (absTag t) 6 f).D.rank → ℤ,
        ggLangReidx (rank_eq_langTag f ht) γ' = u • ggLangReidx (rank_eq_langTag f ht) γ →
          latChar p (Multiplicative.toAdd z').1 γ = latChar p (Multiplicative.toAdd z).1 γ' := by
  classical
  have hR : (ggU (absTag t) 6 f).D.rank = (langTag t).rank := rank_eq_langTag f ht
  let z₁ : Fin (ggU (absTag t) 6 f).D.rank → ZMod p := (Multiplicative.toAdd z).1
  have hz₁ : ∀ i, z₁ (piB t p f i) = z₁ i := (mem_ggFixAdd.mp (Multiplicative.toAdd z).2)
  let T : (Fin (ggU (absTag t) 6 f).D.rank → ℤ) →+ (Fin (ggU (absTag t) 6 f).D.rank → ℤ) :=
    { toFun := fun δ => ggLangReidx hR.symm (u • ggLangReidx hR δ)
      map_zero' := by
        show ggLangReidx hR.symm (u • (0 : Fin (langTag t).rank → ℤ)) = 0
        rw [smul_zero]
        ext j
        rfl
      map_add' := by
        intro a b
        ext j
        simp only [g5_ggLangReidx_add, Pi.add_apply, smul_def, map_add] }
  let z'₁ : Fin (ggU (absTag t) 6 f).D.rank → ZMod p := fun k => latChar p z₁ (T (Pi.single k 1))
  have hT_apply : ∀ δ, T δ = ggLangReidx hR.symm (u • ggLangReidx hR δ) := fun δ => rfl
  have hT_sum : ∀ δ, T δ = ∑ k, (δ k) • T (Pi.single k 1) := by
    intro δ
    conv_lhs => rw [pi_eq_sum_univ δ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    congr 1
    funext j
    by_cases h : k = j <;> simp [Pi.single_apply, h, eq_comm]
  have hT_single : ∀ k : Fin (ggU (absTag t) 6 f).D.rank,
      T (Pi.single k 1) = ggLangReidx hR.symm (u • Pi.single (Fin.cast hR k) 1) := by
    intro k
    rw [hT_apply, g5_ggLangReidx_single]
  have hT_latPerm : ∀ δ, T (latPerm (piB t p f) δ) = latPerm (piB t p f) (T δ) := by
    intro δ
    have h1 : ggLangReidx hR (latPerm (piB t p f) δ) =
        permLattice ((finCongr hR).permCongr (piB t p f)) (ggLangReidx hR δ) :=
      ggReidx_latPerm_permLattice hR (piB t p f) δ
    have h2 := hu (ggLangReidx hR δ)
    have h3 : T (latPerm (piB t p f) δ) =
        ggLangReidx hR.symm (permLattice ((finCongr hR).permCongr (piB t p f))
          (u • ggLangReidx hR δ)) := by
      rw [hT_apply, h1, h2]
    rw [h3, hT_apply]
    have h4 := ggReidx_latPerm_permLattice hR (piB t p f)
      (ggLangReidx hR.symm (u • ggLangReidx hR δ))
    rw [g5_ggLangReidx_symm] at h4
    apply g5_ggLangReidx_injective hR
    rw [g5_ggLangReidx_symm hR, h4]
  have hz'fixed : ∀ k, z'₁ (piB t p f k) = z'₁ k := by
    intro k
    have hsingle : (Pi.single (piB t p f k) 1 : Fin (ggU (absTag t) 6 f).D.rank → ℤ) =
        latPerm (piB t p f) (Pi.single k 1) := by
      ext j
      simp [latPerm, Pi.single_apply, Equiv.symm_apply_eq]
    simp only [z'₁, hsingle]
    rw [hT_latPerm]
    exact g5_latChar_latPerm_fixed hz₁ (T (Pi.single k 1))
  let z' : Multiplicative (ggFixAdd p (piB t p f)) :=
    Multiplicative.ofAdd ⟨z'₁, fun i => hz'fixed i⟩
  have hz'toAdd : (Multiplicative.toAdd z').1 = z'₁ := rfl
  have hchar : ∀ δ, latChar p z'₁ δ = latChar p z₁ (T δ) := by
    intro δ
    have h1 : latChar p z'₁ δ =
        ∑ k, (δ k : ZMod p) * ∑ j, ((T (Pi.single k 1)) j : ZMod p) * z₁ j := by
      simp only [latChar, z'₁]
    have h3 : ∀ j, ((T δ) j : ZMod p) =
        ∑ k, (δ k : ZMod p) * ((T (Pi.single k 1)) j : ZMod p) := by
      intro j
      have h4 := congrFun (hT_sum δ) j
      rw [h4, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
    calc latChar p z'₁ δ
        = ∑ k, (δ k : ZMod p) * ∑ j, ((T (Pi.single k 1)) j : ZMod p) * z₁ j := h1
      _ = ∑ j, (∑ k, (δ k : ZMod p) * ((T (Pi.single k 1)) j : ZMod p)) * z₁ j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ j, ((T δ) j : ZMod p) * z₁ j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h3 j]
      _ = latChar p z₁ (T δ) := rfl
  have hval_eq : ∀ i : Fin (langTag t).rank,
      (z'₁ (Fin.cast hR.symm i) : ZMod p) =
        ∑ j : Fin (langTag t).rank, (ZMod.val (z₁ (Fin.cast hR.symm j)) : ZMod p) *
          (((u • Pi.single i (1 : ℤ)) : Fin (langTag t).rank → ℤ) j : ZMod p) := by
    intro i
    have hk : Fin.cast hR (Fin.cast hR.symm i) = i := by
      simp only [Fin.cast_cast, Fin.cast_refl]
      rfl
    have hz'eq : z'₁ (Fin.cast hR.symm i) =
        latChar p z₁ (ggLangReidx hR.symm (u • Pi.single i 1)) := by
      have hT' : T (Pi.single (Fin.cast hR.symm i) 1) =
          ggLangReidx hR.symm (u • Pi.single i 1) := by
        rw [hT_single, hk]
      change latChar p z₁ (T (Pi.single (Fin.cast hR.symm i) 1)) = _
      rw [hT']
    rw [hz'eq, g5_latChar_ggLangReidx_symm hR]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZMod.natCast_zmod_val]
    ring
  have hparam : ggParam hR ζ z'₁ = weylTuple u⁻¹ (ggParam hR ζ z₁) := by
    funext i
    rw [weylTuple, inv_inv]
    rw [← g5_ggLangReidx_symm hR (u • Pi.single i 1), g5_rootChar_ggParam]
    rw [ggParam]
    rw [← zpow_natCast ζ (z'₁ (Fin.cast hR.symm i)).val]
    apply g5_zeta_zpow_eq_of_dvd hT.ζ_order
    rw [g5_sum_reindex hR z₁ (u • Pi.single i 1)]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    rw [ZMod.natCast_zmod_val]
    exact hval_eq i
  refine ⟨z', ?_, ?_⟩
  · rw [hT.uMap_apply, hT.uMap_apply]
    have hYu : (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u * F.M.D.g0⁻¹)⁻¹ *
        (F.M.D.g0 * rootDiagUnit (langTag t) (ggParam hR ζ z₁) * F.M.D.g0⁻¹) *
        (F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u * F.M.D.g0⁻¹) =
        F.M.D.g0 * (canonicalRep (coxeterSystem (langTag t)) GGL u⁻¹ *
          rootDiagUnit (langTag t) (ggParam hR ζ z₁) *
          (canonicalRep (coxeterSystem (langTag t)) GGL u⁻¹)⁻¹) * F.M.D.g0⁻¹ := by
      rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo (w := u)]
      group
    rw [hYu, canonicalRep_conj_rootDiagUnit, ← hparam]
    rfl
  · intro γ γ' hγ
    rw [hz'toAdd, hchar γ]
    have : T γ = γ' := by
      apply g5_ggLangReidx_injective hR
      rw [hT_apply, g5_ggLangReidx_symm hR]
      exact hγ.symm
    rw [this]

end Conj

end CFSG.StandardType.GGFinModel.G5
