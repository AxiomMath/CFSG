module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFix
public import CFSG.LieType.SeitzGeneration.OrthThree
public import CFSG.LieType.SeitzGeneration.OrthBlocks
public import CFSG.ClassicalGroups.SpecialLinear.TvModLinAlg
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthPieces
public import CFSG.LargeExtraspecial.A2ModLines
public import CFSG.LieType.SeitzGeneration.OrthLift
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem stable_perpPieces_of_commute (F : SevOm.Frame Q p E r) {y : V ≃ₗ[K] V}
    (hyE : ∀ c ∈ E, y * c = c * y)
    (hWfix : ∀ v, v ∈ perp Q (⨆ j, F.U j) ↔ ∀ c ∈ E, c v = v) :
    (∀ w ∈ perp Q (⨆ j, F.U j), y w ∈ perp Q (⨆ j, F.U j)) ∧
      (∀ w ∈ perp Q (⨆ j, F.U j), y.symm w ∈ perp Q (⨆ j, F.U j)) := by
  constructor
  · intro w hw
    rw [hWfix] at hw ⊢
    intro c hc
    have h : y (c w) = c (y w) := by
      have h2 := congrArg (fun f : V ≃ₗ[K] V => f w) (hyE c hc)
      simpa [LinearEquiv.mul_apply] using h2
    rw [hw c hc] at h
    exact h.symm
  · intro w hw
    rw [hWfix] at hw ⊢
    intro c hc
    have h' : y (c (y.symm w)) = c (y (y.symm w)) := by
      have h2 := congrArg (fun f : V ≃ₗ[K] V => f (y.symm w)) (hyE c hc)
      simpa [LinearEquiv.mul_apply] using h2
    rw [LinearEquiv.apply_symm_apply, hw c hc] at h'
    exact y.injective (by rw [h', LinearEquiv.apply_symm_apply])

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem stable_perpPieces_frame (F : SevOm.Frame Q p E r)
    (hWfix : ∀ v, v ∈ perp Q (⨆ j, F.U j) ↔ ∀ c ∈ E, c v = v)
    (hWperp : perp Q (perp Q (⨆ j, F.U j)) = ⨆ j, F.U j) :
    (∀ c ∈ E, ∀ s ∈ perp Q (⨆ j, F.U j), c s ∈ perp Q (⨆ j, F.U j)) ∧
      (∀ c ∈ E, ∀ r ∈ perp Q (perp Q (⨆ j, F.U j)),
        c r ∈ perp Q (perp Q (⨆ j, F.U j))) := by
  constructor
  · intro c hc s hs
    rw [hWfix] at hs ⊢
    intro d hd
    have hcomm : d * c = c * d := by
      obtain ⟨r, rfl⟩ := F.exists_eq hd
      obtain ⟨t, rfl⟩ := F.exists_eq hc
      rw [← map_mul, ← map_mul, mul_comm]
    calc d (c s) = (d * c) s := rfl
      _ = (c * d) s := by rw [hcomm]
      _ = c (d s) := rfl
      _ = c s := by rw [hs d hd]
  · intro c hc r hr
    rw [hWperp] at hr ⊢
    obtain ⟨t, rfl⟩ := F.exists_eq hc
    refine Submodule.iSup_induction
      (motive := fun x => (F.ι t) x ∈ ⨆ j, F.U j) F.U hr ?_ ?_ ?_
    · intro j x hx
      exact Submodule.mem_iSup_of_mem j (F.mapsTo t j x hx)
    · simpa using Submodule.zero_mem (⨆ j, F.U j)
    · intro x y hx hy
      simpa using Submodule.add_mem (⨆ j, F.U j) hx hy

omit [CharP K 2] in
private theorem extendId_perpPieces_eq_one (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (F : SevOm.Frame Q p E r)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E)
    {y : V ≃ₗ[K] V} (hyΩ : y ∈ orthDerived Q) (hyE : ∀ c ∈ E, y * c = c * y)
    {k : ℕ} (hyp : y ^ p ^ k = 1) (hWnd : PolarNondegOn Q (perp Q (⨆ j, F.U j)))
    (hWperp : perp Q (perp Q (⨆ j, F.U j)) = ⨆ j, F.U j)
    (hyS1 : ∀ w ∈ perp Q (⨆ j, F.U j), y w ∈ perp Q (⨆ j, F.U j))
    (hyS2 : ∀ w ∈ perp Q (⨆ j, F.U j), y.symm w ∈ perp Q (⨆ j, F.U j))
    (hSW1 : ∀ c ∈ E, ∀ s ∈ perp Q (⨆ j, F.U j), c s ∈ perp Q (⨆ j, F.U j))
    (hSW2 : ∀ c ∈ E, ∀ r ∈ perp Q (perp Q (⨆ j, F.U j)),
      c r ∈ perp Q (perp Q (⨆ j, F.U j)))
    {w₀ : V} (hw₀ : w₀ ∈ perp Q (⨆ j, F.U j)) (hw₀ne : y w₀ ≠ w₀) :
    extendId hWnd y hyS1 hyS2 = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hyΩ
  have hblock := extendId_isBlock hWnd hyO hyp hyS1 hyS2 ⟨w₀, hw₀, hw₀ne⟩
  have hy'Ω : extendId hWnd y hyS1 hyS2 ∈ orthDerived Q :=
    CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hQ hT
      ((hp.odd_of_ne_two hp2).pow) hblock.mem hblock.pow
  have hy'E : ∀ c ∈ E, extendId hWnd y hyS1 hyS2 * c = c * extendId hWnd y hyS1 hyS2 :=
    extendId_commute_of_stable hWnd hSW1 hSW2 hyE hyS1 hyS2
  by_contra hne
  obtain ⟨z, m, hzm, hzord⟩ := exists_pow_orderOf_eq_prime hp hblock.pow hne
  have hzΩ : z ∈ orthDerived Q := by
    rw [hzm]; exact Subgroup.pow_mem (orthDerived Q) hy'Ω m
  have hzE : ∀ c ∈ E, z * c = c * z := by
    intro c hc; rw [hzm]; exact Commute.pow_left (hy'E c hc) m
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hzEm : z ∈ E := hmax z hzΩ hzE hzp
  have htriv : ∀ j, ∀ u ∈ F.U j, z u = u := by
    intro j u hu
    rw [hzm]
    have hu' : u ∈ perp Q (perp Q (⨆ j, F.U j)) := by
      rw [hWperp]; exact le_iSup F.U j hu
    have h := extendId_pow hWnd hyS1 hyS2 (u := (0 : V)) (r := u)
      (zero_mem (perp Q (⨆ j, F.U j))) hu' m
    simpa using h
  have hz1 : z = 1 := frame_one_of_triv F hzEm htriv
  have h1 : orderOf z = 1 := by rw [hz1]; exact orderOf_one
  exact hp.ne_one (by rw [← hzord]; exact h1)

theorem apply_eq_self_of_forall_apply_eq (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hmax : ∀ g ∈ orthDerived Q, (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E)
    {y : V ≃ₗ[K] V} (hyΩ : y ∈ orthDerived Q) (hyE : ∀ c ∈ E, y * c = c * y)
    (hyp : ∃ k : ℕ, y ^ p ^ k = 1) {v : V} (hv : ∀ c ∈ E, c v = v) : y v = v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hWnd := polarNondegOn_perpPieces hQ hp hp2 hEΩ F
  have hWperp := perp_perpPieces hQ F
  have hWfix := mem_perp_pieces_iff_fixed hp F
  have hvW : v ∈ perp Q (⨆ j, F.U j) := (hWfix v).mpr hv
  obtain ⟨k, hyp⟩ := hyp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero, pow_one] at hyp
    rw [hyp]
    rfl
  · by_cases hmove : ∃ w ∈ perp Q (⨆ j, F.U j), y w ≠ w
    · obtain ⟨w₀, hw₀, hw₀ne⟩ := hmove
      obtain ⟨hyS1, hyS2⟩ := stable_perpPieces_of_commute F hyE hWfix
      obtain ⟨hSW1, hSW2⟩ := stable_perpPieces_frame F hWfix hWperp
      have hy'one : extendId hWnd y hyS1 hyS2 = 1 :=
        extendId_perpPieces_eq_one hQ hT hp hp2 F hmax hyΩ hyE hyp hWnd hWperp
          hyS1 hyS2 hSW1 hSW2 hw₀ hw₀ne
      have h1 : extendId hWnd y hyS1 hyS2 v = y v := by
        simpa using extendId_apply hWnd hyS1 hyS2 hvW
          (zero_mem (perp Q (perp Q (⨆ j, F.U j))))
      rw [hy'one, LinearEquiv.coe_one, id] at h1
      exact h1.symm
    · push Not at hmove
      exact hmove v hvW

omit [Finite K] [FiniteDimensional K V] in
private theorem piece_restrict_commute (hp : p.Prime)
    (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) {g g' : V ≃ₗ[K] V} {j : Fin r}
    (hg1 : ∀ u ∈ F.U j, g u ∈ F.U j) (hg2 : ∀ u ∈ F.U j, g.symm u ∈ F.U j)
    (hg'1 : ∀ u ∈ F.U j, g' u ∈ F.U j) (hg'2 : ∀ u ∈ F.U j, g'.symm u ∈ F.U j)
    (hgE : ∀ c ∈ E, g * c = c * g) (hg'E : ∀ c ∈ E, g' * c = c * g') :
    Commute (restrictEquiv (F.U j) g hg1 hg2).toLinearMap
      (restrictEquiv (F.U j) g' hg'1 hg'2).toLinearMap := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hsj : toAdd (frameDelta (p := p) j) j ≠ 0 := by
    rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero
  have ht1 : ∀ x ∈ F.U j, F.ι (frameDelta j) x ∈ F.U j := fun x hx => F.mapsTo _ j x hx
  have ht2 : ∀ x ∈ F.U j, (F.ι (frameDelta j)).symm x ∈ F.U j := by
    have hinv : (F.ι (frameDelta j))⁻¹ = F.ι (frameDelta j) ^ (p - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, F.pow_p]
    intro x hx
    change (F.ι (frameDelta j))⁻¹ x ∈ F.U j
    rw [hinv]
    exact pow_apply_mem (fun y hy => F.mapsTo _ j y hy) (p - 1) x hx
  have hUnd : PolarNondegOn Q (F.U j) := fun x hx hper =>
    F.nondeg j x hx fun z hz => by rw [polar_comm]; exact hper z hz
  have hf : ∀ c : K,
      (restrictEquiv (F.U j) (F.ι (frameDelta j)) ht1 ht2).toLinearMap ≠ c • 1 :=
    restrictEquiv_not_scalar hUnd (F.ne_bot j)
      (orthDerived_le_orthogonalGroup (hEΩ (F.mem _))) ht1 ht2
      (fun x hx hfix => F.fpf (frameDelta j) j hsj x hx hfix)
  have hfg : Commute (restrictEquiv (F.U j) g hg1 hg2).toLinearMap
      (restrictEquiv (F.U j) (F.ι (frameDelta j)) ht1 ht2).toLinearMap := by
    rw [commute_iff_eq]
    have h := restrictEquiv_commute hg1 hg2 ht1 ht2 (hgE _ (F.mem _))
    simpa [LinearEquiv.coe_toLinearMap_mul] using congrArg LinearEquiv.toLinearMap h
  have hfg' : Commute (restrictEquiv (F.U j) g' hg'1 hg'2).toLinearMap
      (restrictEquiv (F.U j) (F.ι (frameDelta j)) ht1 ht2).toLinearMap := by
    rw [commute_iff_eq]
    have h := restrictEquiv_commute hg'1 hg'2 ht1 ht2 (hg'E _ (F.mem _))
    simpa [LinearEquiv.coe_toLinearMap_mul] using congrArg LinearEquiv.toLinearMap h
  exact CFSG.ClassicalGroups.SpecialLinear.TvMod.commute_of_commute_of_finrank_eq_two
    (hU j) hf hfg.symm hfg'.symm

omit [Finite K] in
private theorem piece_commute (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) {g g' : V ≃ₗ[K] V}
    (hgE : ∀ c ∈ E, g * c = c * g) (hg'E : ∀ c ∈ E, g' * c = c * g')
    (j : Fin r) {u : V} (hu : u ∈ F.U j) : g (g' u) = g' (g u) := by
  have hpres : ∀ (a : V ≃ₗ[K] V), (∀ c ∈ E, a * c = c * a) →
      ∀ j, ∀ u ∈ F.U j, a u ∈ F.U j := by
    intro a ha j u hu
    rw [← commSpace_frameSingle hQ hp hEΩ F j] at hu ⊢
    exact map_commSpace_of_commute (ha _ (F.mem _)) hu
  have h := congrArg (fun f : Module.End K (F.U j) => (f ⟨u, hu⟩ : V))
    ((commute_iff_eq _ _).mp (piece_restrict_commute hp hEΩ F hU
      (hpres g hgE j) (hpres g⁻¹ (fun c hc => Commute.inv_left (hgE c hc)) j)
      (hpres g' hg'E j) (hpres g'⁻¹ (fun c hc => Commute.inv_left (hg'E c hc)) j)
      hgE hg'E))
  simpa [Module.End.mul_apply, LinearEquiv.coe_toLinearMap, coe_restrictEquiv] using h

omit [Finite K] in
theorem commute_of_forall_apply_eq (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) {g g' : V ≃ₗ[K] V}
    (hgE : ∀ c ∈ E, g * c = c * g) (hg'E : ∀ c ∈ E, g' * c = c * g')
    (hgW : ∀ v, (∀ c ∈ E, c v = v) → g v = v)
    (hg'W : ∀ v, (∀ c ∈ E, c v = v) → g' v = v) : g * g' = g' * g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hWnd := polarNondegOn_perpPieces hQ hp hp2 hEΩ F
  have hWperp := perp_perpPieces hQ F
  have hWfix := mem_perp_pieces_iff_fixed hp F
  have hcompl : IsCompl (perp Q (⨆ j, F.U j)) (⨆ j, F.U j) := by
    have h := isCompl_perp hWnd; rwa [hWperp] at h
  have hUall : ∀ u ∈ ⨆ j, F.U j, g (g' u) = g' (g u) := by
    intro u hu
    refine Submodule.iSup_induction (motive := fun x => g (g' x) = g' (g x)) F.U hu ?_ ?_ ?_
    · intro j x hx
      exact piece_commute hQ hp hEΩ F hU hgE hg'E j hx
    · simp
    · intro x y hx hy
      simp only [map_add, hx, hy]
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, hw, u, hu, rfl⟩ :=
    Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hgw : g w = w := hgW w ((hWfix w).mp hw)
  have hg'w : g' w = w := hg'W w ((hWfix w).mp hw)
  simp only [LinearEquiv.mul_apply, map_add, hgw, hg'w, hUall u hu]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem exists_piece_full_order (hp : p.Prime) (F : SevOm.Frame Q p E r) {e : ℕ}
    {y : V ≃ₗ[K] V} (hy : orderOf y = p ^ e)
    (hyW : ∀ v, (∀ c ∈ E, c v = v) → y v = v)
    (hWfix : ∀ v, v ∈ perp Q (⨆ j, F.U j) ↔ ∀ c ∈ E, c v = v)
    (hcompl : IsCompl (perp Q (⨆ j, F.U j)) (⨆ j, F.U j)) (he : 0 < e) :
    ∃ j0 : Fin r, ∃ u ∈ F.U j0, (y ^ p ^ (e - 1)) u ≠ u := by
  by_contra h; push Not at h
  have h1 : y ^ p ^ (e - 1) = 1 := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, hw, u, hu, rfl⟩ :=
      Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top (x := v))
    have h2 := Submodule.iSup_induction (motive := fun x => (y ^ p ^ (e - 1)) x = x) F.U hu
      (fun j x hx => h j x hx) (by simp) (fun x y hx hy => by simp only [map_add, hx, hy])
    rw [map_add, pow_apply_of_fixed (hyW w ((hWfix w).mp hw)) (p ^ (e - 1)), h2]
    rfl
  have hdvd : orderOf y ∣ p ^ (e - 1) := orderOf_dvd_iff_pow_eq_one.mpr h1
  rw [hy] at hdvd
  have hle := Nat.le_of_dvd (pow_pos hp.pos (e - 1)) hdvd
  have hlt : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

omit [Finite K] [CharP K 2] in
private theorem extendId_piece_not_pow {S : Submodule K V} (hS : PolarNondegOn Q S)
    {a : V ≃ₗ[K] V} (h1 : ∀ u ∈ S, a u ∈ S) (h2 : ∀ u ∈ S, a.symm u ∈ S)
    {e : ℕ} {u0 : V} (hu0 : u0 ∈ S) (hne : (a ^ p ^ (e - 1)) u0 ≠ u0) :
    (extendId hS a h1 h2) ^ p ^ (e - 1) ≠ 1 := by
  intro h
  apply hne
  have h1' : (extendId hS a h1 h2 ^ p ^ (e - 1)) u0 = u0 := by rw [h]; rfl
  have h2' : (extendId hS a h1 h2 ^ p ^ (e - 1)) u0 = (a ^ p ^ (e - 1)) u0 := by
    simpa using extendId_pow hS h1 h2 (u := u0) (r := (0 : V)) hu0
      (zero_mem (perp Q S)) (p ^ (e - 1))
  rw [← h2']; exact h1'

omit [Finite K] [CharP K 2] in
private theorem extendId_piece_fix {S : Submodule K V} (hS : PolarNondegOn Q S) {a : V ≃ₗ[K] V}
    (h1 : ∀ u ∈ S, a u ∈ S) (h2 : ∀ u ∈ S, a.symm u ∈ S) :
    ∀ v, v ∈ perp Q S → extendId hS a h1 h2 v = v := by
  intro v hv
  simpa using extendId_apply hS h1 h2 (zero_mem S) hv

omit [CharP K 2] in
private theorem piece_extension (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    {e : ℕ} {y : V ≃ₗ[K] V} (hyΩ : y ∈ orthDerived Q)
    (hyE : ∀ c ∈ E, y * c = c * y) (hy : orderOf y = p ^ e)
    {j0 : Fin r} {u0 : V} (hu0 : u0 ∈ F.U j0)
    (hu0ne : (y ^ p ^ (e - 1)) u0 ≠ u0) :
    ∃ Y : V ≃ₗ[K] V, Y ∈ orthDerived Q ∧ (∀ c ∈ E, Y * c = c * Y) ∧
      Y ^ p ^ e = 1 ∧ Y ^ p ^ (e - 1) ≠ 1 ∧ ∀ v, v ∈ perp Q (F.U j0) → Y v = v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hyΩ
  obtain ⟨hU, hU'⟩ := frame_preserves_piece hQ hp hEΩ F hyE
  have hUj : PolarNondegOn Q (F.U j0) := fun x hx hper =>
    F.nondeg j0 x hx fun z hz => by rw [polar_comm]; exact hper z hz
  have hsj : toAdd (frameDelta (p := p) j0) j0 ≠ 0 := by
    rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero
  have hmove : ∃ s ∈ F.U j0, y s ≠ s := by
    by_contra h; push Not at h
    exact hu0ne (pow_apply_of_fixed (h u0 hu0) (p ^ (e - 1)))
  have hypow : y ^ p ^ e = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hblock := extendId_isBlock hUj hyO hypow (hU j0) (hU' j0) hmove
  set Y : V ≃ₗ[K] V := extendId hUj y (hU j0) (hU' j0) with hY
  have hy0Ω : Y ∈ orthDerived Q := by
    rw [hY]
    exact CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hQ hT
      ((hp.odd_of_ne_two hp2).pow) hblock.mem hblock.pow
  have hS2 := stable_perp_piece hEΩ F j0
  have hy0E : ∀ c ∈ E, Y * c = c * Y := by
    rw [hY]
    exact extendId_commute_of_stable hUj (fun c hc s hs => by
      obtain ⟨t, rfl⟩ := F.exists_eq hc; exact F.mapsTo t j0 s hs) hS2 hyE (hU j0) (hU' j0)
  have hnot : Y ^ p ^ (e - 1) ≠ 1 := by
    rw [hY]
    exact extendId_piece_not_pow hUj (hU j0) (hU' j0) hu0 hu0ne
  have hYfix : ∀ v, v ∈ perp Q (F.U j0) → Y v = v := by
    rw [hY]
    exact extendId_piece_fix hUj (hU j0) (hU' j0)
  exact ⟨Y, hy0Ω, hy0E, by rw [hY]; exact hblock.pow, hnot, hYfix⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem orderOf_piece_extension (hp : p.Prime) {e : ℕ} (he : 0 < e) {Y : V ≃ₗ[K] V}
    (hfin : Y ^ p ^ e = 1) (hnot : Y ^ p ^ (e - 1) ≠ 1) : orderOf Y = p ^ e := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have he' : (e - 1) + 1 = e := Nat.sub_one_add_one he.ne'
  have hfin' : Y ^ p ^ ((e - 1) + 1) = 1 := by rw [he']; exact hfin
  have h := orderOf_eq_prime_pow (n := e - 1) hnot hfin'
  simpa only [he'] using h

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem conj_central (hp : p.Prime) (F : SevOm.Frame Q p E r) {w : V ≃ₗ[K] V}
    (hwE : ∀ c ∈ E, w * c * w⁻¹ ∈ E) {Y : V ≃ₗ[K] V}
    (hYE : ∀ c ∈ E, Y * c = c * Y) :
    ∀ c ∈ E, (w * Y * w⁻¹) * c = c * (w * Y * w⁻¹) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro c hc
  have hsurj : ∃ c' ∈ E, w * c' * w⁻¹ = c := by
    haveI : Finite E := Finite.of_surjective
      (fun s : Multiplicative (Fin r → ZMod p) => (⟨F.ι s, F.mem s⟩ : E))
      (fun x => by obtain ⟨s, hs⟩ := F.exists_eq x.2; exact ⟨s, Subtype.ext hs⟩)
    let φ : E → E := fun x => ⟨w * (x : V ≃ₗ[K] V) * w⁻¹, hwE x x.2⟩
    have hφinj : Function.Injective φ := by
      intro x y hxy
      have h := congrArg (fun z : E => w⁻¹ * (z : V ≃ₗ[K] V) * w) hxy
      simpa [φ, mul_assoc] using h
    obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hφinj ⟨c, hc⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  obtain ⟨c', hc', rfl⟩ := hsurj
  calc w * Y * w⁻¹ * (w * c' * w⁻¹) = w * (Y * c') * w⁻¹ := by group
    _ = w * (c' * Y) * w⁻¹ := by rw [hYE c' hc']
    _ = (w * c' * w⁻¹) * (w * Y * w⁻¹) := by group

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem conj_fixed (F : SevOm.Frame Q p E r) {j0 k : Fin r} {Y w : V ≃ₗ[K] V}
    (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hwUk : (F.U j0).map (w : V →ₗ[K] V) = F.U k)
    (hYfix : ∀ v, v ∈ perp Q (F.U j0) → Y v = v) :
    ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → (w * Y * w⁻¹) v = v := by
  intro v hv
  have hv' : w.symm v ∈ perp Q (F.U j0) := by
    rw [mem_perp]
    intro u hu
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hwO u (w.symm v)
    rw [w.apply_symm_apply] at h1
    rw [← h1]
    exact hv _ (hwUk ▸ Submodule.mem_map_of_mem hu)
  have hYv : Y (w.symm v) = w.symm v := hYfix (w.symm v) hv'
  change w (Y (w.symm v)) = v
  rw [hYv, w.apply_symm_apply]

theorem exists_piece_orderOf (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (htr : ∀ j k : Fin r, ∃ w ∈ orthDerived Q, (∀ c ∈ E, w * c * w⁻¹ ∈ E) ∧
      w * F.ι (ofAdd (Pi.single j 1)) * w⁻¹ = F.ι (ofAdd (Pi.single k 1)))
    {e : ℕ} {y : V ≃ₗ[K] V} (hyΩ : y ∈ orthDerived Q) (hyE : ∀ c ∈ E, y * c = c * y)
    (hy : orderOf y = p ^ e) (hyW : ∀ v, (∀ c ∈ E, c v = v) → y v = v) (k : Fin r) :
    ∃ z ∈ orthDerived Q, (∀ c ∈ E, z * c = c * z) ∧ orderOf z = p ^ e ∧
      ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hWnd := polarNondegOn_perpPieces hQ hp hp2 hEΩ F
  have hWperp := perp_perpPieces hQ F
  have hWfix := mem_perp_pieces_iff_fixed hp F
  have hcompl : IsCompl (perp Q (⨆ j, F.U j)) (⨆ j, F.U j) := by
    have h := isCompl_perp hWnd; rwa [hWperp] at h
  rcases Nat.eq_zero_or_pos e with he | he
  · rw [he, pow_zero] at hy
    exact ⟨1, one_mem _, fun c hc => by simp, by rw [he, pow_zero]; exact orderOf_one,
      fun v _ => by simp⟩
  obtain ⟨j0, u0, hu0, hu0ne⟩ := exists_piece_full_order hp F hy hyW hWfix hcompl he
  obtain ⟨Y, hYΩ, hYE, hYfin, hYnot, hYfix⟩ :=
    piece_extension hQ hT hp hp2 hEΩ F hyΩ hyE hy hu0 hu0ne
  have hYord : orderOf Y = p ^ e := orderOf_piece_extension hp he hYfin hYnot
  obtain ⟨w, hwΩ, hwE, hwt⟩ := htr j0 k
  have hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hwΩ
  have hwUk : (F.U j0).map (w : V →ₗ[K] V) = F.U k := by
    rw [← commSpace_frameSingle hQ hp hEΩ F j0, ← commSpace_frameSingle hQ hp hEΩ F k,
      ← hwt, commSpace_conj]
  refine ⟨w * Y * w⁻¹, mul_mem (mul_mem hwΩ hYΩ) (inv_mem hwΩ),
    conj_central hp F hwE hYE, ?_, conj_fixed F hwO hwUk hYfix⟩
  rw [show w * Y * w⁻¹ = MulAut.conj w Y from (MulAut.conj_apply w Y).symm,
    MulEquiv.orderOf_eq]
  exact hYord

end CFSG.StandardType.OrthTorusGen
