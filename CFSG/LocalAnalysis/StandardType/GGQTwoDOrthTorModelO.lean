module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorModelV
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorOmega
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorModelOAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open TauCeti.QuadraticMap QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

section ModelO

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

private noncomputable def plhPsi (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1) :
    ↥(orthogonalGroup (Qn E a)) →* ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)) where
  toFun h :=
    ⟨LinearEquiv.ofLinearMap (plhPsiLinear E m a ha h) (plhPsiLinear E m a ha h⁻¹)
        (plhPsiLinear_comp E m a ha h) (plhPsiLinear_comp' E m a ha h),
      plhPsiEquiv_mem E hζ m a ha h⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) +
      (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) = v
    abel
  map_mul' h₁ h₂ := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change plhPsiLinear E m a ha (h₁ * h₂) v =
      plhPsiLinear E m a ha h₁ (plhPsiLinear E m a ha h₂ v)
    rw [plhPsiLinear_apply, plhPsiLinear_apply, plhPsiLinear_apply, Subgroup.coe_mul,
      LinearEquiv.mul_apply]
    rw [show plhRes (F := F) (K := K) m a ha (plhExt (F := F) (K := K) m a ha
        (h₂.1 (plhRes (F := F) (K := K) m a ha v)) +
        (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v))) =
        h₂.1 (plhRes (F := F) (K := K) m a ha v) from by
      rw [map_add, plhRes_plhExt, plhRes_eq_zero_of_mem_torStdV₁ (F := F) (K := K) m a ha
        (plh_sub_plhExt_plhRes_mem_torStdV₁ (F := F) (K := K) m a ha v), add_zero]]
    abel

private theorem plhPsi_plhPhi (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) :
    plhPsi E hζ m a ha (plhPhi E hζ m a ha g) = g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change plhPsiLinear E m a ha (plhPhi E hζ m a ha g) v = g.1 v
  rw [plhPsiLinear_apply]
  change plhExt (F := F) (K := K) m a ha
      (plhToEquiv E hζ m a ha g (plhRes (F := F) (K := K) m a ha v)) +
      (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) = g.1 v
  rw [plhToEquiv_apply]
  have hV₁ : torV₁ (torStdM (F := F) ζ m a) = torStdV₁ (F := F) (K := K) m a := torV₁_torStdM hζ m a
  have ht : v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) ∈
      torV₁ (torStdM (F := F) ζ m a) := by
    rw [hV₁]
    exact plh_sub_plhExt_plhRes_mem_torStdV₁ (F := F) (K := K) m a ha v
  have hw : g.1 (plhExt (F := F) (K := K) m a ha
      (plhRes (F := F) (K := K) m a ha v)) ∈ torStdV₀ (F := F) (K := K) m a :=
    plh_mem_torStdV₀_of_mem_torE₀ E hζ m a ha g.2
      (plhExt_mem_torStdV₀ (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v))
  simp only [plhExt_plhRes_of_mem_torStdV₀ (F := F) (K := K) m a ha hw]
  conv_rhs => rw [show v = plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) +
      (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) from by abel,
    map_add, g.2.2 _ ht]

private theorem plhPhi_plhPsi (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (h : ↥(orthogonalGroup (Qn E a))) :
    plhPhi E hζ m a ha (plhPsi E hζ m a ha h) = h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change plhToEquiv E hζ m a ha (plhPsi E hζ m a ha h) z = h.1 z
  rw [plhToEquiv_apply]
  change plhRes (F := F) (K := K) m a ha
      (plhPsiLinear E m a ha h (plhExt (F := F) (K := K) m a ha z)) = h.1 z
  rw [plhPsiLinear_apply, map_add]
  simp only [plhRes_plhExt, sub_self, map_zero, add_zero]

private theorem plh_qtwoStdWin_smul (m a len : ℕ) (h : a + len ≤ m + 1)
    (x : Su K 2 1 len) (c : K) (v : Fin (m + 1) → K) :
    qtwoStdWin (F := F) (K := K) m a len h x (c • v) =
      c • qtwoStdWin (F := F) (K := K) m a len h x v := by
  change suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
      (blockEmb K 2 1 (m + 1) len a h x) (c • v) =
    c • suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
      (blockEmb K 2 1 (m + 1) len a h x) v
  rw [suEndN_apply, suEndN_apply]
  exact smul_comm _ c v

private theorem plhToLinear_smul (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)))
    (hgK : ∀ (c : K) (w : Fin (m + 1) → K), g.1 (c • w) = c • g.1 w)
    (c : K) (z : Fin a → K) :
    plhToLinear E hζ m a ha g (c • z) = c • plhToLinear E hζ m a ha g z := by
  rw [plhToLinear_apply, plhToLinear_apply, plhExt_smul, hgK, plhRes_smul]

private theorem plh_qtwoStdWin_mem_torE₀ (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha3 : 3 ≤ a)
    (ha : a ≤ m + 1) (x : Su K 2 1 3) :
    qtwoStdWin (F := F) (K := K) m 0 3 (by omega) x ∈
      torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a) := by
  have h3 : (0 : ℕ) + 3 ≤ m + 1 := by omega
  refine ⟨?_, ?_⟩
  · change suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
        (blockEmb K 2 1 (m + 1) 3 0 h3 x) ∈ orthogonalGroup (Qn E (m + 1))
    exact suEndN_mem_orthogonalGroup E (m + 1) _
  · rw [torV₁_torStdM hζ m a]
    intro v hv
    change suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
        (blockEmb K 2 1 (m + 1) 3 0 h3 x) v = v
    rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb]
    funext i
    by_cases hi : i.val < 3
    · have hix : blockIdx (0 : ℕ) h3 ⟨i.val, hi⟩ = i := Fin.ext (by simp)
      rw [← hix, blockMat_mulVec_blockIdx h3]
      have hb : (fun y : Fin 3 => v (blockIdx (0 : ℕ) h3 y)) = 0 := by
        funext y
        rw [Pi.zero_apply]
        exact hv _ (by rw [blockIdx_val]; omega)
      rw [hb, Matrix.mulVec_zero, Pi.zero_apply]
      exact (hv (blockIdx (0 : ℕ) h3 ⟨i.val, hi⟩) (by rw [blockIdx_val]; omega)).symm
    · exact blockMat_mulVec_of_not_mem _ _ (fun hcon => hi hcon.2)

private theorem plhPhi_map_commutator (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1) :
    (commutator ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))).map
        (plhPhi E hζ m a ha) =
      commutator ↥(orthogonalGroup (Qn E a)) := by
  have hsurj : Function.Surjective (plhPhi E hζ m a ha) :=
    fun h => ⟨plhPsi E hζ m a ha h, plhPhi_plhPsi E hζ m a ha h⟩
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr hsurj]
  rfl

private theorem plh_mem_torP₀_of_mem_orthDerived (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)))
    (hg : ((plhPhi E hζ m a ha g : ↥(orthogonalGroup (Qn E a))) :
        (Fin a → K) ≃ₗ[F] (Fin a → K)) ∈ orthDerived (Qn E a)) :
    (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      torP₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a) := by
  have hinj : Function.Injective (plhPhi E hζ m a ha) := by
    intro x y hxy
    have h := congrArg (plhPsi E hζ m a ha) hxy
    rwa [plhPsi_plhPhi E hζ m a ha x, plhPsi_plhPhi E hζ m a ha y] at h
  have hmemO : (plhPhi E hζ m a ha g) ∈ commutator ↥(orthogonalGroup (Qn E a)) := by
    have hmap : orthDerived (Qn E a) = (commutator ↥(orthogonalGroup (Qn E a))).map
        (orthogonalGroup (Qn E a)).subtype := (Subgroup.map_subtype_commutator _).symm
    rw [hmap, Subgroup.mem_map] at hg
    obtain ⟨y, hy, hyh⟩ := hg
    have hy' : y = plhPhi E hζ m a ha g := Subtype.ext hyh
    rwa [hy'] at hy
  have hmemE : g ∈ commutator ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)) := by
    have h2 : (plhPhi E hζ m a ha g) ∈
        (commutator ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))).map
          (plhPhi E hζ m a ha) := by
      rw [plhPhi_map_commutator E hζ m a ha]
      exact hmemO
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp h2
    have hx' : x = g := hinj hxg
    rwa [hx'] at hx
  have hmemP : (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      (commutator ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))).map
        (torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)).subtype :=
    Subgroup.mem_map.mpr ⟨g, hmemE, rfl⟩
  rwa [Subgroup.map_subtype_commutator] at hmemP

theorem torStdM_P₀_equiv (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1) :
    Nonempty (↥(torP₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)) ≃* ↥(orthDerived (Qn E a))) := by
  let E₀ := torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)
  let O := orthogonalGroup (Qn E a)
  have hΦ : ↥E₀ ≃* ↥O :=
    (plhPhi E hζ m a ha).toMulEquiv (plhPsi E hζ m a ha)
      (MonoidHom.ext fun g => plhPsi_plhPhi E hζ m a ha g)
      (MonoidHom.ext fun h => plhPhi_plhPsi E hζ m a ha h)
  have hCEsub : (commutator ↥E₀).map E₀.subtype =
      torP₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a) := by
    rw [Subgroup.map_subtype_commutator]
    rfl
  have hCOsub : (commutator ↥O).map O.subtype = orthDerived (Qn E a) := by
    rw [Subgroup.map_subtype_commutator]
  have hΦcomm : (commutator ↥E₀).map hΦ.toMonoidHom = commutator ↥O := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hΦ.surjective]
    rfl
  let eE : ↥(torP₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)) ≃* ↥(commutator ↥E₀) :=
    (hCEsub ▸ Subgroup.equivMapOfInjective (commutator ↥E₀) E₀.subtype
      E₀.subtype_injective).symm
  let eComm : ↥(commutator ↥E₀) ≃* ↥(commutator ↥O) :=
    (MulEquiv.subgroupMap hΦ (commutator ↥E₀)).trans (MulEquiv.subgroupCongr hΦcomm)
  let eO : ↥(commutator ↥O) ≃* ↥(orthDerived (Qn E a)) :=
    hCOsub ▸ Subgroup.equivMapOfInjective (commutator ↥O) O.subtype O.subtype_injective
  exact ⟨eE.trans (eComm.trans eO)⟩

theorem torStdM_win_zero_le_P₀ (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ)
    (ha3 : 3 ≤ a) (ha : a ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m 0 3 (by omega)).range ≤
      torP₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a) := by
  rintro g ⟨x, rfl⟩
  have hwin : qtwoStdWin (F := F) (K := K) m 0 3 (by omega) x ∈
      torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a) :=
    plh_qtwoStdWin_mem_torE₀ E hζ m a ha3 ha x
  have hK : ∀ (c : K) (z : Fin a → K),
      (plhPhi E hζ m a ha ⟨qtwoStdWin (F := F) (K := K) m 0 3 (by omega) x, hwin⟩ :
          ↥(orthogonalGroup (Qn E a))).1 (c • z) =
        c • (plhPhi E hζ m a ha ⟨qtwoStdWin (F := F) (K := K) m 0 3 (by omega) x, hwin⟩ :
          ↥(orthogonalGroup (Qn E a))).1 z := by
    intro c z
    exact plhToLinear_smul E hζ m a ha ⟨qtwoStdWin (F := F) (K := K) m 0 3 (by omega) x, hwin⟩
      (fun c w => plh_qtwoStdWin_smul m 0 3 (by omega) x c w) c z
  have hder : ((plhPhi E hζ m a ha ⟨qtwoStdWin (F := F) (K := K) m 0 3 (by omega) x, hwin⟩ :
      ↥(orthogonalGroup (Qn E a))) : (Fin a → K) ≃ₗ[F] (Fin a → K)) ∈ orthDerived (Qn E a) :=
    torOmega_klinear_le_orthDerived E hF ha3
      (plhPhi E hζ m a ha ⟨qtwoStdWin (F := F) (K := K) m 0 3 (by omega) x, hwin⟩).2 hK
  exact plh_mem_torP₀_of_mem_orthDerived E hζ m a ha _ hder


end ModelO

end CFSG.StandardType.QTwo

end
