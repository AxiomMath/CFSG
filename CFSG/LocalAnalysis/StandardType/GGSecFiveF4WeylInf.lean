module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4WeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylInfDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveAInfLin
import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroF4Adapt
import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCartan
import CFSG.LocalAnalysis.StandardType.GGF4EndpointType
import CFSG.LocalAnalysis.StandardType.GGSecFiveF4ReflMax
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylF4
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroup
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroupIrred
import CFSG.LocalAnalysis.StandardType.ZS.ExcB3
import CFSG.LocalAnalysis.StandardType.ZS.B3Chain
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImage
import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageOfPosition
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.StandardType

section Linear

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem false_of_two_sgn_commuters (hp2 : p ≠ 2)
    (b : Module.Basis (Fin 4) (ZMod p) U) {A W C : Subgroup (U ≃ₗ[ZMod p] U)}
    (hsat : ∀ r ∈ A, ZS.IsRefl p r → r (b 3) = b 3 → r ∈ W)
    (hWfix : ∀ r ∈ W, ZS.IsRefl p r → r (b 3) = b 3 → r ∈ C)
    {s1 s2 : U ≃ₗ[ZMod p] U} (hs1A : s1 ∈ A) (hs2A : s2 ∈ A) (hne : s1 ≠ s2)
    (hs1refl : ZS.IsRefl p s1) (hs2refl : ZS.IsRefl p s2)
    (hc1 : Commute s1 (ZS.diagMap p b (fun j => if j = 3 then 1 else -1)))
    (hc2 : Commute s2 (ZS.diagMap p b (fun j => if j = 3 then 1 else -1)))
    (hs1not : s1 ∉ C) (hs2not : s2 ∉ C) : False := by
  have hmem : ∀ s ∈ A, ZS.IsRefl p s → s (b 3) = b 3 → s ∈ C := fun s hsA hsrefl hfix =>
    hWfix s (hsat s hsA hsrefl hfix) hsrefl hfix
  have hcase1 := ZS.fix_or_eq_sgn_of_commute hp2 b 3 hs1refl hc1
  have hcase2 := ZS.fix_or_eq_sgn_of_commute hp2 b 3 hs2refl hc2
  by_cases hfix1 : s1 (b 3) = b 3
  · exact hs1not (hmem s1 hs1A hs1refl hfix1)
  · have hsgn1 : s1 = ZS.diagMap p b (fun j => if j = 3 then -1 else 1) := by
      rcases hcase1 with h | h
      · exact absurd h hfix1
      · exact h
    have hfix2 : s2 (b 3) = b 3 := by
      by_contra hnot
      have hsgn2 : s2 = ZS.diagMap p b (fun j => if j = 3 then -1 else 1) := by
        rcases hcase2 with h | h
        · exact absurd h hnot
        · exact h
      exact hne (hsgn1.trans hsgn2.symm)
    exact hs2not (hmem s2 hs2A hs2refl hfix2)

private theorem false_of_excRow_of_F4 (hp2 : p ≠ 2)
    (b : Module.Basis (Fin 4) (ZMod p) U) {A W : Subgroup (U ≃ₗ[ZMod p] U)} (hWA : W ≤ A)
    (hperm : ∀ σ, ZS.permMap p b σ ∈ W)
    (hsgn : ∀ i, ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈ W)
    (h1152 : 1152 ∣ Nat.card A)
    (hsat : ∀ r ∈ A, ZS.IsRefl p r → r (b 3) = b 3 → r ∈ W)
    (hWfix : ∀ r ∈ W, ZS.IsRefl p r → r (b 3) = b 3 →
      r ∈ Subgroup.closure {ZS.permMap p b (Equiv.swap 0 1), ZS.permMap p b (Equiv.swap 1 2),
        ZS.diagMap p b (fun j => if j = 2 then -1 else 1)})
    {k : ZS.ExcRow} (hk : k = .N4 ∨ k = .EN4) (hcard : Nat.card A = k.ord)
    (hone : ZS.OneClass p A) (hmod : ZS.ModelIso p k A) : False := by
  rcases hk with rfl | rfl
  · rw [hcard] at h1152
    norm_num [ZS.ExcRow.ord] at h1152
  · have hr1W : ZS.permMap p b (Equiv.swap 0 1) ∈ W := hperm _
    have hr2W : ZS.permMap p b (Equiv.swap 1 2) ∈ W := hperm _
    have hr3W : ZS.diagMap p b (fun j => if j = 2 then -1 else 1) ∈ W := hsgn 2
    have hr1A : ZS.permMap p b (Equiv.swap 0 1) ∈ A := hWA hr1W
    have hr2A : ZS.permMap p b (Equiv.swap 1 2) ∈ A := hWA hr2W
    have hr3A : ZS.diagMap p b (fun j => if j = 2 then -1 else 1) ∈ A := hWA hr3W
    have hr1refl : ZS.IsRefl p (ZS.permMap p b (Equiv.swap 0 1)) :=
      ZS.isRefl_permMap_swap b (i := 0) (j := 1) (by decide)
    have hr2refl : ZS.IsRefl p (ZS.permMap p b (Equiv.swap 1 2)) :=
      ZS.isRefl_permMap_swap b (i := 1) (j := 2) (by decide)
    have hr3refl : ZS.IsRefl p (ZS.diagMap p b (fun j => if j = 2 then -1 else 1)) :=
      ZS.isRefl_diagMap_sign hp2 b 2
    obtain ⟨h12, h23, h13⟩ := ZS.orderOf_b3Chain hp2 b 3
    have hsa0 : (3 : Fin 4).succAbove 0 = 0 := by decide
    have hsa1 : (3 : Fin 4).succAbove 1 = 1 := by decide
    have hsa2 : (3 : Fin 4).succAbove 2 = 2 := by decide
    have h12' : orderOf (ZS.permMap p b (Equiv.swap 0 1) *
        ZS.permMap p b (Equiv.swap 1 2)) = 3 := by
      simpa only [hsa0, hsa1, hsa2] using h12
    have h23' : orderOf (ZS.permMap p b (Equiv.swap 1 2) *
        ZS.diagMap p b (fun j => if j = 2 then -1 else 1)) = 4 := by
      simpa only [hsa1, hsa2] using h23
    have h13' : orderOf (ZS.permMap p b (Equiv.swap 0 1) *
        ZS.diagMap p b (fun j => if j = 2 then -1 else 1)) = 2 := by
      simpa only [hsa0, hsa1, hsa2] using h13
    obtain ⟨s1, hs1A, s2, hs2A, hne, hs1refl, hs2refl, hc1, hc2, hs1not, hs2not⟩ :=
      ZS.exists_two_refl_commute_not_mem_of_EN4 hone hmod hr1A hr2A hr3A hr1refl hr2refl hr3refl
        h12' h23' h13'
    have hz : (ZS.permMap p b (Equiv.swap 0 1) * ZS.permMap p b (Equiv.swap 1 2) *
        ZS.diagMap p b (fun j => if j = 2 then -1 else 1)) ^ 3 =
        ZS.diagMap p b (fun j => if j = 3 then 1 else -1) := by
      simpa only [hsa0, hsa1, hsa2] using ZS.b3Chain_cube b 3
    rw [hz] at hc1 hc2
    exact false_of_two_sgn_commuters hp2 b hsat hWfix hs1A hs2A hne hs1refl hs2refl hc1 hc2
      hs1not hs2not

private theorem exists_diagMap_mul_permMap_of_mem_b3closure
    (b : Module.Basis (Fin 4) (ZMod p) U) {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ Subgroup.closure {ZS.permMap p b (Equiv.swap 0 1),
      ZS.permMap p b (Equiv.swap 1 2),
      ZS.diagMap p b (fun j => if j = 2 then -1 else 1)}) :
    ∃ (d : Fin 4 → (ZMod p)ˣ) (σ : Equiv.Perm (Fin 4)),
      g = ZS.diagMap p b d * ZS.permMap p b σ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, Equiv.swap 0 1, by rw [ZS.diagMap_one, one_mul]⟩
      · exact ⟨1, Equiv.swap 1 2, by rw [ZS.diagMap_one, one_mul]⟩
      · exact ⟨fun j => if j = 2 then -1 else 1, 1, by rw [ZS.permMap_one, mul_one]⟩
  | one => exact ⟨1, 1, by rw [ZS.diagMap_one, ZS.permMap_one, one_mul]⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨dx, σx, rfl⟩ := ihx
      obtain ⟨dy, σy, rfl⟩ := ihy
      exact ⟨dx * (dy ∘ σx.symm), σx * σy, ZS.mul_diagMap_permMap b dx dy σx σy⟩
  | inv x _ ihx =>
      obtain ⟨dx, σx, rfl⟩ := ihx
      exact ⟨dx⁻¹ ∘ σx, σx⁻¹, ZS.inv_diagMap_permMap b dx σx⟩

private theorem monomial_of_mem_b3closure (b : Module.Basis (Fin 4) (ZMod p) U)
    {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ Subgroup.closure {ZS.permMap p b (Equiv.swap 0 1),
      ZS.permMap p b (Equiv.swap 1 2),
      ZS.diagMap p b (fun j => if j = 2 then -1 else 1)}) :
    ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, g (b i) = c i • b (σ i) := by
  obtain ⟨d, σ, rfl⟩ := exists_diagMap_mul_permMap_of_mem_b3closure b hg
  exact ⟨σ, fun i => (d (σ i) : ZMod p), fun i => (d (σ i)).ne_zero, fun i => by
    rw [LinearEquiv.mul_apply, ZS.permMap_apply_basis, ZS.diagMap_apply_basis]⟩

private theorem linWeyl_or_orth_of_F4_coords (hp2 : p ≠ 2)
    (b : Module.Basis (Fin 4) (ZMod p) U) {A W : Subgroup (U ≃ₗ[ZMod p] U)} (hWA : W ≤ A)
    (hfam : ZS.Family p A) (hirr : ZS.AbsIrred p A)
    (hperm : ∀ σ, ZS.permMap p b σ ∈ W)
    (hsgn : ∀ i, ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈ W)
    (h1152 : 1152 ∣ Nat.card A)
    (htv : ∀ τ ∈ A,
      Module.finrank (ZMod p) (LinearMap.range ((τ : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v)
    (hnm : ∃ r ∈ W, ¬ ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, r (b i) = c i • b (σ i))
    (hsat : ∀ r ∈ A, ZS.IsRefl p r → r (b 3) = b 3 → r ∈ W)
    (hWfix : ∀ r ∈ W, ZS.IsRefl p r → r (b 3) = b 3 →
      r ∈ Subgroup.closure {ZS.permMap p b (Equiv.swap 0 1), ZS.permMap p b (Equiv.swap 1 2),
        ZS.diagMap p b (fun j => if j = 2 then -1 else 1)}) :
    ZS.LinWeyl p A ∨ (p = 3 ∧ ∃ Q : QuadraticForm (ZMod p) U,
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ P : Submodule (ZMod p) U, Module.finrank (ZMod p) P = 2 ∧ ∀ w ∈ P, Q w = 0) ∧
      ∀ g, g ∈ A ↔ ZS.IsIsom p Q g) := by
  have hdvd : 2 ^ 4 * Nat.factorial 4 ∣ Nat.card A :=
    dvd_trans (by norm_num : 2 ^ 4 * Nat.factorial 4 ∣ 1152) h1152
  rcases ZS.linWeyl_or_cases_of_signed_four hp2 b hfam hirr (fun σ => hWA (hperm σ))
    (fun i => hWA (hsgn i)) hdvd htv 3 with
    hW | ⟨-, ⟨r, hr, hrefl, hr3, hrmon⟩, -⟩ | ⟨hmon, -⟩ | ⟨hp3, Q, hQ, hplane, hA⟩ |
      ⟨k, hk, hcard, -, hone, hmod, -⟩
  · exact Or.inl hW
  · obtain ⟨σ, c, -, hact⟩ :=
      monomial_of_mem_b3closure b (hWfix r (hsat r hr hrefl hr3) hrefl hr3)
    exact (hrmon ⟨σ, c, hact⟩).elim
  · obtain ⟨r, hrW, hrmon⟩ := hnm
    obtain ⟨σ, c, hc, hact⟩ := hmon r (hWA hrW)
    exact (hrmon ⟨σ, c, hc, hact⟩).elim
  · exact Or.inr ⟨hp3, Q, hQ, hplane, hA⟩
  · exact (false_of_excRow_of_F4 hp2 b hWA hperm hsgn h1152 hsat hWfix hk hcard hone hmod).elim

end Linear

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

private theorem exists_endpointRefl_of_F4
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hWL : GGWeylReflectionGroup p (ggAutomizer L Bs)) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (hx : x ∈ Bs) :
    ∃ t ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection p t ∧ t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹ := by
  obtain ⟨hp, hBs, -, -, h4⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨t, ht, htr, htx, -, -⟩ :=
    ggF4_exists_endpointRefl (p := p) (A := ggAutomizerJoin L Bs 𝒦) hp2 hBs h4
      hR.1.2.2.2.1 (ggAutomizerJoin_le_ggInduced_top L 𝒦) (M := M) (e := e) hP hM
      (hR.eq_one_of_forall_join_fix hTBF hWI) (X := ggAutomizer L Bs)
      (le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦)
      hWL hx hR.1.1.1.2.2.2.2.2.2.1.2.2.1
      (GGSecFiveRestHyp.fixLineComp_L hTBF hR.1 hR.2.1).fix_iff
  exact ⟨t, ht, htr, htx⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem exists_coords_sgn_three_of_F4 [Fact p.Prime] [Finite V]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (ιV : Additive ↥Bs ≃+ V) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizerJoin L Bs 𝒦)
    (htr : GGIsReflection p t) :
    ∃ (e' : Fin 4 → V) (φ : Fin 4 → Module.Dual (ZMod p) V), GGCZDual e' φ ∧
      (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) = ggCZWF4 p e' φ ∧
      ∀ v, ggLin (p := p) ιV t v = v - (2 * φ 3 v) • e' 3 := by
  obtain ⟨-, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨σ, rfl⟩ := hM
  let Θ : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦) :=
    ((CoxeterMatrix.F₄.reindexGroupEquiv σ).symm).trans e
  have hf : ∀ i : Fin 4, GGIsReflection p
      ((Θ (CoxeterMatrix.F₄.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    intro i
    have hΘ : Θ (CoxeterMatrix.F₄.simple i) =
        e ((CoxeterMatrix.F₄.reindex σ).simple (σ i)) := by
      simp [Θ, CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]
    rw [hΘ]
    exact hP.2 (σ i)
  obtain ⟨e0, φ0, hd, -, hmap⟩ :=
    ggCZ_coordsF4 (p := p) (Bs := Bs) hp2 hR.1.2.2.2.1
      (ggAutomizerJoin_le_ggInduced_top L 𝒦) Θ hf ιV
  have hT : ggLin (p := p) ιV t ∈ ggCZWF4 p e0 φ0 := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ ht
  have hTr : GGLinRefl (ggLin (p := p) ιV t) :=
    (ggIsReflection_iff_ggLinRefl hp2 ιV t).mp htr
  obtain ⟨e', φ', hd', hW', hform⟩ :=
    ggCZ_exists_coords_sgn_three (p := p) hp2 hd hT hTr
  exact ⟨e', φ', hd', hmap.trans hW'.symm, hform⟩

omit [Finite G] in
private theorem ofMul_eq_smul_of_sgn_three [Fact p.Prime] (hp2 : p ≠ 2) (ιV : Additive ↥Bs ≃+ V)
    {e' : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} {t : MulAut ↥Bs}
    (ht : ∀ v, ggLin (p := p) ιV t v = v - (2 * φ 3 v) • e' 3) (hx : x ∈ Bs)
    (htx : t ⟨x, hx⟩ = ⟨x, hx⟩⁻¹) :
    ιV (Additive.ofMul ⟨x, hx⟩) = φ 3 (ιV (Additive.ofMul ⟨x, hx⟩)) • e' 3 := by
  set v : V := ιV (Additive.ofMul ⟨x, hx⟩) with hv
  have hneg : ggLin (p := p) ιV t v = -v := by
    rw [hv, ggLin_apply_ofMul, htx, ← map_neg, ← ofMul_inv]
  have hmain : v - (2 * φ 3 v) • e' 3 = -v := by
    rw [← ht v]
    exact hneg
  have h2v : (2 : ZMod p) • v = (2 * φ 3 v) • e' 3 := by
    have h1 : v = -v + (2 * φ 3 v) • e' 3 := (sub_eq_iff_eq_add).mp hmain
    have hvv : v + v = (2 * φ 3 v) • e' 3 := by
      calc
        v + v = (-v + (2 * φ 3 v) • e' 3) + v := congrArg (fun x => x + v) h1
        _ = (2 * φ 3 v) • e' 3 := by abel
    rw [two_smul, hvv]
  have h2 : (2 : ZMod p) • v = (2 : ZMod p) • (φ 3 v • e' 3) := by
    rw [← mul_smul]
    exact h2v
  calc
    v = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • v) := by
      rw [smul_smul, inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_smul]
    _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • (φ 3 v • e' 3)) := by rw [h2]
    _ = φ 3 v • e' 3 := by
      rw [smul_smul, inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_smul]

private theorem sat_map_of_F4 [Fact p.Prime] [Finite V] (hp2 : p ≠ 2)
    (hSat : GGSecFiveF4ReflSatInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (ιV : Additive ↥Bs ≃+ V) (hx : x ∈ Bs) (b : Module.Basis (Fin 4) (ZMod p) V) {c : ZMod p}
    (hxb : ιV (Additive.ofMul ⟨x, hx⟩) = c • b 3) :
    ∀ r ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV), ZS.IsRefl p r → r (b 3) = b 3 →
      r ∈ (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) := by
  intro r hr hrefl hfix
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hr
  have hφfix : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    refine (ggLin_fix_iff (p := p) ιV φ ⟨x, hx⟩).mpr ?_
    rw [hxb, map_smul, hfix]
  have hφrefl : GGIsReflection p φ :=
    (ggIsReflection_iff_ggLinRefl hp2 ιV φ).mpr hrefl
  exact Subgroup.mem_map_of_mem _ <|
    hSat G p B Bs x L D J 𝒦 hR ι M e hP hM hx φ hφ hφrefl hφfix

private theorem finrank_eq_four_of_F4 [Fact p.Prime] [Finite V]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (ιV : Additive ↥Bs ≃+ V) : Module.finrank (ZMod p) V = 4 := by
  obtain ⟨-, -, -, -, h4⟩ := hR.1.1.tableB_facts
  have hcardBs : Nat.card ↥Bs = p ^ 4 :=
    le_antisymm (hR.card_eq_of_typeF4 hTBF hWI e hP hM).2 h4
  have hVcard : Nat.card V = p ^ 4 := by
    rw [← card_eq_of_ggLin ιV]
    exact hcardBs
  have hVp : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    let : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card]
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := V)
    rwa [ZMod.card] at h
  have hpow : p ^ 4 = p ^ Module.finrank (ZMod p) V := by
    rw [← hVcard, hVp]
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hpow).symm

private theorem weyl_of_F4_coords [Fact p.Prime] [Finite V] [Module.Finite (ZMod p) V]
    (hp2 : p ≠ 2)
    (ιV : Additive ↥Bs ≃+ V) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hfr : Module.finrank (ZMod p) V = 4)
    {e' : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} (hd : GGCZDual e' φ)
    (hmap : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) = ggCZWF4 p e' φ)
    (b : Module.Basis (Fin 4) (ZMod p) V) (hb : ∀ i, b i = e' i)
    (hfam : ZS.Family p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)))
    (hirr : ZS.AbsIrred p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)))
    (h1152 : 1152 ∣ Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)))
    (htv : ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV),
      Module.finrank (ZMod p) (LinearMap.range ((τ : V →ₗ[ZMod p] V) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v)
    (hsat : ∀ r ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV), ZS.IsRefl p r →
      r (b 3) = b 3 → r ∈ (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV)) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  have hWA : ggCZWF4 p e' φ ≤ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV) := by
    rw [← hmap]
    exact Subgroup.map_mono (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1)
  have hsatW : ∀ r ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV),
      ZS.IsRefl p r → r (b 3) = b 3 → r ∈ ggCZWF4 p e' φ := by
    intro r hr hrr hfix
    rw [← hmap]
    exact hsat r hr hrr hfix
  rcases linWeyl_or_orth_of_F4_coords (U := V) hp2 b hWA hfam hirr
      (ggCZWF4_permMap_mem hp2 hd hb) (ggCZWF4_sgnMap_mem hp2 hd hb) h1152 htv
      (ggCZWF4_exists_not_monomial hp2 hd hb) hsatW
      (fun _ hr hrr hfix => ggCZWF4_refl_fix_mem_closure hp2 hd hb hr hrr hfix) with hlin | horth
  · exact ggRC_weylReflGroup_of_linWeyl (p := p) ιV (ggAInf p B Bs x L D J) hlin
  · obtain ⟨hp3, Q, hQ, hplus, hAorth⟩ := horth
    exact OrthF3.ggWeylReflectionGroup_of_orth_plus Q hQ hp3 hfr hplus ιV
      (ggAInf p B Bs x L D J) fun g => by
        rw [← Subgroup.mem_map]
        exact hAorth g

private theorem family_of_F4_coords [Fact p.Prime] [Finite V] [Module.Finite (ZMod p) V]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hUse : ZS.UseInput) (hp2 : p ≠ 2)
    (ιV : Additive ↥Bs ≃+ V)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    {e' : Fin 4 → V} {φ : Fin 4 → Module.Dual (ZMod p) V} (hd : GGCZDual e' φ)
    (hmap : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) = ggCZWF4 p e' φ)
    (b : Module.Basis (Fin 4) (ZMod p) V) (hb : ∀ i, b i = e' i)
    (hfr : Module.finrank (ZMod p) V = 4) :
    ZS.Family p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) ∧
      ZS.AbsIrred p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) := by
  have hAKle : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) ≤
      (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV) :=
    Subgroup.map_mono (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1)
  have hpermK : ∀ σ, ZS.permMap p b σ ∈
      (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) := by
    intro σ
    rw [hmap]
    exact ggCZWF4_permMap_mem hp2 hd hb σ
  have hsgnK : ∀ i, ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈
      (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) := by
    intro i
    rw [hmap]
    exact ggCZWF4_sgnMap_mem hp2 hd hb i
  have hpermA : ∀ σ, ZS.permMap p b σ ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV) := fun σ => hAKle (hpermK σ)
  have hsgnA : ∀ i, ZS.diagMap p b (fun j => if j = i then -1 else 1) ∈
      (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV) := fun i => hAKle (hsgnK i)
  have hirr : ZS.AbsIrred p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) :=
    ZS.absIrred_of_signed_le hp2 (by norm_num) b hpermA hsgnA
  have hgen : ZS.ReflGen p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) :=
    hR.reflGen_map_ggAInf hp2 hP ιV
  have hfam : ZS.Family p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) :=
    hUse p V _ hp2 (by rw [hfr]; norm_num) hgen hirr
  exact ⟨hfam, hirr⟩

private theorem dvd_card_map_F4 [Fact p.Prime]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (ιV : Additive ↥Bs ≃+ V) :
    1152 ∣ Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) := by
  have hcardK : Nat.card (ggAutomizerJoin L Bs 𝒦) = 1152 :=
    (hR.card_eq_of_typeF4 hTBF hWI e hP hM).1
  have hdvd : 1152 ∣ Nat.card (ggAInf p B Bs x L D J) := by
    rw [← hcardK]
    exact Subgroup.card_dvd_of_le (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1)
  rw [card_map_ggLin (p := p) ιV (ggAInf p B Bs x L D J)]
  exact hdvd

private theorem ggSecFiveWeylInfAt_F4_aux
    (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hUse : ZS.UseInput) (hSat : GGSecFiveF4ReflSatInput)
    [Fact p.Prime] (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M) :
    GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  obtain ⟨-, hBs, hx, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨t, ht, htr, htx⟩ := exists_endpointRefl_of_F4 hR hTBF hWI
    (GGSecFiveRestHyp.weylReflectionGroup_L hX hTCJ hRig hR.1 hR.2.1) hP hM hx
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) V = 4 := finrank_eq_four_of_F4 hR hTBF hWI hP hM ιV
  obtain ⟨e', φ, hd, hmap, hform⟩ := exists_coords_sgn_three_of_F4 hR hP hM ιV ht htr
  obtain ⟨b, hb, -⟩ := GGCZDual.exists_basis hd hfr
  have hline := ofMul_eq_smul_of_sgn_three hp2 ιV hform hx htx
  have hxb : ιV (Additive.ofMul ⟨x, hx⟩) =
      (φ 3 (ιV (Additive.ofMul ⟨x, hx⟩))) • b 3 := by
    rw [hb 3]
    exact hline
  obtain ⟨hfam, hirr⟩ := family_of_F4_coords hR hUse hp2 ιV hP hd hmap b hb hfr
  have h1152 : 1152 ∣ Nat.card ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) :=
    dvd_card_map_F4 hR hTBF hWI hP hM ιV
  have htv : ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV),
      Module.finrank (ZMod p) (LinearMap.range ((τ : V →ₗ[ZMod p] V) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v := hR.noTransvection_map_ggAInf ιV
  have hsat := sat_map_of_F4 hp2 hSat hR hP hM ιV hx b hxb
  exact weyl_of_F4_coords hp2 ιV hR hfr hd hmap b hb hfam hirr h1152 htv hsat

private noncomputable def f4Eta (p : ℕ) {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 4) (ZMod p) V) : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)) :=
  (AddEquiv.toMultiplicativeRight (ιV.trans b.equivFun.toAddEquiv)).trans
    (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod p)

private noncomputable def coordIota (p : ℕ) :
    Additive (Fin 4 → Multiplicative (ZMod p)) ≃+ (Fin 4 → ZMod p) :=
  (AddEquiv.piAdditive fun _ : Fin 4 => Multiplicative (ZMod p)).trans
    (AddEquiv.piCongrRight fun _ : Fin 4 => AddEquiv.additiveMultiplicative (ZMod p))

private theorem coordIota_apply (p : ℕ)
    (v : Additive (Fin 4 → Multiplicative (ZMod p))) :
    coordIota p v = fun k => Multiplicative.toAdd (Additive.toMul v k) := rfl

private theorem f4Eta_toAdd_apply {p : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 4) (ZMod p) V) (y : ↥Bs) (k : Fin 4) :
    Multiplicative.toAdd ((f4Eta p ιV b) y k) =
      (ιV.trans b.equivFun.toAddEquiv) (Additive.ofMul y) k := rfl

private theorem f4Eta_bCoordIota {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) :
    bCoordIota (f4Eta p ιV b) = ιV.trans b.equivFun.toAddEquiv := by
  refine AddEquiv.ext fun v => ?_
  change (fun k => Multiplicative.toAdd (f4Eta p ιV b (Additive.toMul v) k)) =
    (ιV.trans b.equivFun.toAddEquiv) v
  rfl

private theorem f4Eta_equivFun_basis {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin 4) (ZMod p) V) (i : Fin 4) :
    b.equivFun (b i) = Pi.basisFun (ZMod p) (Fin 4) i := by
  ext j
  rw [Module.Basis.equivFun_self, Pi.basisFun_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]

private theorem f4Eta_apply_eq_one_of_smul_basis {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {x : G} (hx : x ∈ Bs) (ιV : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 4) (ZMod p) V) {c : ZMod p}
    (hxb : ιV (Additive.ofMul ⟨x, hx⟩) = c • b 3) :
    ∀ k, k ≠ 3 → f4Eta p ιV b ⟨x, hx⟩ k = 1 := by
  have hcoords : bCoordIota (f4Eta p ιV b) (Additive.ofMul ⟨x, hx⟩) =
      c • Pi.basisFun (ZMod p) (Fin 4) 3 := by
    rw [f4Eta_bCoordIota, AddEquiv.trans_apply, hxb]
    change b.equivFun (c • b 3) = c • Pi.basisFun (ZMod p) (Fin 4) 3
    rw [map_smul, f4Eta_equivFun_basis]
  intro k hk
  have hk' := congrFun hcoords k
  simp only [bCoordIota_apply_ofMul, Pi.smul_apply, Pi.basisFun_apply,
    Pi.single_eq_of_ne hk, smul_zero] at hk'
  exact toAdd_eq_zero.mp hk'

private theorem f4Eta_coefficient_ne_zero {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {x : G} (hx : x ∈ Bs) (hx1 : x ≠ 1) (ιV : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 4) (ZMod p) V) {c : ZMod p}
    (hxb : ιV (Additive.ofMul ⟨x, hx⟩) = c • b 3) : c ≠ 0 := by
  intro h0
  have hx0 : ιV (Additive.ofMul ⟨x, hx⟩) = 0 := by rw [hxb, h0, zero_smul]
  have hx1' : (⟨x, hx⟩ : ↥Bs) = 1 := by
    have h0' : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := by
      apply ιV.injective
      rw [hx0, map_zero]
    exact Additive.ofMul.injective (by simpa using h0')
  exact hx1 (by simpa using congrArg Subtype.val hx1')

private theorem ggLin_f4Eta_eq_conj {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) (a : MulAut ↥Bs) :
    ggLin (p := p) (bCoordIota (f4Eta p ιV b)) a =
      (b.equivFun.symm.trans (ggLin (p := p) ιV a)).trans b.equivFun := by
  rw [f4Eta_bCoordIota]
  refine LinearEquiv.ext fun v => ?_
  rw [ggLin_apply]
  change (ιV.trans b.equivFun.toAddEquiv) (Additive.ofMul
      (a (Additive.toMul ((ιV.trans b.equivFun.toAddEquiv).symm v)))) =
    b.equivFun ((ggLin (p := p) ιV a) (b.equivFun.symm v))
  rw [ggLin_apply]
  rfl

private theorem ggLin_f4Eta_congr {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) (a : MulAut ↥Bs) :
    ggLin (p := p) (bCoordIota (f4Eta p ιV b)) a =
      ggLin (p := p) (coordIota p) (MulAut.congr (f4Eta p ιV b) a) := by
  let eta := f4Eta p ιV b
  have hκ : (MulEquiv.toAdditive eta.symm).trans (bCoordIota eta) = coordIota p := by
    refine AddEquiv.ext fun v => ?_
    change bCoordIota eta (Additive.ofMul (eta.symm (Additive.toMul v))) = coordIota p v
    rw [show eta = f4Eta p ιV b from rfl, f4Eta_bCoordIota]
    have h := MulEquiv.apply_symm_apply eta (Additive.toMul v)
    have h2 : (fun k => Multiplicative.toAdd (eta (eta.symm (Additive.toMul v)) k)) = v := by
      rw [h]
      rfl
    have hcoord : (ιV.trans b.equivFun.toAddEquiv)
        (Additive.ofMul (eta.symm (Additive.toMul v))) =
        fun k => Multiplicative.toAdd ((f4Eta p ιV b) (eta.symm (Additive.toMul v)) k) := by
      funext k
      exact (f4Eta_toAdd_apply ιV b _ k).symm
    rw [hcoord, coordIota_apply]
    exact h2
  have h := ggLin_mulEquiv_congr (p := p) (e := eta) (ι := bCoordIota eta) a
  rw [hκ] at h
  exact h.symm

private theorem f4Eta_ggLin_refl_permAut {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) (σ : Equiv.Perm (Fin 4)) :
    ggLin (p := p) (coordIota p) (SpCoord.permAut σ) =
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) σ := by
  let eta := f4Eta p ιV b
  have h1 := ggLin_bCoordIota_permAut eta σ
  have h2 := ggLin_f4Eta_congr ιV b ((MulAut.congr eta).symm (SpCoord.permAut σ))
  rw [MulEquiv.apply_symm_apply (MulAut.congr eta) (SpCoord.permAut σ)] at h2
  exact h2.symm.trans h1

private theorem f4Eta_ggLin_refl_sgnAut {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) (i : Fin 4) :
    ggLin (p := p) (coordIota p) (SpCoord.sgnAut i) =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i then -1 else 1) := by
  let eta := f4Eta p ιV b
  have h1 := ggLin_bCoordIota_sgnAut eta i
  have h2 := ggLin_f4Eta_congr ιV b ((MulAut.congr eta).symm (SpCoord.sgnAut i))
  rw [MulEquiv.apply_symm_apply (MulAut.congr eta) (SpCoord.sgnAut i)] at h2
  exact h2.symm.trans h1

private theorem equivFun_conj_permMap {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin 4) (ZMod p) V) (σ : Equiv.Perm (Fin 4)) :
    (b.equivFun.symm.trans (ZS.permMap p b σ)).trans b.equivFun =
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) σ := by
  refine Module.Basis.ext' (Pi.basisFun (ZMod p) (Fin 4)) fun k => ?_
  change b.equivFun (ZS.permMap p b σ (b.equivFun.symm (Pi.basisFun (ZMod p) (Fin 4) k))) =
    ZS.permMap p (Pi.basisFun (ZMod p) (Fin 4)) σ (Pi.basisFun (ZMod p) (Fin 4) k)
  have hsymm : b.equivFun.symm (Pi.basisFun (ZMod p) (Fin 4) k) = b k := by
    rw [← f4Eta_equivFun_basis b k]
    exact b.equivFun.symm_apply_apply (b k)
  rw [hsymm, ZS.permMap_apply_basis, f4Eta_equivFun_basis, ZS.permMap_apply_basis]

private theorem equivFun_conj_diagMap {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin 4) (ZMod p) V) (d : Fin 4 → (ZMod p)ˣ) :
    (b.equivFun.symm.trans (ZS.diagMap p b d)).trans b.equivFun =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) d := by
  refine Module.Basis.ext' (Pi.basisFun (ZMod p) (Fin 4)) fun k => ?_
  change b.equivFun (ZS.diagMap p b d (b.equivFun.symm (Pi.basisFun (ZMod p) (Fin 4) k))) =
    ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) d (Pi.basisFun (ZMod p) (Fin 4) k)
  have hsymm : b.equivFun.symm (Pi.basisFun (ZMod p) (Fin 4) k) = b k := by
    rw [← f4Eta_equivFun_basis b k]
    exact b.equivFun.symm_apply_apply (b k)
  rw [hsymm, ZS.diagMap_apply_basis, ZS.diagMap_apply_basis, map_smul,
    f4Eta_equivFun_basis]

private def b3CoordGens (p : ℕ) : Set (MulAut (Fin 4 → Multiplicative (ZMod p))) :=
  {SpCoord.permAut (Equiv.swap 0 1), SpCoord.permAut (Equiv.swap 1 2), SpCoord.sgnAut 2}

private noncomputable def b3LinGens (p : ℕ) [Fact p.Prime] :
    Set ((Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p)) :=
  ggLin (p := p) (coordIota p) '' b3CoordGens p

private def b3BasisGens (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin 4) (ZMod p) V) : Set (V ≃ₗ[ZMod p] V) :=
  {ZS.permMap p b (Equiv.swap 0 1), ZS.permMap p b (Equiv.swap 1 2),
    ZS.diagMap p b (fun j => if j = 2 then -1 else 1)}

private theorem conj_b3_mem_lin {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V)
    {L : V ≃ₗ[ZMod p] V} (hL : L ∈ Subgroup.closure (b3BasisGens p b)) :
    (b.equivFun.symm.trans L).trans b.equivFun ∈ Subgroup.closure (b3LinGens p) := by
  induction hL using Subgroup.closure_induction with
  | mem x hx =>
      simp only [b3BasisGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [equivFun_conj_permMap]
        exact Subgroup.subset_closure ⟨SpCoord.permAut (Equiv.swap 0 1),
          by simp [b3CoordGens], f4Eta_ggLin_refl_permAut ιV b _⟩
      · rw [equivFun_conj_permMap]
        exact Subgroup.subset_closure ⟨SpCoord.permAut (Equiv.swap 1 2),
          by simp [b3CoordGens], f4Eta_ggLin_refl_permAut ιV b _⟩
      · rw [equivFun_conj_diagMap]
        exact Subgroup.subset_closure ⟨SpCoord.sgnAut 2, by simp [b3CoordGens],
          f4Eta_ggLin_refl_sgnAut ιV b 2⟩
  | one =>
      have h : (b.equivFun.symm.trans (1 : V ≃ₗ[ZMod p] V)).trans b.equivFun = 1 := by
        ext v k
        change b.equivFun (b.equivFun.symm v) k = v k
        rw [b.equivFun.apply_symm_apply]
      rw [h]
      exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
      have h : (b.equivFun.symm.trans (x * y)).trans b.equivFun =
          ((b.equivFun.symm.trans x).trans b.equivFun) *
            ((b.equivFun.symm.trans y).trans b.equivFun) := by
        ext v
        simp [LinearEquiv.trans_apply]
      rw [h]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
      have h : (b.equivFun.symm.trans x⁻¹).trans b.equivFun =
          ((b.equivFun.symm.trans x).trans b.equivFun)⁻¹ := by
        ext v
        simp [LinearEquiv.trans_apply]
      rw [h]
      exact Subgroup.inv_mem _ ihx

private theorem b3Closure_le_bCoordinateBlock (p : ℕ) :
    Subgroup.closure (b3CoordGens p) ≤ bCoordinateBlock 4 p 3 := by
  refine (Subgroup.closure_le (K := bCoordinateBlock 4 p 3)).mpr ?_
  intro x hx
  simp only [b3CoordGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inr ⟨0, 1, by decide, by decide, by decide, rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨1, 2, by decide, by decide, by decide, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨2, by decide, rfl⟩)

private theorem ggLin_map_automizer_le_b3 [Fact p.Prime] [Finite V]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2)
    (hW : GGWeylReflectionGroup p (ggAutomizer L Bs))
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V)
    {eD : Fin 4 → V} {ψ : Fin 4 → Module.Dual (ZMod p) V}
    (hmap : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) = ggCZWF4 p eD ψ)
    (hd : GGCZDual eD ψ) (hb : ∀ i, b i = eD i)
    (hx : x ∈ Bs) {c : ZMod p} (hc0 : c ≠ 0)
    (hxb : ιV (Additive.ofMul ⟨x, hx⟩) = c • b 3) :
    ∀ a ∈ ggAutomizer L Bs, ggLin (p := p) ιV a ∈
      Subgroup.closure (b3BasisGens p b) := by
  obtain ⟨ι', M', hM', f, hf⟩ := hW
  have hgen : ∀ i : ι', ggLin (p := p) ιV
      ((f (M'.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈
      Subgroup.closure (b3BasisGens p b) := by
    intro i
    set a : MulAut ↥Bs := ((f (M'.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) with ha
    have hmemK : a ∈ ggAutomizerJoin L Bs 𝒦 :=
      (le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) (f (M'.simple i)).2
    have hWmem : ggLin (p := p) ιV a ∈ ggCZWF4 p eD ψ := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hmemK
    have hrefl : GGLinRefl (ggLin (p := p) ιV a) :=
      (ggIsReflection_iff_ggLinRefl hp2 ιV a).mp (hf i)
    have hfixx : ggLin (p := p) ιV a (ιV (Additive.ofMul ⟨x, hx⟩)) =
        ιV (Additive.ofMul ⟨x, hx⟩) := by
      rw [ggLin_apply_ofMul]
      have hfix_a : a ⟨x, hx⟩ = ⟨x, hx⟩ :=
        ggRM_AL_fixes_x (ggSecFiveRouteCfg'_of_routeCfg hR) hx a (f (M'.simple i)).2
      rw [hfix_a]
    have hfix : ggLin (p := p) ιV a (b 3) = b 3 := by
      rw [hxb, map_smul] at hfixx
      exact smul_right_injective V hc0 hfixx
    exact ggCZWF4_refl_fix_mem_closure hp2 hd hb hWmem hrefl hfix
  intro a ha
  obtain ⟨w, hw⟩ := f.surjective ⟨a, ha⟩
  have hval : ((f w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) = a := congrArg Subtype.val hw
  have hwP : ggLin (p := p) ιV ((f w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈
      Subgroup.closure (b3BasisGens p b) := by
    refine (M'.toCoxeterSystem).simple_induction
      (p := fun u => ggLin (p := p) ιV
        ((f u : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈
        Subgroup.closure (b3BasisGens p b)) w ?_ ?_ ?_
    · exact hgen
    · simp
    · intro u v ihu ihv
      simpa [map_mul] using Subgroup.mul_mem _ ihu ihv
  rwa [hval] at hwP

private theorem f4Eta_congr_mem_bCoordinateBlock {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) {a : MulAut ↥Bs}
    (hL : ggLin (p := p) ιV a ∈ Subgroup.closure (b3BasisGens p b)) :
    MulAut.congr (f4Eta p ιV b) a ∈ bCoordinateBlock 4 p 3 := by
  let eta := f4Eta p ιV b
  have hconj : (b.equivFun.symm.trans (ggLin (p := p) ιV a)).trans b.equivFun ∈
      Subgroup.closure (b3LinGens p) := conj_b3_mem_lin ιV b hL
  have hΦ : ggLin (p := p) (coordIota p) (MulAut.congr eta a) =
      (b.equivFun.symm.trans (ggLin (p := p) ιV a)).trans b.equivFun := by
    rw [← ggLin_f4Eta_congr ιV b a, ggLin_f4Eta_eq_conj]
  have hmap_closure : (Subgroup.closure (b3CoordGens p)).map
      (ggLin (p := p) (coordIota p)) = Subgroup.closure (b3LinGens p) := by
    rw [MonoidHom.map_closure]
    rfl
  have hQmap : ggLin (p := p) (coordIota p) (MulAut.congr eta a) ∈
      (Subgroup.closure (b3CoordGens p)).map (ggLin (p := p) (coordIota p)) := by
    rw [hmap_closure, hΦ]
    exact hconj
  obtain ⟨Q, hQ, heq⟩ := Subgroup.mem_map.mp hQmap
  have hQQ : Q = MulAut.congr eta a := ggLin_injective _ heq
  exact b3Closure_le_bCoordinateBlock p (hQQ ▸ hQ)

private theorem f4Eta_preimage_sgnAut_lin {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) (i : Fin 4) :
    ggLin (p := p) ιV ((MulAut.congr (f4Eta p ιV b)).symm (SpCoord.sgnAut i)) =
      ZS.diagMap p b (fun j => if j = i then -1 else 1) := by
  let eta := f4Eta p ιV b
  let L : V ≃ₗ[ZMod p] V :=
    ggLin (p := p) ιV ((MulAut.congr eta).symm (SpCoord.sgnAut i))
  let D : V ≃ₗ[ZMod p] V := ZS.diagMap p b (fun j => if j = i then -1 else 1)
  let De : (Fin 4 → ZMod p) ≃ₗ[ZMod p] (Fin 4 → ZMod p) :=
    ZS.diagMap p (Pi.basisFun (ZMod p) (Fin 4)) (fun j => if j = i then -1 else 1)
  have h1 := ggLin_bCoordIota_sgnAut eta i
  have h2 := ggLin_f4Eta_eq_conj ιV b ((MulAut.congr eta).symm (SpCoord.sgnAut i))
  have h3 : (b.equivFun.symm.trans L).trans b.equivFun = De := by
    rw [← h2]
    exact h1
  have h4 : (b.equivFun.symm.trans D).trans b.equivFun = De :=
    equivFun_conj_diagMap (b := b) (d := fun j => if j = i then -1 else 1)
  change L = D
  calc L = b.equivFun.trans
        (((b.equivFun.symm.trans L).trans b.equivFun).trans b.equivFun.symm) := by
        ext v
        simp [LinearEquiv.trans_apply]
    _ = b.equivFun.trans (De.trans b.equivFun.symm) := by rw [h3]
    _ = D := by
        rw [← h4]
        ext v
        simp [LinearEquiv.trans_apply]

omit [Finite G] in
private theorem f4Eta_negOff_mem_join [Fact p.Prime]
    (ιV : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin 4) (ZMod p) V) (hp2 : p ≠ 2)
    {eD : Fin 4 → V} {ψ : Fin 4 → Module.Dual (ZMod p) V}
    (hmap : (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := p) ιV) = ggCZWF4 p eD ψ)
    (hd : GGCZDual eD ψ) (hb : ∀ i, b i = eD i) :
    (MulAut.congr (f4Eta p ιV b)).symm (negOff (p := p) (3 : Fin 4)) ∈
      ggAutomizerJoin L Bs 𝒦 := by
  let eta := f4Eta p ιV b
  let g : MulAut ↥Bs := (MulAut.congr eta).symm (negOff (p := p) (3 : Fin 4))
  have hneg : negOff (p := p) (3 : Fin 4) =
      SpCoord.sgnAut 0 * SpCoord.sgnAut 1 * SpCoord.sgnAut 2 := by
    refine MulEquiv.ext fun f => ?_
    funext i
    fin_cases i <;> simp [SpCoord.sgnAut_apply, negOff_apply]
  have hg : g = (MulAut.congr eta).symm (SpCoord.sgnAut 0) *
      (MulAut.congr eta).symm (SpCoord.sgnAut 1) *
      (MulAut.congr eta).symm (SpCoord.sgnAut 2) := by
    change (MulAut.congr eta).symm (negOff (p := p) (3 : Fin 4)) = _
    rw [hneg, map_mul, map_mul]
  have hW : ggLin (p := p) ιV g ∈ ggCZWF4 p eD ψ := by
    rw [hg, map_mul, map_mul, f4Eta_preimage_sgnAut_lin ιV b 0,
      f4Eta_preimage_sgnAut_lin ιV b 1, f4Eta_preimage_sgnAut_lin ιV b 2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (ggCZWF4_sgnMap_mem hp2 hd hb 0) (ggCZWF4_sgnMap_mem hp2 hd hb 1))
      (ggCZWF4_sgnMap_mem hp2 hd hb 2)
  rw [← hmap] at hW
  obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp hW
  rw [ggLin_injective ιV heq] at hh
  exact hh

private theorem exists_eta_bCoordinateBlock_of_F4_aux
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hWL : GGWeylReflectionGroup p (ggAutomizer L Bs)) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (hx : x ∈ Bs) :
    ∃ eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)),
      (∀ k, k ≠ 3 → eta ⟨x, hx⟩ k = 1) ∧
      (∀ a ∈ ggAutomizer L Bs, MulAut.congr eta a ∈ bCoordinateBlock 4 p 3) ∧
      (MulAut.congr eta).symm (negOff (p := p) (3 : Fin 4)) ∈ ggAutomizerJoin L Bs 𝒦 := by
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨t, ht, htr, htx⟩ := exists_endpointRefl_of_F4 hR hTBF hWI hWL hP hM hx
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) V = 4 := finrank_eq_four_of_F4 hR hTBF hWI hP hM ιV
  obtain ⟨eD, ψ, hd, hmap, hform⟩ := exists_coords_sgn_three_of_F4 hR hP hM ιV ht htr
  obtain ⟨b, hb, -⟩ := GGCZDual.exists_basis hd hfr
  have hline := ofMul_eq_smul_of_sgn_three hp2 ιV hform hx htx
  have hxb : ιV (Additive.ofMul ⟨x, hx⟩) =
      (ψ 3 (ιV (Additive.ofMul ⟨x, hx⟩))) • b 3 := by
    rw [hb 3]
    exact hline
  have hc0 : ψ 3 (ιV (Additive.ofMul ⟨x, hx⟩)) ≠ 0 :=
    f4Eta_coefficient_ne_zero hx hx1 ιV b hxb
  exact ⟨f4Eta p ιV b, f4Eta_apply_eq_one_of_smul_basis hx ιV b hxb,
    fun a ha => f4Eta_congr_mem_bCoordinateBlock ιV b
      (ggLin_map_automizer_le_b3 hR hp2 hWL ιV b hmap hd hb hx hc0 hxb a ha),
    f4Eta_negOff_mem_join ιV b hp2 hmap hd hb⟩

theorem GGSecFiveRouteCfg.exists_eta_bCoordinateBlock_of_F4
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hWL : GGWeylReflectionGroup p (ggAutomizer L Bs)) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (hx : x ∈ Bs) :
    ∃ eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p)),
      (∀ k, k ≠ 3 → eta ⟨x, hx⟩ k = 1) ∧
      ∀ a ∈ ggAutomizer L Bs, MulAut.congr eta a ∈ bCoordinateBlock 4 p 3 := by
  obtain ⟨eta, hxi0, hLB, -⟩ := exists_eta_bCoordinateBlock_of_F4_aux hR hTBF hWI hWL hP hM hx
  exact ⟨eta, hxi0, hLB⟩

end Config

theorem ggSecFiveWeylInfAt_F4_of_inputs
    (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hUse : ZS.UseInput) (hSat : GGSecFiveF4ReflSatInput) :
    GGSecFiveWeylInfAt fun M => GGIsWeylMatrixF4 M := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hP hM
  obtain ⟨hp, -, -, -, -⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  exact ggSecFiveWeylInfAt_F4_aux hTBF hWI hX hTCJ hRig hUse hSat hR e hP hM

theorem ggSecFiveF4ReflSatInput_of_nativeImage
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (ha₀ : GGLNoncyclicInput) : GGSecFiveF4ReflSatInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hP hM hx φ hφ hφrefl hfix
  obtain ⟨hp, hBs, -, -, h4⟩ := hR.1.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hp2, -⟩ :=
    (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hx1 : x ≠ 1 := hR.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hφI : φ ∈ ggInduced ⊤ Bs := ggRM_ainf_le_induced hφ
  have hWL := GGSecFiveRestHyp.weylReflectionGroup_L hX hTCJ hRig hR.1 hR.2.1
  obtain ⟨eta, hxi0, hLB, hneg⟩ := exists_eta_bCoordinateBlock_of_F4_aux hR hTBF hWI hWL hP hM hx
  have hT := ggF4_weylOfType_A3_or_B3 hp2 hBs h4 hR.1.2.2.2.1
    (fun _ hψ => ggAutomizerJoin_le_ggInduced_top L 𝒦 hψ) hP hM
    (hR.eq_one_of_forall_join_fix hTBF hWI) (fun _ ha => Subgroup.mem_sup_left ha) hWL hx hx1
    (GGSecFiveRestHyp.fixLineComp_L hTBF hR.1 hR.2.1).fix_iff
  obtain ⟨c, a, ha, hca⟩ := hR.nativeImage_of_le_bCoordinateBlock_four ha₀
    (by rintro _ ⟨a, ha, rfl⟩; exact hLB a ha) hT hx hφI hfix
  have haB : MulAut.congr eta a ∈ bCoordinateBlock 4 p 3 := hLB a ha
  exact hR.mem_of_native_of_mem_bCoordinateBlock (n := 4) (by norm_num) hx hxi0
    (H := ggAutomizerJoin L Bs 𝒦) (fun h hh => ggAutomizerJoin_le_ggInduced_top L 𝒦 hh)
    hneg hφI hφrefl hfix (Subgroup.mem_sup_left ha) haB hca

end CFSG.StandardType

end
