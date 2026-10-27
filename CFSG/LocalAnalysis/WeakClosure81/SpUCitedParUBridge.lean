module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUBasic
public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURoot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.ComponentInitial CFSG.Open

variable {K : Type} [Field K] {r ε : ℕ}

section Helpers

variable {f : ℕ} [Finite K] [CharP K 2]

private theorem spUCited_bar_apply (h : UnitaryFieldData 2 f K) (c : K) :
    h.bar c = unitaryInvolution K 2 f c := by
  rw [UnitaryFieldData.bar_apply h, unitaryInvolution_apply]

private theorem spUCited_mem_traceZero (h : UnitaryFieldData 2 f K) {c : K} :
    c ∈ h.traceZero ↔ c + unitaryInvolution K 2 f c = 0 := by
  rw [UnitaryFieldData.mem_traceZero h, UnitaryFieldData.trace, spUCited_bar_apply h]

private theorem spUCited_stdHermForm_eq_herm (h : UnitaryFieldData 2 f K) (m : ℕ)
    (u v : Fin m → K) :
    stdHermForm h m u v = herm (unitaryInvolution K 2 f) u v := by
  rw [stdHermForm_apply, herm_def]
  exact Finset.sum_congr rfl fun i _ => by rw [spUCited_bar_apply h (u i)]

private theorem spUCited_herm_transport (h : UnitaryFieldData 2 f K)
    {Rm : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h Rm)
    (x y : HypIndex r ε → K) :
    herm (unitaryInvolution K 2 f) (Rm *ᵥ x) (Rm *ᵥ y) = hypForm h r ε x y := by
  rw [← spUCited_stdHermForm_eq_herm h (2 * r + ε)]
  exact stdHermForm_transport hR x y

private theorem spUCited_transport_transvection (h : UnitaryFieldData 2 f K)
    {Rm : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h Rm)
    {x : HypIndex r ε → K} {c : K} {g : ↥(hypSU h r ε)}
    (hg : mulVecLin (((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) =
      hermTransvection (hypForm h r ε) x c) :
    Rm * (((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) * transportInv h Rm =
      tvMat (unitaryInvolution K 2 f) (Rm *ᵥ x) c := by
  set e : Fin (2 * r + ε) → K := Rm *ᵥ x with he
  rw [Matrix.ext_iff_mulVec]
  intro y
  have hgz : (((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ (transportInv h Rm *ᵥ y) =
      (transportInv h Rm *ᵥ y) +
        (c * hypForm h r ε x (transportInv h Rm *ᵥ y)) • x := by
    have hcongr := LinearMap.congr_fun hg (transportInv h Rm *ᵥ y)
    rwa [Matrix.mulVecLin_apply, hermTransvection_apply] at hcongr
  have hRy : Rm *ᵥ (transportInv h Rm *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, mul_transportInv hR, Matrix.one_mulVec]
  have hxe : transportInv h Rm *ᵥ e = x := by
    rw [he, Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]
  have hform : hypForm h r ε x (transportInv h Rm *ᵥ y) =
      herm (unitaryInvolution K 2 f) e y := by
    rw [← hxe, hypForm_transportInv hR e y]
    exact spUCited_stdHermForm_eq_herm h (2 * r + ε) e y
  calc (Rm * (((g : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) * transportInv h Rm) *ᵥ y
      = Rm *ᵥ ((((g : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ (transportInv h Rm *ᵥ y)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = Rm *ᵥ ((transportInv h Rm *ᵥ y) +
            (c * hypForm h r ε x (transportInv h Rm *ᵥ y)) • x) := by rw [hgz]
      _ = Rm *ᵥ (transportInv h Rm *ᵥ y) +
            (c * hypForm h r ε x (transportInv h Rm *ᵥ y)) • (Rm *ᵥ x) := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = y + (c * herm (unitaryInvolution K 2 f) e y) • e := by
          rw [hRy, hform, ← he]
      _ = tvMat (unitaryInvolution K 2 f) e c *ᵥ y := by rw [tvMat_mulVec]

private theorem spUCited_transportInv_transvection (h : UnitaryFieldData 2 f K)
    {Rm : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h Rm)
    (x : HypIndex r ε → K) (c : K) :
    mulVecLin (transportInv h Rm * tvMat (unitaryInvolution K 2 f) (Rm *ᵥ x) c * Rm) =
      hermTransvection (hypForm h r ε) x c := by
  set e : Fin (2 * r + ε) → K := Rm *ᵥ x with he
  apply LinearMap.ext
  intro y
  rw [Matrix.mulVecLin_apply, hermTransvection_apply]
  have hRy : transportInv h Rm *ᵥ (Rm *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]
  have hxe : transportInv h Rm *ᵥ e = x := by
    rw [he, Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]
  have hform : herm (unitaryInvolution K 2 f) e (Rm *ᵥ y) = hypForm h r ε x y := by
    rw [he]
    exact spUCited_herm_transport h hR x y
  calc (transportInv h Rm * tvMat (unitaryInvolution K 2 f) e c * Rm) *ᵥ y
      = transportInv h Rm *ᵥ (tvMat (unitaryInvolution K 2 f) e c *ᵥ (Rm *ᵥ y)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = transportInv h Rm *ᵥ ((Rm *ᵥ y) +
            (c * herm (unitaryInvolution K 2 f) e (Rm *ᵥ y)) • e) := by rw [tvMat_mulVec]
      _ = transportInv h Rm *ᵥ (Rm *ᵥ y) +
            (c * herm (unitaryInvolution K 2 f) e (Rm *ᵥ y)) •
              (transportInv h Rm *ᵥ e) := by rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = y + (c * hypForm h r ε x y) • x := by rw [hRy, hxe, hform]
      _ = hermTransvection (hypForm h r ε) x c y := by rw [hermTransvection_apply]

private theorem spUCited_suTv_coe {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {e : Fin m → F} {s : F}
    (he : herm (unitaryInvolution F 2 n) e e = 0) (hs : s + unitaryInvolution F 2 n s = 0) :
    (((suTv (isUnitaryInvolution_unitaryInvolution hF) e s :
        ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = tvMat (unitaryInvolution F 2 n) e s := by
  unfold suTv
  rw [dif_pos ⟨he, hs⟩]
  rfl

private theorem spUCited_kFactsSuProjTv_eq {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (m : ℕ) (e : Fin m → F) (s : F) :
    kFactsSuProjTv hF m e s =
      QuotientGroup.mk (MulEquiv.subgroupCongr (SUid_eq_statedSU hF m)
        (suTv (isUnitaryInvolution_unitaryInvolution hF) e s)) := by
  rfl

private theorem spUCited_exists_mulVecLin_hermTransvection (h : UnitaryFieldData 2 f K)
    {Rm : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h Rm)
    (hF : Nat.card K = (2 ^ f) ^ 2) {x : HypIndex r ε → K}
    (he : herm (unitaryInvolution K 2 f) (Rm *ᵥ x) (Rm *ᵥ x) = 0) {c : K}
    (hc : c + unitaryInvolution K 2 f c = 0) :
    ∃ g : ↥(hypSU h r ε),
      mulVecLin (((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) =
        hermTransvection (hypForm h r ε) x c := by
  have hGcoe : (((MulEquiv.subgroupCongr (SUid_eq_statedSU hF (2 * r + ε))
        (suTv (isUnitaryInvolution_unitaryInvolution hF) (Rm *ᵥ x) c) :
          unitarySU 2 f K (2 * r + ε)) : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
      tvMat (unitaryInvolution K 2 f) (Rm *ᵥ x) c := by
    rw [MulEquiv.subgroupCongr_apply, spUCited_suTv_coe hF he hc]
  refine ⟨(hypTransport h hR).symm (MulEquiv.subgroupCongr (SUid_eq_statedSU hF (2 * r + ε))
    (suTv (isUnitaryInvolution_unitaryInvolution hF) (Rm *ᵥ x) c)), ?_⟩
  rw [coe_hypTransport_symm, hGcoe]
  exact spUCited_transportInv_transvection h hR x c

private theorem spUCited_tau_proj_eq_suProjTv (h : UnitaryFieldData 2 f K)
    {Rm : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h Rm)
    (hn : 1 ≤ 2 * r + ε) (hF : Nat.card K = (2 ^ f) ^ 2) {x : HypIndex r ε → K}
    (hx : hypForm h r ε x x = 0) {g : ↥(hypSU h r ε)} {c : K} (hc : c ∈ h.traceZero)
    (hg : mulVecLin (((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) =
      hermTransvection (hypForm h r ε) x c) :
    hypPSUEquivStatedProj h hR hn (hypProj h r ε g) =
      kFactsSuProjTv hF (2 * r + ε) (Rm *ᵥ x) c := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hmembar : c + unitaryInvolution K 2 f c = 0 := (spUCited_mem_traceZero h).mp hc
  have he : herm (unitaryInvolution K 2 f) (Rm *ᵥ x) (Rm *ᵥ x) = 0 := by
    rw [spUCited_herm_transport h hR x x, hx]
  have hmat := spUCited_transport_transvection h hR (x := x) (c := c) (g := g) hg
  have hsub : (hypTransport h hR g : unitarySU 2 f K (2 * r + ε)) =
      MulEquiv.subgroupCongr (SUid_eq_statedSU hF (2 * r + ε))
        (suTv hσ (Rm *ᵥ x) c) := by
    apply Subtype.ext
    rw [MulEquiv.subgroupCongr_apply]
    apply Units.ext
    rw [coe_hypTransport, spUCited_suTv_coe hF he hmembar]
    exact hmat
  calc hypPSUEquivStatedProj h hR hn (hypProj h r ε g)
      = QuotientGroup.mk (hypTransport h hR g : StatedSU (2 * r + ε) (2 ^ f) K) :=
        hypPSUEquivStatedProj_hypProj hR hn g
    _ = QuotientGroup.mk (MulEquiv.subgroupCongr (SUid_eq_statedSU hF (2 * r + ε))
          (suTv hσ (Rm *ᵥ x) c)) := by rw [hsub]
    _ = kFactsSuProjTv hF (2 * r + ε) (Rm *ᵥ x) c :=
        (spUCited_kFactsSuProjTv_eq hF (2 * r + ε) (Rm *ᵥ x) c).symm

end Helpers

theorem uCited_map_root_transport {f : ℕ} [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
    {Rm : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h Rm)
    (hn : 1 ≤ 2 * r + ε) (hF : Nat.card K = (2 ^ f) ^ 2) {x : HypIndex r ε → K}
    (hx : hypForm h r ε x x = 0) :
    ((uCitedRoot h r ε x).map (hypProj h r ε)).map
        (hypPSUEquivStatedProj h hR hn).toMonoidHom =
      spUFixRootU hF (2 * r + ε) (Rm *ᵥ x) := by
  have he : herm (unitaryInvolution K 2 f) (Rm *ᵥ x) (Rm *ᵥ x) = 0 := by
    rw [spUCited_herm_transport h hR x x, hx]
  apply le_antisymm
  · rw [uCitedRoot, MonoidHom.map_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨z, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨c, hc, hgc⟩ := hg
    exact (mem_spUFixRootU hF he).mpr
      ⟨c, (spUCited_mem_traceZero h).mp hc,
        spUCited_tau_proj_eq_suProjTv h hR hn hF hx hc hgc⟩
  · rw [spUFixRootU, Subgroup.closure_le]
    rintro y ⟨c, hc, rfl⟩
    have hc' : c ∈ h.traceZero := (spUCited_mem_traceZero h).mpr hc
    obtain ⟨g, hg⟩ := spUCited_exists_mulVecLin_hermTransvection h hR hF he hc
    have hgX : g ∈ uCitedRoot h r ε x := (mem_uCitedRoot h hx).mpr ⟨c, hc', hg⟩
    exact Subgroup.mem_map.mpr ⟨hypProj h r ε g, Subgroup.mem_map.mpr ⟨g, hgX, rfl⟩,
      spUCited_tau_proj_eq_suProjTv h hR hn hF hx hc' hg⟩

end CFSG.LocalAnalysis.WeakClosure81

end
