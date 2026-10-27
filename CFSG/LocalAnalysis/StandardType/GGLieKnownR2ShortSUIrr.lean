module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUNorm
public import CFSG.Timmesfeld.LieEmbed.UnitaryWittN

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType CFSG.StandardType.GGOppRadSpU CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.QuasithinUnique.B113Lie.Sp CFSG.Timmesfeld.LieEmbed
  Matrix
open scoped Matrix

private lemma suH_beta_uForm {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} (x y : Fin n → F) :
    (suH hc n).β x y = uForm (unitaryInvolution F 2 f) x y := by
  rw [suH, suForm_β, uForm_eq]

private lemma suH_symm {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} (x y : Fin n → F) :
    (suH hc n).β x y = unitaryInvolution F 2 f ((suH hc n).β y x) := by
  rw [suH, suForm_symm]

private lemma suFrame_vw' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v w' = 1 := hfr.1

private lemma suFrame_wv' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w v' = 1 := hfr.2.1

private lemma suFrame_w'v {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w' v = 1 := by
  rw [suH_symm, suFrame_vw' hfr, map_one]

private lemma suFrame_v'w {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v' w = 1 := by
  rw [suH_symm, suFrame_wv' hfr, map_one]

private lemma suFrame_vw {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v w = 0 :=
  hfr.2.2.2.1

private lemma suFrame_vv' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v v' = 0 :=
  hfr.2.2.2.2.1

private lemma suFrame_ww' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w w' = 0 :=
  hfr.2.2.2.2.2.1

private lemma suFrame_v'w' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v' w' = 0 :=
  hfr.2.2.2.2.2.2

private lemma suFrame_wv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w v = 0 := by
  rw [suH_symm, suFrame_vw hfr, map_zero]

private lemma suFrame_v'v {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v' v = 0 := by
  rw [suH_symm, suFrame_vv' hfr, map_zero]

private lemma suFrame_w'w {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w' w = 0 := by
  rw [suH_symm, suFrame_ww' hfr, map_zero]

private lemma suFrame_w'v' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w' v' = 0 := by
  rw [suH_symm, suFrame_v'w' hfr, map_zero]

private lemma suFrame_vv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v v = 0 := hfr.2.2.1.1

private lemma suFrame_ww {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w w = 0 := hfr.2.2.1.2.1

private lemma suFrame_v'v' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β v' v' = 0 := hfr.2.2.1.2.2.1

private lemma suFrame_w'w' {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : (suH hc n).β w' w' = 0 := hfr.2.2.1.2.2.2

private lemma mem_frameW_iff {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (z : Fin n → F) :
    z ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) ↔
      (suH hc n).β v z = 0 ∧ (suH hc n).β w z = 0 ∧
        (suH hc n).β v' z = 0 ∧ (suH hc n).β w' z = 0 := by
  rw [ReflForm.mem_perp]
  constructor
  · intro h
    exact ⟨h v (Submodule.subset_span (by simp)), h w (Submodule.subset_span (by simp)),
      h v' (Submodule.subset_span (by simp)), h w' (Submodule.subset_span (by simp))⟩
  · rintro ⟨h1, h2, h3, h4⟩ x hx
    refine Submodule.span_induction (p := fun x _ => (suH hc n).β x z = 0)
      (fun y hy => ?_) ?_ ?_ ?_ hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · exact (suH hc n).β_zero_left z
    · intro a b ha hb hpa hpb; rw [(suH hc n).add_left, hpa, hpb, add_zero]
    · intro c a ha hpa; rw [(suH hc n).smul_left, hpa, mul_zero]

private lemma mem_planePerp_iff {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w : Fin n → F} (z : Fin n → F) :
    z ∈ (suH hc n).perp (Submodule.span F {v, w}) ↔
      (suH hc n).β v z = 0 ∧ (suH hc n).β w z = 0 := by
  rw [ReflForm.mem_perp]
  constructor
  · intro h
    exact ⟨h v (Submodule.subset_span (by simp)), h w (Submodule.subset_span (by simp))⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [(suH hc n).add_left, (suH hc n).smul_left, (suH hc n).smul_left, h1, h2, mul_zero,
      mul_zero, add_zero]

private lemma span_plane_le_span_frame {F : Type} [Field F] {n : ℕ} {v w v' w' : Fin n → F} :
    Submodule.span F {v, w} ≤ Submodule.span F {v, w, v', w'} := by
  refine Submodule.span_mono ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  rcases hz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

private lemma frame_proj_mem_W {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (y : Fin n → F) :
    y - (suH hc n).β w' y • v - (suH hc n).β v' y • w - (suH hc n).β w y • v' -
        (suH hc n).β v y • w' ∈
      (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
  rw [mem_frameW_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [(suH hc n).β_sub_right, (suH hc n).smul_right, suFrame_vv hfr, suFrame_vw hfr,
      suFrame_vv' hfr, suFrame_vw' hfr, suFrame_wv hfr, suFrame_ww hfr, suFrame_wv' hfr,
      suFrame_ww' hfr, suFrame_v'v hfr, suFrame_v'w hfr, suFrame_v'v' hfr, suFrame_v'w' hfr,
      suFrame_w'v hfr, suFrame_w'w hfr, suFrame_w'v' hfr, suFrame_w'w' hfr, mul_zero, mul_one,
      sub_zero] <;>
    ring

private lemma perp_plane_eq_sup {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    (suH hc n).perp (Submodule.span F {v, w}) =
      Submodule.span F {v, w} ⊔ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [mem_planePerp_iff] at hy
    obtain ⟨hvy, hwy⟩ := hy
    have hz := frame_proj_mem_W hfr y
    rw [hvy, hwy, zero_smul, zero_smul, sub_zero, sub_zero] at hz
    have hdecomp : y = ((suH hc n).β w' y • v + (suH hc n).β v' y • w) +
        (y - (suH hc n).β w' y • v - (suH hc n).β v' y • w) := by abel
    rw [hdecomp]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    · exact Submodule.mem_sup_right hz
  · refine sup_le (suFrame_isTotallyIsotropic hfr) ?_
    exact ReflForm.perp_antitone (suH hc n) span_plane_le_span_frame

private noncomputable def suFramePhi {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (v w v' w' : Fin n → F) :
    (Fin n → F) →ₗ[F] (Fin 4 → F) :=
  LinearMap.pi ![suDual (σ := unitaryInvolution F 2 f)
      (hσ := unitaryInvolution_involutive hc) w',
    suDual (σ := unitaryInvolution F 2 f) (hσ := unitaryInvolution_involutive hc) v',
    suDual (σ := unitaryInvolution F 2 f) (hσ := unitaryInvolution_involutive hc) w,
    suDual (σ := unitaryInvolution F 2 f) (hσ := unitaryInvolution_involutive hc) v]

private lemma suFramePhi_apply {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (v w v' w' z : Fin n → F) :
    suFramePhi hc v w v' w' z =
      ![(suH hc n).β w' z, (suH hc n).β v' z, (suH hc n).β w z, (suH hc n).β v z] := by
  funext i
  fin_cases i <;> rfl

private lemma suFramePhi_ker {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (v w v' w' : Fin n → F) :
    LinearMap.ker (suFramePhi hc v w v' w') =
      (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
  ext z
  rw [LinearMap.mem_ker, mem_frameW_iff]
  constructor
  · intro hz
    rw [suFramePhi_apply] at hz
    exact ⟨congrFun hz 3, congrFun hz 2, congrFun hz 1, congrFun hz 0⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rw [suFramePhi_apply]
    funext i
    fin_cases i
    · exact h4
    · exact h3
    · exact h2
    · exact h1

private lemma suFramePhi_surjective {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : Function.Surjective (suFramePhi hc v w v' w') := by
  intro y
  set z : Fin n → F := y 0 • v + y 1 • w + y 2 • v' + y 3 • w' with hz
  refine ⟨z, ?_⟩
  funext i
  fin_cases i
  · change (suH hc n).β w' z = y 0
    rw [hz]
    simp only [(suH hc n).add_right, (suH hc n).smul_right, suFrame_w'v hfr, suFrame_w'w hfr,
      suFrame_w'v' hfr, suFrame_w'w' hfr, mul_zero, mul_one, zero_add, add_zero]
  · change (suH hc n).β v' z = y 1
    rw [hz]
    simp only [(suH hc n).add_right, (suH hc n).smul_right, suFrame_v'v hfr, suFrame_v'w hfr,
      suFrame_v'v' hfr, suFrame_v'w' hfr, mul_zero, mul_one, zero_add, add_zero]
  · change (suH hc n).β w z = y 2
    rw [hz]
    simp only [(suH hc n).add_right, (suH hc n).smul_right, suFrame_wv hfr, suFrame_ww hfr,
      suFrame_wv' hfr, suFrame_ww' hfr, mul_zero, mul_one, zero_add, add_zero]
  · change (suH hc n).β v z = y 3
    rw [hz]
    simp only [(suH hc n).add_right, (suH hc n).smul_right, suFrame_vv hfr, suFrame_vw hfr,
      suFrame_vv' hfr, suFrame_vw' hfr, mul_zero, mul_one, zero_add, add_zero]

private lemma su_finrank_frameW {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    Module.finrank F ((suH hc n).perp (Submodule.span F {v, w, v', w'})) + 4 = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (suFramePhi hc v w v' w')
  rw [LinearMap.range_eq_top.mpr (suFramePhi_surjective hfr), suFramePhi_ker hc v w v' w',
    finrank_top] at h
  have h4 : Module.finrank F (Fin 4 → F) = 4 := by simp
  have hn : Module.finrank F (Fin n → F) = n := by simp
  rw [h4, hn] at h
  omega

private noncomputable def suRadTheta {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (g : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))) :
    (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w} where
  toFun x := ⟨natRep (SU (unitaryInvolution F 2 f) n) g.1 x - x, by
    have hx : (x : Fin n → F) ∈ (suH hc n).perp (Submodule.span F {v, w}) :=
      ReflForm.perp_antitone (suH hc n) span_plane_le_span_frame x.2
    exact g.2.2 x hx⟩
  map_add' x y := by
    apply Subtype.ext
    change natRep (SU (unitaryInvolution F 2 f) n) g.1 (x + y) - (x + y) =
      (natRep (SU (unitaryInvolution F 2 f) n) g.1 x - x) +
        (natRep (SU (unitaryInvolution F 2 f) n) g.1 y - y)
    rw [map_add]
    abel
  map_smul' c x := by
    apply Subtype.ext
    change natRep (SU (unitaryInvolution F 2 f) n) g.1 (c • x) - c • x =
      c • (natRep (SU (unitaryInvolution F 2 f) n) g.1 x - x)
    rw [map_smul, smul_sub]

@[simp] private lemma suRadTheta_apply {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (g : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr)))
    (x : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    ((suRadTheta hfr g x : Submodule.span F {v, w}) : Fin n → F) =
      natRep (SU (unitaryInvolution F 2 f) n) g.1 x - x := rfl

private lemma suRadTheta_one {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    suRadTheta hfr (1 : ↥(suStabRad hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr))) = 0 := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  change natRep (SU (unitaryInvolution F 2 f) n)
    (1 : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))).1 x - x = 0
  rw [OneMemClass.coe_one, map_one, Module.End.one_apply, sub_self]

private lemma suRadTheta_add {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (g q : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))) :
    suRadTheta hfr (g * q) = suRadTheta hfr g + suRadTheta hfr q := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  change natRep (SU (unitaryInvolution F 2 f) n) (g.1 * q.1) x - x =
    (natRep (SU (unitaryInvolution F 2 f) n) g.1 x - x) +
      (natRep (SU (unitaryInvolution F 2 f) n) q.1 x - x)
  rw [map_mul, Module.End.mul_apply]
  have hx : (x : Fin n → F) ∈ (suH hc n).perp (Submodule.span F {v, w}) :=
    ReflForm.perp_antitone (suH hc n) span_plane_le_span_frame x.2
  have hfix : natRep (SU (unitaryInvolution F 2 f) n) g.1
      (natRep (SU (unitaryInvolution F 2 f) n) q.1 x - x) =
      natRep (SU (unitaryInvolution F 2 f) n) q.1 x - x :=
    g.2.1 _ (q.2.2 x hx)
  have h1 : natRep (SU (unitaryInvolution F 2 f) n) g.1
      (natRep (SU (unitaryInvolution F 2 f) n) q.1 x) =
      (natRep (SU (unitaryInvolution F 2 f) n) q.1 x - x) +
        natRep (SU (unitaryInvolution F 2 f) n) g.1 x := by
    conv_lhs => rw [← sub_add_cancel (natRep (SU (unitaryInvolution F 2 f) n) q.1 x) x]
    rw [map_add, hfix]
  rw [h1]
  abel

private lemma suRadTheta_inv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (g : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))) :
    suRadTheta hfr g⁻¹ = -suRadTheta hfr g := by
  refine LinearMap.ext fun x => ?_
  have h := suRadTheta_add hfr (g := g) (q := g⁻¹)
  rw [mul_inv_cancel, suRadTheta_one] at h
  have hx : suRadTheta hfr g x + suRadTheta hfr g⁻¹ x = 0 := by
    have := congrArg (fun T => T x) h.symm
    simpa using this
  rw [add_comm] at hx
  exact eq_neg_of_add_eq_zero_left hx

private lemma suRadTheta_eq_zero_iff {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (g : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))) :
    suRadTheta hfr g = 0 ↔
      g.1 ∈ suStabFix hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) := by
  constructor
  · intro h
    refine ⟨g.2, fun y hy => ?_⟩
    rw [perp_plane_eq_sup hfr] at hy
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add, g.2.1 a ha]
    congr 1
    have hz0 : natRep (SU (unitaryInvolution F 2 f) n) g.1 z - z = 0 := by
      have h1 : ((suRadTheta hfr g ⟨z, hz⟩ : Submodule.span F {v, w}) : Fin n → F) = 0 := by
        rw [h]
        rfl
      simpa [suRadTheta_apply] using h1
    exact sub_eq_zero.mp hz0
  · rintro ⟨-, hfix⟩
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    change natRep (SU (unitaryInvolution F 2 f) n) g.1 x - x = 0
    have hx : (x : Fin n → F) ∈ (suH hc n).perp (Submodule.span F {v, w}) :=
      ReflForm.perp_antitone (suH hc n) span_plane_le_span_frame x.2
    rw [hfix x hx, sub_self]

private noncomputable def suRk1V {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w} where
  toFun x := ⟨φ x • v, Submodule.smul_mem _ _ (Submodule.subset_span (by simp))⟩
  map_add' x y := by
    apply Subtype.ext
    show φ (x + y) • v = φ x • v + φ y • v
    rw [map_add, add_smul]
  map_smul' c x := by
    apply Subtype.ext
    show φ (c • x) • v = c • (φ x • v)
    rw [map_smul, smul_assoc]

private noncomputable def suRk1W {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w} where
  toFun x := ⟨φ x • w, Submodule.smul_mem _ _ (Submodule.subset_span (by simp))⟩
  map_add' x y := by
    apply Subtype.ext
    show φ (x + y) • w = φ x • w + φ y • w
    rw [map_add, add_smul]
  map_smul' c x := by
    apply Subtype.ext
    show φ (c • x) • w = c • (φ x • w)
    rw [map_smul, smul_assoc]

private noncomputable def suCompV {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F} :
    ((suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}) →ₗ[F]
      ((suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) where
  toFun T := (suDual (σ := unitaryInvolution F 2 f)
      (hσ := unitaryInvolution_involutive hc) w').comp
    ((Submodule.span F {v, w}).subtype.comp T)
  map_add' T T' := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c T := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

private noncomputable def suCompW {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F} :
    ((suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}) →ₗ[F]
      ((suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) where
  toFun T := (suDual (σ := unitaryInvolution F 2 f)
      (hσ := unitaryInvolution_involutive hc) v').comp
    ((Submodule.span F {v, w}).subtype.comp T)
  map_add' T T' := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c T := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

private lemma compV_apply {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w})
    (x : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    suCompV (hc := hc) T x = (suH hc n).β w' (T x) := rfl

private lemma compW_apply {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w})
    (x : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    suCompW (hc := hc) T x = (suH hc n).β v' (T x) := rfl

private lemma suDecomp_point {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w})
    (x : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    T x = suCompV (hc := hc) T x • v + suCompW (hc := hc) T x • w := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (T x).2
  have h1 : suCompV (hc := hc) T x = a := by
    change (suH hc n).β w' ((T x : Submodule.span F {v, w}) : Fin n → F) = a
    rw [← hab]
    simp only [(suH hc n).add_right, (suH hc n).smul_right, suFrame_w'v hfr, suFrame_w'w hfr,
      mul_one, mul_zero, add_zero]
  have h2 : suCompW (hc := hc) T x = b := by
    change (suH hc n).β v' ((T x : Submodule.span F {v, w}) : Fin n → F) = b
    rw [← hab]
    simp only [(suH hc n).add_right, (suH hc n).smul_right, suFrame_v'v hfr, suFrame_v'w hfr,
      mul_zero, mul_one, zero_add]
  rw [h1, h2]
  exact hab.symm

private lemma suDecomp {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}) :
    T = suRk1V (suCompV (hc := hc) T) + suRk1W (suCompW (hc := hc) T) := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  simpa [suRk1V, suRk1W] using suDecomp_point hfr T x

private noncomputable def suThetaU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)) :
    AddSubgroup ((suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F]
      Submodule.span F {v, w}) where
  carrier := {T | ∃ (g : ↥(suStabRad hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr))), g.1 ∈ V ∧ suRadTheta hfr g = T}
  add_mem' := by
    rintro T T' ⟨g, hg, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨g * q, V.mul_mem hg hq, by rw [suRadTheta_add]⟩
  zero_mem' := ⟨1, V.one_mem, suRadTheta_one hfr⟩
  neg_mem' := by
    rintro T ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, V.inv_mem hg, by rw [suRadTheta_inv]⟩

private lemma mem_suThetaU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F]
      Submodule.span F {v, w}) :
    T ∈ suThetaU hfr V ↔ ∃ (g : ↥(suStabRad hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr))), g.1 ∈ V ∧ suRadTheta hfr g = T := Iff.rfl

private lemma suRadTheta_conj_apply {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    {g : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))}
    {k : ↥(SU (unitaryInvolution F 2 f) n)}
    (hkQ : k * g.1 * k⁻¹ ∈ suStabRad hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr))
    (hkW : ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) k y = y)
    (hkWinv : ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) k⁻¹ y = y)
    (x : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    ((suRadTheta hfr ⟨k * g.1 * k⁻¹, hkQ⟩ x : Submodule.span F {v, w}) : Fin n → F) =
      natRep (SU (unitaryInvolution F 2 f) n) k
        ((suRadTheta hfr g x : Submodule.span F {v, w}) : Fin n → F) := by
  rw [suRadTheta_apply, suRadTheta_apply]
  have hcomp : natRep (SU (unitaryInvolution F 2 f) n) (k * g.1 * k⁻¹) x =
      natRep (SU (unitaryInvolution F 2 f) n) k
        (natRep (SU (unitaryInvolution F 2 f) n) g.1
          (natRep (SU (unitaryInvolution F 2 f) n) k⁻¹ x)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [hcomp, hkWinv x x.2, map_sub, hkW x x.2]

private lemma suRadTheta_transv_apply {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    {t : ↥(SU (unitaryInvolution F 2 f) n)}
    (htA : ∀ a ∈ Submodule.span F {v, w},
      natRep (SU (unitaryInvolution F 2 f) n) t a = a)
    (htW : ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) t y ∈
        (suH hc n).perp (Submodule.span F {v, w, v', w'}))
    (ht2 : t * t = 1)
    (g : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr)))
    (htgQ : t * g.1 * t ∈ suStabRad hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr))
    (z : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    ((suRadTheta hfr ⟨t * g.1 * t, htgQ⟩ z : Submodule.span F {v, w}) : Fin n → F) =
      ((suRadTheta hfr g ⟨natRep (SU (unitaryInvolution F 2 f) n) t z, htW z z.2⟩ :
        Submodule.span F {v, w}) : Fin n → F) := by
  rw [suRadTheta_apply, suRadTheta_apply, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply]
  have htz : natRep (SU (unitaryInvolution F 2 f) n) t
      (natRep (SU (unitaryInvolution F 2 f) n) t z) = z := by
    rw [← Module.End.mul_apply, ← map_mul, ht2, map_one, Module.End.one_apply]
  have hgt : natRep (SU (unitaryInvolution F 2 f) n) g.1
      (natRep (SU (unitaryInvolution F 2 f) n) t z) =
      natRep (SU (unitaryInvolution F 2 f) n) t z +
        ((suRadTheta hfr g ⟨natRep (SU (unitaryInvolution F 2 f) n) t z, htW z z.2⟩ :
          Submodule.span F {v, w}) : Fin n → F) := by
    rw [suRadTheta_apply]
    abel
  rw [hgt, map_add, htz, htA _ (suRadTheta hfr g ⟨natRep (SU (unitaryInvolution F 2 f) n) t z,
    htW z z.2⟩).2]
  abel

private lemma su_exists_fixed_ne_zero_ne_one {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    ∃ t : F, unitaryInvolution F 2 f t = t ∧ t ≠ 0 ∧ t ≠ 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Fˣ = (2 ^ f) ^ 2 - 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hc]
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqord : q ^ 2 - 1 = orderOf g := by
    rw [hord, hcard, hq]
  have hpow : g ^ (q ^ 2 - 1) = 1 := by
    rw [hqord]
    exact pow_orderOf_eq_one g
  have hexp : (q + 1) * q = (q ^ 2 - 1) + (q + 1) := by
    have ha : 1 ≤ q ^ 2 := one_le_pow₀ (show 1 ≤ q by omega)
    have h1 : (q + 1) * q = q ^ 2 + q := by ring
    have h2 : (q ^ 2 - 1) + (q + 1) = q ^ 2 + q := by omega
    rw [h1, h2]
  have hu : (g ^ (q + 1) : Fˣ) ^ q = g ^ (q + 1) := by
    rw [← pow_mul, hexp, pow_add, hpow, one_mul]
  refine ⟨((g ^ (q + 1) : Fˣ) : F), ?_, ?_, ?_⟩
  · rw [unitaryInvolution_apply, ← hq, ← Units.val_pow_eq_pow_val]
    exact congrArg (fun u : Fˣ => (u : F)) hu
  · exact Units.ne_zero _
  · intro h1
    have hlt : q + 1 < orderOf g := by
      rw [← hqord, Nat.lt_sub_iff_add_lt]
      nlinarith [hq4]
    exact (pow_ne_one_of_lt_orderOf (by omega : q + 1 ≠ 0) hlt) (Units.ext h1)

private lemma compV_tv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    suCompV (hc := hc) (suRk1V φ) = φ := by
  ext x
  rw [compV_apply]
  change (suH hc n).β w' (φ x • v) = φ x
  rw [(suH hc n).smul_right, suFrame_w'v hfr, mul_one]

private lemma compW_tv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    suCompW (hc := hc) (suRk1V φ) = 0 := by
  ext x
  rw [compW_apply]
  change (suH hc n).β v' (φ x • v) = 0
  rw [(suH hc n).smul_right, suFrame_v'v hfr, mul_zero]

private lemma compV_tw {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    suCompV (hc := hc) (suRk1W φ) = 0 := by
  ext x
  rw [compV_apply]
  change (suH hc n).β w' (φ x • w) = 0
  rw [(suH hc n).smul_right, suFrame_w'w hfr, mul_zero]

private lemma compW_tw {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    suCompW (hc := hc) (suRk1W φ) = φ := by
  ext x
  rw [compW_apply]
  change (suH hc n).β v' (φ x • w) = φ x
  rw [(suH hc n).smul_right, suFrame_v'w hfr, mul_one]

private lemma suRk1V_add {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (φ ψ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    suRk1V (φ + ψ) = suRk1V φ + suRk1V ψ := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  show (φ + ψ) x • v = φ x • v + ψ x • v
  rw [LinearMap.add_apply, add_smul]

private lemma suRk1V_smul {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F} (c : F)
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    suRk1V (c • φ) = c • suRk1V φ := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  show (c • φ) x • v = c • (φ x • v)
  rw [LinearMap.smul_apply, smul_assoc]

private lemma suThetaU_conj {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {k : ↥(SU (unitaryInvolution F 2 f) n)}
    (hk : k ∈ Subgroup.normalizer
      (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)))
    (hkW : ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) k y = y)
    {T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}}
    (hT : T ∈ suThetaU hfr V) :
    ∃ T' ∈ suThetaU hfr V,
      ∀ x : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        ((T' x : Submodule.span F {v, w}) : Fin n → F) =
          natRep (SU (unitaryInvolution F 2 f) n) k
            ((T x : Submodule.span F {v, w}) : Fin n → F) := by
  obtain ⟨g, hgV, hgT⟩ := hT
  have hkV : k ∈ Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)) := hN hk
  have hkgV : k * g.1 * k⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hkV g.1).mp hgV
  have hkgQ : k * g.1 * k⁻¹ ∈ suStabRad hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr) := hVQ hkgV
  have hkWinv : ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) k⁻¹ y = y := by
    intro y hy
    have h1 : natRep (SU (unitaryInvolution F 2 f) n) k⁻¹
        (natRep (SU (unitaryInvolution F 2 f) n) k y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [hkW y hy] at h1
  refine ⟨suRadTheta hfr ⟨k * g.1 * k⁻¹, hkgQ⟩, ?_, fun x => ?_⟩
  · exact ⟨⟨k * g.1 * k⁻¹, hkgQ⟩, hkgV, rfl⟩
  · have h := suRadTheta_conj_apply hfr (g := g) (k := k) hkgQ hkW hkWinv x
    simpa only [hgT] using h

private lemma suThetaU_torus {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {μ ν : F} (hμ : μ ≠ 0) (hν : ν ≠ 0) (hμν : unitaryInvolution F 2 f (μ * ν) = μ * ν)
    {T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}}
    (hT : T ∈ suThetaU hfr V) :
    ∃ T' ∈ suThetaU hfr V,
      ∀ x : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        ((T' x : Submodule.span F {v, w}) : Fin n → F) =
          (μ * suCompV (hc := hc) T x) • v + (ν * suCompW (hc := hc) T x) • w := by
  obtain ⟨k, hkv, hkw, -, -, hkW⟩ := exists_mem_SU_torus hfr hμ hν hμν
  have hk : k ∈ Subgroup.normalizer
      (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) := by
    rw [mem_normalizer_suPair_iff hfr]
    exact Or.inl ⟨μ, ν, hkv, hkw⟩
  obtain ⟨T', hT', hT'eq⟩ := suThetaU_conj hfr hVQ hN hk hkW hT
  refine ⟨T', hT', fun x => ?_⟩
  rw [hT'eq x, suDecomp_point hfr T x, map_add, map_smul, map_smul, hkv, hkw, smul_smul,
    smul_smul, mul_comm (suCompV (hc := hc) T x) μ, mul_comm (suCompW (hc := hc) T x) ν]

private lemma suThetaU_swap {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}}
    (hT : T ∈ suThetaU hfr V) :
    ∃ T' ∈ suThetaU hfr V,
      ∀ x : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        ((T' x : Submodule.span F {v, w}) : Fin n → F) =
          suCompW (hc := hc) T x • v + suCompV (hc := hc) T x • w := by
  obtain ⟨s, hsv, hsw, -, -, hkW⟩ := exists_mem_SU_swap hfr
  have hk : s ∈ Subgroup.normalizer
      (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) := by
    rw [mem_normalizer_suPair_iff hfr]
    exact Or.inr ⟨1, 1, by rw [hsv, one_smul], by rw [hsw, one_smul]⟩
  obtain ⟨T', hT', hT'eq⟩ := suThetaU_conj hfr hVQ hN hk hkW hT
  refine ⟨T', hT', fun x => ?_⟩
  rw [hT'eq x, suDecomp_point hfr T x, map_add, map_smul, map_smul, hsv, hsw, add_comm]

private lemma suThetaU_transv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {x : Fin n → F} (hxW : x ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}))
    (hxx : (suH hc n).β x x = 0)
    {T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}}
    (hT : T ∈ suThetaU hfr V) :
    ∃ T' ∈ suThetaU hfr V,
      ∀ z : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        ((T' z : Submodule.span F {v, w}) : Fin n → F) =
          (suH hc n).β x z • ((T ⟨x, hxW⟩ : Submodule.span F {v, w}) : Fin n → F) := by
  have hTmem : T ∈ suThetaU hfr V := hT
  obtain ⟨g, hgV, hgT⟩ := hT
  obtain ⟨t, ht⟩ := exists_SU_transvection (unitaryInvolution F 2 f)
    (unitaryInvolution_involutive hc) hxx
  have ht' : ∀ y, natRep (SU (unitaryInvolution F 2 f) n) t y =
      y + (suH hc n).β x y • x := ht
  have hxW' := (mem_frameW_iff x).mp hxW
  have hxv0 : (suH hc n).β v x = 0 := hxW'.1
  have hxw0 : (suH hc n).β w x = 0 := hxW'.2.1
  have hxv : (suH hc n).β x v = 0 := by
    have h := suH_symm (hc := hc) (n := n) v x
    rw [hxv0] at h
    exact (map_eq_zero_iff _ (unitaryInvolution F 2 f).injective).mp h.symm
  have hxw : (suH hc n).β x w = 0 := by
    have h := suH_symm (hc := hc) (n := n) w x
    rw [hxw0] at h
    exact (map_eq_zero_iff _ (unitaryInvolution F 2 f).injective).mp h.symm
  have htv : natRep (SU (unitaryInvolution F 2 f) n) t v = v := by
    rw [ht' v, hxv, zero_smul, add_zero]
  have htw : natRep (SU (unitaryInvolution F 2 f) n) t w = w := by
    rw [ht' w, hxw, zero_smul, add_zero]
  have htA : ∀ a ∈ Submodule.span F {v, w},
      natRep (SU (unitaryInvolution F 2 f) n) t a = a := by
    intro a ha
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp ha
    rw [map_add, map_smul, map_smul, htv, htw]
  have htW : ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      natRep (SU (unitaryInvolution F 2 f) n) t y ∈
        (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
    intro y hy
    rw [ht' y]
    exact Submodule.add_mem _ hy (Submodule.smul_mem _ _ hxW)
  have htx : natRep (SU (unitaryInvolution F 2 f) n) t x = x := by
    rw [ht' x, hxx, zero_smul, add_zero]
  have ht2 : t * t = 1 := by
    apply natRep_injective (SU (unitaryInvolution F 2 f) n)
    apply LinearMap.ext
    intro y
    rw [map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
    have h1 : natRep (SU (unitaryInvolution F 2 f) n) t
        (natRep (SU (unitaryInvolution F 2 f) n) t y) =
        natRep (SU (unitaryInvolution F 2 f) n) t
          (y + (suH hc n).β x y • x) :=
      congrArg (natRep (SU (unitaryInvolution F 2 f) n) t) (ht' y)
    rw [h1, map_add, map_smul, htx, ht' y]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have htN : t ∈ Subgroup.normalizer
      (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) := by
    rw [mem_normalizer_suPair_iff hfr]
    exact Or.inl ⟨1, 1, by rw [htv, one_smul], by rw [htw, one_smul]⟩
  have htV : t ∈ Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)) := hN htN
  have htinv : t⁻¹ = t := by
    have h : t * t⁻¹ = t * t := by rw [mul_inv_cancel, ht2]
    exact mul_left_cancel h
  have htgV : t * g.1 * t ∈ V := by
    have h := (Subgroup.mem_normalizer_iff''.mp htV g.1).mp hgV
    simpa [htinv] using h
  have htgQ : t * g.1 * t ∈ suStabRad hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr) := hVQ htgV
  refine ⟨suRadTheta hfr ⟨t * g.1 * t, htgQ⟩ - T, sub_mem ?_ hTmem, fun z => ?_⟩
  · exact ⟨⟨t * g.1 * t, htgQ⟩, htgV, rfl⟩
  · have h := suRadTheta_transv_apply hfr (t := t) htA htW ht2 g htgQ z
    have hsub : (⟨natRep (SU (unitaryInvolution F 2 f) n) t z, htW z z.2⟩ :
        (suH hc n).perp (Submodule.span F {v, w, v', w'})) =
        z + (suH hc n).β x z • ⟨x, hxW⟩ := by
      apply Subtype.ext
      exact ht' z
    have hTlin : ((T ⟨natRep (SU (unitaryInvolution F 2 f) n) t z, htW z z.2⟩ :
          Submodule.span F {v, w}) : Fin n → F) =
        ((T z : Submodule.span F {v, w}) : Fin n → F) +
          (suH hc n).β x z •
            ((T ⟨x, hxW⟩ : Submodule.span F {v, w}) : Fin n → F) := by
      rw [hsub, map_add, map_smul]
      rfl
    change ((suRadTheta hfr ⟨t * g.1 * t, htgQ⟩ z : Submodule.span F {v, w}) : Fin n → F) -
        ((T z : Submodule.span F {v, w}) : Fin n → F) =
      (suH hc n).β x z • ((T ⟨x, hxW⟩ : Submodule.span F {v, w}) : Fin n → F)
    rw [h, hgT, hTlin, add_sub_cancel_left]



private lemma irra_tv_coe {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F)
    (x : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    (((suRk1V (hc := hc) φ) x : Submodule.span F {v, w}) : Fin n → F) = φ x • v := rfl

private lemma irra_tw_coe {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F)
    (x : (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    (((suRk1W (hc := hc) φ) x : Submodule.span F {v, w}) : Fin n → F) = φ x • w := rfl

private lemma irra_inv_mul_assoc {F : Type} [Field F] {a b : F} (ha : a ≠ 0) :
    a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]

private lemma suThetaU_sep {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} (hf : 2 ≤ f) {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {T : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] Submodule.span F {v, w}}
    (hT : T ∈ suThetaU hfr V) :
    suRk1V (suCompV (hc := hc) T) ∈ suThetaU hfr V ∧
      suRk1W (suCompW (hc := hc) T) ∈ suThetaU hfr V := by
  obtain ⟨t, htσ, ht0, ht1⟩ := su_exists_fixed_ne_zero_ne_one hc hf
  have hμν : unitaryInvolution F 2 f (t * 1) = t * 1 := by rw [mul_one, htσ]
  obtain ⟨T₁, hT₁mem, hT₁eq⟩ :=
    suThetaU_torus hfr hVQ hN ht0 one_ne_zero hμν hT
  have hsub : T₁ - T ∈ suThetaU hfr V := (suThetaU hfr V).sub_mem hT₁mem hT
  have hdiff : T₁ - T = suRk1V ((t - 1) • suCompV (hc := hc) T) := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    rw [LinearMap.sub_apply, Submodule.coe_sub, hT₁eq x, suDecomp_point hfr T x, irra_tv_coe]
    simp only [Submodule.coe_add, Submodule.coe_smul, one_mul, LinearMap.smul_apply, smul_eq_mul]
    have h1 : (t * suCompV (hc := hc) T x) • v + suCompW (hc := hc) T x • w -
        (suCompV (hc := hc) T x • v + suCompW (hc := hc) T x • w) =
        (t * suCompV (hc := hc) T x - suCompV (hc := hc) T x) • v := by
      rw [sub_smul]
      abel
    have h2 : t * suCompV (hc := hc) T x - suCompV (hc := hc) T x =
        (t - 1) * suCompV (hc := hc) T x := by ring
    rw [h1, h2]
  have hmem : suRk1V ((t - 1) • suCompV (hc := hc) T) ∈ suThetaU hfr V := by
    rw [← hdiff]
    exact hsub
  have ht1' : t - 1 ≠ 0 := sub_ne_zero_of_ne ht1
  have hσsub : unitaryInvolution F 2 f (t - 1) = t - 1 := by
    rw [map_sub, htσ, map_one]
  have hμν₂ : unitaryInvolution F 2 f ((t - 1)⁻¹ * 1) = (t - 1)⁻¹ * 1 := by
    rw [mul_one, map_inv₀, hσsub]
  obtain ⟨T₂, hT₂mem, hT₂eq⟩ :=
    suThetaU_torus hfr hVQ hN (inv_ne_zero ht1') one_ne_zero hμν₂ hmem
  have hT₂ : T₂ = suRk1V (suCompV (hc := hc) T) := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    rw [hT₂eq x, compV_tv hfr, compW_tv hfr, irra_tv_coe]
    rw [one_mul, LinearMap.zero_apply, zero_smul, add_zero, LinearMap.smul_apply,
      smul_eq_mul, irra_inv_mul_assoc ht1']
  constructor
  · exact hT₂ ▸ hT₂mem
  · have hsubtv : T - suRk1V (suCompV (hc := hc) T) ∈ suThetaU hfr V := by
      rw [hT₂] at hT₂mem
      exact (suThetaU hfr V).sub_mem hT hT₂mem
    have htw : suRk1W (suCompW (hc := hc) T) = T - suRk1V (suCompV (hc := hc) T) := by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.sub_apply]
      apply Subtype.ext
      rw [Submodule.coe_sub, suDecomp_point hfr T x, irra_tw_coe]
      simp only [Submodule.coe_add, Submodule.coe_smul, irra_tv_coe]
      abel
    rw [htw]
    exact hsubtv

private lemma suThetaU_tv_smul {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F}
    (hφ : suRk1V φ ∈ suThetaU hfr V) (c : F) : suRk1V (c • φ) ∈ suThetaU hfr V := by
  by_cases hc0 : c = 0
  · subst hc0
    have hzero : suRk1V ((0 : F) • φ) = 0 := by
      rw [suRk1V_smul (0 : F) φ, zero_smul]
    rw [hzero]
    exact (suThetaU hfr V).zero_mem
  · have hμν : unitaryInvolution F 2 f (c * c⁻¹) = c * c⁻¹ := by
      rw [mul_inv_cancel₀ hc0, map_one]
    obtain ⟨T', hT'mem, hT'eq⟩ :=
      suThetaU_torus hfr hVQ hN hc0 (inv_ne_zero hc0) hμν hφ
    have hT' : T' = suRk1V (c • φ) := by
      refine LinearMap.ext fun x => ?_
      apply Subtype.ext
      rw [hT'eq x, compV_tv hfr, compW_tv hfr, irra_tv_coe]
      rw [LinearMap.zero_apply, mul_zero, zero_smul, add_zero, LinearMap.smul_apply, smul_eq_mul]
    rw [hT'] at hT'mem
    exact hT'mem

private lemma suThetaU_tv_iff_tw {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    suRk1V φ ∈ suThetaU hfr V ↔ suRk1W φ ∈ suThetaU hfr V := by
  constructor
  · intro hφ
    obtain ⟨T', hT'mem, hT'eq⟩ := suThetaU_swap hfr hVQ hN hφ
    have hT' : T' = suRk1W φ := by
      refine LinearMap.ext fun x => ?_
      apply Subtype.ext
      rw [hT'eq x, compW_tv hfr, compV_tv hfr, irra_tw_coe]
      rw [LinearMap.zero_apply, zero_smul, zero_add]
    rw [hT'] at hT'mem
    exact hT'mem
  · intro hφ
    obtain ⟨T', hT'mem, hT'eq⟩ := suThetaU_swap hfr hVQ hN hφ
    have hT' : T' = suRk1V φ := by
      refine LinearMap.ext fun x => ?_
      apply Subtype.ext
      rw [hT'eq x, compW_tw hfr, compV_tw hfr, irra_tv_coe]
      rw [LinearMap.zero_apply, zero_smul, add_zero]
    rw [hT'] at hT'mem
    exact hT'mem

private lemma suThetaU_tv_transv {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n)))
    {φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F}
    (hφ : suRk1V φ ∈ suThetaU hfr V) {x : Fin n → F}
    (hxW : x ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}))
    (hxx : (suH hc n).β x x = 0) (hφx : φ ⟨x, hxW⟩ ≠ 0) :
    ∃ ψ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F,
      (∀ z : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        ψ z = (suH hc n).β x z) ∧ suRk1V ψ ∈ suThetaU hfr V := by
  obtain ⟨T₁, hT₁mem, hT₁eq⟩ := suThetaU_transv hfr hVQ hN hxW hxx hφ
  let ψ₀ : ((suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :=
    (suDual (σ := unitaryInvolution F 2 f) (hσ := unitaryInvolution_involutive hc) x).comp
      (Submodule.subtype ((suH hc n).perp (Submodule.span F {v, w, v', w'})))
  have hψ₀ : ∀ z : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      ψ₀ z = (suH hc n).β x z := fun z => rfl
  have hT₁ : T₁ = suRk1V (φ ⟨x, hxW⟩ • ψ₀) := by
    refine LinearMap.ext fun z => ?_
    apply Subtype.ext
    rw [hT₁eq z]
    simp only [irra_tv_coe]
    rw [LinearMap.smul_apply, smul_eq_mul, hψ₀ z, smul_smul,
      mul_comm (φ ⟨x, hxW⟩) ((suH hc n).β x z)]
  have hcancel : (φ ⟨x, hxW⟩)⁻¹ • (φ ⟨x, hxW⟩ • ψ₀) = ψ₀ := by
    rw [smul_smul, inv_mul_cancel₀ hφx, one_smul]
  have hmem : suRk1V ((φ ⟨x, hxW⟩)⁻¹ • (φ ⟨x, hxW⟩ • ψ₀)) ∈ suThetaU hfr V :=
    suThetaU_tv_smul hfr hVQ hN (hT₁ ▸ hT₁mem) (φ ⟨x, hxW⟩)⁻¹
  refine ⟨ψ₀, hψ₀, ?_⟩
  rwa [hcancel] at hmem



private lemma exists_eq_beta_of_functional {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (φ : (suH hc n).perp (Submodule.span F {v, w, v', w'}) →ₗ[F] F) :
    ∃ s : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      ∀ z : (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        φ z = (suH hc n).β (s : Fin n → F) (z : Fin n → F) := by
  let W : Submodule F (Fin n → F) := (suH hc n).perp (Submodule.span F {v, w, v', w'})
  let Ψ : W → (W →ₗ[F] F) := fun s =>
    { toFun := fun z => (suH hc n).β (s : Fin n → F) (z : Fin n → F)
      map_add' := fun z z' => (suH hc n).add_right (s : Fin n → F) z z'
      map_smul' := fun c z => (suH hc n).smul_right c (s : Fin n → F) z }
  have hinj : Function.Injective Ψ := by
    intro s s' h
    have hz : ∀ z : W, (suH hc n).β (s : Fin n → F) (z : Fin n → F) =
        (suH hc n).β (s' : Fin n → F) (z : Fin n → F) := by
      intro z
      have h1 := congrArg (fun (g : W →ₗ[F] F) => g z) h
      simpa [Ψ] using h1
    have huz : ∀ z : W, (suH hc n).β ((s - s' : W) : Fin n → F) (z : Fin n → F) = 0 := by
      intro z
      rw [Submodule.coe_sub, (suH hc n).β_sub_left, hz z, sub_self]
    have hzero : ((s - s' : W) : Fin n → F) = 0 := by
      apply (suH hc n).nondeg
      intro y
      have hu : ((s - s' : W) : Fin n → F) ∈ W := (s - s').2
      have hu_v : (suH hc n).β ((s - s' : W) : Fin n → F) v = 0 :=
        (suH hc n).refl v _ (hu v (Submodule.subset_span (by simp)))
      have hu_w : (suH hc n).β ((s - s' : W) : Fin n → F) w = 0 :=
        (suH hc n).refl w _ (hu w (Submodule.subset_span (by simp)))
      have hu_v' : (suH hc n).β ((s - s' : W) : Fin n → F) v' = 0 :=
        (suH hc n).refl v' _ (hu v' (Submodule.subset_span (by simp)))
      have hu_w' : (suH hc n).β ((s - s' : W) : Fin n → F) w' = 0 :=
        (suH hc n).refl w' _ (hu w' (Submodule.subset_span (by simp)))
      set a : Fin n → F := (suH hc n).β w' y • v + (suH hc n).β v' y • w +
        (suH hc n).β w y • v' + (suH hc n).β v y • w' with ha
      set z : Fin n → F := y - (suH hc n).β w' y • v - (suH hc n).β v' y • w -
        (suH hc n).β w y • v' - (suH hc n).β v y • w' with hzdef
      have hz_mem : z ∈ W := by
        rw [hzdef]
        exact frame_proj_mem_W hfr y
      have ha_span : a ∈ Submodule.span F {v, w, v', w'} := by
        rw [ha]
        exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have ha0 : (suH hc n).β ((s - s' : W) : Fin n → F) a = 0 :=
        (suH hc n).refl a _ (hu a ha_span)
      have hz0 : (suH hc n).β ((s - s' : W) : Fin n → F) z = 0 := huz ⟨z, hz_mem⟩
      have hdecomp : y = a + z := by
        rw [ha, hzdef]
        abel
      have hsum := (suH hc n).add_right ((s - s' : W) : Fin n → F) a z
      rw [hdecomp, hsum, ha0, hz0, add_zero]
    apply Subtype.ext
    have hsub : (s : Fin n → F) - (s' : Fin n → F) = 0 := by
      simpa using hzero
    exact sub_eq_zero.mp hsub
  have hcard : Nat.card (W →ₗ[F] F) = Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := W →ₗ[F] F),
      Module.natCard_eq_pow_finrank (K := F) (V := W), Subspace.dual_finrank_eq]
  haveI hfin : Finite (W →ₗ[F] F) :=
    Finite.of_injective (fun g : W →ₗ[F] F => (g : W → F))
      (fun g₁ g₂ h => LinearMap.ext fun z => congrFun h z)
  have hsurj : Function.Surjective Ψ :=
    (hinj.bijective_of_nat_card_le hcard.le).2
  obtain ⟨s, hs⟩ := hsurj φ
  refine ⟨s, fun z => ?_⟩
  have h1 := congrArg (fun (g : W →ₗ[F] F) => g z) hs
  simpa [Ψ] using h1.symm



private lemma irrg_frame_PP {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    ∀ i j : Fin 2, uForm (unitaryInvolution F 2 f) (![v, w] i) (![v, w] j) = 0 := by
  intro i j
  rw [← suH_beta_uForm (hc := hc)]
  fin_cases i <;> fin_cases j <;>
    simp [suFrame_vv hfr, suFrame_vw hfr, suFrame_wv hfr, suFrame_ww hfr]

private lemma irrg_frame_QQ {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    ∀ i j : Fin 2, uForm (unitaryInvolution F 2 f) (![w', v'] i) (![w', v'] j) = 0 := by
  intro i j
  rw [← suH_beta_uForm (hc := hc)]
  fin_cases i <;> fin_cases j <;>
    simp [suFrame_w'w' hfr, suFrame_w'v' hfr, suFrame_v'w' hfr, suFrame_v'v' hfr]

private lemma irrg_frame_PQ {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    ∀ i j : Fin 2, uForm (unitaryInvolution F 2 f) (![v, w] i) (![w', v'] j) =
      if i = j then 1 else 0 := by
  intro i j
  rw [← suH_beta_uForm (hc := hc)]
  fin_cases i <;> fin_cases j <;>
    simp [suFrame_vw' hfr, suFrame_vv' hfr, suFrame_ww' hfr, suFrame_wv' hfr]

private lemma irrg_hypProj_mem_W {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (y : Fin n → F) :
    hypProj (unitaryInvolution F 2 f) ![v, w] ![w', v'] y ∈
      (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
  rw [mem_frameW_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [suH_beta_uForm]
    exact uForm_hypProj_P (irrg_frame_PP hfr) (irrg_frame_PQ hfr) y 0
  · rw [suH_beta_uForm]
    exact uForm_hypProj_P (irrg_frame_PP hfr) (irrg_frame_PQ hfr) y 1
  · rw [suH_beta_uForm]
    exact uForm_hypProj_Q (unitaryInvolution_involutive hc) (irrg_frame_QQ hfr)
      (irrg_frame_PQ hfr) y 1
  · rw [suH_beta_uForm]
    exact uForm_hypProj_Q (unitaryInvolution_involutive hc) (irrg_frame_QQ hfr)
      (irrg_frame_PQ hfr) y 0

private lemma irrg_uForm_hypProj_of_mem_W {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    {e : Fin n → F}
    (he : e ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'})) (y : Fin n → F) :
    uForm (unitaryInvolution F 2 f) e
        (hypProj (unitaryInvolution F 2 f) ![v, w] ![w', v'] y) =
      uForm (unitaryInvolution F 2 f) e y := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hc
  obtain ⟨h1, h2, h3, h4⟩ := (mem_frameW_iff e).mp he
  have h1' : uForm (unitaryInvolution F 2 f) v e = 0 := by
    rw [← suH_beta_uForm (hc := hc)]
    exact h1
  have h2' : uForm (unitaryInvolution F 2 f) w e = 0 := by
    rw [← suH_beta_uForm (hc := hc)]
    exact h2
  have h3' : uForm (unitaryInvolution F 2 f) v' e = 0 := by
    rw [← suH_beta_uForm (hc := hc)]
    exact h3
  have h4' : uForm (unitaryInvolution F 2 f) w' e = 0 := by
    rw [← suH_beta_uForm (hc := hc)]
    exact h4
  refine uForm_hypProj_of_perp (P := ![v, w]) (Q := ![w', v']) ?_ ?_ y
  · intro k
    fin_cases k
    · exact uForm_eq_zero_comm hσ h1'
    · exact uForm_eq_zero_comm hσ h2'
  · intro k
    fin_cases k
    · exact uForm_eq_zero_comm hσ h4'
    · exact uForm_eq_zero_comm hσ h3'

private lemma irrg_exists_uForm_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {n : ℕ} {a : Fin n → F} (ha : a ≠ 0) :
    ∃ y : Fin n → F, uForm (unitaryInvolution F 2 f) a y = 1 := by
  obtain ⟨i, hi⟩ := exists_uForm_single_ne_zero (σ := unitaryInvolution F 2 f) ha
  exact ⟨(uForm (unitaryInvolution F 2 f) a (Pi.single (Fin.rev i) 1))⁻¹ •
      Pi.single (Fin.rev i) 1, by
    rw [uForm_smul_right, inv_mul_cancel₀ hi]⟩

private lemma irrg_exists_isotropic_mem_W {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F} (hm : 6 ≤ n) :
    ∃ e ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}), e ≠ 0 ∧
      uForm (unitaryInvolution F 2 f) e e = 0 := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hc
  have hnorm : ∀ d : F, unitaryInvolution F 2 f d = d →
      ∃ l : F, unitaryInvolution F 2 f l * l = d :=
    fun d hd => exists_sigma_mul_self_eq (p := 2) (f := f) hc hd
  obtain ⟨e, he0, hee, hPe, hQe⟩ :=
    exists_isotropic_perp hσ hnorm (P := ![v, w]) (Q := ![w', v']) (by omega)
  refine ⟨e, ?_, he0, hee⟩
  rw [mem_frameW_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [suH_beta_uForm]
  · exact hPe 0
  · exact hPe 1
  · exact hQe 1
  · exact hQe 0

private lemma irrg_exists_isotropic_partner_mem_W {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {e : Fin n → F}
    (he : e ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'})) (he0 : e ≠ 0)
    (hee : uForm (unitaryInvolution F 2 f) e e = 0) :
    ∃ g ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      uForm (unitaryInvolution F 2 f) g g = 0 ∧ uForm (unitaryInvolution F 2 f) e g = 1 := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hc
  have htr : ∀ a : F, unitaryInvolution F 2 f a = a →
      ∃ c : F, c + unitaryInvolution F 2 f c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hc ha
  obtain ⟨y₀, hy₀⟩ := irrg_exists_uForm_eq_one (f := f) (n := n) (a := e) he0
  set y : Fin n → F := hypProj (unitaryInvolution F 2 f) ![v, w] ![w', v'] y₀ with hydef
  have hyW : y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
    rw [hydef]
    exact irrg_hypProj_mem_W hfr y₀
  have hey : uForm (unitaryInvolution F 2 f) e y = 1 := by
    rw [hydef, irrg_uForm_hypProj_of_mem_W he y₀, hy₀]
  have hye : uForm (unitaryInvolution F 2 f) y e = 1 := by
    rw [← uForm_conj (unitaryInvolution F 2 f) hσ, hey, map_one]
  obtain ⟨c, hc'⟩ := htr (-(uForm (unitaryInvolution F 2 f) y y))
    (by rw [map_neg, uForm_conj (unitaryInvolution F 2 f) hσ])
  refine ⟨y + c • e, ?_, ?_, ?_⟩
  · exact ((suH hc n).perp (Submodule.span F {v, w, v', w'})).add_mem hyW
      (((suH hc n).perp (Submodule.span F {v, w, v', w'})).smul_mem c he)
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hee, hey, hye]
    linear_combination hc'
  · rw [uForm_add_right, uForm_smul_right, hee, mul_zero, add_zero, hey]

private lemma irrg_exists_isotropic_mem_W_beta_ne_zero {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (hm : 6 ≤ n) {x : Fin n → F}
    (hx : x ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'})) (hx0 : x ≠ 0) :
    ∃ e ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      uForm (unitaryInvolution F 2 f) e e = 0 ∧ uForm (unitaryInvolution F 2 f) e x ≠ 0 := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hc
  have htr : ∀ a : F, unitaryInvolution F 2 f a = a →
      ∃ c : F, c + unitaryInvolution F 2 f c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hc ha
  obtain ⟨e₀, he₀, he₀0, he₀e₀⟩ :=
    irrg_exists_isotropic_mem_W (hc := hc) (v := v) (w := w) (v' := v') (w' := w') hm
  obtain ⟨f₀, hf₀, hf₀f₀, he₀f₀⟩ :=
    irrg_exists_isotropic_partner_mem_W hfr he₀ he₀0 he₀e₀
  by_cases he₀x : uForm (unitaryInvolution F 2 f) e₀ x = 0
  swap
  · exact ⟨e₀, he₀, he₀e₀, he₀x⟩
  by_cases hf₀x : uForm (unitaryInvolution F 2 f) f₀ x = 0
  swap
  · exact ⟨f₀, hf₀, hf₀f₀, hf₀x⟩
  by_cases hxx : uForm (unitaryInvolution F 2 f) x x = 0
  · obtain ⟨e, he, hee, hxe⟩ := irrg_exists_isotropic_partner_mem_W hfr hx hx0 hxx
    refine ⟨e, he, hee, ?_⟩
    rw [← uForm_conj (unitaryInvolution F 2 f) hσ, hxe, map_one]
    exact one_ne_zero
  have hxe₀ : uForm (unitaryInvolution F 2 f) x e₀ = 0 :=
    uForm_eq_zero_comm hσ he₀x
  have hxf₀ : uForm (unitaryInvolution F 2 f) x f₀ = 0 :=
    uForm_eq_zero_comm hσ hf₀x
  have hf₀e₀ : uForm (unitaryInvolution F 2 f) f₀ e₀ = 1 := by
    rw [← uForm_conj (unitaryInvolution F 2 f) hσ, he₀f₀, map_one]
  obtain ⟨t, ht⟩ := htr (uForm (unitaryInvolution F 2 f) x x)
    (uForm_conj (unitaryInvolution F 2 f) hσ x x)
  refine ⟨f₀ + t • e₀ + x, ?_, ?_, ?_⟩
  · exact ((suH hc n).perp (Submodule.span F {v, w, v', w'})).add_mem
      (((suH hc n).perp (Submodule.span F {v, w, v', w'})).add_mem hf₀
        (((suH hc n).perp (Submodule.span F {v, w, v', w'})).smul_mem t he₀)) hx
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hf₀f₀,
      he₀e₀, he₀f₀, hf₀e₀, he₀x, hf₀x, hxe₀, hxf₀]
    linear_combination ht + CharTwo.add_self_eq_zero (uForm (unitaryInvolution F 2 f) x x)
  · simp only [uForm_add_left, uForm_smul_left, hf₀x, he₀x, mul_zero, zero_add]
    exact hxx

private lemma irrg_exists_isotropic_both_mem_W {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {e e' : Fin n → F}
    (he : e ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}))
    (he' : e' ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'})) (he0 : e ≠ 0) (he'0 : e' ≠ 0)
    (hee : uForm (unitaryInvolution F 2 f) e e = 0)
    (he'e' : uForm (unitaryInvolution F 2 f) e' e' = 0) :
    ∃ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      uForm (unitaryInvolution F 2 f) y y = 0 ∧
        uForm (unitaryInvolution F 2 f) e y ≠ 0 ∧ uForm (unitaryInvolution F 2 f) e' y ≠ 0 := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hc
  obtain ⟨g, hg, hgg, heg⟩ := irrg_exists_isotropic_partner_mem_W hfr he he0 hee
  by_cases he'g : uForm (unitaryInvolution F 2 f) e' g = 0
  swap
  · exact ⟨g, hg, hgg, by rw [heg]; exact one_ne_zero, he'g⟩
  obtain ⟨g', hg', hg'g', he'g'⟩ := irrg_exists_isotropic_partner_mem_W hfr he' he'0 he'e'
  by_cases heg' : uForm (unitaryInvolution F 2 f) e g' = 0
  swap
  · exact ⟨g', hg', hg'g', heg', by rw [he'g']; exact one_ne_zero⟩
  have hg'g : uForm (unitaryInvolution F 2 f) g' g =
      unitaryInvolution F 2 f (uForm (unitaryInvolution F 2 f) g g') :=
    (uForm_conj (unitaryInvolution F 2 f) hσ g g').symm
  obtain ⟨t, ht0, ht⟩ : ∃ t : F, t ≠ 0 ∧
      unitaryInvolution F 2 f t * unitaryInvolution F 2 f (uForm (unitaryInvolution F 2 f) g g') +
        t * uForm (unitaryInvolution F 2 f) g g' = 0 := by
    by_cases hgg' : uForm (unitaryInvolution F 2 f) g g' = 0
    · exact ⟨1, one_ne_zero, by rw [hgg', map_zero, mul_zero, mul_zero, add_zero]⟩
    · refine ⟨(uForm (unitaryInvolution F 2 f) g g')⁻¹, inv_ne_zero hgg', ?_⟩
      rw [← map_mul, inv_mul_cancel₀ hgg', map_one]
      exact CharTwo.add_self_eq_zero 1
  refine ⟨g + t • g', ?_, ?_, ?_, ?_⟩
  · exact ((suH hc n).perp (Submodule.span F {v, w, v', w'})).add_mem hg
      (((suH hc n).perp (Submodule.span F {v, w, v', w'})).smul_mem t hg')
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hgg, hg'g',
      hg'g]
    linear_combination ht
  · rw [uForm_add_right, uForm_smul_right, heg, heg', mul_zero, add_zero]
    exact one_ne_zero
  · rw [uForm_add_right, uForm_smul_right, he'g, he'g', mul_one, zero_add]
    exact ht0

private lemma irrg_exists_isotropic_add_mem_W {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (hm : 6 ≤ n) {w₀ : Fin n → F}
    (hw : w₀ ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'})) :
    ∃ e₁ ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
      ∃ e₂ ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        uForm (unitaryInvolution F 2 f) e₁ e₁ = 0 ∧
          uForm (unitaryInvolution F 2 f) e₂ e₂ = 0 ∧ w₀ = e₁ + e₂ := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hc
  have htr : ∀ a : F, unitaryInvolution F 2 f a = a →
      ∃ c : F, c + unitaryInvolution F 2 f c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hc ha
  have hu0 : uForm (unitaryInvolution F 2 f) (0 : Fin n → F) 0 = 0 :=
    uForm_zero_right 0
  by_cases hww : uForm (unitaryInvolution F 2 f) w₀ w₀ = 0
  · exact ⟨w₀, hw, 0,
      ((suH hc n).perp (Submodule.span F {v, w, v', w'})).zero_mem, hww, hu0,
      (add_zero w₀).symm⟩
  have hw0 : w₀ ≠ 0 := by
    rintro rfl
    exact hww hu0
  obtain ⟨e, he, hee, hew⟩ := irrg_exists_isotropic_mem_W_beta_ne_zero hfr hm hw hw0
  have hwe0 : uForm (unitaryInvolution F 2 f) w₀ e ≠ 0 := by
    rw [← uForm_conj (unitaryInvolution F 2 f) hσ]
    exact (map_ne_zero (unitaryInvolution F 2 f)).2 hew
  obtain ⟨c₀, hc₀⟩ := htr (uForm (unitaryInvolution F 2 f) w₀ w₀)
    (uForm_conj (unitaryInvolution F 2 f) hσ w₀ w₀)
  obtain ⟨c, h1⟩ : ∃ c : F, c * uForm (unitaryInvolution F 2 f) w₀ e = c₀ :=
    ⟨c₀ / uForm (unitaryInvolution F 2 f) w₀ e, div_mul_cancel₀ c₀ hwe0⟩
  have h2 : unitaryInvolution F 2 f c * uForm (unitaryInvolution F 2 f) e w₀ =
      unitaryInvolution F 2 f c₀ := by
    rw [← uForm_conj (unitaryInvolution F 2 f) hσ w₀ e, ← map_mul, h1]
  refine ⟨w₀ + c • e, ?_, c • e, ?_, ?_, ?_, ?_⟩
  · exact ((suH hc n).perp (Submodule.span F {v, w, v', w'})).add_mem hw
      (((suH hc n).perp (Submodule.span F {v, w, v', w'})).smul_mem c he)
  · exact ((suH hc n).perp (Submodule.span F {v, w, v', w'})).smul_mem c he
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hee]
    linear_combination h1 + h2 + hc₀ + CharTwo.add_self_eq_zero
      (uForm (unitaryInvolution F 2 f) w₀ w₀)
  · rw [uForm_smul_left, uForm_smul_right, hee, mul_zero, mul_zero]
  · rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

private lemma frameW_submodule_eq_bot_or {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (S : Submodule F (Fin n → F))
    (hSW : S ≤ (suH hc n).perp (Submodule.span F {v, w, v', w'}))
    (hS : ∀ x ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}), (suH hc n).β x x = 0 →
      ∀ s ∈ S, (suH hc n).β x s ≠ 0 → x ∈ S) :
    S = ⊥ ∨ (suH hc n).perp (Submodule.span F {v, w, v', w'}) ≤ S := by
  have h4 : 4 ≤ n := four_le_of_suFrame hfr
  by_cases hn4 : n = 4
  · left
    have hdim : Module.finrank F ((suH hc n).perp (Submodule.span F {v, w, v', w'})) = 0 := by
      have h := su_finrank_frameW hfr
      omega
    have hbot : (suH hc n).perp (Submodule.span F {v, w, v', w'}) = ⊥ :=
      (Submodule.finrank_eq_zero).mp hdim
    rw [hbot] at hSW
    exact le_bot_iff.mp hSW
  by_cases hn5 : n = 5
  · have hdim : Module.finrank F ((suH hc n).perp (Submodule.span F {v, w, v', w'})) = 1 := by
      have h := su_finrank_frameW hfr
      omega
    rcases Nat.eq_zero_or_pos (Module.finrank F S) with hS0 | hSpos
    · left
      exact (Submodule.finrank_eq_zero).mp hS0
    · right
      have hSle : Module.finrank F S ≤
          Module.finrank F ((suH hc n).perp (Submodule.span F {v, w, v', w'})) :=
        Submodule.finrank_mono hSW
      have hS1 : Module.finrank F S = 1 := by omega
      have heq : S = (suH hc n).perp (Submodule.span F {v, w, v', w'}) :=
        Submodule.eq_of_le_of_finrank_le hSW (by omega)
      exact le_of_eq heq.symm
  · have hm : 6 ≤ n := by omega
    by_cases hSbot : S = ⊥
    · exact Or.inl hSbot
    right
    obtain ⟨x₀, hx₀S, hx₀0⟩ : ∃ x₀ ∈ S, x₀ ≠ 0 := by
      by_contra h
      exact hSbot (le_bot_iff.mp fun x hx => by
        have hx0 : x = 0 := by
          by_contra hxne
          exact h ⟨x, hx, hxne⟩
        rw [hx0]
        exact Submodule.zero_mem ⊥)
    have hx₀W : x₀ ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := hSW hx₀S
    have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
      unitaryInvolution_involutive hc
    obtain ⟨y₁, hy₁W, hy₁y₁, hy₁x₀⟩ :=
      irrg_exists_isotropic_mem_W_beta_ne_zero hfr hm hx₀W hx₀0
    have hy₁S : y₁ ∈ S := by
      refine hS y₁ hy₁W ?_ x₀ hx₀S ?_
      · rw [suH_beta_uForm]; exact hy₁y₁
      · rw [suH_beta_uForm]; exact hy₁x₀
    have hy₁0 : y₁ ≠ 0 := by
      rintro rfl
      exact hy₁x₀ (by simp [uForm_eq])
    have hiso : ∀ u ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        uForm (unitaryInvolution F 2 f) u u = 0 → u ∈ S := by
      intro u hu huu
      by_cases hu0 : u = 0
      · rw [hu0]; exact S.zero_mem
      obtain ⟨y₂, hy₂W, hy₂y₂, huy₂, hy₁y₂⟩ :=
        irrg_exists_isotropic_both_mem_W hfr hu hy₁W hu0 hy₁0 huu hy₁y₁
      have hy₂y₁ : uForm (unitaryInvolution F 2 f) y₂ y₁ ≠ 0 := by
        rw [← uForm_conj (unitaryInvolution F 2 f) hσ]
        exact (map_ne_zero (unitaryInvolution F 2 f)).2 hy₁y₂
      have hy₂S : y₂ ∈ S := by
        refine hS y₂ hy₂W ?_ y₁ hy₁S ?_
        · rw [suH_beta_uForm]; exact hy₂y₂
        · rw [suH_beta_uForm]; exact hy₂y₁
      refine hS u hu ?_ y₂ hy₂S ?_
      · rw [suH_beta_uForm]; exact huu
      · rw [suH_beta_uForm]; exact huy₂
    intro z hz
    obtain ⟨e₁, he₁W, e₂, he₂W, he₁e₁, he₂e₂, rfl⟩ :=
      irrg_exists_isotropic_add_mem_W hfr hm hz
    exact S.add_mem (hiso e₁ he₁W he₁e₁) (hiso e₂ he₂W he₂e₂)



private lemma irrf_suRadTheta_mul_inv_mem {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w')
    (g g' : ↥(suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr)))
    (hg'T : suRadTheta hfr g' = suRadTheta hfr g) :
    (g * g'⁻¹).1 ∈ suStabFix hc n (Submodule.span F {v, w})
      (suFrame_isTotallyIsotropic hfr) := by
  have h1 : suRadTheta hfr (g * g'⁻¹) = 0 := by
    rw [suRadTheta_add hfr g g'⁻¹, suRadTheta_inv hfr g', hg'T]
    exact add_neg_cancel (suRadTheta hfr g)
  exact (suRadTheta_eq_zero_iff hfr (g * g'⁻¹)).mp h1

theorem suStabRad_irreducible {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} (hf : 2 ≤ f) {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {V : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hZV : suStabFix hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) ≤ V)
    (hVQ : V ≤ suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr))
    (hN : Subgroup.normalizer
        (suPair (unitaryInvolution F 2 f) n v w : Set ↥(SU (unitaryInvolution F 2 f) n)) ≤
      Subgroup.normalizer (V : Set ↥(SU (unitaryInvolution F 2 f) n))) :
    V = suStabFix hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) ∨
      V = suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) := by
  let W : Submodule F (Fin n → F) := (suH hc n).perp (Submodule.span F {v, w, v', w'})
  let U : AddSubgroup (W →ₗ[F] Submodule.span F {v, w}) := suThetaU hfr V
  let S : Submodule F (Fin n → F) :=
    { carrier := {s | s ∈ W ∧ ∃ ψ : W →ₗ[F] F,
        (∀ z : W, ψ z = (suH hc n).β s (z : Fin n → F)) ∧ suRk1V ψ ∈ U}
      add_mem' := by
        rintro s s' ⟨hsW, ψ, hψ, htvψ⟩ ⟨hs'W, ψ', hψ', htvψ'⟩
        exact ⟨W.add_mem hsW hs'W, ψ + ψ', fun z => by
            rw [LinearMap.add_apply, hψ z, hψ' z, (suH hc n).add_left], by
            rw [suRk1V_add]
            exact U.add_mem htvψ htvψ'⟩
      zero_mem' := by
        refine ⟨W.zero_mem, 0, ?_, ?_⟩
        · intro z
          rw [(suH hc n).β_zero_left]
          rfl
        · have h0 : suRk1V (0 : W →ₗ[F] F) = 0 := by
            ext z
            simp [suRk1V]
          rw [h0]
          exact U.zero_mem
      smul_mem' := by
        rintro c s ⟨hsW, ψ, hψ, htvψ⟩
        refine ⟨W.smul_mem c hsW, unitaryInvolution F 2 f c • ψ, ?_, ?_⟩
        · intro z
          rw [LinearMap.smul_apply, hψ z, (suH hc n).smul_left, smul_eq_mul]
          rfl
        · exact suThetaU_tv_smul hfr hVQ hN htvψ (unitaryInvolution F 2 f c) }
  have hSW : S ≤ W := fun s hs => hs.1
  have hS : ∀ x ∈ W, (suH hc n).β x x = 0 → ∀ s ∈ S, (suH hc n).β x s ≠ 0 → x ∈ S := by
    intro x hxW hxx s hsS hxs
    obtain ⟨-, ψ, hψ, htvψ⟩ := hsS
    refine ⟨hxW, ?_⟩
    have hxne : ψ ⟨x, hxW⟩ ≠ 0 := by
      rw [hψ]
      intro h0
      have h1 : unitaryInvolution F 2 f ((suH hc n).β x s) = 0 := by
        rwa [suH_symm s x] at h0
      exact hxs ((map_eq_zero_iff _ (unitaryInvolution F 2 f).injective).mp h1)
    obtain ⟨ψ', hψ', htvψ'⟩ := suThetaU_tv_transv hfr hVQ hN htvψ hxW hxx hxne
    exact ⟨ψ', hψ', htvψ'⟩
  rcases frameW_submodule_eq_bot_or hfr S hSW hS with hSbot | hStop
  · left
    refine le_antisymm ?_ hZV
    intro g hgV
    have hgQ : g ∈ suStabRad hc n (Submodule.span F {v, w})
        (suFrame_isTotallyIsotropic hfr) := hVQ hgV
    let T : W →ₗ[F] Submodule.span F {v, w} := suRadTheta hfr ⟨g, hgQ⟩
    have hT : T ∈ U := ⟨⟨g, hgQ⟩, hgV, rfl⟩
    obtain ⟨htvV, htwW⟩ := suThetaU_sep hf hfr hVQ hN hT
    have htvW : suRk1V (suCompW (hc := hc) T) ∈ U :=
      (suThetaU_tv_iff_tw hfr hVQ hN (suCompW (hc := hc) T)).mpr htwW
    obtain ⟨s, hs⟩ := exists_eq_beta_of_functional hfr (suCompV (hc := hc) T)
    have hsS : (s : Fin n → F) ∈ S := ⟨s.2, suCompV (hc := hc) T, hs, htvV⟩
    have hs0 : (s : Fin n → F) = 0 := by
      have hmem : (s : Fin n → F) ∈ (⊥ : Submodule F (Fin n → F)) := by
        rw [← hSbot]
        exact hsS
      simpa using hmem
    have hcompV0 : suCompV (hc := hc) T = 0 := by
      ext z
      rw [hs z, hs0, (suH hc n).β_zero_left]
      rfl
    obtain ⟨s', hs'⟩ := exists_eq_beta_of_functional hfr (suCompW (hc := hc) T)
    have hs'S : (s' : Fin n → F) ∈ S := ⟨s'.2, suCompW (hc := hc) T, hs', htvW⟩
    have hs'0 : (s' : Fin n → F) = 0 := by
      have hmem : (s' : Fin n → F) ∈ (⊥ : Submodule F (Fin n → F)) := by
        rw [← hSbot]
        exact hs'S
      simpa using hmem
    have hcompW0 : suCompW (hc := hc) T = 0 := by
      ext z
      rw [hs' z, hs'0, (suH hc n).β_zero_left]
      rfl
    have hT0 : T = 0 := by
      rw [suDecomp hfr T, hcompV0, hcompW0]
      ext z
      simp [suRk1V, suRk1W]
    exact (suRadTheta_eq_zero_iff hfr ⟨g, hgQ⟩).mp hT0
  · right
    refine le_antisymm hVQ ?_
    have hall_tv : ∀ φ : W →ₗ[F] F, suRk1V φ ∈ U := by
      intro φ
      obtain ⟨s, hs⟩ := exists_eq_beta_of_functional hfr φ
      obtain ⟨-, ψ, hψ, htvψ⟩ := hStop s.2
      have hψφ : ψ = φ := LinearMap.ext fun z => by rw [hψ z, ← hs z]
      rw [← hψφ]
      exact htvψ
    have hall_tw : ∀ φ : W →ₗ[F] F, suRk1W φ ∈ U := fun φ =>
      (suThetaU_tv_iff_tw hfr hVQ hN φ).mp (hall_tv φ)
    intro g hgQ
    let T : W →ₗ[F] Submodule.span F {v, w} := suRadTheta hfr ⟨g, hgQ⟩
    have hT : T ∈ U := by
      rw [suDecomp hfr T]
      exact U.add_mem (hall_tv (suCompV (hc := hc) T)) (hall_tw (suCompW (hc := hc) T))
    obtain ⟨g', hg'V, hg'T⟩ := (mem_suThetaU hfr T).mp hT
    have hZ0 : (⟨g, hgQ⟩ * g'⁻¹).1 ∈ suStabFix hc n (Submodule.span F {v, w})
        (suFrame_isTotallyIsotropic hfr) :=
      irrf_suRadTheta_mul_inv_mem hfr ⟨g, hgQ⟩ g' hg'T
    have h1V : (⟨g, hgQ⟩ * g'⁻¹).1 ∈ V := hZV hZ0
    have h2V : g'.1 ∈ V := hg'V
    have heq : g = (⟨g, hgQ⟩ * g'⁻¹).1 * g'.1 := by
      have hgrp : (⟨g, hgQ⟩ * g'⁻¹) * g' = ⟨g, hgQ⟩ := by group
      calc g = ((⟨g, hgQ⟩ * g'⁻¹) * g').1 := by rw [hgrp]
        _ = (⟨g, hgQ⟩ * g'⁻¹).1 * g'.1 := rfl
    rw [heq]
    exact V.mul_mem h1V h2V


end CFSG.StandardType.LieKnownR2.Short
