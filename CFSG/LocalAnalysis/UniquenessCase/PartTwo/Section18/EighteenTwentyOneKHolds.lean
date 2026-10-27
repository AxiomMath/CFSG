module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4ModelTv
public import CFSG.LieType.Universal.Unitary.SiegelRadical
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open Subgroup CFSG.Quasithin CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Unitary (SUid card_PW_eq_two_pow_four_mul)

section Coords

variable {W : Type} [CommGroup W] [Finite W] {n : ℕ} {F : Type} [Field F] [Finite F]
  {σ : F ≃+* F} {H : Subgroup (MulAut W)}
  {ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F)} {ψ : W ≃* Multiplicative (Fin 4 → F)}

noncomputable def coordsEps (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) :
    ↥H ≃* ↥(SUid σ 4) :=
  ε.trans (MulEquiv.subgroupCongr hS.symm)

noncomputable def coordsE {A : Subgroup (MulAut W)} (hAH : A ≤ H)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) : Subgroup (SUid σ 4) :=
  ((coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)).range

theorem coords_psi_smul (hψ : NatCoordsSU4 H n F ε ψ)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (l : ↥H) (s : W) :
    Multiplicative.toAdd (ψ ((l : MulAut W) s)) =
      (coordsEps (ε := ε) hS l : SUid σ 4) • Multiplicative.toAdd (ψ s) := by
  have h := hψ l s
  rw [h, Subgroup.smul_def]
  have hcoe : ((coordsEps (ε := ε) hS l : SUid σ 4) : GL (Fin 4) F) = (ε l : GL (Fin 4) F) := by
    simp [coordsEps, MulEquiv.subgroupCongr_apply]
  rw [hcoe]
  rfl

theorem mem_fixV_coords {A : Subgroup (MulAut W)} (hAH : A ≤ H)
    (hψ : NatCoordsSU4 H n F ε ψ) (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (w : W) :
    w ∈ fixV A ↔ Multiplicative.toAdd (ψ w) ∈ fixSp (coordsE (ε := ε) hAH hS) := by
  let f : ↥A →* ↥(SUid σ 4) :=
    (coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)
  have hE : coordsE (ε := ε) hAH hS = f.range := rfl
  rw [hE]
  constructor
  · intro hw
    rw [mem_fixSp]
    intro z hz
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hz
    change (coordsEps (ε := ε) hS (Subgroup.inclusion hAH a) : SUid σ 4) •
      Multiplicative.toAdd (ψ w) = Multiplicative.toAdd (ψ w)
    rw [← coords_psi_smul hψ hS (Subgroup.inclusion hAH a) w]
    have h4 : ((Subgroup.inclusion hAH a : ↥H) : MulAut W) w = (a : MulAut W) w := rfl
    rw [h4, hw (a : MulAut W) a.2]
  · intro hw
    rw [mem_fixV]
    intro a ha
    have h := mem_fixSp.mp hw (f ⟨a, ha⟩) (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
    have h2 := coords_psi_smul (H := H) (ε := ε) (ψ := ψ) hψ hS
      (Subgroup.inclusion hAH ⟨a, ha⟩) w
    have h4 : ((Subgroup.inclusion hAH ⟨a, ha⟩ : ↥H) : MulAut W) w = a w := rfl
    rw [h4] at h2
    have h5 : Multiplicative.toAdd (ψ (a w)) = Multiplicative.toAdd (ψ w) := h2.trans h
    exact ψ.injective (Multiplicative.toAdd.injective h5)

theorem mem_commV_coords {A : Subgroup (MulAut W)} (hAH : A ≤ H)
    (hψ : NatCoordsSU4 H n F ε ψ) (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) (w : W) :
    w ∈ commV A ↔ Multiplicative.toAdd (ψ w) ∈ commSp (coordsE (ε := ε) hAH hS) := by
  let e : W → (Fin 4 → F) := fun w => Multiplicative.toAdd (ψ w)
  let f : ↥A →* ↥(SUid σ 4) :=
    (coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)
  have hE : coordsE (ε := ε) hAH hS = f.range := rfl
  have e_add : ∀ a b : W, e (a * b) = e a + e b := fun a b => by simp [e, toAdd_mul]
  have e_inv : ∀ a : W, e a⁻¹ = - e a := fun a => by simp [e]
  have e_one : e 1 = 0 := by simp [e]
  let T : Set (Fin 4 → F) := {y | ∃ z ∈ f.range, ∃ x : Fin 4 → F, y = z • x - x}
  have hcommSp : commSp f.range = Submodule.span F T := rfl
  have hgen : ∀ y ∈ ({w | ∃ x ∈ A, ∃ v : W, x v * v⁻¹ = w} : Set W), e y ∈ Submodule.span F T := by
    rintro y ⟨x, hx, v, rfl⟩
    have hcomp : e (x v * v⁻¹) = f ⟨x, hx⟩ • e v - e v := by
      rw [e_add, e_inv]
      have h2 : e (x v) = f ⟨x, hx⟩ • e v := by
        have h3 := coords_psi_smul (H := H) (ε := ε) (ψ := ψ) hψ hS
          (Subgroup.inclusion hAH ⟨x, hx⟩) v
        have h4 : ((Subgroup.inclusion hAH ⟨x, hx⟩ : ↥H) : MulAut W) v = x v := rfl
        rw [h4] at h3
        exact h3
      rw [h2, sub_eq_add_neg]
    rw [hcomp]
    exact Submodule.subset_span ⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, e v, rfl⟩
  have hfwd : ∀ y ∈ Subgroup.closure ({w | ∃ x ∈ A, ∃ v : W, x v * v⁻¹ = w} : Set W),
      e y ∈ Submodule.span F T := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact hgen z hz
    | one => rw [e_one]; exact Submodule.zero_mem _
    | mul a b ha hb iha ihb => rw [e_add]; exact Submodule.add_mem _ iha ihb
    | inv a ha iha => rw [e_inv]; exact Submodule.neg_mem _ iha
  have hclosure_smul : ∀ (c : F) (m : Fin 4 → F), m ∈ AddSubgroup.closure T →
      c • m ∈ AddSubgroup.closure T := by
    intro c m hm
    induction hm using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨z0, hz0, x, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨z0, hz0, c • x, by rw [smul_sub, smul_comm]⟩
    | zero => simpa using AddSubgroup.zero_mem _
    | add a b ha hb iha ihb => rw [smul_add]; exact AddSubgroup.add_mem _ iha ihb
    | neg a ha iha => rw [smul_neg]; exact AddSubgroup.neg_mem _ iha
  let Smod : Submodule F (Fin 4 → F) :=
    { carrier := AddSubgroup.closure T
      add_mem' := fun hx hy => AddSubgroup.add_mem _ hx hy
      zero_mem' := AddSubgroup.zero_mem _
      smul_mem' := fun c x hx => hclosure_smul c x hx }
  have hspan_le : Submodule.span F T ≤ Smod :=
    Submodule.span_le.mpr (fun y hy => AddSubgroup.subset_closure hy)
  have hTmem : ∀ y ∈ T, ψ.symm (Multiplicative.ofAdd y) ∈ commV A := by
    rintro y ⟨z, hz, x, rfl⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hz
    have hcomp : ψ.symm (Multiplicative.ofAdd (f a • x - x)) =
        (a : MulAut W) (ψ.symm (Multiplicative.ofAdd x)) *
          (ψ.symm (Multiplicative.ofAdd x))⁻¹ := by
      apply ψ.injective
      rw [map_mul, map_inv]
      have h1 : ψ ((a : MulAut W) (ψ.symm (Multiplicative.ofAdd x))) =
          Multiplicative.ofAdd (f a • x) := by
        have h2 := coords_psi_smul (H := H) (ε := ε) (ψ := ψ) hψ hS
          (Subgroup.inclusion hAH a) (ψ.symm (Multiplicative.ofAdd x))
        have h4 : ((Subgroup.inclusion hAH a : ↥H) : MulAut W) (ψ.symm (Multiplicative.ofAdd x))
            = (a : MulAut W) (ψ.symm (Multiplicative.ofAdd x)) := rfl
        rw [h4] at h2
        have h2' : Multiplicative.toAdd (ψ ((a : MulAut W)
            (ψ.symm (Multiplicative.ofAdd x)))) = f a • x := by
          rw [h2]
          simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
          rfl
        simpa using congrArg Multiplicative.ofAdd h2'
      rw [h1]
      simp [map_sub, toAdd_mul, div_eq_mul_inv]
    rw [hcomp]
    exact Subgroup.subset_closure ⟨(a : MulAut W), a.2, ψ.symm (Multiplicative.ofAdd x), rfl⟩
  have hbwd : ∀ y ∈ AddSubgroup.closure T, ψ.symm (Multiplicative.ofAdd y) ∈ commV A := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz => exact hTmem z hz
    | zero => simpa using (commV A).one_mem
    | add a b ha hb iha ihb =>
      have h : ψ.symm (Multiplicative.ofAdd (a + b)) =
          ψ.symm (Multiplicative.ofAdd a) * ψ.symm (Multiplicative.ofAdd b) := by
        simp [map_add]
      rw [h]; exact (commV A).mul_mem iha ihb
    | neg a ha iha =>
      have h : ψ.symm (Multiplicative.ofAdd (-a)) = (ψ.symm (Multiplicative.ofAdd a))⁻¹ := by
        simp
      rw [h]; exact (commV A).inv_mem iha
  rw [hE]
  constructor
  · intro hw
    rw [hcommSp]
    exact hfwd w hw
  · intro hw
    rw [hcommSp] at hw
    have hcl : e w ∈ AddSubgroup.closure T := hspan_le hw
    have hmem := hbwd (e w) hcl
    simpa [e] using hmem

theorem card_fixV_coords {A : Subgroup (MulAut W)} (hAH : A ≤ H)
    (hψ : NatCoordsSU4 H n F ε ψ) (hS : SUid σ 4 = StatedSU 4 (2 ^ n) F) :
    Nat.card ↥(fixV A) = Nat.card ↥(fixSp (coordsE (ε := ε) hAH hS)) := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨Multiplicative.toAdd (ψ x.1),
        (mem_fixV_coords hAH hψ hS x.1).mp x.2⟩
      invFun := fun y => ⟨ψ.symm (Multiplicative.ofAdd y.1), by
        refine (mem_fixV_coords hAH hψ hS _).mpr ?_
        simpa using y.2⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun y => by apply Subtype.ext; simp }

end Coords

theorem k_18_21_Q_unipotent_holds :
    ∀ {W : Type} [CommGroup W] [Finite W] (H A : Subgroup (MulAut W)) (n : ℕ),
      IsSUn ↥H 4 n → NatSUn H ⊤ ⊥ 4 n →
      A ≤ H → IsElemAbelian2 A → 2 * n ≤ rk ↥A →
      (∀ (F : Type) [Field F] [Finite F] (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
        (ψ : W ≃* Multiplicative (Fin 4 → F)),
        Nat.card F = (2 ^ n) ^ 2 → NatCoordsSU4 H n F ε ψ →
        (∀ w ∈ commV A, (∑ i, (Multiplicative.toAdd (ψ w)) i ^ (2 ^ n + 1)) = 0) →
        fixV A = commV A ∧ rk ↥(fixV A) = 4 * n ∧
          ∃ (N B : Subgroup (MulAut W)),
            A ≤ N ∧ N ≤ H ∧ IsElemAbelian2 N ∧ rk ↥N = 4 * n ∧ B ≤ N ∧ rk ↥B = n ∧
              rk ↥(fixV B) = 6 * n ∧ (∀ x ∈ N, (x ∈ B ↔ ∀ z ∈ fixV B, x z = z))) := by
  intro W _ _ H A n _hSUn _hNat hAH hAel hArk F _ _ ε ψ hF hψ hsing
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  set σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := hσdef.symm ▸ isUnitaryInvolution_unitaryInvolution hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hS : SUid σ 4 = StatedSU 4 (2 ^ n) F := by
    rw [hσdef]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hσpow : ∀ c : F, σ c = c ^ (2 ^ n) := fun c => by
    rw [hσdef, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  let f : ↥A →* ↥(SUid σ 4) :=
    (coordsEps (ε := ε) hS).toMonoidHom.comp (Subgroup.inclusion hAH)
  let E : Subgroup (SUid σ 4) := f.range
  have hEeq : E = coordsE (ε := ε) hAH hS := rfl
  have hfinj : Function.Injective f :=
    (coordsEps (ε := ε) hS).injective.comp (Subgroup.inclusion_injective hAH)
  have hEcardA : Nat.card ↥E = Nat.card ↥A :=
    (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hE2 : ∀ a ∈ E, a * a = 1 := by
    rintro x ⟨a, rfl⟩
    rw [← map_mul]
    have ha : a * a = 1 := by
      apply Subtype.ext
      show (a : MulAut W) * (a : MulAut W) = 1
      simpa [pow_two] using hAel.2 a.1 a.2
    rw [ha, map_one]
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    have hab : a * b = b * a := by
      apply Subtype.ext
      exact hAel.1 a.1 a.2 b.1 b.2
    rw [hab]
  have hAcard : Nat.card ↥A = 2 ^ rk ↥A := by
    have hV : ∀ v : ↥A, v ^ 2 = 1 := fun v => Subtype.ext (hAel.2 v.1 v.2)
    exact card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    rw [h0] at hF
    simp at hF
    have hlt := Finite.one_lt_card (α := F)
    omega
  have hEcard : 2 ^ (2 * n) ≤ Nat.card ↥E := by
    rw [hEcardA, hAcard]
    exact Nat.pow_le_pow_right (by norm_num) hArk
  have hts : ∀ u ∈ commSp E, herm σ u u = 0 := by
    intro u hu
    have hmem : ψ.symm (Multiplicative.ofAdd u) ∈ commV A := by
      rw [hEeq] at hu
      exact (mem_commV_coords hAH hψ hS _).mpr (by simpa using hu)
    have hs := hsing _ hmem
    have htoAdd : Multiplicative.toAdd (ψ (ψ.symm (Multiplicative.ofAdd u))) = u := by simp
    rw [htoAdd] at hs
    rw [herm_def]
    calc ∑ i, σ (u i) * u i = ∑ i, u i ^ (2 ^ n) * u i := by
          refine Finset.sum_congr rfl fun i _ => by rw [hσpow]
      _ = ∑ i, u i ^ (2 ^ n + 1) := by
          refine Finset.sum_congr rfl fun i _ => by rw [pow_succ]
      _ = 0 := hs
  obtain ⟨heq, hcardcomm⟩ := ts_plane_model hσ h2 hE2 hEc hn1 hF hEcard hts
  have heqC : commSp (coordsE (ε := ε) hAH hS) = fixSp (coordsE (ε := ε) hAH hS) := by
    rw [← hEeq]; exact heq
  have hcardcomm' : Nat.card ↥(commSp (coordsE (ε := ε) hAH hS)) = 2 ^ (4 * n) := by
    rw [← hEeq]; exact hcardcomm
  have hfin : Module.finrank F ↥(commSp E) = 2 := by
    have hcard : Nat.card ↥(commSp E) = Nat.card F ^ Module.finrank F ↥(commSp E) :=
      Module.natCard_eq_pow_finrank
    have hFp : Nat.card F = 2 ^ (2 * n) := by rw [hF]; ring
    rw [hcardcomm, hFp, ← pow_mul] at hcard
    have hexp : 4 * n = 2 * n * Module.finrank F ↥(commSp E) :=
      Nat.pow_right_injective (by norm_num) hcard
    have hnpos : 0 < n := by omega
    have h2n : 2 * n * 2 = 2 * n * Module.finrank F ↥(commSp E) := by
      rw [← hexp]; ring
    exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by norm_num) hnpos) h2n).symm
  have htisot : ∀ x ∈ commSp E, ∀ y ∈ commSp E, herm σ x y = 0 := by
    intro x hx y hy
    have hxorth : x ∈ horth σ (commSp E) := by
      rw [← fixSp_eq_horth hσ hE2, ← heq]; exact hx
    have h0 : herm σ y x = 0 := mem_horth.mp hxorth y hy
    rw [herm_conj σ hσ.invol y x, h0, map_zero]
  have hmax : ∀ x, (∀ y ∈ commSp E, herm σ x y = 0) → x ∈ commSp E := by
    intro x hx
    have hx' : ∀ y ∈ commSp E, herm σ y x = 0 := by
      intro y hy
      rw [herm_conj σ hσ.invol x y, hx y hy, map_zero]
    have hmem : x ∈ fixSp E := by
      rw [fixSp_eq_horth hσ hE2]
      exact mem_horth.mpr hx'
    rwa [heq]
  let N : Subgroup (SUid σ 4) := PW (σ := σ) (commSp E)
  have hNcard : Nat.card ↥N = 2 ^ (4 * n) :=
    card_PW_eq_two_pow_four_mul hσ h2 hF hfin htisot hmax
  have hN2 : ∀ a ∈ N, a * a = 1 := fun a ha => PW_sq h2 ha
  have hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb => PW_comm ha hb
  have hEN : E ≤ N := by
    intro a ha
    change a ∈ PW (σ := σ) (commSp E)
    rw [mem_PW]
    refine ⟨fun x => sub_mem_commSp ha x, fun w hw => ?_⟩
    rw [hEeq] at hw
    exact mem_fixSp.mp (heq ▸ hw) a ha
  obtain ⟨B₁, _B₂, hB₁N, _hB₂N, hB₁card, _hB₂card, hB₁mem, _hB₂mem, hfixB₁, _hfixB₂,
    _hsupB⟩ :=
    s16_C4ModelTv_two_root_groups hσ h2 hN2 hNc hn1 hF hNcard
  have hNsq : ∀ a ∈ N, a ^ 2 = 1 := fun a ha => by simpa [pow_two] using hN2 a ha
  let fH : ↥(SUid σ 4) →* MulAut W :=
    H.subtype.comp (coordsEps (ε := ε) hS).symm.toMonoidHom
  let Nw : Subgroup (MulAut W) := N.map fH
  let Bw : Subgroup (MulAut W) := B₁.map fH
  have hfH : Function.Injective fH :=
    H.subtype_injective.comp (coordsEps (ε := ε) hS).symm.injective
  have hmap_mem : ∀ (S : Subgroup (SUid σ 4)) (x : MulAut W), x ∈ S.map fH ↔
      ∃ hx : x ∈ H, coordsEps (ε := ε) hS ⟨x, hx⟩ ∈ S := by
    intro S x
    constructor
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
      have hxH : x ∈ H := by
        rw [← hzx]
        exact ((coordsEps (ε := ε) hS).symm z).2
      refine ⟨hxH, ?_⟩
      have hsub : coordsEps (ε := ε) hS ⟨x, hxH⟩ = z := by
        have hsub' : (⟨x, hxH⟩ : ↥H) = (coordsEps (ε := ε) hS).symm z := by
          apply Subtype.ext
          show x = ((coordsEps (ε := ε) hS).symm z : MulAut W)
          exact hzx.symm
        calc coordsEps (ε := ε) hS ⟨x, hxH⟩
            = coordsEps (ε := ε) hS ((coordsEps (ε := ε) hS).symm z) :=
              congrArg (coordsEps (ε := ε) hS) hsub'
          _ = z := by simp
      rwa [hsub]
    · rintro ⟨hx, hxN⟩
      refine Subgroup.mem_map.mpr ⟨coordsEps (ε := ε) hS ⟨x, hx⟩, hxN, ?_⟩
      show H.subtype ((coordsEps (ε := ε) hS).symm (coordsEps (ε := ε) hS ⟨x, hx⟩)) = x
      simp
  have hNw_mem : ∀ x : MulAut W, x ∈ Nw ↔ ∃ hx : x ∈ H,
      coordsEps (ε := ε) hS ⟨x, hx⟩ ∈ N := hmap_mem N
  have hBw_mem : ∀ x : MulAut W, x ∈ Bw ↔ ∃ hx : x ∈ H,
      coordsEps (ε := ε) hS ⟨x, hx⟩ ∈ B₁ := hmap_mem B₁
  have hNwH : Nw ≤ H := by
    rintro x ⟨z, hz, rfl⟩
    exact ((coordsEps (ε := ε) hS).symm z).2
  have hBwH : Bw ≤ H := by
    rintro x ⟨z, hz, rfl⟩
    exact ((coordsEps (ε := ε) hS).symm z).2
  have hANw : A ≤ Nw := by
    intro a ha
    refine (hNw_mem a).mpr ⟨hAH ha, ?_⟩
    exact hEN (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
  have hBwNw : Bw ≤ Nw := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨z, hB₁N hz, hzx⟩
  have hNw_card : Nat.card ↥Nw = Nat.card ↥N :=
    Subgroup.card_map_of_injective hfH
  have hNw_rk : rk ↥Nw = 4 * n := by
    rw [rk, hNw_card, hNcard, padicValNat.prime_pow]
  have hNw_el : IsElemAbelian2 Nw := by
    constructor
    · intro x hx y hy
      obtain ⟨hxH, hxN⟩ := (hNw_mem x).mp hx
      obtain ⟨hyH, hyN⟩ := (hNw_mem y).mp hy
      have hcomm := hNc (coordsEps (ε := ε) hS ⟨x, hxH⟩) hxN
        (coordsEps (ε := ε) hS ⟨y, hyH⟩) hyN
      rw [← map_mul, ← map_mul] at hcomm
      have h1 : (⟨x, hxH⟩ : ↥H) * ⟨y, hyH⟩ = ⟨y, hyH⟩ * ⟨x, hxH⟩ :=
        (coordsEps (ε := ε) hS).injective hcomm
      simpa using congrArg H.subtype h1
    · intro x hx
      obtain ⟨hxH, hxN⟩ := (hNw_mem x).mp hx
      have h1 : (coordsEps (ε := ε) hS ⟨x, hxH⟩) ^ 2 = 1 := hNsq _ hxN
      have h2 : (⟨x, hxH⟩ : ↥H) ^ 2 = 1 := by
        apply (coordsEps (ε := ε) hS).injective
        rw [map_pow, h1, map_one]
      simpa using congrArg H.subtype h2
  have hBw_card : Nat.card ↥Bw = 2 ^ n := by
    rw [show Bw = B₁.map fH from rfl, Subgroup.card_map_of_injective hfH, hB₁card]
  have hBw_rk : rk ↥Bw = n := by
    rw [rk, hBw_card, padicValNat.prime_pow]
  have hB₁eq : coordsE (ε := ε) hBwH hS = B₁ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z0, hz0, hz0x⟩ := Subgroup.mem_map.mp y.2
      have hys : (Subgroup.inclusion hBwH y : ↥H) = (coordsEps (ε := ε) hS).symm z0 := by
        apply Subtype.ext
        rw [Subgroup.coe_inclusion]
        change (y : MulAut W) = ((coordsEps (ε := ε) hS).symm z0 : MulAut W)
        rw [← hz0x]
        rfl
      change coordsEps (ε := ε) hS (Subgroup.inclusion hBwH y) ∈ B₁
      rw [hys]
      simpa using hz0
    · intro hz
      let y0 : ↥Bw := ⟨fH z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩⟩
      refine MonoidHom.mem_range.mpr ⟨y0, ?_⟩
      have hys : (Subgroup.inclusion hBwH y0 : ↥H) = (coordsEps (ε := ε) hS).symm z := by
        apply Subtype.ext
        rfl
      change coordsEps (ε := ε) hS (Subgroup.inclusion hBwH y0) = z
      rw [hys]
      simp
  have hfixBw : ∀ w : W, w ∈ fixV Bw ↔ Multiplicative.toAdd (ψ w) ∈ fixSp B₁ := by
    intro w
    rw [← hB₁eq]
    exact mem_fixV_coords hBwH hψ hS w
  have hchar : ∀ x ∈ Nw, (x ∈ Bw ↔ ∀ z ∈ fixV Bw, x z = z) := by
    intro x hxNw
    obtain ⟨hxH, hxN⟩ := (hNw_mem x).mp hxNw
    have hmem := hB₁mem (coordsEps (ε := ε) hS ⟨x, hxH⟩)
    constructor
    · intro hxB
      have hxB₁ : coordsEps (ε := ε) hS ⟨x, hxH⟩ ∈ B₁ := (hBw_mem x).mp hxB |>.2
      rw [hmem] at hxB₁
      intro z hz
      have hz1 : Multiplicative.toAdd (ψ z) ∈ fixSp B₁ := (hfixBw z).mp hz
      have hzz := hxB₁.2 _ hz1
      have h7 := coords_psi_smul (H := H) (ε := ε) (ψ := ψ) hψ hS ⟨x, hxH⟩ z
      rw [hzz] at h7
      exact ψ.injective (Multiplicative.toAdd.injective h7)
    · intro hxz
      rw [hBw_mem x]
      refine ⟨hxH, ?_⟩
      rw [hmem]
      refine ⟨hxN, fun u hu => ?_⟩
      have hz : ψ.symm (Multiplicative.ofAdd u) ∈ fixV Bw := (hfixBw _).mpr (by simpa using hu)
      have h := hxz _ hz
      have h7 := coords_psi_smul (H := H) (ε := ε) (ψ := ψ) hψ hS ⟨x, hxH⟩
        (ψ.symm (Multiplicative.ofAdd u))
      have h7' : Multiplicative.toAdd (ψ (ψ.symm (Multiplicative.ofAdd u))) =
          (coordsEps (ε := ε) hS ⟨x, hxH⟩) •
            Multiplicative.toAdd (ψ (ψ.symm (Multiplicative.ofAdd u))) := by
        have h8 : ((↑⟨x, hxH⟩ : ↥H) : MulAut W) (ψ.symm (Multiplicative.ofAdd u)) =
            ψ.symm (Multiplicative.ofAdd u) := h
        rw [← h7, h8]
      simpa using h7'.symm
  refine ⟨?_, ?_, Nw, Bw, hANw, hNwH, hNw_el, hNw_rk, hBwNw, hBw_rk, ?_, hchar⟩
  · ext w
    rw [mem_fixV_coords hAH hψ hS w, mem_commV_coords hAH hψ hS w, heqC]
  · have hcard : Nat.card ↥(fixV A) = 2 ^ (4 * n) := by
      rw [card_fixV_coords hAH hψ hS, ← heqC, hcardcomm']
    rw [rk, hcard, padicValNat.prime_pow]
  · have hcard : Nat.card ↥(fixV Bw) = 2 ^ (6 * n) := by
      rw [card_fixV_coords hBwH hψ hS, hB₁eq, hfixB₁]
    rw [rk, hcard, padicValNat.prime_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
