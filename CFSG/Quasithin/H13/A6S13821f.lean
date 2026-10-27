module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S13816a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped IsMulCommutative

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem oTwoRes_solvRad_cases (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) :
    oTwoRes (solvRad H) = ⊥ ∨ (¬ IsHatA6 L ∧ oTwoRes (solvRad H) = S.L1) ∨
      (IsHatA6 L ∧ oTwoRes (solvRad H) = l1plus T L V) := by
  set M := Subgroup.normalizer (L : Set G) with hM
  set R := solvRad H with hR
  set Y := oTwoRes R with hY
  have hLT : S.L1 ⊔ T ≤ H := hH.1.1
  have hHR : H ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H)
  have hRM : R ≤ M := by
    have hsol : Group.IsSolvable ↥(R ⊔ (S.L1 ⊔ T)) :=
      C126.isSolvable_sup_of_le_normalizer' (hLT.trans hHR) (solvRad_isSolvable H)
        (S.isSolvable_L1T h1334 hS)
    have hle : R ⊔ (S.L1 ⊔ T) ≤ S.G1 := sup_le ((solvRad_le H).trans hH.2.1) (hLT.trans hH.2.1)
    exact le_sup_left.trans (h13 G T L V S hS _ le_sup_right hle hsol)
  have hYR : Y ≤ R := oTwoRes_le _
  have hYH : Y ≤ H := hYR.trans (solvRad_le H)
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer hHR
  have hYY : oTwoRes Y = Y := by
    refine le_antisymm (oTwoRes_le _) ?_
    rw [hY, oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
    rw [S.zv, Subgroup.mem_bot] at h1
    exact S.z_ne_one h1
  have hYz : Y ≤ M ⊓ Subgroup.centralizer ({S.z} : Set G) :=
    le_inf (hYR.trans hRM) (hYH.trans hH.2.1)
  have hInH : InH T H := ⟨le_sup_right.trans hLT, hH.1.2⟩
  rcases h139 G T L V H Y S.z S.h13 S.irr S.a6 hInH hH.2.2 hYY hYH hHY hz hzL hYz with
    h | ⟨-, hA6, hhat⟩
  · exact Or.inl h
  · by_cases hh : IsHatA6 L
    · exact Or.inr (Or.inr ⟨hh, hhat hh⟩)
    · exact Or.inr (Or.inl ⟨hh, hA6 (S.nonempty_alt6_of_not_hat hh)⟩)

theorem norm_mem_V1_of_V3 {c : ↥(Subgroup.normalizer (V : Set G))}
    (hc3 : (c : G) ^ 3 = 1) (hρ : S.frame.ρ c = swap 0 1 * swap 1 2)
    (hcV3 : (c : G) ∈ Subgroup.normalizer (S.V3 : Set G)) {v : G} (hv : v ∈ S.V3) :
    v * ((c : G) * v * (c : G)⁻¹) * ((c : G) * ((c : G) * v * (c : G)⁻¹) * (c : G)⁻¹) ∈
      fsuV1 T V := by
  set x : G := (c : G) with hx
  have hconj : ∀ w ∈ S.V3, x * w * x⁻¹ ∈ S.V3 := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hcV3 w).mp hw
  set w := v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) with hw
  have h1 := hconj v hv
  have h2 := hconj _ h1
  have hwV : w ∈ S.V3 := S.V3.mul_mem (S.V3.mul_mem hv h1) h2
  have hxxx : x * x * x = 1 := by rw [← pow_three', hc3]
  have h3 : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = v := by
    calc x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * v * (x * x * x)⁻¹ := by group
      _ = v := by rw [hxxx]; group
  have hcomm : ∀ a ∈ S.V3, ∀ b ∈ S.V3, a * b = b * a := fun a ha b hb => by
    have h := S.frame.ψ.injective (a₁ := ⟨a, S.V3_le_V ha⟩ * ⟨b, S.V3_le_V hb⟩)
      (a₂ := ⟨b, S.V3_le_V hb⟩ * ⟨a, S.V3_le_V ha⟩) (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have hxw : x * w * x⁻¹ = w := by
    have e : x * w * x⁻¹ = (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) *
        (x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹) := by rw [hw]; group
    rw [e, h3, hcomm _ (S.V3.mul_mem h1 h2) v hv, ← mul_assoc]
  exact S.mem_V1_of_c012 hρ hwV (by rw [hxw, mul_inv_cancel]; exact (fsuV1 T V).one_mem)

theorem actH_UH_eq_one_iff (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))] (x : ↥H) :
    actH (hS.hF H hH).toHypF91.H_normalizes_V₁ (le_normalizer_conjClosure S.V3 H) x = 1 ↔
      (x : G) ∈ pCoreOf 2 H := by
  have hF := (hS.hF H hH).toHypF91
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  rw [A6Tv.actH_eq_one_iff hV₁ hIHN (le_normalizer_conjClosure S.V3 H) x,
    hF.pCoreOf_eq_centralizerMod]
  exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩

theorem norm_mem_V1 (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {c : ↥(Subgroup.normalizer (V : Set G))} (hcH : (c : G) ∈ H) (hc3 : (c : G) ^ 3 = 1)
    (hρ : S.frame.ρ c = swap 0 1 * swap 1 2)
    (hcV3 : (c : G) ∈ Subgroup.normalizer (S.V3 : Set G))
    (hconj : ∀ h ∈ H, h * (c : G) * h⁻¹ * (c : G)⁻¹ ∈ pCoreOf 2 H ∨
      h * (c : G) * h⁻¹ * (c : G) ∈ pCoreOf 2 H) :
    ∀ u ∈ conjClosure S.V3 H, u * ((c : G) * u * (c : G)⁻¹) *
      ((c : G) * ((c : G) * u * (c : G)⁻¹) * (c : G)⁻¹) ∈ fsuV1 T V := by
  have hF := (hS.hF H hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hHU := le_normalizer_conjClosure S.V3 H
  have hUN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hV₁V3 : fsuV1 T V ≤ S.V3 := S.V1_le_V2.trans S.V2_le_V3
  set x : G := (c : G) with hxdef
  set Φ := actH hV₁ hHU with hΦ
  have hker : ∀ h : ↥H, Φ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := S.actH_UH_eq_one_iff hS hH
  set xH : ↥H := ⟨x, hcH⟩ with hxH
  set y := Φ xH with hy
  have hy3 : y ^ 3 = 1 := by
    have h1 : xH ^ 3 = 1 := Subtype.ext (by simpa [hxH] using hc3)
    rw [hy, ← map_pow, h1, map_one]
  have hyu : ∀ u (hu : u ∈ conjClosure S.V3 H), y (modMk hUN u hu) =
      modMk hUN (x * u * x⁻¹) ((Subgroup.mem_normalizer_iff.mp (hHU hcH) u).mp hu) :=
    fun u hu => actH_modMk hV₁ hUN hHU xH hu
  have key : ∀ u (hu : u ∈ conjClosure S.V3 H), ∃ hθ, modMk hUN u hu * y (modMk hUN u hu) *
      y (y (modMk hUN u hu)) =
        modMk hUN (u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹)) hθ := by
    intro u hu
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHU hcH) u).mp hu
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHU hcH) _).mp h1
    refine ⟨(conjClosure S.V3 H).mul_mem ((conjClosure S.V3 H).mul_mem hu h1) h2, ?_⟩
    rw [hyu u hu, hyu _ h1]
    apply Subtype.ext
    show secMk _ _ ⟨u, _⟩ * secMk _ _ ⟨x * u * x⁻¹, _⟩ * secMk _ _ ⟨x * (x * u * x⁻¹) * x⁻¹, _⟩ =
      secMk _ _ ⟨u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹), _⟩
    rw [← map_mul, ← map_mul]
    rfl
  let N : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)) :=
    { carrier := {w | w * y w * y (y w) = 1}
      one_mem' := by
        show (1 : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) * y 1 * y (y 1) = 1
        simp only [map_one, mul_one]
      mul_mem' := fun {a b} ha hb => by
        have ha' : a * y a * y (y a) = 1 := ha
        have hb' : b * y b * y (y b) = 1 := hb
        show a * b * y (a * b) * y (y (a * b)) = 1
        rw [map_mul, map_mul, mul_mul_mul_comm a b, mul_mul_mul_comm (a * y a), ha', hb',
          mul_one]
      inv_mem' := fun {a} ha => by
        have ha' : a * y a * y (y a) = 1 := ha
        show a⁻¹ * y a⁻¹ * y (y a⁻¹) = 1
        rw [map_inv, map_inv, ← mul_inv, ← mul_inv, ha', inv_one] }
  have hmemN : ∀ w, w ∈ N ↔ w * y w * y (y w) = 1 := fun w => Iff.rfl
  have hyyy : ∀ w, y (y (y w)) = w := fun w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_three', hy3, MulAut.one_apply]
  have hinv : ∀ h : ↥H, ∀ w ∈ N, Φ h w ∈ N := by
    intro h w hw
    have hw' : w * y w * y (y w) = 1 := hw
    have hyg : ∀ v, y (Φ h v) = Φ h (((Φ h)⁻¹ * y * Φ h) v) := fun v => by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    have hcj : (Φ h)⁻¹ * y * Φ h = Φ (h⁻¹ * xH * h) := by
      rw [map_mul, map_mul, map_inv]
    rw [hmemN, hyg, hyg, hcj, ← map_mul, ← map_mul]
    rcases hconj _ (H.inv_mem h.2) with h1 | h1
    ·
      have h2 : Φ (h⁻¹ * xH * h) = y := by
        have h3 : Φ ((h⁻¹ * xH * h) * xH⁻¹) = 1 := by
          rw [hker]
          simpa [hxH, mul_assoc] using h1
        rw [map_mul, map_inv, mul_inv_eq_one] at h3
        exact h3
      rw [h2, hw', map_one]
    ·
      have h2 : Φ (h⁻¹ * xH * h) = y * y := by
        have h3 : Φ ((h⁻¹ * xH * h) * xH) = 1 := by
          rw [hker]
          simpa [hxH, mul_assoc] using h1
        rw [map_mul, mul_eq_one_iff_eq_inv] at h3
        rw [h3]
        have h4 : y * (y * y) = 1 := by
          rw [← mul_assoc, ← pow_three', hy3]
        exact inv_eq_of_mul_eq_one_right h4
      rw [h2]
      simp only [MulAut.mul_apply]
      rw [hyyy]
      have e3 : w * y (y w) * y w = w * y w * y (y w) := by
        rw [mul_assoc, mul_comm (y (y w)), ← mul_assoc]
      rw [e3, hw', map_one]
  have hVN : subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 ≤ N := by
    intro w hw
    obtain ⟨a, haV, haw⟩ := mem_secImg.mp (show ((w : ↥(tildeOf (fsuV1 T V)
      (conjClosure S.V3 H))) : SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈
      tildeOf (fsuV1 T V) S.V3 from hw)
    have haU : (a : G) ∈ conjClosure S.V3 H := le_conjClosure S.V3 H haV
    have hwa : w = modMk hUN (a : G) haU := Subtype.ext haw.symm
    rw [hmemN, hwa]
    obtain ⟨hθ, he⟩ := key (a : G) haU
    rw [he]
    apply Subtype.ext
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V) (x := ⟨_, hUN hθ⟩)).mpr (S.norm_mem_V1_of_V3 hc3 hρ hcV3 haV)
  have htop := iSup_actH_subM_eq_top hV₁ hUN hHU hV₁V3
  have hNtop : (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) ≤ N := by
    rw [← htop]
    refine iSup₂_le fun m hm => ?_
    obtain ⟨h, -, rfl⟩ := hm
    rintro _ ⟨w, hw, rfl⟩
    exact hinv h w (hVN hw)
  intro u hu
  obtain ⟨hθ, he⟩ := key u hu
  have h1 : modMk hUN u hu ∈ N := hNtop trivial
  rw [hmemN, he] at h1
  exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
    (B := fsuV1 T V) (x := ⟨_, hUN hθ⟩)).mp (congrArg Subtype.val h1)

end Setting4

end CFSG.Quasithin.H13.A6
