module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDispY
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixX
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixXTrans
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeQuot
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseN
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFarSix
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFarSixChart
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBaseLift
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSel
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDel
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixStd
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Raw
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveSix
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorHolds
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6TwE6
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBases

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Weyl

theorem dEvenStab_zero_le_closure_nodes {n : ℕ} (hn : 4 ≤ n) :
    dEvenStab (n + 1) (dBasis (n + 1) 0) ≤ Subgroup.closure
      {w | ∃ t : Fin (n + 1), t ≠ 0 ∧ w = dTau (n + 1) (decide (t.val + 1 = n + 1))
        (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)} := by
  classical
  obtain ⟨e₁, he₁⟩ := dEven_equiv hn
  let φ : (ggCoxeterMatrixD n).Group →* (DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) :=
    (dEvenStab (n + 1) (dBasis (n + 1) 0)).subtype.comp
      ((dLiftEquiv n).toMonoidHom.comp e₁.toMonoidHom)
  have hrange : φ.range = dEvenStab (n + 1) (dBasis (n + 1) 0) := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      exact (dLiftEquiv n (e₁ u)).2
    · intro hw
      obtain ⟨u, hu⟩ := (e₁.trans (dLiftEquiv n)).surjective ⟨w, hw⟩
      exact ⟨u, congrArg Subtype.val hu⟩
  rw [← hrange, MonoidHom.range_eq_map,
    ← (ggCoxeterMatrixD n).toCoxeterSystem.subgroup_closure_range_simple, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  refine ⟨t.succ, Fin.succ_ne_zero t, ?_⟩
  have hφ : φ ((ggCoxeterMatrixD n).toCoxeterSystem.simple t) =
      dLift n ((e₁ ((ggCoxeterMatrixD n).simple t) : dEven n) : DVec n ≃ₗ[ZMod 3] DVec n) := by
    rw [CoxeterMatrix.toCoxeterSystem_simple]
    rfl
  rw [hφ, he₁ t, dLift_dTau n _ (OrthTorus.simpleLo_ne_simpleHi (by omega) t)]
  have hε : decide (t.val + 1 = n) = decide (t.succ.val + 1 = n + 1) := by
    simp [Fin.val_succ]
  have hlo : (OrthTorus.simpleLo t).succ = OrthTorus.simpleLo t.succ := by
    ext
    simp only [OrthTorus.simpleLo, Fin.val_succ]
    split_ifs <;> omega
  have hhi : (OrthTorus.simpleHi t).succ = OrthTorus.simpleHi t.succ := by
    ext
    simp only [OrthTorus.simpleHi, Fin.val_succ]
    split_ifs <;> omega
  rw [hε, hlo, hhi]

theorem eq_smul_single_of_dEvenStab_fix {j : Fin 6} {v : DVec 6}
    (hv : ∀ w ∈ dEvenStab 6 (Pi.single j 1), w v = v) : v = v j • Pi.single j 1 := by
  classical
  funext k
  by_cases hk : k = j
  · subst hk
    simp
  · have key : ∀ j k : Fin 6, k ≠ j → ∃ l : Fin 6, l ≠ j ∧ l ≠ k := by decide
    obtain ⟨l, hlj, hlk⟩ := key j k hk
    have hmem : dSign 6 k l ∈ dEvenStab 6 (Pi.single j 1) := by
      refine ⟨dSign_mem_dEven (Ne.symm hlk), ?_⟩
      funext i
      rw [dSign_apply_vec]
      by_cases hi : i = k ∨ i = l
      · rw [if_pos hi]
        have hij : i ≠ j := by
          rcases hi with rfl | rfl
          · exact hk
          · exact hlj
        simp [Pi.single_apply, hij]
      · rw [if_neg hi]
    have h1 := congrFun (hv _ hmem) k
    rw [dSign_apply_vec, if_pos (Or.inl rfl)] at h1
    have h0 : v k = 0 := (by decide : ∀ x : ZMod 3, -x = x → x = 0) _ h1
    simp [h0, Pi.single_apply, hk]

variable {G : Type} [Group G] [Finite G]

theorem qtwoFar_dEvenStab_le_of_frame {L Bs X : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {n : ℕ} (hn : 4 ≤ n)
    {e' : Fin (n + 1) ≃ ι} (hM : M = (ggCoxeterMatrixD (n + 1)).reindex e')
    (β : Additive ↥Bs ≃+ DVec (n + 1))
    (hβ : ∀ (t : Fin (n + 1)) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
        dTau (n + 1) (decide (t.val + 1 = n + 1)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    (hframe : QTwoFrameAt Bs X M (ggAutomizerJoin L Bs 𝒦) e e') :
    ∃ j : Fin (n + 1), dEvenStab (n + 1) (Pi.single j 1) ≤
      (ggAutomizer X Bs).map (ggLin (p := 3) β) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w₀, hw₀⟩ := hframe
  set W₀ := ggLin (p := 3) β ((e w₀ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) with hW₀
  have hW₀mem : W₀ ∈ dEven (n + 1) := by
    rw [← qtwoD_image_eq (by omega) hM β hβ]
    exact ⟨_, (e w₀).2, rfl⟩
  have hdt : ∀ t : Fin (n + 1),
      ggLin (p := 3) β ((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        dTau (n + 1) (decide (t.val + 1 = n + 1)) (OrthTorus.simpleLo t)
          (OrthTorus.simpleHi t) := by
    intro t
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨s, rfl⟩ : ∃ s : ↥Bs, β (Additive.ofMul s) = v :=
      ⟨Additive.toMul (β.symm v), by simp⟩
    rw [ggLin_apply_ofMul]
    exact hβ t s
  set H := (ggAutomizer X Bs).map (ggLin (p := 3) β) with hH
  have hcl : Subgroup.closure
      {w | ∃ t : Fin (n + 1), t ≠ 0 ∧ w = dTau (n + 1) (decide (t.val + 1 = n + 1))
        (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)} ≤
      H.map (MulAut.conj W₀⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨W₀ * dTau (n + 1) (decide (t.val + 1 = n + 1)) (OrthTorus.simpleLo t)
      (OrthTorus.simpleHi t) * W₀⁻¹, ⟨_, hw₀ t (fun h => ht (Fin.ext h)), ?_⟩, ?_⟩
    · simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hdt t, ← hW₀]
    · simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨σ, c, hc, -, hact⟩ := id hW₀mem
  refine ⟨σ 0, fun w hw => ?_⟩
  have hw2 : w (dBasis (n + 1) (σ 0)) = dBasis (n + 1) (σ 0) := by
    simpa [dBasis, Pi.basisFun_apply] using hw.2
  have hconj : W₀⁻¹ * w * W₀ ∈ dEvenStab (n + 1) (dBasis (n + 1) 0) := by
    refine ⟨mul_mem (mul_mem (inv_mem hW₀mem) hw.1) hW₀mem, ?_⟩
    change W₀⁻¹ (w (W₀ (dBasis (n + 1) 0))) = dBasis (n + 1) 0
    rw [hact 0, map_smul, hw2, ← hact 0, ← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  obtain ⟨h, hh, hhw⟩ := hcl (dEvenStab_zero_le_closure_nodes hn hconj)
  have hhw' : W₀⁻¹ * h * W₀ = W₀⁻¹ * w * W₀ := by
    simpa [MulAut.conj_apply] using hhw
  rw [← mul_left_cancel (mul_right_cancel hhw')]
  exact hh

theorem qtwoFarUnit_le_centralizer {Bs Y J₁ : Subgroup G} (Φ : OrthTorus.OrthFrameCore 3 Bs Y)
    (hΦr : Φ.r = 5) (hcard : Nat.card ↥Bs = 3 ^ 6) {βL : Additive ↥Bs ≃+ DVec 6} {a c : Fin 6}
    (hac : a ≠ c)
    (hconst : ∀ s : ↥Bs, (s : G) ∈ Subgroup.centralizer (J₁ : Set G) →
      ∀ i ∈ Finset.univ.erase c, ∀ j ∈ Finset.univ.erase c,
        βL (Additive.ofMul s) i = βL (Additive.ofMul s) j)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹)
    (hJ₁Y : J₁ ≤ Y) (hJ₂Y : J₁.map (MulAut.conj g).toMonoidHom ≤ Y)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1) :
    Y ≤ Subgroup.centralizer ({(b' : G)} : Set G) := by
  classical
  obtain ⟨s, hs1, hsβ⟩ : ∃ s : ↥Bs, s ≠ 1 ∧ Φ.β s = 1 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective Φ.β :=
      (injective_iff_map_eq_one Φ.β).mpr fun s hs => by
        by_contra h
        exact hcon s h hs
    have hmemA : ∀ s : ↥Bs, ∃ f, Φ.Δ.τ f = (Φ.β s : Φ.V ≃ₗ[Φ.F] Φ.V) := fun s => by
      have h := Φ.hβA s
      rw [← Φ.Δ.τ_range] at h
      exact MonoidHom.mem_range.mp h
    choose F hFτ using hmemA
    have hF : Function.Injective F := by
      intro s t hst
      apply hinj
      apply Subtype.ext
      rw [← hFτ s, ← hFτ t, hst]
    have hle := Nat.card_le_card_of_injective F hF
    rw [hcard, Nat.card_fun, Nat.card_fin, hΦr] at hle
    have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [h3] at hle
    norm_num at hle
  have hsY : ∀ y ∈ Y, (s : G) * y = y * (s : G) := by
    intro y hy
    rw [← Φ.hrange] at hy
    obtain ⟨z, rfl⟩ := hy
    have h := Φ.hcompat s z
    rw [hsβ, one_mul, inv_one, mul_one] at h
    calc (s : G) * Φ.ψ z = (s : G) * Φ.ψ z * (s : G)⁻¹ * (s : G) := by group
      _ = Φ.ψ z * (s : G) := by rw [← h]
  have hs₁ := hconst s (Subgroup.mem_centralizer_iff.mpr fun j hj => (hsY j (hJ₁Y hj)).symm)
  have hs₂ := hconst (α⁻¹ s) (Subgroup.mem_centralizer_iff.mpr fun j hj => by
    have hgj : g * j * g⁻¹ ∈ Y := hJ₂Y ⟨j, hj, rfl⟩
    have h := hsY _ hgj
    have hαs : ((α (α⁻¹ s) : ↥Bs) : G) = g * ((α⁻¹ s : ↥Bs) : G) * g⁻¹ := hg (α⁻¹ s)
    rw [MulAut.apply_inv_self] at hαs
    have ht : ((α⁻¹ s : ↥Bs) : G) = g⁻¹ * (s : G) * g := by
      rw [hαs]
      group
    rw [ht]
    calc j * (g⁻¹ * (s : G) * g) = g⁻¹ * ((g * j * g⁻¹) * (s : G)) * g := by group
      _ = g⁻¹ * ((s : G) * (g * j * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * (s : G) * g * j := by group)
  have hsα : βL (Additive.ofMul s) = dSign 6 a c (βL (Additive.ofMul (α⁻¹ s))) := by
    rw [← hα, MulAut.apply_inv_self]
  obtain ⟨k, hka, hkc⟩ : ∃ k : Fin 6, k ≠ a ∧ k ≠ c := by
    have key : ∀ a c : Fin 6, ∃ k : Fin 6, k ≠ a ∧ k ≠ c := by decide
    exact key a c
  have hmem : ∀ i, i ≠ c → i ∈ Finset.univ.erase c := fun i hi =>
    Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  have hk0 : βL (Additive.ofMul s) k = 0 := by
    have h1 := hs₁ a (hmem a hac) k (hmem k hkc)
    have h2 := hs₂ a (hmem a hac) k (hmem k hkc)
    have h3 := congrFun hsα a
    have h4 := congrFun hsα k
    rw [dSign_apply_vec, if_pos (Or.inl rfl)] at h3
    rw [dSign_apply_vec, if_neg (by rintro (h | h) <;> contradiction)] at h4
    have h5 : βL (Additive.ofMul s) k = -βL (Additive.ofMul s) k :=
      calc βL (Additive.ofMul s) k = βL (Additive.ofMul s) a := h1.symm
        _ = -βL (Additive.ofMul (α⁻¹ s)) a := h3
        _ = -βL (Additive.ofMul (α⁻¹ s)) k := by rw [h2]
        _ = -βL (Additive.ofMul s) k := by rw [h4]
    exact (by decide : ∀ x : ZMod 3, x = -x → x = 0) _ h5
  have hv : βL (Additive.ofMul s) = βL (Additive.ofMul s) c • Pi.single c 1 := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp
    · rw [hs₁ i (hmem i hi) k (hmem k hkc), hk0]
      simp [Pi.single_apply, hi]
  obtain ⟨μ, hv⟩ : ∃ μ : ZMod 3, βL (Additive.ofMul s) = μ • Pi.single c 1 := ⟨_, hv⟩
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hv
    exact hs1 (Additive.ofMul.injective (βL.injective (by rw [hv, ofMul_one, map_zero])))
  have hb's : b' = s ^ μ.val := by
    apply Additive.ofMul.injective
    apply βL.injective
    rw [ofMul_pow, map_nsmul, hv, hb', ← Nat.cast_smul_eq_nsmul (ZMod 3), smul_smul]
    have key : ∀ x : ZMod 3, x ≠ 0 → (x.val : ZMod 3) * x = 1 := by decide
    rw [key _ hμ, one_smul]
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  rw [hb's, SubmonoidClass.coe_pow]
  exact ((Commute.pow_left (hsY y hy) _)).eq

theorem qtwoFarUnit_hamb {L Bs X Y : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {e' : Fin 6 ≃ ι}
    (hM : M = (ggCoxeterMatrixD 6).reindex e') (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)))
    {j : Fin 6} (hstab : dEvenStab 6 (Pi.single j 1) ≤ (ggAutomizer X Bs).map (ggLin (p := 3) β))
    {b : ↥Bs} (hb : β (Additive.ofMul b) = Pi.single j 1)
    (hYb : Y ≤ Subgroup.centralizer ({(b : G)} : Set G)) (hXY : X ≤ Y)
    (hambX : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer X Bs,
      r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' = ggRankTwoIn X Bs r r') :
    ∀ r ∈ ggAutomizer Y Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer Y Bs,
      r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' = ggRankTwoIn Y Bs r r' := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : ∀ r ∈ ggAutomizer Y Bs, r ∈ ggCoxRefl M e → r ∈ ggAutomizer X Bs := by
    intro r hrY hrC
    obtain ⟨w, i, rfl⟩ := hrC
    have hEven : ggLin (p := 3) β ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) :
        MulAut ↥Bs) ∈ dEven 6 := by
      rw [← qtwoD_image_eq (by norm_num) hM β hβ]
      exact ⟨_, (e (w * M.simple i * w⁻¹)).2, rfl⟩
    obtain ⟨y, hyY, -, hy⟩ := mem_ggAutomizer_iff.mp hrY
    have hfix : ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b := by
      apply Subtype.ext
      rw [hy b]
      have hyb : y * (b : G) = (b : G) * y :=
        (Subgroup.mem_centralizer_iff.mp (hYb hyY) (b : G) rfl).symm
      rw [hyb, mul_inv_cancel_right]
    rw [ggLin_fix_iff (p := 3) β, hb] at hfix
    obtain ⟨r₀, hr₀, hr₀eq⟩ := hstab ⟨hEven, hfix⟩
    rw [← ggLin_injective (p := 3) β hr₀eq]
    exact hr₀
  intro r hr hrC r' hr' hr'C hne
  refine le_antisymm ?_ ?_
  · rw [hambX r (hX r hr hrC) hrC r' (hX r' hr' hr'C) hr'C hne]
    exact Subgroup.closure_mono fun _ hz => ⟨⟨hXY hz.1.1, hz.1.2⟩, hz.2⟩
  · exact Subgroup.closure_mono fun _ hz => ⟨hz.1.2, hz.2⟩

end Weyl

private theorem zmod3_val_mul_self {y : ZMod 3} (hy : y ≠ 0) : (y.val : ZMod 3) * y = 1 := by
  revert y
  decide

section Cfg

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]

theorem qtwoFarUnit_data (hEA : GGQTwoEdgeAmbientInputOn fun m => m = 6) (hLB : GGLBalanceInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e') (hcell : qtwoOrthL.compl G L 𝒦) :
    p = 3 ∧ ∃ (β : Additive ↥Bs ≃+ DVec 6) (i₀ : Fin 6) (b : ↥Bs) (Y : Subgroup G),
      (∀ (t : Fin 6) (s : ↥Bs),
        β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
          dTau 6 (decide (t.val + 1 = 6)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
            (β (Additive.ofMul s))) ∧
      β (Additive.ofMul b) = Pi.single i₀ 1 ∧ Y ≤ Subgroup.centralizer ({(b : G)} : Set G) ∧
      dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer Y Bs).map (ggLin (p := 3) β) ∧
      (∀ r ∈ ggAutomizer Y Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer Y Bs,
        r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' = ggRankTwoIn Y Bs r r') ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = 5 ∧
        Subgroup.center ↥Y = ⊥ := by
  classical
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hmark := ggQTwoDUnit_u62_of_six hRig hTBF hWI hcfg e' hM hcell
  obtain ⟨hp3, K, hKf, hKfin, hKchar, Q, hQ, hQfin, f, ψ, ε, hx, βL, ω, hD, hbase, hω, hxcoord',
    hind, hpermβ, hjoin, hcox, hcoxRoot, hnode⟩ := ggQTwoDUnitSix_coords hTBF hWI hcfg e' hM hmark
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxBs, hxord, hcent⟩ := ggQTwoDUnit_base_cent hcfg rfl
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    have hxC : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hcent]
      exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp hxC).2
  have hxcoord := hxcoord' hxBs
  have hK : Nat.card K = 4 := hbase.card_field
  have hψr : ψ.range = NsQuot.img _ f L := hbase.range
  have hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6) := hbase.hyp.ker
  have hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs := by
    intro σ q hq
    have hmem := ((ε σ).1 ⟨q, hq⟩).2
    rw [hbase.perm σ ⟨q, hq⟩] at hmem
    exact hmem
  have hcard : Nat.card ↥Bs = 3 ^ 6 := (Nat.card_congr hD.tau.toEquiv).trans hbase.card_bs
  have hBBs : B ≤ Bs := hcfg.1.1.1.2.1.1
  obtain ⟨u, v, hshape⟩ : ∃ u v : Fin 6, B = Bs ∨ ∀ s : ↥Bs,
      ((s : G) ∈ B ↔ βL (Additive.ofMul s) u = βL (Additive.ofMul s) v) := by
    rcases ggQTwoDUnitSix_B_shape hTBF hWI hcfg e' hM hmark hD hbase hω hind with h | ⟨u, v, -, h⟩
    · exact ⟨0, 0, Or.inl h⟩
    · exact ⟨u, v, Or.inr h⟩
  obtain ⟨a, c, hac, -, -, -, -, b', hb', hb'B⟩ :=
    ggQTwoDUnitSix_selected_coordinates hBBs hshape
  obtain ⟨J₁, hJ₁L, hJ₁perf, hJ₁, hJ₁Z⟩ := ggQTwoDUnitSix_block hK hD hψr hψk c
  obtain ⟨α, -, hα, g, hgJ, hgN, hg⟩ := ggQTwoDUnitSix_signLift hjoin hac
  obtain ⟨Y, hJ₁Y, hJ₂Y, Φ, hΦF, hΦr, hΦZ⟩ := ggQTwoDUnitSix_orthY hRig hLB hcfg
    hcfg.1.1.2.2.1.1 hcard hK hD hψr hψk hε hxBs hxord hxL hxcoord hω hind hpermβ hjoin hac hJ₁L
    hJ₁Z hJ₁ hα hgN hg hb' hb'B
  have hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G) := by
    have hmem : (b' : G) ∈ Subgroup.closure {x, (b' : G)} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rw [← ggQTwoDUnitSix_cent_J hK hD hψk hxBs hxL hxcoord hω hind hJ₁L hJ₁Z hJ₁ hb'] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  have hXY : J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom ≤ Y := sup_le hJ₁Y hJ₂Y
  have hYb' : Y ≤ Subgroup.centralizer ({(b' : G)} : Set G) :=
    qtwoFarUnit_le_centralizer Φ hΦr hcard hac
      (fun _ hsC => ggQTwoDUnitSix_const_of_mem_centralizer hK hD hψk hω hind hJ₁ hsC) hα hg hJ₁Y
      hJ₂Y hb'
  obtain ⟨β, hβ⟩ := ggQTwoDSelModuleInputOn_of_selectedModule (R := fun m => m = 6)
    (fun m (hm : m = 6) => by omega) hTBF hWI G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM
  obtain ⟨j, hstab⟩ := qtwoFar_dEvenStab_le_of_frame (n := 5) (by norm_num) hM β hβ
    (ggQTwoDUnitSix_X_frame hK hD hψk hε hind hpermβ hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hb' hb'J
      hα hgN hg hjoin hnode)
  have hfix : ∀ w ∈ dEvenStab 6 (Pi.single j 1),
      w (β (Additive.ofMul b')) = β (Additive.ofMul b') := by
    intro w hw
    obtain ⟨φ, hφ, rfl⟩ := hstab hw
    rw [← ggLin_fix_iff]
    obtain ⟨y, hyX, -, hy⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hy b']
    have hyb : y * (b' : G) = (b' : G) * y :=
      (Subgroup.mem_centralizer_iff.mp (hYb' (hXY hyX)) (b' : G) rfl).symm
    rw [hyb, mul_inv_cancel_right]
  obtain ⟨μ, hv⟩ : ∃ μ : ZMod 3, β (Additive.ofMul b') = μ • Pi.single j 1 :=
    ⟨_, eq_smul_single_of_dEvenStab_fix hfix⟩
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hv
    have h1 : b' = 1 := Additive.ofMul.injective (β.injective (by rw [hv, ofMul_one, map_zero]))
    have h2 := congrFun hb' c
    rw [h1, ofMul_one, map_zero] at h2
    simp at h2
  have hb : β (Additive.ofMul (b' ^ μ.val)) = Pi.single j 1 := by
    rw [ofMul_pow, map_nsmul, hv, ← Nat.cast_smul_eq_nsmul (ZMod 3), smul_smul,
      zmod3_val_mul_self hμ, one_smul]
  have hYb : Y ≤ Subgroup.centralizer ({((b' ^ μ.val : ↥Bs) : G)} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [SubmonoidClass.coe_pow]
    exact (Commute.pow_left (Subgroup.mem_centralizer_iff.mp (hYb' hy) (b' : G) rfl) _).eq
  exact ⟨rfl, β, j, b' ^ μ.val, Y, hβ, hb, hYb,
    hstab.trans (Subgroup.map_mono (ggAutomizer_mono Bs hXY)),
    qtwoFarUnit_hamb hM β hβ hstab hb hYb hXY
      (ggQTwoDUnitSix_X_rankTwo hEA hcfg hM hmark hD hbase hω hind hpermβ hxBs hxL hxcoord hjoin
        hcox hcoxRoot hac hJ₁L hJ₁Z hJ₁ hb' hb'J hα hgN hg),
    Φ, hΦF, hΦr, hΦZ⟩

theorem ggQTwoFarInputOn_six_unit (hEA : GGQTwoEdgeAmbientInputOn fun m => m = 6)
    (hLB : GGLBalanceInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hgen : GGQTwoSixPlaneGenInput) :
    GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL.compl := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hc i k j l hik hjl hij hil hkj hkl
  subst hm
  obtain ⟨hp3, β, i₀, b, Y, hβ, hb, hYb, hAe, hamb, Φ, hF, -, hZ⟩ :=
    qtwoFarUnit_data hEA hLB hTBF hWI hcfg e' hM hc
  subst hp3
  have hcoord : qtwoCoord β i₀ = (b : G) := by
    rw [qtwoCoord, ← hb, AddEquiv.symm_apply_apply]
    rfl
  obtain ⟨φ₀, hφ₀, hrange, hrot⟩ := qtwoFarSix_exists_chart_of_frameCore Φ hF hZ β one_ne_zero
    b.2 (by rw [one_smul]; exact hb) hYb hAe
  refine qtwoFarSix_of_chart e' hM β hβ hAe
    (fun r hr hrc r' hr' hr'c hne => (hamb r hr hrc r' hr' hr'c hne).trans_le
      ((ggOTwoPrime_le _).trans inf_le_left)) ?_ φ₀ hφ₀ hrange hrot hgen i k j l hik hjl hij hil
      hkj hkl
  rw [hcoord]
  exact hYb

end Cfg

end CFSG.StandardType.QTwo

end
