module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestLin
public import CFSG.LocalAnalysis.StandardType.GGQ2S08T4
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailGlue

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

@[expose] noncomputable def ggQ2CellLin (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) : MulAut ↥Bs →* (Vn n ≃ₗ[ZMod 3] Vn n) :=
  (ggLinConj κ).toMonoidHom.comp (ggLin (p := 3) M.model)

theorem ggQ2CellLin_apply (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (κ : M.V ≃ₗ[ZMod 3] Vn n)
    (φ : MulAut ↥Bs) (v : Vn n) : ggQ2CellLin M κ φ v = κ (ggLin (p := 3) M.model φ (κ.symm v)) :=
  rfl

theorem ggQ2CellLin_injective (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (κ : M.V ≃ₗ[ZMod 3] Vn n) :
    Function.Injective (ggQ2CellLin M κ) := by
  intro φ ψ h
  apply ggLin_injective (p := 3) M.model
  refine LinearEquiv.ext fun v => ?_
  have := congrArg (fun T : Vn n ≃ₗ[ZMod 3] Vn n => κ.symm (T (κ v))) h
  simpa [ggQ2CellLin_apply] using this

theorem ggQ2Cell_dotProduct_eval {n : ℕ} (F : Vn n →ₗ[ZMod 3] ZMod 3) (v : Vn n) :
    (fun j => F (Pi.single j 1)) ⬝ᵥ v = F v := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Vn n) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem ggQ2Cell_mem_zpowers_of_fixes (M : GGQ2LDatum 3 Bs L x) (φ : MulAut ↥Bs)
    (h : ggLin (p := 3) M.model φ M.xV = M.xV ∨ ggLin (p := 3) M.model φ M.xV = -M.xV) :
    φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
  have hφ : ggLin (p := 3) M.model φ M.xV = M.model (Additive.ofMul (φ ⟨x, M.hx⟩)) :=
    ggLin_apply_ofMul (p := 3) M.model φ _
  rw [hφ] at h
  rcases h with h | h
  · rw [GGQ2LDatum.xV] at h
    rw [Additive.ofMul.injective (M.model.injective h)]
    exact Subgroup.mem_zpowers _
  · rw [GGQ2LDatum.xV, ← map_neg, ← ofMul_inv] at h
    rw [Additive.ofMul.injective (M.model.injective h)]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem ggQ2Cell_isRefl [Finite G] (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (κ : M.V ≃ₗ[ZMod 3] Vn n)
    {φ : MulAut ↥Bs} (hφ : GGIsReflection 3 φ) : IsRefl (ggQ2CellLin M κ φ) := by
  have : Finite M.V := Finite.of_equiv _ M.model.toEquiv
  obtain ⟨w, f, hfw, hlin⟩ := exists_of_ggIsReflection (p := 3) M.model hφ
  have hE : ∀ v, (fun j => f (κ.symm (Pi.single j 1))) ⬝ᵥ v = f (κ.symm v) := fun v =>
    ggQ2Cell_dotProduct_eval (f.comp κ.symm.toLinearMap) v
  refine ⟨κ w, fun j => f (κ.symm (Pi.single j 1)), ?_, fun v => ?_⟩
  · rw [hE, LinearEquiv.symm_apply_apply]
    exact hfw
  · rw [ggQ2CellLin_apply, hlin, map_sub, map_smul, LinearEquiv.apply_symm_apply, hE]
    rfl

theorem ggQ2Cell_mem_zpowers_of_fixesLine (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) {x₀ : Vn n} (hκx : κ M.xV = x₀) {φ : MulAut ↥Bs}
    (h : FixesLine x₀ (ggQ2CellLin M κ φ)) :
    φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
  have hκx' : κ.symm x₀ = M.xV := by rw [← hκx, LinearEquiv.symm_apply_apply]
  apply ggQ2Cell_mem_zpowers_of_fixes M φ
  rcases h with h | h <;> rw [ggQ2CellLin_apply, hκx'] at h
  · left
    exact κ.injective (h.trans hκx.symm)
  · right
    exact κ.injective (h.trans (by rw [map_neg, hκx]; rfl))

@[expose] def ggQ2CellDot {n : ℕ} (a : Vn n) : Vn n →ₗ[ZMod 3] ZMod 3 where
  toFun v := a ⬝ᵥ v
  map_add' v w := dotProduct_add a v w
  map_smul' c v := by
    rw [dotProduct_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]

theorem ggQ2CellDot_apply {n : ℕ} (a v : Vn n) : ggQ2CellDot a v = a ⬝ᵥ v :=
  rfl

theorem ggQ2Cell_isTransvection [Finite G] (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) {φ : MulAut ↥Bs} (h : IsTransv (ggQ2CellLin M κ φ)) :
    GGIsTransvection 3 φ := by
  obtain ⟨c, a, hc, ha, hac, hg⟩ := h
  refine ggIsTransvection_of_apply (p := 3) M.model (w := κ.symm c)
    (f := (ggQ2CellDot a).comp κ.toLinearMap) ?_ ?_ ?_ ?_
  · intro h0
    exact hc (by simpa using congrArg κ h0)
  · intro h0
    apply ha
    funext j
    have := congrArg (fun F : Module.Dual (ZMod 3) M.V => F (κ.symm (Pi.single j 1))) h0
    simpa [ggQ2CellDot_apply, dotProduct_single] using this
  · simpa [ggQ2CellDot_apply] using hac
  · intro v
    have := hg (κ v)
    rw [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply] at this
    have h2 := congrArg κ.symm this
    rw [LinearEquiv.symm_apply_apply, map_add, map_smul, LinearEquiv.symm_apply_apply] at h2
    rw [h2]
    rfl

theorem ggQ2Cell_not_mem_zpowers_of_movesLine {φ : MulAut ↥Bs} (hx : x ∈ Bs)
    (h : GGQ2MovesLine Bs x φ) : φ ⟨x, hx⟩ ∉ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨b, hb, hφb⟩ := h
  intro hφx
  apply hφb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hbk : b = (⟨x, hx⟩ : ↥Bs) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hφx
  rw [hbk, map_zpow, ← hm, ← _root_.zpow_mul, Subgroup.coe_zpow]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m * k, rfl⟩

theorem ggQ2Cell_map_automizer_L (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (κ : M.V ≃ₗ[ZMod 3] Vn n)
    {ι : Type} (e : ι ≃ M.Λ) (S : ι → (Vn n ≃ₗ[ZMod 3] Vn n))
    (hκs : ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v) :
    (ggAutomizer L Bs).map (ggQ2CellLin M κ) = Subgroup.closure (Set.range S) := by
  have hs : ∀ i, ggQ2CellLin M κ (M.simple (e i)) = S i := fun i =>
    LinearEquiv.ext fun v => hκs i v
  rw [M.automizer_L, MonoidHom.map_closure]
  congr 1
  ext T
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨e.symm j, by rw [← hs, Equiv.apply_symm_apply]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨M.simple (e i), ⟨e i, rfl⟩, hs i⟩

variable [Finite G]

theorem ggQ2Cell_hyp (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hΓ : GGQ2GammaX 3 B Bs x L D J)
    (hAJ : ggAutomizer J Bs ≠ ⊥) (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (κ : M.V ≃ₗ[ZMod 3] Vn n)
    {x₀ : Vn n} (hκx : κ M.xV = x₀) {W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)}
    (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = W) :
    TestHyp W x₀ ((ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ))
      ((ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs).map
        (ggQ2CellLin M κ)) := by
  have hLN : L ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    le_trans le_sup_left Subgroup.le_normalizer
  refine ⟨Subgroup.map_mono (ggAutomizer_mono Bs le_top), ?_, ?_, ?_, ?_⟩
  · rw [← hW]
    exact Subgroup.map_mono (ggAutomizer_mono Bs hLN)
  · rintro _ ⟨φ, hφ, rfl⟩ htv
    exact hS.1.2.2.2.1 φ (mem_ggAutomizer_iff.mp hφ) (ggQ2Cell_isTransvection M κ htv)
  · rintro _ ⟨φ, hφ, rfl⟩ hfix w hw
    have hzp := ggQ2Cell_mem_zpowers_of_fixesLine M κ hκx hfix
    have hN := ggQ2_lineStab_normalizes_L hLB hP hS.1 hAJ M.hx hφ hzp
    rw [← hW] at hw ⊢
    obtain ⟨ψ, hψ, rfl⟩ := hw
    have hconj : φ * ψ * φ⁻¹ ∈ ggAutomizer L Bs := (Subgroup.mem_normalizer_iff.mp hN ψ).mp hψ
    exact ⟨_, hconj, by rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨φ, hφ, rfl⟩ hfix
    have hzp := ggQ2Cell_mem_zpowers_of_fixesLine M κ hκx hfix
    obtain ⟨g₀, -, hg₀N, hg₀⟩ := mem_ggAutomizer_iff.mp hφ
    have hx : g₀ * x * g₀⁻¹ ∈ Subgroup.zpowers x := by
      have h1 := hg₀ ⟨x, M.hx⟩
      rw [← h1]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
      rw [← hk]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp⟩
    exact ⟨φ, mem_ggAutomizer_iff.mpr ⟨g₀, hΓ g₀ hg₀N hx, hg₀N, hg₀⟩, rfl⟩

theorem ggQ2Cell_normalizes_of_mem {B D J : Subgroup G} (hΓ : GGQ2GammaX 3 B Bs x L D J)
    (hx : x ∈ Bs) {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ)
    (hφ : φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 3 B x L D J : Set G)) Bs) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  obtain ⟨k, hkG0, hkN, hk⟩ := mem_ggAutomizer_iff.mp hφ
  have hkgN : k⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hInd.1
  have hkgx : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = x := by
    have h1 := hk ⟨x, hx⟩
    have h2 := hInd.2 ⟨x, hx⟩
    rw [h1] at h2
    calc (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k := by group
      _ = k⁻¹ * (k * x * k⁻¹) * k := by rw [← h2]
      _ = x := by group
  have hkg : k⁻¹ * g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    hΓ _ hkgN (by rw [hkgx]; exact Subgroup.mem_zpowers x)
  have hg : g = k * (k⁻¹ * g) := by group
  rw [hg]
  exact Subgroup.mul_mem _ hkG0 hkg

theorem ggQ2s08_cell_of_test (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) {x₀ : Vn n} (hκx : κ M.xV = x₀)
    {W : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = W)
    (htest : ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n), TestHyp W x₀ A Mg →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine x₀ r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine x₀ t → t ∈ Mg)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  classical
  have hΓ : GGQ2GammaX 3 B Bs x L D J := hΓi hS rfl hI1 hCav
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hCav
    exact absurd (Nat.le_of_dvd one_pos hCav) (by norm_num)
  have hH := ggQ2Cell_hyp hLB hP hS hΓ hAJ M κ hκx hW
  by_cases hline : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs)
  · refine hΓ g hInd.1 ?_
    have h1 := hInd.2 ⟨x, M.hx⟩
    rw [← h1]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hline
    rw [← hm]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simp⟩
  obtain ⟨ρ, hρM, hρR, hρx⟩ := ggQ2_exists_movesLine_refl_M hTBN hS hI1
  have hmoves : ∀ ψ : MulAut ↥Bs, ψ ⟨x, M.hx⟩ ∉ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) →
      ¬ FixesLine x₀ (ggQ2CellLin M κ ψ) := fun ψ hψ h =>
    hψ (ggQ2Cell_mem_zpowers_of_fixesLine M κ hκx h)
  have hφA : φ ∈ ggAutomizer ⊤ Bs :=
    mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top _, hInd.1, hInd.2⟩
  obtain ⟨φ', hφ'M, hφ'⟩ := htest _ _ hH _ ⟨ρ, hρM, rfl⟩ (ggQ2Cell_isRefl M κ hρR)
    (hmoves ρ (ggQ2Cell_not_mem_zpowers_of_movesLine M.hx hρx)) _ ⟨φ, hφA, rfl⟩
    (ggQ2Cell_isRefl M κ hRefl) (hmoves φ hline)
  obtain rfl := ggQ2CellLin_injective M κ hφ'
  exact ggQ2Cell_normalizes_of_mem hΓ M.hx hInd hφ'M

theorem ggQ2s08_cell_of_coords (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum 3 Bs L x) {n : ℕ} {ι : Type}
    (e : ι ≃ M.Λ) (S : ι → (Vn n ≃ₗ[ZMod 3] Vn n)) (x₀ : Vn n)
    (hcoords : ∃ κ : M.V ≃ₗ[ZMod 3] Vn n, κ M.xV = x₀ ∧
      ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = S i v)
    (htest : ∀ A Mg : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n),
      TestHyp (Subgroup.closure (Set.range S)) x₀ A Mg →
      ∀ r ∈ Mg, IsRefl r → ¬ FixesLine x₀ r →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine x₀ t → t ∈ Mg)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  obtain ⟨κ, hκx, hκs⟩ := hcoords
  exact ggQ2s08_cell_of_test hLB hP hΓi hTBN hS hI1 hCav M κ hκx
    (ggQ2Cell_map_automizer_L M κ e S hκs) htest g φ hInd hRefl

end CFSG.StandardType

end
