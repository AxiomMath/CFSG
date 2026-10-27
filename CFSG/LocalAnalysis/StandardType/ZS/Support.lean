module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.HardMathSupport.Kantor79.CommutatorSpace
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflPair

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

@[expose] def centralizerSpace (H : Subgroup (U ≃ₗ[K] U)) : Submodule K U where
  carrier := {v | ∀ h ∈ H, h v = v}
  add_mem' {u v} hu hv h hh := by rw [map_add, hu h hh, hv h hh]
  zero_mem' h _ := map_zero h
  smul_mem' c v hv h hh := by rw [map_smul, hv h hh]

@[expose] def IrredOnSection (H : Subgroup (U ≃ₗ[K] U)) (W₁ W₂ : Submodule K U) : Prop :=
  ∀ X : Submodule K U, W₁ ≤ X → X ≤ W₂ → (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = W₁ ∨ X = W₂

@[expose] def SplitSupport (H : Subgroup (U ≃ₗ[K] U)) (l : ℕ) : Prop :=
  IsCompl (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H) ∧
    Module.finrank K (HardMathSupport.Kantor79.commutatorSpace H) = l ∧
    IrredOnSection H ⊥ (HardMathSupport.Kantor79.commutatorSpace H)

theorem mem_centralizerSpace {H : Subgroup (U ≃ₗ[K] U)} {v : U} :
    v ∈ centralizerSpace H ↔ ∀ h ∈ H, h v = v :=
  Iff.rfl

private theorem apply_eq_neg_of_mem_movedSpace {t : U ≃ₗ[K] U} (ht : t * t = 1) {x : U}
    (hx : x ∈ HardMathSupport.Kantor79.movedSpace t) : t x = -x := by
  obtain ⟨v, rfl⟩ := hx
  change t (t v - v) = -(t v - v)
  rw [map_sub]
  have htt : t (t v) = v := by
    have h := congrArg (fun e : U ≃ₗ[K] U => e v) ht
    simpa [LinearEquiv.mul_apply] using h
  rw [htt]
  abel

private theorem mem_movedSpace_of_apply_eq_neg {t : U ≃ₗ[K] U} {v : U} (h2 : (2 : K) ≠ 0)
    (ht : t v = -v) : v ∈ HardMathSupport.Kantor79.movedSpace t := by
  refine ⟨-((2 : K)⁻¹) • v, ?_⟩
  change (t : U →ₗ[K] U) (-((2 : K)⁻¹) • v) - (-((2 : K)⁻¹) • v) = v
  rw [map_smul, show (t : U →ₗ[K] U) v = -v from ht]
  have hsum : ((2 : K)⁻¹ + (2 : K)⁻¹) = 1 := by
    rw [← two_mul]
    exact mul_inv_cancel₀ h2
  have h1 : (-((2 : K)⁻¹)) • (-v) = (2 : K)⁻¹ • v := by simp
  have h2 : (-((2 : K)⁻¹)) • v = -((2 : K)⁻¹ • v) := by simp
  rw [h1, h2, sub_neg_eq_add, ← add_smul, hsum, one_smul]

private theorem movedSpace_reflection_le_span {a : U} {φ : Module.Dual K U} (hφ : φ a = 2) :
    HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) ≤ Submodule.span K {a} := by
  rintro w ⟨v, rfl⟩
  change Module.reflection hφ v - v ∈ Submodule.span K {a}
  rw [Module.reflection_apply]
  rw [show v - φ v • a - v = -(φ v • a) by abel]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ (φ v) (Submodule.mem_span_singleton_self a))

private theorem ker_reflection_sub_one {a : U} {φ : Module.Dual K U} (h2 : (2 : K) ≠ 0)
    (hφ : φ a = 2) :
    LinearMap.ker ((Module.reflection hφ : U →ₗ[K] U) - 1) = LinearMap.ker φ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hφ
    exact h2 hφ.symm
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have hval : ((Module.reflection hφ : U →ₗ[K] U) - 1) v = -(φ v • a) := by
    change Module.reflection hφ v - v = -(φ v • a)
    rw [Module.reflection_apply]
    abel
  rw [hval, neg_eq_zero, smul_eq_zero]
  exact ⟨fun h => h.elim id (fun h0 => absurd h0 ha), Or.inl⟩

private theorem map_commutatorSpace_le_of_mem_normalizer {H : Subgroup (U ≃ₗ[K] U)}
    {g : U ≃ₗ[K] U} (hg : g ∈ Subgroup.normalizer (H : Set (U ≃ₗ[K] U))) :
    (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[K] U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨h, hh, v, rfl⟩, rfl⟩
  have hmem : g * h * g⁻¹ ∈ H := (Subgroup.mem_set_normalizer_iff.mp hg h).mp hh
  have hkey : (g : U →ₗ[K] U) (h v - v) = (g * h * g⁻¹) (g v) - g v := by
    rw [map_sub]
    congr 1
    simp [LinearEquiv.mul_apply]
  rw [hkey]
  exact Submodule.subset_span ⟨g * h * g⁻¹, hmem, g v, rfl⟩

private theorem map_centralizerSpace_le_of_mem_normalizer {H : Subgroup (U ≃ₗ[K] U)}
    {g : U ≃ₗ[K] U} (hg : g ∈ Subgroup.normalizer (H : Set (U ≃ₗ[K] U))) :
    (centralizerSpace H).map (g : U →ₗ[K] U) ≤ centralizerSpace H := by
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ∀ h ∈ H, h v = v := (mem_centralizerSpace).mp hv
  refine (mem_centralizerSpace).mpr fun h hh => ?_
  have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set (U ≃ₗ[K] U)) :=
    (Subgroup.normalizer (H : Set (U ≃ₗ[K] U))).inv_mem hg
  have hmem : g⁻¹ * h * g ∈ H := (Subgroup.mem_set_normalizer_iff.mp hg' h).mp hh
  calc h (g v) = g ((g⁻¹ * h * g) v) := by simp [LinearEquiv.mul_apply]
    _ = g v := by rw [hv' _ hmem]

private theorem centralizerSpace_closure_eq_iInf {ι : Type*} (x : ι → U ≃ₗ[K] U) :
    centralizerSpace (Subgroup.closure (Set.range x)) =
      ⨅ i, LinearMap.ker ((x i : U →ₗ[K] U) - 1) := by
  ext v
  rw [mem_centralizerSpace, Submodule.mem_iInf]
  constructor
  · intro h i
    simpa [LinearMap.mem_ker, sub_eq_zero] using h (x i) (Subgroup.subset_closure ⟨i, rfl⟩)
  · intro h
    have hx : ∀ i, x i v = v := fun i => by
      simpa [LinearMap.mem_ker, sub_eq_zero] using h i
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hx i
    | one => rfl
    | mul y z hy hz ihy ihz => rw [LinearEquiv.mul_apply, ihz, ihy]
    | inv y hy ihy =>
      calc y⁻¹ v = y⁻¹ (y v) := by rw [ihy]
        _ = v := by
          change y.symm (y v) = v
          exact LinearEquiv.symm_apply_apply y v

private theorem commutatorSpace_bot :
    HardMathSupport.Kantor79.commutatorSpace (⊥ : Subgroup (U ≃ₗ[K] U)) = ⊥ := by
  rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_eq_bot]
  rintro w ⟨h, hh, v, rfl⟩
  rw [Subgroup.mem_bot.mp hh]
  simp


theorem commutatorSpace_le_iff {H : Subgroup (U ≃ₗ[K] U)} {W : Submodule K U} :
    HardMathSupport.Kantor79.commutatorSpace H ≤ W ↔ ∀ h ∈ H, ∀ v, h v - v ∈ W := by
  constructor
  · intro hle h hh v
    exact hle (Submodule.subset_span ⟨h, hh, v, rfl⟩)
  · intro h
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro w ⟨k, hk, v, rfl⟩
    exact h k hk v

theorem map_eq_self_of_invariant {H : Subgroup (U ≃ₗ[K] U)} {W : Submodule K U}
    (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) {g : U ≃ₗ[K] U} (hg : g ∈ H) :
    W.map (g : U →ₗ[K] U) = W := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw => hW g hg w hw) fun w hw => ?_
  exact ⟨g⁻¹ w, hW g⁻¹ (H.inv_mem hg) w hw, g.apply_symm_apply w⟩

theorem map_commutatorSpace_of_mem_normalizer {H : Subgroup (U ≃ₗ[K] U)} {g : U ≃ₗ[K] U}
    (hg : g ∈ Subgroup.normalizer (H : Set (U ≃ₗ[K] U))) :
    (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[K] U) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  refine le_antisymm (map_commutatorSpace_le_of_mem_normalizer hg) fun w hw => ?_
  refine Submodule.mem_map.mpr ⟨g⁻¹ w,
    map_commutatorSpace_le_of_mem_normalizer
      ((Subgroup.normalizer (H : Set (U ≃ₗ[K] U))).inv_mem hg)
      (Submodule.mem_map_of_mem (f := ((g⁻¹ : U ≃ₗ[K] U) : U →ₗ[K] U)) hw), ?_⟩
  simp

theorem map_centralizerSpace_of_mem_normalizer {H : Subgroup (U ≃ₗ[K] U)} {g : U ≃ₗ[K] U}
    (hg : g ∈ Subgroup.normalizer (H : Set (U ≃ₗ[K] U))) :
    (centralizerSpace H).map (g : U →ₗ[K] U) = centralizerSpace H := by
  refine le_antisymm (map_centralizerSpace_le_of_mem_normalizer hg) fun w hw => ?_
  refine Submodule.mem_map.mpr ⟨g⁻¹ w,
    map_centralizerSpace_le_of_mem_normalizer
      ((Subgroup.normalizer (H : Set (U ≃ₗ[K] U))).inv_mem hg)
      (Submodule.mem_map_of_mem (f := ((g⁻¹ : U ≃ₗ[K] U) : U →ₗ[K] U)) hw), ?_⟩
  simp

theorem apply_eq_self_of_not_movedSpace_le {t : U ≃ₗ[K] U}
    (ht : Module.finrank K (HardMathSupport.Kantor79.movedSpace t) = 1) {W : Submodule K U}
    (hW : ∀ w ∈ W, t w ∈ W) (hle : ¬ HardMathSupport.Kantor79.movedSpace t ≤ W) {w : U}
    (hw : w ∈ W) : t w = w := by
  by_contra hne
  have hx0 : t w - w ≠ 0 := sub_ne_zero.mpr hne
  have hxmem : t w - w ∈ HardMathSupport.Kantor79.movedSpace t := ⟨w, by simp⟩
  have hxW : t w - w ∈ W := W.sub_mem (hW w hw) hw
  have hspan : HardMathSupport.Kantor79.movedSpace t = Submodule.span K {t w - w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one ht hxmem hx0
  exact hle (by
    rw [hspan]
    exact Submodule.span_le.mpr (by rintro x rfl; exact hxW))

theorem eq_one_of_forall_sub_mem_of_finrank_eq_one {A : Subgroup (U ≃ₗ[K] U)}
    (hA : QTwoLin.TransvectionFree A) {W : Submodule K U} (hW : Module.finrank K W = 1)
    {g : U ≃ₗ[K] U} (hg : g ∈ A) (hfix : ∀ w ∈ W, g w = w) (hquot : ∀ v, g v - v ∈ W) :
    g = 1 := by
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hW
    exact Nat.zero_ne_one hW
  obtain ⟨w₀, hw₀mem, hw₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hWspan : W = Submodule.span K {w₀} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hW hw₀mem hw₀ne
  let Φ : U →ₗ[K] (Submodule.span K {w₀}) :=
    LinearMap.codRestrict (Submodule.span K {w₀}) ((g : U →ₗ[K] U) - 1) fun v => by
      rw [← hWspan]
      simpa using hquot v
  let ψ : U →ₗ[K] K :=
    (LinearEquiv.toSpanNonzeroSingleton K U w₀ hw₀ne).symm.toLinearMap.comp Φ
  have hψ : ∀ v, ψ v • w₀ = g v - v := by
    intro v
    simp [ψ, Φ, LinearMap.codRestrict_apply, LinearMap.sub_apply]
  have hψ0 : ψ w₀ = 0 := by
    have h := hψ w₀
    rw [hfix w₀ hw₀mem, sub_self] at h
    exact (smul_eq_zero.mp h).resolve_right hw₀ne
  by_contra hgne
  have hψne : ψ ≠ 0 := by
    intro hzero
    apply hgne
    ext v
    have h := hψ v
    rw [hzero] at h
    simp only [LinearMap.zero_apply, zero_smul] at h
    exact sub_eq_zero.mp h.symm
  exact hA g hg ⟨w₀, ψ, hw₀ne, hψne, hψ0,
    fun v => by rw [hψ v]; abel⟩

private theorem splitSupport_of_disjoint [FiniteDimensional K U] {H : Subgroup (U ≃ₗ[K] U)}
    {l : ℕ} (hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥)
    (hdim : Module.finrank K (HardMathSupport.Kantor79.commutatorSpace H) = l)
    (hle : Module.finrank K U ≤
      Module.finrank K (HardMathSupport.Kantor79.commutatorSpace H) +
        Module.finrank K (centralizerSpace H))
    (hirr : IrredOnSection H ⊥ (HardMathSupport.Kantor79.commutatorSpace H)) :
    SplitSupport H l := by
  refine ⟨?_, hdim, hirr⟩
  have hsum : Module.finrank K
      ↥(HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H) =
      Module.finrank K (HardMathSupport.Kantor79.commutatorSpace H) +
        Module.finrank K (centralizerSpace H) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H)
    rw [hinf, finrank_bot, add_zero] at h
    exact h
  have htop : Module.finrank K
      ↥(HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H) = Module.finrank K U :=
    le_antisymm (Submodule.finrank_le _) (hsum ▸ hle)
  exact IsCompl.of_le (le_of_eq hinf)
    (le_of_eq (Submodule.eq_top_of_finrank_eq htop).symm)

private theorem inf_commutatorSpace_centralizerSpace_eq_bot [FiniteDimensional K U] {r : ℕ}
    (hr : 1 < r) (x : Fin r → U ≃ₗ[K] U)
    (hdim : Module.finrank K
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x))) = r)
    (hirr : IrredOnSection (Subgroup.closure (Set.range x)) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x)))) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x)) ⊓
      centralizerSpace (Subgroup.closure (Set.range x)) = ⊥ := by
  let H := Subgroup.closure (Set.range x)
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let C := centralizerSpace H
  have hdim' : Module.finrank K V = r := hdim
  have hirr' : IrredOnSection H ⊥ V := hirr
  by_contra hne
  have hMinv : ∀ h ∈ H, ∀ y ∈ V ⊓ C, h y ∈ V ⊓ C := by
    intro h hh y hy
    refine ⟨?_, ?_⟩
    · have hm := Submodule.mem_map_of_mem (f := (h : U →ₗ[K] U)) hy.1
      rwa [map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hh)] at hm
    · have hy' : ∀ k ∈ H, k y = y := (mem_centralizerSpace).mp hy.2
      exact (mem_centralizerSpace).mpr fun k hk => by rw [hy' h hh]; exact hy' k hk
  rcases hirr' (V ⊓ C) bot_le inf_le_left hMinv with hM | hM
  · exact hne hM
  · have hVC : V ≤ C := by rw [← hM]; exact inf_le_right
    have hVne : V ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim'
      omega
    obtain ⟨w, hwV, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    have hspanV : Submodule.span K {w} ≤ V :=
      Submodule.span_le.mpr (by rintro y rfl; exact hwV)
    have hspanInv : ∀ h ∈ H, ∀ y ∈ Submodule.span K {w}, h y ∈ Submodule.span K {w} := by
      intro h hh y hy
      have hyfix : h y = y := (mem_centralizerSpace.mp (hVC (hspanV hy))) h hh
      rw [hyfix]
      exact hy
    rcases hirr' (Submodule.span K {w}) bot_le hspanV hspanInv with hs | hs
    · exact hw0 (by
        have hmem := hs ▸ Submodule.subset_span (Set.mem_singleton w)
        simpa using hmem)
    · have h1 : r = 1 := by rw [← hdim', ← hs, finrank_span_singleton hw0]
      omega

private theorem finrank_le_commutatorSpace_add_centralizerSpace [FiniteDimensional K U] {r : ℕ}
    (x : Fin r → U ≃ₗ[K] U)
    (hx : ∀ i, Module.finrank K (HardMathSupport.Kantor79.movedSpace (x i)) = 1)
    (hdim : Module.finrank K
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x))) = r) :
    Module.finrank K U ≤ Module.finrank K
        (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x))) +
      Module.finrank K (centralizerSpace (Subgroup.closure (Set.range x))) := by
  let H := Subgroup.closure (Set.range x)
  let C := centralizerSpace H
  let f : ∀ i, U →ₗ[K] HardMathSupport.Kantor79.movedSpace (x i) := fun i =>
    LinearMap.codRestrict (HardMathSupport.Kantor79.movedSpace (x i))
      ((x i : U →ₗ[K] U) - 1) (fun v => ⟨v, rfl⟩)
  let Ψ : U →ₗ[K] (∀ i, HardMathSupport.Kantor79.movedSpace (x i)) := LinearMap.pi f
  have hker : LinearMap.ker Ψ = C := by
    rw [show C = centralizerSpace (Subgroup.closure (Set.range x)) from rfl,
      centralizerSpace_closure_eq_iInf x]
    change LinearMap.ker (LinearMap.pi f) = ⨅ i, LinearMap.ker ((x i : U →ₗ[K] U) - 1)
    rw [LinearMap.ker_pi]
    refine le_antisymm (le_iInf fun i => ?_) (le_iInf fun i => ?_)
    · exact (iInf_le (fun j => LinearMap.ker (f j)) i).trans
        (le_of_eq (LinearMap.ker_codRestrict _ _ _))
    · exact (iInf_le (fun j => LinearMap.ker ((x j : U →ₗ[K] U) - 1)) i).trans
        (le_of_eq (LinearMap.ker_codRestrict _ _ _).symm)
  have hfin : Module.finrank K (LinearMap.range Ψ) ≤ r := by
    calc Module.finrank K (LinearMap.range Ψ)
        ≤ Module.finrank K (∀ i, HardMathSupport.Kantor79.movedSpace (x i)) :=
          Submodule.finrank_le _
      _ = ∑ i, Module.finrank K (HardMathSupport.Kantor79.movedSpace (x i)) :=
          Module.finrank_pi_fintype (R := K)
      _ = r := by simp [hx]
  have hrk := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hker] at hrk
  simp only [C, H] at hrk ⊢
  omega

theorem splitSupport_of_finrank_movedSpace_eq_one [FiniteDimensional K U] {r : ℕ} (hr : 1 < r)
    (x : Fin r → U ≃ₗ[K] U)
    (hx : ∀ i, Module.finrank K (HardMathSupport.Kantor79.movedSpace (x i)) = 1)
    (hdim : Module.finrank K
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x))) = r)
    (hirr : IrredOnSection (Subgroup.closure (Set.range x)) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x)))) :
    SplitSupport (Subgroup.closure (Set.range x)) r :=
  splitSupport_of_disjoint
    (inf_commutatorSpace_centralizerSpace_eq_bot hr x hdim hirr) hdim
    (finrank_le_commutatorSpace_add_centralizerSpace x hx hdim) hirr

end Field

@[expose] def IsRGroup (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (H : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ReflGen p H ∧ QTwoLin.TransvectionFree H

section Prime

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem IsRefl.ne_one {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) : t ≠ 1 := by
  intro h
  have h2 : Module.finrank (ZMod p)
      (LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 := ht.2
  rw [h] at h2
  have h0 : ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id = 0 := by
    ext x
    simp
  rw [h0, LinearMap.range_zero, finrank_bot] at h2
  exact Nat.zero_ne_one h2

private theorem commutatorSpace_le_of_forall_movedSpace_le {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH : ReflGen p H) {W : Submodule (ZMod p) U}
    (h : ∀ t, t ∈ H → IsRefl p t → HardMathSupport.Kantor79.movedSpace t ≤ W) :
    HardMathSupport.Kantor79.commutatorSpace H ≤ W := by
  rw [commutatorSpace_le_iff]
  intro g hg v
  have hclosure : H = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t} := hH
  have key : ∀ g ∈ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t},
      ∀ v, g v - v ∈ W := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht => exact fun v => h t ht.1 ht.2 ⟨v, by simp⟩
    | one => intro v; simp
    | mul a b ha hb iha ihb =>
      intro v
      have h1 := iha (b v)
      have h2 := ihb v
      rw [LinearEquiv.mul_apply]
      rw [show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
      exact W.add_mem h1 h2
    | inv a ha iha =>
      intro v
      have h1 := iha (a⁻¹ v)
      have h2 : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
        rw [show a (a⁻¹ v) = v from LinearEquiv.apply_symm_apply a v]
        abel
      rw [h2]
      exact W.neg_mem h1
  exact key g (by rw [← hclosure]; exact hg) v

theorem commutatorSpace_eq_iSup_of_reflGen [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hH : ReflGen p H) :
    HardMathSupport.Kantor79.commutatorSpace H =
      ⨆ (t : U ≃ₗ[ZMod p] U) (_ : t ∈ H ∧ IsRefl p t), HardMathSupport.Kantor79.movedSpace t := by
  conv_lhs => rw [hH]
  rw [← Subtype.range_coe_subtype,
    HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
      (fun t : {t : U ≃ₗ[ZMod p] U // t ∈ H ∧ IsRefl p t} => (t : U ≃ₗ[ZMod p] U))]
  exact iSup_subtype'' ({t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t})
    (fun t => HardMathSupport.Kantor79.movedSpace t)

theorem centralizerSpace_eq_iInf_of_reflGen {H : Subgroup (U ≃ₗ[ZMod p] U)} (hH : ReflGen p H) :
    centralizerSpace H =
      ⨅ (t : U ≃ₗ[ZMod p] U) (_ : t ∈ H ∧ IsRefl p t),
        LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) := by
  conv_lhs => rw [hH]
  rw [← Subtype.range_coe_subtype, centralizerSpace_closure_eq_iInf
    (fun t : {t : U ≃ₗ[ZMod p] U // t ∈ H ∧ IsRefl p t} => (t : U ≃ₗ[ZMod p] U))]
  exact iInf_subtype'' ({t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t})
    (fun t => LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1))

private theorem inf_commutatorSpace_centralizerSpace_eq_bot_of_isRefl (hp : p ≠ 2)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : IrredOnSection H ⊥ (HardMathSupport.Kantor79.commutatorSpace H))
    {t : U ≃ₗ[ZMod p] U} (htH : t ∈ H) (htRefl : IsRefl p t) :
    HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  set M : Submodule (ZMod p) U :=
    HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H with hMdef
  have hMinv : ∀ h ∈ H, ∀ x ∈ M, h x ∈ M := by
    intro h hh x hx
    refine ⟨?_, ?_⟩
    · have hm := Submodule.mem_map_of_mem (f := (h : U →ₗ[ZMod p] U)) hx.1
      rwa [map_commutatorSpace_of_mem_normalizer
        (Subgroup.le_normalizer hh)] at hm
    · have hxb' : ∀ k ∈ H, k x = x := (mem_centralizerSpace).mp hx.2
      exact (mem_centralizerSpace).mpr fun k hk => by
        rw [hxb' h hh]
        exact hxb' k hk
  rcases hirr M bot_le inf_le_left hMinv with hM | hM
  · simpa [hMdef] using hM
  · exfalso
    have hVHle : HardMathSupport.Kantor79.commutatorSpace H ≤ centralizerSpace H := by
      rw [← hM]
      exact inf_le_right
    have htfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 :=
      htRefl.2
    have hne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at htfin
      exact Nat.zero_ne_one htfin
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have haVH : a ∈ centralizerSpace H :=
      hVHle (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htH ha)
    have hfix : t a = a := (mem_centralizerSpace.mp haVH) t htH
    have hneg : t a = -a := apply_eq_neg_of_mem_movedSpace htRefl.1 ha
    have haeq : a = -a := by
      rw [hfix] at hneg
      exact hneg
    have h2a : (2 : ZMod p) • a = 0 := by
      rw [two_smul]
      nth_rewrite 2 [haeq]
      rw [add_neg_cancel]
    exact ha0 ((smul_eq_zero.mp h2a).resolve_left h2)

theorem commutatorSpace_inf_centralizerSpace_eq_bot (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH : ReflGen p H) (hirr : IrredOnSection H ⊥ (HardMathSupport.Kantor79.commutatorSpace H)) :
    HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ := by
  by_cases hrefl : ∃ t, t ∈ H ∧ IsRefl p t
  · obtain ⟨t, htH, htRefl⟩ := hrefl
    exact inf_commutatorSpace_centralizerSpace_eq_bot_of_isRefl hp hirr htH htRefl
  · push Not at hrefl
    have hbot : H = ⊥ := by
      rw [hH, Subgroup.closure_eq_bot_iff]
      intro t ht
      rw [Set.mem_singleton_iff]
      exact (hrefl t ht.1 ht.2).elim
    rw [hbot, commutatorSpace_bot, bot_inf_eq]

theorem eq_of_movedSpace_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : QTwoLin.TransvectionFree A) {a b : U ≃ₗ[ZMod p] U}
    (ha : a ∈ A) (hb : b ∈ A) (ha' : IsRefl p a) (hb' : IsRefl p b)
    (hab : HardMathSupport.Kantor79.movedSpace a = HardMathSupport.Kantor79.movedSpace b) :
    a = b := by
  obtain ⟨a₀, φ, hφ, ha_eq⟩ := (isRefl_iff hp a).mp ha'
  obtain ⟨b₀, ψ, hψ, hb_eq⟩ := (isRefl_iff hp b).mp hb'
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hmov : HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) =
      HardMathSupport.Kantor79.movedSpace (Module.reflection hψ) := by
    rw [← ha_eq, ← hb_eq]
    exact hab
  have hb₀mem : b₀ ∈ HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) := by
    rw [hmov]
    exact mem_movedSpace_of_apply_eq_neg h2 (Module.reflection_apply_self hψ)
  have hspan : b₀ ∈ Submodule.span (ZMod p) {a₀} := movedSpace_reflection_le_span hφ hb₀mem
  have hr : Module.reflection hφ ∈ A := by rwa [← ha_eq]
  have hs : Module.reflection hψ ∈ A := by rwa [← hb_eq]
  have hres := reflection_eq_of_mem_span hp hA hφ hψ hr hs hspan
  rw [ha_eq, hb_eq]
  exact hres

theorem eq_of_ker_sub_one_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : QTwoLin.TransvectionFree A) {a b : U ≃ₗ[ZMod p] U}
    (ha : a ∈ A) (hb : b ∈ A) (ha' : IsRefl p a) (hb' : IsRefl p b)
    (hab : LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) = LinearMap.ker ((b : U →ₗ[ZMod p] U) - 1)) :
    a = b := by
  obtain ⟨a₀, φ, hφ, ha_eq⟩ := (isRefl_iff hp a).mp ha'
  obtain ⟨b₀, ψ, hψ, hb_eq⟩ := (isRefl_iff hp b).mp hb'
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hker : LinearMap.ker φ = LinearMap.ker ψ := by
    rw [← ker_reflection_sub_one h2 hφ, ← ker_reflection_sub_one h2 hψ]
    rw [ha_eq, hb_eq] at hab
    exact hab
  have hr : Module.reflection hφ ∈ A := by rwa [← ha_eq]
  have hs : Module.reflection hψ ∈ A := by rwa [← hb_eq]
  have hres := reflection_eq_of_ker_eq hp hA hφ hψ hr hs hker
  rw [ha_eq, hb_eq]
  exact hres

private theorem not_movedSpace_le_centralizerSpace (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (htH : t ∈ H) (ht : IsRefl p t) :
    ¬ HardMathSupport.Kantor79.movedSpace t ≤ centralizerSpace H := by
  intro hle
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2
  have hne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    exact Nat.zero_ne_one hfin
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix : t a = a := (mem_centralizerSpace.mp (hle ha)) t htH
  have hneg : t a = -a := apply_eq_neg_of_mem_movedSpace ht.1 ha
  have haeq : a = -a := by
    rw [hfix] at hneg
    exact hneg
  have h2a : (2 : ZMod p) • a = 0 := by
    rw [two_smul]
    nth_rewrite 2 [haeq]
    rw [add_neg_cancel]
  exact ha0 ((smul_eq_zero.mp h2a).resolve_left h2)

private theorem exists_isRefl_not_movedSpace_le_of_not_commutatorSpace_le
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hH : ReflGen p H) {W : Submodule (ZMod p) U}
    (hVW : ¬ HardMathSupport.Kantor79.commutatorSpace H ≤ W) :
    ∃ t, t ∈ H ∧ IsRefl p t ∧ ¬ HardMathSupport.Kantor79.movedSpace t ≤ W := by
  by_contra h
  push Not at h
  exact hVW (commutatorSpace_le_of_forall_movedSpace_le hH h)

private theorem exists_isRefl_movedSpace_le_of_not_le_centralizer
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hH : ReflGen p H) {W : Submodule (ZMod p) U}
    (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) (hWc : ¬ W ≤ centralizerSpace H) :
    ∃ t, t ∈ H ∧ IsRefl p t ∧ HardMathSupport.Kantor79.movedSpace t ≤ W := by
  by_contra h
  push Not at h
  exact hWc (by
    intro w hw
    rw [centralizerSpace_eq_iInf_of_reflGen hH, Submodule.mem_iInf]
    intro t
    rw [Submodule.mem_iInf]
    intro ht
    have htw := apply_eq_self_of_not_movedSpace_le ht.2.2 (hW t ht.1) (h t ht.1 ht.2) hw
    simpa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using htw)

private theorem commutatorSpace_le_sup_of_isRefl_movedSpace_le
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : IrredOnSection H
      (HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {W : Submodule (ZMod p) U} (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) {t : U ≃ₗ[ZMod p] U}
    (htH : t ∈ H) (hmov : HardMathSupport.Kantor79.movedSpace t ≤ W)
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace t ≤ centralizerSpace H) :
    HardMathSupport.Kantor79.commutatorSpace H ≤ W ⊔ centralizerSpace H := by
  have hXinv : ∀ k ∈ H, ∀ x ∈ (W ⊔ centralizerSpace H) ⊓
      HardMathSupport.Kantor79.commutatorSpace H, k x ∈
      (W ⊔ centralizerSpace H) ⊓ HardMathSupport.Kantor79.commutatorSpace H := by
    intro k hk x hx
    refine ⟨?_, ?_⟩
    · rcases Submodule.mem_sup.mp hx.1 with ⟨w, hw, c, hc, hwc⟩
      rw [← hwc, map_add]
      exact Submodule.add_mem_sup (hW k hk w hw) (by
        have hkc : k c = c := (mem_centralizerSpace.mp hc) k hk
        rw [hkc]
        exact hc)
    · have hm := Submodule.mem_map_of_mem (f := (k : U →ₗ[ZMod p] U)) hx.2
      rwa [map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hk)] at hm
  have hinf_le : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H ≤
      (W ⊔ centralizerSpace H) ⊓ HardMathSupport.Kantor79.commutatorSpace H :=
    fun x hx => ⟨Submodule.mem_sup_right hx.2, hx.1⟩
  have hXle : (W ⊔ centralizerSpace H) ⊓ HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace H := inf_le_right
  rcases hirr ((W ⊔ centralizerSpace H) ⊓ HardMathSupport.Kantor79.commutatorSpace H)
    hinf_le hXle hXinv with hX | hX
  · exfalso
    apply hnot
    have hle : HardMathSupport.Kantor79.movedSpace t ≤
        (W ⊔ centralizerSpace H) ⊓ HardMathSupport.Kantor79.commutatorSpace H :=
      le_inf (hmov.trans le_sup_left) (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htH)
    rw [hX] at hle
    exact le_trans hle inf_le_right
  · rw [← hX]
    exact inf_le_left

private theorem false_of_isRefl_movedSpace_not_le (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {W : Submodule (ZMod p) U} (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) {t : U ≃ₗ[ZMod p] U}
    (htH : t ∈ H) (ht : IsRefl p t) (hmov_not : ¬ HardMathSupport.Kantor79.movedSpace t ≤ W)
    (hVHle : HardMathSupport.Kantor79.commutatorSpace H ≤ W ⊔ centralizerSpace H) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2
  have hne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    exact Nat.zero_ne_one hfin
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have ha_sup : a ∈ W ⊔ centralizerSpace H :=
    hVHle (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htH ha)
  have hfixW : ∀ w ∈ W, t w = w := fun w hw =>
    apply_eq_self_of_not_movedSpace_le ht.2 (hW t htH) hmov_not hw
  rcases Submodule.mem_sup.mp ha_sup with ⟨w, hw, c, hc, hwc⟩
  have ht_a : t a = a := by
    rw [← hwc, map_add, hfixW w hw, (mem_centralizerSpace.mp hc) t htH]
  have hneg : t a = -a := apply_eq_neg_of_mem_movedSpace ht.1 ha
  have haeq : a = -a := by
    rw [ht_a] at hneg
    exact hneg
  have h2a : (2 : ZMod p) • a = 0 := by
    rw [two_smul]
    nth_rewrite 2 [haeq]
    rw [add_neg_cancel]
  exact ha0 ((smul_eq_zero.mp h2a).resolve_left h2)

theorem commutatorSpace_le_or_le_centralizerSpace (hp : p ≠ 2) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH : ReflGen p H)
    (hirr : IrredOnSection H
      (HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H)
      (HardMathSupport.Kantor79.commutatorSpace H))
    {W : Submodule (ZMod p) U} (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) :
    HardMathSupport.Kantor79.commutatorSpace H ≤ W ∨ W ≤ centralizerSpace H := by
  by_cases hWc : W ≤ centralizerSpace H
  · exact Or.inr hWc
  · left
    by_contra hVW
    obtain ⟨h, hh, hrefl, hmov_not⟩ :=
      exists_isRefl_not_movedSpace_le_of_not_commutatorSpace_le hH hVW
    obtain ⟨h₁, hh₁, hrefl₁, hmov₁⟩ :=
      exists_isRefl_movedSpace_le_of_not_le_centralizer hH hW hWc
    have hVHle := commutatorSpace_le_sup_of_isRefl_movedSpace_le hirr hW hh₁ hmov₁
      (not_movedSpace_le_centralizerSpace hp hh₁ hrefl₁)
    exact false_of_isRefl_movedSpace_not_le hp hW hh hrefl hmov_not hVHle

private theorem splitSupport_of_isRefl_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (x : Fin 1 → U ≃ₗ[ZMod p] U) (hx : ∀ i, IsRefl p (x i))
    (hdim : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x))) = 1)
    (hirr : IrredOnSection (Subgroup.closure (Set.range x)) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x)))) :
    SplitSupport (Subgroup.closure (Set.range x)) 1 := by
  have hV : HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x)) =
      HardMathSupport.Kantor79.movedSpace (x 0) := by
    rw [HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace x]
    exact le_antisymm (iSup_le fun i => by
      rw [show i = 0 from Fin.ext (by simp only [Fin.val_zero]; omega)])
      (le_iSup (fun i => HardMathSupport.Kantor79.movedSpace (x i)) 0)
  have hC : centralizerSpace (Subgroup.closure (Set.range x)) =
      LinearMap.ker ((x 0 : U →ₗ[ZMod p] U) - 1) := by
    rw [centralizerSpace_closure_eq_iInf x]
    exact le_antisymm
      (iInf_le (fun i => LinearMap.ker ((x i : U →ₗ[ZMod p] U) - 1)) 0)
      (le_iInf fun i => by
        rw [show i = 0 from Fin.ext (by simp only [Fin.val_zero]; omega)])
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hinf0 : HardMathSupport.Kantor79.movedSpace (x 0) ⊓
      LinearMap.ker ((x 0 : U →ₗ[ZMod p] U) - 1) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
    have hafix : (x 0) a = a := by
      simpa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using ha.2
    have haneg : (x 0) a = -a := apply_eq_neg_of_mem_movedSpace (hx 0).1 ha.1
    have haeq : a = -a := by
      rw [hafix] at haneg
      exact haneg
    have h2a : (2 : ZMod p) • a = 0 := by
      rw [two_smul]
      nth_rewrite 2 [haeq]
      rw [add_neg_cancel]
    exact (smul_eq_zero.mp h2a).resolve_left h2
  have hle0 : Module.finrank (ZMod p) U ≤ 1 +
      Module.finrank (ZMod p) (LinearMap.ker ((x 0 : U →ₗ[ZMod p] U) - 1)) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker ((x 0 : U →ₗ[ZMod p] U) - 1)
    have hx0' : Module.finrank (ZMod p)
        (LinearMap.range ((x 0 : U →ₗ[ZMod p] U) - 1)) = 1 := (hx 0).2
    rw [← hrk, hx0']
  exact splitSupport_of_disjoint (by rw [hV, hC]; exact hinf0) hdim
    (by
      rw [hV, hC]
      rw [show Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace (x 0)) = 1 from
        (hx 0).2]
      exact hle0) hirr

theorem splitSupport_of_isRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    (x : Fin l → U ≃ₗ[ZMod p] U) (hx : ∀ i, IsRefl p (x i))
    (hdim : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x))) = l)
    (hirr : IrredOnSection (Subgroup.closure (Set.range x)) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (Set.range x)))) :
    SplitSupport (Subgroup.closure (Set.range x)) l := by
  rcases l with _ | _ | l
  · have hbot : Subgroup.closure (Set.range x) = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro t ⟨i, _⟩
      exact Fin.elim0 i
    have hCtop : centralizerSpace (⊥ : Subgroup (U ≃ₗ[ZMod p] U)) = ⊤ := by
      refine le_antisymm le_top fun v _ => ?_
      exact (mem_centralizerSpace).mpr fun h hh => by
        rw [Subgroup.mem_bot.mp hh]; rfl
    unfold SplitSupport
    rw [hbot, commutatorSpace_bot, hCtop]
    refine ⟨isCompl_bot_top, by simp, ?_⟩
    intro X hX hXle hXinv
    exact Or.inl (le_antisymm hXle bot_le)
  · exact splitSupport_of_isRefl_one hp x hx hdim hirr
  · exact splitSupport_of_finrank_movedSpace_eq_one (K := ZMod p) (by omega) x
      (fun i => (hx i).2) hdim hirr

end Prime

end CFSG.StandardType.ZS
