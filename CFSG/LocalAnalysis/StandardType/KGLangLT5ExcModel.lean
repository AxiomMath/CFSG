module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusDatum
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrame
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridge
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecHolds
public import CFSG.LocalAnalysis.StandardType.GGL45NtSimp
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralHolds
public import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcGlue
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcTorus
import CFSG.LocalAnalysis.StandardType.KGLangTorusModel
import CFSG.LocalAnalysis.StandardType.KGLangH90PPart
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.C14Exc

theorem kgLangTorusMPart_at_of_bridge {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hconj : GGRawFieldConj p R I F) (hrec : GGL45NtRec p R I F)
    {Γ : Type} [Group Γ] {G : Subgroup Γ} [Finite G] {F₀ : Γ →* Γ}
    (hstab : ∀ g ∈ G, F₀ g ∈ G) (hfix : ∀ g ∈ G, endPow F₀ p g = g)
    (ρ : R →* Γ) (Θ : G →* MulAut R) (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ G)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹)
    (hFj : ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPow F₀ j) (ρ r))
    (P : Subgroup Γ → Prop) (hPconj : ∀ g ∈ G, ∀ E : Subgroup Γ, P E →
      P (E.map (MulAut.conj (g : Γ)⁻¹).toMonoidHom))
    (hT : ∀ E : Subgroup Γ, IsElemAbelian p E → (∀ x ∈ E, x ∈ G ∧ F₀ x = x) → P E →
      ∃ N : Subgroup Γ, N ≤ G ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ (∀ x ∈ N, F₀ x ∈ N) ∧
        (∀ c ∈ N, ((List.range p).map fun i => endPow F₀ i c).prod = 1 →
          ∃ s ∈ N, c = s⁻¹ * F₀ s) ∧ E ≤ N)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hcomm : commutator K = ⊤)
    (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A)
    (hAI : ∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f)
    (hA0 : ∃ α ∈ A, α ≠ 1 ∧ kgInducedAut θ α ∈ I)
    (hP : P (Subgroup.closure {x : Γ | x ∈ G ∧ ∃ α ∈ A, kgInducedAut θ α ∈ I ∧
      ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}))
    (α₀ : MulAut K) (hα₀ : α₀ ∈ A) (hα₀I : kgInducedAut θ α₀ ∉ I) :
    ∃ M : Subgroup K, (∀ a ∈ M, ∀ c ∈ M, a * c = c * a) ∧ (∀ t, α₀ t ∈ M ↔ t ∈ M) ∧
      (∀ α ∈ A, kgInducedAut θ α ∈ I → ∀ t ∈ M, α t = t) ∧
      (∀ c ∈ M, ((List.range p).map fun i => (α₀ ^ i) c).prod = 1 → ∃ s ∈ M, c = s⁻¹ * α₀ s) ∧
      ∃ e ∈ M, e ≠ 1 ∧ e ^ p = 1 ∧ α₀ e = e := by
  obtain ⟨hInn, hinn, hcent⟩ := hrec hs hna
  have hZ := kgLang_coprime_of_centerPrime hp hcent θ hcomm
  obtain ⟨u, hu, f, hf, huf⟩ := hAI α₀ hα₀
  have hxI : u * f ∉ I := by rw [← huf]; exact hα₀I
  have hxp : (u * f) ^ p = 1 := by
    rw [← huf, ← map_pow, hA.2 α₀ hα₀, map_one]
  obtain ⟨u', hu'I, f', hf'F, hf'order, heq⟩ :=
    kgLangFieldConj_root hconj hs hna hu hf hxI hxp
  obtain ⟨g', hg'⟩ := (hI u').1 hu'I
  obtain ⟨j, hpj, hj⟩ := hFj f' hf'F hf'order
  obtain ⟨j', hj'lt, hj'mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((hp.coprime_iff_not_dvd.2 hpj).symm) hp.one_lt
  have hpj' : ¬ p ∣ j' := by
    intro hdvd
    have h0 : j' = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hj'lt
    rw [h0, Nat.mul_zero, Nat.zero_mod] at hj'mod
    omega
  have hjj : j * j' ≡ 1 [MOD p] := by
    rw [Nat.ModEq, hj'mod, Nat.mod_eq_of_lt hp.one_lt]
  let α₁ : MulAut K := α₀ ^ j'
  have hα₁ : α₁ ∈ A := A.pow_mem hα₀ j'
  have hα₁Ieq : kgInducedAut θ α₁ = (Θ g' * f' * (Θ g')⁻¹) ^ j' := by
    rw [show α₁ = α₀ ^ j' from rfl, map_pow, huf, heq, ← hg']
  have hroot := kgLangBridge_root hp hfix hρG hconjΘ hj hjj g'
  let F₁ : Γ →* Γ :=
    (MulAut.conj (g' : Γ)).toMonoidHom.comp (F₀.comp (MulAut.conj (g' : Γ)⁻¹).toMonoidHom)
  have hF₁ : ∀ y : Γ, (g' : Γ) * F₀ ((g' : Γ)⁻¹ * y * (g' : Γ)) * (g' : Γ)⁻¹ = F₁ y := by
    intro y
    simp only [F₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hF₁stab : ∀ y ∈ G, F₁ y ∈ G := by
    intro y hy
    rw [← hF₁ y]
    exact G.mul_mem (G.mul_mem g'.2 (hstab _ (G.mul_mem (G.mul_mem (G.inv_mem g'.2) hy) g'.2)))
      (G.inv_mem g'.2)
  have hF₁p : ∀ z ∈ G, endPow F₁ p z = z := by
    intro z hz
    have h := endPow_conj F₀ F₁ (g' : Γ) hF₁ p ((g' : Γ)⁻¹ * z * (g' : Γ))
    rw [show (g' : Γ) * ((g' : Γ)⁻¹ * z * (g' : Γ)) * (g' : Γ)⁻¹ = z from by group] at h
    rw [hfix _ (G.mul_mem (G.mul_mem (G.inv_mem g'.2) hz) g'.2)] at h
    rw [show (g' : Γ) * ((g' : Γ)⁻¹ * z * (g' : Γ)) * (g' : Γ)⁻¹ = z from by group] at h
    exact h
  have hF₁inj : ∀ x ∈ G, ∀ y ∈ G, F₁ x = F₁ y → x = y := by
    intro x hx y hy hxy
    have hx1 : endPow F₁ (p - 1) (F₁ x) = x := by
      have h1 : endPow F₁ (p - 1) (F₁ x) = endPow F₁ p x := by
        rw [endPow_apply, endPow_apply, ← Function.iterate_succ_apply, Nat.succ_eq_add_one,
          Nat.sub_add_cancel hp.one_le]
      rw [h1, hF₁p x hx]
    have hy1 : endPow F₁ (p - 1) (F₁ y) = y := by
      have h1 : endPow F₁ (p - 1) (F₁ y) = endPow F₁ p y := by
        rw [endPow_apply, endPow_apply, ← Function.iterate_succ_apply, Nat.succ_eq_add_one,
          Nat.sub_add_cancel hp.one_le]
      rw [h1, hF₁p y hy]
    have hcong := congrArg (fun w => endPow F₁ (p - 1) w) hxy
    rwa [hx1, hy1] at hcong
  obtain ⟨β, hβ⟩ := kgLang_exists_mulAut_restrict F₁ hF₁stab hF₁inj
  let ι : R →* G := ρ.codRestrict G hρG
  have hι : Function.Injective ι := fun a b h => hρ (Subtype.ext_iff.mp h)
  have hβι : ∀ r, ι (kgInducedAut θ α₁ r) = β (ι r) := by
    intro r
    apply Subtype.ext
    show ρ (kgInducedAut θ α₁ r) = (β (ι r) : Γ)
    have hιr : (ι r : Γ) = ρ r := rfl
    rw [hβ (ι r), hιr, hα₁Ieq, hroot r]
    exact hF₁ (ρ r)
  have hG1 : ∀ g : G, ∀ k : ℕ, g ^ (p ^ k) = 1 → g ∈ ι.range := by
    intro g k hg
    obtain ⟨r, hr⟩ := kgLangBridge_pElt_mem_range hρ hρG hΘ hI hconjΘ hinn hg
    exact ⟨r, Subtype.ext hr⟩
  have hG5 : ∀ g : G, (∀ r, g * ι r = ι r * g) → g = 1 := by
    intro g hg
    apply kgLangBridge_eq_one_of_commute hρ hΘ hconjΘ
    intro r
    have hcong := congrArg (fun x : G => (x : Γ)) (hg r)
    simpa [ι] using hcong
  let J : Subgroup (MulAut R) := Θ.range
  have hJI : (J : Set (MulAut R)) = I := by
    ext φ
    change φ ∈ Θ.range ↔ φ ∈ I
    rw [MonoidHom.mem_range]
    exact (hI φ).symm
  have hmemJ : ∀ φ : MulAut R, φ ∈ J ↔ φ ∈ I := fun φ => Set.ext_iff.mp hJI φ
  have hG6 : ∀ u ∈ J, ∃ h : G, ∀ r, ι (u r) = h * ι r * h⁻¹ := by
    intro u hu
    rw [MonoidHom.mem_range] at hu
    obtain ⟨g, rfl⟩ := hu
    refine ⟨g, fun r => ?_⟩
    apply Subtype.ext
    change ρ ((Θ g) r) = (g : Γ) * ρ r * (g : Γ)⁻¹
    exact hconjΘ g r
  obtain ⟨h, hmap, hinj, hmul⟩ := kgLangModelHom θ hcomm ι hι hG5 J hG6 A hA α₁ hα₁ β hβι
  let S : Set Γ := {x | ∃ α ∈ A, kgInducedAut θ α ∈ I ∧ x = (g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ)}
  let E : Subgroup Γ := Subgroup.closure S
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x ⟨α, hαA, hαI, rfl⟩ y ⟨β, hβA, hβI, rfl⟩
    have hJα : kgInducedAut θ α ∈ J := (hmemJ _).2 hαI
    have hJβ : kgInducedAut θ β ∈ J := (hmemJ _).2 hβI
    have hαβ : α * β = β * α := by
      letI : IsMulCommutative A := hA.1
      exact congrArg (fun x : A => (x : MulAut K)) (mul_comm' ⟨α, hαA⟩ ⟨β, hβA⟩)
    have h1 : h (α * β) = h α * h β := hmul α hαA β hβA hJα hJβ
    have h2 : h (β * α) = h β * h α := hmul β hβA α hαA hJβ hJα
    have hhcomm : h α * h β = h β * h α := by rw [← h1, ← h2, hαβ]
    calc (g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ) * ((g' : Γ)⁻¹ * (h β : Γ) * (g' : Γ))
        = (g' : Γ)⁻¹ * ((h α : Γ) * (h β : Γ)) * (g' : Γ) := by group
      _ = (g' : Γ)⁻¹ * ((h β : Γ) * (h α : Γ)) * (g' : Γ) := by
            rw [show (h α : Γ) * (h β : Γ) = (h β : Γ) * (h α : Γ) by
              simpa only [Subgroup.coe_mul] using congrArg (fun x : G => (x : Γ)) hhcomm]
      _ = (g' : Γ)⁻¹ * (h β : Γ) * (g' : Γ) * ((g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ)) := by group
  have hpowS : ∀ x ∈ S, x ^ p = 1 := by
    rintro x ⟨α, hαA, hαI, rfl⟩
    have hJα : kgInducedAut θ α ∈ J := (hmemJ _).2 hαI
    have hpα : h α ^ p = 1 := (hmap α hαA hJα).1
    have hpα' : (h α : Γ) ^ p = 1 := by rw [← Subgroup.coe_pow, hpα, Subgroup.coe_one]
    calc ((g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ)) ^ p
        = (g' : Γ)⁻¹ * (h α : Γ) ^ p * (g' : Γ) := by
          rw [show (g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ) = MulAut.conj (g' : Γ)⁻¹ (h α : Γ) by
            rw [MulAut.conj_apply, inv_inv]]
          rw [← map_pow, MulAut.conj_apply, inv_inv]
      _ = 1 := by rw [hpα']; group
  have hEab : IsElemAbelian p E := kgLang_isElemAbelian_closure hcommS hpowS
  have hgen : ∀ x ∈ S, x ∈ G ∧ F₀ x = x := by
    rintro x ⟨α, hαA, hαI, rfl⟩
    have hJα : kgInducedAut θ α ∈ J := (hmemJ _).2 hαI
    have hβh : β (h α) = h α := (hmap α hαA hJα).2.1
    refine ⟨?_, ?_⟩
    · exact G.mul_mem (G.mul_mem (G.inv_mem g'.2) (h α).2) g'.2
    · have h1 : F₁ ((h α : Γ)) = (h α : Γ) := by rw [← hβ (h α), hβh]
      have h4 : (g' : Γ) * F₀ ((g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ)) * (g' : Γ)⁻¹ = (h α : Γ) := by
        rw [hF₁ ((h α : Γ)), h1]
      have h6 : (g' : Γ) * ((g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ)) * (g' : Γ)⁻¹ = (h α : Γ) := by
        group
      have h7 : (g' : Γ) * F₀ ((g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ)) * (g' : Γ)⁻¹ =
          (g' : Γ) * ((g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ)) * (g' : Γ)⁻¹ := h4.trans h6.symm
      exact mul_left_cancel (mul_right_cancel h7)
  have hEG : ∀ x ∈ E, x ∈ G ∧ F₀ x = x := by
    intro x hx
    change x ∈ Subgroup.closure S at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => exact ⟨G.one_mem, map_one F₀⟩
    | mul x y hx hy ihx ihy => exact ⟨G.mul_mem ihx.1 ihy.1, by rw [map_mul, ihx.2, ihy.2]⟩
    | inv x hx ih => exact ⟨G.inv_mem ih.1, by rw [map_inv, ih.2]⟩
  let T : Set Γ := {x : Γ | x ∈ G ∧ ∃ α ∈ A, kgInducedAut θ α ∈ I ∧
    ∀ r, ρ (kgInducedAut θ α r) = x * ρ r * x⁻¹}
  have hPT : P (Subgroup.closure T) := hP
  have hEeq : E = (Subgroup.closure T).map (MulAut.conj (g' : Γ)⁻¹).toMonoidHom := by
    apply le_antisymm
    · change Subgroup.closure S ≤
        (Subgroup.closure T).map (MulAut.conj (g' : Γ)⁻¹).toMonoidHom
      rw [Subgroup.closure_le]
      rintro x ⟨α, hαA, hαI, rfl⟩
      refine Subgroup.mem_map.mpr ⟨(h α : Γ), Subgroup.subset_closure ?_, ?_⟩
      · refine ⟨(h α).2, α, hαA, hαI, ?_⟩
        intro r
        have h := (hmap α hαA ((hmemJ _).2 hαI)).2.2 r
        simpa [ι, Subgroup.coe_mul, Subgroup.coe_inv] using congrArg (fun z : G => (z : Γ)) h
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · change (Subgroup.closure T).map (MulAut.conj (g' : Γ)⁻¹).toMonoidHom ≤
        Subgroup.closure S
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro x ⟨y, hyT, rfl⟩
      obtain ⟨hyG, α, hαA, hαI, hind⟩ := hyT
      refine Subgroup.subset_closure ⟨α, hαA, hαI, ?_⟩
      have hyh : y = (h α : Γ) := by
        have hcomm : (⟨(h α)⁻¹ * y, G.mul_mem (G.inv_mem (h α).2) hyG⟩ : G) = 1 := by
          apply kgLangBridge_eq_one_of_commute hρ hΘ hconjΘ
          intro r
          show (h α : Γ)⁻¹ * y * ρ r = ρ r * ((h α : Γ)⁻¹ * y)
          have hhα : ρ (kgInducedAut θ α r) = (h α : Γ) * ρ r * (h α : Γ)⁻¹ := by
            have h := (hmap α hαA ((hmemJ _).2 hαI)).2.2 r
            simpa [ι, Subgroup.coe_mul, Subgroup.coe_inv] using congrArg (fun z : G => (z : Γ)) h
          have heq : y * ρ r * y⁻¹ = (h α : Γ) * ρ r * (h α : Γ)⁻¹ := by
            rw [← hind r, hhα]
          calc (h α : Γ)⁻¹ * y * ρ r
              = (h α : Γ)⁻¹ * (y * ρ r * y⁻¹) * y := by group
            _ = (h α : Γ)⁻¹ * ((h α : Γ) * ρ r * (h α : Γ)⁻¹) * y := by rw [heq]
            _ = ρ r * ((h α : Γ)⁻¹ * y) := by group
        have hy1 : (h α : Γ)⁻¹ * y = 1 := by
          have := congrArg (fun z : G => (z : Γ)) hcomm
          simpa using this
        exact (inv_mul_eq_one.mp hy1).symm
      rw [hyh]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hPE : P E := by
    rw [hEeq]
    exact hPconj g' g'.2 (Subgroup.closure T) hPT
  obtain ⟨N₀, hN₀G, hN₀ab, hN₀st, hN₀90, hEN₀⟩ := hT E hEab hEG hPE
  let N : Subgroup G := (N₀.map (MulAut.conj (g' : Γ)).toMonoidHom).subgroupOf G
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    change (a : Γ) * (b : Γ) = (b : Γ) * (a : Γ)
    have ha' : (a : Γ) ∈ N₀.map (MulAut.conj (g' : Γ)).toMonoidHom :=
      (Subgroup.mem_subgroupOf).mp ha
    have hb' : (b : Γ) ∈ N₀.map (MulAut.conj (g' : Γ)).toMonoidHom :=
      (Subgroup.mem_subgroupOf).mp hb
    obtain ⟨y, hyN₀, hy⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨z, hzN₀, hz⟩ := Subgroup.mem_map.mp hb'
    rw [← hy, ← hz, ← map_mul, ← map_mul, hN₀ab y hyN₀ z hzN₀]
  have hβNf : ∀ x ∈ N, β x ∈ N := by
    intro x hx
    have hx' : (x : Γ) ∈ N₀.map (MulAut.conj (g' : Γ)).toMonoidHom :=
      (Subgroup.mem_subgroupOf).mp hx
    obtain ⟨y, hyN₀, hy⟩ := Subgroup.mem_map.mp hx'
    refine (Subgroup.mem_subgroupOf).mpr (Subgroup.mem_map.mpr ⟨F₀ y, hN₀st y hyN₀, ?_⟩)
    rw [hβ x, ← hy]
    change (MulAut.conj (g' : Γ)) (F₀ y) = F₁ ((MulAut.conj (g' : Γ)) y)
    rw [← hF₁ ((MulAut.conj (g' : Γ)) y)]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hβN : ∀ x : G, β x ∈ N ↔ x ∈ N := kgLang_mulAut_mem_iff β hβNf
  have hH90 : ∀ c ∈ N, ((List.range p).map fun i => (β ^ i) c).prod = 1 →
      ∃ s ∈ N, c = s⁻¹ * β s := by
    intro c hcN hcn
    have hcN' : (c : Γ) ∈ N₀.map (MulAut.conj (g' : Γ)).toMonoidHom :=
      (Subgroup.mem_subgroupOf).mp hcN
    obtain ⟨x, hxN₀, hx⟩ := Subgroup.mem_map.mp hcN'
    have hterm : ∀ i, ((β ^ i) c : Γ) = MulAut.conj (g' : Γ) (endPow F₀ i x) := by
      intro i
      rw [kgLang_mulAut_pow_coe β F₁ hβ i c, ← hx]
      have hconj : endPow F₁ i (MulAut.conj (g' : Γ) x) = MulAut.conj (g' : Γ) (endPow F₀ i x) := by
        rw [show MulAut.conj (g' : Γ) x = (g' : Γ) * x * (g' : Γ)⁻¹ by rw [MulAut.conj_apply],
          show MulAut.conj (g' : Γ) (endPow F₀ i x) = (g' : Γ) * endPow F₀ i x * (g' : Γ)⁻¹ by
            rw [MulAut.conj_apply]]
        exact endPow_conj F₀ F₁ (g' : Γ) hF₁ i x
      exact hconj
    have hprod : ((List.range p).map fun i => endPow F₀ i x).prod = 1 := by
      have hcoe : (List.map (fun i => ((β ^ i) c : Γ)) (List.range p)).prod = 1 := by
        have hcong := congrArg (fun w : G => (w : Γ)) hcn
        rw [Subgroup.val_list_prod, Subgroup.coe_one] at hcong
        simpa only [List.map_map, Function.comp_def] using hcong
      have hlist : (List.map (fun i => ((β ^ i) c : Γ)) (List.range p))
          = List.map (fun i => MulAut.conj (g' : Γ) (endPow F₀ i x)) (List.range p) := by
        apply List.map_congr_left
        intro i _
        exact hterm i
      rw [hlist] at hcoe
      have hmap : (List.map (fun i => MulAut.conj (g' : Γ) (endPow F₀ i x)) (List.range p)).prod
          = MulAut.conj (g' : Γ) ((List.range p).map (fun i => endPow F₀ i x)).prod := by
        have h := (map_list_prod (MulAut.conj (g' : Γ)).toMonoidHom
          ((List.range p).map (fun i => endPow F₀ i x))).symm
        simpa only [List.map_map, Function.comp_def, MulEquiv.coe_toMonoidHom] using h
      have h1 : MulAut.conj (g' : Γ) ((List.range p).map (fun i => endPow F₀ i x)).prod = 1 := by
        rw [← hmap]; exact hcoe
      exact (MulAut.conj (g' : Γ)).injective (by rw [h1, map_one])
    obtain ⟨s₀, hs₀N₀, hs₀⟩ := hN₀90 x hxN₀ hprod
    let s : G := ⟨MulAut.conj (g' : Γ) s₀,
      G.mul_mem (G.mul_mem g'.2 (hN₀G hs₀N₀)) (G.inv_mem g'.2)⟩
    have hsN : s ∈ N :=
      (Subgroup.mem_subgroupOf).mpr (Subgroup.mem_map.mpr ⟨s₀, hs₀N₀, rfl⟩)
    refine ⟨s, hsN, ?_⟩
    apply Subtype.ext
    change (c : Γ) = (s⁻¹ * β s : G)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hβ s]
    rw [show (s : Γ) = MulAut.conj (g' : Γ) s₀ from rfl]
    rw [← hx, hs₀]
    rw [map_mul, map_inv, ← hF₁ (MulAut.conj (g' : Γ) s₀)]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hh : ∀ α ∈ A, kgInducedAut θ α ∈ I → h α ∈ N ∧ h α ^ p = 1 ∧ β (h α) = h α ∧
      ∀ r, ι (kgInducedAut θ α r) = h α * ι r * (h α)⁻¹ := by
    intro α hαA hαI
    have hJα : kgInducedAut θ α ∈ J := (hmemJ _).2 hαI
    have hspec := hmap α hαA hJα
    refine ⟨?_, hspec.1, hspec.2.1, hspec.2.2⟩
    refine (Subgroup.mem_subgroupOf).mpr (Subgroup.mem_map.mpr
      ⟨(g' : Γ)⁻¹ * (h α : Γ) * (g' : Γ), hEN₀ (Subgroup.subset_closure ⟨α, hαA, hαI, rfl⟩), ?_⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hne : ∃ α ∈ A, kgInducedAut θ α ∈ I ∧ h α ≠ 1 := by
    obtain ⟨α, hαA, hαne, hαI⟩ := hA0
    exact ⟨α, hαA, hαI, hinj α hαA ((hmemJ _).2 hαI) hαne⟩
  obtain ⟨M, hMab, hMst, hMfix, hM90, e, he, he1, hep, heα, heA⟩ :=
    kgLangLT5_of_model hp θ hZ I A α₁ ι hι hG1 β hβι N hNab hβN hH90 h hh hne
  have hd := kgLangDatum_of_pow hp hpj' (hA.2 α₀ hα₀)
    {α : MulAut K | α ∈ A ∧ kgInducedAut θ α ∈ I}
    M hMab hMst (fun α hα => hMfix α hα.1 hα.2) hM90 e he he1 hep heα
  exact ⟨M, hMab, hd.1, (fun α hα hαI => hd.2.1 α ⟨hα, hαI⟩), hd.2.2.1,
    ⟨e, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩⟩

theorem kgLangTorusMPart_of_absBridge {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hconj : GGRawFieldConj p R I F) (hrec : GGL45NtRec p R I F)
    {Γ : Type} [Group Γ] {G : Subgroup Γ} [Finite G] {F₀ : Γ →* Γ}
    (hstab : ∀ g ∈ G, F₀ g ∈ G) (hfix : ∀ g ∈ G, endPow F₀ p g = g)
    (hbr : AbsBridge p I F G F₀) (hT : KGLangTorusInput p G F₀) :
    KGLangTorusMPart p R I F := by
  intro hfin θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  haveI := hfin
  obtain ⟨ρ, Θ, hρ, hρG, hΘ, hI, hconjΘ, hFj⟩ := hbr
  exact kgLangTorusMPart_at_of_bridge hp hs hna hconj hrec hstab hfix ρ Θ hρ hρG hΘ hI hconjΘ hFj
    (fun _ => True) (fun _ _ _ _ => trivial) (fun E hEab hEG _ => hT E hEab hEG)
    θ hcomm A hA hAI hA0 trivial α₀ hα₀ hα₀I

theorem kgLangTorusDatumCont_of_excBridge
    (hM1 : CFSG.StandardType.LieCore.GGLieToralPosition)
    (hM2 : CFSG.StandardType.LieCore.GGLieLangPosition)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hnt : GGL45FamNonTorsion p lab) (hexc : GGL45NtExcLabel lab)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {R : Type} [Group R] {I F : Set (MulAut R)}
    (hbr : ExcBridgeCont p L lab.tag R I F) (hrec : GGL45NtRec p R I F)
    (hsimp : GGL45NtSimp R I F) (hconj : GGRawFieldConj p R I F) (hcyc : GGRawPCyclic p R I F) :
    KGLangTorusDatumCont p R I F := by
  by_cases hna : ∃ a b : R, a * b ≠ b * a
  · have hs : IsSimpleGroup R := hsimp hna
    obtain ⟨J, S, hJI, hJS, hN, hcycS, hpS⟩ := hcyc hs hna
    have hcyc' : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
        (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
        ∀ α ∈ Subgroup.closure (I ∪ F), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S :=
      ⟨J, S, hJI, hJS, hN, hcycS, fun α _ hα => hpS α hα⟩
    have hM : KGLangTorusMPart p R I F := by
      by_cases hF : ∃ f ∈ F, orderOf f = p
      · obtain ⟨e, Q, he, hQ, hbr', hSt, hfin⟩ := hbr hs hF
        obtain ⟨h3, h3D, h5⟩ := nonTorsion_excTag hnt hexc
        haveI := hfin
        exact kgLangTorusMPart_of_absBridge hp hs hna hconj hrec hbr'.stab
          (fun g hg => ratPts_fix hg) hbr'.absBridge
          (kgLangExcTorusInput hM1 hM2 hL hp hp2 h3 h5 he hQ hfin)
      · push Not at hF
        exact kgLangTorusMPart_of_forall_orderOf_ne hconj hs hna hF
    exact kgLangTorusDatumCont_of_models hp hcyc' hM
  · push Not at hna
    exact kgLangTorusDatumCont_of_comm hna

end CFSG.StandardType
