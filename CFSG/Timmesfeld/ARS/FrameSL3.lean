module

public import CFSG.Timmesfeld.ARS.FrameSL3Coord
public import CFSG.Timmesfeld.ARS.FrameSL3Steinberg

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType.Universal Matrix

variable {G : Type*} [Group G]

namespace FrameSL3

theorem exists_aligned {F : Type*} [Field F] {xA xB xC yA yB yC yB' : F → G}
    (hxC : Function.Injective xC) (hxCinv : ∀ r, (xC r)⁻¹ = xC r)
    (hab : ∀ t s, ⁅xA t, xB s⁆ = xC (t * s)) (hyab : ∀ t s, ⁅yB t, yA s⁆ = yC (t * s))
    (hyf : ∀ t s, ⁅yB' t, yC s⁆ = yA (t * s))
    (hA : ∀ s, ∃ r, xA r = yA s) (hB : ∀ t, ∃ r, xB r = yB t)
    (hC : ∀ r, ∃ r', xC r' = yC r) (hC' : ∀ r, ∃ r', yC r' = xC r) (h1 : yC 1 = xC 1) :
    ∃ t₀, ∀ s, ⁅yB' t₀, xC s⁆ = xA s := by
  choose α hα using hA
  choose β hβ using hB
  choose γ hγ using hC
  have key : ∀ t s, γ (t * s) = α s * β t := by
    intro t s
    apply hxC
    rw [hγ, ← hyab, ← hα, ← hβ, ← commutatorElement_inv, hab, hxCinv]
  have hγ1 : γ 1 = 1 := hxC (by rw [hγ, h1])
  have hs := fun s => key 1 s
  have ht := fun t => key t 1
  have h11 : α 1 * β 1 = 1 := by rw [← key, mul_one, hγ1]
  simp only [one_mul, mul_one] at hs ht
  have hmul : ∀ t s, γ (t * s) = γ t * γ s := by
    intro t s
    rw [key, ht t, hs s]
    linear_combination (-(α s * β t)) * h11
  obtain ⟨t₀, ht₀⟩ := hC' (β 1)
  have hγt₀ : γ t₀ = β 1 := hxC (by rw [hγ, ht₀])
  refine ⟨t₀, fun s => ?_⟩
  obtain ⟨r, hr⟩ := hC' s
  have hγr : γ r = s := hxC (by rw [hγ, hr])
  have hαr : α (t₀ * r) = s := by
    have h := hs (t₀ * r)
    rw [hmul, hγt₀, hγr] at h
    have hβ1 : β 1 ≠ 0 := right_ne_zero_of_mul_eq_one h11
    exact (mul_right_cancel₀ hβ1 (by rw [← h, mul_comm])).symm
  rw [← hr, hyf, ← hα, hαr]

theorem commutatorElement_conj (g a b : G) :
    ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

variable {R : Set (Subgroup G)}

theorem special_of_commutator_eq {X Y Z : Subgroup G} (h : ⁅X, Y⁆ = Z) (hZ : Z ∈ R)
    (hX : Commuting Z X) (hY : Commuting Z Y) : Special R X Y := by
  unfold Special
  rw [h]
  exact ⟨hZ, hX, hY⟩

theorem exists_coords [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B A' B' : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hA' : A' ∈ R) (hB' : B' ∈ R)
    (hAB : Special R A B) (hAA' : Opposite A A') (hBB' : Opposite B B')
    (h1 : Commuting A' B) (h2 : ⁅A', ⁅A, B⁆⁆ = B) (h3 : Commuting A B')
    (h4 : ⁅⁅A, B⁆, B'⁆ = A) (h5 : Special R A' B')
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (φ₁ : ↥(A ⊔ A') ≃* SpecialLinearGroup (Fin 2) F)
    (hφ₁ : (A.subgroupOf (A ⊔ A')).map φ₁.toMonoidHom = upperUnipotent F)
    (hφ₁' : (A'.subgroupOf (A ⊔ A')).map φ₁.toMonoidHom = lowerUnipotent F)
    (φ₂ : ↥(B ⊔ B') ≃* SpecialLinearGroup (Fin 2) F)
    (hφ₂ : (B.subgroupOf (B ⊔ B')).map φ₂.toMonoidHom = upperUnipotent F)
    (hφ₂' : (B'.subgroupOf (B ⊔ B')).map φ₂.toMonoidHom = lowerUnipotent F) :
    ∃ xA xB xC xA' xB' xC' : F → G, xA = upPar φ₁ ∧ xA' = lowPar φ₁ ∧
      Set.range xA = (A : Set G) ∧ Set.range xB = (B : Set G) ∧
      Set.range xC = ((⁅A, B⁆ : Subgroup G) : Set G) ∧ Set.range xA' = (A' : Set G) ∧
      Set.range xB' = (B' : Set G) ∧ Set.range xC' = ((⁅A', B'⁆ : Subgroup G) : Set G) ∧
      (∀ s t, xA (s + t) = xA s * xA t) ∧ (∀ s t, xB (s + t) = xB s * xB t) ∧
      (∀ s t, xC (s + t) = xC s * xC t) ∧ (∀ s t, xA' (s + t) = xA' s * xA' t) ∧
      (∀ s t, xB' (s + t) = xB' s * xB' t) ∧ (∀ s t, xC' (s + t) = xC' s * xC' t) ∧
      (∀ s t, ⁅xA s, xB t⁆ = xC (s * t)) ∧ (∀ s t, ⁅xA' s, xC t⁆ = xB (s * t)) ∧
      (∀ s t, ⁅xA s, xC' t⁆ = xB' (s * t)) ∧ (∀ s t, ⁅xA' s, xB' t⁆ = xC' (s * t)) ∧
      (∀ s t, ⁅xB' s, xC t⁆ = xA (s * t)) ∧ (∀ s t, ⁅xB s, xC' t⁆ = xA' (s * t)) := by
  set C := ⁅A, B⁆
  have hC : C ∈ R := hAB.1
  have hCB' : Special R C B' := special_of_commutator_eq h4 hA hAB.2.1.symm h3
  have hA'C : Special R A' C := special_of_commutator_eq h2 hB h1.symm hAB.2.2.symm
  have hlamA := mem_lambdaSet_commutator hR hiso hC hB' hCB'
  rw [h4] at hlamA
  have hlamB := mem_lambdaSet_commutator hR hiso hA' hC hA'C
  rw [h2] at hlamB
  have hCψA' : C ∈ psiSet R A' := ⟨hC, hA'C⟩
  have hCψB' : C ∈ psiSet R B' := ⟨hC, hCB'.symm⟩
  have hB'ψA' : B' ∈ psiSet R A' := ⟨hB', h5⟩
  have hB'C : ⁅B', C⁆ = A := by rw [Subgroup.commutator_comm, h4]
  obtain ⟨w₁, hw₁, hw₁1⟩ := hR.exists_ne_one hC
  obtain ⟨θ₁, hθ₁, hθ₁e, hθ₁C, hθ₁B, hθ₁C', hθ₁B'⟩ :=
    exists_natural_coords hR hiso hA hA' hAA' hlamA.1 hCψA' φ₁ hφ₁ hφ₁' hw₁ hw₁1
  rw [h2] at hθ₁B hθ₁B'
  obtain ⟨θ₂, hθ₂, hθ₂e, hθ₂C, hθ₂A, hθ₂C', -⟩ :=
    exists_natural_coords hR hiso hB hB' hBB' hlamB.2 hCψB' φ₂ hφ₂ hφ₂' (hθ₁C 1)
      (by rw [hθ₁e]; exact hw₁1)
  rw [hB'C] at hθ₂A
  obtain ⟨t₀, ht₀⟩ := exists_aligned (xA := upPar φ₁) (xB := fun s => θ₁ ![0, s])
    (xC := fun s => θ₁ ![s, 0]) (yA := fun s => θ₂ ![0, s]) (yB := upPar φ₂)
    (yC := fun s => θ₂ ![s, 0]) (yB' := lowPar φ₂) (injective_left hθ₁)
    (fun r => hR.inv_eq hC (hθ₁C r))
    (fun t s => by simpa using commutatorElement_upPar hθ₁ t ![0, s])
    (fun t s => by simpa using commutatorElement_upPar hθ₂ t ![0, s])
    (fun t s => by simpa using commutatorElement_lowPar hθ₂ t ![s, 0])
    (fun s => exists_upPar_eq hφ₁ le_sup_left (hθ₂A s))
    (fun t => hθ₁B' _ (upPar_mem hφ₂ t)) (fun r => hθ₁C' _ (hθ₂C r))
    (fun r => hθ₂C' _ (hθ₁C r)) hθ₂e
  have hw'B' : lowPar φ₂ t₀ ∈ B' := lowPar_mem hφ₂' t₀
  have hw'1 : lowPar φ₂ t₀ ≠ 1 := by
    intro h
    have h' := ht₀ 1
    rw [h, commutatorElement_one_left, ← upPar_zero φ₁] at h'
    exact one_ne_zero (upPar_injective φ₁ h').symm
  obtain ⟨θ₃, hθ₃, hθ₃e, hθ₃B', hθ₃C', hθ₃B'', hθ₃C''⟩ :=
    exists_natural_coords hR hiso hA hA' hAA' hlamA.2 hB'ψA' φ₁ hφ₁ hφ₁' hw'B' hw'1
  have hf : ∀ t s, ⁅θ₃ ![t, 0], θ₁ ![s, 0]⁆ = upPar φ₁ (t * s) := by
    intro t s
    by_cases ht : t = 0
    · rw [ht, map_vec_zero hθ₃, commutatorElement_one_left, zero_mul, upPar_zero]
    set u := Units.mk0 t ht
    have e₁ : θ₃ ![t, 0] = torPar φ₁ u * lowPar φ₂ t₀ * (torPar φ₁ u)⁻¹ := by
      rw [← hθ₃e, torPar_conj hθ₃]
      congr 1
      ext i
      fin_cases i <;> simp [u]
    have e₂ : θ₁ ![s, 0] = torPar φ₁ u * θ₁ ![t⁻¹ * s, 0] * (torPar φ₁ u)⁻¹ := by
      rw [torPar_conj hθ₁]
      congr 1
      ext i
      fin_cases i <;> simp [u, ht]
    rw [e₁, e₂, commutatorElement_conj, ht₀, torPar_conj_upPar]
    congr 1
    simp only [u, Units.val_mk0]
    field_simp
  have hg : ∀ t s, ⁅θ₁ ![0, t], θ₃ ![0, s]⁆ = lowPar φ₁ (t * s) := by
    intro t s
    have h := congrArg (fun g => weylPar φ₁ * g * (weylPar φ₁)⁻¹) (hf s t)
    simp only [← commutatorElement_conj, weylPar_conj hθ₃, weylPar_conj hθ₁,
      weylPar_conj_upPar] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [← commutatorElement_inv, h, hR.inv_eq hA' (lowPar_mem hφ₁' _), mul_comm]
  have hrange : ∀ {f : F → G} {H : Subgroup G}, (∀ s, f s ∈ H) → (∀ h ∈ H, ∃ s, f s = h) →
      Set.range f = (H : Set G) := fun hf hH => Set.Subset.antisymm
    (Set.range_subset_iff.2 hf) fun h hh => hH h hh
  refine ⟨upPar φ₁, fun s => θ₁ ![0, s], fun s => θ₁ ![s, 0], lowPar φ₁,
    fun s => θ₃ ![s, 0], fun s => θ₃ ![0, s], rfl, rfl,
    hrange (upPar_mem hφ₁) fun _ h => exists_upPar_eq hφ₁ le_sup_left h,
    hrange hθ₁B hθ₁B', hrange hθ₁C hθ₁C',
    hrange (lowPar_mem hφ₁') fun _ h => exists_lowPar_eq hφ₁' le_sup_right h,
    hrange hθ₃B' hθ₃B'', hrange hθ₃C' hθ₃C'',
    upPar_add φ₁, map_vec_add_right hθ₁, map_vec_add_left hθ₁, lowPar_add φ₁,
    map_vec_add_left hθ₃, map_vec_add_right hθ₃,
    fun s t => by simpa using commutatorElement_upPar hθ₁ s ![0, t],
    fun s t => by simpa using commutatorElement_lowPar hθ₁ s ![t, 0],
    fun s t => by simpa using commutatorElement_upPar hθ₃ s ![0, t],
    fun s t => by simpa using commutatorElement_lowPar hθ₃ s ![t, 0], hf, hg⟩

end FrameSL3

theorem exists_hom_SL3 [Finite G] {R : Set (Subgroup G)} (hR : IsRootClass R)
    (hiso : NoIsolated R) {A B A' B' : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hA' : A' ∈ R)
    (hB' : B' ∈ R) (hAB : Special R A B) (hAA' : Opposite A A') (hBB' : Opposite B B')
    (h1 : Commuting A' B) (h2 : ⁅A', ⁅A, B⁆⁆ = B) (h3 : Commuting A B')
    (h4 : ⁅⁅A, B⁆, B'⁆ = A) (h5 : Special R A' B') {n : ℕ} (hq : Nat.card A = 2 ^ n) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 n) →* G,
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (Pi.single (α₁ (GaloisField 2 n)) 1)).map ψ = A ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (Pi.single (α₂ (GaloisField 2 n)) 1)).map ψ = B ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup (fun _ => 1)).map ψ = ⁅A, B⁆ ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (-Pi.single (α₁ (GaloisField 2 n)) 1)).map ψ = A' ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup
        (-Pi.single (α₂ (GaloisField 2 n)) 1)).map ψ = B' ∧
      ((SpecialLinear.rootDatum 2 (GaloisField 2 n)).rootGroup (-fun _ => 1)).map ψ =
        ⁅A', B'⁆ ∧
      ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 n)) ∧
      ψ.range = A ⊔ A' ⊔ (B ⊔ B') := by
  obtain ⟨n₁, -, hq₁, φ₁, hφ₁, hφ₁'⟩ := hAA'.exists_mulEquiv_SL2' hR hA
  obtain rfl : n₁ = n := Nat.pow_right_injective le_rfl (hq₁.symm.trans hq)
  obtain ⟨n₂, -, hq₂, φ₂, hφ₂, hφ₂'⟩ := hBB'.exists_mulEquiv_SL2' hR hB
  obtain rfl : n₂ = n₁ :=
    Nat.pow_right_injective le_rfl (hq₂.symm.trans ((hR.card_eq hB hA).trans hq₁))
  obtain ⟨xA, xB, xC, xA', xB', xC', -, -, rA, rB, rC, rA', rB', rC', aA, aB, aC, aA', aB', aC',
    r₁, r₂, r₃, r₄, r₅, r₆⟩ :=
    FrameSL3.exists_coords hR hiso hA hB hA' hB' hAB hAA' hBB' h1 h2 h3 h4 h5 φ₁ hφ₁ hφ₁' φ₂
      hφ₂ hφ₂'
  have mem : ∀ {f : GaloisField 2 n₂ → G} {H : Subgroup G}, Set.range f = (H : Set G) →
      ∀ s, f s ∈ H := fun hf s => by
    rw [← SetLike.mem_coe, ← hf]
    exact ⟨s, rfl⟩
  obtain ⟨ψ, hψ⟩ := FrameSL3.exists_hom_of_steinberg
    (FrameSL3.fam_add aA aB aC aA' aB' aC')
    (FrameSL3.fam_comm aA aB aC aA' aB' aC'
      (fun s t => (hAB.2.1 _ (mem rC t) _ (mem rA s)).symm)
      (fun s t => h3 _ (mem rA s) _ (mem rB' t))
      (fun s t => (hAB.2.2 _ (mem rC t) _ (mem rB s)).symm)
      (fun s t => (h1 _ (mem rA' t) _ (mem rB s)).symm)
      (fun s t => (h5.2.1 _ (mem rC' t) _ (mem rA' s)).symm)
      (fun s t => (h5.2.2 _ (mem rC' t) _ (mem rB' s)).symm) r₁ r₂ r₃ r₄ r₅ r₆)
  have e₀₁ := FrameSL3.map_rootSubgroup_eq _ (hψ 0 1 (by decide)) rA
  have e₁₂ := FrameSL3.map_rootSubgroup_eq _ (hψ 1 2 (by decide)) rB
  have e₁₀ := FrameSL3.map_rootSubgroup_eq _ (hψ 1 0 (by decide)) rA'
  have e₂₁ := FrameSL3.map_rootSubgroup_eq _ (hψ 2 1 (by decide)) rB'
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FrameSL3.rootGroup_α₁, e₀₁]
  · rw [FrameSL3.rootGroup_α₂, e₁₂]
  · rw [FrameSL3.rootGroup_α₁₂]
    exact FrameSL3.map_rootSubgroup_eq _ (hψ 0 2 _) rC
  · rw [FrameSL3.rootGroup_neg_α₁, e₁₀]
  · rw [FrameSL3.rootGroup_neg_α₂, e₂₁]
  · rw [FrameSL3.rootGroup_neg_α₁₂]
    exact FrameSL3.map_rootSubgroup_eq _ (hψ 2 0 _) rC'
  ·
    refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (SpecialLinear.isQuasisimple 2 _ le_rfl) ?_
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
    rw [← SetLike.mem_coe, ← rA] at ha
    obtain ⟨s, rfl⟩ := ha
    exact ⟨_, (hψ 0 1 (by decide) s).trans_ne ha1⟩
  ·
    have e : ∀ f : Fin 2 → Subgroup G, ⨆ k, f k = f 0 ⊔ f 1 := fun f => le_antisymm
      (iSup_le fun k => by fin_cases k; exacts [le_sup_left, le_sup_right])
      (sup_le (le_iSup f 0) (le_iSup f 1))
    rw [MonoidHom.range_eq_map, ← SpecialLinear.iSup_fundamentalRootSubgroup_eq_top,
      Subgroup.map_iSup, e]
    simp only [iSup_bool_eq, Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) e₀₁ e₁₀) (congrArg₂ (· ⊔ ·) e₁₂ e₂₁)

end CFSG.Timmesfeld.ARS
