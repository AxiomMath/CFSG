module

public import CFSG.RankThree.PartOne.TCU.IsoLine
public import CFSG.RankThree.PartOne.TCP.ThreeComp
public import CFSG.RankThree.PartOne.S11d.PSUDescent
public import CFSG.RankThree.PartOne.TCU.TwistFix

public section

namespace CFSG.RankThree.PartOne.TCU

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.OddIso
open scoped commutatorElement

variable {F : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

theorem eq_one_of_pow_three_of_pow_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {μ : K}
    (h3 : μ ^ 3 = 1) (hpμ : μ ^ p = 1) : μ = 1 := by
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).mpr (by omega)
  have := pow_gcd_eq_one.mpr ⟨h3, hpμ⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem idForm_smul_smul {n : ℕ} (c : K) (a b : Fin n → K) :
    idForm h n (c • a) (c • b) = h.bar c * c * idForm h n a b := by
  rw [map_smulₛₗ (idForm h n) c a, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
    mul_assoc]

theorem pow_apply_eigen {A : GL (Fin 3) K} {μ : K} {w : Fin 3 → K} (hw : linOf A w = μ • w)
    (k : ℕ) : (linOf A ^ k) w = μ ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, hw, map_smul, ih, smul_smul, pow_succ]
    ring_nf

theorem exists_twistSetup {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpQ : p ∣ 2 ^ F + 1)
    (hq : 4 ≤ 2 ^ F) {A : SUn h 3} (hAp : A ^ p = 1) (hA1 : A ≠ 1) {w : Fin 3 → K} {μ : K}
    (hw0 : w ≠ 0) (hww : idForm h 3 w w = 0) (hAw : linOf (A : GL (Fin 3) K) w = μ • w) :
    ∃ u : Module.End K (Fin 3 → K), TwistSetup h 3 p A u μ := by
  classical
  have hfin : Finite K := h.finite
  have hchar : CharP K 2 := h.charP
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hAp' : linOf (A : GL (Fin 3) K) ^ p = 1 := by
    rw [← linOf_pow, ← Subgroup.coe_pow, hAp]
    exact linOf_one
  have hμ0 : μ ≠ 0 := by
    intro hμ
    apply hw0
    have h0 : linOf (A : GL (Fin 3) K) w = 0 := by rw [hAw, hμ, zero_smul]
    have h1 := (linOf_inv_apply A w).symm
    rw [h0, map_zero] at h1
    exact h1
  have hμp : μ ^ p = 1 := by
    have h1 := pow_apply_eigen hAw p
    rw [hAp', Module.End.one_apply] at h1
    have h2 : (μ ^ p - 1) • w = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0)
  have hNμ : h.bar μ * μ = 1 := by
    obtain ⟨k, hk⟩ := hpQ
    have h1 : μ ^ (2 ^ F + 1) = 1 := by rw [hk, pow_mul, hμp, one_pow]
    rw [h.bar_apply, ← pow_succ]
    exact h1
  set u : Module.End K (Fin 3 → K) := μ⁻¹ • linOf (A : GL (Fin 3) K) with hu
  have hAc : linOf (A : GL (Fin 3) K) = μ • u := by
    rw [hu, smul_inv_smul₀ hμ0]
  have hiso : ∀ v v', idForm h 3 (u v) (u v') = idForm h 3 v v' := by
    intro v v'
    have h1 := linOf_isom_A h A.2 v v'
    have h2 : h.bar μ⁻¹ * μ⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, hNμ, inv_one]
    rw [hu, LinearMap.smul_apply, LinearMap.smul_apply, idForm_smul_smul, h2, one_mul, h1]
  have hup : u ^ p = 1 := by
    rw [hu, smul_pow, hAp', inv_pow, hμp, inv_one, one_smul]
  have hwV₁ : w ∈ LinearMap.ker (u - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hu,
      LinearMap.smul_apply, hAw, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hsep := fixSpace_sep (idForm_separatingLeft h 3) hiso hodd hup
  have hge : 2 ≤ Module.finrank K (LinearMap.ker (u - 1)) := by
    by_contra hlt
    push Not at hlt
    have hne : LinearMap.ker (u - 1) ≠ ⊥ := fun hb => hw0 (by
      have := hwV₁
      rw [hb, Submodule.mem_bot] at this
      exact this)
    have h1 : 1 ≤ Module.finrank K (LinearMap.ker (u - 1)) :=
      Submodule.one_le_finrank_iff.mpr hne
    have h1' : Module.finrank K (LinearMap.ker (u - 1)) = 1 := by omega
    have hspan : LinearMap.ker (u - 1) = Submodule.span K {w} :=
      (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem w _).mpr hwV₁)
        ((finrank_span_singleton hw0).trans h1'.symm)).symm
    have h0 := hsep ⟨w, hwV₁⟩ (fun y => by
      have hy : (y : Fin 3 → K) ∈ Submodule.span K {w} := by
        rw [← hspan]
        exact y.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
      change idForm h 3 w (y : Fin 3 → K) = 0
      rw [← hc, map_smul, hww, smul_zero])
    exact hw0 (congrArg Subtype.val h0)
  have hle2 : Module.finrank K (LinearMap.ker (u - 1)) ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have hle3 := Submodule.finrank_le (LinearMap.ker (u - 1))
    rw [Module.finrank_fin_fun] at hle3
    have h3 : Module.finrank K (LinearMap.ker (u - 1)) = 3 := by omega
    have htop : LinearMap.ker (u - 1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
    have hu1 : ∀ v, linOf (A : GL (Fin 3) K) v = μ • v := by
      intro v
      have hv : v ∈ LinearMap.ker (u - 1) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      rw [hAc, LinearMap.smul_apply, hv]
    have hdet : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = μ ^ 3 := by
      have h1 : linOf (A : GL (Fin 3) K) = μ • LinearMap.id :=
        LinearMap.ext fun v => by rw [hu1 v]; rfl
      rw [← LinearMap.det_toLin' ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)]
      change LinearMap.det (linOf (A : GL (Fin 3) K)) = _
      rw [h1, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun]
    have hdet1 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      ((mem_gramSU_iff_unitary h).mp A.2).2
    have hμ1 : μ = 1 :=
      eq_one_of_pow_three_of_pow_prime hp hp5 (by rw [← hdet, hdet1]) hμp
    apply hA1
    apply Subtype.ext
    apply linOf_injective
    rw [Subgroup.coe_one, linOf_one]
    exact LinearMap.ext fun v => by rw [hu1 v, hμ1, one_smul]; rfl
  have hfinR : Module.finrank K (LinearMap.range (u - 1)) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker (u - 1)
    rw [Module.finrank_fin_fun] at this
    omega
  have hRne : LinearMap.range (u - 1) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hfinR
    exact absurd hfinR (by norm_num)
  obtain ⟨w₀, hw₀R, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
  have hRspan : LinearMap.range (u - 1) = Submodule.span K {w₀} :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem w₀ _).mpr hw₀R)
      ((finrank_span_singleton hw₀0).trans hfinR.symm)).symm
  have hcyc : IsCyclicOn u (LinearMap.range (u - 1)) := by
    refine ⟨w₀, hw₀R, ?_⟩
    rw [hRspan]
    refine Submodule.span_le.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    simpa using pow_mem_cyc u w₀ 0
  exact ⟨u, ⟨hodd, hq, hμ0, hAc, hiso, hup, hcyc, hge⟩⟩

theorem psu3_survivor_component {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpQ : p ∣ 2 ^ F + 1)
    (hq : 4 ≤ 2 ^ F) {x : PSUn h 3} (hxp : x ^ p = 1) (hx1 : x ≠ 1) {S : Subgroup (PSUn h 3)}
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S) (hxS : x ∈ Subgroup.normalizer (S : Set (PSUn h 3))) :
    ∃ D : Subgroup (PSUn h 3), CFSG.IsQuasisimple ↥D ∧
      D ≤ Subgroup.centralizer ({x} : Set (PSUn h 3)) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (PSUn h 3)), ∀ d ∈ D, g * d * g⁻¹ ∈ D) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (PSUn h 3)),
        ∀ g' ∈ Subgroup.centralizer ({x} : Set (PSUn h 3)), ⁅g, g'⁆ ∈ D) ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set (PSUn h 3)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ D) := by
  classical
  have hfin : Finite K := h.finite
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ 3 = 1 → c ^ p = 1 → c = 1 := by
    intro c _ hc3 hcp
    have h3 : (c : K) ^ 3 = 1 := by simpa using congrArg (fun u : Kˣ => (u : K)) hc3
    have hp' : (c : K) ^ p = 1 := by simpa using congrArg (fun u : Kˣ => (u : K)) hcp
    exact Units.ext (by rw [Units.val_one]; exact eq_one_of_pow_three_of_pow_prime hp hp5 h3 hp')
  obtain ⟨A, hAp, rfl⟩ := exists_lift_pow h (by norm_num : 1 ≤ 3) hZp hxp
  have hA1 : A ≠ 1 := fun hA => hx1 (by rw [hA]; exact map_one (piSU h 3))
  obtain ⟨w, μ, hw0, hww, hAw⟩ := exists_isotropic_eigenvector h hS1 hS2 hxS
  obtain ⟨u, S'⟩ := exists_twistSetup h hp hp5 hpQ hq hAp hA1 hw0 hww hAw
  exact psu_core hZp (by norm_num) S' hAp

end CFSG.RankThree.PartOne.TCU

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.TCU
open scoped commutatorElement

set_option linter.unusedVariables false in
theorem threeCompBL_PSU_three (T : Type) [Group T] [Finite T] (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hLR2 : LocalRankLeTwo p T) (h2 : 2 ≤ CFSG.pRank p T) (f₀ : ℕ) (hf₀ : 1 ≤ f₀)
    (hM : LieModel T .PSU 3 2 (p * f₀)) (hpQ : p ∣ 2 ^ (p * f₀) + 1) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (hLRA : LocalRankAut p T α)
    (hX : FixModel .PSU 3 f₀ α) (x : T) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hαx : α x = x)
    (S : Subgroup T) (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S) (hSα : ∀ g ∈ S, α g ∈ S)
    (hxS : x ∈ Subgroup.normalizer (S : Set T)) :
    ∃ D : Subgroup T, IsComponentOf (Subgroup.centralizer ({x} : Set T)) D ∧
      (∀ g ∈ D, α g ∈ D) ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set T), α g = g → (∃ k : ℕ, orderOf g = 2 ^ k) →
        g ∈ D := by
  obtain ⟨K, _, h, φ, σ, hn3, hσ, hZp, hφα⟩ :=
    exists_fieldAut_model_PSU hp hp5 hM hLR2 α hαp hαinn hLRA hX
  have hF5 : 5 ≤ p * f₀ := by nlinarith
  have hq : 4 ≤ 2 ^ (p * f₀) :=
    calc 4 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) hF5
  have hxp' : (φ x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hx1' : φ x ≠ 1 := fun e => hx1 (φ.injective (by rw [e, map_one]))
  have hS1' : S.map φ.toMonoidHom ≠ ⊥ := fun hb =>
    hS1 ((Subgroup.map_eq_bot_iff_of_injective S φ.injective).mp hb)
  have hS2' : IsPGroup 2 ↥(S.map φ.toMonoidHom) := hS2.map φ.toMonoidHom
  have hxS' := normalizer_map_of_mulEquiv φ hxS
  obtain ⟨D, hDq, hDC, hDn, hDc, hD2⟩ :=
    psu3_survivor_component h hp hp5 hpQ hq hxp' hx1' hS1' hS2' hxS'
  exact component_of_commutator_data φ α hαx hDq hDC hDn hDc hD2

end CFSG.RankThree.PartOne.TCX
