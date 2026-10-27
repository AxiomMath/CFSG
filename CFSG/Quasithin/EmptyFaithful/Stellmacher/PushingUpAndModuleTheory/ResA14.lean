module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA10

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X K V₀ : Subgroup G} {c : G}
  (hX : X ≤ Subgroup.normalizer (K : Set G)) (hKd : KData K V₀ c)
  (ψ : ↥X →* Perm (Fin 5)) (hψs : Function.Surjective ψ)
  (hker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ K)

section Core

include hX hKd hψs hker

theorem normClosure_isElemAbelian : IsElemAbelian 2 (normClosure X V₀) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact normClosure_central hX hKd a.2 (normClosure_le_K hX hKd b.2)
  · rw [pow_two]; exact normClosure_sq hX hKd hx

theorem exists_B (hK2 : IsPGroup 2 K) (hcX : c ∈ X) :
    ∃ B : ↥(normClosure X V₀) →* orth.W, Function.Injective B ∧ Function.Surjective B ∧
      ∀ (y : ↥X) (n : ↥(normClosure X V₀)),
        B ((isSec_normClosure hX hKd).conjN y n) = orth.act (ψ y) (B n) := by
  have hs := isSec_normClosure hX hKd
  obtain ⟨e⟩ := normModel_iso_orth hX hKd ψ hψs hker hK2 hcX
  let B : ↥(normClosure X V₀) →* orth.W := e.toMulEquiv.toMonoidHom.comp hs.proj
  refine ⟨B, ?_, e.toMulEquiv.surjective.comp hs.proj_surjective, ?_⟩
  · intro a b hab
    have h1 : hs.proj a = hs.proj b := e.toMulEquiv.injective hab
    rw [hs.proj_eq_proj_iff] at h1
    have h2 : (a : G)⁻¹ * (b : G) = 1 := by simpa using h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  · intro y n
    have h := e.map_act (ψ y) (hs.proj n)
    have h2 := secModule_act_proj hs ψ hψs (ker_le_cSec_normClosure hX hKd ψ hψs hker) y n
    exact (congrArg e.toMulEquiv h2).symm.trans h

theorem normClosure_inf_centralizer (hK2 : IsPGroup 2 K) (hcX : c ∈ X) :
    normClosure X V₀ ⊓ Subgroup.centralizer (conjClosure X c : Set G) = ⊥ := by
  obtain ⟨B, hBinj, -, hBact⟩ := exists_B hX hKd ψ hψs hker hK2 hcX
  have hcne := psi_c_ne_one hX hKd ψ hψs hker hK2 hcX
  rw [eq_bot_iff]
  rintro x ⟨hxN, hxC⟩
  rw [Subgroup.mem_bot]
  have hfix : B ⟨x, hxN⟩ ∈ fixW orth (alternatingGroup (Fin 5)) := by
    intro σ hσ
    obtain ⟨l, hl, hlσ⟩ := alt5_le_map_conjClosure ψ hψs hcX hKd.c3 hcne hσ
    rw [← hlσ, ← hBact]
    congr 1
    apply Subtype.ext
    show (l : G) * x * (l : G)⁻¹ = x
    have := Subgroup.mem_centralizer_iff.mp hxC l hl
    calc (l : G) * x * (l : G)⁻¹ = (l * x) * (l : G)⁻¹ := by group
      _ = (x * l) * (l : G)⁻¹ := by rw [← this]
      _ = x := by group
  rw [fixW_orth_alt5, Subgroup.mem_bot] at hfix
  have := hBinj (hfix.trans (map_one B).symm)
  exact congrArg Subtype.val this

theorem commutator_eq_normClosure (hcX : c ∈ X) :
    ⁅K, conjClosure X c⁆ = normClosure X V₀ :=
  le_antisymm (commutator_le_normClosure hX hKd hcX) (normClosure_le_commutator hX hKd)

theorem K_eq_sup (hK2 : IsPGroup 2 K) (hcX : c ∈ X) :
    K = normClosure X V₀ ⊔ (K ⊓ Subgroup.centralizer (conjClosure X c : Set G)) := by
  refine le_antisymm (fun q hq => ?_) (sup_le (normClosure_le_K hX hKd) inf_le_left)
  obtain ⟨y, hy, o, ho, rfl⟩ := exists_decomp hX hKd ψ hψs hker hK2 hcX hq
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left ho)

theorem commutator_K_le (_hcX : c ∈ X) :
    ⁅K, K⁆ ≤ K ⊓ Subgroup.centralizer (conjClosure X c : Set G) := by
  rw [Subgroup.commutator_le]
  intro k hk k' hk'
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  · exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
  · exact (derived_commute hX hKd hk hk' hl).symm

theorem normalizer_L1 (_hcX : c ∈ X) :
    X ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (conjClosure X c : Set G) : Subgroup G) :
      Set G) := by
  have key : ∀ g ∈ X, ∀ y ∈ K ⊓ Subgroup.centralizer (conjClosure X c : Set G),
      g * y * g⁻¹ ∈ K ⊓ Subgroup.centralizer (conjClosure X c : Set G) := by
    intro g hg y hy
    refine ⟨conj_mem_K hX hKd hy.1 hg, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g ∈ conjClosure X c := by
      have := conj_mem_conjClosure hl (X.inv_mem hg)
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hy.2 _ hl'
    calc l * (g * y * g⁻¹) = g * ((g⁻¹ * l * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * l * g)) * g⁻¹ := by rw [this]
      _ = (g * y * g⁻¹) * l := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (X.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem commutator_N_c (_hcX : c ∈ X) : ⁅normClosure X V₀, Subgroup.zpowers c⁆ = V₀ := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro n hn t ht
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ht)
    have hnK : n ∈ K := normClosure_le_K hX hKd hn
    have h1 := V₀.inv_mem (comm_pow_mem hX hKd m hnK)
    rw [← hm]
    have : ⁅n, c ^ m⁆ = (c ^ m * n * (c ^ m)⁻¹ * n⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [this]; exact h1
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hKd.V_comm v hv
    have hw2 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hKd.V_sq w hw)
    have := Subgroup.commutator_mem_commutator (V0_le_normClosure hw : w ∈ normClosure X V₀)
      (Subgroup.mem_zpowers c)
    have e : ⁅w, c⁆ = w * (c * w * c⁻¹) := by
      rw [commutatorElement_def]
      calc w * c * w⁻¹ * c⁻¹ = w * c * w⁻¹ * c⁻¹ := rfl
        _ = _ := by rw [hw2]; group
    rwa [e] at this

theorem commutator_K_c (hcX : c ∈ X) : ⁅K, Subgroup.zpowers c⁆ = V₀ := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro n hn t ht
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ht)
    have h1 := V₀.inv_mem (comm_pow_mem hX hKd m hn)
    rw [← hm]
    have : ⁅n, c ^ m⁆ = (c ^ m * n * (c ^ m)⁻¹ * n⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [this]; exact h1
  · exact (commutator_N_c hX hKd ψ hψs hker hcX).symm.le.trans
      (Subgroup.commutator_mono (normClosure_le_K hX hKd) le_rfl)

end Core

end CFSG.Quasithin.F53
