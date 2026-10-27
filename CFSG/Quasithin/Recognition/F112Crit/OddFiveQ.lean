module

public import CFSG.Quasithin.Recognition.F112Crit.RigidLocal
public import CFSG.Quasithin.Recognition.F112Crit.BenderCartan
public import CFSG.Quasithin.Recognition.F112Crit.CoprimeCentralizer

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)
open Subgroup

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

section Index

variable [Finite G]

theorem pow_relIndex_mem_of_le_normalizer {B H : Subgroup G} (hBH : B ≤ H)
    (hHB : H ≤ normalizer (B : Set G)) {x : G} (hx : x ∈ H) : x ^ B.relIndex H ∈ B := by
  haveI := (normal_subgroupOf_iff_le_normalizer hBH).mpr hHB
  have h := pow_index_mem (B.subgroupOf H) (⟨x, hx⟩ : ↥H)
  rw [mem_subgroupOf, SubgroupClass.coe_pow] at h
  exact h

theorem relIndex_sup_dvd_card_of_le_normalizer' {A N : Subgroup G}
    (h : A ≤ normalizer (N : Set G)) : N.relIndex (A ⊔ N) ∣ Nat.card A := by
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer h
  rw [C5.card_eq_card_mul_relIndex (le_sup_right : N ≤ A ⊔ N), mul_assoc,
    mul_comm (Nat.card A)] at h1
  exact ⟨_, (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm⟩

theorem exists_pow_two_pow_mem_of_sup {B U Q : Subgroup G} (hU : IsPGroup 2 U)
    (hQ : IsPGroup 2 Q) (hUB : U ≤ normalizer (B : Set G)) (hQB : Q ≤ normalizer (B : Set G))
    (hQUB : Q ≤ normalizer ((U ⊔ B : Subgroup G) : Set G)) :
    ∃ m : ℕ, ∀ x ∈ Q ⊔ (U ⊔ B), x ^ 2 ^ m ∈ B := by
  obtain ⟨a, ha⟩ := hU.exists_card_eq
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  have h1 := relIndex_sup_dvd_card_of_le_normalizer' hUB
  have h2 := relIndex_sup_dvd_card_of_le_normalizer' hQUB
  rw [ha] at h1
  rw [hb] at h2
  have hdvd : B.relIndex (Q ⊔ (U ⊔ B)) ∣ 2 ^ (a + b) := by
    rw [← Subgroup.relIndex_mul_relIndex B (U ⊔ B) (Q ⊔ (U ⊔ B)) le_sup_right le_sup_right,
      pow_add]
    exact mul_dvd_mul h1 h2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨m, fun x hx => ?_⟩
  rw [← hm]
  exact pow_relIndex_mem_of_le_normalizer (le_sup_right.trans le_sup_right)
    (sup_le hQB (sup_le hUB le_normalizer)) hx

end Index

section Generic

variable {G₀ G₁ G₂ : Subgroup G} [Finite G]

theorem le_sup_ballStab_of_rigidAt {μ δ : CosetGeom G₀ G₁ G₂} {L U Q : Subgroup G}
    (hR : RigidAt μ δ L) (hC : CartanLocal μ L) (hδ : δ ∈ nbrs μ) (hLμ : L ≤ stab μ)
    (hLn : stab μ ≤ normalizer (L : Set G)) (hUL : U ≤ L) (hU2 : IsPGroup 2 U)
    (hUδ : U ≤ stab δ)
    (hUtr : ∀ ε ∈ nbrs μ, ∀ ε' ∈ nbrs μ, ε ≠ δ → ε' ≠ δ → ∃ g : ↥G₀, (g : G) ∈ U ∧ g • ε = ε')
    (hUn : stab μ ⊓ stab δ ≤ normalizer ((U ⊔ ballStab 1 μ : Subgroup G) : Set G))
    (hQ2 : IsPGroup 2 Q) (hQ : Q ≤ stab μ ⊓ stab δ)
    (hQn : L ⊓ stab δ ≤ normalizer (Q : Set G)) :
    Q ≤ U ⊔ ballStab 1 μ := by
  obtain ⟨δ', hδ', hne, hrig⟩ := hR
  have hBn : stab μ ≤ normalizer (ballStab 1 μ : Set G) := CosetGeom.le_normalizer_ballStab 1 μ
  have hUμ : U ≤ stab μ := hUL.trans hLμ
  have hQμ : Q ≤ stab μ := hQ.trans inf_le_left
  have hQδ : Q ≤ stab δ := hQ.trans inf_le_right
  obtain ⟨m, hm⟩ := exists_pow_two_pow_mem_of_sup hU2 hQ2 (hUμ.trans hBn) (hQμ.trans hBn)
    (fun x hx => hUn (mem_inf.mpr ⟨hQμ hx, hQδ hx⟩))
  intro g hg
  set g' : ↥G₀ := ⟨g, CosetGeom.stab_le μ (hQμ hg)⟩ with hg'
  have hgμ : g' • μ = μ := CosetGeom.smul_eq_of_mem_stab (hQμ hg)
  have hgδ : g' • δ = δ := CosetGeom.smul_eq_of_mem_stab (hQδ hg)
  have hgδ' : g' • δ' ∈ nbrs μ := by
    have h := (CosetGeom.smul_adj g').mpr hδ'
    rwa [hgμ] at h
  have hgne : g' • δ' ≠ δ := fun h => hne (smul_left_cancel g' (h.trans hgδ.symm))
  obtain ⟨u, hu, hud⟩ := hUtr δ' hδ' (g' • δ') hgδ' hne hgne
  obtain ⟨c, hc⟩ : ∃ c : G, c = (u : G)⁻¹ * g := ⟨_, rfl⟩
  have hcμ : c ∈ stab μ := hc ▸ mul_mem (inv_mem (hUμ hu)) (hQμ hg)
  have hcδ : c ∈ stab δ := hc ▸ mul_mem (inv_mem (hUδ hu)) (hQδ hg)
  have hcδ' : c ∈ stab δ' := by
    have h : (u⁻¹ * g') • δ' = δ' := by rw [mul_smul, ← hud, inv_smul_smul]
    rw [hc]
    exact CosetGeom.mem_stab_of_smul_eq h
  have hcH : c ∈ Q ⊔ (U ⊔ ballStab 1 μ) :=
    hc ▸ mul_mem (mem_sup_right (mem_sup_left (inv_mem hu))) (mem_sup_left hg)
  have hcd : ∀ d ∈ L ⊓ stab δ ⊓ stab δ', c * d * c⁻¹ * d⁻¹ ∈ ballStab 1 μ := by
    intro d hd
    obtain ⟨hd1, hdδ'⟩ := mem_inf.mp hd
    obtain ⟨hdL, hdδ⟩ := mem_inf.mp hd1
    have hdQ := hQn (mem_inf.mpr ⟨hdL, hdδ⟩)
    have hdM := hUn (mem_inf.mpr ⟨hLμ hdL, hdδ⟩)
    have hdH : ∀ x ∈ Q ⊔ (U ⊔ ballStab 1 μ), d * x * d⁻¹ ∈ Q ⊔ (U ⊔ ballStab 1 μ) := by
      have hle : Q ⊔ (U ⊔ ballStab 1 μ) ≤
          (Q ⊔ (U ⊔ ballStab 1 μ)).comap (MulAut.conj d).toMonoidHom :=
        sup_le (fun x hx => mem_comap.mpr (mem_sup_left ((mem_normalizer_iff.mp hdQ x).mp hx)))
          (fun x hx => mem_comap.mpr (mem_sup_right ((mem_normalizer_iff.mp hdM x).mp hx)))
      exact fun x hx => mem_comap.mp (hle hx)
    have hkH : c * d * c⁻¹ * d⁻¹ ∈ Q ⊔ (U ⊔ ballStab 1 μ) := by
      have e : c * d * c⁻¹ * d⁻¹ = c * (d * c⁻¹ * d⁻¹) := by group
      rw [e]
      exact mul_mem hcH (hdH _ (inv_mem hcH))
    have hkA : c * d * c⁻¹ * d⁻¹ ∈ L ⊓ stab δ ⊓ stab δ' := by
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mul_mem ((mem_normalizer_iff.mp (hLn hcμ) d).mp hdL) (inv_mem hdL)
      · exact mul_mem (mul_mem (mul_mem hcδ hdδ) (inv_mem hcδ)) (inv_mem hdδ)
      · exact mul_mem (mul_mem (mul_mem hcδ' hdδ') (inv_mem hcδ')) (inv_mem hdδ')
    exact mem_of_pow_two_pow_mem_of_two_elt (hC.two_elt δ hδ δ' hδ' hne.symm) hkA (hm _ hkH)
  have hcB : c ∈ ballStab 1 μ :=
    hrig c (mem_inf.mpr ⟨mem_inf.mpr ⟨hcμ, hcδ⟩, hcδ'⟩) ⟨m, hm c hcH⟩ hcd
  have e : g = (u : G) * c := by rw [hc]; group
  rw [e]
  exact mul_mem (mem_sup_left hu) (mem_sup_right hcB)

theorem mem_ballStab_of_le_sup {μ δ : CosetGeom G₀ G₁ G₂} {U Q : Subgroup G}
    (hUμ : U ≤ stab μ)
    (hUreg : ∀ g : ↥G₀, (g : G) ∈ U → ∀ ε ∈ nbrs μ, ε ≠ δ → g • ε = ε → (g : G) ∈ ballStab 1 μ)
    (hQ : Q ≤ U ⊔ ballStab 1 μ) {g : G} (hg : g ∈ Q) {δ' : CosetGeom G₀ G₁ G₂}
    (hδ' : δ' ∈ nbrs μ) (hne : δ' ≠ δ) (hfix : g ∈ stab δ') : g ∈ ballStab 1 μ := by
  have hUB : U ≤ normalizer (ballStab 1 μ : Set G) :=
    hUμ.trans (CosetGeom.le_normalizer_ballStab 1 μ)
  have hg' : g ∈ ((U ⊔ ballStab 1 μ : Subgroup G) : Set G) := hQ hg
  rw [coe_mul_of_left_le_normalizer_right U (ballStab 1 μ) hUB] at hg'
  obtain ⟨u, hu, b, hb, hub⟩ := hg'
  replace hub : u * b = g := hub
  replace hu : u ∈ U := hu
  replace hb : b ∈ ballStab 1 μ := hb
  have hadj : (graph G₀ G₁ G₂).Adj μ δ' := hδ'
  have hbδ' : b ∈ stab δ' :=
    CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hadj).le hb
  have huδ' : u ∈ stab δ' := by
    have e : u = g * b⁻¹ := by rw [← hub]; group
    rw [e]
    exact mul_mem hfix (inv_mem hbδ')
  have hu0 : u ∈ G₀ := CosetGeom.stab_le μ (hUμ hu)
  have huB := hUreg ⟨u, hu0⟩ hu δ' hδ' hne
    (CosetGeom.smul_eq_of_mem_stab (g := ⟨u, hu0⟩) huδ')
  rw [← hub]
  exact mul_mem huB hb

theorem pCoreOf_inf_ballStab_le {μ δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ nbrs μ) :
    pCoreOf 2 (stab μ) ⊓ ballStab 1 δ ≤ pCoreOf 2 (stab δ) := fun _ hx =>
  pCoreOf_mono_of_le_normalizer (CosetGeom.ballStab_le_stab 1 δ)
    (CosetGeom.le_normalizer_ballStab 1 δ)
    ((CosetGeom.pCoreOf_stab_inf_ballStab_le hδ).2 ((CosetGeom.pCoreOf_stab_inf_ballStab_le hδ).1 hx))

theorem pCoreOf_stab_le_stab {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {μ δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ nbrs μ) : pCoreOf 2 (stab δ) ≤ stab μ := by
  refine (CosetGeom.pCoreOf_stab_le_ballStab_one hyp δ).trans
    (CosetGeom.ballStab_le_stab_of_dist_le ?_)
  have hadj : (graph G₀ G₁ G₂).Adj μ δ := hδ
  rw [CosetGeom.dist_comm]
  exact (CosetGeom.dist_eq_one_iff_adj.mpr hadj).le

end Generic

section Vertex

variable {G₀ G₁ G₂ : Subgroup G}

structure BenderRigidVertex (μ : CosetGeom G₀ G₁ G₂) (L : Subgroup G) : Prop where
  bender : BenderLocal μ L
  cartan : CartanLocal μ L
  rigid : RigidLocal μ L

variable [Finite G]

theorem BenderRigidVertex.unipotent_pCoreOf {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {μ : CosetGeom G₀ G₁ G₂} {L : Subgroup G} (h : BenderRigidVertex μ L)
    {δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ nbrs μ) :
    ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧ U ≤ stab δ ∧
      (∀ ε ∈ nbrs μ, ∀ ε' ∈ nbrs μ, ε ≠ δ → ε' ≠ δ → ∃ g : ↥G₀, (g : G) ∈ U ∧ g • ε = ε') ∧
      (∀ g : ↥G₀, (g : G) ∈ U → ∀ ε ∈ nbrs μ, ε ≠ δ → g • ε = ε → (g : G) ∈ ballStab 1 μ) ∧
      stab μ ⊓ stab δ ≤ normalizer ((U ⊔ ballStab 1 μ : Subgroup G) : Set G) ∧
      pCoreOf 2 (stab δ) ≤ U ⊔ ballStab 1 μ := by
  obtain ⟨U, hUL, hU2, hUδ, hUtr, hUreg, hUn⟩ := h.bender.unipotent δ hδ
  refine ⟨U, hUL, hU2, hUδ, hUtr, hUreg, hUn, ?_⟩
  exact le_sup_ballStab_of_rigidAt (h.rigid.rigid δ hδ) h.cartan hδ h.bender.le_stab
    h.bender.normal hUL hU2 hUδ hUtr hUn (pCoreOf_isPGroup 2 _)
    (le_inf (pCoreOf_stab_le_stab hyp hδ) (pCoreOf_le 2 _))
    (inf_le_right.trans (le_normalizer_pCoreOf 2 _))

theorem BenderRigidVertex.mem_ballStab_of_mem_pCoreOf {T : Subgroup G}
    (hyp : AmalgamHyp G₀ G₁ G₂ T) {μ : CosetGeom G₀ G₁ G₂} {L : Subgroup G}
    (h : BenderRigidVertex μ L) {δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ nbrs μ) {g : G}
    (hg : g ∈ pCoreOf 2 (stab δ)) {δ' : CosetGeom G₀ G₁ G₂} (hδ' : δ' ∈ nbrs μ) (hne : δ' ≠ δ)
    (hfix : g ∈ stab δ') : g ∈ ballStab 1 μ := by
  obtain ⟨U, hUL, -, -, -, hUreg, -, hQ⟩ := h.unipotent_pCoreOf hyp hδ
  exact mem_ballStab_of_le_sup (hUL.trans h.bender.le_stab) hUreg hQ hg hδ' hne hfix

end Vertex

namespace Setting

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

theorem benderRigidVertex (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂))
    (hR : IsRigidQuot (oTwoQuot ↥L₂)) :
    BenderRigidVertex (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) (oddGen L₂) :=
  ⟨hs.benderLocal hK, hs.cartanLocal hK hC, hs.rigidLocal hK hR⟩

end Setting

end CFSG.Quasithin.F112Crit

end
