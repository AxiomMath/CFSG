module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.He42PData
public import CFSG.Quasithin.Vol2.Asc94.He42Alg

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private lemma he42pf_conj_map {Γ : Type} [Group Γ] (H : Subgroup Γ) {g c : Γ} (hg : g ∈ H)
    (hc : c ∈ (commutator ↥H).map H.subtype) : g * c * g⁻¹ ∈ (commutator ↥H).map H.subtype := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hc
  have hN : (commutator ↥H).Normal := inferInstance
  exact Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : ↥H) * x * (⟨g, hg⟩ : ↥H)⁻¹, hN.conj_mem x hx ⟨g, hg⟩, rfl⟩

private lemma he42pf_L_le {Γ : Type} [Group Γ] (H A : Subgroup Γ) (ψ : ↥H →* Equiv.Perm (Fin 5))
    (hker : ψ.ker = A.subgroupOf H) (hrange : ψ.range = alternatingGroup (Fin 5))
    (C : Subgroup Γ) (hsub : ∀ c ∈ commutator ↥H, (c : Γ) ∈ C) (hA : ∀ a ∈ A, a ∈ C)
    {l : Γ} (hl : l ∈ H) : l ∈ C := by
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  have hmem : ψ ⟨l, hl⟩ ∈ (commutator ↥H).map ψ := by
    rw [map_commutator_eq, hrange, commutator_alternatingGroup_eq_self h5, ← hrange]
    exact MonoidHom.mem_range.mpr ⟨⟨l, hl⟩, rfl⟩
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hmem
  have hk : (⟨l, hl⟩ : ↥H) * c⁻¹ ∈ ψ.ker :=
    MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hcx, mul_inv_cancel])
  rw [hker, Subgroup.mem_subgroupOf] at hk
  have key : (((⟨l, hl⟩ : ↥H) * c⁻¹ : ↥H) : Γ) * (c : Γ) = l := by simp
  have hmul := C.mul_mem (hA _ hk) (hsub c hc)
  rwa [key] at hmul

theorem HeSetup.perfect (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) {y₁ y₂ : G}
    (hY : YSpec S y₁ y₂) (hR : S.StepR y₁ y₂) (hAZ : S.StepAZ y₁ y₂) (hZ : S.StepZcomm)
    {l₁ l₂ : G} (hl : WSpec S y₁ y₂ l₁ l₂) :
    commutator ↥S.L = ⊤ := by
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = (commutator ↥S.L).map S.L.subtype := ⟨_, rfl⟩
  have hL1L : S.L1 ≤ S.L := fun x hx => Subgroup.mem_sup_left hx
  have hL2L : S.L2 ≤ S.L := fun x hx => Subgroup.mem_sup_right hx
  have hCconj : ∀ g ∈ S.L, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    rw [hCdef] at hc ⊢
    exact he42pf_conj_map S.L hg hc
  have hZC : ∀ z ∈ S.Z, z ∈ C := by
    intro z hz
    rw [hCdef]
    exact hZ z hz
  have hsub : ∀ H : Subgroup G, H ≤ S.L → ∀ c ∈ commutator ↥H, (c : G) ∈ C := by
    intro H hH c hc
    have h1 : (c : G) ∈ (commutator ↥H).map H.subtype := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    rw [Subgroup.map_subtype_commutator] at h1
    have h2 : ⁅H, H⁆ ≤ ⁅S.L, S.L⁆ := Subgroup.commutator_mono hH hH
    rw [hCdef, Subgroup.map_subtype_commutator S.L]
    exact h2 h1
  have hAC : ∀ a ∈ S.A, a ∈ C := by
    intro a ha
    obtain ⟨z, hz, r, hr, rfl⟩ := hAZ.1 a ha
    obtain ⟨hrA, hrc⟩ := Subgroup.mem_inf.mp hr
    have hyr : y₂ * r = r * y₂ := Subgroup.mem_centralizer_iff.mp hrc y₂ (Set.mem_singleton y₂)
    have hn : l₁⁻¹ ∈ normalizer (S.A : Set G) := hB.L1_le_normalizer (S.L1.inv_mem hl.mem₁)
    have hrA' : l₁⁻¹ * r * l₁ ∈ S.A := by
      have h := (Subgroup.mem_normalizer_iff.mp hn r).mp hrA
      rw [inv_inv] at h
      exact h
    have h1 : y₁ ^ 3 = 1 := by
      have h := pow_orderOf_eq_one y₁
      rwa [hY.ord₁] at h
    have hcomm := He42Alg.conj_comm_l1 hl.sq₁
      (He42Alg.l1_conj_y2 hY.comm h1 hl.cent₁ hl.inv₁) hyr.symm
    have hrZ : l₁⁻¹ * r * l₁ ∈ S.Z := hR.2.2.2 _ hrA' hcomm
    have hconj := hCconj l₁ (hL1L hl.mem₁) _ (hZC _ hrZ)
    have e : l₁ * (l₁⁻¹ * r * l₁) * l₁⁻¹ = r := by group
    rw [e] at hconj
    exact C.mul_mem (hZC z hz) hconj
  have hAC' : ∀ a ∈ S.A', a ∈ C := by
    intro a ha
    obtain ⟨z, hz, r, hr, rfl⟩ := hAZ.2 a ha
    obtain ⟨hrA, hrc⟩ := Subgroup.mem_inf.mp hr
    have hyr : y₁ * r = r * y₁ := Subgroup.mem_centralizer_iff.mp hrc y₁ (Set.mem_singleton y₁)
    have hn : l₂⁻¹ ∈ normalizer (S.A' : Set G) := hB.L2_le_normalizer (S.L2.inv_mem hl.mem₂)
    have hrA' : l₂⁻¹ * r * l₂ ∈ S.A' := by
      have h := (Subgroup.mem_normalizer_iff.mp hn r).mp hrA
      rw [inv_inv] at h
      exact h
    have h2 : y₂ ^ 3 = 1 := by
      have h := pow_orderOf_eq_one y₂
      rwa [hY.ord₂] at h
    have hcomm := He42Alg.conj_comm_l2 hl.sq₂
      (He42Alg.l2_conj_y1 hY.comm h2 hl.cent₂ hl.inv₂) hyr.symm
    have hrZ : l₂⁻¹ * r * l₂ ∈ S.Z := hR.2.2.1 _ hrA' hcomm
    have hconj := hCconj l₂ (hL2L hl.mem₂) _ (hZC _ hrZ)
    have e : l₂ * (l₂⁻¹ * r * l₂) * l₂⁻¹ = r := by group
    rw [e] at hconj
    exact C.mul_mem (hZC z hz) hconj
  have hL1C : ∀ x ∈ S.L1, x ∈ C := by
    obtain ⟨⟨ψ1, hψ1⟩, -⟩ := hP
    exact fun x hx => he42pf_L_le S.L1 S.A ψ1 hψ1.ker hψ1.range C (hsub S.L1 hL1L) hAC hx
  have hL2C : ∀ x ∈ S.L2, x ∈ C := by
    obtain ⟨-, ⟨ψ2, hψ2⟩⟩ := hP
    exact fun x hx => he42pf_L_le S.L2 S.A' ψ2 hψ2.ker hψ2.range C (hsub S.L2 hL2L) hAC' hx
  have hLC : S.L ≤ C := by
    show S.L1 ⊔ S.L2 ≤ C
    exact sup_le (fun x hx => hL1C x hx) (fun x hx => hL2C x hx)
  rw [eq_top_iff]
  rintro g -
  have hg : (g : G) ∈ C := hLC g.2
  rw [hCdef] at hg
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
  have hxg' : x = g := Subtype.ext hxg
  rw [← hxg']
  exact hx

end CFSG.Quasithin.A94.He42
