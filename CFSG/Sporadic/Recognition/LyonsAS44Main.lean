module

public import CFSG.Sporadic.Recognition.LyonsAS44Conj
public import CFSG.Sporadic.Recognition.LyonsAS44Classes2

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS

section Main

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem exists_conjSub_eq_sylow {p : ℕ} [Fact p.Prime] (P Q : Sylow p G) :
    ∃ c : G, (Q : Subgroup G) = conjSub c (P : Subgroup G) := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨c, ?_⟩
  rw [← hc, Sylow.coe_subgroup_smul]
  ext y
  rw [mem_pointwise_smul_iff_inv_smul_mem, mem_conjSub_iff]
  have : (MulAut.conj c)⁻¹ • y = c⁻¹ * y * c := by
    simp [MulAut.smul_def]
  rw [this]

omit [Finite G] in
theorem preimQ_sup {x : G} (K L : Subgroup (CentQuot x)) :
    preimQ x (K ⊔ L) = preimQ x K ⊔ preimQ x L := by
  have hr : (projQ x).range = ⊤ := MonoidHom.range_eq_top.2 (projQ_surjective x)
  have hK : K ≤ (projQ x).range := by rw [hr]; exact le_top
  have hL : L ≤ (projQ x).range := by rw [hr]; exact le_top
  unfold preimQ
  rw [← Subgroup.comap_sup_eq_of_le_range _ hK hL, Subgroup.map_sup]

namespace LyData

section NoCert

theorem deltaGen_TG {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}
    (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y) :
    deltaGen (x₁ : G) (preimQ (x₁ : G) T) = preimQ (x₁ : G) A := by
  have h : {w : G | w ∈ preimQ (x₁ : G) T ∧ IsConj (x₁ : G) w} =
      {w : G | w ∈ preimQ (x₁ : G) A ∧ IsConj (x₁ : G) w} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨D.mem_AG_of_mem_TG S F h.1 h.2, h.2⟩,
      fun h => ⟨preimQ_mono F.mcl.A_le_T h.1, h.2⟩⟩
  rw [deltaGen, h, ← D.AG_eq_closure S F]

theorem lemma45_TG {R T A : Subgroup (CentQuot (x₁ : G))} {Y : Fin 10 → CentQuot (x₁ : G)}
    (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (F : LyAFacts D S R T A Y) :
    Lemma45 (x₁ : G) (preimQ (x₁ : G) T) := by
  unfold Lemma45
  rw [D.deltaGen_TG S F]
  refine ⟨preimQ (x₁ : G) R, EE (x₁ : G) (x₂ : G), preimQ_mono F.mcl.R_le_T, ?_,
    (D.threeCoreE_RG S F).card.trans (by norm_num), D.EE_le_RG S F, D.card_closure_two S,
    D.RG_center S F, D.RG_commutator_eq S F, D.RG_frattini S F,
    fun r hr => D.RG_pow_three_mem S F hr,
    ?_, (x₁ : G), (x₂ : G), IsConj.refl _, D.isConj_x₁_x₂ S, ?_, rfl, D.deltaIn_RG_eq S F⟩
  · rw [← preimQ_sup, F.mcl.T_sup]
  · intro g hg hg3
    exact D.mem_RG_or_AG_of_orderOf_three S F hg hg3
  · intro h
    have h' : (x₂ : G) ∈ zpowers (x₁ : G) := h ▸ mem_zpowers _
    rcases (zpowers_eq_iff (x₁_pow_three S) (x₁_ne_one S)).1 h.symm with h1 | h1
    · exact (D.six_ne S).1 h1
    · exact (D.six_ne S).2.1 h1

end NoCert

section Cert

theorem lemma45 (hnrm : nrmCheck = true) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (T : Sylow 3 G) : Lemma45 (x₁ : G) (T : Subgroup G) := by
  obtain ⟨R, T₀, A, Y, F⟩ := D.exists_lyAFacts hnrm S
  obtain ⟨c, hc⟩ := exists_conjSub_eq_sylow (D.sylowTG S F) T
  rw [hc, D.coe_sylowTG S F]
  exact (D.lemma45_TG S F).conj c

theorem lemma45_classes (hnrm : nrmCheck = true) (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    (∀ g : G, orderOf g = 3 → IsConj g (x₁ : G) ∨ IsConj g ((x₁ : G) * (x₂ : G))) ∧
      ¬ IsConj (x₁ : G) ((x₁ : G) * (x₂ : G)) := by
  obtain ⟨R, T₀, A, Y, F⟩ := D.exists_lyAFacts hnrm S
  exact D.two_classes S F

end Cert

end LyData

end Main

end CFSG.Sporadic.Recognition.LyonsSims
