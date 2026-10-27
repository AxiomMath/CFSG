module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private theorem he42n_conj_inv_mem {L : Subgroup G} {h : G}
    (hc : ∀ l ∈ L, h * l * h⁻¹ ∈ L) : ∀ l ∈ L, h⁻¹ * l * h ∈ L := by
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = L.map (MulAut.conj h).toMonoidHom := ⟨_, rfl⟩
  have hle : C ≤ L := by
    intro y hy
    rw [hC] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact hc x hx
  have heq : C = L := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hC]
    exact (Subgroup.card_map_of_injective hinj).symm.le
  intro l hl
  have hlC : l ∈ C := by rw [heq]; exact hl
  rw [hC] at hlC
  obtain ⟨x, hx, hxl⟩ := Subgroup.mem_map.1 hlC
  have hx' : x = h⁻¹ * l * h := by
    rw [← hxl]
    show x = h⁻¹ * (h * x * h⁻¹) * h
    group
  rw [← hx']
  exact hx

private theorem he42n_le_of_normal {L A' M : Subgroup G} {ψ : ↥L →* Equiv.Perm (Fin 5)}
    (hker : ψ.ker = A'.subgroupOf L) (hrange : ψ.range = alternatingGroup (Fin 5))
    (hML : M ≤ L) (hMn : ∀ l ∈ L, ∀ m ∈ M, l * m * l⁻¹ ∈ M) (hM : Nat.card M = 64) :
    M ≤ A' := by
  have hsimp : IsSimpleGroup ψ.range := by
    rw [hrange]
    exact alternatingGroup.isSimpleGroup (by simp)
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] <;> decide
  have hMn' : (M.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hMn (g : G) g.2 (n : G) hn
  have hTn : ((M.subgroupOf L).map ψ.rangeRestrict).Normal :=
    hMn'.map ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hcard : Nat.card ↥(M.subgroupOf L) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv, hM]
  have hdvd := Subgroup.card_map_dvd (M.subgroupOf L) ψ.rangeRestrict
  rw [hcard] at hdvd
  intro m hm
  have hx : (⟨m, hML hm⟩ : ↥L) ∈ M.subgroupOf L := Subgroup.mem_subgroupOf.2 hm
  rcases Subgroup.Normal.eq_bot_or_eq_top ((M.subgroupOf L).map ψ.rangeRestrict) with hbot | htop
  · have h1 : ψ.rangeRestrict ⟨m, hML hm⟩ ∈ (M.subgroupOf L).map ψ.rangeRestrict :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : ψ ⟨m, hML hm⟩ = 1 := by
      have h3 := congrArg Subtype.val h1
      simpa using h3
    have h4 : (⟨m, hML hm⟩ : ↥L) ∈ ψ.ker := MonoidHom.mem_ker.2 h2
    rw [hker, Subgroup.mem_subgroupOf] at h4
    exact h4
  · exfalso
    have h5 : Nat.card ((M.subgroupOf L).map ψ.rangeRestrict) = 60 := by
      rw [htop, Subgroup.card_top, hrange, h60]
    rw [h5] at hdvd
    norm_num at hdvd

private theorem he42n_core {A A' L : Subgroup G} {ψ : ↥L →* Equiv.Perm (Fin 5)}
    (hA'L : A' ≤ L) (hAn : ∀ l ∈ L, ∀ a ∈ A', l * a * l⁻¹ ∈ A')
    (hker : ψ.ker = A'.subgroupOf L) (hrange : ψ.range = alternatingGroup (Fin 5))
    (hcard : Nat.card A' = 64) {h : G} (hhA : h ∈ normalizer (A : Set G))
    (hc : ∀ l ∈ L, h * l * h⁻¹ ∈ L) :
    h ∈ normalizer ((A ⊔ A' : Subgroup G) : Set G) := by
  have hinv := he42n_conj_inv_mem hc
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup G, M = A'.map (MulAut.conj h).toMonoidHom := ⟨_, rfl⟩
  have hMmem : ∀ a ∈ A', h * a * h⁻¹ ∈ M := by
    intro a ha
    rw [hMdef]
    exact Subgroup.mem_map.2 ⟨a, ha, rfl⟩
  have hML : M ≤ L := by
    intro y hy
    rw [hMdef] at hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    exact hc a (hA'L ha)
  have hMn : ∀ l ∈ L, ∀ m ∈ M, l * m * l⁻¹ ∈ M := by
    intro l hl m hm
    rw [hMdef] at hm ⊢
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hm
    refine Subgroup.mem_map.2 ⟨(h⁻¹ * l * h) * a * (h⁻¹ * l * h)⁻¹, hAn _ (hinv l hl) a ha, ?_⟩
    show h * ((h⁻¹ * l * h) * a * (h⁻¹ * l * h)⁻¹) * h⁻¹ = l * (h * a * h⁻¹) * l⁻¹
    group
  have hMcard : Nat.card M = 64 := by
    rw [hMdef, Subgroup.card_map_of_injective hinj]
    exact hcard
  have hMA' : M ≤ A' := he42n_le_of_normal hker hrange hML hMn hMcard
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  refine CFSG.Quasithin.A94.HeJ.sup_induction (A := A) (A' := A')
    (P := fun y => h * y * h⁻¹ ∈ A ⊔ A') ?_ ?_ ?_ ?_ ?_ hn
  · intro y hy
    exact (le_sup_left : A ≤ A ⊔ A') ((Subgroup.mem_normalizer_iff.1 hhA y).1 hy)
  · intro y hy
    exact (le_sup_right : A' ≤ A ⊔ A') (hMA' (hMmem y hy))
  · show h * 1 * h⁻¹ ∈ A ⊔ A'
    rw [mul_one, mul_inv_cancel]
    exact (A ⊔ A').one_mem
  · intro x y _ _ hx hy
    show h * (x * y) * h⁻¹ ∈ A ⊔ A'
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    exact (A ⊔ A').mul_mem hx hy
  · intro x _ hx
    show h * x⁻¹ * h⁻¹ ∈ A ⊔ A'
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e]
    exact (A ⊔ A').inv_mem hx

private theorem he42n_le_inf {A B : Subgroup G} (hBA : B ≤ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    A ≤ normalizer (A : Set G) ⊓ centralizer (B : Set G) := by
  intro a ha
  refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (H := A) ha, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro b hb
  exact hcomm b (hBA hb) a ha

theorem HeSetup.stepN (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) : S.StepN := by
  unfold HeSetup.StepPsi at hP
  unfold HeSetup.StepN
  obtain ⟨⟨ψ1, h1⟩, ⟨ψ2, h2⟩⟩ := hP
  refine ⟨fun h hh hc => ?_, fun h hh hc => ?_⟩
  · have hN : h ∈ normalizer ((S.A ⊔ S.A' : Subgroup G) : Set G) :=
      he42n_core (A := S.A) (A' := S.A') (L := S.L2) (ψ := ψ2)
        (he42n_le_inf (hB.B_le_Z.trans hB.Z_le_A') hB.A'_comm) h2.A_normal h2.ker h2.range
        hB.card_A' (hB.L1_le_normalizer hh) hc
    show h ∈ S.N ⊓ centralizer (S.B : Set G)
    rw [S.hN]
    exact Subgroup.mem_inf.2 ⟨hN, hB.L1_le_centralizer hh⟩
  · have hN : h ∈ normalizer ((S.A' ⊔ S.A : Subgroup G) : Set G) :=
      he42n_core (A := S.A') (A' := S.A) (L := S.L1) (ψ := ψ1)
        (he42n_le_inf (hB.B_le_Z.trans hB.Z_le_A) hB.A_comm) h1.A_normal h1.ker h1.range
        hB.card_A (hB.L2_le_normalizer hh) hc
    rw [sup_comm] at hN
    show h ∈ S.N ⊓ centralizer (S.B : Set G)
    rw [S.hN]
    exact Subgroup.mem_inf.2 ⟨hN, hB.L2_le_centralizer hh⟩

end CFSG.Quasithin.A94.He42
