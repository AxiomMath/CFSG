module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixNF
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixJ

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

section Tg

@[expose] noncomputable def Tg (T : Subgroup (MulAut (Cm σ))) : Subgroup (MulAut (Cm σ)) :=
  T ⊓ Subgroup.centralizer ({(fieldActor σ δ : MulAut (Cm σ))} : Set (MulAut (Cm σ)))

variable {T : Subgroup (MulAut (Cm σ))} {S : Subgroup (K ≃+* K)}
  (hT : ∀ α : MulAut (Cm σ), α ∈ T ↔ ∃ u ∈ Ust σ, ∃ δ' ∈ S, α = MulAut.conj u * fieldActor σ δ')

include hT in
theorem mem_Tg_iff (α : MulAut (Cm σ)) :
    α ∈ Tg σ δ T ↔ ∃ u ∈ Ug σ δ, ∃ δ' ∈ S, α = MulAut.conj u * fieldActor σ δ' := by
  constructor
  · rintro ⟨hα, hc⟩
    obtain ⟨u, hu, δ', hδ', rfl⟩ := (hT α).1 hα
    refine ⟨u, ⟨hu, ?_⟩, δ', hδ', rfl⟩
    have h := (Subgroup.mem_centralizer_iff.1 hc) (fieldActor σ δ) rfl
    exact (commute_conj_fieldActor_iff σ δ δ' u).1 h
  · rintro ⟨u, ⟨hu, hfix⟩, δ', hδ', rfl⟩
    refine ⟨(hT _).2 ⟨u, hu, δ', hδ', rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (commute_conj_fieldActor_iff σ δ δ' u).2 hfix

include hf hK hσ hT in
theorem card_Tg : Nat.card (Tg σ δ T) = Nat.card (Ug σ δ) * Nat.card S :=
  card_of_normal_form σ hf hK hσ (mem_Tg_iff σ δ hT)

end Tg

section Ng

variable (Kb : Subgroup (MulAut (Cm σ))) (P : Subgroup (Cm σ))

@[expose] noncomputable def Ng : Subgroup (MulAut (Cm σ)) :=
  Kb ⊓ autStab P ⊓ Subgroup.centralizer ({(fieldActor σ δ : MulAut (Cm σ))} :
    Set (MulAut (Cm σ)))

include hf hK hσ in
theorem mem_Ng_iff (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)
    (hPself : Subgroup.normalizer (P : Set (Cm σ)) = P)
    (hPstab : ∀ δ' : K ≃+* K, (fieldActor σ δ' : MulAut (Cm σ)) ∈ autStab P)
    (α : MulAut (Cm σ)) :
    α ∈ Ng σ δ Kb P ↔ ∃ y ∈ P ⊓ Jfix σ δ, ∃ δ' ∈ Kb.map (theta σ hf hK hσ),
      α = MulAut.conj y * fieldActor σ δ' := by
  constructor
  · rintro ⟨⟨hαK, hαP⟩, hαc⟩
    obtain ⟨y, hy⟩ := exists_conj_fieldActor σ hf hK hσ α
    set δ' := theta σ hf hK hσ α with hδ'
    have hδK : δ' ∈ Kb.map (theta σ hf hK hσ) := Subgroup.mem_map_of_mem _ hαK
    have hconj : (MulAut.conj y : MulAut (Cm σ)) ∈ autStab P := by
      have h1 : (MulAut.conj y : MulAut (Cm σ)) = α * (fieldActor σ δ')⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        exact hy.symm
      rw [h1]
      exact (autStab P).mul_mem hαP ((autStab P).inv_mem (hPstab δ'))
    have hyP : y ∈ P := by
      have := (conj_mem_autStab_iff P y).1 hconj
      rwa [hPself] at this
    have hc := (Subgroup.mem_centralizer_iff.1 hαc) (fieldActor σ δ) rfl
    rw [hy] at hc
    exact ⟨y, ⟨hyP, (commute_conj_fieldActor_iff σ δ δ' y).1 hc⟩, δ', hδK, hy⟩
  · rintro ⟨y, ⟨hyP, hyJ⟩, δ', hδ', rfl⟩
    refine ⟨⟨(conj_mul_fieldActor_mem_iff σ hf hK hσ hinn y δ').2 hδ', ?_⟩,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    · exact (autStab P).mul_mem ((conj_mem_autStab_iff P y).2 (by rw [hPself]; exact hyP))
        (hPstab δ')
    · intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact (commute_conj_fieldActor_iff σ δ δ' y).2 hyJ

include hf hK hσ in
theorem card_Ng (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)
    (hPself : Subgroup.normalizer (P : Set (Cm σ)) = P)
    (hPstab : ∀ δ' : K ≃+* K, (fieldActor σ δ' : MulAut (Cm σ)) ∈ autStab P) :
    Nat.card (Ng σ δ Kb P) = Nat.card (P ⊓ Jfix σ δ : Subgroup (Cm σ)) *
      Nat.card (Kb.map (theta σ hf hK hσ)) :=
  card_of_normal_form σ hf hK hσ (mem_Ng_iff σ δ hf hK hσ Kb P hinn hPself hPstab)

end Ng

end CFSG.Quasithin.H13.F431.D4q.Out
