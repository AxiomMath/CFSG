module

public import CFSG.Quasithin.H13.NQCatT513Out
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Prime

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

theorem cycOddPerm_inner_of_equiv {X M : Type} [Group X] [Group M] [Finite M] [IsSimpleGroup M]
    {c : ℕ → Prop} (e : X ≃* M) (h : CycOddPerm M c) : CycOddPerm ↥(inner X) c := by
  have : IsSimpleGroup X := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact cycOddPerm_inner ((quotCenterEquivOfBot hc).trans e) h
  · intro T Dc _ _ _ _
    left
    refine ⟨0, ?_⟩
    have hsub : Subsingleton ↥(inner X) := by
      constructor
      rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩
      have hx : MulAut.conj x = 1 := by
        rw [← MonoidHom.mem_ker, ker_conj_eq_center, hc]
        exact Subgroup.mem_top x
      have hy : MulAut.conj y = 1 := by
        rw [← MonoidHom.mem_ker, ker_conj_eq_center, hc]
        exact Subgroup.mem_top y
      exact Subtype.ext (hx.trans hy.symm)
    rw [pow_zero]
    exact Nat.card_unique

theorem kind_of_star {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}
    (hst : Star513 Q R S B D) {c : ℕ → Prop} (hout : OddAutThreeInner ↥Q)
    (hDT : CycOddPerm ↥(inner ↥Q) c)
    (h3 : ¬ ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    ∃ n, c n ∧ ∀ (d : A) (hd : d ∈ D) (k : ℕ), actQ Q ⟨d, hst.D_le_Q hd⟩ ^ (3 ^ k) ∈ inner ↥Q →
      d ^ (3 ^ k * n) ∈ Subgroup.centralizer (Q : Set A) :=
  (three_or_of_inner hst.S_le_Q hst.D_le_Q hst.S_two hst.sylow_Q hst.D_cyclic hst.D_odd
    hst.perm_D hout hDT).resolve_left h3

theorem mem_inner_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ ψ : MulAut Y, ψ ∈ inner Y) (φ : MulAut X) : φ ∈ inner X := by
  have h1 := h (MulAut.congr e φ)
  rw [← inner_map_congr e] at h1
  obtain ⟨ψ, hψ, hψe⟩ := h1
  have : ψ = φ := (MulAut.congr e).injective hψe
  rwa [← this]

theorem factType513Prime_of
    (hA7 : CycOddPerm (alternatingGroup (Fin 7)) fun _ => False)
    (hM22 : CycOddPerm (NativeSporadic.Carrier .M22) fun _ => False)
    (hM23 : CycOddPerm (NativeSporadic.Carrier .M23) fun _ => False)
    (hJ1 : CycOddPerm (NativeSporadic.Carrier .J1) fun n => n = 7)
    (hJ2 : CycOddPerm (NativeSporadic.Carrier .J2) fun _ => False)
    (hJ4 : CycOddPerm (NativeSporadic.Carrier .J4) fun _ => False)
    (hHS : CycOddPerm (NativeSporadic.Carrier .HS) fun _ => False)
    (hRu : CycOddPerm (NativeSporadic.Carrier .Ru) fun _ => False) :
    H13.FactType513Prime := by
  intro A _ _ Q R S B D hst hlist h3
  have hfalse : ∀ {M : Type} [Group M] [Finite M] [IsSimpleGroup M], OddAutThreeInner M →
      CycOddPerm M (fun _ => False) → (↥Q ≃* M) → False := by
    intro M _ _ _ hM hC e
    obtain ⟨n, hn, -⟩ :=
      kind_of_star hst (hM.of_equiv e.symm) (cycOddPerm_inner_of_equiv e hC) h3
    exact hn
  have hfalseHat : ∀ {M : Type} [Group M] [Finite M], OddAutThreeInner M →
      CycOddPerm M (fun _ => False) → IsHat ↥Q M → False := by
    intro M _ _ hM hC hQ
    obtain ⟨hq, -, ⟨e⟩⟩ := hQ
    obtain ⟨n, hn, -⟩ := kind_of_star hst (oddAutThreeInner_of_center hq.1 (hM.of_equiv e.symm))
      (cycOddPerm_inner e hC) h3
    exact hn
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have : Finite (NativeSporadic.Carrier .M22) := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).1
  have : IsSimpleGroup (NativeSporadic.Carrier .M22) :=
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  have : Finite (NativeSporadic.Carrier .M23) := (CFSG.Sporadic.Mathieu.fam_m23_simplicity).1
  have : IsSimpleGroup (NativeSporadic.Carrier .M23) :=
    (CFSG.Sporadic.Mathieu.fam_m23_simplicity).2.2
  have : Finite (NativeSporadic.Carrier .J1) := (CFSG.Sporadic.J1.fam_j1_simplicity).1
  have : IsSimpleGroup (NativeSporadic.Carrier .J1) := (CFSG.Sporadic.J1.fam_j1_simplicity).2.2
  have : Finite (NativeSporadic.Carrier .J2) := (CFSG.Sporadic.J2.fam_j2_simplicity).1
  have : IsSimpleGroup (NativeSporadic.Carrier .J2) := (CFSG.Sporadic.J2.fam_j2_simplicity).2.2
  have : Finite (NativeSporadic.Carrier .J4) := (CFSG.Sporadic.J4.fam_j4_simplicity).1
  have : IsSimpleGroup (NativeSporadic.Carrier .J4) := (CFSG.Sporadic.J4.fam_j4_simplicity).2.2
  have : Finite (NativeSporadic.Carrier .HS) := (CFSG.Sporadic.HS.fam_hs_simplicity).1
  have : IsSimpleGroup (NativeSporadic.Carrier .HS) := (CFSG.Sporadic.HS.fam_hs_simplicity).2.2
  have : Finite (NativeSporadic.Carrier .Ru) := (CFSG.Sporadic.Ru.fam_ru_simplicity).1
  have : IsSimpleGroup (NativeSporadic.Carrier .Ru) := (CFSG.Sporadic.Ru.fam_ru_simplicity).2.2
  rcases hlist with hQ | hQ | hQ | hQ | hQ | hQ | hQ | hQ | hQ | hQ
  · obtain ⟨e⟩ := hQ
    exact (hfalse oddAut_alt7 hA7 e).elim
  · exact (hfalseHat oddAut_alt7 hA7 hQ).elim
  · obtain ⟨e⟩ := hQ
    exact (hfalse oddAut_m22 hM22 e).elim
  · exact (hfalseHat oddAut_m22 hM22 hQ).elim
  · obtain ⟨e⟩ := hQ
    exact (hfalse oddAut_m23 hM23 e).elim
  · obtain ⟨e⟩ := hQ
    obtain ⟨n, rfl, hkey⟩ :=
      kind_of_star hst (oddAut_j1.of_equiv e.symm) (cycOddPerm_inner_of_equiv e hJ1) h3
    refine ⟨⟨e⟩, fun d hd => ?_⟩
    have hin : actQ Q ⟨d, hst.D_le_Q hd⟩ ^ (3 ^ 0) ∈ inner ↥Q := by
      rw [pow_zero, pow_one]
      exact mem_inner_of_equiv e allInner_j1 _
    have h1 := hkey d hd 0 hin
    rwa [pow_zero, one_mul] at h1
  · obtain ⟨e⟩ := hQ
    exact (hfalse oddAut_j2 hJ2 e).elim
  · obtain ⟨e⟩ := hQ
    exact (hfalse oddAut_j4 hJ4 e).elim
  · obtain ⟨e⟩ := hQ
    exact (hfalse oddAut_hs hHS e).elim
  · obtain ⟨e⟩ := hQ
    exact (hfalse oddAut_ru hRu e).elim

end CFSG.Quasithin.H13.NQCat.T513P
