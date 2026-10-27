module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.CTP

variable {G : Type*} [Group G]

theorem centralizer_sup_eq (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (by exact_mod_cast le_sup_left))
      (Subgroup.centralizer_le (by exact_mod_cast le_sup_right))
  · intro g hg
    have h1 := Subgroup.mem_centralizer_iff.mp hg.1
    have h2 := Subgroup.mem_centralizer_iff.mp hg.2
    have hle : A ⊔ B ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact (h1 a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact (h2 b hb).symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_centralizer_iff.mp (hle hh) g rfl
    exact this.symm

structure EdgeTorus (p : ℕ) (E A B : Subgroup G) : Prop where
  decA : E = (E ⊓ Subgroup.centralizer (A : Set G)) ⊔ (E ⊓ A)
  idxA : (E ⊓ Subgroup.centralizer (A : Set G)).relIndex E = p
  decB : E = (E ⊓ Subgroup.centralizer (B : Set G)) ⊔ (E ⊓ B)
  idxB : (E ⊓ Subgroup.centralizer (B : Set G)).relIndex E = p
  idxAB : (E ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)).relIndex E = p ^ 2

theorem le_normalizer_of_dec {E A : Subgroup G}
    (h : E = (E ⊓ Subgroup.centralizer (A : Set G)) ⊔ (E ⊓ A)) :
    E ≤ Subgroup.normalizer (A : Set G) := by
  have : (E ⊓ Subgroup.centralizer (A : Set G)) ⊔ (E ⊓ A) ≤ Subgroup.normalizer (A : Set G) := by
    refine sup_le ?_ ?_
    · exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
    · exact inf_le_right.trans (Subgroup.le_normalizer)
  rwa [← h] at this

theorem exists_mem_lt {p : ℕ} (hp : p.Prime) {E C D : Subgroup G} (hCD : D ≤ C)
    (hC : (E ⊓ C).relIndex E = p) (hD : (E ⊓ D).relIndex E = p ^ 2) :
    ∃ e ∈ E, e ∈ C ∧ e ∉ D := by
  by_contra hcon
  push Not at hcon
  have heq : E ⊓ C = E ⊓ D :=
    le_antisymm (fun x hx => ⟨hx.1, hcon x hx.1 hx.2⟩) (inf_le_inf_left _ hCD)
  rw [heq] at hC
  rw [hC] at hD
  have : p = p ^ 2 := hD
  have h1 := hp.one_lt
  nlinarith

theorem EdgeTorus.exists_centralizing {p : ℕ} (hp : p.Prime) {E A B : Subgroup G}
    [CFSG.IsElementaryAbelian p E] (h : EdgeTorus p E A B) :
    ∃ e ∈ E, (∀ x ∈ A, e * x = x * e) ∧ (∃ y ∈ B, e * y ≠ y * e) ∧
      (∀ y ∈ B, e * y * e⁻¹ ∈ B) ∧ orderOf e = p := by
  have hCD : Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) ≤
      Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le (by exact_mod_cast le_sup_left)
  obtain ⟨e, heE, heA, heAB⟩ := exists_mem_lt hp hCD h.idxA h.idxAB
  refine ⟨e, heE, fun x hx => (Subgroup.mem_centralizer_iff.mp heA x hx).symm, ?_, fun y hy => ?_,
    ?_⟩
  · by_contra hcon
    push Not at hcon
    apply heAB
    rw [centralizer_sup_eq]
    exact ⟨heA, Subgroup.mem_centralizer_iff.mpr fun y hy => (hcon y hy).symm⟩
  · have := le_normalizer_of_dec h.decB heE
    have h2 := (Subgroup.mem_normalizer_iff.mp this y).mp hy
    simpa using h2
  · have hpow := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e heE
    have hne : e ≠ 1 := by
      rintro rfl
      exact heAB (Subgroup.one_mem _)
    exact (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hpow) |>.resolve_left
      (fun h1 => hne (orderOf_eq_one_iff.mp h1))

end CFSG.RankThree.PartOne.CTP
