module

public import CFSG.Quasithin.EmptyFaithful.S1421QShape2bA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bG

public section

namespace CFSG.Quasithin.F146Field.Case2b.Shape

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] {T M H K : Subgroup G}

theorem covBy_parab {Y : Type} [Group Y] {m : ℕ} {L U : Subgroup Y} {F : Type} [Field F]
    {P : Fin 2 → Subgroup Y} (hP : ParabData m L U F P) (j : Fin 2) : P j ⋖ L :=
  (hP.max _ (hP.sylow_le j) (hP.le j)).2 ⟨j, rfl⟩

theorem borel_le_Khat (c : Case2a.Setting T M H K) {P : Subgroup (E2.StarQuot (H ⊓ M) H)}
    (hBP : E2.star (H ⊓ M) H K ⊓ Subgroup.normalizer
      ((E2.star (H ⊓ M) H (T ⊓ K) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
        Set (E2.StarQuot (H ⊓ M) H)) ≤ P) :
    K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ Khat (H ⊓ M) c.le_H P := by
  rintro x ⟨hxK, hxN⟩
  have hJH := Case2a.kerIn_le_H M H
  refine mem_Khat.mpr ⟨hxK, hBP ⟨?_, ?_⟩⟩
  · exact (Case2a.mem_star_iff c.le_H hJH _).mpr (Subgroup.mem_sup_left hxK)
  · exact Case2a.mk_mem_normalizer_star (inf_le_right.trans c.le_H) hJH hxN

theorem star_le_normalizer_of_le_normalizer_Khat (c : Case2a.Setting T M H K)
    {P : Subgroup (E2.StarQuot (H ⊓ M) H)} (hP : P ≤ E2.star (H ⊓ M) H K)
    (hT : T ≤ Subgroup.normalizer (Khat (H ⊓ M) c.le_H P : Set G)) :
    E2.star (H ⊓ M) H T ≤ Subgroup.normalizer (P : Set (E2.StarQuot (H ⊓ M) H)) := by
  intro y hy
  obtain ⟨h, hhT, rfl⟩ := Case2a.exists_of_mem_star hy
  have hX : Khat (H ⊓ M) c.le_H P ≤ H := Khat_le.trans c.le_H
  have := Case2a.mk_mem_normalizer_star hX (Case2a.kerIn_le_H M H) (x := h) (hT hhT)
  rwa [star_Khat c.le_H hP] at this

end Basic

section Fin

variable {G : Type} [Group G] [Finite G] {T M H K : Subgroup G}

theorem ker_le_of_covBy (c : Case2a.Setting T M H K) {A : Subgroup G} (hTA : T ⊓ K ≤ A)
    (hAK : A ≤ K) (h : A ⋖ K) : kerIn (H ⊓ M) H ⊓ K ≤ A := by
  by_contra hN
  have hlt : A < A ⊔ (kerIn (H ⊓ M) H ⊓ K) :=
    lt_of_le_of_ne le_sup_left fun heq => hN (le_sup_right.trans heq.symm.le)
  have hsup : A ⊔ (kerIn (H ⊓ M) H ⊓ K) = K :=
    eq_of_le_of_not_lt (sup_le hAK inf_le_right) (h.2 hlt)
  refine not_le_of_gt h.lt (le_of_sup_of_comm hAK inf_le_right hsup
    (perfect_of_mem_cComp c.comp) fun n hn k hk => ?_)
  rw [commutatorElement_def]
  have h1 : n * k * n⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
    ((c.ker n).mp hn.1).2 k (Subgroup.mem_sup_left hk)
  exact hTA ⟨c.pCore_le h1, K.mul_mem (K.mul_mem (K.mul_mem hn.2 hk) (K.inv_mem hn.2))
    (K.inv_mem hk)⟩

theorem covBy_iff_Khat {m : ℕ} {F : Type} [Field F]
    {P : Fin 2 → Subgroup (E2.StarQuot (H ⊓ M) H)} (c : Case2a.Setting T M H K)
    (hP : ParabData m (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H (T ⊓ K)) F P)
    {A : Subgroup G} (hTA : T ⊓ K ≤ A) (hAK : A ≤ K) :
    A ⋖ K ↔ ∃ j, A = Khat (H ⊓ M) c.le_H (P j) := by
  constructor
  · intro h
    have hker := ker_le_of_covBy c hTA hAK h
    have hUA : E2.star (H ⊓ M) H (T ⊓ K) ≤ E2.star (H ⊓ M) H A := GoldS146R.imgJ_mono hTA
    have hAs : E2.star (H ⊓ M) H A ≤ E2.star (H ⊓ M) H K := GoldS146R.imgJ_mono hAK
    obtain ⟨j, hj⟩ := (hP.max _ hUA hAs).1 (covBy_star c.le_H hAK hker h)
    exact ⟨j, by rw [← hj, Khat_star c.le_H hAK hker]⟩
  · rintro ⟨j, rfl⟩
    exact covBy_Khat c.le_H (hP.le j) (covBy_parab hP j)

theorem isMaxParabolic2_Khat_of_parabData {m : ℕ} {F : Type} [Field F]
    {P : Fin 2 → Subgroup (E2.StarQuot (H ⊓ M) H)} (c : Case2a.Setting T M H K)
    (hP : ParabData m (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H (T ⊓ K)) F P) (j : Fin 2) :
    IsMaxParabolic2 K (Khat (H ⊓ M) c.le_H (P j)) := by
  have hcov : Khat (H ⊓ M) c.le_H (P j) ⋖ K := covBy_Khat c.le_H (hP.le j) (covBy_parab hP j)
  refine ⟨⟨Khat_le, T ⊓ K, c.sylow_inf, borel_le_Khat c (hP.borel j)⟩, hcov.ne,
    fun Q hQ hQne hPQ => ?_⟩
  rcases eq_or_lt_of_le hPQ with heq | hlt
  · exact heq.symm
  · exact absurd (lt_of_le_of_ne hQ.1 hQne) (hcov.2 hlt)

theorem parabolic_of_parabData {m : ℕ} {F : Type} [Field F]
    {P : Fin 2 → Subgroup (E2.StarQuot (H ⊓ M) H)} (c : Case2a.Setting T M H K)
    (hP : ParabData m (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H (T ⊓ K)) F P) :
    ∃ P' P'' : Subgroup G, P' ≠ P'' ∧ IsMaxParabolic2 K P' ∧ IsMaxParabolic2 K P'' ∧
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ P' ⊓ P'' ∧
      K1 c (P 1) = perfectCore P' ∧
      ∀ A : Subgroup G, T ⊓ K ≤ A → A ≤ K → (A ⋖ K ↔ A = P' ∨ A = P'') := by
  refine ⟨Khat (H ⊓ M) c.le_H (P 1), Khat (H ⊓ M) c.le_H (P 0), fun h => hP.ne ?_,
    isMaxParabolic2_Khat_of_parabData c hP 1, isMaxParabolic2_Khat_of_parabData c hP 0,
    le_inf (borel_le_Khat c (hP.borel 1)) (borel_le_Khat c (hP.borel 0)), rfl,
    fun A hTA hAK => ?_⟩
  · calc P 0 = E2.star (H ⊓ M) H (Khat (H ⊓ M) c.le_H (P 0)) := (star_Khat c.le_H (hP.le 0)).symm
      _ = E2.star (H ⊓ M) H (Khat (H ⊓ M) c.le_H (P 1)) := by rw [h]
      _ = P 1 := star_Khat c.le_H (hP.le 1)
  · rw [covBy_iff_Khat c hP hTA hAK, Fin.exists_fin_two, or_comm]

theorem diag_of_parabData {m : ℕ} {F : Type} [Field F]
    {P : Fin 2 → Subgroup (E2.StarQuot (H ⊓ M) H)} (c : Case2a.Setting T M H K)
    (hP : ParabData m (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H (T ⊓ K)) F P)
    (hdiag : E2.IsDiagramNontrivial (E2.star (H ⊓ M) H T) (E2.star (H ⊓ M) H K)
      (E2.star (H ⊓ M) H (T ⊓ K))) :
    E2.IsDiagramNontrivial T K (T ⊓ K) := by
  intro Q hQ hBQ hTQ
  have hQK : Q ≤ K := hQ.1.1
  have hTKQ : T ⊓ K ≤ Q := (le_inf inf_le_right Subgroup.le_normalizer).trans hBQ
  obtain ⟨A, hQA, hAcov⟩ := exists_le_covBy_of_lt (lt_of_le_of_ne hQK hQ.2.1)
  obtain ⟨j, hj⟩ := (covBy_iff_Khat c hP (hTKQ.trans hQA) hAcov.le).mp hAcov
  have hmax : IsMaxParabolic2 K A := by
    rw [hj]
    exact isMaxParabolic2_Khat_of_parabData c hP j
  have hQeq : Q = Khat (H ⊓ M) c.le_H (P j) := (hQ.2.2 A hmax.1 hAcov.ne hQA).symm.trans hj
  rw [hQeq] at hTQ
  exact hdiag (P j) (hP.maxPar j) (hP.borel j)
    (star_le_normalizer_of_le_normalizer_Khat c (hP.le j) hTQ)

end Fin

end CFSG.Quasithin.F146Field.Case2b.Shape
