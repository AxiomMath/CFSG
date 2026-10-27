module

public import CFSG.Quasithin.Vol2.Ch11SecOE1A
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE1

open Subgroup CFSG.Quasithin

variable {G : Type} [Group G]

section Conj

variable {X I : Subgroup G} {m : G}

theorem map_conj_eq_self (hm : m ∈ normalizer (X : Set G)) :
    X.map (MulAut.conj m).toMonoidHom = X :=
  mem_normalizer_iff_map_conj_eq.mp hm

theorem map_conj_centralizer (hm : m ∈ normalizer (X : Set G)) :
    (centralizer (X : Set G)).map (MulAut.conj m).toMonoidHom = centralizer (X : Set G) :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_centralizer X hm)

theorem le_normalizer_map_conj (hm : m ∈ normalizer (X : Set G))
    (hXI : X ≤ normalizer (I : Set G)) :
    X ≤ normalizer ((I.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) := by
  calc X = X.map (MulAut.conj m).toMonoidHom := (map_conj_eq_self hm).symm
    _ ≤ (normalizer (I : Set G)).map (MulAut.conj m).toMonoidHom := map_mono hXI
    _ = normalizer ((I.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) :=
      map_equiv_normalizer_eq I (MulAut.conj m)

theorem commutator_map_conj (hm : m ∈ normalizer (X : Set G)) (hIX : ⁅I, X⁆ = I) :
    ⁅I.map (MulAut.conj m).toMonoidHom, X⁆ = I.map (MulAut.conj m).toMonoidHom := by
  calc ⁅I.map (MulAut.conj m).toMonoidHom, X⁆ =
        ⁅I.map (MulAut.conj m).toMonoidHom, X.map (MulAut.conj m).toMonoidHom⁆ := by
        rw [map_conj_eq_self hm]
    _ = (⁅I, X⁆).map (MulAut.conj m).toMonoidHom := (map_commutator I X _).symm
    _ = I.map (MulAut.conj m).toMonoidHom := by rw [hIX]

theorem map_conj_inf_centralizer (hm : m ∈ normalizer (X : Set G)) :
    I.map (MulAut.conj m).toMonoidHom ⊓ centralizer (X : Set G) =
      (I ⊓ centralizer (X : Set G)).map (MulAut.conj m).toMonoidHom := by
  rw [map_inf_eq _ _ _ (MulAut.conj m).injective, map_conj_centralizer hm]

theorem map_conj_inf_lt (hm : m ∈ normalizer (X : Set G))
    (hlt : I ⊓ centralizer (X : Set G) < I) :
    I.map (MulAut.conj m).toMonoidHom ⊓ centralizer (X : Set G) <
      I.map (MulAut.conj m).toMonoidHom := by
  rw [map_conj_inf_centralizer hm]
  exact (map_lt_map_iff_of_injective (MulAut.conj m).injective).mpr hlt

theorem irr_map_conj (hm : m ∈ normalizer (X : Set G))
    (hirr : ∀ J : Subgroup G, I ⊓ centralizer (X : Set G) ≤ J → J ≤ I →
      X ≤ normalizer (J : Set G) → J = I ⊓ centralizer (X : Set G) ∨ J = I) :
    ∀ J : Subgroup G, I.map (MulAut.conj m).toMonoidHom ⊓ centralizer (X : Set G) ≤ J →
      J ≤ I.map (MulAut.conj m).toMonoidHom → X ≤ normalizer (J : Set G) →
      J = I.map (MulAut.conj m).toMonoidHom ⊓ centralizer (X : Set G) ∨
        J = I.map (MulAut.conj m).toMonoidHom := by
  intro J hJ1 hJ2 hJ3
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  have hsurj : Function.Surjective (MulAut.conj m).toMonoidHom := (MulAut.conj m).surjective
  have hXc : X.comap (MulAut.conj m).toMonoidHom = X := by
    have h := comap_map_eq_self_of_injective hinj X
    rwa [map_conj_eq_self hm] at h
  have h1 : I ⊓ centralizer (X : Set G) ≤ J.comap (MulAut.conj m).toMonoidHom := by
    intro z hz
    rw [mem_comap]
    apply hJ1
    rw [map_conj_inf_centralizer hm]
    exact mem_map_of_mem _ hz
  have h2 : J.comap (MulAut.conj m).toMonoidHom ≤ I := by
    have h := comap_mono (f := (MulAut.conj m).toMonoidHom) hJ2
    rwa [comap_map_eq_self_of_injective hinj] at h
  have h3 : X ≤ normalizer ((J.comap (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) := by
    rw [← comap_normalizer_eq_of_surjective J hsurj, ← hXc]
    exact comap_mono hJ3
  have hJ : J = (J.comap (MulAut.conj m).toMonoidHom).map (MulAut.conj m).toMonoidHom :=
    (map_comap_eq_self_of_surjective hsurj J).symm
  rcases hirr _ h1 h2 h3 with h | h
  · left
    rw [hJ, h, map_conj_inf_centralizer hm]
  · right
    rw [hJ, h]

theorem map_conj_le_conjClosure {M : Subgroup G} (hmM : m ∈ M) :
    I.map (MulAut.conj m).toMonoidHom ≤ conjClosure I M := by
  rintro y ⟨i, hi, rfl⟩
  exact mem_conjClosure hmM hi

theorem map_conj_inf_le_conjClosure {M : Subgroup G} (hmM : m ∈ M)
    (hm : m ∈ normalizer (X : Set G)) :
    I.map (MulAut.conj m).toMonoidHom ⊓ centralizer (X : Set G) ≤
      conjClosure (I ⊓ centralizer (X : Set G)) M := by
  rw [map_conj_inf_centralizer hm]
  exact map_conj_le_conjClosure hmM

end Conj

theorem conjClosure_inf_centralizer_le [Finite G] {X I M : Subgroup G}
    (hab : ∀ a ∈ conjClosure I M, ∀ b ∈ conjClosure I M, a * b = b * a)
    (hXM : X ≤ M) (hMX : M ≤ normalizer (X : Set G)) (hXI : X ≤ normalizer (I : Set G))
    (hIX : ⁅I, X⁆ = I) (hlt : I ⊓ centralizer (X : Set G) < I)
    (hirr : ∀ J : Subgroup G, I ⊓ centralizer (X : Set G) ≤ J → J ≤ I →
      X ≤ normalizer (J : Set G) → J = I ⊓ centralizer (X : Set G) ∨ J = I) :
    conjClosure I M ⊓ centralizer (X : Set G) ≤ conjClosure (I ⊓ centralizer (X : Set G)) M := by
  set C := conjClosure (I ⊓ centralizer (X : Set G)) M with hC
  set B := conjClosure I M with hB
  obtain ⟨U, hCU, hUmax⟩ := Finite.exists_le_maximal (a := C)
    (p := fun U : Subgroup G => C ≤ U ∧ U ≤ B ∧ X ≤ normalizer (U : Set G) ∧
      U ⊓ centralizer (X : Set G) ≤ C)
    ⟨le_rfl, conjClosure_mono inf_le_left le_rfl,
      hXM.trans (le_normalizer_conjClosure _ M), inf_le_left⟩
  obtain ⟨⟨-, hUB, hXU, hUC⟩, hmax⟩ := hUmax
  have hconj : ∀ m ∈ M, I.map (MulAut.conj m).toMonoidHom ≤ U := by
    intro m hm
    have hmX := hMX hm
    have hWB := map_conj_le_conjClosure (I := I) hm
    have hXW := le_normalizer_map_conj hmX hXI
    have hP : C ≤ U ⊔ I.map (MulAut.conj m).toMonoidHom ∧
        U ⊔ I.map (MulAut.conj m).toMonoidHom ≤ B ∧
        X ≤ normalizer ((U ⊔ I.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ∧
        (U ⊔ I.map (MulAut.conj m).toMonoidHom) ⊓ centralizer (X : Set G) ≤ C :=
      ⟨hCU.trans le_sup_left, sup_le hUB hWB,
        (le_inf hXU hXW).trans (inf_normalizer_le_normalizer_sup _ _),
        sup_inf_centralizer_le hab hUB hWB hXU hXW (commutator_map_conj hmX hIX)
          (map_conj_inf_lt hmX hlt) (irr_map_conj hmX hirr)
          (map_conj_inf_le_conjClosure hm hmX) hCU hUC⟩
    exact le_sup_right.trans (hmax hP le_sup_left)
  have hBU : B ≤ U := conjClosure_le fun m hm i hi => hconj m hm ⟨i, hi, rfl⟩
  exact (inf_le_inf_right _ hBU).trans hUC

end CFSG.Quasithin.Vol2.Ch11.OE1
