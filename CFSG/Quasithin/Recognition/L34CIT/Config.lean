module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open

structure Config (A : Type) [Group A] where
  T : Sylow 2 A
  L : Subgroup A
  M : Subgroup A
  card_T : Nat.card T = 64
  L_le : L ≤ T
  M_le : M ≤ T
  isElemAbelian_L : IsElemAbelian 2 L
  isElemAbelian_M : IsElemAbelian 2 M
  card_L : Nat.card L = 16
  card_M : Nat.card M = 16
  eq_or_eq : ∀ E : Subgroup A, E ≤ T → IsElemAbelian 2 E → Nat.card E = 16 → E = L ∨ E = M
  card_inf : Nat.card ↥(L ⊓ M) = 4
  inf_le_centralizer : L ⊓ M ≤ centralizer (T : Set A)
  mul_self_mem : ∀ x ∈ T, x * x ∈ L ⊓ M
  mem_or_mem : ∀ x ∈ T, x * x = 1 → x ∈ L ∨ x ∈ M
  centralizer_L : ∀ x ∈ L, x ∉ L ⊓ M → centralizer {x} ⊓ T = L
  centralizer_M : ∀ y ∈ M, y ∉ L ⊓ M → centralizer {y} ⊓ T = M
  isPGroup_centralizer : ∀ e : A, e * e = 1 → e ≠ 1 → IsPGroup 2 (centralizer {e})
  centralizer_L_le : centralizer (L : Set A) ≤ L
  centralizer_M_le : centralizer (M : Set A) ≤ M
  quotL : ↥(normalizer (L : Set A)) →* alternatingGroup (Fin 5)
  quotL_surjective : Function.Surjective quotL
  ker_quotL : quotL.ker = L.subgroupOf (normalizer (L : Set A))
  quotM : ↥(normalizer (M : Set A)) →* alternatingGroup (Fin 5)
  quotM_surjective : Function.Surjective quotM
  ker_quotM : quotM.ker = M.subgroupOf (normalizer (M : Set A))
  exists_conj_L : ∀ x ∈ L, ∀ y ∈ L, x ≠ 1 → y ≠ 1 →
    ∃ k ∈ normalizer (L : Set A), k * x * k⁻¹ = y
  exists_conj_M : ∀ x ∈ M, ∀ y ∈ M, x ≠ 1 → y ≠ 1 →
    ∃ k ∈ normalizer (M : Set A), k * x * k⁻¹ = y
  exists_fpf_L : ∃ f ∈ normalizer (L : Set A), ∀ l ∈ L, f * l = l * f → l = 1
  exists_fpf_M : ∃ f ∈ normalizer (M : Set A), ∀ l ∈ M, f * l = l * f → l = 1

namespace Config

variable {A : Type} [Group A] (C : Config A)

abbrev Z : Subgroup A := C.L ⊓ C.M

@[simp] theorem coe_Z : (C.Z : Set A) = (C.L : Set A) ∩ (C.M : Set A) := rfl

theorem card_Z : Nat.card C.Z = 4 := C.card_inf

theorem Z_le_L : C.Z ≤ C.L := inf_le_left

theorem Z_le_M : C.Z ≤ C.M := inf_le_right

theorem Z_le_T : C.Z ≤ C.T := C.Z_le_L.trans C.L_le

theorem mul_self_eq_one_of_mem_Z {z : A} (hz : z ∈ C.Z) : z * z = 1 := by
  have h := C.isElemAbelian_L.2 z (C.Z_le_L hz)
  simpa [pow_two] using h

theorem mem_Z_iff {x : A} :
    x ∈ C.Z ↔ x ∈ C.T ∧ ∀ y ∈ C.T, x * y = y * x := by
  constructor
  · intro hx
    refine ⟨C.Z_le_T hx, fun y hy => ?_⟩
    have hx' : x ∈ centralizer (C.T : Set A) := C.inf_le_centralizer hx
    exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm
  · rintro ⟨hxT, hcomm⟩
    have hnotL : ¬ C.L ≤ C.Z := by
      intro hle
      have hcard : Nat.card C.Z = Nat.card C.L := by
        rw [show C.Z = C.L from le_antisymm inf_le_left hle]
      rw [C.card_Z, C.card_L] at hcard
      norm_num at hcard
    obtain ⟨y, hyL, hyZ⟩ := SetLike.not_le_iff_exists.mp hnotL
    have hxL : x ∈ C.L := by
      have hxcent : x ∈ centralizer ({y} : Set A) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (hcomm y (C.L_le hyL)).symm
      have hxinf : x ∈ centralizer ({y} : Set A) ⊓ C.T := ⟨hxcent, hxT⟩
      rwa [C.centralizer_L y hyL hyZ] at hxinf
    have hnotM : ¬ C.M ≤ C.Z := by
      intro hle
      have hcard : Nat.card C.Z = Nat.card C.M := by
        rw [show C.Z = C.M from le_antisymm inf_le_right hle]
      rw [C.card_Z, C.card_M] at hcard
      norm_num at hcard
    obtain ⟨y, hyM, hyZ⟩ := SetLike.not_le_iff_exists.mp hnotM
    have hxM : x ∈ C.M := by
      have hxcent : x ∈ centralizer ({y} : Set A) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (hcomm y (C.M_le hyM)).symm
      have hxinf : x ∈ centralizer ({y} : Set A) ⊓ C.T := ⟨hxcent, hxT⟩
      rwa [C.centralizer_M y hyM hyZ] at hxinf
    exact ⟨hxL, hxM⟩

theorem L_ne_M : C.L ≠ C.M := by
  intro h
  have hZ : C.Z = C.L := by
    change C.L ⊓ C.M = C.L
    rw [← h, inf_idem]
  have hcard : Nat.card C.Z = Nat.card C.L := by rw [hZ]
  rw [C.card_Z, C.card_L] at hcard
  norm_num at hcard

private theorem map_conj_eq_self_of_two [Finite A] {t : A} (ht : t ∈ C.T) {E F : Subgroup A}
    (hEt : E ≤ C.T) (hEea : IsElemAbelian 2 E) (hEcard : Nat.card E = 16)
    (hEF : E ≠ F) (hZEF : E ⊓ F = C.Z)
    (honly : ∀ X : Subgroup A, X ≤ C.T → IsElemAbelian 2 X → Nat.card X = 16 →
      X = E ∨ X = F) :
    E.map (MulAut.conj t).toMonoidHom = E := by
  have hE'le : E.map (MulAut.conj t).toMonoidHom ≤ C.T := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    exact C.T.mul_mem (C.T.mul_mem ht (hEt he)) (C.T.inv_mem ht)
  have hE'ea : IsElemAbelian 2 (E.map (MulAut.conj t).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hEea (MulAut.conj t).toMonoidHom
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom :=
    fun x y h => (MulAut.conj t).injective h
  have hE'card : Nat.card (E.map (MulAut.conj t).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (G := A) (H := A) (K := E)
      (f := (MulAut.conj t).toMonoidHom) hinj, hEcard]
  rcases honly _ hE'le hE'ea hE'card with h | h
  · exact h
  · exfalso
    have hZE : C.Z ≤ E := by rw [← hZEF]; exact inf_le_left
    have ht2Z : t * t ∈ C.Z := C.mul_self_mem t ht
    have ht2E : t * t ∈ E := hZE ht2Z
    have ht2norm : t * t ∈ normalizer (E : Set A) := Subgroup.le_normalizer ht2E
    have hfix2 : E.map (MulAut.conj (t * t)).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ht2norm
    have hF'E : F.map (MulAut.conj t).toMonoidHom = E := by
      calc
        F.map (MulAut.conj t).toMonoidHom
            = (E.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
                rw [h]
        _ = E.map ((MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom) := by
                rw [Subgroup.map_map]
        _ = E.map (MulAut.conj (t * t)).toMonoidHom := by
                congr 1
                ext x
                simp [MulAut.conj_apply, mul_assoc]
        _ = E := hfix2
    have hleZ : E.map (MulAut.conj t).toMonoidHom ≤ C.Z := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      have hmF : t * e * t⁻¹ ∈ F := by
        have hm' : t * e * t⁻¹ ∈ E.map (MulAut.conj t).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨e, he, MulAut.conj_apply t e⟩
        rwa [h] at hm'
      have hl'E : t * (t * e * t⁻¹) * t⁻¹ ∈ E := by
        have hl' : t * (t * e * t⁻¹) * t⁻¹ ∈ F.map (MulAut.conj t).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨t * e * t⁻¹, hmF, MulAut.conj_apply t (t * e * t⁻¹)⟩
        rwa [hF'E] at hl'
      have hsq : (t * e) * (t * e) =
          (t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹) * (t * t) := by group
      have hsqZ : (t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹) * (t * t) ∈ C.Z := by
        rw [← hsq]
        exact C.mul_self_mem (t * e) (C.T.mul_mem ht (hEt he))
      have hmlZ : (t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹) ∈ C.Z := by
        have heq : (t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹) =
            ((t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹) * (t * t)) * (t * t)⁻¹ := by
          group
        rw [heq]
        exact C.Z.mul_mem hsqZ (C.Z.inv_mem ht2Z)
      have hmlE : (t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹) ∈ E := hZE hmlZ
      have hmE : t * e * t⁻¹ ∈ E := by
        have := E.mul_mem hmlE (E.inv_mem hl'E)
        simpa [mul_assoc] using this
      have hmZ : t * e * t⁻¹ ∈ C.Z := by
        rw [← hZEF]
        exact ⟨hmE, hmF⟩
      simpa [MulAut.conj_apply] using hmZ
    have hcard := Subgroup.card_map_of_injective (G := A) (H := A) (K := E)
      (f := (MulAut.conj t).toMonoidHom) hinj
    rw [hEcard] at hcard
    have hle : Nat.card (E.map (MulAut.conj t).toMonoidHom) ≤ Nat.card C.Z :=
      Subgroup.card_le_of_le hleZ
    rw [hcard, C.card_Z] at hle
    norm_num at hle

theorem T_le_normalizer_L [Finite A] : (C.T : Subgroup A) ≤ normalizer (C.L : Set A) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact map_conj_eq_self_of_two C ht C.L_le C.isElemAbelian_L C.card_L C.L_ne_M rfl
    (fun X hX hEA hXc => C.eq_or_eq X hX hEA hXc)

theorem T_le_normalizer_M [Finite A] : (C.T : Subgroup A) ≤ normalizer (C.M : Set A) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine map_conj_eq_self_of_two C ht C.M_le C.isElemAbelian_M C.card_M C.L_ne_M.symm ?_ ?_
  · simpa [Config.Z, inf_comm]
  · intro X hX hEA hXc
    rcases C.eq_or_eq X hX hEA hXc with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem L_le_normalizer_M [Finite A] : C.L ≤ normalizer (C.M : Set A) :=
  C.L_le.trans C.T_le_normalizer_M

theorem M_le_normalizer_L [Finite A] : C.M ≤ normalizer (C.L : Set A) :=
  C.M_le.trans C.T_le_normalizer_L

theorem sup_eq [Finite A] : C.L ⊔ C.M = C.T := by
  have hcard :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := C.L) (K := C.M) C.L_le_normalizer_M
  have h1 : Nat.card C.L = 16 := C.card_L
  have h2 : Nat.card C.M = 16 := C.card_M
  have h3 : Nat.card ↥(C.L ⊓ C.M) = 4 := C.card_inf
  rw [h1, h2, h3] at hcard
  have hcard' : Nat.card (C.L ⊔ C.M : Subgroup A) = 64 := by omega
  have hT : Nat.card C.T = 64 := C.card_T
  refine Subgroup.eq_of_le_of_card_ge (sup_le C.L_le C.M_le) ?_
  omega

theorem card_normalizer_L : Nat.card ↥(normalizer (C.L : Set A)) = 960 := by
  have h := Subgroup.card_ker_mul_card_range C.quotL
  rw [C.ker_quotL] at h
  have hker : Nat.card (C.L.subgroupOf (normalizer (C.L : Set A))) = 16 := by
    rw [← C.card_L]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hrange : Nat.card C.quotL.range = 60 := by
    rw [MonoidHom.range_eq_top_of_surjective C.quotL C.quotL_surjective, Subgroup.card_top]
    rw [show Nat.card (alternatingGroup (Fin 5)) = 60 from by
      rw [nat_card_alternatingGroup]
      norm_num]
  rw [hker, hrange] at h
  omega

noncomputable def isSylow_normalizer_L [Finite A] :
    Sylow 2 ↥(normalizer (C.L : Set A)) :=
  C.T.subtype C.T_le_normalizer_L

@[simp] theorem coe_isSylow_normalizer_L [Finite A] :
    (C.isSylow_normalizer_L : Subgroup ↥(normalizer (C.L : Set A))) =
      (C.T : Subgroup A).subgroupOf (normalizer (C.L : Set A)) :=
  Sylow.coe_subtype (P := C.T) (N := normalizer (C.L : Set A)) (h := C.T_le_normalizer_L)

noncomputable def isSylow_normalizer_M [Finite A] :
    Sylow 2 ↥(normalizer (C.M : Set A)) :=
  C.T.subtype C.T_le_normalizer_M

@[simp] theorem coe_isSylow_normalizer_M [Finite A] :
    (C.isSylow_normalizer_M : Subgroup ↥(normalizer (C.M : Set A))) =
      (C.T : Subgroup A).subgroupOf (normalizer (C.M : Set A)) :=
  Sylow.coe_subtype (P := C.T) (N := normalizer (C.M : Set A)) (h := C.T_le_normalizer_M)

end Config

end CFSG.Quasithin.L34CIT
