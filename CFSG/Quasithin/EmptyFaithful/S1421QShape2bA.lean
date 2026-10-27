module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bF

public section

namespace CFSG.Quasithin.F146Field.Case2b.Shape

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem le_of_sup_of_comm {K A N : Subgroup G} (hAK : A ≤ K) (hNK : N ≤ K) (hsup : A ⊔ N = K)
    (hperf : ⁅K, K⁆ = K) (hcomm : ∀ n ∈ N, ∀ k ∈ K, ⁅n, k⁆ ∈ A) : K ≤ A := by
  have hAn : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A := fun n hn a ha => by
    have h := A.mul_mem (hcomm n hn a (hAK ha)) ha
    simpa [commutatorElement_def, mul_assoc] using h
  have hnorm : K ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hsup]
    refine sup_le Subgroup.le_normalizer fun n hn => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hAn n hn h, fun h' => ?_⟩
    have := hAn n⁻¹ (N.inv_mem hn) _ h'
    simpa [mul_assoc] using this
  have hconj : ∀ x ∈ K, ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun x hx a ha =>
    (Subgroup.mem_normalizer_iff.mp (hnorm hx) a).mp ha
  let S : Subgroup G :=
    { carrier := {x | x ∈ K ∧ ∀ y ∈ K, ⁅x, y⁆ ∈ A}
      one_mem' := ⟨K.one_mem, fun y _ => by simp⟩
      mul_mem' := fun {x x'} hx hx' => by
        refine ⟨K.mul_mem hx.1 hx'.1, fun y hy => ?_⟩
        have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact A.mul_mem (hconj x hx.1 _ (hx'.2 y hy)) (hx.2 y hy)
      inv_mem' := fun {x} hx => by
        refine ⟨K.inv_mem hx.1, fun y hy => ?_⟩
        have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hconj x⁻¹ (K.inv_mem hx.1) _ (A.inv_mem (hx.2 y hy)) }
  have hS : K ≤ S := by
    rw [← hsup]
    refine sup_le (fun a ha => ⟨hAK ha, fun y hy => ?_⟩)
      (fun n hn => ⟨hNK hn, hcomm n hn⟩)
    have e : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem ha (hconj y hy a⁻¹ (A.inv_mem ha))
  have h : ⁅K, K⁆ ≤ A := Subgroup.commutator_le.mpr fun x hx y hy => (hS hx).2 y hy
  rwa [hperf] at h

end Generic

section Dict

variable {G : Type} [Group G] {M H K : Subgroup G}

theorem Khat_mono (hKH : K ≤ H) {P Q : Subgroup (E2.StarQuot M H)} (h : P ≤ Q) :
    Khat M hKH P ≤ Khat M hKH Q :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem inf_ker_le_Khat (hKH : K ≤ H) (P : Subgroup (E2.StarQuot M H)) :
    kerIn M H ⊓ K ≤ Khat M hKH P := by
  intro x hx
  refine mem_Khat.mpr ⟨hx.2, ?_⟩
  have h1 : ((⟨x, hKH hx.2⟩ : ↥H) : E2.StarQuot M H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx.1)
  rw [h1]
  exact one_mem _

theorem star_Khat (hKH : K ≤ H) {P : Subgroup (E2.StarQuot M H)} (hP : P ≤ E2.star M H K) :
    E2.star M H (Khat M hKH P) = P := by
  rw [Khat, star_map_subtype (hKH := hKH), Subgroup.map_comap_eq, range_rho,
    inf_eq_right.mpr hP]

theorem Khat_star (hKH : K ≤ H) {A : Subgroup G} (hAK : A ≤ K) (hA : kerIn M H ⊓ K ≤ A) :
    Khat M hKH (E2.star M H A) = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxK, hxs⟩ := mem_Khat.mp hx
    obtain ⟨h, hhA, hhx⟩ := Case2a.exists_of_mem_star hxs
    have hker : (h : G)⁻¹ * x ∈ kerIn M H :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hhx)
    have hKmem : (h : G)⁻¹ * x ∈ K := K.mul_mem (K.inv_mem (hAK hhA)) hxK
    simpa using A.mul_mem hhA (hA ⟨hker, hKmem⟩)
  · intro hx
    exact mem_Khat.mpr ⟨hAK hx, GoldS146R.mem_imgJ.mpr ⟨⟨x, hKH (hAK hx)⟩, hx, rfl⟩⟩

theorem covBy_star (hKH : K ≤ H) {A : Subgroup G} (hAK : A ≤ K) (hA : kerIn M H ⊓ K ≤ A)
    (h : A ⋖ K) : E2.star M H A ⋖ E2.star M H K := by
  have hKK : Khat M hKH (E2.star M H K) = K := Khat_star hKH le_rfl inf_le_right
  have hAA : Khat M hKH (E2.star M H A) = A := Khat_star hKH hAK hA
  refine ⟨lt_of_le_of_ne (GoldS146R.imgJ_mono hAK) fun heq => h.ne ?_, fun B hAB hBK => ?_⟩
  · calc A = Khat M hKH (E2.star M H A) := hAA.symm
      _ = Khat M hKH (E2.star M H K) := by rw [heq]
      _ = K := hKK
  · have hBB : E2.star M H (Khat M hKH B) = B := star_Khat hKH hBK.le
    have h1 : A < Khat M hKH B := by
      refine lt_of_le_of_ne ?_ fun hEq => hAB.ne ?_
      · calc A = Khat M hKH (E2.star M H A) := hAA.symm
          _ ≤ Khat M hKH B := Khat_mono hKH hAB.le
      · calc E2.star M H A = E2.star M H (Khat M hKH B) := by rw [← hEq]
          _ = B := hBB
    have h2 : Khat M hKH B < K := by
      refine lt_of_le_of_ne Khat_le fun hEq => hBK.ne ?_
      calc B = E2.star M H (Khat M hKH B) := hBB.symm
        _ = E2.star M H K := by rw [hEq]
    exact h.2 h1 h2

theorem covBy_Khat (hKH : K ≤ H) {P : Subgroup (E2.StarQuot M H)} (hPK : P ≤ E2.star M H K)
    (h : P ⋖ E2.star M H K) : Khat M hKH P ⋖ K := by
  have hPP : E2.star M H (Khat M hKH P) = P := star_Khat hKH hPK
  refine ⟨lt_of_le_of_ne Khat_le fun heq => h.ne ?_, fun C hPC hCK => ?_⟩
  · calc P = E2.star M H (Khat M hKH P) := hPP.symm
      _ = E2.star M H K := by rw [heq]
  · have hCC : Khat M hKH (E2.star M H C) = C :=
      Khat_star hKH hCK.le ((inf_ker_le_Khat hKH P).trans hPC.le)
    have h1 : P < E2.star M H C := by
      refine lt_of_le_of_ne ?_ fun hEq => hPC.ne ?_
      · calc P = E2.star M H (Khat M hKH P) := hPP.symm
          _ ≤ E2.star M H C := GoldS146R.imgJ_mono hPC.le
      · calc Khat M hKH P = Khat M hKH (E2.star M H C) := by rw [hEq]
          _ = C := hCC
    have h2 : E2.star M H C < E2.star M H K := by
      refine lt_of_le_of_ne (GoldS146R.imgJ_mono hCK.le) fun hEq => hCK.ne ?_
      calc C = Khat M hKH (E2.star M H C) := hCC.symm
        _ = Khat M hKH (E2.star M H K) := by rw [hEq]
        _ = K := Khat_star hKH le_rfl inf_le_right
    exact h.2 h1 h2

end Dict

end CFSG.Quasithin.F146Field.Case2b.Shape
