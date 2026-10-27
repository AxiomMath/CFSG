module

public import Certificates.Kernel.Co1ThreeK.Forest
public import Certificates.Kernel.Co1ThreeK.Coset
public import CFSG.Certificates.Kernel.Co1Three.ActSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl

theorem NF_sub : ∀ x ∈ NF, x ∈ NZ := by decide +kernel

theorem NF_lt : ∀ x ∈ NF, x.1 < 9 := by decide +kernel

theorem RT_eq : CF.RT = [81, 243, 327] := by decide +kernel

theorem forest_NF : forestK 3 ([0, 1, 2, 3, 4, 5] : List Nat).length NF CF.RT CF.DP CF.FT = true := by
  have h := kForest
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem forest_conj {M : Type*} [Group M] (ι : M →* Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hι : Function.Injective ι) (f : Nat → M) (hf : ∀ k < 9, matK (TS k) = ι (f k))
    (hc : ∀ x ∈ ([0, 1, 2, 3, 4, 5] : List Nat), ∀ y ∈ ([0, 1, 2, 3, 4, 5] : List Nat),
      Commute (f x) (f y))
    (ho : ∀ x ∈ ([0, 1, 2, 3, 4, 5] : List Nat), f x ^ 3 = 1) {c : Nat} (h1 : 1 ≤ c)
    (h2 : c < 729) : ∃ r ∈ ([81, 243, 327] : List Nat),
      IsConj (epM f 3 [0, 1, 2, 3, 4, 5] r 1) (epM f 3 [0, 1, 2, 3, 4, 5] c 1) := by
  have hnorm : normK TS 3 EG NZ = true := by
    have h := kNorm
    simp only [Bool.and_eq_true] at h
    exact h.2
  have hG : ∀ g ∈ ([0, 1, 2, 3, 4, 5] : List Nat), g < 9 := by decide
  have hep : ∀ v, epM (fun k => matK (TS k)) 3 [0, 1, 2, 3, 4, 5] v 1 =
      ι (epM f 3 [0, 1, 2, 3, 4, 5] v 1) := fun v => by
    rw [← epM_map ι f 3 _ v 1, map_one]
    exact epM_congr 3 _ (fun g hg => hf g (hG g hg)) v 1
  have hnz : ∀ x ∈ NF, x.2.length = ([0, 1, 2, 3, 4, 5] : List Nat).length ∧
      ∀ j < x.2.length, f (([0, 1, 2, 3, 4, 5] : List Nat).getD j 0) * f x.1 =
        f x.1 * epM f 3 [0, 1, 2, 3, 4, 5] (x.2.getD j 0) 1 := by
    intro x hx
    obtain ⟨hl, h⟩ := normK_sound hnorm x (NF_sub x hx)
    refine ⟨hl, fun j hj => hι ?_⟩
    have e := h j hj
    have hj6 : ([0, 1, 2, 3, 4, 5] : List Nat).getD j 0 < 9 := by
      by_cases hj' : j < 6
      · interval_cases j <;> decide
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        decide
    change matK (TS (([0, 1, 2, 3, 4, 5] : List Nat).getD j 0)) * matK (TS x.1) =
      matK (TS x.1) * epM (fun k => matK (TS k)) 3 [0, 1, 2, 3, 4, 5] (x.2.getD j 0) 1 at e
    rw [hf _ hj6, hf _ (NF_lt x hx), hep] at e
    rw [map_mul, map_mul]
    exact e
  obtain ⟨r, hr, hconj⟩ := forest_isConj f (by norm_num) [0, 1, 2, 3, 4, 5] hc ho forest_NF hnz c h1
    h2
  exact ⟨r, RT_eq ▸ hr, hconj⟩

end CertificateChecks.KernelCo1ThreeK

end
