module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.Quasithin.EmptyFaithful.S153EB6D
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

@[expose] def Nk (K : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup (MulAut W) := K ⊓ centSub U

theorem Nk_conj_mem {K : Subgroup (MulAut W)} {U : Subgroup W} (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U)
    {k n : MulAut W} (hk : k ∈ K) (hn : n ∈ Nk K U) : k * n * k⁻¹ ∈ Nk K U := by
  refine ⟨K.mul_mem (K.mul_mem hk hn.1) (K.inv_mem hk), fun u hu => ?_⟩
  have h1 : k⁻¹ u ∈ U := hKU k⁻¹ (K.inv_mem hk) u hu
  have h2 := hn.2 _ h1
  show k (n (k⁻¹ u)) = u
  rw [h2]
  simp

theorem Nk_inf_eq_bot {K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} (hsup : W₁ ⊔ W₂ = ⊤)
    {x : MulAut W} (h1 : x ∈ Nk K W₁) (h2 : x ∈ Nk K W₂) : x = 1 := by
  have hfix : (fixV (Subgroup.zpowers x)) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hc : (Subgroup.zpowers x) ≤ centSub W₁ := Subgroup.zpowers_le.2 h1.2
      exact hc (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) m) u hu
    · intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hc : (Subgroup.zpowers x) ≤ centSub W₂ := Subgroup.zpowers_le.2 h2.2
      exact hc (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) m) u hu
  ext w
  have : w ∈ fixV (Subgroup.zpowers x) := by rw [hfix]; exact Subgroup.mem_top w
  exact this x (Subgroup.mem_zpowers x)

theorem commV_invariant_of_comm {a h : MulAut W} (hc : h * a = a * h) {r : W}
    (hr : r ∈ commV (Subgroup.zpowers a)) : h r ∈ commV (Subgroup.zpowers a) :=
  CFSG.Quasithin.apply_mem_commV_zpowers_of_commute hc hr

section CommV

variable {a : MulAut W} {U : Subgroup W}

theorem commIn_le (ha2 : a ^ 2 = 1) (haU : ∀ u ∈ U, a u ∈ U) :
    commIn153 (Subgroup.zpowers a) U ≤ U := by
  have hst : Subgroup.zpowers a ≤ stabSub U := Subgroup.zpowers_le.2 (mem_stabSub_of_sq ha2 haU)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨y, hy, w, hw, rfl⟩
  exact U.mul_mem ((hst hy w).2 hw) (U.inv_mem hw)

theorem commV_le_sup {W₁ W₂ : Subgroup W} (hsup : W₁ ⊔ W₂ = ⊤) (ha2 : a ^ 2 = 1)
    (ha₁ : ∀ u ∈ W₁, a u ∈ W₁) (ha₂ : ∀ u ∈ W₂, a u ∈ W₂) :
    commV (Subgroup.zpowers a) ≤ commIn153 (Subgroup.zpowers a) W₁ ⊔
      commIn153 (Subgroup.zpowers a) W₂ := by
  have hst₁ : Subgroup.zpowers a ≤ stabSub W₁ := Subgroup.zpowers_le.2 (mem_stabSub_of_sq ha2 ha₁)
  have hst₂ : Subgroup.zpowers a ≤ stabSub W₂ := Subgroup.zpowers_le.2 (mem_stabSub_of_sq ha2 ha₂)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨y, hy, w, rfl⟩
  have hw : w ∈ W₁ ⊔ W₂ := by rw [hsup]; exact Subgroup.mem_top w
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.1 hw
  have h1 : y (w₁ * w₂) * (w₁ * w₂)⁻¹ = (y w₁ * w₁⁻¹) * (y w₂ * w₂⁻¹) := by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  rw [h1]
  exact Subgroup.mul_mem_sup
    (Subgroup.subset_closure ⟨y, hy, w₁, hw₁, rfl⟩) (Subgroup.subset_closure ⟨y, hy, w₂, hw₂, rfl⟩)

end CommV

end S153EB6

end CFSG.Quasithin
