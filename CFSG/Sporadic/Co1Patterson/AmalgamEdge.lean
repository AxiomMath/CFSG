module

public import CFSG.Sporadic.Co1Patterson.AmalgamKey

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

variable {G X : Type*} [Group G] [Group X] {A Z : G → X} {a e w : G} {t W : X}

@[expose] def homOfMulOn (f : G → X) (B : Subgroup G)
    (hf : ∀ x ∈ B, ∀ y ∈ B, f (x * y) = f x * f y) : B →* X where
  toFun x := f x
  map_one' := by
    have h := hf 1 B.one_mem 1 B.one_mem
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  map_mul' x y := hf x x.2 y y.2

@[simp] theorem homOfMulOn_apply (f : G → X) (B : Subgroup G)
    (hf : ∀ x ∈ B, ∀ y ∈ B, f (x * y) = f x * f y) (x : B) : homOfMulOn f B hf x = f x := rfl

open Classical in
@[expose] noncomputable def edgeFun (A Z : G → X) (a τ x : G) : X :=
  if x ∈ C[a] then A x else A (x * τ⁻¹) * Z τ

theorem edgeFun_of_mem {τ x : G} (hx : x ∈ C[a]) : edgeFun A Z a τ x = A x := by
  simp only [edgeFun, hx, ↓reduceIte]

theorem edgeFun_of_not_mem {τ x : G} (hx : x ∉ C[a]) :
    edgeFun A Z a τ x = A (x * τ⁻¹) * Z τ := by
  simp only [edgeFun, hx, ↓reduceIte]

theorem edgeFun_eq_of_mem_cent {B : Subgroup G} {τ : G} (hZ : IsoOn Z C[w] C[W])
    (hagree : ∀ y ∈ C[a] ⊓ C[w], Z y = A y) (hτw : τ ∈ C[w])
    (hB2 : ∀ x ∈ B, x ∉ C[a] → x * τ⁻¹ ∈ C[a]) {x : G} (hx : x ∈ B) (hxw : x ∈ C[w]) :
    edgeFun A Z a τ x = Z x := by
  by_cases hxa : x ∈ C[a]
  · rw [edgeFun_of_mem hxa, hagree x (mem_inf.2 ⟨hxa, hxw⟩)]
  · have h : x * τ⁻¹ ∈ C[a] ⊓ C[w] :=
      mem_inf.2 ⟨hB2 x hx hxa, mul_mem hxw (inv_mem hτw)⟩
    rw [edgeFun_of_not_mem hxa, ← hagree _ h, ← hZ.map_mul _ (mem_inf.1 h).2 _ hτw,
      inv_mul_cancel_right]

section Edge

variable {B : Subgroup G} {τ : G} (hA : IsoOn A C[a] C[t]) (hZ : IsoOn Z C[w] C[W])
  (hagree : ∀ y ∈ C[a] ⊓ C[w], Z y = A y) (hτw : τ ∈ C[w]) (hτa : τ * a * τ⁻¹ = e)
  (hτe : τ * e * τ⁻¹ = a) (hτB : τ ∈ B) (hB1 : ∀ x ∈ B, x ∈ C[a] → x ∈ C[e])
  (hB2 : ∀ x ∈ B, x ∉ C[a] → x * τ⁻¹ ∈ C[a]) (hkey : KeyId A Z a e 1 τ)
include hA hZ hagree hτw hτa hτe hτB hB1 hB2 hkey

theorem edgeFun_mul : ∀ x ∈ B, ∀ y ∈ B,
    edgeFun A Z a τ (x * y) = edgeFun A Z a τ x * edgeFun A Z a τ y := by
  have hτK : ∀ k ∈ C[a] ⊓ C[e], τ * k * τ⁻¹ ∈ C[a] ⊓ C[e] := fun k hk =>
    (conj_mem_inf_iff_of hτa hτe (fun _ => by rw [inf_comm]) k).1 hk
  have hK : ∀ x ∈ B, x ∉ C[a] → x * τ⁻¹ ∈ C[a] ⊓ C[e] := fun x hx hxa =>
    mem_inf.2 ⟨hB2 x hx hxa, hB1 _ (mul_mem hx (inv_mem hτB)) (hB2 x hx hxa)⟩
  have hτ2 : τ * τ ∈ C[a] := by
    rw [mem_cent_iff]
    calc τ * τ * a = τ * (τ * a * τ⁻¹) * τ⁻¹ * (τ * τ) := by group
      _ = a * (τ * τ) := by rw [hτa, hτe]
  have hτ2w : τ * τ ∈ C[a] ⊓ C[w] := mem_inf.2 ⟨hτ2, mul_mem hτw hτw⟩
  have hkey' : ∀ k ∈ C[a] ⊓ C[e], Z τ * A k = A (τ * k * τ⁻¹) * Z τ := fun k hk => by
    rw [hkey k hk, mul_one]
    group
  intro x hx y hy
  by_cases hxa : x ∈ C[a] <;> by_cases hya : y ∈ C[a]
  · rw [edgeFun_of_mem (mul_mem hxa hya), edgeFun_of_mem hxa, edgeFun_of_mem hya,
      hA.map_mul x hxa y hya]
  · have hxy : x * y ∉ C[a] := fun h => hya (by simpa using mul_mem (inv_mem hxa) h)
    rw [edgeFun_of_mem hxa, edgeFun_of_not_mem hya, edgeFun_of_not_mem hxy, mul_assoc x,
      hA.map_mul x hxa _ (hB2 y hy hya), mul_assoc]
  · have hxy : x * y ∉ C[a] := fun h => hxa (by simpa using mul_mem h (inv_mem hya))
    have hyK : y ∈ C[a] ⊓ C[e] := mem_inf.2 ⟨hya, hB1 y hy hya⟩
    rw [edgeFun_of_not_mem hxa, edgeFun_of_mem hya, edgeFun_of_not_mem hxy]
    calc A (x * y * τ⁻¹) * Z τ = A ((x * τ⁻¹) * (τ * y * τ⁻¹)) * Z τ := by congr 2; group
      _ = A (x * τ⁻¹) * (A (τ * y * τ⁻¹) * Z τ) := by
        rw [hA.map_mul _ (hB2 x hx hxa) _ (mem_inf.1 (hτK y hyK)).1, mul_assoc]
      _ = A (x * τ⁻¹) * Z τ * A y := by rw [← hkey' y hyK, mul_assoc]
  · have h1 := hK x hx hxa
    have h2 := hK y hy hya
    have h3 := hτK _ h2
    have hxy : x * y ∈ C[a] := by
      have : x * y = (x * τ⁻¹) * (τ * (y * τ⁻¹) * τ⁻¹) * (τ * τ) := by group
      rw [this]
      exact mul_mem (mul_mem (mem_inf.1 h1).1 (mem_inf.1 h3).1) hτ2
    rw [edgeFun_of_mem hxy, edgeFun_of_not_mem hxa, edgeFun_of_not_mem hya]
    calc A (x * y) = A ((x * τ⁻¹) * (τ * (y * τ⁻¹) * τ⁻¹) * (τ * τ)) := by congr 1; group
      _ = A (x * τ⁻¹) * A (τ * (y * τ⁻¹) * τ⁻¹) * Z (τ * τ) := by
        rw [hA.map_mul _ (mul_mem (mem_inf.1 h1).1 (mem_inf.1 h3).1) _ hτ2,
          hA.map_mul _ (mem_inf.1 h1).1 _ (mem_inf.1 h3).1, hagree _ hτ2w]
      _ = A (x * τ⁻¹) * (A (τ * (y * τ⁻¹) * τ⁻¹) * Z τ) * Z τ := by
        rw [hZ.map_mul _ hτw _ hτw]; group
      _ = A (x * τ⁻¹) * Z τ * (A (y * τ⁻¹) * Z τ) := by rw [← hkey' _ h2]; group

end Edge

@[expose] def conjFun (A Z : G → X) (k y : G) : X := A k * Z (k⁻¹ * y * k) * (A k)⁻¹

theorem conjFun_mul (hZ : IsoOn Z C[w] C[W]) {k : G} :
    ∀ x ∈ C[k * w * k⁻¹], ∀ y ∈ C[k * w * k⁻¹],
      conjFun A Z k (x * y) = conjFun A Z k x * conjFun A Z k y := by
  have hc : ∀ x ∈ C[k * w * k⁻¹], k⁻¹ * x * k ∈ C[w] := fun x hx => by
    have := (mem_cent_conj_iff k⁻¹ x (k * w * k⁻¹)).1 hx
    simpa [mul_assoc] using this
  intro x hx y hy
  unfold conjFun
  rw [show k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) by group,
    hZ.map_mul _ (hc x hx) _ (hc y hy)]
  group

theorem conjFun_eq_A (hA : IsoOn A C[a] C[t]) (hagree : ∀ y ∈ C[a] ⊓ C[w], Z y = A y)
    {k : G} (hk : k ∈ C[a]) {x : G} (hx : x ∈ C[a] ⊓ C[k * w * k⁻¹]) :
    conjFun A Z k x = A x := by
  have h1 : k⁻¹ * x * k ∈ C[a] ⊓ C[w] := by
    refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hk) (mem_inf.1 hx).1) hk, ?_⟩
    have := (mem_cent_conj_iff k⁻¹ x (k * w * k⁻¹)).1 (mem_inf.1 hx).2
    simpa [mul_assoc] using this
  unfold conjFun
  rw [hagree _ h1, hA.map_mul _ (mul_mem (inv_mem hk) (mem_inf.1 hx).1) _ hk,
    hA.map_mul _ (inv_mem hk) _ (mem_inf.1 hx).1, hA.map_inv hk]
  group

theorem conjFun_eq_of {B : Subgroup G} {F : G → X}
    (hF : ∀ x ∈ B, ∀ y ∈ B, F (x * y) = F x * F y)
    (hFZ : ∀ x ∈ B, x ∈ C[w] → F x = Z x) {k : G} (hkB : k ∈ B) (hFk : F k = A k) {x : G}
    (hx : x ∈ B) (hxp : x ∈ C[k * w * k⁻¹]) : conjFun A Z k x = F x := by
  have h1 : k⁻¹ * x * k ∈ C[w] := by
    have := (mem_cent_conj_iff k⁻¹ x (k * w * k⁻¹)).1 hxp
    simpa [mul_assoc] using this
  have hm : k⁻¹ * x * k ∈ B := mul_mem (mul_mem (inv_mem hkB) hx) hkB
  have hF1 : F 1 = 1 := by
    have h := hF 1 B.one_mem 1 B.one_mem
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  have hFinv : F k⁻¹ = (F k)⁻¹ := by
    have h := hF k hkB k⁻¹ (inv_mem hkB)
    rw [mul_inv_cancel, hF1] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  unfold conjFun
  calc A k * Z (k⁻¹ * x * k) * (A k)⁻¹ = F k * F (k⁻¹ * x * k) * F k⁻¹ := by
        rw [hFinv, hFk, hFZ _ hm h1]
    _ = F (k * (k⁻¹ * x * k) * k⁻¹) := by
        rw [hF _ (mul_mem hkB hm) _ (inv_mem hkB), hF _ hkB _ hm]
    _ = F x := by congr 1; group

end CFSG.Sporadic.Co1Patterson
