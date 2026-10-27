module

public import CFSG.Quasithin.Recognition.M22WittLocal
public import CFSG.Quasithin.Recognition.HSType15c
public import CFSG.Quasithin.Recognition.HSType16a

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam MulAction
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

variable {G : Type*} [Group G]

theorem le_of_lt_L1
    {L L₁ X : Subgroup G}
    (Φ : ↥L ≃* ↥(stabilizer M22 (0 : Fin 22)))
    (hΦ : ∀ x : ↥L, (x : G) ∈ L₁ ↔ ((Φ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab)
    (hX : L₁ ≤ X) {y : G} (hyL : y ∈ L) (hyX : y ∈ X) (hy1 : y ∉ L₁) : L ≤ X := by
  intro k hk
  by_cases hk1 : k ∈ L₁
  · exact hX hk1
  have hk1' : ((Φ ⟨k, hk⟩ : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∉ m22TwoStab := fun h' =>
    hk1 ((hΦ ⟨k, hk⟩).mpr h')
  have hy1' : ((Φ ⟨y, hyL⟩ : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∉ m22TwoStab := fun h' =>
    hy1 ((hΦ ⟨y, hyL⟩).mpr h')
  obtain ⟨a, ha, b, hb, hab⟩ := M22Witt.exists_double_coset_two (Φ ⟨k, hk⟩).2 hk1'
    (Φ ⟨y, hyL⟩).2 hy1'
  set a' : ↥(stabilizer M22 (0 : Fin 22)) := ⟨a, (Subgroup.mem_inf.mp ha).1⟩
  set b' : ↥(stabilizer M22 (0 : Fin 22)) := ⟨b, (Subgroup.mem_inf.mp hb).1⟩
  have he : Φ ⟨k, hk⟩ = a' * Φ ⟨y, hyL⟩ * b' := Subtype.ext hab
  have hk' : (⟨k, hk⟩ : ↥L) = Φ.symm a' * ⟨y, hyL⟩ * Φ.symm b' := by
    apply Φ.injective
    rw [he, map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have ha'X : ((Φ.symm a' : ↥L) : G) ∈ X :=
    hX ((hΦ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact ha))
  have hb'X : ((Φ.symm b' : ↥L) : G) ∈ X :=
    hX ((hΦ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact hb))
  have := congrArg Subtype.val hk'
  simp only [Subgroup.coe_mul] at this
  rw [this]
  exact X.mul_mem (X.mul_mem ha'X hyX) hb'X

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

include M in
theorem L2_not_le_hsNB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN) :
    ¬ M.L1.map (MulAut.conj g).toMonoidHom ≤ hsNB z s := by
  intro hle
  have hB' : ∀ x ∈ M.L1.map (MulAut.conj g).toMonoidHom, ∀ u ∈ (hsB z s).map
      (MulAut.conj g).toMonoidHom, x * u * x⁻¹ ∈ (hsB z s).map (MulAut.conj g).toMonoidHom := by
    intro x hx u hu
    rw [mem_map_conj_iff] at hx hu ⊢
    have := conj_mem_hsB_of_mem (M.L1_le_hsNB hx) hu
    rwa [show g⁻¹ * x * g * (g⁻¹ * u * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * u * x⁻¹) * g by
      group] at this
  have hNN : M.L1.map (MulAut.conj g).toMonoidHom ≤ M.NN := by
    intro x hx
    refine M.mem_NN_of_normalizes (hle hx) (Subgroup.mem_normalizer_iff.mpr fun u => ?_)
    rw [← M.hsB_inf_hsB' h hsmemH hsnotK hss hg₀ hg hgNN]
    constructor
    · rintro ⟨hu₁, hu₂⟩
      exact ⟨conj_mem_hsB_of_mem (hle hx) hu₁, hB' x hx u hu₂⟩
    · rintro ⟨hu₁, hu₂⟩
      have hxi : x⁻¹ ∈ M.L1.map (MulAut.conj g).toMonoidHom := Subgroup.inv_mem _ hx
      refine ⟨?_, ?_⟩
      · have := conj_mem_hsB_of_mem (hle hxi) hu₁
        rwa [show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group] at this
      · have := hB' x⁻¹ hxi _ hu₂
        rwa [show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group] at this
  have h1 := Subgroup.card_le_of_le hNN
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    M.card_L1 h hsmemH hsnotK hss hg₀, M.card_NN h hsmemH hsnotK hss hg₀] at h1
  omega

include M in
theorem inf_hsNB_le_L1
    [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN)
    (Φ : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) ≃* ↥(stabilizer M22 (0 : Fin 22)))
    (hΦ : ∀ x : ↥(M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom), (x : G) ∈ M.L1 ↔
      ((Φ x : ↥(stabilizer M22 (0 : Fin 22))) : M22) ∈ m22TwoStab) {y : G}
    (hyL : y ∈ M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) (hyN : y ∈ hsNB z s) :
    y ∈ M.L1 := by
  by_contra hy1
  have hle := le_of_lt_L1 (X := (M.L1 ⊔ M.L1.map (MulAut.conj g).toMonoidHom) ⊓ hsNB z s) Φ hΦ
    (le_inf le_sup_left M.L1_le_hsNB) hyL ⟨hyL, hyN⟩ hy1
  exact M.L2_not_le_hsNB h hsmemH hsnotK hss hg₀ hg hgNN fun x hx =>
    (hle (Subgroup.mem_sup_right hx)).2

include M in
theorem mem_pre_alt_cases {y : ↥(hsNB z s)} (hyst : M.π y ∈ stabS)
    (hyalt : M.π y ∈ alternatingGroup (Fin 6)) (hyl : M.π y ∉ lamS) {w : G}
    (hw : w ∈ M.pre (alternatingGroup (Fin 6))) :
    w ∈ M.L1 ∨ ∃ a ∈ M.L1, ∃ b ∈ M.L1, w = a * y * b := by
  obtain ⟨hwN, hwπ⟩ := M.mem_pre.mp hw
  rcases alt_eq_union hwπ with hl | ⟨b, hb, hab⟩
  · exact Or.inl (M.mem_pre.mpr ⟨hwN, hl⟩)
  right
  have hℓ := mul_ρS0_inv_mem_lam0 hyst hyalt hyl
  obtain ⟨u, hu⟩ := M.π_surj (M.π ⟨w, hwN⟩ * (ρS0 * b)⁻¹ * (M.π y * ρS0⁻¹)⁻¹)
  obtain ⟨v, hv⟩ := M.π_surj b
  have huL : (u : G) ∈ M.L1 := M.mem_pre.mpr ⟨u.2, by
    rw [show (⟨(u : G), u.2⟩ : ↥(hsNB z s)) = u from rfl, hu]
    exact lamS.mul_mem hab (lamS.inv_mem hℓ.1)⟩
  have hvL : (v : G) ∈ M.L1 := M.mem_pre.mpr ⟨v.2, by
    rw [show (⟨(v : G), v.2⟩ : ↥(hsNB z s)) = v from rfl, hv]
    exact cosetB_mem b hb⟩
  have hπ : M.π ⟨w, hwN⟩ = M.π (u * y * v) := by
    rw [map_mul, map_mul, hu, hv]
    group
  have hB : w * ((u : G) * y * v)⁻¹ ∈ hsB z s :=
    (M.ker (⟨w, hwN⟩ * (u * y * v)⁻¹)).mp (by rw [map_mul, map_inv, hπ, mul_inv_cancel])
  exact ⟨w * ((u : G) * y * v)⁻¹ * u, M.L1.mul_mem (M.hsB_le_L1 hB) huL, v, hvL, by group⟩

end S6Model

end HSSetting

end CFSG.Quasithin.HSType
