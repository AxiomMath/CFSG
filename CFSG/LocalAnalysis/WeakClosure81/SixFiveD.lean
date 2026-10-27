module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s65_SixFiveD_le_normalizer_of_conj {X S : Subgroup G}
    (h : ∀ x ∈ X, ∀ s ∈ S, x * s * x⁻¹ ∈ S) : X ≤ normalizer (S : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact h x hx s
  · intro hs
    have h2 := h x⁻¹ (X.inv_mem hx) (x * s * x⁻¹) hs
    rwa [show x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s by group] at h2

theorem KOf_le_LOf (M V : Subgroup G) (g : G) : KOf M V g ≤ LOf V g := by
  unfold KOf LOf UOf BOf
  exact sup_le_sup inf_le_left inf_le_left

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem commutator_U_B_le_N (h : Hyp65 n M V₀ V g) :
    ⁅UOf M V g, BOf M V g⁆ ≤ NOf M V g := by
  rw [Subgroup.commutator_le]
  intro u hu b hb
  obtain ⟨huV, huMg⟩ := hu
  obtain ⟨hbVg, hbM⟩ := hb
  have hbN : b ∈ normalizer (V : Set G) := by rwa [h.normalizer_eq]
  have huN : u ∈ normalizer (conjSubgroup V g : Set G) := by rwa [h.swap.normalizer_eq]
  have hbuV : b * u⁻¹ * b⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hbN u⁻¹).1 (V.inv_mem huV)
  have hcV : ⁅u, b⁆ ∈ V := by
    rw [commutatorElement_def, show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group]
    exact V.mul_mem huV hbuV
  have hubVg : u * b * u⁻¹ ∈ conjSubgroup V g :=
    (Subgroup.mem_normalizer_iff.1 huN b).1 hbVg
  have hcVg : ⁅u, b⁆ ∈ conjSubgroup V g := by
    rw [commutatorElement_def]
    exact (conjSubgroup V g).mul_mem hubVg ((conjSubgroup V g).inv_mem hbVg)
  rw [NOf, Subgroup.mem_inf]
  refine ⟨⟨hcV, h.conjV_le_conjM hcVg⟩, hcVg, h.le_M hcV⟩

theorem N_le_centralizer_L (h : Hyp65 n M V₀ V g) :
    NOf M V g ≤ centralizer (LOf V g : Set G) := by
  have hNV : NOf M V g ≤ V := by
    rw [NOf, UOf]
    exact inf_le_left.trans inf_le_left
  have hNB : NOf M V g ≤ conjSubgroup V g := by
    rw [NOf, BOf]
    exact inf_le_right.trans inf_le_left
  rw [Subgroup.le_centralizer_iff]
  rw [LOf]
  refine sup_le ?_ ?_
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h.elemAbelian.comm hv (hNV hw)).symm
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (h.swap.elemAbelian.comm hv (hNB hw)).symm

theorem L_not_le_M (h : Hyp65 n M V₀ V g) : ¬ LOf V g ≤ M := by
  intro hle
  rw [LOf] at hle
  exact h.not_conjV_le_M (le_sup_right.trans hle)

theorem U_le_C (h : Hyp65 n M V₀ V g) : UOf M V g ≤ COf M V₀ V g := by
  rw [COf]
  refine le_inf ?_ ?_
  · rw [UOf, LOf]
    exact inf_le_left.trans le_sup_left
  · exact (le_of_eq (V_inf_centralizer_L0 h).symm).trans inf_le_right

theorem B_le_C (h : Hyp65 n M V₀ V g) : BOf M V g ≤ COf M V₀ V g := by
  have h' := U_le_C h.swap
  rwa [UOf_swap, COf_swap] at h'

theorem K_le_C (h : Hyp65 n M V₀ V g) : KOf M V g ≤ COf M V₀ V g := by
  rw [KOf]
  exact sup_le (U_le_C h) (B_le_C h)

theorem L_le_normalizer_C (h : Hyp65 n M V₀ V g) :
    LOf V g ≤ normalizer (COf M V₀ V g : Set G) := by
  refine s65_SixFiveD_le_normalizer_of_conj ?_
  intro l hl c hc
  have hlinvN : l⁻¹ ∈ normalizer (L0Of M V₀ g : Set G) :=
    (normalizer (L0Of M V₀ g : Set G)).inv_mem (L_le_normalizer_L0 h hl)
  have hcL : c ∈ LOf V g := by
    have h := hc; rw [COf, Subgroup.mem_inf] at h; exact h.1
  have hcC : c ∈ centralizer (L0Of M V₀ g : Set G) := by
    have h := hc; rw [COf, Subgroup.mem_inf] at h; exact h.2
  rw [COf, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · exact (LOf V g).mul_mem ((LOf V g).mul_mem hl hcL) ((LOf V g).inv_mem hl)
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : l⁻¹ * s * l ∈ L0Of M V₀ g := by
      simpa using (Subgroup.mem_normalizer_iff.1 hlinvN s).1 hs
    have hcomm : (l⁻¹ * s * l) * c = c * (l⁻¹ * s * l) :=
      Subgroup.mem_centralizer_iff.1 hcC (l⁻¹ * s * l) hs'
    have ht : l * (l⁻¹ * s * l) * l⁻¹ = s := by group
    calc s * (l * c * l⁻¹)
        = (l * (l⁻¹ * s * l) * l⁻¹) * (l * c * l⁻¹) := by rw [ht]
      _ = l * ((l⁻¹ * s * l) * c) * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * s * l)) * l⁻¹ := by rw [hcomm]
      _ = (l * c * l⁻¹) * (l * (l⁻¹ * s * l) * l⁻¹) := by group
      _ = (l * c * l⁻¹) * s := by rw [ht]

theorem C_le_M (h : Hyp65 n M V₀ V g) : COf M V₀ V g ≤ M := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Z0_ne_bot h)
  have hzV0 : (z : G) ∈ V₀ := z.2.1
  have hz1' : (z : G) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hzL0 : (z : G) ∈ L0Of M V₀ g := Subgroup.mem_sup_left z.2
  have hzcent : COf M V₀ V g ≤ centralizer ({(z : G)} : Set G) := by
    intro c hc
    have hcC : c ∈ centralizer (L0Of M V₀ g : Set G) := by
      have h := hc; rw [COf, Subgroup.mem_inf] at h; exact h.2
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact Subgroup.mem_centralizer_iff.1 hcC z hzL0
  exact hzcent.trans
    (centralizer_le_M_of_mem_V₀ h.isTI h.normalizer₀ hzV0 hz1')

theorem C_inf_V (h : Hyp65 n M V₀ V g) : COf M V₀ V g ⊓ V = UOf M V g := by
  have hVL : V ≤ LOf V g := by rw [LOf]; exact le_sup_left
  rw [COf, ← V_inf_centralizer_L0 h]
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨hxL, hxC⟩, hxV⟩
    exact ⟨hxV, hxC⟩
  · rintro ⟨hxV, hxC⟩
    exact ⟨⟨hVL hxV, hxC⟩, hxV⟩

theorem C_inf_conjV (h : Hyp65 n M V₀ V g) :
    COf M V₀ V g ⊓ conjSubgroup V g = BOf M V g := by
  have h' := C_inf_V h.swap
  rwa [COf_swap, UOf_swap] at h'

theorem commutator_C_V_le_U (h : Hyp65 n M V₀ V g) :
    ⁅COf M V₀ V g, V⁆ ≤ UOf M V g := by
  rw [Subgroup.commutator_le]
  intro c hc v hv
  have hcL : c ∈ LOf V g := by
    have h := hc; rw [COf, Subgroup.mem_inf] at h; exact h.1
  have hvL : v ∈ LOf V g := by
    have hVL : V ≤ LOf V g := by rw [LOf]; exact le_sup_left
    exact hVL hv
  have hcv : v * c⁻¹ * v⁻¹ ∈ COf M V₀ V g :=
    (Subgroup.mem_normalizer_iff.1 (L_le_normalizer_C h hvL) c⁻¹).1
      ((COf M V₀ V g).inv_mem hc)
  have hcM : c ∈ M := C_le_M h hc
  rw [← C_inf_V h, Subgroup.mem_inf]
  constructor
  · rw [commutatorElement_def, show c * v * c⁻¹ * v⁻¹ = c * (v * c⁻¹ * v⁻¹) by group]
    exact (COf M V₀ V g).mul_mem hc hcv
  · have hcvV : c * v * c⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (by rw [h.normalizer_eq]; exact hcM) v).1 hv
    rw [commutatorElement_def]
    exact V.mul_mem hcvV (V.inv_mem hv)

theorem commutator_C_conjV_le_B (h : Hyp65 n M V₀ V g) :
    ⁅COf M V₀ V g, conjSubgroup V g⁆ ≤ BOf M V g := by
  have h' := commutator_C_V_le_U h.swap
  rwa [COf_swap, UOf_swap] at h'

theorem commutator_B_V_le_U (h : Hyp65 n M V₀ V g) : ⁅BOf M V g, V⁆ ≤ UOf M V g :=
  (Subgroup.commutator_mono (B_le_C h) le_rfl).trans (commutator_C_V_le_U h)

theorem commutator_U_conjV_le_B (h : Hyp65 n M V₀ V g) :
    ⁅UOf M V g, conjSubgroup V g⁆ ≤ BOf M V g :=
  (Subgroup.commutator_mono (U_le_C h) le_rfl).trans (commutator_C_conjV_le_B h)

theorem K_coe_eq_mul (h : Hyp65 n M V₀ V g) :
    (KOf M V g : Set G) = (BOf M V g : Set G) * (UOf M V g : Set G) := by
  have hBU : BOf M V g ≤ normalizer (UOf M V g : Set G) := by
    refine s65_SixFiveD_le_normalizer_of_conj ?_
    intro b hb u hu
    have hcN : ⁅u, b⁆ ∈ NOf M V g :=
      commutator_U_B_le_N h (Subgroup.commutator_mem_commutator hu hb)
    have hcU : ⁅b, u⁆ ∈ UOf M V g := by
      have hcN' : ⁅b, u⁆ ∈ NOf M V g := by
        simpa [commutatorElement_inv] using (NOf M V g).inv_mem hcN
      rw [NOf] at hcN'
      exact hcN'.1
    have hbub : b * u * b⁻¹ = ⁅b, u⁆ * u := by
      rw [commutatorElement_def]; group
    rw [hbub]
    exact (UOf M V g).mul_mem hcU hu
  rw [KOf, sup_comm]
  exact Subgroup.coe_mul_of_left_le_normalizer_right (BOf M V g) (UOf M V g) hBU

theorem L_le_normalizer_K (h : Hyp65 n M V₀ V g) :
    LOf V g ≤ normalizer (KOf M V g : Set G) := by
  have hUK : UOf M V g ≤ KOf M V g := by rw [KOf]; exact le_sup_left
  have hBK : BOf M V g ≤ KOf M V g := by rw [KOf]; exact le_sup_right
  have hVK : V ≤ normalizer (KOf M V g : Set G) := by
    refine s65_SixFiveD_le_normalizer_of_conj ?_
    intro v hv x hx
    change x ∈ (KOf M V g : Set G) at hx
    rw [K_coe_eq_mul h, Set.mem_mul] at hx
    obtain ⟨b, hbB, u, huU, rfl⟩ := hx
    have huV : u ∈ V := (show UOf M V g ≤ V by rw [UOf]; exact inf_le_left) huU
    have hcvU : ⁅v, b⁆ ∈ UOf M V g := by
      simpa [commutatorElement_inv] using
        (UOf M V g).inv_mem (commutator_B_V_le_U h
          (Subgroup.commutator_mem_commutator hbB hv))
    have hvu : v * u * v⁻¹ = u := by
      rw [h.elemAbelian.comm hv huV]; group
    have hvb : v * b * v⁻¹ = ⁅v, b⁆ * b := by rw [commutatorElement_def]; group
    rw [show v * (b * u) * v⁻¹ = (v * b * v⁻¹) * (v * u * v⁻¹) by group, hvb, hvu]
    exact (KOf M V g).mul_mem ((KOf M V g).mul_mem (hUK hcvU) (hBK hbB)) (hUK huU)
  have hVgK : conjSubgroup V g ≤ normalizer (KOf M V g : Set G) := by
    refine s65_SixFiveD_le_normalizer_of_conj ?_
    intro v hv x hx
    change x ∈ (KOf M V g : Set G) at hx
    rw [K_coe_eq_mul h, Set.mem_mul] at hx
    obtain ⟨b, hbB, u, huU, rfl⟩ := hx
    have hvb : v * b * v⁻¹ = b := by
      rw [h.swap.elemAbelian.comm hv hbB.1]; group
    have hcuB : ⁅v, u⁆ ∈ BOf M V g := by
      simpa [commutatorElement_inv] using
        (BOf M V g).inv_mem (commutator_U_conjV_le_B h
          (Subgroup.commutator_mem_commutator huU hv))
    have hvu : v * u * v⁻¹ = ⁅v, u⁆ * u := by rw [commutatorElement_def]; group
    rw [show v * (b * u) * v⁻¹ = (v * b * v⁻¹) * (v * u * v⁻¹) by group, hvb, hvu]
    exact (KOf M V g).mul_mem (hBK hbB) ((KOf M V g).mul_mem (hBK hcuB) (hUK huU))
  rw [LOf]
  exact sup_le hVK hVgK

theorem K_normal (h : Hyp65 n M V₀ V g) :
    ((KOf M V g).subgroupOf (LOf V g)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (KOf_le_LOf M V g)).2 (L_le_normalizer_K h)

theorem V_inf_K (h : Hyp65 n M V₀ V g) : V ⊓ KOf M V g = UOf M V g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxK⟩ := hx
    change x ∈ (KOf M V g : Set G) at hxK
    rw [K_coe_eq_mul h, Set.mem_mul] at hxK
    obtain ⟨b, hbB, u, huU, rfl⟩ := hxK
    have huV : u ∈ V := (show UOf M V g ≤ V by rw [UOf]; exact inf_le_left) huU
    have hbV : b ∈ V := by
      have h1 : (b * u) * u⁻¹ ∈ V := V.mul_mem hxV (V.inv_mem huV)
      have h2 : (b * u) * u⁻¹ = b := by group
      rwa [h2] at h1
    have hbU : b ∈ UOf M V g := by
      rw [UOf, Subgroup.mem_inf]
      exact ⟨hbV, h.conjV_le_conjM hbB.1⟩
    exact (UOf M V g).mul_mem hbU huU
  · intro x hx
    exact ⟨(show UOf M V g ≤ V by rw [UOf]; exact inf_le_left) hx,
      (show UOf M V g ≤ KOf M V g by rw [KOf]; exact le_sup_left) hx⟩

theorem conjV_inf_K (h : Hyp65 n M V₀ V g) :
    conjSubgroup V g ⊓ KOf M V g = BOf M V g := by
  have h' := V_inf_K h.swap
  rwa [KOf_swap, UOf_swap] at h'

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
