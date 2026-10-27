module

public import CFSG.Quasithin.H13.VolII16Central

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c11_v1_fpf_closure_le {W W' : Type} [CommGroup W] [CommGroup W']
    {A : Subgroup (MulAut W)} {B : Subgroup (MulAut W')} (e : ↥B →* ↥A)
    (he : Function.Surjective e) {t₁ t₂ : MulAut W'} (h₁ : t₁ ∈ B) (h₂ : t₂ ∈ B)
    (hgen : B ≤ Subgroup.closure
      {h : MulAut W' | h ∈ B ∧ (h * t₁ = t₁ * h ∨ h * t₂ = t₂ * h)}) :
    A ≤ Subgroup.closure {h : MulAut W | h ∈ A ∧
      (h * (e ⟨t₁, h₁⟩ : MulAut W) = (e ⟨t₁, h₁⟩ : MulAut W) * h ∨
        h * (e ⟨t₂, h₂⟩ : MulAut W) = (e ⟨t₂, h₂⟩ : MulAut W) * h)} := by
  let b₁ : ↥B := ⟨t₁, h₁⟩
  let b₂ : ↥B := ⟨t₂, h₂⟩
  let SB : Set (MulAut W') := {h | h ∈ B ∧ (h * t₁ = t₁ * h ∨ h * t₂ = t₂ * h)}
  let SA : Set (MulAut W) := {h | h ∈ A ∧
    (h * (e b₁ : MulAut W) = (e b₁ : MulAut W) * h ∨
      h * (e b₂ : MulAut W) = (e b₂ : MulAut W) * h)}
  change A ≤ Subgroup.closure SA
  have hSBle : Subgroup.closure SB ≤ B :=
    (Subgroup.closure_le B).2 (fun h hh => hh.1)
  have key : ∀ (x : MulAut W') (hx : x ∈ Subgroup.closure SB),
      (e ⟨x, hSBle hx⟩ : MulAut W) ∈ Subgroup.closure SA := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
        have hzB : z ∈ B := hz.1
        have hmem : (e ⟨z, hzB⟩ : MulAut W) ∈ SA := by
          refine ⟨(e ⟨z, hzB⟩).2, ?_⟩
          rcases hz.2 with hc | hc
          · left
            have hmul : (⟨z, hzB⟩ : ↥B) * b₁ = b₁ * ⟨z, hzB⟩ := by
              apply Subtype.ext
              simpa [b₁] using hc
            rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul e ⟨z, hzB⟩ b₁,
              ← map_mul e b₁ ⟨z, hzB⟩, hmul]
          · right
            have hmul : (⟨z, hzB⟩ : ↥B) * b₂ = b₂ * ⟨z, hzB⟩ := by
              apply Subtype.ext
              simpa [b₂] using hc
            rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul e ⟨z, hzB⟩ b₂,
              ← map_mul e b₂ ⟨z, hzB⟩, hmul]
        have hEq : (⟨z, hSBle (Subgroup.subset_closure hz)⟩ : ↥B) = ⟨z, hzB⟩ :=
          Subtype.ext rfl
        rw [hEq]
        exact Subgroup.subset_closure hmem
    | one =>
        have hEq : (⟨(1 : MulAut W'), hSBle (one_mem (Subgroup.closure SB))⟩ : ↥B) = 1 :=
          Subtype.ext rfl
        rw [hEq, map_one]
        exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
        have hEq : (⟨x, hSBle hx⟩ : ↥B) * ⟨y, hSBle hy⟩
            = ⟨x * y, hSBle (mul_mem hx hy)⟩ := Subtype.ext rfl
        rw [← hEq, map_mul]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        have hEq : (⟨x, hSBle hx⟩ : ↥B)⁻¹
            = ⟨x⁻¹, hSBle (inv_mem hx)⟩ := Subtype.ext rfl
        rw [← hEq, map_inv]
        exact Subgroup.inv_mem _ ih
  intro a ha
  obtain ⟨b, hb⟩ := he ⟨a, ha⟩
  have hbkey := key (b : MulAut W') (hgen b.2)
  have hEq : (⟨(b : MulAut W'), hSBle (hgen b.2)⟩ : ↥B) = b := Subtype.ext rfl
  rw [hEq, hb] at hbkey
  simpa using hbkey

theorem s16c11_v1_kernel_eq_bot_of_fpf {W W' : Type} [CommGroup W] [Finite W] [CommGroup W']
    (hW2 : ∀ w : W, w ^ 2 = 1) {κ : W →* W'}
    {A : Subgroup (MulAut W)} {B : Subgroup (MulAut W')} (e : ↥B →* ↥A)
    (he : Function.Surjective e)
    (hequiv : ∀ (b : ↥B) (w : W), κ ((e b : MulAut W) w) = (b : MulAut W') (κ w))
    (hker : ∀ w, κ w = 1 → w ∈ fixV A) (hcomm : commV A = ⊤)
    {t₁ t₂ : MulAut W'} (h₁ : t₁ ∈ B) (h₂ : t₂ ∈ B) (h₁₂ : t₁ * t₂ = t₂ * t₁)
    {k₁ k₂ : ℕ} (hk₁ : Odd k₁) (hk₂ : Odd k₂) (ht₁ : t₁ ^ k₁ = 1) (ht₂ : t₂ ^ k₂ = 1)
    (hfpf₁ : ∀ w', t₁ w' = w' → w' = 1) (hfpf₂ : ∀ w', t₂ w' = w' → w' = 1)
    (hgen : B ≤ Subgroup.closure
      {h : MulAut W' | h ∈ B ∧ (h * t₁ = t₁ * h ∨ h * t₂ = t₂ * h)}) :
    κ.ker = ⊥ := by
  let b₁ : ↥B := ⟨t₁, h₁⟩
  let b₂ : ↥B := ⟨t₂, h₂⟩
  have hb₁₂ : b₁ * b₂ = b₂ * b₁ := by
    apply Subtype.ext
    simpa using h₁₂
  have hb₁k : b₁ ^ k₁ = 1 := by
    apply Subtype.ext
    simpa using ht₁
  have hb₂k : b₂ ^ k₂ = 1 := by
    apply Subtype.ext
    simpa using ht₂
  have ha₁₂ : (e b₁ : MulAut W) * (e b₂ : MulAut W)
      = (e b₂ : MulAut W) * (e b₁ : MulAut W) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul e b₁ b₂, ← map_mul e b₂ b₁, hb₁₂]
  have ha₁k : (e b₁ : MulAut W) ^ k₁ = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow e b₁ k₁, hb₁k, map_one]
    rfl
  have ha₂k : (e b₂ : MulAut W) ^ k₂ = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow e b₂ k₂, hb₂k, map_one]
    rfl
  have hfpf₁' : ∀ w : W, (e b₁ : MulAut W) w = w → w ∈ κ.ker := by
    intro w hw
    have h : (b₁ : MulAut W') (κ w) = κ w := by
      have h1 := hequiv b₁ w
      rw [hw] at h1
      exact h1.symm
    exact (MonoidHom.mem_ker (f := κ)).mpr (hfpf₁ (κ w) h)
  have hfpf₂' : ∀ w : W, (e b₂ : MulAut W) w = w → w ∈ κ.ker := by
    intro w hw
    have h : (b₂ : MulAut W') (κ w) = κ w := by
      have h1 := hequiv b₂ w
      rw [hw] at h1
      exact h1.symm
    exact (MonoidHom.mem_ker (f := κ)).mpr (hfpf₂ (κ w) h)
  have hgen' := (s16c11_v1_fpf_closure_le e he h₁ h₂ hgen).trans
    (Subgroup.closure_mono fun h hh => hh.2)
  exact CFSG.Quasithin.H13.VolI.eq_bot_of_two_fpf hW2 (Z := κ.ker)
    (fun w hw => hker w hw) hcomm (e b₁).2 (e b₂).2 ha₁₂ hk₁ hk₂ ha₁k ha₂k
    hfpf₁' hfpf₂' hgen'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
