module

public import CFSG.Quasithin.H13.A6S13824c
public import CFSG.Quasithin.Background.SmithB45Alt7Sym
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Rep
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Emb
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.A6

namespace A7F

open Equiv Equiv.Perm CFSG.Quasithin

@[expose] def ext4 (τ : Perm (Fin 4)) (x : Fin 7) : Fin 7 :=
  if h : x.val < 4 then ⟨(τ ⟨x.val, h⟩).val, by omega⟩ else x

theorem ext4_mul (τ τ' : Perm (Fin 4)) (x : Fin 7) : ext4 (τ * τ') x = ext4 τ (ext4 τ' x) := by
  unfold ext4
  by_cases h : x.val < 4
  · have h' : (τ' ⟨x.val, h⟩).val < 4 := (τ' ⟨x.val, h⟩).2
    simp only [h, ↓reduceDIte, Perm.mul_apply, h']
  · simp only [h, ↓reduceDIte]

theorem ext4_one (x : Fin 7) : ext4 1 x = x := by
  unfold ext4
  split_ifs <;> rfl

@[expose] def ι4 : Perm (Fin 4) →* Perm (Fin 7) where
  toFun τ :=
    { toFun := ext4 τ
      invFun := ext4 τ⁻¹
      left_inv := fun x => by rw [← ext4_mul, inv_mul_cancel, ext4_one]
      right_inv := fun x => by rw [← ext4_mul, mul_inv_cancel, ext4_one] }
  map_one' := Equiv.ext ext4_one
  map_mul' τ τ' := Equiv.ext (ext4_mul τ τ')

theorem ι4_apply (τ : Perm (Fin 4)) (x : Fin 7) : ι4 τ x = ext4 τ x := rfl

theorem ι4_injective : Function.Injective ι4 := by
  intro τ τ' h
  ext i
  have h1 := congrArg (fun σ : Perm (Fin 7) => (σ ⟨i.val, by omega⟩ : Fin 7).val) h
  simp only [ι4_apply, ext4, i.2, ↓reduceDIte] at h1
  exact h1

theorem exists_ι4 {σ : Perm (Fin 7)} (h4 : σ 4 = 4) (h5 : σ 5 = 5) (h6 : σ 6 = 6) :
    ∃ τ : Perm (Fin 4), ι4 τ = σ := by
  have hlt : ∀ x : Fin 7, x.val < 4 → (σ x).val < 4 := by
    intro x hx
    by_contra h
    push Not at h
    have hσx : σ x = 4 ∨ σ x = 5 ∨ σ x = 6 := by omega
    rcases hσx with e | e | e
    · have := σ.injective (e.trans h4.symm); subst this; simp at hx
    · have := σ.injective (e.trans h5.symm); subst this; simp at hx
    · have := σ.injective (e.trans h6.symm); subst this; simp at hx
  have hlt' : ∀ x : Fin 7, x.val < 4 → (σ⁻¹ x).val < 4 := by
    intro x hx
    by_contra h
    push Not at h
    have hσx : σ⁻¹ x = 4 ∨ σ⁻¹ x = 5 ∨ σ⁻¹ x = 6 := by omega
    have e4 : σ⁻¹ 4 = 4 := by rw [Perm.inv_eq_iff_eq, h4]
    have e5 : σ⁻¹ 5 = 5 := by rw [Perm.inv_eq_iff_eq, h5]
    have e6 : σ⁻¹ 6 = 6 := by rw [Perm.inv_eq_iff_eq, h6]
    rcases hσx with e | e | e
    · have := σ⁻¹.injective (e.trans e4.symm); subst this; simp at hx
    · have := σ⁻¹.injective (e.trans e5.symm); subst this; simp at hx
    · have := σ⁻¹.injective (e.trans e6.symm); subst this; simp at hx
  let τ : Perm (Fin 4) :=
    { toFun := fun i => ⟨(σ ⟨i.val, by omega⟩).val, hlt _ (by simp)⟩
      invFun := fun i => ⟨(σ⁻¹ ⟨i.val, by omega⟩).val, hlt' _ (by simp)⟩
      left_inv := fun i => by
        apply Fin.ext
        simp
      right_inv := fun i => by
        apply Fin.ext
        simp }
  refine ⟨τ, Equiv.ext fun x => ?_⟩
  rw [ι4_apply]
  unfold ext4
  split_ifs with h
  · rfl
  · have hx : x = 4 ∨ x = 5 ∨ x = 6 := by omega
    rcases hx with rfl | rfl | rfl
    · exact h4.symm
    · exact h5.symm
    · exact h6.symm

theorem two_elem_four : ∀ σ y : Perm (Fin 4), y ^ 3 = 1 → y ≠ 1 → σ ^ 4 = 1 →
    σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 0 3 * swap 1 2 ∨
    (∃ w ∈ [σ * (y * σ * y⁻¹), σ * (y⁻¹ * σ * y), σ * σ * (y * σ * y⁻¹),
      (y * σ * y⁻¹) * (y⁻¹ * σ * y)], w ^ 3 = 1 ∧ w ≠ 1) := by
  decide +kernel

theorem ι4_K4 : ι4 (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 ∧
    ι4 (swap 0 2 * swap 1 3) = swap 0 2 * swap 1 3 ∧
    ι4 (swap 0 3 * swap 1 2) = swap 0 3 * swap 1 2 := by
  refine ⟨Equiv.ext fun x => ?_, Equiv.ext fun x => ?_, Equiv.ext fun x => ?_⟩ <;>
    rw [ι4_apply] <;> revert x <;> decide

theorem two_elem_fix456 {σ y : Perm (Fin 7)} (hσ4 : σ 4 = 4) (hσ5 : σ 5 = 5) (hσ6 : σ 6 = 6)
    (hy4 : y 4 = 4) (hy5 : y 5 = 5) (hy6 : y 6 = 6) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hσ2 : σ ^ 4 = 1) :
    σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 0 3 * swap 1 2 ∨
    (∃ w ∈ [σ * (y * σ * y⁻¹), σ * (y⁻¹ * σ * y), σ * σ * (y * σ * y⁻¹),
      (y * σ * y⁻¹) * (y⁻¹ * σ * y)], w ^ 3 = 1 ∧ w ≠ 1) := by
  obtain ⟨τ, rfl⟩ := exists_ι4 hσ4 hσ5 hσ6
  obtain ⟨υ, rfl⟩ := exists_ι4 hy4 hy5 hy6
  have hυ3 : υ ^ 3 = 1 := ι4_injective (by rw [map_pow, hy3, map_one])
  have hυ1 : υ ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hτ2 : τ ^ 4 = 1 := ι4_injective (by rw [map_pow, hσ2, map_one])
  obtain ⟨hK1, hK2, hK3⟩ := ι4_K4
  rcases two_elem_four τ υ hυ3 hυ1 hτ2 with h | h | h | h | ⟨w, hw, hw3, hw1⟩
  · left; rw [h, map_one]
  · right; left; rw [h, hK1]
  · right; right; left; rw [h, hK2]
  · right; right; right; left; rw [h, hK3]
  · right; right; right; right
    refine ⟨ι4 w, ?_, by rw [← map_pow, hw3, map_one],
      fun h => hw1 (ι4_injective (by rw [h, map_one]))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with rfl | rfl | rfl | rfl <;> simp [map_mul, map_inv]

theorem pv_eq_pv : ∀ a b c d : Fin 7, a ≠ b → B45Alt7.pv a b = B45Alt7.pv c d →
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  unfold B45Alt7.pv
  decide +kernel

theorem permAct_pv' (σ : Perm (Fin 7)) (a b : Fin 7) :
    G6.permAct 7 σ (Multiplicative.ofAdd (B45Alt7.pv a b)) =
      Multiplicative.ofAdd (B45Alt7.pv (σ a) (σ b)) := B45Alt7.permAct_pv σ a b

theorem fix456_of_fix {σ : Perm (Fin 7)}
    (h45 : G6.permAct 7 σ (Multiplicative.ofAdd (B45Alt7.pv 4 5)) =
      Multiplicative.ofAdd (B45Alt7.pv 4 5))
    (h46 : G6.permAct 7 σ (Multiplicative.ofAdd (B45Alt7.pv 4 6)) =
      Multiplicative.ofAdd (B45Alt7.pv 4 6)) : σ 4 = 4 ∧ σ 5 = 5 ∧ σ 6 = 6 := by
  rw [permAct_pv'] at h45 h46
  have e45 := pv_eq_pv 4 5 (σ 4) (σ 5) (by decide) (Multiplicative.ofAdd.injective h45).symm
  have e46 := pv_eq_pv 4 6 (σ 4) (σ 6) (by decide) (Multiplicative.ofAdd.injective h46).symm
  rcases e45 with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> rcases e46 with ⟨h4', h6⟩ | ⟨h4', h6⟩
  · exact ⟨h4, h5, h6⟩
  · exact absurd (h4.symm.trans h4') (by decide)
  · exact absurd (h4.symm.trans h4') (by decide)
  · exact absurd (h4.symm.trans h4') (by decide)

abbrev InK4 (σ : Perm (Fin 7)) : Prop :=
  σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 0 3 * swap 1 2

abbrev pvm (a b : Fin 7) : G6.PermMod 7 := Multiplicative.ofAdd (B45Alt7.pv a b)

theorem not_transv_K4 {σ : Perm (Fin 7)} (hσ : InK4 σ) : ∃ j : Fin 7,
    G6.permAct 7 σ (pvm 0 4) * (pvm 0 4)⁻¹ ≠ 1 ∧ G6.permAct 7 σ (pvm j 4) * (pvm j 4)⁻¹ ≠ 1 ∧
      G6.permAct 7 σ (pvm 0 4) * (pvm 0 4)⁻¹ ≠ G6.permAct 7 σ (pvm j 4) * (pvm j 4)⁻¹ := by
  rcases hσ with rfl | rfl | rfl
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨1, by decide +kernel⟩
  · exact ⟨1, by decide +kernel⟩

theorem not_quad_K4 {σ τ : Perm (Fin 7)} (hσ : InK4 σ) (hτ : InK4 τ) (hne : σ ≠ τ) :
    G6.permAct 7 τ (G6.permAct 7 σ (pvm 0 4) * (pvm 0 4)⁻¹) *
      (G6.permAct 7 σ (pvm 0 4) * (pvm 0 4)⁻¹)⁻¹ ≠ 1 := by
  rcases hσ with rfl | rfl | rfl <;> rcases hτ with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | decide +kernel

theorem pow_twelve_four : ∀ τ : Perm (Fin 4), τ ^ 12 = 1 := by decide +kernel

theorem pow_four_of_fix {σ : Perm (Fin 7)} (h4 : σ 4 = 4) (h5 : σ 5 = 5) (h6 : σ 6 = 6)
    {k : ℕ} (hk : σ ^ 2 ^ k = 1) : σ ^ 4 = 1 := by
  obtain ⟨τ, rfl⟩ := exists_ι4 h4 h5 h6
  have h12 : (ι4 τ) ^ 12 = 1 := by rw [← map_pow, pow_twelve_four, map_one]
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hd := orderOf_dvd_of_pow_eq_one h12
  rw [hjo] at hd
  have hj3 : j ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hjo]
  interval_cases j <;> simp_all

theorem eq_one_of_pow_three {M : Type*} [Monoid M] {w : M} (h3 : w ^ 3 = 1) {k : ℕ}
    (hk : w ^ 2 ^ k = 1) : w = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one h3
  have h2 := orderOf_dvd_of_pow_eq_one hk
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_right k (by norm_num))) h2)

end A7F

end CFSG.Quasithin.H13.A6
