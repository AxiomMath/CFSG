module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5MultG

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.shapeTensor_cent_card (hw2 : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    {M : Subgroup W} (hKM : StableUnder K M) (hfaith : ∀ k ∈ K, (∀ m ∈ M, k m = m) → k = 1)
    (hsurjM : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W))
    (hrk : rk ↥M = n) (hn : 2 ≤ n) (x : MulAut W) (hdis : M ⊓ M.map x.toMonoidHom = ⊥)
    (hsup : M ⊔ M.map x.toMonoidHom = ⊤) (xcomm : ∀ k ∈ K, k * x = x * k) :
    Nat.card ↥(Subgroup.centralizer (K : Set (MulAut W))) ≤ 6 := by
  classical
  let C : Subgroup (MulAut W) := Subgroup.centralizer (K : Set (MulAut W))
  change Nat.card ↥C ≤ 6
  have hxmem : x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact xcomm k hk
  have h1mem : (1 : MulAut W) ∈ C := Subgroup.one_mem C
  have hcardM : Nat.card ↥M = 2 ^ n := by rw [card_eq_two_pow hw2 M, hrk]
  have hcardxM : Nat.card ↥(M.map x.toMonoidHom) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective x.injective, hcardM]
  have hrkxM : rk ↥(M.map x.toMonoidHom) = n := by
    have h := card_eq_two_pow hw2 (M.map x.toMonoidHom)
    rw [hcardxM] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h.symm
  have hrkW : rk W = 2 * n := by
    have h := rk_sup_add_rk_inf (V := W) M (M.map x.toMonoidHom)
    rw [hsup, rk_top, hdis, rk_bot, hrk, hrkxM] at h
    omega
  have hcardW : Nat.card W = 2 ^ (2 * n) := by
    rw [card_eq_two_pow_rk hw2, hrkW]
  have h1eq : M.map (1 : MulAut W).toMonoidHom = M := by
    have h1 : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by
      ext w
      rfl
    rw [h1, Subgroup.map_id]
  have hMle : M ≤ ⨆ c ∈ C, M.map c.toMonoidHom := by
    have h := le_iSup₂ (f := fun c (_ : c ∈ C) => M.map c.toMonoidHom) (1 : MulAut W) h1mem
    rwa [h1eq] at h
  have hxle : M.map x.toMonoidHom ≤ ⨆ c ∈ C, M.map c.toMonoidHom :=
    le_iSup₂ (f := fun c (_ : c ∈ C) => M.map c.toMonoidHom) x hxmem
  have hspan : ⨆ c ∈ C, M.map c.toMonoidHom = ⊤ := by
    apply le_antisymm le_top
    rw [← hsup]
    exact sup_le hMle hxle
  have honto : ∀ τ : MulAut ↥M, ∃ l ∈ K, ∀ y : ↥M, l (y : W) = (τ y : W) := by
    intro τ
    obtain ⟨k, hk, hkτ⟩ := hsurjM τ
    exact ⟨k, hk, fun m => (hkτ m).symm⟩
  obtain ⟨m, θ, _hθK, hθfaith, _hfix, hWcard⟩ :=
    CFSG.Quasithin.H13.Mult.exists_rep' (W := W) hw2 (Ls := K) (Yg := M) hKM honto hn hcardM
      hspan
  have hm2 : m = 2 := by
    have h : (2 ^ m) ^ n = (2 ^ 2) ^ n := by
      rw [hWcard] at hcardW
      rw [Nat.pow_mul] at hcardW
      exact hcardW
    have h2 : (2 : ℕ) ^ (m * n) = 2 ^ (2 * n) := by
      rw [Nat.pow_mul, Nat.pow_mul]
      exact h
    have hmn : m * n = 2 * n := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    exact Nat.mul_right_cancel (by omega : 0 < n) hmn
  let incl : ↥C →* ↥(C ⊔ K) :=
    { toFun := fun a => ⟨(a : MulAut W), Subgroup.mem_sup_left a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : ↥C →* MulAut (Multiplicative (Fin m → ZMod 2)) := θ.comp incl
  have hφapply : ∀ a : ↥C, φ a = θ ⟨(a : MulAut W), Subgroup.mem_sup_left a.2⟩ := fun _ => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hmem : (a : MulAut W) * (b : MulAut W)⁻¹ ∈ C := C.mul_mem a.2 (C.inv_mem b.2)
    have h1 : φ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : θ ⟨(a : MulAut W) * (b : MulAut W)⁻¹, Subgroup.mem_sup_left hmem⟩ = 1 := by
      show φ (a * b⁻¹) = 1
      exact h1
    have h3 := hθfaith ((a : MulAut W) * (b : MulAut W)⁻¹) hmem h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hcardC : Nat.card ↥C ≤ Nat.card (MulAut (Multiplicative (Fin m → ZMod 2))) :=
    Nat.card_le_card_of_injective φ hφinj
  have hcardAut : Nat.card (MulAut (Multiplicative (Fin m → ZMod 2))) = 6 := by
    rw [hm2]
    rw [Nat.card_congr (CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 2).toEquiv]
    rw [Matrix.card_GL_field (𝔽 := ZMod 2) (n := 2)]
    decide
  calc Nat.card ↥C ≤ Nat.card (MulAut (Multiplicative (Fin m → ZMod 2))) := hcardC
    _ = 6 := hcardAut

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
