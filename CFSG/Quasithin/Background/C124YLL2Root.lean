module

public import CFSG.Quasithin.Background.C124YLPack
public import CFSG.Quasithin.Background.C124L2MP
public import CFSG.Quasithin.Background.C124YLL2Ctx
public import CFSG.Quasithin.Background.C124YLS2Alg

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped MatrixGroups

namespace S2

variable (F : Type*) [Field F]

theorem uSL_zero : uSL (0 : F) = 1 := by
  apply Subtype.ext
  simp [uSL, Matrix.one_fin_two]

@[expose] def rootHom : Multiplicative F →* SL(2, F) where
  toFun b := uSL (Multiplicative.toAdd b)
  map_one' := by simpa using uSL_zero F
  map_mul' a b := by simpa using (uSL_mul (Multiplicative.toAdd a) (Multiplicative.toAdd b)).symm

theorem rootHom_injective : Function.Injective (rootHom F) := by
  intro a b h
  exact Multiplicative.toAdd.injective (uSL_injective h)

end S2

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

@[expose] def Kroot : Subgroup (MulAut W) :=
  (((S2.rootHom F).range).map C.θ).map Ls.subtype

theorem mem_Kroot {g : MulAut W} :
    g ∈ C.Kroot ↔ ∃ b : F, g = ((C.θ (S2.uSL b) : ↥Ls) : MulAut W) := by
  unfold Kroot
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨l, ⟨s, ⟨b, rfl⟩, rfl⟩, rfl⟩
    exact ⟨Multiplicative.toAdd b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨C.θ (S2.uSL b), ⟨S2.uSL b, ⟨Multiplicative.ofAdd b, rfl⟩, rfl⟩, rfl⟩

theorem Kroot_le : C.Kroot ≤ Ls := by
  intro g hg
  obtain ⟨b, rfl⟩ := C.mem_Kroot.1 hg
  exact (C.θ _).2

theorem card_Kroot : Nat.card C.Kroot = 4 := by
  unfold Kroot
  rw [Subgroup.card_map_of_injective Ls.subtype_injective,
    Subgroup.card_map_of_injective C.θ_inj]
  rw [Nat.card_congr (MonoidHom.ofInjective (S2.rootHom_injective F)).toEquiv.symm]
  rw [Nat.card_congr Multiplicative.toAdd]
  exact C.hF4

theorem Kroot_pow_two {g : MulAut W} (hg : g ∈ C.Kroot) : g ^ 2 = 1 := by
  obtain ⟨b, rfl⟩ := C.mem_Kroot.1 hg
  obtain ⟨ω, -, -, -, h2, -⟩ := S2.F4_data C.hF4
  have : S2.uSL b * S2.uSL b = 1 := by
    rw [S2.uSL_mul, show b + b = 0 by linear_combination b * h2, S2.uSL_zero]
  have h3 := congrArg (fun s => ((C.θ s : ↥Ls) : MulAut W)) this
  simp only [map_mul, map_one] at h3
  simpa [pow_two] using h3

theorem Kroot_elem : IsElemAbelian2 C.Kroot := by
  refine ⟨fun a ha b hb => ?_, fun a ha => C.Kroot_pow_two ha⟩
  obtain ⟨x, rfl⟩ := C.mem_Kroot.1 ha
  obtain ⟨y, rfl⟩ := C.mem_Kroot.1 hb
  have : S2.uSL x * S2.uSL y = S2.uSL y * S2.uSL x := by
    rw [S2.uSL_mul, S2.uSL_mul, add_comm]
  have h3 := congrArg (fun s => ((C.θ s : ↥Ls) : MulAut W)) this
  simpa only [map_mul, Subgroup.coe_mul] using h3

include C in
theorem card_Ls : Nat.card Ls = 60 := by
  rw [← L2.card_sl2_four C.hF4]
  exact Nat.card_congr (MulEquiv.ofBijective C.θ ⟨C.θ_inj, C.θ_surj⟩).toEquiv.symm

theorem Kroot_sylow : IsSylowTwoOf C.Kroot Ls := by
  refine ⟨C.Kroot_le, isPGroup_of_isElemAbelian2 C.Kroot_elem, ?_⟩
  show ¬ 2 ∣ C.Kroot.relIndex Ls
  have h := Subgroup.relIndex_mul_card C.Kroot Ls
  rw [inf_eq_left.2 C.Kroot_le, C.card_Kroot, C.card_Ls] at h
  have : C.Kroot.relIndex Ls = 15 := by omega
  rw [this]
  omega

end L2Ctx

end CFSG.Quasithin.C124.YL
