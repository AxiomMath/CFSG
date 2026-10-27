module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompA

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Comp12626L2Odd : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v → ∀ p f : ℕ, p.Prime → p ≠ 2 → (f = 1 ∨ f = 2) →
      StatedClassicalModel ↥K .PSL 2 p f → p = 11 ∧ f = 1

@[expose] def Comp12626L3U3Odd : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ (StatedClassicalModel ↥K .PSL 3 p 1 ∨ StatedClassicalModel ↥K .PSU 3 p 1)

@[expose] def Comp12626CovOdd : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v →
      ¬ ((∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsSLEps3 s p ↥K) ∨ IsSLEps3 false 2 ↥K ∨
        IsHat ↥K (alternatingGroup (Fin 6)))

section Inner

variable {M : Type} [Group M]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : a * g * a⁻¹ = b * g * b⁻¹ := DFunLike.congr_fun hab g
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc)

@[expose] def innerPart (Lb : Subgroup (MulAut M)) : Subgroup M :=
  Lb.comap (MulAut.conj : M →* MulAut M)

theorem mem_innerPart {Lb : Subgroup (MulAut M)} {c : M} :
    c ∈ innerPart Lb ↔ MulAut.conj c ∈ Lb :=
  Iff.rfl

variable {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)}

theorem AutConf.exists_orderOf_three (h : AutConf M ν Lb Pb) : ∃ l ∈ Lb, orderOf l = 3 := by
  by_contra hcon
  push Not at hcon
  apply h.ne_bot
  rw [← h.gen, eq_bot_iff, oTwoUpper, Subgroup.closure_le]
  rintro l ⟨hl, hodd⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one (h.three l hl hodd)) with
    h1 | h1
  · exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp h1)
  · exact absurd h1 (hcon l hl)

theorem AutConf.fix_of_mem_innerPart (h : AutConf M ν Lb Pb) (hZ : Subgroup.center M = ⊥)
    {c : M} (hc : c ∈ innerPart Lb) : ν c = c := by
  have hcomm := h.comm _ hc
  have hconj : MulAut.conj (ν c) = MulAut.conj c := by
    refine MulEquiv.ext fun x => ?_
    have h1 := DFunLike.congr_fun hcomm (ν.symm x)
    change c * ν (ν.symm x) * c⁻¹ = ν (c * ν.symm x * c⁻¹) at h1
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  exact conj_injective_of_center_eq_bot hZ hconj

theorem AutConf.conj_mem_innerPart (h : AutConf M ν Lb Pb) {d : M} (hd : ν d = d) {c : M}
    (hc : c ∈ innerPart Lb) : d * c * d⁻¹ ∈ innerPart Lb := by
  rw [mem_innerPart, map_mul, map_mul, map_inv]
  exact h.norm d hd _ hc

theorem AutConf.pow_three_of_mem_innerPart (h : AutConf M ν Lb Pb) (hZ : Subgroup.center M = ⊥)
    {c : M} (hc : c ∈ innerPart Lb) (hodd : Odd (orderOf c)) : c ^ 3 = 1 := by
  have hinj := conj_injective_of_center_eq_bot hZ
  have h3 := h.three _ hc (by rwa [orderOf_injective _ hinj])
  rw [← map_pow] at h3
  exact hinj (h3.trans (map_one _).symm)

theorem AutConf.exists_innerPart_three (h : AutConf M ν Lb Pb) (hZ : Subgroup.center M = ⊥)
    (hinn : ∀ α : MulAut M, α ^ 3 = 1 → α ∈ (MulAut.conj : M →* MulAut M).range) :
    ∃ c ∈ innerPart Lb, orderOf c = 3 := by
  obtain ⟨l, hl, hl3⟩ := h.exists_orderOf_three
  obtain ⟨c, rfl⟩ := hinn l (by rw [← hl3]; exact pow_orderOf_eq_one l)
  refine ⟨c, hl, ?_⟩
  rwa [orderOf_injective _ (conj_injective_of_center_eq_bot hZ)] at hl3

end Inner

end CFSG.Quasithin.H13.S126C
