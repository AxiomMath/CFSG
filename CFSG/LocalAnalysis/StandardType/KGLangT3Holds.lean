module

public import CFSG.LocalAnalysis.StandardType.KGLangT3Defs
public import CFSG.LocalAnalysis.StandardType.KGLangT3Glue
public import CFSG.LocalAnalysis.StandardType.KGLangT3Lift
public import CFSG.LocalAnalysis.StandardType.KGLangT3Data
public import CFSG.LocalAnalysis.StandardType.KGLangT3Transport
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem kgLangT3_pow_three {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {A : Subgroup (MulAut (GGTriD4R n K))}
    (hA : IsElemAbelian 3 A) {h : GGTriD4R n K} (hhA : MulAut.conj h ∈ A) : h ^ 3 = 1 := by
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn K hK
  have h3 : (MulAut.conj h) ^ 3 = 1 := hA.2 _ hhA
  have hc : MulAut.conj (h ^ 3) = 1 := by rw [map_pow]; exact h3
  have hmem : h ^ 3 ∈ Subgroup.center (GGTriD4R n K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut (GGTriD4R n K) => f x) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * h ^ 3 = (h ^ 3 * x * (h ^ 3)⁻¹) * h ^ 3 := by rw [this]
      _ = h ^ 3 * x := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem kgLangT3Strong_holds {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) : KGLangT3Strong n K := by
  intro A hA α₀ hα₀A hα₀o h h1 hhA J₀ hJ E _ _ θ₀ hAt
  obtain ⟨k, _, _, hk⟩ := triD4Line_exists_subfield K hK
  have h3 := kgLangT3_pow_three (by omega) K hK hA hhA
  obtain ⟨D, hD⟩ := kgLangT3_exists_data hn hev K hK k hk h h1 h3 J₀ hJ E θ₀
  subst hD
  exact kgLangT3_core_z0 hn hev K hK k hk D A hA hhA α₀ hα₀A hα₀o J₀ hJ
    (kgLangT3_E_le_component hn hev K hK k hk D A hA hhA α₀ hα₀A hα₀o J₀ hJ E θ₀ hAt)

theorem kgLangAxisT3Input_holds : KGLangAxisT3Input :=
  kgLangAxisT3Input_of_strong fun _ K _ _ hn hev hK => kgLangT3Strong_holds hn hev K hK

end CFSG.StandardType
