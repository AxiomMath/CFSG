module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Quot
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Cent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}
variable {Y : Type} [Group Y]

theorem nine3_thm77 (h : Nine3T79Setup V T A K S X p g x) {ρ : ↥K →* Equiv.Perm (ZMod p)}
    (hρ : Nine3FibreAct K S p x ρ) {π : ↥(nineH0 V K g) →* Y}
    (hπ : Nine3QuotHyp (nineH0 V K g) π) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) {c : ZMod p} (hUc : Nine3Fib K p ρ U c) (hc0 : c ≠ 0)
    {a u : ↥(nineH0 V K g)} (haA : (a : G) ∈ A) (haR : (a : G) ∉ pCoreOf 2 K)
    (huU : (u : G) ∈ U) (huR : (u : G) ∉ pCoreOf 2 K) (hau : π a * π u ≠ π u * π a)
    {D : Subgroup G} (hD : D ∈ nine3Dcal V (nineH0 V K g)) {d : ↥(nineH0 V K g)}
    (hdD : (d : G) ∈ D) (hdV : ∀ w : ↥(nineH0 V K g), (w : G) ∈ V → π w ≠ π d)
    (hda : π d * π a = π a * π d) (hdu : π d * π u = π u * π d) : False := by
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨h.hc.core.A_mem_nineOmegaIn.1, h.hc.core.A_mem_nineOmegaIn.2.trans h.hc.core.S_le_K⟩
  have hAdcal : A ∈ nine3Dcal V (nineH0 V K g) := (nine3_omega_le_dcal h hAΩ).1
  have hUdcal : U ∈ nine3Dcal V (nineH0 V K g) := (nine3_omega_le_dcal h hU).1
  have hπa : π a ≠ 1 := fun h1 => hau (by rw [h1, one_mul, mul_one])
  have hπu : π u ≠ 1 := fun h1 => hau (by rw [h1, mul_one, one_mul])
  have hπd : π d ≠ 1 := by
    have h1 := hdV (1 : ↥(nineH0 V K g)) (by simp)
    rw [map_one] at h1
    exact fun hd1 => h1 hd1.symm
  have hda' : π d ≠ π a := by
    intro heq
    apply hau
    calc π a * π u = π d * π u := by rw [← heq]
      _ = π u * π d := hdu
      _ = π u * π a := by rw [heq]
  have hdu' : π d ≠ π u := by
    intro heq
    apply hau
    calc π a * π u = π a * π d := by rw [← heq]
      _ = π d * π a := hda.symm
      _ = π u * π a := by rw [heq]
  have hDA : ∀ z ∈ D, ∀ w ∈ A, z * w = w * z :=
    nine3_dcal_comm_of_quot h hπ hD hAdcal hdD haA hπd hπa hda' hda
  have hDU : ∀ z ∈ D, ∀ w ∈ U, z * w = w * z :=
    nine3_dcal_comm_of_quot h hπ hD hUdcal hdD huU hπd hπu hdu' hdu
  obtain ⟨k, hk, rfl⟩ := hD
  have hkK : k ∉ normalizer (V : Set G) := by
    intro hkM
    have hVeq : conjSubgroup V k = V := conjSubgroup_eq_iff_mem_normalizer.mpr hkM
    have hdmem : (d : G) ∈ V := le_of_eq hVeq hdD
    exact (hdV d hdmem) rfl
  have haK : (a : G) ∈ K := h.hc.core.S_le_K (h.hc.core.A_le_S haA)
  have huK : (u : G) ∈ K := hU.2 huU
  exact nine3_thm77_core (a := ⟨(a : G), haK⟩) (u := ⟨(u : G), huK⟩)
    h.hc hρ hUc hc0 haA haR huU huR hkK
    (fun z hz => hDA z hz (a : G) haA)
    (fun z hz => hDU z hz (u : G) huU)

end CFSG.LocalAnalysis.WeakClosure81
