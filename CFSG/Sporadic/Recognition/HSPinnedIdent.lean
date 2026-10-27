module

public import CFSG.Sporadic.Recognition.HSPinned
public import CFSG.Sporadic.Recognition.HSGraph
public import CFSG.Sporadic.Recognition.HSPinnedIdentInputs
public import Certificates.Certificate6102
public meta import CFSG.Sporadic.Recognition.HSGraphModel
public meta import Certificates.Data.CFSGNative.Recognition.HSPinnedData
public import Certificates.Certificate2028
public import Certificates.Certificate2031
public import Certificates.Certificate2037
public import Certificates.Certificate2038
public import Certificates.Certificate2195
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate2035
public import Certificates.Certificate3029
public import Certificates.Certificate3167
public import Certificates.Certificate2039
public import Certificates.Certificate2040
public import Certificates.Certificate6100
public import Certificates.Certificate6101
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.Sporadic.Recognition.HSPinned

open CFSG.Sporadic.Recognition.HSGraph CFSG.ComponentClassification.WittDesign
  CFSG.Sporadic.Recognition.HSPinned.Native CFSG.Blueprint

theorem isoFun_injective : Function.Injective isoFun := by
  have : ∀ i j : Fin 100, isoFun i = isoFun j → i = j := Certificates.certificate6102.1
  exact fun i j h => this i j h

theorem iso_check : ∀ i j : Fin 100, adjB i.val j.val = true ↔
    (hsGraph hexads).Adj (modelVertAtF (isoFun i)) (modelVertAtF (isoFun j)) :=
  Certificates.certificate6102.2

@[expose] noncomputable def sigmaIso :
    Fin 100 ≃ Vert hexads :=
  (Equiv.ofBijective isoFun
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨isoFun_injective, rfl⟩)).trans modelVertEquiv

theorem sigmaIso_adj
    (i j : Fin 100) :
    (hsGraph hexads).Adj (sigmaIso i) (sigmaIso j) ↔ sigmaExplicit.Adj i j :=
  (iso_check i j).symm

theorem sigmaIso_permCongr_mem
    (g : NativeSporadic.HS) :
    sigmaIso.permCongr (hsPerm g) ∈ autGroup hexads := by
  intro u v
  obtain ⟨x, rfl⟩ := sigmaIso.surjective u
  obtain ⟨y, rfl⟩ := sigmaIso.surjective v
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, sigmaIso_adj, sigmaIso_adj, sigmaExplicit_adj, sigmaExplicit_adj,
    hsPerm_apply, hsPerm_apply, hs_smul_def, hs_smul_def, adjB_smul]

@[expose] noncomputable def autHom :
    NativeSporadic.HS →* autGroup hexads :=
  (sigmaIso.permCongrHom.toMonoidHom.comp hsPerm).codRestrict (autGroup hexads)
    sigmaIso_permCongr_mem

theorem autHom_apply
    (g : NativeSporadic.HS) :
    (autHom g : Equiv.Perm (Vert hexads)) = sigmaIso.permCongr (hsPerm g) := rfl

theorem autHom_injective :
    Function.Injective autHom := by
  intro g h hgh
  apply hsPerm_injective
  have := congrArg Subtype.val hgh
  rw [autHom_apply, autHom_apply] at this
  exact sigmaIso.permCongrHom.injective this

universe u

theorem eq_range_and_nonempty_mulEquiv
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    {𝓑 : Finset (Finset Ω)} (h : IsSteinerTriple 𝓑) (f : NativeSporadic.HS →* autGroup 𝓑)
    (hf : Function.Injective f) (H : Subgroup (autGroup 𝓑)) (hH : H.index = 2) :
    H = f.range ∧ Nonempty (H ≃* NativeSporadic.HS) := by
  obtain ⟨-, -, ⟨-, hA, -⟩, ⟨⟨H₀, -, huniq⟩, -⟩⟩ :=
    higman_sims_1968_graph_automorphism_group 𝓑 h
  have hcard : Nat.card f.range = 44352000 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  have hidx : f.range.index = 2 := by
    have h2 := Subgroup.card_mul_index f.range
    rw [hcard, hA] at h2
    omega
  have e : H = f.range := (huniq H hH).trans (huniq _ hidx).symm
  exact ⟨e, ⟨(MulEquiv.subgroupCongr e).trans (MonoidHom.ofInjective hf).symm⟩⟩

theorem nonempty_mulEquiv_hs :
    ∀ H : Subgroup (autGroup hexads), H.index = 2 → Nonempty (H ≃* NativeSporadic.HS) :=
  fun H hH => (eq_range_and_nonempty_mulEquiv isSteinerTriple_hexads autHom autHom_injective H hH).2

end CFSG.Sporadic.Recognition.HSPinned
