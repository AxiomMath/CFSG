module

public import CFSG.RankThree.PartOne.KF.R9Model
public import CFSG.RankThree.PartOne.KF.SymCtx

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne

namespace R9Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {L F : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (C : R9Ctx p L F f K)

@[expose] noncomputable def torU : torusVec p 4 K →* unitarySU 2 f K 4 :=
  (diagUHom.comp (torusVec p 4 K).subtype).codRestrict (unitarySU 2 f K 4) fun d =>
    C.torus_le _ (mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩)

theorem coe_torU (d : torusVec p 4 K) : ((C.torU d : unitarySU 2 f K 4) : GL (Fin 4) K) =
    diagU (d : Fin 4 → Kˣ) := rfl

@[expose] noncomputable def tor : torusVec p 4 K →* F :=
  (C.phi.comp C.torU).codRestrict F fun d =>
    (C.phi_mem_F_iff _).mpr (by
      rw [coe_torU]
      exact mem_torusSU_iff.mpr ⟨d.1, d.2.1, d.2.2, rfl⟩)

theorem coe_tor (d : torusVec p 4 K) : ((C.tor d : F) : G) = C.phi (C.torU d) := rfl

theorem torU_injective : Function.Injective C.torU := by
  intro d e h
  have h1 := congrArg (fun x : unitarySU 2 f K 4 => (x : GL (Fin 4) K)) h
  exact Subtype.ext (diagU_injective h1)

theorem tor_injective : Function.Injective C.tor := by
  intro d e h
  have h1 := congrArg (fun x : F => (x : G)) h
  exact C.torU_injective (C.phi_injective h1)

theorem tor_surjective : Function.Surjective C.tor := by
  intro e
  obtain ⟨x, hx, hxe⟩ := C.exists_decomp e.2
  obtain ⟨d, hd1, hd2, hdx⟩ := mem_torusSU_iff.mp hx
  refine ⟨⟨d, hd1, hd2⟩, Subtype.ext ?_⟩
  rw [coe_tor, ← hxe]
  congr 1
  exact Subtype.ext hdx

@[expose] noncomputable def torEquiv : torusVec p 4 K ≃* F :=
  MulEquiv.ofBijective C.tor ⟨C.tor_injective, C.tor_surjective⟩

theorem torEquiv_apply (d : torusVec p 4 K) : C.torEquiv d = C.tor d := rfl

theorem weylHom_tor (σ : Equiv.Perm (Fin 4)) (d : torusVec p 4 K) :
    C.weylHom σ (C.tor d) = C.tor (symAct p K σ d) := by
  apply Subtype.ext
  rw [coe_weylHom_apply, coe_tor, coe_tor]
  have h1 : C.phi (C.permHom σ) * C.phi (C.torU d) * (C.phi (C.permHom σ))⁻¹ =
      C.phi (C.permHom σ * C.torU d * (C.permHom σ)⁻¹) := by simp [map_mul, map_inv]
  rw [h1]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_permHom, coe_torU]
  rw [permGL_conj_diagU]
  rfl

theorem weylHom_eq : C.weylHom = (MulAut.congr C.torEquiv).toMonoidHom.comp (symAut p K) := by
  refine MonoidHom.ext fun σ => MulEquiv.ext fun e => ?_
  obtain ⟨d, rfl⟩ := C.tor_surjective e
  show C.weylHom σ (C.tor d) = C.torEquiv (symAct p K σ (C.torEquiv.symm (C.tor d)))
  rw [← C.torEquiv_apply, MulEquiv.symm_apply_apply, C.torEquiv_apply, C.weylHom_tor]
  rfl

@[expose] noncomputable def toSymCtx : SymCtx p 4 K L F where
  tor := C.torEquiv
  exists_elt σ := ⟨C.phi (C.permHom σ), C.phi_perm_mem_normalizer σ, C.phi_mem_L _, by
    have h := DFunLike.congr_fun C.weylHom_eq σ
    exact h⟩
  induced g hg hgL := by
    have hmem : F.normalizerMonoidHom ⟨g, hg⟩ ∈ torusImage F L :=
      Sec12Three.mem_torusImage_iff.mpr ⟨g, hgL, hg, rfl⟩
    rw [C.torusImage_eq_range] at hmem
    obtain ⟨σ, hσ⟩ := hmem
    exact ⟨σ, by rw [← hσ]; exact DFunLike.congr_fun C.weylHom_eq σ⟩

end R9Ctx

end CFSG.RankThree.PartOne.KFU
