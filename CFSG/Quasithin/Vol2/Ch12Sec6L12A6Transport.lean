module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeaves
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

variable {G S : Type} [Group G] [Group S]

theorem commutator_map_mulEquiv_self (ψ : G ≃* S) {Y : Subgroup G} (h : ⁅Y, Y⁆ = Y) :
    ⁅Y.map ψ.toMonoidHom, Y.map ψ.toMonoidHom⁆ = Y.map ψ.toMonoidHom := by
  rw [← Subgroup.map_commutator, h]

theorem quasithinO2QuotientIso_map_mulEquiv (ψ : G ≃* S) {Y : Subgroup G} {H : Type*} [Group H]
    (h : quasithinO2QuotientIso Y H) : quasithinO2QuotientIso (Y.map ψ.toMonoidHom) H := by
  obtain ⟨φ, hφs, hφk⟩ := h
  let χ : ↥Y ≃* ↥(Y.map ψ.toMonoidHom) :=
    Subgroup.equivMapOfInjective Y ψ.toMonoidHom ψ.injective
  have hker : (φ.comp χ.symm.toMonoidHom).ker = (pCore 2 ↥Y).map χ.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, ← hφk, MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact Iff.rfl
  exact ⟨φ.comp χ.symm.toMonoidHom, hφs.comp χ.symm.surjective,
    by rw [hker, CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 χ]⟩

theorem pCoreOf_map_mulEquiv (ψ : G ≃* S) (Y : Subgroup G) :
    pCoreOf 2 (Y.map ψ.toMonoidHom) = (pCoreOf 2 Y).map ψ.toMonoidHom := by
  let χ : ↥Y ≃* ↥(Y.map ψ.toMonoidHom) :=
    Subgroup.equivMapOfInjective Y ψ.toMonoidHom ψ.injective
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 χ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isElemAbelian_map_mulEquiv' (ψ : G ≃* S) {E : Subgroup G} (h : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E.map ψ.toMonoidHom) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨x', hx', hx⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨y', hy', hy⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg ψ.toMonoidHom
      (congrArg Subtype.val (h.1.is_comm.comm (⟨x', hx'⟩ : E) ⟨y', hy'⟩))
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, h.2 x' hx', map_one]

theorem a6Config_map_mulEquiv (ψ : G ≃* S) {Y F : Subgroup G} (h : A6Config Y F) :
    A6Config (Y.map ψ.toMonoidHom) (F.map ψ.toMonoidHom) := by
  obtain ⟨hperf, hiso, hFQ, hFe, hN, hcomm⟩ := h
  refine ⟨commutator_map_mulEquiv_self ψ hperf, quasithinO2QuotientIso_map_mulEquiv ψ hiso, ?_,
    isElemAbelian_map_mulEquiv' ψ hFe, ?_, ?_⟩
  · rw [pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hFQ
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro s
    obtain ⟨g, rfl⟩ := ψ.surjective s
    have hyN := Subgroup.mem_normalizer_iff.1 (hN hy) g
    constructor
    · intro hs
      obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.1 hs
      have : g' = g := ψ.injective hgg'
      subst this
      exact ⟨y * g' * y⁻¹, hyN.1 hg', by simp⟩
    · intro hs
      obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.1 hs
      have : g' = y * g * y⁻¹ := ψ.injective (by simpa using hgg')
      subst this
      exact ⟨g, hyN.2 hg', by simp⟩
  · rw [← Subgroup.map_commutator, hcomm]

end CFSG.Quasithin.H13.K1262Two
