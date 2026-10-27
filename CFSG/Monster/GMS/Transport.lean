module

public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {X Y : Type*} [Group X] [Group Y]

theorem map_centralizer_singleton (e : X ≃* Y) (x : X) :
    (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y) := by
  apply le_antisymm
  · have := Subgroup.map_centralizer_le_centralizer_image ({x} : Set X) e.toMonoidHom
    simpa using this
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    apply e.injective
    simpa using hy

@[expose] noncomputable def centralizerMulEquiv (e : X ≃* Y) (x : X) :
    Subgroup.centralizer ({x} : Set X) ≃* Subgroup.centralizer ({e x} : Set Y) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton e x))

@[simp]
theorem coe_centralizerMulEquiv (e : X ≃* Y) (x : X) (c : Subgroup.centralizer ({x} : Set X)) :
    (centralizerMulEquiv e x c : Y) = e c := rfl

private theorem map_center_mulEquiv {P R : Type*} [Group P] [Group R] (e : P ≃* R) :
    (Subgroup.center P).map e.toMonoidHom = Subgroup.center R := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

private theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {P R : Type*} [Group P] [Group R]
    (e : P ≃* R) (h : IsExtraspecialPGroup p P) : IsExtraspecialPGroup p R := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator P).map e.toMonoidHom = commutator R := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini P).map e.toMonoidHom = frattini R :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, map_center_mulEquiv]
  · rw [← hf, hfrat, map_center_mulEquiv]
  · rw [← map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]

theorem GMSLeechCentralizer.of_mulEquiv (e : X ≃* Y) {z : X} (h : GMSLeechCentralizer z) :
    GMSLeechCentralizer (e z) := by
  obtain ⟨hz, hQ, hcard, ⟨φ, hφ, hker⟩, hcon⟩ := h
  set eC := centralizerMulEquiv e z with heC
  have hcore : (pCore 2 (Subgroup.centralizer ({z} : Set X))).map eC.toMonoidHom =
      pCore 2 (Subgroup.centralizer ({e z} : Set Y)) := pCore_map_iso 2 eC
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact hz, ?_, ?_, ⟨φ.comp eC.symm.toMonoidHom, ?_, ?_⟩, ?_⟩
  · rw [← hcore]
    exact isExtraspecialPGroup_of_mulEquiv (eC.subgroupMap _) hQ
  · rw [← hcore, Subgroup.card_map_of_injective eC.injective]
    exact hcard
  · exact hφ.comp eC.symm.surjective
  · rw [← hcore, ← hker]
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map_equiv, MonoidHom.mem_ker]
    rfl
  · intro c hc
    rw [← hcore, Subgroup.mem_map_equiv]
    apply hcon
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro q hq
    have hq' : eC q ∈ pCore 2 (Subgroup.centralizer ({e z} : Set Y)) := by
      rw [← hcore]
      exact Subgroup.mem_map_of_mem _ hq
    have := hc (eC q) hq'
    apply eC.injective
    simpa using this

theorem GMSDoubleF2Centralizer.of_mulEquiv (e : X ≃* Y) {d₀ : B} {a : X}
    (h : GMSDoubleF2Centralizer d₀ a) : GMSDoubleF2Centralizer d₀ (e a) := by
  obtain ⟨ha, hperf, H, _, φ, hφ, hker, hF2⟩ := h
  set eC := centralizerMulEquiv e a with heC
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact ha, ?_, H, inferInstance,
    φ.comp eC.symm.toMonoidHom, hφ.comp eC.symm.surjective, ?_, hF2⟩
  · have hc : (commutator (Subgroup.centralizer ({a} : Set X))).map eC.toMonoidHom =
        commutator (Subgroup.centralizer ({e a} : Set Y)) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ eC.surjective]
    rw [← hc, hperf, Subgroup.map_top_of_surjective _ eC.surjective]
  · have hk : (φ.comp eC.symm.toMonoidHom).ker = φ.ker.map eC.toMonoidHom := by
      ext c
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map_equiv, MonoidHom.mem_ker]
      rfl
    rw [hk, Subgroup.map_map]
    have hcomp : (Subgroup.centralizer ({e a} : Set Y)).subtype.comp eC.toMonoidHom =
        e.toMonoidHom.comp (Subgroup.centralizer ({a} : Set X)).subtype := by
      ext c
      rfl
    rw [hcomp, ← Subgroup.map_map, hker, MonoidHom.map_zpowers]
    rfl

theorem GMSF1Type.of_mulEquiv (e : X ≃* Y) {d₀ : B} {a z : X} (h : GMSF1Type d₀ a z) :
    GMSF1Type d₀ (e a) (e z) :=
  ⟨h.1.of_mulEquiv e, h.2.of_mulEquiv e⟩

end CFSG.Monster.GMS
