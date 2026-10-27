module

public import CFSG.Monster.GMS.Transport

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

@[expose] def IsTwoBabyCentralizer (a : G) : Prop :=
  orderOf a = 2 ∧ commutator (Subgroup.centralizer ({a} : Set G)) = ⊤ ∧
    ∃ φ : Subgroup.centralizer ({a} : Set G) →* B, Function.Surjective φ ∧
      φ.ker.map (Subgroup.centralizer ({a} : Set G)).subtype = Subgroup.zpowers a

@[expose] def SLSStatement (d₀ : B) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H] (d : H), orderOf d = 2 →
    Nonempty (Subgroup.centralizer ({d} : Set H) ≃* Subgroup.centralizer ({d₀} : Set B)) →
      Nonempty (H ≃* B)

theorem GMSDoubleF2Centralizer.isTwoBabyCentralizer [Finite G] {d₀ : B} (hSLS : SLSStatement d₀)
    {a : G} (h : GMSDoubleF2Centralizer d₀ a) : IsTwoBabyCentralizer a := by
  obtain ⟨ha, hperf, H, _, φ, hφ, hker, hsimple, x, hx, ⟨e⟩⟩ := h
  have : Finite H := Finite.of_surjective φ hφ
  obtain ⟨ψ⟩ := @hSLS H _ _ hsimple x hx ⟨e⟩
  refine ⟨ha, hperf, (MonoidHom.ofClass ψ).comp φ, ?_, ?_⟩
  · intro y
    obtain ⟨h, rfl⟩ := ψ.surjective y
    obtain ⟨c, rfl⟩ := hφ h
    exact ⟨c, rfl⟩
  · have hk : ((MonoidHom.ofClass ψ).comp φ).ker = φ.ker := by
      ext c
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.coe_ofClass,
        MulEquiv.map_eq_one_iff]
    rw [hk, hker]

theorem IsTwoBabyCentralizer.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a : X}
    (h : IsTwoBabyCentralizer a) : IsTwoBabyCentralizer (e a) := by
  obtain ⟨ha, hperf, φ, hφ, hker⟩ := h
  set eC := centralizerMulEquiv e a with heC
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact ha, ?_, φ.comp eC.symm.toMonoidHom,
    hφ.comp eC.symm.surjective, ?_⟩
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

end CFSG.Monster.GMS
