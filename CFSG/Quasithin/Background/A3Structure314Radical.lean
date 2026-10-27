module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin.A314

open CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] [Finite X]

theorem map_solvableRadical_eq_center {V : Subgroup X} [V.Normal] (hV : Group.IsSolvable ↥V)
    (hQ : CFSG.IsQuasisimple (X ⧸ V)) :
    (CFSG.solvableRadical X).map (QuotientGroup.mk' V) = Subgroup.center (X ⧸ V) := by
  have hRs : Group.IsSolvable ↥(CFSG.solvableRadical X) := A3.solvableRadical_isSolvable
  have hVR : V ≤ CFSG.solvableRadical X := A3.le_solvableRadical inferInstance hV
  have hnt : Nontrivial (X ⧸ V) := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  apply le_antisymm
  · have hN : ((CFSG.solvableRadical X).map (QuotientGroup.mk' V)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective V)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hN with htop | hle
    · exfalso
      let f : ↥(CFSG.solvableRadical X) →* ↥((CFSG.solvableRadical X).map (QuotientGroup.mk' V)) :=
        ((QuotientGroup.mk' V).comp (CFSG.solvableRadical X).subtype).codRestrict _
          (fun r => ⟨r, r.2, rfl⟩)
      have hf : Function.Surjective f := by
        rintro ⟨_, ⟨r, hr, rfl⟩⟩
        exact ⟨⟨r, hr⟩, rfl⟩
      have h1 : Group.IsSolvable ↥((CFSG.solvableRadical X).map (QuotientGroup.mk' V)) :=
        Group.isSolvable_of_surjective hf
      have h2 : Group.IsSolvable (X ⧸ V) := by
        have e : ↥((CFSG.solvableRadical X).map (QuotientGroup.mk' V)) ≃* (X ⧸ V) :=
          (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
        exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
      have : Group.IsPerfect (X ⧸ V) := hQ.1
      exact Group.IsPerfect.not_isSolvable (X ⧸ V) h2
    · exact hle
  · set C : Subgroup X := (Subgroup.center (X ⧸ V)).comap (QuotientGroup.mk' V) with hC
    have hVC : V ≤ C := fun v hv => by
      show QuotientGroup.mk' V v ∈ Subgroup.center (X ⧸ V)
      have h1 : QuotientGroup.mk' V v = 1 := (QuotientGroup.eq_one_iff v).mpr hv
      rw [h1]
      exact Subgroup.one_mem _
    have hCn : C.Normal := Subgroup.Normal.comap inferInstance _
    have hCs : Group.IsSolvable ↥C := by
      let g : ↥C →* ↥(Subgroup.center (X ⧸ V)) :=
        ((QuotientGroup.mk' V).comp C.subtype).codRestrict _ (fun c => c.2)
      have hcomm : Group.IsSolvable ↥(Subgroup.center (X ⧸ V)) :=
        Group.isSolvable_of_comm fun a b => Subtype.ext (by
          have := Subgroup.mem_center_iff.mp a.2 (b : X ⧸ V)
          exact this.symm)
      exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion hVC) g (by
        intro c hc
        have h1 : QuotientGroup.mk' V (c : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
        exact ⟨⟨c, (QuotientGroup.eq_one_iff (c : X)).mp h1⟩, rfl⟩)
    have hCR : C ≤ CFSG.solvableRadical X := A3.le_solvableRadical hCn hCs
    calc Subgroup.center (X ⧸ V)
        = C.map (QuotientGroup.mk' V) :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) _).symm
      _ ≤ (CFSG.solvableRadical X).map (QuotientGroup.mk' V) := Subgroup.map_mono hCR

theorem solvableRadical_quotient_equiv {V : Subgroup X} [V.Normal] (hV : Group.IsSolvable ↥V)
    (hQ : CFSG.IsQuasisimple (X ⧸ V)) :
    Nonempty ((X ⧸ CFSG.solvableRadical X) ≃* ((X ⧸ V) ⧸ Subgroup.center (X ⧸ V))) := by
  have hVR : V ≤ CFSG.solvableRadical X := A3.le_solvableRadical inferInstance hV
  have hmap := map_solvableRadical_eq_center hV hQ
  exact ⟨(QuotientGroup.quotientQuotientEquivQuotient V (CFSG.solvableRadical X) hVR).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hmap)⟩

theorem solvableRadical_eq_of_simple {V : Subgroup X} [V.Normal] (hV : Group.IsSolvable ↥V)
    (hs : IsSimpleGroup (X ⧸ V)) (hna : ∃ a b : X ⧸ V, a * b ≠ b * a) :
    CFSG.solvableRadical X = V := by
  have hQ : CFSG.IsQuasisimple (X ⧸ V) := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna |>.1
  have hVR : V ≤ CFSG.solvableRadical X := A3.le_solvableRadical inferInstance hV
  refine le_antisymm (fun x hx => ?_) hVR
  have h1 : QuotientGroup.mk' V x ∈ (CFSG.solvableRadical X).map (QuotientGroup.mk' V) :=
    ⟨x, hx, rfl⟩
  rw [map_solvableRadical_eq_center hV hQ] at h1
  have hc : Subgroup.center (X ⧸ V) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ V)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center (X ⧸ V) := by rw [h]; trivial
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  rw [hc, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).mp h1

end CFSG.Quasithin.A314
