module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspU5Model
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspU4
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.Ch4.U5A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.Sec53F.Unit

theorem exists_standard_parabolic {f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 f F) (P : Subgroup (hypPSU h 2 1))
    (hP : P ∈ UnitaryHigher.maximalParabolics h 2 1) :
    ∃ a : MulAut (hypPSU h 2 1),
      P.map a.toMonoidHom = u5PtP h ∨ P.map a.toMonoidHom = u5LnP h := by
  rw [(UnitaryHigher.unitary_maximal_parabolics h (by norm_num) (by norm_num)).1] at hP
  obtain ⟨W, ⟨hW0, hW⟩, rfl⟩ := hP
  obtain ⟨hd1, hd2, g, hg⟩ := UnitaryHigher.exists_smul_hypFlag_eq h (by norm_num) hW0 hW
  let a := MulAut.conj (hypProj h 2 1 g⁻¹)
  have hback : g⁻¹ • W = hypFlag h 2 1 (Module.finrank F W) :=
    (congrArg (fun X => g⁻¹ • X) hg.symm).trans (inv_smul_smul g _)
  have heq : (UnitaryHigher.projIsoStabilizer h 2 1 W).map a.toMonoidHom =
      UnitaryHigher.projIsoStabilizer h 2 1 (hypFlag h 2 1 (Module.finrank F W)) := by
    rw [UnitaryHigher.projIsoStabilizer_map_conj, hback]
  refine ⟨a, ?_⟩
  have hd : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
  rcases hd with hd | hd
  · left
    rw [heq, hd]
  · right
    rw [heq, hd]

theorem exists_unitary5_parabolic {G : Type} [Group G] [Finite G]
    (K P : Subgroup G) (m : ℕ)
    (hU : IsPSU 5 2 m (↥K ⧸ Subgroup.center ↥K))
    (hP : IsMaxParabolic2 K P) (hZ : IsPGroup 2 ↥(centerOf K)) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 m F),
      ∃ e : (↥K ⧸ Subgroup.center ↥K) ≃* hypPSU h 2 1,
        (C48Spor.img (Subgroup.center ↥K) P).map e.toMonoidHom = u5PtP h ∨
        (C48Spor.img (Subgroup.center ↥K) P).map e.toMonoidHom = u5LnP h := by
  obtain ⟨hadm, F, _, _, hF, ⟨e₁⟩⟩ := hU
  have h : UnitaryFieldData 2 m F :=
    ⟨Nat.prime_two, hadm.2.1, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  let e₀ : (↥K ⧸ Subgroup.center ↥K) ≃* hypPSU h 2 1 :=
    ((hypPSUEquivStatedProj h hR (by norm_num)).trans e₁.symm).symm
  have := h.finite
  have := finite_hypPSU_five h
  let Q := (C48Spor.img (Subgroup.center ↥K) P).map e₀.toMonoidHom
  obtain ⟨S, hS, hNS, hco⟩ := U4A.maxParabolic_center_image K P hP hZ
  have hS' : IsSylowTwoOf (S.map e₀.toMonoidHom) ⊤ :=
    L3M.isSylowTwoOf_map_top hS e₀.surjective
  have hco' : IsCoatom Q :=
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e₀) _).mpr hco
  have hNS' : Subgroup.normalizer (S.map e₀.toMonoidHom : Set (hypPSU h 2 1)) ≤ Q := by
    rw [← Subgroup.map_normalizer_eq_of_bijective S e₀.bijective]
    exact Subgroup.map_mono hNS
  have hi : ¬ 2 ∣ (S.map e₀.toMonoidHom).index := by
    have he : ((S.map e₀.toMonoidHom).subgroupOf ⊤).index =
        (S.map e₀.toMonoidHom).index := Subgroup.relIndex_top_right _
    rw [← he]
    exact hS'.2.2
  have hQ : Q ∈ UnitaryHigher.maximalParabolics h 2 1 := by
    refine ⟨hco', Subgroup.normalizer (S.map e₀.toMonoidHom : Set (hypPSU h 2 1)), ?_, hNS'⟩
    exact ⟨hS'.2.1.toSylow hi, rfl⟩
  obtain ⟨a, ha | ha⟩ := exists_standard_parabolic h Q hQ
  · refine ⟨F, inferInstance, h, e₀.trans a, Or.inl ?_⟩
    change (C48Spor.img (Subgroup.center ↥K) P).map
      (a.toMonoidHom.comp e₀.toMonoidHom) = u5PtP h
    rw [← Subgroup.map_map]
    exact ha
  · refine ⟨F, inferInstance, h, e₀.trans a, Or.inr ?_⟩
    change (C48Spor.img (Subgroup.center ↥K) P).map
      (a.toMonoidHom.comp e₀.toMonoidHom) = u5LnP h
    rw [← Subgroup.map_map]
    exact ha

theorem false_of_isPSU5_natural {G : Type} [Group G] [Finite G]
    (K P V : Subgroup G) (m : ℕ) (hm : 2 ≤ m)
    (hZ : IsPGroup 2 ↥(centerOf K))
    (hU : IsPSU 5 2 m (↥K ⧸ Subgroup.center ↥K))
    (hP : IsMaxParabolic2 K P)
    (hpsl : IsPSL 2 2 m (ModO2 (perfectCore P)))
    (hnat : ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ m ∧
      IsNaturalSection (perfectCore P) V (V ⊓ centerOf K)
        (CFSG.pCore 2 ↥(perfectCore P)) (StatedSL 2 k))
    (hV : V ≤ CFSG.Open.pCoreOf 2 (perfectCore P) ⊓
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 (perfectCore P) : Set G)) : False := by
  obtain ⟨F, _, h, e, hQ | hQ⟩ := exists_unitary5_parabolic K P m hU hP hZ
  · let δ := U4A.modO2_perfectCore_center_image K P (u5PtP h) hP.1.1 hZ e hQ
    apply U5M.false_of_isPSL_point h hm
    obtain ⟨ha, k, _, _, hk, ⟨e₁⟩⟩ := hpsl
    exact ⟨ha, k, inferInstance, inferInstance, hk, ⟨δ.symm.trans e₁⟩⟩
  · let δ := U4A.modO2_perfectCore_center_image K P (u5LnP h) hP.1.1 hZ e hQ
    apply U5M.false_of_isPSL_line h hm
    obtain ⟨ha, k, _, _, hk, ⟨e₁⟩⟩ := hpsl
    exact ⟨ha, k, inferInstance, inferInstance, hk, ⟨δ.symm.trans e₁⟩⟩

end CFSG.Quasithin.H13.Ch4.U5A
