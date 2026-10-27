module

public import CFSG.Quasithin.Background.D2Seventeen
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V]

theorem conj_mem_Jhat [Finite V] {X : Subgroup (MulAut V)} {g j : MulAut V} (hg : g ∈ X)
    (hj : j ∈ Jhat X) : g * j * g⁻¹ ∈ Jhat X := by
  have h : Jhat X ≤ (Jhat X).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun A hA a ha => ?_
    exact le_Jhat (conjBy_mem_QhatStar hA hg) (mem_conjBy_of_mem ha)
  exact h hj

theorem conj_mem_fittingOf_of_normalizes {J : Subgroup (MulAut V)} [Finite V] {g f : MulAut V}
    (hg : g ∈ Subgroup.normalizer (J : Set (MulAut V))) (hf : f ∈ fittingOf J) :
    g * f * g⁻¹ ∈ fittingOf J := by
  obtain ⟨f', hf', rfl⟩ := hf
  let φ : MulAut ↥J := conjAct J ⟨g, hg⟩
  have hφ := Subgroup.characteristic_iff_comap_eq.mp
    (inferInstance : (CFSG.fittingSubgroup ↥J).Characteristic) φ
  have h1 : f' ∈ (CFSG.fittingSubgroup ↥J).comap φ.toMonoidHom := by
    rw [hφ]
    exact hf'
  refine ⟨φ f', Subgroup.mem_comap.mp h1, ?_⟩
  exact (Subgroup.normalizerMonoidHom_apply_apply_coe J (Subgroup.inclusion le_rfl ⟨g, hg⟩) f')

theorem conj_mem_fittingOf_Jhat [Finite V] {X : Subgroup (MulAut V)} {g f : MulAut V} (hg : g ∈ X)
    (hf : f ∈ fittingOf (Jhat X)) : g * f * g⁻¹ ∈ fittingOf (Jhat X) := by
  refine conj_mem_fittingOf_of_normalizes ?_ hf
  rw [Subgroup.mem_normalizer_iff]
  intro j
  exact ⟨fun hj => conj_mem_Jhat hg hj, fun hj => by
    have := conj_mem_Jhat (X.inv_mem hg) hj
    simpa [mul_assoc] using this⟩

theorem map_conj_Jhat [Finite V] {X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) :
    (Jhat X).map (MulAut.conj g).toMonoidHom = Jhat X := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact conj_mem_Jhat hg hj
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := conj_mem_Jhat (X.inv_mem hg) hx
      simpa [mul_assoc] using this
    · simp [MulAut.conj_apply, mul_assoc]

theorem pCoreOf_two_Jhat [Finite V] {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥) :
    pCoreOf 2 (Jhat X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : X ≤ Subgroup.normalizer ((pCoreOf 2 (Jhat X) : Subgroup (MulAut V)) :
      Set (MulAut V)) := by
    intro g hg
    have h1 := pCoreOf_map_mulEquiv (r := 2) (MulAut.conj g) (Jhat X)
    rw [map_conj_Jhat hg] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.symm
  have hle : pCoreOf 2 (Jhat X) ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 (Jhat X)).trans (Jhat_le X)) hnorm
      (pCoreOf_isPGroup 2 (Jhat X))
  rw [hO2] at hle
  exact le_bot_iff.mp hle

theorem odd_card_fittingJ [Finite V] {X : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥) :
    Odd (Nat.card (fittingOf (Jhat X))) :=
  odd_card_fittingOf (pCoreOf_two_Jhat hO2)

section Decomp

variable [Finite V] {X : Subgroup (MulAut V)}

theorem commV_sup_fixV (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 X = ⊥) :
    commV (fittingOf (Jhat X)) ⊔ fixV (fittingOf (Jhat X)) = ⊤ ∧
      commV (fittingOf (Jhat X)) ⊓ fixV (fittingOf (Jhat X)) = ⊥ := by
  have h := coprime_decomp (P := fittingOf (Jhat X)) (odd_card_fittingJ hO2) hV (W := ⊤)
    (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at h
  exact h

theorem apply_mem_commV_F {g : MulAut V} (hg : g ∈ X) {v : V}
    (hv : v ∈ commV (fittingOf (Jhat X))) : g v ∈ commV (fittingOf (Jhat X)) := by
  induction hv using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨f, hf, v', rfl⟩ := hw
    refine Subgroup.subset_closure ⟨g * f * g⁻¹, conj_mem_fittingOf_Jhat hg hf, g v', ?_⟩
    simp [MulAut.mul_apply]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem apply_mem_fixV_F {g : MulAut V} (hg : g ∈ X) {v : V}
    (hv : v ∈ fixV (fittingOf (Jhat X))) : g v ∈ fixV (fittingOf (Jhat X)) := by
  intro f hf
  have h2 : (g⁻¹ * f * g⁻¹⁻¹) v = v := hv _ (conj_mem_fittingOf_Jhat (X.inv_mem hg) hf)
  have h3 := congrArg g h2
  simpa [MulAut.mul_apply] using h3

theorem eq_one_of_mem_F_fix_commV (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 X = ⊥)
    {f : MulAut V} (hf : f ∈ fittingOf (Jhat X)) (hfix : ∀ v ∈ commV (fittingOf (Jhat X)), f v = v) :
    f = 1 := by
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ commV (fittingOf (Jhat X)) ⊔ fixV (fittingOf (Jhat X)) := by
    rw [(commV_sup_fixV hV hO2).1]
    exact Subgroup.mem_top v
  obtain ⟨v₀, hv₀, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul, hfix v₀ hv₀, hc f hf]
  rfl

theorem eq_one_of_fix_commV (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) {j : MulAut V} (hj : j ∈ Jhat X)
    (hfix : ∀ v ∈ commV (fittingOf (Jhat X)), j v = v) : j = 1 := by
  have hcent : ∀ f ∈ fittingOf (Jhat X), j * f = f * j := by
    intro f hf
    have hF' : j * f * j⁻¹ ∈ fittingOf (Jhat X) := conj_mem_fittingOf hj hf
    have hc : j * f * j⁻¹ * f⁻¹ ∈ fittingOf (Jhat X) :=
      Subgroup.mul_mem _ hF' (Subgroup.inv_mem _ hf)
    have h1 : j * f * j⁻¹ * f⁻¹ = 1 := by
      refine eq_one_of_mem_F_fix_commV hV hO2 hc fun v hv => ?_
      have hfv : f⁻¹ v ∈ commV (fittingOf (Jhat X)) :=
        apply_mem_commV_F (((fittingOf_le _).trans (Jhat_le X)) (Subgroup.inv_mem _ hf)) hv
      have hjv : j⁻¹ (f⁻¹ v) = f⁻¹ v :=
        (MulEquiv.symm_apply_eq j).mpr (hfix _ hfv).symm
      calc (j * f * j⁻¹ * f⁻¹) v = j (f (j⁻¹ (f⁻¹ v))) := rfl
        _ = j (f (f⁻¹ v)) := by rw [hjv]
        _ = j v := by rw [show f (f⁻¹ v) = v from f.apply_symm_apply v]
        _ = v := hfix v hv
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hJsolv : Group.IsSolvable ↥(Jhat X) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (Jhat_le X))
  have hjF : j ∈ fittingOf (Jhat X) := by
    have hcen : (⟨j, hj⟩ : ↥(Jhat X)) ∈
        Subgroup.centralizer (CFSG.fittingSubgroup ↥(Jhat X) : Set ↥(Jhat X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f' hf'
      exact Subtype.ext (hcent (f' : MulAut V) ⟨f', hf', rfl⟩).symm
    exact ⟨⟨j, hj⟩, CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hJsolv hcen, rfl⟩
  exact eq_one_of_mem_F_fix_commV hV hO2 hjF hfix

end Decomp

end Gap6

end CFSG.Quasithin
