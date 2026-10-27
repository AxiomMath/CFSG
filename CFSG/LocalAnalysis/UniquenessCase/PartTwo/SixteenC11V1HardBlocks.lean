module

public import CFSG.Quasithin.H13.A6Realize
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.Quasithin.H13

theorem s16c11_v1_fixV_card_of_realizes {n : ℕ} (hn : 3 ≤ n) {J : Type} [CommGroup J] [Finite J]
    {H : Subgroup (MulAut J)} (hR : (altCoreModel n).Realizes H ⊤ ⊥)
    (B : Subgroup (Equiv.Perm (Fin n))) (hB : B ≤ alternatingGroup (Fin n)) :
    ∃ E : Subgroup (MulAut J), E ≤ H ∧ Nonempty (↥E ≃* ↥B) ∧
      Nat.card ↥(fixV E) = Nat.card ↥(fixV (B.map (G6.coreAct n))) := by
  classical
  obtain ⟨π, hπ⟩ := hR
  have hF : (altCoreModel n).Faithful := CFSG.Quasithin.H13.A6.altCoreModel_faithful hn
  have hinj : Function.Injective π := FFModel.RealizesVia.injective_of_faithful hF hπ
  obtain ⟨e₀, he₀⟩ := G64.RealizesVia.exists_secEquiv (D := altCoreModel n) rfl hπ
  let e : J ≃* ↥(G6.coreMod n) := e₀
  have he : ∀ (γ : ↥(alternatingGroup (Fin n))) (v : J),
      ((e (((π γ : ↥H) : MulAut J) v) : ↥(G6.coreMod n)) : G6.PermMod n) =
        G6.permAct n (γ : Equiv.Perm (Fin n)) ((e v : ↥(G6.coreMod n)) : G6.PermMod n) := by
    intro γ v
    exact he₀ γ v
  let φ : ↥(alternatingGroup (Fin n)) →* MulAut J := H.subtype.comp π
  let Bσ : Subgroup ↥(alternatingGroup (Fin n)) := B.comap (alternatingGroup (Fin n)).subtype
  let E : Subgroup (MulAut J) := Bσ.map φ
  have hinjφ : Function.Injective φ := fun a b hab => hinj (H.subtype_injective hab)
  let eBσB : ↥Bσ ≃* ↥B :=
    { toFun := fun b => ⟨((b : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)), b.2⟩
      invFun := fun b => ⟨⟨(b : Equiv.Perm (Fin n)), hB b.2⟩, b.2⟩
      left_inv := fun b => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun b => by apply Subtype.ext; rfl
      map_mul' := fun b c => by apply Subtype.ext; rfl }
  refine ⟨E, ?_, ⟨(Subgroup.equivMapOfInjective Bσ φ hinjφ).symm.trans eBσB⟩, ?_⟩
  · intro x hx
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (π b).2
  · have hmem : ∀ v : J, v ∈ fixV E ↔ e v ∈ fixV (B.map (G6.coreAct n)) := by
      intro v
      rw [mem_fixV, mem_fixV]
      constructor
      · intro hv y hy
        obtain ⟨σ, hσB, rfl⟩ := Subgroup.mem_map.mp hy
        have hbσ : (⟨σ, hB hσB⟩ : ↥(alternatingGroup (Fin n))) ∈ Bσ :=
          Subgroup.mem_comap.mpr hσB
        have hx : φ ⟨σ, hB hσB⟩ ∈ E := Subgroup.mem_map.mpr ⟨_, hbσ, rfl⟩
        have hvx : φ ⟨σ, hB hσB⟩ v = v := hv _ hx
        have hev : e (φ ⟨σ, hB hσB⟩ v) = (G6.coreAct n σ) (e v) := by
          apply Subtype.ext
          rw [G6.coreAct_coe]
          exact he ⟨σ, hB hσB⟩ v
        rw [hvx] at hev
        exact hev.symm
      · intro hw x hx
        obtain ⟨b, hbBσ, rfl⟩ := Subgroup.mem_map.mp hx
        have hbB : (b : Equiv.Perm (Fin n)) ∈ B := Subgroup.mem_comap.mp hbBσ
        have hfix := hw _ (Subgroup.mem_map.mpr ⟨(b : Equiv.Perm (Fin n)), hbB, rfl⟩)
        apply e.injective
        have he' : e (φ b v) = (G6.coreAct n (b : Equiv.Perm (Fin n))) (e v) := by
          apply Subtype.ext
          rw [G6.coreAct_coe]
          exact he b v
        exact he'.trans hfix
    exact Nat.card_congr (Equiv.subtypeEquiv e hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
