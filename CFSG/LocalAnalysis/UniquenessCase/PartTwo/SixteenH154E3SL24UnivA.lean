module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24UnivB
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_univ_universal (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    (hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L) :
    ∀ (V' : Type) [CommGroup V'] [Finite V']
      (ρ' : ↥(CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range →* MulAut V')
      (W0' : Subgroup V')
      (ψ' : V' →* ↥(commSub ⊤ L) ⧸ (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L)),
      (∀ v : V', v ^ 2 = 1) →
        (∀ w ∈ W0', ∀ g : ↥(CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range,
          ρ' g w = w) →
      Subgroup.closure {w : V' | ∃ (g : ↥(CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range)
        (v : V'), w = ρ' g v * v⁻¹} = ⊤ →
      Function.Surjective ψ' → ψ'.ker = W0' →
      (∀ (g : ↥(CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range) (v' : V')
        (v : ↥(commSub ⊤ L)), ψ' v' = QuotientGroup.mk v →
        ψ' (ρ' g v') = QuotientGroup.mk ((g : MulAut ↥(commSub ⊤ L)) v)) →
      ∃ θ : ↥(commSub ⊤ L) →* V', Function.Surjective θ ∧
        (∀ (g : ↥(CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range) (v : ↥(commSub ⊤ L)),
          θ ((g : MulAut ↥(commSub ⊤ L)) v) = ρ' g (θ v)) ∧
        ∀ v : ↥(commSub ⊤ L), ψ' (θ v) = QuotientGroup.mk v := by
  intro V' _ _ ρ' W0' ψ' hV2 hfix hgen hψs hψk hψe
  classical
  have hperf : Group.IsPerfect ↥L := by
    obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hrow.2
    letI := hKf
    letI := hKfin
    obtain ⟨π, hπ⟩ := hreal
    have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
    haveI : Group.IsPerfect (FFModel.nat (StatedSL 2 K)).Gam :=
      CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
    exact Group.IsPerfect.ofSurjective (f := π) hπ.1
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) (fun l _ y _ => Subgroup.mem_top (l y))
  have hcomm : XMod.commOf ↥L (commSub ⊤ L) = commSub ⊤ L := by
    rw [commOf_eq_commSub, hUc]
  have hcommV : commV (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range = ⊤ :=
    CFSG.Quasithin.H13.VolI.commV_resHom_range hU hcomm
  let G : Subgroup (MulAut ↥(commSub ⊤ L)) :=
    (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range
  let αE : (s16h_sl24_univModel L hU).Gam →* MulAut ↥(s16h_sl24_univModel L hU).sec :=
    Subgroup.subtype _
  have hαE : ∀ (γ : ↥G) (m : ↥(commSub ⊤ L)),
      ((αE γ m : ↥(commSub ⊤ L)) : W) = (s16h_sl24_univModel L hU).act γ (m : W) := by
    intro γ m
    show (((γ : MulAut ↥(commSub ⊤ L)) m : ↥(commSub ⊤ L)) : W) = _
    simp only [s16h_sl24_univModel]
    rw [dif_pos m.2]
  have hkfix : ∀ (γ : ↥G) (m : ↥(commSub ⊤ L)), (m : W) ∈ commSub ⊤ L ⊓ fixV L →
      αE γ m = m := by
    intro γ m hm
    have hmZ : m ∈ (commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L) := hm
    have h := CFSG.Quasithin.H13.VolI.subgroupOf_le_fixV_resHom_range hU
      (inf_le_right : commSub ⊤ L ⊓ fixV L ≤ fixV L) hmZ
    exact mem_fixV.1 h (γ : MulAut ↥(commSub ⊤ L)) γ.2
  have hgenE : ∀ m : ↥(commSub ⊤ L),
      m ∈ Subgroup.closure {x | ∃ γ y, x = αE γ y * y⁻¹} :=
    fun m => CFSG.Quasithin.H13.VolI.mem_closure_of_commV (ρ := αE) (H := G)
      (fun γ => γ.2) (fun x hx => ⟨⟨x, hx⟩, rfl⟩) hcommV m
  have hE2 : ∀ m : ↥(commSub ⊤ L), m ^ 2 = 1 :=
    fun m => CFSG.Quasithin.H13.VolI.sq_eq_one_of_subgroup hW m
  have hbound : ∀ (W' : Type) [CommGroup W'] [Finite W'], (∀ w : W', w ^ 2 = 1) →
      ∀ C : CFSG.Quasithin.H13.VolI.ModelCover (s16h_sl24_univModel L hU) W',
        Nat.card C.β.ker ≤
          Nat.card ↥((s16h_sl24_univModel L hU).ker.subgroupOf
            (s16h_sl24_univModel L hU).sec) :=
    fun W' _ _ hW2 C => s16h_sl24_univ_bound hW hrow hZ4 hU hW2 C
  let C : CFSG.Quasithin.H13.VolI.ModelCover (s16h_sl24_univModel L hU) V' :=
    { ρ := ρ'
      β := ψ'
      surj := hψs
      fix := fun γ v hv => hfix v (hψk ▸ (MonoidHom.mem_ker.2 hv)) γ
      equiv := fun γ v m hm hvm => by
        have h := hψe γ v m hvm
        have hmm : (⟨(s16h_sl24_univModel L hU).act γ (m : W), hm⟩ : ↥(commSub ⊤ L)) =
            (γ : MulAut ↥(commSub ⊤ L)) m :=
          Subtype.ext (hαE γ m).symm
        rw [hmm]
        exact h
      gen := fun v => hgen ▸ Subgroup.mem_top v }
  obtain ⟨θ, hθs, -, hθe, hθβ⟩ := CFSG.Quasithin.MS93.ModelCover.exists_quotient αE hαE hkfix
    hgenE hE2 hbound hV2 C
  exact ⟨θ, hθs, fun g v => hθe g v, fun v => hθβ v⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
