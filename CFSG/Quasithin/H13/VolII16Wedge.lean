module

public import CFSG.Quasithin.H13.VolII16SLNat
public import CFSG.Quasithin.Background.JonesParshallWedgeH1

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Matrix Subgroup

theorem wedgeMat_transpose (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    wedgeMat Mᵀ = (wedgeMat M)ᵀ := by
  ext k l
  simp only [wedgeMat, Matrix.of_apply, Matrix.transpose_apply]
  ring

theorem muW_invTranspose (g : SpecialLinearGroup (Fin 5) (ZMod 2)) (x : Fin 10 → ZMod 2) :
    muW (ZMod 2) (invTransposeSL 5 (ZMod 2) g) x =
      (wedgeMat ((g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))ᵀ *ᵥ x := by
  rw [muW_apply, invTransposeSL_coe, wedgeMat_transpose]

theorem wedge_data {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (h : (FFModel.extSq (ZMod 2) 5).Realizes H ⊤ Z) :
    ∃ (ρ : SpecialLinearGroup (Fin 5) (ZMod 2) →* MulAut W)
      (β : W →* Multiplicative (Fin 10 → ZMod 2)),
      (∀ g, ρ g ∈ H) ∧ (∀ x ∈ H, ∃ g, ρ g = x) ∧ Function.Surjective β ∧
        (∀ w, β w = 1 ↔ w ∈ Z) ∧
        ∀ g w, Multiplicative.toAdd (β (ρ g w)) =
          wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Multiplicative.toAdd (β w) := by
  obtain ⟨π₀, b₀, hπs, hbs, hbk, hbe⟩ := topBot_data (D := FFModel.extSq (ZMod 2) 5) rfl rfl h
  set ψ := specialLinearGroupEquivStatedSL 5 (ZMod 2)
  let π : ↥(StatedSL 5 (ZMod 2)) →* ↥H := π₀
  let b : W →* Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) := b₀
  have hbe' : ∀ (g : SpecialLinearGroup (Fin 5) (ZMod 2)) (w : W),
      Multiplicative.toAdd (b (((π (ψ g) : ↥H) : MulAut W) w)) =
      exteriorPower.map 2 (Matrix.toLin' (g : Matrix (Fin 5) (Fin 5) (ZMod 2)))
        (Multiplicative.toAdd (b w)) := fun g w => congrArg Multiplicative.toAdd (hbe (ψ g) w)
  let ρ : SpecialLinearGroup (Fin 5) (ZMod 2) →* MulAut W := H.subtype.comp (π.comp ψ.toMonoidHom)
  let c : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) ≃* Multiplicative (Fin 10 → ZMod 2) :=
    AddEquiv.toMultiplicative (wedgeEquiv (ZMod 2)).toAddEquiv
  have hc : ∀ x, Multiplicative.toAdd (c x) = wedgeCoord (Multiplicative.toAdd x) := fun _ => rfl
  refine ⟨ρ, c.toMonoidHom.comp b, fun g => (π (ψ g)).2, fun x hx => ?_, ?_, fun w => ?_,
    fun g w => ?_⟩
  · obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := ψ.surjective γ
    exact ⟨g, congrArg Subtype.val hγ⟩
  · exact c.surjective.comp hbs
  · show c (b w) = 1 ↔ w ∈ Z
    rw [c.map_eq_one_iff]
    exact hbk w
  · show Multiplicative.toAdd (c (b (((π (ψ g) : ↥H) : MulAut W) w))) =
      wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Multiplicative.toAdd (c (b w))
    rw [hc, hc, hbe', wedgeCoord_map]

theorem wedge_cover
    {W : Type} [CommGroup W] (hW2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤)
    (h : (FFModel.extSq (ZMod 2) 5).Realizes H ⊤ Z) : Z = ⊥ := by
  obtain ⟨ρ, β, hρH, hρs, hβs, hβk, hβe⟩ := wedge_data h
  exact eq_bot_of_Z1A_eq_B1A (μ := fun g : SpecialLinearGroup (Fin 5) (ZMod 2) =>
    wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (θ := invTransposeSL 5 (ZMod 2)) muW_invTranspose Z1A_eq_B1A_wedge hW2 hβs hβk
    (fun g z hz => hZ hz _ (hρH g)) hβe (mem_closure_of_commV hρH hρs hcomm)

theorem sLExteriorTwo_five_eq_bot
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (hI : commV L ∈ IrrPlus L ⊤)
    (h : SLExteriorTwo L (commV L) (fixV L ⊓ commV L) 5) : fixV L ⊓ commV L = ⊥ :=
  eq_bot_of_restrict _ (fun _ _ _ hW2 _ _ hZ hcomm hR => wedge_cover hW2 hZ hcomm hR) hV2 hI h

end CFSG.Quasithin.H13.VolI
