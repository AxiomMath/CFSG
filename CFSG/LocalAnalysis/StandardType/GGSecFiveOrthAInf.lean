module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private noncomputable def ct_ainf_orthHom
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}
    (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    ↥(ggAInf 3 B Bs x L D J) → ↥(QuadraticMap.orthogonalGroup Q) :=
  fun a => ⟨ggLin (p := 3) ι (a : MulAut ↥Bs),
    QuadraticMap.mem_orthogonalGroup_iff.mpr
      ((S.orth (ggLin (p := 3) ι a)).mp ⟨(a : MulAut ↥Bs), a.2, rfl⟩)⟩

private theorem ct_ainf_orthHom_injective
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}
    (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    Function.Injective (ct_ainf_orthHom S) := by
  intro a b h
  exact Subtype.ext (ggLin_injective (p := 3) ι (congrArg Subtype.val h))

private theorem ct_ainf_orthHom_surjective
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}
    (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    Function.Surjective (ct_ainf_orthHom S) := by
  intro g
  obtain ⟨a, ha, hga⟩ := (S.orth (g : V ≃ₗ[ZMod 3] V)).mpr
    (QuadraticMap.mem_orthogonalGroup_iff.mp g.2)
  exact ⟨⟨a, ha⟩, Subtype.ext hga⟩

private noncomputable def ct_ainf_orthEquiv
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}
    (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    ↥(ggAInf 3 B Bs x L D J) ≃ ↥(QuadraticMap.orthogonalGroup Q) :=
  Equiv.ofBijective (ct_ainf_orthHom S)
    ⟨ct_ainf_orthHom_injective S, ct_ainf_orthHom_surjective S⟩

private theorem ct_ainf_le_top
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} :
    ggAInf 3 B Bs x L D J ≤ ggAutomizer ⊤ Bs := by
  unfold ggAInf
  refine sup_le (ggAutomizer_mono Bs le_top) ?_
  exact iSup_le fun y => iSup_le fun K => iSup_le fun _ => ggAutomizer_mono Bs le_top

theorem GGOrthSetup.card_ggAInf
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) :
    Nat.card ↥(ggAInf 3 B Bs x L D J) = Nat.card (QuadraticMap.orthogonalGroup Q) := by
  exact Nat.card_congr (ct_ainf_orthEquiv S)

theorem GGOrthSetup.stab_ge
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hd : Module.finrank (ZMod 3) V = 5) (hx : x ∈ Bs) (hQx : Q (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0) :
    1152 ≤ Nat.card {φ : ↥(ggAutomizer ⊤ Bs) // (φ : MulAut ↥Bs) ⟨x, hx⟩ = ⟨x, hx⟩} := by
  classical
  have : Finite ↥Bs :=
    Finite.of_injective (fun b : ↥Bs => (b : G)) Subtype.coe_injective
  have : Finite V := Finite.of_equiv ↥Bs (Additive.ofMul.trans ι.toEquiv)
  have : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  have : Finite ↥(ggAutomizer ⊤ Bs) :=
    Finite.of_injective (fun φ : ↥(ggAutomizer ⊤ Bs) => (φ : MulAut ↥Bs)) Subtype.coe_injective
  let vx : V := ι (Additive.ofMul ⟨x, hx⟩)
  have hcard := card_stabilizer_five Q S.nondeg hd vx hQx
  let f : {g : QuadraticMap.orthogonalGroup Q // (g : V ≃ₗ[ZMod 3] V) vx = vx} →
      {φ : ↥(ggAutomizer ⊤ Bs) // (φ : MulAut ↥Bs) ⟨x, hx⟩ = ⟨x, hx⟩} := fun g =>
    ⟨⟨((ct_ainf_orthEquiv S).symm g).val,
        ct_ainf_le_top ((ct_ainf_orthEquiv S).symm g).2⟩, by
      have h1 : ct_ainf_orthHom S ((ct_ainf_orthEquiv S).symm g) = g :=
        Equiv.apply_symm_apply (ct_ainf_orthEquiv S) g
      have h2 : ggLin (p := 3) ι (((ct_ainf_orthEquiv S).symm g).val) =
          (g : V ≃ₗ[ZMod 3] V) :=
        congrArg (fun z : ↥(QuadraticMap.orthogonalGroup Q) => (z : V ≃ₗ[ZMod 3] V)) h1
      exact (ggLin_fix_iff (p := 3) ι (((ct_ainf_orthEquiv S).symm g).val) ⟨x, hx⟩).mpr
        (by rw [h2]; exact g.2)⟩
  have hf : Function.Injective f := by
    intro g₁ g₂ h
    apply Subtype.ext
    have hval : ((ct_ainf_orthEquiv S).symm g₁).val = ((ct_ainf_orthEquiv S).symm g₂).val :=
      congrArg (fun z => z.val.val) h
    have heq : (ct_ainf_orthEquiv S).symm g₁ = (ct_ainf_orthEquiv S).symm g₂ :=
      Subtype.ext hval
    calc (g₁ : ↥(QuadraticMap.orthogonalGroup Q)) =
          (ct_ainf_orthEquiv S) ((ct_ainf_orthEquiv S).symm g₁) :=
          (Equiv.apply_symm_apply (ct_ainf_orthEquiv S) g₁).symm
      _ = (ct_ainf_orthEquiv S) ((ct_ainf_orthEquiv S).symm g₂) := by rw [heq]
      _ = (g₂ : ↥(QuadraticMap.orthogonalGroup Q)) :=
          Equiv.apply_symm_apply (ct_ainf_orthEquiv S) g₂
  have hle : Nat.card {g : QuadraticMap.orthogonalGroup Q // (g : V ≃ₗ[ZMod 3] V) vx = vx} ≤
      Nat.card {φ : ↥(ggAutomizer ⊤ Bs) // (φ : MulAut ↥Bs) ⟨x, hx⟩ = ⟨x, hx⟩} :=
    Nat.card_le_card_of_injective f hf
  rcases hcard with h | h
  · rw [h] at hle; exact hle
  · omega

end CFSG.StandardType.OrthF3

end
