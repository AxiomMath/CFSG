module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LangPositionPart1

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.RankThree.PartOne.KE
open CFSG.StandardType.F4ExplicitPos.FamilyPosition CFSG.StandardType.F4ExplicitPos.ConnectedJoint
open scoped Pointwise

namespace CFSG.StandardType.F4ExplicitPos.LangPosition

theorem f4_exists_lang_torus_of_conj_torus
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (f : ℕ) (hf : 1 ≤ f) {p : ℕ} (hpq : Nat.Coprime p (2 ^ f))
    {A : Subgroup (ModGL Tag.F4 Ω)} (hexp : ∀ x ∈ A, x ^ p = 1)
    (hFix : ∀ x ∈ A, entrywiseFrobGL Tag.F4 Ω 2 f x = x) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω) (hgA : ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup Tag.F4 Ω) :
    ∃ w : WeylGroup Tag.F4, ∃ g0 ∈ adjointGroup Tag.F4 Ω,
      entrywiseFrobGL Tag.F4 Ω 2 f g0 = g0 * canonicalRep (coxeterSystem Tag.F4) Ω w ∧
      ∀ x ∈ A, x ∈ (twistedTorusOf (canonicalRep (coxeterSystem Tag.F4) Ω w)
        (entrywiseFrobGL Tag.F4 Ω 2 f)).map (MulAut.conj g0).toMonoidHom := by
  classical
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hgA x x.2)
  have hexp' : ∀ (x : A) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit Tag.F4 (a x ^ p) = rootDiagUnit Tag.F4 1 := by
      have : rootDiagUnit Tag.F4 (a x ^ p) = rootDiagUnit Tag.F4 (a x) ^ p :=
        ((rootDiagUnitHom Tag.F4 Ω).map_pow (a x) p)
      rw [this, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * (x : ModGL Tag.F4 Ω) * g) ^ p = g⁻¹ * (x : ModGL Tag.F4 Ω) ^ p * g := by
            have := conj_pow (a := g⁻¹) (b := (x : ModGL Tag.F4 Ω)) (i := p)
            rwa [inv_inv] at this
        _ = 1 := by rw [hexp x x.2]; group
    have h2 : a x ^ p = 1 := rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hn : ∀ x : A, (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g) *
      entrywiseFrobGL Tag.F4 Ω 2 f (rootDiagUnit Tag.F4 (a x)) *
      (g⁻¹ * entrywiseFrobGL Tag.F4 Ω 2 f g)⁻¹ = rootDiagUnit Tag.F4 (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix x x.2]
    group
  obtain ⟨w', z, hz, hlang⟩ :=
    f4_exists_lang_datum_of_plane (Ω := Ω) (a := a) f hf hpq hexp' hg hn
  have hzC := familyGroup_le_familyCentralizer (K := Ω) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL Tag.F4 Ω 2 f (g * z) =
      (g * z) * canonicalRep (coxeterSystem Tag.F4) Ω w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨w', g * z, mul_mem hg hzG, hu, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, d = rootDiagUnit Tag.F4 (a ⟨x, hx⟩) := ⟨_, rfl⟩
  have hzd : z⁻¹ * d * z = d := by
    have := hzcomm ⟨x, hx⟩
    rw [← hd, mul_inv_eq_iff_eq_mul] at this
    calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
      _ = z⁻¹ * (z * d) := by rw [this]
      _ = d := by group
  have ht : (g * z)⁻¹ * x * (g * z) = d := by
    have h0 := ha ⟨x, hx⟩
    rw [← hd] at h0
    calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
      _ = d := by rw [h0, hzd]
  refine ⟨(g * z)⁻¹ * x * (g * z), ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_twistedTorusOf, ht]
    refine ⟨hd ▸ rootDiagUnit_mem_torusGroup _, ?_⟩
    have hFd : entrywiseFrobGL Tag.F4 Ω 2 f d =
        (canonicalRep (coxeterSystem Tag.F4) Ω w')⁻¹ * d *
          canonicalRep (coxeterSystem Tag.F4) Ω w' := by
      rw [← ht, map_mul, map_mul, map_inv, hFix x hx, hu]
      group
    rw [hFd]
    group
  · change (g * z) * ((g * z)⁻¹ * x * (g * z)) * (g * z)⁻¹ = x
    group

end CFSG.StandardType.F4ExplicitPos.LangPosition

end

end
