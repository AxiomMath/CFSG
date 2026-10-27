module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section Lifts

variable {K : Type} [Field K] {n : ℕ} {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}

theorem descAut_eq_of_induces (hψ : Function.Surjective ψ) (hZ : ψ.ker = Subgroup.center L')
    {a : MulAut L'} {φ : MulAut (TwE6Delta.RecipeR K n)} (h : ∀ l, φ (ψ l) = ψ (a l)) :
    BstarDesc.descAut hψ hZ a = φ :=
  MulEquiv.ext fun r => by
    obtain ⟨l, rfl⟩ := hψ r
    rw [BstarDesc.descAut_apply, h]

theorem descAut_conj (hψ : Function.Surjective ψ) (hZ : ψ.ker = Subgroup.center L') (l : L') :
    BstarDesc.descAut hψ hZ (MulAut.conj l) = MulAut.conj (ψ l) :=
  descAut_eq_of_induces hψ hZ fun m => by
    simp only [MulAut.conj_apply, map_mul, map_inv]

end Lifts

theorem torusLiftNineInput_holds :
    TorusLiftNineInput := by
  intro K _ _ n hn hK h3 h9 L' _ _ ψ hψ hker hperf hZ3 A hA h5 hind
  classical
  have hZR := TwE6Delta.center_recipeR_eq_bot hn hK
  have hkc : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hZR
  have hδinj := BstarDesc.descAut_injective hψ hkc hperf
  have hXI : ((A.map (BstarDesc.descAut hψ hkc) : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
      Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφa⟩ := hind a ha
    rw [descAut_eq_of_induces hψ hkc hφa]
    exact hφ
  obtain ⟨Y, hXY, hY, -, hYc, h9Y⟩ := TwE6DD2.exists_cubeTorus_recipe hn hK h3
    (hA.map (BstarDesc.descAut hψ hkc)) hXI
    (by rw [Subgroup.card_map_of_injective hδinj]; exact h5)
  obtain ⟨hYinn, W, hW, hW9, hYW⟩ := h9Y h9
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Subgroup L', ∀ l, l ∈ Λ ↔ MulAut.conj (ψ l) ∈ Y :=
    ⟨(Y.comap MulAut.conj).comap ψ, fun l => Iff.rfl⟩
  have hΛc : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y = y * x := fun x hx y hy =>
    TwE6DD2.commute_of_cube_mem hn hK hψ hker hperf hW hW9 hYW ((hΛ x).1 hx) ((hΛ y).1 hy)
  have hconj1 : ∀ r : TwE6Delta.RecipeR K n, MulAut.conj r = 1 → r = 1 := by
    intro r hr
    have hrZ : r ∈ Subgroup.center (TwE6Delta.RecipeR K n) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut (TwE6Delta.RecipeR K n) => f g) hr
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * r = r * g * r⁻¹ * r := by rw [h]
        _ = r * g := by group
    rw [hZR] at hrZ
    exact hrZ
  have hcube : ∀ x ∈ Λ, x ^ 3 ∈ Subgroup.center L' := by
    intro x hx
    rw [← hkc, MonoidHom.mem_ker]
    apply hconj1
    rw [map_pow, map_pow]
    exact hY.2 _ ((hΛ x).1 hx)
  let f : Λ →* Y := ((MulAut.conj : TwE6Delta.RecipeR K n →* MulAut _).comp
    (ψ.comp Λ.subtype)).codRestrict Y fun x => (hΛ x).1 x.2
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨r, rfl⟩ := hYinn hy
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨⟨l, (hΛ l).2 hy⟩, rfl⟩
  have hZΛ : ∀ z ∈ Subgroup.center L', z ∈ Λ := by
    intro z hz
    have hz' : ψ z = 1 := by rw [← MonoidHom.mem_ker, hkc]; exact hz
    rw [hΛ, hz', map_one]
    exact Y.one_mem
  have hZf : Nat.card (Subgroup.center L') ≤ Nat.card f.ker := by
    refine Nat.card_le_card_of_injective
      (fun z => (⟨⟨z, hZΛ z z.2⟩, ?_⟩ : f.ker)) fun z w h => ?_
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have hz' : ψ z = 1 := by rw [← MonoidHom.mem_ker, hkc]; exact z.2
      change MulAut.conj (ψ z) = 1
      rw [hz', map_one]
    · exact Subtype.ext (congrArg (fun x : f.ker => ((x : Λ) : L')) h)
  have hΛcard : 3 * 3 ^ 6 ≤ Nat.card Λ := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hfs, hYc]
    rw [hZ3] at hZf
    exact Nat.mul_le_mul_right _ hZf
  let g : Λ →* L' :=
    { toFun := fun x => (x : L') ^ 3
      map_one' := by simp
      map_mul' := fun x y => by
        change ((x : L') * y) ^ 3 = (x : L') ^ 3 * (y : L') ^ 3
        exact (show Commute (x : L') y from hΛc x x.2 y y.2).mul_pow 3 }
  have hgr : Nat.card g.range ≤ 3 := by
    rw [← hZ3]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨x, rfl⟩
    exact hcube x x.2
  have hEΛ : g.ker.map Λ.subtype ≤ Λ := Subgroup.map_subtype_le _
  refine ⟨g.ker.map Λ.subtype, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · exact hΛc a (hEΛ a.2) b (hEΛ b.2)
  · rintro _ ⟨x, hx, rfl⟩
    exact (MonoidHom.mem_ker).1 hx
  · rw [Subgroup.card_map_of_injective Λ.subtype_injective]
    have h1 : 3 * 3 ^ 6 ≤ Nat.card g.ker * 3 :=
      hΛcard.trans ((Subgroup.card_ker_mul_card_range g).symm.le.trans
        (Nat.mul_le_mul_left _ hgr))
    norm_num at h1 ⊢
    omega
  · rintro a ha _ ⟨x, -, rfl⟩
    have hax : BstarDesc.descAut hψ hkc a ∈ Y := hXY ⟨a, ha, rfl⟩
    obtain ⟨r, hr⟩ := hYinn hax
    obtain ⟨l, rfl⟩ := hψ r
    have hl : l ∈ Λ := (hΛ l).2 (by rw [hr]; exact hax)
    have hla : MulAut.conj l = a := hδinj (by rw [descAut_conj]; exact hr)
    rw [← hla, MulAut.conj_apply]
    change l * (x : L') * l⁻¹ = x
    rw [hΛc l hl x x.2, mul_inv_cancel_right]

end CFSG.StandardType.TwE6D3
