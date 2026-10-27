module

public import CFSG.Milestones.ASVolI.H6
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.ASVolI.ChH

variable {W : Type} [CommGroup W]

private theorem s16jp_zmod2_cases (k : ZMod 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem s16jp_permModAct_single {Γ : Type} [Group Γ] [DecidableEq Γ] (γ x : Γ)
    (c : ZMod 2) :
    permModAct Γ Γ γ (Multiplicative.ofAdd (Pi.single x c)) =
      Multiplicative.ofAdd (Pi.single (γ * x) c) := by
  apply Multiplicative.toAdd.injective
  funext y
  have happly : Multiplicative.toAdd (permModAct Γ Γ γ
      (Multiplicative.ofAdd (Pi.single x c))) y =
      Pi.single (M := fun _ => ZMod 2) x c (γ⁻¹ * y) := rfl
  rw [happly]
  by_cases hy : y = γ * x
  · subst hy
    rw [inv_mul_cancel_left, toAdd_ofAdd, Pi.single_eq_same, Pi.single_eq_same]
  · have h1 : γ⁻¹ * y ≠ x := by
      intro h
      exact hy (by rw [← mul_inv_cancel_left γ y, h])
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 2) h1 c, toAdd_ofAdd,
      Pi.single_eq_of_ne (M := fun _ => ZMod 2) hy c]

private theorem s16jp_hom_ext_basis {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f g : Multiplicative (ι → ZMod 2) →* G)
    (h : ∀ i, f (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) =
      g (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))) : f = g := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  have hs : ∀ s : Finset ι, f (Multiplicative.ofAdd (∑ i ∈ s, Pi.single i (v i))) =
      g (Multiplicative.ofAdd (∑ i ∈ s, Pi.single i (v i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, ofAdd_add, map_mul, map_mul, ih]
      congr 1
      rcases s16jp_zmod2_cases (v j) with h0 | h1
      · rw [h0]; simp
      · rw [h1]; exact h j
  have := hs Finset.univ
  rwa [Finset.univ_sum_single] at this

private theorem s16jp_sq_eq_one_sub {V : Type} [CommGroup V] (hV2 : ∀ v : V, v ^ 2 = 1)
    (U : Subgroup V) (u : ↥U) : u * u = 1 := by
  apply Subtype.ext
  simpa [pow_two] using hV2 (u : V)

private def s16jp_actU {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (l : ↥L) (u : ↥U) : ↥U :=
  ⟨(l : MulAut V) (u : V), hU (l : MulAut V) l.2 (u : V) u.2⟩

private def s16jp_actUHom {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (l : ↥L) : ↥U →* ↥U where
  toFun := s16jp_actU hU l
  map_one' := by
    apply Subtype.ext
    simp [s16jp_actU]
  map_mul' := fun u v => by
    apply Subtype.ext
    simp [s16jp_actU, map_mul]

private def s16jp_pv {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) {Γ : Type} [Group Γ] (π : Γ →* ↥L) (w₀ : ↥U)
    (γ : Γ) : ↥U :=
  s16jp_actU hU (π γ) w₀

private def s16jp_gHom {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hV2 : ∀ v : V, v ^ 2 = 1) {Γ : Type} [Group Γ]
    (π : Γ →* ↥L) (w₀ : ↥U) (γ : Γ) : Multiplicative (ZMod 2) →* ↥U where
  toFun y := if Multiplicative.toAdd y = 0 then 1 else s16jp_pv hU π w₀ γ
  map_one' := by simp
  map_mul' := fun y z => by
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases s16jp_zmod2_cases (Multiplicative.toAdd y) with hy | hy <;>
      rcases s16jp_zmod2_cases (Multiplicative.toAdd z) with hz | hz
    · simp [toAdd_mul, hy, hz, h10]
    · simp [toAdd_mul, hy, hz, h10]
    · simp [toAdd_mul, hy, hz, h10]
    · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      have hsq := s16jp_sq_eq_one_sub hV2 U (s16jp_pv hU π w₀ γ)
      simp [toAdd_mul, hy, hz, h10, h11, hsq]

private theorem s16jp_gHom_ofAdd_one {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hV2 : ∀ v : V, v ^ 2 = 1)
    {Γ : Type} [Group Γ] (π : Γ →* ↥L) (w₀ : ↥U) (γ : Γ) :
    s16jp_gHom hU hV2 π w₀ γ (Multiplicative.ofAdd (1 : ZMod 2)) =
      s16jp_pv hU π w₀ γ := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp [s16jp_gHom, h10]

private theorem s16jp_gHom_pairwise {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hV2 : ∀ v : V, v ^ 2 = 1)
    {Γ : Type} [Group Γ] (π : Γ →* ↥L) (w₀ : ↥U) :
    Pairwise fun i j => ∀ x y : Multiplicative (ZMod 2),
      Commute (s16jp_gHom hU hV2 π w₀ i x) (s16jp_gHom hU hV2 π w₀ j y) :=
  fun _ _ _ _ _ => Commute.all _ _

private def s16jp_Phi {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hV2 : ∀ v : V, v ^ 2 = 1) {Γ : Type} [Group Γ]
    [Fintype Γ] [DecidableEq Γ] (π : Γ →* ↥L) (w₀ : ↥U) :
    Multiplicative (Γ → ZMod 2) →* ↥U :=
  (MonoidHom.noncommPiCoprod (fun γ => s16jp_gHom hU hV2 π w₀ γ)
    (s16jp_gHom_pairwise hU hV2 π w₀)).comp
    (MulEquiv.piMultiplicative (fun _ : Γ => ZMod 2)).toMonoidHom

private theorem s16jp_Phi_single {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hV2 : ∀ v : V, v ^ 2 = 1)
    {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] (π : Γ →* ↥L) (w₀ : ↥U) (γ : Γ) :
    s16jp_Phi hU hV2 π w₀ (Multiplicative.ofAdd (Pi.single γ (1 : ZMod 2))) =
      s16jp_pv hU π w₀ γ := by
  have hpi : (MulEquiv.piMultiplicative (fun _ : Γ => ZMod 2))
      (Multiplicative.ofAdd (Pi.single γ (1 : ZMod 2))) =
      Pi.mulSingle γ (Multiplicative.ofAdd (1 : ZMod 2)) := by
    funext j
    by_cases hj : j = γ
    · subst hj
      simp [MulEquiv.piMultiplicative, Pi.mulSingle]
    · simp [MulEquiv.piMultiplicative, Pi.mulSingle, Pi.single, hj]
  simp only [s16jp_Phi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hpi, MonoidHom.noncommPiCoprod_mulSingle]
  exact s16jp_gHom_ofAdd_one hU hV2 π w₀ γ

private theorem s16jp_Phi_equiv_hom {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hV2 : ∀ v : V, v ^ 2 = 1)
    {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ] (π : Γ →* ↥L) (w₀ : ↥U) (δ : Γ) :
    (s16jp_Phi hU hV2 π w₀).comp (permModAct Γ Γ δ) =
      (s16jp_actUHom hU (π δ)).comp (s16jp_Phi hU hV2 π w₀) := by
  apply s16jp_hom_ext_basis
  intro γ
  change (s16jp_Phi hU hV2 π w₀) ((permModAct Γ Γ δ)
      (Multiplicative.ofAdd (Pi.single γ (1 : ZMod 2)))) =
    (s16jp_actUHom hU (π δ)) ((s16jp_Phi hU hV2 π w₀)
      (Multiplicative.ofAdd (Pi.single γ (1 : ZMod 2))))
  rw [s16jp_permModAct_single (Γ := Γ), s16jp_Phi_single, s16jp_Phi_single]
  apply Subtype.ext
  simp [s16jp_pv, s16jp_actUHom, s16jp_actU, map_mul]

theorem s16jp_eq_bot_of_regular_summand [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    (hc : commSub U L = U) (hZU : Z ≤ U) (hZ : ∀ z ∈ Z, ∀ l ∈ L, l z = z)
    {Γ : Type} [Group Γ] [Finite Γ] (π : Γ →* ↥L) (hπ : Function.Surjective π)
    {A : Type} [CommGroup A] (actA : Γ →* MulAut A) (Q : Subgroup A)
    (β : ↥U →* ↥Q) (hβs : Function.Surjective β) (hβk : ∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : Γ) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
      ((β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ : ↥Q) : A) = actA γ ((β u : ↥Q) : A))
    (ι : ↥Q →* Multiplicative (Γ → ZMod 2)) (ρ : Multiplicative (Γ → ZMod 2) →* A)
    (hρι : ∀ q : ↥Q, ρ (ι q) = (q : A)) (hρQ : ∀ f, ρ f ∈ Q)
    (hι : ∀ (γ : Γ) (q q' : ↥Q), (q' : A) = actA γ (q : A) → ι q' = permModAct Γ Γ γ (ι q))
    (hρ : ∀ (γ : Γ) (f : Multiplicative (Γ → ZMod 2)),
      ρ (permModAct Γ Γ γ f) = actA γ (ρ f)) :
    Z = ⊥ := by
  classical
  letI : Fintype Γ := Fintype.ofFinite Γ
  let δ₁ : Multiplicative (Γ → ZMod 2) :=
    Multiplicative.ofAdd (Pi.single (1 : Γ) (1 : ZMod 2))
  have hδ₁ : δ₁ = Multiplicative.ofAdd (Pi.single (1 : Γ) (1 : ZMod 2)) := rfl
  have hρδ₁Q : ρ δ₁ ∈ Q := hρQ δ₁
  obtain ⟨w₀, hw₀⟩ := hβs ⟨ρ δ₁, hρδ₁Q⟩
  have hw₀A : ((β w₀ : ↥Q) : A) = ρ δ₁ := congrArg Subtype.val hw₀
  let Φ : Multiplicative (Γ → ZMod 2) →* ↥U := s16jp_Phi hU hW2 π w₀
  have hΦ_single : ∀ γ : Γ,
      Φ (Multiplicative.ofAdd (Pi.single γ (1 : ZMod 2))) = s16jp_pv hU π w₀ γ := by
    intro γ
    simpa [Φ] using s16jp_Phi_single hU hW2 π w₀ γ
  have hΦ_equiv : ∀ (δ : Γ) (f : Multiplicative (Γ → ZMod 2)),
      Φ (permModAct Γ Γ δ f) = s16jp_actU hU (π δ) (Φ f) := by
    intro δ f
    have hh := DFunLike.congr_fun (s16jp_Phi_equiv_hom hU hW2 π w₀ δ) f
    simpa [Φ, MonoidHom.comp_apply, s16jp_actUHom] using hh
  have hβΦ : ∀ f : Multiplicative (Γ → ZMod 2),
      ((β (Φ f) : ↥Q) : A) = ρ f := by
    intro f
    have hh : (Subgroup.subtype Q).comp (β.comp Φ) = ρ := by
      apply s16jp_hom_ext_basis
      intro γ
      change ((β (Φ (Multiplicative.ofAdd (Pi.single γ (1 : ZMod 2)))) : ↥Q) : A) =
        ρ (Multiplicative.ofAdd (Pi.single γ (1 : ZMod 2)))
      rw [hΦ_single]
      have hβe' : ((β (s16jp_pv hU π w₀ γ) : ↥Q) : A) = actA γ ((β w₀ : ↥Q) : A) :=
        hβe γ w₀ (hU ((π γ : ↥L) : MulAut W) (π γ).2 (w₀ : W) w₀.2)
      rw [hβe', hw₀A, ← hρ γ δ₁, hδ₁, s16jp_permModAct_single (Γ := Γ), mul_one]
    have hthis := DFunLike.congr_fun hh f
    simpa [MonoidHom.comp_apply] using hthis
  let σ : ↥Q →* ↥U := Φ.comp ι
  have hβσ : ∀ q : ↥Q, β (σ q) = q := by
    intro q
    apply Subtype.ext
    show ((β (σ q) : ↥Q) : A) = (q : A)
    rw [show σ q = Φ (ι q) from rfl, hβΦ (ι q), hρι q]
  have hactQ : ∀ (γ : Γ) (q : ↥Q), actA γ (q : A) ∈ Q := by
    intro γ q
    rw [← hρι q, ← hρ γ (ι q)]
    exact hρQ _
  have hσ_equiv : ∀ (γ : Γ) (q : ↥Q),
      σ ⟨actA γ (q : A), hactQ γ q⟩ = s16jp_actU hU (π γ) (σ q) := by
    intro γ q
    have hι' := hι γ q ⟨actA γ (q : A), hactQ γ q⟩ rfl
    show Φ (ι ⟨actA γ (q : A), hactQ γ q⟩) = s16jp_actU hU (π γ) (Φ (ι q))
    rw [hι', hΦ_equiv γ (ι q)]
  let S : Subgroup W := σ.range.map (Subgroup.subtype U)
  have hσ_mem_S : ∀ q : ↥Q, (σ q : W) ∈ S := by
    intro q
    exact Subgroup.mem_map.mpr ⟨σ q, ⟨q, rfl⟩, rfl⟩
  have hS_le_U : S ≤ U := Subgroup.map_subtype_le σ.range
  have hS_inv : ∀ l ∈ L, ∀ s ∈ S, l s ∈ S := by
    intro l hl s hs
    obtain ⟨γ, hγ⟩ := hπ ⟨l, hl⟩
    have hγ' : ((π γ : ↥L) : MulAut W) = l := congrArg Subtype.val hγ
    rw [← hγ']
    obtain ⟨u, hu_range, hus⟩ := Subgroup.mem_map.mp hs
    obtain ⟨q, hq⟩ := hu_range
    have hs_eq : s = (σ q : W) := by
      rw [← hus, ← hq]
      rfl
    have hval : ((π γ : ↥L) : MulAut W) s =
        (σ ⟨actA γ (q : A), hactQ γ q⟩ : W) := by
      rw [hs_eq, congrArg Subtype.val (hσ_equiv γ q)]
      rfl
    rw [hval]
    exact hσ_mem_S _
  have hZS : Z ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzZ, hzS⟩ := hz
    rw [Subgroup.mem_bot]
    obtain ⟨u, hu_range, hus⟩ := Subgroup.mem_map.mp hzS
    obtain ⟨q, hq⟩ := hu_range
    have hzu : z = (σ q : W) := by
      rw [← hus, ← hq]
      rfl
    have hmem : ((σ q : ↥U) : W) ∈ Z := by
      rw [← hzu]
      exact hzZ
    have hβ1 : β (σ q) = 1 := (hβk (σ q)).mpr hmem
    have hq1 : q = 1 := by
      rw [← hβσ q, hβ1]
    have hσq1 : σ q = 1 := by rw [hq1, map_one]
    rw [hzu, hσq1]
    rfl
  have hUS : Z ⊔ S = U := by
    apply le_antisymm
    · exact sup_le hZU hS_le_U
    · intro u hu
      let uU : ↥U := ⟨u, hu⟩
      let w : ↥U := uU * (σ (β uU))⁻¹
      have hwβ : β w = 1 := by
        show β (uU * (σ (β uU))⁻¹) = 1
        rw [map_mul, map_inv, hβσ (β uU), mul_inv_cancel]
      have hwZ : (w : W) ∈ Z := (hβk w).mp hwβ
      have hwval : (w : W) * ((σ (β uU) : ↥U) : W) = u := by
        have hwW : (w : W) = u * (((σ (β uU) : ↥U)) : W)⁻¹ := by simp [w, uU]
        rw [hwW, mul_assoc, inv_mul_cancel, mul_one]
      rw [Subgroup.mem_sup']
      exact ⟨⟨(w : W), hwZ⟩, ⟨((σ (β uU) : ↥U) : W), hσ_mem_S (β uU)⟩, hwval⟩
  have hcomm_le_S : commSub U L ≤ S := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨l, hl, u, hu, rfl⟩
    obtain ⟨z, hzZ, s, hsS, hzs⟩ := Subgroup.mem_sup.mp (by rw [hUS]; exact hu)
    have hlu : l u * u⁻¹ = l s * s⁻¹ := by
      rw [← hzs, map_mul, mul_inv_rev, hZ z hzZ l hl]
      calc z * l s * (s⁻¹ * z⁻¹)
          = (l s * s⁻¹) * (z * z⁻¹) := by ac_rfl
        _ = (l s * s⁻¹) * 1 := by rw [mul_inv_cancel]
        _ = l s * s⁻¹ := by rw [mul_one]
    rw [hlu]
    exact mul_mem (hS_inv l hl s hsS) (inv_mem hsS)
  have hZ_le_S : Z ≤ S := by
    refine le_trans hZU ?_
    rw [← hc]
    exact hcomm_le_S
  rw [eq_bot_iff]
  intro z hz
  have hzS : z ∈ S := hZ_le_S hz
  have hzbot : z ∈ Z ⊓ S := ⟨hz, hzS⟩
  rw [hZS] at hzbot
  exact hzbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
