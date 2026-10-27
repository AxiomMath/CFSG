module

public import CFSG.RankThree.PartOne.S10.PlaneContract
import CFSG.RankThree.PartOne.S10.FaithfulPlaneTwoActionMinimalFactors
import CFSG.RankThree.PartOne.S10.PlaneCoreBounds
import CFSG.RankThree.PartOne.S10.PlaneExtraspecialCase
import CFSG.RankThree.PartOne.S10.PlaneHyperplane
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly
open scoped commutatorElement

namespace PlaneObstruction

variable {p : ℕ} {B S D : Type} [Group B] [Group S] [Group D] [Finite B] [Finite S] [Finite D]
  [MulDistribMulAction B S]

theorem elementary_pair_contradiction (hp : p.Prime) (hp3 : 3 < p) (hDp : IsPGroup p D)
    (hDexp : ∀ x : D, x ^ p = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D) (hβ : Function.Injective β)
    (hS : IsPGroup 2 S)
    (he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3)
    {X E : Subgroup S} (hX : IsElementaryAbelian 2 X) (hE : IsElementaryAbelian 2 E)
    (hXE : ∀ x ∈ X, ∀ e ∈ E, x * e = e * x) (hdisj : X ⊓ E = ⊥) (hX5 : 5 ≤ Nat.card X)
    (hE4 : 4 ≤ Nat.card E) : False := by
  let f : (X × E) →* S := X.subtype.noncommCoprod E.subtype (fun x e => hXE x x.2 e e.2)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, e⟩ h
    have h1 : (x : S) * e = 1 := by
      have : f (x, e) = (x : S) * e := MonoidHom.noncommCoprod_apply _ _ _ _
      rwa [this] at h
    have h2 : (x : S) = (e : S)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (x : S) ∈ X ⊓ E := ⟨x.2, h2 ▸ E.inv_mem e.2⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have hx : x = 1 := Subtype.ext h3
    have he1 : (e : S) = 1 := by rw [h3, one_mul] at h1; exact h1
    have he1' : e = 1 := Subtype.ext he1
    rw [hx, he1']
    rfl
  have h16 := PlaneCore.card_le_sixteen β hp hp3 hDp hDexp hDcl hβ hS he (A := X × E)
    (fun a b => Prod.ext (hX.is_comm.comm a.1 b.1) (hE.is_comm.comm a.2 b.2))
    (fun a => Prod.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) a.1) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) a.2)) f hf
  rw [Nat.card_prod] at h16
  nlinarith

theorem exists_four_subgroup (hp : p.Prime) (hp3 : 3 < p) (hS : IsPGroup 2 S) {X : Subgroup S}
    (hX : MinimalPlaneFactor B X) {Bi Bj : Subgroup B} (hBjc : Nat.card Bj = p)
    (hBi : ∀ c : B, c ∈ Bi ↔ ∀ s ∈ X, c • s = s) (hsup : Bi ⊔ Bj = ⊤)
    (hcommB : ∀ x y : B, x * y = y * x) :
    ∃ E : Subgroup S, E ≤ X ∧ IsElementaryAbelian 2 E ∧ 4 ≤ Nat.card E := by
  by_cases hel : IsElementaryAbelian 2 X
  · obtain ⟨h5, -⟩ := PlaneFactorCases.elementary_factor_data hp hp3 hX hel hBjc hBi hsup hcommB
    exact ⟨X, le_rfl, hel, le_trans (by norm_num) h5⟩
  · obtain ⟨n, hsp⟩ := PlaneFactorCases.special_factor_package hp hp3 hS hX hel hBjc hBi hsup
      hcommB
    obtain ⟨E, hEX, hE, hE4⟩ := hsp.four_group
    exact ⟨E, hEX, hE, hE4.ge⟩

omit [Finite B] [Finite S] in
theorem actionCentralizes_sup {X Y : Subgroup S} (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hX : ActionCentralizes B X) (hY : ActionCentralizes B Y) :
    ActionCentralizes B (X ⊔ Y) := by
  intro b g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := PlaneCommuting.exists_mul_of_mem_sup hXY hg
  rw [smul_mul', hX b x hx, hY b y hy]

theorem plane_core (hp : p.Prime) (hp3 : 3 < p) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S)
    (hfaith : ∀ c : B, (∀ s : S, c • s = s) → c = 1) (hDp : IsPGroup p D)
    (hDexp : ∀ x : D, x ^ p = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D) (hβ : Function.Injective β)
    (he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, S₁, S₂, hS₀inv, hS₁ne, hS₂ne, hS₁S₀, hS₂S₀, hS₀eq, hcomm, hfaith₀, hM₁, hM₂,
    ⟨B₁, B₂, hB₁c, hB₂c, hB₁₂, hB₁₂bot, hB₁₂sup, hB₁k, hB₂k⟩, hJc, hJfix⟩ :=
    faithful_plane_two_action_commuting_minimal_factors p hp hp2 B S hB hBcard hS hfaith
  have hcommB : ∀ x y : B, x * y = y * x := fun x y => hB.is_comm.comm x y
  have hcomm' : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx)
      y hy).symm
  have hsup' : B₂ ⊔ B₁ = ⊤ := by rw [sup_comm]; exact hB₁₂sup
  have hfixJ : ∀ J : Subgroup S, J ≤ S₁ ⊓ S₂ → ActionCentralizes B J :=
    fun J hJ b s hs => hJfix b s (hJ hs)
  by_cases hel₁ : IsElementaryAbelian 2 S₁
  · obtain ⟨h5, hno⟩ := PlaneFactorCases.elementary_factor_data hp hp3 hM₁ hel₁ hB₂c hB₁k
      hB₁₂sup hcommB
    obtain ⟨E, hES₂, hE, hE4⟩ := exists_four_subgroup hp hp3 hS hM₂ hB₁c hB₂k hsup' hcommB
    have hdisj : S₁ ⊓ E = ⊥ := hno _ inf_le_left (hfixJ _ (inf_le_inf_left S₁ hES₂))
    exact elementary_pair_contradiction hp hp3 hDp hDexp hDcl β hβ hS he hel₁ hE
      (fun x hx e he' => hcomm' x hx e (hES₂ he')) hdisj h5 hE4
  by_cases hel₂ : IsElementaryAbelian 2 S₂
  · obtain ⟨h5, hno⟩ := PlaneFactorCases.elementary_factor_data hp hp3 hM₂ hel₂ hB₁c hB₂k
      hsup' hcommB
    obtain ⟨E, hES₁, hE, hE4⟩ := exists_four_subgroup hp hp3 hS hM₁ hB₂c hB₁k hB₁₂sup hcommB
    have hdisj : S₂ ⊓ E = ⊥ := hno _ inf_le_left (hfixJ _ fun x hx => ⟨hES₁ hx.2, hx.1⟩)
    exact elementary_pair_contradiction hp hp3 hDp hDexp hDcl β hβ hS he hel₂ hE
      (fun x hx e he' => (hcomm' e (hES₁ he') x hx).symm) hdisj h5 hE4
  obtain ⟨n₁, hsp₁⟩ := PlaneFactorCases.special_factor_package hp hp3 hS hM₁ hel₁ hB₂c hB₁k
    hB₁₂sup hcommB
  obtain ⟨n₂, hsp₂⟩ := PlaneFactorCases.special_factor_package hp hp3 hS hM₂ hel₂ hB₁c hB₂k
    hsup' hcommB
  have hZ₁Z₂ : ∀ x ∈ inSubgroup Subgroup.center S₁, ∀ y ∈ inSubgroup Subgroup.center S₂,
      x * y = y * x := fun x hx y hy => hcomm' x (hsp₁.le hx) y (hsp₂.le hy)
  have h1 := hsp₁.elementary
  have h2 := hsp₂.elementary
  have hZel : IsElementaryAbelian 2 ↥(inSubgroup Subgroup.center S₁ ⊔
      inSubgroup Subgroup.center S₂) :=
    IsElementaryAbelian.sup_of_le_centralizer fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun x hx => hZ₁Z₂ x hx y hy
  have hZfix := actionCentralizes_sup hZ₁Z₂ hsp₁.fixed hsp₂.fixed
  have hZcent : ∀ z ∈ inSubgroup Subgroup.center S₁ ⊔ inSubgroup Subgroup.center S₂,
      ∀ s ∈ S₁, z * s = s * z := by
    intro z hz s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := PlaneCommuting.exists_mul_of_mem_sup hZ₁Z₂ hz
    calc x * y * s = x * (y * s) := mul_assoc _ _ _
      _ = x * (s * y) := by rw [hcomm' s hs y (hsp₂.le hy)]
      _ = x * s * y := (mul_assoc _ _ _).symm
      _ = s * x * y := by rw [hsp₁.central x hx s hs]
      _ = s * (x * y) := mul_assoc _ _ _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hS.to_subgroup
    (inSubgroup Subgroup.center S₁ ⊔ inSubgroup Subgroup.center S₂))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have hbot := Subgroup.card_eq_one.mp hk
    exact hsp₁.ne_bot (eq_bot_iff.mpr (le_sup_left.trans hbot.le))
  by_cases hk1 : k = 1
  · subst hk1
    exact PlaneExtraspecialCase.extraspecial_case_contradiction hp hp3 hS hDp hDexp hDcl β hβ he
      hsp₁ hsp₂ hcomm' (by simpa using hk)
  · have hZ4 : 4 ≤ Nat.card ↥(inSubgroup Subgroup.center S₁ ⊔ inSubgroup Subgroup.center S₂) := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hB₁ne : B₁ ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hB₁c
      exact hp.one_lt.ne hB₁c
    obtain ⟨⟨b₁, hb₁B₁⟩, hb₁1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB₁ne
    exact PlaneHyperplane.hyperplane_contradiction hp hp3 hB hS hDp hDexp hDcl β hβ he hsp₁
      (fun h => hb₁1' (Subtype.ext h)) ((hB₁k b₁).mp hb₁B₁) le_sup_left hZel hZfix hZcent hZ4

end PlaneObstruction

theorem faithful_plane_two_action_on_defining_prime_group_rank_obstruction :
    ∀ (p : ℕ), p.Prime → 3 < p → ∀ (B S : Type) [Group B] [Group S] [Finite B] [Finite S]
      [MulDistribMulAction B S], IsElementaryAbelian p B → Nat.card B = p ^ 2 → IsPGroup 2 S →
      (∀ c : B, (∀ s : S, c • s = s) → c = 1) →
      ∀ (D : Type) [Group D] [Finite D], IsPGroup p D →
      ∀ β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D, Function.Injective β →
        3 < evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) := by
  intro p hp hp3 B S _ _ _ _ _ hB hBcard hS hfaith D _ _ hDp β hβ
  by_contra hcon
  have he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3 := not_lt.mp hcon
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hBp : IsPGroup p B := IsPGroup.of_card (n := 2) hBcard
  have hDnt : Nontrivial D := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : Subsingleton (MulAut D) := ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    have h2 : Subsingleton (S ⋊[MulDistribMulAction.toMulAut B S] B) := hβ.subsingleton
    have h3 : Subsingleton B :=
      (SemidirectProduct.inr_injective (φ := MulDistribMulAction.toMulAut B S)).subsingleton
    have h4 : Nat.card B = 1 := Nat.card_of_subsingleton 1
    rw [hBcard] at h4
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨D₀, hchar, hne, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hDp
  have := hchar
  let β₀ : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D₀ :=
    (MulAut.characteristic D₀).comp β
  have hker : IsPGroup p β₀.ker := by
    refine IsPGroup.of_injective hfix ((β.comp β₀.ker.subtype).codRestrict _ ?_) ?_
    · intro t
      rw [mem_fixingSubgroup_iff (MulAut D)]
      intro d hd
      have := congrArg (fun φ : MulAut D₀ => ((φ ⟨d, hd⟩ : D₀) : D)) (MonoidHom.mem_ker.mp t.2)
      exact this
    · intro a b hab
      exact Subtype.ext (hβ (congrArg Subtype.val hab))
  have hbot : β₀.ker = ⊥ :=
    PlaneSemidirect.eq_bot_of_normal_isPGroup hp hp2 hBp hS hfaith β₀.ker hker
  have hβ₀ : Function.Injective β₀ := (MonoidHom.ker_eq_bot_iff β₀).mp hbot
  have hDp₀ : IsPGroup p D₀ := hDp.to_subgroup D₀
  have hDexp₀ : ∀ x : D₀, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hDcl₀ : commutator D₀ ≤ Subgroup.center D₀ := PlaneCore.commutator_le_center_of_critical hcl
  let ι : D₀ ⋊[β₀] (S ⋊[MulDistribMulAction.toMulAut B S] B) →*
      D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B) :=
    SemidirectProduct.map D₀.subtype (MonoidHom.id _) fun k => MonoidHom.ext fun d => rfl
  have hι : Function.Injective ι := by
    intro x y hxy
    have hl : (ι x).left = (ι y).left := congrArg SemidirectProduct.left hxy
    have hr : (ι x).right = (ι y).right := congrArg SemidirectProduct.right hxy
    exact SemidirectProduct.ext (D₀.subtype_injective hl) hr
  have he₀ : evenRank (D₀ ⋊[β₀] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3 :=
    (PlaneAux.evenRank_le_of_injective ι hι).trans he
  exact PlaneObstruction.plane_core hp hp3 hB hBcard hS hfaith hDp₀ hDexp₀ hDcl₀ β₀ hβ₀ he₀

end CFSG.RankThree.PartOne
