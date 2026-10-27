module

public import CFSG.Quasithin.Background.B69SL3
public import CFSG.Quasithin.Background.B69Comp2

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.SL3Pair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open B6
open scoped commutatorElement

namespace B69

section TwoSections

variable {V : Type} [CommGroup V] [Finite V]

theorem arith_ul_ff {a k k' aY cY c₁ c₂ s₁ s₂ d y : ℕ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hd : 0 < d) (ha : 0 < a) (H1 : y ≤ aY * cY) (H2 : k ≤ k') (H3 : aY * k' = a)
    (H4 : cY ≤ c₁ * c₂ * d) (H5 : y = s₁ * s₂ * d) (H6 : 2 * a * c₁ * c₂ ≤ s₁ * s₂ * k) :
    False := by
  have h1 : y * k ≤ a * (c₁ * c₂ * d) := by
    calc y * k ≤ aY * cY * k := Nat.mul_le_mul_right _ H1
      _ ≤ aY * cY * k' := Nat.mul_le_mul_left _ H2
      _ = a * cY := by rw [← H3]; ring
      _ ≤ a * (c₁ * c₂ * d) := Nat.mul_le_mul_left _ H4
  have h2 : 2 * (a * (c₁ * c₂ * d)) ≤ y * k := by
    calc 2 * (a * (c₁ * c₂ * d)) = (2 * a * c₁ * c₂) * d := by ring
      _ ≤ (s₁ * s₂ * k) * d := Nat.mul_le_mul_right _ H6
      _ = y * k := by rw [H5]; ring
  have hpos : 0 < a * (c₁ * c₂ * d) := by positivity
  linarith


theorem false_of_two_sections_ff (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {W₁ W₂ : Subgroup V} (h₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (h₂ : W₂ ∈ IrrPlus L (⊤ : Subgroup V)) (hne : W₁ ≠ W₂)
    (hGT : 2 * Nat.card A * Nat.card ↥(fixV (autSec A W₁ (fixV L))) *
        Nat.card ↥(fixV (autSec A W₂ (fixV L))) ≤
      Nat.card (Sec W₁ (fixV L)) * Nat.card (Sec W₂ (fixV L)) *
        Nat.card ↥(A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L))) : False := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hA₁ := a_stab_irr hV hA hL hLA h₁
  have hA₂ := a_stab_irr hV hA hL hLA h₂
  have hind := inf_le_fixV_of_ne h₁ h₂ hne
  have hAY : ∀ a ∈ A, ∀ y ∈ W₁ ⊔ W₂, a y ∈ W₁ ⊔ W₂ := isInv_sup hA₁ hA₂
  have hAst : A ≤ stabSub (W₁ ⊔ W₂) := B1.le_stabSub_of_invariant hAY
  have hnt : commSub (W₁ ⊔ W₂) A ≠ ⊥ := fun h =>
    commSub_ne_bot_of_irr hLA h₁ (eq_bot_iff.2 (h ▸ commSub_mono le_sup_left le_rfl))
  obtain ⟨hmin, -⟩ := B1_5_2 hV hA hAY hnt
  have hY1 : Nat.card ↥(W₁ ⊔ W₂) ≤
      Nat.card ↥(autSub A (W₁ ⊔ W₂)) * Nat.card ↥(fixV (autSub A (W₁ ⊔ W₂))) := by
    have h := hmin.1.2.2.2 ⊥ bot_le
    have e : fixV (⊥ : Subgroup (MulAut ↥(W₁ ⊔ W₂))) = ⊤ := eq_top_iff.2 fun v _ x hx => by
      rw [Subgroup.mem_bot.1 hx]
      rfl
    rwa [Subgroup.card_bot, one_mul, e, Subgroup.card_top] at h
  have hK0 : A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L) ≤ A ⊓ centSub (W₁ ⊔ W₂) := by
    intro a ha
    obtain ⟨⟨haA, ha1⟩, ha2⟩ := ha
    refine ⟨haA, ?_⟩
    have e1 := sec_triv_imp_triv hL hAn h₁ hA₁ haA ha1.2
    have e2 := sec_triv_imp_triv hL hAn h₂ hA₂ haA ha2.2
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [map_mul, e1 x hx, e2 z hz]
  have hk' := Subgroup.card_le_of_le hK0
  have hA3 := card_autSub_mul hAst
  exact arith_ul_ff Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos hY1 hk' hA3
    (card_fixY_le (fixV L) hind hA₁ hA₂) (card_Y_eq (fixV L) hind) hGT


end TwoSections

theorem false_of_twist_ff {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A L : Subgroup (MulAut V)} (hA : IsFFStarMin X A)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (r : ↥L →* ↥(StatedSL 3 K)) (hr : Function.Surjective r)
    {W₁ : Subgroup V} (hW₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (e₁ : Sec W₁ (fixV L) ≃* StdMod (Fin 3) K)
    (he₁ : ∀ (hLW : L ≤ stabSub W₁) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W₁ (fixV L)),
      e₁ (B5.secHom L hLW hLU l s) = matAut ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) (e₁ s))
    (t : MulAut V) (ht : ∀ x ∈ L, t * x * t⁻¹ ∈ L) (ht' : ∀ x ∈ L, t⁻¹ * x * t ∈ L)
    (thb : MulAut (projectiveSL 3 K))
    (hthb : ∀ l l' : ↥L, (l' : MulAut V) = t * l * t⁻¹ →
      thb (proj 3 K ((slEquiv K).symm (r l))) = proj 3 K ((slEquiv K).symm (r l')))
    (hnot : ¬ TypePres thb) : False := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hLperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)) := mem_normalizer_of_forall_mem ht ht'
  set W₂ : Subgroup V := W₁.map (t⁻¹ : MulAut V).toMonoidHom with hW₂
  have hW₂irr : W₂ ∈ IrrPlus L (⊤ : Subgroup V) :=
    irrPlus_map (g := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht' x hx)
      (fun x hx => by rw [inv_inv]; exact ht x hx) hW₁
  have hmemW₂ : ∀ w, w ∈ W₂ ↔ t w ∈ W₁ := fun w => by
    rw [hW₂, mem_map_aut_iff, inv_inv]
  have hLW₁ : L ≤ stabSub W₁ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₁).1
  have hLW₂ : L ≤ stabSub W₂ := B1.le_stabSub_of_invariant (mem_irrPlus_top_iff.1 hW₂irr).1
  have hLU : L ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant (isInv_fixV L)
  have hA₁ := a_stab_irr hV hA hL hLA hW₁
  have hA₂ := a_stab_irr hV hA hL hLA hW₂irr
  have hAW₁ : A ≤ stabSub W₁ := B1.le_stabSub_of_invariant hA₁
  have hAW₂ : A ≤ stabSub W₂ := B1.le_stabSub_of_invariant hA₂
  have hAU : A ≤ stabSub (fixV L) := B1.le_stabSub_of_invariant fun a ha w hw =>
    mem_fixV_of_conj (fun x hx => by simpa using hAn a⁻¹ (A.inv_mem ha) x hx) hw
  let eT : ↥W₂ ≃* ↥W₁ :=
    { toFun := fun w => ⟨t (w : V), (hmemW₂ w).1 w.2⟩
      invFun := fun w => ⟨t⁻¹ (w : V), (hmemW₂ _).2 (by simp)⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hfixt : ∀ w ∈ fixV L, t w ∈ fixV L := fun w hw => mem_fixV_of_conj ht' hw
  have hfixt' : ∀ w ∈ fixV L, t⁻¹ w ∈ fixV L := fun w hw =>
    mem_fixV_of_conj (t := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht x hx) hw
  have hmapC : ((fixV L).subgroupOf W₂).map eT.toMonoidHom = (fixV L).subgroupOf W₁ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hfixt _ hx
    · intro hy
      exact ⟨eT.symm y, hfixt' _ hy, eT.apply_symm_apply y⟩
  let τ : Sec W₂ (fixV L) ≃* Sec W₁ (fixV L) := QuotientGroup.congr _ _ eT hmapC
  let c : MulAut ↥L := indAut L t
  have hc : ∀ l : ↥L, ((c l : ↥L) : MulAut V) = t * l * t⁻¹ := fun l => coe_indAut_apply htN l
  have hτ : ∀ (l : ↥L) (s : Sec W₂ (fixV L)),
      τ (B5.secHom L hLW₂ hLU l s) = B5.secHom L hLW₁ hLU (c l) (τ s) := by
    intro l s
    induction s using QuotientGroup.induction_on with
    | H w =>
      refine congrArg QuotientGroup.mk (Subtype.ext ?_)
      show t ((l : MulAut V) (w : V)) = ((c l : ↥L) : MulAut V) (t (w : V))
      rw [hc]
      simp [MulAut.mul_apply]
  let e₂₀ : Sec W₂ (fixV L) ≃* StdMod (Fin 3) K := τ.trans e₁
  have he₂₀ : ∀ (l : ↥L) (s : Sec W₂ (fixV L)),
      e₂₀ (B5.secHom L hLW₂ hLU l s) =
        matAut ((r (c l) : ↥(StatedSL 3 K)) : GL (Fin 3) K) (e₂₀ s) := by
    intro l s
    show e₁ (τ (B5.secHom L hLW₂ hLU l s)) = matAut _ (e₁ (τ s))
    rw [hτ]
    exact he₁ hLW₁ hLU (c l) (τ s)
  obtain ⟨e₂', he₂'⟩ := exists_dual_coord (K := K) (B5.secHom L hLW₂ hLU) r (r.comp c.toMonoidHom)
    thb (fun l => hthb l (c l) (hc l)) hnot e₂₀ he₂₀
  have hB : ¬ A ≤ centSec W₁ (fixV L) := by
    intro hle
    apply commSub_ne_bot_of_irr hLA hW₁
    rw [commSub_eq_bot_iff]
    intro w hw a ha
    exact sec_triv_imp_triv hL hAn hW₁ hA₁ ha (hle ha).2 w hw
  have hne : W₁ ≠ W₂ := ne_of_dual r hr hLW₁ hLW₂ hLU e₁ e₂' (he₁ hLW₁ hLU) he₂'
  have hGT := two_mul_card_le_of_dual hn hK hA.1.2.2.1 hAn hAW₁ hAW₂ hAU hLW₁ hLW₂ hLU r hr e₁ e₂'
    (he₁ hLW₁ hLU) he₂' hB
  exact false_of_two_sections_ff hV hA hL hLA hW₁ hW₂irr hne hGT

section NatData

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem n2_natural_data {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {n : ℕ}
    (hn : BinaryNaturalSL (autSec L W (W ⊓ fixV L)) ⊤ ⊥ 3 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ r : ↥L →* ↥(StatedSL 3 K), Function.Surjective r ∧
        ∃ e₁ : Sec W (fixV L) ≃* StdMod (Fin 3) K,
          ∀ (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub (fixV L)) (l : ↥L) (s : Sec W (fixV L)),
            e₁ (B5.secHom L hLW hLU l s) =
              matAut ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) (e₁ s) := by
  classical
  obtain ⟨K, hKf, hKfin, hK, π, hπ⟩ := hn
  obtain ⟨hinv, -, -, -⟩ := mem_irrPlus_top_iff.1 hW
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant hinv
  have hLZ : L ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hinv (isInv_fixV L))
  let σ := B5.secHom L hLW hLZ
  have hσ : ∀ l, σ l ∈ autSec L W (W ⊓ fixV L) := fun l => by
    have : σ l ∈ σ.range := ⟨l, rfl⟩
    rwa [B5.range_secHom] at this
  let ρ : ↥L →* ↥(autSec L W (W ⊓ fixV L)) := σ.codRestrict _ hσ
  have hρ : Function.Surjective ρ := by
    intro ψ
    have : (ψ : MulAut (Sec W (W ⊓ fixV L))) ∈ σ.range := by
      rw [B5.range_secHom]
      exact ψ.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  have hπinj : Function.Injective π := natRealizes_injective hπ
  let πe : ↥(StatedSL 3 K) ≃* ↥(autSec L W (W ⊓ fixV L)) := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_realizesVia (StatedSL 3 K) hπ
  let r : ↥L →* ↥(StatedSL 3 K) := πe.symm.toMonoidHom.comp ρ
  have hr : Function.Surjective r := πe.symm.surjective.comp hρ
  have hπr : ∀ l, π (r l) = ρ l := fun l => πe.apply_symm_apply (ρ l)
  have hsub : (W ⊓ fixV L).subgroupOf W = (fixV L).subgroupOf W := Subgroup.inf_subgroupOf_left _ _
  let E : Sec W (W ⊓ fixV L) ≃* Sec W (fixV L) := QuotientGroup.quotientMulEquivOfEq hsub
  refine ⟨K, hKf, hKfin, hK, r, hr, E.symm.trans e', fun hLW' hLU' l s => ?_⟩
  have hE : ∀ x, E (σ l x) = B5.secHom L hLW' hLU' l (E x) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H w => rfl
  have h1 : E.symm (B5.secHom L hLW' hLU' l s) = σ l (E.symm s) := by
    rw [MulEquiv.symm_apply_eq, hE, MulEquiv.apply_symm_apply]
  show e' (E.symm (B5.secHom L hLW' hLU' l s)) = matAut _ (e' (E.symm s))
  rw [h1]
  have h2 : σ l (E.symm s) = ((π (r l) : ↥(autSec L W (W ⊓ fixV L))) : MulAut _) (E.symm s) := by
    rw [hπr]
    rfl
  rw [h2]
  exact he' (r l) (E.symm s)

end NatData

theorem noRankTwoSL3_of {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X T M A L : Subgroup (MulAut V)} (hH : CompHyp X T M A L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hc : B42Case2 (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec L W (W ⊓ fixV L))) : False := by
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨-, ⟨n, hn⟩, -⟩ := hc
  obtain ⟨K, hKf, hKfin, hK, r, hr, e₁, he₁⟩ := n2_natural_data hW hn
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  have h2K : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLX : L ≤ X := hL.1
  have : Finite (MulAut V) := MulEquiv.finite_left
  let π₀ : ↥L →* projectiveSL 3 K := (proj 3 K).comp ((slEquiv K).symm.toMonoidHom.comp r)
  have hπ₀ : Function.Surjective π₀ :=
    (proj_surjective 3 K).comp ((slEquiv K).symm.surjective.comp hr)
  have : Nontrivial (projectiveSL 3 K) := nontrivial_projectiveSL_three h2K
  have hker₀ : π₀.ker = Subgroup.center ↥L :=
    ker_eq_center_of_surj hLq center_projectiveSL_three π₀ hπ₀
  have hLhat : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := isComponentOf_subgroupOf hL
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let πh : ↥(L.subgroupOf X) →* projectiveSL 3 K := π₀.comp e0.toMonoidHom
  have hπh : Function.Surjective πh := hπ₀.comp e0.surjective
  have hkerh : πh.ker = Subgroup.center ↥(L.subgroupOf X) :=
    ker_eq_center_of_surj hLhat.2.2 center_projectiveSL_three πh hπh
  obtain ⟨t, -, htN, hall⟩ := exists_swap swapGeo_sl3 (even_card_projectiveSL_three h2K)
    hmp.subgroupOf hLhat πh hπh hkerh
  have ht : ∀ x ∈ L, (t : MulAut V) * x * (t : MulAut V)⁻¹ ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp htN ⟨x, hLX hx⟩).mp hx'
    exact this
  have ht' : ∀ x ∈ L, (t : MulAut V)⁻¹ * x * (t : MulAut V) ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) ⟨x, hLX hx⟩).mp hx'
    exact this
  have htV : (t : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mem_normalizer_of_forall_mem ht ht'
  obtain ⟨thb, hthb⟩ := exists_aut_of_ker_eq π₀ hπ₀ (indAut L (t : MulAut V)) (by
    intro l
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker₀]
    exact mem_center_map_iff _ l)
  have hind : ∀ l l' : ↥L, (l' : MulAut V) = (t : MulAut V) * l * (t : MulAut V)⁻¹ →
      indAut L (t : MulAut V) l = l' := by
    intro l l' hl'
    apply Subtype.ext
    rw [coe_indAut_apply htV, hl']
  have hnot : ¬ TypePres thb := by
    refine hall thb fun l l' hl' => ?_
    have h1 : indAut L (t : MulAut V) (e0 l) = e0 l' := by
      apply hind
      show ((l' : ↥X) : MulAut V) = _
      rw [hl']
      rfl
    show thb (π₀ (e0 l)) = π₀ (e0 l')
    rw [hthb, h1]
  exact false_of_twist_ff hV hA hLq hLA hn1 hK r hr hW e₁ he₁ (t : MulAut V) ht ht' thb
    (fun l l' hl' => by
      have := hthb l
      rw [hind l l' hl'] at this
      exact this) hnot

end B69

end CFSG.Quasithin
