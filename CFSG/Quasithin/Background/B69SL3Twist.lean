module

public import CFSG.Quasithin.Background.B69Cnt
public import CFSG.Quasithin.Background.B69Dual
public import CFSG.Quasithin.Background.B69Theta
public import CFSG.Quasithin.Background.B69Par
public import CFSG.Quasithin.Background.B69SL3Aux
public import CFSG.Quasithin.Background.B6Aut

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.SL3Pair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open B6

namespace B69

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem ne_of_dual {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K] [Finite K]
    (r : ↥L →* ↥(StatedSL 3 K)) (hr : Function.Surjective r) {W₁ W₂ U : Subgroup V}
    (hLW₁ : L ≤ stabSub W₁) (hLW₂ : L ≤ stabSub W₂) (hLU : L ≤ stabSub U)
    (e₁ : Sec W₁ U ≃* StdMod (Fin 3) K) (e₂ : Sec W₂ U ≃* StdMod (Fin 3) K)
    (he₁ : ∀ (l : ↥L) (s : Sec W₁ U), e₁ (B5.secHom L hLW₁ hLU l s) =
      matAut ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) (e₁ s))
    (he₂ : ∀ (l : ↥L) (s : Sec W₂ U), e₂ (B5.secHom L hLW₂ hLU l s) =
      matAut (dualGL ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K)) (e₂ s)) : W₁ ≠ W₂ := by
  rintro rfl
  refine not_exists_dual_iso (e₁.symm.trans e₂) fun g hg x => ?_
  obtain ⟨l, hl⟩ := hr ⟨g, hg⟩
  have hlg : ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) = g := congrArg Subtype.val hl
  have h1 : e₁.symm (matAut g x) = B5.secHom L hLW₁ hLU l (e₁.symm x) := by
    rw [MulEquiv.symm_apply_eq, he₁, MulEquiv.apply_symm_apply, hlg]
  show e₂ (e₁.symm (matAut g x)) = matAut (dualGL g) (e₂ (e₁.symm x))
  rw [h1, he₂, hlg]

omit [CommGroup V] in
theorem false_of_twist {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X A L : Subgroup (MulAut V)} (hA : IsFFStarMin X A) (hAs : rAV A < 1)
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
  exact false_of_two_sections hV hA hAs hL hLA hW₁ hW₂irr hne hGT

end B69

end CFSG.Quasithin
