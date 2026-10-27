module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Step
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Strip
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sub
import CFSG.LocalAnalysis.UniquenessCase.UC22K148LemFP
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Split
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.RankThree.FFModules.FixSubConj
import CFSG.Quasithin.Background.G119Group2
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem card_mul_card_fixSub_le_cenOn [Finite V] {X : Subgroup G} {N W : Submodule (ZMod 2) V}
    (hNW : IsCompl N W) (hN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X N) (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X W) (hE : NoExcess ρ X N) :
    Nat.card X * Nat.card (fixSub ρ X) ≤
      Nat.card (cenOn ρ X N) * Nat.card (fixSub ρ (cenOn ρ X N)) := by
  have hX'X : cenOn ρ X N ≤ X := fun x hx => hx.1
  have hfixN : fixOn ρ (cenOn ρ X N) N = N :=
    inf_eq_left.2 fun n hn => mem_fixSub.2 fun x hx => hx.2 n hn
  have hcmono : Nat.card (fixOn ρ X W) ≤ Nat.card (fixOn ρ (cenOn ρ X N) W) := by
    rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank]
    exact Nat.pow_le_pow_right (by norm_num)
      (Submodule.finrank_mono (inf_le_inf_left W (fixSub_antitone hX'X)))
  have hE' : Nat.card X * Nat.card (fixOn ρ X N) ≤ Nat.card N * Nat.card (cenOn ρ X N) := hE
  rw [card_fixSub_eq_mul_of_isCompl hNW hN hW, card_fixSub_eq_mul_of_isCompl hNW
    (fun x hx => hN x (hX'X hx)) (fun x hx => hW x (hX'X hx)), hfixN]
  calc Nat.card X * (Nat.card (fixOn ρ X N) * Nat.card (fixOn ρ X W))
      = Nat.card X * Nat.card (fixOn ρ X N) * Nat.card (fixOn ρ X W) := (mul_assoc _ _ _).symm
    _ ≤ Nat.card N * Nat.card (cenOn ρ X N) * Nat.card (fixOn ρ (cenOn ρ X N) W) :=
        Nat.mul_le_mul hE' hcmono
    _ = Nat.card (cenOn ρ X N) * (Nat.card N * Nat.card (fixOn ρ (cenOn ρ X N) W)) := by ring

theorem card_mul_card_fixSub_le_card [Finite V] {ι : Type} (N W : ι → Submodule (ZMod 2) V)
    (J : Finset ι) :
    ∀ {X : Subgroup G},
      (∀ k ∈ J, IsCompl (N k) (W k) ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X (N k) ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X (W k) ∧
        ∀ Y ≤ X, NoExcess ρ Y (N k)) →
      (∀ x ∈ X, (∀ k ∈ J, ∀ n ∈ N k, ρ x n = n) → x = 1) →
      Nat.card X * Nat.card (fixSub ρ X) ≤ Nat.card V := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro X _ hX
    have hbot : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 fun x hx =>
      hX x hx fun k hk => absurd hk (Finset.notMem_empty k)
    rw [hbot, Subgroup.card_bot, fixSub_bot, one_mul, card_top_submodule]
  | @insert k J hk ih =>
    intro X hJ hX
    obtain ⟨hNW, hN, hW, hE⟩ := hJ k (Finset.mem_insert_self k J)
    have hX'X : cenOn ρ X (N k) ≤ X := fun x hx => hx.1
    refine (card_mul_card_fixSub_le_cenOn hNW hN hW (hE X le_rfl)).trans
      (ih (fun l hl => ?_) fun x hx hxN => hX x hx.1 fun l hl => ?_)
    · obtain ⟨h1, h2, h3, h4⟩ := hJ l (Finset.mem_insert_of_mem hl)
      exact ⟨h1, fun x hx => h2 x (hX'X hx), fun x hx => h3 x (hX'X hx),
        fun Y hY => h4 Y (hY.trans hX'X)⟩
    · rcases Finset.mem_insert.1 hl with rfl | hl
      · exact hx.2
      · exact hxN l hl

theorem map_subtype_sup_zpowers_le {K : Subgroup G} (hK : K.Normal) {a : G}
    {L : Subgroup ↥(K ⊔ Subgroup.zpowers a)} (hL : IsComponentOf L ⊤) :
    L.map (K ⊔ Subgroup.zpowers a).subtype ≤ K := by
  have hq := (CFSG.Open.IsQuasisimple.congr
    (L.equivMapOfInjective _ (K ⊔ Subgroup.zpowers a).subtype_injective)).1 hL.2.2
  haveI : Group.IsPerfect ↥(L.map (K ⊔ Subgroup.zpowers a).subtype) := ⟨hq.1⟩
  exact CFSG.Quasithin.G11.g119_le_of_perfect_of_sup_zpowers le_sup_left
    (fun g _ n hn => hK.conj_mem n hn g) rfl (Subgroup.map_subtype_le L) inferInstance

theorem isComponentOf_map_subtype_sup_zpowers {K : Subgroup G} (hK : K.Normal) {a : G}
    {L : Subgroup ↥(K ⊔ Subgroup.zpowers a)} (hL : IsComponentOf L ⊤) :
    IsComponentOf (L.map (K ⊔ Subgroup.zpowers a).subtype) ⊤ := by
  have h0 : CFSG.Open.IsSubnormal (L.map (K ⊔ Subgroup.zpowers a).subtype)
      (K ⊔ Subgroup.zpowers a) := by
    have h := hL.2.1.map (K ⊔ Subgroup.zpowers a).subtype
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have h1 := h0.inf_of_le (le_sup_left : K ≤ K ⊔ Subgroup.zpowers a)
  rw [inf_eq_left.2 (map_subtype_sup_zpowers_le hK hL)] at h1
  exact ⟨le_top, h1.trans (.step le_top (hK.subgroupOf ⊤) (.refl ⊤)),
    (CFSG.Open.IsQuasisimple.congr
      (L.equivMapOfInjective _ (K ⊔ Subgroup.zpowers a).subtype_injective)).1 hL.2.2⟩

theorem allowed_shape_sup_zpowers {K : Subgroup G} (hK : K.Normal) {a : G}
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    {L : Subgroup ↥(K ⊔ Subgroup.zpowers a)} (hL : IsComponentOf L ⊤) :
    (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))) :=
  RedAux.allowedShape_of_mulEquiv
    (L.equivMapOfInjective _ (K ⊔ Subgroup.zpowers a).subtype_injective)
    (hshape _ (isComponentOf_map_subtype_sup_zpowers hK hL))

theorem injective_subRep_sup_zpowers (hρ : Function.Injective ρ) {N : Subgroup G} (hN : N.Normal)
    (hW : ∀ g : G, ∀ w ∈ fixSub ρ N, ρ g w ∈ fixSub ρ N) (hcod : commOn ρ N ⊤ ⊔ fixSub ρ N = ⊤)
    {a : G} (ha2 : a * a = 1)
    (hO₀ : CFSG.pCore 2 ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊥) :
    Function.Injective (subRep (ρ.comp (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a).subtype)
      (fixSub ρ N) fun g w hw => hW g w hw) := by
  set K := cenOn ρ ⊤ (commOn ρ N ⊤)
  set K₀ := K ⊔ Subgroup.zpowers a
  have hK : K.Normal := cenOn_commOn_normal hN
  have hsq : ∀ c ∈ K₀, (∀ w ∈ fixSub ρ N, ρ c w = w) → c * c = 1 := fun c hc hcE => by
    have hcK : c * c ∈ K := by
      rcases CFSG.Quasithin.G11.g119_mem_or_mul_mem_of_sup_zpowers ha2
        (fun k hk => hK.conj_mem k hk a) hc with h | h
      · exact K.mul_mem h h
      · have e : c * c = c * a * (a * (c * a) * a⁻¹) := by
          calc c * c = c * (a * a) * c := by rw [ha2, mul_one]
            _ = c * a * (a * (c * a) * a⁻¹) := by group
        rw [e]
        exact K.mul_mem h (hK.conj_mem _ h a)
    refine hρ (LinearMap.ext fun v => ?_)
    have hv : v ∈ commOn ρ N ⊤ ⊔ fixSub ρ N := by
      rw [hcod]
      exact Submodule.mem_top
    obtain ⟨x, hx, e, he, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_one, Module.End.one_apply, map_add, hcK.2 x hx, glRep_mul_apply, hcE e he, hcE e he]
  have hCn : (cenOn ρ ⊤ (fixSub ρ N)).Normal := ⟨fun k hk g => ⟨Subgroup.mem_top _, fun x hx => by
    rw [glRep_mul_apply, glRep_mul_apply, hk.2 _ (hW g⁻¹ x hx), glRep_apply_inv]⟩⟩
  set C := (cenOn ρ ⊤ (fixSub ρ N)).comap K₀.subtype
  have hp : IsPGroup 2 ↥C := fun c => ⟨1, Subtype.ext (Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow, pow_two, Subgroup.coe_one, Subgroup.coe_one]
    exact hsq _ c.1.2 c.2.2))⟩
  have hle : C ≤ CFSG.pCore 2 ↥K₀ :=
    le_sSup (s := {M : Subgroup ↥K₀ | M.Normal ∧ IsPGroup 2 M}) ⟨hCn.comap _, hp⟩
  rw [hO₀, le_bot_iff] at hle
  refine (injective_subRep_iff _).2 fun g hg => ?_
  have hgC : g ∈ C := ⟨Subgroup.mem_top _, hg⟩
  rw [hle] at hgC
  exact (Subgroup.mem_bot).1 hgC

theorem hP_subRep_sup_zpowers_eq_top [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hH : hP ρ = ⊤) {N : Subgroup G} {a : G} (hN : N.Normal)
    (hW : ∀ g : G, ∀ w ∈ fixSub ρ N, ρ g w ∈ fixSub ρ N) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x) :
    hP (subRep (ρ.comp (cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a).subtype)
      (fixSub ρ N) fun g w hw => hW g w hw) = ⊤ :=
  hP_subRep_comp_subtype_eq_top hρ hH hN (inf_sup_zpowers_eq_bot hN ha2 hfa hout)
    (sup_sup_zpowers_eq_top hact) hW fun n hn w hw => mem_fixSub.1 hw n hn

theorem hasFactors148_sup_zpowers [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hshape : ∀ L : Subgroup G, IsComponentOf L ⊤ →
      (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))))
    (hH : hP ρ = ⊤) (IH : HasFactors148Below (Nat.card G)) {N : Subgroup G} {a : G}
    (hN : N.Normal) (hN1 : N ≠ ⊥) (hcod : commOn ρ N ⊤ ⊔ fixSub ρ N = ⊤) (ha2 : a * a = 1)
    (hfa : ∀ n ∈ N, (∀ x ∈ commOn ρ N ⊤, ρ n x = x) → n = 1)
    (hact : ∀ g : G, ∃ h ∈ N ⊔ Subgroup.zpowers a, ∀ x ∈ commOn ρ N ⊤, ρ g x = ρ h x)
    (hout : ∀ n ∈ N, ¬ ∀ x ∈ commOn ρ N ⊤, ρ a x = ρ n x)
    (hO₀ : CFSG.pCore 2 ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) = ⊥) :
    HasFactors148 ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) := by
  have hNK := inf_sup_zpowers_eq_bot hN ha2 hfa hout
  have hlt : cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hN1 (by rw [← inf_top_eq N, ← h, hNK])
  have hcard : Nat.card ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) < Nat.card G := by
    have h := Subgroup.card_lt_of_lt hlt
    rwa [Subgroup.card_top] at h
  have hW : ∀ g : G, ∀ w ∈ fixSub ρ N, ρ g w ∈ fixSub ρ N := fun g w hw =>
    rep_apply_mem_fixSub_of_normal ρ hN g hw
  exact IH ↥(cenOn ρ ⊤ (commOn ρ N ⊤) ⊔ Subgroup.zpowers a) ↥(fixSub ρ N) _ hcard hO₀
    (injective_subRep_sup_zpowers hρ hN hW hcod ha2 hO₀)
    (fun L hL => allowed_shape_sup_zpowers (cenOn_commOn_normal hN) hshape hL)
    (hP_subRep_sup_zpowers_eq_top hρ hH hN hW ha2 hfa hact hout)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
