module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.QuasithinUnique (IsComponentIn)
open CFSG.QuasithinUnique.Setup.Offender (weight commGL fixGL)
open scoped commutatorElement

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem card_le_weight_imgGL [Finite G] {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hbest : IsBestOffenderOn ρ B (commOn ρ K ⊤)) :
    Nat.card ↥(commOn ρ K ⊤) ≤ weight (MonoidHom.id (↥(commOn ρ K ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ K ⊤)))
      (imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv B) := by
  have hBH : B ≤ K ⊔ B := le_sup_right
  have hcpos : 0 < Nat.card (cenOn ρ B (commOn ρ K ⊤)) := Nat.card_pos
  rw [weight_imgGL hBH]
  have h1 := hbest.isOffenderOn.2
  rw [← card_imgGL_mul_card_cenOn (hU := hinv) hBH, mul_assoc,
    mul_comm (Nat.card (cenOn ρ B (commOn ρ K ⊤))), ← mul_assoc] at h1
  exact Nat.le_of_mul_le_mul_right h1 hcpos

theorem weight_lt_weight_imgGL [Finite G] {K B : Subgroup G}
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hstrict : ∀ B' : Subgroup G, cenOn ρ B (commOn ρ K ⊤) ≤ B' → B' < B →
      ¬ B' ≤ cenOn ρ B (commOn ρ K ⊤) →
        Nat.card B' * Nat.card (fixOn ρ B' (commOn ρ K ⊤)) <
          Nat.card B * Nat.card (fixOn ρ B (commOn ρ K ⊤)))
    (B₂ : Subgroup (↥(commOn ρ K ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ K ⊤))) (hbot : ⊥ < B₂)
    (hlt : B₂ < imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv B) :
    weight (MonoidHom.id (↥(commOn ρ K ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ K ⊤))) B₂ <
      weight (MonoidHom.id (↥(commOn ρ K ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ K ⊤)))
        (imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv B) := by
  set U := commOn ρ K ⊤ with hU
  set H := K ⊔ B with hH
  have hBH : B ≤ H := le_sup_right
  obtain ⟨B', hB'B, hcB', hB'⟩ := exists_imgGL_eq (hU := hinv) hBH hlt.le
  have hB'H : B' ≤ H := hB'B.trans hBH
  have hne : B' ≠ B := by
    rintro rfl
    exact hlt.ne hB'.symm
  have hnc : ¬ B' ≤ cenOn ρ B U := by
    intro h
    have : imgGL ρ H U hinv B' = ⊥ := (imgGL_eq_bot_iff hB'H).2 fun b hb => ⟨hb, (h hb).2⟩
    rw [hB'] at this
    exact hbot.ne' this
  have key := hstrict B' hcB' (lt_of_le_of_ne hB'B hne) hnc
  have hc : cenOn ρ B' U = cenOn ρ B U := by
    rw [cenOn_eq_inf_of_le hB'B]
    exact inf_eq_right.2 hcB'
  have h1 := card_imgGL_mul_card_cenOn (hU := hinv) hB'H
  have h2 := card_imgGL_mul_card_cenOn (hU := hinv) hBH
  rw [hc] at h1
  rw [← h1, ← h2] at key
  have key' : Nat.card (imgGL ρ H U hinv B') * Nat.card (fixOn ρ B' U) <
      Nat.card (imgGL ρ H U hinv B) * Nat.card (fixOn ρ B U) := by
    have : Nat.card (cenOn ρ B U) * (Nat.card (imgGL ρ H U hinv B') * Nat.card (fixOn ρ B' U)) <
        Nat.card (cenOn ρ B U) * (Nat.card (imgGL ρ H U hinv B) * Nat.card (fixOn ρ B U)) := by
      calc _ = Nat.card (imgGL ρ H U hinv B') * Nat.card (cenOn ρ B U) *
            Nat.card (fixOn ρ B' U) := by ring
        _ < Nat.card (imgGL ρ H U hinv B) * Nat.card (cenOn ρ B U) *
            Nat.card (fixOn ρ B U) := key
        _ = _ := by ring
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
  have e1 := weight_imgGL (hU := hinv) hB'H
  rw [hB'] at e1
  rw [e1, weight_imgGL hBH, ← hB']
  exact key'

theorem eq_one_of_forall_commute_imgGL {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B (commOn ρ K ⊤) →
      ∃ k ∈ K, ∃ u ∈ commOn ρ K ⊤, ρ b (ρ k u) ≠ ρ k (ρ b u))
    {x : ↥(commOn ρ K ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ K ⊤)} (hx : x ∈ imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv B)
    (hc : ∀ y ∈ imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv K, x * y = y * x) : x = 1 := by
  obtain ⟨b, hbB, rfl⟩ := mem_imgGL.1 hx
  rw [resGL_eq_one_iff]
  by_contra hne
  obtain ⟨k, hk, u, hu, hku⟩ := hmove b hbB fun h => hne h.2
  have h2 := hc _ (resGL_mem_imgGL (hU := hinv) hk (le_sup_left (a := K) hk))
  exact hku (congrArg (fun f : ↥(commOn ρ K ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ K ⊤) =>
    ((f ⟨u, hu⟩ : ↥(commOn ρ K ⊤)) : V)) h2)

theorem imgGL_ne_bot {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hBU : ¬ B ≤ cenOn ρ B (commOn ρ K ⊤)) : imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv B ≠ ⊥ :=
  fun h => hBU ((imgGL_eq_bot_iff (le_sup_right : B ≤ K ⊔ B)).1 h)

theorem commutator_imgGL_ne_bot {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hBU : ¬ B ≤ cenOn ρ B (commOn ρ K ⊤))
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B (commOn ρ K ⊤) →
      ∃ k ∈ K, ∃ u ∈ commOn ρ K ⊤, ρ b (ρ k u) ≠ ρ k (ρ b u)) :
    ⁅imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv K, imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv B⁆ ≠ ⊥ := by
  intro h
  refine imgGL_ne_bot hinv hBU (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 ?_)
  refine eq_one_of_forall_commute_imgGL hinv hmove hx fun y hy => ?_
  have hm := Subgroup.commutator_mem_commutator hy hx
  rw [h, Subgroup.mem_bot] at hm
  exact (commutatorElement_eq_one_iff_mul_comm.1 hm).symm

theorem range_resGL_comp_inclusion {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤)) :
    ((resGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ B))).range =
      imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv K := by
  ext x
  rw [MonoidHom.mem_range, mem_imgGL]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, le_sup_left (a := K) k.2⟩, k.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem injective_resGL_comp_inclusion {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hKs : IsSimpleGroup ↥K) (hKU : ¬ K ≤ cenOn ρ K (commOn ρ K ⊤)) :
    Function.Injective
      ((resGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ B))) := by
  haveI := hKs
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((resGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ B))).ker
    with h | h
  · exact h
  · refine absurd (fun k hk => ?_) hKU
    have hmem : (⟨k, hk⟩ : ↥K) ∈
        ((resGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ B))).ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact ⟨hk, (resGL_eq_one_iff (hU := hinv) (⟨k, le_sup_left (a := K) hk⟩ : ↥(K ⊔ B))).1
      (MonoidHom.mem_ker.1 hmem)⟩

theorem exists_mulEquiv_imgGL {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hKs : IsSimpleGroup ↥K) (hKU : ¬ K ≤ cenOn ρ K (commOn ρ K ⊤)) :
    ∃ e : ↥K ≃* ↥(imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv K), ∀ k : ↥K,
      (e k : ↥(commOn ρ K ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ K ⊤)) =
        resGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv ⟨k, le_sup_left (a := K) k.2⟩ :=
  ⟨(MonoidHom.ofInjective (injective_resGL_comp_inclusion hinv hKs hKU)).trans
    (MulEquiv.subgroupCongr (range_resGL_comp_inclusion hinv)), fun _ => rfl⟩

theorem isComponentIn_imgGL {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hK : IsComponentOf K ⊤) (hKs : IsSimpleGroup ↥K) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hKU : ¬ K ≤ cenOn ρ K (commOn ρ K ⊤)) :
    IsComponentIn (imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv K)
      (imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv (K ⊔ B)) := by
  have hle := imgGL_mono (hU := hinv) (le_sup_left : K ≤ K ⊔ B)
  have hHN : K ⊔ B ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hBN
  obtain ⟨e, -⟩ := exists_mulEquiv_imgGL hinv hKs hKU
  refine ⟨hle, (CFSG.IsQuasisimple.congr (e.trans (Subgroup.subgroupOfEquivOfLe hle).symm)).1
    (ExcAux.isQuasisimple_of_isComponentOf hK), ?_⟩
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (imgGL_le_normalizer hHN)).isSubnormal

theorem center_imgGL_eq_bot {K B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hK : IsComponentOf K ⊤) (hKs : IsSimpleGroup ↥K) (hKU : ¬ K ≤ cenOn ρ K (commOn ρ K ⊤)) :
    Subgroup.center ↥(imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv K) = ⊥ := by
  obtain ⟨e, -⟩ := exists_mulEquiv_imgGL hinv hKs hKU
  haveI := hKs
  haveI : IsSimpleGroup ↥(imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv K) := e.symm.isSimpleGroup
  exact ExcAux.center_eq_bot ((CFSG.IsQuasisimple.congr e).1 (ExcAux.isQuasisimple_of_isComponentOf hK))

theorem map_commGL_imgGL {K B X : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hX : X ≤ K ⊔ B) :
    (commGL (imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv X) ⊤).map (commOn ρ K ⊤).subtype =
      commOn ρ X (commOn ρ K ⊤) := by
  simp only [commGL, CFSG.QuasithinUnique.Setup.Offender.commSub]
  rw [Submodule.map_span]
  show _ = Submodule.span (ZMod 2) {w | ∃ a ∈ X, ∃ u ∈ commOn ρ K ⊤, w = ρ a u - u}
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨m, hm, u, -, rfl⟩, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := mem_imgGL.1 hm
    exact ⟨x, hxX, u, u.2, rfl⟩
  · rintro ⟨x, hxX, u, hu, rfl⟩
    exact ⟨_, ⟨resGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv ⟨x, hX hxX⟩, resGL_mem_imgGL hxX (hX hxX), ⟨u, hu⟩,
      Submodule.mem_top, rfl⟩, rfl⟩

theorem commGL_imgGL_eq_top {K B X : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤))
    (hX : X ≤ K ⊔ B) (h : commOn ρ X (commOn ρ K ⊤) = commOn ρ K ⊤) :
    commGL (imgGL ρ (K ⊔ B) (commOn ρ K ⊤) hinv X) ⊤ = ⊤ := by
  apply Submodule.map_injective_of_injective (commOn ρ K ⊤).injective_subtype
  rw [map_commGL_imgGL hinv hX, h, Submodule.map_subtype_top]

structure TransportGL (ρ : Representation (ZMod 2) G V) (L B : Subgroup G)
    (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)) : Prop where
  comp : IsComponentIn (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L)
    (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv (L ⊔ B))
  iso : ∃ e : ↥L ≃* ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L), ∀ l : ↥L,
    (e l : ↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)) =
      resGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv ⟨l, le_sup_left (a := L) l.2⟩
  center : Subgroup.center ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) = ⊥
  le : imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B ≤ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv (L ⊔ B)
  elem : CFSG.IsElementaryAbelian 2 ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B)
  ne_bot : imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B ≠ ⊥
  off : Nat.card ↥(commOn ρ L ⊤) ≤ weight (MonoidHom.id (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)))
    (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B)
  strict : ∀ B₂ : Subgroup (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)), ⊥ < B₂ →
    B₂ < imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B →
      weight (MonoidHom.id (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤))) B₂ <
        weight (MonoidHom.id (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)))
          (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B)
  comm : ⁅imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L, imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B⁆ ≠ ⊥
  cen : ∀ x ∈ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B,
    (∀ y ∈ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L, x * y = y * x) → x = 1
  commU : commGL (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) ⊤ = ⊤

theorem transportGL_of [Finite G] {L B : Subgroup G} (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤))
    (hL : IsComponentOf L ⊤) (hLs : IsSimpleGroup ↥L) (hBe : CFSG.IsElementaryAbelian 2 ↥B)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hLU : ¬ L ≤ cenOn ρ L (commOn ρ L ⊤))
    (hBU : ¬ B ≤ cenOn ρ B (commOn ρ L ⊤)) (hbest : IsBestOffenderOn ρ B (commOn ρ L ⊤))
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B (commOn ρ L ⊤) →
      ∃ k ∈ L, ∃ u ∈ commOn ρ L ⊤, ρ b (ρ k u) ≠ ρ k (ρ b u))
    (hstrict : ∀ B' : Subgroup G, cenOn ρ B (commOn ρ L ⊤) ≤ B' → B' < B →
      ¬ B' ≤ cenOn ρ B (commOn ρ L ⊤) →
        Nat.card B' * Nat.card (fixOn ρ B' (commOn ρ L ⊤)) <
          Nat.card B * Nat.card (fixOn ρ B (commOn ρ L ⊤)))
    (hUL : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤) : TransportGL ρ L B hinv where
  comp := isComponentIn_imgGL hinv hL hLs hBN hLU
  iso := exists_mulEquiv_imgGL hinv hLs hLU
  center := center_imgGL_eq_bot hinv hL hLs hLU
  le := imgGL_mono le_sup_right
  elem := isElementaryAbelian_imgGL le_sup_right hBe le_rfl
  ne_bot := imgGL_ne_bot hinv hBU
  off := card_le_weight_imgGL hinv hbest
  strict := weight_lt_weight_imgGL hinv hstrict
  comm := commutator_imgGL_ne_bot hinv hBU hmove
  cen _ hx hc := eq_one_of_forall_commute_imgGL hinv hmove hx hc
  commU := commGL_imgGL_eq_top hinv le_sup_left hUL

theorem exists_transportGL [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G}
    (hL : IsComponentOf L ⊤) (hLs : IsSimpleGroup ↥L) {A : Subgroup G} (hA : A ∈ calP ρ)
    (hLA : ⁅L, A⁆ ≠ ⊥) :
    ∃ (B : Subgroup G) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤)),
      B ≤ A ∧ IsBestOffenderOn ρ B (commOn ρ L ⊤) ∧ IsQuadraticOn ρ B (commOn ρ L ⊤) ∧
      ¬ B ≤ cenOn ρ B (commOn ρ L ⊤) ∧
      (∀ b ∈ B, b ∉ cenOn ρ B (commOn ρ L ⊤) →
        ∃ k ∈ L, ∃ u ∈ commOn ρ L ⊤, ρ b (ρ k u) ≠ ρ k (ρ b u)) ∧
      TransportGL ρ L B hinv := by
  classical
  have hAN := le_normalizer_of_mem_calP hρ hL hA
  have hLA' := commutator_eq_self_of_mem_calP hρ hL hA hLA
  have hAe := isElementaryAbelian_of_mem_calP hA
  have hbest := isBestOffenderOn_of_mem_calP hρ hA
  haveI := hLs
  have hLnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro hle
    have hL1 : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply hρ
      ext w
      simp [(hle hl).2 w Submodule.mem_top]
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance hL1
  obtain ⟨B, hBA, hinv, hLU, hBU, hBbest, hquad, hmov, hstrict⟩ :=
    exists_strictMin_moving L A hAe hAN hLA' hLnt hbest
  exact ⟨B, hinv, hBA, hBbest, hquad, hBU, hmov,
    transportGL_of hinv hL hLs (CFSG.IsElementaryAbelian.of_le hAe hBA) (hBA.trans hAN) hLU hBU hBbest hmov
      hstrict (commOn_commOn_eq hAe hAN hLA')⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
