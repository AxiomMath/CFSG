module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Emb

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45 L0S B0 P1 P2 xY x45 x45_mul_self repL_x xY_ne_one)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45)
open scoped Pointwise

@[expose] def gTA (k : ℕ) : Ah := incl (U42.gTY k)

@[expose] def Thl : List PL := Tl ++ Tl.map fun t => comp t fhatL

@[expose] def That : Subgroup Ah :=
  Subgroup.closure (Set.range (fun k : Fin 5 => gTA k) ∪ {fhatA})

theorem Thl_check : idL ∈ Thl ∧ (∀ l ∈ Thl, ∀ k < 5, comp l (gTL k) ∈ Thl) ∧
    (∀ l ∈ Thl, comp l fhatL ∈ Thl) := by
  decide +kernel

theorem Thl_center : ∀ l ∈ Thl, (∀ k < 5, comp l (gTL k) = comp (gTL k) l) →
    comp l fhatL = comp fhatL l → l = idL ∨ l = xL := by
  decide +kernel

theorem repL_gTA (k : ℕ) :
    RepL (gTL k) ((gTA k : Ah) : P45) := U42.repL_gTY k

theorem gTA_mem_That {k : ℕ} (hk : k < 5) : gTA k ∈ That :=
  Subgroup.subset_closure (Or.inl ⟨⟨k, hk⟩, rfl⟩)

theorem fhatA_mem_That : fhatA ∈ That := Subgroup.subset_closure (Or.inr rfl)

theorem map_T_le_That : (U42.T).map incl ≤ That := by
  rw [U42.T, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact gTA_mem_That k.2

theorem exists_T_of_mem_Tl {t : PL} (ht : t ∈ Tl) :
    ∃ g : Y, g ∈ U42.T ∧ RepL t (g : P45) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
  have hi64 : i < 64 := by have := U42.chkT_spec.1; omega
  obtain ⟨g, hg, hrep⟩ := U42.exists_Tel hi64
  exact ⟨g, hg, by rwa [List.getD_eq_getElem _ _ hi] at hrep⟩

theorem exists_That_of_mem_Thl {l : PL} (hl : l ∈ Thl) :
    ∃ g ∈ That, RepL l (g : P45) := by
  rcases List.mem_append.1 hl with h | h
  · obtain ⟨g, hg, hrep⟩ := exists_T_of_mem_Tl h
    exact ⟨incl g, map_T_le_That (Subgroup.mem_map_of_mem _ hg), hrep⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    obtain ⟨g, hg, hrep⟩ := exists_T_of_mem_Tl ht
    exact ⟨incl g * fhatA, That.mul_mem (map_T_le_That (Subgroup.mem_map_of_mem _ hg))
      fhatA_mem_That, repL_mul hrep repL_fhat⟩

theorem mem_That_iff (g : Ah) :
    g ∈ That ↔ ∃ l ∈ Thl, RepL l (g : P45) := by
  constructor
  · intro hg
    have key : ((That : Subgroup Ah) : Set Ah) ⊆ {g : Ah | ∃ l ∈ Thl, RepL l (g : P45)} := by
      refine closure_subset_of_right_closed
        (S := Set.range (fun k : Fin 5 => gTA k) ∪ {fhatA}) ?_ ?_ ?_
      · intro s _
        obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
        exact ⟨n, hn, h⟩
      · exact ⟨idL, Thl_check.1, repL_one 45⟩
      · rintro p ⟨l, hl, hp⟩ s (⟨k, rfl⟩ | rfl)
        · exact ⟨comp l (gTL k), Thl_check.2.1 l hl k k.2, repL_mul hp (repL_gTA k)⟩
        · exact ⟨comp l fhatL, Thl_check.2.2 l hl, repL_mul hp repL_fhat⟩
    exact key hg
  · rintro ⟨l, hl, hrep⟩
    obtain ⟨g', hg', hrep'⟩ := exists_That_of_mem_Thl hl
    have : g = g' := Subtype.ext (eq_of_repL hrep hrep')
    rwa [this]

theorem comap_That :
    That.comap incl = U42.T := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => map_T_le_That (Subgroup.mem_map_of_mem _ hy))
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff _).1 hy
  rcases List.mem_append.1 hl with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
    rw [U42.mem_T_iff]
    exact ⟨i, by have := U42.chkT_spec.1; omega, by
      rwa [List.getD_eq_getElem _ _ hi]⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    obtain ⟨g, hg, hgrep⟩ := exists_T_of_mem_Tl ht
    exfalso
    have heq : incl y = incl g * fhatA := Subtype.ext (eq_of_repL hrep (repL_mul hgrep repL_fhat))
    have h1 := signA_incl y
    rw [heq, map_mul, signA_incl, signA_fhatA] at h1
    exact absurd h1 (by decide)

theorem card_That :
    Nat.card That = 128 := by
  rw [card_eq_two_mul fhatA_mem_That, comap_That, U42.card_T]

theorem That_le_Bh : That ≤ Bh := by
  rw [That, Subgroup.closure_le]
  rintro _ (⟨k, rfl⟩ | rfl)
  · have : U42.gTY k ∈ B0 := U42.gTY_mem_B0 k k.2
    rw [← comap_Bh] at this
    exact this
  · exact fhatA_mem_Bh

theorem isSylowTwoOf_That_Bh :
    CFSG.QuasithinUnique.IsSylowTwoOf That Bh := by
  refine ⟨That_le_Bh, IsPGroup.of_card (n := 7) (by rw [card_That]; norm_num), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := That) (K := Bh)
  rw [inf_eq_left.2 That_le_Bh, card_That, card_Bh] at h
  show ¬ 2 ∣ That.relIndex Bh
  omega

theorem isSylowTwoOf_That_top :
    CFSG.QuasithinUnique.IsSylowTwoOf That ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 7) (by rw [card_That]; norm_num), ?_⟩
  show ¬ 2 ∣ That.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.index_mul_card (H := That)
  rw [card_That, card_A] at h
  generalize That.index = n at h ⊢
  omega

@[expose] def xA : Ah := incl xY

theorem xA_coe : (xA : P45) = x45 := rfl

theorem xA_sq : xA * xA = 1 := Subtype.ext (by
  rw [Subgroup.coe_mul, xA_coe]
  exact x45_mul_self)

theorem xA_ne_one : xA ≠ 1 := fun h => xY_ne_one (incl_injective (h.trans (map_one incl).symm))

theorem xA_mem_That : xA ∈ That :=
  map_T_le_That (Subgroup.mem_map_of_mem _ U42.xY_mem_T)

theorem center_That {w : Ah} (hw : w ∈ That)
    (hc : ∀ t ∈ That, w * t = t * w) : w = 1 ∨ w = xA := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff w).1 hw
  have hcomm : ∀ (s : Ah) (sL : PL), s ∈ That → RepL sL (s : P45) → comp l sL = comp sL l := by
    intro s sL hs hsrep
    have h1 : (w : P45) * (s : P45) = (s : P45) * (w : P45) := congrArg Subtype.val (hc s hs)
    exact repL_unique (repL_mul hrep hsrep) (h1 ▸ repL_mul hsrep hrep)
  rcases Thl_center l hl (fun k hk => hcomm (gTA k) (gTL k) (gTA_mem_That hk) (repL_gTA k))
      (hcomm fhatA fhatL fhatA_mem_That repL_fhat) with h | h
  · left
    exact Subtype.ext (eq_of_repL hrep (h ▸ repL_one 45))
  · right
    exact Subtype.ext (eq_of_repL hrep (h ▸ repL_x))

theorem central_invol_Bh {g : Ah}
    (hg : g ∈ Bh) (hc : ∀ b ∈ Bh, b * g = g * b) (hg2 : g * g = 1) (hg1 : g ≠ 1) : g = xA := by
  have hgT : g ∈ That := mem_of_central_of_isSylowTwoOf isSylowTwoOf_That_Bh hg hc hg2
  rcases center_That hgT (fun t ht => (hc t (That_le_Bh ht)).symm) with h | h
  · exact absurd h hg1
  · exact h

end CFSG.Quasithin.H13.F431.U42Aut
