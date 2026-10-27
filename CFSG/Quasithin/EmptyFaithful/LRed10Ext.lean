module

public import CFSG.Quasithin.EmptyFaithful.LRed10Blk

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.Quasithin.Ch3n317A5

namespace LRed10

section Aux

variable {W : Type*} [CommGroup W]

theorem iSup_eq_of_mem_single {α : Type*} [CompleteLattice α] (f : Subgroup (MulAut W) → α)
    {I : Finset (Subgroup (MulAut W))} {L₁ : Subgroup (MulAut W)}
    (hI : ∀ L, L ∈ I ↔ L = L₁) : ⨆ L ∈ I, f L = f L₁ :=
  le_antisymm (iSup₂_le fun L hL => ((hI L).1 hL) ▸ le_rfl)
    (le_iSup₂_of_le L₁ ((hI L₁).2 rfl) le_rfl)

theorem iSup_eq_of_mem_pair {α : Type*} [CompleteLattice α] (f : Subgroup (MulAut W) → α)
    {I : Finset (Subgroup (MulAut W))} {L₁ L₂ : Subgroup (MulAut W)}
    (hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂) : ⨆ L ∈ I, f L = f L₁ ⊔ f L₂ := by
  refine le_antisymm (iSup₂_le fun L hL => ?_)
    (sup_le (le_iSup₂_of_le L₁ ((hI L₁).2 (Or.inl rfl)) le_rfl)
      (le_iSup₂_of_le L₂ ((hI L₂).2 (Or.inr rfl)) le_rfl))
  rcases (hI L).1 hL with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem iSup_ne_of_mem_pair {α : Type*} [CompleteLattice α] (f : Subgroup (MulAut W) → α)
    {I : Finset (Subgroup (MulAut W))} {L₁ L₂ : Subgroup (MulAut W)} (hne : L₁ ≠ L₂)
    (hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂) : ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₁), f L' = f L₂ := by
  refine le_antisymm (iSup₂_le fun L hL => iSup_le fun hLne => ?_)
    (le_iSup₂_of_le L₂ ((hI L₂).2 (Or.inr rfl)) (le_iSup_of_le hne.symm le_rfl))
  rcases (hI L).1 hL with rfl | rfl
  · exact absurd rfl hLne
  · exact le_rfl

theorem map_conj_mul_of_commute {P : Subgroup (MulAut W)} {g₁ g₂ : MulAut W}
    (h : ∀ y ∈ P, y * g₂ = g₂ * y) :
    P.map (MulAut.conj (g₁ * g₂)).toMonoidHom = P.map (MulAut.conj g₁).toMonoidHom := by
  have e : ∀ y ∈ P, (MulAut.conj (g₁ * g₂)).toMonoidHom y = (MulAut.conj g₁).toMonoidHom y := by
    intro y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    calc g₁ * g₂ * y * (g₂⁻¹ * g₁⁻¹) = g₁ * (g₂ * y) * g₂⁻¹ * g₁⁻¹ := by group
      _ = g₁ * (y * g₂) * g₂⁻¹ * g₁⁻¹ := by rw [h y hy]
      _ = g₁ * y * g₁⁻¹ := by group
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (e y hy).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, e y hy⟩

end Aux

section Ext

variable {W : Type*} [CommGroup W] [Finite W]

theorem a5_bundle {Kst Jst Tst : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}
    (hcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hsup : fixV Kst ⊔ ⨆ L ∈ I, commV L = ⊤)
    (hinf : ∀ L ∈ I, commV L ⊓ (fixV Kst ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤ fixV Kst)
    (hA5 : ∀ L ∈ I, E2.IsA5Module L)
    (hJdec : Jst = ⨆ L ∈ I, (L ⊓ Jst))
    (hL4 : ∀ L ∈ I, Nat.card ↥(L ⊓ Jst) = 4 ∧ ∃ θ' : ↥L ≃* Perm (Fin 5), L ⊓ Jst =
      Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ Tst ∧ (θ' ⟨x, hx⟩).IsSwap})
    (hK : ∀ L ∈ I, ∀ x ∈ L, Odd (orderOf x) → x ∈ Kst)
    (hkinv : ∀ φ ∈ Jst, ∀ w ∈ fixV Kst, φ w ∈ fixV Kst) :
    ∃ L₁ L₂ P₁ P₂ : Subgroup (MulAut W), Pair2 L₁ L₂ P₁ P₂ Kst ∧ Jst = P₁ ⊔ P₂ ∧
      (⨆ L ∈ I, L) = L₁ ⊔ L₂ ∧
      ∃ gs ∈ Kst, L₁ ⊔ L₂ ≤ Jst ⊔ Jst.map (MulAut.conj gs).toMonoidHom := by
  classical
  have hmapmono : ∀ (g : MulAut W) {P : Subgroup (MulAut W)}, P ≤ Jst →
      P.map (MulAut.conj g).toMonoidHom ≤ Jst.map (MulAut.conj g).toMonoidHom :=
    fun g _ h => Subgroup.map_mono h
  rcases hcard with h1 | h2
  ·
    obtain ⟨L₁, hI⟩ := Finset.card_eq_one.mp h1
    have hmem : ∀ L, L ∈ I ↔ L = L₁ := fun L => by rw [hI]; simp
    have hL₁ : L₁ ∈ I := (hmem L₁).2 rfl
    obtain ⟨hblk, hv, g, hgL, hgK, hg⟩ := block_data (hA5 L₁ hL₁) (hL4 L₁ hL₁) (hK L₁ hL₁)
    have hJ : Jst = (L₁ ⊓ Jst) ⊔ ⊥ := by
      rw [sup_bot_eq]
      conv_lhs => rw [hJdec, iSup_eq_of_mem_single _ hmem]
    have hsup' : fixV Kst ⊔ commV L₁ ⊔ commV (⊥ : Subgroup (MulAut W)) = ⊤ := by
      rw [commV_bot, sup_bot_eq]
      have := hsup
      rwa [iSup_eq_of_mem_single _ hmem] at this
    refine ⟨L₁, ⊥, L₁ ⊓ Jst, ⊥, ⟨hblk, BlkProp.bot, fun a _ b hb => ?_, inf_bot_eq _, hsup', ?_, ?_,
      hv, ?_, ?_⟩, hJ, ?_, g, hgK, ?_⟩
    · rw [Subgroup.mem_bot.1 hb]
      simp
    · rw [commV_bot, sup_bot_eq]
      exact inf_le_right
    · rw [commV_bot, bot_inf_eq]
      exact bot_le
    · rw [commV_bot, inf_bot_eq]
    · intro φ hφ w hw
      rw [← hJ] at hφ
      exact hkinv φ hφ w hw
    · rw [sup_bot_eq, iSup_eq_of_mem_single _ hmem]
    · rw [sup_bot_eq]
      exact hg.trans (sup_le_sup inf_le_right (hmapmono g inf_le_right))
  ·
    obtain ⟨L₁, L₂, hne, hI⟩ := Finset.card_eq_two.mp h2
    have hmem : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂ := fun L => by rw [hI]; simp
    have hL₁ : L₁ ∈ I := (hmem L₁).2 (Or.inl rfl)
    have hL₂ : L₂ ∈ I := (hmem L₂).2 (Or.inr rfl)
    obtain ⟨hblk₁, hv₁, g₁, hg₁L, hg₁K, hg₁⟩ := block_data (hA5 L₁ hL₁) (hL4 L₁ hL₁) (hK L₁ hL₁)
    obtain ⟨hblk₂, hv₂, g₂, hg₂L, hg₂K, hg₂⟩ := block_data (hA5 L₂ hL₂) (hL4 L₂ hL₂) (hK L₂ hL₂)
    have hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hcomm L₁ hL₁ L₂ hL₂ hne
    have hJ : Jst = (L₁ ⊓ Jst) ⊔ (L₂ ⊓ Jst) := by
      conv_lhs => rw [hJdec, iSup_eq_of_mem_pair (fun L => L ⊓ Jst) hmem]
    have hind₁ : L₁ ⊓ L₂ = ⊥ := by
      refine eq_bot_iff.2 ?_
      rw [← hind L₁ hL₁]
      refine inf_le_inf_left _ ?_
      rw [iSup_ne_of_mem_pair (fun L => L) hne hmem]
    have hcV₂ : ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₂), commV L' = commV L₁ := by
      have := iSup_ne_of_mem_pair (fun L => commV L) hne.symm
        (fun L => (hmem L).trans (or_comm))
      exact this
    refine ⟨L₁, L₂, L₁ ⊓ Jst, L₂ ⊓ Jst, ⟨hblk₁, hblk₂, hc, hind₁, ?_, ?_, ?_, hv₁, hv₂, ?_⟩, hJ,
      iSup_eq_of_mem_pair (fun L => L) hmem, g₁ * g₂, Subgroup.mul_mem _ hg₁K hg₂K, ?_⟩
    · have := hsup
      rwa [iSup_eq_of_mem_pair (fun L => commV L) hmem, ← sup_assoc] at this
    · have := hinf L₁ hL₁
      rwa [iSup_ne_of_mem_pair (fun L => commV L) hne hmem] at this
    · have := hinf L₂ hL₂
      rwa [hcV₂] at this
    · intro φ hφ w hw
      rw [← hJ] at hφ
      exact hkinv φ hφ w hw
    · have e₁ : (L₁ ⊓ Jst).map (MulAut.conj (g₁ * g₂)).toMonoidHom =
          (L₁ ⊓ Jst).map (MulAut.conj g₁).toMonoidHom :=
        map_conj_mul_of_commute fun y hy => hc y hy.1 g₂ hg₂L
      have e₂ : (L₂ ⊓ Jst).map (MulAut.conj (g₁ * g₂)).toMonoidHom =
          (L₂ ⊓ Jst).map (MulAut.conj g₂).toMonoidHom := by
        have hgg : g₁ * g₂ = g₂ * g₁ := hc g₁ hg₁L g₂ hg₂L
        rw [hgg]
        exact map_conj_mul_of_commute fun y hy => (hc g₁ hg₁L y hy.1).symm
      refine sup_le ?_ ?_
      · refine hg₁.trans (sup_le (le_sup_of_le_left inf_le_right) ?_)
        rw [← e₁]
        exact (hmapmono (g₁ * g₂) inf_le_right).trans le_sup_right
      · refine hg₂.trans (sup_le (le_sup_of_le_left inf_le_right) ?_)
        rw [← e₂]
        exact (hmapmono (g₁ * g₂) inf_le_right).trans le_sup_right

end Ext

end LRed10

end CFSG.Quasithin
