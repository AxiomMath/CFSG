module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Ctx
public import CFSG.Quasithin.Vol2.Ch12Sec6L23d
public import CFSG.Quasithin.Vol2.Ch12Sec6L20a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N
open scoped IsMulCommutative

namespace S126T2

theorem pv_add_pv_cases : ∀ a b c d : Fin 8, a ≠ b →
    (B5FinS8.pv a b + B5FinS8.pv c d = 0 ∨ B5FinS8.pv a b + B5FinS8.pv c d = fun _ => 1) →
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  decide +kernel

theorem mk_pe_eq_mk_pe {a b c d : Fin 8} (hab : a ≠ b)
    (h : (QuotientGroup.mk (pe a b) : D8) = QuotientGroup.mk (pe c d)) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have h1 : (QuotientGroup.mk (pe a b * (pe c d)⁻¹) : D8) = 1 := by
    rw [QuotientGroup.mk_mul, h, QuotientGroup.mk_inv, mul_inv_cancel]
  have hneg : ∀ u : Fin 8 → ZMod 2, -u = u := by decide +kernel
  have key : Multiplicative.toAdd ((pe a b * (pe c d)⁻¹ : ↥(coreMod 8)) : PermMod 8) =
      B5FinS8.pv a b + B5FinS8.pv c d := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, S126L20a.toAdd_pe,
      S126L20a.toAdd_pe, hneg]
  refine pv_add_pv_cases a b c d hab ?_
  rcases (S126FE.mk_eq_one_iff _).1 h1 with e | e
  · left
    rw [← key, e]
    rfl
  · right
    rw [← key, e]
    rfl

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem mem_Gv_iff (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    {σ : Equiv.Perm (Fin 8)} (hσ : ActsAs F x σ) :
    x ∈ Gv v ↔ (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hxV v).1 hv
  have hact := hσ ⟨v, hv⟩ ⟨_, hxv⟩ rfl
  rw [hβ, S126L20a.dAct_pe] at hact
  constructor
  · intro hx
    have e : x * v * x⁻¹ = v := by
      rw [Gv, Subgroup.mem_centralizer_singleton_iff] at hx
      rw [hx, mul_inv_cancel_right]
    have h1 : F.β ⟨x * v * x⁻¹, hxv⟩ = F.β ⟨v, hv⟩ := by
      congr 1
      exact Subtype.ext e
    rw [h1, hβ] at hact
    rcases mk_pe_eq_mk_pe (by decide : (0 : Fin 8) ≠ 1) hact with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro h01
    have hpe : pe (σ 0) (σ 1) = pe 0 1 := by
      rcases h01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
      · rw [h0, h1, S126L20a.pe_comm]
    have e : x * v * x⁻¹ = v := by
      by_cases hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
      ·
        have hβi : Function.Injective F.β := by
          rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
          intro w hw
          have h1 : (w : G) ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨w.2, (F.β_ker w).1 hw⟩
          rw [hZ] at h1
          exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h1))
        have h2 : F.β ⟨x * v * x⁻¹, hxv⟩ = F.β ⟨v, hv⟩ := by rw [hact, hpe, hβ]
        exact congrArg Subtype.val (hβi h2)
      · obtain ⟨E⟩ := S126FE.exists_frame126E h1222 F hH hZ
        have hγ := E.act x hxL hxV σ hσ ⟨v, hv⟩ ⟨_, hxv⟩ rfl
        have hfix : coreAct 8 σ (E.γ ⟨v, hv⟩) = E.γ ⟨v, hv⟩ := by
          have h1 : (QuotientGroup.mk (E.γ ⟨v, hv⟩ * (pe 0 1)⁻¹) : D8) = 1 := by
            rw [QuotientGroup.mk_mul, ← E.β_eq, hβ, QuotientGroup.mk_inv, mul_inv_cancel]
          have h2 : E.γ ⟨v, hv⟩ = (E.γ ⟨v, hv⟩ * (pe 0 1)⁻¹) * pe 0 1 := by group
          rw [h2, map_mul, S126L20a.coreAct_pe, hpe]
          congr 1
          rcases (S126FE.mk_eq_one_iff _).1 h1 with e1 | e1
          · rw [e1, map_one]
          · rw [e1, S126FE.coreAct_eOm]
        rw [hfix] at hγ
        exact congrArg Subtype.val (E.γ.injective hγ)
    rw [Gv, Subgroup.mem_centralizer_singleton_iff]
    calc x * v = x * v * x⁻¹ * x := by group
      _ = v * x := by rw [e]

theorem exists_TL_of_Q8 (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ∀ σ ∈ S126L1c.Q8, ∃ t ∈ T ⊓ L, ActsAs F t σ := by
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTL := hyp.normalizes
  have hcardA := S126L1c.card_autOn hH hLV
  let f : ↥(alternatingGroup (Fin 8)) →* MulAut ↥V := (autOn L V).subtype.comp F.π
  have hfi : Function.Injective f := Subtype.val_injective.comp (S126N.pi_bijective F hH).1
  have hfr : f.range = autOn L V := by
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact (F.π σ).2
    · intro hx
      obtain ⟨σ, hσ⟩ := F.π_surj ⟨x, hx⟩
      exact ⟨σ, by simp [f, hσ]⟩
  have hsylTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hS := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hsylTL hLV
  have hS64 : Nat.card ↥(autOn (T ⊓ L) V) = 2 ^ 6 :=
    S126L1c.card_of_isSylowTwoOf hS (m := 315) (by rw [hcardA, card_A8]; norm_num) (by decide)
  let P₀ : Subgroup ↥(alternatingGroup (Fin 8)) := (autOn (T ⊓ L) V).comap f
  have hP₀ : Nat.card P₀ = 64 := by
    have h1 : P₀.map f = autOn (T ⊓ L) V := by
      rw [Subgroup.map_comap_eq, hfr]
      exact inf_of_le_right hS.1
    have h2 : Nat.card (P₀.map f) = Nat.card P₀ :=
      Nat.card_congr (Subgroup.equivMapOfInjective P₀ f hfi).toEquiv.symm
    rw [← h2, h1, hS64]
    norm_num
  let P : Subgroup (Equiv.Perm (Fin 8)) := P₀.map (alternatingGroup (Fin 8)).subtype
  have hP : Nat.card P = 64 := by
    rw [← hP₀]
    exact Nat.card_congr (Subgroup.equivMapOfInjective P₀ _ Subtype.val_injective).toEquiv.symm
  have hact : ∀ σ ∈ P₀, ∃ t ∈ T ⊓ L, ActsAs F t σ := by
    intro σ hσ
    obtain ⟨t, ht, htTL, hta⟩ := mem_autOn_iff_exists.mp (show f σ ∈ autOn (T ⊓ L) V from hσ)
    exact ⟨t, htTL, actsAs_of_pi F ht σ hta⟩
  have hPQ : P ≤ S126L1c.Q8 := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨t, htTL, hta⟩ := hact σ hσ
    obtain ⟨τ, hτP, hτ⟩ := actsAs_of_mem_T F htTL.1
    have e : (σ : Equiv.Perm (Fin 8)) = τ := ActsAs.unique hta hτ (hLV htTL.2)
    refine ⟨?_, σ.2⟩
    change (σ : Equiv.Perm (Fin 8)) ∈ _
    rw [e]
    exact S126L23d.mem_P8_of_presPart hτP
  have hPeq : P = S126L1c.Q8 := Subgroup.eq_of_le_of_card_ge hPQ (by
    have := S126L1c.card_Q8_le
    omega)
  intro σ hσ
  rw [← hPeq] at hσ
  obtain ⟨σ', hσ', rfl⟩ := hσ
  exact hact σ' hσ'

theorem fix01_of {ρ : Equiv.Perm (Fin 8)} (hρ : ∀ i, ρ (partner i) = partner (ρ i))
    (h0 : ρ 0 = 0 ∨ ρ 0 = 1) : (ρ 0 = 0 ∧ ρ 1 = 1) ∨ (ρ 0 = 1 ∧ ρ 1 = 0) := by
  have h1 : ρ 1 = partner (ρ 0) := hρ 0
  rcases h0 with h | h
  · exact Or.inl ⟨h, by rw [h1, h]; rfl⟩
  · exact Or.inr ⟨h, by rw [h1, h]; rfl⟩

theorem partner_comm_mul {σ τ : Equiv.Perm (Fin 8)} (hσ : ∀ i, σ (partner i) = partner (σ i))
    (hτ : ∀ i, τ (partner i) = partner (τ i)) : ∀ i, (σ⁻¹ * τ) (partner i) =
      partner ((σ⁻¹ * τ) i) := by
  intro i
  have hσ' : ∀ j, σ⁻¹ (partner j) = partner (σ⁻¹ j) := fun j => by
    apply σ.injective
    rw [S126Ex.perm_apply_inv, hσ, S126Ex.perm_apply_inv]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ, hσ']

theorem pair_cases : ∀ a : Fin 8, (a = 0 ∨ a = 1) ∨ (S126L1c.g2⁻¹ a = 0 ∨ S126L1c.g2⁻¹ a = 1) ∨
    (S126L1c.bsw⁻¹ a = 0 ∨ S126L1c.bsw⁻¹ a = 1) ∨
    ((S126L1c.bsw * S126L1c.g2)⁻¹ a = 0 ∨ (S126L1c.bsw * S126L1c.g2)⁻¹ a = 1) := by
  decide

theorem g2_mem_Q8 : S126L1c.g2 ∈ S126L1c.Q8 :=
  S126L1c.tau20_eq ▸ S126L1c.mem_Q8.2.1

theorem bsw_g2_mem_Q8 : S126L1c.bsw * S126L1c.g2 ∈ S126L1c.Q8 :=
  S126L1c.Q8.mul_mem S126L1c.mem_Q8.2.2.2.2 g2_mem_Q8

theorem partner_comm_of_mem_Q8 {σ : Equiv.Perm (Fin 8)} (h : σ ∈ S126L1c.Q8) :
    ∀ i, σ (partner i) = partner (σ i) :=
  (S126Ex.presPart_of_mem (S126Ex.P8_le_presSub h.1)).1

theorem relIndex_Tv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    (Tv T v).relIndex T = 4 := by
  classical
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  let _ : MulAction ↥T G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp T.subtype)
  have hsmul : ∀ (t : ↥T) (x : G), t • x = (t : G) * x * (t : G)⁻¹ := fun t x => rfl
  have hstab : MulAction.stabilizer ↥T v = (Gv v).subgroupOf T := by
    ext t
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Gv,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (t : G) * v = t * v * (t : G)⁻¹ * t := by group
        _ = v * t := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have hrel : (Tv T v).relIndex T = (MulAction.orbit ↥T v).ncard := by
    rw [← MulAction.index_stabilizer, hstab, Subgroup.relIndex, Tv, Subgroup.inf_subgroupOf_left]
  rw [hrel]
  obtain ⟨t₁, ht₁, hσ₁⟩ := exists_TL_of_Q8 F hH _ g2_mem_Q8
  obtain ⟨t₂, ht₂, hσ₂⟩ := exists_TL_of_Q8 F hH _ S126L1c.mem_Q8.2.2.2.2
  obtain ⟨t₃, ht₃, hσ₃⟩ := exists_TL_of_Q8 F hH _ bsw_g2_mem_Q8
  have hsub : MulAction.orbit ↥T v ⊆
      ({v, t₁ * v * t₁⁻¹, t₂ * v * t₂⁻¹, t₃ * v * t₃⁻¹} : Set G) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨τ, hτP, hτ⟩ := actsAs_of_mem_T F t.2
    have hconj : ∀ (s : G) (hs : s ∈ T) (σ : Equiv.Perm (Fin 8)), ActsAs F s σ →
        σ ∈ S126L1c.Q8 → (σ⁻¹ (τ 0) = 0 ∨ σ⁻¹ (τ 0) = 1) → t • v = s * v * s⁻¹ := by
      intro s hs σ hσ hσQ h0
      have hmul : ActsAs F (s⁻¹ * t) (σ⁻¹ * τ) := hσ.inv.mul hτ (hTV t.2)
      have hfix := fix01_of (partner_comm_mul (partner_comm_of_mem_Q8 hσQ) hτP.1)
        (by rw [Equiv.Perm.mul_apply]; exact h0)
      have hmem := (mem_Gv_iff h1222 F hH hv hβ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTL hs))
        (hTL t.2)) (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTV hs)) (hTV t.2)) hmul).2 hfix
      rw [Gv, Subgroup.mem_centralizer_singleton_iff] at hmem
      rw [hsmul]
      calc (t : G) * v * (t : G)⁻¹ = s * ((s⁻¹ * t) * v) * (t : G)⁻¹ := by group
        _ = s * (v * (s⁻¹ * t)) * (t : G)⁻¹ := by rw [hmem]
        _ = s * v * s⁻¹ := by group
    show t • v ∈ _
    rcases pair_cases (τ 0) with h | h | h | h
    · left
      have := hconj 1 T.one_mem 1 (ActsAs.one F) S126L1c.Q8.one_mem (by simpa using h)
      rw [this]
      group
    · exact Or.inr (Or.inl (hconj t₁ ht₁.1 _ hσ₁ g2_mem_Q8 h))
    · exact Or.inr (Or.inr (Or.inl (hconj t₂ ht₂.1 _ hσ₂ S126L1c.mem_Q8.2.2.2.2 h)))
    · exact Or.inr (Or.inr (Or.inr (hconj t₃ ht₃.1 _ hσ₃ bsw_g2_mem_Q8 h)))
  have hsup : ({v, t₁ * v * t₁⁻¹, t₂ * v * t₂⁻¹, t₃ * v * t₃⁻¹} : Set G) ⊆
      MulAction.orbit ↥T v := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact MulAction.mem_orbit_self _
    · exact ⟨⟨t₁, ht₁.1⟩, rfl⟩
    · exact ⟨⟨t₂, ht₂.1⟩, rfl⟩
    · exact ⟨⟨t₃, ht₃.1⟩, rfl⟩
  rw [Set.Subset.antisymm hsub hsup]
  have hval : ∀ (s : G) (hs : s ∈ T) (σ : Equiv.Perm (Fin 8)), ActsAs F s σ →
      F.β ⟨s * v * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hTV hs) v).1 hv⟩ =
        QuotientGroup.mk (pe (σ 0) (σ 1)) := by
    intro s hs σ hσ
    rw [hσ ⟨v, hv⟩ _ rfl, hβ, S126L20a.dAct_pe]
  have hne : ∀ (s s' : G) (hs : s ∈ T) (hs' : s' ∈ T) (σ σ' : Equiv.Perm (Fin 8)), ActsAs F s σ →
      ActsAs F s' σ' → σ 0 ≠ σ 1 → ¬ ((σ' 0 = σ 0 ∧ σ' 1 = σ 1) ∨ (σ' 0 = σ 1 ∧ σ' 1 = σ 0)) →
      s * v * s⁻¹ ≠ s' * v * s'⁻¹ := by
    intro s s' hs hs' σ σ' hσ hσ' h01 hpair heq
    have h1 := hval s hs σ hσ
    have h2 := hval s' hs' σ' hσ'
    have h3 : F.β ⟨s * v * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hTV hs) v).1 hv⟩ =
        F.β ⟨s' * v * s'⁻¹, (Subgroup.mem_normalizer_iff.1 (hTV hs') v).1 hv⟩ := by
      congr 1
      exact Subtype.ext heq
    rw [h1, h2] at h3
    exact hpair (mk_pe_eq_mk_pe h01 h3)
  have h1 := ActsAs.one F
  have e1 : (1 : G) * v * 1⁻¹ = v := by group
  have hn01 := hne 1 t₁ T.one_mem ht₁.1 1 _ h1 hσ₁ (by decide) (by decide)
  have hn02 := hne 1 t₂ T.one_mem ht₂.1 1 _ h1 hσ₂ (by decide) (by decide)
  have hn03 := hne 1 t₃ T.one_mem ht₃.1 1 _ h1 hσ₃ (by decide) (by decide)
  have hn12 := hne t₁ t₂ ht₁.1 ht₂.1 _ _ hσ₁ hσ₂ (by decide) (by decide)
  have hn13 := hne t₁ t₃ ht₁.1 ht₃.1 _ _ hσ₁ hσ₃ (by decide) (by decide)
  have hn23 := hne t₂ t₃ ht₂.1 ht₃.1 _ _ hσ₂ hσ₃ (by decide) (by decide)
  rw [e1] at hn01 hn02 hn03
  rw [Set.ncard_insert_of_notMem (by simp [hn01, hn02, hn03]),
    Set.ncard_insert_of_notMem (by simp [hn12, hn13]),
    Set.ncard_pair hn23]

end S126T2

end CFSG.Quasithin.H13
