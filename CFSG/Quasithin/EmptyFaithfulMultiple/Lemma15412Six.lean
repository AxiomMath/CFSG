module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Two
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Quot
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Five
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Psi

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

theorem eight_le_card_of_moves {W : Type*} [Group W] [Finite W] {P : Subgroup (MulAut W)}
    (hP : IsPGroup 2 P) {A B : Subgroup W} (hAB : A ⊓ B = ⊥) {α β γ : MulAut W} (hα : α ∈ P)
    (hβ : β ∈ P) (hγ : γ ∈ P) {a b : W} (ha : a ∈ A) (ha1 : a ≠ 1) (hαa : α a ≠ a)
    (hαA : α a ∈ A) (hβa : β a = a) (hαb : α b = b) (hβb : β b ≠ b) (hγa : γ a ∈ B) :
    8 ≤ Nat.card P := by
  classical
  have hdisj : ∀ x ∈ A, x ∈ B → x = 1 := fun x hx hx' => by
    have hm : x ∈ A ⊓ B := ⟨hx, hx'⟩
    rwa [hAB, Subgroup.mem_bot] at hm
  have hαa1 : α a ≠ 1 := fun h => ha1 (α.injective (by rw [h, map_one]))
  have hαβa : (α * β) a = α a := by rw [MulAut.mul_apply, hβa]
  have hαβb : (α * β) b ≠ b := by
    rw [MulAut.mul_apply]
    intro h
    apply hβb
    apply α.injective
    rw [h, hαb]
  have n1 : (1 : MulAut W) ≠ α := fun h => hαa (by rw [← h]; rfl)
  have n2 : (1 : MulAut W) ≠ β := fun h => hβb (by rw [← h]; rfl)
  have n3 : (1 : MulAut W) ≠ α * β := fun h => hαa (by rw [← hαβa, ← h]; rfl)
  have n4 : (1 : MulAut W) ≠ γ := fun h => ha1 (hdisj a ha (by rw [← h] at hγa; exact hγa))
  have n5 : α ≠ β := fun h => hαa (by rw [h, hβa])
  have n6 : α ≠ α * β := fun h => hαβb (by rw [← h, hαb])
  have n7 : α ≠ γ := fun h => hαa1 (hdisj _ hαA (by rw [h]; exact hγa))
  have n8 : β ≠ α * β := fun h => hαa (by rw [← hαβa, ← h, hβa])
  have n9 : β ≠ γ := fun h => ha1 (hdisj a ha (by rw [← hβa, h]; exact hγa))
  have n10 : α * β ≠ γ := fun h => hαa1 (hdisj _ hαA (by rw [← hαβa, h]; exact hγa))
  let s : Finset (MulAut W) := {1, α, β, α * β, γ}
  have hs : s.card = 5 := by
    simp only [s]
    rw [Finset.card_insert_of_notMem (by simp [n1, n2, n3, n4]),
      Finset.card_insert_of_notMem (by simp [n5, n6, n7]),
      Finset.card_insert_of_notMem (by simp [n8, n9]), Finset.card_pair n10]
  have hsub : ∀ x ∈ s, x ∈ P := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact hα
    · exact hβ
    · exact P.mul_mem hα hβ
    · exact hγ
  have h5 : 5 ≤ Nat.card P := by
    rw [← hs, ← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective (fun x : s => (⟨x, hsub x x.2⟩ : P))
      (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn] at h5 ⊢
  rcases n with _ | _ | _ | n
  · norm_num at h5
  · norm_num at h5
  · norm_num at h5
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem convI_val_eq {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : IsElemAbelian 2 U)
    {g : G} (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (u : IntMod V hV) (hu : u.val ∈ U) :
    (convI hU ⟨g, hgU⟩ (IntMod.mk hU ⟨u.val, hu⟩)).val = (convI hV ⟨g, hgV⟩ u).val := by
  rw [convI_apply_val, convI_apply_val]
  rfl

namespace Setup

variable (h : Setup T M) {Y : Subgroup G}
include h

theorem le_normalizer_commutator_sup (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    Y ⊔ T ≤ Subgroup.normalizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) :=
  (h.sup_le_M hYM).trans (h.le_normalizer_commutator hY hYM)

theorem relIndex_sup_eq_mul (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ((Y ⊔ T) ⊓ Subgroup.centralizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G)).relIndex (Y ⊔ T) =
      Nat.card (autI (h.isElemAbelian_commutator hYM) T) * (pCoreOf 2 Y).relIndex Y := by
  set U := (⁅VZ T M, Y⁆ : Subgroup G)
  have hU := h.isElemAbelian_commutator hYM
  have hTN : T ≤ Subgroup.normalizer (U : Set G) :=
    le_sup_right.trans (h.le_normalizer_commutator_sup hY hYM)
  rw [h.inf_centralizer_commutator_eq hY hYM]
  have hOT : pCoreOf 2 (Y ⊔ T) ≤ T := pCoreOf_le_of_isSylowTwoOf h.isSylowTwoOf_sup
  have e1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (Y ⊔ T)) T (Y ⊔ T) hOT le_sup_right
  rw [relIndex_sup_eq (basic hY).2.1, h.inf_eq_pCoreOf hY hYM] at e1
  have e2 : T ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 (Y ⊔ T) := by
    have e3 := h.inf_centralizer_commutator_eq hY hYM
    apply le_antisymm
    · rw [← e3]
      exact inf_le_inf_right _ le_sup_right
    · intro t ht
      have ht' : t ∈ (Y ⊔ T) ⊓ Subgroup.centralizer (U : Set G) := e3 ▸ ht
      exact ⟨hOT ht, ht'.2⟩
  rw [card_autI_eq hU hTN, e2, ← e1]

theorem six_one (hY : IsYFamily T Y) (hYM : Y ≤ M) (hs : (pCoreOf 2 Y).relIndex Y = 3)
    (hU4 : Nat.card (⁅VZ T M, Y⁆ : Subgroup G) = 4)
    (hidx : (eCentOf T Y).relIndex (eOf T) = 2) : Concl15412Six G T M Y := by
  have hU := h.isElemAbelian_commutator hYM
  have hTN : T ≤ Subgroup.normalizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans (h.le_normalizer_commutator_sup hY hYM)
  refine Or.inl ⟨hs, quotientIso_sym3 hU4 (h.le_normalizer_commutator_sup hY hYM)
    (h.inf_centralizer_commutator_eq hY hYM) ?_, hidx⟩
  rw [h.relIndex_sup_eq_mul hY hYM, hs]
  have hne : autI hU T ≠ ⊥ := by
    rw [Ne, autI_eq_bot_iff hU hTN]
    intro hle
    exact h.not_thompsonJ_le hY hYM ((thompsonJ_le_self T).trans hle)
  have h2 : 2 ≤ Nat.card (autI hU T) := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card (autI hU T) = 1 := by
      have := Nat.card_pos (α := autI hU T)
      omega
    exact hne (Subgroup.eq_bot_of_card_eq _ h1)
  omega

theorem six_two (hY : IsYFamily T Y) (hYM : Y ≤ M)
    {𝓗 I : Finset (Subgroup (MulAut (IntMod (VZ T M) h.elem)))} (B : E2.Blocks h.elem M 𝓗 I)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) h.elem))} (hL₁ : L₁ ∈ I) (hL₂ : L₂ ∈ I)
    (h12 : L₁ ≠ L₂) (hI' : ∀ L ∈ I, L = L₁ ∨ L = L₂)
    {f₁ f₂ : MulAut (IntMod (VZ T M) h.elem)} (hf₁ : f₁ ∈ L₁) (hf₂ : f₂ ∈ L₂)
    (h3₁ : orderOf f₁ = 3) (h3₂ : orderOf f₂ = 3)
    (hD : autI h.elem Y = Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂)
    {x : MulAut (IntMod (VZ T M) h.elem)} (hx : x ∈ autI h.elem T)
    (hxL : B1.conjAut x L₁ = L₂) : Concl15412Six G T M Y := by
  have hW : ∀ w : IntMod (VZ T M) h.elem, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hp : ∀ {f : MulAut (IntMod (VZ T M) h.elem)}, orderOf f = 3 → f ^ 3 = 1 := fun hf => by
    rw [← hf]
    exact pow_orderOf_eq_one _
  have s₁ := B.sub hL₁
  have s₂ := B.sub hL₂
  have hZ₁M : Subgroup.zpowers f₁ ≤ autI h.elem M := Subgroup.zpowers_le.mpr (B.le_autI hL₁ hf₁)
  have hZ₂M : Subgroup.zpowers f₂ ≤ autI h.elem M := Subgroup.zpowers_le.mpr (B.le_autI hL₂ hf₂)
  have ho₁ := odd_orderOf_of_isElemAbelian (isElemAbelian_zpowers (hp h3₁))
  have ho₂ := odd_orderOf_of_isElemAbelian (isElemAbelian_zpowers (hp h3₂))
  have hc₁ : Nat.card (Subgroup.zpowers f₁) = 3 := by rw [Nat.card_zpowers, h3₁]
  have hc₂ : Nat.card (Subgroup.zpowers f₂) = 3 := by rw [Nat.card_zpowers, h3₂]
  have hodd3 : Odd 3 := by decide
  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁, Y₁ = h.ps (Subgroup.zpowers f₁) := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y₂, Y₂ = h.ps (Subgroup.zpowers f₂) := ⟨_, rfl⟩
  have hA₁ : autI h.elem Y₁ = Subgroup.zpowers f₁ := hY₁ ▸ h.autI_ps hZ₁M ho₁
  have hA₂ : autI h.elem Y₂ = Subgroup.zpowers f₂ := hY₂ ▸ h.autI_ps hZ₂M ho₂
  have hY₁M : Y₁ ≤ M := hY₁ ▸ h.ps_le _
  have hY₂M : Y₂ ≤ M := hY₂ ▸ h.ps_le _
  have hYeq : Y = Y₁ ⊔ Y₂ := by
    rw [hY₁, hY₂, ← h.ps_sup hZ₁M hZ₂M ho₁ ho₂, ← hD]
    exact h.eq_psi hY hYM
  have hV₁ : ⁅VZ T M, Y₁⁆ = (commSub ⊤ L₁).map (E2.valHom h.elem) := by
    rw [h.commutator_eq hY₁M, hA₁, commSub_zpowers_eq hW B.hb s₁ hf₁ h3₁]
  have hV₂ : ⁅VZ T M, Y₂⁆ = (commSub ⊤ L₂).map (E2.valHom h.elem) := by
    rw [h.commutator_eq hY₂M, hA₂, commSub_zpowers_eq hW B.hb s₂ hf₂ h3₂]
  have hcV₁ : Nat.card (⁅VZ T M, Y₁⁆ : Subgroup G) = 4 := by
    rw [hV₁, card_map_valHom, B.hb.card_comm L₁ s₁]
  have hcV₂ : Nat.card (⁅VZ T M, Y₂⁆ : Subgroup G) = 4 := by
    rw [hV₂, card_map_valHom, B.hb.card_comm L₂ s₂]
  have hVinf : ⁅VZ T M, Y₁⁆ ⊓ ⁅VZ T M, Y₂⁆ = ⊥ := by
    rw [hV₁, hV₂, ← map_valHom_inf, commSub_inf_eq_bot_of_ne hW B.hb s₁ s₂ h12, Subgroup.map_bot]
  have hVsup : ⁅VZ T M, Y⁆ = ⁅VZ T M, Y₁⁆ ⊔ ⁅VZ T M, Y₂⁆ := by
    rw [h.commutator_eq hYM, hD, commSub_sup_eq, Subgroup.map_sup,
      commSub_zpowers_eq hW B.hb s₁ hf₁ h3₁, commSub_zpowers_eq hW B.hb s₂ hf₂ h3₂, hV₁, hV₂]
  have hcardY : Nat.card (autI h.elem Y) = 9 := by
    rw [hD]
    exact card_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂
  have hidx9 : (pCoreOf 2 Y).relIndex Y = 9 := by
    rw [relIndex_pCoreOf_eq h.elem (hYM.trans h.le_normalizer) (h.odd_card_autI hY hYM)
      (h.isPGroup_inf' hYM), hcardY]
  obtain ⟨s, hs, hsidx, -, -, hsJ⟩ := h.three hY hYM
  have hs2 : s = 2 := by
    rcases hs with rfl | rfl
    · rw [hidx9] at hsidx
      norm_num at hsidx
    · rfl
  rw [hs2] at hsJ
  have hidx4 : (eCentOf T Y).relIndex (eOf T) = 4 := by
    have := h.relIndex_eCentOf hY hYM hsJ
    norm_num at this
    exact this
  have hcV : ∀ g ∈ M, ∀ K : Subgroup G, cjSub g ⁅VZ T M, K⁆ = ⁅VZ T M, cjSub g K⁆ := by
    intro g hg K
    show (⁅VZ T M, K⁆).map (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_commutator]
    show ⁅cjSub g (VZ T M), cjSub g K⁆ = _
    rw [cjSub_eq_of_mem_normalizer (h.le_normalizer hg)]
  have hcY : ∀ g (hg : g ∈ M) (D : Subgroup (MulAut (IntMod (VZ T M) h.elem))),
      cjSub g (h.ps D) = h.ps (B1.conjAut (convI h.elem ⟨g, h.le_normalizer hg⟩) D) :=
    fun g hg D => cjSub_psi h.elem h.le_normalizer hg D
  have hpermM : ∀ g ∈ M,
      (cjSub g ⁅VZ T M, Y₁⁆ = ⁅VZ T M, Y₁⁆ ∧ cjSub g ⁅VZ T M, Y₂⁆ = ⁅VZ T M, Y₂⁆) ∨
        (cjSub g ⁅VZ T M, Y₁⁆ = ⁅VZ T M, Y₂⁆ ∧ cjSub g ⁅VZ T M, Y₂⁆ = ⁅VZ T M, Y₁⁆) := by
    intro g hg
    have hgM : convI h.elem ⟨g, h.le_normalizer hg⟩ ∈ autI h.elem M :=
      convI_mem_autI h.elem hg (h.le_normalizer hg)
    rw [hcV g hg, hcV g hg, hY₁, hY₂, hcY g hg, hcY g hg]
    rcases hI' _ (B.conjAut_mem hgM hL₁) with e1 | e1
    · have e2 : B1.conjAut (convI h.elem ⟨g, h.le_normalizer hg⟩) L₂ = L₂ :=
        (hI' _ (B.conjAut_mem hgM hL₂)).resolve_left fun e =>
          h12 (conjAut_injective _ (e1.trans e.symm))
      left
      rw [conjAut_zpowers_eq B.hb s₁ e1 hf₁ hf₁ h3₁ h3₁,
        conjAut_zpowers_eq B.hb s₂ e2 hf₂ hf₂ h3₂ h3₂]
      exact ⟨rfl, rfl⟩
    · have e2 : B1.conjAut (convI h.elem ⟨g, h.le_normalizer hg⟩) L₂ = L₁ :=
        (hI' _ (B.conjAut_mem hgM hL₂)).resolve_right fun e =>
          h12 (conjAut_injective _ (e1.trans e.symm))
      right
      rw [conjAut_zpowers_eq B.hb s₂ e1 hf₁ hf₂ h3₁ h3₂,
        conjAut_zpowers_eq B.hb s₁ e2 hf₂ hf₁ h3₂ h3₁]
      exact ⟨rfl, rfl⟩
  have hU := h.isElemAbelian_commutator hYM
  have hTN : T ≤ Subgroup.normalizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans (h.le_normalizer_commutator_sup hY hYM)
  have hV₁U : ⁅VZ T M, Y₁⁆ ≤ ⁅VZ T M, Y⁆ := hVsup ▸ le_sup_left
  have hV₂U : ⁅VZ T M, Y₂⁆ ≤ ⁅VZ T M, Y⁆ := hVsup ▸ le_sup_right
  have h8 : 8 ≤ Nat.card (autI hU T) := by
    obtain ⟨τ₁, hτ₁L, hτ₁T, -, hτ₁2⟩ := B.exists_orderOf_eq_two h.red h.sylowM hL₁
    obtain ⟨τ₂, hτ₂L, hτ₂T, -, hτ₂2⟩ := B.exists_orderOf_eq_two h.red h.sylowM hL₂
    obtain ⟨g₁, hg₁T, rfl⟩ := (mem_autI h.elem).1 hτ₁T
    obtain ⟨g₂, hg₂T, rfl⟩ := (mem_autI h.elem).1 hτ₂T
    obtain ⟨σ, hσT, rfl⟩ := (mem_autI h.elem).1 hx
    have hτ₁1 : convI h.elem g₁ ≠ 1 := fun e => by
      rw [e, orderOf_one] at hτ₁2
      norm_num at hτ₁2
    have hτ₂1 : convI h.elem g₂ ≠ 1 := fun e => by
      rw [e, orderOf_one] at hτ₂2
      norm_num at hτ₂2
    obtain ⟨u₁, hu₁, hmv₁⟩ := exists_ne_of_ne_one B.hb s₁ hτ₁L hτ₁1
    obtain ⟨u₂, hu₂, hmv₂⟩ := exists_ne_of_ne_one B.hb s₂ hτ₂L hτ₂1
    have hu₁V : u₁.val ∈ ⁅VZ T M, Y₁⁆ := by
      rw [hV₁]
      exact ⟨u₁, hu₁, rfl⟩
    have hu₂V : u₂.val ∈ ⁅VZ T M, Y₂⁆ := by
      rw [hV₂]
      exact ⟨u₂, hu₂, rfl⟩
    have hval : ∀ (g : Subgroup.normalizer (VZ T M : Set G)) (hgT : (g : G) ∈ T)
        (u : IntMod (VZ T M) h.elem) (hu : u.val ∈ ⁅VZ T M, Y⁆),
        (convI hU ⟨g, hTN hgT⟩ (IntMod.mk hU ⟨u.val, hu⟩)).val = (convI h.elem g u).val :=
      fun g hgT u hu => convI_val_eq h.elem hU g.2 (hTN hgT) u hu
    have hAB : (⁅VZ T M, Y₁⁆ : Subgroup G).comap (E2.valHom hU) ⊓
        (⁅VZ T M, Y₂⁆ : Subgroup G).comap (E2.valHom hU) = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hw1, hw2⟩
      have hm : w.val ∈ ⁅VZ T M, Y₁⁆ ⊓ ⁅VZ T M, Y₂⁆ := ⟨hw1, hw2⟩
      rw [hVinf, Subgroup.mem_bot] at hm
      exact IntMod.val_injective hm
    refine eight_le_card_of_moves (B2F.isPGroup_autI hU h.isPGroup hTN) hAB
      (convI_mem_autI hU hg₁T (hTN hg₁T)) (convI_mem_autI hU hg₂T (hTN hg₂T))
      (convI_mem_autI hU hσT (hTN hσT)) (a := IntMod.mk hU ⟨u₁.val, hV₁U hu₁V⟩)
      (b := IntMod.mk hU ⟨u₂.val, hV₂U hu₂V⟩) hu₁V ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro he
      apply hmv₁
      have h1 : u₁.val = 1 := congrArg IntMod.val he
      have h2 : u₁ = 1 := IntMod.val_injective h1
      rw [h2, map_one]
    · intro he
      apply hmv₁
      apply IntMod.val_injective
      rw [← hval g₁ hg₁T u₁ (hV₁U hu₁V), he]
      rfl
    · show (convI hU ⟨g₁, hTN hg₁T⟩ (IntMod.mk hU ⟨u₁.val, hV₁U hu₁V⟩)).val ∈ ⁅VZ T M, Y₁⁆
      rw [hval g₁ hg₁T u₁ (hV₁U hu₁V), hV₁]
      exact ⟨_, B.hb.stab L₁ s₁ _ hτ₁L u₁ hu₁, rfl⟩
    · apply IntMod.val_injective
      rw [hval g₂ hg₂T u₁ (hV₁U hu₁V),
        B.hb.triv L₂ s₂ L₁ s₁ (Ne.symm h12) _ hτ₂L u₁ hu₁]
      rfl
    · apply IntMod.val_injective
      rw [hval g₁ hg₁T u₂ (hV₂U hu₂V), B.hb.triv L₁ s₁ L₂ s₂ h12 _ hτ₁L u₂ hu₂]
      rfl
    · intro he
      apply hmv₂
      apply IntMod.val_injective
      rw [← hval g₂ hg₂T u₂ (hV₂U hu₂V), he]
      rfl
    · show (convI hU ⟨σ, hTN hσT⟩ (IntMod.mk hU ⟨u₁.val, hV₁U hu₁V⟩)).val ∈ ⁅VZ T M, Y₂⁆
      rw [hval σ hσT u₁ (hV₁U hu₁V), hV₂, ← hxL, ← IsTransvectionBlocks.map_commSub_conjAut]
      exact ⟨_, ⟨u₁, hu₁, rfl⟩, rfl⟩
  have hker : (Y ⊔ T) ⊓ Subgroup.centralizer
      ((⁅VZ T M, Y₁⁆ ⊔ ⁅VZ T M, Y₂⁆ : Subgroup G) : Set G) = pCoreOf 2 (Y ⊔ T) := by
    rw [← hVsup]
    exact h.inf_centralizer_commutator_eq hY hYM
  have hcard72 : 72 ≤ ((Y ⊔ T) ⊓ Subgroup.centralizer
      ((⁅VZ T M, Y₁⁆ ⊔ ⁅VZ T M, Y₂⁆ : Subgroup G) : Set G)).relIndex (Y ⊔ T) := by
    rw [← hVsup, h.relIndex_sup_eq_mul hY hYM, hidx9]
    omega
  have hiso := quotientIso_wreath hcV₁ hcV₂ hVinf
    (fun g hg => hpermM g (h.sup_le_M hYM hg)) hker hcard72
  have hJM : thompsonJ T ≤ M := (thompsonJ_le_self T).trans h.T_le
  have hSM : baum T ≤ M := inf_le_left.trans h.T_le
  have hJN : ∀ {L : Subgroup (MulAut (IntMod (VZ T M) h.elem))}
      {f : MulAut (IntMod (VZ T M) h.elem)},
      L ∈ I → f ∈ L → orderOf f = 3 →
      thompsonJ T ≤ Subgroup.normalizer (h.ps (Subgroup.zpowers f) : Set G) :=
    fun hL hf hf3 j hj => mem_normalizer_psi h.elem h.le_normalizer (hJM hj)
      (h.conjAut_zpowers_of_thompsonJ B hL hf hf3 (convI_mem_autI h.elem hj _))
  have hS₁ : baum T ≤ Subgroup.normalizer (Y₁ : Set G) := by
    intro x' hx'
    rw [hY₁]
    exact mem_normalizer_psi h.elem h.le_normalizer (hSM hx')
      (conjAut_zpowers_eq B.hb s₁ (h.conjAut_baum B hL₁ hL₂ h12 hI'
        (convI_mem_autI h.elem hx' _)) hf₁ hf₁ h3₁ h3₁)
  have hS₂ : baum T ≤ Subgroup.normalizer (Y₂ : Set G) := by
    intro x' hx'
    rw [hY₂]
    exact mem_normalizer_psi h.elem h.le_normalizer (hSM hx')
      (conjAut_zpowers_eq B.hb s₂ (h.conjAut_baum B hL₂ hL₁ (Ne.symm h12)
        (fun L hL => (hI' L hL).symm) (convI_mem_autI h.elem hx' _)) hf₂ hf₂ h3₂ h3₂)
  have hcomm := (comm_of_mem_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂).1
  have hYN : ∀ {f : MulAut (IntMod (VZ T M) h.elem)},
      f ∈ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ →
      Y ≤ Subgroup.normalizer (h.ps (Subgroup.zpowers f) : Set G) := by
    intro f hf y hy
    refine mem_normalizer_psi h.elem h.le_normalizer (hYM hy) ?_
    have hyD : convI h.elem ⟨y, h.le_normalizer (hYM hy)⟩ ∈
        Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := hD ▸ h.convI_mem_autI' hy (hYM hy)
    rw [conjAut_eq_map, MonoidHom.map_zpowers]
    congr 1
    show convI h.elem ⟨y, h.le_normalizer (hYM hy)⟩ * f *
      (convI h.elem ⟨y, h.le_normalizer (hYM hy)⟩)⁻¹ = f
    rw [setLike_mul_comm hyD hf, mul_inv_cancel_right]
  refine Or.inr ⟨hidx9, hiso, Y₁, Y₂, hYeq, hY₁ ▸ psi_eq_oTwoUpper h.elem h.le_normalizer _,
    hY₂ ▸ psi_eq_oTwoUpper h.elem h.le_normalizer _, ?_, ?_, hVsup, hVinf, hcV₁, hcV₂, ?_, ?_,
    hS₁, hS₂, ?_, hidx4, ?_, ?_⟩
  · rw [hY₁, h.relIndex_ps hZ₁M ho₁ (by rw [hc₁]; exact hodd3), hc₁]
  · rw [hY₂, h.relIndex_ps hZ₂M ho₂ (by rw [hc₂]; exact hodd3), hc₂]
  · rw [hY₁]
    exact h.commutator_thompsonJ_ps hZ₁M ho₁ (hJN hL₁ hf₁ h3₁)
      (h.commutator_zpowers_thompsonJ B hL₁ hf₁ h3₁)
  · rw [hY₂]
    exact h.commutator_thompsonJ_ps hZ₂M ho₂ (hJN hL₂ hf₂ h3₂)
      (h.commutator_zpowers_thompsonJ B hL₂ hf₂ h3₂)
  · obtain ⟨σ, hσT, hσx⟩ := (mem_autI h.elem).1 hx
    refine ⟨σ, hσT, ?_⟩
    show Y₂ = cjSub (σ : G) Y₁
    rw [hY₁, hY₂, hcY _ (h.T_le hσT)]
    congr 1
    have e : (⟨(σ : G), h.le_normalizer (h.T_le hσT)⟩ : Subgroup.normalizer (VZ T M : Set G)) =
      σ := rfl
    rw [e, hσx, conjAut_zpowers_eq B.hb s₂ hxL hf₁ hf₂ h3₁ h3₂]
  · rw [hY₁]
    exact hYN (Subgroup.mem_sup_left (Subgroup.mem_zpowers f₁))
  · rw [hY₂]
    exact hYN (Subgroup.mem_sup_right (Subgroup.mem_zpowers f₂))

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
