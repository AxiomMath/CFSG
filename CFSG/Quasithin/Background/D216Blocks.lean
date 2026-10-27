module

public import CFSG.Quasithin.Background.D216Sub
public import CFSG.Quasithin.Background.D2Decomp

public section

namespace CFSG.Quasithin

section Elem

variable {V : Type*} [CommGroup V]

theorem mem_of_commV_le216 {G : Subgroup (MulAut V)} {U : Subgroup V} (h : commV G ≤ U)
    {g : MulAut V} (hg : g ∈ G) {u : V} (hu : u ∈ U) : g u ∈ U := by
  have h1 : g u * u⁻¹ ∈ commV G := Subgroup.subset_closure ⟨g, hg, u, rfl⟩
  have h2 : g u = (g u * u⁻¹) * u := by group
  rw [h2]
  exact U.mul_mem (h h1) hu

theorem apply_eq_of_commSub_eq_bot216 {G : Subgroup (MulAut V)} {U : Subgroup V}
    (h : commSub U G = ⊥) {g : MulAut V} (hg : g ∈ G) {u : V} (hu : u ∈ U) : g u = u :=
  (commSub_eq_bot_iff.mp h) hu g hg

theorem commute_of_split216 {G₁ G₂ : Subgroup (MulAut V)} {V₁ V₂ : Subgroup V}
    (hd : V₁ ⊔ V₂ = ⊤) (hc₁ : commV G₁ ≤ V₁) (hc₂ : commV G₂ ≤ V₂)
    (hz₁ : commSub V₂ G₁ = ⊥) (hz₂ : commSub V₁ G₂ = ⊥) :
    ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a := by
  intro a ha b hb
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ V₁ ⊔ V₂ := by rw [hd]; exact Subgroup.mem_top v
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
  have ha1 : a v₁ ∈ V₁ := mem_of_commV_le216 hc₁ ha hv₁
  have hb2 : b v₂ ∈ V₂ := mem_of_commV_le216 hc₂ hb hv₂
  have e1 : b v₁ = v₁ := apply_eq_of_commSub_eq_bot216 hz₂ hb hv₁
  have e2 : a v₂ = v₂ := apply_eq_of_commSub_eq_bot216 hz₁ ha hv₂
  have e3 : b (a v₁) = a v₁ := apply_eq_of_commSub_eq_bot216 hz₂ hb ha1
  have e4 : a (b v₂) = b v₂ := apply_eq_of_commSub_eq_bot216 hz₁ ha hb2
  show a (b (v₁ * v₂)) = b (a (v₁ * v₂))
  rw [map_mul, map_mul, map_mul, map_mul, e1, e2, e3, e4]

theorem inf_eq_bot_of_split216 {G₁ G₂ : Subgroup (MulAut V)} {V₁ V₂ : Subgroup V}
    (hd : V₁ ⊔ V₂ = ⊤) (hz₁ : commSub V₂ G₁ = ⊥) (hz₂ : commSub V₁ G₂ = ⊥) :
    G₁ ⊓ G₂ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ V₁ ⊔ V₂ := by rw [hd]; exact Subgroup.mem_top v
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
  have e1 : g v₁ = v₁ := apply_eq_of_commSub_eq_bot216 hz₂ hg.2 hv₁
  have e2 : g v₂ = v₂ := apply_eq_of_commSub_eq_bot216 hz₁ hg.1 hv₂
  show g (v₁ * v₂) = (1 : MulAut V) (v₁ * v₂)
  rw [map_mul, e1, e2]
  rfl


end Elem

section Blocks

variable {V : Type*} [CommGroup V] [Finite V]

omit [CommGroup V] [Finite V] in
theorem mem_sup_of_commute216 {H : Type*} [Group H] {K N : Subgroup H}
    (h : ∀ a ∈ K, ∀ b ∈ N, a * b = b * a) {x : H} (hx : x ∈ K ⊔ N) :
    ∃ a ∈ K, ∃ b ∈ N, x = a * b := by
  let S : Subgroup H :=
    { carrier := {x | ∃ a ∈ K, ∃ b ∈ N, x = a * b}
      one_mem' := ⟨1, K.one_mem, 1, N.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', K.mul_mem ha ha', b * b', N.mul_mem hb hb', ?_⟩
        have := h a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← this]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, K.inv_mem ha, b⁻¹, N.inv_mem hb, ?_⟩
        have := h a⁻¹ (K.inv_mem ha) b⁻¹ (N.inv_mem hb)
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := this.symm }
  have hK : K ≤ S := fun a ha => ⟨a, ha, 1, N.one_mem, by simp⟩
  have hN : N ≤ S := fun b hb => ⟨1, K.one_mem, b, hb, by simp⟩
  exact (sup_le hK hN) hx

open Classical in
structure IsBlocks216 (X : Subgroup (MulAut V)) (I : Finset (Subgroup (MulAut V))) : Prop where
  ne_bot : ∀ L ∈ I, L ≠ ⊥
  indec : ∀ L ∈ I, IsIndecomposablePair L
  sup_eq : X = ⨆ L ∈ I, L
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  indep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I.erase L, L' = ⊥
  indepV : ∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I.erase L, commV L' = ⊥
  triv : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → commV L ≤ fixV L'
  qstar : ∀ L ∈ I, QhatStar L = {A | A ∈ QhatStar X ∧ A ≤ L}
  cover : ∀ A ∈ QhatStar X, ∃ L ∈ I, A ≤ L

end Blocks

section BlocksUnion

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_mono216 {X X' : Subgroup (MulAut V)} (h : X ≤ X') : commV X ≤ commV X' := by
  rw [commV_eq_commSub, commV_eq_commSub]
  exact commSub_mono le_rfl h

open Classical in
theorem IsBlocks216.union {X G₁ G₂ : Subgroup (MulAut V)} {I₁ I₂ : Finset (Subgroup (MulAut V))}
    {V₁ V₂ : Subgroup V} (h₁ : IsBlocks216 G₁ I₁) (h₂ : IsBlocks216 G₂ I₂)
    (hd : V₁ ⊔ V₂ = ⊤) (hV : V₁ ⊓ V₂ = ⊥) (hc₁ : commV G₁ ≤ V₁) (hc₂ : commV G₂ ≤ V₂)
    (hz₁ : commSub V₂ G₁ = ⊥) (hz₂ : commSub V₁ G₂ = ⊥) (hX : X = G₁ ⊔ G₂)
    (hq₁ : QhatStar G₁ = {A | A ∈ QhatStar X ∧ A ≤ G₁})
    (hq₂ : QhatStar G₂ = {A | A ∈ QhatStar X ∧ A ≤ G₂})
    (hcov : ∀ A ∈ QhatStar X, A ≤ G₁ ∨ A ≤ G₂) : IsBlocks216 X (I₁ ∪ I₂) := by
  have hcomm12 := commute_of_split216 hd hc₁ hc₂ hz₁ hz₂
  have hinf := inf_eq_bot_of_split216 hd hz₁ hz₂
  have hLle₁ : ∀ L ∈ I₁, L ≤ G₁ := fun L hL =>
    h₁.sup_eq ▸ le_iSup₂ (f := fun L (_ : L ∈ I₁) => L) L hL
  have hLle₂ : ∀ L ∈ I₂, L ≤ G₂ := fun L hL =>
    h₂.sup_eq ▸ le_iSup₂ (f := fun L (_ : L ∈ I₂) => L) L hL
  have hdisj : ∀ L ∈ I₁, L ∉ I₂ := fun L hL1 hL2 =>
    h₁.ne_bot L hL1 (le_bot_iff.mp (hinf ▸ le_inf (hLle₁ L hL1) (hLle₂ L hL2)))
  have hdisj' : ∀ L ∈ I₂, L ∉ I₁ := fun L hL2 hL1 => hdisj L hL1 hL2
  have hVfix₁ : V₁ ≤ fixV G₂ := commSub_eq_bot_iff.mp hz₂
  have hVfix₂ : V₂ ≤ fixV G₁ := commSub_eq_bot_iff.mp hz₁
  have hcL₁ : ∀ L ∈ I₁, commV L ≤ V₁ := fun L hL => (commV_mono216 (hLle₁ L hL)).trans hc₁
  have hcL₂ : ∀ L ∈ I₂, commV L ≤ V₂ := fun L hL => (commV_mono216 (hLle₂ L hL)).trans hc₂
  refine
    { ne_bot := fun L hL => ?_
      indec := fun L hL => ?_
      sup_eq := ?_
      comm := fun L hL L' hL' hne a ha b hb => ?_
      indep := fun L hL => ?_
      indepV := fun L hL => ?_
      triv := fun L hL L' hL' hne => ?_
      qstar := fun L hL => ?_
      cover := fun A hA => ?_ }
  · rcases Finset.mem_union.1 hL with h | h
    exacts [h₁.ne_bot L h, h₂.ne_bot L h]
  · rcases Finset.mem_union.1 hL with h | h
    exacts [h₁.indec L h, h₂.indec L h]
  · rw [Finset.iSup_union, ← h₁.sup_eq, ← h₂.sup_eq, hX]
  · rcases Finset.mem_union.1 hL with h1 | h2 <;> rcases Finset.mem_union.1 hL' with h1' | h2'
    · exact h₁.comm L h1 L' h1' hne a ha b hb
    · exact hcomm12 a (hLle₁ L h1 ha) b (hLle₂ L' h2' hb)
    · exact (hcomm12 b (hLle₁ L' h1' hb) a (hLle₂ L h2 ha)).symm
    · exact h₂.comm L h2 L' h2' hne a ha b hb
  · rcases Finset.mem_union.1 hL with h1 | h2
    · rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hdisj L h1), Finset.iSup_union,
        ← h₂.sup_eq]
      have hAle : (⨆ L' ∈ I₁.erase L, L') ≤ G₁ :=
        iSup₂_le fun L' hL' => hLle₁ L' (Finset.mem_of_mem_erase hL')
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute216
        (K := ⨆ L' ∈ I₁.erase L, L') (N := G₂) (fun a ha b hb => hcomm12 a (hAle ha) b hb) hx.2
      have hbG₁ : b ∈ G₁ := by
        have := G₁.mul_mem (G₁.inv_mem (hAle ha)) (hLle₁ L h1 hx.1)
        simpa using this
      have hb1 : b = 1 := by
        have : b ∈ G₁ ⊓ G₂ := ⟨hbG₁, hb⟩
        rw [hinf] at this
        exact this
      have : a ∈ L ⊓ ⨆ L' ∈ I₁.erase L, L' := ⟨by simpa [hb1] using hx.1, ha⟩
      rw [h₁.indep L h1] at this
      simpa [hb1, this] using (Subgroup.mem_bot.mp this)
    · rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hdisj' L h2), Finset.iSup_union,
        ← h₁.sup_eq]
      have hBle : (⨆ L' ∈ I₂.erase L, L') ≤ G₂ :=
        iSup₂_le fun L' hL' => hLle₂ L' (Finset.mem_of_mem_erase hL')
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute216
        (K := G₁) (N := ⨆ L' ∈ I₂.erase L, L') (fun a ha b hb => hcomm12 a ha b (hBle hb)) hx.2
      have haG₂ : a ∈ G₂ := by
        have := G₂.mul_mem (hLle₂ L h2 hx.1) (G₂.inv_mem (hBle hb))
        simpa using this
      have ha1 : a = 1 := by
        have : a ∈ G₁ ⊓ G₂ := ⟨ha, haG₂⟩
        rw [hinf] at this
        exact this
      have : b ∈ L ⊓ ⨆ L' ∈ I₂.erase L, L' := ⟨by simpa [ha1] using hx.1, hb⟩
      rw [h₂.indep L h2] at this
      simpa [ha1, this] using (Subgroup.mem_bot.mp this)
  · rcases Finset.mem_union.1 hL with h1 | h2
    · rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hdisj L h1), Finset.iSup_union]
      have hA : (⨆ L' ∈ I₁.erase L, commV L') ≤ V₁ :=
        iSup₂_le fun L' hL' => hcL₁ L' (Finset.mem_of_mem_erase hL')
      have hB : (⨆ L' ∈ I₂, commV L') ≤ V₂ := iSup₂_le fun L' hL' => hcL₂ L' hL'
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hx.2
      have hbV : b ∈ V₁ ⊓ V₂ := by
        refine ⟨?_, hB hb⟩
        have : b = a⁻¹ * x := by rw [← hab]; group
        rw [this]
        exact V₁.mul_mem (V₁.inv_mem (hA ha)) (hcL₁ L h1 hx.1)
      rw [hV] at hbV
      have hb1 : b = 1 := hbV
      have hxa : x = a := by rw [← hab, hb1, mul_one]
      have : a ∈ commV L ⊓ ⨆ L' ∈ I₁.erase L, commV L' := ⟨hxa ▸ hx.1, ha⟩
      rw [h₁.indepV L h1] at this
      rw [hxa]
      exact this
    · rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (hdisj' L h2), Finset.iSup_union]
      have hA : (⨆ L' ∈ I₁, commV L') ≤ V₁ := iSup₂_le fun L' hL' => hcL₁ L' hL'
      have hB : (⨆ L' ∈ I₂.erase L, commV L') ≤ V₂ :=
        iSup₂_le fun L' hL' => hcL₂ L' (Finset.mem_of_mem_erase hL')
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hx.2
      have haV : a ∈ V₁ ⊓ V₂ := by
        refine ⟨hA ha, ?_⟩
        have : a = x * b⁻¹ := by rw [← hab]; group
        rw [this]
        exact V₂.mul_mem (hcL₂ L h2 hx.1) (V₂.inv_mem (hB hb))
      rw [hV] at haV
      have ha1 : a = 1 := haV
      have hxb : x = b := by rw [← hab, ha1, one_mul]
      have : b ∈ commV L ⊓ ⨆ L' ∈ I₂.erase L, commV L' := ⟨hxb ▸ hx.1, hb⟩
      rw [h₂.indepV L h2] at this
      rw [hxb]
      exact this
  · rcases Finset.mem_union.1 hL with h1 | h2 <;> rcases Finset.mem_union.1 hL' with h1' | h2'
    · exact h₁.triv L h1 L' h1' hne
    · exact (hcL₁ L h1).trans (hVfix₁.trans (fixV_anti (hLle₂ L' h2')))
    · exact (hcL₂ L h2).trans (hVfix₂.trans (fixV_anti (hLle₁ L' h1')))
    · exact h₂.triv L h2 L' h2' hne
  · rcases Finset.mem_union.1 hL with h1 | h2
    · rw [h₁.qstar L h1, hq₁]
      ext A
      exact ⟨fun ⟨⟨hA, _⟩, hAL⟩ => ⟨hA, hAL⟩, fun ⟨hA, hAL⟩ => ⟨⟨hA, hAL.trans (hLle₁ L h1)⟩, hAL⟩⟩
    · rw [h₂.qstar L h2, hq₂]
      ext A
      exact ⟨fun ⟨⟨hA, _⟩, hAL⟩ => ⟨hA, hAL⟩, fun ⟨hA, hAL⟩ => ⟨⟨hA, hAL.trans (hLle₂ L h2)⟩, hAL⟩⟩
  · rcases hcov A hA with h | h
    · have hA1 : A ∈ QhatStar G₁ := by rw [hq₁]; exact ⟨hA, h⟩
      obtain ⟨L, hL, hAL⟩ := h₁.cover A hA1
      exact ⟨L, Finset.mem_union_left _ hL, hAL⟩
    · have hA2 : A ∈ QhatStar G₂ := by rw [hq₂]; exact ⟨hA, h⟩
      obtain ⟨L, hL, hAL⟩ := h₂.cover A hA2
      exact ⟨L, Finset.mem_union_right _ hL, hAL⟩

end BlocksUnion

section BlocksExists

variable {V : Type*} [CommGroup V] [Finite V]

open Classical in
theorem exists_isBlocks216 {r : ℚ} (hr2 : r ≤ 2) :
    ∀ (X : Subgroup (MulAut V)), qhatOf X = (r : WithTop ℚ) → Jhat X = X →
      ∃ I : Finset (Subgroup (MulAut V)), IsBlocks216 X I := by
  have key : ∀ (n : ℕ) (X : Subgroup (MulAut V)), (QhatStar X).ncard = n →
      qhatOf X = (r : WithTop ℚ) → Jhat X = X →
      ∃ I : Finset (Subgroup (MulAut V)), IsBlocks216 X I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X hn hr hJ
      obtain ⟨A₀, hA₀⟩ := QhatStar_nonempty hr hr2
      have hXne : X ≠ ⊥ := fun hb => ne_bot_of_mem_QhatStar216 hA₀ (le_bot_iff.mp (hb ▸ le_of_mem_QhatStar216 hA₀))
      by_cases hdec : HasSumDecomposition X
      · obtain ⟨G₁, G₂, V₁, V₂, hG₁ne, hG₂ne, Q₁, Q₂, hQ, hdisj, hG₁, hG₂, hdir, hc₁, hc₂, hz₁, hz₂⟩ :=
          hdec
        have hQ₁sub : Q₁ ⊆ QhatStar X := fun A hA => by rw [hQ]; exact Or.inl hA
        have hQ₂sub : Q₂ ⊆ QhatStar X := fun A hA => by rw [hQ]; exact Or.inr hA
        have hQ₁ne : Q₁.Nonempty := by
          by_contra h
          rw [Set.not_nonempty_iff_eq_empty] at h
          apply hG₁ne
          rw [hG₁, h]
          simp
        have hQ₂ne : Q₂.Nonempty := by
          by_contra h
          rw [Set.not_nonempty_iff_eq_empty] at h
          apply hG₂ne
          rw [hG₂, h]
          simp
        have hG₁X : G₁ ≤ X := by
          rw [hG₁]; exact iSup₂_le fun A hA => le_of_mem_QhatStar216 (hQ₁sub hA)
        have hG₂X : G₂ ≤ X := by
          rw [hG₂]; exact iSup₂_le fun A hA => le_of_mem_QhatStar216 (hQ₂sub hA)
        have hle₁ : ∀ A ∈ Q₁, A ≤ G₁ := fun A hA => hG₁ ▸ le_iSup₂ (f := fun A (_ : A ∈ Q₁) => A) A hA
        have hle₂ : ∀ A ∈ Q₂, A ≤ G₂ := fun A hA => hG₂ ▸ le_iSup₂ (f := fun A (_ : A ∈ Q₂) => A) A hA
        have hinf := inf_eq_bot_of_split216 hdir.1 hz₁ hz₂
        obtain ⟨A₁, hA₁⟩ := hQ₁ne
        obtain ⟨A₂, hA₂⟩ := hQ₂ne
        have hq₁ : QhatStar G₁ = Q₁ := by
          rw [QhatStar_of_le216 hr hr2 (hQ₁sub hA₁) (hle₁ A₁ hA₁) hG₁X]
          ext A
          constructor
          · rintro ⟨hA, hAG⟩
            rcases (hQ ▸ hA : A ∈ Q₁ ∪ Q₂) with h | h
            · exact h
            · exfalso
              have : A ≤ G₁ ⊓ G₂ := le_inf hAG (hle₂ A h)
              rw [hinf] at this
              exact ne_bot_of_mem_QhatStar216 hA (le_bot_iff.mp this)
          · intro h
            exact ⟨hQ₁sub h, hle₁ A h⟩
        have hq₂ : QhatStar G₂ = Q₂ := by
          rw [QhatStar_of_le216 hr hr2 (hQ₂sub hA₂) (hle₂ A₂ hA₂) hG₂X]
          ext A
          constructor
          · rintro ⟨hA, hAG⟩
            rcases (hQ ▸ hA : A ∈ Q₁ ∪ Q₂) with h | h
            · exfalso
              have : A ≤ G₁ ⊓ G₂ := le_inf (hle₁ A h) hAG
              rw [hinf] at this
              exact ne_bot_of_mem_QhatStar216 hA (le_bot_iff.mp this)
            · exact h
          · intro h
            exact ⟨hQ₂sub h, hle₂ A h⟩
        have hqq₁ : QhatStar G₁ = {A | A ∈ QhatStar X ∧ A ≤ G₁} := QhatStar_of_le216 hr hr2 (hQ₁sub hA₁) (hle₁ A₁ hA₁) hG₁X
        have hqq₂ : QhatStar G₂ = {A | A ∈ QhatStar X ∧ A ≤ G₂} := QhatStar_of_le216 hr hr2 (hQ₂sub hA₂) (hle₂ A₂ hA₂) hG₂X
        have hfin : (QhatStar X).Finite := Set.toFinite _
        have hlt₁ : (QhatStar G₁).ncard < n := by
          rw [hq₁, ← hn]
          refine Set.ncard_lt_ncard ⟨hQ₁sub, fun h => ?_⟩ hfin
          have : A₂ ∈ Q₁ := h (hQ₂sub hA₂)
          exact absurd hdisj (Set.not_disjoint_iff.mpr ⟨A₂, this, hA₂⟩)
        have hlt₂ : (QhatStar G₂).ncard < n := by
          rw [hq₂, ← hn]
          refine Set.ncard_lt_ncard ⟨hQ₂sub, fun h => ?_⟩ hfin
          have : A₁ ∈ Q₂ := h (hQ₁sub hA₁)
          exact absurd hdisj (Set.not_disjoint_iff.mpr ⟨A₁, hA₁, this⟩)
        have hr₁ := qhatOf_eq_of_le216 hr (hQ₁sub hA₁) (hle₁ A₁ hA₁) hG₁X
        have hr₂ := qhatOf_eq_of_le216 hr (hQ₂sub hA₂) (hle₂ A₂ hA₂) hG₂X
        have hJ₁ := Jhat_eq_of_gen216 hr hr2 hQ₁sub ⟨A₁, hA₁⟩ hG₁
        have hJ₂ := Jhat_eq_of_gen216 hr hr2 hQ₂sub ⟨A₂, hA₂⟩ hG₂
        obtain ⟨I₁, hI₁⟩ := ih _ hlt₁ G₁ rfl hr₁ hJ₁
        obtain ⟨I₂, hI₂⟩ := ih _ hlt₂ G₂ rfl hr₂ hJ₂
        have hXsup : X = G₁ ⊔ G₂ := by
          have : X = ⨆ A ∈ QhatStar X, A := hJ.symm
          rw [this, hQ, iSup_union, ← hG₁, ← hG₂]
        refine ⟨I₁ ∪ I₂, IsBlocks216.union hI₁ hI₂ hdir.1 hdir.2 hc₁ hc₂ hz₁ hz₂ hXsup hqq₁ hqq₂ ?_⟩
        intro A hA
        rcases (hQ ▸ hA : A ∈ Q₁ ∪ Q₂) with h | h
        · exact Or.inl (hle₁ A h)
        · exact Or.inr (hle₂ A h)
      · refine ⟨{X}, ?_⟩
        refine
          { ne_bot := fun L hL => ?_
            indec := fun L hL => ?_
            sup_eq := ?_
            comm := fun L hL L' hL' hne => ?_
            indep := fun L hL => ?_
            indepV := fun L hL => ?_
            triv := fun L hL L' hL' hne => ?_
            qstar := fun L hL => ?_
            cover := fun A hA => ?_ }
        · rw [Finset.mem_singleton] at hL
          rw [hL]; exact hXne
        · rw [Finset.mem_singleton] at hL
          rw [hL]; exact ⟨hJ.symm, hdec⟩
        · simp
        · rw [Finset.mem_singleton] at hL hL'
          exact absurd (hL.trans hL'.symm) hne
        · rw [Finset.mem_singleton] at hL
          subst hL
          simp
        · rw [Finset.mem_singleton] at hL
          subst hL
          simp
        · rw [Finset.mem_singleton] at hL hL'
          exact absurd (hL.trans hL'.symm) hne
        · rw [Finset.mem_singleton] at hL
          subst hL
          ext A
          exact ⟨fun h => ⟨h, le_of_mem_QhatStar216 h⟩, fun h => h.1⟩
        · exact ⟨X, Finset.mem_singleton_self X, le_of_mem_QhatStar216 hA⟩
  intro X hr hJ
  exact key _ X rfl hr hJ

end BlocksExists

end CFSG.Quasithin
