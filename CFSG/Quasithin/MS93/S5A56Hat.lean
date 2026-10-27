module

public import CFSG.Quasithin.MS93.S5A56
public import CFSG.Quasithin.MS93.MSPLevi
public import CFSG.Quasithin.MS93.S5A56Sp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5

section Groups

variable {Γ : Type*} [Group Γ]

theorem sq_mem_and_commutator_mem {A Q : Subgroup Γ} (hAQ : A ≤ Subgroup.normalizer (Q : Set Γ))
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA2 : ∀ a ∈ A, a * a = 1) {x y : Γ}
    (hx : x ∈ A ⊔ Q) (hy : y ∈ A ⊔ Q) : x * x ∈ Q ∧ x * y * x⁻¹ * y⁻¹ ∈ Q := by
  have hx' : x ∈ ((A ⊔ Q : Subgroup Γ) : Set Γ) := hx
  have hy' : y ∈ ((A ⊔ Q : Subgroup Γ) : Set Γ) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A Q hAQ] at hx' hy'
  obtain ⟨a, ha, q, hq, rfl⟩ := hx'
  obtain ⟨a', ha', q', hq', rfl⟩ := hy'
  have hc : ∀ {g : Γ}, g ∈ A → ∀ {r : Γ}, r ∈ Q → g * r * g⁻¹ ∈ Q := fun hg r hr =>
    (Subgroup.mem_normalizer_iff.1 (hAQ hg) r).1 hr
  have hc' : ∀ {g : Γ}, g ∈ A → ∀ {r : Γ}, r ∈ Q → g⁻¹ * r * g ∈ Q := fun hg r hr => by
    have := hc (A.inv_mem hg) hr
    rwa [inv_inv] at this
  refine ⟨?_, ?_⟩
  · have e : a * q * (a * q) = (a⁻¹ * q * a) * q := by
      have h2 : a * a = 1 := hA2 a ha
      calc a * q * (a * q) = a * a * (a⁻¹ * q * a) * q := by group
        _ = (a⁻¹ * q * a) * q := by rw [h2, one_mul]
    rw [e]
    exact mul_mem (hc' ha hq) hq
  · have e : a * q * (a' * q') * (a * q)⁻¹ * (a' * q')⁻¹ =
        (a * a') * ((a'⁻¹ * q * a') * q' * q⁻¹ * (a⁻¹ * q'⁻¹ * a)) * (a * a')⁻¹ := by
      have hcomm : a * a' = a' * a := hA a ha a' ha'
      calc a * q * (a' * q') * (a * q)⁻¹ * (a' * q')⁻¹ =
          a * a' * ((a'⁻¹ * q * a') * q' * q⁻¹ * (a⁻¹ * q'⁻¹ * a)) * (a' * a)⁻¹ := by group
        _ = _ := by rw [hcomm]
    rw [e]
    refine hc (A.mul_mem ha ha') (mul_mem (mul_mem (mul_mem (hc' ha' hq) hq') (Q.inv_mem hq))
      (hc' ha (Q.inv_mem hq')))

theorem conj_eq_or_of_le_closure_sup {A Q Z : Subgroup Γ}
    (hAQ : A ≤ Subgroup.normalizer (Q : Set Γ)) (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hA2 : ∀ a ∈ A, a * a = 1) (hQZ : Q ≤ Subgroup.centralizer (Z : Set Γ)) {t₁ t₂ : Γ}
    (ht₁ : t₁ ∈ A ⊔ Q) (ht₂ : t₂ ∈ A ⊔ Q) (hA12 : A ≤ Subgroup.closure ({t₁, t₂} : Set Γ) ⊔ Q)
    (hZ₁ : t₁ ∈ Subgroup.normalizer (Z : Set Γ)) {z : Γ} (hz : z ∈ Z) (hz₂ : t₂ * z = z * t₂)
    {b : Γ} (hb : b ∈ A) : b * z * b⁻¹ = z ∨ b * z * b⁻¹ = t₁ * z * t₁⁻¹ := by
  set z' := t₁ * z * t₁⁻¹ with hz'
  have hz'Z : z' ∈ Z := (Subgroup.mem_normalizer_iff.1 hZ₁ z).1 hz
  have hq : ∀ q ∈ Q, ∀ w ∈ Z, q * w * q⁻¹ = w := fun q hq w hw => by
    rw [← Subgroup.mem_centralizer_iff.1 (hQZ hq) w hw, mul_inv_cancel_right]
  let S : Subgroup Γ :=
    { carrier := {g | (g * z * g⁻¹ = z ∧ g * z' * g⁻¹ = z') ∨
        (g * z * g⁻¹ = z' ∧ g * z' * g⁻¹ = z)}
      one_mem' := Or.inl ⟨by group, by group⟩
      mul_mem' := by
        rintro g k (⟨hg1, hg2⟩ | ⟨hg1, hg2⟩) (⟨hk1, hk2⟩ | ⟨hk1, hk2⟩)
        · refine Or.inl ⟨?_, ?_⟩
          · rw [show g * k * z * (g * k)⁻¹ = g * (k * z * k⁻¹) * g⁻¹ by group, hk1, hg1]
          · rw [show g * k * z' * (g * k)⁻¹ = g * (k * z' * k⁻¹) * g⁻¹ by group, hk2, hg2]
        · refine Or.inr ⟨?_, ?_⟩
          · rw [show g * k * z * (g * k)⁻¹ = g * (k * z * k⁻¹) * g⁻¹ by group, hk1, hg2]
          · rw [show g * k * z' * (g * k)⁻¹ = g * (k * z' * k⁻¹) * g⁻¹ by group, hk2, hg1]
        · refine Or.inr ⟨?_, ?_⟩
          · rw [show g * k * z * (g * k)⁻¹ = g * (k * z * k⁻¹) * g⁻¹ by group, hk1, hg1]
          · rw [show g * k * z' * (g * k)⁻¹ = g * (k * z' * k⁻¹) * g⁻¹ by group, hk2, hg2]
        · refine Or.inl ⟨?_, ?_⟩
          · rw [show g * k * z * (g * k)⁻¹ = g * (k * z * k⁻¹) * g⁻¹ by group, hk1, hg2]
          · rw [show g * k * z' * (g * k)⁻¹ = g * (k * z' * k⁻¹) * g⁻¹ by group, hk2, hg1]
      inv_mem' := by
        rintro g (⟨hg1, hg2⟩ | ⟨hg1, hg2⟩)
        · refine Or.inl ⟨?_, ?_⟩
          · nth_rw 1 [← hg1]
            group
          · nth_rw 1 [← hg2]
            group
        · refine Or.inr ⟨?_, ?_⟩
          · nth_rw 1 [← hg2]
            group
          · nth_rw 1 [← hg1]
            group }
  have hQS : Q ≤ S := fun q hq' => Or.inl ⟨hq q hq' z hz, hq q hq' z' hz'Z⟩
  have h₁S : t₁ ∈ S := by
    refine Or.inr ⟨rfl, ?_⟩
    have h11 := (sq_mem_and_commutator_mem hAQ hA hA2 ht₁ ht₁).1
    rw [hz', show t₁ * (t₁ * z * t₁⁻¹) * t₁⁻¹ = (t₁ * t₁) * z * (t₁ * t₁)⁻¹ by group,
      hq _ h11 z hz]
  have h₂S : t₂ ∈ S := by
    refine Or.inl ⟨by rw [hz₂, mul_inv_cancel_right], ?_⟩
    have hc := (sq_mem_and_commutator_mem hAQ hA hA2 ht₂ ht₁).2
    have e : t₂ * z' * t₂⁻¹ = (t₂ * t₁ * t₂⁻¹ * t₁⁻¹) * (t₁ * (t₂ * z * t₂⁻¹) * t₁⁻¹) *
        (t₂ * t₁ * t₂⁻¹ * t₁⁻¹)⁻¹ := by
      rw [hz']
      group
    rw [e, hz₂, mul_inv_cancel_right, ← hz', hq _ hc z' hz'Z]
  have hle : Subgroup.closure ({t₁, t₂} : Set Γ) ⊔ Q ≤ S := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) hQS
    rintro t (rfl | rfl)
    · exact h₁S
    · exact h₂S
  rcases hle (hA12 hb) with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

theorem relIndex_centralizer_le_two_of_conj {A : Subgroup Γ} {z z' : Γ}
    (h : ∀ b ∈ A, b * z * b⁻¹ = z ∨ b * z * b⁻¹ = z') :
    (Subgroup.centralizer ({z} : Set Γ)).relIndex A ≤ 2 := by
  have hC : ∀ {b : Γ}, b ∈ Subgroup.centralizer ({z} : Set Γ) ↔ b * z * b⁻¹ = z := by
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hb
      rw [hb, mul_inv_cancel_right]
    · intro hb
      calc b * z = b * z * b⁻¹ * b := by group
        _ = z * b := by rw [hb]
  by_cases hall : ∀ b ∈ A, b * z * b⁻¹ = z
  · rw [Subgroup.relIndex_eq_one.2 fun b hb => hC.2 (hall b hb)]
    norm_num
  push Not at hall
  obtain ⟨b₀, hb₀, hb₀z⟩ := hall
  have hb₀' : b₀ * z * b₀⁻¹ = z' := (h b₀ hb₀).resolve_left hb₀z
  have hzz' : z' ≠ z := hb₀' ▸ hb₀z
  refine le_of_eq (Subgroup.index_eq_two_iff.2 ⟨⟨b₀, hb₀⟩, fun ⟨b, hb⟩ => ?_⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hbb := h (b * b₀) (A.mul_mem hb hb₀)
  rw [show b * b₀ * z * (b * b₀)⁻¹ = b * (b₀ * z * b₀⁻¹) * b⁻¹ by group, hb₀'] at hbb
  rw [hC, hC, show b * b₀ * z * (b * b₀)⁻¹ = b * (b₀ * z * b₀⁻¹) * b⁻¹ by group, hb₀']
  rcases h b hb with hbz | hbz
  ·
    have hbz' : b * z' * b⁻¹ = z' := by
      rcases hbb with h1 | h1
      · exfalso
        apply hzz'
        calc z' = b⁻¹ * (b * z' * b⁻¹) * b := by group
          _ = b⁻¹ * (b * z * b⁻¹) * b := by rw [h1, hbz]
          _ = z := by group
      · exact h1
    rw [hbz', hbz]
    exact Or.inr ⟨rfl, hzz'⟩
  ·
    have hbz' : b * z' * b⁻¹ = z := by
      rcases hbb with h1 | h1
      · exact h1
      · exfalso
        apply hzz'
        have e1 : z = b⁻¹ * (b * z * b⁻¹) * b := by group
        have e2 : z' = b⁻¹ * (b * z' * b⁻¹) * b := by group
        rw [e1, e2, hbz, h1]
    rw [hbz', hbz]
    exact Or.inl ⟨rfl, hzz'⟩

end Groups

section Trans

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_transv_of_relIndex_le_two (h : PUHyp M T L) (hd : IsSp4Data M T L k F a)
    (hq : Nat.card F = 2) {s : ↥M} (hs : a s ≠ 1)
    (hrel : (Subgroup.centralizer ({(s : G)} : Set G)).relIndex (Z0q M T) ≤ 2) :
    ∃ v : MSP.V4 F, v ≠ 0 ∧ a s = MSP.transv v 1 := by
  have := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  set E : Subgroup G := Subgroup.closure {(s : G)}
  have hCE : Subgroup.centralizer (E : Set G) = Subgroup.centralizer ({(s : G)} : Set G) :=
    Subgroup.centralizer_closure _
  have hne : (Subgroup.centralizer ({(s : G)} : Set G)).relIndex (Z0q M T) ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have hUrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≤ 2 := by
    rw [hCE]
    exact (Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) hne).trans hrel
  have hsE : a s ∈ imSp a E := mem_imSp.2 ⟨s, Subgroup.subset_closure rfl, s.2, rfl⟩
  have hcard := nv.card_le_relIndex E
  rw [MSP.card_V4, MSP.card_fixSp, hq] at hcard
  have hd4 : Module.finrank F (MSP.fixSp (imSp a E)) ≠ 4 := by
    intro h4
    have htop : MSP.fixSp (imSp a E) = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4]; simp)
    rw [MSP.fixSp_eq_top_iff] at htop
    exact hs (by rw [htop] at hsE; exact hsE)
  have hdle : Module.finrank F (MSP.fixSp (imSp a E)) ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp (imSp a E))
    simpa using this
  have hd3 : Module.finrank F (MSP.fixSp (imSp a E)) = 3 := by
    have h16 : 2 ^ 4 ≤ 2 ^ Module.finrank F (MSP.fixSp (imSp a E)) * 2 :=
      hcard.trans (Nat.mul_le_mul_left _ hUrel)
    have h3 : 3 ≤ Module.finrank F (MSP.fixSp (imSp a E)) := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ Module.finrank F (MSP.fixSp (imSp a E)) * 2 ≤ 2 ^ 2 * 2 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    omega
  obtain ⟨p, hp, -, hEp⟩ := MSP.exists_point_of_finrank_fixSp_three hd3
  obtain ⟨v, hv, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
  obtain ⟨c, hc⟩ := (MSP.mem_xPoint_span hv).1 (hEp hsE)
  rcases eq_zero_or_eq_one_of_card_two hq c with rfl | rfl
  · exact absurd (by rw [← hc, MSP.transv_zero]) hs
  · exact ⟨v, hv, hc.symm⟩

omit [Fintype F] in
theorem xPoint_span_le_of_card_two (hq : Nat.card F = 2) {v : MSP.V4 F} (hv : v ≠ 0)
    {K : Subgroup ↥(StatedSp 2 F)} (hK : MSP.transv v 1 ∈ K) : MSP.xPoint (F ∙ v) ≤ K := by
  intro g hg
  obtain ⟨c, rfl⟩ := (MSP.mem_xPoint_span hv).1 hg
  rcases eq_zero_or_eq_one_of_card_two hq c with rfl | rfl
  · rw [MSP.transv_zero]
    exact one_mem K
  · exact hK

omit [Fintype F] in
theorem form_eq_zero_of_commute_transv [CharP F 2] {u v : MSP.V4 F} (hu : u ≠ 0)
    (h : MSP.transv u 1 * MSP.transv v 1 = MSP.transv v 1 * MSP.transv u 1) :
    MSP.form F u v = 0 := by
  have hv := MSP.mulVec_eq_of_commute_transv (g := MSP.transv v 1) hu h.symm
  rw [MSP.transv_mulVec, add_eq_left, one_mul, smul_eq_zero] at hv
  rcases hv with hv | rfl
  · rw [← neg_eq_zero, ← MSP.form_swap]
    exact hv
  · exact map_zero _

omit [Fintype F] in
theorem eq_add_of_form_eq_zero [CharP F 2] (hq : Nat.card F = 2) {c₁ c₂ c : MSP.V4 F}
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) (h₁₂ : c₁ ≠ c₂) (hf : MSP.form F c₁ c₂ = 0) (hc : c ≠ 0)
    (hc₁ : MSP.form F c₁ c = 0) (hc₂ : MSP.form F c₂ c = 0) (hne₁ : c ≠ c₁) (hne₂ : c ≠ c₂) :
    c = c₁ + c₂ := by
  set W := Submodule.span F ({c₁, c₂} : Set (MSP.V4 F)) with hW
  have h01 := eq_zero_or_eq_one_of_card_two hq
  have hind : LinearIndependent F ![c₁, c₂] := by
    rw [LinearIndependent.pair_iff]
    intro x y hxy
    rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp only [zero_smul, one_smul, zero_add] at hxy
      exact absurd hxy h₂
    · simp only [zero_smul, one_smul, add_zero] at hxy
      exact absurd hxy h₁
    · simp only [one_smul] at hxy
      exact absurd (CharTwo.add_eq_zero.1 hxy) h₁₂
  have hW2 : Module.finrank F W = 2 := by
    have := finrank_span_eq_card hind
    rw [Fintype.card_fin] at this
    rwa [hW, ← Matrix.range_cons_cons_empty]
  have hperp : ∀ v : MSP.V4 F, MSP.form F c₁ v = 0 → MSP.form F c₂ v = 0 → v ∈ MSP.perp W := by
    intro v hv₁ hv₂
    refine MSP.mem_perp.2 fun w hw => ?_
    obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.1 hw
    simp [hv₁, hv₂]
  have hWle : W ≤ MSP.perp W := fun w hw => by
    obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.1 hw
    refine hperp _ ?_ ?_
    · simp [MSP.form_self, hf]
    · simp [MSP.form_self, MSP.form_swap c₁ c₂, hf]
  have heq : MSP.perp W = W := by
    refine (Submodule.eq_of_le_of_finrank_eq hWle ?_).symm
    have := MSP.finrank_perp W
    omega
  have hcW : c ∈ W := heq ▸ hperp c hc₁ hc₂
  obtain ⟨x, y, rfl⟩ := Submodule.mem_span_pair.1 hcW
  rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl
  · simp at hc
  · simp at hne₂
  · simp at hne₁
  · simp

end Trans

section Alpha

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

include h in
theorem relIndex_zm_le_two_of_pair {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') {t t' : (puAmalgam h.le).Universal}
    (ht : t ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1))
    (h12 : ZM _ (baseA (puAmalgam h.le)) ⊔ Qv _ α' =
      Subgroup.closure ({t, t'} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α')
    {z : (puAmalgam h.le).Universal} (hz : z ∈ ZM (puAmalgam h.le) α') (hz' : t' * z = z * t') :
    (Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal)).relIndex
      (ZM (puAmalgam h.le) (baseA _)) ≤ 2 := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hcr' := ms22_iii _ hyp hb0 h.centHyp hc
  have hZαst : ZM (puAmalgam h.le) (baseA _) ≤ stab _ α' :=
    zm_le_stab_of_isCritical _ hyp hb0 hcr'
  have hab := isElemAbelian_zm _ hyp hb0 (isMVtx_baseA (puAmalgam h.le))
  have hA : ∀ b ∈ ZM (puAmalgam h.le) (baseA _), ∀ b' ∈ ZM (puAmalgam h.le) (baseA _),
      b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hA2 : ∀ b ∈ ZM (puAmalgam h.le) (baseA _), b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact hab.2 b hb
  have hQZ : Qv _ α' ≤ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _) :=
    (qv_le_centralizer_xm _ α').trans (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hα'))
  have hmem : ∀ s ∈ ({t, t'} : Set (puAmalgam h.le).Universal),
      s ∈ ZM _ (baseA (puAmalgam h.le)) ⊔ Qv _ α' := fun s hs => by
    rw [h12]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure hs)
  have htst : t ∈ stab _ α' :=
    qv_le_stab_of_adj _ (adj_geo_one_of_isCritical _ hb0 hcr').symm ht
  exact relIndex_centralizer_le_two_of_conj (z' := t * z * t⁻¹) fun b hb =>
    conj_eq_or_of_le_closure_sup (hZαst.trans (stab_le_normalizer_qv _ α')) hA hA2 hQZ
      (hmem t (by simp)) (hmem t' (by simp)) (le_sup_left.trans h12.le)
      (stab_le_normalizer_zm _ α' htst) hz hz' hb

theorem hat_shape (hd : IsSp4Data M T L k F a) (hq : Nat.card F = 2)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {t₁ t₂ t₃ : (puAmalgam h.le).Universal}
    (ht : IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃)
    (hZh : zHat _ (baseA (puAmalgam h.le)) α' =
      ZM _ α' ⊓ Subgroup.centralizer ({t₃} : Set (puAmalgam h.le).Universal))
    (hZ4 : 4 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α')) :
    ∃ v₁ v₂ : MSP.V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧ MSP.form F v₁ v₂ = 0 ∧
      MSP.transv v₁ 1 ∈ vIm h.le a (ZM _ α') ∧ MSP.transv v₂ 1 ∈ vIm h.le a (ZM _ α') ∧
      (MSP.transv v₁ 1 ∈ vIm h.le a (zHat _ (baseA _) α') ∨
        MSP.transv v₂ 1 ∈ vIm h.le a (zHat _ (baseA _) α') ∨
        MSP.transv v₁ 1 * MSP.transv v₂ 1 ∈ vIm h.le a (zHat _ (baseA _) α')) := by
  have := hd.charP
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  obtain ⟨ht₁, ht₂, -, hi₁, hi₂, hi₃, -, h12, -⟩ := ht
  have h21 : ZM _ (baseA (puAmalgam h.le)) ⊔ Qv _ α' =
      Subgroup.closure ({t₂, t₁} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
    rw [Set.pair_comm]
    exact h12
  set Z' := ZM (puAmalgam h.le) α' with hZ'
  set C₁ := Subgroup.centralizer ({t₁} : Set (puAmalgam h.le).Universal) with hC₁
  set C₂ := Subgroup.centralizer ({t₂} : Set (puAmalgam h.le).Universal) with hC₂
  set C₃ := Subgroup.centralizer ({t₃} : Set (puAmalgam h.le).Universal) with hC₃
  have hZst : Z' ≤ stab (puAmalgam h.le) (baseA _) := zm_le_stab_of_isCritical _ hyp hb0 hc
  have hZ2 : IsPGroup 2 Z' := by
    have hadj := adj_geo_one_of_isCritical _ hb0 hc
    have hnot : ¬ IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 1) :=
      (isMVtx_iff_of_adj _ hadj).1 (isMVtx_baseA _)
    exact (isPGroup_qv _ hyp hnot).to_le (zm_le_qv_geo_one _ hyp hb0 hc)
  have hab := isElemAbelian_zm _ hyp hb0 hα'
  have hQZ : Qv _ α' ≤ Subgroup.centralizer (Z' : Set _) :=
    (qv_le_centralizer_xm _ α').trans (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hα'))
  have hst : stab (puAmalgam h.le) (baseA _) = (puAmalgam h.le).ofA.range :=
    (ofA_range_eq h.le).symm
  have hpre : ∀ w ∈ Z', ∃ m : ↥M, (puAmalgam h.le).ofA m = w := fun w hw => by
    have := hZst hw
    rw [hst] at this
    exact this
  have hmemC : ∀ {w u : (puAmalgam h.le).Universal},
      w ∈ Subgroup.centralizer ({u} : Set _) ↔ u * w = w * u := fun {w u} => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  have hker₁ : ∀ m : ↥M, (puAmalgam h.le).ofA m ∈ Z' → (puAmalgam h.le).ofA m ∈ C₁ →
      (puAmalgam h.le).ofA m ∈ C₂ → a m = 1 := by
    intro m hmZ hm₁ hm₂
    have hcent : Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ≤
        Subgroup.centralizer ({(puAmalgam h.le).ofA m} : Set _) := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) fun q hq => ?_
      · rintro u (rfl | rfl)
        · exact hmemC.2 (hmemC.1 hm₁).symm
        · exact hmemC.2 (hmemC.1 hm₂).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (hQZ hq) _ hmZ).symm
    have hZc := (le_sup_left.trans h12.le).trans hcent
    have hmZ0 : (m : G) ∈ Subgroup.centralizer (Z0q M T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (puAmalgam h.le).ofA ⟨y, Z0q_le M T hy⟩ ∈ ZM (puAmalgam h.le) (baseA _) := by
        rw [hZα]
        exact ⟨⟨y, Z0q_le M T hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 (hZc hy')
      rw [← map_mul, ← map_mul] at this
      exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective this)
    obtain ⟨hm', hm1⟩ := (mem_kerG a).1 (hd.centralizer_Z0q_le_kerG h m.2 hmZ0)
    exact hm1
  have hker₂ : ∀ m : ↥M, (puAmalgam h.le).ofA m ∈ Z' → a m = 1 →
      (puAmalgam h.le).ofA m ∈ C₁ ∧ (puAmalgam h.le).ofA m ∈ C₂ := by
    intro m hmZ hm1
    have hmk : (m : G) ∈ kerG a := (mem_kerG a).2 ⟨m.2, hm1⟩
    have hmZ0 := hd.kerG_le_centralizer_Z0q h hmk
    have hcent : ZM (puAmalgam h.le) (baseA _) ⊔ Qv _ α' ≤
        Subgroup.centralizer ({(puAmalgam h.le).ofA m} : Set _) := by
      refine sup_le (fun y hy => ?_) fun q hq => ?_
      · rw [hZα] at hy
        obtain ⟨y', hy', rfl⟩ := hy
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hmZ0 _
          (Subgroup.mem_subgroupOf.1 hy'))
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (hQZ hq) _ hmZ).symm
    have hle := h12.symm.le.trans hcent
    refine ⟨hmemC.2 ?_, hmemC.2 ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_sup_left
        (Subgroup.subset_closure (show t₁ ∈ ({t₁, t₂} : Set _) by simp))))
    · exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_sup_left
        (Subgroup.subset_closure (show t₂ ∈ ({t₁, t₂} : Set _) by simp))))
  have hkerQ : ∀ m : ↥M, (puAmalgam h.le).ofA m ∈ Z' → a m = 1 →
      (puAmalgam h.le).ofA m ∈ Qv (puAmalgam h.le) (baseA _) := by
    intro m hmZ hm1
    have hmk : (m : G) ∈ kerG a := (mem_kerG a).2 ⟨m.2, hm1⟩
    obtain ⟨e, he⟩ := hZ2 ⟨_, hmZ⟩
    have hm2 : (m : G) ^ 2 ^ e = 1 := by
      have h1 : (puAmalgam h.le).ofA (m ^ 2 ^ e) = (puAmalgam h.le).ofA 1 := by
        rw [map_pow, map_one]
        simpa using congrArg Subtype.val he
      have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
      simpa using h2
    rw [qv_baseA_eq h]
    exact ⟨m, Subgroup.mem_subgroupOf.2 (hd.mem_pCoreOf_of_mem_kerG h hmk ⟨e, hm2⟩), rfl⟩
  have htrans : ∀ m : ↥M, (puAmalgam h.le).ofA m ∈ Z' → a m ≠ 1 →
      ((puAmalgam h.le).ofA m ∈ C₁ ∨ (puAmalgam h.le).ofA m ∈ C₂) →
      ∃ v : MSP.V4 F, v ≠ 0 ∧ a m = MSP.transv v 1 := by
    intro m hmZ hm1 hmC
    have hrel : (Subgroup.centralizer ({(puAmalgam h.le).ofA m} : Set _)).relIndex
        (ZM (puAmalgam h.le) (baseA _)) ≤ 2 := by
      rcases hmC with hm | hm
      · exact relIndex_zm_le_two_of_pair h hc ht₂ h21 hmZ (hmemC.1 hm)
      · exact relIndex_zm_le_two_of_pair h hc ht₁ h12 hmZ (hmemC.1 hm)
    rw [hZα, S5B.relIndex_centralizer_ofA h.le (Z0q_le M T) m] at hrel
    exact exists_transv_of_relIndex_le_two h hd hq hm1 hrel
  have hsmall : ∀ C : Subgroup (puAmalgam h.le).Universal, C.relIndex Z' = 2 →
      ¬ (∀ w ∈ Z', w ∈ C → w ∈ Qv (puAmalgam h.le) (baseA _)) := by
    intro C hC hall
    have hle : C ⊓ Z' ≤ Qv (puAmalgam h.le) (baseA _) := fun w hw => hall w hw.2 hw.1
    have h0 : (C ⊓ Z').relIndex Z' ≠ 0 := by rw [Subgroup.inf_relIndex_right, hC]; norm_num
    have := Subgroup.relIndex_le_of_le_left hle h0
    rw [Subgroup.inf_relIndex_right, hC] at this
    omega
  have hex : ∀ {C C' : Subgroup (puAmalgam h.le).Universal}, C = C₁ ∧ C' = C₂ ∨ C = C₂ ∧ C' = C₁ →
      ∃ z ∈ Z', z ∈ C' ∧ z ∉ C := by
    intro C C' hCC'
    by_contra hno
    push Not at hno
    refine hsmall C' (by rcases hCC' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption) fun w hw hwC' => ?_
    obtain ⟨m, rfl⟩ := hpre w hw
    refine hkerQ m hw (hker₁ m hw ?_ ?_)
    · rcases hCC' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hno _ hw hwC'
      · exact hwC'
    · rcases hCC' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hwC'
      · exact hno _ hw hwC'
  obtain ⟨z₁, hz₁Z, hz₁₂, hz₁₁⟩ := hex (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨z₂, hz₂Z, hz₂₁, hz₂₂⟩ := hex (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨m₁, rfl⟩ := hpre z₁ hz₁Z
  obtain ⟨m₂, rfl⟩ := hpre z₂ hz₂Z
  have ha₁ : a m₁ ≠ 1 := fun h1 => hz₁₁ (hker₂ m₁ hz₁Z h1).1
  have ha₂ : a m₂ ≠ 1 := fun h1 => hz₂₂ (hker₂ m₂ hz₂Z h1).2
  obtain ⟨v₁, hv₁, he₁⟩ := htrans m₁ hz₁Z ha₁ (Or.inr hz₁₂)
  obtain ⟨v₂, hv₂, he₂⟩ := htrans m₂ hz₂Z ha₂ (Or.inl hz₂₁)
  have hrelI : ∀ C : Subgroup (puAmalgam h.le).Universal, C.relIndex Z' = 2 →
      ∀ {x y}, x ∈ Z' → y ∈ Z' → x ∉ C → y ∉ C → x⁻¹ * y ∈ C := fun C hC x y hx hy hxC hyC =>
    S5B.inv_mul_mem_of_relIndex_le_two hC.le (by rw [hC]; norm_num) hx hy hxC hyC
  have heq : ∀ m m' : ↥M, (puAmalgam h.le).ofA m ∈ Z' → (puAmalgam h.le).ofA m' ∈ Z' →
      ((puAmalgam h.le).ofA m)⁻¹ * (puAmalgam h.le).ofA m' ∈ C₁ →
      ((puAmalgam h.le).ofA m)⁻¹ * (puAmalgam h.le).ofA m' ∈ C₂ → a m = a m' := by
    intro m m' hm hm' h1 h2
    have e : ((puAmalgam h.le).ofA m)⁻¹ * (puAmalgam h.le).ofA m' =
        (puAmalgam h.le).ofA (m⁻¹ * m') := by rw [map_mul, map_inv]
    rw [e] at h1 h2
    have hZ : (puAmalgam h.le).ofA (m⁻¹ * m') ∈ Z' := by
      rw [← e]
      exact mul_mem (inv_mem hm) hm'
    have := hker₁ _ hZ h1 h2
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hv₁₂ : v₁ ≠ v₂ := by
    rintro rfl
    have hm : a m₁ = a m₂ := by rw [he₁, he₂]
    have hk : a (m₁⁻¹ * m₂) = 1 := by rw [map_mul, map_inv, hm, inv_mul_cancel]
    have hZ : (puAmalgam h.le).ofA (m₁⁻¹ * m₂) ∈ Z' := by
      rw [map_mul, map_inv]
      exact mul_mem (inv_mem hz₁Z) hz₂Z
    have h1 := (hker₂ _ hZ hk).1
    rw [map_mul, map_inv] at h1
    apply hz₁₁
    have := mul_mem h1 (inv_mem hz₂₁)
    rw [mul_inv_cancel_right] at this
    exact inv_mem_iff.1 this
  have hform : MSP.form F v₁ v₂ = 0 := by
    refine form_eq_zero_of_commute_transv hv₁ ?_
    rw [← he₁, ← he₂, ← map_mul, ← map_mul]
    congr 1
    refine (puAmalgam h.le).ofA_injective ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨_, hz₁Z⟩ ⟨_, hz₂Z⟩)
  have hvIm : ∀ m : ↥M, (puAmalgam h.le).ofA m ∈ Z' → a m ∈ vIm h.le a Z' :=
    fun m hm => ⟨m, hm, rfl⟩
  refine ⟨v₁, v₂, hv₁, hv₂, hv₁₂, hform, he₁ ▸ hvIm m₁ hz₁Z, he₂ ▸ hvIm m₂ hz₂Z, ?_⟩
  obtain ⟨w, hwZ, hw₃, hwa⟩ : ∃ w ∈ Z', w ∈ C₃ ∧
      ∀ m : ↥M, (puAmalgam h.le).ofA m = w → a m ≠ 1 := by
    by_contra hno
    push Not at hno
    refine hsmall C₃ hi₃ fun w hw hw₃ => ?_
    obtain ⟨m, hm, hm1⟩ := hno w hw hw₃
    exact hm ▸ hkerQ m (hm ▸ hw) hm1
  obtain ⟨mw, rfl⟩ := hpre w hwZ
  have hwa' := hwa mw rfl
  have hwZh : (puAmalgam h.le).ofA mw ∈ zHat _ (baseA (puAmalgam h.le)) α' := by
    rw [hZh]
    exact ⟨hwZ, hw₃⟩
  have hwIm : a mw ∈ vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') := ⟨mw, hwZh, rfl⟩
  by_cases hw₁ : (puAmalgam h.le).ofA mw ∈ C₁ <;> by_cases hw₂ : (puAmalgam h.le).ofA mw ∈ C₂
  · exact absurd (hker₁ mw hwZ hw₁ hw₂) hwa'
  ·
    right; left
    have hm := heq mw m₂ hwZ hz₂Z (mul_mem (inv_mem hw₁) hz₂₁) (hrelI C₂ hi₂ hwZ hz₂Z hw₂ hz₂₂)
    rw [← he₂, ← hm]
    exact hwIm
  ·
    left
    have hm := heq mw m₁ hwZ hz₁Z (hrelI C₁ hi₁ hwZ hz₁Z hw₁ hz₁₁) (mul_mem (inv_mem hw₂) hz₁₂)
    rw [← he₁, ← hm]
    exact hwIm
  ·
    right; right
    set y := ((puAmalgam h.le).ofA mw)⁻¹ * (puAmalgam h.le).ofA m₁ with hy
    have hy₁ : y ∈ C₁ := hrelI C₁ hi₁ hwZ hz₁Z hw₁ hz₁₁
    have hy₂ : y ∉ C₂ := fun hy₂ => hw₂ (by
      have := mul_mem hz₁₂ (inv_mem hy₂)
      rwa [hy, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at this)
    have hyZ : y ∈ Z' := mul_mem (inv_mem hwZ) hz₁Z
    have hym : y = (puAmalgam h.le).ofA (mw⁻¹ * m₁) := by rw [hy, map_mul, map_inv]
    rw [hym] at hy₁ hy₂ hyZ
    have hm := heq (mw⁻¹ * m₁) m₂ hyZ hz₂Z (mul_mem (inv_mem hy₁) hz₂₁)
      (hrelI C₂ hi₂ hyZ hz₂Z hy₂ hz₂₂)
    have hwv : a mw = MSP.transv v₁ 1 * MSP.transv v₂ 1 := by
      rw [map_mul, map_inv, he₁, he₂] at hm
      have e2 : (MSP.transv v₂ 1)⁻¹ = MSP.transv v₂ 1 := by
        rw [MSP.transv_inv, CharTwo.neg_eq]
      calc a mw = (a mw)⁻¹⁻¹ := (inv_inv _).symm
        _ = (MSP.transv v₂ 1 * (MSP.transv v₁ 1)⁻¹)⁻¹ := by
          rw [← hm]
          group
        _ = MSP.transv v₁ 1 * MSP.transv v₂ 1 := by
          rw [_root_.mul_inv_rev, inv_inv, e2]
    rw [← hwv]
    exact hwIm

end Alpha

section AlphaPrime

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

theorem map_eq_one_of_ofA_mem_qv (hd : IsSp4Data M T L k F a) {m : ↥M}
    (hm : (puAmalgam h.le).ofA m ∈ Qv (puAmalgam h.le) (baseA _)) : a m = 1 := by
  rw [qv_baseA_eq h] at hm
  obtain ⟨m', hm', he⟩ := hm
  rw [(puAmalgam h.le).ofA_injective he] at hm'
  obtain ⟨hmM, h1⟩ := (mem_kerG a).1 (hd.pCoreOf_le_kerG h (Subgroup.mem_subgroupOf.1 hm'))
  exact h1

theorem ofA_mem_qv_of_map_eq_one (hd : IsSp4Data M T L k F a) {m : ↥M} (hm1 : a m = 1)
    {K : Subgroup (puAmalgam h.le).Universal} (hK : IsPGroup 2 K)
    (hmK : (puAmalgam h.le).ofA m ∈ K) :
    (puAmalgam h.le).ofA m ∈ Qv (puAmalgam h.le) (baseA _) := by
  have hmk : (m : G) ∈ kerG a := (mem_kerG a).2 ⟨m.2, hm1⟩
  obtain ⟨e, he⟩ := hK ⟨_, hmK⟩
  have hm2 : (m : G) ^ 2 ^ e = 1 := by
    have h1 : (puAmalgam h.le).ofA (m ^ 2 ^ e) = (puAmalgam h.le).ofA 1 := by
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val he
    have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
    simpa using h2
  rw [qv_baseA_eq h]
  exact ⟨m, Subgroup.mem_subgroupOf.2 (hd.mem_pCoreOf_of_mem_kerG h hmk ⟨e, hm2⟩), rfl⟩

theorem hat_centers (hd : IsSp4Data M T L k F a) (hq : Nat.card F = 2)
    {μ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ (baseA (puAmalgam h.le)))
    {t₁ t₂ t₃ : (puAmalgam h.le).Universal}
    (ht : IsHatTriple _ μ (baseA (puAmalgam h.le)) t₁ t₂ t₃) :
    ∃ c₁ c₂ : MSP.V4 F, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ c₁ ≠ c₂ ∧ MSP.form F c₁ c₂ = 0 ∧
      (∀ m : ↥M, (puAmalgam h.le).ofA m = t₁ → a m = MSP.transv c₁ 1) ∧
      (∀ m : ↥M, (puAmalgam h.le).ofA m = t₂ → a m = MSP.transv c₂ 1) ∧
      ∀ s₁ s₂ s₃ : (puAmalgam h.le).Universal, IsHatTriple _ μ (baseA _) s₁ s₂ s₃ →
        s₃ ∉ Subgroup.closure ({s₁, s₂} : Set (puAmalgam h.le).Universal) ⊔
          Qv _ (baseA (puAmalgam h.le)) →
        ∀ m : ↥M, (puAmalgam h.le).ofA m = s₃ → a m = MSP.transv (c₁ + c₂) 1 := by
  have := hd.charP
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hcr := ms22_iii _ hyp hb0 h.centHyp hc
  obtain ⟨ht₁, ht₂, -, hi₁, hi₂, -, h12n, h12, -⟩ := ht
  set A := ZM (puAmalgam h.le) μ with hAdef
  set Z := ZM (puAmalgam h.le) (baseA _) with hZdef
  set Q := Qv (puAmalgam h.le) (baseA _) with hQdef
  set T' := Qv (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) μ 1) with hT'
  set R := critR (puAmalgam h.le) μ (baseA _) with hR
  have hadj := adj_geo_one_of_isCritical _ hb0 hcr
  have hT'st : T' ≤ stab (puAmalgam h.le) (baseA _) := qv_le_stab_of_adj _ hadj.symm
  have hT'2 : IsPGroup 2 T' :=
    isPGroup_qv _ hyp ((isMVtx_iff_of_adj _ hadj).1 (isMVtx_baseA _))
  have hAst : A ≤ stab (puAmalgam h.le) (baseA _) := zm_le_stab_of_isCritical _ hyp hb0 hcr
  have hAQ : A ≤ Subgroup.normalizer (Q : Set _) := hAst.trans (stab_le_normalizer_qv _ _)
  have habA := isElemAbelian_zm _ hyp hb0 hc.1
  have hA : ∀ b ∈ A, ∀ b' ∈ A, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (habA.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hA2 : ∀ b ∈ A, b * b = 1 := fun b hb => by
    rw [← pow_two]
    exact habA.2 b hb
  have hQZ : Q ≤ Subgroup.centralizer (Z : Set _) :=
    (qv_le_centralizer_xm _ _).trans
      (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 (isMVtx_baseA _)))
  have hst : stab (puAmalgam h.le) (baseA _) = (puAmalgam h.le).ofA.range :=
    (ofA_range_eq h.le).symm
  have hpre : ∀ w ∈ T', ∃ m : ↥M, (puAmalgam h.le).ofA m = w := fun w hw => by
    have := hT'st hw
    rw [hst] at this
    exact this
  have hZα : Z = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  have hAQm : ∀ s ∈ ({t₁, t₂} : Set (puAmalgam h.le).Universal), s ∈ A ⊔ Q := fun s hs => by
    rw [h12]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure hs)
  have htv : ∀ {t : (puAmalgam h.le).Universal}, t ∈ T' →
      (Subgroup.centralizer ({t} : Set _)).relIndex Z = 2 →
      ∃ m : ↥M, (puAmalgam h.le).ofA m = t ∧ ∃ v : MSP.V4 F, v ≠ 0 ∧ a m = MSP.transv v 1 := by
    intro t htT hi
    obtain ⟨m, rfl⟩ := hpre t htT
    rw [hZα, S5B.relIndex_centralizer_ofA h.le (Z0q_le M T) m] at hi
    refine ⟨m, rfl, exists_transv_of_relIndex_le_two h hd hq (fun h1 => ?_) hi.le⟩
    have hmZ := hd.kerG_le_centralizer_Z0q h ((mem_kerG a).2 ⟨m.2, h1⟩)
    rw [Subgroup.relIndex_eq_one.2 fun y hy => ?_] at hi
    · exact absurd hi (by norm_num)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hmZ y hy)
  obtain ⟨m₁, rfl, c₁, hc₁, he₁⟩ := htv ht₁ hi₁
  obtain ⟨m₂, rfl, c₂, hc₂, he₂⟩ := htv ht₂ hi₂
  have hmodQ : ∀ m m' : ↥M, (puAmalgam h.le).ofA m ∈ T' → (puAmalgam h.le).ofA m' ∈ T' →
      a m = a m' → (puAmalgam h.le).ofA m ∈ Q ⊔ Subgroup.closure {(puAmalgam h.le).ofA m'} := by
    intro m m' hm hm' he
    have h1 : a (m * m'⁻¹) = 1 := by rw [map_mul, map_inv, he, mul_inv_cancel]
    have hT : (puAmalgam h.le).ofA (m * m'⁻¹) ∈ T' := by
      rw [map_mul, map_inv]
      exact mul_mem hm (inv_mem hm')
    have hq' := ofA_mem_qv_of_map_eq_one h hd h1 hT'2 hT
    have e : (puAmalgam h.le).ofA m =
        (puAmalgam h.le).ofA (m * m'⁻¹) * (puAmalgam h.le).ofA m' := by
      rw [map_mul, map_inv, inv_mul_cancel_right]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hq') (Subgroup.mem_sup_right (Subgroup.subset_closure rfl))
  have hc₁₂ : c₁ ≠ c₂ := by
    rintro rfl
    apply h12n
    have h1 : a (m₁ * m₂⁻¹) = 1 := by rw [map_mul, map_inv, he₁, he₂, mul_inv_cancel]
    have hT : (puAmalgam h.le).ofA (m₁ * m₂⁻¹) ∈ T' := by
      rw [map_mul, map_inv]
      exact mul_mem ht₁ (inv_mem ht₂)
    have := ofA_mem_qv_of_map_eq_one h hd h1 hT'2 hT
    rwa [map_mul, map_inv] at this
  have hform : MSP.form F c₁ c₂ = 0 := by
    refine form_eq_zero_of_commute_transv hc₁ ?_
    have hcq := (sq_mem_and_commutator_mem hAQ hA hA2
      (hAQm _ (show (puAmalgam h.le).ofA m₁ ∈ ({(puAmalgam h.le).ofA m₁,
        (puAmalgam h.le).ofA m₂} : Set _) by simp))
      (hAQm _ (show (puAmalgam h.le).ofA m₂ ∈ ({(puAmalgam h.le).ofA m₁,
        (puAmalgam h.le).ofA m₂} : Set _) by simp))).2
    have e : (puAmalgam h.le).ofA m₁ * (puAmalgam h.le).ofA m₂ * ((puAmalgam h.le).ofA m₁)⁻¹ *
        ((puAmalgam h.le).ofA m₂)⁻¹ = (puAmalgam h.le).ofA (m₁ * m₂ * m₁⁻¹ * m₂⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e] at hcq
    have h1 := map_eq_one_of_ofA_mem_qv h hd hcq
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, he₁, he₂] at h1
    calc MSP.transv c₁ 1 * MSP.transv c₂ 1 =
        (MSP.transv c₁ 1 * MSP.transv c₂ 1 * (MSP.transv c₁ 1)⁻¹ * (MSP.transv c₂ 1)⁻¹) *
          (MSP.transv c₂ 1 * MSP.transv c₁ 1) := by group
      _ = MSP.transv c₂ 1 * MSP.transv c₁ 1 := by rw [h1, one_mul]
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hdecomp : ∀ {x : (puAmalgam h.le).Universal}, x ∈ A ⊔ Q → ∃ b ∈ A, ∃ q ∈ Q, x = b * q :=
    fun {x} hx => by
      have hx' : x ∈ ((A ⊔ Q : Subgroup _) : Set _) := hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right A Q hAQ] at hx'
      obtain ⟨b, hb, q, hq', rfl⟩ := hx'
      exact ⟨b, hb, q, hq', rfl⟩
  have hfixc : ∀ {m : ↥M} {c : MSP.V4 F}, (puAmalgam h.le).ofA m ∈ A ⊔ Q →
      a m = MSP.transv c 1 → c ≠ 0 → ∀ y : ↥M,
      (puAmalgam h.le).ofA y ∈ Subgroup.centralizer (R : Set _) → MSP.mat (a y) *ᵥ c = c := by
    intro m c hmAQ hmc hc0 y hy
    obtain ⟨w, hw⟩ := MSP.exists_form_eq_one hc0
    obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd w)
    have huv : nv.vec u = w := by rw [NatVec.vec, hu]; rfl
    have hmu : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn m.2) u).1 u.2
    set d : ↥(Uq M T L) := ⟨(m : G) * u * (m : G)⁻¹, hmu⟩ * u⁻¹ with hd'
    have hdv : nv.vec d = c := by
      rw [hd', nv.vec_mul, nv.vec_inv, nv.vec_conj m u hmu, huv, hmc, MSP.transv_mulVec, hw,
        one_mul, one_smul]
      abel
    have huM : (u : G) ∈ M := Uq_le h.L_le u.2
    have huZ : (puAmalgam h.le).ofA ⟨u, huM⟩ ∈ Z := by
      rw [hZα]
      exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.2 (Uq_le_Z0q h.L_le u.2), rfl⟩
    have hdM : (d : G) ∈ M := Uq_le h.L_le d.2
    have hdR : (puAmalgam h.le).ofA ⟨d, hdM⟩ ∈ R := by
      obtain ⟨b, hb, q, hq', hbq⟩ := hdecomp hmAQ
      have hqu : q * (puAmalgam h.le).ofA ⟨u, huM⟩ * q⁻¹ = (puAmalgam h.le).ofA ⟨u, huM⟩ := by
        rw [← Subgroup.mem_centralizer_iff.1 (hQZ hq') _ huZ, mul_inv_cancel_right]
      have e : (puAmalgam h.le).ofA ⟨d, hdM⟩ = ⁅b, (puAmalgam h.le).ofA ⟨u, huM⟩⁆ := by
        have e1 : (⟨d, hdM⟩ : ↥M) = m * ⟨u, huM⟩ * m⁻¹ * ⟨u, huM⟩⁻¹ := Subtype.ext rfl
        rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hbq, commutatorElement_def]
        calc b * q * (puAmalgam h.le).ofA ⟨u, huM⟩ * (b * q)⁻¹ *
              ((puAmalgam h.le).ofA ⟨u, huM⟩)⁻¹ =
            b * (q * (puAmalgam h.le).ofA ⟨u, huM⟩ * q⁻¹) * b⁻¹ *
              ((puAmalgam h.le).ofA ⟨u, huM⟩)⁻¹ := by group
          _ = _ := by rw [hqu]
      rw [e]
      exact Subgroup.commutator_mem_commutator hb huZ
    have hyd : (y : G) * d = d * y := by
      have := Subgroup.mem_centralizer_iff.1 hy _ hdR
      rw [← map_mul, ← map_mul] at this
      exact (congrArg Subtype.val ((puAmalgam h.le).ofA_injective this)).symm
    have := nv.mat_mulVec_vec_of_commute y d hyd
    rwa [hdv] at this
  have hfix₁ := @hfixc m₁ c₁ (hAQm _ (by simp)) he₁ hc₁
  have hfix₂ := @hfixc m₂ c₂ (hAQm _ (show (puAmalgam h.le).ofA m₂ ∈
    ({(puAmalgam h.le).ofA m₁, (puAmalgam h.le).ofA m₂} : Set _) by simp)) he₂ hc₂
  have hthird : ∀ {m₀ : ↥M} {c₀ : MSP.V4 F} {s₁ s₂ : (puAmalgam h.le).Universal},
      (puAmalgam h.le).ofA m₀ ∈ T' → a m₀ = MSP.transv c₀ 1 → c₀ ≠ 0 →
      T' ⊓ Subgroup.centralizer (R : Set _) ⊔ Q =
        Subgroup.closure ({s₁, s₂, (puAmalgam h.le).ofA m₀} : Set _) ⊔ Q →
      A ⊔ Q = Subgroup.closure ({s₁, s₂} : Set _) ⊔ Q →
      (puAmalgam h.le).ofA m₀ ∉ Subgroup.closure ({s₁, s₂} : Set _) ⊔ Q → c₀ = c₁ + c₂ := by
    intro m₀ c₀ s₁ s₂ hm₀T he₀ hc₀ h3 h2 hn₀
    have hmem : (puAmalgam h.le).ofA m₀ ∈ T' ⊓ Subgroup.centralizer (R : Set _) ⊔ Q := by
      rw [h3]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    have hKQ : T' ⊓ Subgroup.centralizer (R : Set _) ≤ Subgroup.normalizer (Q : Set _) :=
      inf_le_left.trans (hT'st.trans (stab_le_normalizer_qv _ _))
    have hmem' : (puAmalgam h.le).ofA m₀ ∈
        ((T' ⊓ Subgroup.centralizer (R : Set _) ⊔ Q : Subgroup _) : Set _) := hmem
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ Q hKQ] at hmem'
    obtain ⟨y, ⟨hyT, hyR⟩, q, hq', hyq⟩ := hmem'
    obtain ⟨my, rfl⟩ := hpre y hyT
    obtain ⟨mq, rfl⟩ : ∃ mq : ↥M, (puAmalgam h.le).ofA mq = q := by
      have := (qv_le_stab _ _).trans hst.le hq'
      exact this
    have hmq := map_eq_one_of_ofA_mem_qv h hd hq'
    have he : a m₀ = a my := by
      have hyq' : (puAmalgam h.le).ofA my * (puAmalgam h.le).ofA mq =
          (puAmalgam h.le).ofA m₀ := hyq
      rw [← map_mul] at hyq'
      rw [← (puAmalgam h.le).ofA_injective hyq', map_mul, hmq, mul_one]
    have hf₀ : ∀ c : MSP.V4 F, MSP.mat (a my) *ᵥ c = c → MSP.form F c₀ c = 0 := by
      intro c hcf
      rw [← he, he₀, MSP.transv_mulVec, add_eq_left, one_mul, smul_eq_zero] at hcf
      exact hcf.resolve_right hc₀
    have hne : ∀ {m' : ↥M} {c' : MSP.V4 F}, (puAmalgam h.le).ofA m' ∈ T' →
        (puAmalgam h.le).ofA m' ∈ A ⊔ Q → a m' = MSP.transv c' 1 → c₀ ≠ c' := by
      rintro m' c' hm'T hm'AQ he' rfl
      apply hn₀
      have hmod := hmodQ m₀ m' hm₀T hm'T (by rw [he₀, he'])
      rw [← h2]
      exact (sup_le le_sup_right ((Subgroup.closure_le _).2 (by
        rintro _ rfl
        exact hm'AQ))) hmod
    have hc₀₁ := hf₀ c₁ (hfix₁ my hyR)
    have hc₀₂ := hf₀ c₂ (hfix₂ my hyR)
    rw [MSP.form_swap, neg_eq_zero] at hc₀₁ hc₀₂
    exact eq_add_of_form_eq_zero hq hc₁ hc₂ hc₁₂ hform hc₀ hc₀₁ hc₀₂
      (hne ht₁ (hAQm _ (by simp)) he₁)
      (hne ht₂ (hAQm _ (show (puAmalgam h.le).ofA m₂ ∈
        ({(puAmalgam h.le).ofA m₁, (puAmalgam h.le).ofA m₂} : Set _) by simp)) he₂)
  refine ⟨c₁, c₂, hc₁, hc₂, hc₁₂, hform, fun m hm => ?_, fun m hm => ?_, ?_⟩
  · rw [(puAmalgam h.le).ofA_injective hm]
    exact he₁
  · rw [(puAmalgam h.le).ofA_injective hm]
    exact he₂
  · intro s₁ s₂ s₃ hs hsn m hm
    obtain ⟨-, -, hs₃, -, -, hsi₃, -, hs12, hs123⟩ := hs
    subst hm
    obtain ⟨m', hm', c₀, hc₀, he₀⟩ := htv hs₃ hsi₃
    rw [(puAmalgam h.le).ofA_injective hm'] at he₀
    rw [he₀, hthird hs₃ he₀ hc₀ hs123 hs12 hsn]

theorem zm_inf_centralizer_le_of_isHatTriple (hd : IsSp4Data M T L k F a) (hq : Nat.card F = 2)
    {μ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ (baseA (puAmalgam h.le)))
    {t₁ t₂ t₃ t₁' t₂' t₃' : (puAmalgam h.le).Universal}
    (ht : IsHatTriple _ μ (baseA (puAmalgam h.le)) t₁ t₂ t₃)
    (hn : t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔
      Qv _ (baseA (puAmalgam h.le)))
    (ht' : IsHatTriple _ μ (baseA (puAmalgam h.le)) t₁' t₂' t₃')
    (hn' : t₃' ∉ Subgroup.closure ({t₁', t₂'} : Set (puAmalgam h.le).Universal) ⊔
      Qv _ (baseA (puAmalgam h.le))) :
    ZM (puAmalgam h.le) (baseA _) ⊓ Subgroup.centralizer ({t₃} : Set _) ≤
      Subgroup.centralizer ({t₃'} : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hcr := ms22_iii _ hyp hb0 h.centHyp hc
  obtain ⟨c₁, c₂, -, -, -, -, -, -, h3cl⟩ := hat_centers h hd hq hc ht
  have hadj := adj_geo_one_of_isCritical _ hb0 hcr
  have hst : stab (puAmalgam h.le) (baseA _) = (puAmalgam h.le).ofA.range :=
    (ofA_range_eq h.le).symm
  have hpre : ∀ w ∈ Qv (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) μ 1),
      ∃ m : ↥M, (puAmalgam h.le).ofA m = w := fun w hw => by
    have := (qv_le_stab_of_adj _ hadj.symm).trans hst.le hw
    exact this
  have hZα : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  obtain ⟨m₃, rfl⟩ := hpre t₃ ht.2.2.1
  obtain ⟨m₃', rfl⟩ := hpre t₃' ht'.2.2.1
  have h3 := h3cl _ _ _ ht hn m₃ rfl
  have h3' := h3cl _ _ _ ht' hn' m₃' rfl
  have hk : a (m₃' * m₃⁻¹) = 1 := by rw [map_mul, map_inv, h3, h3', mul_inv_cancel]
  have hkZ := hd.kerG_le_centralizer_Z0q h ((mem_kerG a).2 ⟨(m₃' * m₃⁻¹).2, hk⟩)
  rintro z ⟨hzZ, hz₃⟩
  rw [hZα] at hzZ
  obtain ⟨y, hy, rfl⟩ := hzZ
  have hy' : (y : G) ∈ Z0q M T := Subgroup.mem_subgroupOf.1 hy
  set K := (puAmalgam h.le).ofA (m₃' * m₃⁻¹) with hK
  have hcK : (puAmalgam h.le).ofA y * K = K * (puAmalgam h.le).ofA y := by
    rw [hK, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hkZ _ hy')
  have hc3 := Subgroup.mem_centralizer_singleton_iff.1 hz₃
  have e : (puAmalgam h.le).ofA m₃' = K * (puAmalgam h.le).ofA m₃ := by
    rw [hK, map_mul, map_inv, inv_mul_cancel_right]
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  rw [e]
  calc (puAmalgam h.le).ofA y * (K * (puAmalgam h.le).ofA m₃) =
      ((puAmalgam h.le).ofA y * K) * (puAmalgam h.le).ofA m₃ := by group
    _ = K * ((puAmalgam h.le).ofA y * (puAmalgam h.le).ofA m₃) := by rw [hcK]; group
    _ = K * ((puAmalgam h.le).ofA m₃ * (puAmalgam h.le).ofA y) := by rw [hc3]
    _ = K * (puAmalgam h.le).ofA m₃ * (puAmalgam h.le).ofA y := by group

omit [Finite G] in
theorem conj_mem_closure_pair_sup_qv {X : GoldAmalgam (↥M) (↥T) (Hol ↥T)} (g : X.Universal)
    (α' : Vtx X) (t₁ t₂ t : X.Universal) :
    g * t * g⁻¹ ∈ Subgroup.closure ({g * t₁ * g⁻¹, g * t₂ * g⁻¹} : Set X.Universal) ⊔
        Qv X (g • α') ↔ t ∈ Subgroup.closure ({t₁, t₂} : Set X.Universal) ⊔ Qv X α' := by
  have hcl : Subgroup.closure ({g * t₁ * g⁻¹, g * t₂ * g⁻¹} : Set X.Universal) =
      (Subgroup.closure ({t₁, t₂} : Set X.Universal)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure]
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [hcl, qv_smul, ← Subgroup.map_sup, PU.mem_map_conj]
  simp [mul_assoc]

theorem zHat_eq_of_isHatTriple (hd : IsSp4Data M T L k F a) (hq : Nat.card F = 2)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {t₁ t₂ t₃ : (puAmalgam h.le).Universal}
    (ht : IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃)
    (hn : t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α') :
    zHat _ (baseA (puAmalgam h.le)) α' =
      ZM _ α' ⊓ Subgroup.centralizer ({t₃} : Set (puAmalgam h.le).Universal) := by
  refine le_antisymm (le_inf inf_le_left (zHat_le_centralizer ht hn)) ?_
  refine le_inf inf_le_left (le_iInf fun τ => le_iInf fun hτ => le_iInf fun hτn => ?_)
  obtain ⟨c, hc'⟩ := exists_eq_smul_baseA _ (hc.isMVtx_right _ h.hyp20)
  have hgα' : c⁻¹ • α' = baseA (puAmalgam h.le) := by rw [hc', inv_smul_smul]
  have hcrit : IsCritical _ (c⁻¹ • baseA (puAmalgam h.le)) (baseA _) := by
    have := (isCritical_smul _ c⁻¹ _ _).2 hc
    rwa [hgα'] at this
  have hT := (isHatTriple_smul _ c⁻¹ _ _ t₁ t₂ t₃).2 ht
  have hT' := (isHatTriple_smul _ c⁻¹ _ _ τ.1 τ.2.1 τ.2.2).2 hτ
  rw [hgα'] at hT hT'
  have hN := (conj_mem_closure_pair_sup_qv c⁻¹ α' t₁ t₂ t₃).not.2 hn
  have hN' := (conj_mem_closure_pair_sup_qv c⁻¹ α' τ.1 τ.2.1 τ.2.2).not.2 hτn
  rw [hgα'] at hN hN'
  have key := zm_inf_centralizer_le_of_isHatTriple h hd hq hcrit hT hN hT' hN'
  rintro z ⟨hzZ, hz₃⟩
  have hzZ' : c⁻¹ * z * c⁻¹⁻¹ ∈ ZM (puAmalgam h.le) (baseA _) := by
    rw [← hgα', zm_smul]
    exact ⟨z, hzZ, rfl⟩
  have hz₃' : c⁻¹ * z * c⁻¹⁻¹ ∈ Subgroup.centralizer ({c⁻¹ * t₃ * c⁻¹⁻¹} : Set _) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have := Subgroup.mem_centralizer_singleton_iff.1 hz₃
    calc c⁻¹ * z * c⁻¹⁻¹ * (c⁻¹ * t₃ * c⁻¹⁻¹) = c⁻¹ * (z * t₃) * c⁻¹⁻¹ := by group
      _ = c⁻¹ * (t₃ * z) * c⁻¹⁻¹ := by rw [this]
      _ = c⁻¹ * t₃ * c⁻¹⁻¹ * (c⁻¹ * z * c⁻¹⁻¹) := by group
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 (key ⟨hzZ', hz₃'⟩)
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  calc z * τ.2.2 = c * ((c⁻¹ * z * c⁻¹⁻¹) * (c⁻¹ * τ.2.2 * c⁻¹⁻¹)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * τ.2.2 * c⁻¹⁻¹) * (c⁻¹ * z * c⁻¹⁻¹)) * c⁻¹ := by rw [h1]
    _ = τ.2.2 * z := by group

end AlphaPrime

end S5

end CFSG.Quasithin.MS93
