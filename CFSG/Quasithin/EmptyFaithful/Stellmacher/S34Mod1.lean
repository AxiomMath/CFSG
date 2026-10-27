module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34ModDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Fe
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolTrace

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher

namespace S34

theorem faithful_of_alt_ne_top {Q : Model 5} (h : fixW Q (alternatingGroup (Fin 5)) ≠ ⊤) :
    Q.Faithful := by
  have hker : ∀ σ, Q.act σ = 1 → σ = 1 := by
    intro σ hσ
    have hKn : (Q.act.ker).Normal := MonoidHom.normal_ker _
    have hn : (Q.act.ker.subgroupOf (alternatingGroup (Fin 5))).Normal := hKn.subgroupOf _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Q.act.ker.subgroupOf (alternatingGroup (Fin 5))) with hb | ht
    · have hc : ∀ g : Perm (Fin 5), σ * g = g * σ := by
        intro g
        have h1 : σ * g * σ⁻¹ * g⁻¹ ∈ Q.act.ker := by
          have : g * σ⁻¹ * g⁻¹ ∈ Q.act.ker := hKn.conj_mem _ ((Q.act.ker).inv_mem hσ) g
          have h2 := (Q.act.ker).mul_mem hσ this
          simpa [mul_assoc] using h2
        have h2 : σ * g * σ⁻¹ * g⁻¹ ∈ alternatingGroup (Fin 5) := by
          rw [Perm.mem_alternatingGroup]
          simp only [map_mul, map_inv]
          rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1 <;>
            rcases Int.units_eq_one_or (Perm.sign g) with h2 | h2 <;> simp [h1, h2]
        have h3 : (⟨σ * g * σ⁻¹ * g⁻¹, h2⟩ : alternatingGroup (Fin 5)) ∈
            Q.act.ker.subgroupOf (alternatingGroup (Fin 5)) := h1
        rw [hb, Subgroup.mem_bot] at h3
        have h4 : σ * g * σ⁻¹ * g⁻¹ = 1 := congrArg Subtype.val h3
        calc σ * g = (σ * g * σ⁻¹ * g⁻¹) * (g * σ) := by group
          _ = g * σ := by rw [h4, one_mul]
      have key : ∀ τ : Perm (Fin 5), (∀ a b : Fin 5, τ * swap a b = swap a b * τ) → τ = 1 := by
        decide +kernel
      exact key σ fun a b => hc _
    · exfalso
      apply h
      rw [eq_top_iff]
      intro w _ b hb
      have : (⟨b, hb⟩ : alternatingGroup (Fin 5)) ∈ Q.act.ker.subgroupOf
          (alternatingGroup (Fin 5)) := by rw [ht]; trivial
      have h1 : Q.act b = 1 := this
      rw [h1]; rfl
  intro σ τ hστ
  have : Q.act (σ * τ⁻¹) = 1 := by rw [map_mul, map_inv, hστ, mul_inv_cancel]
  have := hker _ this
  exact mul_inv_eq_one.mp this

theorem card_fixW_eq_of_iso {M N : Model 5} (e : M.Iso N) (B : Subgroup (Perm (Fin 5))) :
    Nat.card (fixW N B) = Nat.card (fixW M B) := by
  rw [e.fixW_eq B]
  exact Subgroup.card_map_of_injective e.toMulEquiv.injective

theorem nonempty_iso_quot_of_eq_bot (Q : Model 5) (hK : IsInvSub Q ⊤ (fixW Q ⊤))
    (hb : fixW Q ⊤ = ⊥) : Nonempty (Q.Iso (Q.quot (fixW Q ⊤) hK)) := by
  have hinj : Function.Injective (Q.projQuot (fixW Q ⊤) hK) := by
    rw [← MonoidHom.ker_eq_bot_iff, Q.ker_projQuot, hb]
  exact ⟨{ toMulEquiv := MulEquiv.ofBijective (Q.projQuot (fixW Q ⊤) hK)
            ⟨hinj, Q.projQuot_surjective _ hK⟩
           map_act := fun σ w => (Q.projQuot_act _ hK σ w).symm }⟩

theorem idx_swap_eq (M : Model 5) {t t' : Perm (Fin 5)} (ht : t.IsSwap) (ht' : t'.IsSwap) :
    idx M t = idx M t' := by
  obtain ⟨x, y, hxy, rfl⟩ := ht
  obtain ⟨a, b, hab, rfl⟩ := ht'
  obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_swap hxy hab)
  rw [← hc, idx_conj]

theorem card_fixQ_eq (M : Model 5) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (B : Subgroup (Perm (Fin 5))) :
    Nat.card (fixQ M B U) = Nat.card U * Nat.card (fixW (M.quot U hU) B) := by
  have h1 := Subgroup.card_mul_index (fixQ M B U)
  have h2 := Subgroup.card_mul_index (fixW (M.quot U hU) B)
  have h3 := Subgroup.card_mul_index U
  rw [index_fixW_quot M U hU B] at h2
  have h4 : Nat.card (M.quot U hU).W = U.index := rfl
  have h5 : (fixQ M B U).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h5)
  have h6 : U.index = Nat.card (fixW (M.quot U hU) B) * (fixQ M B U).index := h4 ▸ h2.symm
  calc Nat.card (fixQ M B U) * (fixQ M B U).index = Nat.card M.W := h1
    _ = Nat.card U * U.index := h3.symm
    _ = Nat.card U * Nat.card (fixW (M.quot U hU) B) * (fixQ M B U).index := by
      rw [h6]; ring

theorem shapeMod1_of_CEMod {M : Model 5} (h : CEMod M) : ShapeMod1 M := by
  obtain ⟨t0, ht0, ht0le⟩ := h.small
  have ht01 : t0 ≠ 1 := ((isSwap_iff t0).mp ht0).1
  obtain ⟨U, hU, hUbot, hirr⟩ := exists_minimal_inv M h.nt
  have hmoved : ∃ σ w, (M.restrict U hU).act σ w ≠ w := by
    by_contra hall
    push Not at hall
    apply hUbot
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have hfix : u ∈ fixW M ⊤ := fun b _ => congrArg Subtype.val (hall b ⟨u, hu⟩)
    rwa [h.fix, Subgroup.mem_bot] at hfix
  have hcls := model5_irred_classification _ hirr hmoved
  have hQA : fixW (M.quot U hU) (alternatingGroup (Fin 5)) ≠ ⊤ := by
    intro hQ
    have hN : ∀ a ∈ alternatingGroup (Fin 5), ∀ w : M.W, M.act a w * w⁻¹ ∈ U := by
      intro a ha w
      have : M.projQuot U hU w ∈ fixW (M.quot U hU) (alternatingGroup (Fin 5)) := by
        rw [hQ]; trivial
      exact (M.projQuot_mem_fixW_iff U hU _ w).mp this a ha
    have hUtop : U = ⊤ := by
      apply h.gen U hU
      intro c hc
      obtain ⟨n, hn, f, hf, hcnf⟩ := trace_model M (S := S5Syl) (G := ⊤)
        (A := alternatingGroup (Fin 5)) le_top odd_relIndex_S5Syl
        (fun g _ => perm5_eq_alt5_mul_syl g) U hN hc
      rw [h.fix, Subgroup.mem_bot] at hf
      rw [hcnf, hf, mul_one]
      exact hn
    have e0 := M.isoRestrictTop U hU hUtop
    apply h.red
    rcases hcls with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨e0.trans e⟩
    · exact Or.inr ⟨e0.trans e⟩
  set Q := M.quot U hU with hQdef
  have hQ1 : fixW Q ⊤ ≠ ⊤ := by
    intro h1
    have h2 := fixW_antitone Q (le_top : alternatingGroup (Fin 5) ≤ ⊤)
    rw [h1] at h2
    exact hQA (eq_top_iff.mpr h2)
  have hQt : 2 ≤ idx Q t0 := by
    have h1 : idx Q t0 ≠ 1 := fun h1 =>
      hQ1 (fixW_top_of_swap Q ht0 (Subgroup.index_eq_one.mp h1))
    have h0 : idx Q t0 ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hprod : idx (M.restrict U hU) t0 * idx Q t0 ≤ idx M t0 :=
    idx_restrict_mul_idx_quot_le M U hU t0
  have hUt : idx (M.restrict U hU) t0 = 2 ∧ Nonempty ((M.restrict U hU).Iso orth) := by
    rcases hcls with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact ⟨by rw [← e.idx_eq]; exact ((transvections t0 ht01).2).mpr ht0, ⟨e⟩⟩
    · exfalso
      have h4 : 4 ≤ idx (M.restrict U hU) t0 := by
        rw [← e.idx_eq]; exact (transvections t0 ht01).1
      nlinarith
  obtain ⟨hUt2, ⟨eU⟩⟩ := hUt
  have hQt2 : idx Q t0 = 2 := by rw [hUt2] at hprod; omega
  have hf : Q.Faithful := faithful_of_alt_ne_top hQA
  obtain ⟨-, ⟨eQ0⟩⟩ := hss_1_5_top Q hf ht01 hQt2
  have hMle : Nat.card M.W ≤ 256 := by
    calc Nat.card M.W ≤ idx M t0 ^ 4 := card_le_idx_pow_four M ht0 h.fix
      _ ≤ 4 ^ 4 := Nat.pow_le_pow_left ht0le 4
  have hU16 : Nat.card U = 16 := by
    have h1 := eU.card_eq
    rw [card_orth] at h1
    exact h1
  have hMU : Nat.card M.W = 16 * Nat.card Q.W := by
    rw [← Subgroup.card_mul_index U, hU16]; rfl
  have hK : IsInvSub Q ⊤ (fixW Q ⊤) := isInvSub_fixW_of_normal Q Subgroup.normal_top
  have hcK : Nat.card (fixW Q ⊤) * 16 = Nat.card Q.W := by
    have h1 := Subgroup.card_mul_index (fixW Q ⊤)
    have h2 : (fixW Q ⊤).index = 16 := by
      have h3 := eQ0.card_eq
      rw [card_orth] at h3
      exact h3
    rw [h2] at h1
    exact h1
  have hKcard : Nat.card (fixW Q ⊤) = 1 := by
    have : 0 < Nat.card (fixW Q ⊤) := Nat.card_pos
    omega
  obtain ⟨e1⟩ := nonempty_iso_quot_of_eq_bot Q hK (Subgroup.card_eq_one.mp hKcard)
  have eQ : Q.Iso orth := e1.trans eQ0
  refine ⟨⟨U, hU, ⟨eU⟩, ⟨eQ⟩⟩, by omega, ?_, ?_⟩
  · intro P hP
    have hUP : IsInvSub M P U := fun b _ => hU b (Subgroup.mem_top b)
    have h1 := bf4_card hUP
    rw [card_fixQ_eq M U hU P] at h1
    have hP2 : Nat.card (fixW orth P) = 2 := by
      have h2 := congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) (profile_sylow orth (Or.inl rfl) hP)
      simpa [profile] using h2
    have hQP : Nat.card (fixW Q P) = 2 := (card_fixW_eq_of_iso eQ P).symm.trans hP2
    have hUP2 : Nat.card ↥(U ⊓ fixW M P) = 2 := by
      have h3 := card_fixW_eq_of_iso eU P
      rw [fixW_restrict, hP2] at h3
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective U)]
      exact h3.symm
    rw [hQP, hUP2] at h1
    have h4 : Nat.card (fixW M P) * Nat.card U ≤ 4 * Nat.card U := by
      calc Nat.card (fixW M P) * Nat.card U ≤ 2 * (Nat.card U * 2) := h1
        _ = 4 * Nat.card U := by ring
    exact Nat.le_of_mul_le_mul_right h4 Nat.card_pos
  · intro t ht
    rw [idx_swap_eq M ht ht0]
    have := h.swap4 t0 ht0
    omega

end S34

end F53.Stellmacher

end CFSG.Quasithin
