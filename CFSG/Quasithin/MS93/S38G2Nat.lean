module

public import CFSG.Quasithin.MS93.S38G2Ker
public import CFSG.Quasithin.MS93.S38G2Hyp

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

theorem exists_mem_derived_apply_e (v : ModQ) (hv : v ≠ 1) :
    ∃ δ ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) δ (codeQ ⟨2, by decide⟩) = v := by
  obtain ⟨c, rfl⟩ := codeQ_surjective v
  have h0 : ¬ (c.1 = 0 ∨ c.1 = 129) := fun h => hv ((codeQ_eq_one_iff c).2 h)
  rw [not_or] at h0
  obtain ⟨c', hc'mem, hcc', hn, hd0, hd1⟩ : ∃ c' : ℕ, ∃ h : c' ∈ o0Codes,
      codeQ c = codeQ ⟨c', h⟩ ∧ zornNorm (decodeZ c') = 0 ∧ decodeZ c' ≠ 0 ∧
        decodeZ c' ≠ zornOne := by
    rcases singular_or c.1 c.2 h0.1 h0.2 with ⟨hn, hd0, hd1⟩ | ⟨hn, hd0, hd1⟩
    · exact ⟨c.1, c.2, rfl, hn, hd0, hd1⟩
    · refine ⟨c.1 ^^^ 129, xor_mem_o0Codes c.2 (by decide), ?_, hn, hd0, hd1⟩
      rw [codeQ_eq_iff]
      exact Or.inr rfl
  obtain ⟨hwc, hwl⟩ := singular_word hc'mem hn hd0 hd1
  refine ⟨wordGG (g2Words.getD c' []), wordGG_mem_derived _, ?_⟩
  rw [hcc']
  exact codeQ_word_e hwl hc'mem _ hwc

theorem modQ_irred (W : Subgroup ModQ)
    (hW : ∀ δ ∈ g2Derived (ZMod 2), ∀ w ∈ W, g2QAct (ZMod 2) δ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  rcases W.bot_or_exists_ne_one with hbot | ⟨w, hw, hw1⟩
  · exact Or.inl hbot
  right
  obtain ⟨δ, hδ, hδw⟩ := exists_mem_derived_apply_e w hw1
  have he : codeQ ⟨2, by decide⟩ ∈ W := by
    have h1 := hW δ⁻¹ (inv_mem hδ) w hw
    rwa [← hδw, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h1
  rw [eq_top_iff]
  intro v _
  by_cases hv : v = 1
  · rw [hv]
    exact W.one_mem
  obtain ⟨δ', hδ', rfl⟩ := exists_mem_derived_apply_e v hv
  exact hW δ' hδ' _ he

theorem stab_comm_codes : applyG stabW1 4 ^^^ 4 = 237 ∧ applyG stabW1 8 ^^^ 8 = 167 ∧
    applyG stabW1 16 ^^^ 16 = 229 ∧ applyG stabW1 64 ^^^ 64 = 98 ∧
      applyG stabW2 4 ^^^ 4 = 12 := by
  decide +kernel

@[expose] def xorSpan (l : List ℕ) : List ℕ := l.foldl (fun acc g => acc ++ acc.map (· ^^^ g)) [0]

theorem xorSpan_stab : (xorSpan [237, 167, 229, 98, 12]).length = 32 ∧
    (∀ c ∈ xorSpan [237, 167, 229, 98, 12], c ∈ o0Codes) ∧
    (xorSpan [237, 167, 229, 98, 12]).Nodup ∧
    ∀ c ∈ xorSpan [237, 167, 229, 98, 12], ∀ d ∈ xorSpan [237, 167, 229, 98, 12],
      (d = c ∨ d = c ^^^ 129) → c = d := by
  decide +kernel

theorem codeQ_mem_of_mem_foldl {S : Subgroup ModQ} (l : List ℕ) :
    ∀ acc : List ℕ, (∀ g ∈ l, ∃ hg : g ∈ o0Codes, codeQ ⟨g, hg⟩ ∈ S) →
      (∀ c ∈ acc, ∃ hc : c ∈ o0Codes, codeQ ⟨c, hc⟩ ∈ S) →
        ∀ c ∈ l.foldl (fun acc g => acc ++ acc.map (· ^^^ g)) acc,
          ∃ hc : c ∈ o0Codes, codeQ ⟨c, hc⟩ ∈ S := by
  induction l with
  | nil => exact fun acc _ hacc => hacc
  | cons g l ih =>
    intro acc hl hacc
    simp only [List.foldl_cons]
    refine ih _ (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) fun c hc => ?_
    rcases List.mem_append.mp hc with hc | hc
    · exact hacc c hc
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hamem, haS⟩ := hacc a ha
      obtain ⟨hgmem, hgS⟩ := hl g (by simp)
      refine ⟨xor_mem_o0Codes hamem hgmem, ?_⟩
      have e : (⟨a ^^^ g, xor_mem_o0Codes hamem hgmem⟩ : O0C) =
          o0Xor ⟨a, hamem⟩ ⟨g, hgmem⟩ := rfl
      rw [e, codeQ_xor]
      exact S.mul_mem haS hgS

theorem index_le_two_of_stab (S : Subgroup ModQ)
    (hS : ∀ w ∈ [stabW1, stabW2], ∀ q : ModQ, g2QAct (ZMod 2) (wordGG w) q * q⁻¹ ∈ S) :
    S.index ≤ 2 := by
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  obtain ⟨hw1, hw2, -, -⟩ := stab_words
  have hgen : ∀ w ∈ [stabW1, stabW2], ∀ c (hc : c ∈ o0Codes) (d : ℕ) (hd : d ∈ o0Codes),
      applyG w c ^^^ c = d → codeQ ⟨d, hd⟩ ∈ S := by
    intro w hw c hc d hd hcd
    have hwl : ∀ t ∈ w, t = 1 ∨ t = 2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      exacts [hw1, hw2]
    have h1 := hS w hw (codeQ ⟨c, hc⟩)
    rw [g2QAct_codeQ, codeQ_inv, ← codeQ_xor] at h1
    convert h1 using 2
    apply Subtype.ext
    change d = (o0Act (wordGG w) ⟨c, hc⟩).1 ^^^ c
    rw [o0Act_wordGG hwl, hcd]
  obtain ⟨h1, h2, h3, h4, h5⟩ := stab_comm_codes
  have hgS : ∀ g ∈ [237, 167, 229, 98, 12], ∃ hg : g ∈ o0Codes, codeQ ⟨g, hg⟩ ∈ S := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, hgen stabW1 (by simp) 4 (by decide) _ _ h1⟩
    · exact ⟨by decide, hgen stabW1 (by simp) 8 (by decide) _ _ h2⟩
    · exact ⟨by decide, hgen stabW1 (by simp) 16 (by decide) _ _ h3⟩
    · exact ⟨by decide, hgen stabW1 (by simp) 64 (by decide) _ _ h4⟩
    · exact ⟨by decide, hgen stabW2 (by simp) 4 (by decide) _ _ h5⟩
  obtain ⟨hlen, -, hnd, hinj⟩ := xorSpan_stab
  have hcsS : ∀ c ∈ xorSpan [237, 167, 229, 98, 12], ∃ hc : c ∈ o0Codes, codeQ ⟨c, hc⟩ ∈ S :=
    codeQ_mem_of_mem_foldl _ [0] hgS fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      refine ⟨zero_mem_o0Codes, ?_⟩
      have e : (⟨0, zero_mem_o0Codes⟩ : O0C) = o0Zero := rfl
      rw [e, codeQ_zero]
      exact S.one_mem
  let F : {c // c ∈ xorSpan [237, 167, 229, 98, 12]} → ↥S := fun c =>
    ⟨codeQ ⟨c.1, (hcsS c.1 c.2).1⟩, (hcsS c.1 c.2).2⟩
  have hF : Function.Injective F := by
    rintro ⟨c, hc⟩ ⟨d, hd⟩ he
    have he' := congrArg Subtype.val he
    have he'' : codeQ ⟨c, (hcsS c hc).1⟩ = codeQ ⟨d, (hcsS d hd).1⟩ := he'
    rw [codeQ_eq_iff] at he''
    exact Subtype.ext (hinj c hc d hd he'')
  have hcard : Nat.card {c // c ∈ xorSpan [237, 167, 229, 98, 12]} = 32 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun c => (List.mem_toFinset (l := xorSpan
      [237, 167, 229, 98, 12])).symm), Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup hnd, hlen]
  have hle : 32 ≤ Nat.card S := hcard ▸ Nat.card_le_card_of_injective F hF
  have hmul := S.index_mul_card
  rw [card_ModQ] at hmul
  by_contra hlt
  push Not at hlt
  have h6 : 3 * 32 ≤ S.index * Nat.card S := Nat.mul_le_mul hlt hle
  rw [hmul] at h6
  norm_num at h6

section Transport

universe w

variable {U₀ U₁ : Type w} [Group U₀] [Group U₁]

theorem NatHyp.of_equiv {G₀ L₀ Q₀ : Subgroup U₀} {G₁ L₁ Q₁ : Subgroup U₁} (e : ↥G₀ ≃* ↥G₁)
    (hL : ∀ x : ↥G₀, (x : U₀) ∈ L₀ ↔ (e x : U₁) ∈ L₁)
    (hQ : ∀ x : ↥G₀, (x : U₀) ∈ Q₀ ↔ (e x : U₁) ∈ Q₁) (hN : NatHyp G₀ L₀ Q₀) :
    NatHyp G₁ L₁ Q₁ := by
  intro Y _ _ hY2 hYc ρ hρQ hρL
  obtain ⟨hirr, y₀, hy₀, hidx⟩ := hN Y hY2 hYc (ρ.comp e.toMonoidHom)
    (fun q hq => hρQ (e q) ((hQ q).mp hq)) (by
      obtain ⟨l, hl, hl1⟩ := hρL
      refine ⟨e.symm l, (hL _).mpr (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hl1)
  refine ⟨fun W hW => hirr W fun l hl w hw => hW (e l) ((hL l).mp hl) w hw, y₀, hy₀, ?_⟩
  refine le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le (Subgroup.closure_mono ?_))) hidx
  rintro x ⟨l, hl, hly, y, rfl⟩
  exact ⟨e l, (hL l).mp hl, hly, y, rfl⟩

end Transport

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace G2Rep

variable {h : PUHyp M T L} {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ}
  {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem natHyp
    (hR : G2Rep h f φ) : NatHyp M L (pCoreOf 2 M) := by
  intro Y _ _ hY2 hYc ρ hρQ hρL
  let φL : ↥L →* ↥(g2Derived (ZMod 2)) :=
    (φ.comp (Subgroup.inclusion h.L_le)).codRestrict _ fun l => hR.L_le _ l.2
  have hsurj : Function.Surjective φL := by
    intro δ
    obtain ⟨l, hl, hlδ⟩ := hR.L_onto δ.1 δ.2
    exact ⟨⟨l, hl⟩, Subtype.ext hlδ⟩
  have hker : φL.ker ≤ (ρ.comp (Subgroup.inclusion h.L_le)).ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 := congrArg Subtype.val hl
    exact hρQ _ (hR.mem_pCoreOf_of_mem_L l h1)
  let ψ : ↥(g2Derived (ZMod 2)) →* MulAut Y :=
    φL.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨ρ.comp (Subgroup.inclusion h.L_le), hker⟩
  have hψ : ∀ l : ↥L, ψ (φL l) = ρ (Subgroup.inclusion h.L_le l) := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply φL _ _ ⟨ρ.comp (Subgroup.inclusion h.L_le), hker⟩ l
  have hψinj : Function.Injective ψ := by
    have := isSimpleGroup_g2Derived'
    rcases ψ.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff ψ).mp hk
    · exfalso
      obtain ⟨l, hl, hl1⟩ := hρL
      apply hl1
      have h1 : ψ (φL ⟨l, hl⟩) = 1 := by
        rw [← MonoidHom.mem_ker, hk]
        exact Subgroup.mem_top _
      rw [hψ] at h1
      exact h1
  set H : Subgroup (MulAut Y) := ψ.range with hH
  have hHtype : B42TypeU33 ↥H :=
    SmithC27.b42TypeU33_of_equiv (Nat.card_zmod 2)
      ((MonoidHom.ofInjective hψinj).symm.trans
        (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)))
  have hHcard : Nat.card ↥H = 6048 := B42U33.card_of_b42TypeU33 hHtype
  have hYp : IsPGroup 2 Y := fun y => ⟨1, by rw [pow_one]; exact hY2 y⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hYp
  have hk6 := B42U33.six_le_of_card_dvd hY2 hk H hHcard
  have hY6 : Nat.card Y = 2 ^ 6 := by
    rw [hk] at hYc ⊢
    have : k ≤ 6 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hYc
    rw [show k = 6 by omega]
  obtain ⟨e, he⟩ :=
    B42U33.exists_equiv_of_g2NaturalDerived (B42U33.u33SixNatural Y hY2 hY6 H hHtype)
  have hdict : ∀ δ ∈ g2Derived (ZMod 2), ∃ l : ↥M, (l : G) ∈ L ∧
      ∀ y, e (ρ l y) = g2QAct (ZMod 2) δ (e y) := by
    intro δ hδ
    have hmem : g2QAct (ZMod 2) δ ∈ H.map (MulAut.congr e).toMonoidHom := by
      rw [he]
      exact ⟨δ, hδ, rfl⟩
    obtain ⟨x, ⟨δ', rfl⟩, hx⟩ := hmem
    obtain ⟨l, rfl⟩ := hsurj δ'
    refine ⟨Subgroup.inclusion h.L_le l, l.2, fun y => ?_⟩
    rw [← hx, ← hψ l]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  refine ⟨fun W hW => ?_, e.symm (codeQ ⟨2, by decide⟩), ?_, ?_⟩
  ·
    have hW' : ∀ δ ∈ g2Derived (ZMod 2), ∀ w ∈ W.map e.toMonoidHom,
        g2QAct (ZMod 2) δ w ∈ W.map e.toMonoidHom := by
      rintro δ hδ _ ⟨w, hw, rfl⟩
      obtain ⟨l, hl, hle⟩ := hdict δ hδ
      exact ⟨ρ l w, hW l hl w hw, hle w⟩
    rcases modQ_irred _ hW' with h1 | h1
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective W e.injective).mp h1)
    · right
      rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective W, h1,
        Subgroup.comap_top]
  · intro h1
    have h2 := congrArg e h1
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    exact absurd ((codeQ_eq_one_iff _).mp h2) (by decide)
  ·
    obtain ⟨hw1, hw2, hs1, hs2⟩ := stab_words
    have hS : ∀ w ∈ [stabW1, stabW2], ∀ q : ModQ, g2QAct (ZMod 2) (wordGG w) q * q⁻¹ ∈
        (Subgroup.closure {x | ∃ l : ↥M, (l : G) ∈ L ∧
          ρ l (e.symm (codeQ ⟨2, by decide⟩)) = e.symm (codeQ ⟨2, by decide⟩) ∧
            ∃ y : Y, x = ρ l y * y⁻¹}).map e.toMonoidHom := by
      intro w hw q
      have hw' : (∀ t ∈ w, t = 1 ∨ t = 2) ∧ applyG w 2 = 2 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        exacts [⟨hw1, hs1⟩, ⟨hw2, hs2⟩]
      have hfix : g2QAct (ZMod 2) (wordGG w) (codeQ ⟨2, by decide⟩) = codeQ ⟨2, by decide⟩ :=
        codeQ_word_e hw'.1 _ _ hw'.2
      obtain ⟨l, hl, hle⟩ := hdict (wordGG w) (wordGG_mem_derived w)
      refine ⟨ρ l (e.symm q) * (e.symm q)⁻¹, Subgroup.subset_closure ⟨l, hl, ?_, e.symm q, rfl⟩,
        ?_⟩
      · apply e.injective
        rw [hle, MulEquiv.apply_symm_apply, hfix]
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, hle, MulEquiv.apply_symm_apply]
    have h2 := index_le_two_of_stab _ hS
    rwa [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective] at h2

end G2Rep

end CFSG.Quasithin.MS93.S38G
