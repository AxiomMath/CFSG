module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.SmithB42Alt7Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourMain
public import CFSG.Quasithin.Background.HA7Rec
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.SmithB42Alt7Ctx
public import CFSG.Quasithin.Background.SmithB42Alt7Model

public section

namespace CFSG.Quasithin

namespace B42Alt7

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)}

theorem one_le_rAV_of_le_index (hV : ∀ v : S, v ^ 2 = 1) {X B : Subgroup (MulAut S)}
    (hB : IsA2 X B) (h : Nat.card B ≤ (fixV B).index) : 1 ≤ rAV B :=
  CFSG.Quasithin.RAV.one_le_rAV_of_le_index hV hB h

theorem card_of_altConjTo {P : Subgroup ↥(alternatingGroup (Fin 7))}
    (h : AltConjTo 7 P kleinRegular7) : Nat.card P = 4 := by
  obtain ⟨c, -, hc⟩ := h
  have h1 : Nat.card (P.map (alternatingGroup (Fin 7)).subtype) = Nat.card P :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective
  rw [← h1, hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact B42A57.card_V0

theorem case7 (hV : ∀ v : S, v ^ 2 = 1) (C : Bridge.Alt57.Ctx G L 7)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) {A : Subgroup (MulAut S)}
    (hA : IsFFStarOffender G A) (hcard : Nat.card S = 2 ^ 4) : B42Case7 G L A := by
  have hS2 : ∀ s : S, s * s = 1 := fun s => by simpa [pow_two] using hV s
  have hS16 : Nat.card S = 16 := by rw [hcard]; norm_num
  have hL2520 : Nat.card ↥L = 2520 := by
    rw [C.card_eq]
    exact L246.C123.card_A7
  have hnorm := L246.C123.normalizer_eq_of_card_2520 hV hS16 hL2520
  have hGL : G = L := by
    refine le_antisymm (fun g hg => ?_) C.le_G
    have hg' : g ∈ Subgroup.normalizer (L : Set (MulAut S)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro l
      refine ⟨fun hl => C.normal g hg l hl, fun hl => ?_⟩
      have := C.normal g⁻¹ (G.inv_mem hg) _ hl
      simpa [mul_assoc] using this
    rw [hnorm] at hg'
    exact hg'
  have hJL : ffJ G = L := le_antisymm (hGL ▸ B6.ffJ_le G) (C.le_ffJ hA)
  obtain ⟨ι, e, hinj, hL, -⟩ := B42A57.exists_embedding C
  refine ⟨hGL.trans hJL.symm, hJL, ?_, hcard, ?_, ?_⟩
  · exact H.A7.a7Four_of_faithful C.iso (fun _ _ _ _ => trivial) (fun u _ => hS2 u)
      (by rw [Subgroup.card_top]; exact hcard) (fun h _ hh => MulEquiv.ext fun v => hh v trivial)
  · refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, B1_4_1 hV hA⟩
    have hBL : B ≤ L := hGL ▸ hB.1
    have h4 : Nat.card B = 4 := by
      have h := card_of_altConjTo
        (B42A57.asB42A7Four_holds S hV G L B C hirr hB hcard ι.symm)
      have e1 : (B.subgroupOf L).comap ι.symm.toMonoidHom = (B.subgroupOf L).map ι.toMonoidHom :=
        Subgroup.comap_equiv_eq_map_symm ι.symm _
      rw [e1, Subgroup.card_map_of_injective ι.injective] at h
      rw [← h]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv).symm
    obtain ⟨h1, hc, h2, hcardB⟩ := B42A57.offender_image hB e hinj
    obtain ⟨r, f, hf, hbound, hcl⟩ := B42A57.gen7 h1 hc h2
    have hle := card_le_index_pow C hirr B ι e hinj hL f hf hcl
    refine one_le_rAV_of_le_index hV hB.isA2 ?_
    rw [h4]
    refine four_le_of_pow_le ?_ (hcard ▸ hle) (by rw [← h4, ← hcardB]; exact hbound)
    rw [← hcard]
    exact Subgroup.index_dvd_card _
  · intro π
    exact B42A57.asB42A7Four_holds S hV G L A C hirr hA hcard π

omit [Finite S] in
theorem card_fixV_le_four {C : Bridge.Alt57.Ctx G L 7} (M : SymModel C)
    {A : Subgroup (MulAut S)} {a b c d e f : Fin 7} (hnd : [a, b, c, d, e, f].Nodup)
    (h1 : M.ρ (swap e f) ∈ A) (h2 : M.ρ (swap a b * swap c d) ∈ A)
    (h3 : M.ρ (swap a c * swap b d) ∈ A) : Nat.card (fixV A) ≤ 4 := by
  let φ : ↥(fixV A) → ZMod 2 × ZMod 2 := fun v =>
    (Multiplicative.toAdd (M.β v : G6.PermMod 7) a, Multiplicative.toAdd (M.β v : G6.PermMod 7) e)
  have key : ∀ (u : ↥(fixV A)) (σ : Perm (Fin 7)), M.ρ σ ∈ A → ∀ i,
      Multiplicative.toAdd (M.β u : G6.PermMod 7) (σ⁻¹ i) =
        Multiplicative.toAdd (M.β u : G6.PermMod 7) i := by
    intro u σ hσ i
    have h := M.β_equiv σ u
    rw [u.2 _ hσ] at h
    have h' := congrArg (fun x : G6.PermMod 7 => Multiplicative.toAdd x i) h
    simp only [G6.permAct_apply] at h'
    exact h'.symm
  have hsum : ∀ u : ↥(fixV A), ∑ i, Multiplicative.toAdd (M.β u : G6.PermMod 7) i = 0 :=
    fun u => (M.β u).2
  have hφ : Function.Injective φ := by
    intro v w hvw
    have hxy := eq_of_fix_R4 hnd (hsum v) (hsum w) (key v _ h1) (key v _ h2) (key v _ h3)
      (key w _ h1) (key w _ h2) (key w _ h3) (congrArg Prod.fst hvw) (congrArg Prod.snd hvw)
    apply Subtype.ext
    apply M.β.injective
    apply Subtype.ext
    exact Multiplicative.toAdd.injective hxy
  calc Nat.card (fixV A) ≤ Nat.card (ZMod 2 × ZMod 2) := Nat.card_le_card_of_injective φ hφ
    _ = 4 := by simp

theorem card_coreMod_seven : Nat.card (G6.coreMod 7) = 2 ^ 6 := by
  have h : (G6.coreMod 7 : Set (G6.PermMod 7)) =
      ↑(Finset.univ.filter fun x : G6.PermMod 7 => ∑ i, Multiplicative.toAdd x i = 0) := by
    ext x
    simp [G6.mem_coreMod]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_coe_finset]
  decide

@[expose] def Res7Gen (E : Subgroup (Perm (Fin 7))) : Prop :=
  (Nat.card E = 2 ∧ ∃ a b : Fin 7, a ≠ b ∧ swap a b ∈ E) ∨
  (Nat.card E = 4 ∧ ∃ a b c' d : Fin 7, [a, b, c', d].Nodup ∧ swap a b ∈ E ∧ swap c' d ∈ E) ∨
  (Nat.card E = 8 ∧ ∃ a b c' d e f : Fin 7, [a, b, c', d, e, f].Nodup ∧ swap a b ∈ E ∧
    swap c' d ∈ E ∧ swap e f ∈ E)

theorem le_closure_swaps {E : Subgroup (Perm (Fin 7))} (h : Res7Gen E) :
    E ≤ Subgroup.closure {x | x ∈ E ∧ x.IsSwap} := by
  set T : Set (Perm (Fin 7)) := {x | x ∈ E ∧ x.IsSwap} with hT
  have hTE : Subgroup.closure T ≤ E := by
    rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  have hmem : ∀ a b : Fin 7, a ≠ b → swap a b ∈ E → swap a b ∈ Subgroup.closure T :=
    fun a b hab h => Subgroup.subset_closure ⟨h, a, b, hab, rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge hTE ?_).ge
  rcases h with ⟨hc2, a, b, hab, h1⟩ | ⟨hc4, a, b, c', d, hnd, h1, h2⟩ |
    ⟨hc8, a, b, c', d, e, f, hnd, h1, h2, h3⟩
  · rw [hc2]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hz : Subgroup.zpowers (swap a b) ≤ Subgroup.closure T :=
      Subgroup.zpowers_le.2 (hmem a b hab h1)
    calc 2 = Nat.card (Subgroup.zpowers (swap a b)) := by
          rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two, swap_mul_self])
            (B42A57.swap_ne_one' hab)]
      _ ≤ _ := Subgroup.card_le_of_le hz
  · rw [hc4, ← B42A57.card_swap_pair hnd]
    refine Subgroup.card_le_of_le (Subgroup.closure_le _ |>.2 ?_)
    rintro x (rfl | rfl)
    · exact hmem a b (B42A57.ne_of_nodup4 hnd) h1
    · have : c' ≠ d := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true, not_false_eq_true] at hnd
        exact hnd.2.2
      exact hmem c' d this h2
  · have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at hnd'
    obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩, hef⟩ :=
      hnd'
    have hnd4 : [a, b, c', d].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
    set K := Subgroup.closure ({swap a b, swap c' d} : Set (Perm (Fin 7))) with hK
    have hKT : K ≤ Subgroup.closure T := by
      rw [hK, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hmem a b hab h1
      · exact hmem c' d hcd h2
    have hK4 : Nat.card K = 4 := B42A57.card_swap_pair hnd4
    have hstab : K ≤ MulAction.stabilizer (Perm (Fin 7)) e := by
      rw [hK, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · show swap a b • e = e
        rw [Perm.smul_def, swap_apply_of_ne_of_ne (Ne.symm hae) (Ne.symm hbe)]
      · show swap c' d • e = e
        rw [Perm.smul_def, swap_apply_of_ne_of_ne (Ne.symm hce) (Ne.symm hde)]
    have h3K : swap e f ∉ K := by
      intro h
      have h' := hstab h
      rw [MulAction.mem_stabilizer_iff, Perm.smul_def, swap_apply_left] at h'
      exact hef h'.symm
    have hlt : K < Subgroup.closure T :=
      lt_of_le_of_ne hKT fun h => h3K (h ▸ hmem e f hef h3)
    have hlt' := Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card (Subgroup.closure T) ∣ Nat.card E := Subgroup.card_dvd_of_le hTE
    rw [hc8] at hdvd ⊢
    rw [hK4] at hlt'
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 3 from hdvd)
    rw [hk'] at hlt' ⊢
    interval_cases k <;> simp_all

theorem case5 (hV : ∀ v : S, v ^ 2 = 1)
    (C : Bridge.Alt57.Ctx G L 7) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) (hbig : 32 ≤ Nat.card S) :
    B42Case5 G A := by
  have hS2 : ∀ s : S, s * s = 1 := fun s => by simpa [pow_two] using hV s
  obtain ⟨M⟩ := exists_symModel hS2 C hirr hA hbig
  have hcard : Nat.card S = 2 ^ 6 := by
    rw [Nat.card_congr M.β.toEquiv, card_coreMod_seven]
  have hJ : ffJ G = G := by
    refine le_antisymm (B6.ffJ_le G) ?_
    obtain ⟨a, b, hab, hoff⟩ := M.transp
    have hswap : ∀ c d : Fin 7, c ≠ d → M.ρ (swap c d) ∈ ffJ G := by
      intro c d hcd
      obtain ⟨g, hg⟩ := B42A57.exists_perm_list [a, b] [c, d] (by simpa using hab)
        (by simpa using hcd) rfl
      have ga : g a = c := hg 0 (by simp)
      have gb : g b = d := hg 1 (by simp)
      have hconj : swap c d = g * swap a b * g⁻¹ := by
        rw [← ga, ← gb, Equiv.swap_apply_apply]
      have hoff' := B1.isFFStarOffender_conjAut hoff (M.ρ_mem g)
      refine B6.le_ffJ hoff' ?_
      rw [B1.mem_conjAut, hconj, map_mul, map_mul, map_inv]
      have : (M.ρ g)⁻¹ * (M.ρ g * M.ρ (swap a b) * (M.ρ g)⁻¹) * M.ρ g = M.ρ (swap a b) := by
        group
      rw [this]
      exact Subgroup.mem_zpowers _
    have htop : (⊤ : Subgroup (Perm (Fin 7))) ≤ (ffJ G).comap M.ρ := by
      rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
      rintro σ ⟨c, d, hcd, rfl⟩
      exact hswap c d hcd
    intro g hg
    have hσ := htop (Subgroup.mem_top (M.e ⟨g, hg⟩))
    rw [Subgroup.mem_comap, M.ρ_e] at hσ
    exact hσ
  let π : Perm (Fin 7) →* ↥(ffJ G) :=
    M.ρ.codRestrict (ffJ G) fun σ => by rw [hJ]; exact M.ρ_mem σ
  have hπs : Function.Surjective π := by
    intro x
    have hx : (x : MulAut S) ∈ G := hJ.le x.2
    refine ⟨M.e ⟨x, hx⟩, Subtype.ext ?_⟩
    exact M.ρ_e ⟨x, hx⟩
  have hR : (FFModel.symDn 7).RealizesVia (ffJ G) ⊤ ⊥ π :=
    realizesVia_of_equivariant (FFModel.symDn_isActionModel 7) B42A57.altDn7_ker' (ffJ G) π hπs
      M.β fun γ s => M.β_equiv γ s
  obtain ⟨h1, hc, h2, hcardE⟩ := B42A57.offender_image hA M.e M.e_inj
  set E := (A.subgroupOf G).map M.e with hE
  have hEA : ∀ σ ∈ E, M.ρ σ ∈ A := by
    rintro σ ⟨g, hg, rfl⟩
    rw [M.ρ_e]
    exact Subgroup.mem_subgroupOf.1 hg
  have hAE : ∀ x ∈ A, ∃ σ ∈ E, M.ρ σ = x := fun x hx =>
    ⟨M.e ⟨x, hA.1 hx⟩, ⟨_, Subgroup.mem_subgroupOf.2 hx, rfl⟩, M.ρ_e _⟩
  have hres : Res7Gen E := by
    rcases B42A57.classify7 h1 hc h2 with ⟨r, f, hf, hbound, hcl⟩ | hres
    · exfalso
      have := B42A57.card_le_of_cert C hirr hA M.ι M.e M.e_inj M.e_ι f hf (N := 2 ^ 4)
        (by rw [← hcardE]; exact hbound) hcl
      rw [hcard] at this
      norm_num at this
    rcases hres with h | h | h | ⟨hc8, a, b, c', d, e, f, hnd, h1', h2', h3'⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exfalso
      have hfix := card_fixV_le_four M hnd (hEA _ h1') (hEA _ h2') (hEA _ h3')
      have hoff := hA.card_le (bot_le : (⊥ : Subgroup (MulAut S)) ≤ A)
      rw [B1.card_bot_mul_card_fixV, ← hcardE, hc8, hcard] at hoff
      have : 8 * Nat.card (fixV A) ≤ 8 * 4 := Nat.mul_le_mul_left 8 hfix
      omega
  refine ⟨⟨7, Or.inr rfl, π, hR, {x | x ∈ E ∧ x.IsSwap}, fun t ht => ht.2,
    fun x hx y hy _ => hc x hx.1 y hy.1, ?_⟩, ?_⟩
  · have hcl : Subgroup.closure {x | x ∈ E ∧ x.IsSwap} = E := by
      refine le_antisymm ?_ (le_closure_swaps hres)
      rw [Subgroup.closure_le]
      exact fun x hx => hx.1
    rw [hcl]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hx
      obtain ⟨σ, hσ, hσx⟩ := hAE x hx
      exact ⟨σ, hσ, Subtype.ext hσx⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact hEA σ hσ
  · refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, B1_4_1 hV hA⟩
    obtain ⟨h1, hc, h2, hcardB⟩ := B42A57.offender_image hB M.e M.e_inj
    obtain ⟨r, f, hf, hbound, hcl⟩ := B42A57.gen7 h1 hc h2
    have hle := card_le_index_pow C hirr B M.ι M.e M.e_inj M.e_ι f hf hcl
    refine one_le_rAV_of_le_index hV hB.isA2 ?_
    refine le_of_pow_le (s := 6) (by norm_num) ?_ (B1.card_elemAbelian hB.2.2.1)
      (hcard ▸ hle) ?_
    · rw [← hcard]
      exact Subgroup.index_dvd_card _
    · rw [← hcardB]
      exact hbound

end B42Alt7

theorem asB42Alt7_holds : AsB42Alt7 := by
  unfold AsB42Alt7 AsB42For
  intro V _ _ hV G L hB hT A hA
  have C := B42Alt7.ctx_of_b4Hyp hB hT
  have hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ := hB.2.2.2
  have hS2 : ∀ s : V, s * s = 1 := fun s => by simpa [pow_two] using hV s
  have hup := (QuasithinUnique.B42A57.card_le_of_offender C hirr hA).2 rfl
  have hlo := QuasithinUnique.B42A57.card_ge_of_faithful C hS2
  by_cases h16 : Nat.card V = 2 ^ 4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (B42Alt7.case7 hV C hirr hA h16)))))))
  · have hbig : 32 ≤ Nat.card V := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := V)).1
        (QuasithinUnique.B42A57.isPGroup_two hS2)
      rw [hk] at hlo h16 ⊢
      have hk4 : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 hlo
      have hk5 : 5 ≤ k := by
        rcases Nat.lt_or_ge k 5 with h | h
        · exact absurd (by rw [show k = 4 by omega]) h16
        · exact h
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (B42Alt7.case5 hV C hirr hA hbig)))))

end CFSG.Quasithin
