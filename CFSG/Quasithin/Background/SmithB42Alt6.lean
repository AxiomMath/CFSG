module

public import CFSG.Quasithin.Background.RAVBounds
public import CFSG.Quasithin.Background.SmithB42Alt6Conj
public import CFSG.Quasithin.Background.SmithB42Alt6Sp4
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.FFC6M
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

namespace CFSG.Quasithin

namespace B42Alt6

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm CFSG.Quasithin.S143

@[expose] def e8List : List (Perm (Fin 6)) :=
  [1, swap 0 1, swap 2 3, swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5,
    swap 2 3 * swap 4 5, swap 0 1 * swap 2 3 * swap 4 5]

theorem e8_mul : ∀ a ∈ e8List, ∀ b ∈ e8List, a * b ∈ e8List := by decide +kernel

theorem e8_comm : ∀ a ∈ e8List, ∀ b ∈ e8List, a * b = b * a := by decide +kernel

theorem e8_sq : ∀ a ∈ e8List, a * a = 1 := by decide +kernel

theorem e8_nodup : e8List.Nodup := by decide +kernel

@[expose] def E8 : Subgroup (Perm (Fin 6)) where
  carrier := {x | x ∈ e8List}
  mul_mem' := fun {a b} ha hb => e8_mul a ha b hb
  one_mem' := by simp [e8List]
  inv_mem' := fun {a} ha => by
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right (e8_sq a ha)
    show a⁻¹ ∈ e8List
    rw [this]
    exact ha

theorem card_fix_e8 :
    (Finset.univ.filter fun a : N6 => ∀ σ ∈ e8List, n6Act σ a = a).card = 4 := by
  decide +kernel

variable {S : Type} [CommGroup S] [Finite S] {G L : Subgroup (MulAut S)}

omit [Finite S] in
theorem N6Model.card_fixV_e8 (M : N6Model L) : Nat.card (fixV (E8.map M.ρ)) = 4 := by
  rw [M.card_fixV_map, ← card_fix_e8]
  rw [show Nat.card {a : N6 // ∀ σ ∈ E8, n6Act σ a = a} =
      Nat.card {a : N6 // ∀ σ ∈ e8List, n6Act σ a = a} from
    Nat.card_congr (Equiv.subtypeEquivRight fun a => Iff.rfl)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem exists_n6Equiv_alt {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥H} (h : (FFModel.altDn 6).RealizesVia H ⊤ ⊥ π) :
    ∃ Θ : W ≃* N6, ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : W),
      Θ (((π γ : ↥H) : MulAut W) w) = n6Act γ (Θ w) := by
  obtain ⟨e, he⟩ := G64.RealizesVia.exists_modEquiv h
  let e' : W ≃* (FFModel.symDn 6).Mod := e
  refine ⟨e'.trans S1549D.psiN6, fun γ w => ?_⟩
  obtain ⟨m₀, hm⟩ : ∃ m₀ : ↥(G6.coreMod 6), (QuotientGroup.mk m₀ : (FFModel.symDn 6).Mod) = e' w :=
    QuotientGroup.mk_surjective _
  have hact : G6.permAct 6 (γ : Perm (Fin 6)) (m₀ : G6.PermMod 6) ∈ G6.coreMod 6 :=
    G6.permAct_mem_coreMod (γ : Perm (Fin 6)) m₀.2
  have h1 : e' (((π γ : ↥H) : MulAut W) w) =
      (QuotientGroup.mk ⟨G6.permAct 6 (γ : Perm (Fin 6)) (m₀ : G6.PermMod 6), hact⟩ :
        (FFModel.symDn 6).Mod) :=
    he γ w m₀ hact hm.symm
  show S1549D.psiN6 (e' (((π γ : ↥H) : MulAut W) w)) = n6Act γ (S1549D.psiN6 (e' w))
  rw [h1, ← hm]
  exact S1549D.n6Rep_permAct (γ : Perm (Fin 6)) m₀

theorem one_le_rAV_of_le_index (hV : ∀ v : S, v ^ 2 = 1) {X B : Subgroup (MulAut S)}
    (hB : IsA2 X B) (h : Nat.card B ≤ (fixV B).index) : 1 ≤ rAV B :=
  CFSG.Quasithin.RAV.one_le_rAV_of_le_index hV hB h

theorem exists_perm_pair {c d : Fin 6} (hcd : c ≠ d) : ∃ g : Perm (Fin 6), g 0 = c ∧ g 1 = d := by
  set d' := swap 0 c d with hd'
  have hd'0 : d' ≠ 0 := by
    rw [hd']
    intro h
    have : d = c := by
      have h2 := congrArg (swap 0 c) h
      simpa using h2
    exact hcd this.symm
  refine ⟨swap 0 c * swap 1 d', ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (by decide) hd'0.symm, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_left, hd', swap_apply_self]

theorem case6 (hV : ∀ v : S, v ^ 2 = 1) (C : Ctx G L)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) (M : N6Model L) (hGL : G = L)
    {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) : B42Case6 G L A := by
  classical
  have hcard : Nat.card S = 16 := M.card_eq
  have hJ : ffJ G = L := le_antisymm (hGL ▸ B6.ffJ_le G) (C.le_ffJ hA)
  have hrk : ∀ B : Subgroup (MulAut S), B ≤ G → B ≠ ⊥ → IsElemAbelian2 B →
      ∃ r, Nat.card B = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 2 := by
    intro B hBG hB1 hB
    obtain ⟨r, i, hr, -, hr1, hr3, -⟩ := exists_rank C hirr hcard hBG hB1 hB
    exact ⟨r, hr, hr1, card_le_four_of_le_L C (hGL ▸ hBG) hB hr hr3⟩
  have hle : ∀ B : Subgroup (MulAut S), B ≤ G → B ≠ ⊥ → IsElemAbelian2 B →
      Nat.card B ≤ (fixV B).index := by
    intro B hBG hB1 hB
    obtain ⟨r, hr, -, hr2⟩ := hrk B hBG hB1 hB
    refine card_le_index C hirr hcard hBG hB1 hB ?_
    rw [hr]
    calc 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hr2
      _ = 4 := by norm_num
  have hA4 : Nat.card A = 4 := by
    obtain ⟨r, hr, hr1, hr2⟩ := hrk A hA.1 hA.2.1 hA.2.2.1
    rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
    · exfalso
      obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
      have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
      have haL : a ∈ L := hGL ▸ hA.1 haA
      obtain ⟨t, htA, rfl⟩ := M.mem_L_iff.1 haL
      have ht1 : t ≠ 1 := by
        rintro rfl
        exact ha1' (map_one _)
      have ht2 : t * t = 1 := by
        apply M.ρ_inj
        rw [map_mul, map_one, ← pow_two]
        exact hA.2.2.1.2 _ haA
      have hz : Subgroup.zpowers (M.ρ t) = A := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haA) ?_
        rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hA.2.2.1.2 _ haA) ha1',
          hr]
        norm_num
      have hfix : Nat.card (fixV A) = 4 := by
        rw [← hz, ← MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, M.card_fixV_closure,
          ← (n6_invol t htA ht1 ht2).1]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp)
      have hoff := hA.card_le (bot_le : (⊥ : Subgroup (MulAut S)) ≤ A)
      rw [B1.card_bot_mul_card_fixV, hr, hfix, hcard] at hoff
      norm_num at hoff
    · rw [hr]
      norm_num
  refine ⟨hJ, M.alternatingNatural, ?_, ?_, ?_⟩
  · unfold rk
    rw [hA4, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact padicValNat.prime_pow 2
  · refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, B1_4_1 hV hA⟩
    exact one_le_rAV_of_le_index hV hB.isA2 (hle B hB.1 hB.2.1 hB.2.2.1)
  · intro π hR
    have hπs : Function.Surjective π := hR.1
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    obtain ⟨ι⟩ := C.iso
    have : Nontrivial ↥L := by
      have : Nontrivial (alternatingGroup (Fin 6)) :=
        alternatingGroup.nontrivial_of_three_le_card (by simp)
      exact ι.toEquiv.nontrivial
    have hπi : Function.Injective π := Bridge.injective_of_surjective_of_simple π hπs
    obtain ⟨Θ', hΘ'⟩ := exists_n6Equiv_alt hR
    set P := (A.subgroupOf L).comap π with hP
    set P' := P.map (alternatingGroup (Fin 6)).subtype with hP'
    have hAL : A ≤ L := hGL ▸ hA.1
    have hmemP : ∀ γ : ↥(alternatingGroup (Fin 6)), γ ∈ P ↔ ((π γ : ↥L) : MulAut S) ∈ A :=
      fun γ => Iff.rfl
    have hP'A : P' ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨γ, -, rfl⟩
      exact γ.2
    have hP'4 : Nat.card P' = 4 := by
      rw [hP', Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
        ← Subgroup.card_map_of_injective hπi, hP, Subgroup.map_comap_eq_self_of_surjective hπs,
        ← hA4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
    have hP'el : ∀ x ∈ P', x * x = 1 := by
      rintro _ ⟨γ, hγ, rfl⟩
      have h1 : π (γ * γ) = 1 := by
        apply Subtype.ext
        rw [map_mul, Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
        exact hA.2.2.1.2 _ ((hmemP γ).1 hγ)
      have h2 : γ * γ = 1 := hπi (by rw [h1, map_one])
      exact congrArg Subtype.val h2
    have hP'fix : 4 ≤ Nat.card {a : N6 // ∀ σ ∈ P', n6Act σ a = a} := by
      have heq : Nat.card (fixV A) = Nat.card {a : N6 // ∀ σ ∈ P', n6Act σ a = a} := by
        refine Nat.card_congr
          { toFun := fun v => ⟨Θ' v, ?_⟩
            invFun := fun a => ⟨Θ'.symm a, ?_⟩
            left_inv := fun v => Subtype.ext (Θ'.symm_apply_apply _)
            right_inv := fun a => Subtype.ext (Θ'.apply_symm_apply _) }
        · rintro _ ⟨γ, hγ, rfl⟩
          rw [show ((alternatingGroup (Fin 6)).subtype γ : Perm (Fin 6)) = γ from rfl, ← hΘ',
            v.2 _ ((hmemP γ).1 hγ)]
        · intro x hx
          obtain ⟨γ, hγ⟩ := hπs ⟨x, hAL hx⟩
          have hγP : γ ∈ P := by
            rw [hmemP, hγ]
            exact hx
          apply Θ'.injective
          have h1 := hΘ' γ (Θ'.symm a)
          rw [hγ] at h1
          rw [h1, Θ'.apply_symm_apply]
          exact a.2 _ ⟨γ, hγP, rfl⟩
      have hoff := hA.card_le (bot_le : (⊥ : Subgroup (MulAut S)) ≤ A)
      rw [B1.card_bot_mul_card_fixV, hA4, hcard, heq] at hoff
      omega
    obtain ⟨c, hc, hcP⟩ := altConj_of_fix hP'A hP'4 hP'el hP'fix
    exact ⟨c, hc, hcP⟩

theorem case3 (hV : ∀ v : S, v ^ 2 = 1) (C : Ctx G L)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤) (M : N6Model L) (hG : ∀ σ, M.ρ σ ∈ G)
    (hG' : ∀ g ∈ G, ∃ σ, M.ρ σ = g) : B42Case3 G L := by
  classical
  have hcard : Nat.card S = 16 := M.card_eq
  have hoff : IsFFStarOffender G (Subgroup.zpowers (M.ρ (swap 0 1))) := by
    refine FFC.B59.isFFStarOffender_zpowers (hG _) ?_ ?_ ?_
    · intro h
      have : swap (0 : Fin 6) 1 = 1 := M.ρ_inj (by rw [h, map_one])
      exact absurd this (by decide)
    · rw [← map_pow, pow_two, swap_mul_self, map_one]
    · rw [M.card_fixV_swap, hcard]
  have hJ : ffJ G = G := by
    refine le_antisymm (B6.ffJ_le G) ?_
    have hswap : ∀ c d : Fin 6, c ≠ d → M.ρ (swap c d) ∈ ffJ G := by
      intro c d hcd
      obtain ⟨g, hg0, hg1⟩ := exists_perm_pair hcd
      have hconj : swap c d = g * swap 0 1 * g⁻¹ := by
        rw [← hg0, ← hg1, Equiv.swap_apply_apply]
      have hoff' := B1.isFFStarOffender_conjAut hoff (hG g)
      refine B6.le_ffJ hoff' ?_
      rw [B1.mem_conjAut, hconj, map_mul, map_mul, map_inv]
      have : (M.ρ g)⁻¹ * (M.ρ g * M.ρ (swap 0 1) * (M.ρ g)⁻¹) * M.ρ g = M.ρ (swap 0 1) := by
        group
      rw [this]
      exact Subgroup.mem_zpowers _
    have htop : (⊤ : Subgroup (Perm (Fin 6))) ≤ (ffJ G).comap M.ρ := by
      rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
      rintro σ ⟨c, d, hcd, rfl⟩
      exact hswap c d hcd
    intro g hg
    obtain ⟨σ, rfl⟩ := hG' g hg
    exact htop (Subgroup.mem_top σ)
  refine ⟨⟨1, ?_, fun h => absurd h (lt_irrefl 1)⟩, ?_⟩
  · rw [hJ]
    exact M.binaryNaturalSp4 hG hG'
  set A8 := E8.map M.ρ with hA8
  have hA8G : A8 ≤ G := by
    rintro _ ⟨σ, -, rfl⟩
    exact hG σ
  have hA8el : IsElemAbelian2 A8 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, e8_comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, pow_two, e8_sq a ha, map_one]
  have hA81 : A8 ≠ ⊥ := by
    intro h
    have hmem : M.ρ (swap 0 1) ∈ A8 := ⟨swap 0 1, by simp [E8, e8List], rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have : swap (0 : Fin 6) 1 = 1 := M.ρ_inj (by rw [hmem, map_one])
    exact absurd this (by decide)
  have hA8c : Nat.card A8 = 8 := by
    obtain ⟨r, i, hr, -, -, hr3, -⟩ := exists_rank C hirr hcard hA8G hA81 hA8el
    have hge : 8 ≤ Nat.card A8 := by
      rw [hA8, Subgroup.card_map_of_injective M.ρ_inj]
      have := length_le_card E8 e8List e8_nodup fun x hx => hx
      simpa [e8List] using this
    have : r = 3 := by
      by_contra h
      have : r ≤ 2 := by omega
      have : 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    rw [hr, this]
    norm_num
  have hA8fix : Nat.card (fixV A8) = 4 := M.card_fixV_e8
  have hA8off : IsFFStarOffender G A8 := by
    refine ⟨hA8G, hA81, hA8el, fun B hB => ?_⟩
    rw [hA8c, hA8fix]
    by_cases hB1 : B = ⊥
    · rw [hB1, B1.card_bot_mul_card_fixV, hcard]
      norm_num
    have hBel : IsElemAbelian2 B :=
      ⟨fun a ha b hb => hA8el.1 a (hB ha) b (hB hb), fun a ha => hA8el.2 a (hB ha)⟩
    obtain ⟨r, i, hr, -, -, hr3, -⟩ := exists_rank C hirr hcard (hB.trans hA8G) hB1 hBel
    rcases (show r ≤ 2 ∨ r = 3 by omega) with hr2 | rfl
    · have h1 := card_le_index C hirr hcard (hB.trans hA8G) hB1 hBel (by
        rw [hr]
        calc 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hr2
          _ = 4 := by norm_num)
      calc Nat.card B * Nat.card (fixV B) ≤ (fixV B).index * Nat.card (fixV B) :=
            Nat.mul_le_mul_right _ h1
        _ = 16 := by rw [Subgroup.index_mul_card, hcard]
        _ ≤ 8 * 4 := by norm_num
    · have hBA : B = A8 := Subgroup.eq_of_le_of_card_ge hB (by rw [hA8c, hr]; norm_num)
      rw [hBA, hA8c, hA8fix]
  refine qOf_eq_of_offenders hV (by norm_num)
    (fun B hB => two_thirds_le_rAV C hirr hcard hB.1 hB.2.1 hB.2.2.1) ⟨A8, hA8off, ?_⟩
  have hidx : (fixV A8).index = 2 ^ 2 := by
    have h1 := Subgroup.index_mul_card (fixV A8)
    rw [hA8fix, hcard] at h1
    omega
  have hrk : rk A8 = 3 := by
    unfold rk
    rw [hA8c, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact padicValNat.prime_pow 3
  have hrkI : rkIdx (fixV A8) = 2 := by
    unfold rkIdx
    rw [hidx]
    exact padicValNat.prime_pow 2
  unfold rAV
  rw [hrk, hrkI]
  norm_num

end B42Alt6

theorem asB42Alt6_holds : AsB42Alt6 := by
  unfold AsB42Alt6 AsB42For
  intro V _ _ hV G L hB hT A hA
  have C := B42Alt6.ctx_of_b4Hyp hB hT
  have hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ := hB.2.2.2
  have hS2 : ∀ s : V, s * s = 1 := fun s => by simpa [pow_two] using hV s
  have h64 := B42Alt6.card_le_sixtyfour C hirr hA
  obtain ⟨M⟩ := B42Alt6.exists_n6Model hS2 C hirr h64
  obtain ⟨ι⟩ := C.iso
  have hGρ : ∀ g ∈ G, ∃ σ, M.ρ σ = g := by
    intro g hg
    refine M.le_range hS2 ι ?_
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => C.normal g hg l hl, fun hl => ?_⟩
    have := C.normal g⁻¹ (G.inv_mem hg) _ hl
    simpa [mul_assoc] using this
  by_cases hGL : G ≤ L
  · have hGL' : G = L := le_antisymm hGL C.le_G
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (B42Alt6.case6 hV C hirr M hGL' hA))))))
  · obtain ⟨g, hg, hgL⟩ := Set.not_subset.1 hGL
    obtain ⟨σ₀, rfl⟩ := hGρ g hg
    have hσ₀ : σ₀ ∉ alternatingGroup (Fin 6) := fun h => hgL (M.ρ_mem_L h)
    have hG : ∀ σ, M.ρ σ ∈ G := by
      intro σ
      by_cases hσ : σ ∈ alternatingGroup (Fin 6)
      · exact C.le_G (M.ρ_mem_L hσ)
      · have h1 : σ * σ₀⁻¹ ∈ alternatingGroup (Fin 6) := by
          rw [Equiv.Perm.mem_alternatingGroup] at hσ hσ₀ ⊢
          rw [map_mul, map_inv]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
          · exact absurd h hσ
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h' | h'
          · exact absurd h' hσ₀
          rw [h, h']
          decide
        have h2 : σ = σ * σ₀⁻¹ * σ₀ := by group
        rw [h2, map_mul]
        exact G.mul_mem (C.le_G (M.ρ_mem_L h1)) hg
    exact Or.inr (Or.inr (Or.inl (B42Alt6.case3 hV C hirr M hG hGρ)))

end CFSG.Quasithin
