module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoSetup
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdRRoot

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.StandardType.TableBUE
  CFSG.StandardType.SmallU CFSG.StandardType.UnitTB CFSG.StandardType.LineU
  CFSG.StandardType.IOneUDvdR
open scoped commutatorElement

theorem root_downstairs {Lb : Type} [Group Lb] [Finite Lb] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {φ : ↥(unitarySU 2 1 K 6) →* Lb} (hM : Model φ)
    {Ab : Subgroup (MulAut Lb)} (hAb : CFSG.Open.IsElemAbelian 3 Ab)
    (hdiag : ∀ a ∈ Ab, ∃ t : Fin 6 → K, ActsDiagU φ a t) {s t : Fin 6} (hst : s ≠ t)
    (hpair : ∀ a ∈ Ab, ∀ σ : Fin 6 → Kˣ, ActsU φ a σ → σ s = σ t)
    (hr : 3 ^ 3 ≤ Nat.card Ab) :
    ∃ (g : MulAut Lb) (S : Finset (Fin 6)), GGIsEndNode Ab g ∧ s ∈ S ∧ t ∈ S ∧
      (S.card = 5 ∨ S.card = 4) ∧ LargeEvenLayer (ggFix g) = (blockSU S).map φ ∧
      (S.card = 4 → ∀ g₁ : MulAut Lb, GGIsEndNode Ab g₁ →
        ∃ S₁ : Finset (Fin 6), S₁.card = 4 ∧
          LargeEvenLayer (ggFix g₁) = (blockSU S₁).map φ) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hd3 : 3 ≤ 6 := by norm_num
  have hAp : ∀ a ∈ Ab, a ^ 3 = 1 := hAb.2
  obtain ⟨ν, hν⟩ := exists_nu_actsU hM hd3 hdiag s
  have hs1 : ∀ g : ↥Ab, ν g s = 1 := fun g => (hν g).2
  have ht1 : ∀ g : ↥Ab, ν g t = 1 := fun g => by
    rw [← hpair g.1 g.2 (ν g) (hν g).1, (hν g).2]
  have hpow : ∀ (g : ↥Ab) (k : Fin 6), ((ν g k : Kˣ) : K) ^ 3 = 1 := by
    intro g k
    have h := ActsU.pow_ratio hM hd3 (hν g).1 (hAp g g.2) k s
    rw [(hν g).2, inv_one, mul_one] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    have h1 := (hν g).1
    rw [hg] at h1
    exact ActsU.eq_one_of_const hM h1 s (fun _ _ => rfl)
  have hcoord : ∀ (g' : ↥Ab) (i : Fin 6), (cls (ν g') i).card = 5 →
      ∃ c, ν g' c ≠ 1 ∧ ∀ k, k ≠ c → ν g' k = 1 := by
    intro g' i h5
    have hc1 : (cls (ν g') i)ᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h5]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hc1
    have hmem : ∀ k, k ∉ cls (ν g') i ↔ k = c := fun k => by
      have := Finset.ext_iff.mp hc k
      simpa using this
    have hts : ν g' t = ν g' s := (hpair g'.1 g'.2 (ν g') (hν g').1).symm
    have hsmem : s ∈ cls (ν g') i := by
      by_contra hs
      have hs' := (hmem s).mp hs
      have ht' : t ∉ cls (ν g') i := fun ht => hs (by
        rw [mem_cls] at ht ⊢
        rw [← hts]
        exact ht)
      exact hst (hs'.trans ((hmem t).mp ht').symm)
    have hi1 : ν g' i = 1 := by
      rw [← hs1 g']
      exact (mem_cls.mp hsmem).symm
    refine ⟨c, fun h => (hmem c).mpr rfl (mem_cls.mpr (by rw [h, hi1])), fun k hk => ?_⟩
    have hk' : k ∈ cls (ν g') i := by
      by_contra hk''
      exact hk ((hmem k).mp hk'')
    rw [mem_cls.mp hk', hi1]
  by_cases hI : ∃ (g : ↥Ab) (c : Fin 6), ν g c ≠ 1 ∧ ∀ k, k ≠ c → ν g k = 1
  ·
    obtain ⟨g, c, hgc, hg1⟩ := hI
    have hcs : c ≠ s := fun h => hgc (h ▸ hs1 g)
    have hct : c ≠ t := fun h => hgc (h ▸ ht1 g)
    set S : Finset (Fin 6) := Finset.univ.erase c with hSdef
    have hS5 : S.card = 5 := by
      rw [hSdef, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
        Fintype.card_fin]
    have hsS : s ∈ S := Finset.mem_erase.mpr ⟨hcs.symm, Finset.mem_univ s⟩
    have htS : t ∈ S := Finset.mem_erase.mpr ⟨hct.symm, Finset.mem_univ t⟩
    have hτ : IsNodeOn (ν g) S := by
      constructor
      · intro i hi j hj
        rw [hg1 i (Finset.mem_erase.mp hi).1, hg1 j (Finset.mem_erase.mp hj).1]
      · intro i hi j hj
        have hic : i = c := by
          by_contra h'
          exact hi (Finset.mem_erase.mpr ⟨h', Finset.mem_univ i⟩)
        subst hic
        rw [hg1 j hj]
        exact fun e => hgc e.symm
    have hbig : BigOK 1 S := Or.inl (by omega)
    obtain ⟨hlay, hcomp⟩ := layer_eq_block_of_isNodeOn hM (hν g).1 hτ hbig
    have hle : LargeEvenLayer (ggFix (g : MulAut Lb)) ≤ ggFix (g : MulAut Lb) :=
      sSup_le fun _ hK' => hK'.1
    have hprim : IsPrimitiveRoot ((ν g c : Kˣ) : K) 3 :=
      IsPrimitiveRoot.coe_units_iff.mpr
        (IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (by
          apply Units.ext
          simpa using hpow g c) hgc))
    have hcentEnd : ∀ a' ∈ Ab, ((∀ j ∈ LargeEvenLayer (ggFix (g : MulAut Lb)), a' j = j) ↔
        a' ∈ Subgroup.zpowers (g : MulAut Lb)) := by
      intro a' ha'
      constructor
      · intro hfix
        have hfixU : ∀ y ∈ blockSU S, a' (φ y) = φ y := by
          intro y hy
          apply hfix
          rw [hlay]
          exact ⟨y, hy, rfl⟩
        have hconst := ActsU.const_of_fix hM (hν ⟨a', ha'⟩).1 (k₀ := c)
          (by simp [hSdef]) hfixU
        have hy1 : ∀ k, k ≠ c → ν ⟨a', ha'⟩ k = 1 := fun k hk =>
          (hconst k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) s hsS).trans (hs1 _)
        obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one (hpow ⟨a', ha'⟩ c)
        have hνeq : ν ⟨a', ha'⟩ = ν (g ^ j) := by
          funext k
          by_cases hk : k = c
          · subst hk
            rw [map_pow, Pi.pow_apply]
            exact Units.ext (by rw [Units.val_pow_eq_pow_val, hj])
          · rw [hy1 k hk, map_pow, Pi.pow_apply, hg1 k hk, one_pow]
        have hga : (⟨a', ha'⟩ : ↥Ab) = g ^ j := hinj hνeq
        refine Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), ?_⟩
        have := congrArg Subtype.val hga
        simpa using this.symm
      · intro hz j hj
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact IOneUDelta.zpow_fix_of (hle hj) k
    have hg1' : (g : MulAut Lb) ≠ 1 := by
      intro h1
      have hg' : g = 1 := Subtype.ext (by simpa using h1)
      rw [hg', map_one] at hgc
      exact hgc rfl
    refine ⟨(g : MulAut Lb), S, ⟨g.2, hg1', hcomp, hcentEnd⟩, hsS, htS, Or.inl hS5, hlay,
      fun h4 => absurd hS5 (by omega)⟩
  ·
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp (TableBUE.dvd_card_sub_one hK hpq)
    set F : Finset (Fin 6) := ({s, t} : Finset (Fin 6))ᶜ with hFdef
    have hF : ∀ (g : ↥Ab) (k : Fin 6), k ∉ F → ν g k = 1 := by
      intro g k hk
      simp only [hFdef, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
        not_not] at hk
      rcases hk with h | h
      · rw [h]
        exact hs1 g
      · rw [h]
        exact ht1 g
    obtain ⟨v, hvmul, hvzero, hvform, hvinj, hvpow, M, hM_mem, hrank⟩ :=
      exists_zmod_span hζ F ν hpow hF hinj 3 hr
    have hFcard : Fintype.card ↥F = 4 := by
      rw [Fintype.card_coe, hFdef, Finset.card_compl, Fintype.card_fin, Finset.card_pair hst]
    have hp2 : (3 : ℕ) ≠ 2 := by norm_num
    have h3F : 2 < Fintype.card ↥F := by omega
    have hdim : Fintype.card ↥F - 1 ≤ Module.finrank (ZMod 3) M := by omega
    have hnode : ∃ g : ↥Ab, ∃ T : Finset (Fin 6), T.card ≤ 2 ∧ (∀ i, ν g i ≠ 1 → i ∈ T) ∧
        (∀ i j, ν g i ≠ 1 → ν g j = ν g i → j = i) ∧ (∃ i, ν g i ≠ 1) ∧
        (∀ y ∈ M, (∀ k : ↥F, ν g k.1 = 1 → y k = 0) → ∃ α : ZMod 3, y = α • v g) := by
      rcases IOneUDvd.exists_endNode_of_finrank hp2 h3F hdim with
        ⟨c, hc⟩ | ⟨c, c', hcc', x, hxM, hx0, hxc, hxc', hxne, huniq⟩
      ·
        exfalso
        apply hI
        obtain ⟨g, hg⟩ := (hM_mem _).mp hc
        have hvne : ∀ k : ↥F, k ≠ c → v g k = 0 := fun k hk => by
          rw [hg, Pi.single_apply, if_neg hk]
        have hν1 : ∀ k : ↥F, k ≠ c → ν g k.1 = 1 := fun k hk => (hvzero g k).mp (hvne k hk)
        have hcne : ν g c.1 ≠ 1 := fun h => by
          have h1 := (hvzero g c).mpr h
          rw [hg, Pi.single_apply, if_pos rfl] at h1
          exact one_ne_zero h1
        refine ⟨g, c.1, hcne, fun k hk => ?_⟩
        by_cases hkF : k ∈ F
        · exact hν1 ⟨k, hkF⟩ (fun h => hk (congrArg Subtype.val h))
        · exact hF g k hkF
      · obtain ⟨g, hg⟩ := (hM_mem _).mp hxM
        have hν1 : ∀ k : ↥F, k ≠ c → k ≠ c' → ν g k.1 = 1 := fun k hk1 hk2 =>
          (hvzero g k).mp (by rw [hg]; exact hx0 k hk1 hk2)
        have hdistν : ν g c.1 ≠ ν g c'.1 := by
          intro h
          apply hxne
          have h' : v g c = v g c' := by rw [hvform, hvform, h]
          rw [hg] at h'
          exact h'
        have hcne : ν g c.1 ≠ 1 := fun h => hxc (by
          rw [← hg]
          exact (hvzero g c).mpr h)
        have hTmem : ∀ i, ν g i ≠ 1 → i = c.1 ∨ i = c'.1 := by
          intro i hi
          by_cases hiF : i ∈ F
          · by_cases hk1 : (⟨i, hiF⟩ : ↥F) = c
            · exact Or.inl (congrArg Subtype.val hk1)
            · by_cases hk2 : (⟨i, hiF⟩ : ↥F) = c'
              · exact Or.inr (congrArg Subtype.val hk2)
              · exact absurd (hν1 ⟨i, hiF⟩ hk1 hk2) hi
          · exact absurd (hF g i hiF) hi
        refine ⟨g, {c.1, c'.1}, Finset.card_le_two, fun i hi => ?_, ?_, ⟨c.1, hcne⟩, ?_⟩
        · rcases hTmem i hi with h | h
          · rw [h]
            simp
          · rw [h]
            simp
        · intro i j hi hj
          have hj' : ν g j ≠ 1 := by
            rw [hj]
            exact hi
          rcases hTmem i hi with hi' | hi' <;> rcases hTmem j hj' with hj'' | hj''
          · rw [hi', hj'']
          · rw [hi', hj''] at hj
            exact absurd hj.symm hdistν
          · rw [hi', hj''] at hj
            exact absurd hj hdistν
          · rw [hi', hj'']
        · intro y hy hyk
          obtain ⟨α, hα⟩ := huniq y hy (fun k hk1 hk2 => hyk k (hν1 k hk1 hk2))
          exact ⟨α, by rw [hg]; exact hα⟩
    obtain ⟨g, T, hTcard, hT, hdist, ⟨c₀, hc₀⟩, hlin⟩ := hnode
    have hsS : s ∈ cls (ν g) s := mem_cls.mpr rfl
    have htS : t ∈ cls (ν g) s := mem_cls.mpr (by rw [ht1 g, hs1 g])
    have hτ : IsNodeOn (ν g) (cls (ν g) s) := by
      refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
      · rw [mem_cls.mp hi, mem_cls.mp hj]
      · intro hν'
        have hi1 : ν g i ≠ 1 := fun h1 => hi (mem_cls.mpr (by rw [h1, hs1 g]))
        exact hj (hdist i j hi1 hν')
    have hScard : 4 ≤ (cls (ν g) s).card := by
      have hsub : (cls (ν g) s)ᶜ ⊆ T := fun i hi => hT i (fun h1 =>
        (Finset.mem_compl.mp hi) (mem_cls.mpr (by rw [h1, hs1 g])))
      have h1 := Finset.card_le_card hsub
      have h2 : (cls (ν g) s)ᶜ.card = 6 - (cls (ν g) s).card := by
        rw [Finset.card_compl, Fintype.card_fin]
      omega
    have hBig : BigOK 1 (cls (ν g) s) := Or.inl hScard
    have hcent : ∀ a' ∈ Ab, (∀ y ∈ blockSU (K := K) (n := 1) (cls (ν g) s), a' (φ y) = φ y) →
        a' ∈ Subgroup.zpowers (g : MulAut Lb) := by
      intro a' ha' hfix
      have hk₀ : c₀ ∉ cls (ν g) s := fun h => hc₀ ((mem_cls.mp h).trans (hs1 g))
      have hconst := ActsU.const_of_fix hM (hν ⟨a', ha'⟩).1 hk₀ hfix
      have hyS : ∀ k : ↥F, ν g k.1 = 1 → ν ⟨a', ha'⟩ k.1 = 1 := fun k hk => by
        have hkS : k.1 ∈ cls (ν g) s := mem_cls.mpr (by rw [hk, hs1 g])
        exact (hconst k.1 hkS s hsS).trans (hs1 _)
      obtain ⟨α, hα⟩ := hlin (v ⟨a', ha'⟩) ((hM_mem _).mpr ⟨⟨a', ha'⟩, rfl⟩)
        (fun k hk => (hvzero _ k).mpr (hyS k hk))
      have hv2 : v ⟨a', ha'⟩ = v (g ^ α.val) := by
        rw [hvpow, ZMod.natCast_zmod_val]
        exact hα
      have hEq : (⟨a', ha'⟩ : ↥Ab) = g ^ α.val := hvinj hv2
      have h1 : a' = (g : MulAut Lb) ^ α.val := by
        have := congrArg Subtype.val hEq
        simpa using this
      rw [h1]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    obtain ⟨hcomp, hlay, hcentEnd⟩ := centEnd_of_node hM (hν g).1 hτ hBig hcent
    have hSne : cls (ν g) s ≠ Finset.univ := by
      intro h
      have hc' : c₀ ∈ cls (ν g) s := by
        rw [h]
        exact Finset.mem_univ _
      exact hc₀ ((mem_cls.mp hc').trans (hs1 g))
    have hg1 : (g : MulAut Lb) ≠ 1 := by
      intro h
      apply hc₀
      have hg' : g = 1 := Subtype.ext (by simpa using h)
      rw [hg', map_one]
      rfl
    have hSlt : (cls (ν g) s).card < 6 := by
      have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hSne)
      simpa using this
    have hnot5 : (cls (ν g) s).card ≠ 5 := fun h5 => hI ⟨g, hcoord g s h5⟩
    have hS4 : (cls (ν g) s).card = 4 := by omega
    refine ⟨(g : MulAut Lb), cls (ν g) s, ⟨g.2, hg1, hcomp, hcentEnd⟩, hsS, htS, Or.inr hS4,
      hlay, fun _ g₁ hg₁ => ?_⟩
    have hg₁Ab : g₁ ∈ Ab := hg₁.1
    obtain ⟨i, hbig₁⟩ := exists_bigOK_cls hM (by norm_num) le_rfl (hν ⟨g₁, hg₁Ab⟩).1 hg₁.2.2.1
    have hlay₁ := layer_eq_block hM (hν ⟨g₁, hg₁Ab⟩).1 (cls_isCls (ν ⟨g₁, hg₁Ab⟩) i)
      (isQuasisimple_block hM hbig₁) hg₁.2.2.1
    refine ⟨cls (ν ⟨g₁, hg₁Ab⟩) i, ?_, hlay₁⟩
    have hge4 : 4 ≤ (cls (ν ⟨g₁, hg₁Ab⟩) i).card := by
      rcases hbig₁ with h | ⟨h2, -⟩
      · exact h
      · omega
    have hne6 : (cls (ν ⟨g₁, hg₁Ab⟩) i).card ≠ 6 := by
      intro h6
      apply hg₁.2.1
      refine ActsU.eq_one_of_const hM (hν ⟨g₁, hg₁Ab⟩).1 i fun a b => ?_
      have hall : ∀ k, k ∈ cls (ν ⟨g₁, hg₁Ab⟩) i := fun k => by
        have := Finset.eq_univ_of_card (cls (ν ⟨g₁, hg₁Ab⟩) i) (by rw [h6]; simp)
        rw [this]
        exact Finset.mem_univ k
      rw [mem_cls.mp (hall a), mem_cls.mp (hall b)]
    have hne5 : (cls (ν ⟨g₁, hg₁Ab⟩) i).card ≠ 5 := fun h5 => hI ⟨⟨g₁, hg₁Ab⟩, hcoord _ i h5⟩
    have hle6 : (cls (ν ⟨g₁, hg₁Ab⟩) i).card ≤ 6 := by
      simpa using Finset.card_le_univ (cls (ν ⟨g₁, hg₁Ab⟩) i)
    omega

end CFSG.StandardType.USixTwo

end
