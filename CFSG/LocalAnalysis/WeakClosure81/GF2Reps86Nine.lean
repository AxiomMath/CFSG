module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Ind
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Recognition
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv Equiv.Perm

section Perm

private def N9Spread (σ : Perm (Fin 9)) (p q : Fin 9) : Prop :=
  ∀ a b : Fin 9, ∃ z, z ≠ p ∧ z ≠ q ∧ z ≠ a ∧ z ≠ b ∧ σ z ≠ z

private theorem n9_exists_two_fixed {σ : Perm (Fin 9)} (hσ : σ ^ 2 = 1)
    (hodd : σ ∉ alternatingGroup (Fin 9)) : ∃ p q : Fin 9, p ≠ q ∧ σ p = p ∧ σ q = q := by
  by_contra hcon
  refine hodd ?_
  have hle : Fintype.card (Function.fixedPoints σ) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    by_contra hab
    exact hcon ⟨a, b, fun h => hab (Subtype.ext h), ha, hb⟩
  rw [mem_alternatingGroup, sign_of_pow_two_eq_one hσ, Fintype.card_fin]
  have h4 : (9 - Fintype.card (Function.fixedPoints σ)) / 2 = 4 := by omega
  rw [h4]
  decide

private theorem n9_spread_of_fixed {σ : Perm (Fin 9)} (hσ1 : σ ≠ 1) (hsw : ¬ σ.IsSwap)
    {p q : Fin 9} (hp : σ p = p) (hq : σ q = q) : N9Spread σ p q := by
  intro a b
  by_contra hcon
  push Not at hcon
  have hsub : σ.support ⊆ {a, b} := fun z hz => by
    rw [mem_support] at hz
    by_contra hzab
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzab
    exact hz (hcon z (fun h => hz (by rw [h]; exact hp)) (fun h => hz (by rw [h]; exact hq))
      hzab.1 hzab.2)
  have hcard : σ.support.card ≤ 2 := (Finset.card_le_card hsub).trans Finset.card_le_two
  have h0 : σ.support.card ≠ 0 := fun h => hσ1 (card_support_eq_zero.1 h)
  have h2 : σ.support.card ≠ 2 := fun h => hsw (card_support_eq_two.1 h)
  exact card_support_ne_one σ (by omega)

private theorem n9_exists_swapped_pair {σ : Perm (Fin 9)} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hfix : ∀ a b : Fin 9, σ a = a → σ b = b → a = b) :
    ∃ p q : Fin 9, p ≠ q ∧ σ p = q ∧ σ q = p ∧ N9Spread σ p q := by
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have hσσ : σ (σ p) = p := by
    have := congrArg (fun g : Perm (Fin 9) => g p) hσ2
    simpa [pow_two] using this
  refine ⟨p, σ p, fun h => hp h.symm, rfl, hσσ, fun a b => ?_⟩
  by_contra hcon
  push Not at hcon
  have hcard : 1 < (({p, σ p, a, b} : Finset (Fin 9))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_four (a := p) (b := σ p) (c := a) (d := b)
    omega
  obtain ⟨z₁, z₂, hz₁, hz₂, hne⟩ := Finset.one_lt_card_iff.1 hcard
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hz₁ hz₂
  exact hne (hfix z₁ z₂ (hcon z₁ hz₁.1 hz₁.2.1 hz₁.2.2.1 hz₁.2.2.2)
    (hcon z₂ hz₂.1 hz₂.2.1 hz₂.2.2.1 hz₂.2.2.2))

private theorem n9_exists_stable_pair {σ : Perm (Fin 9)} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hsw : ¬ σ.IsSwap) :
    ∃ p q : Fin 9, p ≠ q ∧ (σ p = p ∧ σ q = q ∨ σ p = q ∧ σ q = p) ∧ N9Spread σ p q := by
  by_cases h : ∃ p q : Fin 9, p ≠ q ∧ σ p = p ∧ σ q = q
  · obtain ⟨p, q, hpq, hp, hq⟩ := h
    exact ⟨p, q, hpq, Or.inl ⟨hp, hq⟩, n9_spread_of_fixed hσ1 hsw hp hq⟩
  · obtain ⟨p, q, hpq, hp, hq, hs⟩ := n9_exists_swapped_pair hσ2 hσ1 fun a b ha hb => by
      by_contra hab
      exact h ⟨a, b, hab, ha, hb⟩
    exact ⟨p, q, hpq, Or.inr ⟨hp, hq⟩, hs⟩

private theorem n9_restrict_ne {σ : Perm (Fin 9)} {p q : Fin 9} (hs : N9Spread σ p q)
    {ι : Fin 7 ↪ Fin 9} (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) {τ : Perm (Fin 7)}
    (hτ : ∀ i, ι (τ i) = σ (ι i)) : τ ≠ 1 ∧ ¬ τ.IsSwap := by
  have key : ¬ ∃ x y : Fin 7, ∀ i, i ≠ x → i ≠ y → τ i = i := by
    rintro ⟨x, y, hxy⟩
    obtain ⟨z, hzp, hzq, hza, hzb, hz⟩ := hs (ι x) (ι y)
    obtain ⟨i, rfl⟩ := (hι z).2 ⟨hzp, hzq⟩
    refine hz ?_
    rw [← hτ, hxy i (fun h => hza (congrArg ι h)) (fun h => hzb (congrArg ι h))]
  refine ⟨fun h => key ⟨0, 0, fun i _ _ => by rw [h]; rfl⟩, ?_⟩
  rintro ⟨x, y, -, h⟩
  exact key ⟨x, y, fun i hix hiy => by rw [h]; exact swap_apply_of_ne_of_ne hix hiy⟩

private theorem n9_exists_even_lift {ι : Fin 7 ↪ Fin 9} {p q : Fin 9} (hpq : p ≠ q)
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) {τ : Perm (Fin 7)} (hτ : sign τ = -1) :
    ∃ g : Perm (Fin 9), g ∈ alternatingGroup (Fin 9) ∧ g ∈ permSetStab (Set.range ι) ∧
      ∀ i, g (ι i) = ι (τ i) := by
  refine ⟨viaEmbedding τ ι * swap p q, ?_, ?_, fun i => ?_⟩
  · rw [mem_alternatingGroup, map_mul, sign_viaEmbedding, hτ, sign_swap hpq]
    decide
  · refine Subgroup.mul_mem _ (fun x => ?_) (swap_mem_permSetStab hι)
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [viaEmbedding_apply]
      exact ⟨fun _ => ⟨i, rfl⟩, fun _ => ⟨_, rfl⟩⟩
    · rw [viaEmbedding_apply_of_notMem _ _ _ hx]
  · have hip : ι i ≠ p := ((hι _).1 ⟨i, rfl⟩).1
    have hiq : ι i ≠ q := ((hι _).1 ⟨i, rfl⟩).2
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hip hiq, viaEmbedding_apply]

end Perm

section Step

variable {V : Type} [CommGroup V]

private theorem n9_natVia_of_restrict (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {ψ : ↥H →* Perm (Fin 9)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 9) ≤ ψ.range) (ι : Fin 7 ↪ Fin 9) {K : Subgroup (MulAut V)}
    (hK : K ≤ preSub ψ (permSetStab (Set.range ι)))
    (hlift : ∀ σ : alternatingGroup (Fin 7), ∃ k : ↥K, restrictHom ψ ι K hK k = σ ∧
      ∃ hk : (k : MulAut V) ∈ H, ψ ⟨k, hk⟩ = altLift ι σ)
    (hnat : NatVia (restrictHom ψ ι K hK) (commV K)) : NatVia ψ (commV H) :=
  natVia_commV_of_natShape (by norm_num) hψ hA (natShape_of_stab₂ hV (by norm_num) ι
    (by norm_num) _ (natShape_altRho_comp_altLift hψ hA _ ι hlift hnat))

variable [Finite V]

private theorem n9_even (h7 : T86 7) (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {ψ : ↥H →* Perm (Fin 9)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 9) ≤ ψ.range) {t : ↥H} (ht2 : t ^ 2 = 1) (ht1 : ψ t ≠ 1)
    (htsw : ¬ (ψ t).IsSwap) (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8)
    (hev : ψ t ∈ alternatingGroup (Fin 9)) : NatVia ψ (commV H) := by
  have hσ2 : ψ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  obtain ⟨p, q, hpq, hstab, hs⟩ := n9_exists_stable_pair hσ2 ht1 htsw
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne_ne (m := 7) (by norm_num) hpq
  have hD : preSub ψ (alternatingGroup (Fin 9) ⊓ permSetStab (Set.range ι)) ≤
      preSub ψ (permSetStab (Set.range ι)) :=
    preSub_mono inf_le_right
  have hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin 9) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ preSub ψ (alternatingGroup (Fin 9) ⊓ permSetStab (Set.range ι)) :=
    fun h h1 h2 => coe_mem_preSub.2 ⟨h1, h2⟩
  have hinj : Function.Injective (restrictHom ψ ι _ hD) :=
    restrictHom_injective (hK := hD) hψ fun k hk => by
      have hk2 := (coe_mem_preSub (ψ := ψ) (x := Subgroup.inclusion (hD.trans preSub_le) k)).1
        k.2
      exact eq_one_of_apply_eq_of_range_ne_ne hpq hι hk2.2 hk2.1 hk
  have htK : (t : MulAut V) ∈ preSub ψ (alternatingGroup (Fin 9) ⊓ permSetStab (Set.range ι)) :=
    hKmem t hev (mem_permSetStab_of_pair hι hstab)
  have ht'2 : (⟨(t : MulAut V), htK⟩ : ↥(preSub ψ (alternatingGroup (Fin 9) ⊓
      permSetStab (Set.range ι)))) ^ 2 = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val ht2)
  have hκt : ∀ i, ι (restrictHom ψ ι _ hD ⟨(t : MulAut V), htK⟩ i) = ψ t (ι i) := fun i =>
    restrictHom_apply_apply (hK := hD) ⟨(t : MulAut V), htK⟩ i
  obtain ⟨hκ1, hκsw⟩ := n9_restrict_ne hs hι hκt
  rcases h7 V hV _ (restrictHom ψ ι _ hD) hinj
      (alternatingGroup_le_range_restrictHom hA hKmem) _ ht'2 hκ1 hκsw hidx with
    hnat | ⟨-, hrange⟩
  · exact n9_natVia_of_restrict hV hψ hA ι hD (exists_restrictHom_eq_altLift hA hKmem) hnat
  · exfalso
    obtain ⟨g, hgA, hgS, hg⟩ := n9_exists_even_lift hpq hι
      (sign_swap (show (0 : Fin 7) ≠ 1 by decide))
    obtain ⟨h, hh⟩ := hA hgA
    have hhK := hKmem h (by rw [hh]; exact hgA) (by rw [hh]; exact hgS)
    have hmem : swap (0 : Fin 7) 1 ∈ (restrictHom ψ ι _ hD).range :=
      ⟨⟨h, hhK⟩, (restrictHom_eq_iff _ _).2 fun i => by
        change ψ h (ι i) = _
        rw [hh]
        exact hg i⟩
    rw [hrange, mem_alternatingGroup, sign_swap (show (0 : Fin 7) ≠ 1 by decide)] at hmem
    exact absurd hmem (by decide)

private theorem n9_odd (h7 : T86 7) (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {ψ : ↥H →* Perm (Fin 9)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 9) ≤ ψ.range) {t : ↥H} (ht2 : t ^ 2 = 1) (ht1 : ψ t ≠ 1)
    (htsw : ¬ (ψ t).IsSwap) (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8)
    (hodd : ψ t ∉ alternatingGroup (Fin 9)) : NatVia ψ (commV H) := by
  have hσ2 : ψ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  obtain ⟨p, q, hpq, hp, hq⟩ := n9_exists_two_fixed hσ2 hodd
  have hs := n9_spread_of_fixed ht1 htsw hp hq
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne_ne (m := 7) (by norm_num) hpq
  have hpn : p ∉ Set.range ι := fun h => ((hι p).1 h).1 rfl
  have hqn : q ∉ Set.range ι := fun h => ((hι q).1 h).2 rfl
  have hout : ∀ z, z ∉ Set.range ι → z = p ∨ z = q := fun z hz => by
    by_contra hcon
    push Not at hcon
    exact hz ((hι z).2 hcon)
  let S : Subgroup (Perm (Fin 9)) :=
    MulAction.stabilizer (Perm (Fin 9)) p ⊓ MulAction.stabilizer (Perm (Fin 9)) q
  have hS : ∀ g : Perm (Fin 9), g ∈ S ↔ g p = p ∧ g q = q := fun g => Iff.rfl
  have hD : preSub ψ S ≤ preSub ψ (permSetStab (Set.range ι)) :=
    preSub_mono fun g hg => mem_permSetStab_of_pair hι (Or.inl ((hS g).1 hg))
  have hinj : Function.Injective (restrictHom ψ ι (preSub ψ S) hD) :=
    restrictHom_injective (hK := hD) hψ fun k hk => by
      have hk2 := (hS _).1 ((coe_mem_preSub (ψ := ψ)
        (x := Subgroup.inclusion (hD.trans preSub_le) k)).1 k.2)
      refine Equiv.ext fun z => ?_
      rw [Perm.one_apply]
      by_cases hz : z ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hz
        exact hk i
      · rcases hout z hz with rfl | rfl
        · exact hk2.1
        · exact hk2.2
  have hlift : ∀ σ : alternatingGroup (Fin 7), ∃ k : ↥(preSub ψ S),
      restrictHom ψ ι (preSub ψ S) hD k = σ ∧
        ∃ hk : (k : MulAut V) ∈ H, ψ ⟨k, hk⟩ = altLift ι σ := fun σ => by
    obtain ⟨h, hh⟩ := hA (altLift ι σ).2
    have hhK : (h : MulAut V) ∈ preSub ψ S := coe_mem_preSub.2 ((hS _).2
      ⟨by rw [hh]; exact altLift_apply_of_notMem ι σ hpn,
        by rw [hh]; exact altLift_apply_of_notMem ι σ hqn⟩)
    exact ⟨⟨h, hhK⟩, restrictHom_eq_of_eq_altLift hh, h.2, hh⟩
  have htK : (t : MulAut V) ∈ preSub ψ S := coe_mem_preSub.2 ((hS _).2 ⟨hp, hq⟩)
  have ht'2 : (⟨(t : MulAut V), htK⟩ : ↥(preSub ψ S)) ^ 2 = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val ht2)
  have hκt : ∀ i, ι (restrictHom ψ ι (preSub ψ S) hD ⟨(t : MulAut V), htK⟩ i) = ψ t (ι i) :=
    fun i => restrictHom_apply_apply (hK := hD) ⟨(t : MulAut V), htK⟩ i
  obtain ⟨hκ1, hκsw⟩ := n9_restrict_ne hs hι hκt
  rcases h7 V hV _ (restrictHom ψ ι (preSub ψ S) hD) hinj
      (fun σ hσ => (hlift ⟨σ, hσ⟩).elim fun k hk => ⟨k, hk.1⟩) _ ht'2 hκ1 hκsw hidx with
    hnat | ⟨-, hrange⟩
  · exact n9_natVia_of_restrict hV hψ hA ι hD hlift hnat
  · exfalso
    have hmem : restrictHom ψ ι (preSub ψ S) hD ⟨(t : MulAut V), htK⟩ ∈
        (restrictHom ψ ι (preSub ψ S) hD).range := ⟨_, rfl⟩
    rw [hrange, mem_alternatingGroup] at hmem
    have hvia : viaEmbedding (restrictHom ψ ι (preSub ψ S) hD ⟨(t : MulAut V), htK⟩) ι = ψ t := by
      refine Equiv.ext fun z => ?_
      by_cases hz : z ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hz
        rw [viaEmbedding_apply, hκt i]
      · rw [viaEmbedding_apply_of_notMem _ _ _ hz]
        rcases hout z hz with rfl | rfl
        · exact hp.symm
        · exact hq.symm
    refine hodd ?_
    rw [mem_alternatingGroup, ← hvia, sign_viaEmbedding]
    exact hmem

end Step

theorem t86_nine (h7 : T86 7) : T86 9 := by
  intro V _ _ hV H ψ hψ hA t ht2 ht1 htsw hidx
  refine Or.inl ?_
  by_cases hev : ψ t ∈ alternatingGroup (Fin 9)
  · exact n9_even h7 hV hψ hA ht2 ht1 htsw hidx hev
  · exact n9_odd h7 hV hψ hA ht2 ht1 htsw hidx hev

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
