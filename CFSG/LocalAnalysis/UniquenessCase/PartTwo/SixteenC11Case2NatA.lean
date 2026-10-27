module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {W W' : Type} [CommGroup W] [CommGroup W']

theorem s16c11_case2nat_pairs_ncard_eq {L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')}
    {J : Subgroup W} {J' : Subgroup W'} (ψ : ↥L ≃* ↥L') (φ : ↥J ≃* ↥J')
    (hLJ : ∀ l ∈ L, ∀ y ∈ J, l y ∈ J) (hL'J' : ∀ l ∈ L', ∀ y ∈ J', l y ∈ J')
    (hint : ∀ (l : ↥L) (u : ↥J),
      (φ ⟨(l : MulAut W) (u : W), hLJ l l.2 u u.2⟩ : W') =
        ((ψ l : ↥L') : MulAut W') (φ u : W'))
    (T₁ : Subgroup (MulAut W)) (hT₁L : T₁ ≤ L) (N : ℕ) :
    (S16C11Pairs L J T₁ N).ncard =
      (S16C11Pairs L' J' ((T₁.subgroupOf L).map ψ.toMonoidHom |>.map L'.subtype) N).ncard := by
  classical
  let Ψ : Subgroup (MulAut W) → Subgroup (MulAut W') :=
    fun X => ((X.subgroupOf L).map ψ.toMonoidHom).map L'.subtype
  let Ψ' : Subgroup (MulAut W') → Subgroup (MulAut W) :=
    fun X' => ((X'.subgroupOf L').map ψ.symm.toMonoidHom).map L.subtype
  let Φ : W → W' := fun y => if hy : y ∈ J then (φ ⟨y, hy⟩ : W') else 1
  let Φ' : W' → W := fun y' => if hy' : y' ∈ J' then (φ.symm ⟨y', hy'⟩ : W) else 1
  have hΦ : ∀ (y : W) (hy : y ∈ J), Φ y = (φ ⟨y, hy⟩ : W') := fun y hy => dif_pos hy
  have hΦ' : ∀ (y' : W') (hy' : y' ∈ J'), Φ' y' = (φ.symm ⟨y', hy'⟩ : W) :=
    fun y' hy' => dif_pos hy'
  have hΦJ : ∀ y ∈ J, Φ y ∈ J' := fun y hy => by rw [hΦ y hy]; exact (φ ⟨y, hy⟩).2
  have hΦ'J : ∀ y' ∈ J', Φ' y' ∈ J := fun y' hy' => by rw [hΦ' y' hy']; exact (φ.symm ⟨y', hy'⟩).2
  have hΦi : Set.InjOn Φ (J : Set W) := by
    intro y hy z hz h
    rw [hΦ y hy, hΦ z hz] at h
    exact Subtype.ext_iff.mp (φ.injective (Subtype.ext h))
  have hΦ'i : Set.InjOn Φ' (J' : Set W') := by
    intro y' hy' z' hz' h
    rw [hΦ' y' hy', hΦ' z' hz'] at h
    exact Subtype.ext_iff.mp (φ.symm.injective (Subtype.ext h))
  have hΦΦ' : ∀ y ∈ J, Φ' (Φ y) = y := by
    intro y hy
    have h1 := hΦ' (Φ y) (hΦJ y hy)
    have h2 : (⟨Φ y, hΦJ y hy⟩ : ↥J') = φ ⟨y, hy⟩ := Subtype.ext (hΦ y hy)
    rw [h2] at h1
    rw [h1]
    exact congrArg Subtype.val (MulEquiv.symm_apply_apply φ ⟨y, hy⟩)
  have hΦ'Φ : ∀ y' ∈ J', Φ (Φ' y') = y' := by
    intro y' hy'
    have h1 := hΦ (Φ' y') (hΦ'J y' hy')
    have h2 : (⟨Φ' y', hΦ'J y' hy'⟩ : ↥J) = φ.symm ⟨y', hy'⟩ := Subtype.ext (hΦ' y' hy')
    rw [h2] at h1
    rw [h1]
    exact congrArg Subtype.val (MulEquiv.apply_symm_apply φ ⟨y', hy'⟩)
  have hΦ_hint : ∀ (l : ↥L) (y : W) (hy : y ∈ J),
      Φ ((l : MulAut W) y) = ((ψ l : ↥L') : MulAut W') (Φ y) := by
    intro l y hy
    rw [hΦ ((l : MulAut W) y) (hLJ l l.2 y hy), hΦ y hy]
    exact hint l ⟨y, hy⟩
  have hΦ'_hint : ∀ (l : ↥L) (y' : W') (hy' : y' ∈ J'),
      Φ' (((ψ l : ↥L') : MulAut W') y') = (l : MulAut W) (Φ' y') := by
    intro l y' hy'
    have hcoe : ((φ ⟨Φ' y', hΦ'J y' hy'⟩ : ↥J') : W') = y' := by
      rw [show (⟨Φ' y', hΦ'J y' hy'⟩ : ↥J) = φ.symm ⟨y', hy'⟩ from Subtype.ext (hΦ' y' hy')]
      exact congrArg Subtype.val (MulEquiv.apply_symm_apply φ ⟨y', hy'⟩)
    have hstep : ((ψ l : ↥L') : MulAut W') y' = Φ ((l : MulAut W) (Φ' y')) := by
      have h1 : ((ψ l : ↥L') : MulAut W') y' =
          ((ψ l : ↥L') : MulAut W') (φ ⟨Φ' y', hΦ'J y' hy'⟩ : W') := by rw [hcoe]
      have h2 : ((ψ l : ↥L') : MulAut W') (φ ⟨Φ' y', hΦ'J y' hy'⟩ : W') =
          (φ ⟨(l : MulAut W) (Φ' y'), hLJ l l.2 (Φ' y') (hΦ'J y' hy')⟩ : W') :=
        (hint l ⟨Φ' y', hΦ'J y' hy'⟩).symm
      have h3 : (φ ⟨(l : MulAut W) (Φ' y'), hLJ l l.2 (Φ' y') (hΦ'J y' hy')⟩ : W') =
          Φ ((l : MulAut W) (Φ' y')) :=
        (hΦ ((l : MulAut W) (Φ' y')) (hLJ l l.2 (Φ' y') (hΦ'J y' hy'))).symm
      exact h1.trans (h2.trans h3)
    calc Φ' (((ψ l : ↥L') : MulAut W') y')
        = Φ' (Φ ((l : MulAut W) (Φ' y'))) := congrArg Φ' hstep
      _ = (l : MulAut W) (Φ' y') :=
          hΦΦ' ((l : MulAut W) (Φ' y')) (hLJ l l.2 (Φ' y') (hΦ'J y' hy'))
  have hΦ_orbit : ∀ y ∈ J, Φ '' {z : W | ∃ l ∈ L, l y = z} =
      {z' : W' | ∃ l' ∈ L', l' (Φ y) = z'} := by
    intro y hy
    ext z'
    constructor
    · rintro ⟨z, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨(ψ ⟨l, hl⟩ : ↥L'), (ψ ⟨l, hl⟩).2, (hΦ_hint ⟨l, hl⟩ y hy).symm⟩
    · rintro ⟨l', hl', rfl⟩
      obtain ⟨l, hl_eq⟩ := ψ.surjective ⟨l', hl'⟩
      refine ⟨(l : MulAut W) y, ⟨l, l.2, rfl⟩, ?_⟩
      rw [hΦ_hint l y hy, congrArg Subtype.val hl_eq]
  have hΦ'_orbit : ∀ y' ∈ J', Φ' '' {z' : W' | ∃ l' ∈ L', l' y' = z'} =
      {z : W | ∃ l ∈ L, l (Φ' y') = z} := by
    intro y' hy'
    ext z
    constructor
    · rintro ⟨z', ⟨l', hl', rfl⟩, rfl⟩
      obtain ⟨l, hl_eq⟩ := ψ.surjective ⟨l', hl'⟩
      have hlval : ((ψ l : ↥L') : MulAut W') = l' := congrArg Subtype.val hl_eq
      refine ⟨(l : MulAut W), l.2, ?_⟩
      rw [← hlval]
      exact (hΦ'_hint l y' hy').symm
    · rintro ⟨l, hl, rfl⟩
      exact ⟨((ψ ⟨l, hl⟩ : ↥L') : MulAut W') y',
        ⟨ψ ⟨l, hl⟩, (ψ ⟨l, hl⟩).2, rfl⟩, hΦ'_hint ⟨l, hl⟩ y' hy'⟩
  have hΨL' : ∀ X : Subgroup (MulAut W), Ψ X ≤ L' := fun X =>
    (Subgroup.map_le_range L'.subtype ((X.subgroupOf L).map ψ.toMonoidHom)).trans_eq
      L'.range_subtype
  have hΨ'L : ∀ X' : Subgroup (MulAut W'), Ψ' X' ≤ L := fun X' =>
    (Subgroup.map_le_range L.subtype ((X'.subgroupOf L').map ψ.symm.toMonoidHom)).trans_eq
      L.range_subtype
  have hΨ'Ψ : ∀ X ≤ L, Ψ' (Ψ X) = X := by
    intro X hXL
    set A : Subgroup ↥L' := (X.subgroupOf L).map ψ.toMonoidHom with hA
    show ((((A.map L'.subtype).subgroupOf L').map ψ.symm.toMonoidHom).map L.subtype) = X
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L'.subtype_injective A]
    rw [hA, Subgroup.map_map (g := ψ.symm.toMonoidHom) (f := ψ.toMonoidHom)]
    have hcomp : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id (↥L) := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id, Subgroup.subgroupOf_map_subtype X L, inf_eq_left.mpr hXL]
  have hΨΨ' : ∀ X' ≤ L', Ψ (Ψ' X') = X' := by
    intro X' hX'L'
    set A : Subgroup ↥L := (X'.subgroupOf L').map ψ.symm.toMonoidHom with hA
    show ((((A.map L.subtype).subgroupOf L).map ψ.toMonoidHom).map L'.subtype) = X'
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective A]
    rw [hA, Subgroup.map_map (g := ψ.toMonoidHom) (f := ψ.symm.toMonoidHom)]
    have hcomp : ψ.toMonoidHom.comp ψ.symm.toMonoidHom = MonoidHom.id (↥L') := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id, Subgroup.subgroupOf_map_subtype X' L', inf_eq_left.mpr hX'L']
  have hΨmono : ∀ {X Y : Subgroup (MulAut W)}, X ≤ Y → Ψ X ≤ Ψ Y :=
    fun h => Subgroup.map_mono (Subgroup.map_mono (Subgroup.subgroupOf_mono L h))
  have hΨ'mono : ∀ {X' Y' : Subgroup (MulAut W')}, X' ≤ Y' → Ψ' X' ≤ Ψ' Y' :=
    fun h => Subgroup.map_mono (Subgroup.map_mono (Subgroup.subgroupOf_mono L' h))
  have hΨrel : ∀ X ≤ L, (Ψ T₁).relIndex (Ψ X) = T₁.relIndex X := by
    intro X hXL
    show ((((T₁.subgroupOf L).map ψ.toMonoidHom).map L'.subtype)).relIndex
      ((((X.subgroupOf L).map ψ.toMonoidHom).map L'.subtype)) = T₁.relIndex X
    rw [Subgroup.relIndex_map_map_of_injective ((T₁.subgroupOf L).map ψ.toMonoidHom)
        ((X.subgroupOf L).map ψ.toMonoidHom) L'.subtype_injective,
      Subgroup.relIndex_map_map_of_injective (T₁.subgroupOf L) (X.subgroupOf L) ψ.injective,
      Subgroup.relIndex_subgroupOf hXL]
  let F : W × Subgroup (MulAut W) → W' × Subgroup (MulAut W') := fun p => (Φ p.1, Ψ p.2)
  let F' : W' × Subgroup (MulAut W') → W × Subgroup (MulAut W) := fun q => (Φ' q.1, Ψ' q.2)
  have hF_mem : ∀ p ∈ S16C11Pairs L J T₁ N,
      F p ∈ S16C11Pairs L' J' (Ψ T₁) N := by
    rintro ⟨y, X⟩ hp
    obtain ⟨hyJ, hfix, horb, hXL, hT₁X, hidx, hmov⟩ := hp
    refine ⟨hΦJ y hyJ, ?_, ?_, hΨL' X, hΨmono hT₁X, ?_, ?_⟩
    · intro t' ht'
      obtain ⟨Y, hY, rfl⟩ := Subgroup.mem_map.1 ht'
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hY
      have htT : (t : MulAut W) ∈ T₁ := Subgroup.mem_subgroupOf.1 ht
      show ((ψ t : ↥L') : MulAut W') (Φ y) = Φ y
      rw [← hΦ_hint t y hyJ, hfix (t : MulAut W) htT]
    · change {z' : W' | ∃ l' ∈ L', l' (Φ y) = z'}.ncard ≤ N
      have hsub : {z : W | ∃ l ∈ L, l y = z} ⊆ (J : Set W) := by
        rintro z ⟨l, hl, rfl⟩
        exact hLJ l hl y hyJ
      rw [← hΦ_orbit y hyJ, (hΦi.mono hsub).ncard_image]
      exact horb
    · rw [hΨrel X hXL, hidx]
    · obtain ⟨g, hg, hgy⟩ := hmov
      refine ⟨(ψ ⟨g, hXL hg⟩ : ↥L'), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem L'.subtype (Subgroup.mem_map_of_mem ψ.toMonoidHom hg)
      · rw [← hΦ_hint ⟨g, hXL hg⟩ y hyJ]
        exact fun h => hgy (hΦi (hLJ g (hXL hg) y hyJ) hyJ h)
  have hF'_mem : ∀ q ∈ S16C11Pairs L' J' (Ψ T₁) N,
      F' q ∈ S16C11Pairs L J T₁ N := by
    rintro ⟨y', X'⟩ hq
    obtain ⟨hy'J', hfix', horb', hX'L', hT₁'X', hidx', hmov'⟩ := hq
    refine ⟨hΦ'J y' hy'J', ?_, ?_, hΨ'L X', ?_, ?_, ?_⟩
    · intro t ht
      have htL : t ∈ L := hT₁L ht
      have ht' : L'.subtype (ψ ⟨t, htL⟩) ∈ Ψ T₁ :=
        Subgroup.mem_map_of_mem L'.subtype
          (Subgroup.mem_map_of_mem ψ.toMonoidHom (Subgroup.mem_subgroupOf.2 ht))
      have hft : ((ψ ⟨t, htL⟩ : ↥L') : MulAut W') y' = y' := hfix' _ ht'
      show (t : MulAut W) (Φ' y') = Φ' y'
      rw [← hΦ'_hint ⟨t, htL⟩ y' hy'J', hft]
    · change {z : W | ∃ l ∈ L, l (Φ' y') = z}.ncard ≤ N
      have hsub : {z' : W' | ∃ l' ∈ L', l' y' = z'} ⊆ (J' : Set W') := by
        rintro z' ⟨l', hl', rfl⟩
        exact hL'J' l' hl' y' hy'J'
      rw [← hΦ'_orbit y' hy'J', (hΦ'i.mono hsub).ncard_image]
      exact horb'
    · rw [← hΨ'Ψ T₁ hT₁L]
      exact hΨ'mono hT₁'X'
    · rw [← hΨrel (Ψ' X') (hΨ'L X'), hΨΨ' X' hX'L']
      exact hidx'
    · obtain ⟨g', hg', hg'y'⟩ := hmov'
      have hg'L' : g' ∈ L' := hX'L' hg'
      refine ⟨L.subtype (ψ.symm ⟨g', hg'L'⟩), ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem L.subtype
          (Subgroup.mem_map_of_mem ψ.symm.toMonoidHom (Subgroup.mem_subgroupOf.2 hg'))
      · intro hgy
        have hmove : Φ' (g' y') = Φ' y' := by
          have h := hgy
          change ((ψ.symm ⟨g', hg'L'⟩ : ↥L) : MulAut W) (Φ' y') = Φ' y' at h
          rw [← hΦ'_hint (ψ.symm ⟨g', hg'L'⟩) y' hy'J'] at h
          simpa using h
        exact hg'y' (hΦ'i (hL'J' g' hg'L' y' hy'J') hy'J' hmove)
  refine Set.ncard_congr (fun p _ => F p) hF_mem ?_ ?_
  · intro a b ha hb hab
    obtain ⟨y, X⟩ := a
    obtain ⟨y₂, X₂⟩ := b
    obtain ⟨hyJ, -, -, hXL, -, -, -⟩ := ha
    obtain ⟨hy₂J, -, -, hX₂L, -, -, -⟩ := hb
    have h1 : Φ y = Φ y₂ := congrArg Prod.fst hab
    have h2 : Ψ X = Ψ X₂ := congrArg Prod.snd hab
    have hy : y = y₂ := hΦi hyJ hy₂J h1
    have hX : X = X₂ := by
      have hh := congrArg Ψ' h2
      rw [hΨ'Ψ X hXL, hΨ'Ψ X₂ hX₂L] at hh
      exact hh
    exact Prod.ext hy hX
  · intro b hb
    obtain ⟨y', X'⟩ := b
    exact ⟨(Φ' y', Ψ' X'), hF'_mem (y', X') hb, by
      obtain ⟨hy'J', -, -, hX'L', -, -, -⟩ := hb
      apply Prod.ext
      · exact hΦ'Φ y' hy'J'
      · exact hΨΨ' X' hX'L'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
