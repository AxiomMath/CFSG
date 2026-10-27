module

public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.A3Structure37
public import CFSG.Quasithin.Background.A3Structure36
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.A3Structure312Transport
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C2A3Orbits

section Abstract

variable {Q : Type} [Group Q]

theorem map_conj_map {Q' : Type} [Group Q'] (π : Q →* Q') (K : Subgroup Q) (g : Q) :
    (K.map π).map (MulAut.conj (π g)).toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).map π := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem conj_mem_cComp_top {K : Subgroup Q} (hK : K ∈ cComp (⊤ : Subgroup Q)) (g : Q) :
    K.map (MulAut.conj g).toMonoidHom ∈ cComp (⊤ : Subgroup Q) := by
  have := C2Nine.conjByElt_mem_cComp (X := ⊤) (t := g) hK (Subgroup.le_normalizer (Subgroup.mem_top g))
  exact this

theorem eq_or_eq_of_le_sup (h37 : A37Statement Q) {A B K : Subgroup Q}
    (hA : A ∈ cComp (⊤ : Subgroup Q)) (hB : B ∈ cComp (⊤ : Subgroup Q))
    (hK : K ∈ cComp (⊤ : Subgroup Q)) (hKW : K ≤ A ⊔ B) : K = A ∨ K = B := by
  by_contra hcon
  obtain ⟨hne1, hne2⟩ := not_or.mp hcon
  have h1 : ⁅K, A⁆ = ⊥ := h37 K hK A hA hne1
  have h2 : ⁅K, B⁆ = ⊥ := h37 K hK B hB hne2
  have hA' : A ≤ Subgroup.centralizer (K : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h1)
  have hB' : B ≤ Subgroup.centralizer (K : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h2)
  have hKK : ⁅K, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKW.trans (sup_le hA' hB'))
  rw [perfect_of_mem_cComp hK] at hKK
  exact ne_bot_of_mem_cComp hK hKK

end Abstract

section Main

variable {Q : Type} [Group Q] [Finite Q]

theorem a3Orbits_abstract (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) (hQ : SQTKGroup Q)
    {T L : Subgroup Q} (hT : IsSylowTwoOf T ⊤) (hL : L ∈ cComp (⊤ : Subgroup Q)) :
    conjSubgroupsBy ⊤ L = conjSubgroupsBy T L ∧
      ((∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set Q)) ∨
        ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set Q) ∧
          conjSubgroupsBy T L = {L, conjByElt t L} ∧
          ⁅L, conjByElt t L⁆ ≤ CFSG.pCore 2 Q ∧
          (L ⊔ CFSG.pCore 2 Q) ⊓ (conjByElt t L ⊔ CFSG.pCore 2 Q) = CFSG.pCore 2 Q) := by
  classical
  have hGb : SQTKHyp (Q ⧸ CFSG.pCore 2 Q) := SQTKHyp.of_sqtkGroup Q hQ
  have h37 := hA37 _ hGb
  have h38 := hA38 _ hGb
  have hNsolv : Group.IsSolvable (CFSG.pCore 2 Q) := by
    have := (CFSG.pCore_isPGroup (G := Q) (p := 2)).isNilpotent
    infer_instance
  have hbij := cComp_quotient_bijOn (CFSG.pCore 2 Q) hNsolv
  set π : Q →* Q ⧸ CFSG.pCore 2 Q := QuotientGroup.mk' (CFSG.pCore 2 Q) with hπ
  have hinj : ∀ {K₁ K₂ : Subgroup Q}, K₁ ∈ cComp (⊤ : Subgroup Q) → K₂ ∈ cComp (⊤ : Subgroup Q) →
      K₁.map π = K₂.map π → K₁ = K₂ := fun h₁ h₂ h => hbij.injOn h₁ h₂ h
  have hLb : L.map π ∈ cComp (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) := hbij.mapsTo hL
  have hTb : IsSylowTwoOf (T.map π) ⊤ :=
    A312.isSylowTwoOf_top_map π (QuotientGroup.mk'_surjective _) hT
  have hone : ∀ K : Subgroup Q, K.map (MulAut.conj (1 : Q)).toMonoidHom = K := fun K =>
    A38.map_conj_eq_iff.mpr (Subgroup.one_mem _)
  have hnormiff : ∀ g : Q, g ∈ Subgroup.normalizer (L : Set Q) ↔
      π g ∈ Subgroup.normalizer ((L.map π : Subgroup (Q ⧸ CFSG.pCore 2 Q)) :
        Set (Q ⧸ CFSG.pCore 2 Q)) := by
    intro g
    have key := map_conj_map π L g
    constructor
    · intro h
      have h' : L.map (MulAut.conj g).toMonoidHom = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp h
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      show (L.map π).map (MulAut.conj (π g)).toMonoidHom = L.map π
      rw [key, h']
    · intro h
      have h' : (L.map π).map (MulAut.conj (π g)).toMonoidHom = L.map π :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp h
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      show L.map (MulAut.conj g).toMonoidHom = L
      rw [key] at h'
      exact hinj (conj_mem_cComp_top hL g) hL h'
  obtain ⟨hfirst, hsecond⟩ := h38 (L.map π) hLb
  rcases hsecond (T.map π) hTb with ⟨hnorm, hset, -⟩ | ⟨tb, htb, htn, hset, -, hcomm, hint, -, -⟩
  ·
    have hnQ : ∀ g : Q, g ∈ Subgroup.normalizer (L : Set Q) := fun g =>
      (hnormiff g).mpr (by rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]; exact Subgroup.mem_top _)
    have hconj1 : ∀ g : Q, L.map (MulAut.conj g).toMonoidHom = L := fun g =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnQ g)
    have hS : ∀ S : Subgroup Q, conjSubgroupsBy S L = {L} := fun S => by
      ext K'
      constructor
      · rintro ⟨s, -, rfl⟩
        exact hconj1 s
      · intro hK'
        rw [Set.mem_singleton_iff] at hK'
        exact ⟨1, S.one_mem, by rw [hK', hconj1]⟩
    exact ⟨(hS ⊤).trans (hS T).symm, Or.inl fun t _ => hnQ t⟩
  · obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp htb
    have htnQ : t ∉ Subgroup.normalizer (L : Set Q) := fun h => htn ((hnormiff t).mp h)
    have hLt : conjByElt t L ∈ cComp (⊤ : Subgroup Q) := conj_mem_cComp_top hL t
    have hmapt : (conjByElt t L).map π = (L.map π).map (MulAut.conj (π t)).toMonoidHom :=
      (map_conj_map π L t).symm
    have hconjT : conjSubgroupsBy T L = {L, conjByElt t L} := by
      ext K'
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hmem : (L.map π).map (MulAut.conj (π s)).toMonoidHom ∈
            conjSubgroupsBy (T.map π) (L.map π) := ⟨π s, Subgroup.mem_map_of_mem π hs, rfl⟩
        rw [hset] at hmem
        rcases hmem with h | h
        · left
          rw [map_conj_map] at h
          exact hinj (conj_mem_cComp_top hL s) hL h
        · right
          have h' : (L.map π).map (MulAut.conj (π s)).toMonoidHom =
              (L.map π).map (MulAut.conj (π t)).toMonoidHom := h
          rw [map_conj_map] at h'
          exact hinj (conj_mem_cComp_top hL s) hLt (h'.trans hmapt.symm)
      · rintro (h | h)
        · exact ⟨1, T.one_mem, h.trans (hone L).symm⟩
        · exact ⟨t, htT, h⟩
    have hLbnn : ¬ (L.map π).Normal := fun hn => htn (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hn]; exact Subgroup.mem_top _)
    obtain ⟨-, t₀, -, -, -, hcl⟩ := hfirst.resolve_left hLbnn
    have hL0b : (L.map π).map (MulAut.conj t₀).toMonoidHom ∈
        cComp (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) := conj_mem_cComp_top hLb t₀
    have hsub : ∀ g : Q ⧸ CFSG.pCore 2 Q,
        (L.map π).map (MulAut.conj g).toMonoidHom ≤ conjClosure (L.map π) ⊤ := by
      intro g x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      simpa [MulAut.conj_apply] using mem_conjClosure (Subgroup.mem_top g) hy
    have hLtb : (L.map π).map (MulAut.conj (π t)).toMonoidHom ∈
        cComp (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) := conj_mem_cComp_top hLb (π t)
    have hne : (L.map π).map (MulAut.conj (π t)).toMonoidHom ≠ L.map π := fun h =>
      htn (A38.map_conj_eq_iff.mp h)
    have hLt0 : (L.map π).map (MulAut.conj (π t)).toMonoidHom =
        (L.map π).map (MulAut.conj t₀).toMonoidHom := by
      have hle := hsub (π t)
      rw [hcl] at hle
      exact (eq_or_eq_of_le_sup h37 hLb hL0b hLtb hle).resolve_left hne
    have hallconj : ∀ g : Q, L.map (MulAut.conj g).toMonoidHom = L ∨
        L.map (MulAut.conj g).toMonoidHom = conjByElt t L := by
      intro g
      have hgc := conj_mem_cComp_top hL g
      have hgb : (L.map π).map (MulAut.conj (π g)).toMonoidHom ∈
          cComp (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) := conj_mem_cComp_top hLb (π g)
      have hle := hsub (π g)
      rw [hcl] at hle
      rcases eq_or_eq_of_le_sup h37 hLb hL0b hgb hle with h | h
      · exact Or.inl (hinj hgc hL ((map_conj_map π L g).symm.trans h))
      · exact Or.inr (hinj hgc hLt
          ((map_conj_map π L g).symm.trans (h.trans (hLt0.symm.trans hmapt.symm))))
    have hconjTop : conjSubgroupsBy (⊤ : Subgroup Q) L = {L, conjByElt t L} := by
      ext K'
      constructor
      · rintro ⟨g, -, rfl⟩
        exact hallconj g
      · rintro (h | h)
        · exact ⟨1, Subgroup.mem_top _, h.trans (hone L).symm⟩
        · exact ⟨t, Subgroup.mem_top _, h⟩
    have hker : (CFSG.pCore 2 Q).map π = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm)
    refine ⟨hconjTop.trans hconjT.symm, Or.inr ⟨t, htT, htnQ, hconjT, ?_, ?_⟩⟩
    · have h1 : (⁅L, conjByElt t L⁆).map π = ⊥ := by
        rw [Subgroup.map_commutator, hmapt]
        exact hcomm
      exact ((Subgroup.map_eq_bot_iff _).mp h1).trans (le_of_eq (QuotientGroup.ker_mk' _))
    · have hmapsup : ∀ K : Subgroup Q, (K ⊔ CFSG.pCore 2 Q).map π = K.map π := by
        intro K
        rw [Subgroup.map_sup, hker, sup_bot_eq]
      apply le_antisymm
      · intro x hx
        have h1 : π x ∈ (L ⊔ CFSG.pCore 2 Q).map π := Subgroup.mem_map_of_mem π hx.1
        have h2 : π x ∈ (conjByElt t L ⊔ CFSG.pCore 2 Q).map π := Subgroup.mem_map_of_mem π hx.2
        rw [hmapsup] at h1 h2
        rw [hmapt] at h2
        have h3 : π x ∈ L.map π ⊓ (L.map π).map (MulAut.conj (π t)).toMonoidHom := ⟨h1, h2⟩
        rw [hint] at h3
        have h4 : π x = 1 := Subgroup.mem_bot.mp h3
        have h5 : x ∈ π.ker := MonoidHom.mem_ker.mpr h4
        rwa [show π.ker = CFSG.pCore 2 Q from QuotientGroup.ker_mk' _] at h5
      · exact le_inf le_sup_right le_sup_right

end Main

section Ambient

variable {G : Type} [Group G]

theorem pCoreOf_eq_map_pCore (K : Subgroup G) :
    pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := CFSG.openPCoreOf_eq_map_pCore 2 K

theorem conjByElt_map_subtype (X : Subgroup G) (K : Subgroup ↥X) (g : ↥X) :
    conjByElt (g : G) (K.map X.subtype) = (conjByElt g K).map X.subtype :=
  map_conj_map X.subtype K g

theorem conjSubgroupsBy_map_subtype (X : Subgroup G) (S' L' : Subgroup ↥X) :
    conjSubgroupsBy (S'.map X.subtype) (L'.map X.subtype) =
      Subgroup.map X.subtype '' conjSubgroupsBy S' L' := by
  ext K
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
    exact ⟨_, ⟨s', hs', rfl⟩, (map_conj_map X.subtype L' s').symm⟩
  · rintro ⟨K', ⟨s', hs', rfl⟩, rfl⟩
    exact ⟨X.subtype s', Subgroup.mem_map_of_mem _ hs', (map_conj_map X.subtype L' s').symm⟩

theorem mem_normalizer_map_subtype (X : Subgroup G) (K : Subgroup ↥X) (g : ↥X) :
    (g : G) ∈ Subgroup.normalizer ((K.map X.subtype : Subgroup G) : Set G) ↔
      g ∈ Subgroup.normalizer (K : Set ↥X) := by
  rw [← A38.map_conj_eq_iff, ← A38.map_conj_eq_iff]
  have h : (K.map X.subtype).map (MulAut.conj (g : G)).toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).map X.subtype := map_conj_map X.subtype K g
  rw [h]
  exact (Subgroup.map_injective X.subtype_injective).eq_iff

theorem conjByElt_conjByElt (s t : G) (K : Subgroup G) :
    (conjByElt t K).map (MulAut.conj s).toMonoidHom = K.map (MulAut.conj (s * t)).toMonoidHom := by
  unfold conjByElt
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_of_conj_le {K : Subgroup G} {s : G}
    (h1 : K.map (MulAut.conj s).toMonoidHom ≤ K) (h2 : K.map (MulAut.conj s⁻¹).toMonoidHom ≤ K) :
    s ∈ Subgroup.normalizer (K : Set G) := by
  rw [← A38.map_conj_eq_iff]
  refine le_antisymm h1 fun x hx => ?_
  have hx' : s⁻¹ * x * s ∈ K := h2 ⟨x, hx, by simp⟩
  exact ⟨s⁻¹ * x * s, hx', by simp [MulAut.conj_apply, mul_assoc]⟩

theorem pair_le_normalizer {T L : Subgroup G} {t : G} (ht : t ∈ T)
    (h : conjSubgroupsBy T L = {L, conjByElt t L}) :
    T ≤ Subgroup.normalizer ((L ⊔ conjByElt t L : Subgroup G) : Set G) := by
  have hmem : ∀ s ∈ T, L.map (MulAut.conj s).toMonoidHom ∈ ({L, conjByElt t L} : Set (Subgroup G)) :=
    fun s hs => by rw [← h]; exact ⟨s, hs, rfl⟩
  have hmem2 : ∀ s ∈ T,
      (conjByElt t L).map (MulAut.conj s).toMonoidHom ∈ ({L, conjByElt t L} : Set (Subgroup G)) :=
    fun s hs => by
      rw [← h]
      exact ⟨s * t, T.mul_mem hs ht, conjByElt_conjByElt s t L⟩
  have hle : ∀ s ∈ T, (L ⊔ conjByElt t L).map (MulAut.conj s).toMonoidHom ≤ L ⊔ conjByElt t L := by
    intro s hs
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rcases hmem s hs with h1 | h1
      · rw [h1]; exact le_sup_left
      · rw [(Set.mem_singleton_iff.mp h1)]; exact le_sup_right
    · rcases hmem2 s hs with h1 | h1
      · rw [h1]; exact le_sup_left
      · rw [(Set.mem_singleton_iff.mp h1)]; exact le_sup_right
  intro s hs
  exact mem_normalizer_of_conj_le (hle s hs) (hle s⁻¹ (T.inv_mem hs))

end Ambient

end C2A3Orbits

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem a3Orbits_of_a37_a38 (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) : A3Orbits G := by
  classical
  intro X T L hX hT hL
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hT' : IsSylowTwoOf (T.subgroupOf X) (⊤ : Subgroup ↥X) := by
    rw [A312.isSylowTwoOf_top_iff_map, Subgroup.map_subgroupOf_eq_of_le hT.1]
    exact hT
  have hL' : L.subgroupOf X ∈ cComp (⊤ : Subgroup ↥X) := (cComp_subgroupOf_bijOn X).mapsTo hL
  obtain ⟨horb, hcase⟩ := C2A3Orbits.a3Orbits_abstract hA37 hA38 hX hT' hL'
  have hTmap : (T.subgroupOf X).map X.subtype = T := Subgroup.map_subgroupOf_eq_of_le hT.1
  have hLmap : (L.subgroupOf X).map X.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLX
  have hXmap : (⊤ : Subgroup ↥X).map X.subtype = X := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hP : pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := C2A3Orbits.pCoreOf_eq_map_pCore X
  have horbit : conjSubgroupsBy X L = conjSubgroupsBy T L := by
    have h1 := C2A3Orbits.conjSubgroupsBy_map_subtype X (⊤ : Subgroup ↥X) (L.subgroupOf X)
    have h2 := C2A3Orbits.conjSubgroupsBy_map_subtype X (T.subgroupOf X) (L.subgroupOf X)
    rw [hXmap, hLmap] at h1
    rw [hTmap, hLmap] at h2
    rw [h1, h2, horb]
  refine ⟨horbit, ?_⟩
  rcases hcase with hnorm | ⟨t', ht'T, ht'n, hpair, hcomm, hint⟩
  · refine Or.inl fun t ht => ?_
    have hmem : (⟨t, hT.1 ht⟩ : ↥X) ∈ T.subgroupOf X := ht
    have h := (C2A3Orbits.mem_normalizer_map_subtype X (L.subgroupOf X) ⟨t, hT.1 ht⟩).mpr
      (hnorm _ hmem)
    rwa [hLmap] at h
  · have hLt : conjByElt (t' : G) L = (conjByElt t' (L.subgroupOf X)).map X.subtype := by
      have := C2A3Orbits.conjByElt_map_subtype X (L.subgroupOf X) t'
      rwa [hLmap] at this
    have hpairG : conjSubgroupsBy T L = {L, conjByElt (t' : G) L} := by
      have h2 := C2A3Orbits.conjSubgroupsBy_map_subtype X (T.subgroupOf X) (L.subgroupOf X)
      rw [hTmap, hLmap, hpair, Set.image_pair, hLmap, ← hLt] at h2
      exact h2
    refine Or.inr ⟨(t' : G), ht'T, ?_, hpairG, ?_, ?_, C2A3Orbits.pair_le_normalizer ht'T hpairG⟩
    · intro h
      refine ht'n ((C2A3Orbits.mem_normalizer_map_subtype X (L.subgroupOf X) t').mp ?_)
      rwa [hLmap]
    · have h := Subgroup.map_mono (f := X.subtype) hcomm
      rw [Subgroup.map_commutator, hLmap, ← hP,
        ← C2A3Orbits.conjByElt_map_subtype X (L.subgroupOf X) t', hLmap] at h
      exact h
    · have h := congrArg (Subgroup.map X.subtype) hint
      rw [Subgroup.map_inf _ _ _ X.subtype_injective, Subgroup.map_sup, Subgroup.map_sup,
        ← hP, hLmap, ← C2A3Orbits.conjByElt_map_subtype X (L.subgroupOf X) t', hLmap] at h
      exact h

theorem a3Orbits_of_facts (hF36 : A36Facts) (hF38 : A38Facts) : A3Orbits G := by
  have h37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y := fun Y _ hY => by
    have := hY.finite
    exact A37.a37_of_a36 (a36 hF36 hY)
  exact a3Orbits_of_a37_a38 h37 fun Y _ hY => A38.a38_part3 hF38 hY (a36 hF36 hY) (h37 Y hY)

end Transfer

end CFSG.Quasithin
