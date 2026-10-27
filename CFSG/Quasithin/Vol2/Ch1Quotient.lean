
module

public import CFSG.Quasithin.Background.A3Structure39Aut
public import CFSG.Quasithin.Background.A3Structure312Embed
public import CFSG.Quasithin.Background.A3Structure38Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Abstract

variable {X : Type*} [Group X] [Finite X]

theorem map_cCompSpan_quotient (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N) :
    (cCompSpan (⊤ : Subgroup X)).map (QuotientGroup.mk' N) =
      cCompSpan (⊤ : Subgroup (X ⧸ N)) := by
  unfold cCompSpan
  rw [(Subgroup.gc_map_comap (QuotientGroup.mk' N)).l_sSup, ← sSup_image,
    image_cComp_quotient N hN]

theorem cCompSpan_eq_perfectCore_of_quotient (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N)
    (h : cCompSpan (⊤ : Subgroup (X ⧸ N)) = perfectCore (⊤ : Subgroup (X ⧸ N))) :
    cCompSpan (⊤ : Subgroup X) = perfectCore (⊤ : Subgroup X) := by
  refine le_antisymm (le_perfectCore_of_perfect le_top cCompSpan_perfect) ?_
  set S := cCompSpan (⊤ : Subgroup X) with hS
  have hSn : S.Normal := cCompSpan_normal
  have hmap : (perfectCore (⊤ : Subgroup X)).map (QuotientGroup.mk' N) =
      S.map (QuotientGroup.mk' N) := by
    rw [hS, map_cCompSpan_quotient N hN, h, map_perfectCore,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have h1 : perfectCore (⊤ : Subgroup X) ≤ S ⊔ N := by
    have := Subgroup.comap_mono (f := QuotientGroup.mk' N) hmap.le
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    exact le_sup_left.trans this
  calc perfectCore (⊤ : Subgroup X)
      = perfectCore (perfectCore (⊤ : Subgroup X)) :=
        (perfectCore_eq_self_of_perfect (perfectCore_perfect _)).symm
    _ ≤ perfectCore (S ⊔ N) := perfectCore_mono h1
    _ ≤ S := perfectCore_le_of_sup_solvable le_sup_left Subgroup.normal_subgroupOf rfl hN

theorem isSolvable_pCore_two_group (X : Type*) [Group X] [Finite X] :
    Group.IsSolvable (CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have : Group.IsNilpotent (CFSG.pCore 2 X) := h.isNilpotent
  infer_instance

theorem cCompSpan_eq_perfectCore_of_pCore
    (h : cCompSpan (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) =
      perfectCore (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X))) :
    cCompSpan (⊤ : Subgroup X) = perfectCore (⊤ : Subgroup X) :=
  cCompSpan_eq_perfectCore_of_quotient (CFSG.pCore 2 X) (isSolvable_pCore_two_group X) h

end Abstract

section Nested

variable {X : Type*} [Group X] [Finite X] {Q : Type*} [Group Q] [Finite Q]

theorem map_mem_cComp_of_le (f : X →* Q) (hker : Group.IsSolvable f.ker) {Y L : Subgroup X}
    (hkerY : f.ker ≤ Y) (hL : L ∈ cComp Y) : L.map f ∈ cComp (Y.map f) := by
  have h3 := cComp_commutator_perfectCore hL hkerY hker Subgroup.le_normalizer_of_normal
  refine ⟨?_, ?_, A3.subnormal_map f (subnormal_of_mem_cComp hL), ?_⟩
  · intro hbot
    have hLk : L ≤ f.ker := (Subgroup.map_eq_bot_iff L).mp hbot
    have : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLk)
        (Subgroup.inclusion_injective hLk)
    exact not_isSolvable_of_mem_cComp hL this
  · rw [← Subgroup.map_commutator, perfect_of_mem_cComp hL]
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hK'range : K' ≤ f.range := hK'lt.le.trans (Subgroup.map_le_range f L)
    have hfK : (K'.comap f).map f = K' := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hK'range]
    have hYY : (Y.map f).comap f = Y := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerY]
    have hKsub : IsSubnormal (K'.comap f) Y := by
      have := A3.subnormal_comap f hK'sub
      rwa [hYY] at this
    have hKinf : K'.comap f ≤ L ⊔ f.ker :=
      calc K'.comap f ≤ (L.map f).comap f := Subgroup.comap_mono hK'lt.le
        _ = L ⊔ f.ker := Subgroup.comap_map_eq f L
    have hcore_le : perfectCore (K'.comap f) ≤ L :=
      calc perfectCore (K'.comap f) ≤ perfectCore (L ⊔ f.ker) := perfectCore_mono hKinf
        _ = L := h3.2
    have hcore_ne : perfectCore (K'.comap f) ≠ ⊥ := by
      intro h
      apply hK'ne
      have := map_perfectCore f (K'.comap f)
      rw [h, Subgroup.map_bot, hfK, perfectCore_eq_self_of_perfect hK'perf] at this
      exact this.symm
    have hcore_eq : perfectCore (K'.comap f) = L := by
      by_contra hne
      exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hcore_le hne) hcore_ne
        (perfectCore_perfect _) (A3.subnormal_perfectCore hKsub)
    have : L.map f = K' := by
      rw [← hcore_eq, map_perfectCore, hfK, perfectCore_eq_self_of_perfect hK'perf]
    exact hK'lt.ne this.symm

end Nested

section Transfer

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isSylowTwoOf_top_map_of_surjective {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) {Q : Type*} [Group Q]
    (f : X →* Q) (hf : Function.Surjective f) : IsSylowTwoOf (S.map f) ⊤ := by
  refine ⟨le_top, hS.2.1.map f, fun h => hS.2.2 ?_⟩
  have h1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  have h2 : ((S.map f).subgroupOf ⊤).index = (S.map f).index := Subgroup.relIndex_top_right _
  rw [h2] at h
  rw [h1]
  exact h.trans (Subgroup.index_map_dvd S hf)

theorem exists_cComp_ge_of_lFamily (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N)
    (h37 : A37Statement (X ⧸ N)) (h39 : A39Statement (X ⧸ N)) {S B : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hNS : N ≤ S) (hB : B ∈ lFamily S) :
    ∃ K ∈ cComp (⊤ : Subgroup X), B ≤ K := by
  have hB' : B ∈ cComp (B ⊔ S) := hB
  have hker : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']; exact hN
  have hkerle : (QuotientGroup.mk' N).ker ≤ B ⊔ S := by
    rw [QuotientGroup.ker_mk']; exact hNS.trans le_sup_right
  have hBbar := map_mem_cComp_of_le (QuotientGroup.mk' N) hker hkerle hB'
  rw [Subgroup.map_sup] at hBbar
  have hSbar := isSylowTwoOf_top_map_of_surjective hS (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  obtain ⟨Lbar, hLbar, hBL⟩ := A312.exists_le_cComp hSbar hBbar h37 h39
  obtain ⟨L, hL, rfl⟩ := (cComp_quotient_bijOn N hN).surjOn hLbar
  refine ⟨L, hL, ?_⟩
  have hBle : B ≤ L ⊔ N := by
    have := Subgroup.comap_mono (f := QuotientGroup.mk' N) hBL
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    exact le_sup_left.trans this
  have h3 := cComp_commutator_perfectCore hL le_top hN Subgroup.le_normalizer_of_normal
  rw [← h3.2]
  exact le_perfectCore_of_perfect hBle (perfect_of_mem_cComp hB')

theorem normal_conjClosure_of_normal_map (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N)
    {L T : Subgroup X} (hL : L ∈ cComp (⊤ : Subgroup X))
    (hn : ((conjClosure L T).map (QuotientGroup.mk' N)).Normal) : (conjClosure L T).Normal := by
  set A := conjClosure L T with hA
  have hperfA : ⁅A, A⁆ = A := A3.conjClosure_perfect (perfect_of_mem_cComp hL)
  have hkey : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
    intro n hn' a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨t, ht, l, hl, rfl⟩ := hx
      have hLt : L.map (MulAut.conj t).toMonoidHom ∈ cComp (⊤ : Subgroup X) := A38.cComp_conj hL
      have hcomm := (cComp_commutator_perfectCore hLt le_top hN
        Subgroup.le_normalizer_of_normal).1
      have hNn : N ≤ Subgroup.normalizer (L.map (MulAut.conj t).toMonoidHom : Set X) :=
        Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm
      have hx : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
        ⟨l, hl, by simp [MulAut.conj_apply]⟩
      have h1 : n * (t * l * t⁻¹) * n⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
        (Subgroup.mem_normalizer_iff.mp (hNn hn') _).mp hx
      obtain ⟨l', hl', hl'e⟩ := h1
      have : l' ∈ L := hl'
      rw [← hl'e]
      simpa [MulAut.conj_apply] using mem_conjClosure ht this
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using A.mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using A.inv_mem ih
  have hNA : N ≤ Subgroup.normalizer (A : Set X) := by
    intro n hn'
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hkey n hn' a ha, fun ha => ?_⟩
    have := hkey n⁻¹ (N.inv_mem hn') _ ha
    simpa [mul_assoc] using this
  have hAn : (A.subgroupOf (A ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hNA)
  have hcore : perfectCore (A ⊔ N) = A :=
    le_antisymm (perfectCore_le_of_sup_solvable le_sup_left hAn rfl hN)
      (le_perfectCore_of_perfect le_sup_left hperfA)
  have hpre : A ⊔ N = (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hnormAN : (A ⊔ N).Normal := by
    rw [hpre]
    exact Subgroup.Normal.comap hn _
  have h1 := normalizer_le_normalizer_perfectCore (A ⊔ N)
  rw [hcore, Subgroup.normalizer_eq_top_iff.mpr hnormAN] at h1
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)

theorem normal_conjClosure_of_cComp (N : Subgroup X) [N.Normal] (hN : Group.IsSolvable N)
    (h37 : A37Statement (X ⧸ N)) (h38 : A38Part3 (X ⧸ N)) {L T : Subgroup X}
    (hL : L ∈ cComp (⊤ : Subgroup X)) (hT : IsSylowTwoOf T ⊤) : (conjClosure L T).Normal := by
  have hker : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']; exact hN
  have hLbar := map_mem_cComp_top (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker hL
  have hTbar := isSylowTwoOf_top_map_of_surjective hT (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  refine normal_conjClosure_of_normal_map N hN hL ?_
  rw [A3.map_conjClosure]
  obtain ⟨hL1, hL2⟩ := h38 _ hLbar
  rcases hL2 _ hTbar with ⟨hnorm, -, -⟩ | ⟨t, htT, htn, -, -, -, -, -, -⟩
  · have : conjClosure (L.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N)) =
        L.map (QuotientGroup.mk' N) :=
      le_antisymm (conjClosure_le fun h _ z hz => by simpa using hnorm.conj_mem z hz h)
        (le_conjClosure _ _)
    rw [this]
    exact hnorm
  · rcases hL1 with hnorm | ⟨-, t', ht'n, -, -, hcl'⟩
    · exact absurd (by
        rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]; exact Subgroup.mem_top t) htn
    · set Lb := L.map (QuotientGroup.mk' N) with hLb
      have hLt : Lb.map (MulAut.conj t).toMonoidHom ∈ cComp (⊤ : Subgroup (X ⧸ N)) :=
        A38.cComp_conj hLbar
      have hLt' : Lb.map (MulAut.conj t').toMonoidHom ∈ cComp (⊤ : Subgroup (X ⧸ N)) :=
        A38.cComp_conj hLbar
      have hle : Lb.map (MulAut.conj t).toMonoidHom ≤
          Lb ⊔ Lb.map (MulAut.conj t').toMonoidHom := by
        rw [← hcl']
        intro x hx
        rw [A38.mem_map_conj] at hx
        have := mem_conjClosure (Subgroup.mem_top t) hx
        simpa [mul_assoc] using this
      have hTt : Lb.map (MulAut.conj t).toMonoidHom ≤
          conjClosure Lb (T.map (QuotientGroup.mk' N)) := by
        intro x hx
        rw [A38.mem_map_conj] at hx
        have := mem_conjClosure htT hx
        simpa [mul_assoc] using this
      rcases A38.eq_or_eq_of_le_sup h37 hLt hLbar hLt' hle with h | h
      · exact absurd (A38.map_conj_eq_iff.mp h) htn
      · have heq : conjClosure Lb (T.map (QuotientGroup.mk' N)) = conjClosure Lb ⊤ := by
          refine le_antisymm (conjClosure_mono le_rfl le_top) ?_
          rw [hcl', ← h]
          exact sup_le (le_conjClosure _ _) hTt
        rw [heq]
        exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_conjClosure _ _))

end Transfer

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem cCompSpan_eq_perfectCore_of_subgroup (H : Subgroup G)
    (h : cCompSpan (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) =
      perfectCore (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) :
    cCompSpan H = perfectCore H := by
  have h1 := cCompSpan_eq_perfectCore_of_pCore h
  have h2 := map_perfectCore H.subtype (⊤ : Subgroup ↥H)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h2
  rw [cCompSpan_eq_map_subtype, h1, h2]

end Ambient

section Ambient2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_mem_cComp_of_le {H Y L : Subgroup G} (hYH : Y ≤ H) (hL : L ∈ cComp Y) :
    L.subgroupOf H ∈ cComp (Y.subgroupOf H) := by
  have hLH : L ≤ H := (le_of_mem_cComp hL).trans hYH
  have hLL' : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  refine ⟨?_, ?_, A4.subnormal_subgroupOf H (subnormal_of_mem_cComp hL), ?_⟩
  · intro h
    apply ne_bot_of_mem_cComp hL
    rw [← hLL', h, Subgroup.map_bot]
  · apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hLL', perfect_of_mem_cComp hL]
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hKlt : K'.map H.subtype < L := by
      rw [← hLL']
      exact lt_of_le_of_ne (Subgroup.map_mono hK'lt.le) fun h =>
        hK'lt.ne (Subgroup.map_injective H.subtype_injective h)
    have hKne : K'.map H.subtype ≠ ⊥ := fun h =>
      hK'ne ((Subgroup.map_eq_bot_iff_of_injective K' H.subtype_injective).mp h)
    have hKperf : ⁅K'.map H.subtype, K'.map H.subtype⁆ = K'.map H.subtype := by
      rw [← Subgroup.map_commutator, hK'perf]
    have hKsub : IsSubnormal (K'.map H.subtype) Y := by
      have := A3.subnormal_map H.subtype hK'sub
      rwa [Subgroup.map_subgroupOf_eq_of_le hYH] at this
    exact not_subnormal_of_mem_cComp hL hKlt hKne hKperf hKsub

omit [Finite G] in
theorem isSylowTwoOf_top_subgroupOf {S H : Subgroup G} (hS : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.subgroupOf H) (⊤ : Subgroup ↥H) := by
  refine ⟨le_top, A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1, ?_⟩
  have h1 : ((S.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).index = (S.subgroupOf H).index :=
    Subgroup.relIndex_top_right _
  rw [h1]
  exact hS.2.2

omit [Finite G] in
theorem pCore_two_le_subgroupOf {S H : Subgroup G} (hS : IsSylowTwoOf S H) :
    CFSG.pCore 2 ↥H ≤ S.subgroupOf H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  exact (CFSG.pCore_isPGroup (G := ↥H) (p := 2)).le_sylow_of_normal (A4.toSylow hS)

theorem exists_cComp_ge_of_subgroup {H S B : Subgroup G} (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H))
    (h39 : A39Statement (↥H ⧸ CFSG.pCore 2 ↥H)) : ∃ K ∈ cComp H, B ≤ K := by
  have hB' : B ∈ cComp (B ⊔ S) := hB
  have hBS : B ⊔ S ≤ H := sup_le hBH hS.1
  have hB'' : B.subgroupOf H ∈ lFamily (S.subgroupOf H) := by
    show B.subgroupOf H ∈ cComp (B.subgroupOf H ⊔ S.subgroupOf H)
    rw [← Subgroup.subgroupOf_sup hBH hS.1]
    exact subgroupOf_mem_cComp_of_le hBS hB'
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  obtain ⟨K', hK', hBK'⟩ := exists_cComp_ge_of_lFamily (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group _)
    h37 h39 (isSylowTwoOf_top_subgroupOf hS) (pCore_two_le_subgroupOf hS) hB''
  refine ⟨K'.map H.subtype, map_subtype_mem_cComp hK', ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hBH]
  exact Subgroup.map_mono hBK'

theorem normal_conjClosure_of_subgroup {H T L : Subgroup G} (hT : IsSylowTwoOf T H)
    (hL : L ∈ cComp H) (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H))
    (h38 : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H)) :
    H ≤ Subgroup.normalizer (conjClosure L T : Set G) := by
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hn := normal_conjClosure_of_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group _) h37 h38
    (subgroupOf_mem_cComp hL) (isSylowTwoOf_top_subgroupOf hT)
  have hmap : (conjClosure (L.subgroupOf H) (T.subgroupOf H)).map H.subtype = conjClosure L T := by
    rw [A3.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL),
      Subgroup.map_subgroupOf_eq_of_le hT.1]
  intro h hh
  have h1 : (⟨h, hh⟩ : ↥H) ∈ Subgroup.normalizer
      (conjClosure (L.subgroupOf H) (T.subgroupOf H) : Set ↥H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hn]
    exact Subgroup.mem_top _
  have h2 := Subgroup.le_normalizer_map (H := conjClosure (L.subgroupOf H) (T.subgroupOf H))
    H.subtype ⟨⟨h, hh⟩, h1, rfl⟩
  rwa [hmap] at h2

end Ambient2

end CFSG.Quasithin
