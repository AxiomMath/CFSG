module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.Ordering
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace A3

theorem isSubnormal_of_subnormal {H K : Subgroup G} (h : IsSubnormal H K) (hK : K.IsSubnormal) :
    H.IsSubnormal :=
  h.mathlib hK

theorem subnormal_top_iff {H : Subgroup G} : IsSubnormal H ⊤ ↔ H.IsSubnormal :=
  CFSG.Open.IsSubnormal.top_iff

theorem subnormal_top_map {Q : Type*} [Group Q] {f : G →* Q} (hf : Function.Surjective f)
    {H : Subgroup G} (h : IsSubnormal H ⊤) : IsSubnormal (H.map f) ⊤ := by
  have := subnormal_map f h
  rwa [Subgroup.map_top_of_surjective f hf] at this

theorem subnormal_top_comap {Q : Type*} [Group Q] (f : G →* Q) {H : Subgroup Q}
    (h : IsSubnormal H ⊤) : IsSubnormal (H.comap f) ⊤ := by
  have := subnormal_comap f h
  rwa [Subgroup.comap_top] at this

theorem eq_top_or_le_center_of_subnormal {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {H : Subgroup Q} (hH : H.IsSubnormal) : H = ⊤ ∨ H ≤ Subgroup.center Q := by
  induction hH with
  | top => exact Or.inl rfl
  | step H K hle _ hN ih =>
    rcases ih with rfl | hKc
    · have hHn : H.Normal := by
        have := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
        rw [top_le_iff, Subgroup.normalizer_eq_top_iff] at this
        exact this
      exact CFSG.LocalCores.quasisimple_normal_subgroups hQ hHn
    · exact Or.inr (hle.trans hKc)

end A3

instance A3.instNormalSolvableRadical (G : Type*) [Group G] : (CFSG.solvableRadical G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem A3.solvableRadical_eq_solvRad_top (G : Type*) [Group G] :
    CFSG.solvableRadical G = solvRad (⊤ : Subgroup G) := by
  unfold CFSG.solvableRadical solvRad
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, le_top, true_and]
  have : (N.subgroupOf ⊤).Normal ↔ N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top, top_le_iff,
      Subgroup.normalizer_eq_top_iff]
  rw [this]

theorem A3.solvableRadical_isSolvable [Finite G] : Group.IsSolvable (CFSG.solvableRadical G) := by
  have h := solvRad_isSolvable (⊤ : Subgroup G)
  rw [← A3.solvableRadical_eq_solvRad_top] at h
  exact h

theorem A3.le_solvableRadical {N : Subgroup G} (hN : N.Normal) (hs : Group.IsSolvable N) :
    N ≤ CFSG.solvableRadical G :=
  le_sSup ⟨hN, hs⟩

theorem A3.solvableRadical_quotient_eq_bot (G : Type*) [Group G] [Finite G] :
    CFSG.solvableRadical (G ⧸ CFSG.solvableRadical G) = ⊥ := by
  set R := CFSG.solvableRadical G with hR
  set R' := CFSG.solvableRadical (G ⧸ R) with hR'
  have hRs : Group.IsSolvable R := A3.solvableRadical_isSolvable
  have hR's : Group.IsSolvable R' := A3.solvableRadical_isSolvable
  let Φ : G →* G ⧸ R := QuotientGroup.mk' R
  let P : Subgroup G := R'.comap Φ
  have hRP : R ≤ P := fun x hx => by
    have h1 : (x : G ⧸ R) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show (x : G ⧸ R) ∈ R'
    rw [h1]
    exact R'.one_mem
  have hPnormal : P.Normal := Subgroup.Normal.comap inferInstance _
  have hPs : Group.IsSolvable P := by
    let g : ↥P →* ↥R' := (Φ.comp P.subtype).codRestrict R' (fun p => p.2)
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hRP) g (fun p hp => ?_)
    have h1 : Φ p = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
      exact this
    have h2 : (p : G) ∈ R := (QuotientGroup.eq_one_iff (p : G)).mp h1
    exact ⟨⟨p, h2⟩, rfl⟩
  have hPR : P ≤ R := A3.le_solvableRadical hPnormal hPs
  have h3 : R'  = P.map Φ := (Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective R) R').symm
  have h4 : P.map Φ ≤ ⊥ := by
    have := Subgroup.map_mono (f := Φ) hPR
    rwa [QuotientGroup.map_mk'_self] at this
  exact le_bot_iff.mp (h3 ▸ h4)

theorem cComp_map_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') {X L : Subgroup G}
    (hL : L ∈ cComp X) : L.map e.toMonoidHom ∈ cComp (X.map e.toMonoidHom) := by
  refine ⟨?_, ?_, A3.subnormal_map _ (subnormal_of_mem_cComp hL), ?_⟩
  · intro h
    exact ne_bot_of_mem_cComp hL ((Subgroup.map_eq_bot_iff_of_injective L e.injective).mp h)
  · rw [← Subgroup.map_commutator, perfect_of_mem_cComp hL]
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hKL : K'.comap e.toMonoidHom < L := by
      refine lt_of_le_of_ne ?_ ?_
      · calc K'.comap e.toMonoidHom ≤ (L.map e.toMonoidHom).comap e.toMonoidHom :=
            Subgroup.comap_mono hK'lt.le
          _ = L := Subgroup.comap_map_eq_self_of_injective e.injective L
      · intro h
        have := congrArg (Subgroup.map e.toMonoidHom) h
        rw [Subgroup.map_comap_eq_self_of_surjective e.surjective] at this
        exact hK'lt.ne this
    have hKne : K'.comap e.toMonoidHom ≠ ⊥ := by
      intro h
      apply hK'ne
      have := congrArg (Subgroup.map e.toMonoidHom) h
      rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective, Subgroup.map_bot] at this
    have hKperf : ⁅K'.comap e.toMonoidHom, K'.comap e.toMonoidHom⁆ = K'.comap e.toMonoidHom := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective e.surjective, hK'perf]
    have hKsub : IsSubnormal (K'.comap e.toMonoidHom) X := by
      have := A3.subnormal_comap e.toMonoidHom hK'sub
      rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at this
    exact not_subnormal_of_mem_cComp hL hKL hKne hKperf hKsub

theorem map_mem_cComp_top [Finite G] {Q : Type*} [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker) {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) : L.map f ∈ cComp (⊤ : Subgroup Q) := by
  have : Finite Q := Finite.of_surjective f hf
  have h3 := fun K (hK : K ∈ cComp (⊤ : Subgroup G)) =>
    cComp_commutator_perfectCore hK le_top hker Subgroup.le_normalizer_of_normal
  refine ⟨?_, ?_, A3.subnormal_top_map hf (subnormal_of_mem_cComp hL), ?_⟩
  · intro hbot
    have hLk : L ≤ f.ker := (Subgroup.map_eq_bot_iff L).mp hbot
    have : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLk)
        (Subgroup.inclusion_injective hLk)
    exact not_isSolvable_of_mem_cComp hL this
  · rw [← Subgroup.map_commutator, perfect_of_mem_cComp hL]
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hfK : (K'.comap f).map f = K' := Subgroup.map_comap_eq_self_of_surjective hf K'
    have hKsub : IsSubnormal (K'.comap f) ⊤ := A3.subnormal_top_comap f hK'sub
    have hKinf : K'.comap f ≤ L ⊔ f.ker :=
      calc K'.comap f ≤ (L.map f).comap f := Subgroup.comap_mono hK'lt.le
        _ = L ⊔ f.ker := Subgroup.comap_map_eq f L
    have hKcore_le : perfectCore (K'.comap f) ≤ L :=
      calc perfectCore (K'.comap f) ≤ perfectCore (L ⊔ f.ker) := perfectCore_mono hKinf
        _ = L := (h3 L hL).2
    have hKcore_ne : perfectCore (K'.comap f) ≠ ⊥ := by
      intro h
      apply hK'ne
      have := map_perfectCore f (K'.comap f)
      rw [h, Subgroup.map_bot, hfK, perfectCore_eq_self_of_perfect hK'perf] at this
      exact this.symm
    have hKcore_eq : perfectCore (K'.comap f) = L := by
      by_contra hne
      exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hKcore_le hne) hKcore_ne
        (perfectCore_perfect _) (A3.subnormal_perfectCore hKsub)
    have : L.map f = K' := by
      rw [← hKcore_eq, map_perfectCore, hfK, perfectCore_eq_self_of_perfect hK'perf]
    exact hK'lt.ne this.symm

theorem map_injOn_cComp_top [Finite G] {Q : Type*} [Group Q] (f : G →* Q)
    (hker : Group.IsSolvable f.ker) : Set.InjOn (Subgroup.map f) (cComp (⊤ : Subgroup G)) := by
  intro L hL L₁ hL₁ h
  have e : L ⊔ f.ker = L₁ ⊔ f.ker := by
    rw [← Subgroup.comap_map_eq, ← Subgroup.comap_map_eq, h]
  have h3 := fun K (hK : K ∈ cComp (⊤ : Subgroup G)) =>
    cComp_commutator_perfectCore hK le_top hker Subgroup.le_normalizer_of_normal
  calc L = perfectCore (L ⊔ f.ker) := ((h3 L hL).2).symm
    _ = perfectCore (L₁ ⊔ f.ker) := by rw [e]
    _ = L₁ := (h3 L₁ hL₁).2

theorem map_surjOn_cComp_top [Finite G] {Q : Type*} [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker) :
    Set.SurjOn (Subgroup.map f) (cComp (⊤ : Subgroup G)) (cComp (⊤ : Subgroup Q)) := by
  intro K' hK'
  have : Finite Q := Finite.of_surjective f hf
  have hfK : (K'.comap f).map f = K' := Subgroup.map_comap_eq_self_of_surjective hf K'
  have hKsub : IsSubnormal (K'.comap f) ⊤ :=
    A3.subnormal_top_comap f (subnormal_of_mem_cComp hK')
  have hcore_sub : IsSubnormal (perfectCore (K'.comap f)) ⊤ := A3.subnormal_perfectCore hKsub
  have hcore_ne : perfectCore (K'.comap f) ≠ ⊥ := by
    intro h
    apply ne_bot_of_mem_cComp hK'
    have := map_perfectCore f (K'.comap f)
    rw [h, Subgroup.map_bot, hfK, perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK')]
      at this
    exact this.symm
  obtain ⟨L, hLmin⟩ := (Set.toFinite {J : Subgroup G | J ≤ perfectCore (K'.comap f) ∧ J ≠ ⊥ ∧
      ⁅J, J⁆ = J ∧ IsSubnormal J ⊤}).exists_minimal
    ⟨perfectCore (K'.comap f), le_rfl, hcore_ne, perfectCore_perfect _, hcore_sub⟩
  obtain ⟨hLle, hLne, hLperf, hLsub⟩ := hLmin.prop
  have hL : L ∈ cComp (⊤ : Subgroup G) := by
    refine ⟨hLne, hLperf, hLsub, fun J hJL hJne hJperf hJsub => ?_⟩
    exact hJL.ne (hLmin.eq_of_le ⟨hJL.le.trans hLle, hJne, hJperf, hJsub⟩ hJL.le)
  refine ⟨L, hL, ?_⟩
  have hLf : L.map f ∈ cComp (⊤ : Subgroup Q) := map_mem_cComp_top f hf hker hL
  have hle : L.map f ≤ K' :=
    calc L.map f ≤ (K'.comap f).map f :=
          Subgroup.map_mono (hLle.trans (perfectCore_le _))
      _ = K' := hfK
  by_contra hne
  exact not_subnormal_of_mem_cComp hK' (lt_of_le_of_ne hle hne) (ne_bot_of_mem_cComp hLf)
    (perfect_of_mem_cComp hLf) (subnormal_of_mem_cComp hLf)

theorem cComp_map_bijOn [Finite G] {Q : Type*} [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker) :
    Set.BijOn (Subgroup.map f) (cComp (⊤ : Subgroup G)) (cComp (⊤ : Subgroup Q)) :=
  ⟨fun _ hL => map_mem_cComp_top f hf hker hL, map_injOn_cComp_top f hker,
    map_surjOn_cComp_top f hf hker⟩

theorem cComp_quotient_bijOn [Finite G] (N : Subgroup G) [N.Normal] (hN : Group.IsSolvable N) :
    Set.BijOn (Subgroup.map (QuotientGroup.mk' N)) (cComp (⊤ : Subgroup G))
      (cComp (⊤ : Subgroup (G ⧸ N))) :=
  cComp_map_bijOn (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by rw [QuotientGroup.ker_mk']; exact hN)

theorem image_cComp_quotient [Finite G] (N : Subgroup G) [N.Normal] (hN : Group.IsSolvable N) :
    Subgroup.map (QuotientGroup.mk' N) '' cComp (⊤ : Subgroup G) =
      cComp (⊤ : Subgroup (G ⧸ N)) :=
  (cComp_quotient_bijOn N hN).image_eq

theorem isComponent_of_mem_cComp_top [Finite G] (hG : CFSG.solvableRadical G = ⊥)
    {K : Subgroup G} (hK : K ∈ cComp (⊤ : Subgroup G)) : CFSG.IsComponent K := by
  have hsub : K.IsSubnormal := A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hK)
  have hrad : solvRad K = ⊥ := by
    have h1 := solvRad_le_solvRad_of_subnormal (subnormal_of_mem_cComp hK)
    rw [← A3.solvableRadical_eq_solvRad_top, hG] at h1
    exact le_bot_iff.mp h1
  have hnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr (ne_bot_of_mem_cComp hK)
  have hsimple : IsSimpleGroup ↥K := by
    refine ⟨fun T hT => ?_⟩
    rcases normal_eq_top_or_map_le_solvRad hK T with h | h
    · exact Or.inr h
    · left
      rw [hrad, le_bot_iff] at h
      exact (Subgroup.map_eq_bot_iff_of_injective T K.subtype_injective).mp h
  have hnonab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    exact not_isSolvable_of_mem_cComp hK (Group.isSolvable_of_comm hcomm)
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1, hsub⟩

theorem mem_cComp_top_of_isComponent [Finite G] {K : Subgroup G} (hK : CFSG.IsComponent K) :
    K ∈ cComp (⊤ : Subgroup G) := by
  obtain ⟨hq, hsub⟩ := hK
  have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨(Subgroup.nontrivial_iff_ne_bot K).mp hnt, hperf, A3.subnormal_top_iff.mpr hsub,
    fun K' hK'lt hK'ne hK'perf hK'sub => ?_⟩
  have h1 : IsSubnormal K' K := A3.subnormal_of_le_of_le hK'sub hK'lt.le le_top
  have h2 : (K'.subgroupOf K).IsSubnormal := by
    have := A3.subnormal_comap K.subtype h1
    have h3 : K.comap K.subtype = ⊤ := Subgroup.subgroupOf_self K
    rw [h3] at this
    exact A3.subnormal_top_iff.mp this
  rcases A3.eq_top_or_le_center_of_subnormal hq h2 with htop | hcenter
  · exact hK'lt.not_ge (Subgroup.subgroupOf_eq_top.mp htop)
  · apply hK'ne
    rw [← hK'perf]
    refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
    have hac : (⟨a, hK'lt.le ha⟩ : ↥K) ∈ Subgroup.center ↥K :=
      hcenter (Subgroup.mem_subgroupOf.mpr ha)
    have := Subgroup.mem_center_iff.mp hac ⟨b, hK'lt.le hb⟩
    have h4 : b * a = a * b := congrArg Subtype.val this
    exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr h4.symm)

theorem cComp_top_eq_components [Finite G] (hG : CFSG.solvableRadical G = ⊥) :
    cComp (⊤ : Subgroup G) = {K | CFSG.IsComponent K} :=
  Set.ext fun _ => ⟨isComponent_of_mem_cComp_top hG, mem_cComp_top_of_isComponent⟩

theorem A3.isQuasisimple_iff_open {Q : Type*} [Group Q] :
    CFSG.IsQuasisimple Q ↔ CFSG.Open.IsQuasisimple Q := by
  constructor
  · rintro ⟨hp, hs, -⟩
    exact ⟨Group.isPerfect_def.mp hp, hs⟩
  · rintro ⟨hc, hs⟩
    refine ⟨Group.isPerfect_def.mpr hc, hs, ?_⟩
    by_contra hcomm
    push Not at hcomm
    have hle : commutator Q ≤ Subgroup.center Q := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      have h1 : QuotientGroup.mk' (Subgroup.center Q) ⁅a, b⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
      exact (QuotientGroup.eq_one_iff _).mp h1
    have htop : Subgroup.center Q = ⊤ := top_le_iff.mp (hc ▸ hle)
    have : Nontrivial (Q ⧸ Subgroup.center Q) := hs.toNontrivial
    exact QuotientGroup.nontrivial_iff.mp this htop

theorem A3.isComponentOf_top_iff {K : Subgroup G} :
    CFSG.Open.IsComponentOf K ⊤ ↔ CFSG.IsComponent K := by
  constructor
  · rintro ⟨-, hsub, hq⟩
    exact ⟨A3.isQuasisimple_iff_open.mpr hq, A3.subnormal_top_iff.mp hsub⟩
  · rintro ⟨hq, hsub⟩
    exact ⟨le_top, A3.subnormal_top_iff.mpr hsub, A3.isQuasisimple_iff_open.mp hq⟩

theorem mem_cComp_top_iff_isCComponent {L : Subgroup G} :
    L ∈ cComp (⊤ : Subgroup G) ↔ CFSG.IsCComponent L := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, A3.subnormal_top_iff.mp h3, fun K hK hK' hK'' hsub =>
      h4 K hK hK' hK'' (A3.subnormal_top_iff.mpr hsub)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, A3.subnormal_top_iff.mpr h3, fun K hK hK' hK'' hsub =>
      h4 K hK hK' hK'' (A3.subnormal_top_iff.mp hsub)⟩

theorem cComp_top_eq_isComponentOf [Finite G] (hG : CFSG.solvableRadical G = ⊥) :
    cComp (⊤ : Subgroup G) = {K | CFSG.Open.IsComponentOf K ⊤} := by
  rw [cComp_top_eq_components hG]
  ext K
  exact A3.isComponentOf_top_iff.symm

@[expose] def oInftyE (G : Type*) [Group G] : Subgroup G :=
  (CFSG.layer (G ⧸ CFSG.solvableRadical G)).comap (QuotientGroup.mk' (CFSG.solvableRadical G))

@[expose] def cCompSpan (X : Subgroup G) : Subgroup G := sSup (cComp X)

theorem le_cCompSpan {X L : Subgroup G} (hL : L ∈ cComp X) : L ≤ cCompSpan X := le_sSup hL

theorem map_cCompSpan_eq_layer [Finite G] :
    (cCompSpan (⊤ : Subgroup G)).map (QuotientGroup.mk' (CFSG.solvableRadical G)) =
      CFSG.layer (G ⧸ CFSG.solvableRadical G) := by
  have hbij := cComp_quotient_bijOn (CFSG.solvableRadical G)
    (A3.solvableRadical_isSolvable (G := G))
  have h1 : {K : Subgroup (G ⧸ CFSG.solvableRadical G) | CFSG.IsComponent K} =
      Subgroup.map (QuotientGroup.mk' (CFSG.solvableRadical G)) '' cComp (⊤ : Subgroup G) := by
    rw [← cComp_top_eq_components (A3.solvableRadical_quotient_eq_bot G)]
    exact hbij.image_eq.symm
  simp only [CFSG.layer.eq_sSup]; unfold cCompSpan
  rw [h1, sSup_image]
  exact (Subgroup.gc_map_comap (QuotientGroup.mk' (CFSG.solvableRadical G))).l_sSup

theorem cCompSpan_normal [Finite G] : (cCompSpan (⊤ : Subgroup G)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmap : (cCompSpan (⊤ : Subgroup G)).map (MulAut.conj g : G →* G) ≤
      cCompSpan (⊤ : Subgroup G) := by
    unfold cCompSpan
    rw [(Subgroup.gc_map_comap _).l_sSup]
    refine iSup₂_le fun L hL => le_sSup ?_
    have := cComp_map_mulEquiv (MulAut.conj g) hL
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at this
  exact hmap ⟨n, hn, rfl⟩

theorem cCompSpan_perfect [Finite G] :
    ⁅cCompSpan (⊤ : Subgroup G), cCompSpan (⊤ : Subgroup G)⁆ = cCompSpan (⊤ : Subgroup G) := by
  have : cCompSpan (⊤ : Subgroup G) = ⨆ L : cComp (⊤ : Subgroup G), (L : Subgroup G) :=
    sSup_eq_iSup' _
  rw [this]
  exact A3.commutator_iSup_eq_of_perfect _ fun L => perfect_of_mem_cComp L.2

theorem cComp_part_five [Finite G] :
    cComp (⊤ : Subgroup (G ⧸ CFSG.solvableRadical G)) = {K | CFSG.IsComponent K} ∧
      cCompSpan (⊤ : Subgroup G) = perfectCore (oInftyE G) := by
  refine ⟨cComp_top_eq_components (A3.solvableRadical_quotient_eq_bot G), ?_⟩
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := A3.solvableRadical_isSolvable
  have hoE : oInftyE G = cCompSpan (⊤ : Subgroup G) ⊔ CFSG.solvableRadical G := by
    show (CFSG.layer (G ⧸ CFSG.solvableRadical G)).comap
      (QuotientGroup.mk' (CFSG.solvableRadical G)) = _
    rw [← map_cCompSpan_eq_layer, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [hoE]
  have := (cCompSpan_normal (G := G))
  refine le_antisymm (le_perfectCore_of_perfect le_sup_left cCompSpan_perfect) ?_
  exact perfectCore_le_of_sup_solvable le_sup_left Subgroup.normal_subgroupOf rfl hRs

theorem cComp_normal_span [Finite G] {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G)) :
    L ≤ cCompSpan (⊤ : Subgroup G) ∧ (L.subgroupOf (cCompSpan (⊤ : Subgroup G))).Normal := by
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := A3.solvableRadical_isSolvable
  have hker : Group.IsSolvable (QuotientGroup.mk' (CFSG.solvableRadical G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hRs
  have hK : L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ∈
      cComp (⊤ : Subgroup (G ⧸ CFSG.solvableRadical G)) :=
    map_mem_cComp_top _ (QuotientGroup.mk'_surjective _) hker hL
  have hKcomp := isComponent_of_mem_cComp_top (A3.solvableRadical_quotient_eq_bot G) hK
  have hlayer_norm : CFSG.layer (G ⧸ CFSG.solvableRadical G) ≤
      Subgroup.normalizer (L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) : Set _) := by
    refine sSup_le fun K' hK' => ?_
    rcases CFSG.LocalCores.distinct_components_commute hK' hKcomp with h | h
    · rw [h]
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
        (Subgroup.centralizer_le_normalizer _)
  refine ⟨le_cCompSpan hL, (Subgroup.normal_subgroupOf_iff (le_cCompSpan hL)).mpr
    fun l h hl hh => ?_⟩
  have hΦh : QuotientGroup.mk' (CFSG.solvableRadical G) h ∈
      CFSG.layer (G ⧸ CFSG.solvableRadical G) := by
    rw [← map_cCompSpan_eq_layer]
    exact Subgroup.mem_map_of_mem _ hh
  have hΦnorm := hlayer_norm hΦh
  have hL'le : L.map (MulAut.conj h : G →* G) ≤ L ⊔ CFSG.solvableRadical G := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : QuotientGroup.mk' (CFSG.solvableRadical G) (h * y * h⁻¹) ∈
        L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hΦnorm _).mp (Subgroup.mem_map_of_mem _ hy)
    have h2 : h * y * h⁻¹ ∈
        (L.map (QuotientGroup.mk' (CFSG.solvableRadical G))).comap
          (QuotientGroup.mk' (CFSG.solvableRadical G)) := h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hL'perf : ⁅L.map (MulAut.conj h : G →* G), L.map (MulAut.conj h : G →* G)⁆ =
      L.map (MulAut.conj h : G →* G) := by
    rw [← Subgroup.map_commutator, perfect_of_mem_cComp hL]
  have hL'core : L.map (MulAut.conj h : G →* G) ≤ L := by
    have := le_perfectCore_of_perfect hL'le hL'perf
    rwa [(cComp_commutator_perfectCore hL le_top hRs Subgroup.le_normalizer_of_normal).2]
      at this
  exact hL'core ⟨l, hl, rfl⟩

theorem A3.le_normalizer_commutator_left (A B : Subgroup G) :
    A ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ A, ⁅A, B⁆ ≤ (⁅A, B⁆).comap (MulAut.conj a : G →* G) := by
    intro a ha
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    show a * ⁅x, y⁆ * a⁻¹ ∈ ⁅A, B⁆
    have : a * ⁅x, y⁆ * a⁻¹ = ⁅a * x, y⁆ * ⁅a, y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (A.mul_mem ha hx) hy)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hy))
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key a ha hz, fun hz => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) hz
  simpa [mul_assoc] using this

theorem A3.sup_le_normalizer_commutator (A B : Subgroup G) :
    A ⊔ B ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) :=
  sup_le (A3.le_normalizer_commutator_left A B)
    (by rw [Subgroup.commutator_comm]; exact A3.le_normalizer_commutator_left B A)

theorem A3.map_conjClosure {G' : Type*} [Group G'] (f : G →* G') (Z H : Subgroup G) :
    (conjClosure Z H).map f = conjClosure (Z.map f) (H.map f) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine conjClosure_le fun h hh z hz => ?_
    show f (h * z * h⁻¹) ∈ conjClosure (Z.map f) (H.map f)
    rw [map_mul, map_mul, map_inv]
    exact mem_conjClosure (Subgroup.mem_map_of_mem f hh) (Subgroup.mem_map_of_mem f hz)
  · refine conjClosure_le fun h' hh' z' hz' => ?_
    obtain ⟨h, hh, rfl⟩ := hh'
    obtain ⟨z, hz, rfl⟩ := hz'
    exact ⟨h * z * h⁻¹, mem_conjClosure hh hz, by simp⟩

theorem A3.commutator_le_conjClosure (Z H : Subgroup G) : ⁅Z, H⁆ ≤ conjClosure Z H := by
  refine Subgroup.commutator_le.mpr fun z hz h hh => ?_
  have : ⁅z, h⁆ = z * (h * z⁻¹ * h⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact Subgroup.mul_mem _ (le_conjClosure Z H hz) (mem_conjClosure hh (Z.inv_mem hz))

theorem A3.conjClosure_le_sup (Z H : Subgroup G) : conjClosure Z H ≤ Z ⊔ H :=
  conjClosure_le fun _ hh _ hz => Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hz))
    (Subgroup.inv_mem _ (Subgroup.mem_sup_right hh))

theorem A3.conjClosure_perfect {Z H : Subgroup G} (hZ : ⁅Z, Z⁆ = Z) :
    ⁅conjClosure Z H, conjClosure Z H⁆ = conjClosure Z H := by
  refine le_antisymm (A3.commutator_self_le _) (conjClosure_le fun h hh z hz => ?_)
  have hz' : z ∈ ⁅conjClosure Z H, conjClosure Z H⁆ := by
    have : z ∈ ⁅Z, Z⁆ := by rw [hZ]; exact hz
    exact Subgroup.commutator_mono (le_conjClosure Z H) (le_conjClosure Z H) this
  have hnorm : h ∈ Subgroup.normalizer
      ((⁅conjClosure Z H, conjClosure Z H⁆ : Subgroup G) : Set G) := by
    have h1 := map_conj_derivedSeriesOf (le_normalizer_conjClosure Z H hh) 1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  exact (Subgroup.mem_normalizer_iff.mp hnorm z).mp hz'

theorem cComp_commutator_dichotomy [Finite G] {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (X : Subgroup G) :
    (⁅L, X⁆ ≤ CFSG.solvableRadical G ∧ Group.IsSolvable ↥⁅L, X⁆) ∨
      ⁅L, X⁆ = conjClosure L X := by
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := A3.solvableRadical_isSolvable
  have hker : Group.IsSolvable (QuotientGroup.mk' (CFSG.solvableRadical G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hRs
  have hK : L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ∈
      cComp (⊤ : Subgroup (G ⧸ CFSG.solvableRadical G)) :=
    map_mem_cComp_top _ (QuotientGroup.mk'_surjective _) hker hL
  have hKcomp := isComponent_of_mem_cComp_top (A3.solvableRadical_quotient_eq_bot G) hK
  by_cases hcomm : ⁅L.map (QuotientGroup.mk' (CFSG.solvableRadical G)),
      X.map (QuotientGroup.mk' (CFSG.solvableRadical G))⁆ = ⊥
  · left
    have hle : ⁅L, X⁆ ≤ CFSG.solvableRadical G := by
      have : (⁅L, X⁆).map (QuotientGroup.mk' (CFSG.solvableRadical G)) = ⊥ := by
        rw [Subgroup.map_commutator]
        exact hcomm
      rw [← QuotientGroup.ker_mk' (CFSG.solvableRadical G)]
      exact (Subgroup.map_eq_bot_iff _).mp this
    exact ⟨hle, Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)⟩
  · right
    have hKM : L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ≤
        L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ⊔
          X.map (QuotientGroup.mk' (CFSG.solvableRadical G)) := le_sup_left
    have hYnorm := A3.sup_le_normalizer_commutator
      (L.map (QuotientGroup.mk' (CFSG.solvableRadical G)))
      (X.map (QuotientGroup.mk' (CFSG.solvableRadical G)))
    have hYM : ⁅L.map (QuotientGroup.mk' (CFSG.solvableRadical G)),
        X.map (QuotientGroup.mk' (CFSG.solvableRadical G))⁆ ≤
        L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ⊔
          X.map (QuotientGroup.mk' (CFSG.solvableRadical G)) :=
      Subgroup.commutator_le.mpr fun a ha b hb => Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
          (Subgroup.mem_sup_right hb)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha)))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hb))
    have hKcompM := CFSG.LocalCores.component_overgroup hKcomp hKM
    have hYn := Subgroup.normal_subgroupOf_of_le_normalizer hYnorm
    have hKY : L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ≤
        ⁅L.map (QuotientGroup.mk' (CFSG.solvableRadical G)),
          X.map (QuotientGroup.mk' (CFSG.solvableRadical G))⁆ := by
      rcases CFSG.LocalCores.component_normal_subgroup hKcompM hYn with h | h
      · exact CFSG.LocalCores.le_of_subgroupOf_le hKM h
      · exfalso
        have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hKM h
        rw [inf_eq_left.mpr hYM] at h1
        apply hcomm
        refine CFSG.LocalCores.perfect_double_commutator hKcomp.1.1 ?_
        rw [Subgroup.commutator_comm] at h1
        exact h1
    have hYeq : ⁅L.map (QuotientGroup.mk' (CFSG.solvableRadical G)),
        X.map (QuotientGroup.mk' (CFSG.solvableRadical G))⁆ =
        conjClosure (L.map (QuotientGroup.mk' (CFSG.solvableRadical G)))
          (X.map (QuotientGroup.mk' (CFSG.solvableRadical G))) := by
      refine le_antisymm (A3.commutator_le_conjClosure _ _) (conjClosure_le fun h hh z hz => ?_)
      have hn := hYnorm (Subgroup.mem_sup_right hh)
      exact (Subgroup.mem_normalizer_iff.mp hn z).mp (hKY hz)
    have himg : (⁅L, X⁆).map (QuotientGroup.mk' (CFSG.solvableRadical G)) =
        (conjClosure L X).map (QuotientGroup.mk' (CFSG.solvableRadical G)) := by
      rw [Subgroup.map_commutator, A3.map_conjClosure]
      exact hYeq
    have hsup : ⁅L, X⁆ ⊔ CFSG.solvableRadical G = conjClosure L X ⊔ CFSG.solvableRadical G := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.solvableRadical G))) himg
      rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    have hcJ : ⁅L, X⁆ ≤ conjClosure L X := A3.commutator_le_conjClosure L X
    have hJle : conjClosure L X ≤ ⁅L, X⁆ ⊔ CFSG.solvableRadical G :=
      le_of_le_of_eq le_sup_left hsup.symm
    have hJeq : conjClosure L X = ⁅L, X⁆ ⊔ (conjClosure L X ⊓ CFSG.solvableRadical G) :=
      A3.eq_sup_inf_of_le_sup Subgroup.le_normalizer_of_normal hcJ hJle
    have hnormJ : (⁅L, X⁆.subgroupOf (conjClosure L X)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        ((A3.conjClosure_le_sup L X).trans (A3.sup_le_normalizer_commutator L X))
    have hRJ : Group.IsSolvable ↥(conjClosure L X ⊓ CFSG.solvableRadical G) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_right : conjClosure L X ⊓ CFSG.solvableRadical G ≤
          CFSG.solvableRadical G)) (Subgroup.inclusion_injective _)
    have h1 : perfectCore (conjClosure L X) ≤ ⁅L, X⁆ :=
      perfectCore_le_of_sup_solvable hcJ hnormJ hJeq hRJ
    rw [perfectCore_eq_self_of_perfect (A3.conjClosure_perfect (perfect_of_mem_cComp hL))] at h1
    exact le_antisymm hcJ h1

end CFSG.Quasithin
