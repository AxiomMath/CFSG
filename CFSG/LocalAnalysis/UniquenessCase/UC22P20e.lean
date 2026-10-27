module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p20e_eq_top_of_central_sylow {Γ : Type} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    (N' S' : Subgroup Γ) [N'.Normal] (hS2 : IsPGroup 2 S') (hSodd : ¬ 2 ∣ S'.index)
    (hcomm : ∀ s ∈ S', ∀ g : Γ, ⁅s, g⁆ ∈ N') : N' = ⊤ := by
  let φ : Γ →* Γ ⧸ N' := QuotientGroup.mk' N'
  let Z : Subgroup (Γ ⧸ N') := S'.map φ
  have hZc : ∀ z ∈ Z, ∀ y : Γ ⧸ N', z * y = y * z := by
    rintro _ ⟨s, hs, rfl⟩ y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N' y
    have h1 : φ ⁅s, g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcomm s hs g)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  haveI hZn : Z.Normal := ⟨fun n hn g => by
    have := hZc n hn g
    rw [show g * n * g⁻¹ = n by rw [← this]; group]
    exact hn⟩
  haveI hZcomm : IsMulCommutative Z := ⟨⟨fun a b => Subtype.ext (hZc a a.2 b)⟩⟩
  haveI hZs : Group.IsSolvable Z := inferInstance
  have hindex : ¬ 2 ∣ Z.index := fun h =>
    hSodd (h.trans (Subgroup.index_map_dvd S' (QuotientGroup.mk'_surjective N')))
  haveI hq : Group.IsSolvable ((Γ ⧸ N') ⧸ Z) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.2 (by omega)
  haveI hΞ : Group.IsSolvable (Γ ⧸ N') :=
    Group.isSolvable_of_ker_le_range Z.subtype (QuotientGroup.mk' Z)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  haveI : Subsingleton (Γ ⧸ N') := by
    by_contra hns
    haveI : Nontrivial (Γ ⧸ N') := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isSolvable (Γ ⧸ N') hΞ
  rw [eq_top_iff]
  intro x _
  exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)

theorem uc22p20e_le_commutator_sylow {Q : Type} [Group Q] [Finite Q] (S : Sylow 2 Q)
    (Λ : Subgroup Q) (hS : (S : Subgroup Q) ≤ normalizer (Λ : Set Q)) (hperf : ⁅Λ, Λ⁆ = Λ) :
    Λ ≤ ⁅(S : Subgroup Q), Λ⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup Q) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, S.isPGroup', by
      rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have h2 : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup Q) (Λ ⊔ S) :=
    h1.of_le le_sup_right le_top
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup Q) ⊓ Λ) Λ :=
    h2.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hS)
  obtain ⟨hSΛ, hS₀2, hS₀odd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hSyl
  set S₀ : Subgroup Q := (S : Subgroup Q) ⊓ Λ with hS₀
  have hN₀Λ : ⁅S₀, Λ⁆ ≤ Λ := by
    calc ⁅S₀, Λ⁆ ≤ ⁅Λ, Λ⁆ := Subgroup.commutator_mono hSΛ le_rfl
      _ = Λ := hperf
  have hnorm : Λ ≤ normalizer ((⁅S₀, Λ⁆ : Subgroup Q) : Set Q) :=
    le_sup_right.trans (CFSG.Quasithin.A3.sup_le_normalizer_commutator S₀ Λ)
  haveI hN : ((⁅S₀, Λ⁆).subgroupOf Λ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀Λ).2 hnorm
  haveI : Group.IsPerfect ↥Λ := Subgroup.isPerfect_iff.2 hperf
  have htop : (⁅S₀, Λ⁆).subgroupOf Λ = ⊤ := by
    refine uc22p20e_eq_top_of_central_sylow ((⁅S₀, Λ⁆).subgroupOf Λ) (S₀.subgroupOf Λ)
      hS₀2.comap_subtype hS₀odd ?_
    intro s hs g
    have hs' : (s : Q) ∈ S₀ := hs
    show ((⁅s, g⁆ : ↥Λ) : Q) ∈ ⁅S₀, Λ⁆
    have : ((⁅s, g⁆ : ↥Λ) : Q) = ⁅(s : Q), (g : Q)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact Subgroup.commutator_mem_commutator hs' g.2
  have hΛle : Λ ≤ ⁅S₀, Λ⁆ := Subgroup.subgroupOf_eq_top.1 htop
  exact hΛle.trans (Subgroup.commutator_mono inf_le_left le_rfl)

theorem uc22p20e_le_commutator_sup_ker {Γ Q : Type} [Group Γ] [Group Q] [Finite Q] (f : Γ →* Q)
    (S : Sylow 2 Q) (Lg Pg : Subgroup Γ) (hP : Pg.map f = (S : Subgroup Q))
    (hPL : Pg ≤ normalizer (Lg : Set Γ)) (hperf : ⁅Lg, Lg⁆ = Lg) :
    Lg ≤ ⁅Pg, Lg⁆ ⊔ f.ker := by
  have hS : (S : Subgroup Q) ≤ normalizer ((Lg.map f : Subgroup Q) : Set Q) := by
    rw [← hP]
    exact (Subgroup.map_mono hPL).trans (Subgroup.le_normalizer_map f)
  have hperf' : ⁅Lg.map f, Lg.map f⁆ = Lg.map f := by
    rw [← Subgroup.map_commutator, hperf]
  have h := uc22p20e_le_commutator_sylow S (Lg.map f) hS hperf'
  rw [← hP, ← Subgroup.map_commutator] at h
  intro x hx
  obtain ⟨y, hy, hyx⟩ := h ⟨x, hx, rfl⟩
  have hx' : x = y * (y⁻¹ * x) := by group
  rw [hx']
  refine Subgroup.mul_mem_sup hy ?_
  rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]

theorem uc22p20e_le_commutator_sup {X W C Lg P : Subgroup G}
    (hWX : W ≤ X) (hXW : X ≤ normalizer (W : Set G)) (hCX : C ≤ X) (hX : X ≤ C ⊔ W)
    (hLX : Lg ≤ X) (hP : CFSG.ABGLocalTools.IsSylowOf 2 P C)
    (hPL : P ≤ normalizer (Lg : Set G)) (hperf : ⁅Lg, Lg⁆ = Lg) : Lg ≤ ⁅P, Lg⁆ ⊔ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hWn : (W.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).2 hXW
  let f : ↥X →* ↥X ⧸ W.subgroupOf X := QuotientGroup.mk' (W.subgroupOf X)
  let g : ↥C →* ↥X ⧸ W.subgroupOf X := f.comp (Subgroup.inclusion hCX)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf X) y
    have hx' : x ∈ ((C ⊔ W : Subgroup G) : Set G) := hX hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C W (hCX.trans hXW)] at hx'
    obtain ⟨c, hc, w, hw, rfl⟩ := hx'
    refine ⟨⟨c, hc⟩, ?_⟩
    show f ⟨c, hCX hc⟩ = f ⟨c * w, hx⟩
    refine (QuotientGroup.eq).2 ?_
    show ((c⁻¹ * (c * w) : G)) ∈ W
    simpa using hw
  obtain ⟨Pc, hPc⟩ := hP.exists_sylow_eq_subgroupOf
  let S : Sylow 2 (↥X ⧸ W.subgroupOf X) := Pc.mapSurjective hg
  have hPC : P ≤ C := hP.le
  have hSP : (P.subgroupOf X).map f = (S : Subgroup _) := by
    show _ = (Pc : Subgroup ↥C).map g
    rw [hPc]
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hPC hp⟩, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Subgroup.inclusion hCX p, hp, rfl⟩
  have hperf' : ⁅Lg.subgroupOf X, Lg.subgroupOf X⁆ = Lg.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLX, hperf]
  have hPL' : P.subgroupOf X ≤ normalizer ((Lg.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    (Subgroup.comap_mono hPL).trans (Subgroup.le_normalizer_comap X.subtype)
  have h := uc22p20e_le_commutator_sup_ker f S (Lg.subgroupOf X) (P.subgroupOf X) hSP hPL'
    hperf'
  rw [QuotientGroup.ker_mk'] at h
  have h2 := Subgroup.map_mono (f := X.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hLX, Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hLX, Subgroup.map_subgroupOf_eq_of_le (hPC.trans hCX),
    Subgroup.map_subgroupOf_eq_of_le hWX] at h2

theorem uc22p20e_eq_top_of_subnormal_map {Γ : Type} [Group Γ] [Group.IsPerfect Γ]
    (N : Subgroup Γ) [N.Normal] [Group.IsSolvable N] {K : Subgroup Γ} (hsub : K.IsSubnormal)
    (hmap : K.map (QuotientGroup.mk' N) = ⊤) : K = ⊤ := by
  induction hsub with
  | top => rfl
  | step H K' hle _ hN ih =>
    have hK' : K' = ⊤ := ih (top_le_iff.1 (hmap ▸ Subgroup.map_mono hle))
    subst hK'
    have hsup : H ⊔ N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : QuotientGroup.mk' N x ∈ H.map (QuotientGroup.mk' N) := hmap ▸ Subgroup.mem_top _
      obtain ⟨h, hh, hhx⟩ := hx
      have hx' : x = h * (h⁻¹ * x) := by group
      rw [hx']
      refine Subgroup.mul_mem_sup hh ?_
      have : QuotientGroup.mk' N (h⁻¹ * x) = 1 := by rw [map_mul, map_inv, hhx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have h1 := CFSG.Quasithin.perfectCore_le_of_sup_solvable (A := H) (B := N) (Y := ⊤) le_top
      hN hsup.symm inferInstance
    have h2 : CFSG.Quasithin.perfectCore (⊤ : Subgroup Γ) = ⊤ :=
      CFSG.Quasithin.perfectCore_eq_self_of_perfect
        (by rw [← _root_.commutator_def]; exact Group.IsPerfect.commutator_eq_top)
    exact top_le_iff.1 (h2 ▸ h1)

theorem uc22p20e_subnormal_perfect_eq_top_or_bot {Γ : Type} [Group Γ] [Finite Γ]
    [Group.IsPerfect Γ] (N : Subgroup Γ) [N.Normal] [Group.IsSolvable N]
    (hq : CFSG.IsQuasisimple (Γ ⧸ N)) {K : Subgroup Γ} (hsub : K.IsSubnormal)
    (hperf : ⁅K, K⁆ = K) : K = ⊤ ∨ K = ⊥ := by
  haveI hKp : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hperf
  have hmap : (K.map (QuotientGroup.mk' N)).IsSubnormal :=
    CFSG.Quasithin.A3.subnormal_top_iff.1 (CFSG.Quasithin.A3.subnormal_top_map
      (QuotientGroup.mk'_surjective N) (CFSG.Quasithin.A3.subnormal_top_iff.2 hsub))
  rcases CFSG.Quasithin.A3.eq_top_or_le_center_of_subnormal hq hmap with htop | hcen
  · exact Or.inl (uc22p20e_eq_top_of_subnormal_map N hsub htop)
  · right
    haveI : Group.IsPerfect (K.map (QuotientGroup.mk' N)) := Group.IsPerfect.map _
    haveI hcomm : IsMulCommutative (K.map (QuotientGroup.mk' N)) :=
      ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hcen a.2) b).symm⟩⟩
    have hbot : K.map (QuotientGroup.mk' N) = ⊥ := Subgroup.eq_bot_of_subsingleton _
    have hKN : K ≤ N := by
      have := (Subgroup.map_eq_bot_iff _).1 hbot
      rwa [QuotientGroup.ker_mk'] at this
    haveI : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKN)
        (Subgroup.inclusion_injective hKN)
    haveI : Subsingleton K := by
      by_contra hns
      haveI : Nontrivial K := not_subsingleton_iff_nontrivial.1 hns
      exact Group.IsPerfect.not_isSolvable K inferInstance
    exact Subgroup.eq_bot_of_subsingleton K

theorem uc22p20e_cComp_of_calC {L K₀ : Subgroup G} (h : K₀ ∈ calC L) :
    K₀ ∈ CFSG.Quasithin.cComp L := by
  obtain ⟨hsub, hperf, hq⟩ := h
  have hqs : CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hq
  have hne : K₀ ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := hqs.2.2
    exact hab (Subsingleton.elim _ _)
  refine ⟨hne, hperf, hsub, fun K hKlt hKne hKperf hKsub => ?_⟩
  have hK₀L : K₀ ≤ L := CFSG.Quasithin.A3.subnormal_le hsub
  have hKK₀ : IsSubnormal K K₀ :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hKsub hKlt.le hK₀L
  have hsubΓ : (K.subgroupOf K₀).IsSubnormal := by
    have := CFSG.Quasithin.A3.subnormal_comap K₀.subtype hKK₀
    rw [show K₀.comap K₀.subtype = ⊤ from Subgroup.subgroupOf_self K₀] at this
    exact CFSG.Quasithin.A3.subnormal_top_iff.1 this
  have hperfΓ : ⁅K.subgroupOf K₀, K.subgroupOf K₀⁆ = K.subgroupOf K₀ := by
    apply Subgroup.map_injective K₀.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKlt.le, hKperf]
  haveI : Group.IsPerfect ↥K₀ := Subgroup.isPerfect_iff.2 hperf
  haveI : (CFSG.pCore 2 ↥K₀).Normal := CFSG.pCore_normal
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥K₀) := by
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K₀) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    infer_instance
  rcases uc22p20e_subnormal_perfect_eq_top_or_bot (CFSG.pCore 2 ↥K₀) hqs hsubΓ hperfΓ with
    htop | hbot
  · exact absurd (Subgroup.subgroupOf_eq_top.1 htop) (not_le_of_gt hKlt)
  · apply hKne
    rw [← Subgroup.map_subgroupOf_eq_of_le hKlt.le, hbot, Subgroup.map_bot]

theorem uc22p20e_comm_le_solvRad {X C C' : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp X)
    (hC' : C' ∈ CFSG.Quasithin.cComp X) (hne : C ≠ C') :
    ⁅C, C'⁆ ≤ CFSG.Quasithin.solvRad X := by
  have hnormC' : CFSG.Quasithin.cCompSpan X ≤ normalizer (C' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.Quasithin.cComp_normal_span_of_le hC').1).1
      (CFSG.Quasithin.cComp_normal_span_of_le hC').2
  rcases CFSG.Quasithin.cComp_commutator_dichotomy_of_le hC
      (CFSG.Quasithin.le_of_mem_cComp hC') with ⟨h1, -⟩ | h2
  · exact h1
  · exfalso
    have hle : ⁅C, C'⁆ ≤ C' := by
      refine Subgroup.commutator_le.mpr fun c' hc' k' hk' => ?_
      have hc'N := hnormC' (CFSG.Quasithin.le_cCompSpan hC hc')
      have : c' * k' * c'⁻¹ ∈ C' := (Subgroup.mem_normalizer_iff.1 hc'N k').1 hk'
      exact C'.mul_mem this (C'.inv_mem hk')
    have hCle' : C ≤ C' := (CFSG.Quasithin.le_conjClosure C C').trans (h2 ▸ hle)
    rcases eq_or_lt_of_le hCle' with heq | hlt
    · exact hne heq
    · exact CFSG.Quasithin.not_subnormal_of_mem_cComp hC' hlt
        (CFSG.Quasithin.ne_bot_of_mem_cComp hC) (CFSG.Quasithin.perfect_of_mem_cComp hC)
        (CFSG.Quasithin.subnormal_of_mem_cComp hC)

theorem uc22p20e_cCompSpan_le (H : Subgroup G) : CFSG.Quasithin.cCompSpan H ≤ H :=
  sSup_le fun _ hC => CFSG.Quasithin.le_of_mem_cComp hC

theorem uc22p20e_cCompSpan_le_normalizer {H C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp H) :
    CFSG.Quasithin.cCompSpan H ≤ normalizer (C : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.Quasithin.cComp_normal_span_of_le hC).1).1 (CFSG.Quasithin.cComp_normal_span_of_le hC).2

@[expose] def uc22p20eCentMod (H A : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ H ∧ ∀ a ∈ A, ⁅a, x⁆ ∈ CFSG.Quasithin.solvRad H}
  one_mem' := ⟨H.one_mem, fun a _ => by simpa using (CFSG.Quasithin.solvRad H).one_mem⟩
  mul_mem' := by
    rintro g h ⟨hgH, hg⟩ ⟨hhH, hh⟩
    refine ⟨H.mul_mem hgH hhH, fun a ha => ?_⟩
    have e : ⁅a, g * h⁆ = ⁅a, g⁆ * (g * ⁅a, h⁆ * g⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (CFSG.Quasithin.solvRad H).mul_mem (hg a ha)
      (CFSG.Quasithin.conj_mem_solvRad (Subgroup.le_normalizer hgH) (hh a ha))
  inv_mem' := by
    rintro g ⟨hgH, hg⟩
    refine ⟨H.inv_mem hgH, fun a ha => ?_⟩
    have e : ⁅a, g⁻¹⁆ = g⁻¹ * ⁅a, g⁆⁻¹ * g := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := CFSG.Quasithin.conj_mem_solvRad (Subgroup.le_normalizer (H.inv_mem hgH))
      ((CFSG.Quasithin.solvRad H).inv_mem (hg a ha))
    simpa [mul_assoc] using this

@[expose] def uc22p20eW (H C : Subgroup G) : Subgroup G :=
  uc22p20eCentMod H C ⊓ CFSG.Quasithin.cCompSpan H

theorem uc22p20e_le_normalizer_of_conj {A B : Subgroup G} (h : ∀ y ∈ A, ∀ x ∈ B, y * x * y⁻¹ ∈ B) :
    A ≤ normalizer (B : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h y hy x, fun hx => ?_⟩
  have := h y⁻¹ (A.inv_mem hy) _ hx
  simpa [mul_assoc] using this

theorem uc22p20e_W_normalized {H C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp H) :
    CFSG.Quasithin.cCompSpan H ≤ normalizer (uc22p20eW H C : Set G) := by
  refine uc22p20e_le_normalizer_of_conj fun y hy x hx => ?_
  obtain ⟨⟨hxH, hxc⟩, hxX⟩ := hx
  have hyH : y ∈ H := uc22p20e_cCompSpan_le H hy
  refine ⟨⟨H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH), fun c hc => ?_⟩,
    (CFSG.Quasithin.cCompSpan H).mul_mem ((CFSG.Quasithin.cCompSpan H).mul_mem hy hxX)
      ((CFSG.Quasithin.cCompSpan H).inv_mem hy)⟩
  have hc' : y⁻¹ * c * y⁻¹⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.1 (uc22p20e_cCompSpan_le_normalizer hC
      ((CFSG.Quasithin.cCompSpan H).inv_mem hy)) c).1 hc
  have h1 := hxc _ hc'
  have e : ⁅c, y * x * y⁻¹⁆ = y * ⁅y⁻¹ * c * y⁻¹⁻¹, x⁆ * y⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have := CFSG.Quasithin.conj_mem_solvRad (Subgroup.le_normalizer hyH) h1
  simpa [mul_assoc] using this

theorem uc22p20e_cCompSpan_le_sup {H C : Subgroup G} (hC : C ∈ CFSG.Quasithin.cComp H) :
    CFSG.Quasithin.cCompSpan H ≤ C ⊔ uc22p20eW H C := by
  refine sSup_le fun C' hC' => ?_
  by_cases hCC' : C = C'
  · exact hCC' ▸ le_sup_left
  · refine le_sup_of_le_right fun x hx => ?_
    refine ⟨⟨(CFSG.Quasithin.le_of_mem_cComp hC') hx, fun c hc => ?_⟩,
      CFSG.Quasithin.le_cCompSpan hC' hx⟩
    exact uc22p20e_comm_le_solvRad hC hC' hCC' (Subgroup.commutator_mem_commutator hc hx)

theorem uc22p20e_exists_not_le_W {H K₀ : Subgroup G} (hK₀X : K₀ ≤ CFSG.Quasithin.cCompSpan H)
    (hperf : ⁅K₀, K₀⁆ = K₀) (hns : ¬ Group.IsSolvable ↥K₀) :
    ∃ C ∈ CFSG.Quasithin.cComp H, ¬ K₀ ≤ uc22p20eW H C := by
  by_contra hcon
  push Not at hcon
  have hX : CFSG.Quasithin.cCompSpan H ≤ uc22p20eCentMod H K₀ := by
    refine sSup_le fun C hC x hx => ?_
    refine ⟨(CFSG.Quasithin.le_of_mem_cComp hC) hx, fun k hk => ?_⟩
    have h1 := (hcon C hC hk).1.2 x hx
    have : ⁅k, x⁆ = ⁅x, k⁆⁻¹ := (commutatorElement_inv x k).symm
    rw [this]
    exact (CFSG.Quasithin.solvRad H).inv_mem h1
  have hKR : K₀ ≤ CFSG.Quasithin.solvRad H := by
    rw [← hperf]
    refine Subgroup.commutator_le.mpr fun k hk k' hk' => ?_
    exact (hX (hK₀X hk')).2 k hk
  haveI : Group.IsSolvable ↥(CFSG.Quasithin.solvRad H) := CFSG.Quasithin.solvRad_isSolvable H
  exact hns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKR)
    (Subgroup.inclusion_injective hKR))

theorem uc22p20e_exists_cComp_ge (D : Data G) {H L K₀ : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hLX : L ≤ CFSG.Quasithin.cCompSpan H) (hLT : D.T ≤ normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hK₀ : K₀ ∈ CFSG.Quasithin.cComp L) :
    ∃ C ∈ CFSG.Quasithin.cComp H, K₀ ≤ C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀L : K₀ ≤ L := CFSG.Quasithin.le_of_mem_cComp hK₀
  have hK₀perf : ⁅K₀, K₀⁆ = K₀ := CFSG.Quasithin.perfect_of_mem_cComp hK₀
  obtain ⟨C, hC, hKW⟩ := uc22p20e_exists_not_le_W (hK₀L.trans hLX) hK₀perf
    (CFSG.Quasithin.not_isSolvable_of_mem_cComp hK₀)
  refine ⟨C, hC, ?_⟩
  have hCX : C ≤ CFSG.Quasithin.cCompSpan H := CFSG.Quasithin.le_cCompSpan hC
  have hXC : CFSG.Quasithin.cCompSpan H ≤ normalizer (C : Set G) :=
    uc22p20e_cCompSpan_le_normalizer hC
  have hXH : CFSG.Quasithin.cCompSpan H ≤ H := uc22p20e_cCompSpan_le H
  have hHX : H ≤ normalizer (CFSG.Quasithin.cCompSpan H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).1 (uc22p20b_normal_cCompSpan H)
  have hWX : uc22p20eW H C ≤ CFSG.Quasithin.cCompSpan H := inf_le_right
  have hXW : CFSG.Quasithin.cCompSpan H ≤ normalizer (uc22p20eW H C : Set G) :=
    uc22p20e_W_normalized hC
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hH.1 le_top
  have hTX : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ CFSG.Quasithin.cCompSpan H)
      (CFSG.Quasithin.cCompSpan H) := hTH.inf_of_le_normalizer hXH hHX
  have hTC : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ C) C := by
    have := hTX.inf_of_le_normalizer hCX hXC
    rwa [inf_assoc, inf_eq_right.2 hCX] at this
  have hPL : D.T ⊓ C ≤ normalizer (L : Set G) := inf_le_left.trans hLT
  have hLW := uc22p20e_le_commutator_sup hWX hXW hCX (uc22p20e_cCompSpan_le_sup hC) hLX hTC hPL
    hperf
  have hcomm : ⁅D.T ⊓ C, L⁆ ≤ L ⊓ C := by
    refine Subgroup.commutator_le.mpr fun p hp l hl => ?_
    refine ⟨?_, ?_⟩
    · have : p * l * p⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hPL hp) l).1 hl
      exact L.mul_mem this (L.inv_mem hl)
    · have hlC := hXC (hLX hl)
      have : l * p⁻¹ * l⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 hlC p⁻¹).1 (C.inv_mem hp.2)
      have e : ⁅p, l⁆ = p * (l * p⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact C.mul_mem hp.2 this
  have hLDW : L ≤ (L ⊓ C) ⊔ uc22p20eW H C := hLW.trans (sup_le_sup_right hcomm _)
  have hLD : L ≤ normalizer ((L ⊓ C : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hXC (hLX hl)⟩
  have hLE : L ≤ normalizer ((L ⊓ uc22p20eW H C : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hXW (hLX hl)⟩
  have hdich : ∀ N : Subgroup G, N ≤ L → L ≤ normalizer (N : Set G) →
      K₀ ≤ N ∨ ⁅K₀, N⁆ ≤ CFSG.Quasithin.solvRad L := by
    intro N hNL hLN
    rcases CFSG.Quasithin.cComp_commutator_dichotomy_of_le hK₀ hNL with ⟨h1, -⟩ | h2
    · exact Or.inr h1
    · left
      have hle : ⁅K₀, N⁆ ≤ N := Subgroup.commutator_le.mpr fun k hk n hn => by
        have : k * n * k⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hLN (hK₀L hk)) n).1 hn
        exact N.mul_mem this (N.inv_mem hn)
      exact (CFSG.Quasithin.le_conjClosure K₀ N).trans (h2 ▸ hle)
  by_contra hKC
  have h1 := (hdich (L ⊓ C) inf_le_left hLD).resolve_left fun h => hKC (h.trans inf_le_right)
  have h2 := (hdich (L ⊓ uc22p20eW H C) inf_le_left hLE).resolve_left fun h =>
    hKW (h.trans inf_le_right)
  have hKR : K₀ ≤ CFSG.Quasithin.solvRad L := by
    rw [← hK₀perf]
    refine Subgroup.commutator_le.mpr fun k hk k' hk' => ?_
    have hk'L : k' ∈ L := hK₀L hk'
    have hmem : k' ∈ ((L ⊓ C ⊔ uc22p20eW H C : Subgroup G) : Set G) := hLDW hk'L
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (L ⊓ C) (uc22p20eW H C)
      ((inf_le_right.trans hCX).trans hXW)] at hmem
    obtain ⟨d, hd, w, hw, rfl⟩ := hmem
    have hwL : w ∈ L := by
      have := L.mul_mem (L.inv_mem hd.1) hk'L
      simpa using this
    have e : ⁅k, d * w⁆ = ⁅k, d⁆ * (d * ⁅k, w⁆ * d⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (CFSG.Quasithin.solvRad L).mul_mem
      (h1 (Subgroup.commutator_mem_commutator hk hd))
      (CFSG.Quasithin.conj_mem_solvRad (Subgroup.le_normalizer hd.1)
        (h2 (Subgroup.commutator_mem_commutator hk ⟨hwL, hw⟩)))
  haveI : Group.IsSolvable ↥(CFSG.Quasithin.solvRad L) := CFSG.Quasithin.solvRad_isSolvable L
  exact CFSG.Quasithin.not_isSolvable_of_mem_cComp hK₀
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKR)
      (Subgroup.inclusion_injective hKR))

theorem uc22p20e_le_cCompSpan (D : Data G) (h1930 : H1930 D) (h20_3 : S20_3 D) {H L : Subgroup G}
    (hH : H ∈ hSet D.T D.M) (hLH : L ≤ H) (hperf : ⁅L, L⁆ = L) :
    L ≤ CFSG.Quasithin.cCompSpan H := by
  have h3 := h20_3 h1930 H hH
  have hL1 : L ≤ Hinf H := by
    have : Hinf H = CFSG.Quasithin.perfectCore H := by
      unfold Hinf CFSG.inSubgroup
      rw [CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
    rw [this]
    exact CFSG.Quasithin.le_perfectCore_of_perfect hLH hperf
  rw [(CFSG.Quasithin.cComp_part_five_of_le H).2]
  exact CFSG.Quasithin.le_perfectCore_of_perfect (hL1.trans h3) hperf

theorem uc22p20e_orb_mono {T K₀ C : Subgroup G} (h : K₀ ≤ C) :
    uc22p20bOrb T K₀ ≤ uc22p20bOrb T C :=
  iSup_mono fun _ => Subgroup.map_mono h

theorem uc22p20e_orb_le_of_invariant {T C K : Subgroup G} (hT : T ≤ normalizer (K : Set G))
    (hCK : C ≤ K) : uc22p20bOrb T C ≤ K := by
  refine iSup_le fun t x hx => ?_
  obtain ⟨y, hy, rfl⟩ := uc22p20b_mem_cj.1 hx
  exact (Subgroup.mem_normalizer_iff.1 (hT t.2) y).1 (hCK hy)

theorem uc22p20e_exists_orb (D : Data G) (h1930 : H1930 D) (h20_3 : S20_3 D) {H L : Subgroup G}
    (hH : H ∈ hSet D.T D.M) (hL : L ∈ calL D.T D.M) (hLH : L ≤ H) :
    ∃ C ∈ CFSG.Quasithin.cComp H, ¬ C ≤ D.M ∧ L ≤ uc22p20bOrb D.T C := by
  obtain ⟨hLT, hperf, hLTH, K₀, hK₀, hLK⟩ := hL
  have hK₀c : K₀ ∈ CFSG.Quasithin.cComp L := uc22p20e_cComp_of_calC hK₀
  have hLX := uc22p20e_le_cCompSpan D h1930 h20_3 hH hLH hperf
  obtain ⟨C, hC, hKC⟩ := uc22p20e_exists_cComp_ge D hH hLX hLT hperf hK₀c
  have hLeq : L = uc22p20bOrb D.T K₀ := hLK
  have hLC : L ≤ uc22p20bOrb D.T C := hLeq ▸ uc22p20e_orb_mono hKC
  refine ⟨C, hC, fun hCM => ?_, hLC⟩
  exact hLTH.2.1 (sup_le (hLC.trans (uc22p20b_orb_le D.sylowM.le hCM)) D.sylowM.le)

theorem s20_5_of (D : Data G) (h20_2 : S20_2 D) (h20_3 : S20_3 D) (hB : ListBNonabelian)
    (hS : ListBNotSmall) : S20_5 D := by
  intro h1930 L hL H hH hLH
  obtain ⟨C, hC, hCM, hLC⟩ := uc22p20e_exists_orb D h1930 h20_3 hH hL hLH
  obtain ⟨K, hK, hCK⟩ := uc22p20b_compInCalL D h1930 h20_2 hB hS H hH C hC hCM
  exact ⟨K, hK, hLC.trans (uc22p20e_orb_le_of_invariant hK.1.1 hCK)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
