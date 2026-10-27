module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.RankThree.GF2n.ConjTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.GF2n.Smith81.Bridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

section Models

theorem isSLModel_of_mulEquiv {n q : ℕ} (X Y : Type) [Group X] [Group Y] (f : X ≃* Y)
    (h : IsSLModel n q X) : IsSLModel n q Y := by
  obtain ⟨K, hK, hKf, hc, ⟨ψ⟩⟩ := h
  exact ⟨K, hK, hKf, hc, ⟨f.symm.trans ψ⟩⟩

theorem isPSLModel_of_mulEquiv {n q : ℕ} (X Y : Type) [Group X] [Group Y] (f : X ≃* Y)
    (h : IsPSLModel n q X) : IsPSLModel n q Y := by
  obtain ⟨K, hK, hKf, hc, ⟨ψ⟩⟩ := h
  exact ⟨K, hK, hKf, hc, ⟨f.symm.trans ψ⟩⟩

theorem isPSUModel_of_mulEquiv {n q : ℕ} (X Y : Type) [Group X] [Group Y] (f : X ≃* Y)
    (h : IsPSUModel n q X) : IsPSUModel n q Y := by
  obtain ⟨K, hK, hKf, hc, ⟨ψ⟩⟩ := h
  exact ⟨K, hK, hKf, hc, ⟨f.symm.trans ψ⟩⟩

theorem isOmegaPlus_of_mulEquiv {m q : ℕ} (X Y : Type) [Group X] [Group Y] (f : X ≃* Y)
    (h : IsOmegaPlus m q X) : IsOmegaPlus m q Y := by
  obtain ⟨K, hK, hKf, hc, ⟨ψ⟩⟩ := h
  exact ⟨K, hK, hKf, hc, ⟨f.symm.trans ψ⟩⟩

theorem isOmegaMinus_of_mulEquiv {m q : ℕ} (X Y : Type) [Group X] [Group Y] (f : X ≃* Y)
    (h : IsOmegaMinus m q X) : IsOmegaMinus m q Y := by
  obtain ⟨K, hK, hKf, hc, b, c, hbc, ⟨ψ⟩⟩ := h
  exact ⟨K, hK, hKf, hc, b, c, hbc, ⟨f.symm.trans ψ⟩⟩

theorem isProdOf_of_mulEquiv {P₁ P₂ : ∀ (X : Type) [Group X], Prop} (X Y : Type) [Group X]
    [Group Y] (f : X ≃* Y) (h : IsProdOf P₁ P₂ X) : IsProdOf P₁ P₂ Y := by
  obtain ⟨A, B, hA, hB, h1, h2, ⟨ψ⟩⟩ := h
  exact ⟨A, B, hA, hB, h1, h2, ⟨f.symm.trans ψ⟩⟩

end Models

section Transport

variable {G G' : Type} [Group G] [Group G'] (e : G ≃* G')

private def eqv (S : Subgroup G) : ↥S ≃* ↥(S.map e.toMonoidHom) :=
  MulEquiv.subgroupMap e S

private theorem mem_map_apply {S : Subgroup G} {x : G} :
    e x ∈ S.map e.toMonoidHom ↔ x ∈ S :=
  Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective

private theorem map_symm_map (S : Subgroup G) :
    (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext e.symm_apply_apply
  rw [this, Subgroup.map_id]

private theorem map_map_symm (S : Subgroup G') :
    (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
  simpa using map_symm_map e.symm S

private theorem card_map (S : Subgroup G) : Nat.card ↥(S.map e.toMonoidHom) = Nat.card ↥S :=
  Subgroup.card_map_of_injective e.injective

private theorem map_inf (S T : Subgroup G) :
    (S ⊓ T).map e.toMonoidHom = S.map e.toMonoidHom ⊓ T.map e.toMonoidHom :=
  Subgroup.map_inf_eq _ _ _ e.injective

private theorem conjSubgroup_map (g : G) (S : Subgroup G) :
    conjSubgroup (e g) (S.map e.toMonoidHom) = (conjSubgroup g S).map e.toMonoidHom :=
  (map_conjSubgroup e.toMonoidHom g S).symm

private theorem centralizer_map (s : Set G) :
    Subgroup.centralizer (e '' s) = (Subgroup.centralizer s).map e.toMonoidHom := by
  ext x'
  obtain ⟨x, rfl⟩ := e.surjective x'
  rw [mem_map_apply, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    apply e.injective
    simpa only [map_mul] using h (e s) ⟨s, hs, rfl⟩
  · rintro h _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, h s hs]

private theorem centralizer_map_subgroup (S : Subgroup G) :
    Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (S : Set G)).map e.toMonoidHom := by
  rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, centralizer_map]

private theorem normalizer_map (S : Subgroup G) :
    Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.normalizer (S : Set G)).map e.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq S e).symm

private theorem inSubgroup_map (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (A B : Type) [Group A] [Group B] (f : A ≃* B), (F A).map f.toMonoidHom = F B)
    (H : Subgroup G) :
    inSubgroup F (H.map e.toMonoidHom) = (inSubgroup F H).map e.toMonoidHom := by
  unfold inSubgroup
  rw [← hF _ _ (eqv e H), Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem inSubgroup_pCore_map (p : ℕ) (H : Subgroup G) :
    inSubgroup (pCore p) (H.map e.toMonoidHom) = (inSubgroup (pCore p) H).map e.toMonoidHom :=
  inSubgroup_map e (pCore p) (fun _ _ _ _ f => pCore_map_iso p f) H

private theorem inSubgroup_generalizedFitting_map (H : Subgroup G) :
    inSubgroup generalizedFitting (H.map e.toMonoidHom) =
      (inSubgroup generalizedFitting H).map e.toMonoidHom :=
  inSubgroup_map e generalizedFitting
    (fun _ _ _ _ f => WholeGroup.generalizedFitting_map_mulEquiv f) H

theorem cen_map (Q : Subgroup G) : cen (Q.map e.toMonoidHom) = (cen Q).map e.toMonoidHom := by
  rw [cen_eq, cen_eq, map_inf, centralizer_map_subgroup]

theorem QB_map (B : Subgroup G) : QB (B.map e.toMonoidHom) = (QB B).map e.toMonoidHom := by
  unfold QB
  rw [normalizer_map, inSubgroup_generalizedFitting_map]

theorem LB_map (M Q B : Subgroup G) :
    LB (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (B.map e.toMonoidHom) =
      (LB M Q B).map e.toMonoidHom := by
  unfold LB
  rw [Subgroup.map_sup, map_inf, QB_map]

theorem H0_map (M Z : Subgroup G) :
    H0 (M.map e.toMonoidHom) (Z.map e.toMonoidHom) = (H0 M Z).map e.toMonoidHom := by
  unfold H0
  rw [map_inf, centralizer_map_subgroup]

theorem Lgen_map (M L : Subgroup G) :
    Lgen (M.map e.toMonoidHom) (L.map e.toMonoidHom) = (Lgen M L).map e.toMonoidHom := by
  unfold Lgen
  apply le_antisymm
  · refine iSup₂_le fun m' hm' => ?_
    obtain ⟨m, hm, rfl⟩ := hm'
    rw [MulEquiv.coe_toMonoidHom, conjSubgroup_map]
    exact Subgroup.map_mono (le_iSup₂_of_le m hm le_rfl)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun m hm => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← conjSubgroup_map]
    exact le_iSup₂_of_le (e m) (Subgroup.mem_map_of_mem _ hm) le_rfl

theorem Rt_map (M L : Subgroup G) (t : G) :
    Rt (M.map e.toMonoidHom) (L.map e.toMonoidHom) (e t) = (Rt M L t).map e.toMonoidHom := by
  unfold Rt
  apply le_antisymm
  · refine iSup₂_le fun m' hm' => iSup_le fun ht => ?_
    obtain ⟨m, hm, rfl⟩ := hm'
    rw [MulEquiv.coe_toMonoidHom, conjSubgroup_map] at ht ⊢
    exact Subgroup.map_mono
      (le_iSup₂_of_le m hm (le_iSup_of_le ((mem_map_apply e).mp ht) le_rfl))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun m hm => iSup_le fun ht => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← conjSubgroup_map]
    refine le_iSup₂_of_le (e m) (Subgroup.mem_map_of_mem _ hm) (le_iSup_of_le ?_ le_rfl)
    rw [conjSubgroup_map]
    exact (mem_map_apply e).mpr ht

theorem Nt_map (M L : Subgroup G) (t : G) :
    Nt (M.map e.toMonoidHom) (L.map e.toMonoidHom) (e t) = (Nt M L t).map e.toMonoidHom := by
  unfold Nt
  rw [Rt_map, inSubgroup_pCore_map]

private theorem isPLocal_two_map {H : Subgroup G} (hH : IsPLocal 2 H) :
    IsPLocal 2 (H.map e.toMonoidHom) := by
  obtain ⟨P, hP, hP2, hHP⟩ := hH
  refine ⟨P.map e.toMonoidHom,
    fun h => hP ((Subgroup.map_eq_bot_iff_of_injective P e.injective).mp h), hP2.map _, ?_⟩
  rw [hHP, Subgroup.map_equiv_normalizer_eq]

private theorem isMaximalTwoLocal_map {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    IsMaximalTwoLocal (M.map e.toMonoidHom) := by
  refine ⟨isPLocal_two_map e hM.1, fun H hlt hH => ?_⟩
  have hH' := isPLocal_two_map e.symm hH
  have hlt' : M < H.map e.symm.toMonoidHom := by
    rw [← map_map_symm e H] at hlt
    exact (MulEquiv.mapSubgroup e).lt_iff_lt.mp hlt
  exact hM.2 _ hlt' hH'

private theorem isTI_map {Z : Subgroup G} (h : IsTI Z) : IsTI (Z.map e.toMonoidHom) := by
  intro g'
  obtain ⟨g, rfl⟩ := e.surjective g'
  rw [conjSubgroup_map, ← map_inf]
  rcases h g with h1 | h1
  · left
    rw [h1, Subgroup.map_bot]
  · right
    rw [h1]

private theorem iSup_conjSubgroup_le_map (Q Z : Subgroup G) :
    (⨆ (g : G') (_ : conjSubgroup g (Z.map e.toMonoidHom) ≤ Q.map e.toMonoidHom),
      conjSubgroup g (Z.map e.toMonoidHom)) =
      (⨆ (g : G) (_ : conjSubgroup g Z ≤ Q), conjSubgroup g Z).map e.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun g' hg' => ?_
    obtain ⟨g, rfl⟩ := e.surjective g'
    rw [conjSubgroup_map] at hg' ⊢
    exact Subgroup.map_mono (le_iSup₂_of_le g
      ((Subgroup.map_le_map_iff_of_injective e.injective).mp hg') le_rfl)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g hg => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← conjSubgroup_map]
    refine le_iSup₂_of_le (e g) ?_ le_rfl
    rw [conjSubgroup_map]
    exact Subgroup.map_mono hg

private theorem map_eqv_map_subtype (D : Subgroup G) (K : Subgroup D) :
    (K.map (eqv e D).toMonoidHom).map (D.map e.toMonoidHom).subtype =
      (K.map D.subtype).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem center_map_subtype (D : Subgroup G) :
    (Subgroup.center ↥(D.map e.toMonoidHom)).map (D.map e.toMonoidHom).subtype =
      ((Subgroup.center ↥D).map D.subtype).map e.toMonoidHom := by
  rw [← map_eqv_map_subtype]
  congr 1
  exact (Subgroup.map_center_eq (eqv e D)).symm

theorem _root_.CFSG.RankThree.GF2n.Tim79.IsL3Type.map {n : ℕ} {D : Subgroup G}
    (h : Tim79.IsL3Type n D) : Tim79.IsL3Type n (D.map e.toMonoidHom) := by
  obtain ⟨φ⟩ := h
  exact ⟨(eqv e D).symm.trans φ⟩

theorem _root_.CFSG.RankThree.GF2n.Tim79.IsCentralProductOfL3.map {Q Z : Subgroup G}
    {n k : ℕ} (h : Tim79.IsCentralProductOfL3 Q Z n k) :
    Tim79.IsCentralProductOfL3 (Q.map e.toMonoidHom) (Z.map e.toMonoidHom) n k := by
  obtain ⟨hk, D, hDQ, hDL, hDZ, hDc, hDsup⟩ := h
  refine ⟨hk, fun i => (D i).map e.toMonoidHom, fun i => Subgroup.map_mono (hDQ i),
    fun i => (hDL i).map e, fun i => by rw [center_map_subtype, hDZ i], ?_, ?_⟩
  · intro i j hij x hx y hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hDc i j hij x hx y hy]
  · rw [← hDsup, Subgroup.map_iSup]

theorem _root_.CFSG.RankThree.GF2n.Stroth80.StrothHyp.map {M Q Z : Subgroup G}
    (h : StrothHyp M Q Z) :
    StrothHyp (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom) where
  o2 := by rw [← pCore_map_iso 2 e, h.o2, Subgroup.map_bot]
  maxLocal := isMaximalTwoLocal_map e h.maxLocal
  fitting := by
    rw [← WholeGroup.generalizedFitting_map_mulEquiv (eqv e M), ← pCore_map_iso 2 (eqv e M),
      h.fitting]
  hQ := by rw [inSubgroup_pCore_map, ← h.hQ]
  hZ := by rw [cen_map, ← h.hZ]
  cp := by
    obtain ⟨n, k, hn, hcp⟩ := h.cp
    exact ⟨n, k, by rw [card_map]; exact hn, hcp.map e⟩
  q4 := by rw [card_map]; exact h.q4
  maxAb := maximal_abelianNormal_map_mulEquiv e h.maxAb
  ti := isTI_map e h.ti
  notWC := by
    intro hwc
    apply h.notWC
    have := weaklyClosedIn_map_mulEquiv e.symm hwc
    rwa [map_symm_map, map_symm_map] at this
  gen := by rw [iSup_conjSubgroup_le_map, ← h.gen]

theorem _root_.CFSG.RankThree.GF2n.Stroth80.Ctx.map {M Q Z B : Subgroup G} (h : Ctx M Q Z B) :
    Ctx (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) where
  hyp := h.hyp.map e
  conj := by
    obtain ⟨g, hg⟩ := h.conj
    exact ⟨e g, by rw [hg, conjSubgroup_map]⟩
  le := Subgroup.map_mono h.le
  ne := fun h' => h.ne (Subgroup.map_injective e.injective h')

private theorem subgroupOf_map (S N : Subgroup G) :
    (N.subgroupOf S).map (eqv e S).toMonoidHom =
      (N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom) := by
  ext ⟨x', hx'⟩
  obtain ⟨x, hx, rfl⟩ := hx'
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, congrArg Subtype.val hyx⟩
  · rintro ⟨y, hy, hyx⟩
    obtain rfl : y = x := e.injective hyx
    exact ⟨⟨y, hx⟩, hy, rfl⟩

private theorem normal_map {S N : Subgroup G} (hN : (N.subgroupOf S).Normal) :
    ((N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)).Normal := by
  rw [← subgroupOf_map]
  exact hN.map _ (eqv e S).surjective

private def quotEqv (S N : Subgroup G) [(N.subgroupOf S).Normal]
    [((N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)).Normal] :
    ↥S ⧸ N.subgroupOf S ≃*
      ↥(S.map e.toMonoidHom) ⧸ (N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom) :=
  QuotientGroup.congr _ _ (eqv e S) (subgroupOf_map e S N)

private theorem quotEqv_mk (S N : Subgroup G) [(N.subgroupOf S).Normal]
    [((N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)).Normal] (x : S) :
    quotEqv e S N (QuotientGroup.mk x) = QuotientGroup.mk (eqv e S x) :=
  QuotientGroup.congr_mk _ _ _ _ x

private theorem quotEqv_symm_mk (S N : Subgroup G) [(N.subgroupOf S).Normal]
    [((N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)).Normal]
    (x : ↥(S.map e.toMonoidHom)) :
    (quotEqv e S N).symm (QuotientGroup.mk x) = QuotientGroup.mk ((eqv e S).symm x) := by
  rw [MulEquiv.symm_apply_eq, quotEqv_mk, MulEquiv.apply_symm_apply]

private theorem bar_map (H N S : Subgroup G) [(N.subgroupOf H).Normal]
    [((N.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)).Normal] :
    bar (H.map e.toMonoidHom) (N.map e.toMonoidHom) (S.map e.toMonoidHom) =
      (bar H N S).map (quotEqv e H N).toMonoidHom := by
  unfold bar
  rw [← subgroupOf_map e H S, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem _root_.CFSG.RankThree.GF2n.Stroth80.QuotSat.map {S N : Subgroup G}
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → P X → P Y) (h : QuotSat S N P) :
    QuotSat (S.map e.toMonoidHom) (N.map e.toMonoidHom) P := by
  obtain ⟨hN, hPS⟩ := h
  haveI := hN
  haveI hN' := normal_map e hN
  exact ⟨hN', hP _ _ (quotEqv e S N) hPS⟩

private theorem comm_mem_map_iff {Q S : Subgroup G} {h : G} :
    (∀ x' ∈ S.map e.toMonoidHom, ⁅e h, x'⁆ ∈ Q.map e.toMonoidHom) ↔ ∀ x ∈ S, ⁅h, x⁆ ∈ Q := by
  constructor
  · intro H x hx
    have := H (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    rwa [← map_commutatorElement, mem_map_apply] at this
  · rintro H _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_commutatorElement, mem_map_apply]
    exact H x hx

theorem _root_.CFSG.RankThree.GF2n.Stroth80.SectionAct.map {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {S V Z : Subgroup G} {φ : S →* GL ι K}
    {act : GL ι K → Matrix ι ι K} (h : SectionAct K S V Z φ act)
    {φ' : ↥(S.map e.toMonoidHom) →* GL ι K}
    (hφ : ∀ s : S, φ' ⟨e s, Subgroup.mem_map_of_mem e.toMonoidHom s.2⟩ = φ s) :
    SectionAct K (S.map e.toMonoidHom) (V.map e.toMonoidHom) (Z.map e.toMonoidHom) φ' act := by
  obtain ⟨hSV, hN, ψ, hψ⟩ := h
  haveI := hN
  haveI hN' := normal_map e hN
  refine ⟨?_, hN', (quotEqv e V Z).symm.trans ψ, ?_⟩
  · rw [normalizer_map]
    exact Subgroup.map_mono hSV
  · intro s' v' w' hw
    obtain ⟨s, rfl⟩ := (eqv e S).surjective s'
    obtain ⟨v, rfl⟩ := (eqv e V).surjective v'
    obtain ⟨w, rfl⟩ := (eqv e V).surjective w'
    have hw' : (w : G) = (s : G) * v * (s : G)⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      exact hw
    simp only [MulEquiv.trans_apply, quotEqv_symm_mk, MulEquiv.symm_apply_apply]
    rw [show φ' (eqv e S s) = φ s from hφ s]
    exact hψ s v w hw'

theorem _root_.CFSG.RankThree.GF2n.Stroth80.CentDvd.map {M Q Z S : Subgroup G}
    (h : CentDvd M Q Z S) :
    CentDvd (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (S.map e.toMonoidHom) := by
  obtain ⟨C, hQC, hCH, hC, hdvd⟩ := h
  refine ⟨C.map e.toMonoidHom, Subgroup.map_mono hQC, ?_, fun h' => ?_, ?_⟩
  · rw [H0_map]
    exact Subgroup.map_mono hCH
  · obtain ⟨h, rfl⟩ := e.surjective h'
    rw [mem_map_apply, H0_map, mem_map_apply, comm_mem_map_iff]
    exact hC h
  · rw [card_map, card_map, card_map]
    exact hdvd

theorem CentDvdN.map {c : ℕ} {M Q Z S : Subgroup G} (h : CentDvdN c M Q Z S) :
    CentDvdN c (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (S.map e.toMonoidHom) := by
  obtain ⟨C, hQC, hCH, hC, hdvd⟩ := h
  refine ⟨C.map e.toMonoidHom, Subgroup.map_mono hQC, ?_, fun h' => ?_, ?_⟩
  · rw [H0_map]
    exact Subgroup.map_mono hCH
  · obtain ⟨h, rfl⟩ := e.surjective h'
    rw [mem_map_apply, H0_map, mem_map_apply, comm_mem_map_iff]
    exact hC h
  · rw [card_map, card_map, card_map]
    exact hdvd

theorem _root_.CFSG.RankThree.GF2n.Stroth80.FrobClause.map {M Z : Subgroup G}
    (h : FrobClause M Z) : FrobClause (M.map e.toMonoidHom) (Z.map e.toMonoidHom) := by
  obtain ⟨⟨K, hK, hKf, hc, eZ, hm⟩, hdvd⟩ := h
  refine ⟨⟨K, hK, hKf, by rw [card_map]; exact hc, (eqv e Z).symm.trans eZ, ?_⟩, ?_⟩
  · rintro _ ⟨m, hmM, rfl⟩
    obtain ⟨a, σ, haσ⟩ := hm m hmM
    refine ⟨a, σ, fun z' w' hw => ?_⟩
    obtain ⟨z, rfl⟩ := (eqv e Z).surjective z'
    obtain ⟨w, rfl⟩ := (eqv e Z).surjective w'
    have hw' : (w : G) = m * z * m⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      exact hw
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using haσ z w hw'
  · rw [H0_map, Subgroup.relIndex_map_map_of_injective _ _ e.injective, card_map]
    exact hdvd

theorem _root_.CFSG.RankThree.GF2n.Stroth80.IsTIMod.map {M Q L : Subgroup G}
    (h : IsTIMod M Q L) :
    IsTIMod (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, conjSubgroup_map, ← map_inf]
  rcases h m hm with h1 | h1
  · left
    rw [h1]
  · right
    rw [h1]

theorem isTIMod_map_iff {M Q L : Subgroup G} :
    IsTIMod (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (L.map e.toMonoidHom) ↔
      IsTIMod M Q L := by
  refine ⟨fun h => ?_, fun h => h.map e⟩
  have := h.map e.symm
  rwa [map_symm_map, map_symm_map, map_symm_map] at this

theorem _root_.CFSG.RankThree.GF2n.Stroth80.CentTrivial.map {M Q Z S : Subgroup G}
    (h : CentTrivial M Q Z S) :
    CentTrivial (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (S.map e.toMonoidHom) := by
  intro h' hh' hcomm
  obtain ⟨k, rfl⟩ := e.surjective h'
  rw [H0_map, mem_map_apply] at hh'
  rw [comm_mem_map_iff] at hcomm
  exact (mem_map_apply e).mpr (h k hh' hcomm)

theorem _root_.CFSG.RankThree.GF2n.Stroth80.IsA2.map {Q Z : Subgroup G} {a : G}
    (h : IsA2 Q Z a) : IsA2 (Q.map e.toMonoidHom) (Z.map e.toMonoidHom) (e a) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : ⁅Q.map e.toMonoidHom, Subgroup.zpowers (e a)⁆ =
      ⁅Q, Subgroup.zpowers a⁆.map e.toMonoidHom := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [normalizer_map, mem_map_apply]
    exact h1
  · rwa [mem_map_apply]
  · rw [← map_pow, mem_map_apply]
    exact h3
  · rw [hc, ← Subgroup.map_sup, card_map, card_map]
    exact h4
  · rw [hc]
    exact h5.map _

theorem isA2_map_iff {Q Z : Subgroup G} {a : G} :
    IsA2 (Q.map e.toMonoidHom) (Z.map e.toMonoidHom) (e a) ↔ IsA2 Q Z a := by
  refine ⟨fun h => ?_, fun h => h.map e⟩
  have := h.map e.symm
  rwa [map_symm_map, map_symm_map, MulEquiv.symm_apply_apply] at this

theorem noA2_map_iff {Q Z L : Subgroup G} :
    NoA2 (Q.map e.toMonoidHom) (Z.map e.toMonoidHom) (L.map e.toMonoidHom) ↔ NoA2 Q Z L := by
  constructor
  · intro h a ha ha2
    exact h (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha) ((isA2_map_iff e).mpr ha2)
  · rintro h _ ⟨a, ha, rfl⟩ ha2
    exact h a ha ((isA2_map_iff e).mp ha2)

theorem _root_.CFSG.RankThree.GF2n.Stroth80.NoA2All.map {M Q Z : Subgroup G}
    (h : NoA2All M Q Z) :
    NoA2All (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom) := by
  intro B' ⟨g, hg⟩ hB'Q hB'Z
  have h1 : B' = (conjSubgroup (e.symm g) Z).map e.toMonoidHom := by
    rw [hg, ← conjSubgroup_map, MulEquiv.apply_symm_apply]
  have hle : conjSubgroup (e.symm g) Z ≤ Q := by
    have := Subgroup.map_mono (f := e.symm.toMonoidHom) (h1 ▸ hB'Q)
    rwa [map_symm_map, map_symm_map] at this
  have hne : conjSubgroup (e.symm g) Z ≠ Z := fun h' => hB'Z (by rw [h1, h'])
  rw [h1, LB_map]
  exact (noA2_map_iff e).mpr (h _ ⟨_, rfl⟩ hle hne)

theorem _root_.CFSG.RankThree.GF2n.Stroth80.SubConfig.map {M Q Z N : Subgroup G}
    (h : SubConfig M Q Z N) :
    SubConfig (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (N.map e.toMonoidHom) := by
  unfold SubConfig at h ⊢
  rw [H0_map]
  obtain ⟨hN, hS⟩ := h
  haveI := hN
  haveI hN' := normal_map e hN
  refine ⟨hN', ?_⟩
  have h1 := hS.map (quotEqv e (H0 M Z) Q)
  rw [← cen_map, ← normalizer_map, ← cen_map, ← bar_map] at h1
  exact h1

private theorem layer_quot_map {M Q S : Subgroup G}
    (h : ∃ hN : (Q.subgroupOf M).Normal, haveI := hN
      layer (↥M ⧸ Q.subgroupOf M) = (S.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) :
    ∃ hN : ((Q.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom)).Normal, haveI := hN
      layer (↥(M.map e.toMonoidHom) ⧸ (Q.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom)) =
        ((S.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom)).map
          (QuotientGroup.mk' ((Q.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom))) := by
  obtain ⟨hN, hL⟩ := h
  haveI := hN
  haveI hN' := normal_map e hN
  refine ⟨hN', ?_⟩
  have h1 := bar_map e M Q S
  unfold bar at h1
  rw [h1, ← hL, WholeGroup.layer_map_mulEquiv]

section Cases

variable {M Q Z B : Subgroup G}

theorem CaseD1.map {n : ℕ} (h : CaseD1 Q Z n) :
    CaseD1 (Q.map e.toMonoidHom) (Z.map e.toMonoidHom) n :=
  ⟨by rw [card_map]; exact h.1, h.2.map e⟩

theorem CaseD2.map (h : CaseD2 M Q Z B) :
    CaseD2 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) := by
  obtain ⟨h1, h2⟩ := h
  unfold CaseD2
  rw [LB_map, Lgen_map, card_map, card_map]
  exact ⟨h1, h2.map e isSLModel_of_mulEquiv⟩

theorem CaseD3.map (h : CaseD3 M Q Z B) :
    CaseD3 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold CaseD3
  rw [LB_map, Lgen_map, card_map, card_map]
  exact ⟨h1, h2.map e isSLModel_of_mulEquiv, h3.map e⟩

theorem CtxD4.map {t : G} (h : CtxD4 M Q Z B t) :
    CtxD4 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) (e t) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold CtxD4
  rw [LB_map, Lgen_map, isTIMod_map_iff, mem_map_apply, mem_map_apply]
  exact ⟨h1, h2, h3, h4.map e⟩

theorem CaseE1.map {t : G} (h : CaseE1 M Q Z B t) :
    CaseE1 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) (e t) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold CaseE1
  rw [LB_map, Nt_map, Rt_map, card_map, card_map, card_map]
  refine ⟨h1, h2, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl (h3.map e isOmegaPlus_of_mulEquiv)
  · exact Or.inr (h3.map e isOmegaMinus_of_mulEquiv)

theorem CaseE2.map {t : G} {m : ℕ} (h : CaseE2 M Q Z B t m) :
    CaseE2 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) (e t) m := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold CaseE2
  rw [LB_map, Nt_map, Rt_map, Lgen_map, card_map, card_map, card_map]
  refine ⟨h0, h1, h2, ?_⟩
  rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨h3.map e isOmegaPlus_of_mulEquiv, h4.map e isProdOf_of_mulEquiv⟩
  · exact Or.inr ⟨h3.map e isOmegaMinus_of_mulEquiv, h4.map e isProdOf_of_mulEquiv⟩

theorem CaseE3.map (h : CaseE3 M Q Z B) :
    CaseE3 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold CaseE3
  rw [LB_map, Lgen_map, card_map, card_map]
  refine ⟨h1, layer_quot_map e h2, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl (h3.map e isPSUModel_of_mulEquiv)
  · exact Or.inr (h3.map e isPSLModel_of_mulEquiv)

theorem CaseE4.map {t : G} (h : CaseE4 M Q Z B t) :
    CaseE4 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) (e t) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold CaseE4
  rw [LB_map, Nt_map, Rt_map, card_map, card_map, card_map]
  exact ⟨h1, h2, h3.map e isOmegaPlus_of_mulEquiv, h4.map e⟩

theorem CaseE5.map {t : G} (h : CaseE5 M Q Z B t) :
    CaseE5 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) (e t) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold CaseE5
  rw [LB_map, Nt_map, Rt_map, card_map, card_map, card_map]
  exact ⟨h1, h2, h3.map e isOmegaPlus_of_mulEquiv, h4.map e⟩

private theorem range_ker_comp {n : ℕ} {K : Type} [Field K] {S Q : Subgroup G}
    {φ : S →* GL (Fin n) K} (hr : φ.range = StatedSL n K) (hk : φ.ker = Q.subgroupOf S) :
    (φ.comp (eqv e S).symm.toMonoidHom).range = StatedSL n K ∧
      (φ.comp (eqv e S).symm.toMonoidHom).ker =
        (Q.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom) := by
  constructor
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (eqv e S).symm.surjective,
      ← MonoidHom.range_eq_map, hr]
  · rw [← MonoidHom.comap_ker, hk, ← subgroupOf_map e S Q]
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom]

theorem CaseE6.map {n : ℕ} (h : CaseE6 M Q Z B n) :
    CaseE6 (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) n := by
  obtain ⟨K, hK, hKf, hc, φ, hr, hk, V₁, V₂, h1, h2, h3, h4, h5, h6, hs1, hs2, ⟨x, hx, hxV⟩,
    hC⟩ := h
  unfold CaseE6
  rw [LB_map, Lgen_map]
  obtain ⟨hr', hk'⟩ := range_ker_comp e hr hk
  refine ⟨K, hK, hKf, by rw [card_map]; exact hc, φ.comp (eqv e _).symm.toMonoidHom, hr', hk',
    V₁.map e.toMonoidHom, V₂.map e.toMonoidHom, Subgroup.map_mono h1, Subgroup.map_mono h2,
    Subgroup.map_mono h3, Subgroup.map_mono h4, by rw [← map_inf, h5],
    by rw [← Subgroup.map_sup, h6], hs1.map e (fun s => ?_), hs2.map e (fun s => ?_),
    ⟨e x, Subgroup.mem_map_of_mem _ hx, by rw [conjSubgroup_map, hxV]⟩, hC.map e⟩
  · exact congrArg φ ((eqv e _).symm_apply_apply s)
  · exact congrArg φ ((eqv e _).symm_apply_apply s)

theorem OrthCase.map (h : OrthCase M Q Z B) :
    OrthCase (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) := by
  obtain ⟨t, h1, h2⟩ := h
  refine ⟨e t, h1.map e, ?_⟩
  rcases h2 with h2 | ⟨m, h2⟩
  · exact Or.inl (h2.map e)
  · exact Or.inr ⟨m, h2.map e⟩

theorem ECase.map (h : ECase M Q Z B) :
    ECase (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) := by
  obtain ⟨t, h1, h2⟩ := h
  refine ⟨e t, h1.map e, ?_⟩
  rcases h2 with h2 | h2 | h2
  · exact Or.inl (h2.map e)
  · exact Or.inr (Or.inl (h2.map e))
  · exact Or.inr (Or.inr (h2.map e))

theorem _root_.CFSG.RankThree.GF2n.Stroth80.StrothConclusion.map
    (h : StrothConclusion M Q Z B) :
    StrothConclusion (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) := by
  rw [strothConclusion_iff_cases] at h ⊢
  obtain ⟨h1, hF⟩ := h
  refine ⟨?_, hF.map e⟩
  rcases h1 with ⟨n, hD1⟩ | hD2 | hD3 | ⟨hTI, ⟨hNo, t, ht, htQ, hCT, hE⟩ | ⟨n, hE6⟩⟩
  · exact Or.inl ⟨n, hD1.map e⟩
  · exact Or.inr (Or.inl (hD2.map e))
  · exact Or.inr (Or.inr (Or.inl (hD3.map e)))
  · obtain ⟨h1', h2', h3', h4'⟩ := CtxD4.map e (t := t) ⟨hTI, ht, htQ, hCT⟩
    refine Or.inr (Or.inr (Or.inr ⟨h1', Or.inl ⟨hNo.map e, e t, h2', h3', h4', ?_⟩⟩))
    rcases hE with hE | ⟨m, hE⟩ | hE | hE | hE
    · exact Or.inl (hE.map e)
    · exact Or.inr (Or.inl ⟨m, hE.map e⟩)
    · exact Or.inr (Or.inr (Or.inl (hE.map e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hE.map e))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hE.map e))))
  · refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inr ⟨n, hE6.map e⟩⟩))
    rw [LB_map, isTIMod_map_iff]
    exact hTI

theorem Cfg.map (h : Cfg M Q Z B) :
    Cfg (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) :=
  ⟨h.ctx.map e, h.conclusion.map e⟩

theorem LinSetup.map {n : ℕ} {V₁ V₂ : Subgroup G} (h : LinSetup M Q Z B n V₁ V₂) :
    LinSetup (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) n (V₁.map e.toMonoidHom) (V₂.map e.toMonoidHom) := by
  obtain ⟨K, hK, hKf, hc, φ, hr, hk, h1, h2, h3, h4, h5, h6, hs1, hs2, ⟨x, hx, hxV⟩,
    hC⟩ := h
  unfold LinSetup
  rw [LB_map, Lgen_map]
  obtain ⟨hr', hk'⟩ := range_ker_comp e hr hk
  refine ⟨K, hK, hKf, by rw [card_map]; exact hc, φ.comp (eqv e _).symm.toMonoidHom, hr', hk',
    Subgroup.map_mono h1, Subgroup.map_mono h2, Subgroup.map_mono h3, Subgroup.map_mono h4,
    by rw [← map_inf, h5], by rw [← Subgroup.map_sup, h6], hs1.map e (fun s => ?_),
    hs2.map e (fun s => ?_), ⟨e x, Subgroup.mem_map_of_mem _ hx, by rw [conjSubgroup_map, hxV]⟩,
    hC.map e⟩
  · exact congrArg φ ((eqv e _).symm_apply_apply s)
  · exact congrArg φ ((eqv e _).symm_apply_apply s)

end Cases

end Transport

section Conj

variable {G : Type} [Group G]

theorem LB_conj (y : G) (M Q B : Subgroup G) :
    LB (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y B) = conjSubgroup y (LB M Q B) :=
  LB_map (MulAut.conj y) M Q B

theorem Rt_conj (y : G) (M L : Subgroup G) (t : G) :
    Rt (conjSubgroup y M) (conjSubgroup y L) (y * t * y⁻¹) = conjSubgroup y (Rt M L t) :=
  Rt_map (MulAut.conj y) M L t

theorem _root_.CFSG.RankThree.GF2n.Stroth80.StrothHyp.conj {M Q Z : Subgroup G}
    (h : StrothHyp M Q Z) (y : G) :
    StrothHyp (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) :=
  h.map (MulAut.conj y)

theorem _root_.CFSG.RankThree.GF2n.Stroth80.Ctx.conjBy {M Q Z B : Subgroup G}
    (h : Ctx M Q Z B) (y : G) :
    Ctx (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) :=
  h.map (MulAut.conj y)

theorem _root_.CFSG.RankThree.GF2n.Stroth80.QuotSat.conj {S N : Subgroup G}
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → P X → P Y) (h : QuotSat S N P)
    (y : G) : QuotSat (conjSubgroup y S) (conjSubgroup y N) P :=
  h.map (MulAut.conj y) hP

theorem noA2_conj_iff (y : G) {Q Z L : Subgroup G} :
    NoA2 (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y L) ↔ NoA2 Q Z L :=
  noA2_map_iff (MulAut.conj y)

theorem CtxD4.conj {M Q Z B : Subgroup G} {t : G} (h : CtxD4 M Q Z B t) (y : G) :
    CtxD4 (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B)
      (y * t * y⁻¹) :=
  h.map (MulAut.conj y)

theorem CaseE4.conj {M Q Z B : Subgroup G} {t : G} (h : CaseE4 M Q Z B t) (y : G) :
    CaseE4 (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B)
      (y * t * y⁻¹) :=
  h.map (MulAut.conj y)

theorem CaseE5.conj {M Q Z B : Subgroup G} {t : G} (h : CaseE5 M Q Z B t) (y : G) :
    CaseE5 (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B)
      (y * t * y⁻¹) :=
  h.map (MulAut.conj y)

theorem OrthCase.conj {M Q Z B : Subgroup G} (h : OrthCase M Q Z B) (y : G) :
    OrthCase (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) :=
  h.map (MulAut.conj y)

theorem ECase.conj {M Q Z B : Subgroup G} (h : ECase M Q Z B) (y : G) :
    ECase (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) :=
  h.map (MulAut.conj y)

theorem Cfg.conj {M Q Z B : Subgroup G} (h : Cfg M Q Z B) (y : G) :
    Cfg (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) :=
  h.map (MulAut.conj y)

theorem LinSetup.conj {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (h : LinSetup M Q Z B n V₁ V₂) (y : G) :
    LinSetup (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) n
      (conjSubgroup y V₁) (conjSubgroup y V₂) :=
  h.map (MulAut.conj y)

end Conj

end CFSG.RankThree.GF2n.Smith81
