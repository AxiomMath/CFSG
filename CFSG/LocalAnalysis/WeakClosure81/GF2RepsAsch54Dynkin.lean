module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54DynkinAlt6
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Orbit
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2OrbitFrame
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2FamCl
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Psi
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Shape
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Red
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Top
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CFb
public import CFSG.LocalAnalysis.WeakClosure81.W183Cited
import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54AS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt OInf)

theorem map_subtype_maximal_of_isCoatom {Q : Type} [Group Q] {L : Subgroup Q}
    {P' : Subgroup ↥L} (hP' : IsCoatom P') :
    P'.map L.subtype < L ∧ ∀ Y : Subgroup Q, P'.map L.subtype < Y → Y ≤ L → Y = L := by
  have hlt : P'.map L.subtype < L := by
    refine lt_of_le_of_ne (Subgroup.map_subtype_le P') fun h => hP'.1 ?_
    apply Subgroup.map_injective L.subtype_injective
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨hlt, fun Y hPY hYL => ?_⟩
  have hle : P' ≤ Y.subgroupOf L := fun p hp =>
    Subgroup.mem_subgroupOf.mpr (hPY.le (Subgroup.mem_map_of_mem _ hp))
  have hne : P' ≠ Y.subgroupOf L := by
    intro h
    apply hPY.ne
    rw [h, Subgroup.map_subgroupOf_eq_of_le hYL]
  have htop := hP'.2 _ (lt_of_le_of_ne hle hne)
  refine le_antisymm hYL fun l hl => ?_
  have : (⟨l, hl⟩ : ↥L) ∈ Y.subgroupOf L := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_actsOnDynkinMod_bot_alt6 {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    (hLn : L.Normal) (ψ : ↥L ≃* DynkinAlt6.A6) (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤)
    (hMt : M < ⊤) (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) :
    ∃ t ∈ T, ActsOnDynkinMod ⊥ L t := by
  have hT2 : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hT2 le_top (Subgroup.normalizer_eq_top_iff.mpr hLn).ge
  have hDp : IsPGroup 2 ((T ⊓ L).subgroupOf L) := hS.2.1.comap_of_injective _ L.subtype_injective
  obtain ⟨P₁', P₂', hne', hP₁', hP₂', hN₁', hN₂'⟩ :=
    DynkinAlt6.exists_two_isCoatom_of_alt6 ψ hDp hS.2.2
  have hNle : ∀ {P' : Subgroup ↥L}, normalizer (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ P' →
      L ⊓ normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ P'.map L.subtype := by
    intro P' hP' q hq
    obtain ⟨hqL, hqN⟩ := Subgroup.mem_inf.mp hq
    refine ⟨⟨q, hqL⟩, hP' ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hqN ⊢
    intro h
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hqN h
  obtain ⟨hP₁L, hP₁m⟩ := map_subtype_maximal_of_isCoatom (L := L) hP₁'
  obtain ⟨hP₂L, hP₂m⟩ := map_subtype_maximal_of_isCoatom (L := L) hP₂'
  set P₁ := P₁'.map L.subtype with hP₁def
  set P₂ := P₂'.map L.subtype with hP₂def
  have hN₁ := hNle hN₁'
  have hN₂ := hNle hN₂'
  by_contra hno
  have hnorm : ∀ {P : Subgroup Q}, P < L → (∀ Y : Subgroup Q, P < Y → Y ≤ L → Y = L) →
      L ⊓ normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ P → T ≤ normalizer (P : Set Q) := by
    intro P hPL hPm hPN t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra hmov
    exact hno ⟨t, ht, Chev2Orbit.actsOnDynkinMod_bot_of_swap hLn hT ht hPL hPm hPN hmov⟩
  have hproper : ∀ {P : Subgroup Q}, P < L → T ≤ normalizer (P : Set Q) →
      L ⊓ normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ P → P ⊔ T < ⊤ := by
    intro P hPL hTN hPN
    refine lt_top_iff_ne_top.mpr fun htop => hPL.ne (le_antisymm hPL.le fun l hl => ?_)
    have hl' : l ∈ ((P ⊔ T : Subgroup Q) : Set Q) := by rw [htop]; trivial
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P T hTN] at hl'
    obtain ⟨p, hp, t, ht, rfl⟩ := hl'
    have htL : t ∈ L := by
      have : t = p⁻¹ * (p * t) := by group
      rw [this]
      exact L.mul_mem (L.inv_mem (hPL.le hp)) hl
    have htP : t ∈ P := hPN ⟨htL, Subgroup.le_normalizer ⟨ht, htL⟩⟩
    exact P.mul_mem hp htP
  have hX₁ := hMax _ le_sup_right (hproper hP₁L (hnorm hP₁L hP₁m hN₁) hN₁)
  have hX₂ := hMax _ le_sup_right (hproper hP₂L (hnorm hP₂L hP₂m hN₂) hN₂)
  have hne : P₁ ≠ P₂ := fun h => hne' (Subgroup.map_injective L.subtype_injective h)
  have hsup : P₁ ⊔ P₂ = L := by
    refine hP₁m _ (lt_of_le_of_ne le_sup_left fun h => hne ?_) (sup_le hP₁L.le hP₂L.le)
    have h21 : P₂ ≤ P₁ := h ▸ le_sup_right
    by_contra h12
    exact hP₁L.ne (hP₂m P₁ (lt_of_le_of_ne h21 (Ne.symm h12)) hP₁L.le)
  have hLM : L ≤ M := hsup ▸ sup_le (le_sup_left.trans hX₁) (le_sup_left.trans hX₂)
  have hTM : T ≤ M := le_sup_right.trans hX₁
  exact hMt.ne (top_le_iff.mp (hLT ▸ sup_le hLM hTM))

theorem exists_actsOnDynkinMod_bot_of_uniqueMax {Q : Type} [Group Q] [Finite Q]
    {L T M : Subgroup Q} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤)
    (hMt : M < ⊤) (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (hsh : IsAlt ↥L 6 ∨ IsL3 ↥L 1) : ∃ t ∈ T, ActsOnDynkinMod ⊥ L t := by
  rcases hsh with hA | hL3
  · obtain ⟨ψ⟩ : Nonempty (↥L ≃* alternatingGroup (Fin 6)) := hA
    exact exists_actsOnDynkinMod_bot_alt6 hLn ψ hT hLT hMt hMax
  · have hm : CFSG.Models.LieModel ↥L .PSL 3 2 1 :=
      CFSG.Models.LieModel.of_blueprint (by decide) hL3
    obtain ⟨K, _, _, D, nn, H, π, e, hBQ, hrank⟩ := Chev2Orbit.hasBQRank_psl hm
    obtain ⟨π', hU⟩ := Chev2Orbit.exists_umaxBQ hLn hLs hnab hT hMt hMax hBQ
    obtain ⟨t, ht, P, hPL, hPm, hPN, hne⟩ := hU.exists_swap hrank
    exact ⟨t, ht, Chev2Orbit.actsOnDynkinMod_bot_of_swap hLn hT ht hPL hPm hPN hne⟩

open CFSG.Quasithin.Vol2.Ch11.SecB (E111Reduced) in
open CFSG.Quasithin.E2.E22N.E111R (IsComp) in
theorem exists_uniqueMax_autQ {G : Type} [Group G] [Finite G] {X T J : Subgroup G}
    (hR : E111Reduced G X T) (hJ : IsComp X J) {M : Subgroup G} (hM : M < ⊤)
    (hMax : ∀ Y : Subgroup G, T ≤ Y → Y < ⊤ → Y ≤ M) :
    ∃ MQ : Subgroup ↥(autQ T J), MQ < ⊤ ∧
      ∀ W : Subgroup ↥(autQ T J), (autT T J).subgroupOf (autQ T J) ≤ W → W < ⊤ → W ≤ MQ := by
  set MA : Subgroup (MulAut ↥J) := (M.subgroupOf (normalizer (J : Set G))).map (autJ J)
    with hMA
  have hlift : ∀ W : Subgroup ↥(autQ T J), (autT T J).subgroupOf (autQ T J) ≤ W → W < ⊤ →
      liftN T J (W.map (autQ T J).subtype) ≤ M := fun W hTW hWt =>
    hMax _ (le_liftN T J _) (liftN_lt_top hR hJ (autT_le_map_subtype hTW)
      (Subgroup.map_subtype_le W) (map_subtype_ne_of_lt_top hWt))
  have hle : ∀ W : Subgroup ↥(autQ T J), (autT T J).subgroupOf (autQ T J) ≤ W → W < ⊤ →
      W.map (autQ T J).subtype ≤ MA := by
    intro W hTW hWt
    rw [← map_liftN hR hJ (autT_le_map_subtype hTW) (Subgroup.map_subtype_le W)]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hlift W hTW hWt (Subgroup.mem_subgroupOf.mp hx))
  have hTM : T ≤ M := (le_liftN T J _).trans (hlift _ le_rfl (autT_subgroupOf_lt_top hR hJ))
  refine ⟨MA.subgroupOf (autQ T J), lt_top_iff_ne_top.mpr fun htop => hM.ne ?_,
    fun W hTW hWt w hw => Subgroup.mem_subgroupOf.mpr (hle W hTW hWt ⟨w, hw, rfl⟩)⟩
  have hQ : autQ T J ≤ MA := fun x hx => by
    have : (⟨x, hx⟩ : ↥(autQ T J)) ∈ MA.subgroupOf (autQ T J) := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  exact eq_top_of_le hR hJ (le_of_innAutOf_le hR hJ hTM ((innAutOf_le_autQ T J).trans hQ)) hTM

theorem exists_mulEquiv_of_hasQuotShape {G : Type*} [Group G] {K : Subgroup G} {N : Set G}
    {P : ∀ (X : Type) [Group X], Prop} (h : HasQuotShape K N P) {Y : Type*} [Group Y]
    (ψ : ↥K →* Y) (hψ : Function.Surjective ψ) (hker : ∀ k : ↥K, ψ k = 1 ↔ (k : G) ∈ N) :
    ∃ (X : Type) (_ : Group X), P X ∧ Nonempty (Y ≃* X) := by
  obtain ⟨X, hX, φ, hφ, hkerφ, hPX⟩ := h
  have hk : ψ.ker = φ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hkerφ]
  exact ⟨X, hX, hPX, ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))⟩⟩

theorem asch5_4Dynkin_of_asch5_4 (h54 : Asch5_4) : Asch5_4Dynkin := by
  intro G _ _ H T hK hT hTH hno hne hrank L hL hLT hsh
  have hN : calNIn H T = {lGen IsCalL0 H T} := by
    rcases h54 G H T hK hT hTH hno with h1 | ⟨p, hp, hp2, h3, h1'⟩ | ⟨hN, -⟩
    · exact absurd h1 hne
    · rcases hrank p hp hp2 with h | h <;> omega
    · exact hN
  set M := lGen IsCalL0 H T with hMdef
  have hMmem : M ∈ calNIn H T := by rw [hN]; exact Set.mem_singleton M
  have hMax : ∀ Y : Subgroup G, T ≤ Y → Y < H → Y ≤ M := by
    intro Y hTY hYH
    obtain ⟨X, hX, hYX⟩ := exists_mem_calNIn_of_lt hTY hYH
    rw [hN, Set.mem_singleton_iff] at hX
    exact hX ▸ hYX
  set S := T.subgroupOf H with hSdef
  have hS : IsSylowIn 2 S ⊤ := isSylowIn_subgroupOf_top hT
  have hRs : Group.IsSolvable ↥(CFSG.solvableRadical ↥H) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  set R := CFSG.solvableRadical ↥H with hRdef
  set π := QuotientGroup.mk' R with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hkerπ : π.ker = R := QuotientGroup.ker_mk' R
  have hrad : CFSG.solvableRadical (↥H ⧸ R) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient
  have hOInf : OInf H = π.ker.map H.subtype := by rw [hkerπ]; rfl
  set Sb := S.map π with hSbdef
  have hSb : IsSylowIn 2 Sb ⊤ := isSylowIn_map_top hπ hS
  have hLH : L ≤ H := hL.2.2.1
  have hRL : R ≤ L.subgroupOf H := fun r hr =>
    Subgroup.mem_subgroupOf.mpr (hL.2.1 (Subgroup.mem_map_of_mem H.subtype hr))
  set E := (L.subgroupOf H).map π with hEdef
  have hpre : preG π E = L := by
    rw [preG, hEdef, Subgroup.comap_map_eq, hkerπ, sup_of_le_left hRL]
    exact Subgroup.map_subgroupOf_eq_of_le hLH
  let ψ : ↥L →* ↥E := (toE π E).comp (MulEquiv.subgroupCongr hpre.symm).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (toE_surjective hπ E).comp (MulEquiv.subgroupCongr hpre.symm).surjective
  have hψker : ∀ l : ↥L, ψ l = 1 ↔ (l : G) ∈ OInf H := fun l => by
    rw [hOInf]
    exact toE_eq_one_iff π E _
  obtain ⟨X₁, _, hX₁, ⟨e₁⟩⟩ := exists_mulEquiv_of_hasQuotShape hL.2.2.2.2 ψ hψ hψker
  obtain ⟨X₂, _, hX₂, ⟨e₂⟩⟩ := exists_mulEquiv_of_hasQuotShape hsh ψ hψ hψker
  have hE : CFSG.IsComponent E :=
    ⟨CFSG.IsQuasisimple.of_mulEquiv e₁ hX₁,
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hLH).1 hL.2.2.2.1).map hπ⟩
  have hESb : E ⊔ Sb = ⊤ := by
    have h1 : L.subgroupOf H ⊔ S = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH,
        Subgroup.map_subgroupOf_eq_of_le hT.1, hLT, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have h2 := congrArg (Subgroup.map π) h1
    rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective π hπ] at h2
  obtain ⟨hR, hJ⟩ := e111Reduced_normalClosure hrad hE hSb hESb
  obtain ⟨hEs, hEnab⟩ := isSimpleGroup_of_isComponent hrad hE
  have hHns : ¬ Group.IsSolvable ↥H := fun hs =>
    not_isSolvable_of_isComponentModN hL (solvable_of_solvable_injective
      (Subgroup.inclusion_injective hLH))
  have hYns : ¬ Group.IsSolvable (↥H ⧸ R) := fun _ =>
    hHns (Group.isSolvable_of_subgroup_quotient R)
  set MH := M.subgroupOf H with hMHdef
  have hMH : ∀ Y : Subgroup ↥H, S ≤ Y → Y < ⊤ → Y ≤ MH := by
    intro Y hSY hYt
    have hYG : Y.map H.subtype ≤ M := hMax _
      (fun t ht => ⟨⟨t, hT.1 ht⟩, hSY (Subgroup.mem_subgroupOf.mpr ht), rfl⟩)
      (map_subtype_lt_iff.mpr hYt)
    exact fun y hy => Subgroup.mem_subgroupOf.mpr (hYG ⟨y, hy, rfl⟩)
  have hRM : R ≤ MH := by
    have hSR : S ⊔ R < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => hYns ?_
      have hSbt : Sb = ⊤ := by
        have h2 := congrArg (Subgroup.map π) h
        rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff R).mpr hkerπ.ge, sup_bot_eq,
          Subgroup.map_top_of_surjective π hπ] at h2
      have hp : IsPGroup 2 (↥H ⧸ R) := by
        have h3 := hSb.2.1
        rw [hSbt] at h3
        exact h3.of_equiv Subgroup.topEquiv
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := hp.isNilpotent
      infer_instance
    exact le_sup_right.trans (hMH _ le_sup_left hSR)
  have hMY : ∀ Z : Subgroup (↥H ⧸ R), Sb ≤ Z → Z < ⊤ → Z ≤ MH.map π := by
    intro Z hSZ hZt
    have h1 : S ≤ Z.comap π := fun s hs => hSZ ⟨s, hs, rfl⟩
    have h2 : Z.comap π < ⊤ := lt_top_iff_ne_top.mpr fun h => hZt.ne (by
      rw [← Subgroup.map_comap_eq_self_of_surjective hπ Z, h, Subgroup.map_top_of_surjective π hπ])
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ Z]
    exact Subgroup.map_mono (hMH _ h1 h2)
  have hMYt : MH.map π < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hMmem.2.1.ne (le_antisymm hMmem.2.1.le fun x hx => ?_)
    have h1 := congrArg (Subgroup.comap π) h
    rw [Subgroup.comap_map_eq, hkerπ, sup_of_le_left hRM, Subgroup.comap_top] at h1
    have : (⟨x, hx⟩ : ↥H) ∈ MH := h1 ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨MQ, hMQ, hMQmax⟩ := exists_uniqueMax_autQ hR hJ hMYt hMY
  have hZ : center ↥E = ⊥ := center_eq_bot_of_isComp hJ
  have hAinn : innAutOf ↥E ≤ autQ Sb E := innAutOf_le_autQ Sb E
  have hLn : ((innAutOf ↥E).subgroupOf (autQ Sb E)).Normal :=
    Subgroup.Normal.subgroupOf (innAutOf_normal ↥E) _
  let eL : ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) ≃* ↥E :=
    (Subgroup.subgroupOfEquivOfLe hAinn).trans (innAutOfEquiv hJ)
  have := hEs
  have hLs : IsSimpleGroup ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) := eL.isSimpleGroup
  have hLnab : ∃ a b : ↥((innAutOf ↥E).subgroupOf (autQ Sb E)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hEnab
    refine ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩
    simpa using congrArg eL h
  have hTh : IsSylowIn 2 ((autT Sb E).subgroupOf (autQ Sb E)) ⊤ :=
    isSylowIn_autT_subgroupOf hR hJ
  have hLT' : (innAutOf ↥E).subgroupOf (autQ Sb E) ⊔ (autT Sb E).subgroupOf (autQ Sb E) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (innAutOf_le_autQ Sb E) (autT_le_autQ Sb E), innAutOf_sup_autT,
      Subgroup.subgroupOf_self]
  have hshQ : IsAlt ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) 6 ∨
      IsL3 ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) 1 := by
    rcases hX₂ with hA | h3
    · obtain ⟨e⟩ : Nonempty (X₂ ≃* alternatingGroup (Fin 6)) := hA
      exact Or.inl ⟨(eL.trans e₂).trans e⟩
    · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv (eL.trans e₂).symm h3)
  obtain ⟨t', ht', hD⟩ :=
    exists_actsOnDynkinMod_bot_of_uniqueMax hLn hLs hLnab hTh hLT' hMQ hMQmax hshQ
  obtain ⟨s, hsT, n, hn, hnt⟩ := exists_of_mem_autT π (Subgroup.mem_subgroupOf.mp ht')
  have hD' : ActsOnDynkinMod (OInf H) (preG π E) s := by
    refine actsOnDynkinMod_of_surjective ?_ (innPsi π E hAinn) (innPsi_surjective hπ E hAinn) ?_ ?_
      (mem_normalizer_preG (hn ▸ n.2)) ?_ hD
    · rw [hOInf]
      exact Subgroup.map_mono (MonoidHom.ker_le_comap π E)
    · intro l
      rw [hOInf]
      exact innPsi_eq_one_iff π hZ hAinn l
    · intro l hl
      exact Subtype.ext (Subgroup.mem_bot.mp hl)
    · intro l l₂ h
      apply Subtype.ext
      rw [innPsi_conj π E hAinn hn l l₂ h, hnt]
      rfl
  exact ⟨s, hsT, hpre ▸ hD'⟩

end CFSG.LocalAnalysis.WeakClosure81

end
