module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLift
public import CFSG.Quasithin.EmptyFaithful.S151S9ULift
public import CFSG.Quasithin.EmptyFaithful.S151S9UCQ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2G3

public section

namespace CFSG.Quasithin.J4Local

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239

@[expose] def CanonicalOver {X : Type*} [Group X] (S₀ H₀ : Subgroup X) : Prop :=
  ∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → H₀.map α.toMonoidHom = H₀

variable {G : Type} [Group G] {L R : Subgroup G}

theorem exists_canonical_conj [Finite G] (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hS : IsSylowTwoOf (R ⊓ L) L) {X : Type} [Group X] [Finite X] (θ0 : ↥L →* X)
    (hθ0 : Function.Surjective θ0) (hker : θ0.ker = CFSG.pCore 2 ↥L) (S₀ : Subgroup X)
    (hS₀ : IsPGroup 2 ↥S₀) (hS₀i : ¬ 2 ∣ S₀.index) (H₀ : Subgroup X)
    (hinv : CanonicalOver S₀ H₀) :
    ∃ θ : ↥L →* X, Function.Surjective θ ∧ θ.ker = θ0.ker ∧
      ((R ⊓ L).subgroupOf L).map θ = S₀ ∧
      R ≤ Subgroup.normalizer (((H₀.comap θ).map L.subtype : Subgroup G) : Set G) := by
  classical
  set SL : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSL
  have hSL2 : IsPGroup 2 SL := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSLi : ¬ 2 ∣ SL.index := hS.2.2
  have hSX2 : IsPGroup 2 (SL.map θ0) := hSL2.map θ0
  have hSXi : ¬ 2 ∣ (SL.map θ0).index := fun h => hSLi (h.trans (Subgroup.index_map_dvd SL hθ0))
  obtain ⟨x, hx⟩ := exists_conj_of_sylow_two hSX2 hSXi hS₀ hS₀i
  let θ : ↥L →* X := (MulAut.conj x).toMonoidHom.comp θ0
  have hθ : Function.Surjective θ := (MulAut.conj x).surjective.comp hθ0
  have hθker : θ.ker = θ0.ker := by
    ext l
    simp [θ, MonoidHom.mem_ker]
  have hθS : SL.map θ = S₀ := by
    rw [← hx, ← Subgroup.map_map]
  have hind : ∀ (r : G) (hr : r ∈ R), ∃ cbar : MulAut X, S₀.map cbar.toMonoidHom = S₀ ∧
      ∀ l : ↥L, cbar (θ l) = θ (L.normalizerMonoidHom ⟨r, hRN hr⟩ l) := by
    intro r hr
    set c : MulAut ↥L := L.normalizerMonoidHom ⟨r, hRN hr⟩ with hc
    have hkerc : θ.ker.comap c.toMonoidHom = θ.ker := by
      rw [hθker, hker]
      exact (Subgroup.Characteristic.fixed (H := CFSG.pCore 2 ↥L) inferInstance c)
    obtain ⟨cbar, hcbar⟩ := exists_induced_mulAut θ hθ c hkerc
    have hSc : SL.map c.toMonoidHom = SL := by
      ext y
      constructor
      · rintro ⟨l, hl, rfl⟩
        have hl' : (l : G) ∈ R ⊓ L := hl
        have : ((c l : ↥L) : G) ∈ R ⊓ L :=
          ⟨(conj_mem_sylow_iff hRN hr l).2 hl'.1, (c l).2⟩
        exact this
      · intro hy
        have hy' : (y : G) ∈ R ⊓ L := hy
        refine ⟨c.symm y, ?_, by simp⟩
        have h1 : ((c (c.symm y) : ↥L) : G) ∈ R := by simpa using hy'.1
        show ((c.symm y : ↥L) : G) ∈ R ⊓ L
        exact ⟨(conj_mem_sylow_iff hRN hr (c.symm y)).1 h1, (c.symm y).2⟩
    refine ⟨cbar, ?_, hcbar⟩
    rw [← hθS, Subgroup.map_map]
    have : cbar.toMonoidHom.comp θ = θ.comp c.toMonoidHom := by
      ext l
      exact hcbar l
    rw [this, ← Subgroup.map_map, hSc]
  refine ⟨θ, hθ, hθker, hθS, ?_⟩
  have hmem : ∀ g : G, g ∈ (H₀.comap θ).map L.subtype ↔ ∃ hg : g ∈ L, θ ⟨g, hg⟩ ∈ H₀ := by
    intro g
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.2, hl⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hkey : ∀ r ∈ R, ∀ g ∈ (H₀.comap θ).map L.subtype,
      r * g * r⁻¹ ∈ (H₀.comap θ).map L.subtype := by
    intro r hr g hg
    obtain ⟨hgL, hgK⟩ := (hmem g).1 hg
    obtain ⟨cbar, hS₀c, hcbar⟩ := hind r hr
    have hKc := hinv cbar hS₀c
    have hgL' : r * g * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hRN hr) g).1 hgL
    refine (hmem _).2 ⟨hgL', ?_⟩
    have h1 : θ ⟨r * g * r⁻¹, hgL'⟩ = cbar (θ ⟨g, hgL⟩) := by
      rw [hcbar]
      rfl
    have h2 : cbar (θ ⟨g, hgL⟩) ∈ H₀.map cbar.toMonoidHom := ⟨θ ⟨g, hgL⟩, hgK, rfl⟩
    rw [hKc] at h2
    rw [h1]
    exact h2
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hkey r hr g, fun hg => ?_⟩
  have := hkey r⁻¹ (R.inv_mem hr) _ hg
  simpa [mul_assoc] using this

theorem exists_hom_of_equiv {L X : Type*} [Group L] [Group X] (N : Subgroup L) [N.Normal]
    (e : (L ⧸ N) ≃* X) : ∃ θ0 : L →* X, Function.Surjective θ0 ∧ θ0.ker = N := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N), e.surjective.comp
    (QuotientGroup.mk'_surjective N), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem mem_cComp_sup_of_normalizes {K : Subgroup G} (hK : K ∈ cComp K)
    (hR : R ≤ Subgroup.normalizer (K : Set G)) : K ∈ cComp (K ⊔ R) := by
  obtain ⟨hne, hperf, -, hmin⟩ := hK
  have hnorm : K ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (Subgroup.le_normalizer) hR
  refine ⟨hne, hperf, A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnorm), ?_⟩
  intro K' hlt hK'ne hK'perf hsub
  exact hmin K' hlt hK'ne hK'perf (A3.subnormal_of_le_of_le hsub hlt.le le_sup_left)

theorem eq_top_of_sup_central {L : Type*} [Group L] (hperf : commutator L = ⊤) {D Z : Subgroup L}
    (hZ : Z ≤ Subgroup.center L) (hDZ : D ⊔ Z = ⊤) : D = ⊤ := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  have hcomm : commutator L ≤ D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have ha : a ∈ D ⊔ Z := hDZ ▸ Subgroup.mem_top a
    have hb : b ∈ D ⊔ Z := hDZ ▸ Subgroup.mem_top b
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
    obtain ⟨d', hd', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hb
    rw [S151S9U.commutatorElement_mul_central_mul_central (hZ hz) (hZ hz'), commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd hd') (D.inv_mem hd)) (D.inv_mem hd')
  rw [hperf, top_le_iff] at hcomm
  exact hcomm

theorem exists_local_of_canonical [Finite G] (hLperf : ⁅L, L⁆ = L)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hR2 : IsPGroup 2 ↥R)
    (hS : IsSylowTwoOf (R ⊓ L) L)
    (hne : ¬ L ≤ Subgroup.centralizer (centerOf (R ⊓ L) : Set G))
    {X : Type} [Group X] [Finite X] (θ0 : ↥L →* X) (hθ0 : Function.Surjective θ0)
    (hker : θ0.ker = CFSG.pCore 2 ↥L) (hkerc : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L)
    (S₀ H₀ : Subgroup X) (hS₀ : IsPGroup 2 ↥S₀) (hS₀i : ¬ 2 ∣ S₀.index) (hSH : S₀ ≤ H₀)
    (hinv : CanonicalOver S₀ H₀)
    (hperf : ⁅H₀, H₀⁆ = H₀) (hgood : GoodLocal H₀) (N : Subgroup ↥H₀) [N.Normal]
    (hN2 : IsPGroup 2 ↥N) (hNsimple : IsSimpleGroup (↥H₀ ⧸ N)) (hcoat : IsCoatom H₀)
    (hgen : ∀ W : Subgroup X, W ≤ centerOf S₀ → W ≠ ⊥ → ¬ Subgroup.centralizer (W : Set X) ≤ H₀) :
    ∃ K : Subgroup G, K ≤ L ∧ ⁅K, K⁆ = K ∧ R ≤ Subgroup.normalizer (K : Set G) ∧
      K ∈ cComp (K ⊔ R) ∧ ¬ 2 ∣ (R.subgroupOf (K ⊔ R)).index ∧ CharTwo K ∧
      Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥H₀ ⧸ N)) ∧
      K ⊔ (L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G)) = L := by
  classical
  have : IsSimpleGroup (↥H₀ ⧸ N) := hNsimple
  obtain ⟨θ, hθ, hθker, hθS, hθN⟩ :=
    exists_canonical_conj hRN hS θ0 hθ0 hker S₀ hS₀ hS₀i H₀ hinv
  have hθker' : θ.ker = CFSG.pCore 2 ↥L := hθker.trans hker
  have hker2 : IsPGroup 2 ↥θ.ker := by
    rw [hθker']
    exact CFSG.pCore_isPGroup
  have hkerZ : θ.ker ≤ Subgroup.center ↥L := by
    rw [hθker']
    exact hkerc
  set Y : Subgroup G := (H₀.comap θ).map L.subtype with hYdef
  have hYL : Y ≤ L := by
    rintro _ ⟨l, _, rfl⟩
    exact l.2
  have hSLY : R ⊓ L ≤ Y := by
    rintro x ⟨hxR, hxL⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    have h1 : θ ⟨x, hxL⟩ ∈ ((R ⊓ L).subgroupOf L).map θ := ⟨⟨x, hxL⟩, ⟨hxR, hxL⟩, rfl⟩
    rw [hθS] at h1
    exact hSH h1
  have hY' : Y.subgroupOf L = H₀.comap θ := by
    ext l
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨l', hl', hll'⟩
      have : l' = l := Subtype.ext hll'
      rw [← this]
      exact hl'
    · intro h
      exact ⟨l, h, rfl⟩
  have hYmap : (Y.subgroupOf L).map θ = H₀ := by
    rw [hY']
    exact Subgroup.map_comap_eq_self_of_surjective hθ H₀
  have hH0ne : H₀ ≠ ⊥ := by
    intro h0
    have : Nontrivial (↥H₀ ⧸ N) := hNsimple.toNontrivial
    have hsub : Subsingleton ↥H₀ := by
      rw [h0]
      exact inferInstance
    have : Subsingleton (↥H₀ ⧸ N) := (QuotientGroup.mk'_surjective N).subsingleton
    exact not_subsingleton _ this
  have hH0c : H₀ ∈ cComp H₀ := by
    refine S151S9U.mem_cComp_self_of_simple_quotient (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) hH0ne hperf ?_
    rw [QuotientGroup.ker_mk']
    have : Group.IsNilpotent ↥N := hN2.isNilpotent
    infer_instance
  have hPerf : S151S9U.PerfCore (((R ⊓ L).subgroupOf L).map θ) ((Y.subgroupOf L).map θ) := by
    rw [hθS, hYmap, S151S9U.PerfCore, perfectCore_eq_self_of_perfect hperf]
    exact ⟨hH0ne, hH0c, sup_eq_left.2 hSH⟩
  obtain ⟨hKne, hKc, hKsup⟩ := S151S9U.perfCore_lift θ hkerZ hker2 hYL hSLY hS hPerf
  set K : Subgroup G := perfectCore Y with hKdef
  have hKY : K ≤ Y := perfectCore_le Y
  have hKL : K ≤ L := hKY.trans hYL
  have hKR : R ≤ Subgroup.normalizer (K : Set G) :=
    hθN.trans (normalizer_le_normalizer_perfectCore Y)
  have hKperf : ⁅K, K⁆ = K := perfectCore_perfect Y
  have hMY : (Y.subgroupOf L).map L.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYL
  have hKmap : K = (perfectCore (Y.subgroupOf L)).map L.subtype := by
    rw [hKdef, map_perfectCore, hMY]
  have hK' : K.subgroupOf L = perfectCore (Y.subgroupOf L) := by
    rw [hKmap]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hθK : (K.subgroupOf L).map θ = H₀ := by
    rw [hK', map_perfectCore, hYmap, perfectCore_eq_self_of_perfect hperf]
  let φ₀ : ↥K →* X := θ.comp (Subgroup.inclusion hKL)
  have hφ₀range : φ₀.range = H₀ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, hθK]
  have hφ₀mem : ∀ x, φ₀ x ∈ H₀ := fun x => hφ₀range ▸ MonoidHom.mem_range.2 ⟨x, rfl⟩
  let φ : ↥K →* ↥H₀ := φ₀.codRestrict H₀ hφ₀mem
  have hφs : Function.Surjective φ := by
    rintro ⟨h, hh⟩
    have : h ∈ φ₀.range := hφ₀range ▸ hh
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 this
    exact ⟨x, Subtype.ext hx⟩
  have hφk : IsPGroup 2 ↥φ.ker := by
    have hker0 : φ.ker = θ.ker.comap (Subgroup.inclusion hKL) := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_comap, φ, φ₀, MonoidHom.codRestrict_apply,
        MonoidHom.comp_apply, Subtype.ext_iff, OneMemClass.coe_one]
    rw [hker0]
    exact hker2.comap_of_injective _ (Subgroup.inclusion_injective hKL)
  obtain ⟨hchar, -⟩ := hgood G K φ hφs hφk
  let ψ : ↥K →* (↥H₀ ⧸ N) := (QuotientGroup.mk' N).comp φ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective N).comp hφs
  have hψker : ψ.ker = N.comap φ := by
    have h1 := MonoidHom.comap_ker (QuotientGroup.mk' N) φ
    rw [QuotientGroup.ker_mk'] at h1
    exact h1.symm
  have hψ2 : IsPGroup 2 ↥ψ.ker := by
    rw [hψker]
    exact hN2.comap_of_ker_isPGroup φ hφk
  have hnot2 : ¬ IsPGroup 2 (↥H₀ ⧸ N) := by
    intro h2
    have hP : Group.IsPerfect ↥H₀ := Subgroup.isPerfect_iff.2 hperf
    have hPq : Group.IsPerfect (↥H₀ ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    have : Nontrivial (↥H₀ ⧸ N) := hNsimple.toNontrivial
    have : Group.IsNilpotent (↥H₀ ⧸ N) := h2.isNilpotent
    exact Group.IsPerfect.not_isSolvable (↥H₀ ⧸ N) inferInstance
  have hpc : CFSG.pCore 2 ↥K = ψ.ker := by
    refine le_antisymm ?_ (le_sSup ⟨ψ.normal_ker, hψ2⟩)
    have hn : ((CFSG.pCore 2 ↥K).map ψ).Normal := CFSG.pCore_normal.map ψ hψs
    rcases hNsimple.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥K).map ψ) with h0 | htop
    · exact (Subgroup.map_eq_bot_iff _).1 h0
    · exfalso
      apply hnot2
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥K).map ψ) := CFSG.pCore_isPGroup.map ψ
      rw [htop] at hp
      exact hp.of_equiv Subgroup.topEquiv
  have hquot : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥H₀ ⧸ N)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩
  have hodd : ¬ 2 ∣ (R.subgroupOf (K ⊔ R)).index := by
    have h1 : IsSylowTwoOf R (L ⊔ R) := Lin2.isSylowTwoOf_sup_of_inf_aux hR2 hRN hS
    have h2 : IsSylowTwoOf R (K ⊔ R) :=
      A4.isSylowTwoOf_mono h1 le_sup_right (sup_le_sup_right hKL R)
    exact h2.2.2
  obtain ⟨hWle, hWne, hCpre⟩ := S151S9U.central_quotient_centralizer hS θ hθ hkerZ hker2 hne
    (W := (centerOf ((R ⊓ L).subgroupOf L)).map θ) rfl
  have hWle' : (centerOf ((R ⊓ L).subgroupOf L)).map θ ≤ centerOf S₀ := by
    rw [hθS] at hWle
    exact hWle
  have hnotle : ¬ Subgroup.centralizer (((centerOf ((R ⊓ L).subgroupOf L)).map θ : Subgroup X) :
      Set X) ≤ H₀ := hgen _ hWle' hWne
  have hsup : H₀ ⊔ Subgroup.centralizer (((centerOf ((R ⊓ L).subgroupOf L)).map θ : Subgroup X) :
      Set X) = ⊤ :=
    codisjoint_iff.1 (hcoat.not_le_iff_codisjoint.1 hnotle)
  have hCL : L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G) ≤ L := inf_le_left
  have hCmap : ((L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G)).subgroupOf L).map θ =
      Subgroup.centralizer (((centerOf ((R ⊓ L).subgroupOf L)).map θ : Subgroup X) : Set X) := by
    rw [hCpre]
    exact Subgroup.map_comap_eq_self_of_surjective hθ _
  have hD : ((K.subgroupOf L) ⊔
      (L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G)).subgroupOf L).map θ = ⊤ := by
    rw [Subgroup.map_sup, hθK, hCmap, hsup]
  have hDker : ((K.subgroupOf L) ⊔
      (L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G)).subgroupOf L) ⊔ θ.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hD, Subgroup.comap_top]
  have hDtop : (K.subgroupOf L) ⊔
      (L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G)).subgroupOf L = ⊤ :=
    eq_top_of_sup_central (Subgroup.isPerfect_iff.2 hLperf).commutator_eq_top hkerZ hDker
  have hKC : K ⊔ (L ⊓ Subgroup.centralizer (centerOf (R ⊓ L) : Set G)) = L := by
    have h1 := congrArg (Subgroup.map L.subtype) hDtop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hCL, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  exact ⟨K, hKL, hKperf, hKR, mem_cComp_sup_of_normalizes hKc hKR, hodd, hchar, hquot, hKC⟩

end CFSG.Quasithin.J4Local
