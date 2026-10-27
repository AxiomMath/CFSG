module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameO
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Lift
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open

open scoped commutatorElement

section LiftO

variable {X Y : Type} [Group X] [Group Y] {G₀ B : Subgroup X} (fr : GGTCUFrameO G₀ B Y)

@[expose] noncomputable def GGTCUFrameO.langHom : ↥G₀ →* Y :=
  fr.Θ.comp (QuotientGroup.mk' (Subgroup.center ↥G₀))

theorem GGTCUFrameO.langHom_ker (g : ↥G₀) (hg : fr.langHom g = 1) :
    g ∈ Subgroup.center ↥G₀ := by
  have h0 : fr.Θ (QuotientGroup.mk g) = 1 := by
    simpa [GGTCUFrameO.langHom] using hg
  have h1 : (QuotientGroup.mk g : ↥G₀ ⧸ Subgroup.center ↥G₀) = 1 :=
    fr.Θinj (by simpa using h0)
  exact (QuotientGroup.eq_one_iff g).mp h1

theorem GGTCUFrameO.range_langHom : fr.langHom.range = fr.Θ.range := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk' (Subgroup.center ↥G₀) g, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q
    exact ⟨g, by simpa [GGTCUFrameO.langHom] using congrArg fr.Θ (by simpa using hg)⟩

private theorem w5L_commutator_mem_center_of_lang_commute
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    {D₁ : Subgroup X} (hD : D₁ ≤ B) {K : Subgroup X} (hKG : K ≤ G₀)
    (hcomm : fr.JimgO K ≤
      Subgroup.centralizer ((fr.DimgO D₁ : Subgroup Y) : Set Y)) :
    ∀ d ∈ D₁, ∀ k ∈ K,
      d * k * d⁻¹ * k⁻¹ ∈ (Subgroup.center ↥G₀).map G₀.subtype := by
  intro d hd k hk
  set b : ↥B := ⟨d, hD hd⟩ with hb
  set kG : ↥G₀ := ⟨k, hKG hk⟩ with hkG
  have hKmem : fr.Θ (QuotientGroup.mk kG) ∈ fr.JimgO K :=
    ⟨_, ⟨kG, Subgroup.mem_subgroupOf.2 hk, rfl⟩, rfl⟩
  have hDmem : fr.ν b ∈ fr.DimgO D₁ :=
    ⟨b, Subgroup.mem_subgroupOf.2 hd, rfl⟩
  have hcen := Subgroup.mem_centralizer_iff.1 (hcomm hKmem) (fr.ν b) hDmem
  set dk : ↥G₀ := ⟨d * k * d⁻¹, GGTCUFrameO.mem_conj_of_normalizer hBN b kG⟩ with hdk
  have hact := fr.act b kG dk rfl
  have hΘ : fr.Θ (QuotientGroup.mk dk) = fr.Θ (QuotientGroup.mk kG) := by
    rw [hact, hcen, mul_inv_cancel_right]
  have hmk : (QuotientGroup.mk dk : ↥G₀ ⧸ Subgroup.center ↥G₀) =
      QuotientGroup.mk kG := fr.Θinj hΘ
  have hc : kG⁻¹ * dk ∈ Subgroup.center ↥G₀ := QuotientGroup.eq.1 hmk.symm
  refine ⟨kG⁻¹ * dk, hc, ?_⟩
  have h1 : d * k * d⁻¹ = k * ((kG⁻¹ * dk : ↥G₀) : X) := by
    simp [dk, kG, Subgroup.coe_mul]
  have h2 : ((kG⁻¹ * dk : ↥G₀) : X) * k = k * ((kG⁻¹ * dk : ↥G₀) : X) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hc kG).symm
  show ((kG⁻¹ * dk : ↥G₀) : X) = d * k * d⁻¹ * k⁻¹
  rw [h1, ← h2]
  group

private theorem w5L_le_centralizer_of_lang_centralizer
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    {D₁ : Subgroup X} (hD : D₁ ≤ B) {K : Subgroup X} (hKG : K ≤ G₀)
    (hKperf : commutator ↥K = ⊤)
    (hcomm : fr.JimgO K ≤
      Subgroup.centralizer ((fr.DimgO D₁ : Subgroup Y) : Set Y)) :
    K ≤ Subgroup.centralizer (D₁ : Set X) := by
  have hZ := w5L_commutator_mem_center_of_lang_commute fr hBN hD hKG hcomm
  have hZJ : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype,
      ∀ j ∈ K, z * j = j * z := by
    rintro _ ⟨c, hc, rfl⟩ j hj
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨j, hKG hj⟩)).symm
  have hZZ : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype,
      ∀ z' ∈ (Subgroup.center ↥G₀).map G₀.subtype, z * z' = z' * z := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc c')).symm
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact commute_of_central_commutator' hKperf hZJ hZZ (hZ d hd) k hk

theorem GGTCUFrameO.exists_component_lift (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    {D₁ : Subgroup X} (hD : D₁ ≤ B) {Kt : Subgroup Y}
    (hK : IsComponentOf Kt (fr.Θ.range ⊓ Subgroup.centralizer (fr.DimgO D₁ : Set Y))) :
    ∃ K : Subgroup X, K ≤ G₀ ∧
      IsComponentOf K (G₀ ⊓ Subgroup.centralizer (D₁ : Set X)) ∧ fr.JimgO K = Kt := by
  classical
  set ψ := fr.langHom with hψ
  set C : Subgroup ↥G₀ :=
    (fr.Θ.range ⊓ Subgroup.centralizer (fr.DimgO D₁ : Set Y)).comap ψ with hC
  have hCmap : C.map ψ = fr.Θ.range ⊓ Subgroup.centralizer (fr.DimgO D₁ : Set Y) := by
    rw [hC, Subgroup.map_comap_eq, hψ, fr.range_langHom]
    exact inf_of_le_right inf_le_left
  have hKb : IsComponentOf Kt (C.map ψ) := by rw [hCmap]; exact hK
  obtain ⟨K₀, hK₀, hK₀map⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift ψ fr.langHom_ker hKb
  set K : Subgroup X := K₀.map G₀.subtype with hKdef
  have hKG : K ≤ G₀ := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hKsub : K.subgroupOf G₀ = K₀ := by
    ext g
    simp only [Subgroup.mem_subgroupOf, hKdef, Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, hhg⟩
      exact (Subtype.ext hhg : h = g) ▸ hh
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hJL : fr.JimgO K = Kt := by
    unfold GGTCUFrameO.JimgO
    rw [hKsub, Subgroup.map_map]
    exact hK₀map
  have hKperf : commutator ↥K = ⊤ := by
    have e : ↥K₀ ≃* ↥K := Subgroup.equivMapOfInjective K₀ G₀.subtype Subtype.val_injective
    have hp0 : Group.IsPerfect ↥K₀ := Group.isPerfect_def.mpr hK₀.2.2.1
    exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have hKcomm : fr.JimgO K ≤
      Subgroup.centralizer ((fr.DimgO D₁ : Subgroup Y) : Set Y) := by
    rw [hJL]
    exact fun y hy => (hK.1 hy).2
  have hKd : K ≤ Subgroup.centralizer (D₁ : Set X) :=
    w5L_le_centralizer_of_lang_centralizer fr hBN hD hKG hKperf hKcomm
  set C₂ : Subgroup ↥G₀ := (Subgroup.centralizer (D₁ : Set X)).comap G₀.subtype with hC₂
  have hC₂C : C₂ ≤ C := by
    intro g hg
    rw [hC, Subgroup.mem_comap]
    refine ⟨?_, Subgroup.mem_centralizer_iff.2 ?_⟩
    · exact MonoidHom.mem_range.2 ⟨QuotientGroup.mk g, rfl⟩
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hdg : (b : X) * (g : X) = (g : X) * (b : X) :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hg) (b : X)
        (Subgroup.mem_subgroupOf.1 hb)
    set dg : ↥G₀ := ⟨(b : X) * (g : X) * (b : X)⁻¹,
      GGTCUFrameO.mem_conj_of_normalizer hBN b g⟩ with hdgdef
    have hact := fr.act b g dg rfl
    have hdg_eq : dg = g := by
      apply Subtype.ext
      dsimp only [dg]
      rw [hdg, mul_inv_cancel_right]
    rw [hdg_eq] at hact
    rw [eq_mul_inv_iff_mul_eq] at hact
    exact hact.symm
  have hK₀C₂ : K₀ ≤ C₂ := fun k hk => hKd ⟨k, hk, rfl⟩
  have hK₀' : IsComponentOf K₀ C₂ :=
    CFSG.Assembly.isComponentOf_iff_open.1
      (CFSG.Assembly.IsComponentOf.of_le_of_le (CFSG.Assembly.isComponentOf_iff_open.2 hK₀)
        hK₀C₂ hC₂C)
  obtain ⟨-, hsub, hq⟩ := hK₀'
  have hmapC₂ : C₂.map G₀.subtype = G₀ ⊓ Subgroup.centralizer (D₁ : Set X) := by
    rw [hC₂, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  refine ⟨K, hKG, ⟨le_inf hKG hKd, ?_, ?_⟩, hJL⟩
  · have h := CFSG.Open.IsSubnormal.map G₀.subtype hsub
    rwa [hmapC₂] at h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.equivMapOfInjective K₀ G₀.subtype Subtype.val_injective).symm hq

@[expose] noncomputable def GGTCUFrameO.restrictJ {K : Subgroup X} (hKG : K ≤ G₀) :
    ↥K →* ↥(fr.JimgO K) :=
  MonoidHom.codRestrict (fr.langHom.comp (Subgroup.inclusion hKG)) (fr.JimgO K)
    fun k => ⟨QuotientGroup.mk' (Subgroup.center ↥G₀) ⟨k, hKG k.2⟩,
      ⟨⟨k, hKG k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩, rfl⟩

theorem GGTCUFrameO.restrictJ_apply {K : Subgroup X} (hKG : K ≤ G₀) (k : ↥K) :
    ((fr.restrictJ hKG k : ↥(fr.JimgO K)) : Y) = fr.langHom ⟨k, hKG k.2⟩ :=
  rfl

private theorem w5L_restrictJ_surjective {K : Subgroup X} (hKG : K ≤ G₀) :
    Function.Surjective (fr.restrictJ hKG) := by
  rintro ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩⟩
  exact ⟨⟨(g : X), Subgroup.mem_subgroupOf.1 hg⟩, Subtype.ext rfl⟩

private theorem w5L_restrictJ_ker {K : Subgroup X} (hKG : K ≤ G₀) :
    (fr.restrictJ hKG).ker ≤ Subgroup.center ↥K := by
  intro k hk
  have h1 : fr.langHom ⟨k, hKG k.2⟩ = 1 := by
    have h0 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
    simpa [GGTCUFrameO.restrictJ_apply] using h0
  have h2 := fr.langHom_ker ⟨k, hKG k.2⟩ h1
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro g
  have h3 := congrArg Subtype.val (h2 ⟨g, hKG g.2⟩)
  apply Subtype.ext
  simpa using h3

theorem GGTCUFrameO.exists_centerQuotEquivO {K : Subgroup X} (hKG : K ≤ G₀)
    (hKperf : commutator ↥K = ⊤) :
    ∃ e : ↥K ⧸ Subgroup.center ↥K ≃* ↥(fr.JimgO K) ⧸ Subgroup.center ↥(fr.JimgO K),
      ∀ k : ↥K, e (QuotientGroup.mk k) = QuotientGroup.mk (fr.restrictJ hKG k) := by
  have hP : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKperf
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect hP (fr.restrictJ hKG)
    (w5L_restrictJ_surjective fr hKG) (w5L_restrictJ_ker fr hKG)
  let g : ↥K ⧸ Subgroup.center ↥K →* ↥(fr.JimgO K) ⧸ Subgroup.center ↥(fr.JimgO K) :=
    QuotientGroup.map _ _ (fr.restrictJ hKG) hc.ge
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : fr.restrictJ hKG k ∈ Subgroup.center ↥(fr.JimgO K) :=
      (QuotientGroup.eq_one_iff _).1 hq
    have hk : k ∈ Subgroup.center ↥K := by
      rw [← hc]
      exact h1
    exact (QuotientGroup.eq_one_iff k).2 hk
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, rfl⟩ := w5L_restrictJ_surjective fr hKG y
    exact ⟨QuotientGroup.mk k, rfl⟩
  exact ⟨MulEquiv.ofBijective g ⟨hinj, hsurj⟩, fun k => rfl⟩

theorem GGTCUFrameO.langHom_conj (b : ↥B) {l l' : ↥G₀}
    (h : (l' : X) = (b : X)⁻¹ * l * b) :
    fr.langHom l' = (fr.ν b)⁻¹ * fr.langHom l * fr.ν b := by
  have hl : (l : X) = (b : X) * (l' : X) * (b : X)⁻¹ := by
    rw [h]; group
  have hact := fr.act b l' l hl
  have hact' : fr.Θ (QuotientGroup.mk' (Subgroup.center ↥G₀) l) =
      fr.ν b * fr.Θ (QuotientGroup.mk' (Subgroup.center ↥G₀) l') * (fr.ν b)⁻¹ := hact
  change fr.Θ (QuotientGroup.mk' (Subgroup.center ↥G₀) l') =
    (fr.ν b)⁻¹ * fr.Θ (QuotientGroup.mk' (Subgroup.center ↥G₀) l) * fr.ν b
  rw [hact']
  group

theorem GGTCUFrameO.ggInnerDiagOn_of_lang [Finite X] {x : X} (hx : x ∈ B) {K : Subgroup X}
    (hKG : K ≤ G₀) (hKperf : commutator ↥K = ⊤)
    (hKnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set X))
    (h : GGInnerDiagOn (Subgroup.zpowers (fr.ν ⟨x, hx⟩)) (fr.JimgO K)) :
    GGInnerDiagOn (Subgroup.zpowers x) K := by
  obtain ⟨e, he⟩ := fr.exists_centerQuotEquivO hKG hKperf
  unfold GGInnerDiagOn at h ⊢
  obtain ⟨-, lab, hΛ, hraw⟩ := h
  refine ⟨hKperf, lab, hΛ, ?_⟩
  refine CFSG.StandardType.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨hsimple, hnonab, θ, hnorm, hind⟩
  refine ⟨hsimple, hnonab, e.trans θ, hKnorm, ?_⟩
  intro b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  obtain ⟨φ, hφI, hφ⟩ := hind (fr.ν ⟨x, hx⟩ ^ m) (Subgroup.zpow_mem_zpowers _ m)
  refine ⟨φ, hφI, ?_⟩
  intro l l' hrel
  show φ (θ (e (QuotientGroup.mk l))) = θ (e (QuotientGroup.mk l'))
  rw [he l, he l']
  apply hφ
  have hxm : x ^ m ∈ B := zpow_mem hx m
  have hconj := fr.langHom_conj ⟨x ^ m, hxm⟩ (l := ⟨l, hKG l.2⟩) (l' := ⟨l', hKG l'.2⟩)
    (by simpa using hrel)
  have hlang : fr.ν ⟨x ^ m, hxm⟩ = fr.ν ⟨x, hx⟩ ^ m := by
    have h := map_zpow fr.ν (⟨x, hx⟩ : ↥B) m
    exact h
  rw [GGTCUFrameO.restrictJ_apply, GGTCUFrameO.restrictJ_apply, hconj, hlang]

theorem GGTCUFrameO.zpowers_le_normalizer (hBN : B ≤ Subgroup.normalizer (G₀ : Set X)) {x : X}
    (hx : x ∈ B) {K : Subgroup X} (hKG : K ≤ G₀) (hKperf : commutator ↥K = ⊤)
    (hnorm : Subgroup.zpowers (fr.ν ⟨x, hx⟩) ≤
      Subgroup.normalizer ((fr.JimgO K : Subgroup Y) : Set Y)) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set X) := by
  have core : ∀ b : ↥B,
      fr.ν b ∈ Subgroup.normalizer ((fr.JimgO K : Subgroup Y) : Set Y) →
      ∀ k ∈ K, (b : X) * k * (b : X)⁻¹ ∈ K := by
    intro b hb k hk
    let φ : ↥G₀ →* ↥G₀ := MonoidHom.codRestrict
      ((MulAut.conj (b : X)).toMonoidHom.comp G₀.subtype) G₀
      (fun y => GGTCUFrameO.mem_conj_of_normalizer hBN b y)
    set K₀ : Subgroup ↥G₀ := K.subgroupOf G₀ with hK₀
    have hperfK : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKperf
    have hperf0 : Group.IsPerfect ↥K₀ :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKG).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKG).symm.surjective
    have hP : ⁅K₀.map φ, K₀.map φ⁆ = K₀.map φ := by
      rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hperf0]
    have hle : K₀.map φ ≤ K₀ ⊔ Subgroup.center ↥G₀ := by
      rintro _ ⟨k', hk', rfl⟩
      have hψk' : fr.langHom k' ∈ fr.JimgO K :=
        ⟨_, ⟨k', hk', rfl⟩, rfl⟩
      have hconj : fr.langHom (φ k') = fr.ν b * fr.langHom k' * (fr.ν b)⁻¹ :=
        fr.act b k' (φ k') rfl
      have hmem : fr.langHom (φ k') ∈ fr.JimgO K := by
        rw [hconj]
        exact (Subgroup.mem_normalizer_iff.1 hb (fr.langHom k')).1 hψk'
      obtain ⟨_, ⟨k₀, hk₀, rfl⟩, hq⟩ := hmem
      refine Subgroup.mem_sup_of_normal_right.2 ⟨k₀, hk₀,
        k₀⁻¹ * φ k', ?_, by simp⟩
      refine fr.langHom_ker _ ?_
      rw [map_mul, map_inv]
      have hq' : fr.langHom k₀ = fr.langHom (φ k') := hq
      rw [hq', inv_mul_cancel]
    have hPK := perfect_le_of_le_sup_center hP hle
    have hk₁ : φ (⟨k, hKG hk⟩ : ↥G₀) ∈ K₀ :=
      hPK ⟨⟨k, hKG hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
    have hkX : ((φ (⟨k, hKG hk⟩ : ↥G₀)) : X) ∈ K := Subgroup.mem_subgroupOf.1 hk₁
    have hval : ((φ (⟨k, hKG hk⟩ : ↥G₀)) : X) = (b : X) * k * (b : X)⁻¹ := rfl
    rwa [hval] at hkX
  intro b hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hB : ∀ m : ℤ, x ^ m ∈ B := fun m => zpow_mem hx m
  have hlang : ∀ m : ℤ, fr.ν ⟨x ^ m, hB m⟩ = fr.ν ⟨x, hx⟩ ^ m := fun m =>
    map_zpow fr.ν (⟨x, hx⟩ : ↥B) m
  have hnm : ∀ m : ℤ, fr.ν ⟨x ^ m, hB m⟩ ∈
      Subgroup.normalizer ((fr.JimgO K : Subgroup Y) : Set Y) := fun m => by
    rw [hlang]
    exact hnorm (Subgroup.zpow_mem_zpowers _ m)
  constructor
  · intro hh
    exact core ⟨x ^ m, hB m⟩ (hnm m) h hh
  · intro hh
    have hres := core ⟨x ^ (-m), hB (-m)⟩ (hnm (-m)) _ hh
    simpa [zpow_neg, mul_assoc] using hres

end LiftO

end CFSG.StandardType.TableCRes

end
