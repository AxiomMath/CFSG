module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoComp
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoGen
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyA11NbrOn
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggTorusRootGenAvoidKG_ggSL9 :
    GGTorusRootGenAvoidKG 7 3 (GGSL9V ≃ₗ[ZMod 2] GGSL9V)
      (Set.range (MulAut.conj :
        (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _ _
  let e0 : (GGSL9V ≃ₗ[ZMod 2] GGSL9V) ≃* projectiveSL 9 (ZMod 2) :=
    (ggSL9ProjEquiv (K := ZMod 2) (Nat.card_zmod 2)).symm
  have hψinj : Function.Injective ψ := by
    obtain ⟨φ, hφs, hφker⟩ :=
      TypeA.exists_sl_cover (TypeA.slHasSections_of_five_le (d := 9) (K := ZMod 2) (by norm_num))
        (e0.toMonoidHom.comp ψ) (e0.surjective.comp hψ)
        (by
          intro l hl
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hl
          exact hker (MonoidHom.mem_ker.mpr (e0.injective (by
            rw [show e0 (ψ l) = 1 from hl, map_one]))))
        hperf
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    obtain ⟨g, rfl⟩ := hφs l
    rw [Subgroup.mem_bot]
    have h1 : ψ (φ g) = 1 := MonoidHom.mem_ker.mp hl
    have h2 : proj 9 (ZMod 2) g = 1 := by
      rw [← hφker g, MonoidHom.comp_apply, h1, map_one]
    have h3 : g = 1 :=
      proj_nine_injective_of_card_two (K := ZMod 2) (Nat.card_zmod 2) (by rw [h2, map_one])
    rw [h3, map_one]
  let Ψ : L' ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩
  have hψsymm : ∀ x : GGSL9V ≃ₗ[ZMod 2] GGSL9V, ψ (Ψ.symm x) = x :=
    fun x => MulEquiv.apply_symm_apply Ψ x
  let Λ : (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut L' :=
    (MulAut.conj : L' →* MulAut L').comp Ψ.symm.toMonoidHom
  have hΛinj : Function.Injective Λ := by
    intro e₁ e₂ h
    have h1 : MulAut.conj (Ψ.symm e₁) = MulAut.conj (Ψ.symm e₂) := h
    have h2 := ReflInner.map_eq_of_conj_eq hψ center_ggSL9_eq_bot h1
    simpa only [hψsymm] using h2
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [show (Λ e) l = MulAut.conj (Ψ.symm e) l from rfl, MulAut.conj_apply, map_mul, map_mul,
      map_inv, hψsymm e, ← hφ l, MulAut.conj_apply]
  set E : Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from by rw [he]; exact a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian 7 E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  obtain ⟨g, hgE⟩ := exists_conj_eq_ggSL9Torus hEab (by rw [hcardE]; exact hr)
  have hcardA : Nat.card A = 7 ^ 3 := by
    rw [← hcardE, hgE, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      card_ggSL9Torus]
  let Φ : (GGSL9V ≃ₗ[ZMod 2] GGSL9V) ≃* L' := (MulAut.conj g).trans Ψ.symm
  have hψΦ : ∀ x : GGSL9V ≃ₗ[ZMod 2] GGSL9V, ψ (Φ x) = MulAut.conj g x :=
    fun x => hψsymm (MulAut.conj g x)
  let σ : Multiplicative (Fin 3 → ZMod 7) →* L' := Φ.toMonoidHom.comp ggSL9TorusCoord
  have hψσ : ∀ f, ψ (σ f) = MulAut.conj g (ggSL9TorusCoord f) :=
    fun f => hψΦ (ggSL9TorusCoord f)
  have hconj_inj : Function.Injective (MulAut.conj : L' →* MulAut L') :=
    fun x y h => hψinj (ReflInner.map_eq_of_conj_eq hψ center_ggSL9_eq_bot h)
  have hσmem : ∀ f, (MulAut.conj (σ f) : MulAut L') ∈ A := by
    intro f
    have hmemE : MulAut.conj g (ggSL9TorusCoord f) ∈ E := by
      rw [hgE]
      refine Subgroup.mem_map_of_mem _ ?_
      rw [← range_ggSL9TorusCoord]
      exact ⟨f, rfl⟩
    rw [hE] at hmemE
    exact hmemE
  let Θ₀ : Multiplicative (Fin 3 → ZMod 7) →* ↥A :=
    ((MulAut.conj : L' →* MulAut L').comp σ).codRestrict A hσmem
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => ?_, fun a => ?_⟩
    · have h1 : MulAut.conj (σ f) = MulAut.conj (σ g) := congrArg Subtype.val hfg
      exact ggSL9TorusCoord_injective (Φ.injective (hconj_inj h1))
    · obtain ⟨e, he⟩ := hAΛ a a.2
      have heE : e ∈ E := by
        rw [hE]
        change Λ e ∈ A
        rw [he]
        exact a.2
      rw [hgE] at heE
      obtain ⟨x, hxT, hxe⟩ := Subgroup.mem_map.mp heE
      obtain ⟨f, hf⟩ := (show x ∈ ggSL9TorusCoord.range from by
        rw [range_ggSL9TorusCoord]; exact hxT)
      refine ⟨f, Subtype.ext ?_⟩
      show MulAut.conj (σ f) = a
      rw [← he, ← hxe, ← hf]
      rfl
  let Θ : Multiplicative (Fin 3 → ZMod 7) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f => rfl
  intro ρ
  let wOf (t : Fin 3 × Fin 3 × ZMod 3) (ht : t ∈ GGSL9Refl) :
      GGSL9V ≃ₗ[ZMod 2] GGSL9V := ggSL9W t.1 t.2.1 ht.ne t.2.2
  let sOf (t : Fin 3 × Fin 3 × ZMod 3) (ht : t ∈ GGSL9Refl) :
      MulAut (Multiplicative (Fin 3 → ZMod 7)) := ggSL9WCoord t.1 t.2.1 ht.ne t.2.2
  let nOf (t : Fin 3 × Fin 3 × ZMod 3) (ht : t ∈ GGSL9Refl) : L' := Φ (wOf t ht)
  have hreflect_congr : ∀ (t : Fin 3 × Fin 3 × ZMod 3) (ht : t ∈ GGSL9Refl),
      GGIsReflection 7 (MulAut.congr Θ (sOf t ht)) := by
    intro t ht
    have hsq : MulAut.congr Θ (sOf t ht) * MulAut.congr Θ (sOf t ht) = 1 := by
      rw [← map_mul, ggSL9WCoord_mul_self, map_one]
    refine ⟨hsq, ?_⟩
    have hfix : Nat.card {b : ↥A // MulAut.congr Θ (sOf t ht) b = b} =
        Nat.card {f : Multiplicative (Fin 3 → ZMod 7) // sOf t ht f = f} := by
      refine Nat.card_congr (Equiv.subtypeEquiv Θ.symm.toEquiv fun b => ?_)
      rw [MulAut.congr_apply]
      show Θ (sOf t ht (Θ.symm b)) = b ↔ sOf t ht (Θ.symm b) = Θ.symm b
      constructor
      · intro hb
        have h1 := congrArg Θ.symm hb
        rwa [MulEquiv.symm_apply_apply] at h1
      · intro hb
        rw [hb, MulEquiv.apply_symm_apply]
    rw [hfix, card_fix_ggSL9WCoord ht.ne t.2.2, hcardA]
    norm_num
  have hkey : ∀ (t : Fin 3 × Fin 3 × ZMod 3) (ht : t ∈ GGSL9Refl),
      ∃ (hn : MulAut.conj (nOf t ht) ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGTorusWeylElt 7 A (nOf t ht) ∧ GGIsReflection 7 (ggConjAut A hn) ∧
          ggConjAut A hn = MulAut.congr Θ (sOf t ht) := by
    intro t ht
    have hs : ∀ f, ψ (nOf t ht) * ψ (σ f) * (ψ (nOf t ht))⁻¹ = ψ (σ (sOf t ht f)) := by
      intro f
      rw [hψΦ (wOf t ht), hψσ f, hψσ (sOf t ht f)]
      simp only [MulAut.conj_apply]
      rw [show g * ggSL9TorusCoord (sOf t ht f) * g⁻¹ =
          g * (wOf t ht * ggSL9TorusCoord f * (wOf t ht)⁻¹) * g⁻¹ from by
        rw [ggSL9W_conj_torusCoord]]
      group
    obtain ⟨hn, heq⟩ := exists_ggConjAut_eq_congr hker Θ hΘval
      (n := nOf t ht) (s := sOf t ht) hs
    have hweyl : GGTorusWeylElt 7 A (nOf t ht) :=
      ggTorusWeylElt_of_model (p := 7) (k := 3) hker Θ hΘval (n := nOf t ht)
        (fun f => ⟨sOf t ht f, hs f⟩)
    have hreflect : GGIsReflection 7 (ggConjAut A hn) := by
      rw [heq]
      exact hreflect_congr t ht
    exact ⟨hn, hweyl, hreflect, heq⟩
  have huniq : ∀ t u : {t : Fin 3 × Fin 3 × ZMod 3 // t ∈ GGSL9Refl},
      ggConjAut A ((hkey t.1 t.2).choose) = ggConjAut A ((hkey u.1 u.2).choose) → t = u := by
    intro t u h
    have ht := (hkey t.1 t.2).choose_spec.2.2
    have hu := (hkey u.1 u.2).choose_spec.2.2
    have h1 : MulAut.congr Θ (sOf t.1 t.2) = MulAut.congr Θ (sOf u.1 u.2) := by
      rw [← ht, ← hu]
      exact h
    have h2 : sOf t.1 t.2 = sOf u.1 u.2 := (MulAut.congr Θ).injective h1
    have h3 := ggSL9WCoord_inj t.2 u.2 h2
    apply Subtype.ext
    exact Prod.ext h3.1 (Prod.ext h3.2.1 h3.2.2)
  set ρ₀ : Fin 3 × Fin 3 × ZMod 3 :=
    if h : ∃ t : {t : Fin 3 × Fin 3 × ZMod 3 // t ∈ GGSL9Refl},
        ggConjAut A ((hkey t.1 t.2).choose) = ρ
    then (Classical.choose h).1 else (0, 0, 0) with hρ₀def
  have hρ₀ : ∀ t : {t : Fin 3 × Fin 3 × ZMod 3 // t ∈ GGSL9Refl},
      ggConjAut A ((hkey t.1 t.2).choose) = ρ → t.1 = ρ₀ := by
    intro t ht
    have hex : ∃ u : {t : Fin 3 × Fin 3 × ZMod 3 // t ∈ GGSL9Refl},
        ggConjAut A ((hkey u.1 u.2).choose) = ρ := ⟨t, ht⟩
    have hspec := Classical.choose_spec hex
    have huu : t = Classical.choose hex := huniq t (Classical.choose hex) (ht.trans hspec.symm)
    rw [hρ₀def, dif_pos hex]
    exact congrArg Subtype.val huu
  have hhyp : ∀ (t : Fin 3 × Fin 3 × ZMod 3) (ht : t ∈ GGSL9Refl),
      ggHypCent A (nOf t ht) = (Subgroup.centralizer
        {x : GGSL9V ≃ₗ[ZMod 2] GGSL9V | x ∈ ggSL9Torus ∧
          wOf t ht * x = x * wOf t ht}).map Φ.toMonoidHom := by
    intro t ht
    have hwcomm : ∀ f, (MulAut.conj (nOf t ht) * Θ f = Θ f * MulAut.conj (nOf t ht)) ↔
        (wOf t ht * ggSL9TorusCoord f = ggSL9TorusCoord f * wOf t ht) := by
      intro f
      rw [hΘval f]
      constructor
      · intro h
        have h' : MulAut.conj (nOf t ht * σ f) = MulAut.conj (σ f * nOf t ht) := by
          simpa only [map_mul] using h
        have h2 : nOf t ht * σ f = σ f * nOf t ht := hconj_inj h'
        exact Φ.injective (by rw [map_mul, map_mul]; exact h2)
      · intro h
        have h1 : nOf t ht * σ f = σ f * nOf t ht := by
          change Φ (wOf t ht) * Φ (ggSL9TorusCoord f) =
            Φ (ggSL9TorusCoord f) * Φ (wOf t ht)
          rw [← map_mul, ← map_mul]
          exact congrArg Φ h
        rw [← map_mul, ← map_mul]
        exact congrArg MulAut.conj h1
    have hmem : ∀ l : L', l ∈ ggHypCent A (nOf t ht) ↔
        ∀ f, wOf t ht * ggSL9TorusCoord f = ggSL9TorusCoord f * wOf t ht →
          σ f * l = l * σ f := by
      intro l
      rw [ggHypCent]
      simp only [Subgroup.mem_iInf, mem_ggFix]
      constructor
      · intro hl f hf
        have h1 : ((Θ f : ↥A) : MulAut L') l = l :=
          hl ((Θ f : ↥A) : MulAut L') ⟨(Θ f).2, (hwcomm f).mpr hf⟩
        rw [hΘval f, MulAut.conj_apply] at h1
        calc σ f * l = (σ f * l * (σ f)⁻¹) * σ f := by group
          _ = l * σ f := by rw [h1]
      · intro hl a ha
        obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha.1⟩
        have hae : ((Θ f : ↥A) : MulAut L') = a := congrArg Subtype.val hf
        have hcomm : MulAut.conj (nOf t ht) * ((Θ f : ↥A) : MulAut L') =
            ((Θ f : ↥A) : MulAut L') * MulAut.conj (nOf t ht) := by
          rw [hae]
          exact ha.2
        rw [← hae, hΘval f, MulAut.conj_apply]
        have hf' : wOf t ht * ggSL9TorusCoord f = ggSL9TorusCoord f * wOf t ht :=
          (hwcomm f).mp hcomm
        rw [hl f hf']
        group
    have hmem2 : ∀ l : L', l ∈ (Subgroup.centralizer
        {x : GGSL9V ≃ₗ[ZMod 2] GGSL9V | x ∈ ggSL9Torus ∧
          wOf t ht * x = x * wOf t ht}).map Φ.toMonoidHom ↔
        ∀ f, wOf t ht * ggSL9TorusCoord f = ggSL9TorusCoord f * wOf t ht →
          σ f * l = l * σ f := by
      intro l
      constructor
      · intro hl f hf
        rw [Subgroup.mem_map] at hl
        obtain ⟨y, hy, hyl⟩ := hl
        have hx : ggSL9TorusCoord f ∈ {x : GGSL9V ≃ₗ[ZMod 2] GGSL9V |
            x ∈ ggSL9Torus ∧ wOf t ht * x = x * wOf t ht} :=
          ⟨by rw [← range_ggSL9TorusCoord]; exact ⟨f, rfl⟩, hf⟩
        have hcomm := (Subgroup.mem_centralizer_iff.mp hy) (ggSL9TorusCoord f) hx
        have hyl' : Φ y = l := hyl
        have h1 : Φ (ggSL9TorusCoord f) * l = l * Φ (ggSL9TorusCoord f) := by
          rw [← hyl']
          rw [← map_mul, ← map_mul, hcomm]
        exact h1
      · intro hl
        rw [Subgroup.mem_map]
        refine ⟨Φ.symm l, ?_, Φ.apply_symm_apply l⟩
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        obtain ⟨f, hf⟩ := (show x ∈ ggSL9TorusCoord.range from by
          rw [range_ggSL9TorusCoord]; exact hx.1)
        rw [← hf] at hx ⊢
        apply Φ.injective
        rw [map_mul, map_mul, Φ.apply_symm_apply]
        exact hl f hx.2
    refine Subgroup.ext fun l => ?_
    rw [hmem l, hmem2 l]
  have hgen := ggSL9_avoidOne ρ₀
  refine le_antisymm le_top ?_
  rw [← Subgroup.map_top_of_surjective Φ.toMonoidHom Φ.surjective, ← hgen,
    MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Set.mem_iUnion] at hy
  obtain ⟨t, hy⟩ := hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨ht, hy⟩ := hy
  have htRefl : t ∈ GGSL9Refl := ht.1
  have htne : t ≠ ρ₀ := by simpa only [Set.mem_singleton_iff] using ht.2
  have hweyl : GGTorusWeylElt 7 A (nOf t htRefl) := (hkey t htRefl).choose_spec.1
  have hreflect : GGIsReflection 7 (ggConjAut A ((hkey t htRefl).choose)) :=
    (hkey t htRefl).choose_spec.2.1
  have hne : ggConjAut A ((hkey t htRefl).choose) ≠ ρ := by
    intro hcon
    exact htne (hρ₀ ⟨t, htRefl⟩ hcon)
  have hnmemJ : nOf t htRefl ∈ (ggSL9J t.1 t.2.1 t.2.2).map Φ.toMonoidHom :=
    Subgroup.mem_map_of_mem Φ.toMonoidHom (ggSL9W_mem_J htRefl.ne t.2.2)
  have hdvd : 7 ∣ Nat.card ((ggSL9J t.1 t.2.1 t.2.2).map Φ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective Φ.injective]
    exact seven_dvd_card_ggSL9J htRefl.ne t.2.2
  have hComp : IsComponentOf ((ggSL9J t.1 t.2.1 t.2.2).map Φ.toMonoidHom)
      (ggHypCent A (nOf t htRefl)) := by
    have h1 := isComponentOf_map_mulEquiv Φ (isComponentOf_ggSL9J htRefl.ne t.2.2)
    rwa [← hhyp t htRefl] at h1
  have hle : ((ggSL9J t.1 t.2.1 t.2.2).map Φ.toMonoidHom) ≤
      (⨆ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
        (J : Subgroup L') (_ : GGTorusWeylElt 7 A n ∧ GGIsReflection 7 (ggConjAut A hn) ∧
          ggConjAut A hn ≠ ρ ∧ n ∈ J ∧ IsComponentOf J (ggHypCent A n) ∧
          7 ∣ Nat.card J), J) := by
    refine le_iSup_of_le (nOf t htRefl) ?_
    refine le_iSup_of_le ((hkey t htRefl).choose) ?_
    refine le_iSup_of_le ((ggSL9J t.1 t.2.1 t.2.2).map Φ.toMonoidHom) ?_
    refine le_iSup_of_le ⟨hweyl, hreflect, hne, hnmemJ, hComp, hdvd⟩ ?_
    exact le_rfl
  exact hle (Subgroup.mem_map_of_mem Φ.toMonoidHom hy)

@[expose] def GGRootGenKGA8SevenInput : Prop := GGRootGenKGAvoidOn GGLabA8Seven

private theorem recipeLinear_a8seven {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear 9 2 Q) :
    LargeEvenRecipeLinear 9 2 fun R _ I F => Q R I F ∧ ∃ r, GGTorusLift 7 r R ∧
      GGTorusRootGenAvoidKG 7 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 3,
    TypeA.ggTorusLift_of_mulEquiv (ggSL9RecipeEquiv hK) ggTorusLift_ggSL9,
    ggTorusRootGenAvoidKG_of_mulEquiv (ggSL9RecipeEquiv hK)
      (fun _ hφ => congr_ggSL9RecipeEquiv_mem hK hφ) ggTorusRootGenAvoidKG_ggSL9⟩

theorem ggRootGenKGA8SevenInput_holds : GGRootGenKGA8SevenInput := by
  intro p lab hp hp2 hlab hS
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hS
  exact fun Q hQ => recipeLinear_a8seven hQ

end CFSG.StandardType

end
