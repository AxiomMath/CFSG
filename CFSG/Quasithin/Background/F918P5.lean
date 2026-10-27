module

public import CFSG.Quasithin.Background.F918P4
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section CentralCover

variable {X Y : Type} [Group X] [Group Y]

theorem quotCenter_mulEquiv_of_central_ker (f : X →* Y) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) :
    Nonempty ((X ⧸ Subgroup.center X) ≃* (Y ⧸ Subgroup.center Y)) := by
  let g : X →* Y ⧸ Subgroup.center Y := (QuotientGroup.mk' (Subgroup.center Y)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = Subgroup.center X := by
    apply le_antisymm
    ·
      have hcomm : ∀ x ∈ g.ker, ∀ x' : X, x * x' * x⁻¹ * x'⁻¹ ∈ Subgroup.center X := by
        intro x hx x'
        apply hker
        have hx' : f x ∈ Subgroup.center Y :=
          (QuotientGroup.eq_one_iff (N := Subgroup.center Y) (f x)).mp hx
        have hc := Subgroup.mem_center_iff.mp hx' (f x')
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        calc f x * f x' * (f x)⁻¹ * (f x')⁻¹ = f x' * f x * (f x)⁻¹ * (f x')⁻¹ := by rw [hc]
          _ = 1 := by group
      have h1 : ⁅(⊤ : Subgroup X), g.ker⁆ ≤ Subgroup.center X := by
        rw [Subgroup.commutator_le]
        intro p _ a ha
        have := hcomm a ha p
        have e : ⁅p, a⁆ = (a * p * a⁻¹ * p⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact inv_mem this
      have h2 : ⁅⁅(⊤ : Subgroup X), g.ker⁆, (⊤ : Subgroup X)⁆ ≤ ⊥ := by
        rw [Subgroup.commutator_le]
        intro c hc p _
        have hcc : c * p = p * c := (Subgroup.mem_center_iff.mp (h1 hc) p).symm
        rw [Subgroup.mem_bot]
        simp only [commutatorElement_def]
        rw [hcc]
        group
      have hbot : Subgroup.normalizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr inferInstance
      have h3 := commutator_le_of_commutator_commutator_le (Q := ⊥) (A := g.ker) (P := ⊤)
        (le_of_le_of_eq le_top hbot.symm) (le_of_le_of_eq le_top hbot.symm) hperf h2
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro p
      have h4 := (Subgroup.commutator_le.mp h3) x hx p (Subgroup.mem_top p)
      rw [Subgroup.mem_bot] at h4
      simp only [commutatorElement_def] at h4
      have h5 : x * p * x⁻¹ = p := mul_inv_eq_one.mp h4
      calc p * x = (x * p * x⁻¹) * x := by rw [h5]
        _ = x * p := by group
    · intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro y
      obtain ⟨x', rfl⟩ := hf y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx x']
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

theorem quotCenter_mulEquiv_of_two_surj {Y₂ : Type} [Group Y₂] (f₁ : X →* Y) (f₂ : X →* Y₂)
    (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂) (hle : f₁.ker ≤ f₂.ker)
    (hcomm : ∀ x ∈ f₂.ker, ∀ x' : X, x * x' * x⁻¹ * x'⁻¹ ∈ f₁.ker)
    (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) :
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (Y₂ ⧸ Subgroup.center Y₂)) := by
  let f : Y →* Y₂ := f₁.liftOfRightInverse (Function.surjInv h₁) (Function.rightInverse_surjInv h₁)
    ⟨f₂, hle⟩
  have hff : ∀ x, f (f₁ x) = f₂ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply f₁ (Function.surjInv h₁)
      (Function.rightInverse_surjInv h₁) ⟨f₂, hle⟩ x
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := h₂ y
    exact ⟨f₁ x, hff x⟩
  have hker : f.ker ≤ Subgroup.center Y := by
    intro y hy
    obtain ⟨x, rfl⟩ := h₁ y
    have hx : x ∈ f₂.ker := by
      rw [MonoidHom.mem_ker, ← hff]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨x', rfl⟩ := h₁ y'
    have := hcomm x hx x'
    rw [MonoidHom.mem_ker] at this
    simp only [map_mul, map_inv] at this
    have h5 : f₁ x * f₁ x' = f₁ x' * f₁ x := by
      calc f₁ x * f₁ x' = f₁ x * f₁ x' * (f₁ x)⁻¹ * (f₁ x')⁻¹ * f₁ x' * f₁ x := by group
        _ = f₁ x' * f₁ x := by rw [this]; group
    exact h5.symm
  have hperfY : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
    have h1 : (⊤ : Subgroup X).map f₁ = ⊤ := MonoidHom.range_eq_top.mpr h₁ ▸ Subgroup.map_top f₁
    rw [← h1, ← Subgroup.map_commutator, hperf]
  exact quotCenter_mulEquiv_of_central_ker f hf hker hperfY

end CentralCover

theorem mulEquiv_range_of_simple {S Y : Type} [Group S] [Group Y] [IsSimpleGroup S] (f : S →* Y)
    (hne : f.range ≠ ⊥) : Nonempty (S ≃* f.range) := by
  have hker : f.ker = ⊥ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      have : x ∈ f.ker := by rw [h]; exact Subgroup.mem_top x
      rw [Subgroup.mem_bot]
      exact this
  exact ⟨MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff f).mp hker)⟩

theorem fourList_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : FourList X) :
    FourList Y := by
  rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | h | h | h | h | h
  · refine Or.inl ⟨n, hn, ?_⟩
    rcases h with h | h | h
    · exact Or.inl (IsPSL.of_mulEquiv e h)
    · exact Or.inr (Or.inl (IsSz.of_mulEquiv e h))
    · exact Or.inr (Or.inr (IsPSU.of_mulEquiv e h))
  · exact Or.inr (Or.inl ⟨n, hn, IsPSL.of_mulEquiv e h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, IsPSp4.of_mulEquiv e h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (IsAlt.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, IsG2.of_mulEquiv e h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsPSU.of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsPSL.of_mulEquiv e h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (IsPSL.of_mulEquiv e h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (IsAlt.of_mulEquiv e h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (IsSporadic.of_mulEquiv e h)))))))))

section Data

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem factElem (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))) :=
  ⟨h.isElemAbelian_tilde_conjClosure hIU (Or.inr rfl)⟩

@[expose] noncomputable def toAutI (h : HypF918 T V L V₁ Vp H K) (I : Subgroup G) :
    ↥K →* ↥(autIH V₁ I H K) :=
  ((actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)).comp
      (Subgroup.inclusion (le_of_mem_cComp h.K_cComp))).codRestrict (autIH V₁ I H K) fun x => by
    rw [autIH_eq_map h (le_of_mem_cComp h.K_cComp)]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩

omit [Finite G] in
theorem toAutI_coe (h : HypF918 T V L V₁ Vp H K) (I : Subgroup G) (x : ↥K) :
    ((toAutI h I x : ↥(autIH V₁ I H K)) : MulAut ↥(tildeOf V₁ (conjClosure I H))) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
        (Subgroup.inclusion (le_of_mem_cComp h.K_cComp) x) := rfl

omit [Finite G] in
theorem toAutI_surjective (h : HypF918 T V L V₁ Vp H K) (I : Subgroup G) :
    Function.Surjective (toAutI h I) := by
  rintro ⟨a, ha⟩
  have ha' : a ∈ (K.subgroupOf H).map (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [← autIH_eq_map h (le_of_mem_cComp h.K_cComp)]
    exact ha
  obtain ⟨y, hy, hya⟩ := ha'
  exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext hya⟩

theorem mem_pCoreOf_of_actH_eq_one (h : HypF918 T V L V₁ Vp H K) {x : ↥H}
    (hx : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x = 1) :
    (x : G) ∈ pCoreOf 2 H := by
  have := factElem h (le_conjClosure Vp H)
  rw [h.toHypF98.toHypF91.pCoreOf_eq_centralizerMod]
  exact ⟨x.2, h.H_le_normalizer_V₁ x.2, fun u hu =>
    h.commutator_mem_of_actH_eq_one (I := Vp) (le_conjClosure Vp H) hx u hu⟩

omit [Finite G] in
theorem toAutI_eq_one_iff (h : HypF918 T V L V₁ Vp H K) (I : Subgroup G) (x : ↥K) :
    toAutI h I x = 1 ↔ actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
      (Subgroup.inclusion (le_of_mem_cComp h.K_cComp) x) = 1 := by
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    exact Subtype.ext hx

theorem toAutI_ker_le (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    (toAutI h Vp).ker ≤ (toAutI h I).ker := by
  have := factElem h hIU
  intro x hx
  rw [MonoidHom.mem_ker, toAutI_eq_one_iff] at hx ⊢
  exact h.actH_eq_one_of_mem_pCoreOf hIU (mem_pCoreOf_of_actH_eq_one h hx)

theorem toAutI_comm (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    ∀ x ∈ (toAutI h I).ker, ∀ x' : ↥K, x * x' * x⁻¹ * x'⁻¹ ∈ (toAutI h Vp).ker := by
  have hF := factElem h hIU
  have hF' := factElem h (le_conjClosure Vp H)
  intro x hx x'
  rw [MonoidHom.mem_ker, toAutI_eq_one_iff] at hx ⊢
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hc := h.central_of_actH_eq_one hIU hnt
    (x := Subgroup.inclusion hKH x) (le_conjClosure K T x.2) hx (x' : G)
    (le_conjClosure K T x'.2)
  have hmem : ((x * x' * x⁻¹ * x'⁻¹ : ↥K) : G) ∈ pCoreOf 2 H := by
    simpa using hc
  exact h.actH_eq_one_of_mem_pCoreOf (I := Vp) (le_conjClosure Vp H)
    (x := Subgroup.inclusion hKH (x * x' * x⁻¹ * x'⁻¹)) hmem

end Data

section Final

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] noncomputable def IsIrrPlusTildeT (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem h hIU
  subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
    (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T)

@[expose] noncomputable def F918Four (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem h hIU
  H ≤ Subgroup.normalizer (I : Set G) ∨
    ModFourRest (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)

theorem F918_4 (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU)
    (h310 : D310) (h391 : D391) (hI4 : Insp4) :
    FourList (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K)) ∧ F918Four h hIU := by
  have hF := factElem h hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK]
  have h4 := mod4_core h310 h391 hD hirr' hMp hA
  have hqM := hA.qhat_M hD.sylow.1
  have hshape := hI4 _ _ _ _ _ _ ⟨hD, hA.qhat_VT hD.exp, hirr'⟩ hMp hqM (hA.qOf_VT hD.exp)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  refine ⟨?_, ?_⟩
  · have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
      have := (Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.K_cComp)).commutator_eq_top
      rwa [_root_.commutator_def] at this
    obtain ⟨e⟩ := quotCenter_mulEquiv_of_two_surj (toAutI h Vp) (toAutI h I)
      (toAutI_surjective h Vp) (toAutI_surjective h I) (toAutI_ker_le h hIU)
      (toAutI_comm h hIU hnt) hperf
    exact fourList_congr e.symm hshape
  · show H ≤ Subgroup.normalizer (I : Set G) ∨
      ModFourRest (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
        (subM V₁ (conjClosure I H) I)
    rcases h4 with hst | hrest
    · left
      rw [autIH_eq_map h (le_refl H)] at hst
      exact (map_actH_le_stabSub_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
        (le_normalizer_conjClosure I H) hV₁I).mp hst
    · exact Or.inr hrest

@[expose] def F918Fine4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H K : Subgroup G), HypF918 T V L V₁ Vp H K →
    SQTKGroup ↥H → conjClosure K T = K →
    (IsAlt 7 (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K)) →
        ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 7))) ∧
      (IsSporadic .M22 (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K)) →
        IsSporadic .M22 ↥(autIH V₁ Vp H K) ∨
          IsHat ↥(autIH V₁ Vp H K) (CFSG.Blueprint.NativeSporadic.Carrier .M22))

theorem F918_4_fine (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU)
    (h310 : D310) (h391 : D391) (hI4 : Insp4) (hFine : F918Fine4) :
    FourListFine ↥(autIH V₁ Vp H K) ∧ F918Four h hIU := by
  obtain ⟨h1, h2⟩ := F918_4 h hH hK hV₁I hIU hirr h310 h391 hI4
  obtain ⟨h3, h4⟩ := hFine G T V L V₁ Vp H K h hH hK
  exact ⟨⟨h1, h3, h4⟩, h2⟩

end Final

section Five

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem injective_of_isSimpleGroup {S Y : Type} [Group S] [Group Y] [IsSimpleGroup S]
    (f : S →* Y) (hne : ∃ s, f s ≠ 1) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs⟩ := hne
    apply hs
    have : s ∈ f.ker := by rw [h]; exact Subgroup.mem_top s
    exact this

theorem nonempty_mulEquiv_quotient_autI (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hne : autIH V₁ I H K ≠ ⊥) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autIH V₁ I H K)) := by
  have hF := factElem h hIU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : CFSG.pCore 2 ↥K ≤ (toAutI h I).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    apply h.actH_eq_one_of_mem_pCoreOf hIU
    have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
      assumption
    have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp) hx1
  let f : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autIH V₁ I H K) := QuotientGroup.lift _ (toAutI h I) hker
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := toAutI_surjective h I y
    exact ⟨QuotientGroup.mk x, hx⟩
  have hinj : Function.Injective f := by
    apply injective_of_isSimpleGroup
    obtain ⟨y, hyS, hy1⟩ : ∃ y ∈ autIH V₁ I H K, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hne ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨s, hs⟩ := hsurj ⟨y, hyS⟩
    refine ⟨s, fun h1 => hy1 ?_⟩
    rw [h1] at hs
    exact congrArg Subtype.val hs.symm
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem five_group_data (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K) :
    A38Types (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      ∀ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) →
        K.map (MulAut.conj t).toMonoidHom ∈ cComp H ∧
        conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
        ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 H ∧
        ∀ x ∈ H, x ∈ Subgroup.normalizer (K : Set G) ∨ t⁻¹ * x ∈ Subgroup.normalizer (K : Set G) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hQ : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHyp.of_sqtkGroup ↥H hH
  have h37' := hA37 _ hQ
  have h38' := hA38 _ hQ
  have hnn : ¬ (K.subgroupOf H).Normal := by
    intro hnorm
    apply hK
    apply le_antisymm
    · refine conjClosure_le fun t ht z hz => ?_
      have : t ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hnorm (h.T_le_H ht)
      exact (Subgroup.mem_normalizer_iff.mp this z).mp hz
    · exact le_conjClosure K T
  obtain ⟨hncard, hA38K⟩ :=
    (lemma_1_2_1_three_of_a3_sq h37' h38' h.K_cComp).resolve_left hnn
  refine ⟨hA38K, fun t ht htK => ?_⟩
  have htH : t ∈ H := h.T_le_H ht
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ cComp H := map_conj_mem_cComp h.K_cComp htH
  have hne : K.map (MulAut.conj t).toMonoidHom ≠ K := fun he => htK (A38.map_conj_eq_iff.mp he)
  have hsub : ({K, K.map (MulAut.conj t).toMonoidHom} : Set (Subgroup G)) ⊆ conjSubgroupsBy H K := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨1, H.one_mem, (A38.map_conj_eq_iff.mpr (Subgroup.one_mem _)).symm⟩
    · exact ⟨t, htH, rfl⟩
  have hset : conjSubgroupsBy H K = {K, K.map (MulAut.conj t).toMonoidHom} :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hncard, Set.ncard_pair hne.symm])
      (Set.toFinite _)).symm
  refine ⟨hKt, ?_, commutator_le_pCoreOf_of_ne h37' h.K_cComp hKt hne.symm, ?_⟩
  swap
  · intro x hx
    have hmem : K.map (MulAut.conj x).toMonoidHom ∈ conjSubgroupsBy H K := ⟨x, hx, rfl⟩
    rw [hset] at hmem
    rcases hmem with he | he
    · exact Or.inl (A38.map_conj_eq_iff.mp he)
    · right
      have hmemx : ∀ w, w ∈ K.map (MulAut.conj x).toMonoidHom ↔
          w ∈ K.map (MulAut.conj t).toMonoidHom := fun w => by rw [he]
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have h1 := hmemx (x * z * x⁻¹)
      rw [A38.mem_map_conj, A38.mem_map_conj] at h1
      have e1 : x⁻¹ * (x * z * x⁻¹) * x = z := by group
      have e2 : t⁻¹ * (x * z * x⁻¹) * t = t⁻¹ * x * z * (t⁻¹ * x)⁻¹ := by group
      rw [e1, e2] at h1
      exact h1
  apply le_antisymm
  · refine conjClosure_le fun u hu z hz => ?_
    have hmem : K.map (MulAut.conj u).toMonoidHom ∈ conjSubgroupsBy H K := ⟨u, h.T_le_H hu, rfl⟩
    rw [hset] at hmem
    have hz' : u * z * u⁻¹ ∈ K.map (MulAut.conj u).toMonoidHom :=
      ⟨z, hz, by simp [MulAut.conj_apply]⟩
    rcases hmem with he | he
    · rw [he] at hz'
      exact Subgroup.mem_sup_left hz'
    · rw [he] at hz'
      exact Subgroup.mem_sup_right hz'
  · refine sup_le (le_conjClosure K T) ?_
    rintro x ⟨z, hz, rfl⟩
    exact mem_conjClosure ht hz

omit [Finite G] in
theorem conjAutSub_map_subgroupOf {W : Type} [CommGroup W] (φ : ↥H →* MulAut W) {t : G} (ht : t ∈ H)
    {X : Subgroup G} :
    conjAutSub (φ ⟨t, ht⟩) ((X.subgroupOf H).map φ) =
      ((X.map (MulAut.conj t).toMonoidHom).subgroupOf H).map φ := by
  unfold conjAutSub
  rw [Subgroup.map_map]
  have e1 : (X.map (MulAut.conj t).toMonoidHom).subgroupOf H =
      (X.subgroupOf H).map (MulAut.conj (⟨t, ht⟩ : ↥H)).toMonoidHom := by
    ext x
    rw [Subgroup.mem_subgroupOf, A38.mem_map_conj, A38.mem_map_conj, Subgroup.mem_subgroupOf]
    rfl
  have e2 : (MulAut.conj (φ ⟨t, ht⟩)).toMonoidHom.comp φ =
      φ.comp (MulAut.conj (⟨t, ht⟩ : ↥H)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [e2, e1, ← Subgroup.map_map]

theorem five_prelim
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T ≠ K)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) :
    A38Types ↥(autIH V₁ I H K) ∧
      (FiveShape ↥(autIH V₁ I H K) → FiveShape ↥(autIH V₁ Vp H K)) ∧
      ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) →
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩ ∈
            autIH V₁ I H T ∧
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩ ∉
            Subgroup.normalizer ((autIH V₁ I H K : Subgroup _) : Set _) ∧
        autIH V₁ I H (conjClosure K T) = autIH V₁ I H K ⊔
          conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
            ⟨t, h.T_le_H ht⟩) (autIH V₁ I H K) ∧
        ∀ x ∈ H, x ∈ Subgroup.normalizer (K : Set G) ∨ t⁻¹ * x ∈ Subgroup.normalizer (K : Set G) := by
  have hFU := factElem h (le_conjClosure Vp H)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  obtain ⟨hA38K, hdata⟩ := five_group_data h hH hA37 hA38 hK
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
  have hneL : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  obtain ⟨eL⟩ := nonempty_mulEquiv_quotient_autI h hIU hS hneL
  have hneU : autIH V₁ Vp H K ≠ ⊥ := by
    intro hbot
    apply hneL
    rw [eq_bot_iff]
    rintro y hy
    obtain ⟨x, hx⟩ := toAutI_surjective h I ⟨y, hy⟩
    have hx1 : toAutI h Vp x = 1 := by
      have : ((toAutI h Vp x : ↥(autIH V₁ Vp H K)) :
          MulAut ↥(tildeOf V₁ (conjClosure Vp H))) ∈
          (⊥ : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) := by
        rw [← hbot]
        exact (toAutI h Vp x).2
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    have h2 : x ∈ (toAutI h I).ker := toAutI_ker_le h hIU (show x ∈ (toAutI h Vp).ker from hx1)
    rw [MonoidHom.mem_ker] at h2
    rw [Subgroup.mem_bot]
    have h3 := congrArg Subtype.val hx
    rw [h2] at h3
    exact h3.symm
  obtain ⟨eU⟩ := nonempty_mulEquiv_quotient_autI h (le_conjClosure Vp H) hS hneU
  refine ⟨a38Types_congr eL hA38K, fun hsh => fiveShape_congr (eL.symm.trans eU) hsh, ?_⟩
  intro t ht htK
  obtain ⟨hKt, hK₀, hcomm, hcoset⟩ := hdata t ht htK
  have htH : t ∈ H := h.T_le_H ht
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  have hconj : conjAutSub (φ ⟨t, htH⟩) (autIH V₁ I H K) =
      autIH V₁ I H (K.map (MulAut.conj t).toMonoidHom) := by
    rw [autIH_eq_map h hKH, autIH_eq_map h hKtH]
    exact conjAutSub_map_subgroupOf φ htH
  have hMp : autIH V₁ I H (conjClosure K T) =
      autIH V₁ I H K ⊔ conjAutSub (φ ⟨t, htH⟩) (autIH V₁ I H K) := by
    rw [hconj, hK₀, autIH_eq_map h (sup_le hKH hKtH), autIH_eq_map h hKH, autIH_eq_map h hKtH,
      Subgroup.subgroupOf_sup hKH hKtH, Subgroup.map_sup]
  have ht'T : φ ⟨t, htH⟩ ∈ autIH V₁ I H T := by
    rw [autIH_eq_map h h.T_le_H]
    exact ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have ht'L : φ ⟨t, htH⟩ ∉ Subgroup.normalizer ((autIH V₁ I H K : Subgroup _) : Set _) := by
    intro hnorm
    have h1 : conjAutSub (φ ⟨t, htH⟩) (autIH V₁ I H K) = autIH V₁ I H K :=
      A38.map_conj_eq_iff.mpr hnorm
    rw [hconj] at h1
    have h2 : ⁅autIH V₁ I H K, autIH V₁ I H (K.map (MulAut.conj t).toMonoidHom)⁆ = ⊥ := by
      rw [autIH_eq_map h hKH, autIH_eq_map h hKtH, ← Subgroup.map_commutator,
        Subgroup.map_eq_bot_iff]
      intro c hc
      have hc' : (c : G) ∈ ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ := by
        have := Subgroup.mem_map_of_mem H.subtype hc
        rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
          Subgroup.map_subgroupOf_eq_of_le hKtH] at this
      exact h.actH_eq_one_of_mem_pCoreOf hIU (hcomm hc')
    rw [h1] at h2
    have h3 : ⁅autIH V₁ I H K, autIH V₁ I H K⁆ = autIH V₁ I H K := by
      rw [autIH_eq_map h hKH, ← Subgroup.map_commutator,
        perfect_of_mem_cComp (subgroupOf_mem_cComp h.K_cComp)]
    exact hneL (h3.symm.trans h2)
  exact ⟨ht'T, ht'L, hMp, hcoset⟩

@[expose] noncomputable def F918Five (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) : Prop :=
  haveI := factElem h hIU
  ModFive (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
    (subM V₁ (conjClosure I H) I)
    (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)

@[expose] noncomputable def F918FiveTop (h : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hIU : I ≤ conjClosure Vp H) {t : G} (ht : t ∈ T) : Prop :=
  haveI := factElem h hIU
  ModFiveTop (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
    (subM V₁ (conjClosure I H) I)
    (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)

theorem F918_5
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T ≠ K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) :
    FiveShape ↥(autIH V₁ Vp H K) ∧
      ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) → F918Five h hIU ht := by
  have hF := factElem h hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  obtain ⟨hL38, hshape, hdata⟩ := five_prelim h hH hK hIU hnt hA37 hA38
  have key : ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) → F918Five h hIU ht := by
    intro t ht htK
    obtain ⟨ht'T, ht'L, hMp, -⟩ := hdata t ht htK
    show ModFive (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
      (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)
    exact mod5_core hD36 hD37 hD321 hI5 hD hirr' ht'T ht'L hMp hL38 hA
  obtain ⟨t₀, ht₀, ht₀K⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hK
    apply le_antisymm
    · refine conjClosure_le fun t ht z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  exact ⟨hshape (key t₀ ht₀ ht₀K).fiveShape, key⟩

theorem F918_5_inv
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T ≠ K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU)
    (hinv : ∀ x ∈ H, x ∈ Subgroup.normalizer (K : Set G) → x ∈ Subgroup.normalizer (I : Set G))
    (hD36 : D36) (hD37 : D37) (hI5 : Insp5a) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) :
    FiveShape ↥(autIH V₁ Vp H K) ∧
      ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) → F918FiveTop h hIU ht := by
  have hF := factElem h hIU
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  obtain ⟨hL38, hshape, hdata⟩ := five_prelim h hH hK hIU hnt hA37 hA38
  have key : ∀ t (ht : t ∈ T), t ∉ Subgroup.normalizer (K : Set G) → F918FiveTop h hIU ht := by
    intro t ht htK
    obtain ⟨ht'T, ht'L, hMp, hcoset⟩ := hdata t ht htK
    have htH : t ∈ H := h.T_le_H ht
    set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
    have hVT : orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I) = ⊤ := by
      rw [eq_top_iff, ← iSup_actH_subM_eq_top h.H_le_normalizer_V₁
        (h.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I]
      refine iSup₂_le fun m hm => ?_
      obtain ⟨x, -, rfl⟩ := hm
      have hxH : (x : G) ∈ H := x.2
      have hstab : ∀ y : ↥H, (y : G) ∈ Subgroup.normalizer (K : Set G) →
          φ y ∈ stabSub (subM V₁ (conjClosure I H) I) := fun y hy =>
        (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
          (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) y).mpr (hinv _ y.2 hy)
      rcases hcoset x hxH with hx | hx
      · rintro _ ⟨v, hv, rfl⟩
        exact le_orbSup _ _ (((hstab x hx) v).mpr hv)
      · set y : ↥H := ⟨t⁻¹ * x, H.mul_mem (H.inv_mem htH) hxH⟩ with hy
        have hxy : x = ⟨t, htH⟩ * y := by
          apply Subtype.ext
          simp [hy]
        rintro _ ⟨v, hv, rfl⟩
        have hyv : φ y v ∈ subM V₁ (conjClosure I H) I := ((hstab y hx) v).mpr hv
        have hmem := map_le_orbSup (V := subM V₁ (conjClosure I H) I) ht'T ⟨φ y v, hyv, rfl⟩
        have hxv : (φ x).toMonoidHom v = (φ ⟨t, htH⟩).toMonoidHom ((φ y) v) := by
          show (φ x) v = (φ ⟨t, htH⟩) ((φ y) v)
          rw [hxy, map_mul]
          rfl
        have hfin : (φ x).toMonoidHom v ∈ orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I) := by
          rw [hxv]
          exact hmem
        exact hfin
    show ModFiveTop (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
      (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, h.T_le_H ht⟩)
    exact mod5_of_top hD36 hD37 hI5 hD hirr' ht'T ht'L hMp hL38 hA hVT
  obtain ⟨t₀, ht₀, ht₀K⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hK
    apply le_antisymm
    · refine conjClosure_le fun t ht z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  exact ⟨hshape (key t₀ ht₀ ht₀K).toModFive.fiveShape, key⟩

end Five


end CFSG.Quasithin
