module

public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin

open CFSG CFSG.Open CFSG.LieType.BorelTits

section GenFitting

variable {B : Type*} [Group B]

private theorem comap_map_subtype_eq (Y : Subgroup B) (c : Subgroup Y) :
    (c.map Y.subtype).subgroupOf Y = c :=
  Subgroup.comap_map_eq_self_of_injective Y.subtype_injective c

theorem quasithinGenFitting_eq_map_subtype (Y : Subgroup B) :
    CFSG.Open.quasithinGenFitting Y =
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup Y).map Y.subtype := by
  unfold CFSG.Open.quasithinGenFitting; simp only [CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup]
  rw [Subgroup.map_sup]
  congr 1
  ·
    simp only [CFSG.ComponentClassification.Fitting.subgroup.eq_sSup]
    apply le_antisymm
    · refine sSup_le fun N hN => ?_
      obtain ⟨hNY, hNn, hNnil⟩ := hN
      have hnil : Group.IsNilpotent (N.subgroupOf Y) :=
        (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNY)).mpr hNnil
      calc N = (N.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hNY).symm
        _ ≤ _ := Subgroup.map_mono (le_sSup (show N.subgroupOf Y ∈
            {c : Subgroup Y | c.Normal ∧ Group.IsNilpotent c} from ⟨hNn, hnil⟩))
    · rw [(Subgroup.gc_map_comap Y.subtype).l_sSup]
      refine iSup₂_le fun c hc => ?_
      obtain ⟨hcn, hcnil⟩ := hc
      refine le_sSup ?_
      refine ⟨Subgroup.map_subtype_le c, ?_, ?_⟩
      · rw [comap_map_subtype_eq]
        exact hcn
      · exact (Group.isNilpotent_congr (c.equivMapOfInjective Y.subtype Y.subtype_injective)).mp
          hcnil
  ·
    simp only [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    apply le_antisymm
    · refine sSup_le fun K hK => ?_
      obtain ⟨hKY, hK'⟩ := isComponentOf_iff_subgroupOf.mp hK
      calc K = (K.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hKY).symm
        _ ≤ _ := Subgroup.map_mono (le_sSup hK')
    · rw [(Subgroup.gc_map_comap Y.subtype).l_sSup]
      refine iSup₂_le fun c hc => le_sSup ?_
      refine isComponentOf_iff_subgroupOf.mpr ⟨Subgroup.map_subtype_le c, ?_⟩
      rw [comap_map_subtype_eq]
      exact hc

variable [Finite B]

theorem quasithinGenFitting_le_of_normal (K : Subgroup B) [K.Normal] :
    CFSG.Open.quasithinGenFitting K ≤ K ⊓ CFSG.generalizedFitting B := by
  refine le_inf (quasithinGenFitting_le K) ?_
  rw [quasithinGenFitting_eq_map_subtype, CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.normal_monotone K

theorem pCoreOf_two_eq_bot_of_normal (hB : CFSG.pCore 2 B = ⊥) (N : Subgroup B) [N.Normal] :
    pCoreOf 2 N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNtop : Subgroup.normalizer (N : Set B) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hPcoreB : (pCoreOf 2 N).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← hNtop]
    exact normalizer_le_normalizer_pCoreOf 2 N
  have hle : pCoreOf 2 N ≤ CFSG.Open.pCore 2 B := le_pCore 2 hPcoreB (pCoreOf_isPGroup 2 N)
  refine le_bot_iff.mp (hle.trans ?_)
  rw [hB]

theorem eq_bot_of_isPGroup_of_le_fitting (hB : CFSG.pCore 2 B = ⊥) {S : Subgroup B}
    (hS : IsPGroup 2 S) (hSF : S ≤ CFSG.fittingSubgroup B) : S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup B := CFSG.fittingSubgroup B with hN
  have : N.Normal := CFSG.fittingSubgroup_normal
  have : Group.IsNilpotent N := CFSG.fittingSubgroup_nilpotent
  have hS' : IsPGroup 2 (S.subgroupOf N) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSF).symm
  obtain ⟨P, hSP⟩ := hS'.exists_le_sylow
  have hPcore : (P : Subgroup N) ≤ CFSG.Open.pCore 2 ↥N :=
    le_pCore 2 inferInstance P.isPGroup'
  have hbot : pCoreOf 2 N = ⊥ := pCoreOf_two_eq_bot_of_normal hB N
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hSF hx⟩ : N) ∈ S.subgroupOf N := hx
  have h2 : (⟨x, hSF hx⟩ : N) ∈ CFSG.Open.pCore 2 ↥N := hPcore (hSP h1)
  have h3 : x ∈ pCoreOf 2 N := ⟨_, h2, rfl⟩
  rw [hbot] at h3
  exact h3

end GenFitting

section FixedPoints

variable {B : Type*} [Group B]

private theorem le_normalizer_of_comm_elems {A V : Subgroup B}
    (h : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) : A ≤ Subgroup.normalizer (V : Set B) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => ?_, fun hu => ?_⟩
  · have : a * v * a⁻¹ = v := by rw [h a ha v hv]; group
    rwa [this]
  · have h2 : a * (a * v * a⁻¹) = a * v := by
      calc a * (a * v * a⁻¹) = (a * v * a⁻¹) * a := h a ha _ hu
        _ = a * v := by group
    have h3 : a * v * a⁻¹ = v := mul_left_cancel h2
    rwa [h3] at hu

private theorem conj_mem_iSup' {ι : Type*} (X : ι → Subgroup B) {j : B}
    (hj : ∀ i, j ∈ Subgroup.normalizer (X i : Set B)) {v : B} (hv : v ∈ ⨆ i, X i) :
    j * v * j⁻¹ ∈ ⨆ i, X i := by
  refine Subgroup.iSup_induction X (C := fun v => j * v * j⁻¹ ∈ ⨆ i, X i) hv
    (fun i x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_normalizer_iff.mp (hj i) x).mp hx)
  · have : j * (x * y) * j⁻¹ = (j * x * j⁻¹) * (j * y * j⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy

private theorem conj_mem_biSup' {ι : Type*} (X : ι → Subgroup B) (S : Finset ι) {j : B}
    (hj : ∀ i, j ∈ Subgroup.normalizer (X i : Set B)) {v : B} (hv : v ∈ ⨆ i ∈ S, X i) :
    j * v * j⁻¹ ∈ ⨆ i ∈ S, X i := by
  rw [iSup_subtype'] at hv ⊢
  exact conj_mem_iSup' (fun i : {i // i ∈ S} => X i.1) (fun i => hj i.1) hv

private theorem comm_of_mem_biSup' {ι : Type*} (X : ι → Subgroup B) (S : Finset ι) {x : B}
    (hx : ∀ i ∈ S, ∀ y ∈ X i, x * y = y * x) {v : B} (hv : v ∈ ⨆ i ∈ S, X i) :
    x * v = v * x := by
  have hle : (⨆ i ∈ S, X i) ≤ Subgroup.centralizer ({x} : Set B) := by
    refine iSup₂_le fun i hi y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx i hi y hy).symm
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
  exact this.symm

theorem fixed_eq_one_of_biSup {ι : Type*} [DecidableEq ι] (J : Subgroup B) (X : ι → Subgroup B)
    (hnorm : ∀ i, J ≤ Subgroup.normalizer (X i : Set B))
    (hcomm : ∀ i k, ∀ x ∈ X i, ∀ y ∈ X k, x * y = y * x)
    (hprime : ∀ i, ∀ Y : Subgroup B, Y ≤ X i → Y = ⊥ ∨ Y = X i)
    (hfix : ∀ i, ∀ x ∈ X i, (∀ j ∈ J, j * x = x * j) → x = 1) (S : Finset ι) :
    ∀ v ∈ (⨆ i ∈ S, X i : Subgroup B), (∀ j ∈ J, j * v = v * j) → v = 1 := by
  induction S using Finset.induction_on with
  | empty =>
    intro v hv _
    simpa using hv
  | insert a S haS ih =>
    intro v hv hvJ
    rw [Finset.iSup_insert] at hv
    by_cases hle : X a ≤ ⨆ i ∈ S, X i
    · rw [sup_eq_right.mpr hle] at hv
      exact ih v hv hvJ
    · have hinf : X a ⊓ (⨆ i ∈ S, X i) = ⊥ := by
        rcases hprime a (X a ⊓ (⨆ i ∈ S, X i)) inf_le_left with h | h
        · exact h
        · exact absurd (h ▸ inf_le_right) hle
      have hcomm' : ∀ x ∈ X a, ∀ y ∈ (⨆ i ∈ S, X i : Subgroup B), x * y = y * x :=
        fun x hx y hy =>
          comm_of_mem_biSup' X S (fun i _ z hz => hcomm a i x hx z hz) hy
      have hmem : v ∈ ((X a ⊔ ⨆ i ∈ S, X i : Subgroup B) : Set B) := hv
      rw [Subgroup.coe_mul_of_left_le_normalizer_right (X a) (⨆ i ∈ S, X i)
        (le_normalizer_of_comm_elems hcomm')] at hmem
      obtain ⟨x, hx, y, hy, hxy⟩ := hmem
      have hxy' : x * y = v := hxy
      subst hxy'
      have key : ∀ j ∈ J, j * x * j⁻¹ = x ∧ j * y * j⁻¹ = y := by
        intro j hj
        have h1 : j * x * j⁻¹ ∈ X a := (Subgroup.mem_normalizer_iff.mp (hnorm a hj) x).mp hx
        have h2 : j * y * j⁻¹ ∈ ⨆ i ∈ S, X i :=
          conj_mem_biSup' X S (fun i => hnorm i hj) hy
        have h3 : (j * x * j⁻¹) * (j * y * j⁻¹) = x * y := by
          have := hvJ j hj
          calc (j * x * j⁻¹) * (j * y * j⁻¹) = j * (x * y) * j⁻¹ := by group
            _ = x * y := by rw [this]; group
        have h4 : x⁻¹ * (j * x * j⁻¹) ∈ X a ⊓ (⨆ i ∈ S, X i) := by
          refine ⟨Subgroup.mul_mem _ (inv_mem hx) h1, ?_⟩
          have : x⁻¹ * (j * x * j⁻¹) = y * (j * y * j⁻¹)⁻¹ := by
            have h5 : j * x * j⁻¹ = x * y * (j * y * j⁻¹)⁻¹ := by
              calc j * x * j⁻¹ = (j * x * j⁻¹) * (j * y * j⁻¹) * (j * y * j⁻¹)⁻¹ := by group
                _ = x * y * (j * y * j⁻¹)⁻¹ := by rw [h3]
            rw [h5]; group
          rw [this]
          exact Subgroup.mul_mem _ hy (inv_mem h2)
        rw [hinf, Subgroup.mem_bot] at h4
        have hxj : j * x * j⁻¹ = x := by
          calc j * x * j⁻¹ = x * (x⁻¹ * (j * x * j⁻¹)) := by group
            _ = x := by rw [h4]; group
        refine ⟨hxj, ?_⟩
        have := h3
        rw [hxj] at this
        exact mul_left_cancel this
      have hx1 : x = 1 := hfix a x hx fun j hj => by
        have := (key j hj).1
        calc j * x = (j * x * j⁻¹) * j := by group
          _ = x * j := by rw [this]
      have hy1 : y = 1 := ih y hy fun j hj => by
        have := (key j hj).2
        calc j * y = (j * y * j⁻¹) * j := by group
          _ = y * j := by rw [this]
      rw [hx1, hy1, one_mul]

end FixedPoints

section Main

variable {B : Type*} [Group B] [Finite B]

theorem le_centralizer_of_fixed (hB : CFSG.pCore 2 B = ⊥)
    {Kb Rb Hb Jb Vb : Subgroup B} [hK : Kb.Normal]
    (hR2 : IsPGroup 2 Rb) (hHn : Hb ≤ Subgroup.normalizer (Rb : Set B))
    (hE : CFSG.layer B ≤ Hb) (hJR : Jb ≤ Rb)
    (hJV : Jb ≤ Subgroup.normalizer (Vb : Set B)) (hVK : Vb ⊓ Kb = ⊥)
    (hVfix : ∀ v ∈ Vb, (∀ j ∈ Jb, j * v = v * j) → v = 1)
    (hF : ∀ f ∈ CFSG.fittingSubgroup B, ∃ a ∈ CFSG.fittingSubgroup B ⊓ Hb, ∃ v ∈ Vb, f = a * v) :
    Rb ≤ Subgroup.centralizer (Kb : Set B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn : (CFSG.layer B).Normal := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.normal B
  have hFn : (CFSG.fittingSubgroup B).Normal := CFSG.fittingSubgroup_normal
  have hEc : ∀ e ∈ CFSG.layer B, ∀ r ∈ Rb, e * r = r * e := by
    intro e he r hr
    set S : Subgroup B := CFSG.layer B ⊓ Rb with hS
    have hS2 : IsPGroup 2 S := hR2.to_le inf_le_right
    have key : ∀ e'' ∈ CFSG.layer B, ∀ s ∈ S, e'' * s * e''⁻¹ ∈ S := fun e'' he'' s hs =>
      ⟨hLn.conj_mem s hs.1 e'', (Subgroup.mem_normalizer_iff.mp (hHn (hE he'')) s).mp hs.2⟩
    have hSn : CFSG.layer B ≤ Subgroup.normalizer (S : Set B) := by
      intro e' he'
      rw [Subgroup.mem_normalizer_iff]
      intro s
      refine ⟨key e' he' s, fun hs => ?_⟩
      have := key e'⁻¹ (inv_mem he') _ hs
      simpa [mul_assoc] using this
    have hSle : S ≤ pCoreOf 2 (CFSG.layer B) := le_pCoreOf_of_le_normalizer 2 inf_le_left hSn hS2
    have hbot : pCoreOf 2 (CFSG.layer B) = ⊥ := pCoreOf_two_eq_bot_of_normal hB _
    have hcomm : e * r * e⁻¹ * r⁻¹ ∈ S := by
      refine ⟨?_, ?_⟩
      · have : e * r * e⁻¹ * r⁻¹ = e * (r * e⁻¹ * r⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ he (hLn.conj_mem _ (inv_mem he) r)
      · exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hHn (hE he)) r).mp hr)
          (inv_mem hr)
    have h1 : e * r * e⁻¹ * r⁻¹ = 1 := by
      have := hSle hcomm
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    calc e * r = (e * r * e⁻¹ * r⁻¹) * (r * e) := by group
      _ = r * e := by rw [h1, one_mul]
  have hAc : ∀ a ∈ CFSG.fittingSubgroup B ⊓ Hb, ∀ r ∈ Rb, a * r = r * a := by
    intro a ha r hr
    set S : Subgroup B := CFSG.fittingSubgroup B ⊓ Rb with hS
    have hS2 : IsPGroup 2 S := hR2.to_le inf_le_right
    have hS1 : S = ⊥ := eq_bot_of_isPGroup_of_le_fitting hB hS2 inf_le_left
    have hcomm : a * r * a⁻¹ * r⁻¹ ∈ S := by
      refine ⟨?_, ?_⟩
      · have : a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ ha.1 (hFn.conj_mem _ (inv_mem ha.1) r)
      · exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hHn ha.2) r).mp hr)
          (inv_mem hr)
    have h1 : a * r * a⁻¹ * r⁻¹ = 1 := by
      have := hcomm
      rw [hS1, Subgroup.mem_bot] at this
      exact this
    calc a * r = (a * r * a⁻¹ * r⁻¹) * (r * a) := by group
      _ = r * a := by rw [h1, one_mul]
  have hPF : Rb ≤ Subgroup.centralizer (CFSG.Open.quasithinGenFitting Kb : Set B) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨hxK, hxF⟩ := quasithinGenFitting_le_of_normal Kb hx
    have hxs : x ∈ CFSG.fittingSubgroup B ⊔ CFSG.layer B := hxF
    obtain ⟨f, hf, e, he, hfe⟩ := Subgroup.mem_sup_of_normal_right.mp hxs
    obtain ⟨a, ha, v, hv, rfl⟩ := hF f hf
    have hxform : x = a * v * e := hfe.symm
    have hv1 : v = 1 := by
      apply hVfix v hv
      intro j hj
      have hjR : j ∈ Rb := hJR hj
      have hej : e * j = j * e := hEc e he j hjR
      have haj : a * j = j * a := hAc a ha j hjR
      have hej' : e * j * e⁻¹ = j := by rw [hej]; group
      have haj' : a⁻¹ * j⁻¹ = j⁻¹ * a⁻¹ := by
        have := congrArg (fun y => y⁻¹) haj
        simpa using this.symm
      have hxj : x * j * x⁻¹ * j⁻¹ ∈ Kb := by
        have : x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hxK (hK.conj_mem _ (inv_mem hxK) j)
      have hcalc : x * j * x⁻¹ * j⁻¹ = a * (v * j * v⁻¹ * j⁻¹) * a⁻¹ := by
        rw [hxform]
        calc a * v * e * j * (a * v * e)⁻¹ * j⁻¹
            = a * v * (e * j * e⁻¹) * v⁻¹ * (a⁻¹ * j⁻¹) := by group
          _ = a * v * j * v⁻¹ * (j⁻¹ * a⁻¹) := by rw [hej', haj']
          _ = a * (v * j * v⁻¹ * j⁻¹) * a⁻¹ := by group
      have hu : v * j * v⁻¹ * j⁻¹ ∈ Vb ⊓ Kb := by
        refine ⟨?_, ?_⟩
        · have : v * j * v⁻¹ * j⁻¹ = v * (j * v⁻¹ * j⁻¹) := by group
          rw [this]
          exact Subgroup.mul_mem _ hv
            ((Subgroup.mem_normalizer_iff.mp (hJV hj) v⁻¹).mp (inv_mem hv))
        · have h2 : v * j * v⁻¹ * j⁻¹ = a⁻¹ * (x * j * x⁻¹ * j⁻¹) * a := by
            rw [hcalc]; group
          rw [h2]
          have := hK.conj_mem _ hxj a⁻¹
          simpa using this
      rw [hVK, Subgroup.mem_bot] at hu
      calc j * v = (v * j * v⁻¹ * j⁻¹) * (j * v) * 1 := by rw [hu]; group
        _ = v * j := by group
    subst hv1
    have hx2 : x = a * e := by rw [hxform]; group
    rw [hx2]
    calc a * e * r = a * (e * r) := by group
      _ = a * (r * e) := by rw [hEc e he r hr]
      _ = (a * r) * e := by group
      _ = (r * a) * e := by rw [hAc a ha r hr]
      _ = r * (a * e) := by group
  have hKcore : pCoreOf 2 Kb = ⊥ := pCoreOf_two_eq_bot_of_normal hB Kb
  have hKn : Rb ≤ Subgroup.normalizer (Kb : Set B) := by
    intro r _
    rw [Subgroup.normalizer_eq_top_iff.mpr hK]
    exact Subgroup.mem_top r
  exact centralizer_of_centralizes_genFitting hR2 hKn hKcore hPF

end Main

end CFSG.Quasithin
