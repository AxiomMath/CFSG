module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def RT8One (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L),
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
    v1Sub D.M V₀ V h.hyp151.isElemAbelian L = ⊥ →
    s15 D.M V₀ V h.hyp151.isElemAbelian L = 4 →
    3 ≤ gamma15 D.M V₀ V h.hyp151.isElemAbelian L →
    ∀ u : G, u ∈ D.M → u * u = 1 →
      (suppAct (wConj D.M V₀ V h.hyp151.isElemAbelian L) u).ncard ≤ 3 →
      (∀ E ∈ suppAct (wConj D.M V₀ V h.hyp151.isElemAbelian L) u,
        conjSubgroup E u = E ∧ E3.mQuot E (E ⊓ centralizer ({u} : Set G)) = 1) →
      ∀ a ∈ V, a * u * a⁻¹ * u⁻¹ ≠ 1 →
        centralizer ({a * u * a⁻¹ * u⁻¹} : Set G) ≤ D.M

private theorem s15_T8_conjSubgroup_le_centralizer {X : Subgroup G} {g u v : G}
    (hu : u = g * v * g⁻¹)
    (h : conjSubgroup X g ≤ Subgroup.centralizer ({v} : Set G)) :
    X ≤ Subgroup.centralizer ({u} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hx' : g⁻¹ * x * g ∈ conjSubgroup X g := by
    rw [mem_conjSubgroup_iff]
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  have h2 : (g⁻¹ * x * g) * v = v * (g⁻¹ * x * g) :=
    (Subgroup.mem_centralizer_singleton_iff).1 (h hx')
  calc x * u = g * ((g⁻¹ * x * g) * v) * g⁻¹ := by rw [hu]; group
    _ = g * (v * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
    _ = u * x := by rw [hu]; group

private theorem s15_T8_conjSubgroup_centralizer_singleton (g u v : G) (h : u = g * v * g⁻¹) :
    conjSubgroup (Subgroup.centralizer ({u} : Set G)) g =
      Subgroup.centralizer ({v} : Set G) := by
  ext x
  rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * v = g⁻¹ * ((g * x * g⁻¹) * u) * g := by rw [h]; group
      _ = g⁻¹ * (u * (g * x * g⁻¹)) * g := by rw [hx]
      _ = v * x := by rw [h]; group
  · intro hx
    calc (g * x * g⁻¹) * u = g * (x * v) * g⁻¹ := by rw [h]; group
      _ = g * (v * x) * g⁻¹ := by rw [hx]
      _ = u * (g * x * g⁻¹) := by rw [h]; group

theorem rt8_of_one {D : Data G} (h : RT8One D) : RT8 D := by
  intro V₀ V L h154 hL hV1 hs4 hγ g v hv hv2 hsupp hfix a ha hc
  have hV := h154.hyp151.isElemAbelian
  set u : G := g * v * g⁻¹ with hu
  set a' : G := g * a * g⁻¹ with ha'
  have huM : u ∈ D.M := by
    rw [hu]
    exact mem_conjSubgroup_iff.1 hv
  have hu2 : u * u = 1 := by
    rw [hu, show g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ by group, hv2]
    group
  have ha'V : a' ∈ V := by
    rw [ha']
    exact mem_conjSubgroup_iff.1 ha
  have hz' : a' * u * a'⁻¹ * u⁻¹ = g * (a * v * a⁻¹ * v⁻¹) * g⁻¹ := by
    rw [ha', hu]; group
  have hc' : a' * u * a'⁻¹ * u⁻¹ ≠ 1 := by
    rw [hz']
    intro h1
    apply hc
    have h2 := congrArg (fun x => g⁻¹ * x * g) h1
    rw [show g⁻¹ * (g * (a * v * a⁻¹ * v⁻¹) * g⁻¹) * g =
      a * v * a⁻¹ * v⁻¹ by group] at h2
    simpa using h2
  have hinj : Function.Injective (fun X : Subgroup G => conjSubgroup X g) := by
    intro A B hAB
    have := congrArg (fun Z => conjSubgroup Z g⁻¹) hAB
    simpa only [conjSubgroup_conjSubgroup_inv] using this
  have hsub : (fun X => conjSubgroup X g) '' suppAct (wConj D.M V₀ V hV L) u ⊆
      suppAct (wConjG D.M V₀ V hV L g) v := by
    rintro Y ⟨X, hX, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [mem_wConjG]
      exact ⟨X, hX.1, rfl⟩
    · intro hle
      exact hX.2 (s15_T8_conjSubgroup_le_centralizer hu hle)
  have hncard : (suppAct (wConj D.M V₀ V hV L) u).ncard ≤ 3 := by
    calc (suppAct (wConj D.M V₀ V hV L) u).ncard
        = ((fun X => conjSubgroup X g) '' suppAct (wConj D.M V₀ V hV L) u).ncard :=
          (Set.ncard_image_of_injective _ hinj).symm
      _ ≤ (suppAct (wConjG D.M V₀ V hV L g) v).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 3 := hsupp
  have hfix' : ∀ E' ∈ suppAct (wConj D.M V₀ V hV L) u,
      conjSubgroup E' u = E' ∧ E3.mQuot E' (E' ⊓ centralizer ({u} : Set G)) = 1 := by
    intro E' hE'
    set E : Subgroup G := conjSubgroup E' g with hEdef
    have hEmem : E ∈ suppAct (wConjG D.M V₀ V hV L g) v := by
      rw [hEdef]
      exact hsub ⟨E', hE', rfl⟩
    obtain ⟨hEfix, hEmq⟩ := hfix E hEmem
    have hEu : conjSubgroup E' u = E' := by
      refine hinj ?_
      calc conjSubgroup (conjSubgroup E' u) g = conjSubgroup E' (u * g) :=
            conjSubgroup_conjSubgroup E' u g
        _ = conjSubgroup E' (g * v) := by
              congr 1
              rw [hu]; group
        _ = conjSubgroup (conjSubgroup E' g) v := (conjSubgroup_conjSubgroup E' g v).symm
        _ = conjSubgroup E v := by rw [hEdef]
        _ = E := hEfix
        _ = conjSubgroup E' g := hEdef
    have hcent : conjSubgroup (E' ⊓ Subgroup.centralizer ({u} : Set G)) g =
        E ⊓ Subgroup.centralizer ({v} : Set G) := by
      rw [E3.conjSubgroup_inf, hEdef, s15_T8_conjSubgroup_centralizer_singleton g u v hu]
    have hmq : E3.mQuot E' (E' ⊓ Subgroup.centralizer ({u} : Set G)) = 1 := by
      have h1 := E3.mQuot_conjSubgroup E' (E' ⊓ Subgroup.centralizer ({u} : Set G)) g
      rw [← hEdef, hcent, hEmq] at h1
      exact h1.symm
    exact ⟨hEu, hmq⟩
  have hres := h V₀ V L h154 hL hV1 hs4 hγ u huM hu2 hncard hfix' a' ha'V hc'
  have hconv : conjSubgroup (Subgroup.centralizer ({a' * u * a'⁻¹ * u⁻¹} : Set G)) g ≤
      conjSubgroup D.M g := E3.conjSubgroup_mono_left g hres
  rw [s15_T8_conjSubgroup_centralizer_singleton g (a' * u * a'⁻¹ * u⁻¹)
    (a * v * a⁻¹ * v⁻¹) hz'] at hconv
  exact hconv

theorem s15_T8_transvection (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hL : barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥) (h1217 : R1217 D)
    (hV1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L = ⊥) {u : G} (hu : u ∈ D.M)
    (hu2 : u * u = 1)
    (hfix : ∀ E ∈ suppAct (wConj D.M V₀ V h.hyp151.isElemAbelian L) u,
      conjSubgroup E u = E ∧ E3.mQuot E (E ⊓ centralizer ({u} : Set G)) = 1)
    {a : G} (ha : a ∈ V) (hc : a * u * a⁻¹ * u⁻¹ ≠ 1) :
    ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) V h.hyp151.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.hyp151.isElemAbelian L) := by
  have hleV0 : V₀ ≤ v1Sub D.M V₀ V h.hyp151.isElemAbelian L :=
    s15_Infra_le_v1Sub D.M V₀ V h.hyp151.isElemAbelian L
  have hV0 : V₀ = ⊥ := le_bot_iff.1 (by rwa [hV1] at hleV0)
  obtain rfl : V₀ = ⊥ := hV0
  have hV := h.hyp151.isElemAbelian
  have hV1' : v1Sub D.M ⊥ V hV L = ⊥ := hV1
  have hW0leV : wSub ⊥ V hV L ≤ V := preTil_le ⊥ V hV (wTil ⊥ V hV L)
  have hex : ∃ E ∈ wConj D.M ⊥ V hV L, ¬ E ≤ Subgroup.centralizer ({u} : Set G) := by
    by_contra hcon
    have hle : (⨆ X ∈ wConj D.M ⊥ V hV L, X) ≤ Subgroup.centralizer ({u} : Set G) :=
      iSup₂_le fun X hX => by
        by_contra hXC
        exact hcon ⟨X, hX, hXC⟩
    have hgen : (⨆ X ∈ wConj D.M ⊥ V hV L, X) = V :=
      iSup_wConj_eq D h1217 h.hyp151 hV hL
    have hau : a * u = u * a :=
      (Subgroup.mem_centralizer_singleton_iff).1 (hle (hgen.symm ▸ ha))
    exact hc (by rw [hau]; group)
  obtain ⟨E, hEw, hEC⟩ := hex
  have hEmem : E ∈ suppAct (wConj D.M ⊥ V hV L) u := ⟨hEw, hEC⟩
  obtain ⟨m, hm, hEeq⟩ := hEw
  obtain ⟨hEfix, hEmq⟩ := hfix E hEmem
  obtain ⟨e, heE, heC⟩ : ∃ e ∈ E, e ∉ Subgroup.centralizer ({u} : Set G) := by
    by_contra hcon
    exact hEC fun e he => by
      by_contra heC
      exact hcon ⟨e, he, heC⟩
  have heu : u * e * u⁻¹ ≠ e := by
    intro heq
    apply heC
    have h2 : e * u = u * e := by
      calc e * u = (u * e * u⁻¹) * u := by rw [heq]
        _ = u * e := by group
    exact (Subgroup.mem_centralizer_singleton_iff).2 h2
  set x : G := m * u * m⁻¹ with hx
  have hxM : x ∈ D.M := by
    rw [hx]
    exact D.M.mul_mem (D.M.mul_mem hm hu) (D.M.inv_mem hm)
  have hW0 : conjSubgroup E m⁻¹ = wSub ⊥ V hV L := by
    rw [hEeq, conjSubgroup_conjSubgroup_inv]
  have hxW : conjSubgroup (wSub ⊥ V hV L) x = wSub ⊥ V hV L := by
    have h1 : conjSubgroup (wSub ⊥ V hV L) (m * u * m⁻¹) = conjSubgroup E m⁻¹ := by
      calc conjSubgroup (wSub ⊥ V hV L) (m * u * m⁻¹)
          = conjSubgroup (conjSubgroup (wSub ⊥ V hV L) m) (u * m⁻¹) := by
            rw [show m * u * m⁻¹ = m * (u * m⁻¹) by group, conjSubgroup_conjSubgroup]
        _ = conjSubgroup (conjSubgroup (conjSubgroup (wSub ⊥ V hV L) m) u) m⁻¹ :=
            (conjSubgroup_conjSubgroup (conjSubgroup (wSub ⊥ V hV L) m) u m⁻¹).symm
        _ = conjSubgroup (conjSubgroup E u) m⁻¹ := by rw [hEeq]
        _ = conjSubgroup E m⁻¹ := by rw [hEfix]
    rw [hx, h1]
    exact hW0
  have hxV1 : conjSubgroup (v1Sub D.M ⊥ V hV L) x = v1Sub D.M ⊥ V hV L :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV hxM)
  have hxN : x ∈ normalizer (((wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L : Subgroup G)) : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, s15_T7_conjSubgroup_sup, hxW, hxV1]
  set F : Subgroup G := Subgroup.zpowers x with hF
  have hFM : F ≤ D.M := by rw [hF]; exact Subgroup.zpowers_le.2 hxM
  have hFN : F ≤ normalizer (((wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L : Subgroup G)) : Set G) := by
    rw [hF]; exact Subgroup.zpowers_le.2 hxN
  set K₀ : Subgroup G := conjSubgroup (E ⊓ Subgroup.centralizer ({u} : Set G)) m⁻¹ with hK₀
  have hK₀W : K₀ ≤ wSub ⊥ V hV L := by
    rw [hK₀]
    have h1 := E3.conjSubgroup_mono_left m⁻¹ (inf_le_left :
      E ⊓ Subgroup.centralizer ({u} : Set G) ≤ E)
    rwa [hW0] at h1
  have hmK₀ : E3.mQuot (wSub ⊥ V hV L) K₀ = 1 := by
    have h1 := E3.mQuot_conjSubgroup E (E ⊓ Subgroup.centralizer ({u} : Set G)) m⁻¹
    rw [hW0, ← hK₀] at h1
    rw [h1, hEmq]
  have hKle : imgTil (v1Sub D.M ⊥ V hV L) V hV K₀ ≤ wStar D.M ⊥ V hV L :=
    s15_LP_imgTil_mono hV hK₀W
  have hmK : E3.mQuot (wStar D.M ⊥ V hV L)
      (imgTil (v1Sub D.M ⊥ V hV L) V hV K₀) ≤ 1 :=
    (s15_LP_mQuot_imgTil_le hV hK₀W hW0leV).trans hmK₀.le
  have hxs1 : x ∈ stabTil (v1Sub D.M ⊥ V hV L) V :=
    s15_T7_le_stabTil_v1Sub h.hyp151 hxM
  set φ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV) :=
    actTil (v1Sub D.M ⊥ V hV L) V hV ⟨x, hxs1⟩ with hφdef
  have hφF : φ ∈ barSub (v1Sub D.M ⊥ V hV L) V hV F := by
    rw [hφdef]
    exact actTil_mem_barSub (v1Sub D.M ⊥ V hV L) V hV (X := F)
      (Subgroup.mem_zpowers x) hxs1
  have hφstab : φ ∈ stabSub (wStar D.M ⊥ V hV L) :=
    s15_T7_barSub_le_stabSub_wStar D h.hyp151 hFM hFN hφF
  have hxfix : ∀ z ∈ K₀, x * z * x⁻¹ = z := by
    intro z hz
    have hzm : m⁻¹ * z * m ∈ E ⊓ Subgroup.centralizer ({u} : Set G) := by
      rw [hK₀] at hz
      have h := mem_conjSubgroup_iff.1 hz
      simpa using h
    have hzC : (m⁻¹ * z * m) * u = u * (m⁻¹ * z * m) :=
      (Subgroup.mem_centralizer_singleton_iff).1 hzm.2
    have hconj : u * (m⁻¹ * z * m) * u⁻¹ = m⁻¹ * z * m := by
      rw [← hzC]; group
    have hzeq : z = m * (m⁻¹ * z * m) * m⁻¹ := by group
    calc x * z * x⁻¹ = m * (u * (m⁻¹ * z * m) * u⁻¹) * m⁻¹ := by rw [hx, hzeq]; group
      _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [hconj]
      _ = z := hzeq.symm
  have hφK : ∀ k ∈ imgTil (v1Sub D.M ⊥ V hV L) V hV K₀, φ k = k := by
    intro k hk
    obtain ⟨z, hzK₀, rfl⟩ := (mem_imgTil (v1Sub D.M ⊥ V hV L) V hV K₀ k).1 hk
    rw [hφdef, actTil_mk]
    have hz : actStab (v1Sub D.M ⊥ V hV L) V hV ⟨x, hxs1⟩ z = z :=
      IntMod.val_injective (by rw [actStab_apply_val, hxfix z.val hzK₀])
    rw [hz]
  have hmove : ∃ q ∈ wStar D.M ⊥ V hV L, φ q ≠ q := by
    have hwW : m * e * m⁻¹ ∈ wSub ⊥ V hV L := by
      rw [hEeq] at heE
      exact mem_conjSubgroup_iff.1 heE
    have hwV : m * e * m⁻¹ ∈ V := hW0leV hwW
    refine ⟨mkTil (v1Sub D.M ⊥ V hV L) V hV (IntMod.mk hV ⟨m * e * m⁻¹, hwV⟩), ?_, ?_⟩
    · exact (mem_imgTil (v1Sub D.M ⊥ V hV L) V hV (wSub ⊥ V hV L) _).2
        ⟨IntMod.mk hV ⟨m * e * m⁻¹, hwV⟩, hwW, rfl⟩
    · have hne' : x * (m * e * m⁻¹) * x⁻¹ ≠ m * e * m⁻¹ := by
        intro heq
        exact heu (by
          have h2 := congrArg (fun z => m⁻¹ * z * m) heq
          rw [hx] at h2
          calc u * e * u⁻¹
              = m⁻¹ * (m * u * m⁻¹ * (m * e * m⁻¹) * (m * u * m⁻¹)⁻¹) * m := by group
            _ = m⁻¹ * (m * e * m⁻¹) * m := by rw [h2]
            _ = e := by group)
      intro hq
      rw [hφdef, actTil_mk] at hq
      apply hne'
      have h1 := (mkTil_eq_iff (v1Sub D.M ⊥ V hV L) V hV
        (actStab (v1Sub D.M ⊥ V hV L) V hV ⟨x, hxs1⟩
          (IntMod.mk hV ⟨m * e * m⁻¹, hwV⟩))
        (IntMod.mk hV ⟨m * e * m⁻¹, hwV⟩)).1 hq
      rw [actStab_apply_val] at h1
      have h2 : (x * (m * e * m⁻¹) * x⁻¹) * (m * e * m⁻¹)⁻¹ = 1 :=
        Subgroup.mem_bot.1 (hV1' ▸ h1)
      exact mul_inv_eq_one.1 h2
  refine ⟨φ, ?_, ?_⟩
  · rw [hφdef]
    exact actTil_mem_barSub (v1Sub D.M ⊥ V hV L) V hV (X := D.M) hxM hxs1
  · exact s15_T7_inducesTransvection (s15_LP_vtil_sq_eq_one (v1Sub D.M ⊥ V hV L) V hV)
      hKle hmK hφstab hφK hmove

theorem s15_T8_caseThree (D : Data G) (h153 : R15_3 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hs4 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 4)
    (htr : ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) V h.hyp151.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.hyp151.isElemAbelian L)) :
    Case153_3 D V₀ V h.hyp151.isElemAbelian L := by
  rcases h153 V₀ V L h.hyp151 htr with h1 | h2 | h3
  · obtain ⟨-, -, -, -, h1s, -⟩ := h1
    omega
  · exfalso
    obtain ⟨K₀, p, -, -, -, -, -, hrs, -⟩ := h2
    rw [hs4] at hrs
    have hne : (conjSet (barSub V₀ V h.hyp151.isElemAbelian K₀)
        (Mbar D.M V₀ V h.hyp151.isElemAbelian ⊓
          normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _))).Nonempty :=
      ⟨barSub V₀ V h.hyp151.isElemAbelian K₀, 1, Subgroup.one_mem _, by ext x; simp⟩
    have hpos := (Set.ncard_pos (Set.toFinite _)).2 hne
    omega
  · exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
