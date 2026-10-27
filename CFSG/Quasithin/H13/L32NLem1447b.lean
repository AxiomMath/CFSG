module

public import CFSG.Quasithin.H13.L32NLem1447a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace L1447

variable {G : Type} [Group G]

theorem eq_oTwoUpper_sup [Finite G] {X S : Subgroup G} (hS : IsSylowTwoOf S X) :
    X = oTwoUpper X ⊔ S := by
  classical
  have hNX : X ≤ Subgroup.normalizer (oTwoUpper X : Set G) := le_normalizer_oTwoUpper X
  have hnorm : ((oTwoUpper X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNX
  have hQ : IsPGroup 2 (↥X ⧸ (oTwoUpper X).subgroupOf X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  set f : ↥X →* (↥X ⧸ (oTwoUpper X).subgroupOf X) := QuotientGroup.mk' _ with hf
  have hdvd := Subgroup.index_map_dvd (H := S.subgroupOf X) (f := f)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ.index ((S.subgroupOf X).map f)
  have h1 : ((S.subgroupOf X).map f).index = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exfalso
      refine hS.2.2 ?_
      rw [hn] at hdvd
      exact (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
  rw [Subgroup.index_eq_one] at h1
  refine le_antisymm (fun x hx => ?_) (sup_le (oTwoUpper_le X) hS.1)
  have hmem : f ⟨x, hx⟩ ∈ (S.subgroupOf X).map f := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp hmem
  have h2 : (t : ↥X)⁻¹ * ⟨x, hx⟩ ∈ (oTwoUpper X).subgroupOf X := by
    rw [← QuotientGroup.eq]
    exact hteq
  have h3 : (t : G)⁻¹ * x ∈ oTwoUpper X := Subgroup.mem_subgroupOf.mp h2
  have h4 : x = (t : G) * ((t : G)⁻¹ * x) := by group
  have h5 : x ∈ S ⊔ oTwoUpper X := by
    rw [h4]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp ht) h3
  rwa [sup_comm] at h5

theorem isSylowTwoOf_of_le [Finite G] {T X : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTX : T ≤ X) : IsSylowTwoOf T X := by
  refine ⟨hTX, hT.1, fun h => hT.2 ?_⟩
  rw [← Subgroup.relIndex_mul_index hTX]
  exact Dvd.dvd.mul_right h _

theorem conj_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : CFSG.conjugate X g = X := by
  ext y
  rw [mem_conj]
  constructor
  · intro h
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp h
    simpa [mul_assoc] using this
  · exact fun h => (Subgroup.mem_normalizer_iff.mp hg y).mp h

end L1447

namespace L144B.Base

open L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
variable (C : Base G T L V V₂ g)
include C

theorem sup_conj_T : L ⊔ CFSG.conjugate T g = L ⊔ T := by
  have h1 : CFSG.conjugate (L ⊔ T) g = L ⊔ T :=
    conj_eq_of_mem_normalizer (Subgroup.le_normalizer C.g_mem_LT)
  have h2 : CFSG.conjugate (L ⊔ T) g = CFSG.conjugate L g ⊔ CFSG.conjugate T g :=
    Subgroup.map_sup _ _ _
  rw [← h1, h2, conj_eq_of_mem_normalizer C.gL]

theorem Tg_le_Hg : CFSG.conjugate T g ≤ CFSG.conjugate (l32nH T V) g := fun _ ht =>
  mem_conj.mpr (C.TH (mem_conj.mp ht))

theorem Tg_le_NL : CFSG.conjugate T g ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  intro t ht
  have h1 : g * t * g⁻¹ ∈ Subgroup.normalizer (L : Set G) := S.TL (mem_conj.mp ht)
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ C.gL) h1) C.gL
  simpa [mul_assoc] using this

theorem Q_le_T : pCoreOf 2 (l32nH T V) ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le C.hyp.fsu.sylow C.TH)

theorem cdL_eq_bot (h12213 : Stmt12_2_13) (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g)
    (hF3 : F3 T V V₂ g⁻¹) : dG T V g ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨_, S⟩ := C.set14
  set X : Subgroup G := Subgroup.closure {y | ∃ h ∈ CFSG.conjugate (l32nH T V) g,
    ∃ w ∈ l32nW T V V₂, y = h * w * h⁻¹} with hX
  have hXD : ∀ y ∈ X, ∀ d ∈ dG T V g, y * d = d * y := by
    intro y hy d hd
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, w, hw, rfl⟩ := hy
      have hd' : h⁻¹ * d * h⁻¹⁻¹ ∈ dG T V g := dG_normal (Subgroup.inv_mem _ hh) hd
      have hc := C.dG_comm_W hF1 hF2 hd' hw
      calc h * w * h⁻¹ * d = h * (w * (h⁻¹ * d * h⁻¹⁻¹)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * d * h⁻¹⁻¹) * w) * h⁻¹ := by rw [hc]
        _ = d * (h * w * h⁻¹) := by group
    | one => simp
    | mul y y' _ _ hy hy' =>
      calc y * y' * d = y * (y' * d) := by group
        _ = y * (d * y') := by rw [hy']
        _ = (y * d) * y' := by group
        _ = d * y * y' := by rw [hy]
        _ = d * (y * y') := by group
    | inv y _ hy =>
      calc y⁻¹ * d = y⁻¹ * (d * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * d) * y⁻¹ := by rw [hy]
        _ = d * y⁻¹ := by group
  by_contra hne
  set C₀ := dG T V g ⊓ Subgroup.centralizer (L : Set G) with hC₀
  have hC₀2 : IsPGroup 2 C₀ := fun c => by
    obtain ⟨k, hk⟩ := C.dG_pow c.2.1
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (C₀ : Set G) := by
    rw [← C.sup_conj_T]
    refine sup_le (fun l hl => ?_) (fun t ht => ?_)
    · refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨fun hc => ?_, fun hc => ?_⟩
      · have := Subgroup.mem_centralizer_iff.mp hc.2 l hl
        rw [this]
        simpa using hc
      · have h1 : l * c * l⁻¹ ∈ Subgroup.centralizer (L : Set G) := hc.2
        have h2 := Subgroup.mem_centralizer_iff.mp h1 l hl
        have h3 : l * c * l⁻¹ = c := mul_left_cancel (h2.trans (by group))
        exact h3 ▸ hc
    · have htH := C.Tg_le_Hg ht
      have htL := C.Tg_le_NL ht
      refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨fun hc => ⟨dG_normal htH hc.1, ?_⟩,
        fun hc => ⟨?_, ?_⟩⟩
      · refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
        have hl' : t⁻¹ * l * t⁻¹⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) l).mp hl
        have hc' := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
        calc l * (t * c * t⁻¹) = t * ((t⁻¹ * l * t⁻¹⁻¹) * c) * t⁻¹ := by group
          _ = t * (c * (t⁻¹ * l * t⁻¹⁻¹)) * t⁻¹ := by rw [hc']
          _ = t * c * t⁻¹ * l := by group
      · have := dG_normal (Subgroup.inv_mem _ htH) hc.1
        simpa [mul_assoc] using this
      · refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
        have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL l).mp hl
        have hc' := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
        calc l * c = t⁻¹ * ((t * l * t⁻¹) * (t * c * t⁻¹)) * t := by group
          _ = t⁻¹ * ((t * c * t⁻¹) * (t * l * t⁻¹)) * t := by rw [hc']
          _ = c * l := by group
  have huniq := (stmt13_3_2_two_of_stmt13_3_2 C.h1332 G T L C.hyp.hyp.h13 L
    C.hyp.hyp.h13.faithful).2.2.2
  obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
    (⟨C₀, hne, hC₀2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₀ : Set G)))
  have hM'eq := huniq M' hM' (hLTN.trans hNM')
  have hNL : Subgroup.normalizer (C₀ : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    hM'eq ▸ hNM'
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    refine fun y hy => hNL (Subgroup.mem_normalizer_iff.mpr fun c => ⟨fun hc => ?_, fun hc => ?_⟩)
    · rw [hXD y hy c hc.1]
      simpa using hc
    · have hcd : c ∈ dG T V g := by
        have h1 := hXD y hy _ hc.1
        have : c = y * c * y⁻¹ := by
          calc c = y⁻¹ * ((y * c * y⁻¹) * y) := by group
            _ = y⁻¹ * (y * (y * c * y⁻¹)) := by rw [h1]
            _ = y * c * y⁻¹ := by group
        rw [this]
        exact hc.1
      refine ⟨hcd, ?_⟩
      have h1 := hXD y hy c hcd
      have : c = y * c * y⁻¹ := by rw [h1]; group
      rw [this]
      exact hc.2
  have hgen : ∀ y ∈ {y | ∃ h ∈ l32nH T V, ∃ w ∈ CFSG.conjugate (l32nW T V V₂) g⁻¹,
      y = h * w * h⁻¹}, y ∈ Subgroup.normalizer (L : Set G) := by
    rintro y ⟨h, hh, w, hw, rfl⟩
    have h1 : g⁻¹ * h * g ∈ CFSG.conjugate (l32nH T V) g := mem_conj.mpr (by group; exact hh)
    have h2 : g⁻¹ * w * g ∈ l32nW T V V₂ := by
      have := mem_conj.mp hw
      simpa using this
    have h3 : g⁻¹ * (h * w * h⁻¹) * g ∈ X := by
      refine Subgroup.subset_closure ⟨_, h1, _, h2, ?_⟩
      group
    have h4 := hXL h3
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ C.gL h4) (Subgroup.inv_mem _ C.gL)
    simpa [mul_assoc] using this
  have hKL : oTwoUpper (l32nH T V) ≤ Subgroup.normalizer (L : Set G) :=
    hF3.trans (sup_le ((Subgroup.closure_le _).mpr hgen) (C.Q_le_T.trans S.TL))
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 C.h1332
  have hV := stmtL32NModule_of_inputs C.h1332 C.h1334
  have h1283 := lemma12_8_3 h12213 G T L V 3 (C.hyp.hyp1281One h13322 hV)
  exact h1283.2.2.2 _ (C.hyp.isTSub_fsuV1 hV)
    ((eq_oTwoUpper_sup (isSylowTwoOf_of_le C.hyp.fsu.sylow C.TH)).le.trans (sup_le hKL S.TL))

end L144B.Base

end CFSG.Quasithin.H13
