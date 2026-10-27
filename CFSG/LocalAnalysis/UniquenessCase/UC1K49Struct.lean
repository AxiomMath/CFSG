module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Setup
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofAlt1C
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7LemmaS
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjugate_conjugate (L : Subgroup G) (y x : G) :
    CFSG.conjugate (CFSG.conjugate L y) x = CFSG.conjugate L (y * x) := by
  have h : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom =
      (MulAut.conj (y * x)⁻¹).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    group
  rw [CFSG.conjugate, CFSG.conjugate, CFSG.conjugate, Subgroup.map_map, h]

theorem conjugate_le_of_mem_normalizer {H L : Subgroup G} (hLH : L ≤ H) {x : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) : CFSG.conjugate L x ≤ H := by
  have hx' : x⁻¹ ∈ Subgroup.normalizer (H : Set G) := (Subgroup.normalizer _).inv_mem hx
  have hmap : H.map (MulAut.conj x⁻¹).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx'
  exact (Subgroup.map_mono hLH).trans hmap.le

theorem le_normalizer_iSup {ι : Type*} {S : Subgroup G} {K : ι → Subgroup G}
    (h : ∀ i, S ≤ Subgroup.normalizer (K i : Set G)) :
    S ≤ Subgroup.normalizer (⨆ i, K i : Subgroup G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => Subgroup.mem_normalizer_iff_map_conj_eq.mp (h i hg)

@[expose] noncomputable def I49 (L X : Subgroup G) : Subgroup G :=
  ⨆ x : X, CFSG.conjugate L (x : G)

theorem I49_eq (L X : Subgroup G) :
    I49 L X = ⨆ x ∈ X, CFSG.conjugate L x := by
  rw [I49, iSup_subtype]

theorem conjugate_mem_oTwoComponentsIn {H L : Subgroup G}
    (hL : L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H) {x : G} (hx : x ∈ H) :
    CFSG.conjugate L x ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H := by
  have hx' : x⁻¹ ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer (H.inv_mem hx)
  have hmap : Subgroup.map (MulAut.conj x⁻¹).toMonoidHom H = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx'
  have h := CFSG.RankThree.PartTwo.map_mem_oTwoComponentsIn (MulAut.conj x⁻¹) hL
  rwa [hmap] at h

omit [Finite G] in
theorem isAlt_bar2_conjugate {L : Subgroup G} (h : IsAlt (Bar2 L) 5) (x : G) :
    IsAlt (Bar2 (CFSG.conjugate L x)) 5 := by
  obtain ⟨e⟩ := h
  exact ⟨(CFSG.RankThree.PartTwo.Sec18.Item18ResProof.nonempty_quotient_map_conj x⁻¹ e).some⟩

theorem pCoreOf_le_normalizer_of_mem_oTwoComponentsIn {H L : Subgroup G}
    (hL : L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H) :
    CFSG.Open.pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) := by
  have hres : CFSG.inSubgroup CFSG.perfectResidual (L ⊔ CFSG.Open.pCoreOf 2 H) = L :=
    CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_sup_pCoreOf hL
  have hchar : (CFSG.perfectResidual (L ⊔ CFSG.Open.pCoreOf 2 H : Subgroup G)).Characteristic :=
    (CFSG.perfect_residual_characterization (G := (L ⊔ CFSG.Open.pCoreOf 2 H : Subgroup G))).2.1
  have hnorm : (L ⊔ CFSG.Open.pCoreOf 2 H : Subgroup G) ≤
      Subgroup.normalizer
        (CFSG.inSubgroup CFSG.perfectResidual (L ⊔ CFSG.Open.pCoreOf 2 H) : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.perfectResidual (L ⊔ CFSG.Open.pCoreOf 2 H : Subgroup G)))
  rw [hres] at hnorm
  exact le_sup_right.trans hnorm

theorem pCoreOf_le_normalizer_conjugate {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : x ∈ X) : Q ≤ Subgroup.normalizer (CFSG.conjugate L x : Set G) := by
  rw [h.Q_eq]
  exact pCoreOf_le_normalizer_of_mem_oTwoComponentsIn
    (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hx))

theorem conjugate_inf_pCoreOf_eq {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : x ∈ X) :
    CFSG.conjugate L x ⊓ Q = CFSG.Open.pCoreOf 2 (CFSG.conjugate L x) := by
  have hmem : CFSG.conjugate L x ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H :=
    conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hx)
  rw [h.Q_eq]
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · refine (le_inf Subgroup.le_normalizer ?_).trans
        Subgroup.inf_normalizer_le_normalizer_inf
      exact (conjugate_le_of_mem_normalizer
        (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn h.L_mem)
        (Subgroup.le_normalizer (h.X_le hx))).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hmem)

theorem I_le_H {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) : I ≤ H := by
  rw [h.I_eq]
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact conjugate_le_of_mem_normalizer
    (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn h.L_mem)
    (Subgroup.le_normalizer (h.X_le hx))

theorem le_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) : L ≤ I := by
  have h1 : CFSG.conjugate L (1 : G) = L := by
    rw [CFSG.conjugate]
    have : (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
      ext z; simp [MulAut.conj_apply]
    rw [this, Subgroup.map_id]
  have hI : I = I49 L X := h.I_eq.trans (I49_eq L X).symm
  rw [hI, I49]
  exact h1.ge.trans (le_iSup (fun x : X => CFSG.conjugate L (x : G)) ⟨1, X.one_mem⟩)

theorem eq_sup_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    H = I ⊔ X ⊔ Q := by
  refine le_antisymm ?_ ?_
  · rw [h.H_eq]
    refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact (le_sup_right : X ≤ I ⊔ X).trans le_sup_left
    · exact ((le_I h).trans (le_sup_left : I ≤ I ⊔ X)).trans le_sup_left
  · refine sup_le (sup_le ?_ h.X_le) ?_
    · exact I_le_H h
    · exact h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)

theorem le_normalizer_I_of_le {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {S : Subgroup G} (hS : ∀ x : X, S ≤ Subgroup.normalizer (CFSG.conjugate L (x : G) : Set G)) :
    S ≤ Subgroup.normalizer (I : Set G) := by
  have hI : I = I49 L X := h.I_eq.trans (I49_eq L X).symm
  rw [hI]
  exact le_normalizer_iSup hS

theorem le_normalizer_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    H ≤ Subgroup.normalizer (I : Set G) := by
  have hL : L ≤ Subgroup.normalizer (I : Set G) := by
    refine le_normalizer_I_of_le h fun x => ?_
    by_cases hx : CFSG.conjugate L (x : G) = L
    · rw [hx]; exact Subgroup.le_normalizer
    · intro g hg
      refine CFSG.RankThree.PartTwo.Sec18.Item18ResProof.mem_normalizer_of_commutator_mem
        (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le x.2))
        (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn h.L_mem hg) ?_
      intro y hy
      exact CFSG.RankThree.PartTwo.Sec19.Step1910Proof.commutator_mem_pCoreOf h.L_mem
        (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le x.2)) (Ne.symm hx) hg hy
  have hQ : Q ≤ Subgroup.normalizer (I : Set G) :=
    le_normalizer_I_of_le h fun x => pCoreOf_le_normalizer_conjugate h x.2
  have hX : X ≤ Subgroup.normalizer (I : Set G) := by
    intro x hx
    have key : I.map (MulAut.conj x).toMonoidHom ≤ I := by
      rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
      rw [Subgroup.map_iSup]
      refine iSup_le fun y => ?_
      have h1 : (CFSG.conjugate L (y : G)).map (MulAut.conj x).toMonoidHom =
          CFSG.conjugate L ((y : G) * x⁻¹) := by
        simpa only [CFSG.conjugate, inv_inv] using conjugate_conjugate L (y : G) x⁻¹
      rw [h1]
      exact le_iSup (fun z : X => CFSG.conjugate L (z : G))
        ⟨(y : G) * x⁻¹, X.mul_mem y.2 (X.inv_mem hx)⟩
    exact CFSG.RankThree.PartTwo.Sec18.Item18ResProof.mem_normalizer_of_map_conj_le key
  rw [h.H_eq]
  exact sup_le (sup_le hX hL) hQ

theorem commutator_I_eq {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) : ⁅I, I⁆ = I := by
  rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
  exact CFSG.Quasithin.A3.commutator_iSup_eq_of_perfect _
    fun x => CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn
      (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le x.2))

theorem conjugate_one (L : Subgroup G) : CFSG.conjugate L (1 : G) = L := by
  rw [CFSG.conjugate]
  have : (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
    ext z; simp [MulAut.conj_apply]
  rw [this, Subgroup.map_id]

theorem commutator_conjugate_le {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (hne : CFSG.conjugate L x ≠ CFSG.conjugate L y) :
    ⁅CFSG.conjugate L x, CFSG.conjugate L y⁆ ≤ Q := by
  rw [h.Q_eq]
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  exact CFSG.RankThree.PartTwo.Sec19.Step1910Proof.commutator_mem_pCoreOf
    (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hx))
    (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hy)) hne ha hb

theorem conjugate_normalize_of_ne {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (hne : CFSG.conjugate L x ≠ CFSG.conjugate L y) :
    CFSG.conjugate L x ≤ Subgroup.normalizer (CFSG.conjugate L y : Set G) := by
  intro g hg
  refine CFSG.RankThree.PartTwo.Sec18.Item18ResProof.mem_normalizer_of_commutator_mem
    (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hy))
    ((CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn
      (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hx))) hg) ?_
  intro z hz
  exact CFSG.RankThree.PartTwo.Sec19.Step1910Proof.commutator_mem_pCoreOf
    (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hx))
    (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hy)) hne hg hz

private theorem conjugate_sq_ne_conjugate_of_ne {L : Subgroup G} {x : G}
    (hneL : CFSG.conjugate L x ≠ L) :
    CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x := by
  intro hc
  have h1 := congrArg (fun K => CFSG.conjugate K x⁻¹) hc
  rw [conjugate_conjugate, conjugate_conjugate] at h1
  rw [mul_inv_cancel, conjugate_one] at h1
  have hxe : x ^ 2 * x⁻¹ = x := by rw [pow_two, mul_assoc, mul_inv_cancel, mul_one]
  rw [hxe] at h1
  exact hneL h1

theorem exists_generator49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    ∃ x ∈ X, X = Subgroup.zpowers x ∧ CFSG.conjugate L x ≠ L ∧
      CFSG.conjugate L (x ^ 2) ≠ L ∧
      CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x := by
  obtain ⟨x, hxX, hxN⟩ := by
    simpa only [SetLike.le_def, not_forall, not_imp] using h.X_nle
  have hx1 : x ≠ 1 := by rintro rfl; exact hxN (Subgroup.one_mem _)
  have hord : orderOf x ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard X hxX
    rwa [h.card_X] at this
  have hord3 : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h3
  have hx3 : x ^ 3 = 1 := by rw [← hord3]; exact pow_orderOf_eq_one x
  have hgen : X = Subgroup.zpowers x := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) ?_).symm
    rw [h.card_X, Nat.card_zpowers, hord3]
  have hneL : CFSG.conjugate L x ≠ L := by
    intro hc
    apply hxN
    have hx' : x⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [CFSG.conjugate] using hc)
    simpa using (Subgroup.normalizer _).inv_mem hx'
  have hx2N : x ^ 2 ∉ Subgroup.normalizer (L : Set G) := by
    intro h2
    apply hxN
    have h4 : (x ^ 2) ^ 2 ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer _).pow_mem h2 2
    rwa [show (x ^ 2) ^ 2 = x by
      rw [← pow_mul, show (2:ℕ) * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]] at h4
  have hneL2 : CFSG.conjugate L (x ^ 2) ≠ L := by
    intro hc
    apply hx2N
    have hx' : (x ^ 2)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [CFSG.conjugate] using hc)
    simpa using (Subgroup.normalizer _).inv_mem hx'
  have hne2 := conjugate_sq_ne_conjugate_of_ne hneL
  exact ⟨x, hxX, hgen, hneL, hneL2, hne2⟩

theorem mem_sup_of_le_normalizer {s t : Subgroup G}
    (h : s ≤ Subgroup.normalizer (t : Set G)) {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, x, hx, by simp⟩
    · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      have hy₂' : y₂⁻¹ ∈ Subgroup.normalizer (t : Set G) :=
        (Subgroup.normalizer _).inv_mem (h hy₂)
      have hz : y₂⁻¹ * z₁ * y₂ ∈ t := by
        simpa using ((Subgroup.mem_normalizer_iff.mp hy₂') z₁).mp hz₁
      refine ⟨y₁ * y₂, s.mul_mem hy₁ hy₂, (y₂⁻¹ * z₁ * y₂) * z₂,
        t.mul_mem hz hz₂, by group⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      have hz' : y * z⁻¹ * y⁻¹ ∈ t :=
        ((Subgroup.mem_normalizer_iff.mp (h hy)) z⁻¹).mp (t.inv_mem hz)
      refine ⟨y⁻¹, s.inv_mem hy, y * z⁻¹ * y⁻¹, hz', by group⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

theorem center_bar2_eq_bot {L : Subgroup G} (halt : IsAlt (Bar2 L) 5) :
    Subgroup.center (Bar2 L) = ⊥ := by
  obtain ⟨e⟩ := halt
  have h5 : 4 ≤ Nat.card (Fin 5) := by simp [Nat.card_eq_fintype_card]
  have h := alternatingGroup.center_eq_bot (α := Fin 5) h5
  rw [eq_bot_iff] at h
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← e.map_mul, ← e.map_mul, hz a]
  have := h hz'
  rw [Subgroup.mem_bot] at this
  exact e.injective (by simpa using this)

theorem mem_pCoreOf_iff {L : Subgroup G} {x : G} (hx : x ∈ L) :
    x ∈ CFSG.Open.pCoreOf 2 L ↔ (⟨x, hx⟩ : L) ∈ CFSG.pCore 2 L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← this]
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem map_quotient_eq_bot_of_odd_of_isAlt {L M : Subgroup G}
    (hML : M ≤ L) (hMn : (M.subgroupOf L).Normal) (hModd : Odd (Nat.card M))
    (halt : IsAlt (Bar2 L) 5) :
    (M.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
  obtain ⟨e⟩ := halt
  haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
  have hnormal : ((M.subgroupOf L).map π).Normal :=
    hMn.map π (QuotientGroup.mk'_surjective _)
  haveI := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M.subgroupOf L).map π) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card ↥((M.subgroupOf L).map π)) := by
      refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd (M.subgroupOf L) π)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv]
    rw [h, Subgroup.card_top] at hodd
    have hcard : Nat.card (Bar2 L) = Nat.card (alternatingGroup (Fin 5)) :=
      Nat.card_congr e.toEquiv
    rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hodd
    norm_num at hodd

theorem le_pCoreOf_of_odd_of_isAlt {L M : Subgroup G}
    (hML : M ≤ L) (hMn : (M.subgroupOf L).Normal) (hModd : Odd (Nat.card M))
    (halt : IsAlt (Bar2 L) 5) : M ≤ CFSG.Open.pCoreOf 2 L := by
  have hbot := map_quotient_eq_bot_of_odd_of_isAlt hML hMn hModd halt
  have hle : M.subgroupOf L ≤ CFSG.pCore 2 L := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 L)]
    exact (Subgroup.map_eq_bot_iff (M.subgroupOf L)).mp hbot
  calc M = Subgroup.map L.subtype (M.subgroupOf L) := (Subgroup.map_subgroupOf_eq_of_le hML).symm
    _ ≤ Subgroup.map L.subtype (CFSG.pCore 2 L) := Subgroup.map_mono hle
    _ = CFSG.Open.pCoreOf 2 L := rfl

theorem inf_eq_bot_of_odd_of_isPGroup {A B : Subgroup G} (hAodd : Odd (Nat.card ↥A))
    (hB : IsPGroup 2 ↥B) : A ⊓ B = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(A ⊓ B)) :=
    Odd.of_dvd_nat hAodd (Subgroup.card_dvd_of_le inf_le_left)
  have hAB : IsPGroup 2 ↥(A ⊓ B) := hB.to_le inf_le_right
  rcases (IsPGroup.iff_card (p := 2) (G := ↥(A ⊓ B))).mp hAB with ⟨n, hn⟩
  have hn0 : n = 0 := by
    cases n with
    | zero => rfl
    | succ m =>
      exfalso
      rw [pow_succ] at hn
      rw [hn] at hodd
      exact (Nat.not_odd_iff_even.mpr ⟨2 ^ m, by ring⟩) hodd
  rw [hn0, pow_zero] at hn
  exact Subgroup.card_eq_one.mp hn

theorem commutator_eq_bot_of_odd_of_isAlt {K H N : Subgroup G}
    (hKH : K ≤ H) (hKsub : (K.subgroupOf H).IsSubnormal) (hKperf : ⁅K, K⁆ = K)
    (halt : IsAlt (Bar2 K) 5) (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal)
    (hNodd : Odd (Nat.card N)) : ⁅K, N⁆ = ⊥ := by
  haveI : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hNK : N ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.ClassicalInvolution.le_normalizer_of_isSubnormal_of_perfect_of_normal
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hKH).mpr hKsub) hKperf hNH hNn
  have hinf : K ⊓ N = ⊥ := by
    have hnorm : ((K ⊓ N).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      refine le_trans ?_ Subgroup.inf_normalizer_le_normalizer_inf
      exact le_inf Subgroup.le_normalizer
        (hKH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNn))
    have hodd : Odd (Nat.card ↥(K ⊓ N)) :=
      Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_right)
    have hle : K ⊓ N ≤ CFSG.Open.pCoreOf 2 K :=
      le_pCoreOf_of_odd_of_isAlt inf_le_left hnorm hodd halt
    have h := inf_eq_bot_of_odd_of_isPGroup hodd
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    rwa [inf_eq_left.mpr hle] at h
  have hleK : ⁅K, N⁆ ≤ K := by
    refine Subgroup.commutator_le.mpr fun k hk n hn => ?_
    rw [commutatorElement_def]
    have hnk : n * k * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hNK hn) k).mp hk
    have h1 : k * (n * k * n⁻¹)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hnk)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h1
  have hleN : ⁅K, N⁆ ≤ N := by
    refine Subgroup.commutator_le.mpr fun k hk n hn => ?_
    rw [commutatorElement_def]
    have hkn : k * n * k⁻¹ ∈ N :=
      (Subgroup.normal_subgroupOf_iff hNH).mp hNn n k hn (hKH hk)
    exact N.mul_mem hkn (N.inv_mem hn)
  exact le_bot_iff.mp (hinf ▸ le_inf hleK hleN)

theorem mem_zpowers_of_orderOf_eq_three {x y : G} (hx : orderOf x = 3)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hy
  obtain ⟨k, hk, hky⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_range] at hk
  interval_cases k
  · exact Or.inl (by simpa using hky.symm)
  · exact Or.inr (Or.inl (by simpa using hky.symm))
  · exact Or.inr (Or.inr (by simpa using hky.symm))

theorem odd_normal_le_centralizer_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N : Subgroup G} (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal)
    (hNodd : Odd (Nat.card N)) : I ≤ Subgroup.centralizer (N : Set G) := by
  have hI : I = I49 L X := h.I_eq.trans (I49_eq L X).symm
  rw [hI, I49]
  refine iSup_le fun x => ?_
  have hmem := conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le x.2)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_odd_of_isAlt
      (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn hmem)
      (CFSG.RankThree.PartTwo.mem_oTwoComponentsIn_iff.mp hmem).2.2.1
      (CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn hmem)
      (isAlt_bar2_conjugate h.L_alt (x : G)) hNH hNn hNodd)

theorem commutator_first_mem {H Q : Subgroup G} (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    {a b c m : G} (ha : a ∈ H) (hb : b ∈ H)
    (hbQ : ⁅b, m⁆ ∈ Q) (hcQ : ⁅c, m⁆ ∈ Q) (habcQ : ⁅(a * b) * c, m⁆ ∈ Q) :
    ⁅a, m⁆ ∈ Q := by
  have hc' : (a * b) * ⁅c, m⁆ * (a * b)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn (H.mul_mem ha hb)) ⁅c, m⁆).mp hcQ
  have hb' : a * ⁅b, m⁆ * a⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn ha) ⁅b, m⁆).mp hbQ
  have hident : ⁅(a * b) * c, m⁆ =
      ((a * b) * ⁅c, m⁆ * (a * b)⁻¹) * (a * ⁅b, m⁆ * a⁻¹) * ⁅a, m⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul (a * b) c m,
      commutatorElement_mul_left_eq_conj_mul a b m]
    group
  have hprod : ((a * b) * ⁅c, m⁆ * (a * b)⁻¹) * (a * ⁅b, m⁆ * a⁻¹) * ⁅a, m⁆ ∈ Q :=
    hident ▸ habcQ
  have hAB : ((a * b) * ⁅c, m⁆ * (a * b)⁻¹) * (a * ⁅b, m⁆ * a⁻¹) ∈ Q := Q.mul_mem hc' hb'
  have := Q.mul_mem (Q.inv_mem hAB) hprod
  convert this using 1
  group

theorem commutator_middle_mem {H Q : Subgroup G} (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    {a b c m : G} (ha : a ∈ H) (hb : b ∈ H)
    (haQ : ⁅a, m⁆ ∈ Q) (hcQ : ⁅c, m⁆ ∈ Q) (habcQ : ⁅(a * b) * c, m⁆ ∈ Q) :
    ⁅b, m⁆ ∈ Q := by
  have hc' : (a * b) * ⁅c, m⁆ * (a * b)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn (H.mul_mem ha hb)) ⁅c, m⁆).mp hcQ
  have hident : ⁅(a * b) * c, m⁆ =
      ((a * b) * ⁅c, m⁆ * (a * b)⁻¹) * (a * ⁅b, m⁆ * a⁻¹) * ⁅a, m⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul (a * b) c m,
      commutatorElement_mul_left_eq_conj_mul a b m]
    group
  have hprod : ((a * b) * ⁅c, m⁆ * (a * b)⁻¹) * (a * ⁅b, m⁆ * a⁻¹) * ⁅a, m⁆ ∈ Q :=
    hident ▸ habcQ
  have hB : a * ⁅b, m⁆ * a⁻¹ ∈ Q := by
    have := Q.mul_mem (Q.mul_mem (Q.inv_mem hc') hprod) (Q.inv_mem haQ)
    convert this using 1
    group
  have hconj :=
    (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem ha)) (a * ⁅b, m⁆ * a⁻¹)).mp hB
  convert hconj using 1
  group

theorem commutator_third_mem {H Q : Subgroup G} (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    {a b c m : G} (ha : a ∈ H) (hb : b ∈ H)
    (haQ : ⁅a, m⁆ ∈ Q) (hbQ : ⁅b, m⁆ ∈ Q) (habcQ : ⁅(a * b) * c, m⁆ ∈ Q) :
    ⁅c, m⁆ ∈ Q := by
  have hb' : a * ⁅b, m⁆ * a⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn ha) ⁅b, m⁆).mp hbQ
  have hident : ⁅(a * b) * c, m⁆ =
      ((a * b) * ⁅c, m⁆ * (a * b)⁻¹) * (a * ⁅b, m⁆ * a⁻¹) * ⁅a, m⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul (a * b) c m,
      commutatorElement_mul_left_eq_conj_mul a b m]
    group
  have hprod : ((a * b) * ⁅c, m⁆ * (a * b)⁻¹) * (a * ⁅b, m⁆ * a⁻¹) * ⁅a, m⁆ ∈ Q :=
    hident ▸ habcQ
  have hA : (a * b) * ⁅c, m⁆ * (a * b)⁻¹ ∈ Q := by
    have := Q.mul_mem (Q.mul_mem hprod (Q.inv_mem haQ)) (Q.inv_mem hb')
    convert this using 1
    group
  have hconj := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem (H.mul_mem ha hb)))
    ((a * b) * ⁅c, m⁆ * (a * b)⁻¹)).mp hA
  convert hconj using 1
  group

theorem mem_pCoreOf_of_centralizer_mod {K H Q : Subgroup G} (halt : IsAlt (Bar2 K) 5)
    (hKQ : K ⊓ Q = CFSG.Open.pCoreOf 2 K) (hKH : K ≤ H) {k : G} (hk : k ∈ K)
    (hcentral : ∀ m ∈ K, ⁅k, m⁆ ∈ Q) : k ∈ Q := by
  have hcore : (⟨k, hk⟩ : K) ∈ CFSG.pCore 2 K := by
    have hz : QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k, hk⟩ ∈ Subgroup.center (Bar2 K) := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← commutatorElement_eq_one_iff_mul_comm]
      change ⁅(QuotientGroup.mk' (CFSG.pCore 2 K)) ⟨m, hm⟩,
        (QuotientGroup.mk' (CFSG.pCore 2 K)) ⟨k, hk⟩⁆ = 1
      rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hKmem : ⁅m, k⁆ ∈ K := by
        rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem hm hk) (K.inv_mem hm)) (K.inv_mem hk)
      have hQmk : ⁅m, k⁆ ∈ Q := by
        simpa only [commutatorElement_inv] using Q.inv_mem (hcentral m hm)
      have hmem : (⟨⁅m, k⁆, hKmem⟩ : K) ∈ CFSG.pCore 2 K := by
        rw [← mem_pCoreOf_iff hKmem]
        have : ⁅m, k⁆ ∈ K ⊓ Q := ⟨hKmem, hQmk⟩
        rwa [hKQ] at this
      convert hmem using 1
    rw [center_bar2_eq_bot halt, Subgroup.mem_bot, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hz
    exact hz
  have hmem : k ∈ CFSG.Open.pCoreOf 2 K := (mem_pCoreOf_iff hk).mpr hcore
  exact (Subgroup.mem_inf.mp (by rwa [← hKQ] at hmem)).2

private theorem conjugate_le_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : x ∈ X) : CFSG.conjugate L x ≤ I := by
  rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
  exact le_iSup (fun x : X => CFSG.conjugate L (x : G)) ⟨x, hx⟩

private theorem exists_factor_mem_conjugates {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) (hgen : X = Subgroup.zpowers x) (hord3 : orderOf x = 3)
    (hneL : CFSG.conjugate L x ≠ L) (hneL2 : CFSG.conjugate L (x ^ 2) ≠ L)
    (hne2 : CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x)
    {i : G} (hi : i ∈ I) :
    ∃ l0 ∈ L, ∃ l1 ∈ CFSG.conjugate L x, ∃ l2 ∈ CFSG.conjugate L (x ^ 2),
      i = (l0 * l1) * l2 := by
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  set L1 := CFSG.conjugate L x with hL1
  set L2 := CFSG.conjugate L (x ^ 2) with hL2
  have hI3 : I = L ⊔ L1 ⊔ L2 := by
    refine le_antisymm ?_ ?_
    · rw [h.I_eq]
      refine iSup_le fun y => iSup_le fun hy => ?_
      have hy' : y ∈ Subgroup.zpowers x := hgen ▸ hy
      rcases mem_zpowers_of_orderOf_eq_three hord3 hy' with rfl | rfl | rfl
      · rw [conjugate_one]
        exact (le_sup_left : L ≤ L ⊔ L1).trans le_sup_left
      · exact (le_sup_right : L1 ≤ L ⊔ L1).trans le_sup_left
      · exact le_sup_right
    · refine sup_le (sup_le (le_I h) ?_) ?_
      · exact conjugate_le_I h hxX
      · exact conjugate_le_I h hx2X
  have hL0NL1 : L ≤ Subgroup.normalizer (L1 : Set G) := by
    simpa only [conjugate_one] using
      conjugate_normalize_of_ne h X.one_mem hxX (by rw [conjugate_one]; exact Ne.symm hneL)
  have hL0NL2 : L ≤ Subgroup.normalizer (L2 : Set G) := by
    simpa only [conjugate_one] using
      conjugate_normalize_of_ne h X.one_mem hx2X (by rw [conjugate_one]; exact Ne.symm hneL2)
  have hL1NL2 : L1 ≤ Subgroup.normalizer (L2 : Set G) :=
    conjugate_normalize_of_ne h hxX hx2X (Ne.symm hne2)
  have hsN : L ⊔ L1 ≤ Subgroup.normalizer (L2 : Set G) := sup_le hL0NL2 hL1NL2
  have hi' : i ∈ (L ⊔ L1) ⊔ L2 := by rw [← hI3]; exact hi
  obtain ⟨y, hy, l2, hl2, hy_eq⟩ := (mem_sup_of_le_normalizer hsN).mp hi'
  obtain ⟨l0, hl0, l1, hl1, hl_eq⟩ := (mem_sup_of_le_normalizer hL0NL1).mp hy
  exact ⟨l0, hl0, l1, hl1, l2, hl2, by rw [← hy_eq, ← hl_eq]⟩

private theorem commutator_left_mem_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x l0 l1 l2 : G} (hxX : x ∈ X) (hl0 : l0 ∈ L)
    (hl1 : l1 ∈ CFSG.conjugate L x) (hl2 : l2 ∈ CFSG.conjugate L (x ^ 2))
    (hneL : CFSG.conjugate L x ≠ L) (hneL2 : CFSG.conjugate L (x ^ 2) ≠ L)
    (hl0H : l0 ∈ H) (hl1H : l1 ∈ H)
    (hkey : ∀ m ∈ I, ⁅(l0 * l1) * l2, m⁆ ∈ Q) :
    ∀ m ∈ L, ⁅l0, m⁆ ∈ Q := by
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  intro m hm
  have h1 : ⁅l1, m⁆ ∈ Q := by
    have hle : ⁅CFSG.conjugate L x, L⁆ ≤ Q := by
      simpa only [conjugate_one] using
        commutator_conjugate_le h hxX X.one_mem (by rw [conjugate_one]; exact hneL)
    exact (Subgroup.commutator_le.mp hle) l1 hl1 m hm
  have h2 : ⁅l2, m⁆ ∈ Q := by
    have hle : ⁅CFSG.conjugate L (x ^ 2), L⁆ ≤ Q := by
      simpa only [conjugate_one] using
        commutator_conjugate_le h hx2X X.one_mem (by rw [conjugate_one]; exact hneL2)
    exact (Subgroup.commutator_le.mp hle) l2 hl2 m hm
  exact commutator_first_mem hQn hl0H hl1H h1 h2 (hkey m (le_I h hm))

private theorem commutator_middle_mem_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x l0 l1 l2 : G} (hxX : x ∈ X) (hl0 : l0 ∈ L)
    (hl1 : l1 ∈ CFSG.conjugate L x) (hl2 : l2 ∈ CFSG.conjugate L (x ^ 2))
    (hneL : CFSG.conjugate L x ≠ L) (hne2 : CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x)
    (hl0H : l0 ∈ H) (hl1H : l1 ∈ H)
    (hkey : ∀ m ∈ I, ⁅(l0 * l1) * l2, m⁆ ∈ Q) :
    ∀ m ∈ CFSG.conjugate L x, ⁅l1, m⁆ ∈ Q := by
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  intro m hm
  have h0 : ⁅l0, m⁆ ∈ Q := by
    have hle : ⁅L, CFSG.conjugate L x⁆ ≤ Q := by
      simpa only [conjugate_one] using
        commutator_conjugate_le h X.one_mem hxX (by rw [conjugate_one]; exact Ne.symm hneL)
    exact (Subgroup.commutator_le.mp hle) l0 hl0 m hm
  have h2 : ⁅l2, m⁆ ∈ Q := by
    have hle : ⁅CFSG.conjugate L (x ^ 2), CFSG.conjugate L x⁆ ≤ Q :=
      commutator_conjugate_le h hx2X hxX hne2
    exact (Subgroup.commutator_le.mp hle) l2 hl2 m hm
  exact commutator_middle_mem hQn hl0H hl1H h0 h2 (hkey m (conjugate_le_I h hxX hm))

private theorem commutator_right_mem_pCoreOf {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x l0 l1 l2 : G} (hxX : x ∈ X) (hl0 : l0 ∈ L)
    (hl1 : l1 ∈ CFSG.conjugate L x) (hl2 : l2 ∈ CFSG.conjugate L (x ^ 2))
    (hneL2 : CFSG.conjugate L (x ^ 2) ≠ L) (hne2 : CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x)
    (hl0H : l0 ∈ H) (hl1H : l1 ∈ H)
    (hkey : ∀ m ∈ I, ⁅(l0 * l1) * l2, m⁆ ∈ Q) :
    ∀ m ∈ CFSG.conjugate L (x ^ 2), ⁅l2, m⁆ ∈ Q := by
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  intro m hm
  have h0 : ⁅l0, m⁆ ∈ Q := by
    have hle : ⁅L, CFSG.conjugate L (x ^ 2)⁆ ≤ Q := by
      simpa only [conjugate_one] using
        commutator_conjugate_le h X.one_mem hx2X (by rw [conjugate_one]; exact Ne.symm hneL2)
    exact (Subgroup.commutator_le.mp hle) l0 hl0 m hm
  have h1 : ⁅l1, m⁆ ∈ Q := by
    have hle : ⁅CFSG.conjugate L x, CFSG.conjugate L (x ^ 2)⁆ ≤ Q :=
      commutator_conjugate_le h hxX hx2X (Ne.symm hne2)
    exact (Subgroup.commutator_le.mp hle) l1 hl1 m hm
  exact commutator_third_mem hQn hl0H hl1H h0 h1 (hkey m (conjugate_le_I h hx2X hm))

theorem mem_pCoreOf_of_commutator_mem {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {i : G} (hi : i ∈ I) (hcent : ∀ l ∈ I, ⁅i, l⁆ ∈ Q) : i ∈ Q := by
  obtain ⟨x, hxX, hgen, hneL, hneL2, hne2⟩ := exists_generator49 h
  have hx2X : x ^ 2 ∈ X := X.pow_mem hxX 2
  have hord3 : orderOf x = 3 := by
    have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [← hgen]; exact h.card_X
    rwa [Nat.card_zpowers] at hcard
  have hLH : L ≤ H := CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn h.L_mem
  have hL1H : CFSG.conjugate L x ≤ H :=
    conjugate_le_of_mem_normalizer hLH (Subgroup.le_normalizer (h.X_le hxX))
  have hL2H : CFSG.conjugate L (x ^ 2) ≤ H :=
    conjugate_le_of_mem_normalizer hLH (Subgroup.le_normalizer (h.X_le hx2X))
  obtain ⟨l0, hl0, l1, hl1, l2, hl2, hi_eq⟩ :=
    exists_factor_mem_conjugates h hxX hgen hord3 hneL hneL2 hne2 hi
  have hkey : ∀ m ∈ I, ⁅(l0 * l1) * l2, m⁆ ∈ Q := fun m hm => hi_eq ▸ hcent m hm
  have hc0 :=
    commutator_left_mem_pCoreOf h hxX hl0 hl1 hl2 hneL hneL2 (hLH hl0) (hL1H hl1) hkey
  have hc1 :=
    commutator_middle_mem_pCoreOf h hxX hl0 hl1 hl2 hneL hne2 (hLH hl0) (hL1H hl1) hkey
  have hc2 :=
    commutator_right_mem_pCoreOf h hxX hl0 hl1 hl2 hneL2 hne2 (hLH hl0) (hL1H hl1) hkey
  have hLinfQ : L ⊓ Q = CFSG.Open.pCoreOf 2 L := by
    simpa only [conjugate_one] using conjugate_inf_pCoreOf_eq h (X.one_mem : (1 : G) ∈ X)
  have hL1infQ : CFSG.conjugate L x ⊓ Q = CFSG.Open.pCoreOf 2 (CFSG.conjugate L x) :=
    conjugate_inf_pCoreOf_eq h hxX
  have hL2infQ : CFSG.conjugate L (x ^ 2) ⊓ Q =
      CFSG.Open.pCoreOf 2 (CFSG.conjugate L (x ^ 2)) :=
    conjugate_inf_pCoreOf_eq h hx2X
  have hl0Q : l0 ∈ Q := mem_pCoreOf_of_centralizer_mod h.L_alt hLinfQ hLH hl0 hc0
  have hl1Q : l1 ∈ Q :=
    mem_pCoreOf_of_centralizer_mod (isAlt_bar2_conjugate h.L_alt x) hL1infQ hL1H hl1 hc1
  have hl2Q : l2 ∈ Q :=
    mem_pCoreOf_of_centralizer_mod (isAlt_bar2_conjugate h.L_alt (x ^ 2)) hL2infQ hL2H hl2 hc2
  exact hi_eq ▸ Q.mul_mem (Q.mul_mem hl0Q hl1Q) hl2Q

theorem I_le_normalizer_L {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    I ≤ Subgroup.normalizer (L : Set G) := by
  rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
  refine iSup_le fun y => ?_
  by_cases hy : CFSG.conjugate L (y : G) = L
  · rw [hy]; exact Subgroup.le_normalizer
  · simpa only [conjugate_one] using
      conjugate_normalize_of_ne h y.2 X.one_mem (by rw [conjugate_one]; exact hy)

theorem conjugate_pow_eq_of_conjugate_eq {K : Subgroup G} {a : G}
    (ha : CFSG.conjugate K a = K) (j : ℕ) : CFSG.conjugate K (a ^ j) = K := by
  induction j with
  | zero => rw [pow_zero, conjugate_one]
  | succ j ih => rw [pow_succ, ← conjugate_conjugate, ih, ha]

private theorem commutator_mem_of_factor_sup {I Q : Subgroup G} {N : Subgroup G}
    (hIcent : I ≤ Subgroup.centralizer (N : Set G))
    (hINQ : I ≤ Subgroup.normalizer (Q : Set G))
    {n i q : G} (hnN : n ∈ N) (hiI : i ∈ I) (hqQ : q ∈ Q) (hiq : i * q = n) :
    ∀ l ∈ I, ⁅i, l⁆ ∈ Q := by
  intro l hl
  have hnl : ⁅n, l⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hIcent hl)) n hnN
  have hql : ⁅q, l⁆ ∈ Q := by
    rw [commutatorElement_def]
    have h1 : l * q⁻¹ * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hINQ hl) q⁻¹).mp (Q.inv_mem hqQ)
    simpa only [mul_assoc] using Q.mul_mem hqQ h1
  have hmain : ⁅n, l⁆ = i * ⁅q, l⁆ * i⁻¹ * ⁅i, l⁆ := by
    rw [← hiq, commutatorElement_mul_left_eq_conj_mul i q l]
  have hconj : i * ⁅q, l⁆ * i⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hINQ hiI) ⁅q, l⁆).mp hql
  have hzero : i * ⁅q, l⁆ * i⁻¹ * ⁅i, l⁆ = 1 := by
    rw [← hmain]; exact hnl
  have hprod : (i * ⁅q, l⁆ * i⁻¹)⁻¹ * (i * ⁅q, l⁆ * i⁻¹ * ⁅i, l⁆) ∈ Q :=
    Q.mul_mem (Q.inv_mem hconj) (by rw [hzero]; exact Q.one_mem)
  convert hprod using 1
  group

private theorem odd_normal_inf_sup_pCoreOf_eq_bot {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {N : Subgroup G} (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (hNodd : Odd (Nat.card N)) :
    N ⊓ (I ⊔ Q) = ⊥ := by
  have hIcent : I ≤ Subgroup.centralizer (N : Set G) :=
    odd_normal_le_centralizer_I h hNH hNn hNodd
  have hI_le_H : I ≤ H := I_le_H h
  have hQnorm : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hINQ : I ≤ Subgroup.normalizer (Q : Set G) := hI_le_H.trans hQnorm
  have hQ2 : IsPGroup 2 ↥Q := by rw [h.Q_eq]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hNQinf : N ⊓ Q = ⊥ := inf_eq_bot_of_odd_of_isPGroup hNodd hQ2
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnN : n ∈ N := (Subgroup.mem_inf.mp hn).1
  have hnIQ : n ∈ I ⊔ Q := (Subgroup.mem_inf.mp hn).2
  obtain ⟨i, hiI, q, hqQ, hiq⟩ := (mem_sup_of_le_normalizer hINQ).mp hnIQ
  have hiQ : i ∈ Q := mem_pCoreOf_of_commutator_mem h hiI
    (commutator_mem_of_factor_sup hIcent hINQ hnN hiI hqQ hiq)
  have hnQ : n ∈ Q := hiq ▸ Q.mul_mem hiQ hqQ
  exact Subgroup.mem_bot.mp (hNQinf ▸ Subgroup.mem_inf.mpr ⟨hnN, hnQ⟩)

private theorem card_quotient_le_card_X {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    (Q' : Subgroup ↥H) [Q'.Normal] (hQ' : Q' = (I ⊔ Q).subgroupOf H)
    (hIQnorm : H ≤ Subgroup.normalizer ((I ⊔ Q : Subgroup G) : Set G)) :
    Nat.card (↥H ⧸ Q') ≤ Nat.card X := by
  have hQH : Q ≤ H := h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIQs : I ⊔ Q ≤ H := sup_le (I_le_H h) hQH
  let π : ↥H →* ↥H ⧸ Q' := QuotientGroup.mk' Q'
  have hHX : H = (I ⊔ Q) ⊔ X := by rw [eq_sup_I h]; ac_rfl
  have hXnorm : X ≤ Subgroup.normalizer ((I ⊔ Q : Subgroup G) : Set G) := h.X_le.trans hIQnorm
  have hXsurj : Function.Surjective (fun x : X => π ⟨x.1, h.X_le x.2⟩) := by
    intro z
    obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective Q' z
    have hh' : (h' : G) ∈ X ⊔ (I ⊔ Q) := by
      rw [sup_comm]; rw [← hHX]; exact h'.2
    obtain ⟨x, hx, q, hq, hxq⟩ := (mem_sup_of_le_normalizer hXnorm).mp hh'
    refine ⟨⟨x, hx⟩, ?_⟩
    have hqQ' : (⟨q, hIQs hq⟩ : ↥H) ∈ Q' := by
      rw [hQ']; exact Subgroup.mem_subgroupOf.mpr hq
    have hxh : h' = (⟨x, h.X_le hx⟩ : ↥H) * ⟨q, hIQs hq⟩ := by
      refine Subtype.ext ?_
      exact hxq.symm
    rw [hxh, map_mul,
      show π ⟨q, hIQs hq⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr hqQ', mul_one]
  exact Nat.card_le_card_of_surjective _ hXsurj

private theorem card_le_card_quotient_of_inf_eq_bot {H Q I : Subgroup G} {N : Subgroup G}
    (hNH : N ≤ H) (Q' : Subgroup ↥H) [Q'.Normal] (hQ' : Q' = (I ⊔ Q).subgroupOf H)
    (hdisj : N ⊓ (I ⊔ Q) = ⊥) : Nat.card N ≤ Nat.card (↥H ⧸ Q') := by
  let π : ↥H →* ↥H ⧸ Q' := QuotientGroup.mk' Q'
  have hNinj : Function.Injective (fun n : N => π ⟨n.1, hNH n.2⟩) := by
    intro n n' heq
    have h1 : (⟨n.1, hNH n.2⟩ : ↥H)⁻¹ * ⟨n'.1, hNH n'.2⟩ ∈ Q' :=
      QuotientGroup.eq.mp heq
    have h2 : n.1⁻¹ * n'.1 ∈ I ⊔ Q := by
      have h1' : (⟨n.1, hNH n.2⟩ : ↥H)⁻¹ * ⟨n'.1, hNH n'.2⟩ ∈ (I ⊔ Q).subgroupOf H := by
        simpa [hQ'] using h1
      have := Subgroup.mem_subgroupOf.mp h1'
      simpa using this
    have h3 : n.1⁻¹ * n'.1 ∈ N := N.mul_mem (N.inv_mem n.2) n'.2
    have h4 : n.1⁻¹ * n'.1 = 1 := by
      have := (hdisj ▸ Subgroup.mem_inf.mpr ⟨h3, h2⟩ : n.1⁻¹ * n'.1 ∈ (⊥ : Subgroup G))
      exact Subgroup.mem_bot.mp this
    have h5 : n.1⁻¹ * n'.1 = n.1⁻¹ * n.1 := by rw [h4, inv_mul_cancel]
    exact Subtype.ext (mul_left_cancel h5).symm
  exact Nat.card_le_card_of_injective _ hNinj

private theorem odd_normal_card_le_three {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N : Subgroup G} (hNH : N ≤ H)
    (hIQnorm : H ≤ Subgroup.normalizer ((I ⊔ Q : Subgroup G) : Set G))
    (hdisj : N ⊓ (I ⊔ Q) = ⊥) : Nat.card N ≤ 3 := by
  have hQH : Q ≤ H := h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIQs : I ⊔ Q ≤ H := sup_le (I_le_H h) hQH
  let Q' : Subgroup ↥H := (I ⊔ Q).subgroupOf H
  haveI hQ'n : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hIQs).mpr hIQnorm
  have hcardQ : Nat.card (↥H ⧸ Q') ≤ Nat.card X := card_quotient_le_card_X h Q' rfl hIQnorm
  exact (card_le_card_quotient_of_inf_eq_bot hNH Q' rfl hdisj).trans
    (hcardQ.trans (le_of_eq h.card_X))

private theorem exists_order_three_of_card_three {N : Subgroup G} (hNcard : Nat.card N = 3) :
    ∃ n : N, orderOf (n : G) = 3 ∧ (n : G) ^ 3 = 1 ∧ (n : G) ≠ 1 := by
  have hNne : N ≠ ⊥ := by
    intro hbot; rw [hbot, Subgroup.card_bot] at hNcard; norm_num at hNcard
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
  obtain ⟨n, hn1⟩ := exists_ne (1 : N)
  have hnord : orderOf (n : G) = 3 := by
    have hdvd : orderOf (n : G) ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard N n.2
      rwa [hNcard] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) (by simpa using hn1)
    · exact h3
  have hn3 : (n : G) ^ 3 = 1 := by rw [← hnord]; exact pow_orderOf_eq_one _
  exact ⟨n, hnord, hn3, fun h => hn1 (Subtype.ext h)⟩

private theorem le_normalizer_L_of_odd_normal {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N : Subgroup G} (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (hNodd : Odd (Nat.card N)) :
    N ≤ Subgroup.normalizer (L : Set G) ∧
      I ⊔ Q ≤ Subgroup.normalizer (L : Set G) := by
  have hLN : ⁅L, N⁆ = ⊥ := commutator_eq_bot_of_odd_of_isAlt
    (CFSG.RankThree.PartTwo.le_of_mem_oTwoComponentsIn h.L_mem)
    (CFSG.RankThree.PartTwo.mem_oTwoComponentsIn_iff.mp h.L_mem).2.2.1
    (CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn h.L_mem)
    h.L_alt hNH hNn hNodd
  have hNLc : N ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hLN)
  have hNL : N ≤ Subgroup.normalizer (L : Set G) :=
    hNLc.trans (Subgroup.centralizer_le_normalizer (L : Set G))
  have hQNL : Q ≤ Subgroup.normalizer (L : Set G) := by
    rw [h.Q_eq]; exact pCoreOf_le_normalizer_of_mem_oTwoComponentsIn h.L_mem
  exact ⟨hNL, sup_le (I_le_normalizer_L h) hQNL⟩

private theorem conjugate_eq_of_mul_inv_pow_mem {L : Subgroup G} {N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {I Q : Subgroup G}
    (hsupN : I ⊔ Q ≤ Subgroup.normalizer (L : Set G))
    {n x : G} (hnN : n ∈ N) (j : ℕ) (hmem : x * (n ^ j)⁻¹ ∈ I ⊔ Q) :
    CFSG.conjugate L x = L := by
  have hq : CFSG.conjugate L (x * (n ^ j)⁻¹) = L := by
    have hmemN : x * (n ^ j)⁻¹ ∈ Subgroup.normalizer (L : Set G) := hsupN hmem
    have := (Subgroup.normalizer _).inv_mem hmemN
    rw [CFSG.conjugate]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp this
  have hLn : CFSG.conjugate L n = L := by
    have := (Subgroup.normalizer _).inv_mem (hNL hnN)
    rw [CFSG.conjugate]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp this
  have hnj : CFSG.conjugate L (n ^ j) = L := conjugate_pow_eq_of_conjugate_eq hLn j
  have hxeq : x = (x * (n ^ j)⁻¹) * n ^ j := by group
  rw [hxeq, ← conjugate_conjugate L (x * (n ^ j)⁻¹) (n ^ j), hq, hnj]

private theorem pi_image_ne_one_of_inf_eq_bot {H Q I : Subgroup G} {N : Subgroup G}
    (hNH : N ≤ H) (Q' : Subgroup ↥H) [Q'.Normal] (hQ' : Q' = (I ⊔ Q).subgroupOf H)
    (hdisj : N ⊓ (I ⊔ Q) = ⊥) {n : N} (hn : (n : G) ≠ 1) :
    QuotientGroup.mk' Q' ⟨n.1, hNH n.2⟩ ≠ 1 := by
  intro hcon
  have hmem : (⟨n.1, hNH n.2⟩ : ↥H) ∈ Q' :=
    (QuotientGroup.eq_one_iff _).mp (by simpa using hcon)
  have hIQ : n.1 ∈ I ⊔ Q := by
    rw [hQ'] at hmem
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hmem' : n.1 ∈ N ⊓ (I ⊔ Q) := ⟨n.2, hIQ⟩
  rw [hdisj, Subgroup.mem_bot] at hmem'
  exact hn hmem'

private theorem odd_normal_card_three_contra {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N : Subgroup G} (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal) (hNodd : Odd (Nat.card N))
    (hNcard : Nat.card N = 3) (hdisj : N ⊓ (I ⊔ Q) = ⊥)
    (hIQnorm : H ≤ Subgroup.normalizer ((I ⊔ Q : Subgroup G) : Set G)) : False := by
  obtain ⟨n, hnord, hn3, hn_ne⟩ := exists_order_three_of_card_three hNcard
  obtain ⟨x, hxX, hgen, hneL, hneL2, hne2⟩ := exists_generator49 h
  let n' : ↥H := ⟨n.1, hNH n.2⟩
  let x' : ↥H := ⟨x, h.X_le hxX⟩
  obtain ⟨hNL, hsupN⟩ := le_normalizer_L_of_odd_normal h hNH hNn hNodd
  have hQH : Q ≤ H := h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIQs : I ⊔ Q ≤ H := sup_le (I_le_H h) hQH
  let Q' : Subgroup ↥H := (I ⊔ Q).subgroupOf H
  haveI hQ'n : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hIQs).mpr hIQnorm
  let π : ↥H →* ↥H ⧸ Q' := QuotientGroup.mk' Q'
  have hcardQ : Nat.card (↥H ⧸ Q') ≤ Nat.card X := card_quotient_le_card_X h Q' rfl hIQnorm
  have hn'3 : n' ^ 3 = 1 := Subtype.ext (by simpa [n'] using hn3)
  have hpi3 : (π n') ^ 3 = 1 := by rw [← map_pow, hn'3, map_one]
  have hpi1 : π n' ≠ 1 := pi_image_ne_one_of_inf_eq_bot hNH Q' rfl hdisj hn_ne
  have hpiord : orderOf (π n') = 3 := orderOf_eq_prime hpi3 hpi1
  have htop : Subgroup.zpowers (π n') = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top, Nat.card_zpowers, hpiord]
    exact hcardQ.trans (le_of_eq h.card_X)
  have hxmem : π x' ∈ Subgroup.zpowers (π n') := by rw [htop]; exact Subgroup.mem_top _
  have hcontra : ∀ j : ℕ, π x' = (π n') ^ j → False := by
    intro j hj
    have hrel : π (x' * (n' ^ j)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hj, mul_inv_cancel]
    have hmem : x' * (n' ^ j)⁻¹ ∈ Q' :=
      (QuotientGroup.eq_one_iff _).mp (by simpa [π] using hrel)
    have hIQ : x * (n.1 ^ j)⁻¹ ∈ I ⊔ Q := by
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa [x', n'] using this
    exact hneL (conjugate_eq_of_mul_inv_pow_mem hNL hsupN n.2 j hIQ)
  rcases mem_zpowers_of_orderOf_eq_three hpiord hxmem with hcase | hcase | hcase
  · exact hcontra 0 (by rw [pow_zero]; exact hcase)
  · exact hcontra 1 (by rw [pow_one]; exact hcase)
  · exact hcontra 2 hcase

theorem odd_normal_eq_bot49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) → Odd (Nat.card N) → N = ⊥ := by
  intro N hNH hNnorm hNodd
  have hNn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hNnorm
  have hQnorm : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hIQnorm : H ≤ Subgroup.normalizer ((I ⊔ Q : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_I h) hQnorm).trans (Subgroup.inf_normalizer_le_normalizer_sup I Q)
  have hdisj : N ⊓ (I ⊔ Q) = ⊥ := odd_normal_inf_sup_pCoreOf_eq_bot h hNH hNn hNodd
  have hNle3 : Nat.card N ≤ 3 := odd_normal_card_le_three h hNH hIQnorm hdisj
  rcases lt_or_eq_of_le hNle3 with hlt | heq
  · have h1 : Nat.card N = 1 := by
      obtain ⟨k, hk⟩ := hNodd
      omega
    exact Subgroup.card_eq_one.mp h1
  · exact (odd_normal_card_three_contra h hNH hNn hNodd heq hdisj hIQnorm).elim

theorem struct49_main {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    I ≤ H ∧ H ≤ Subgroup.normalizer (I : Set G) ∧ H = I ⊔ X ⊔ Q ∧ ⁅I, I⁆ = I ∧
    (∀ x ∈ X, CFSG.conjugate L x ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H ∧
        IsAlt (Bar2 (CFSG.conjugate L x)) 5 ∧
        Q ≤ Subgroup.normalizer (CFSG.conjugate L x : Set G) ∧
        CFSG.conjugate L x ⊓ Q = CFSG.Open.pCoreOf 2 (CFSG.conjugate L x)) ∧
    (∃ x ∈ X, X = Subgroup.zpowers x ∧ CFSG.conjugate L x ≠ L ∧
        CFSG.conjugate L (x ^ 2) ≠ L ∧ CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x) ∧
    (∀ x ∈ X, ∀ y ∈ X, CFSG.conjugate L x ≠ CFSG.conjugate L y →
        CFSG.conjugate L x ≤ Subgroup.normalizer (CFSG.conjugate L y : Set G) ∧
        ⁅CFSG.conjugate L x, CFSG.conjugate L y⁆ ≤ Q) :=
  ⟨I_le_H h, le_normalizer_I h, eq_sup_I h, commutator_I_eq h,
    fun x hx => ⟨conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hx),
      isAlt_bar2_conjugate h.L_alt x, pCoreOf_le_normalizer_conjugate h hx,
      conjugate_inf_pCoreOf_eq h hx⟩,
    exists_generator49 h,
    fun x hx y hy hne => ⟨conjugate_normalize_of_ne h hx hy hne,
      commutator_conjugate_le h hx hy hne⟩⟩

theorem struct49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) :
    I ≤ H ∧ H ≤ Subgroup.normalizer (I : Set G) ∧ H = I ⊔ X ⊔ Q ∧ ⁅I, I⁆ = I ∧
    (∀ x ∈ X, CFSG.conjugate L x ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H ∧
        IsAlt (Bar2 (CFSG.conjugate L x)) 5 ∧
        Q ≤ Subgroup.normalizer (CFSG.conjugate L x : Set G) ∧
        CFSG.conjugate L x ⊓ Q = CFSG.Open.pCoreOf 2 (CFSG.conjugate L x)) ∧
    (∃ x ∈ X, X = Subgroup.zpowers x ∧ CFSG.conjugate L x ≠ L ∧
        CFSG.conjugate L (x ^ 2) ≠ L ∧ CFSG.conjugate L (x ^ 2) ≠ CFSG.conjugate L x) ∧
    (∀ x ∈ X, ∀ y ∈ X, CFSG.conjugate L x ≠ CFSG.conjugate L y →
        CFSG.conjugate L x ≤ Subgroup.normalizer (CFSG.conjugate L y : Set G) ∧
        ⁅CFSG.conjugate L x, CFSG.conjugate L y⁆ ≤ Q) ∧
    (∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) → Odd (Nat.card N) →
        N = ⊥) :=
  ⟨(struct49_main h).1, (struct49_main h).2.1, (struct49_main h).2.2.1,
    (struct49_main h).2.2.2.1, (struct49_main h).2.2.2.2.1, (struct49_main h).2.2.2.2.2.1,
    (struct49_main h).2.2.2.2.2.2, odd_normal_eq_bot49 h⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
