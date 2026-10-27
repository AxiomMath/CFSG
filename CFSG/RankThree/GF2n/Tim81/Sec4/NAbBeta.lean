module

public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbAlpha
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup
public import CFSG.RankThree.GF2n.Tim81.Sec4.MinimalNormal
public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Factor
public import CFSG.Timmesfeld.Bridge.OddLocalQd

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec2
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem RootHyp.not_commutator_W0_Pc_le_V
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    ¬ ⁅W₀, Pc M V⁆ ≤ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  set B : Subgroup G := conjSubgroup y V ⊓ W₀ with hB
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPy2 : IsPGroup 2 (conjSubgroup y (Pc M V)) := hP2.map _
  have hW02 : IsPGroup 2 W₀ := (isElemAbelian_xOf h hPH hVH).isPGroup.to_le hW₀
  have hBN : conjSubgroup y (Pc M V) ≤ Subgroup.normalizer (W₀ : Set G) := by
    have h1 : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hyH
    exact h1.trans hN
  have hB_ne : B ≠ ⊥ := by
    have hne := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
      Nat.prime_two hPy2 hW02 hW₀ne hBN
    have hWinf : Tim79a.xOf V H ⊓ Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G) =
        conjSubgroup y V := RootHyp.xOf_inf_centralizer_conj_Pc h hyH
    intro hbot'
    apply hne
    calc W₀ ⊓ Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G)
        = (W₀ ⊓ Tim79a.xOf V H) ⊓
            Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G) := by
          rw [inf_eq_left.mpr hW₀]
      _ = W₀ ⊓ (Tim79a.xOf V H ⊓
            Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G)) := by rw [inf_assoc]
      _ = W₀ ⊓ conjSubgroup y V := by rw [hWinf]
      _ = B := by rw [hB, inf_comm]
      _ = ⊥ := hbot'
  have hBM : B ≤ M := (inf_le_right : B ≤ W₀).trans (hW₀.trans (xOf_le_M h hPH hVH))
  have hB_CV : B ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have hxW : x ∈ Tim79a.xOf V H := hW₀ (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((isElemAbelian_xOf h hPH hVH).comm hxW (le_xOf_self V H hv)).symm
  have hPB : ⁅Pc M V, B⁆ ≤ V := by
    have h1 : ⁅Pc M V, B⁆ ≤ ⁅Pc M V, W₀⁆ := Subgroup.commutator_mono le_rfl inf_le_right
    have h2 : ⁅Pc M V, W₀⁆ ≤ V := by
      rw [Subgroup.commutator_comm]
      exact hbot
    exact h1.trans h2
  have hBQ : B ≤ inSubgroup (pCore 2) M :=
    h.toHyp.le_pCore_of_commutator_le hBM hB_CV hPB
  have hBP : B ≤ Pc M V := le_inf hBQ hB_CV
  have hBbot : B = ⊥ := by
    rw [eq_bot_iff]
    have hle : B ≤ conjSubgroup y V ⊓ Pc M V := le_inf inf_le_left hBP
    rwa [RootHyp.conjSubgroup_inf_Pc_eq_bot h hHy hnM] at hle
  exact hB_ne hBbot

theorem RootHyp.not_inf_Pc_W0_le_V
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    ¬ Pc M V ⊓ W₀ ≤ V := by
  intro hle
  exact RootHyp.not_commutator_W0_Pc_le_V h hPH hVH hH hnM hW₀ hN hW₀ne
    ((RootHyp.commutator_W0_Pc_le h hPH hVH hW₀ hN).trans hle)

private theorem exists_conj_eq_of_frobeniusComplement {P R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (P : Set G))
    (hRcard : Nat.card R = Nat.card P - 1)
    (hfpf : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ P, r * x * r⁻¹ = x → x = 1)
    {x : G} (hxP : x ∈ P) (hx1 : x ≠ 1) :
    ∀ y ∈ P, y ≠ 1 → ∃ r ∈ R, r * x * r⁻¹ = y := by
  classical
  have hxP' : x ∈ P := hxP
  let f : ↥R → G := fun r => (r : G) * x * (r : G)⁻¹
  have hinj : Function.Injective f := by
    rintro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ heq
    have h1 : r₁ * x * r₁⁻¹ = r₂ * x * r₂⁻¹ := heq
    have h2 : r₂⁻¹ * r₁ ∈ R := R.mul_mem (R.inv_mem hr₂) hr₁
    have h3 : (r₂⁻¹ * r₁) * x * (r₂⁻¹ * r₁)⁻¹ = x := by
      rw [mul_inv_rev, inv_inv]
      calc r₂⁻¹ * r₁ * x * (r₁⁻¹ * r₂) = r₂⁻¹ * (r₁ * x * r₁⁻¹) * r₂ := by group
        _ = r₂⁻¹ * (r₂ * x * r₂⁻¹) * r₂ := by rw [h1]
        _ = x := by group
    by_cases h21 : r₂⁻¹ * r₁ = 1
    · have h12 : r₁ = r₂ := by
        have h := congrArg (fun t => r₂ * t) h21
        simpa [mul_assoc] using h
      exact Subtype.ext h12
    · exact absurd (hfpf (r₂⁻¹ * r₁) h2 h21 x hxP' h3) hx1
  have hnot1 : (1 : G) ∉ Set.range f := by
    rintro ⟨r, hr⟩
    have h1 : (r : G) * x * (r : G)⁻¹ = 1 := hr
    apply hx1
    have h := congrArg (fun t => (r : G)⁻¹ * t * (r : G)) h1
    simpa [mul_assoc] using h
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hcover : Set.range f ∪ {(1 : G)} = (P : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro z (hz | hz)
      · obtain ⟨r, rfl⟩ := hz
        exact (Subgroup.mem_normalizer_iff.mp (hRN r.2) x).mp hxP'
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact P.one_mem
    · have hdisj : Disjoint (Set.range f) ({(1 : G)} : Set G) := by
        rw [Set.disjoint_singleton_right]
        exact hnot1
      have h1 : (Set.range f ∪ {(1 : G)} : Set G).ncard = (Set.range f).ncard + 1 := by
        rw [Set.ncard_union_eq hdisj, Set.ncard_singleton]
      have h2 : (Set.range f).ncard = Nat.card R := by
        rw [← Nat.card_coe_set_eq]
        exact Nat.card_range_of_injective hinj
      have h3 : (P : Set G).ncard = Nat.card P := (Nat.card_coe_set_eq (P : Set G)).symm
      rw [h1, h2, h3, hRcard]
      omega
  intro y hyP hy1
  have hy : y ∈ Set.range f ∪ {(1 : G)} := by rw [hcover]; exact hyP
  rcases hy with hy | hy
  · obtain ⟨r, hr⟩ := hy
    exact ⟨r, r.2, hr⟩
  · rw [Set.mem_singleton_iff] at hy
    exact absurd hy hy1

private theorem RootHyp.exists_conj_inf_not_le_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥) :
    ∃ c ∈ Subgroup.centralizer (V : Set G),
      ¬ conjSubgroup c (Pc M V ⊓ W₀) ≤ kOf V H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup G := V ⊔ (Pc M V ⊓ W₀) with hLdef
  have hLW : L ≤ Tim79a.xOf V H :=
    sup_le (le_xOf_self V H) (inf_le_right.trans hW₀)
  have hLV : ¬ L ≤ V := by
    intro hle
    exact RootHyp.not_inf_Pc_W0_le_V h hPH hVH hH hnM hW₀ hN hW₀ne
      ((le_sup_right : Pc M V ⊓ W₀ ≤ L).trans hle)
  obtain ⟨c₀, hc₀, hc₀L⟩ :=
    RootHyp.exists_conj_not_le_kOf h hPH hVH hH hnM hK hnab hL hLW hLV
  have hc₀V : conjSubgroup c₀ V = V :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hc₀)
  refine ⟨c₀, hc₀, ?_⟩
  intro hle
  apply hc₀L
  have hLc : conjSubgroup c₀ L = V ⊔ conjSubgroup c₀ (Pc M V ⊓ W₀) := by
    rw [hLdef, conjSubgroup_sup_eq_sup, hc₀V]
  rw [hLc]
  exact sup_le (le_kOf h hPH hVH) hle

private theorem RootHyp.exists_betaSubgroup_basic
    (h : RootHyp M V) {W₀ : Subgroup G} {c₀ : G}
    (hc₀ : c₀ ∈ Subgroup.centralizer (V : Set G))
    (hc₀K : ¬ conjSubgroup c₀ (Pc M V ⊓ W₀) ≤ kOf V H) :
    ∃ E : Subgroup G,
      E = Subgroup.closure {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
        x ∈ conjSubgroup c (Pc M V ⊓ W₀)} ∧
      E ≤ Pc M V ∧ ¬ E ≤ kOf V H := by
  classical
  have hCVleM : Subgroup.centralizer (V : Set G) ≤ M := h.centralizer_le_M
  refine ⟨Subgroup.closure {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
    x ∈ conjSubgroup c (Pc M V ⊓ W₀)}, rfl, ?_, ?_⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨c, hc, hx⟩
    have hcP : conjSubgroup c (Pc M V) = Pc M V :=
      conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc (hCVleM hc))
    have h1 : conjSubgroup c (Pc M V ⊓ W₀) ≤ conjSubgroup c (Pc M V) :=
      Subgroup.map_mono inf_le_left
    rw [hcP] at h1
    exact h1 hx
  · intro hle
    apply hc₀K
    intro x hx
    exact hle (Subgroup.subset_closure ⟨c₀, hc₀, hx⟩)

private theorem RootHyp.betaSubgroup_conj_inv
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {W₀ : Subgroup G} (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {E : Subgroup G}
    (hE : E = Subgroup.closure {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
      x ∈ conjSubgroup c (Pc M V ⊓ W₀)}) :
    ∀ z : ↥H, piK V H z ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) →
      conjSubgroup (z : G) E = E := by
  classical
  set gens : Set G := {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
    x ∈ conjSubgroup c (Pc M V ⊓ W₀)} with hgens
  intro z hz
  obtain ⟨hzM, -⟩ :=
    RootHyp.mem_M_and_mem_normalizer_inf_of_mem_normalizer_imgK h hPH hz
  have hzCV : conjSubgroup (z : G) (Subgroup.centralizer (V : Set G)) =
      Subgroup.centralizer (V : Set G) :=
    conjSubgroup_eq_self_iff.mpr (h.le_normalizer_centralizer_V hzM)
  have hzP : conjSubgroup (z : G) (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hzM)
  have hzW : conjSubgroup (z : G) W₀ = W₀ := conjSubgroup_eq_self_iff.mpr (hN z.2)
  have hsub : (⇑(MulAut.conj (z : G)).toMonoidHom) '' gens ⊆ gens := by
    rintro x ⟨u, ⟨c, hc, hu⟩, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
    refine ⟨(z : G) * c * (z : G)⁻¹, ?_, ?_⟩
    · have h1 : (z : G) * c * (z : G)⁻¹ ∈
          conjSubgroup (z : G) (Subgroup.centralizer (V : Set G)) :=
        conj_mem_conjSubgroup (z : G) hc
      rwa [hzCV] at h1
    · refine Subgroup.mem_map.mpr ⟨(z : G) * w * (z : G)⁻¹, ?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (h.toHyp.le_normalizer_Pc hzM) w).mp hw.1
        · exact (Subgroup.mem_normalizer_iff.mp (hN z.2) w).mp hw.2
      · show MulAut.conj ((z : G) * c * (z : G)⁻¹) ((z : G) * w * (z : G)⁻¹) =
          MulAut.conj (z : G) (MulAut.conj c w)
        simp only [MulAut.conj_apply]
        group
  have hle : conjSubgroup (z : G) E ≤ E := by
    rw [hE, conjSubgroup, MonoidHom.map_closure]
    exact (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure (hsub hx)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

private theorem RootHyp.betaSubgroup_imgK_inv_and_ne
    (hPH : Pc M V ≤ H)
    {E : Subgroup G} (hE_le_P : E ≤ Pc M V) (hE_notK : ¬ E ≤ kOf V H)
    (hE_inv : ∀ z : ↥H, piK V H z ∈ Subgroup.normalizer
        (imgK V H (Pc M V) : Set (HBar V H)) → conjSubgroup (z : G) E = E) :
    (∀ zbar ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)),
        conjSubgroup zbar (imgK V H E) = imgK V H E) ∧
      imgK V H E ≠ ⊥ := by
  have hE_le_H : E ≤ H := hE_le_P.trans hPH
  constructor
  · intro zbar hzbar
    obtain ⟨z, rfl⟩ := piK_surjective V H zbar
    have h1 := hE_inv z hzbar
    rw [← imgK_conjSubgroup (V := V) (H := H) (S := E) z.2 hE_le_H, h1]
  · intro hbot
    apply hE_notK
    intro x hx
    have hxH : x ∈ H := hE_le_H hx
    have hmem : piK V H ⟨x, hxH⟩ ∈ imgK V H E :=
      Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot] at hmem
    exact (piK_eq_one_iff (V := V) (H := H) ⟨x, hxH⟩).mp (Subgroup.mem_bot.mp hmem)

private theorem RootHyp.imgK_betaSubgroup_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hL : IsL2OrSz V H)
    {E : Subgroup G} (hE_le_P : E ≤ Pc M V)
    (hEbar_ne : imgK V H E ≠ ⊥)
    (hEbar_inv : ∀ zbar ∈ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)),
      conjSubgroup zbar (imgK V H E) = imgK V H E) :
    imgK V H E = imgK V H (Pc M V) := by
  refine le_antisymm (imgK_mono hE_le_P) ?_
  obtain ⟨R, hRN, hRcard, -, hRfpf⟩ :=
    RootHyp.exists_frobeniusComplement_imgK h hPH hVH hH hnM hL
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEbar_ne
  have hxne : (x : HBar V H) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hxP : (x : HBar V H) ∈ imgK V H (Pc M V) := imgK_mono hE_le_P x.2
  intro y hyP
  by_cases hy1 : y = 1
  · rw [hy1]
    exact (imgK V H E).one_mem
  · obtain ⟨r, hrR, hry⟩ :=
      exists_conj_eq_of_frobeniusComplement hRN hRcard hRfpf hxP hxne y hyP hy1
    have hry' : y ∈ conjSubgroup r (imgK V H E) := by
      rw [show y = r * (x : HBar V H) * r⁻¹ from hry.symm]
      exact conj_mem_conjSubgroup r x.2
    rwa [hEbar_inv r (hRN hrR)] at hry'

private theorem RootHyp.betaSup_eq_of_imgK_eq
    (hPH : Pc M V ≤ H) {E : Subgroup G} (hE_le_P : E ≤ Pc M V)
    (hEbar_eq : imgK V H E = imgK V H (Pc M V)) :
    Pc M V = (Pc M V ⊓ kOf V H) ⊔ E := by
  refine le_antisymm ?_ (sup_le inf_le_left hE_le_P)
  intro p hp
  have hpH : p ∈ H := hPH hp
  have hpbar : piK V H ⟨p, hpH⟩ ∈ imgK V H E := by
    rw [hEbar_eq]
    exact Subgroup.mem_map.mpr ⟨⟨p, hpH⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
  obtain ⟨e, heE, heq⟩ := mem_imgK_iff.mp hpbar
  have hpx : p * (e : G)⁻¹ ∈ kOf V H := by
    have hmemH : p * (e : G)⁻¹ ∈ H := H.mul_mem hpH (H.inv_mem e.2)
    refine (piK_eq_one_iff (V := V) (H := H) ⟨p * (e : G)⁻¹, hmemH⟩).mp ?_
    have h1 : (⟨p * (e : G)⁻¹, hmemH⟩ : ↥H) = ⟨p, hpH⟩ * e⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_inv, heq]
    group
  have hpxP : p * (e : G)⁻¹ ∈ Pc M V :=
    (Pc M V).mul_mem hp ((Pc M V).inv_mem (hE_le_P heE))
  have hmem : p = (p * (e : G)⁻¹) * e := by group
  rw [hmem]
  exact ((Pc M V ⊓ kOf V H) ⊔ E).mul_mem
    (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hpxP, hpx⟩))
    (Subgroup.mem_sup_right heE)

theorem RootHyp.exists_beta_decomposition
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    ∃ E : Subgroup G,
      E = Subgroup.closure {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
        x ∈ conjSubgroup c (Pc M V ⊓ W₀)} ∧
      E ≤ Pc M V ∧ ¬ E ≤ kOf V H ∧ Pc M V = (Pc M V ⊓ kOf V H) ⊔ E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c₀, hc₀, hc₀K⟩ :=
    exists_conj_inf_not_le_kOf h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  obtain ⟨E, hE, hE_le_P, hE_notK⟩ := exists_betaSubgroup_basic h hc₀ hc₀K
  have hE_inv := betaSubgroup_conj_inv h hPH hN hE
  obtain ⟨hEbar_inv, hEbar_ne⟩ :=
    betaSubgroup_imgK_inv_and_ne hPH hE_le_P hE_notK hE_inv
  have hEbar_eq :=
    imgK_betaSubgroup_eq h hPH hVH hH hnM hL hE_le_P hEbar_ne hEbar_inv
  exact ⟨E, hE, hE_le_P, hE_notK, betaSup_eq_of_imgK_eq hPH hE_le_P hEbar_eq⟩

private theorem RootHyp.commutator_betaGenerator_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {X : Subgroup G} (hXP : X ≤ Pc M V) :
    ∀ s ∈ {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
      x ∈ conjSubgroup c (Pc M V ⊓ W₀)}, ∀ t ∈ X, ⁅s, t⁆ ∈ V ⊓ W₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCVleM : Subgroup.centralizer (V : Set G) ≤ M := h.centralizer_le_M
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  rintro s ⟨c, hc, hs⟩ t ht
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hs
  have hcN : c ∈ Subgroup.normalizer (Pc M V : Set G) :=
    h.toHyp.le_normalizer_Pc (hCVleM hc)
  have hxc : c⁻¹ * t * c ∈ Pc M V := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) t).mp (hXP ht)
    simpa using h
  have hwc : w ∈ Pc M V ⊓ W₀ := hw
  have h1 : ⁅w, c⁻¹ * t * c⁆ ∈ V :=
    h.toHyp.frattini_Pc_le
      (commutatorElement_mem_inSubgroup_frattini hP2 hw.1 hxc)
  have hPW : ⁅Pc M V, W₀⁆ ≤ Pc M V ⊓ W₀ := by
    rw [Subgroup.commutator_comm]
    exact RootHyp.commutator_W0_Pc_le h hPH hVH hW₀ hN
  have h2 : ⁅w, c⁻¹ * t * c⁆ ∈ W₀ := by
    have hmem : ⁅c⁻¹ * t * c, w⁆ ∈ Pc M V ⊓ W₀ :=
      hPW (Subgroup.commutator_mem_commutator hxc hwc.2)
    have hinv : ⁅w, c⁻¹ * t * c⁆ = ⁅c⁻¹ * t * c, w⁆⁻¹ :=
      (commutatorElement_inv (c⁻¹ * t * c) w).symm
    rw [hinv]
    exact (Subgroup.mem_inf.mp (Subgroup.inv_mem _ hmem)).2
  have hA : ⁅w, c⁻¹ * t * c⁆ ∈ V ⊓ W₀ := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  have hconj : ⁅c * w * c⁻¹, t⁆ = c * ⁅w, c⁻¹ * t * c⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  change ⁅c * w * c⁻¹, t⁆ ∈ V ⊓ W₀
  rw [hconj]
  have hcA : c * ⁅w, c⁻¹ * t * c⁆ * c⁻¹ = ⁅w, c⁻¹ * t * c⁆ := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hc ⁅w, c⁻¹ * t * c⁆ hA.1
    calc c * ⁅w, c⁻¹ * t * c⁆ * c⁻¹ = ⁅w, c⁻¹ * t * c⁆ * c * c⁻¹ := by
          rw [hcomm]
      _ = ⁅w, c⁻¹ * t * c⁆ := by group
  rw [hcA]
  exact hA

private theorem commutator_X_betaSubgroup_le
    (hPH : Pc M V ≤ H)
    {W₀ : Subgroup G} (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {X E : Subgroup G} (hXP : X ≤ Pc M V) (hE_le_P : E ≤ Pc M V)
    (hE : E = Subgroup.closure {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
      x ∈ conjSubgroup c (Pc M V ⊓ W₀)})
    (hgen : ∀ s ∈ {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
      x ∈ conjSubgroup c (Pc M V ⊓ W₀)}, ∀ t ∈ X, ⁅s, t⁆ ∈ V ⊓ W₀) :
    ⁅X, E⁆ ≤ V ⊓ W₀ := by
  have hPCV : Pc M V ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hPA : Pc M V ≤ Subgroup.normalizer ((V ⊓ W₀ : Subgroup G) : Set G) := by
    intro p hp
    rw [mem_normalizer_iff_conjSubgroup_eq, CFSG.RankThree.GF2n.conjSubgroup_inf,
      conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer (V : Set G) (hPCV hp)),
      conjSubgroup_eq_self_iff.mpr (hN (hPH hp))]
  have hXE : ⁅X, E⁆ ≤ V ⊓ W₀ := by
    have hcl := CFSG.Timmesfeld.Bridge.OddLocal.commutator_closure_le
      (S := {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
        x ∈ conjSubgroup c (Pc M V ⊓ W₀)})
      (T := (X : Set G)) (N := V ⊓ W₀)
      ?hS ?hT ?hpair
    · have hcl' : ⁅Subgroup.closure {x : G | ∃ c ∈ Subgroup.centralizer (V : Set G),
          x ∈ conjSubgroup c (Pc M V ⊓ W₀)}, X⁆ ≤ V ⊓ W₀ := by
        simpa [Subgroup.closure_eq] using hcl
      rw [hE, Subgroup.commutator_comm]
      exact hcl'
    · exact hE ▸ hE_le_P.trans hPA
    · exact (Subgroup.closure_le _).mpr fun x hx => (hXP.trans hPA) hx
    · exact hgen
  exact hXE

private theorem RootHyp.normal_inf_kOf_subgroupOf (hPH : Pc M V ≤ H) :
    ((Pc M V ⊓ kOf V H).subgroupOf (Pc M V)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨haP, haK⟩
    refine Subgroup.mem_inf.mpr
      ⟨(Pc M V).mul_mem ((Pc M V).mul_mem hq haP) ((Pc M V).inv_mem hq), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H (hPH hq)) a).mp haK
  · rintro ⟨haP, haK⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (Pc M V).mul_mem ((Pc M V).mul_mem ((Pc M V).inv_mem hq) haP) hq
      simpa [mul_assoc] using h
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kOf V H (hPH hq)) a).mpr haK

private theorem RootHyp.commutator_le_betaSup
    {W₀ : Subgroup G} {E : Subgroup G} (hE_le_P : E ≤ Pc M V)
    (hP_eq : Pc M V = (Pc M V ⊓ kOf V H) ⊔ E)
    {X : Subgroup G}
    (hXK : ⁅X, Pc M V ⊓ kOf V H⁆ = ⊥)
    (hXE : ⁅X, E⁆ ≤ V ⊓ W₀)
    (hAnorm : ((Pc M V ⊓ kOf V H).subgroupOf (Pc M V)).Normal) :
    ⁅X, Pc M V⁆ ≤ V ⊓ W₀ := by
  haveI : ((Pc M V ⊓ kOf V H).subgroupOf (Pc M V)).Normal := hAnorm
  have hPCV : Pc M V ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  rw [Subgroup.commutator_le]
  intro x hx p hp
  have hmem : p ∈ (Pc M V ⊓ kOf V H) ⊔ E := by
    rw [← hP_eq]
    exact hp
  have hmemP : (⟨p, hp⟩ : ↥(Pc M V)) ∈
      (Pc M V ⊓ kOf V H).subgroupOf (Pc M V) ⊔ E.subgroupOf (Pc M V) := by
    rw [← Subgroup.subgroupOf_sup inf_le_left hE_le_P]
    exact Subgroup.mem_subgroupOf.mpr hmem
  obtain ⟨k, hk, e, he, hke⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (Pc M V ⊓ kOf V H).subgroupOf (Pc M V))
      (t := E.subgroupOf (Pc M V))).mp hmemP
  have hkG : (k : G) ∈ Pc M V ⊓ kOf V H := Subgroup.mem_subgroupOf.mp hk
  have heG : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
  have hpe : (k : G) * (e : G) = p := congrArg Subtype.val hke
  have hxk : ⁅x, (k : G)⁆ = 1 := by
    have hmem : ⁅x, (k : G)⁆ ∈ ⁅X, Pc M V ⊓ kOf V H⁆ :=
      Subgroup.commutator_mem_commutator hx hkG
    rw [hXK] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcomm_xk : x * (k : G) * x⁻¹ = k := by
    have h := commutatorElement_eq_one_iff_mul_comm.mp hxk
    calc x * (k : G) * x⁻¹ = (k : G) * x * x⁻¹ := by rw [h]
      _ = k := by group
  have hid : ⁅x, (k : G) * (e : G)⁆ = (k : G) * ⁅x, (e : G)⁆ * (k : G)⁻¹ := by
    have h1 : ⁅x, (k : G) * (e : G)⁆ =
        (x * (k : G) * x⁻¹) * (x * (e : G) * x⁻¹ * (e : G)⁻¹) * (k : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hcomm_xk]
    simp only [commutatorElement_def]
  have hxe : ⁅x, (e : G)⁆ ∈ V ⊓ W₀ :=
    hXE (Subgroup.commutator_mem_commutator hx heG)
  have hkA : (k : G) * ⁅x, (e : G)⁆ * (k : G)⁻¹ = ⁅x, (e : G)⁆ := by
    have hcomm := Subgroup.mem_centralizer_iff.mp (hPCV hkG.1) ⁅x, (e : G)⁆ hxe.1
    calc (k : G) * ⁅x, (e : G)⁆ * (k : G)⁻¹ = ⁅x, (e : G)⁆ * (k : G) * (k : G)⁻¹ := by
          rw [hcomm]
      _ = ⁅x, (e : G)⁆ := by group
  rw [← hpe, hid, hkA]
  exact hxe

theorem RootHyp.commutator_le_inf_of_commutator_inf_kOf_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥)
    {X : Subgroup G} (hXP : X ≤ Pc M V)
    (hXK : ⁅X, Pc M V ⊓ kOf V H⁆ = ⊥) :
    ⁅X, Pc M V⁆ ≤ V ⊓ W₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEdef, hE_le_P, -, hP_eq⟩ :=
    RootHyp.exists_beta_decomposition h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  have hgen := commutator_betaGenerator_le h hPH hVH hW₀ hN hXP
  have hXE := commutator_X_betaSubgroup_le hPH hN hXP hE_le_P hEdef hgen
  have hAnorm := normal_inf_kOf_subgroupOf (V := V) (H := H) (M := M) hPH
  exact commutator_le_betaSup hE_le_P hP_eq hXK hXE hAnorm

theorem RootHyp.commutator_inf_conj_Pc_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    ⁅Pc M V ⊓ conjSubgroup h₀ (Pc M V), Pc M V⁆ ≤ V ⊓ W₀ := by
  classical
  obtain ⟨y, hyH, hPy, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  refine RootHyp.commutator_le_inf_of_commutator_inf_kOf_eq_bot h hPH hVH hH hnM hK hnab hL
    hW₀ hN hW₀ne inf_le_left ?_
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  have haP : a ∈ Pc M V := ha.1
  have haPy : a ∈ conjSubgroup y (Pc M V) := by simpa [hPy] using ha.2
  have hbP : b ∈ Pc M V := hb.1
  have hbK : b ∈ kOf V H := hb.2
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hV : ⁅a, b⁆ ∈ V :=
    h.toHyp.frattini_Pc_le (commutatorElement_mem_inSubgroup_frattini hP2 haP hbP)
  have hbN : b ∈ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) :=
    RootHyp.kOf_le_normalizer_conjSubgroup_Pc_of_mem h hyH hbK
  have hPy : ⁅a, b⁆ ∈ conjSubgroup y (Pc M V) := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ conjSubgroup y (Pc M V) :=
      (Subgroup.mem_normalizer_iff.mp hbN (a⁻¹)).mp
        ((conjSubgroup y (Pc M V)).inv_mem haPy)
    have he : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact (conjSubgroup y (Pc M V)).mul_mem haPy h1
  have hmem : ⁅a, b⁆ ∈ V ⊓ conjSubgroup y (Pc M V) := Subgroup.mem_inf.mpr ⟨hV, hPy⟩
  rw [RootHyp.inf_conj_Pc_eq_bot h hHy hnM] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem RootHyp.commutator_inf_xOf_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    ⁅Pc M V ⊓ Tim79a.xOf V H, Pc M V⁆ ≤ V ⊓ W₀ := by
  refine RootHyp.commutator_le_inf_of_commutator_inf_kOf_eq_bot h hPH hVH hH hnM hK hnab hL
    hW₀ hN hW₀ne inf_le_left ?_
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  have hcomm : a * b = b * a :=
    Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hb.2).2 a ha.2
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

end CFSG.RankThree.GF2n.Tim81
