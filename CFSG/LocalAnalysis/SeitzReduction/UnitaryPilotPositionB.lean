module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotFusion
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotPositionBRootSU2
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionTransport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionPerfectOdd

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Open (standardComponentIsStandard)
open CFSG.Quasithin (perfectCore map_perfectCore)

theorem forall_normal_isPGroup_eq_bot_of_isQuasisimple_of_odd_center {M : Type*} [Group M]
    [Finite M] (hM : CFSG.IsQuasisimple M) (hZ : Odd (Nat.card (center M))) (N : Subgroup M)
    (hN : N.Normal) (hNp : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hM N with hNZ | hNtop
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hNp
    have hdvd : Nat.card N ∣ Nat.card (center M) := Subgroup.card_dvd_of_le hNZ
    rw [hk] at hdvd
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero] at hk
      exact Subgroup.card_eq_one.1 hk
    · exfalso
      have h2 : 2 ∣ Nat.card (center M) := (dvd_pow_self 2 hpos.ne').trans hdvd
      exact (Nat.not_even_iff_odd.2 hZ) (even_iff_two_dvd.2 h2)
  · exfalso
    have hMp : IsPGroup 2 M := by
      rw [hNtop] at hNp
      exact hNp.of_equiv Subgroup.topEquiv
    have : IsSimpleGroup (M ⧸ center M) := hM.2.1
    have htop := EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup (p := 2) hM.2.2
      (⊤ : Subgroup (M ⧸ center M)) inferInstance ((hMp.to_quotient (center M)).to_subgroup ⊤)
    obtain ⟨x, hx⟩ := exists_ne (1 : M ⧸ center M)
    exact hx (by simpa [htop] using (mem_top x : x ∈ (⊤ : Subgroup (M ⧸ center M))))

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem forall_normal_isPGroup_eq_bot_blockSU_compl_pair (hn : 6 ≤ n) {i j : Fin n}
    (hij : i ≠ j) (N : Subgroup (blockSU h ({i, j}ᶜ : Finset (Fin n)))) (hN : N.Normal)
    (hNp : IsPGroup 2 N) : N = ⊥ := by
  have := finite_unitaryPSU h n
  exact forall_normal_isPGroup_eq_bot_of_isQuasisimple_of_odd_center
    (isQuasisimple_blockSU_compl_pair h hn hij)
    (odd_card_center_blockSU h (by rw [card_compl_pair hij]; omega)) N hN hNp

section Coordinates

variable {G : Type*} [Group G] [Finite G] {φ φ' : unitaryPSU h n →* G}

omit [Finite G] in
theorem map_conj_map_map_conj (H : Subgroup (unitaryPSU h n)) (g₀ : unitaryPSU h n) (q₀ : G) :
    ((H.map (MulAut.conj g₀).toMonoidHom).map φ').map (MulAut.conj q₀).toMonoidHom =
      (H.map φ').map (MulAut.conj (q₀ * φ' g₀)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]
  group

omit [Finite G] in
theorem exists_le_range_inf_centralizer_of_le_conj_rootSU2 (hφ' : Function.Injective φ')
    {c d : Fin n} {X : Subgroup G} {h₀ : G} (hh₀ : h₀ ∈ φ'.range)
    (hX : X ≤ ((rootSU2 h c d).map φ').map (MulAut.conj h₀).toMonoidHom) :
    ∃ P₀ : Subgroup G, P₀ ≤ φ'.range ⊓ centralizer (X : Set G) ∧
      Nonempty (P₀ ≃* blockSU h ({c, d}ᶜ : Finset (Fin n))) := by
  refine ⟨((blockSU h ({c, d}ᶜ : Finset (Fin n))).map φ').map (MulAut.conj h₀).toMonoidHom,
    le_inf ?_ ?_, ?_⟩
  · rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    obtain ⟨y, rfl⟩ := hh₀
    exact ⟨y * s * y⁻¹, by simp [MulAut.conj_apply]⟩
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hX hx
    have hsr : r * s = s * r :=
      commute_blockSU_of_disjoint h disjoint_compl_right r hr s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h₀ * φ' r * h₀⁻¹ * (h₀ * φ' s * h₀⁻¹) = h₀ * φ' (r * s) * h₀⁻¹ := by
          rw [map_mul]; group
      _ = h₀ * φ' (s * r) * h₀⁻¹ := by rw [hsr]
      _ = h₀ * φ' s * h₀⁻¹ * (h₀ * φ' r * h₀⁻¹) := by rw [map_mul]; group
  · exact ⟨((((blockSU h ({c, d}ᶜ : Finset (Fin n))).map φ').equivMapOfInjective _
      (MulAut.conj h₀).injective).symm.trans
      ((blockSU h ({c, d}ᶜ : Finset (Fin n))).equivMapOfInjective _ hφ').symm)⟩

theorem exists_le_range_inf_centralizer_mulEquiv_blockSU (hn : 6 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') {i j : Fin n} (hij : i ≠ j)
    (hΛ : (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ =
      (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ')
    {a b : Fin n} (ha : a ∈ ({i, j}ᶜ : Finset (Fin n))) (hb : b ∈ ({i, j}ᶜ : Finset (Fin n)))
    (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (rootSU2 h a b).map φ) :
    ∃ P₀ : Subgroup G, P₀ ≤ φ'.range ⊓ centralizer (X : Set G) ∧
      Nonempty (P₀ ≃* blockSU h ({a, b}ᶜ : Finset (Fin n))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := blockSU h ({i, j}ᶜ : Finset (Fin n)) with hMdef
  obtain ⟨Q, hQp, hΛeq, hQM, hMN, -⟩ := perfectCore_centralizer_stdTransvection h hn hij
  rw [hΛeq] at hΛ
  have hM := forall_normal_isPGroup_eq_bot_blockSU_compl_pair h hn hij
  have hJ : rootSU2 h a b ≤ M := rootSU2_le_blockSU h ha hb
  have hX2 : ¬ 2 ∣ Nat.card X := fun h2 => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h2)
  obtain ⟨hQeq, ι, -, q₀, hq₀, hXq⟩ := EPilot.exists_conj_le_map_of_two_decompositions hφ hφ' hQp
    hQp hM hM hMN hMN (disjoint_iff.2 hQM) (disjoint_iff.2 hQM) hΛ hJ hXJ hX2
  have hcard : ({i, j}ᶜ : Finset (Fin n)).card = n - 2 := card_compl_pair hij
  obtain ⟨g₀, -, hψ⟩ := exists_map_rootSU2_of_mulAut_blockSU h (by omega)
    (fun h3 => by have := h3.1; omega) (by omega) ι ha hb hab
  have hιJ : (((rootSU2 h a b).subgroupOf M).map ι.toMonoidHom).map M.subtype ≤
      (rootSU2 h a b).map (MulAut.conj g₀).toMonoidHom := by
    rw [hψ, subgroupOf_map_subtype]
    exact inf_le_left
  have hq₀' : q₀ ∈ φ'.range := by
    rw [hQeq] at hq₀
    obtain ⟨x, -, rfl⟩ := hq₀
    exact ⟨x, rfl⟩
  have hX' : X ≤ ((rootSU2 h a b).map φ').map (MulAut.conj (q₀ * φ' g₀)).toMonoidHom := by
    rw [← map_conj_map_map_conj h]
    exact hXq.trans (map_mono (map_mono hιJ))
  exact exists_le_range_inf_centralizer_of_le_conj_rootSU2 h hφ' (mul_mem hq₀' ⟨g₀, rfl⟩) hX'

end Coordinates

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
private theorem range_subtype_comp_symm {C : Type*} [Group C] (e : L ≃* C) :
    (L.subtype.comp e.symm.toMonoidHom).range = L := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact (e.symm c).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp⟩

private theorem map_perfectCore_centralizer_singleton_of_injective {A : Type*} [Group A] [Finite A]
    {f : A →* G} (hf : Function.Injective f) (a : A) :
    (perfectCore (centralizer ({a} : Set A))).map f =
      perfectCore (f.range ⊓ centralizer ({f a} : Set G)) := by
  rw [map_perfectCore]
  congr 1
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine mem_inf.2 ⟨⟨b, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hb
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hb]
  · intro hx
    obtain ⟨⟨b, rfl⟩, hb⟩ := mem_inf.1 hx
    refine ⟨b, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hb
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact hf hb

theorem exists_le_centralizer_mulEquiv_of_seitzSetting (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSU2 h a b).map e.symm.toMonoidHom).map L.subtype) :
    ∃ g₁ y₁ : G,
      y₁ ∈ ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype ∧
      orderOf y₁ = 2 ∧ g₁⁻¹ * t * g₁ = t * y₁ ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({t * y₁} : Set G) ∧
        Nonempty (P ≃* ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
          L.subtype) := by
  have := finite_unitaryPSU h n
  have hKt := inf_centralizer_eq_zpowers hset e (by omega) htC ht
  have hq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hOut := isSolvable_outer_of_mulEquiv h (by omega) hq e
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1
    (show 1 < ({a, b}ᶜ : Finset (Fin n)).card by rw [card_compl_pair hab]; omega)
  have haij : a ∈ ({i, j}ᶜ : Finset (Fin n)) :=
    mem_compl_of_ne (ne_left_of_mem_compl hi).symm (ne_left_of_mem_compl hj).symm
  have hbij : b ∈ ({i, j}ᶜ : Finset (Fin n)) :=
    mem_compl_of_ne (ne_right_of_mem_compl hi).symm (ne_right_of_mem_compl hj).symm
  obtain ⟨g, y, -, hg, ⟨hyL, hye⟩, ⟨hyL', hyT'⟩, hact⟩ :=
    exists_conj_eq_mul_stdTransvection h hset e hn ht hKt hij
  set φ : unitaryPSU h n →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := range_subtype_comp_symm e
  have hmap : ∀ H : Subgroup (unitaryPSU h n),
      (H.map e.symm.toMonoidHom).map L.subtype = H.map φ := fun H => by rw [Subgroup.map_map]
  rw [hmap] at hXJ ⊢
  have hyφ : φ (stdTransvection h hij) = y := by
    rw [← hye]
    simp [hφdef]
  have hz2 : stdTransvection h hij * stdTransvection h hij = 1 := by
    rw [stdTransvection, ← map_mul, tvTransSU_mul_self, map_one]
  have hy2 : orderOf y = 2 := by
    rw [← hyφ, orderOf_injective φ hφ]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) (stdTransvection_ne_one h hij)
  refine ⟨g, y, ⟨_, stdTransvection_mem_blockSU h hij hi hj, hyφ⟩, hy2, hg, ?_⟩
  have hw' : y⁻¹ * t ∈ centralizer (CFSG.conjugate L g : Set G) :=
    EPilot.inv_mul_mem_centralizer_of_conj_eq hact
  have hΛeq := EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset.standardSetting hOut
    htC ht (Or.inr hg) hw'
  set e' : CFSG.conjugate L g ≃* unitaryPSU h n := (conjugateMulEquiv L g).symm.trans e
    with he'
  obtain ⟨c', hc'⟩ := exists_conj_eq_stdTransvection h (by omega) hyT' hij
  set φ' : unitaryPSU h n →* G :=
    ((CFSG.conjugate L g).subtype.comp e'.symm.toMonoidHom).comp (MulAut.conj c'⁻¹).toMonoidHom
    with hφ'def
  have hφ' : Function.Injective φ' :=
    ((CFSG.conjugate L g).subtype_injective.comp e'.symm.injective).comp
      (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, range_subtype_comp_symm]
  have hconj : (MulAut.conj c'⁻¹) (stdTransvection h hij) = e' ⟨y, hyL'⟩ := by
    rw [← hc', MulAut.conj_apply, inv_inv]
    group
  have hφ'y : φ' (stdTransvection h hij) = y := by
    rw [hφ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hconj, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hΛ : (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ =
      (perfectCore (centralizer ({stdTransvection h hij} : Set (unitaryPSU h n)))).map φ' := by
    rw [map_perfectCore_centralizer_singleton_of_injective hφ,
      map_perfectCore_centralizer_singleton_of_injective hφ', hφr, hφ'r, hyφ, hφ'y, hΛeq]
  obtain ⟨P₀, hP₀, ⟨eP₀⟩⟩ := exists_le_range_inf_centralizer_mulEquiv_blockSU h hn hφ hφ'
    hij hΛ haij hbij hab hXodd hXJ
  refine ⟨P₀, le_inf (hP₀.trans inf_le_right) ?_,
    ⟨eP₀.trans ((blockSU h ({a, b}ᶜ : Finset (Fin n))).equivMapOfInjective φ hφ)⟩⟩
  have hP₀L : P₀ ≤ CFSG.conjugate L g := hφ'r ▸ hP₀.trans inf_le_left
  rw [← hg]
  exact hP₀L.trans (EPilot.conjugate_le_centralizer_conj htC g)

theorem not_normal_neighbour_unitaryRootTorus (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G} (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  obtain ⟨-, htX, -, hXc, hXJ, -, hDC, hDq, -, hZ, hOutD⟩ :=
    neighbour_data_unitaryRootTorus h e hn hab htC hX hDe
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_unitaryRootTorus_of_seitzSetting h hset e hn htC ht hab hX htX hDe
  have hXodd : Odd (Nat.card X) := hXc ▸ odd_two_pow_add_one h.one_le
  obtain ⟨-, y₁, hy₁D, hy₁, -, P, hP, hPD⟩ :=
    exists_le_centralizer_mulEquiv_of_seitzSetting h hset e hn htC ht hab hXodd hXJ
  rw [← hDe] at hy₁D hPD
  exact LinearPilot.not_normal_map_oddCore_centralizer_of_mulEquiv_of_odd_center htX ht
    (hDC.trans inf_le_left) hDq hZ hOutD (hDC.trans inf_le_right) hsyl hy₁D hy₁ (Or.inr rfl) hP
    hPD

end Setting

end CFSG.SeitzReduction.UnitaryPilot
