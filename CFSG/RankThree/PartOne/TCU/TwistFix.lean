module

public import CFSG.RankThree.PartOne.S11d.PSUGood

public section

namespace CFSG.RankThree.PartOne.TCU

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.OddIso
open scoped commutatorElement

variable {F n p : ℕ} {K : Type} [Field K]

section Defs

variable (h : UnitaryFieldData 2 F K) {u : Module.End K (Fin n → K)}

@[expose] noncomputable def DqU (hodd : Odd p) (hup : u ^ p = 1) : Subgroup (SUn h n) :=
  haveI : CharP K 2 := h.charP
  (Dfix (idForm h n) (isCompl_ker_range hodd hup)).comap
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)
      ).toMonoidHom.comp (gramSU h (idGram K n)).subtype)

theorem mem_DqU (hiso : ∀ v w, idForm h n (u v) (u w) = idForm h n v w) (hodd : Odd p)
    (hup : u ^ p = 1) (g : SUn h n) :
    g ∈ DqU h hodd hup ↔ ∀ w ∈ LinearMap.range (u - 1), linOf (g : GL (Fin n) K) w = w := by
  have : CharP K 2 := h.charP
  change Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) ∈
    Dfix (idForm h n) (isCompl_ker_range hodd hup) ↔ _
  rw [mem_Dfix_iff' (idForm_isSymm h n) (idForm_separatingLeft h n) hiso hodd hup,
    toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (g : GL (Fin n) K)]
  simp only [coe_toLin_eq, and_iff_right g.2]

end Defs

structure TwistSetup (h : UnitaryFieldData 2 F K) (n p : ℕ) (A : SUn h n)
    (u : Module.End K (Fin n → K)) (c : K) : Prop where
  hodd : Odd p
  hq : 4 ≤ 2 ^ F
  hc : c ≠ 0
  hAc : linOf (A : GL (Fin n) K) = c • u
  hiso : ∀ v w, idForm h n (u v) (u w) = idForm h n v w
  hup : u ^ p = 1
  hcyc : IsCyclicOn u (LinearMap.range (u - 1))
  hm : 2 ≤ Module.finrank K (LinearMap.ker (u - 1))

section Basic

variable {h : UnitaryFieldData 2 F K} {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K}
  (S : TwistSetup h n p A u c)

noncomputable abbrev TwistSetup.D : Subgroup (SUn h n) := DqU h S.hodd S.hup

theorem TwistSetup.mem_D (g : SUn h n) :
    g ∈ S.D ↔ ∀ w ∈ LinearMap.range (u - 1), linOf (g : GL (Fin n) K) w = w :=
  mem_DqU h S.hiso S.hodd S.hup g

omit S in
theorem linOf_inv_apply (g : SUn h n) (v : Fin n → K) :
    linOf ((g⁻¹ : SUn h n) : GL (Fin n) K) (linOf (g : GL (Fin n) K) v) = v := by
  rw [← Module.End.mul_apply, ← linOf_mul, Subgroup.coe_inv, inv_mul_cancel, linOf_one]
  rfl

omit S in
theorem linOf_apply_inv (g : SUn h n) (v : Fin n → K) :
    linOf (g : GL (Fin n) K) (linOf ((g⁻¹ : SUn h n) : GL (Fin n) K) v) = v := by
  rw [← Module.End.mul_apply, ← linOf_mul, Subgroup.coe_inv, mul_inv_cancel, linOf_one]
  rfl

include S in
theorem TwistSetup.commute_iff (g : SUn h n) :
    g * A = A * g ↔ linOf (g : GL (Fin n) K) * u = u * linOf (g : GL (Fin n) K) := by
  have h1 : g * A = A * g ↔ (g : GL (Fin n) K) * A = A * g := by
    constructor
    · intro e
      exact congrArg Subtype.val e
    · intro e
      exact Subtype.ext e
  rw [h1, ← linOf_injective.eq_iff, linOf_mul, linOf_mul, S.hAc, mul_smul_comm, smul_mul_assoc]
  exact smul_right_injective _ S.hc |>.eq_iff

include S in
theorem TwistSetup.mem_centralizer_iff (g : SUn h n) :
    g ∈ Subgroup.centralizer ({A} : Set (SUn h n)) ↔
      linOf (g : GL (Fin n) K) * u = u * linOf (g : GL (Fin n) K) := by
  rw [Subgroup.mem_centralizer_singleton_iff, S.commute_iff]

theorem TwistSetup.apply_ker {g : SUn h n} (hg : g ∈ S.D) {v : Fin n → K}
    (hv : v ∈ LinearMap.ker (u - 1)) : linOf (g : GL (Fin n) K) v ∈ LinearMap.ker (u - 1) := by
  have : CharP K 2 := h.charP
  obtain ⟨δ, -, hδg⟩ := hg
  have h1 := extGL_apply_left (isCompl_ker_range S.hodd S.hup) δ hv
  have hδg' : extGL (isCompl_ker_range S.hodd S.hup) δ =
      Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) := hδg
  have h2 : ((extGL (isCompl_ker_range S.hodd S.hup) δ : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) v = linOf (g : GL (Fin n) K) v := by
    rw [hδg', coe_toLin_eq]
  rw [← h2, h1]
  exact (((δ : LinearMap.GeneralLinearGroup K ↥(LinearMap.ker (u - 1))) :
    ↥(LinearMap.ker (u - 1)) →ₗ[K] ↥(LinearMap.ker (u - 1))) ⟨v, hv⟩).2

theorem TwistSetup.D_comm {g : SUn h n} (hg : g ∈ S.D) :
    linOf (g : GL (Fin n) K) * u = u * linOf (g : GL (Fin n) K) := by
  have : CharP K 2 := h.charP
  refine LinearMap.ext fun v => ?_
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range S.hodd S.hup v
  have huv₁ : u v₁ = v₁ := sub_eq_zero.mp (LinearMap.mem_ker.mp hv₁)
  have hgv₁ : u (linOf (g : GL (Fin n) K) v₁) = linOf (g : GL (Fin n) K) v₁ :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp (S.apply_ker hg hv₁))
  have hgw : linOf (g : GL (Fin n) K) w = w := (S.mem_D g).mp hg w hw
  have huw : u w ∈ LinearMap.range (u - 1) := range_invariant u hw
  have hguw : linOf (g : GL (Fin n) K) (u w) = u w := (S.mem_D g).mp hg _ huw
  simp only [Module.End.mul_apply, map_add]
  rw [huv₁, hgw, hgv₁, hguw]

theorem TwistSetup.D_le_centralizer : S.D ≤ Subgroup.centralizer ({A} : Set (SUn h n)) :=
  fun _ hg => (S.mem_centralizer_iff _).mpr (S.D_comm hg)

theorem TwistSetup.D_norm : ∀ g ∈ Subgroup.centralizer ({A} : Set (SUn h n)), ∀ f ∈ S.D,
    g * f * g⁻¹ ∈ S.D := by
  intro g hg f hf
  have hginv : linOf ((g⁻¹ : SUn h n) : GL (Fin n) K) * u =
      u * linOf ((g⁻¹ : SUn h n) : GL (Fin n) K) :=
    (S.mem_centralizer_iff _).mp ((Subgroup.centralizer _).inv_mem hg)
  rw [S.mem_D]
  intro w hw
  have hw' : linOf ((g⁻¹ : SUn h n) : GL (Fin n) K) w ∈ LinearMap.range (u - 1) :=
    range_map_mem hginv hw
  have h1 := (S.mem_D f).mp hf _ hw'
  rw [Subgroup.coe_mul, Subgroup.coe_mul, linOf_mul, linOf_mul, Module.End.mul_apply,
    Module.End.mul_apply, h1]
  exact linOf_apply_inv g w

theorem TwistSetup.D_commutator {g g' : SUn h n}
    (hg : g ∈ Subgroup.centralizer ({A} : Set (SUn h n)))
    (hg' : g' ∈ Subgroup.centralizer ({A} : Set (SUn h n))) : ⁅g, g'⁆ ∈ S.D := by
  have hgc := (S.mem_centralizer_iff _).mp hg
  have hg'c := (S.mem_centralizer_iff _).mp hg'
  have hginv := (S.mem_centralizer_iff _).mp ((Subgroup.centralizer _).inv_mem hg)
  have hg'inv := (S.mem_centralizer_iff _).mp ((Subgroup.centralizer _).inv_mem hg')
  rw [S.mem_D]
  intro w hw
  have hw₁ : linOf ((g'⁻¹ : SUn h n) : GL (Fin n) K) w ∈ LinearMap.range (u - 1) :=
    range_map_mem hg'inv hw
  have hw₂ : linOf ((g⁻¹ : SUn h n) : GL (Fin n) K)
      (linOf ((g'⁻¹ : SUn h n) : GL (Fin n) K) w) ∈ LinearMap.range (u - 1) :=
    range_map_mem hginv hw₁
  have hcomm := commute_on_range S.hcyc hgc hg'c _ hw₂
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, linOf_mul,
    linOf_mul, linOf_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [hcomm, linOf_apply_inv g, linOf_apply_inv g']

theorem TwistSetup.two_mem_D {g : SUn h n} (hg : g ∈ Subgroup.centralizer ({A} : Set (SUn h n)))
    {k : ℕ} (hk : g ^ 2 ^ k = 1) : g ∈ S.D := by
  have : CharP K 2 := h.charP
  rw [S.mem_D]
  refine eq_id_on_range_of_two_pow S.hodd S.hup S.hcyc ((S.mem_centralizer_iff _).mp hg)
    (k := k) ?_
  rw [← linOf_pow, ← Subgroup.coe_pow, hk]
  exact linOf_one

theorem TwistSetup.D_quasisimple : CFSG.IsQuasisimple ↥S.D := by
  have : CharP K 2 := h.charP
  set hc := isCompl_ker_range S.hodd S.hup with hchc
  let ψ : SUn h n →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)
      ).toMonoidHom.comp (gramSU h (idGram K n)).subtype
  have hψinj : Function.Injective ψ :=
    Matrix.GeneralLinearGroup.toLin.injective.comp Subtype.val_injective
  have hle : Dfix (idForm h n) hc ≤ ψ.range := by
    intro δ hδ
    obtain ⟨hδS, -⟩ := (mem_Dfix_iff' (idForm_isSymm h n) (idForm_separatingLeft h n) S.hiso
      S.hodd S.hup δ).mp hδ
    have hmem : (Matrix.GeneralLinearGroup.toLin.symm δ : GL (Fin n) K) ∈ gramSU h (idGram K n) :=
      (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) _).mp (by
        rw [MulEquiv.apply_symm_apply]
        exact hδS)
    exact ⟨⟨_, hmem⟩, by
      change Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm δ) = δ
      exact MulEquiv.apply_symm_apply _ _⟩
  have hmap : S.D.map ψ = Dfix (idForm h n) hc :=
    Subgroup.map_comap_eq_self hle
  let e1 : ↥S.D ≃* ↥(Dfix (idForm h n) hc) :=
    (Subgroup.equivMapOfInjective S.D ψ hψinj).trans (MulEquiv.subgroupCongr hmap)
  let e2 : ↥(Dfix (idForm h n) hc) ≃* sesqSpecialUnitaryGroup
      ((idForm h n).domRestrict₁₂ (LinearMap.ker (u - 1)) (LinearMap.ker (u - 1))) :=
    (Subgroup.equivMapOfInjective _ (extGL hc) (extGL_injective hc)).symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2).symm
    (KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le h
      (fixSpace_isSymm (idForm_isSymm h n))
      (fixSpace_sep (idForm_separatingLeft h n) S.hiso S.hodd S.hup) S.hm
      ⟨fun _ => S.hq, fun _ => by have := S.hq; omega⟩)

end Basic

section Proj

variable {h : UnitaryFieldData 2 F K} {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K}

theorem psu_core (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    (hn1 : 1 ≤ n) (S : TwistSetup h n p A u c) (hAp : A ^ p = 1) :
    ∃ D : Subgroup (PSUn h n), CFSG.IsQuasisimple ↥D ∧
      D ≤ Subgroup.centralizer ({(A : PSUn h n)} : Set (PSUn h n)) ∧
      (∀ g ∈ Subgroup.centralizer ({(A : PSUn h n)} : Set (PSUn h n)), ∀ d ∈ D,
        g * d * g⁻¹ ∈ D) ∧
      (∀ g ∈ Subgroup.centralizer ({(A : PSUn h n)} : Set (PSUn h n)),
        ∀ g' ∈ Subgroup.centralizer ({(A : PSUn h n)} : Set (PSUn h n)), ⁅g, g'⁆ ∈ D) ∧
      (∀ g ∈ Subgroup.centralizer ({(A : PSUn h n)} : Set (PSUn h n)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ D) := by
  classical
  have : CharP K 2 := h.charP
  have hsurj : Function.Surjective (piSU h n) := QuotientGroup.mk'_surjective _
  have hlift : ∀ y ∈ Subgroup.centralizer ({(A : PSUn h n)} : Set (PSUn h n)),
      ∃ g : SUn h n, piSU h n g = y ∧ g ∈ Subgroup.centralizer ({A} : Set (SUn h n)) := by
    intro y hy
    obtain ⟨g, rfl⟩ := hsurj y
    refine ⟨g, rfl, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact commute_of_mk_commute h hn1 hZp hAp (Subgroup.mem_centralizer_singleton_iff.mp hy)
  refine ⟨S.D.map (piSU h n), ?_, ?_, ?_, ?_, ?_⟩
  · refine CFSG.LocalCores.isQuasisimple_map S.D_quasisimple (piSU h n) fun hle => ?_
    exact not_le_center_of_isQuasisimple S.D_quasisimple (hle.trans (piSU_ker_le_center h))
  · rintro _ ⟨d, hd, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (S.D_le_centralizer hd)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change piSU h n d * piSU h n A = piSU h n A * piSU h n d
    rw [← map_mul, ← map_mul, h1]
  · rintro y hy _ ⟨d, hd, rfl⟩
    obtain ⟨g, rfl, hg⟩ := hlift y hy
    refine ⟨g * d * g⁻¹, S.D_norm g hg d hd, ?_⟩
    simp only [map_mul, map_inv]
  · intro y hy y' hy'
    obtain ⟨g, rfl, hg⟩ := hlift y hy
    obtain ⟨g', rfl, hg'⟩ := hlift y' hy'
    refine ⟨⁅g, g'⁆, S.D_commutator hg hg', ?_⟩
    simp only [map_commutatorElement]
  · intro y hy hk
    obtain ⟨k, hk⟩ := hk
    have hy2 : y ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    obtain ⟨g, hg2, rfl⟩ := exists_lift_two_pow h hn1 hy2
    have hgC : g ∈ Subgroup.centralizer ({A} : Set (SUn h n)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_mk_commute h hn1 hZp hAp (Subgroup.mem_centralizer_singleton_iff.mp hy))
    exact ⟨g, S.two_mem_D hgC hg2, rfl⟩

end Proj

end CFSG.RankThree.PartOne.TCU
