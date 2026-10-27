module

public import CFSG.RankThree.PartOne.S11d.PSUPair
public import CFSG.RankThree.PartOne.S11d.PSULift
public import CFSG.RankThree.PartOne.S11d.PSUModel
public import CFSG.RankThree.PartOne.S11d.PerfectCentral
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.OddIso
open CFSG.Blueprint (LieModel)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

variable {F n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

structure PSUSetup (h : UnitaryFieldData 2 F K) (n p : ℕ) (σ : K ≃+* K) (A : GL (Fin n) K) :
    Prop where
  hn : 3 ≤ n
  hp : p.Prime
  hp5 : 5 ≤ p
  hσ : orderOf σ = p
  hq : 4 ≤ 2 ^ F
  hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1
  hA : A ∈ gramSU h (idGram K n)
  hAp : A ^ p = 1
  hA1 : A ≠ 1
  hσA : glAut σ A = A
  hcyc : IsCyclicOn (linOf A) (LinearMap.range (linOf A - 1))
  hm : 2 ≤ Module.finrank K (LinearMap.ker (linOf A - 1))

section Basic

variable {σ : K ≃+* K} {A : GL (Fin n) K} (S : PSUSetup h n p σ A)

include S

theorem PSUSetup.hodd : Odd p := S.hp.odd_of_ne_two (by have := S.hp5; omega)

theorem PSUSetup.hAp' : linOf A ^ p = 1 := by rw [← linOf_pow, S.hAp, linOf_one]

theorem PSUSetup.hn1 : 1 ≤ n := by have := S.hn; omega

end Basic

section Subgroups

variable {σ : K ≃+* K} {A : GL (Fin n) K} (S : PSUSetup h n p σ A)

theorem range_ne_bot_of_ne_one (hA1 : A ≠ 1) : LinearMap.range (linOf A - 1) ≠ ⊥ := by
  intro hbot
  apply hA1
  apply linOf_injective
  rw [linOf_one]
  refine LinearMap.ext fun v => ?_
  have h0 : (linOf A - 1) v = 0 := by
    have hv : (linOf A - 1) v ∈ LinearMap.range (linOf A - 1) := ⟨v, rfl⟩
    rw [hbot] at hv
    exact (Submodule.mem_bot K).mp hv
  exact sub_eq_zero.mp (by simpa using h0)

@[expose] noncomputable def Bq : Subgroup (SUn h n) :=
  (Dq h S.hodd S.hAp').subgroupOf (gramSU h (idGram K n))

theorem Dq_apply_fix {g : GL (Fin n) K} (hg : g ∈ Dq h S.hodd S.hAp') {v : Fin n → K}
    (hv : v ∈ LinearMap.ker (linOf A - 1)) : linOf g v ∈ LinearMap.ker (linOf A - 1) := by
  have : CharP K 2 := h.charP
  obtain ⟨δ, -, hδg⟩ := hg
  have h1 := extGL_apply_left (isCompl_ker_range S.hodd S.hAp') δ hv
  have hδg' : extGL (isCompl_ker_range S.hodd S.hAp') δ = Matrix.GeneralLinearGroup.toLin g := hδg
  have h2 : ((extGL (isCompl_ker_range S.hodd S.hAp') δ : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) v = linOf g v := by
    rw [hδg', coe_toLin_eq]
  rw [← h2, h1]
  exact (((δ : LinearMap.GeneralLinearGroup K ↥(LinearMap.ker (linOf A - 1))) :
    ↥(LinearMap.ker (linOf A - 1)) →ₗ[K] ↥(LinearMap.ker (linOf A - 1))) ⟨v, hv⟩).2

theorem Dq_comm {g : GL (Fin n) K} (hg : g ∈ Dq h S.hodd S.hAp') : g * A = A * g := by
  have : CharP K 2 := h.charP
  have hgfix := ((mem_Dq_iff h S.hodd S.hA S.hAp' g).mp hg).2
  apply linOf_injective
  rw [linOf_mul, linOf_mul]
  refine LinearMap.ext fun v => ?_
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range S.hodd S.hAp' v
  have hAv₁ : linOf A v₁ = v₁ := sub_eq_zero.mp (LinearMap.mem_ker.mp hv₁)
  have hgv₁ : linOf A (linOf g v₁) = linOf g v₁ :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp (Dq_apply_fix h S hg hv₁))
  have hAw : linOf A w ∈ LinearMap.range (linOf A - 1) := range_invariant (linOf A) hw
  simp only [Module.End.mul_apply, map_add]
  rw [hAv₁, hgfix w hw, hgfix _ hAw, hgv₁]

theorem Bq_le_centralizer :
    Bq h S ≤ Subgroup.centralizer ({(⟨A, S.hA⟩ : SUn h n)} : Set (SUn h n)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Dq_comm h S hg)

theorem Bq_norm : ∀ g ∈ Subgroup.centralizer ({(⟨A, S.hA⟩ : SUn h n)} : Set (SUn h n)),
    ∀ f ∈ Bq h S, g * f * g⁻¹ ∈ Bq h S := by
  have : CharP K 2 := h.charP
  intro g hg f hf
  have hgA : (g : GL (Fin n) K) * A = A * g := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact congrArg Subtype.val this
  have hgU : Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) ∈ sesqUnitaryGroup (idForm h n) :=
    (toLin_mem_sesqUnitaryGroup_iff _).mpr ((mem_gramSU_iff_unitary h).mp g.2).1
  have hcomm : ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) * linOf A =
      linOf A * ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) := by
    rw [coe_toLin_eq, ← linOf_mul, ← linOf_mul, hgA]
  have := conj_mem_Dfix (idForm_isSymm h n) (idForm_separatingLeft h n) (linOf_isom_A h S.hA)
    S.hodd S.hAp' hgU hcomm (δ := Matrix.GeneralLinearGroup.toLin (f : GL (Fin n) K)) hf
  change Matrix.GeneralLinearGroup.toLin ((g : GL (Fin n) K) * (f : GL (Fin n) K) *
    (g : GL (Fin n) K)⁻¹) ∈ Dfix (idForm h n) (isCompl_ker_range S.hodd S.hAp')
  rw [map_mul, map_mul, map_inv]
  exact this

noncomputable def eBq : ↥(Bq h S) ≃* sesqSpecialUnitaryGroup
    ((idForm h n).domRestrict₁₂ (LinearMap.ker (linOf A - 1)) (LinearMap.ker (linOf A - 1))) :=
  haveI : CharP K 2 := h.charP
  ((Subgroup.subgroupOfEquivOfLe (Dq_le_gramSU h S.hodd S.hA S.hAp')).trans
    ((Subgroup.equivMapOfInjective (Dq h S.hodd S.hAp')
      Matrix.GeneralLinearGroup.toLin.toMonoidHom Matrix.GeneralLinearGroup.toLin.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective
        Matrix.GeneralLinearGroup.toLin.surjective _)))).trans
    (Subgroup.equivMapOfInjective _ (extGL (isCompl_ker_range S.hodd S.hAp'))
      (extGL_injective _)).symm

theorem Bq_quasisimple : CFSG.IsQuasisimple ↥(Bq h S) := by
  have : CharP K 2 := h.charP
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (eBq h S).symm
    (KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le h
      (fixSpace_isSymm (idForm_isSymm h n))
      (fixSpace_sep (idForm_separatingLeft h n) (linOf_isom_A h S.hA) S.hodd S.hAp') S.hm
      ⟨fun _ => S.hq, fun _ => by have := S.hq; omega⟩)

theorem scalar_mem_Bq {c : Kˣ} (hc : (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈
    Dq h S.hodd S.hAp') : c = 1 := by
  have hfix := ((mem_Dq_iff h S.hodd S.hA S.hAp' _).mp hc).2
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (range_ne_bot_of_ne_one S.hA1)
  have h1 := hfix w hw
  rw [linOf_apply] at h1
  have h2 : (c : K) • w = w := by
    have h1' : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ w = (c : K) • w := by
      funext i
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    exact h1'.symm.trans h1
  have h3 : ((c : K) - 1) • w = 0 := by rw [sub_smul, h2, one_smul, sub_self]
  have h4 := (smul_eq_zero.mp h3).resolve_right hw0
  exact Units.ext (sub_eq_zero.mp h4)

theorem Bq_mk_injective :
    Function.Injective (fun g : ↥(Bq h S) => ((g : SUn h n) : PSUn h n)) := by
  intro g₁ g₂ hg
  have hz : (g₁ : SUn h n)⁻¹ * g₂ ∈ ZSU h n := QuotientGroup.eq.mp hg
  obtain ⟨c, -, -, hzc⟩ := hz
  have hmem : ((g₁ : SUn h n)⁻¹ * g₂ : SUn h n) ∈ Bq h S := mul_mem (inv_mem g₁.2) g₂.2
  have hmem' : (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈ Dq h S.hodd S.hAp' := by
    rw [← hzc]
    exact hmem
  have hc1 := scalar_mem_Bq h S hmem'
  apply Subtype.ext
  have : (g₁ : SUn h n)⁻¹ * g₂ = 1 := by
    apply Subtype.ext
    rw [hzc, hc1, map_one]
    rfl
  exact inv_mul_eq_one.mp this

abbrev piSU (h : UnitaryFieldData 2 F K) (n : ℕ) : SUn h n →* PSUn h n :=
  QuotientGroup.mk' (ZSU h n)

theorem piSU_ker_le_center : (piSU h n).ker ≤ Subgroup.center (SUn h n) := by
  rw [piSU, QuotientGroup.ker_mk']
  exact normOneScalars_le_center h _ n

theorem Bq_perfect : Group.IsPerfect ↥(Bq h S) := (Bq_quasisimple h S).1

noncomputable abbrev Dsub : Subgroup (PSUn h n) := (Bq h S).map (piSU h n)

theorem isComponentOf_Dsub :
    IsComponentOf (Subgroup.centralizer ({piSU h n ⟨A, S.hA⟩} : Set (PSUn h n))) (Dsub h S) :=
  isComponentOf_map_block (piSU h n) (QuotientGroup.mk'_surjective (ZSU h n))
    (piSU_ker_le_center h)
    ⟨A, S.hA⟩ (Bq h S) (Bq_quasisimple h S) (Bq_le_centralizer h S) (Bq_norm h S)

theorem mem_center_of_pi_eq_one {g : SUn h n} (hg : piSU h n g = 1) :
    g ∈ Subgroup.center (SUn h n) := piSU_ker_le_center h (MonoidHom.mem_ker.mpr hg)

theorem hAp'' : (⟨A, S.hA⟩ : SUn h n) ^ p = 1 := Subtype.ext S.hAp

theorem toLin_comm_of_comm {g : SUn h n} (hgA : g * (⟨A, S.hA⟩ : SUn h n) = ⟨A, S.hA⟩ * g) :
    ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) * linOf A =
    linOf A * ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) := by
  have : (g : GL (Fin n) K) * A = A * g := congrArg Subtype.val hgA
  rw [coe_toLin_eq, ← linOf_mul, ← linOf_mul, this]

theorem commute_of_centralizes {g g' : SUn h n}
    (hg : (g : PSUn h n) ∈ Subgroup.centralizer ({piSU h n ⟨A, S.hA⟩} : Set (PSUn h n)))
    (hgD : (g : PSUn h n) ∈ Subgroup.centralizer ((Dsub h S : Subgroup (PSUn h n)) :
      Set (PSUn h n)))
    (hg' : (g' : PSUn h n) ∈ Subgroup.centralizer ({piSU h n ⟨A, S.hA⟩} : Set (PSUn h n))) :
    g * g' = g' * g := by
  have : CharP K 2 := h.charP
  have hgA := commute_of_mk_commute h S.hn1 S.hZp (hAp'' h S)
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hg'A := commute_of_mk_commute h S.hn1 S.hZp (hAp'' h S)
    (Subgroup.mem_centralizer_singleton_iff.mp hg')
  have hgB : ∀ q ∈ Bq h S, g * q = q * g := by
    refine commute_of_commutator_central (Bq_perfect h S) fun q hq => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hgD (piSU h n q) ⟨q, hq, rfl⟩
    refine mem_center_of_pi_eq_one h ?_
    rw [map_mul, map_mul, map_inv, map_inv]
    change (g : PSUn h n) * (q : PSUn h n) * (g : PSUn h n)⁻¹ * (q : PSUn h n)⁻¹ = 1
    have h2 : (g : PSUn h n) * (q : PSUn h n) = (q : PSUn h n) * (g : PSUn h n) := h1.symm
    rw [h2]
    group
  have hq2 : 2 ≤ 2 ^ F := by have := S.hq; omega
  have hDc : ∀ δ ∈ Dfix (idForm h n) (isCompl_ker_range S.hodd S.hAp'),
      Commute (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K)) δ := by
    intro δ hδ
    set f₀ : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm δ with hf₀
    have hf₀D : f₀ ∈ Dq h S.hodd S.hAp' := by
      change Matrix.GeneralLinearGroup.toLin f₀ ∈
        Dfix (idForm h n) (isCompl_ker_range S.hodd S.hAp')
      rw [hf₀, MulEquiv.apply_symm_apply]
      exact hδ
    have hf₀H : f₀ ∈ gramSU h (idGram K n) := Dq_le_gramSU h S.hodd S.hA S.hAp' hf₀D
    have h3 := hgB ⟨f₀, hf₀H⟩ hf₀D
    have h4 : (g : GL (Fin n) K) * f₀ = f₀ * g := congrArg Subtype.val h3
    have h5 : Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) * δ =
        δ * Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) := by
      rw [← MulEquiv.apply_symm_apply Matrix.GeneralLinearGroup.toLin δ, ← hf₀, ← map_mul,
        ← map_mul, h4]
    exact h5
  obtain ⟨c, hc⟩ := scalar_of_commute_Dfix (idForm_isSymm h n) (idForm_separatingLeft h n)
    (linOf_isom_A h S.hA) S.hodd S.hAp' S.hm hq2 (toLin_comm_of_comm h S hgA) hDc
  have key := commute_of_scalar S.hodd S.hAp' S.hcyc (toLin_comm_of_comm h S hgA)
    (toLin_comm_of_comm h S hg'A) ⟨c, hc⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.toLin.injective
  change Matrix.GeneralLinearGroup.toLin ((g : GL (Fin n) K) * (g' : GL (Fin n) K)) =
    Matrix.GeneralLinearGroup.toLin ((g' : GL (Fin n) K) * (g : GL (Fin n) K))
  rw [map_mul, map_mul]
  exact key

theorem centralizer_solvable :
    Group.IsSolvable ↥(Subgroup.centralizer ({piSU h n ⟨A, S.hA⟩} : Set (PSUn h n)) ⊓
      Subgroup.centralizer ((⨆ _ : Unit, Dsub h S : Subgroup (PSUn h n)) : Set (PSUn h n))) := by
  rw [iSup_const]
  refine Group.isSolvable_of_comm fun u v => Subtype.ext ?_
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp u.2
  obtain ⟨hv1, -⟩ := Subgroup.mem_inf.mp v.2
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (u : PSUn h n)
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (v : PSUn h n)
  have := commute_of_centralizes h S (g := g) (g' := g') (hg ▸ hu1) (hg ▸ hu2) (hg' ▸ hv1)
  change (u : PSUn h n) * v = v * u
  rw [← hg, ← hg', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]

theorem two_mem_Dsub {g' : PSUn h n}
    (hg' : g' ∈ Subgroup.centralizer ({piSU h n ⟨A, S.hA⟩} : Set (PSUn h n))) {k : ℕ}
    (hk : g' ^ (2 ^ k) = 1) : g' ∈ Dsub h S := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg2, rfl⟩ := exists_lift_two_pow h S.hn1 hk
  have hgA := commute_of_mk_commute h S.hn1 S.hZp (hAp'' h S)
    (Subgroup.mem_centralizer_singleton_iff.mp hg')
  have hmem : (g : GL (Fin n) K) ∈ Dq h S.hodd S.hAp' := by
    change Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) ∈
      Dfix (idForm h n) (isCompl_ker_range S.hodd S.hAp')
    refine two_mem_Dfix (idForm_isSymm h n) (idForm_separatingLeft h n) (linOf_isom_A h S.hA)
      S.hodd S.hAp' S.hcyc ((toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) _).mpr g.2)
      (toLin_comm_of_comm h S hgA) (k := k) ?_
    rw [coe_toLin_eq, ← linOf_pow, ← Subgroup.coe_pow, hg2]
    exact linOf_one
  exact ⟨g, hmem, rfl⟩

noncomputable def eDsub : ↥(Dsub h S) ≃* sesqSpecialUnitaryGroup
    ((idForm h n).domRestrict₁₂ (LinearMap.ker (linOf A - 1)) (LinearMap.ker (linOf A - 1))) :=
  (((MonoidHom.ofInjective (f := (piSU h n).comp (Bq h S).subtype)
    (Bq_mk_injective h S)).trans (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]))).symm).trans (eBq h S)

theorem sigma_sq_ne' {σ : K ≃+* K} (hσ : orderOf σ = p) (hp5 : 5 ≤ p) : ∃ x, σ (σ x) ≠ x := by
  by_contra hcon
  push Not at hcon
  have h1 : σ ^ 2 = 1 := by
    ext x
    rw [pow_two]
    exact hcon x
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hσ] at h2
  have h3 := Nat.le_of_dvd (by norm_num) h2
  omega

noncomputable abbrev fieldAut (h : UnitaryFieldData 2 F K) (σ : K ≃+* K) : MulAut (PSUn h n) :=
  primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ

theorem fieldAut_mk (b : SUn h n) :
    fieldAut h σ (piSU h n b) =
      piSU h n (primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ b) :=
  primeFormFieldAut_mk h _ σ b

theorem Dsub_outer : ∀ e ∈ Dsub h S, ¬ ∀ g ∈ Dsub h S, fieldAut h σ g = e * g * e⁻¹ := by
  rintro _ ⟨e₀, he₀, rfl⟩ hcon
  have hH : ∀ b ∈ Bq h S, primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ b =
      e₀ * b * e₀⁻¹ := by
    have := hom_eq_of_div_central (Bq_perfect h S)
      ((primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ).toMonoidHom.comp
        (Bq h S).subtype) ((MulAut.conj e₀).toMonoidHom.comp (Bq h S).subtype) (fun q => ?_)
    · intro b hb
      exact congrArg (fun f => f ⟨b, hb⟩) this
    · have h1 := hcon (piSU h n (q : SUn h n)) ⟨q, q.2, rfl⟩
      rw [fieldAut_mk] at h1
      refine mem_center_of_pi_eq_one h ?_
      change piSU h n (primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ
        (q : SUn h n) * (e₀ * (q : SUn h n) * e₀⁻¹)⁻¹) = 1
      rw [map_mul, map_inv, h1, map_mul, map_mul, map_inv]
      exact mul_inv_cancel _
  have hmem : (e₀ : GL (Fin n) K) ∈ Dq h S.hodd S.hAp' := he₀
  refine outer_Dq h S.hodd S.hA S.hAp' S.hm (sigma_sq_ne' S.hσ S.hp5) (e₀ : GL (Fin n) K) hmem
    (fun g hg => ?_)
  have hgH : g ∈ gramSU h (idGram K n) := Dq_le_gramSU h S.hodd S.hA S.hAp' hg
  have := hH ⟨g, hgH⟩ hg
  exact congrArg Subtype.val this

theorem Dsub_pair : ∃ t₁ ∈ Dsub h S, fieldAut h σ t₁ = t₁ ∧ ∃ t₂ ∈ Dsub h S,
    fieldAut h σ t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧
      t₁ * t₂ ≠ t₂ * t₁ := by
  have hp2 : p ≠ 2 := by have := S.hp5; omega
  have hfinK : Finite K := h.finite
  obtain ⟨a, b, haV, hbV, hσa, hσb, haa, hbb, hab⟩ :=
    exists_rational_unitary_pair h S.hp hp2 S.hσ S.hA S.hAp S.hσA S.hm
  obtain ⟨t₁, ht₁D, ht₁σ, ht₁2, ht₁1, t₂, ht₂D, ht₂σ, ht₂2, ht₂1, hnc⟩ :=
    pair_Dq h S.hodd S.hA S.hAp' haV hbV hσa hσb haa hbb hab
  let T₁ : SUn h n := ⟨t₁, Dq_le_gramSU h S.hodd S.hA S.hAp' ht₁D⟩
  let T₂ : SUn h n := ⟨t₂, Dq_le_gramSU h S.hodd S.hA S.hAp' ht₂D⟩
  have hT₁ : T₁ ∈ Bq h S := ht₁D
  have hT₂ : T₂ ∈ Bq h S := ht₂D
  have hinj := Bq_mk_injective h S
  have hord : ∀ (T : SUn h n) (hT : T ∈ Bq h S), (T : GL (Fin n) K) ^ 2 = 1 →
      (T : GL (Fin n) K) ≠ 1 → ∃ k : ℕ, orderOf (T : PSUn h n) = 2 ^ k := by
    intro T hT hT2 hT1
    refine ⟨1, ?_⟩
    rw [pow_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow]
      have : T ^ 2 = 1 := Subtype.ext hT2
      rw [this]
      rfl
    · intro h1
      have h2 : (⟨T, hT⟩ : ↥(Bq h S)) = 1 := hinj (by
        change (T : PSUn h n) = ((1 : SUn h n) : PSUn h n)
        rw [h1]
        rfl)
      exact hT1 (congrArg (fun z : ↥(Bq h S) => ((z : SUn h n) : GL (Fin n) K)) h2)
  have hfix : ∀ (T : SUn h n), glAut σ (T : GL (Fin n) K) = T →
      fieldAut h σ (T : PSUn h n) = (T : PSUn h n) := by
    intro T hT
    change fieldAut h σ (piSU h n T) = piSU h n T
    rw [fieldAut_mk]
    congr 1
    exact Subtype.ext hT
  refine ⟨piSU h n T₁, ⟨T₁, hT₁, rfl⟩, hfix T₁ ht₁σ, piSU h n T₂, ⟨T₂, hT₂, rfl⟩,
    hfix T₂ ht₂σ, hord T₁ hT₁ ht₁2 ht₁1, hord T₂ hT₂ ht₂2 ht₂1, ?_⟩
  intro hcomm
  have h1 : (T₁ * T₂ : SUn h n) ∈ Bq h S := mul_mem hT₁ hT₂
  have h2 : (T₂ * T₁ : SUn h n) ∈ Bq h S := mul_mem hT₂ hT₁
  have h3 : (⟨T₁ * T₂, h1⟩ : ↥(Bq h S)) = ⟨T₂ * T₁, h2⟩ := hinj (by
    change ((T₁ * T₂ : SUn h n) : PSUn h n) = ((T₂ * T₁ : SUn h n) : PSUn h n)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hcomm)
  exact hnc (congrArg (fun z : ↥(Bq h S) => ((z : SUn h n) : GL (Fin n) K)) h3)

theorem goodConclusion_of_setup {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hF : F = p * f₀) :
    GoodConclusion p (PSUn h n) (fieldAut h σ) (piSU h n ⟨A, S.hA⟩) := by
  have hfinP : Finite (PSUn h n) := finite_primeFormP
  have hcomp := isComponentOf_Dsub h S
  have hQ : ∀ _ : Unit, IsComponentOf
      (Subgroup.centralizer ({piSU h n ⟨A, S.hA⟩} : Set (PSUn h n))) (Dsub h S) := fun _ => hcomp
  have hsolv := centralizer_solvable h S
  have hlayer := inSubgroup_layer_eq_of_decomposition (fun _ : Unit => Dsub h S) hQ hsolv
  rw [iSup_const] at hlayer
  refine ⟨⟨_, hcomp⟩, fun E hE _ => ?_, fun g hg _ hg2 => ?_⟩
  · obtain ⟨_, rfl⟩ := isComponentOf_eq_of_decomposition (fun _ : Unit => Dsub h S) hQ hsolv hE
    refine ⟨Dsub_outer h S, ?_, Dsub_pair h S⟩
    have : CharP K 2 := h.charP
    obtain ⟨t', n', hmodel⟩ := lieModel_of_sesqSU h (fixSpace_isSymm (idForm_isSymm h n))
      (fixSpace_sep (idForm_separatingLeft h n) (linOf_isom_A h S.hA) S.hodd S.hAp') S.hm S.hq
      (eDsub h S)
    exact ⟨t', n', f₀, hf₀, @Eq.rec ℕ F (fun m _ => LieModel (↥(Dsub h S) ⧸
      Subgroup.center ↥(Dsub h S)) t' n' 2 m) hmodel (p * f₀) hF⟩
  · rw [hlayer]
    obtain ⟨k, hk⟩ := hg2
    exact two_mem_Dsub h S hg (k := k) (by rw [← hk]; exact pow_orderOf_eq_one g)

end Subgroups

section Top

variable {σ : K ≃+* K}

theorem psu_good_conclusion (hn : 3 ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hF : F = p * f₀) (hσ : orderOf σ = p)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    (hrank : CFSG.pRank p (PSUn h n) ≤ 1) {x y : PSUn h n} (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hσx : fieldAut h σ x = x) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) :
    GoodConclusion p (PSUn h n) (fieldAut h σ) x := by
  have hfinK : Finite K := h.finite
  have hn1 : 1 ≤ n := by omega
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨A', hA'p, hA'x⟩ := exists_lift_pow h hn1 hZp hxp
  have hσA : glAut σ (A' : GL (Fin n) K) = A' :=
    lift_sigma_fixed h hn1 hZp hA'p (by rw [hA'x]; exact hσx)
  have hA'1 : A' ≠ 1 := fun e => hx1 (by rw [← hA'x, e]; rfl)
  obtain ⟨Y₀, hY₀⟩ := QuotientGroup.mk_surjective y
  have hN : Odd (Nat.card (ZSU h n)) := odd_card_ZSU h hn1
  let Y : SUn h n := Y₀ ^ Nat.card (ZSU h n)
  have hYπ : (Y : PSUn h n) = y := by
    change ((Y₀ ^ Nat.card (ZSU h n) : SUn h n) : PSUn h n) = y
    rw [QuotientGroup.mk_pow, hY₀]
    obtain ⟨m, hm⟩ := hN
    rw [hm, pow_succ, pow_mul, hy2, one_pow, one_mul]
  have hY2 : Y ^ 2 = 1 := by
    have hz : Y₀ ^ 2 ∈ ZSU h n := (QuotientGroup.eq_one_iff _).mp (by
      rw [QuotientGroup.mk_pow, hY₀, hy2])
    have h1 : (⟨Y₀ ^ 2, hz⟩ : ↥(ZSU h n)) ^ Nat.card (ZSU h n) = 1 := pow_card_eq_one'
    calc Y ^ 2 = (Y₀ ^ 2) ^ Nat.card (ZSU h n) := by
          change (Y₀ ^ Nat.card (ZSU h n)) ^ 2 = _
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := congrArg Subtype.val h1
  have hYc : Y * A' = A' * Y :=
    commute_of_mk_commute h hn1 hZp hA'p (by rw [hYπ, hA'x]; exact hxy.symm)
  have hY1 : Y ≠ 1 := fun e => hy1 (by rw [← hYπ, e]; rfl)
  have hAU : (A' : GL (Fin n) K) ∈ gramSU h (idGram K n) := A'.2
  have hAp : (A' : GL (Fin n) K) ^ p = 1 := congrArg Subtype.val hA'p
  have hA1 : (A' : GL (Fin n) K) ≠ 1 := fun e => hA'1 (Subtype.ext e)
  have hrankH : CFSG.pRank p ↥(gramSU h (idGram K n)) ≤ 1 := by
    have := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp (ZSU h n)
      (not_dvd_card_ZSU h hn1 hp hZp)
    rw [← this]
    exact hrank
  have hpq := not_dvd_of_rank h hn hp hrankH
  have hcyc := cyclic_of_rank h hp hodd hpq hAU hAp hA1 hrankH
  have hm := two_le_finrank_fix h hodd hAp hcyc (congrArg Subtype.val hYc)
    (congrArg Subtype.val hY2) (fun e => hY1 (Subtype.ext e))
  have hq : 4 ≤ 2 ^ F := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ F := Nat.pow_le_pow_right (by norm_num) (by rw [hF]; nlinarith [hp.two_le])
  have S : PSUSetup h n p σ (A' : GL (Fin n) K) :=
    ⟨hn, hp, hp5, hσ, hq, hZp, hAU, hAp, hA1, hσA, hcyc, hm⟩
  have := goodConclusion_of_setup h S hf₀ hF
  have hx : piSU h n ⟨(A' : GL (Fin n) K), S.hA⟩ = x := by
    rw [Subtype.coe_eta]
    exact hA'x
  rwa [hx] at this

end Top

end CFSG.RankThree.PartOne
