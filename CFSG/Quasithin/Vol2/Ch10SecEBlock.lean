module

public import CFSG.Quasithin.Vol2.Ch10SecA1012SixE23
public import CFSG.Quasithin.Vol2.Ch10SecEL0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem isSolvable_of_isAltType_three [Finite G] {K : Subgroup G} (h : IsAltType K 3) :
    Group.IsSolvable ↥K := by
  obtain ⟨α, -, hker, -⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  have : Group.IsSolvable ↥(alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥K).subtype α
    (by rw [hker, Subgroup.range_subtype])

theorem commutator_sup_le {K A B N : Subgroup G} (hA : ⁅K, A⁆ ≤ N) (hB : ⁅K, B⁆ ≤ N)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G)) :
    ⁅K, A ⊔ B⁆ ≤ N := by
  let C : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (N : Set G) ∧ ∀ k ∈ K, ⁅k, x⁆ ∈ N}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, fun k hk => by
        have e : ⁅k, x * y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hx.2 k hk)
          ((Subgroup.mem_normalizer_iff.mp hx.1 _).mp (hy.2 k hk))⟩
      one_mem' := ⟨Subgroup.one_mem _, fun k _ => by
        rw [commutatorElement_def]; simp⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, fun k hk => by
        have e : ⁅k, x⁻¹⁆ = x⁻¹ * ⁅k, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx.1) _).mp
          (N.inv_mem (hx.2 k hk))⟩ }
  have hAC : A ≤ C := fun a ha =>
    ⟨hAN ha, fun k hk => hA (Subgroup.commutator_mem_commutator hk ha)⟩
  have hBC : B ≤ C := fun b hb =>
    ⟨hBN hb, fun k hk => hB (Subgroup.commutator_mem_commutator hk hb)⟩
  rw [Subgroup.commutator_le]
  intro k hk x hx
  exact (sup_le hAC hBC hx).2 k hk

variable [Finite G] {T L I : Subgroup G}

theorem mem_cComp_L0T (hyp : Hyp10 G T L I) : L ∈ cComp (fsuL0 T L ⊔ T) :=
  cComp_mem_of_le (SecA.mem_cComp_fsuM hyp.fsu.maximal.1)
    ((SecA.le_fsuL0 T L).trans le_sup_left) (sup_le (SecA.fsuL0_le_fsuM T L) (SecA.le_fsuM T L))

theorem false_of_isSolvable_subnormal (hyp : Hyp10 G T L I) {K : Subgroup G}
    (hKX : K ≤ fsuL0 T L ⊔ T) (hsub : (K.subgroupOf (fsuL0 T L ⊔ T)).IsSubnormal)
    (hsol : Group.IsSolvable ↥K) (heq : fsuL0 T L ⊔ T = K ⊔ T) : False := by
  set X := fsuL0 T L ⊔ T with hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsol' : Group.IsSolvable ↥(K.subgroupOf X) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hKX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKX).symm.surjective
  set R := CFSG.solvableRadical ↥X with hR
  have hKR : K.subgroupOf X ≤ R := by
    rw [hR, A3.solvableRadical_eq_solvRad_top]
    exact le_solvRad_of_subnormal (A3.subnormal_top_iff.mpr hsub) hsol'
  have hTX : T ≤ X := le_sup_right
  have htop : R ⊔ T.subgroupOf X = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup ↥X) = (K ⊔ T).subgroupOf X := by rw [← heq, Subgroup.subgroupOf_self]
      _ = K.subgroupOf X ⊔ T.subgroupOf X := Subgroup.subgroupOf_sup hKX hTX
      _ ≤ R ⊔ T.subgroupOf X := sup_le_sup_right hKR _
  have hT2 : IsPGroup 2 ↥(T.subgroupOf X) :=
    hyp.fsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' R).comp (T.subgroupOf X).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    have hx : x ∈ ((R ⊔ T.subgroupOf X : Subgroup ↥X) : Set ↥X) := by rw [htop]; trivial
    rw [Subgroup.normal_mul] at hx
    obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hx
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h1 := (A3.instNormalSolvableRadical ↥X).conj_mem r hr s⁻¹
    simpa [mul_assoc] using h1
  have hQ : IsPGroup 2 (↥X ⧸ R) := hT2.of_surjective _ hsurj
  have : Group.IsNilpotent (↥X ⧸ R) := hQ.isNilpotent
  have : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
  have hXs : Group.IsSolvable ↥X :=
    Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hLX : L ≤ X := (SecA.le_fsuL0 T L).trans le_sup_left
  have hLs : Group.IsSolvable ↥L :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLX).surjective
  exact not_isSolvable_of_mem_cComp (mem_cComp_L0T hyp) hLs

theorem eq_or_eq_of_mem_cComp_L0T (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {K : Subgroup G}
    (hK : K ∈ cComp (fsuL0 T L ⊔ T)) : K = L ∨ K = CFSG.conjugate L t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := hyp.fsu.simple
  set X := fsuL0 T L ⊔ T with hX
  have hloc := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hXne := SecA.pCoreOf_L0T_ne_bot hyp
  have hLX := mem_cComp_L0T hyp
  have hLtX : CFSG.conjugate L t ∈ cComp X := by
    exact map_conj_mem_cComp hLX (X.inv_mem ((le_sup_right : T ≤ X) ht))
  by_contra hne
  push Not at hne
  obtain ⟨hne₁, hne₂⟩ := hne
  have hc₁ := Vol2Native.lemma_1_2_1_two hloc h37 hXne hK hLX hne₁
  have hc₂ := Vol2Native.lemma_1_2_1_two hloc h37 hXne hK hLtX hne₂
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hKL0 : K ≤ fsuL0 T L := by
    have h1 := oTwoUpper_mono (le_of_mem_cComp hK)
    rw [← eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hK),
      oTwoUpper_fsuL0_sup h37 h38 hyp] at h1
    exact h1
  have hcomm : ⁅K, fsuL0 T L⁆ ≤ pCoreOf 2 X := by
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact commutator_sup_le (hc₁.1.trans hc₁.2) (hc₂.1.trans hc₂.2)
      (((SecA.le_fsuL0 T L).trans le_sup_left).trans hXN)
      (((SecA.conjugate_le_fsuL0 ht).trans le_sup_left).trans hXN)
  have hKO : K ≤ pCoreOf 2 X := by
    calc K = ⁅K, K⁆ := (perfect_of_mem_cComp hK).symm
      _ ≤ ⁅K, fsuL0 T L⁆ := Subgroup.commutator_mono le_rfl hKL0
      _ ≤ pCoreOf 2 X := hcomm
  have hK2 : IsPGroup 2 ↥K :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hKO
  have : Group.IsNilpotent ↥K := hK2.isNilpotent
  exact not_isSolvable_of_mem_cComp hK inferInstance

end CFSG.Quasithin.Vol2.Ch10.SecE
