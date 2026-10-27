module

public import CFSG.Quasithin.Recognition.St84.Sec5Hyp
public import CFSG.RankThree.GF2n.NaturalDecomp
public import CFSG.RankThree.GF2n.QuadraticSection
public import CFSG.Quasithin.Vol2.Ch3Sec1L319GoodFix
public import CFSG.GroupTheory.SL2SylowTwo
public import CFSG.GroupTheory.SupIndepFixedPointFree

public section

namespace CFSG.Quasithin.St84

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped MatrixGroups commutatorElement

private theorem commutator_commutator_mem_of_quad {G : Type} [Group G]
    {L V Z P : Subgroup G} (hsec : IsElemSec Z V) (hPL : P ≤ L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hquad : ∀ v ∈ V, ∀ a ∈ P, ∀ b ∈ P, ⁅⁅v, a⁆, b⁆ ∈ Z) :
    ∀ a ∈ P, ∀ b ∈ P, ∀ x ∈ V, ⁅b, ⁅a, x⁆⁆ ∈ Z := by
  have hVNZ : V ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono le_rfl hsec.1).trans hsec.2.1)
  intro a ha b hb x hx
  have haL : a ∈ L := hPL ha
  have hx2 : a * x⁻¹ * a⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hLV haL) x⁻¹).mp (V.inv_mem hx)
  have hyV : ⁅x, a⁆ ∈ V := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using V.mul_mem hx hx2
  have h1 : ⁅⁅x, a⁆, b⁆ ∈ Z := hquad x hx a ha b hb
  have hconj : ⁅x, a⁆⁻¹ * ⁅⁅x, a⁆, b⁆ * ⁅x, a⁆ ∈ Z := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (hVNZ (V.inv_mem hyV)) _).mp h1
  rwa [show ⁅b, ⁅a, x⁆⁆ = ⁅x, a⁆⁻¹ * ⁅⁅x, a⁆, b⁆ * ⁅x, a⁆ from by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group]

private theorem smul_eq_self_of_mem_closure_centralizer {G : Type*} [Group G]
    {K : Type*} [Field K] {L V Z P : Subgroup G}
    {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L V Z φ)
    (hAX : ∀ a ∈ L, ∀ x ∈ V, a * x * a⁻¹ ∈ V)
    (hPU : (P.subgroupOf L).map φ = CFSG.Timmesfeld.upperUnipotent K) :
    ∀ w ∈ AddSubgroup.closure {w | ∃ x : ↥V, (x : G) ∈ Subgroup.centralizer (P : Set G) ∧
      S.π x = w},
      ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K, a • w = w := by
  intro w hw a ha
  have ha_map : a ∈ (P.subgroupOf L).map φ := hPU ▸ ha
  obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp ha_map
  have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
  let fixA : AddSubgroup S.W :=
    { carrier := {w | a • w = w}
      zero_mem' := by show a • (0 : S.W) = 0; rw [smul_zero]
      add_mem' := fun {u v} hu hv => by
        show a • (u + v) = u + v
        rw [smul_add, hu, hv]
      neg_mem' := fun {u} hu => by
        show a • (-u) = -u
        rw [smul_neg, hu] }
  have hT : {w | ∃ x : ↥V, (x : G) ∈ Subgroup.centralizer (P : Set G) ∧
      S.π x = w} ⊆ fixA := by
    rintro w ⟨x, hxC, rfl⟩
    show a • S.π x = S.π x
    rw [← hpa]
    exact (S.smul_eq_iff_commutator_mem hAX p x).mpr (by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hxC (p : G) hpP)]
      exact Z.one_mem)
  have hle : AddSubgroup.closure {w | ∃ x : ↥V,
      (x : G) ∈ Subgroup.centralizer (P : Set G) ∧ S.π x = w} ≤ fixA :=
    (AddSubgroup.closure_le (K := fixA)).mpr hT
  exact hle hw

private theorem eq_top_of_closure_centralizer_le {G : Type*} [Group G]
    {K : Type*} [Field K] {L V Z P : Subgroup G}
    {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K}
    (S : CFSG.RankThree.GF2n.SectionModule L V Z φ) (hZV : Z ≤ V)
    (hAX : ∀ a ∈ L, ∀ x ∈ V, a * x * a⁻¹ ∈ V)
    (hgen : V = (⨆ l ∈ L, (V ⊓ Subgroup.centralizer (P : Set G)).map
      (MulAut.conj l).toMonoidHom) ⊔ Z)
    (U : AddSubgroup S.W)
    (hU : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U)
    (hLU : AddSubgroup.closure {w | ∃ x : ↥V, (x : G) ∈ Subgroup.centralizer (P : Set G) ∧
      S.π x = w} ≤ U) : U = ⊤ := by
  let Y : Subgroup G :=
    { carrier := {y | ∃ x : ↥V, (x : G) = y ∧ S.π x ∈ U}
      one_mem' := ⟨1, rfl, by rw [S.map_one]; exact U.zero_mem⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨x₁, rfl, hx₁⟩ ⟨x₂, rfl, hx₂⟩
        exact ⟨x₁ * x₂, rfl, by rw [S.map_mul]; exact U.add_mem hx₁ hx₂⟩
      inv_mem' := by
        rintro y ⟨x, rfl, hx⟩
        exact ⟨x⁻¹, rfl, by rw [S.map_inv]; exact U.neg_mem hx⟩ }
  have hZY : Z ≤ Y := by
    intro z hz
    exact ⟨⟨z, hZV hz⟩, rfl, (S.eq_zero_iff ⟨z, hZV hz⟩).mpr hz ▸ U.zero_mem⟩
  have hconj : ∀ l ∈ L, (V ⊓ Subgroup.centralizer (P : Set G)).map
      (MulAut.conj l).toMonoidHom ≤ Y := by
    intro l hl
    rw [Subgroup.map_le_iff_le_comap]
    rintro y hy
    have hyV : y ∈ V := (Subgroup.mem_inf.mp hy).1
    have hyC : y ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hy).2
    have hconjV : (MulAut.conj l).toMonoidHom y ∈ V := by
      change (MulAut.conj l) y ∈ V
      rw [MulAut.conj_apply]
      exact hAX l hl y hyV
    have hgenT : S.π ⟨y, hyV⟩ ∈ AddSubgroup.closure {w | ∃ x : ↥V,
        (x : G) ∈ Subgroup.centralizer (P : Set G) ∧ S.π x = w} :=
      AddSubgroup.subset_closure ⟨⟨y, hyV⟩, hyC, rfl⟩
    have hsm : φ ⟨l, hl⟩ • S.π ⟨y, hyV⟩ =
        S.π ⟨(MulAut.conj l).toMonoidHom y, hconjV⟩ :=
      S.smul_eq ⟨l, hl⟩ ⟨y, hyV⟩ ⟨_, hconjV⟩ rfl
    refine ⟨⟨(MulAut.conj l).toMonoidHom y, hconjV⟩, rfl, ?_⟩
    rw [← hsm]
    exact hU (φ ⟨l, hl⟩) _ (hLU hgenT)
  have hVY : V ≤ Y := by
    rw [hgen]
    exact sup_le (iSup₂_le hconj) hZY
  rw [eq_top_iff]
  intro w _
  obtain ⟨x, rfl⟩ := S.surjective w
  obtain ⟨v, hv, hvU⟩ := hVY x.2
  have hveq : v = x := Subtype.ext hv
  rw [hveq] at hvU
  exact hvU

private theorem eq_zero_of_fixed_on_natural {K : Type} [Field K] [CharP K 2] {W : Type*}
    [AddCommGroup W] [DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) K) W]
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (hg : g ≠ 1) (hodd : Odd (orderOf g))
    (θ : (Fin 2 → K) →+ W) (hθinj : Function.Injective θ)
    (hθ : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v)
    {v : W} (hv : v ∈ θ.range) (hfix : g • v = v) : v = 0 := by
  obtain ⟨u, hu⟩ := hv
  rw [← hu] at hfix ⊢
  have hmat : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u := by
    apply hθinj
    rw [hθ, hfix]
  have hu0 : u = 0 := by
    by_contra hu0
    exact hg (CFSG.Quasithin.H13.L319.sl2_eq_one_of_odd_fixed g hodd hu0 hmat)
  rw [hu0, map_zero]

theorem higmanQuad (n₀ : ℕ) : HigmanQuad n₀ := by
  unfold HigmanQuad
  intro G _ _ L V Z P hL2 hP hsec hVL hLV hLZ hcent hfixL hquad hgen k hkL hkodd hk1
  intro e heV heZ
  let K := GaloisField 2 n₀
  obtain ⟨φ', hφ's, hφ'ker, hU'eq⟩ :=
    CFSG.GroupTheory.exists_SL2_hom_map_sylowTwo_eq_upperUnipotent hL2 hP
  have hXX : ∀ x ∈ V, ∀ y ∈ V, ⁅x, y⁆ ∈ Z :=
    fun x hx y hy => (Subgroup.commutator_le.mp hsec.2.1) x hx y hy
  have hAX : ∀ a ∈ L, ∀ x ∈ V, a * x * a⁻¹ ∈ V :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hLV ha) x).mp hx
  have hAC : ∀ a ∈ L, ∀ x ∈ Z, a * x * a⁻¹ ∈ Z :=
    fun a ha x hx => (Subgroup.mem_normalizer_iff.mp (hLZ ha) x).mp hx
  have hker' : ∀ a : ↥L, φ' a = 1 → ∀ x ∈ V, ⁅(a : G), x⁆ ∈ Z := by
    intro a ha x hx
    have hmem : a ∈ φ'.ker := ha
    rw [hφ'ker] at hmem
    exact hcent (a : G) (Subgroup.mem_subgroupOf.mp hmem) x hx
  obtain ⟨S'⟩ := CFSG.RankThree.GF2n.exists_sectionModule φ' hφ's hsec.1 hXX hAX hAC hker'
  haveI : Finite S'.W := Finite.of_surjective S'.π S'.surjective
  have hfix : ∀ v : S'.W, (∀ x : Matrix.SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 := by
    intro v hv
    obtain ⟨x, rfl⟩ := S'.surjective v
    have hcomm : ∀ l : ↥L, ⁅(x : G), (l : G)⁆ ∈ Z := fun l => by
      simpa only [commutatorElement_inv] using
        Z.inv_mem ((S'.smul_eq_iff_commutator_mem hAX l x).mp (hv (φ' l)))
    have hxZ : (x : G) ∈ Z := hfixL x x.2 (fun l hl => hcomm ⟨l, hl⟩)
    rw [← (S'.eq_zero_iff x).mpr hxZ]
  let T : Set S'.W := {w | ∃ x : ↥V, (x : G) ∈ Subgroup.centralizer (P : Set G) ∧ S'.π x = w}
  let Lsub : AddSubgroup S'.W := AddSubgroup.closure T
  have hquadA : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K,
      ∀ a' ∈ CFSG.Timmesfeld.upperUnipotent K, ∀ v : S'.W,
        a' • (a • v - v) = a • v - v := by
    have h := S'.quadratic (A := L) (C := Z) (X := V) (Q := P) hAX hP.1
      (commutator_commutator_mem_of_quad hsec hP.1 hLV hquad)
    rwa [hU'eq] at h
  have hLsub : ∀ w ∈ Lsub, ∀ a ∈ CFSG.Timmesfeld.upperUnipotent K, a • w = w :=
    smul_eq_self_of_mem_closure_centralizer S' hAX hU'eq
  have hgenW : ∀ U : AddSubgroup S'.W,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) →
      Lsub ≤ U → U = ⊤ :=
    eq_top_of_closure_centralizer_le S' hsec.1 hAX hgen
  obtain ⟨s, hs_ind, hs_top, hs⟩ :=
    CFSG.RankThree.GF2n.exists_supIndep_natural (K := K) (V := S'.W) hfix hquadA hLsub hgenW
  set k' : ↥L := ⟨k, hkL⟩ with hk'def
  have hxne : φ' k' ≠ 1 := by
    intro h1
    have hmem : k' ∈ φ'.ker := h1
    rw [hφ'ker] at hmem
    have hkO : k ∈ pCoreOf 2 L := Subgroup.mem_subgroupOf.mp hmem
    have h1 : (⟨k, hkO⟩ : ↥(pCoreOf 2 L)) = 1 :=
      CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hkodd
        (Subtype.ext (by simp [pow_orderOf_eq_one]))
    exact hk1 (congrArg Subtype.val h1)
  have hxodd : Odd (orderOf (φ' k')) := by
    have hk'ord : orderOf k' = orderOf k := by
      rw [hk'def]
      exact Subgroup.orderOf_mk k hkL
    exact Odd.of_dvd_nat (hk'ord ▸ hkodd) (orderOf_map_dvd φ' k')
  have hfixe : φ' k' • S'.π ⟨e, heV⟩ = S'.π ⟨e, heV⟩ :=
    (S'.smul_eq_iff_commutator_mem hAX k' ⟨e, heV⟩).mpr (by
      show ⁅k, e⁆ ∈ Z
      rw [← commutatorElement_inv]
      exact Z.inv_mem heZ)
  let gK : S'.W →+ S'.W :=
    (DistribMulAction.toAddMonoidEnd (Matrix.SpecialLinearGroup (Fin 2) K) S'.W) (φ' k')
  have hgK : ∀ w, gK w = φ' k' • w := fun w => rfl
  have hinv : ∀ W ∈ s, ∀ v ∈ W, gK v ∈ W := by
    intro W hW v hv
    rw [hgK]
    exact (hs W hW).1 (φ' k') v hv
  have hfixW : ∀ W ∈ s, ∀ v ∈ W, gK v = v → v = 0 := by
    intro W hW v hv hgv
    obtain ⟨-, -, -, θ, hθinj, hθrange, hθ⟩ := hs W hW
    exact eq_zero_of_fixed_on_natural (φ' k') hxne hxodd θ hθinj hθ (hθrange ▸ hv)
      (by rwa [hgK] at hgv)
  have hπe : S'.π ⟨e, heV⟩ = 0 :=
    CFSG.GroupTheory.eq_zero_of_mem_finset_sup_of_fixedPointFree gK hs_ind hinv hfixW
      (w := S'.π ⟨e, heV⟩) (by rw [hs_top]; exact AddSubgroup.mem_top _) hfixe
  exact (S'.eq_zero_iff ⟨e, heV⟩).mp hπe

end CFSG.Quasithin.St84
