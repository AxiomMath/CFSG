module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylStruct
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylPlace
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylAltConj
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylOuter
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylArith
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylConjStep
import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylFixTorus
import CFSG.LocalAnalysis.StandardType.GGTriD4LineRecog
import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputsModel
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma triD4Line_conj_conj {G : Type*} [Group G] (g x : G) :
    MulAut.conj (MulAut.conj g) (MulAut.conj x) = MulAut.conj (g * x * g⁻¹) := by
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]

private lemma triD4Line_conj_mul {G : Type*} [Group G] (m e : G) :
    MulAut.conj (m * e * m⁻¹) = MulAut.conj m * MulAut.conj e * (MulAut.conj m)⁻¹ := by
  simp only [map_mul, map_inv]

private lemma triD4Line_ggFix_le_of_mem_zpowers {G : Type*} [Group G] {a b : MulAut G}
    (h : b ∈ Subgroup.zpowers a) : ggFix a ≤ ggFix b := by
  intro x hx
  have hx' : a x = x := hx
  let S : Subgroup (MulAut G) :=
    { carrier := {f | f x = x}
      one_mem' := by simp
      mul_mem' := by
        intro f g hf hg
        show (f * g) x = x
        rw [MulAut.mul_apply, hg, hf]
      inv_mem' := by
        intro f hf
        show f⁻¹ x = x
        apply f.injective
        rw [MulAut.inv_apply, MulEquiv.apply_symm_apply, hf] }
  have haS : a ∈ S := hx'
  exact Subgroup.zpowers_le.mpr haS h

private lemma triD4Line_ggFix_eq_of_zpowers_eq {G : Type*} [Group G] {a b : MulAut G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) : ggFix a = ggFix b := by
  apply le_antisymm
  · exact triD4Line_ggFix_le_of_mem_zpowers (by rw [h]; exact Subgroup.mem_zpowers b)
  · exact triD4Line_ggFix_le_of_mem_zpowers (by rw [← h]; exact Subgroup.mem_zpowers a)

private lemma triD4Line_zpowers_eq_of_mem_zpowers_of_prime {G : Type*} [Group G] {y z : G}
    {p : ℕ} (hp : p.Prime) (hpow : y ^ p = 1) (hz : z ≠ 1)
    (hzy : z ∈ Subgroup.zpowers y) : Subgroup.zpowers z = Subgroup.zpowers y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot] at hzy
    exact hz (Subgroup.mem_bot.mp hzy)
  have hyfin : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hpow⟩
  haveI := hyfin.finite_zpowers
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hzy
  have hzp : z ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzy
    rw [← hk, ← zpow_natCast (y ^ k) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow,
      one_zpow]
  have hcardz : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzp hz]
  have hcardy : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hpow hy1]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardy, hcardz])

private lemma triD4Line_ggFix_conj_eq_of_zpowers_eq {G : Type*} [Group G] {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    ggFix (MulAut.conj x) = ggFix (MulAut.conj y) := by
  have hc : Subgroup.zpowers (MulAut.conj x) = Subgroup.zpowers (MulAut.conj y) := by
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, h]
  exact triD4Line_ggFix_eq_of_zpowers_eq hc

private lemma triD4LineAlt_of_conj_step
    {n : ℕ} (hn : 2 ≤ n) (hev : Even n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (k : Type) [Field k] [Algebra k K]
    (hk : Nat.card k = 2 ^ n) (D : TriD4LineKGXData n K k)
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A)
    (hz : MulAut.conj D.z₀ ∈ A) (e : GGTriD4R n K) (he : MulAut.conj e ∈ A)
    (hline : e ∉ Subgroup.zpowers D.z₀) :
    triD4LineAlt n K A (MulAut.conj e) := by
  obtain ⟨m, hclause, hmove⟩ := triD4Line_conj_step hn hev K hK k hk D A hA h27 hz e he hline
  left
  refine ⟨m, hclause, ?_⟩
  intro hmem
  apply hmove
  have hmem' : MulAut.conj (m * e * m⁻¹) ∈ Subgroup.zpowers (MulAut.conj e) := by
    rwa [triD4Line_conj_mul]
  exact (triD4Line_conj_mem_zpowers_iff K hZ (m * e * m⁻¹) e).mp hmem'

theorem ggTriD4LineWeylStrong_holds
    {n : ℕ} (K : Type) [Field K] (hn : 2 ≤ n) (hev : Even n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (hs : IsSimpleGroup (GGTriD4R n K)) : GGTriD4LineWeylStrong n K := by
  rw [ggTriD4LineWeylStrong_iff]
  intro A hA h27 a₀ ha₀ ha₀ne ha₀I
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn1 : 1 ≤ n := by omega
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn1 K hK
  have hID : GGTriD4ID n K = Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) :=
    ggTriD4InnDiagInput_holds n hn1 K hK hs
  have ha₀range : a₀ ∈ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) := by
    rw [← hID]; exact ha₀I
  obtain ⟨e₀, rfl⟩ := ha₀range
  have he₀ne : e₀ ≠ 1 := by
    intro h1; exact ha₀ne (by rw [h1, map_one])
  obtain ⟨k, hk_field, hk_alg, hk⟩ := triD4Line_exists_subfield K hK
  letI : Field k := hk_field
  letI : Algebra k K := hk_alg
  obtain ⟨D⟩ := triD4Line_kgXData K hev hK k hk
  have hEAelab : IsElemAbelian 3 (triD4LineE n K A) := triD4Line_E_isElemAbelian K hZ A hA
  have hEApg : IsPGroup 3 (triD4LineE n K A) := CFSG.Open.IsElemAbelian.isPGroup hEAelab
  obtain ⟨g, hg⟩ := triD4Line_placement K hK k D (triD4LineE n K A) hEApg
  apply triD4LineAlt_of_conj K (MulAut.conj g) A (MulAut.conj e₀)
  set A' : Subgroup (MulAut (GGTriD4R n K)) :=
    A.map (MulAut.conj (MulAut.conj g)).toMonoidHom with hA'def
  set e₀' : GGTriD4R n K := g * e₀ * g⁻¹ with he₀'def
  have heq : (MulAut.conj (MulAut.conj g)) (MulAut.conj e₀) = MulAut.conj e₀' := by
    rw [he₀'def]; exact triD4Line_conj_conj g e₀
  rw [heq]
  have hA' : IsElemAbelian 3 A' := by
    rw [hA'def]
    exact CFSG.Open.IsElemAbelian.map hA _
  have h27' : 27 ≤ Nat.card A' := by
    rw [hA'def, Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj g)).injective]
    exact h27
  have hEAcard : Nat.card (triD4LineE n K A) = 9 :=
    (triD4Line_A_structure hn1 hev K hK A hA h27).1
  have hEA' : triD4LineE n K A' = (triD4LineE n K A).map (MulAut.conj g).toMonoidHom := by
    rw [hA'def]; exact triD4Line_E_map_conj K g A
  have hEA'card : Nat.card (triD4LineE n K A') = 9 := by
    rw [hEA', Subgroup.card_map_of_injective (MulAut.conj g).injective, hEAcard]
  have hEA'elab : IsElemAbelian 3 (triD4LineE n K A') := triD4Line_E_isElemAbelian K hZ A' hA'
  have hEA'le : triD4LineE n K A' ≤ Subgroup.centralizer {D.z₀} := by
    rw [hEA']
    rintro x ⟨e, he, rfl⟩
    exact hg e he
  have hz₀E' : D.z₀ ∈ triD4LineE n K A' :=
    triD4Line_mem_of_order_nine hn1 hev K hK k D (triD4LineE n K A') hEA'elab hEA'card hEA'le
  have hz' : MulAut.conj D.z₀ ∈ A' := mem_triD4LineE.mp hz₀E'
  have he₀EA : e₀ ∈ triD4LineE n K A := mem_triD4LineE.mpr ha₀
  have he₀'A' : MulAut.conj e₀' ∈ A' := by
    rw [← mem_triD4LineE, hEA', he₀'def]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom he₀EA
  by_cases hline' : e₀' ∈ Subgroup.zpowers D.z₀
  · have hz₀pow : D.z₀ ^ 3 = 1 := by
      rw [← D.orderOf_z₀]; exact pow_orderOf_eq_one D.z₀
    have he₀'ne : e₀' ≠ 1 := by
      rw [he₀'def, ← MulAut.conj_apply]
      intro h
      exact he₀ne ((MulAut.conj g).injective (by rw [h, map_one]))
    have hzp_eq : Subgroup.zpowers e₀' = Subgroup.zpowers D.z₀ :=
      triD4Line_zpowers_eq_of_mem_zpowers_of_prime Nat.prime_three hz₀pow he₀'ne hline'
    have hggFix : ggFix (MulAut.conj e₀') = ggFix (MulAut.conj D.z₀) :=
      triD4Line_ggFix_conj_eq_of_zpowers_eq hzp_eq
    rcases triD4Line_fix_or_torus_R hn hev K hK k hk D A' hA' h27' hz' with
      ⟨f, hfA', hfouter, hffix⟩ | ⟨e₁, he₁A', he₁not, T, hT, hTiso⟩
    · right
      refine ⟨f, hfA', ?_, ?_⟩
      · intro hfz
        have hle : Subgroup.zpowers (MulAut.conj e₀') ≤
            (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)).range :=
          Subgroup.zpowers_le.mpr (Set.mem_range_self e₀')
        exact hfouter (hle hfz)
      · intro J₁ hJ l hl
        exact hffix J₁ (by rw [← hggFix]; exact hJ) l hl
    · have he₁E' : e₁ ∈ triD4LineE n K A' := mem_triD4LineE.mpr he₁A'
      have he₁pow : e₁ ^ 3 = 1 := hEA'elab.2 e₁ he₁E'
      have he₁ne : e₁ ≠ 1 := by
        intro h1; exact he₁not (by rw [h1]; exact Subgroup.one_mem _)
      have he₁order : orderOf e₁ = 3 := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact orderOf_eq_prime he₁pow he₁ne
      obtain ⟨g₂, hg₂⟩ := triD4Line_conj_z0_of_torus K hn hK D.z₀ e₁ D.orderOf_z₀ he₁order
        (triD4Line_not_dvd_commutator hn K hK k hk D) T hT hTiso
      set A'' : Subgroup (MulAut (GGTriD4R n K)) :=
        A'.map (MulAut.conj (MulAut.conj g₂)).toMonoidHom with hA''def
      set e₀'' : GGTriD4R n K := g₂ * e₀' * g₂⁻¹ with he₀''def
      have hA'' : IsElemAbelian 3 A'' := by
        rw [hA''def]; exact CFSG.Open.IsElemAbelian.map hA' _
      have h27'' : 27 ≤ Nat.card A'' := by
        rw [hA''def, Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj g₂)).injective]
        exact h27'
      have hzE'' : D.z₀ ∈ triD4LineE n K A'' := by
        rw [hA''def, triD4Line_E_map_conj K g₂ A', ← hg₂]
        exact Subgroup.mem_map_of_mem (MulAut.conj g₂).toMonoidHom he₁E'
      have hz'' : MulAut.conj D.z₀ ∈ A'' := mem_triD4LineE.mp hzE''
      have he₀''A'' : MulAut.conj e₀'' ∈ A'' := by
        rw [← mem_triD4LineE, hA''def, triD4Line_E_map_conj K g₂ A', he₀''def]
        exact Subgroup.mem_map_of_mem (MulAut.conj g₂).toMonoidHom (mem_triD4LineE.mpr he₀'A')
      have hline'' : e₀'' ∉ Subgroup.zpowers D.z₀ := by
        intro h
        have he₀'ine1 : e₀' ∈ Subgroup.zpowers e₁ := by
          have hmap : e₀'' ∈ (Subgroup.zpowers e₁).map (MulAut.conj g₂).toMonoidHom := by
            rw [MonoidHom.map_zpowers,
              show (MulAut.conj g₂).toMonoidHom e₁ = D.z₀ from hg₂]
            exact h
          obtain ⟨x, hx, hxx⟩ := Subgroup.mem_map.mp hmap
          have hxeq : x = e₀' := by
            apply (MulAut.conj g₂).injective
            change (MulAut.conj g₂).toMonoidHom x = (MulAut.conj g₂).toMonoidHom e₀'
            rw [hxx, he₀''def]
            rfl
          rwa [← hxeq]
        have hz0ine1 : D.z₀ ∈ Subgroup.zpowers e₁ := by
          have h1 : D.z₀ ∈ Subgroup.zpowers e₀' := by
            rw [hzp_eq]; exact Subgroup.mem_zpowers D.z₀
          exact Subgroup.zpowers_le.mpr he₀'ine1 h1
        have hz₀ne : D.z₀ ≠ 1 := by
          intro h1
          have h2 : orderOf D.z₀ = 1 := by rw [h1, orderOf_one]
          rw [D.orderOf_z₀] at h2
          norm_num at h2
        have hzeq : Subgroup.zpowers D.z₀ = Subgroup.zpowers e₁ :=
          triD4Line_zpowers_eq_of_mem_zpowers_of_prime Nat.prime_three he₁pow hz₀ne hz0ine1
        exact he₁not (by rw [hzeq]; exact Subgroup.mem_zpowers e₁)
      have halt'' := triD4LineAlt_of_conj_step hn hev K hK k hk D hZ A'' hA'' h27'' hz'' e₀''
        he₀''A'' hline''
      have hgoal : triD4LineAlt n K A''
          ((MulAut.conj (MulAut.conj g₂)) (MulAut.conj e₀')) := by
        rw [triD4Line_conj_conj, ← he₀''def]; exact halt''
      exact triD4LineAlt_of_conj K (MulAut.conj g₂) A' (MulAut.conj e₀') hgoal
  · exact triD4LineAlt_of_conj_step hn hev K hK k hk D hZ A' hA' h27' hz' e₀' he₀'A' hline'

theorem ggNbrKGFieldTriD4ThreeLineWeyl_holds
    : GGNbrKGFieldTriD4ThreeLineWeyl :=
  ggNbrKGFieldTriD4ThreeLineWeyl_of_strong fun K _ _ hn hev hK hs =>
    ggTriD4LineWeylStrong_holds K hn hev hK hs

end CFSG.StandardType
