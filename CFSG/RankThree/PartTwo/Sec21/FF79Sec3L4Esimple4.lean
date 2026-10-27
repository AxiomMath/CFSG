module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple3
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]
variable {β : MulAut H} {Z K : Subgroup H} {z₀ : H}

theorem e34_K_simple (hd : FF79APData β Z K z₀) : IsSimpleGroup ↥K := by
  obtain ⟨e⟩ := hd.K_a5
  haveI := alternatingGroup.isSimpleGroup_five
  exact e.isSimpleGroup

theorem e34_K_perfect (hd : FF79APData β Z K z₀) : ⁅K, K⁆ = K := by
  obtain ⟨e⟩ := hd.K_a5
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top h5)
  haveI : Group.IsPerfect ↥K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp inferInstance

theorem e34_K_inf_normal_eq_bot (hd : FF79APData β Z K z₀) {N : Subgroup H} [N.Normal]
    (hKN : ¬ K ≤ N) : ∀ k ∈ K, k ∈ N → k = 1 := by
  haveI := e34_K_simple hd
  intro k hk hkN
  have hnor : (N.subgroupOf K).Normal := inferInstance
  rcases hnor.eq_bot_or_eq_top with h | h
  · have : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := hkN
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exact absurd (fun g hg => by
      have : (⟨g, hg⟩ : ↥K) ∈ N.subgroupOf K := by rw [h]; trivial
      exact this) hKN

theorem e34_K_le_of_le_sup (hd : FF79APData β Z K z₀) {E : Subgroup H} [E.Normal]
    (hK : K ≤ E ⊔ Subgroup.zpowers z₀) : K ≤ E := by
  have hz : z₀ ∈ Subgroup.center H := hd.Z_central hd.z₀_mem
  rw [← e34_K_perfect hd]
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  obtain ⟨e1, he1, w1, hw1, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hK hg)
  obtain ⟨e2, he2, w2, hw2, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hK hh)
  have hc : ∀ w ∈ Subgroup.zpowers z₀, ∀ g : H, g * w = w * g := fun w hw g =>
    (Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hz hw) g)
  have hw : w1 * w2 = w2 * w1 := (hc w1 hw1 w2).symm
  have h1 : (QuotientGroup.mk' E) (e1 * w1) = (QuotientGroup.mk' E) w1 := by
    rw [map_mul, show (QuotientGroup.mk' E) e1 = 1 from (QuotientGroup.eq_one_iff e1).mpr he1,
      one_mul]
  have h2 : (QuotientGroup.mk' E) (e2 * w2) = (QuotientGroup.mk' E) w2 := by
    rw [map_mul, show (QuotientGroup.mk' E) e2 = 1 from (QuotientGroup.eq_one_iff e2).mpr he2,
      one_mul]
  have key : (QuotientGroup.mk' E) ⁅e1 * w1, e2 * w2⁆ = 1 := by
    rw [map_commutatorElement, h1, h2, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr hw, map_one]
  exact (QuotientGroup.eq_one_iff _).mp key

theorem e34_K_le_layer (hd : FF79APData β Z K z₀) : K ≤ layer H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := e34_layer_normal (H := H)
  by_contra hKE
  obtain ⟨e⟩ := hd.K_a5
  obtain ⟨x, hxK, hx3, -⟩ := e34_a5_data e
  have hE : layer H ≠ ⊥ := e34_layer_ne_bot hd
  have hS := hd.absyl
  have hO := hd.core
  have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx3
    exact absurd hx3 (by decide)
  have hKE0 := e34_K_inf_normal_eq_bot hd hKE
  have hxE : x ∉ layer H := fun h => hx1 (hKE0 x hxK h)
  have hβx : β x = x := hd.K_fix x hxK
  obtain ⟨Q, hxQ, hQβ⟩ := e34_exists_fixed_sylow hd.beta3 hx3' hβx
  have hQc := e34_comm_of_pGroup hS Q.isPGroup'
  obtain ⟨C, hC⟩ : ∃ C : Subgroup H, IsComponent C := by
    by_contra hno
    push Not at hno
    exact hE (LocalCores.layer_eq_bot_of_forall hno)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3
    (e34_comp_three_dvd hO hC (e34_comp_ne_bot hC))
  have hgo : orderOf (g : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hg
  have hgE : (g : H) ∈ layer H := LocalCores.component_le_layer hC g.2
  have hQsyl : IsSylowOf 3 (Q : Subgroup H) ⊤ :=
    ⟨le_top, Q.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr Q.not_dvd_index⟩
  have hg3 : (g : H) ^ 3 = 1 := hgo ▸ pow_orderOf_eq_one _
  obtain ⟨k, -, hk⟩ := L41.exists_conj_le_sylowOf_p (p := 3) hQsyl
    (le_top : Subgroup.zpowers (g : H) ≤ ⊤)
    (e34_pGroup_zpowers (p := 3) (k := 1) (by simpa using hg3))
  have hy0Q : k * (g : H) * k⁻¹ ∈ (Q : Subgroup H) := hk _ (Subgroup.mem_zpowers _)
  have hy0E : k * (g : H) * k⁻¹ ∈ layer H := by
    have := (e34_layer_normal (H := H)).conj_mem _ hgE k
    exact this
  have hy01 : k * (g : H) * k⁻¹ ≠ 1 := by
    intro h
    have : (g : H) = 1 := by
      have h' : (g : H) = k⁻¹ * (k * (g : H) * k⁻¹) * k := by group
      rw [h'] at *
      rw [h]; group
    rw [this, orderOf_one] at hgo
    exact absurd hgo (by decide)
  have hy03 : (k * (g : H) * k⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hg3]; simp
  obtain ⟨y, ⟨hyQ, hyE⟩, hy1, hy3, hβy⟩ := e34_fixed_elem (β := β) hd.beta3
    (A := (Q : Subgroup H) ⊓ layer H)
    (fun a ha b hb => hQc a ha.1 b hb.1)
    (fun a ha => ⟨hQβ a ha.1, e34_layer_inv β ha.2⟩) (t := k * (g : H) * k⁻¹)
    ⟨hy0Q, hy0E⟩ hy01 hy03
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hz0c : ∀ w : H, w * z₀ = z₀ * w := fun w =>
    (Subgroup.mem_center_iff.mp (hd.Z_central hd.z₀_mem) w)
  have hz0o : orderOf z₀ = 3 := hd.z₀_ord
  have hz0E : z₀ ∉ layer H := by
    intro h
    have h1 := e34_center_layer_trivial hO hS h (fun w _ => hz0c w)
    rw [h1, orderOf_one] at hz0o
    exact absurd hz0o (by decide)
  have hzc : ∀ b ∈ Subgroup.zpowers z₀, ∀ g : H, g * b = b * g := fun b hb g =>
    Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr (hd.Z_central hd.z₀_mem) hb) g
  have hyz : Subgroup.zpowers y ⊓ Subgroup.zpowers z₀ = ⊥ := by
    rw [inf_comm]
    apply e34_zpowers_inf_eq_bot hz0o
    intro hz
    exact hz0E ((Subgroup.zpowers_le.mpr hyE) hz)
  have hW : IsElemAb 3 (1 + 1) (Subgroup.zpowers y ⊔ Subgroup.zpowers z₀) :=
    e34_elemAb_sup (e34_elemAb_zpowers hyo) (e34_elemAb_zpowers hz0o)
      (fun a _ b hb => hzc b hb a) hyz
  haveI : (Subgroup.zpowers z₀).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (hd.Z_central hd.z₀_mem))
  have hxN : x ∉ layer H ⊔ Subgroup.zpowers z₀ := by
    intro h
    by_cases hKN : K ≤ layer H ⊔ Subgroup.zpowers z₀
    · exact hKE (e34_K_le_of_le_sup hd hKN)
    · exact hx1 (e34_K_inf_normal_eq_bot hd hKN x hxK h)
  have hWN : Subgroup.zpowers y ⊔ Subgroup.zpowers z₀ ≤ layer H ⊔ Subgroup.zpowers z₀ :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hyE))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀)))
  have hxW : x ∉ Subgroup.zpowers y ⊔ Subgroup.zpowers z₀ := fun h => hxN (hWN h)
  have hxinf : Subgroup.zpowers x ⊓ (Subgroup.zpowers y ⊔ Subgroup.zpowers z₀) = ⊥ :=
    e34_zpowers_inf_eq_bot hx3 hxW
  have hxy : y * x = x * y := hQc y hyQ x hxQ
  have hWc : Subgroup.zpowers y ⊔ Subgroup.zpowers z₀ ≤ Subgroup.centralizer ({x} : Set H) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxy))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (hzc z₀ (Subgroup.mem_zpowers z₀) x).symm))
  have hcommxW : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers z₀,
      a * b = b * a := by
    intro a ha b hb
    have hb' : b * x = x * b := (Subgroup.mem_centralizer_singleton_iff.mp (hWc hb))
    have : a ∈ Subgroup.centralizer ({b} : Set H) :=
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hb'.symm)) ha
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hT : IsElemAb 3 (1 + (1 + 1))
      (Subgroup.zpowers x ⊔ (Subgroup.zpowers y ⊔ Subgroup.zpowers z₀)) :=
    e34_elemAb_sup (e34_elemAb_zpowers hx3) hW hcommxW hxinf
  have hfix : ∀ t ∈ Subgroup.zpowers x ⊔ (Subgroup.zpowers y ⊔ Subgroup.zpowers z₀), β t = t := by
    have hle : Subgroup.zpowers x ⊔ (Subgroup.zpowers y ⊔ Subgroup.zpowers z₀) ≤
        β.toMonoidHom.eqLocus (MonoidHom.id H) :=
      sup_le (Subgroup.zpowers_le.mpr hβx)
        (sup_le (Subgroup.zpowers_le.mpr hβy) (Subgroup.zpowers_le.mpr hd.z₀_fix))
    exact fun t ht => hle ht
  exact hd.no27 _ hfix (by simpa using hT)

end CFSG.RankThree.PartTwo.Sec21.FF79
