module

public import CFSG.RankThree.PartOne.S10.SemisimpleContract
import CFSG.RankThree.PartOne.S10.ComponentOrbitSemisimpleLocalRankWitness
import CFSG.RankThree.PartOne.S10.CyclicSemisimpleSectionOrbit
import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartOne.SemisimpleSection

open CFSG CFSG.LocalCores Subgroup
open CFSG.Assembly (evenRank)
open CFSG.Assembly.RankThreeEven (localRank)

section Conjugation

variable {Y : Type*} [Group Y]

theorem map_conj_map_conj_zpow (M : Subgroup Y) (x : Y) (n : ℤ) :
    (M.map (MulAut.conj (x ^ n)).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      M.map (MulAut.conj (x ^ (n + 1))).toMonoidHom := by
  rw [← RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← zpow_one_add, add_comm]

theorem exists_pow_eq_zpow [Finite Y] (x : Y) (k : ℤ) : ∃ n : ℕ, x ^ n = x ^ k :=
  ⟨(k % (orderOf x : ℤ)).toNat, by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := orderOf_pos x
      omega)), zpow_mod_orderOf]⟩

theorem mulEquiv_apply_mem_center_iff (ν : Y ≃* Y) (q : Y) : ν q ∈ center Y ↔ q ∈ center Y := by
  simpa only [← SetLike.mem_coe, Subgroup.coe_center] using
    MulEquivClass.apply_mem_center_iff ν (x := q)

theorem mk_mem_map_iff_mk_apply_mem_map (ν : Y ≃* Y) (M : Subgroup Y) (q : Y) :
    (q : Y ⧸ center Y) ∈ M.map (QuotientGroup.mk' (center Y)) ↔
      (ν q : Y ⧸ center Y) ∈ (M.map ν.toMonoidHom).map (QuotientGroup.mk' (center Y)) := by
  constructor
  · rintro ⟨m, hm, hmq⟩
    refine ⟨ν m, ⟨m, hm, rfl⟩, ?_⟩
    rw [QuotientGroup.mk'_apply] at hmq ⊢
    rw [QuotientGroup.eq] at hmq ⊢
    have := (mulEquiv_apply_mem_center_iff ν (m⁻¹ * q)).mpr hmq
    simpa using this
  · rintro ⟨_, ⟨m, hm, rfl⟩, hmq⟩
    refine ⟨m, hm, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hmq ⊢
    have := (mulEquiv_apply_mem_center_iff ν (m⁻¹ * q)).mp (by simpa using hmq)
    exact this

theorem map_conjNormal_subgroupOf (K : Subgroup Y) [K.Normal] (g : Y) (M : Subgroup Y) :
    (M.subgroupOf K).map (MulAut.conjNormal g).toMonoidHom =
      (M.map (MulAut.conj g).toMonoidHom).subgroupOf K := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y₀, hy₀, rfl⟩
    exact ⟨y₀, hy₀, by simp [MulAut.conjNormal_apply]⟩
  · rintro ⟨m, hm, hmy⟩
    refine ⟨(MulAut.conjNormal g).symm y, ?_, by simp⟩
    rw [MulAut.conjNormal_symm_apply]
    have : g⁻¹ * (y : Y) * g = m := by rw [← hmy]; group
    rw [this]
    exact hm

theorem map_subtype_map_conj (W : Subgroup Y) (g : W) (M : Subgroup W) :
    (M.map (MulAut.conj g).toMonoidHom).map W.subtype =
      (M.map W.subtype).map (MulAut.conj (g : Y)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

end Conjugation

section Core

theorem orbit_card_le_of_generated {G : Type} [Group G] [Finite G] {m : ℕ}
    (hm : evenRank G ≤ m) (h2 : CyclicSemisimpleSectionOrbitBound) {Y : Type} [Group Y]
    [Finite Y] (H : Subgroup G) (π₀ : H →* Y) (hπ₀ : Function.Surjective π₀) {r : ℕ}
    (hr : r.Prime) {x : Y} (hx : ∃ k : ℕ, orderOf x = r ^ k) {L : Subgroup Y}
    (hL : IsComponent L) (hgen : conjOrbitJoin x L ⊔ Subgroup.zpowers x = ⊤) :
    (conjOrbit x L).ncard ≤ m + 1 := by
  classical
  set A : ℤ → Subgroup Y := fun n => L.map (MulAut.conj (x ^ n)).toMonoidHom with hA
  have hAcomp : ∀ n, IsComponent (A n) := fun n =>
    isComponent_map_mulEquiv (MulAut.conj (x ^ n)) hL
  have hKA : conjOrbitJoin x L = ⨆ n, A n := rfl
  have hdA : conjOrbit x L = Set.range A := rfl
  rw [hKA] at hgen
  rw [hdA]
  set K : Subgroup Y := ⨆ n, A n with hK
  have hxK : x ∈ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hK, Subgroup.map_iSup]
    have h1 : ∀ n, (A n).map (↑(MulAut.conj x) : Y →* Y) = A (n + 1) := fun n =>
      map_conj_map_conj_zpow L x n
    simp only [h1]
    exact (Equiv.addRight (1 : ℤ)).iSup_comp (g := A)
  have hKn : K.Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← hgen]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxK)
  set Z : Subgroup Y := (center ↥K).map K.subtype with hZ
  have hZn : Z.Normal := by
    rw [hZ]
    infer_instance
  let μ : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  have hμs : Function.Surjective μ := QuotientGroup.mk'_surjective Z
  let π : ↥H →* Y ⧸ Z := μ.comp π₀
  have hπ : Function.Surjective π := hμs.comp hπ₀
  set S : Subgroup (Y ⧸ Z) := K.map μ with hS
  have hSn : S.Normal := hKn.map μ hμs
  set z : Y ⧸ Z := μ x with hz
  have hSz : S ⊔ Subgroup.zpowers z = ⊤ := by
    have h := congrArg (Subgroup.map μ) hgen
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top_of_surjective μ hμs] at h
  have hzord : ∃ k : ℕ, orderOf z = r ^ k := by
    obtain ⟨k, hk⟩ := hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp (hk ▸ orderOf_map_dvd μ x)
    exact ⟨j, hj⟩
  have hE : layer ↥K = ⊤ := layer_iSup_eq_top A hAcomp
  obtain ⟨φA, hφA⟩ := exists_mulEquiv_quotient_center_pi_components hE
  let ι : ↥K →* ↥S := μ.subgroupMap K
  have hιs : Function.Surjective ι := μ.subgroupMap_surjective K
  have hιker : ι.ker = center ↥K := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  let e1 : ↥K ⧸ center ↥K ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hιker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ι hιs)
  have he1 : ∀ k : ↥K, e1 (k : ↥K ⧸ center ↥K) = ι k := fun k => rfl
  let φ : ↥S ≃* (∀ C : ComponentIndex ↥K, C.1 ⧸ center C.1) := e1.symm.trans φA
  have hφι : ∀ k : ↥K, φ (ι k) = φA (k : ↥K ⧸ center ↥K) := by
    intro k
    show φA (e1.symm (ι k)) = _
    rw [← he1, MulEquiv.symm_apply_apply]
  have hconj : ∀ (n : ℕ) (k : ↥K),
      MulAut.conjNormal (z ^ n) (ι k) = ι (MulAut.conjNormal (x ^ n) k) := by
    intro n k
    apply Subtype.ext
    change (MulAut.conjNormal (z ^ n) (ι k) : Y ⧸ Z) =
      μ ((MulAut.conjNormal (x ^ n) k : ↥K) : Y)
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, map_mul, map_mul, map_inv, map_pow]
    rfl
  have hcompat : ∀ C D : ComponentIndex ↥K, ∃ n : ℕ, ∀ s : ↥S,
      φ s ∈ coordSubgroup (fun C : ComponentIndex ↥K => C.1 ⧸ center C.1) C ↔
        φ (MulAut.conjNormal (z ^ n) s) ∈
          coordSubgroup (fun C : ComponentIndex ↥K => C.1 ⧸ center C.1) D := by
    intro C D
    obtain ⟨a, ha⟩ := exists_eq_subgroupOf_of_isComponent_iSup A hAcomp C.2
    obtain ⟨b, hb⟩ := exists_eq_subgroupOf_of_isComponent_iSup A hAcomp D.2
    obtain ⟨n, hn⟩ := exists_pow_eq_zpow x (b - a)
    refine ⟨n, fun s => ?_⟩
    obtain ⟨k, rfl⟩ := hιs s
    have hAab : (A a).map (MulAut.conj (x ^ n)).toMonoidHom = A b := by
      show (L.map (MulAut.conj (x ^ a)).toMonoidHom).map (MulAut.conj (x ^ n)).toMonoidHom =
        L.map (MulAut.conj (x ^ b)).toMonoidHom
      rw [← RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, hn, ← zpow_add,
        sub_add_cancel]
    have hCD : D.1 = C.1.map (MulAut.conjNormal (x ^ n)).toMonoidHom := by
      rw [ha, hb, map_conjNormal_subgroupOf, hAab]
    rw [hconj, hφι, hφι, phi_mem_coordSubgroup_iff φA hφA C,
      phi_mem_coordSubgroup_iff φA hφA D, hCD]
    exact mk_mem_map_iff_mk_apply_mem_map (MulAut.conjNormal (x ^ n)) C.1 k
  have hnonab : ∀ C : ComponentIndex ↥K, ∃ a b : C.1 ⧸ center C.1, a * b ≠ b * a :=
    fun C => C.2.1.2.2
  have : ∀ C : ComponentIndex ↥K, IsSimpleGroup (C.1 ⧸ center C.1) := fun C => C.2.1.2.1
  have heven : ∀ C : ComponentIndex ↥K, Even (Nat.card (C.1 ⧸ center C.1)) := fun C =>
    (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even (hnonab C)).1
  have : Nonempty (ComponentIndex ↥K) :=
    ⟨⟨(A 0).subgroupOf K, isComponent_subgroupOf_iSup A hAcomp 0⟩⟩
  have hbound := h2 G m hm H (Y ⧸ Z) π hπ r hr z hzord S hSz (ComponentIndex ↥K)
    (fun C => C.1 ⧸ center C.1) hnonab heven φ hcompat
  have hcard : Fintype.card (ComponentIndex ↥K) = (Set.range A).ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_componentIndex_iSup A hAcomp
  rw [← hcard]
  exact hbound

end Core

end CFSG.RankThree.PartOne.SemisimpleSection

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalCores Subgroup SemisimpleSection
open CFSG.Assembly (evenRank)

theorem quotient_component_orbit_bound_of (h2 : CyclicSemisimpleSectionOrbitBound) :
    QuotientComponentOrbitBound := by
  intro G _ _ m hm N _ r hr x hx L hL hmove d hd
  have : IsSimpleGroup (L ⧸ center L) := hL.1.2.1
  have hnab : ∃ a b : L ⧸ center L, a * b ≠ b * a := hL.1.2.2
  obtain ⟨q, hq, hq2, hqdvd⟩ := exists_odd_prime_dvd_card_of_nonabelian_simple hnab
  have h2L : 2 ∣ Nat.card (L ⧸ center L) :=
    (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1.two_dvd
  have hqL : 2 * q ∣ Nat.card (L ⧸ center L) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm) h2L
      hqdvd
  obtain ⟨-, hrd, -⟩ := component_orbit_semisimple_local_rank_witness (G ⧸ N) r hr x hx L hL
    hmove q hq hq2 hqL d (conjOrbitJoin x L) hd rfl
  refine ⟨hrd, ?_⟩
  set A : ℤ → Subgroup (G ⧸ N) := fun n => L.map (MulAut.conj (x ^ n)).toMonoidHom with hA
  have hKA : conjOrbitJoin x L = ⨆ n, A n := rfl
  have hdA : conjOrbit x L = Set.range A := rfl
  set W : Subgroup (G ⧸ N) := conjOrbitJoin x L ⊔ Subgroup.zpowers x with hW
  have hxW : x ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hLW : L ≤ W := by
    intro g hg
    refine le_sup_left (a := conjOrbitJoin x L) (le_iSup A 0 ⟨g, hg, ?_⟩)
    simp
  let x' : ↥W := ⟨x, hxW⟩
  let L' : Subgroup ↥W := L.subgroupOf W
  have hL' : IsComponent L' := component_overgroup hL hLW
  have hx' : ∃ k : ℕ, orderOf x' = r ^ k := by
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, (Subgroup.orderOf_coe x').symm.trans hk⟩
  have hmapA : ∀ n : ℤ, (L'.map (MulAut.conj (x' ^ n)).toMonoidHom).map W.subtype = A n := by
    intro n
    rw [map_subtype_map_conj, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLW]
    rfl
  have hord : (conjOrbit x' L').ncard = (conjOrbit x L).ncard := by
    have hrange : Set.range A = Subgroup.map W.subtype '' conjOrbit x' L' := by
      rw [conjOrbit, ← Set.range_comp]
      exact congrArg Set.range (funext fun n => (hmapA n).symm)
    rw [hdA, hrange]
    exact (Set.ncard_image_of_injective _ (Subgroup.map_injective W.subtype_injective)).symm
  have hgen : conjOrbitJoin x' L' ⊔ Subgroup.zpowers x' = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_sup, conjOrbitJoin, Subgroup.map_iSup, MonoidHom.map_zpowers,
      Subgroup.map_top, Subgroup.range_subtype]
    simp only [hmapA]
    rfl
  have hπ₀ : Function.Surjective ((QuotientGroup.mk' N).subgroupComap W) :=
    MonoidHom.subgroupComap_surjective _ W (QuotientGroup.mk'_surjective N)
  have hcore := orbit_card_le_of_generated hm h2 (W.comap (QuotientGroup.mk' N))
    ((QuotientGroup.mk' N).subgroupComap W) hπ₀ hr hx' hL' hgen
  rw [hd, ← hord]
  exact hcore

theorem quotient_component_orbit_bound : QuotientComponentOrbitBound :=
  quotient_component_orbit_bound_of cyclic_semisimple_section_orbit_bound

end CFSG.RankThree.PartOne
