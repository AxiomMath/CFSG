module

import CFSG.Walter.W67.Prop23
public import CFSG.Walter.W67.Lemma21

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_of_odd_relIndex {L M : Subgroup G} (hn : (L.subgroupOf M).Normal)
    (hodd : Odd (L.subgroupOf M).index) {x : G} (hxM : x ∈ M) {k : ℕ} (hx : orderOf x = 2 ^ k) :
    x ∈ L := by
  have := hn
  have := mem_of_odd_index (N := L.subgroupOf M) hodd (y := ⟨x, hxM⟩) (k := k)
    (by rw [Subgroup.orderOf_mk, hx])
  exact Subgroup.mem_subgroupOf.mp this

theorem le_of_odd_relIndex {L M W : Subgroup G} (hn : (L.subgroupOf M).Normal)
    (hodd : Odd (L.subgroupOf M).index) (hWM : W ≤ M) (hW : IsPGroup 2 W) : W ≤ L := by
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hW ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  exact mem_of_odd_relIndex hn hodd (hWM hx) hk

theorem mem_of_odd_index' {N : Subgroup G} (hN : N.Normal) (hodd : Odd N.index) {x : G} {k : ℕ}
    (hx : orderOf x = 2 ^ k) : x ∈ N := by
  have := hN
  exact mem_of_odd_index hodd hx

omit [Finite G] in
theorem commutator_le_of_index_two {M N : Subgroup G} (hn : (N.subgroupOf M).Normal)
    (h2 : (N.subgroupOf M).index = 2) : ⁅M, M⁆ ≤ N := by
  have := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (M ⧸ N.subgroupOf M) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, h2])
  have h1 := Abelianization.commutator_subset_ker (QuotientGroup.mk' (N.subgroupOf M))
  rw [QuotientGroup.ker_mk'] at h1
  rw [← Subgroup.map_subtype_commutator]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h1 hx)

theorem index_ne_two_of_sylow_le_commutator {M : Subgroup G} (P : Sylow 2 G)
    (hP : (P : Subgroup G) ≤ ⁅M, M⁆) :
    ∀ N : Subgroup G, N ≤ M → (N.subgroupOf M).Normal → (N.subgroupOf M).index ≠ 2 := by
  intro N hNM hn h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : (P : Subgroup G) ≤ N := hP.trans (commutator_le_of_index_two hn h2)
  apply P.not_dvd_index
  rw [← Subgroup.relIndex_mul_index hPN, ← Subgroup.relIndex_mul_index hNM]
  change 2 ∣ (P : Subgroup G).relIndex N * ((N.subgroupOf M).index * M.index)
  rw [h2]
  exact dvd_mul_of_dvd_right (dvd_mul_right 2 _) _

omit [Finite G] in
theorem index_ne_two_subtype {M : Subgroup G}
    (hM : ∀ N : Subgroup G, N ≤ M → (N.subgroupOf M).Normal → (N.subgroupOf M).index ≠ 2) :
    ∀ N : Subgroup M, N.Normal → N.index ≠ 2 := by
  intro N hn h2
  have hc : (N.map M.subtype).subgroupOf M = N :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective N
  apply hM (N.map M.subtype) (Subgroup.map_subtype_le N)
  · rw [hc]
    exact hn
  · rw [hc]
    exact h2

theorem odd_index_commutator (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    Odd (commutator G).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have h2 : 2 ∣ Nat.card (Abelianization G) := by
    rw [Abelianization, ← Subgroup.index_eq_card]
    exact even_iff_two_dvd.mp hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Abelianization G) 2 h2
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨P, hP⟩ := hz2.exists_le_sylow
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz
    omega
  obtain ⟨H, hHn, hH⟩ := JT.exists_normal_index_eq_of_commute_normalizer P
    ⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩ (hP (Subgroup.mem_zpowers z)) hz1
    (fun n _ => mul_comm n z)
  apply hidx (H.comap Abelianization.of) (hHn.comap _)
  rw [Subgroup.index_comap_of_surjective (f := Abelianization.of) H
    (QuotientGroup.mk'_surjective (commutator G))]
  exact hH

namespace PSL2Sub

variable {X : Type} [Group X] {p f : ℕ} [Fact p.Prime] {K : Subgroup X}

theorem exists_three
    [Finite X] (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {V : Subgroup X} (hVK : V ≤ K) (hV : IsKleinFour V) :
    ∃ z ∈ K, orderOf z = 3 ∧ z ∈ Subgroup.normalizer (V : Set X) ∧
      z ∉ Subgroup.centralizer (V : Set X) := by
  have h12 := card_inf_normalizer e hp hf h8 hVK hV
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (K ⊓ Subgroup.normalizer (V : Set X) :
    Subgroup X)) 3 (by rw [h12]; norm_num)
  have hz3 : orderOf (z : X) = 3 := by rw [Subgroup.orderOf_coe, hz]
  refine ⟨z, z.2.1, hz3, z.2.2, fun hzC => ?_⟩
  have : (z : X) ∈ K ⊓ Subgroup.centralizer (V : Set X) := ⟨z.2.1, hzC⟩
  rw [inf_centralizer_eq e hp hf hVK hV] at this
  have h4 : orderOf (z : X) ∣ 4 := hV.card_four ▸ Subgroup.orderOf_dvd_natCard _ this
  rw [hz3] at h4
  omega

end PSL2Sub

theorem le_commutator_of_orderOf_three {X : Type} [Group X] {V W : Subgroup X}
    (hV : IsKleinFour V) (hVW : V ≤ W) {z : X} (hzW : z ∈ W) (hz3 : orderOf z = 3)
    (hzN : z ∈ Subgroup.normalizer (V : Set X)) (hzC : z ∉ Subgroup.centralizer (V : Set X)) :
    V ≤ ⁅W, W⁆ := by
  have : Finite V := by
    have := hV.card_four
    exact Nat.finite_of_card_ne_zero (by omega)
  set c : V → V := fun t => ⟨z * t * z⁻¹ * (t : X)⁻¹, V.mul_mem
    ((Subgroup.mem_normalizer_iff.mp hzN t).mp t.2) (V.inv_mem t.2)⟩ with hc
  have hcinj : Function.Injective c := by
    intro s t hst
    have h1 : z * s * z⁻¹ * (s : X)⁻¹ = z * t * z⁻¹ * (t : X)⁻¹ := congrArg Subtype.val hst
    have hfix : z * ((t : X)⁻¹ * s) * z⁻¹ = (t : X)⁻¹ * s := by
      have hab := hV.isMulCommutative
      have hts : (s : X)⁻¹ * (t : X) = (t : X) * (s : X)⁻¹ :=
        congrArg Subtype.val (hab.is_comm.comm (s⁻¹) t)
      calc z * ((t : X)⁻¹ * s) * z⁻¹ = (z * t * z⁻¹)⁻¹ * (z * s * z⁻¹) := by group
        _ = (z * t * z⁻¹ * (t : X)⁻¹ * t)⁻¹ * (z * s * z⁻¹ * (s : X)⁻¹ * s) := by group
        _ = (z * s * z⁻¹ * (s : X)⁻¹ * t)⁻¹ * (z * s * z⁻¹ * (s : X)⁻¹ * s) := by rw [h1]
        _ = (t : X)⁻¹ * s := by group
    have := JT.eq_one_of_conj_eq_of_orderOf_eq_three hV hz3 hzN hzC
      (V.mul_mem (V.inv_mem t.2) s.2) hfix
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  have hcsurj := Finite.injective_iff_surjective.mp hcinj
  intro t ht
  obtain ⟨s, hs⟩ := hcsurj ⟨t, ht⟩
  have := congrArg Subtype.val hs
  change z * s * z⁻¹ * (s : X)⁻¹ = t at this
  rw [← this]
  exact Subgroup.commutator_mem_commutator hzW (hVW s.2)

namespace PSL2Sub

variable {X : Type} [Group X] {p f : ℕ} [Fact p.Prime] {K : Subgroup X}

theorem le_commutator
    [Finite X] (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {V W : Subgroup X} (hVK : V ≤ K) (hV : IsKleinFour V)
    (hKW : K ≤ W) : V ≤ ⁅W, W⁆ := by
  obtain ⟨z, hzK, hz3, hzN, hzC⟩ := exists_three e hp hf h8 hVK hV
  exact le_commutator_of_orderOf_three hV (hVK.trans hKW) (hKW hzK) hz3 hzN hzC

theorem exists_ne_zero_sq_ne_one {F : Type*} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h => ?_⟩
  have h1 : orderOf x ≤ 2 := orderOf_le_of_pow_eq_one zero_lt_two (Units.ext (by simpa using h))
  rw [orderOf_eq_card_of_forall_mem_zpowers hx] at h1
  have := Nat.card_eq_card_units_add_one F
  omega

theorem isSimpleGroup (e : K ≃* PSL(2, GaloisField p f)) (hf : 0 < f) (hq : 3 < p ^ f) :
    IsSimpleGroup K := by
  have : IsSimpleGroup PSL(2, GaloisField p f) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card p f hf.ne']
      omega)
  exact e.isSimpleGroup

theorem commutator_eq (e : K ≃* PSL(2, GaloisField p f)) (hf : 0 < f) (hq : 3 < p ^ f) :
    ⁅K, K⁆ = K := by
  have hc : commutator PSL(2, GaloisField p f) = ⊤ :=
    SL2Simple.PSL_commutator_eq_top (exists_ne_zero_sq_ne_one (by
      rw [GaloisField.card p f hf.ne']
      omega))
  have hK : commutator K = ⊤ := by
    have h2 : (⊤ : Subgroup PSL(2, GaloisField p f)).map e.symm.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e.symm.surjective
    have h1 : (commutator PSL(2, GaloisField p f)).map e.symm.toMonoidHom = commutator K := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, h2]
    rw [hc, h2] at h1
    exact h1.symm
  rw [← Subgroup.map_subtype_commutator, hK, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end PSL2Sub

theorem conj_mem_commutator_of_mem_normalizer {X : Type} [Group X] {M : Subgroup X} {y t : X}
    (hy : y ∈ Subgroup.normalizer (M : Set X)) (ht : t ∈ ⁅M, M⁆) : y * t * y⁻¹ ∈ ⁅M, M⁆ := by
  have hM : M.map (MulAut.conj y).toMonoidHom = M := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hy m).mp hm
    · intro hx
      refine ⟨y⁻¹ * x * y, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * x * y)).mpr
        apply this
        simpa [mul_assoc] using hx
      · simp [MulAut.conj_apply, mul_assoc]
  have := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom ht
  rw [Subgroup.map_commutator, hM] at this
  simpa [MulAut.conj_apply] using this

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem S_le_commutator {M : Subgroup G} (hTM : fr.T ≤ ⁅M, M⁆) {y t : G}
    (hy : y ∈ Subgroup.normalizer (M : Set G)) (ht : t ∈ fr.T) (hJ : y * t * y⁻¹ = h.J) :
    (fr.S : Subgroup G) ≤ ⁅M, M⁆ := by
  rw [← fr.zpowers_J_sup_T]
  refine sup_le (Subgroup.zpowers_le.mpr ?_) hTM
  rw [← hJ]
  exact conj_mem_commutator_of_mem_normalizer hy (hTM ht)

end Frame

theorem exists_zpowers_sup_of_outCyclic {X : Type} [Group X] {L : Subgroup X} [L.Normal]
    (hout : OutCyclic L) :
    ∃ g : X, Subgroup.zpowers g ⊔ (L ⊔ Subgroup.centralizer (L : Set X)) = ⊤ := by
  obtain ⟨α, hα⟩ := hout
  set φ : X →* MulAut L := MulAut.conjNormal
  set B : Subgroup (MulAut L) := Subgroup.zpowers α ⊓ φ.range
  have : IsCyclic B := Subgroup.isCyclic_of_le (H' := Subgroup.zpowers α) inf_le_left
  obtain ⟨⟨β, hβ⟩, hgen⟩ := IsCyclic.exists_generator (α := B)
  obtain ⟨g, hg⟩ := hβ.2
  have hconj : ∀ ℓ : L, MulAut.conj ℓ = φ (ℓ : X) := fun ℓ => by
    ext y
    simp [φ, MulAut.conjNormal_apply, MulAut.conj_apply]
  refine ⟨g, eq_top_iff.mpr fun x _ => ?_⟩
  obtain ⟨k, ℓ, hk⟩ := hα (φ x)
  have hαk : α ^ k ∈ B := ⟨Subgroup.zpow_mem_zpowers α k, ⟨x * (ℓ : X)⁻¹, by
    rw [map_mul, map_inv, ← hconj, hk, mul_inv_cancel_right]⟩⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨α ^ k, hαk⟩)
  have hm' : β ^ m = α ^ k := congrArg Subtype.val hm
  have hx : φ x = φ (g ^ m * ℓ) := by
    rw [map_mul, map_zpow, hg, hm', ← hconj, hk]
  have hker : x * (g ^ m * ℓ)⁻¹ ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : φ (x * (g ^ m * ℓ)⁻¹) = 1 := by rw [map_mul, map_inv, hx, mul_inv_cancel]
    have h2 := congrArg (fun a : MulAut L => ((a ⟨y, hy⟩ : L) : X)) h1
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc y * (x * (g ^ m * ℓ)⁻¹) = (x * (g ^ m * ℓ)⁻¹ * y * (x * (g ^ m * ℓ)⁻¹)⁻¹) *
          (x * (g ^ m * ℓ)⁻¹) := by rw [h2]
      _ = _ := by group
  have hxe : x = (x * (g ^ m * ℓ)⁻¹) * (g ^ m * ℓ) := by group
  rw [hxe]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_right hker))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers g m))
      (Subgroup.mem_sup_right (Subgroup.mem_sup_left ℓ.2)))

end CFSG.Walter.W67
