module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleTorus
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleOrbit
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.Tactic.NormNum

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.USixTwo
open USixTwo TorConj TorHomKernel MainProof TorHyperplanes
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G} {ω : K}

@[expose] noncomputable def piOf
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))

theorem piOf_surjective
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    Function.Surjective (piOf (K := K) θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective _)

private theorem piOf_ker
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    (piOf (K := K) θ).ker = Subgroup.center L := by
  ext y
  rw [MonoidHom.mem_ker, piOf, MonoidHom.comp_apply]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (Subgroup.center L) y = 1 := by
      apply θ.injective
      simpa using h
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center L) y).mp h1
  · intro h
    rw [QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff (N := Subgroup.center L) y).mpr h, map_one]

private theorem eq_one_of_mem_center_of_pow_three {y : L}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hy : y ∈ Subgroup.center L) (hy3 : y ^ 3 = 1) :
    y = 1 := by
  have hc : orderOf (⟨y, hy⟩ : ↥(Subgroup.center L)) = orderOf y :=
    (Subgroup.orderOf_coe (⟨y, hy⟩ : ↥(Subgroup.center L))).symm
  obtain ⟨k, hk⟩ := isPGroup_iff_orderOf_dvd_pow.mp hZ2 ⟨y, hy⟩
  rw [hc] at hk
  have h3 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
  have hcop : Nat.Coprime (2 ^ k) 3 := (by norm_num : Nat.Coprime 2 3).pow_left k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hk h3)

theorem piOf_injective_of_pow_three
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) {z z' : L} (hz : z ^ 3 = 1) (hz' : z' ^ 3 = 1)
    (h : piOf (K := K) θ z = piOf (K := K) θ z') : z = z' := by
  set c : L := z'⁻¹ * z with hcdef
  have hcZ : c ∈ Subgroup.center L := by
    rw [← piOf_ker (K := K) θ, MonoidHom.mem_ker]
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hzc : z = z' * c := by rw [hcdef]; group
  have hcomm : Commute z' c := Subgroup.mem_center_iff.mp hcZ z'
  have hc3 : c ^ 3 = 1 := by
    have h1 : (z' * c) ^ 3 = 1 := by rw [← hzc]; exact hz
    rwa [hcomm.mul_pow, hz', one_mul] at h1
  have hc1 : c = 1 := eq_one_of_mem_center_of_pow_three hZ2 hcZ hc3
  rw [hzc, hc1, mul_one]

theorem pow_three_of_mem_inf (hBs : IsElemAbelian 3 Bs) {y : L}
    (hy : y ∈ (Bs ⊓ L).subgroupOf L) : y ^ 3 = 1 := by
  apply Subtype.ext
  exact hBs.2 ((y : L) : G) (Subgroup.mem_subgroupOf.mp hy).1

private theorem piOf_injective_inf
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs) :
    Function.Injective ((piOf (K := K) θ).comp ((Bs ⊓ L).subgroupOf L).subtype) := by
  intro a b hab
  have h3a : ((a : ↥((Bs ⊓ L).subgroupOf L)) : L) ^ 3 = 1 :=
    pow_three_of_mem_inf hBs a.2
  have h3b : ((b : ↥((Bs ⊓ L).subgroupOf L)) : L) ^ 3 = 1 :=
    pow_three_of_mem_inf hBs b.2
  exact Subtype.ext (piOf_injective_of_pow_three θ hZ2 h3a h3b hab)

private theorem card_inf_Bs_L (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 := by
  have hbij : Function.Bijective
      (fun y : ↥((Bs ⊓ L).subgroupOf L) =>
        (⟨piOf (K := K) θ (y : L), Subgroup.mem_map_of_mem (piOf (K := K) θ) y.2⟩ :
          ↥(((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ)))) := by
    constructor
    · intro y z hyz
      exact piOf_injective_inf θ hZ2 hBs (congrArg Subtype.val hyz)
    · intro y
      obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨l, hl⟩, Subtype.ext hly⟩
  calc Nat.card ↥(Bs ⊓ L)
      = Nat.card ↥((Bs ⊓ L).subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    _ = Nat.card ↥(((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ)) :=
        Nat.card_congr (Equiv.ofBijective _ hbij)
    _ = Nat.card (USixTwo.torU K) := by rw [hmap]
    _ = 3 ^ 4 := USixTwo.card_torU hK

theorem orderOf_x_of_mem (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs) (hxL : x ∉ L) :
    orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime (hBs.2 x hx) ?_
  intro h
  exact hxL (h ▸ L.one_mem)

private theorem zpowers_inf_Bs_L (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs) (hxL : x ∉ L) :
    Subgroup.zpowers x ⊓ (Bs ⊓ L) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyP, hyQ⟩ := Subgroup.mem_inf.mp hy
  have hx3 : x ^ 3 = 1 := hBs.2 x hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx3⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, orderOf_x_of_mem hBs hx hxL] at hyP
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hyP
  rw [Finset.mem_range] at hi
  have hx4 : x ^ 4 = x := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
  have hx2L : x ^ 2 ∉ L := by
    intro h
    apply hxL
    rw [show x = (x ^ 2) ^ 2 from by rw [← pow_mul]; exact hx4.symm]
    exact L.pow_mem h 2
  rw [Subgroup.mem_bot]
  interval_cases i
  · simp
  · exact absurd (by simpa using hyQ.2) hxL
  · exact absurd (by simpa using hyQ.2) hx2L

theorem Bs_eq_zpowers_sup (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K) (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) :
    Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
  have hnorm : (Bs ⊓ L) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro y hy
    have hyx : y * x * y⁻¹ = x := by
      rw [show y * x = x * y from
        Subgroup.mem_centralizer_singleton_iff.mp (hLx hy.2)]
      group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (y * x * y⁻¹) = Subgroup.zpowers x
    rw [hyx]
  have hdisj : Disjoint (Subgroup.zpowers x) (Bs ⊓ L) :=
    disjoint_iff.mpr (zpowers_inf_Bs_L hBs hx hxL)
  have hcardsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers x) (Bs ⊓ L) hnorm hdisj
  have hle : Subgroup.zpowers x ⊔ (Bs ⊓ L) ≤ Bs :=
    sup_le (Subgroup.zpowers_le.mpr hx) inf_le_left
  have hsupcard : Nat.card ↥(Subgroup.zpowers x ⊔ (Bs ⊓ L)) = 3 ^ 5 := by
    rw [hcardsup, Nat.card_zpowers, orderOf_x_of_mem hBs hx hxL,
      card_inf_Bs_L hK θ hZ2 hBs hmap]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hsupcard])).symm

theorem inf_le_normalizer_zpowers (hLx : L ≤ Subgroup.centralizer {x}) :
    Bs ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  intro y hy
  have hyx : y * x * y⁻¹ = x := by
    rw [show y * x = x * y from
      Subgroup.mem_centralizer_singleton_iff.mp (hLx hy.2)]
    group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (y * x * y⁻¹) = Subgroup.zpowers x
  rw [hyx]

theorem exists_mul_zpowers (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hmap : ((Bs ⊓ L).subgroupOf L).map (piOf (K := K) θ) = USixTwo.torU K)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) {x : G} (hx : x ∈ Bs)
    (hxL : x ∉ L) (hLx : L ≤ Subgroup.centralizer {x}) {g : G} (hg : g ∈ Bs) :
    ∃ p ∈ Subgroup.zpowers x, ∃ q ∈ Bs ⊓ L, p * q = g := by
  have hsup := Bs_eq_zpowers_sup hK θ hZ2 hBs hcard hmap hx hxL hLx
  have hnorm := inf_le_normalizer_zpowers (Bs := Bs) (x := x) hLx
  have hg' : g ∈ ((Subgroup.zpowers x : Subgroup G) : Set G) *
      ((Bs ⊓ L : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers x) (Bs ⊓ L) hnorm]
    rw [← hsup]
    exact hg
  exact hg'

private def eps (i j : Fin 6) : Fin 6 → ZMod 3 := Pi.single i 1 - Pi.single j 1

private theorem sum_eps (i j : Fin 6) : ∑ k, eps i j k = 0 := by
  fin_cases i <;> fin_cases j <;> simp [eps, Fin.sum_univ_six] <;> decide

private theorem eps_apply_left {i j : Fin 6} (hij : i ≠ j) : eps i j i = 1 := by
  rw [eps, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij]
  simp

private theorem eps_apply_right {i j : Fin 6} (hij : i ≠ j) : eps i j j = -1 := by
  rw [eps, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same]
  decide

private theorem eps_apply_of_ne {i j k : Fin 6} (hki : k ≠ i) (hkj : k ≠ j) : eps i j k = 0 := by
  simp [eps, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

private theorem eps_eq_one_iff {i j x : Fin 6} (hij : i ≠ j) : eps i j x = 1 ↔ x = i := by
  constructor
  · intro h
    by_cases hxi : x = i
    · exact hxi
    · by_cases hxj : x = j
      · rw [hxj, eps_apply_right hij] at h
        exact absurd h (by decide)
      · rw [eps_apply_of_ne hxi hxj] at h
        exact absurd h (by decide)
  · intro hx
    rw [hx]
    exact eps_apply_left hij

private theorem eps_eq_neg_one_iff {i j x : Fin 6} (hij : i ≠ j) : eps i j x = -1 ↔ x = j := by
  constructor
  · intro h
    by_cases hxi : x = i
    · rw [hxi, eps_apply_left hij] at h
      exact absurd h (by decide)
    · by_cases hxj : x = j
      · exact hxj
      · rw [eps_apply_of_ne hxi hxj] at h
        exact absurd h (by decide)
  · intro hx
    rw [hx]
    exact eps_apply_right hij

def epsS {i j : Fin 6} (hij : i ≠ j) : ↥sumZeroSubgroup :=
  ⟨Multiplicative.ofAdd (eps i j), sum_eps i j⟩

private theorem coe_permX_epsS (σ : Equiv.Perm (Fin 6)) {i j : Fin 6} (hij : i ≠ j) :
    Multiplicative.toAdd ((TorConj.permX σ (epsS hij) : ↥sumZeroSubgroup) :
      Multiplicative (Fin 6 → ZMod 3)) = eps (σ i) (σ j) := by
  funext k
  rw [TorConj.coe_permX]
  change eps i j ((Equiv.symm σ) k) = eps (σ i) (σ j) k
  by_cases hki : k = σ i
  · have h1 : σ.symm k = i := by
      rw [Equiv.symm_apply_eq]
      exact hki
    rw [h1, eps_apply_left hij, hki, eps_apply_left (σ.injective.ne hij)]
  · have h1 : σ.symm k ≠ i := by
      intro h
      exact hki (by rwa [Equiv.symm_apply_eq] at h)
    by_cases hkj : k = σ j
    · have h2 : σ.symm k = j := by
        rw [Equiv.symm_apply_eq]
        exact hkj
      rw [h2, eps_apply_right hij, hkj, eps_apply_right (σ.injective.ne hij)]
    · have h2 : σ.symm k ≠ j := by
        intro h
        exact hkj (by rwa [Equiv.symm_apply_eq] at h)
      rw [eps_apply_of_ne h1 h2, eps_apply_of_ne hki hkj]

private theorem eps_eq_of_sub_const {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d)
    (h : ∃ k : ZMod 3, ∀ x, eps a b x - eps c d x = k) : a = c ∧ b = d := by
  classical
  obtain ⟨k, hk⟩ := h
  have hcard : ({a, b, c, d} : Finset (Fin 6)).card < 6 := by
    have h4 := Finset.card_le_four (a := a) (b := b) (c := c) (d := d)
    have h6 : (Finset.univ : Finset (Fin 6)).card = 6 := by simp
    omega
  obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, d} : Finset (Fin 6))) (t := Finset.univ) hcard
  have hea : e ≠ a := by intro h; exact he (by simp [h])
  have heb : e ≠ b := by intro h; exact he (by simp [h])
  have hec : e ≠ c := by intro h; exact he (by simp [h])
  have hed : e ≠ d := by intro h; exact he (by simp [h])
  have hk0 : k = 0 := by
    have h1 := hk e
    rw [eps_apply_of_ne hea heb, eps_apply_of_ne hec hed] at h1
    simpa using h1.symm
  have hzero : ∀ x, eps a b x = eps c d x := by
    intro x
    have h1 := hk x
    rw [hk0, sub_eq_zero] at h1
    exact h1
  have hac : a = c := by
    have h1 : eps c d a = 1 := by
      rw [← hzero a, eps_apply_left hab]
    exact (eps_eq_one_iff hcd).mp h1
  have hbd : b = d := by
    have h1 : eps c d b = -1 := by
      rw [← hzero b, eps_apply_right hab]
    exact (eps_eq_neg_one_iff hcd).mp h1
  exact ⟨hac, hbd⟩

theorem eq_of_permX_sub_const (σ τ : Equiv.Perm (Fin 6))
    (h : ∀ (i j : Fin 6) (hij : i ≠ j), ∃ c : ZMod 3,
      ∀ k, Multiplicative.toAdd ((TorConj.permX σ (epsS hij) : ↥sumZeroSubgroup) :
        Multiplicative (Fin 6 → ZMod 3)) k -
        Multiplicative.toAdd ((TorConj.permX τ (epsS hij) : ↥sumZeroSubgroup) :
        Multiplicative (Fin 6 → ZMod 3)) k = c) :
    σ = τ := by
  apply Equiv.Perm.ext
  intro i
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card
    (α := Fin 6) (by simp : 1 < Fintype.card (Fin 6)) i
  have hij : i ≠ j := fun h => hji h.symm
  obtain ⟨c, hc⟩ := h i j hij
  have hc' : ∀ k, eps (σ i) (σ j) k - eps (τ i) (τ j) k = c := by
    intro k
    rw [← coe_permX_epsS σ hij, ← coe_permX_epsS τ hij]
    exact hc k
  exact (eps_eq_of_sub_const (σ.injective.ne hij) (τ.injective.ne hij) ⟨c, hc'⟩).1

theorem permX_swap_deltaS_inv (i : Fin 5) :
    permX (Equiv.swap i.castSucc 5) (deltaS i) = (deltaS i)⁻¹ := by
  refine Subtype.ext ?_
  funext k
  show Multiplicative.toAdd ((permX (Equiv.swap i.castSucc 5) (deltaS i)).1) k =
    Multiplicative.toAdd (((deltaS i)⁻¹ : ↥sumZeroSubgroup).1) k
  rw [TorConj.coe_permX, Subgroup.coe_inv, toAdd_inv, Pi.neg_apply]
  change delta i ((Equiv.swap i.castSucc 5).symm k) = - delta i k
  fin_cases i <;> fin_cases k <;>
    simp [delta, delta0, delta1, delta2, delta3, delta4, Equiv.swap_apply_def] <;>
    decide

theorem eq_one_of_inv_eq_self {a : Multiplicative (ZMod 3)} (h : a⁻¹ = a) : a = 1 := by
  revert a
  decide

private theorem threeAArg_not_mem_constSubgroup : threeAArg ∉ TorHomKernel.constSubgroup := by
  intro h
  obtain ⟨c, hc⟩ := h
  have h0 : (1 : ZMod 3) = c := by simpa [threeAArg, threeAVec] using hc 0
  have h1 : (2 : ZMod 3) = c := by simpa [threeAArg, threeAVec] using hc 1
  rw [← h1] at h0
  exact absurd h0 (by decide)

theorem threeA_ne_one (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    threeA hω ≠ 1 := by
  intro h
  have h1 : torHom hK hω threeAArg = 1 := by
    apply Subtype.ext
    change (torHom hK hω threeAArg : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 1
    rw [MainProof.torHom_threeAArg, h]
  exact threeAArg_not_mem_constSubgroup
    ((TorHomKernel.torHom_eq_one_iff hK hω threeAArg).mp h1)

private theorem toAdd_inv_mul_permX_swap01 (v : ↥sumZeroSubgroup) :
    Multiplicative.toAdd ((v⁻¹ * permX (Equiv.swap 0 1) v : ↥sumZeroSubgroup) :
        Multiplicative (Fin 6 → ZMod 3)) =
      (Multiplicative.toAdd (v : Multiplicative (Fin 6 → ZMod 3)) 1 -
        Multiplicative.toAdd (v : Multiplicative (Fin 6 → ZMod 3)) 0) • threeAVec := by
  funext k
  show -Multiplicative.toAdd (v : Multiplicative (Fin 6 → ZMod 3)) k +
      Multiplicative.toAdd ((permX (Equiv.swap 0 1) v : ↥sumZeroSubgroup) :
        Multiplicative (Fin 6 → ZMod 3)) k = _
  rw [TorConj.coe_permX]
  generalize hc0 : Multiplicative.toAdd (v : Multiplicative (Fin 6 → ZMod 3)) 0 = c0
  generalize hc1 : Multiplicative.toAdd (v : Multiplicative (Fin 6 → ZMod 3)) 1 = c1
  fin_cases k <;> fin_cases c0 <;> fin_cases c1 <;>
    simp_all [threeAVec, Equiv.swap_apply_def, Pi.smul_apply, smul_eq_mul] <;> abel

private theorem toAdd_threeAArg_pow (n : ℕ) :
    Multiplicative.toAdd (((threeAArg ^ n : ↥sumZeroSubgroup) :
        Multiplicative (Fin 6 → ZMod 3))) = n • threeAVec := by
  rw [Subgroup.coe_pow, toAdd_pow]
  rfl

theorem inv_mul_permX_swap01_mem_zpowers (v : ↥sumZeroSubgroup) :
    v⁻¹ * permX (Equiv.swap 0 1) v ∈ Subgroup.zpowers threeAArg := by
  set d : ZMod 3 := Multiplicative.toAdd (v : Multiplicative (Fin 6 → ZMod 3)) 1 -
    Multiplicative.toAdd (v : Multiplicative (Fin 6 → ZMod 3)) 0 with hd
  have hpow : threeAArg ^ d.val = (v⁻¹ * permX (Equiv.swap 0 1) v : ↥sumZeroSubgroup) := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    rw [toAdd_threeAArg_pow, toAdd_inv_mul_permX_swap01, ← hd]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [← hpow]
  exact Subgroup.npow_mem_zpowers threeAArg d.val

theorem permX_swap01_threeAArg :
    permX (Equiv.swap 0 1) threeAArg = threeAArg⁻¹ := by
  refine Subtype.ext ?_
  funext k
  show Multiplicative.toAdd ((permX (Equiv.swap 0 1) threeAArg).1) k =
    Multiplicative.toAdd (((threeAArg)⁻¹ : ↥sumZeroSubgroup).1) k
  rw [TorConj.coe_permX, Subgroup.coe_inv, toAdd_inv, Pi.neg_apply]
  change threeAVec ((Equiv.swap 0 1).symm k) = - threeAVec k
  fin_cases k <;> simp [threeAVec, Equiv.swap_apply_def] <;> decide

end CFSG.StandardType.E6QTwo

end
