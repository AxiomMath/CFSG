module

public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GroupTheory.ConjTransport
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement
open CFSG.GH74.GLS.C3.Layer1.Back (mem_conjugate_iff' card_conjugate' conjugate_inf'
  conjugate_of_mem conjugate_le_conjugate' isPGroup_conjugate' isSylowOf_conjugate
  conjugate_centralizer_singleton isElementaryAbelian_of_forall forall_of_isElementaryAbelian
  isElementaryAbelian_conjugate conjugate_one' exists_mem_conjugate_le_of_isSylowOf)
open CFSG.GroupTheory (centralizer_map_conj centralizer_zpowers_eq mem_normalizer_zpowers_iff
  isSylowOf_of_forall_pElement_normalizer_le)

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem centerIn_conjugate (D : Subgroup G) (g : G) :
    centerIn (CFSG.conjugate D g) = CFSG.conjugate (centerIn D) g := by
  rw [centerIn, centerIn, CFSG.conjugate, CFSG.conjugate,
    Subgroup.map_inf D (Subgroup.centralizer (D : Set G)) (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective,
    centralizer_map_conj g⁻¹ D]

private theorem conjugate_centralizer_singleton_eq {a b g : G}
    (h : CFSG.conjugate (Subgroup.zpowers a) g = Subgroup.zpowers b) :
    CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) g =
      Subgroup.centralizer ({b} : Set G) := by
  have hzp : Subgroup.zpowers (g⁻¹ * a * g) = Subgroup.zpowers b := by
    rw [← h, CFSG.conjugate, MonoidHom.map_zpowers]
    congr 1
    change g⁻¹ * a * g = MulAut.conj g⁻¹ a
    rw [MulAut.conj_apply, inv_inv]
  rw [conjugate_centralizer_singleton,
    ← centralizer_zpowers_eq (g⁻¹ * a * g), ← centralizer_zpowers_eq b, hzp]

private theorem conj_mem_centerIn_of_mem_normalizer {D : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) {a : G} (ha : a ∈ centerIn D) :
    g * a * g⁻¹ ∈ centerIn D := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg a).mp ha.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro s hs
  have hs' : g⁻¹ * s * g ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
  have hcomm := Subgroup.mem_centralizer_iff.mp ha.2 (g⁻¹ * s * g) hs'
  calc s * (g * a * g⁻¹) = g * ((g⁻¹ * s * g) * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * s * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * a * g⁻¹) * s := by group

private theorem mem_centerIn_of_conj_eq {S T : Subgroup G} (hST : S ≤ T) {x : G}
    (hcos : ∀ b ∈ T, b * x ∈ S ∨ b ∈ S) {a : G} (ha : a ∈ centerIn S)
    (hax : x * a * x⁻¹ = a) : a ∈ centerIn T := by
  have hcommx : x * a = a * x := by
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [hax]
  have hxinv : x⁻¹ * a = a * x⁻¹ := by
    calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * a) * x⁻¹ := by rw [← hcommx]
      _ = a * x⁻¹ := by group
  refine ⟨hST ha.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro t ht
  rcases hcos t ht with htx | htS
  · have hca := Subgroup.mem_centralizer_iff.mp ha.2 (t * x) htx
    calc t * a = (t * x) * (x⁻¹ * a) := by group
      _ = (t * x) * (a * x⁻¹) := by rw [hxinv]
      _ = ((t * x) * a) * x⁻¹ := by group
      _ = (a * (t * x)) * x⁻¹ := by rw [hca]
      _ = a * t := by group
  · exact Subgroup.mem_centralizer_iff.mp ha.2 t htS

private noncomputable def centerConjHom {S : Subgroup G} (x : G)
    (hconjZ : ∀ a ∈ centerIn S, x * a * x⁻¹ ∈ centerIn S) : centerIn S →* G :=
  { toFun := fun a => (a : G) * (x * (a : G) * x⁻¹)
    map_one' := by simp
    map_mul' := by
      intro a b
      have hA' : x * (a : G) * x⁻¹ ∈ centerIn S := hconjZ (a : G) a.2
      have hcomm : (b : G) * (x * (a : G) * x⁻¹) = (x * (a : G) * x⁻¹) * (b : G) :=
        (Subgroup.mem_centralizer_iff.mp b.2.2 (x * (a : G) * x⁻¹) hA'.1).symm
      simp only [Subgroup.coe_mul]
      calc ((a : G) * (b : G)) * (x * ((a : G) * (b : G)) * x⁻¹)
          = (a : G) * (b : G) * (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹) := by group
        _ = (a : G) * ((b : G) * (x * (a : G) * x⁻¹)) * (x * (b : G) * x⁻¹) := by group
        _ = (a : G) * ((x * (a : G) * x⁻¹) * (b : G)) * (x * (b : G) * x⁻¹) := by rw [hcomm]
        _ = ((a : G) * (x * (a : G) * x⁻¹)) * ((b : G) * (x * (b : G) * x⁻¹)) := by group }

private theorem centerConjHom_ker_le {S T : Subgroup G} {x : G}
    (hconjZ : ∀ a ∈ centerIn S, x * a * x⁻¹ ∈ centerIn S)
    (hexp : ∀ a ∈ centerIn S, a * a = 1)
    (hcenter_of : ∀ a ∈ centerIn S, x * a * x⁻¹ = a → a ∈ centerIn T) :
    (centerConjHom x hconjZ).ker.map (centerIn S).subtype ≤ centerIn T := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
  have haf : (a : G) * (x * (a : G) * x⁻¹) = 1 := by
    simpa [centerConjHom] using MonoidHom.mem_ker.mp ha
  have hxa : x * (a : G) * x⁻¹ = (a : G)⁻¹ :=
    (inv_eq_of_mul_eq_one_right haf).symm
  have hainv : (a : G)⁻¹ = (a : G) :=
    (eq_inv_of_mul_eq_one_left (hexp (a : G) a.2)).symm
  exact hcenter_of (a : G) a.2 (by rw [hxa, hainv])

private theorem centerConjHom_range_le {S T : Subgroup G} {x : G}
    (hcos : ∀ b ∈ T, b * x ∈ S ∨ b ∈ S)
    (hconjZ : ∀ a ∈ centerIn S, x * a * x⁻¹ ∈ centerIn S) (hx2S : x * x ∈ S)
    (hcenter_of : ∀ a ∈ centerIn S, x * a * x⁻¹ = a → a ∈ centerIn T) :
    (centerConjHom x hconjZ).range ≤ centerIn T := by
  rintro y ⟨a, rfl⟩
  have hA : (a : G) ∈ centerIn S := a.2
  have hA' : x * (a : G) * x⁻¹ ∈ centerIn S := hconjZ (a : G) a.2
  have hprod : (a : G) * (x * (a : G) * x⁻¹) ∈ centerIn S :=
    (centerIn S).mul_mem hA hA'
  have hxA : x * (x * (a : G) * x⁻¹) * x⁻¹ = (a : G) := by
    have h1 : (x * x) * (a : G) = (a : G) * (x * x) :=
      Subgroup.mem_centralizer_iff.mp hA.2 (x * x) hx2S
    calc x * (x * (a : G) * x⁻¹) * x⁻¹ = (x * x) * (a : G) * (x * x)⁻¹ := by group
      _ = (a : G) * (x * x) * (x * x)⁻¹ := by rw [h1]
      _ = (a : G) := by group
  have hxprod : x * ((a : G) * (x * (a : G) * x⁻¹)) * x⁻¹ =
      (a : G) * (x * (a : G) * x⁻¹) := by
    calc x * ((a : G) * (x * (a : G) * x⁻¹)) * x⁻¹
        = (x * (a : G) * x⁻¹) * (x * (x * (a : G) * x⁻¹) * x⁻¹) := by group
      _ = (x * (a : G) * x⁻¹) * (a : G) := by rw [hxA]
      _ = (a : G) * (x * (a : G) * x⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hA.2 (x * (a : G) * x⁻¹) hA'.1
  exact hcenter_of _ hprod hxprod

theorem card_centerIn_le_sq_of_relIndex_eq_two {S T : Subgroup G} (hST : S ≤ T)
    (h2 : S.relIndex T = 2) (hexp : ∀ a ∈ centerIn S, a * a = 1) :
    Nat.card (centerIn S) ≤ Nat.card (centerIn T) ^ 2 := by
  classical
  obtain ⟨x, hxT, hxS, hcos⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and).mp h2
  have hNT : T ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mp
      (Subgroup.normal_of_index_eq_two h2)
  have hconjZ : ∀ a ∈ centerIn S, x * a * x⁻¹ ∈ centerIn S :=
    fun a ha => conj_mem_centerIn_of_mem_normalizer (hNT hxT) ha
  have hx2S : x * x ∈ S := by
    rcases hcos x hxT with h | h
    · exact h
    · exact absurd h hxS
  have hcenter_of : ∀ a ∈ centerIn S, x * a * x⁻¹ = a → a ∈ centerIn T :=
    fun a ha hax => mem_centerIn_of_conj_eq hST hcos ha hax
  let f : centerIn S →* G := centerConjHom (S := S) x hconjZ
  have hker_le : f.ker.map (centerIn S).subtype ≤ centerIn T :=
    centerConjHom_ker_le hconjZ hexp hcenter_of
  have hrange_le : f.range ≤ centerIn T :=
    centerConjHom_range_le hcos hconjZ hx2S hcenter_of
  have hk : Nat.card f.ker ≤ Nat.card (centerIn T) := by
    rw [← Subgroup.card_map_of_injective (K := f.ker) (f := (centerIn S).subtype)
      (centerIn S).subtype_injective]
    exact Subgroup.card_le_of_le hker_le
  have hr : Nat.card f.range ≤ Nat.card (centerIn T) := Subgroup.card_le_of_le hrange_le
  calc Nat.card (centerIn S) = Nat.card f.ker * Nat.card f.range :=
        (Subgroup.card_ker_mul_card_range f).symm
    _ ≤ Nat.card (centerIn T) * Nat.card (centerIn T) := Nat.mul_le_mul hk hr
    _ = Nat.card (centerIn T) ^ 2 := by ring

theorem isSylowOf_centralizer_of_centerIn_eq_zpowers {b : G} (hz : orderOf z = 2)
    {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({z} : Set G) ⊓ centralizer ({b} : Set G)))
    (hZ : centerIn T = zpowers z) : IsSylowOf 2 T (centralizer ({b} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_forall_pElement_normalizer_le hT ?_
  intro g hgM hgN hgP
  have hgcenter : g ∈ Subgroup.normalizer (centerIn T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨conj_mem_centerIn_of_mem_normalizer hgN, fun ha => by
      have h := conj_mem_centerIn_of_mem_normalizer (Subgroup.inv_mem _ hgN) ha
      simpa [mul_assoc] using h⟩
  have hzcenter : z ∈ centerIn T := by rw [hZ]; exact Subgroup.mem_zpowers z
  have hgz_mem : g * z * g⁻¹ ∈ Subgroup.zpowers z := by
    have h := (Subgroup.mem_normalizer_iff.mp hgcenter z).mp hzcenter
    rwa [hZ] at h
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hgz_val : g * z * g⁻¹ = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgz_mem
    have hkmod : z ^ k = z ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k hz2
    have hord_conj : orderOf (g * z * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hkmod
      rw [← hk, hkmod, orderOf_one] at hord_conj
      norm_num at hord_conj
    · rw [h1, zpow_one] at hkmod
      rw [← hk, hkmod]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hgz_val]

private theorem card_centerIn_conjugate (D : Subgroup G) (h : G) :
    Nat.card (centerIn (CFSG.conjugate D h)) = Nat.card (centerIn D) := by
  rw [centerIn_conjugate, card_conjugate' (centerIn D) h]

private theorem exp_centerIn_conjugate {D : Subgroup G} (h : G)
    (hexp : ∀ x ∈ centerIn D, x * x = 1) :
    ∀ x ∈ centerIn (CFSG.conjugate D h), x * x = 1 := by
  intro x hx
  rw [centerIn_conjugate] at hx
  have hy : h * x * h⁻¹ ∈ centerIn D := mem_conjugate_iff.mp hx
  have hy2 : (h * x * h⁻¹) * (h * x * h⁻¹) = 1 := hexp _ hy
  calc x * x = h⁻¹ * ((h * x * h⁻¹) * (h * x * h⁻¹)) * h := by group
    _ = h⁻¹ * 1 * h := by rw [hy2]
    _ = 1 := by group

theorem conjugate_zpowers_ne_of_card_centerIn {a b : G} {Ta Tb : Subgroup G}
    (hTb : IsSylowOf 2 Tb (centralizer ({b} : Set G))) (hTa : IsPGroup 2 Ta)
    (hTaC : Ta ≤ centralizer ({a} : Set G)) (hcard : Nat.card Tb = 2 * Nat.card Ta)
    (hexp : ∀ x ∈ centerIn Ta, x * x = 1)
    (hlt : Nat.card (centerIn Tb) ^ 2 < Nat.card (centerIn Ta)) (g : G) :
    CFSG.conjugate (zpowers a) g ≠ zpowers b := by
  intro hconj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) g =
      Subgroup.centralizer ({b} : Set G) :=
    conjugate_centralizer_singleton_eq hconj
  have hTagC : CFSG.conjugate Ta g ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [← hcent]
    exact conjugate_le_conjugate' hTaC g
  have hTagP : IsPGroup 2 (CFSG.conjugate Ta g) := isPGroup_conjugate' hTa g
  obtain ⟨c, hc, hcS⟩ := exists_mem_conjugate_le_of_isSylowOf hTb hTagC hTagP
  let S : Subgroup G := CFSG.conjugate Ta (g * c)
  have hSle : S ≤ Tb := by
    change CFSG.conjugate Ta (g * c) ≤ Tb
    rw [← CFSG.LocalCores.conjugate_conjugate]
    exact hcS
  have hScard : Nat.card S = Nat.card Ta := card_conjugate' Ta (g * c)
  have hrel : S.relIndex Tb = 2 := by
    have hmul := Subgroup.relIndex_mul_card S Tb
    rw [inf_eq_left.mpr hSle, hScard, hcard] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hcardS : Nat.card (centerIn S) = Nat.card (centerIn Ta) :=
    card_centerIn_conjugate Ta (g * c)
  have hexpS : ∀ x ∈ centerIn S, x * x = 1 :=
    exp_centerIn_conjugate (g * c) hexp
  have hle := card_centerIn_le_sq_of_relIndex_eq_two hSle hrel hexpS
  rw [hcardS] at hle
  exact (not_le.mpr hlt) hle

private theorem mem_commutator_conjugate {Ta Tb : Subgroup G} {h x : G}
    (hx : x ∈ ⁅Ta, Ta⁆) (hSle : CFSG.conjugate Ta h ≤ Tb) :
    h⁻¹ * x * h ∈ ⁅Tb, Tb⁆ := by
  have hxS : h⁻¹ * x * h ∈ CFSG.conjugate (⁅Ta, Ta⁆) h := by
    have hx' : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [mem_conjugate_iff, hx']
  have hmap : CFSG.conjugate (⁅Ta, Ta⁆) h =
      ⁅CFSG.conjugate Ta h, CFSG.conjugate Ta h⁆ := by
    rw [CFSG.conjugate, Subgroup.map_commutator]
    rfl
  rw [hmap] at hxS
  exact Subgroup.commutator_mono hSle hSle hxS

private theorem inf_centralizer_le_conjugate_inf {a b y h : G} {Tb : Subgroup G}
    (hCb : CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) h =
      Subgroup.centralizer ({b} : Set G))
    (hCy : CFSG.conjugate (Subgroup.centralizer ({z} : Set G)) h =
      Subgroup.centralizer ({y} : Set G))
    (hTb : Tb ≤ Subgroup.centralizer ({b} : Set G)) :
    Tb ⊓ Subgroup.centralizer ({y} : Set G) ≤
      CFSG.conjugate (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({a} : Set G)) h := by
  intro x hx
  obtain ⟨hxTb, hxCy⟩ := hx
  have hxCb : x ∈ Subgroup.centralizer ({b} : Set G) := hTb hxTb
  have hx'a : h * x * h⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    have hx' : x ∈ CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) h := by
      rw [hCb]; exact hxCb
    exact mem_conjugate_iff.mp hx'
  have hx'z : h * x * h⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    have hx' : x ∈ CFSG.conjugate (Subgroup.centralizer ({z} : Set G)) h := by
      rw [hCy]; exact hxCy
    exact mem_conjugate_iff.mp hx'
  exact mem_conjugate_iff.mpr ⟨hx'z, hx'a⟩

private theorem card_le_of_le_conjugate_isSylowOf {K Ta R : Subgroup G} {h : G}
    (hTa : IsSylowOf 2 Ta K) (hR : R ≤ CFSG.conjugate K h)
    (hRp : IsPGroup 2 R) : Nat.card R ≤ Nat.card Ta := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowOf 2 (CFSG.conjugate Ta h) (CFSG.conjugate K h) :=
    isSylowOf_conjugate hTa h
  obtain ⟨k, hk, hkR⟩ := exists_mem_conjugate_le_of_isSylowOf hSyl hR hRp
  calc Nat.card R = Nat.card ↥(CFSG.conjugate R k) := (card_conjugate' R k).symm
    _ ≤ Nat.card ↥(CFSG.conjugate Ta h) := Subgroup.card_le_of_le hkR
    _ = Nat.card Ta := card_conjugate' Ta h

theorem conjugate_zpowers_ne_of_mem_commutator {a b : G} {Ta Tb : Subgroup G}
    (hTb : IsSylowOf 2 Tb (centralizer ({b} : Set G)))
    (hTa : IsSylowOf 2 Ta (centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G)))
    (hz : z ∈ ⁅Ta, Ta⁆)
    (hlt : ∀ y : G, y ∈ ⁅Tb ⊓ centralizer ({y} : Set G), Tb ⊓ centralizer ({y} : Set G)⁆ →
      Nat.card Ta < Nat.card ↥(Tb ⊓ centralizer ({y} : Set G)))
    (g : G) : CFSG.conjugate (zpowers a) g ≠ zpowers b := by
  intro hconj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) g =
      Subgroup.centralizer ({b} : Set G) :=
    conjugate_centralizer_singleton_eq hconj
  have hTagC : CFSG.conjugate Ta g ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [← hcent]
    exact conjugate_le_conjugate' (hTa.le.trans inf_le_right) g
  have hTagP : IsPGroup 2 (CFSG.conjugate Ta g) := isPGroup_conjugate' hTa.isPGroup g
  obtain ⟨c, hc, hcS⟩ := exists_mem_conjugate_le_of_isSylowOf hTb hTagC hTagP
  let h : G := g * c
  have hSle : CFSG.conjugate Ta h ≤ Tb := by
    change CFSG.conjugate Ta (g * c) ≤ Tb
    rw [← CFSG.LocalCores.conjugate_conjugate]
    exact hcS
  let y : G := h⁻¹ * z * h
  have hy_eq : y = h⁻¹ * z * h := rfl
  have hCb : CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) h =
      Subgroup.centralizer ({b} : Set G) := by
    change CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) (g * c) =
      Subgroup.centralizer ({b} : Set G)
    rw [← CFSG.LocalCores.conjugate_conjugate, hcent]
    exact conjugate_of_mem hc
  have hCy : CFSG.conjugate (Subgroup.centralizer ({z} : Set G)) h =
      Subgroup.centralizer ({y} : Set G) := by
    rw [hy_eq]
    exact conjugate_centralizer_singleton z h
  have hSle' : CFSG.conjugate Ta h ≤ Tb ⊓ centralizer ({y} : Set G) :=
    le_inf hSle (by
      rw [← hCy]
      exact conjugate_le_conjugate' (hTa.le.trans inf_le_left) h)
  have hy' : y ∈ ⁅Tb ⊓ centralizer ({y} : Set G), Tb ⊓ centralizer ({y} : Set G)⁆ := by
    rw [hy_eq]
    exact mem_commutator_conjugate hz hSle'
  have hRle : Tb ⊓ Subgroup.centralizer ({y} : Set G) ≤
      CFSG.conjugate (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ({a} : Set G)) h :=
    inf_centralizer_le_conjugate_inf hCb hCy hTb.le
  have hRp : IsPGroup 2 ↥(Tb ⊓ Subgroup.centralizer ({y} : Set G)) :=
    IsPGroup.to_le (K := Tb) hTb.isPGroup inf_le_left
  have hcard_le : Nat.card ↥(Tb ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      Nat.card Ta :=
    card_le_of_le_conjugate_isSylowOf hTa hRle hRp
  exact (not_le.mpr (hlt y hy')) hcard_le

theorem conjugate_zpowers_ne_of_elementaryAbelian {a b : G} {Ta E : Subgroup G}
    (hTa : IsSylowOf 2 Ta (centralizer ({a} : Set G)))
    (hnoE : ∀ F : Subgroup G, F ≤ Ta → Nat.card F = 16 →
      ¬ ((∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1))
    (hEb : E ≤ centralizer ({b} : Set G)) (hEc : Nat.card E = 16)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1) (g : G) :
    CFSG.conjugate (zpowers a) g ≠ zpowers b := by
  intro hconj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) g =
      Subgroup.centralizer ({b} : Set G) :=
    conjugate_centralizer_singleton_eq hconj
  have hcent_inv : Subgroup.centralizer ({a} : Set G) =
      CFSG.conjugate (Subgroup.centralizer ({b} : Set G)) g⁻¹ := by
    have h := congrArg (fun P => CFSG.conjugate P g⁻¹) hcent
    rwa [CFSG.LocalCores.conjugate_conjugate, mul_inv_cancel, conjugate_one'] at h
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hEc]; norm_num)
  have hF0C : CFSG.conjugate E g⁻¹ ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hcent_inv]
    exact conjugate_le_conjugate' hEb g⁻¹
  have hF0p : IsPGroup 2 (CFSG.conjugate E g⁻¹) := isPGroup_conjugate' hEp g⁻¹
  obtain ⟨c, hc, hcF⟩ := exists_mem_conjugate_le_of_isSylowOf hTa hF0C hF0p
  let F : Subgroup G := CFSG.conjugate (CFSG.conjugate E g⁻¹) c
  have hFle : F ≤ Ta := hcF
  have hFcard : Nat.card F = 16 := by
    rw [show F = CFSG.conjugate (CFSG.conjugate E g⁻¹) c from rfl,
      card_conjugate' (CFSG.conjugate E g⁻¹) c, card_conjugate' E g⁻¹, hEc]
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := isElementaryAbelian_of_forall hEab hE2
  have hFel : CFSG.IsElementaryAbelian 2 ↥F :=
    isElementaryAbelian_conjugate (isElementaryAbelian_conjugate hEel g⁻¹) c
  exact hnoE F hFle hFcard (forall_of_isElementaryAbelian hFel)

theorem star_of_orderThree_classes {σ a b : G}
    (hcls : ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ h ∈ H z, CFSG.conjugate R h = zpowers σ ∨ CFSG.conjugate R h = zpowers a ∨
        CFSG.conjugate R h = zpowers b)
    (hσ : orderOf σ = 3)
    (ha : ∀ g : G, CFSG.conjugate (zpowers σ) g ≠ zpowers a)
    (hb : ∀ g : G, CFSG.conjugate (zpowers σ) g ≠ zpowers b) :
    ∀ g : G, CFSG.conjugate (zpowers σ) g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (zpowers σ) g = CFSG.conjugate (zpowers σ) h := by
  intro g hg
  have hRcard : Nat.card (CFSG.conjugate (Subgroup.zpowers σ) g) = 3 := by
    rw [card_conjugate', Nat.card_zpowers, hσ]
  obtain ⟨h, hhH, hheq⟩ := hcls _ hg hRcard
  have hgh : CFSG.conjugate (CFSG.conjugate (Subgroup.zpowers σ) g) h =
      CFSG.conjugate (Subgroup.zpowers σ) (g * h) :=
    CFSG.LocalCores.conjugate_conjugate (Subgroup.zpowers σ) g h
  rcases hheq with h1 | h1 | h1
  · refine ⟨h⁻¹, (H z).inv_mem hhH, ?_⟩
    have hghσ : CFSG.conjugate (Subgroup.zpowers σ) (g * h) = Subgroup.zpowers σ := by
      rw [← hgh, h1]
    have hkey : CFSG.conjugate (CFSG.conjugate (Subgroup.zpowers σ) (g * h)) h⁻¹ =
        CFSG.conjugate (Subgroup.zpowers σ) g := by
      rw [CFSG.LocalCores.conjugate_conjugate]
      congr 1
      group
    calc CFSG.conjugate (Subgroup.zpowers σ) g
        = CFSG.conjugate (CFSG.conjugate (Subgroup.zpowers σ) (g * h)) h⁻¹ := hkey.symm
      _ = CFSG.conjugate (Subgroup.zpowers σ) h⁻¹ := by rw [hghσ]
  · exfalso
    have hghσ : CFSG.conjugate (Subgroup.zpowers σ) (g * h) = Subgroup.zpowers a := by
      rw [← hgh, h1]
    exact ha (g * h) hghσ
  · exfalso
    have hghσ : CFSG.conjugate (Subgroup.zpowers σ) (g * h) = Subgroup.zpowers b := by
      rw [← hgh, h1]
    exact hb (g * h) hghσ

private theorem conj_eq_or_inv_of_mem_normalizer_zpowers {σ n : G} (hσ : orderOf σ = 3)
    (hn : n ∈ normalizer (zpowers σ : Set G)) :
    n * σ * n⁻¹ = σ ∨ n * σ * n⁻¹ = σ⁻¹ := by
  have hσ3 : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  have hσ2 : σ ^ 2 = σ⁻¹ := by
    have h2 : σ ^ 2 * σ = 1 := by
      calc σ ^ 2 * σ = σ ^ 3 := by group
        _ = 1 := hσ3
    exact eq_inv_of_mul_eq_one_left h2
  have hnσ : n * σ * n⁻¹ ∈ Subgroup.zpowers σ :=
    (Subgroup.mem_normalizer_iff.mp hn σ).mp (Subgroup.mem_zpowers σ)
  have hord : orderOf (n * σ * n⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hσ]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnσ
  have hkmod : n * σ * n⁻¹ = σ ^ (k % (3 : ℤ)) := by
    rw [← hk]
    exact zpow_eq_zpow_emod' k hσ3
  have hk3 : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by
    have h0 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
    have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hk3 with h | h | h
  · rw [h, zpow_zero] at hkmod
    rw [hkmod, orderOf_one] at hord
    norm_num at hord
  · left
    rwa [h, zpow_one] at hkmod
  · right
    rw [h] at hkmod
    have hσ2z : σ ^ (2 : ℤ) = σ⁻¹ := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact hσ2
    exact hkmod.trans hσ2z

private theorem mem_centralizer_zpowers_of_conj_eq {σ c : G} (h : c * σ * c⁻¹ = σ) :
    c ∈ centralizer (zpowers σ : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hcomm : Commute c σ := by
    show c * σ = σ * c
    calc c * σ = (c * σ * c⁻¹) * c := by group
      _ = σ * c := by rw [h]
  exact (Commute.zpow_right hcomm k).eq.symm

theorem normalizer_zpowers_eq_mul_of_inv {σ w : G} (hσ : orderOf σ = 3) (hwH : w ∈ H z)
    (hw : w * σ * w⁻¹ = σ⁻¹) :
    ∀ n ∈ normalizer (zpowers σ : Set G), ∃ h ∈ normalizer (zpowers σ : Set G) ⊓ H z,
      ∃ c ∈ centralizer (zpowers σ : Set G), h * c = n := by
  intro n hn
  rcases conj_eq_or_inv_of_mem_normalizer_zpowers hσ hn with hτ | hτ
  · refine ⟨1, ?_, n, mem_centralizer_zpowers_of_conj_eq hτ, by simp⟩
    rw [Subgroup.mem_inf]
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  · have hwN : w ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
      change Subgroup.zpowers (MulAut.conj w σ) = Subgroup.zpowers σ
      rw [MulAut.conj_apply, hw, Subgroup.zpowers_inv]
    have hw' : w⁻¹ * σ⁻¹ * w = σ := by
      calc w⁻¹ * σ⁻¹ * w = w⁻¹ * (w * σ * w⁻¹) * w := by rw [hw]
        _ = σ := by group
    have hcσ : (w⁻¹ * n) * σ * (w⁻¹ * n)⁻¹ = σ := by
      calc (w⁻¹ * n) * σ * (w⁻¹ * n)⁻¹ = w⁻¹ * (n * σ * n⁻¹) * w := by group
        _ = w⁻¹ * σ⁻¹ * w := by rw [hτ]
        _ = σ := hw'
    refine ⟨w, ?_, w⁻¹ * n, mem_centralizer_zpowers_of_conj_eq hcσ, by group⟩
    rw [Subgroup.mem_inf]
    exact ⟨hwN, hwH⟩

theorem exists_centralizer_conj_of_isConj {σ w : G} (hσ : orderOf σ = 3) (hσH : σ ∈ H z)
    (hstar : ∀ g : G, CFSG.conjugate (zpowers σ) g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (zpowers σ) g = CFSG.conjugate (zpowers σ) h)
    (hwH : w ∈ H z) (hw : w * σ * w⁻¹ = σ⁻¹)
    {t : G} (ht2 : orderOf t = 2) (htH : t ∈ H z) (htσ : t ∈ centralizer ({σ} : Set G))
    (hzt : IsConj z t) :
    ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z := by
  have hP : IsPGroup 3 (Subgroup.zpowers σ) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hσ, pow_one]
  have hPne : Subgroup.zpowers σ ≠ ⊥ := by
    rw [Subgroup.zpowers_ne_bot]
    intro h1
    rw [h1, orderOf_one] at hσ
    norm_num at hσ
  have hPH : Subgroup.zpowers σ ≤ H z := Subgroup.zpowers_le_of_mem hσH
  have hN := normalizer_zpowers_eq_mul_of_inv hσ hwH hw
  have htP : ∀ x ∈ Subgroup.zpowers σ, t * x = x * t := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute t σ := Subgroup.mem_centralizer_singleton_iff.mp htσ
    exact (Commute.zpow_right hcomm k).eq
  obtain ⟨c, hc⟩ := isConj_iff.mp hzt
  have hconj : ∃ g : G, g⁻¹ * t * g = z :=
    ⟨c, by rw [← hc]; group⟩
  obtain ⟨c, hcP, hc⟩ :=
    (prop4_fusion_centralizer Nat.prime_three (by norm_num) hP hPne hPH hstar hN ht2 htH
      htP).mp hconj
  exact ⟨c, by rwa [centralizer_zpowers_eq] at hcP, hc⟩

theorem lemma53 (h : Tim79a.ParrottHyp z) {σ₁ σ σ₃ : G} {T₁ T₂ T₃ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ centralizer ({σ₁} : Set G))) (hT₁c : Nat.card T₁ = 2 ^ 7)
    (hZ₁ : Nat.card (centerIn T₁) = 8) (hZ₁e : ∀ x ∈ centerIn T₁, x * x = 1)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G))) (hT₂c : Nat.card T₂ = 2 ^ 8)
    (hZ₂ : centerIn T₂ = zpowers z)
    (hT₃ : IsSylowOf 2 T₃ (H z ⊓ centralizer ({σ₃} : Set G))) (hz₃ : z ∈ ⁅T₃, T₃⁆)
    (hT₂₃ : ∀ y : G, y ∈ ⁅T₂ ⊓ centralizer ({y} : Set G), T₂ ⊓ centralizer ({y} : Set G)⁆ →
      Nat.card T₃ < Nat.card ↥(T₂ ⊓ centralizer ({y} : Set G))) :
    IsSylowOf 2 T₂ (centralizer ({σ} : Set G)) ∧
      (∀ g : G, CFSG.conjugate (zpowers σ) g ≠ zpowers σ₁) ∧
      (∀ g : G, CFSG.conjugate (zpowers σ) g ≠ zpowers σ₃) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₂syl : IsSylowOf 2 T₂ (centralizer ({σ} : Set G)) :=
    isSylowOf_centralizer_of_centerIn_eq_zpowers h.1 hT₂ hZ₂
  have hcard : Nat.card T₂ = 2 * Nat.card T₁ := by
    rw [hT₂c, hT₁c]
    norm_num
  have hlt : Nat.card (centerIn T₂) ^ 2 < Nat.card (centerIn T₁) := by
    rw [hZ₂, Nat.card_zpowers, h.1, hZ₁]
    norm_num
  have hne₁ : ∀ g : G, CFSG.conjugate (Subgroup.zpowers σ₁) g ≠ Subgroup.zpowers σ :=
    conjugate_zpowers_ne_of_card_centerIn hT₂syl hT₁.isPGroup
      (hT₁.le.trans inf_le_right) hcard hZ₁e hlt
  have hne₃ : ∀ g : G, CFSG.conjugate (Subgroup.zpowers σ₃) g ≠ Subgroup.zpowers σ :=
    conjugate_zpowers_ne_of_mem_commutator hT₂syl hT₃ hz₃ hT₂₃
  have h₁ : ∀ g : G, CFSG.conjugate (Subgroup.zpowers σ) g ≠ Subgroup.zpowers σ₁ := by
    intro g hg
    have h' : Subgroup.zpowers σ = CFSG.conjugate (Subgroup.zpowers σ₁) g⁻¹ := by
      have h := congrArg (fun P => CFSG.conjugate P g⁻¹) hg
      rwa [CFSG.LocalCores.conjugate_conjugate, mul_inv_cancel, conjugate_one'] at h
    exact hne₁ g⁻¹ h'.symm
  have h₃ : ∀ g : G, CFSG.conjugate (Subgroup.zpowers σ) g ≠ Subgroup.zpowers σ₃ := by
    intro g hg
    have h' : Subgroup.zpowers σ = CFSG.conjugate (Subgroup.zpowers σ₃) g⁻¹ := by
      have h := congrArg (fun P => CFSG.conjugate P g⁻¹) hg
      rwa [CFSG.LocalCores.conjugate_conjugate, mul_inv_cancel, conjugate_one'] at h
    exact hne₃ g⁻¹ h'.symm
  exact ⟨hT₂syl, h₁, h₃⟩

theorem exists_centralizer_sigma_conj (h : Tim79a.ParrottHyp z) {σ₁ σ σ₃ w : G}
    {T₁ T₂ T₃ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ centralizer ({σ₁} : Set G))) (hT₁c : Nat.card T₁ = 2 ^ 7)
    (hZ₁ : Nat.card (centerIn T₁) = 8) (hZ₁e : ∀ x ∈ centerIn T₁, x * x = 1)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ centralizer ({σ} : Set G))) (hT₂c : Nat.card T₂ = 2 ^ 8)
    (hZ₂ : centerIn T₂ = zpowers z)
    (hT₃ : IsSylowOf 2 T₃ (H z ⊓ centralizer ({σ₃} : Set G))) (hz₃ : z ∈ ⁅T₃, T₃⁆)
    (hT₂₃ : ∀ y : G, y ∈ ⁅T₂ ⊓ centralizer ({y} : Set G), T₂ ⊓ centralizer ({y} : Set G)⁆ →
      Nat.card T₃ < Nat.card ↥(T₂ ⊓ centralizer ({y} : Set G)))
    (hσ : orderOf σ = 3) (hσH : σ ∈ H z)
    (hcls : ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ h ∈ H z, CFSG.conjugate R h = zpowers σ₁ ∨ CFSG.conjugate R h = zpowers σ ∨
        CFSG.conjugate R h = zpowers σ₃)
    (hwH : w ∈ H z) (hw : w * σ * w⁻¹ = σ⁻¹)
    {t : G} (ht2 : orderOf t = 2) (htH : t ∈ H z) (htσ : t ∈ centralizer ({σ} : Set G))
    (hzt : IsConj z t) :
    ∃ c ∈ centralizer ({σ} : Set G), c * t * c⁻¹ = z := by
  obtain ⟨-, h₁, h₃⟩ :=
    lemma53 h hT₁ hT₁c hZ₁ hZ₁e hT₂ hT₂c hZ₂ hT₃ hz₃ hT₂₃
  have hcls' : ∀ R : Subgroup G, R ≤ H z → Nat.card R = 3 →
      ∃ h ∈ H z, CFSG.conjugate R h = zpowers σ ∨ CFSG.conjugate R h = zpowers σ₁ ∨
        CFSG.conjugate R h = zpowers σ₃ := by
    intro R hR hRcard
    obtain ⟨h, hh, hcase⟩ := hcls R hR hRcard
    refine ⟨h, hh, ?_⟩
    rcases hcase with h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  have hstar := star_of_orderThree_classes hcls' hσ h₁ h₃
  exact exists_centralizer_conj_of_isConj hσ hσH hstar hwH hw ht2 htH htσ hzt

end CFSG.RankThree.GF2n.Parrott
