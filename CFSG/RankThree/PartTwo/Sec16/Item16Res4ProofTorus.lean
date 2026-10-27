module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofEnd
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTorus
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofGen
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofQL
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec21.Item223Of
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec16.Item163Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Torus1619

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec15.Torus1519
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {π : Bool} {f : ℕ}

theorem dvd_qSubPi_of_sign {m r : ℕ} (hq : ModThree π (2 ^ m))
    (h2 : (2 : ZMod r) ^ m = sign1519 m r) : r ∣ qSubPi π (2 ^ m) := by
  cases π
  · change 2 ^ m % 3 = 2 at hq
    have hs : sign1519 m r = -1 := by simp [sign1519, hq]
    rw [hs] at h2
    change r ∣ 2 ^ m + 1
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [h2]
    ring
  · change 2 ^ m % 3 = 1 at hq
    have hs : sign1519 m r = 1 := by simp [sign1519, hq]
    rw [hs] at h2
    change r ∣ 2 ^ m - 1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow,
      Nat.cast_ofNat, h2, Nat.cast_one, sub_self]

@[expose] noncomputable def ehatT (r : ℕ) : Subgroup (GL (Fin 3) K) :=
  ((rootsOfUnity r K).prod (rootsOfUnity r K)).map torusHom

theorem ehatT_le_slPi {p : ℕ} {r : ℕ} (hK : PiField π p f K) (hr : r ∣ qSubPi π (p ^ f)) :
    ehatT (K := K) r ≤ slPi π 3 (p ^ f) K := by
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  exact torusHom_mem_slPi hK (rootsOfUnity_le_of_dvd hr ha) (rootsOfUnity_le_of_dvd hr hb)

theorem card_ehatT [Finite K] {r : ℕ} [NeZero r] (hr : r ∣ Nat.card K - 1) :
    Nat.card (ehatT (K := K) r) = r ^ 2 := by
  rw [ehatT, Subgroup.card_map_of_injective torusHom_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd hr, sq]

theorem isElemAbelian_ehatT (r : ℕ) : CFSG.Assembly.IsElemAbelian r (ehatT (K := K) r) := by
  have hc : IsMulCommutative ((rootsOfUnity r K).prod (rootsOfUnity r K)) :=
    ⟨⟨fun x y => Subtype.ext (mul_comm _ _)⟩⟩
  refine CFSG.SectionRank.isElemAbelian_map ⟨hc, fun x hx => ?_⟩ torusHom
  obtain ⟨ha, hb⟩ := hx
  exact Prod.ext ((mem_rootsOfUnity _ _).mp ha) ((mem_rootsOfUnity _ _).mp hb)

theorem cycThree_mem_normalizer_ehatT (r : ℕ) :
    cycThree ∈ Subgroup.normalizer (ehatT (K := K) r : Set (GL (Fin 3) K)) := by
  have key : ∀ x ∈ ehatT (K := K) r, cycThree * x * cycThree⁻¹ ∈ ehatT (K := K) r := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    rw [cycThree_conj_torusHom]
    exact ⟨((a * b)⁻¹, a), Subgroup.mem_prod.mpr ⟨inv_mem (mul_mem ha hb), ha⟩, rfl⟩
  have hord : cycThree ^ 3 = (1 : GL (Fin 3) K) := cycThree_pow_three
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key x, fun hx => ?_⟩
  have h2 := key _ (key _ hx)
  have e : cycThree * (cycThree * (cycThree * x * cycThree⁻¹) * cycThree⁻¹) * cycThree⁻¹ =
      (cycThree * cycThree * cycThree) * x * (cycThree * cycThree * cycThree)⁻¹ := by group
  rw [e, ← pow_three', hord, one_mul, inv_one, mul_one] at h2
  exact h2

theorem ehatT_inf_center {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    ehatT (K := K) r ⊓ Subgroup.center (GL (Fin 3) K) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, hz⟩
  rw [Subgroup.mem_bot]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨l, hl⟩ := hz
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hl
  simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_torusHom] at hm
  have h0 := congrFun (congrFun hm 0) 0
  have h1 := congrFun (congrFun hm 1) 1
  have h2 := congrFun (congrFun hm 2) 2
  simp [Matrix.scalar_apply] at h0 h1 h2
  have hab : a = b := Units.ext (h0.symm.trans h1)
  subst hab
  have ha3 : a ^ 3 = 1 := by
    apply Units.ext
    have : ((a * a)⁻¹ : Kˣ) = a := Units.ext (by simpa using h2.symm.trans h0)
    have h' : a * a * a = 1 := by
      calc a * a * a = a * a * (a * a)⁻¹ := by rw [this]
        _ = 1 := mul_inv_cancel _
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three', ← Units.val_mul, ← Units.val_mul, h',
      Units.val_one]
  have har : a ^ r = 1 := (mem_rootsOfUnity _ _).mp ha
  have hcop : Nat.Coprime r 3 := (Nat.coprime_primes hr Nat.prime_three).mpr hr3
  have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one har) (orderOf_dvd_of_pow_eq_one ha3))
  subst ha1
  exact map_one torusHom

theorem centralizer_diagTau_le_centralizer_ehat (hK : PiField π 2 f K)
    (hq : ModThree π (2 ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (r : ℕ) :
    slPi π 3 (2 ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} ≤
      Subgroup.centralizer (ehatT (K := K) r : Set (GL (Fin 3) K)) := by
  rw [centralizer_diagTau_eq hK hq hτ hτ1]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨⟨a', b'⟩, -, rfl⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.prodMap, MonoidHom.coe_prod,
    MonoidHom.coe_comp, Subgroup.coe_subtype]
  rw [← map_mul, ← map_mul, mul_comm]

theorem exists_torus_cent_aux (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f)) (hf : 1 ≤ f)
    {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hrd : r ∣ qSubPi π (2 ^ f))
    (L : Subgroup (GL (Fin 3) K)) (hL : L = slPi π 3 (2 ^ f) K)
    {D : Subgroup ↥(projImage L)} (hD : IsPGroup 3 D) (hD9 : Nat.card D = 9) :
    ∃ P : Subgroup ↥(projImage L),
      CFSG.Assembly.IsElemAbelian r P ∧ Nat.card P = r ^ 2 ∧
        D ≤ Subgroup.normalizer (P : Set _) ∧
        ∃ d ∈ D, d ≠ 1 ∧ P ≤ Subgroup.centralizer ({d} : Set _) := by
  subst hL
  have := hK.finite
  have : Finite (GL (Fin 3) K) := inferInstance
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  let L := slPi π 3 (2 ^ f) K
  set ρ : ↥L →* ↥(projImage L) :=
    (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).subgroupMap L with hρ
  have hρs : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
  have hρ1 : ∀ x : ↥L, ρ x = 1 → (x : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro x hx
    rw [← ProjGenLinGroup.mk_eq_one]
    exact congrArg Subtype.val hx
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  set C₀ := slPi π 3 (2 ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} with hC₀
  set M₀ := C₀ ⊔ Subgroup.zpowers cycThree with hM₀
  have hC₀M₀ : C₀ ≤ M₀ := le_sup_left
  have hML : M₀ ≤ L := sup_le inf_le_left (Subgroup.zpowers_le.mpr (cycThree_mem_slPi hπ))
  have hMc : M₀ ≤ centMod (slPi π 3 (2 ^ f) K) (diagTau hτ) :=
    sup_le (centralizer_le_centMod _ _) (Subgroup.zpowers_le.mpr (cycThree_mem_centMod hK hτ hτ1))
  have hmul' := Subgroup.relIndex_mul_relIndex C₀ M₀ _ hC₀M₀ hMc
  rw [relindex_centralizer_diagTau hK hq hτ hτ1] at hmul'
  have hdvd : C₀.relIndex M₀ ∣ 3 := Dvd.intro _ hmul'
  have hrel3 : C₀.relIndex M₀ = 3 := by
    have hne1 : C₀.relIndex M₀ ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle
      exact cycThree_not_mem_centralizer hτ hτ1
        (hle (le_sup_right (a := C₀) (Subgroup.mem_zpowers cycThree))).2
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have hcC₀ : Nat.card C₀ = qSubPi π (2 ^ f) ^ 2 := by
    obtain ⟨e⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have hz : Nat.card (Multiplicative (ZMod (qSubPi π (2 ^ f)))) = qSubPi π (2 ^ f) := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hz, sq]
  have hcM₀ : Nat.card M₀ = 3 * qSubPi π (2 ^ f) ^ 2 := by
    have hcard := Subgroup.card_mul_index (C₀.subgroupOf M₀)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC₀M₀).toEquiv] at hcard
    change Nat.card C₀ * C₀.relIndex M₀ = Nat.card M₀ at hcard
    rw [← hcard, hcC₀, hrel3, mul_comm]
  set C := C₀.subgroupOf L with hC
  set M := M₀.subgroupOf L with hM
  have hkerC : ρ.ker ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_subgroupOf]
    refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_center_iff.mp (hρ1 x hx) _).symm
  have hker : ρ.ker ≤ M := hkerC.trans fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hC₀M₀ (Subgroup.mem_subgroupOf.mp hx))
  have hidx : (M.map ρ).index = M.index := Subgroup.index_map_eq M hρs hker
  have hcM : Nat.card M = 3 * qSubPi π (2 ^ f) ^ 2 := by
    rw [hM, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv, hcM₀]
  have hmul : M.index * (3 * qSubPi π (2 ^ f) ^ 2) =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) := by
    rw [← hcM, mul_comm, Subgroup.card_mul_index]
    exact Sec13.card_slPi_three hK
  have h3 : ¬ 3 ∣ M.index :=
    not_three_dvd_of_mul_eq (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)) hq
      hmul
  have h3' : ¬ 3 ∣ (M.map ρ).index := by
    rw [hidx]
    exact h3
  obtain ⟨g, hg⟩ := exists_conj_map_le h3' hD
  have hrelbar : (C.map ρ).relIndex (M.map ρ) = C₀.relIndex M₀ := by
    rw [Subgroup.relIndex_map_map, sup_eq_left.mpr hkerC, sup_eq_left.mpr hker, hC, hM,
      Subgroup.relIndex_subgroupOf hML]
  have hD'9 : Nat.card (D.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hD9]
  have hne : (C.map ρ).relIndex (M.map ρ) ≠ 0 := by
    rw [hrelbar]
    intro h0
    rw [h0] at hdvd
    norm_num at hdvd
  have hle3 : (C.map ρ).relIndex (D.map (MulAut.conj g).toMonoidHom) ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hg hne).trans
      (hrelbar ▸ Nat.le_of_dvd (by norm_num) hdvd)
  have hcardinf :=
    Subgroup.relIndex_mul_card (H := C.map ρ) (K := D.map (MulAut.conj g).toMonoidHom)
  rw [hD'9] at hcardinf
  have hinf : 1 < Nat.card (C.map ρ ⊓ D.map (MulAut.conj g).toMonoidHom : Subgroup _) := by
    by_contra hle
    push Not at hle
    have := Nat.mul_le_mul hle3 hle
    omega
  obtain ⟨⟨d', hd'C, hd'D⟩, hd'1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot _).mp hinf)
  have hd'1' : d' ≠ 1 := fun h => hd'1 (Subtype.ext h)
  set Eh := (ehatT (K := K) r).subgroupOf L with hEh
  have hEL : ehatT (K := K) r ≤ L := ehatT_le_slPi hK hrd
  have hM₀E : M₀ ≤ Subgroup.normalizer (ehatT (K := K) r : Set (GL (Fin 3) K)) :=
    sup_le ((centralizer_diagTau_le_centralizer_ehat hK hq hτ hτ1 r).trans
      (Subgroup.centralizer_le_normalizer _))
      (Subgroup.zpowers_le.mpr (cycThree_mem_normalizer_ehatT r))
  have hME : M ≤ Subgroup.normalizer (Eh : Set ↥L) := by
    intro x hx
    have hxn := hM₀E (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hEh, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp hxn y)
  set E := Eh.map ρ with hE
  have hNE : M.map ρ ≤ Subgroup.normalizer (E : Set _) :=
    (Subgroup.map_mono hME).trans (Subgroup.le_normalizer_map ρ)
  have hCE : ∀ e ∈ E, e * d' = d' * e := by
    obtain ⟨x, hx, rfl⟩ := hd'C
    rintro _ ⟨y, hy, rfl⟩
    have hxy : (y : GL (Fin 3) K) * x = x * y :=
      Subgroup.mem_centralizer_iff.mp
        (centralizer_diagTau_le_centralizer_ehat hK hq hτ hτ1 r (Subgroup.mem_subgroupOf.mp hx))
        _ (Subgroup.mem_subgroupOf.mp hy)
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext hxy)
  obtain ⟨d, hdD, hdd'⟩ := hd'D
  refine ⟨E.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, d, hdD, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map
      (Proof1517.isElemAbelian_subgroupOf (isElemAbelian_ehatT r) L) ρ) _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE]
    rw [card_map_of_injOn ρ (H := Eh) fun x hx hx1 => ?_]
    · rw [hEh, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
      exact card_ehatT ((hrd.trans (qSubPi_dvd hK)))
    · have hz := ehatT_inf_center (K := K) hr hr3
      have hmem : (x : GL (Fin 3) K) ∈ ehatT (K := K) r ⊓ Subgroup.center (GL (Fin 3) K) :=
        ⟨Subgroup.mem_subgroupOf.mp hx, hρ1 x hx1⟩
      rw [hz, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
  · have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hg.trans hNE)
    rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_map] at h1
    have hid : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hid, Subgroup.map_id] at h1
  · rintro rfl
    apply hd'1'
    rw [← hdd', map_one]
  · rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := hCE e he
    rw [← hdd'] at hc
    have hc' := congrArg (MulAut.conj g⁻¹).toMonoidHom hc
    simp only [map_mul] at hc'
    have hgd : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom d) = d := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hgd] at hc'
    exact hc'

theorem exists_torus_cent (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f)) (hf : 1 ≤ f)
    {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hrd : r ∣ qSubPi π (2 ^ f))
    {D : Subgroup ↥(projImage (slPi π 3 (2 ^ f) K))} (hD : IsPGroup 3 D) (hD9 : Nat.card D = 9) :
    ∃ P : Subgroup ↥(projImage (slPi π 3 (2 ^ f) K)),
      CFSG.Assembly.IsElemAbelian r P ∧ Nat.card P = r ^ 2 ∧
        D ≤ Subgroup.normalizer (P : Set _) ∧
        ∃ d ∈ D, d ≠ 1 ∧ P ≤ Subgroup.centralizer ({d} : Set _) :=
  exists_torus_cent_aux hK hq hf hr hr3 hrd _ rfl hD hD9

theorem exists_torus_cent_of_isoLThreePi {X : Type} [Group X] [Finite X] {m p : ℕ}
    (hiso : Sec4.IsoLThreePi X 2 m) (hp : p.Prime) (hp3 : 3 < p)
    (hpm : (2 : ZMod p) ^ m = sign1519 m p) {D : Subgroup X}
    (_hDE : CFSG.Assembly.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    ∃ P : Subgroup X, CFSG.Assembly.IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
      D ≤ Subgroup.normalizer (P : Set X) ∧
      ∃ d ∈ D, d ≠ 1 ∧ P ≤ Subgroup.centralizer ({d} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exfalso
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨h2, -⟩
    · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 0)
      rw [Sec21.natCard_galoisField_two_zero, ← Nat.card_congr φ.toEquiv] at hc
      norm_num at hc
      have hdvd : 9 ∣ Nat.card X := hD9 ▸ Subgroup.card_subgroup_dvd_card D
      omega
    · norm_num at h2
  · obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hm hiso
    have hrd := dvd_qSubPi_of_sign hq hpm
    have hD3 : IsPGroup 3 (D.map φ.toMonoidHom) := IsPGroup.of_card (n := 2) (by
      rw [Subgroup.card_map_of_injective φ.injective, hD9]
      norm_num)
    have hD9' : Nat.card (D.map φ.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective φ.injective, hD9]
    obtain ⟨P, hPE, hPc, hDP, d, hdD, hd1, hPd⟩ :=
      exists_torus_cent hK hq hm hp (by omega) hrd hD3 hD9'
    obtain ⟨d₀, hd₀, rfl⟩ := hdD
    refine ⟨P.map φ.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hPE _,
      by rw [Subgroup.card_map_of_injective φ.symm.injective, hPc], ?_, d₀, hd₀, ?_, ?_⟩
    · have h1 := Subgroup.map_mono (f := φ.symm.toMonoidHom) hDP
      rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_map] at h1
      have hid : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by
        ext x
        simp
      rwa [hid, Subgroup.map_id] at h1
    · rintro rfl
      exact hd1 (map_one _)
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hPd hy)
      have hc' := congrArg φ.symm hc
      simp only [map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hc'
      exact hc'

end Torus1619

open Torus1619 Proof169Theta Proof1612Gen

theorem para1619At_of
    (h135 : Item135Simple) (h142 : Concl142R) : Para1619At := by
  intro G _ _ A c L h n hn _ _ _ p hp hp3 hpn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨hcL, h9, hAc⟩ := facts_of_isZ3LThreeTwo hD hn
  have hn1 : 1 ≤ n := hn.1
  have hiso := hn.2.1
  have hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨2, n, inferInstance, hn1, hiso⟩
  have hθ := theta_eq_pCore_two_of_item135Simple h135 hD (Or.inl hL3)
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  set Ab := (A.subgroupOf L).map π with hAb
  have hAb9 : Nat.card Ab = 9 := by
    rw [hAb, hπ, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hEab : CFSG.Assembly.IsElemAbelian 3 Ab :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π _
      (isElemAbelian_subgroupOf hD.isElemAbelian)
  obtain ⟨Pb, hPbE, hPb2, hAbPb, db, hdb, hdb1, hPbC⟩ :=
    exists_torus_cent_of_isoLThreePi hiso hp hp3 hpn hEab hAb9
  obtain ⟨⟨b, hbL⟩, hbA, rfl⟩ := hdb
  have hbA' : b ∈ A := Subgroup.mem_subgroupOf.mp hbA
  have hp2 : p ≠ 2 := by omega
  have hp3' : p ≠ 3 := by omega
  have hPb3 : ¬ 3 ∣ Nat.card Pb := by
    rw [hPb2]
    intro h3
    exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  obtain ⟨hKGL, hKG3', hAKG⟩ := Proof163L4A7.mem_invariantPiSubgroups_of_inner h.toSec15R hAc
    Pb hPb3 hAbPb
  set KG := (Pb.comap π).map L.subtype with hKG
  have hKG3 : ¬ 3 ∣ Nat.card KG := (isPiSubgroup_piCompl_iff Nat.prime_three KG).mp hKG3'
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨P, hPK, hPp, hAP, hPcard⟩ := Sec17.HeadProof.exists_invariant_sylow hA3 hKG3 hAKG hp
  have hPL : P ≤ L := hPK.trans hKGL
  have hPimg : ∀ x (hx : x ∈ P), π ⟨x, hPL hx⟩ ∈ Pb := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hPK hx
    have : (⟨x, hPL hx⟩ : ↥L) = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  have hinj : ∀ x (hx : x ∈ P), π ⟨x, hPL hx⟩ = 1 → x = 1 := by
    intro x hx h1
    have hxθ : (⟨x, hPL hx⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hθ, ← QuotientGroup.eq_one_iff]
      exact h1
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hxθ⟩
    obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
    have hxa : x ^ 2 ^ a = 1 := by
      simpa using congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) ha
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime (2 ^ a) (p ^ k) :=
      Nat.Coprime.pow a k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hxa) (orderOf_dvd_of_pow_eq_one hxk))
  have hinj' : ∀ x (hx : x ∈ P) y (hy : y ∈ P), π ⟨x, hPL hx⟩ = π ⟨y, hPL hy⟩ → x = y := by
    intro x hx y hy hxy
    have h1 : π ⟨x⁻¹ * y, hPL (mul_mem (inv_mem hx) hy)⟩ = 1 := by
      have e : (⟨x⁻¹ * y, hPL (mul_mem (inv_mem hx) hy)⟩ : ↥L) =
          (⟨x, hPL hx⟩ : ↥L)⁻¹ * ⟨y, hPL hy⟩ := rfl
      rw [e, map_mul, map_inv, hxy, inv_mul_cancel]
    have := hinj _ (mul_mem (inv_mem hx) hy) h1
    rw [inv_mul_eq_one] at this
    exact this
  have hPle : Nat.card P ≤ p ^ 2 := by
    rw [← hPb2]
    refine Nat.card_le_card_of_injective (fun x : P => (⟨π ⟨x, hPL x.2⟩, hPimg x x.2⟩ : Pb))
      fun x y hxy => Subtype.ext (hinj' x x.2 y y.2 (congrArg Subtype.val hxy))
  have hdvdK : p ^ 2 ∣ Nat.card KG := by
    rw [hKG, Subgroup.card_map_of_injective L.subtype_injective, ← hPb2]
    have hmap := Subgroup.map_comap_eq_self_of_surjective hπs Pb
    have hd := Subgroup.card_map_dvd (Pb.comap π) π
    rwa [hmap] at hd
  have hfac : 2 ≤ (Nat.card KG).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvdK
  have hPcard2 : Nat.card P = p ^ 2 := by
    refine le_antisymm hPle ?_
    rw [hPcard]
    exact Nat.pow_le_pow_right hp.pos hfac
  have hPE : CFSG.Assembly.IsElemAbelian p P := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hx := x.2
      have hy := y.2
      refine hinj' _ (mul_mem hx hy) _ (mul_mem hy hx) ?_
      have hc := congrArg Subtype.val
        (isMulCommutative_iff.mp hPbE.1 ⟨_, hPimg x hx⟩ ⟨_, hPimg y hy⟩)
      simp only [Subgroup.coe_mul] at hc
      rw [← map_mul, ← map_mul] at hc
      exact hc
    · refine hinj _ (pow_mem hx p) ?_
      have e : (⟨x ^ p, hPL (pow_mem hx p)⟩ : ↥L) = (⟨x, hPL hx⟩ : ↥L) ^ p := rfl
      rw [e, map_pow]
      exact hPbE.2 _ (hPimg x hx)
  have hPb : P ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy : b * x * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hAP hbA') x).mp hx
    have hxy := hinj' _ hy _ hx (by
      have e : (⟨b * x * b⁻¹, hPL hy⟩ : ↥L) = ⟨b, hbL⟩ * ⟨x, hPL hx⟩ * (⟨b, hbL⟩ : ↥L)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hPbC (hPimg x hx))
      rw [← hc, mul_inv_cancel_right])
    calc x * b = (b * x * b⁻¹) * b := by rw [hxy]
      _ = b * x := by group
  have hbc : b ∉ Subgroup.zpowers c := by
    intro hbc
    have hb1 : b ∈ L ⊓ Subgroup.zpowers c := ⟨hbL, hbc⟩
    rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL,
      Subgroup.mem_bot] at hb1
    apply hdb1
    have : (⟨b, hbL⟩ : ↥L) = 1 := Subtype.ext hb1
    rw [this, map_one]
  have hP3 : ¬ 3 ∣ Nat.card P := by
    rw [hPcard2]
    intro h3
    exact hp3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hPQ : P ∈ scriptQ A (lB A) := mem_scriptQ_of_concl142 (h142 G A c L h.toSec15R)
    h.zpowers_mem_omegaA ⟨hPL.trans (h.le_centralizer.trans
      (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr hP3, hAP⟩
  exact ⟨b, P, ⟨hbA', hbL, hbc, hn, hp, hp3, hpn,
    ⟨⟨hPQ, le_inf hPL hPb⟩, (isPiSubgroup_piOf_iff hp P).mpr hPp⟩, hPE, hPcard2⟩⟩

end CFSG.RankThree.PartTwo.Sec16
