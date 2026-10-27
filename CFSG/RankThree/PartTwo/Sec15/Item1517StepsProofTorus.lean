module

import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec21.Item223Of
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec15.Item15Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Proof1517

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian p A) (L : Subgroup G) :
    CFSG.Assembly.IsElemAbelian p (A.subgroupOf L) := CFSG.Open.IsElemAbelian.subgroupOf hA L

end Proof1517

namespace Torus1519

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

noncomputable def ehat (r : ℕ) : Subgroup (GL (Fin 3) K) :=
  ((rootsOfUnity r K).prod (rootsOfUnity r K)).map torusHom

theorem ehat_le_slPi {π : Bool} {p f r : ℕ} (hK : PiField π p f K) (hr : r ∣ qSubPi π (p ^ f)) :
    ehat (K := K) r ≤ slPi π 3 (p ^ f) K := by
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  exact torusHom_mem_slPi hK (rootsOfUnity_le_of_dvd hr ha) (rootsOfUnity_le_of_dvd hr hb)

theorem card_ehat [Finite K] {r : ℕ} [NeZero r] (hr : r ∣ Nat.card K - 1) :
    Nat.card (ehat (K := K) r) = r ^ 2 := by
  rw [ehat, Subgroup.card_map_of_injective torusHom_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd hr, sq]

theorem isElemAbelian_ehat (r : ℕ) : CFSG.Assembly.IsElemAbelian r (ehat (K := K) r) := by
  have hc : IsMulCommutative ((rootsOfUnity r K).prod (rootsOfUnity r K)) :=
    ⟨⟨fun x y => Subtype.ext (mul_comm _ _)⟩⟩
  refine CFSG.SectionRank.isElemAbelian_map ⟨hc, fun x hx => ?_⟩ torusHom
  obtain ⟨ha, hb⟩ := hx
  exact Prod.ext ((mem_rootsOfUnity _ _).mp ha) ((mem_rootsOfUnity _ _).mp hb)

theorem cycThree_conj_torusHom (a b : Kˣ) :
    cycThree * torusHom (a, b) * cycThree⁻¹ = torusHom ((a * b)⁻¹, a) := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [show ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, 1, 0; 0, 0, 1; 1, 0, 0] from rfl, coe_cycThree, coe_torusHom, coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal, mul_comm]

theorem cycThree_mem_normalizer_ehat (r : ℕ) :
    cycThree ∈ Subgroup.normalizer (ehat (K := K) r : Set (GL (Fin 3) K)) := by
  have key : ∀ x ∈ ehat (K := K) r, cycThree * x * cycThree⁻¹ ∈ ehat (K := K) r := by
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

theorem ehat_inf_center {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    ehat (K := K) r ⊓ Subgroup.center (GL (Fin 3) K) = ⊥ := by
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

theorem dvd_qSubPi_of_isChoice1519 {π : Bool} {m r : ℕ} (hq : ModThree π (2 ^ m))
    (hr : IsChoice1519 m r) : r ∣ qSubPi π (2 ^ m) := by
  obtain ⟨-, h2, -⟩ := hr
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
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat,
      h2, Nat.cast_one, sub_self]

theorem not_three_dvd_of_mul_eq {π : Bool} {q n : ℕ} (hq2 : 2 ≤ q) (hq : ModThree π q)
    (h : n * (3 * qSubPi π q ^ 2) = q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1)) :
    ¬ 3 ∣ n := by
  cases π
  · change q % 3 = 2 at hq
    change n * (3 * (q + 1) ^ 2) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) at h
    obtain ⟨u, rfl⟩ : ∃ u, q = 3 * u + 2 := ⟨q / 3, by omega⟩
    have e1 : (3 * u + 2) ^ 2 - 1 = (3 * u + 1) * (3 * u + 3) := by
      have : (3 * u + 2) ^ 2 = (3 * u + 1) * (3 * u + 3) + 1 := by ring
      omega
    have e2 : (3 * u + 2) ^ 3 + 1 = (3 * u + 3) * (3 * (3 * u ^ 2 + 3 * u + 1)) := by ring
    rw [e1, e2] at h
    have h' : n * 3 * (3 * u + 3) ^ 2 =
        3 * ((3 * u + 2) ^ 3 * (3 * u + 1) * (3 * u ^ 2 + 3 * u + 1)) * (3 * u + 3) ^ 2 := by
      have : (3 * u + 2 + 1) = 3 * u + 3 := by ring
      rw [this] at h
      linarith [h]
    have h3 : n * 3 = 3 * ((3 * u + 2) ^ 3 * (3 * u + 1) * (3 * u ^ 2 + 3 * u + 1)) :=
      Nat.eq_of_mul_eq_mul_right (by positivity) h'
    have hn : n = (3 * u + 2) ^ 3 * (3 * u + 1) * (3 * u ^ 2 + 3 * u + 1) := by omega
    rw [hn]
    intro hd
    have := (Nat.dvd_iff_mod_eq_zero ..).mp hd
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod] at this
  · change q % 3 = 1 at hq
    change n * (3 * (q - 1) ^ 2) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) at h
    obtain ⟨u, rfl⟩ : ∃ u, q = 3 * u + 1 := ⟨q / 3, by omega⟩
    have hu : 1 ≤ u := by omega
    have e0 : 3 * u + 1 - 1 = 3 * u := by omega
    have e1 : (3 * u + 1) ^ 2 - 1 = (3 * u) * (3 * u + 2) := by
      have : (3 * u + 1) ^ 2 = (3 * u) * (3 * u + 2) + 1 := by ring
      omega
    have e2 : (3 * u + 1) ^ 3 - 1 = (3 * u) * (3 * (3 * u ^ 2 + 3 * u + 1)) := by
      have : (3 * u + 1) ^ 3 = (3 * u) * (3 * (3 * u ^ 2 + 3 * u + 1)) + 1 := by ring
      omega
    rw [e0, e1, e2] at h
    have h' : n * 3 * (3 * u) ^ 2 =
        3 * ((3 * u + 1) ^ 3 * (3 * u + 2) * (3 * u ^ 2 + 3 * u + 1)) * (3 * u) ^ 2 := by
      linarith [h]
    have h3 : n * 3 = 3 * ((3 * u + 1) ^ 3 * (3 * u + 2) * (3 * u ^ 2 + 3 * u + 1)) :=
      Nat.eq_of_mul_eq_mul_right (by positivity) h'
    have hn : n = (3 * u + 1) ^ 3 * (3 * u + 2) * (3 * u ^ 2 + 3 * u + 1) := by omega
    rw [hn]
    intro hd
    have := (Nat.dvd_iff_mod_eq_zero ..).mp hd
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod] at this

section Normalizer

variable {π : Bool} {p f : ℕ}

noncomputable def mhat (π : Bool) (q : ℕ) (K : Type) [Field K] {τ : K} (hτ : τ ^ 3 = 1) :
    Subgroup (GL (Fin 3) K) :=
  (slPi π 3 q K ⊓ Subgroup.centralizer {diagTau hτ}) ⊔ Subgroup.zpowers cycThree

theorem mhat_le_slPi (hK : PiField π p f K) {τ : K} (hτ : τ ^ 3 = 1) :
    mhat π (p ^ f) K hτ ≤ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  exact sup_le inf_le_left (Subgroup.zpowers_le.mpr (cycThree_mem_slPi hπ))

theorem mhat_le_normalizer_ehat (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (r : ℕ) :
    mhat π (p ^ f) K hτ ≤ Subgroup.normalizer (ehat (K := K) r : Set (GL (Fin 3) K)) := by
  refine sup_le ?_ (Subgroup.zpowers_le.mpr (cycThree_mem_normalizer_ehat r))
  rw [centralizer_diagTau_eq hK hq hτ hτ1]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
  rintro _ ⟨⟨a', b'⟩, -, rfl⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.prodMap, MonoidHom.coe_prod,
    MonoidHom.coe_comp, Subgroup.coe_subtype]
  rw [← map_mul, ← map_mul, mul_comm]

theorem slPi_inf_center_le_mhat {τ : K} (hτ : τ ^ 3 = 1) :
    slPi π 3 (p ^ f) K ⊓ Subgroup.center (GL (Fin 3) K) ≤ mhat π (p ^ f) K hτ := by
  rintro x ⟨hxL, hxZ⟩
  refine le_sup_left (a := slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ})
    ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  exact (Subgroup.mem_center_iff.mp hxZ _).symm

theorem cycThree_mem_centMod (hK : PiField π p f K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    cycThree ∈ centMod (slPi π 3 (p ^ f) K) (diagTau hτ) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set u : Kˣ := Units.mk0 (τ ^ 2) (pow_ne_zero 2 hτ0)
  refine mem_centMod_iff_scalar.mpr ⟨cycThree_mem_slPi hπ, GeneralLinearGroup.scalar (Fin 3) u,
    ⟨u, rfl⟩, Units.ext ?_⟩
  rw [cycThree_conj_diagTau, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  rfl

theorem cycThree_not_mem_centralizer {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    cycThree ∉ Subgroup.centralizer ({diagTau hτ} : Set (GL (Fin 3) K)) := by
  intro h
  have hc : cycThree * diagTau hτ * cycThree⁻¹ = diagTau hτ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right]
  have hm := cycThree_conj_diagTau hτ
  rw [hc, coe_diagTau_eq_diagonal] at hm
  have h22 := congrFun (congrFun hm 2) 2
  simp at h22
  have hτ2 : τ ^ 2 = 1 := h22.symm
  apply hτ1
  calc τ = τ * τ ^ 2 := by rw [hτ2, mul_one]
    _ = τ ^ 3 := by ring
    _ = 1 := hτ

theorem card_mhat (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) : Nat.card (mhat π (p ^ f) K hτ) = 3 * qSubPi π (p ^ f) ^ 2 := by
  set C := slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} with hC
  set M := mhat π (p ^ f) K hτ with hM
  have hCM : C ≤ M := le_sup_left
  have hMc : M ≤ centMod (slPi π 3 (p ^ f) K) (diagTau hτ) :=
    sup_le (centralizer_le_centMod _ _) (Subgroup.zpowers_le.mpr (cycThree_mem_centMod hK hτ hτ1))
  have h3 := relindex_centralizer_diagTau hK hq hτ hτ1
  have hmul := Subgroup.relIndex_mul_relIndex C M _ hCM hMc
  rw [h3] at hmul
  have hne : C.relIndex M ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    exact cycThree_not_mem_centralizer hτ hτ1
      (hle (le_sup_right (a := C) (Subgroup.mem_zpowers cycThree))).2
  have hrel : C.relIndex M = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hmul) with h | h
    · exact absurd h hne
    · exact h
  have hCc : Nat.card C = qSubPi π (p ^ f) ^ 2 := by
    obtain ⟨e⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have hz : Nat.card (Multiplicative (ZMod (qSubPi π (p ^ f)))) = qSubPi π (p ^ f) := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hz, sq]
  have hcard := Subgroup.card_mul_index (C.subgroupOf M)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv] at hcard
  change Nat.card C * C.relIndex M = Nat.card M at hcard
  rw [← hcard, hCc, hrel, mul_comm]

end Normalizer

section Model

variable {π : Bool} {p f : ℕ}

omit [Field K] in
theorem exists_conj_map_le {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {H : Subgroup G} (hH : ¬ r ∣ H.index) {P : Subgroup G} (hP : IsPGroup r P) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨S₀⟩ : Nonempty (Sylow r H) := inferInstance
  set S := (S₀ : Subgroup H).map H.subtype
  have hS : IsPGroup r S := S₀.isPGroup'.map H.subtype
  have hSi : ¬ r ∣ S.index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : r.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hH
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hS.toSylow hSi)
  refine ⟨g, ?_⟩
  calc P.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hPQ
    _ = S := by
        have h := congrArg (fun T : Sylow r G => (T : Subgroup G)) hg
        simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
        rw [← h, Subgroup.pointwise_smul_def]
        rfl
    _ ≤ H := Subgroup.map_subtype_le _

omit [Field K] in
theorem card_map_of_injOn {G G' : Type*} [Group G] [Group G'] (f : G →* G') {H : Subgroup G}
    (hinj : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card (H.map f) = Nat.card H := by
  have hi : Function.Injective (f.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  calc Nat.card (H.map f) = Nat.card (f.comp H.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
    _ = Nat.card H := (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm

theorem exists_torus_normalized (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f)) (hf : 1 ≤ f)
    {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hrd : r ∣ qSubPi π (2 ^ f))
    {D : Subgroup ↥(CFSG.Assembly.RankThreeEven.projImage (slPi π 3 (2 ^ f) K))}
    (hD : IsPGroup 3 D) :
    ∃ P : Subgroup ↥(CFSG.Assembly.RankThreeEven.projImage (slPi π 3 (2 ^ f) K)),
      CFSG.Assembly.IsElemAbelian r P ∧ Nat.card P = r ^ 2 ∧
        D ≤ Subgroup.normalizer (P : Set _) := by
  have := hK.finite
  have : Finite (GL (Fin 3) K) := inferInstance
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set L := slPi π 3 (2 ^ f) K with hL
  set ρ : ↥L →* ↥(CFSG.Assembly.RankThreeEven.projImage L) :=
    (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).subgroupMap L with hρ
  have hρs : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
  have hρ1 : ∀ x : ↥L, ρ x = 1 → (x : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro x hx
    rw [← ProjGenLinGroup.mk_eq_one]
    exact congrArg Subtype.val hx
  set M := (mhat π (2 ^ f) K hτ).subgroupOf L with hM
  have hML : mhat π (2 ^ f) K hτ ≤ L := mhat_le_slPi hK hτ
  have hker : ρ.ker ≤ M := by
    intro x hx
    rw [hM, Subgroup.mem_subgroupOf]
    exact slPi_inf_center_le_mhat hτ ⟨x.2, hρ1 x hx⟩
  have hidx : (M.map ρ).index = M.index := Subgroup.index_map_eq M hρs hker
  have hcM : Nat.card M = 3 * qSubPi π (2 ^ f) ^ 2 := by
    rw [hM, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv, card_mhat hK hq hτ hτ1]
  have hmul : M.index * (3 * qSubPi π (2 ^ f) ^ 2) =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) := by
    rw [← hcM, mul_comm, Subgroup.card_mul_index, hL]
    exact Sec13.card_slPi_three hK
  have h3 : ¬ 3 ∣ M.index :=
    not_three_dvd_of_mul_eq (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)) hq
      hmul
  set Eh := (ehat (K := K) r).subgroupOf L with hEh
  have hEL : ehat (K := K) r ≤ L := ehat_le_slPi hK hrd
  have hME : M ≤ Subgroup.normalizer (Eh : Set ↥L) := by
    intro x hx
    have hxn := mhat_le_normalizer_ehat hK hq hτ hτ1 r (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hEh, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp hxn y)
  set E := Eh.map ρ with hE
  have hNE : M.map ρ ≤ Subgroup.normalizer (E : Set _) :=
    (Subgroup.map_mono hME).trans (Subgroup.le_normalizer_map ρ)
  have h3' :
      ¬ 3 ∣ (Subgroup.normalizer (E : Set ↥(CFSG.Assembly.RankThreeEven.projImage L))).index :=
    fun h => h3 (hidx ▸ h.trans (Subgroup.index_dvd_of_le hNE))
  obtain ⟨g, hg⟩ := exists_conj_map_le h3' hD
  refine ⟨E.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map
      (Proof1517.isElemAbelian_subgroupOf (isElemAbelian_ehat r) L) ρ) _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE]
    rw [card_map_of_injOn ρ (H := Eh) fun x hx hx1 => ?_]
    · rw [hEh, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
      exact card_ehat ((hrd.trans (qSubPi_dvd hK)))
    · have hz := ehat_inf_center (K := K) hr hr3
      have hmem : (x : GL (Fin 3) K) ∈ ehat (K := K) r ⊓ Subgroup.center (GL (Fin 3) K) :=
        ⟨Subgroup.mem_subgroupOf.mp hx, hρ1 x hx1⟩
      rw [hz, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
  · have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_map] at h1
    have hid : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [hid, Subgroup.map_id] at h1

end Model

theorem ks1519Torus :
    ∀ (X : Type) [Group X] [Finite X] (m p : ℕ), Sec4.IsoLThreePi X 2 m → IsChoice1519 m p →
      3 < p → ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
        ∃ P : Subgroup X, CFSG.Assembly.IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
          D ≤ Subgroup.normalizer (P : Set X) := by
  intro X _ _ m p hiso hp hp3 D hDE hD9
  have hpp : p.Prime := hp.1
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
    have hrd := dvd_qSubPi_of_isChoice1519 hq hp
    have hD3 : IsPGroup 3 (D.map φ.toMonoidHom) := IsPGroup.of_card (n := 2) (by
      rw [Subgroup.card_map_of_injective φ.injective, hD9]
      norm_num)
    obtain ⟨P, hPE, hPc, hDP⟩ := exists_torus_normalized hK hq hm hpp (by omega) hrd hD3
    refine ⟨P.map φ.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hPE _,
      by rw [Subgroup.card_map_of_injective φ.symm.injective, hPc], ?_⟩
    have h1 := Subgroup.map_mono (f := φ.symm.toMonoidHom) hDP
    rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_map] at h1
    have hid : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by
      ext x
      simp
    rwa [hid, Subgroup.map_id] at h1

end Torus1519

end CFSG.RankThree.PartTwo.Sec15
