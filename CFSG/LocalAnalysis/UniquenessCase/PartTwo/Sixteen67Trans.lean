module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67H
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67S3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G} {g : G}

theorem three_dvd_orderOf_sq (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {t i : G}
    (ht : t ∈ V) (htU : t ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) : 3 ∣ orderOf ((t * i) ^ 2) := by
  set x : G := t * i with hx
  have hx3 : x ^ 3 ∈ (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) := by
    rw [hx]
    exact cube_mem_K h hg ht htU hi hiB
  have hKM : (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) ≤ M :=
    sup_le (fun u hu => h.le_M hu.1) (fun b hb => hb.2)
  have hx3M : x ^ 3 ∈ M := hKM hx3
  by_contra h3
  have hcop : Nat.Coprime 3 (orderOf (x ^ 2)) :=
    (Nat.prime_three.coprime_iff_not_dvd).2 h3
  have hx2zp : x ^ 2 ∈ Subgroup.zpowers ((x ^ 2) ^ 3) := by
    rw [mem_zpowers_pow_iff]
    exact hcop
  have hx6 : (x ^ 2) ^ 3 = (x ^ 3) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
  have hx2M : x ^ 2 ∈ M := by
    have hpow : (x ^ 3) ^ 2 ∈ M := pow_mem hx3M 2
    have hle : Subgroup.zpowers ((x ^ 2) ^ 3) ≤ M := by
      rw [hx6]
      exact Subgroup.zpowers_le.mpr hpow
    exact hle hx2zp
  have hxM : x ∈ M := by
    have h2 : x ^ 3 * (x ^ 2)⁻¹ ∈ M := M.mul_mem hx3M (M.inv_mem hx2M)
    rwa [show x ^ 3 * (x ^ 2)⁻¹ = x by group] at h2
  have hiM : i ∈ M := by
    have h2 : t⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (h.le_M ht)) hxM
    rw [hx] at h2
    simpa using h2
  exact hiB ⟨hi, hiM⟩

private theorem relIndex_ne_zero_of_isPGroup {A : Subgroup G} (hA : IsPGroup 2 A)
    (B : Subgroup G) : B.relIndex A ≠ 0 := by
  rw [E3.relIndex_eq_two_pow hA B]
  exact pow_ne_zero _ (by norm_num)

private theorem mQuot_le_one_of_relIndex_le_two {A : Subgroup G} (hA : IsPGroup 2 A)
    {B : Subgroup G} (h : B.relIndex A ≤ 2) : E3.mQuot A B ≤ 1 := by
  by_contra hc
  have hc' : 2 ≤ E3.mQuot A B := by omega
  have hpow : B.relIndex A = 2 ^ E3.mQuot A B := E3.relIndex_eq_two_pow hA B
  have h4 : 4 ≤ B.relIndex A := by
    rw [hpow]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot A B := pow_le_pow_right' (by norm_num) hc'
  omega

theorem inCalO_of_le (h : Cfg1667 M V W₁ W₂) {n : G} {F : Subgroup G} (hFV : F ≤ V)
    (hF : F.relIndex V ≤ 2) (hFM : F ≤ conjSubgroup M n) (hFn : conjSubgroup F n ≤ M)
    (hc : ⁅V, conjSubgroup V n⁆ ≠ ⊥) : InCalO 1 M ⊥ V n := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hle
    exact hc (h.comm_eq_bot n hle)
  · refine mQuot_le_one_of_relIndex_le_two hV ?_
    have hdvd : (conjSubgroup M n).relIndex V ∣ F.relIndex V :=
      Subgroup.relIndex_dvd_of_le_left V hFM
    exact le_trans (Nat.le_of_dvd
      (Nat.pos_of_ne_zero (relIndex_ne_zero_of_isPGroup hV F)) hdvd) hF
  · intro hbot
    exact absurd rfl hbot
  · intro hle
    have hVn : conjSubgroup V n⁻¹ ≤ M := by
      intro y hy
      have hyV : n⁻¹ * y * n ∈ V := by
        simpa only [inv_inv] using mem_conjSubgroup_iff.mp hy
      have h2 : n * (n⁻¹ * y * n) * n⁻¹ ∈ M := mem_conjSubgroup_iff.mp (hle hyV)
      rwa [show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at h2
    have hcomm : ⁅V, conjSubgroup V n⁻¹⁆ = ⊥ := h.comm_eq_bot n⁻¹ hVn
    have hconj : ⁅conjSubgroup V n, V⁆ = ⊥ := by
      have := congrArg (fun X => conjSubgroup X n) hcomm
      rwa [E3.conjSubgroup_commutator, E3.conjSubgroup_bot,
        E3.conjSubgroup_inv_conj] at this
    exact hc (by rw [Subgroup.commutator_comm]; exact hconj)
  · refine mQuot_le_one_of_relIndex_le_two (E3.isPGroup_conjSubgroup hV n) ?_
    have hdvd : M.relIndex (conjSubgroup V n) ∣ (conjSubgroup F n).relIndex (conjSubgroup V n) :=
      Subgroup.relIndex_dvd_of_le_left (conjSubgroup V n) hFn
    rw [E3.relIndex_conjSubgroup] at hdvd
    exact le_trans (Nat.le_of_dvd
      (Nat.pos_of_ne_zero (relIndex_ne_zero_of_isPGroup hV F)) hdvd) hF
  · intro hbot
    exact absurd rfl hbot

theorem cube_mem_sup_of_le (h : Cfg1667 M V W₁ W₂) {n : G} {F : Subgroup G} (hFV : F ≤ V)
    (hF : F.relIndex V ≤ 2) (hFM : F ≤ conjSubgroup M n) (hFn : conjSubgroup F n ≤ M)
    (hc : ⁅V, conjSubgroup V n⁆ ≠ ⊥) {t : G} (ht : t ∈ V) (htF : t ∉ F) :
    (t * (n⁻¹ * t * n)) ^ 3 ∈ F ⊔ conjSubgroup F n := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  have hn : InCalO 1 M ⊥ V n := inCalO_of_le h hFV hF hFM hFn hc
  have hUF : V ⊓ conjSubgroup M n = F := by
    refine le_antisymm ?_ (le_inf hFV hFM)
    have hrel : F.relIndex (V ⊓ conjSubgroup M n) * (V ⊓ conjSubgroup M n).relIndex V
        = F.relIndex V :=
      Subgroup.relIndex_mul_relIndex F (V ⊓ conjSubgroup M n) V (le_inf hFV hFM) inf_le_left
    rw [relIndex_U (g := n) h hn] at hrel
    have hposV : F.relIndex V ≠ 0 := relIndex_ne_zero_of_isPGroup hV F
    have hpos : F.relIndex (V ⊓ conjSubgroup M n) ≠ 0 :=
      fun h0 => hposV (by rw [← hrel, h0, zero_mul])
    have hle1 : F.relIndex (V ⊓ conjSubgroup M n) ≤ 1 := by
      have : F.relIndex (V ⊓ conjSubgroup M n) * 2 ≤ 2 := by rw [hrel]; exact hF
      omega
    exact Subgroup.relIndex_eq_one.mp (by omega)
  have hBF : conjSubgroup V n ⊓ M = conjSubgroup F n := by
    refine le_antisymm ?_ (le_inf (E3.conjSubgroup_mono_left n hFV) hFn)
    have hrel : (conjSubgroup F n).relIndex (conjSubgroup V n ⊓ M) *
        (conjSubgroup V n ⊓ M).relIndex (conjSubgroup V n)
        = (conjSubgroup F n).relIndex (conjSubgroup V n) :=
      Subgroup.relIndex_mul_relIndex (conjSubgroup F n) (conjSubgroup V n ⊓ M)
        (conjSubgroup V n) (le_inf (E3.conjSubgroup_mono_left n hFV) hFn) inf_le_left
    rw [relIndex_B (g := n) h hn, E3.relIndex_conjSubgroup] at hrel
    have hposV : F.relIndex V ≠ 0 := relIndex_ne_zero_of_isPGroup hV F
    have hpos : (conjSubgroup F n).relIndex (conjSubgroup V n ⊓ M) ≠ 0 :=
      fun h0 => hposV (by rw [← hrel, h0, zero_mul])
    have hle1 : (conjSubgroup F n).relIndex (conjSubgroup V n ⊓ M) ≤ 1 := by
      have : (conjSubgroup F n).relIndex (conjSubgroup V n ⊓ M) * 2 ≤ 2 := by
        rw [hrel]; exact hF
      omega
    exact Subgroup.relIndex_eq_one.mp (by omega)
  have hi : n⁻¹ * t * n ∈ conjSubgroup V n := by
    rw [mem_conjSubgroup_iff]
    convert ht using 1
    group
  have hiB : n⁻¹ * t * n ∉ conjSubgroup V n ⊓ M := by
    rw [hBF]
    intro hmem
    exact htF (by
      have h2 : n * (n⁻¹ * t * n) * n⁻¹ ∈ F := mem_conjSubgroup_iff.mp hmem
      convert h2 using 1
      group)
  have hres := cube_mem_K (g := n) h hn ht (by rw [hUF]; exact htF) hi hiB
  rwa [hUF, hBF] at hres

theorem not_le_relPPrimeCore (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    ¬ V ≤ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
  let H : Subgroup G := centralizer ({z} : Set G)
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  change ¬ V ≤ K
  intro hVK
  have hVgH : conjSubgroup V g ≤ H := le_sup_right.trans (h.le_centralizer_of_eq_zpowers hz)
  have hKH : K ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hKN : (K.subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three H
  have hcop : Nat.Coprime 3 (Nat.card K) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three H
  obtain ⟨t, htV, htU, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := V ⊓ conjSubgroup M g) (K := V)).mp (relIndex_U h hg)
  obtain ⟨i, hiVg, hiB, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := conjSubgroup V g ⊓ M) (K := conjSubgroup V g)).mp (relIndex_B h hg)
  have hi2 : i * i = 1 := by
    simpa [pow_two] using (h.conj g).elemAbelian.2 i hiVg
  have hii : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hti2K : (t * i) ^ 2 ∈ K := by
    have htK : t ∈ K := hVK htV
    have hnorm : i ∈ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKN (hVgH hiVg)
    have hconjK : i * t * i⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hnorm t).1 htK
    have heq : (t * i) ^ 2 = t * (i * t * i⁻¹) := by
      rw [pow_two, hii]
      group
    rw [heq]
    exact K.mul_mem htK hconjK
  have hdvdK : orderOf ((t * i) ^ 2) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hti2K
  have h3 := three_dvd_orderOf_sq h hg htV htU hiVg hiB
  have h3K : 3 ∣ Nat.card K := h3.trans hdvdK
  exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop h3K

theorem not_le_sup_relPPrimeCore (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    ¬ centralizer ({z} : Set G) ≤
      centralizer ({z} : Set G) ⊓ M ⊔ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
  let H : Subgroup G := centralizer ({z} : Set G)
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  change ¬ H ≤ H ⊓ M ⊔ K
  intro hle
  have hVH : V ≤ H := le_sup_left.trans (h.le_centralizer_of_eq_zpowers hz)
  have hVgH : conjSubgroup V g ≤ H := le_sup_right.trans (h.le_centralizer_of_eq_zpowers hz)
  have hKH : K ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hKN : (K.subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three H
  have hHnormK : H ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKN
  have hcop : Nat.Coprime 3 (Nat.card K) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three H
  obtain ⟨t, htV, htU, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := V ⊓ conjSubgroup M g) (K := V)).mp (relIndex_U h hg)
  obtain ⟨i, hiVg, hiB, -⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
    (H := conjSubgroup V g ⊓ M) (K := conjSubgroup V g)).mp (relIndex_B h hg)
  have hiH : i ∈ H := hVgH hiVg
  have hHMnormK : H ⊓ M ≤ normalizer (K : Set G) := inf_le_left.trans hHnormK
  have hicoe : i ∈ ((H ⊓ M : Subgroup G) : Set G) * (K : Set G) := by
    have hmem : i ∈ (((H ⊓ M) ⊔ K : Subgroup G) : Set G) := hle hiH
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (H ⊓ M) K hHMnormK] at hmem
    exact hmem
  obtain ⟨m, hmHM, k, hkK, hmk⟩ := hicoe
  have hi2 : i * i = 1 := by
    simpa [pow_two] using (h.conj g).elemAbelian.2 i hiVg
  have hii : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hmM : m ∈ M := hmHM.2
  have hmNormV : m ∈ normalizer (V : Set G) := by rw [h.normalizer_eq]; exact hmM
  have hmtV : m * t * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hmNormV t).1 htV
  have hvV : t * (m * t * m⁻¹) ∈ V := V.mul_mem htV hmtV
  have hk1K : m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹ ∈ K := by
    have htK : t⁻¹ * k * t ∈ K := by
      have hnorm : t ∈ normalizer (K : Set G) := hHnormK (hVH htV)
      exact (Subgroup.mem_normalizer_iff''.mp hnorm k).1 hkK
    have hprod : (t⁻¹ * k * t) * k⁻¹ ∈ K := K.mul_mem htK (K.inv_mem hkK)
    have hnorm : m ∈ normalizer (K : Set G) := hHnormK hmHM.1
    exact (Subgroup.mem_normalizer_iff.mp hnorm _).1 hprod
  set y : G := (t * i) ^ 2 with hy
  have hy_eq : y = (t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
    have hconj : i * t * i⁻¹ = (m * t * m⁻¹) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
      rw [← hmk]
      group
    calc y = t * (i * t * i⁻¹) := by rw [hy, pow_two, hii]; group
      _ = (t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
        rw [hconj]; group
  have hy2K : y ^ 2 ∈ K := by
    have hv2 : (t * (m * t * m⁻¹)) * (t * (m * t * m⁻¹)) = 1 := by
      simpa [pow_two] using h.elemAbelian.2 (t * (m * t * m⁻¹)) hvV
    have hvinv : (t * (m * t * m⁻¹))⁻¹ = t * (m * t * m⁻¹) :=
      inv_eq_of_mul_eq_one_right hv2
    have hmem : (t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹)
        * (t * (m * t * m⁻¹))⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHnormK (hVH hvV)) _).1 hk1K
    rw [hy_eq]
    have hsq : ((t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹)) ^ 2
        = ((t * (m * t * m⁻¹)) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹)
            * (t * (m * t * m⁻¹))⁻¹) * (m * ((t⁻¹ * k * t) * k⁻¹) * m⁻¹) := by
      rw [pow_two, hvinv]
      group
    rw [hsq]
    exact K.mul_mem hmem hk1K
  have hdvdK : orderOf (y ^ 2) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hy2K
  have h3y : 3 ∣ orderOf y := by
    rw [hy]
    exact three_dvd_orderOf_sq h hg htV htU hiVg hiB
  have h3y2 : 3 ∣ orderOf (y ^ 2) := by
    by_contra h3
    have h1 : orderOf y ∣ 2 * orderOf (y ^ 2) := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
      exact pow_orderOf_eq_one (y ^ 2)
    have h3dvd : 3 ∣ 2 * orderOf (y ^ 2) := h3y.trans h1
    have h32 : Nat.Coprime 3 2 := by norm_num
    exact h3 (h32.dvd_of_dvd_mul_left h3dvd)
  have h3K : 3 ∣ Nat.card K := h3y2.trans hdvdK
  exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop h3K

private theorem exists_pow_mul_eq_mul {X N : Subgroup G}
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {h e : G} (hh : h ∈ X) (he : e ∈ N)
    (k : ℕ) : ∃ e' ∈ N, (h * e) ^ k = h ^ k * e' := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨e', he', hk⟩ := ih
    have h1 : h⁻¹ * e' * h⁻¹⁻¹ ∈ N := hnorm h⁻¹ (X.inv_mem hh) e' he'
    rw [inv_inv] at h1
    refine ⟨(h⁻¹ * e' * h) * e, N.mul_mem h1 he, ?_⟩
    rw [pow_succ, hk, pow_succ]
    group

theorem sq_or_cube_mem_relPPrimeCore (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z)
    {S : Subgroup G} (hVS : V ≤ S) (hSM : S ≤ M)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)))
    (hK : (CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))).relIndex V ≤ 2) {t : G}
    (ht : t ∈ V) (htK : t ∉ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))) {a : G}
    (ha : a ∈ centralizer ({z} : Set G)) :
    (t * (a * t * a⁻¹)) ^ 2 ∈ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) ∨
      (t * (a * t * a⁻¹)) ^ 3 ∈ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := centralizer ({z} : Set G)
  let K : Subgroup G := CFSG.Open.relPPrimeCore 3 H
  change (t * (a * t * a⁻¹)) ^ 2 ∈ K ∨ (t * (a * t * a⁻¹)) ^ 3 ∈ K
  have hVH : V ≤ H := le_sup_left.trans (h.le_centralizer_of_eq_zpowers hz)
  have hKH : K ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H
  have hKN : (K.subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three H
  have hHnormK : H ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKN
  have hS' : IsSylowIn 2 S H := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hR : IsSylowIn 2 (S ⊓ K) K := hS'.inf_normal hKH hKN
  obtain ⟨k, hkK, n, hn, hakn⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.frattini_argument hKH hKN hR ha
  have hnH : n ∈ H := hn.1
  have hnNormR : n ∈ normalizer ((S ⊓ K : Subgroup G) : Set G) := hn.2
  set w : G := n * t * n⁻¹ with hw
  have hwH : w ∈ H := H.mul_mem (H.mul_mem hnH (hVH ht)) (H.inv_mem hnH)
  have hwVg : w ∈ conjSubgroup V n⁻¹ := by
    rw [mem_conjSubgroup_iff]
    convert ht using 1
    rw [hw]
    group
  set e : G := (w⁻¹ * k * w) * k⁻¹ with he
  have heK : e ∈ K := by
    have h1 : w⁻¹ * k * w ∈ K :=
      (Subgroup.mem_normalizer_iff''.mp (hHnormK hwH) k).1 hkK
    rw [he]
    exact K.mul_mem h1 (K.inv_mem hkK)
  have hdecomp : t * (a * t * a⁻¹) = (t * w) * e := by
    rw [hakn]
    rw [he, hw]
    group
  have hnormK : ∀ x ∈ H, ∀ y ∈ K, x * y * x⁻¹ ∈ K := by
    intro x hx y hy
    exact (Subgroup.mem_normalizer_iff.mp (hHnormK hx) y).1 hy
  have htwH : t * w ∈ H := H.mul_mem (hVH ht) hwH
  have hpow2 : ∃ e' ∈ K, (t * (a * t * a⁻¹)) ^ 2 = (t * w) ^ 2 * e' := by
    obtain ⟨e', he', heq⟩ :=
      exists_pow_mul_eq_mul (X := H) (N := K) hnormK htwH heK 2
    exact ⟨e', he', by rw [hdecomp]; exact heq⟩
  have hpow3 : ∃ e' ∈ K, (t * (a * t * a⁻¹)) ^ 3 = (t * w) ^ 3 * e' := by
    obtain ⟨e', he', heq⟩ :=
      exists_pow_mul_eq_mul (X := H) (N := K) hnormK htwH heK 3
    exact ⟨e', he', by rw [hdecomp]; exact heq⟩
  suffices hmain : (t * w) ^ 2 ∈ K ∨ (t * w) ^ 3 ∈ K by
    obtain ⟨e2, he2, h2⟩ := hpow2
    obtain ⟨e3, he3, h3⟩ := hpow3
    rcases hmain with hmain | hmain
    · left
      rw [h2]
      exact K.mul_mem hmain he2
    · right
      rw [h3]
      exact K.mul_mem hmain he3
  set F : Subgroup G := V ⊓ K with hF
  have hFV : F ≤ V := by rw [hF]; exact inf_le_left
  have hFrel : F.relIndex V ≤ 2 := by
    rw [hF, Subgroup.inf_relIndex_left]
    exact hK
  have htF : t ∉ F := by
    rw [hF]
    exact fun hmem => htK hmem.2
  have hFM : F ≤ conjSubgroup M n⁻¹ := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    have hxR : x ∈ S ⊓ K := ⟨hVS hx.1, hx.2⟩
    have hnxR : n⁻¹ * x * n ∈ S ⊓ K :=
      (Subgroup.mem_normalizer_iff''.mp hnNormR x).1 hxR
    simpa only [inv_inv] using hSM hnxR.1
  have hFn : conjSubgroup F n⁻¹ ≤ M := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hx' : n⁻¹ * x * n ∈ F := by simpa only [inv_inv] using hx
    have hxR : n⁻¹ * x * n ∈ S ⊓ K := ⟨hVS hx'.1, hx'.2⟩
    have hnxR : n * (n⁻¹ * x * n) * n⁻¹ ∈ S ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp hnNormR _).1 hxR
    have hxeq : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rw [hxeq] at hnxR
    exact hSM hnxR.1
  by_cases hc : ⁅V, conjSubgroup V n⁻¹⁆ = ⊥
  · left
    have hcomm : V ≤ Subgroup.centralizer ((conjSubgroup V n⁻¹ : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    have hwt : w * t = t * w := (Subgroup.mem_centralizer_iff.mp (hcomm ht)) w hwVg
    have ht2 : t * t = 1 := by simpa [pow_two] using h.elemAbelian.2 t ht
    have hw2 : w * w = 1 := by
      rw [hw]
      calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
        _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
    have h1 : (t * w) ^ 2 = 1 := by
      rw [pow_two]
      calc t * w * (t * w) = t * (w * t) * w := by group
        _ = t * (t * w) * w := by rw [hwt]
        _ = t * t * (w * w) := by group
        _ = 1 := by rw [ht2, hw2, one_mul]
    rw [h1]
    exact K.one_mem
  · right
    have hcube := cube_mem_sup_of_le h (n := n⁻¹) (F := F) hFV hFrel hFM hFn hc ht htF
    have hcube' : (t * w) ^ 3 ∈ F ⊔ conjSubgroup F n⁻¹ := by
      simpa only [inv_inv, ← hw] using hcube
    have hsub : F ⊔ conjSubgroup F n⁻¹ ≤ K := by
      refine sup_le (by rw [hF]; exact inf_le_right) ?_
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have hxn : n⁻¹ * x * n ∈ K := by
        have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ V ⊓ K := by rwa [hF] at hx
        have hxK : n⁻¹ * x * n⁻¹⁻¹ ∈ K := (Subgroup.mem_inf.mp hx').2
        simpa only [inv_inv] using hxK
      have hthis : n * (n⁻¹ * x * n) * n⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hHnormK hnH) (n⁻¹ * x * n)).1 hxn
      rwa [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at hthis
    exact hsub hcube'

end Cfg1667

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
