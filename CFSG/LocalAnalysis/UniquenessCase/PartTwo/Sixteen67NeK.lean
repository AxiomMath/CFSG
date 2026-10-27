module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeJ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

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

theorem inCalO_of_le (h : Cfg1667Ne M V₀ V W₁ W₂) {n : G} {F : Subgroup G} (hFV : F ≤ V)
    (hF : F.relIndex V ≤ 2) (hFM : F ≤ conjSubgroup M n) (hFn : conjSubgroup F n ≤ M)
    (hV₀F : V₀ ≤ F) (hc : ⁅V, conjSubgroup V n⁆ ≠ ⊥) : InCalO 1 M V₀ V n := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hle
    exact hc (h.comm_eq_bot n hle)
  · refine mQuot_le_one_of_relIndex_le_two hV ?_
    have hdvd : (conjSubgroup M n).relIndex V ∣ F.relIndex V :=
      Subgroup.relIndex_dvd_of_le_left V hFM
    exact le_trans (Nat.le_of_dvd
      (Nat.pos_of_ne_zero (relIndex_ne_zero_of_isPGroup hV F)) hdvd) hF
  · intro _
    have hV₀M : V₀ ≤ conjSubgroup M n := hV₀F.trans hFM
    rw [inf_of_le_left hV₀M]
    exact h.ne_bot
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
  · intro _
    have hV₀nM : conjSubgroup V₀ n ≤ M := (E3.conjSubgroup_mono_left n hV₀F).trans hFn
    rw [inf_of_le_left hV₀nM]
    exact fun hbot => h.ne_bot (conjSubgroup_eq_bot_iff.mp hbot)

theorem cube_mem_sup_of_le (h : Cfg1667Ne M V₀ V W₁ W₂)
    (hstar : ∀ y : G, InCalO 1 M V₀ V y → InCalOStar 1 M V₀ V y ∧
      InCalOStar 1 (conjSubgroup M y) (conjSubgroup V₀ y) (conjSubgroup V y) y⁻¹)
    {n : G} {F : Subgroup G} (hFV : F ≤ V) (hF : F.relIndex V ≤ 2)
    (hFM : F ≤ conjSubgroup M n) (hFn : conjSubgroup F n ≤ M) (hV₀F : V₀ ≤ F)
    (hc : ⁅V, conjSubgroup V n⁆ ≠ ⊥) {t : G} (ht : t ∈ V) (htF : t ∉ F) :
    (t * (n⁻¹ * t * n)) ^ 3 ∈ F ⊔ conjSubgroup F n := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  have hn : InCalO 1 M V₀ V n := inCalO_of_le h hFV hF hFM hFn hV₀F hc
  obtain ⟨hs, hs'⟩ := hstar n hn
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
  have hres := cube_mem_K (g := n) h hs hs' ht (by rw [hUF]; exact htF) hi hiB
  rwa [hUF, hBF] at hres

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

theorem sq_or_cube_mem_relPPrimeCore (h : Cfg1667Ne M V₀ V W₁ W₂)
    (hstar : ∀ y : G, InCalO 1 M V₀ V y → InCalOStar 1 M V₀ V y ∧
      InCalOStar 1 (conjSubgroup M y) (conjSubgroup V₀ y) (conjSubgroup V y) y⁻¹)
    {z : G} (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z)
    {S : Subgroup G} (hVS : V ≤ S) (hSM : S ≤ M)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)))
    (hK : (CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))).relIndex V ≤ 2)
    (hV₀K : V₀ ≤ CFSG.Open.relPPrimeCore 3 (centralizer ({z} : Set G))) {t : G}
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
  have hV₀F : V₀ ≤ F := by
    rw [hF]
    exact le_inf h.V₀_le hV₀K
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
    have hcube := cube_mem_sup_of_le h hstar (n := n⁻¹) (F := F) hFV hFrel hFM hFn hV₀F hc ht htF
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

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
