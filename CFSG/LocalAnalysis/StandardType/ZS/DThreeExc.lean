module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.ReflHyp
public import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport
public import CFSG.LocalAnalysis.StandardType.ZS.DThreeObstruction
public import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryFive
public import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernarySix
public import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryOrder
public import CFSG.LocalAnalysis.StandardType.GGZSKModelIso
public import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux
import all CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
public import Certificates.Certificate709541
public import Certificates.Certificate709542
public import CFSG.LocalAnalysis.StandardType.GGWitSlpm

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

local instance (priority := high) zkgZModAddCommGroup : AddCommGroup (ZMod p) :=
  Ring.toAddCommGroup

private theorem zkg_exists_lift (hirr : AbsIrred p A) (hn : 3 ≤ Module.finrank (ZMod p) U)
    {k : ℕ} {d : Fin k → ↥A ⧸ Subgroup.center ↥A} (hd : ∀ i, d i ∈ reflImage p A) :
    ∃ t : Fin k → ↥A, (∀ i, IsRefl p (t i : U ≃ₗ[ZMod p] U)) ∧
      ∀ i, QuotientGroup.mk (s := Subgroup.center ↥A) (t i) = d i := by
  have hex : ∀ i, ∃ s : ↥A, IsRefl p (s : U ≃ₗ[ZMod p] U) ∧
      QuotientGroup.mk (s := Subgroup.center ↥A) s = d i :=
    fun i => (exists_unique_refl_of_mem_reflImage hirr hn (hd i)).exists
  choose t ht using hex
  exact ⟨t, fun i => (ht i).1, fun i => (ht i).2⟩

private theorem zkg_pow_eq_one_of_mk_pow (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {s t : ↥A}
    (hs : IsRefl p (s : U ≃ₗ[ZMod p] U)) (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) {n : ℕ}
    (h : (QuotientGroup.mk (s := Subgroup.center ↥A) s *
      QuotientGroup.mk (s := Subgroup.center ↥A) t) ^ n = 1) :
    (s * t) ^ n = 1 := by
  have hdvd : orderOf (s * t) ∣ n := by
    rw [← hirr.orderOf_mk_mul_mk hn hs ht]
    exact orderOf_dvd_of_pow_eq_one h
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private theorem zkg_conj_mul_pow_three (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {x y w : ↥A}
    (hx : IsRefl p (x : U ≃ₗ[ZMod p] U)) (hy : IsRefl p (y : U ≃ₗ[ZMod p] U))
    (hw : IsRefl p (w : U ≃ₗ[ZMod p] U))
    (h : (QuotientGroup.mk (s := Subgroup.center ↥A) y *
      QuotientGroup.mk (s := Subgroup.center ↥A) x *
      QuotientGroup.mk (s := Subgroup.center ↥A) y *
      QuotientGroup.mk (s := Subgroup.center ↥A) w) ^ 3 = 1) :
    (y * x * y * w) ^ 3 = 1 := by
  have hconj : IsRefl p (((y * x * y : ↥A) : U ≃ₗ[ZMod p] U)) := hx.conj_mul_self hy
  exact zkg_pow_eq_one_of_mk_pow hirr hn hconj hw (n := 3) (by
    simpa only [QuotientGroup.mk_mul] using h)

private theorem zkg_closure_range_coe_eq_top (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A) {k : ℕ} {t : Fin k → ↥A}
    (ht : ∀ i, IsRefl p (t i : U ≃ₗ[ZMod p] U))
    {d : Fin k → ↥A ⧸ Subgroup.center ↥A}
    (htmk : ∀ i, QuotientGroup.mk (s := Subgroup.center ↥A) (t i) = d i)
    (hdtop : Subgroup.closure (Set.range d) = ⊤) :
    Subgroup.closure (Set.range fun i => (t i : U ≃ₗ[ZMod p] U)) = A := by
  have himg : QuotientGroup.mk (s := Subgroup.center ↥A) '' Set.range t = Set.range d := by
    ext x
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (htmk i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨t i, ⟨i, rfl⟩, htmk i⟩
  have hcl : Subgroup.closure (Set.range t) = ⊤ :=
    closure_eq_top_of_closure_mk_eq_top hgen hirr hn hone (fun s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact ht i) (by rw [himg]; exact hdtop)
  have hmap : (Subgroup.closure (Set.range t)).map A.subtype =
      Subgroup.closure (Set.range fun i => (t i : U ≃ₗ[ZMod p] U)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨t i, ⟨i, rfl⟩, rfl⟩
  rw [← hmap, hcl, Subgroup.map_top, Subgroup.range_subtype]

omit [Module.Finite (ZMod p) U] in
private theorem zkg_neg_mem_center (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A) :
    (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) ∈ Subgroup.center ↥A := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  ext x
  simp

omit [Module.Finite (ZMod p) U] in
private theorem zkg_neg_ne_one (hp : p ≠ 2) (hn : 3 ≤ Module.finrank (ZMod p) U)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A) :
    (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) ≠ 1 := by
  intro h
  have h1 : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) = 1 := by
    have := congrArg (fun e : ↥A => (e : U ≃ₗ[ZMod p] U)) h
    simpa using this
  have hU : Nontrivial U := by
    rcases subsingleton_or_nontrivial U with hsub | hnt
    · have : Subsingleton U := hsub
      have h0 : Module.finrank (ZMod p) U = 0 := Module.finrank_zero_of_subsingleton
      omega
    · exact hnt
  obtain ⟨x, hx0⟩ := exists_ne (0 : U)
  have hx : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) x = x := by rw [h1]; rfl
  rw [LinearEquiv.neg_apply] at hx
  have h3 : x + x = 0 := by simpa using (congrArg (fun y => x + y) hx).symm
  have h2 : (2 : ZMod p) • x = 0 := by rw [two_smul, h3]
  exact absurd ((smul_eq_zero_iff_left hx0).mp h2) (wSlpmC_two_ne_zero hp)

private theorem zkg_two_le_natCard_center (hp : p ≠ 2) (hn : 3 ≤ Module.finrank (ZMod p) U)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A) :
    2 ≤ Nat.card (Subgroup.center ↥A) := by
  have hmem := zkg_neg_mem_center hneg
  have hne := zkg_neg_ne_one hp hn hneg
  have hU : Finite U := Module.finite_of_finite (ZMod p)
  have hE : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  have hA : Finite ↥A := inferInstance
  have h01 : (⟨⟨LinearEquiv.neg (ZMod p), hneg⟩, hmem⟩ : Subgroup.center ↥A) ≠ 1 := by
    intro h
    apply hne
    have := congrArg (fun x : Subgroup.center ↥A => (x : ↥A)) h
    simpa using this
  have hnt : Nontrivial (Subgroup.center ↥A) :=
    ⟨⟨⟨LinearEquiv.neg (ZMod p), hneg⟩, hmem⟩, 1, h01⟩
  exact Finite.one_lt_card_iff_nontrivial.mpr hnt

omit [Module.Finite (ZMod p) U] in
private theorem zkg_exists_not_commute_refl (hgen : ReflGen p A)
    (hcard : Nat.card (↥A ⧸ Subgroup.center ↥A) ≠ 1) :
    ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ ¬ Commute x y := by
  by_contra hcon
  push Not at hcon
  have hcomm : IsMulCommutative ↥A := by
    rw [hgen]
    exact Subgroup.isMulCommutative_closure (by
      intro u hu v hv _
      exact hcon u hu.1 v hv.1 hu.2 hv.2)
  have hcenter : Subgroup.center ↥A = ⊤ := Subgroup.center_eq_top
  rw [hcenter] at hcard
  exact hcard (@Nat.card_of_subsingleton _ (QuotientGroup.mk (1 : ↥A))
    QuotientGroup.subsingleton_quotient_top)

private theorem zkg_orderOf_mul_eq_three {x y : U ≃ₗ[ZMod p] U} (hxA : x ∈ A) (hyA : y ∈ A)
    (hxr : IsRefl p x) (hyr : IsRefl p y) (hnc : ¬ Commute x y)
    (hle : orderOf (x * y) ≤ 3) : orderOf (x * y) = 3 :=
  orderOf_mul_eq_three_of_not_commute (A := A) (x := ⟨x, hxA⟩) (y := ⟨y, hyA⟩) hxr hyr hnc hle

omit [Module.Finite (ZMod p) U] in
private theorem zkg_orderOf_neg (hp : p ≠ 2) (hn : 3 ≤ Module.finrank (ZMod p) U)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A) :
    orderOf (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) = 2 := by
  have hne := zkg_neg_ne_one hp hn hneg
  rw [← Subgroup.orderOf_coe (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A),
    orderOf_eq_iff (by norm_num : 0 < 2)]
  refine ⟨?_, ?_⟩
  · rw [pow_two]
    ext x
    simp
  · intro k hk _
    interval_cases k
    simpa using hne

omit [Module.Finite (ZMod p) U] in
private theorem zkg_cube_root_data (hp3 : p ≠ 3)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {ω : ZMod p} (hω : ω ^ 2 + ω + 1 = 0)
    (g : U ≃ₗ[ZMod p] U) (hgA : g ∈ A) (hgv : ∀ v, g v = ω • v) :
    ω ^ 3 = 1 ∧ ω ≠ 1 ∧ (⟨g, hgA⟩ : ↥A) ^ 3 = 1 ∧ (⟨g, hgA⟩ : ↥A) ≠ 1 ∧
      (⟨g, hgA⟩ : ↥A) ∈ Subgroup.center ↥A := by
  have hω3 : ω ^ 3 = 1 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by rw [hω, mul_zero]
    have h' : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [h'] at h
    exact sub_eq_zero.mp h
  have hω1 : ω ≠ 1 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by
      rw [h] at hω
      linear_combination hω
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h3))
  have hpow : ∀ (n : ℕ) (v : U), (g ^ n) v = (ω ^ n) • v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, hgv, map_smul, ih, smul_smul, ← pow_succ']
  have hg3 : (⟨g, hgA⟩ : ↥A) ^ 3 = 1 := by
    apply Subtype.ext
    change g ^ 3 = 1
    apply LinearEquiv.ext
    intro v
    rw [hpow 3 v, hω3]
    simp
  have hgne : (⟨g, hgA⟩ : ↥A) ≠ 1 := by
    intro h
    have h1 : g = 1 := by
      have := congrArg (fun e : ↥A => (e : U ≃ₗ[ZMod p] U)) h
      simpa using this
    have hU : Nontrivial U := by
      rcases subsingleton_or_nontrivial U with hsub | hnt
      · have : Subsingleton U := hsub
        have h0 : Module.finrank (ZMod p) U = 0 := Module.finrank_zero_of_subsingleton
        omega
      · exact hnt
    obtain ⟨v, hv0⟩ := exists_ne (0 : U)
    have hv : g v = v := by rw [h1]; rfl
    rw [hgv v] at hv
    have hz : (ω - 1) • v = 0 := by
      rw [sub_smul, one_smul]
      rw [hv, sub_self]
    exact hω1 (sub_eq_zero.mp ((smul_eq_zero_iff_left hv0).mp hz))
  have hcenter : (⟨g, hgA⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    ext v
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hgv, hgv]
    simp
  exact ⟨hω3, hω1, hg3, hgne, hcenter⟩


private theorem zkg_frame_data (hp : p ≠ 2) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {m : ℕ} (hm : 0 < m)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m 1))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 m 1))
    {d₀ : Fin m → R3 (diagF3 m 1)} (hd₀ : ∀ i, d₀ i ∈ D3 (diagF3 m 1))
    (hinj₀ : Function.Injective d₀) (hcomm₀ : Pairwise fun i j => Commute (d₀ i) (d₀ j))
    (hprod₀ : (List.ofFn d₀).prod = 1) :
    Module.finrank (ZMod p) U = m ∧ (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A := by
  let d : Fin m → ↥A ⧸ Subgroup.center ↥A := φ.symm ∘ d₀
  have hd : ∀ i, d i ∈ reflImage p A := fun i => (hφ (d i)).mpr (by simpa [d] using hd₀ i)
  have hinj : Function.Injective d := φ.symm.injective.comp hinj₀
  have hcomm : Pairwise fun i j => Commute (d i) (d j) :=
    fun i j hij => (hcomm₀ hij).map φ.symm
  have hprod : (List.ofFn d).prod = 1 := by
    have h : (List.ofFn (φ.symm ∘ d₀)).prod = φ.symm (List.ofFn d₀).prod := by
      rw [← List.map_ofFn, List.prod_hom]
    have hd_def : d = φ.symm ∘ d₀ := rfl
    rw [hd_def, h, hprod₀, map_one]
  exact finrank_eq_and_neg_mem_of_prod_eq_one hp hirr hn hm hd hinj hcomm hprod

private theorem zkg_lift_tuple (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A) {m : ℕ}
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m 1))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 m 1))
    {r : Fin m → R3 (diagF3 m 1)} (hr : ∀ i, r i ∈ D3 (diagF3 m 1))
    (hrgen : Subgroup.closure (Set.range r) = ⊤) :
    ∃ t : Fin m → ↥A, (∀ i, IsRefl p (t i : U ≃ₗ[ZMod p] U)) ∧
      (∀ i, QuotientGroup.mk (s := Subgroup.center ↥A) (t i) = φ.symm (r i)) ∧
      Subgroup.closure (Set.range fun i => (t i : U ≃ₗ[ZMod p] U)) = A := by
  let dq : Fin m → ↥A ⧸ Subgroup.center ↥A := φ.symm ∘ r
  have hdq : ∀ i, dq i ∈ reflImage p A := fun i => (hφ (dq i)).mpr (by simpa [dq] using hr i)
  obtain ⟨t, htrefl, htmk⟩ := zkg_exists_lift hirr hn hdq
  have hqtop : Subgroup.closure (Set.range dq) = ⊤ := closure_range_symm_comp_eq_top φ hrgen
  have hAt : Subgroup.closure (Set.range fun i => (t i : U ≃ₗ[ZMod p] U)) = A :=
    zkg_closure_range_coe_eq_top hgen hirr hn hone htrefl htmk hqtop
  exact ⟨t, htrefl, htmk, hAt⟩

private theorem zkg_six_dvd_natCard_center (hp : p ≠ 2) (hp3 : p ≠ 3) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hdeg : Module.finrank (ZMod p) U = 6)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 6 1))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 6 1)) :
    6 ∣ Nat.card (Subgroup.center ↥A) := by
  obtain ⟨a, b, c, a', b', c', htri, htri', hcommt⟩ :=
    exists_affineTriangle_pair_D3_diagF3_six_one
  have htriA : AffineTriangle (reflImage p A) (φ.symm a) (φ.symm b) (φ.symm c) :=
    AffineTriangle.comap φ hφ htri
  have htriA' : AffineTriangle (reflImage p A) (φ.symm a') (φ.symm b') (φ.symm c') :=
    AffineTriangle.comap φ hφ htri'
  have hcommA : ∀ x ∈ [φ.symm a, φ.symm b, φ.symm c],
      ∀ y ∈ [φ.symm a', φ.symm b', φ.symm c'], Commute x y := by
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      exact (hcommt _ (by simp) _ (by simp)).map φ.symm
  obtain ⟨ω, hω, g, hgA, hgv⟩ :=
    exists_smul_mem_of_affineTriangle_pair hp hp3 hirr hdeg htriA htriA' hcommA
  obtain ⟨-, -, hg3, hgne, hgcenter⟩ := zkg_cube_root_data hp3 hn hω g hgA hgv
  let gg : ↥A := ⟨g, hgA⟩
  have hnegA : (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) ∈ Subgroup.center ↥A :=
    zkg_neg_mem_center hneg
  have hcommg : Commute (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) gg :=
    (Subgroup.mem_center_iff.mp hnegA gg).symm
  have hzcenter : (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) * gg ∈ Subgroup.center ↥A :=
    Subgroup.mul_mem (Subgroup.center ↥A) hnegA hgcenter
  have hzord : orderOf ((⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) * gg) = 6 := by
    have hgord : orderOf gg = 3 := by
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime hg3 hgne
    have hcop : (orderOf (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A)).Coprime (orderOf gg) := by
      rw [zkg_orderOf_neg hp hn hneg, hgord]
      decide
    have h := Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcommg hcop
    rw [zkg_orderOf_neg hp hn hneg, hgord] at h
    exact h.trans (by norm_num)
  have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥A)
    (x := (⟨LinearEquiv.neg (ZMod p), hneg⟩ : ↥A) * gg) hzcenter
  rwa [hzord] at h

private theorem zkg_lift_rel (hirr : AbsIrred p A) (hn : 3 ≤ Module.finrank (ZMod p) U)
    {m k : ℕ} {φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m 1)} {r : Fin k → R3 (diagF3 m 1)}
    {t : Fin k → ↥A} (htrefl : ∀ i, IsRefl p (t i : U ≃ₗ[ZMod p] U))
    (htmk : ∀ i, QuotientGroup.mk (s := Subgroup.center ↥A) (t i) = φ.symm (r i))
    (E : Fin k → Fin k → ℕ) (a b c : Fin k)
    (hrel : (∀ i j, (r i * r j) ^ E i j = 1) ∧ (r b * r a * r b * r c) ^ 3 = 1) :
    (∀ i j, ((t i : U ≃ₗ[ZMod p] U) * (t j : U ≃ₗ[ZMod p] U)) ^ E i j = 1) ∧
      ((t b : U ≃ₗ[ZMod p] U) * (t a : U ≃ₗ[ZMod p] U) * (t b : U ≃ₗ[ZMod p] U) *
        (t c : U ≃ₗ[ZMod p] U)) ^ 3 = 1 := by
  have hpair : ∀ i j, (t i * t j) ^ E i j = 1 := fun i j =>
    zkg_pow_eq_one_of_mk_pow hirr hn (htrefl i) (htrefl j) (by
      rw [htmk i, htmk j]; simpa using congrArg φ.symm (hrel.1 i j))
  have hextra : (t b * t a * t b * t c) ^ 3 = 1 :=
    zkg_conj_mul_pow_three hirr hn (htrefl a) (htrefl b) (htrefl c) (by
      rw [htmk a, htmk b, htmk c]; simpa using congrArg φ.symm hrel.2)
  exact ⟨fun i j => congrArg (fun z : ↥A => (z : U ≃ₗ[ZMod p] U)) (hpair i j),
    congrArg (fun z : ↥A => (z : U ≃ₗ[ZMod p] U)) hextra⟩

private theorem zkg_dMax (hgen : ReflGen p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    (hcard : Nat.card (↥A ⧸ Subgroup.center ↥A) ≠ 1) : DMax p A 3 := by
  obtain ⟨x, hxA, y, hyA, hxr, hyr, hnc⟩ := zkg_exists_not_commute_refl hgen hcard
  exact ⟨h3, x, hxA, y, hyA, hxr, hyr,
    zkg_orderOf_mul_eq_three hxA hyA hxr hyr hnc (h3 x hxA y hyA hxr hyr)⟩

theorem family_of_mulEquiv_R3_five_one
    (hp : p ≠ 2) (hp3 : p ≠ 3)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 5 1))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 5 1)) : Family p A := by
  classical
  have hone : OneClass p A := oneClass_of_orderOf_mul_le_three hp hgen hirr h3
  obtain ⟨d₀, hd₀, hinj₀, hcomm₀, hprod₀⟩ := exists_frame_D3_diagF3_five_one
  obtain ⟨hdeg, hneg⟩ := zkg_frame_data hp hirr hn (by norm_num) φ hφ hd₀ hinj₀ hcomm₀ hprod₀
  obtain ⟨r, hrD3, hrel, hgenr⟩ := exists_hsFiveRel_D3_diagF3_five_one
  change (∀ i j, (r i * r j) ^ kFiveExp i j = 1) ∧
    (r 2 * r 1 * r 2 * r 3) ^ 3 = 1 at hrel
  obtain ⟨t, htrefl, htmk, hAt⟩ := zkg_lift_tuple hgen hirr hn hone φ hφ hrD3 hgenr
  have hrelGL : HSFiveRel fun i => (t i : U ≃ₗ[ZMod p] U) :=
    zkg_lift_rel hirr hn htrefl htmk kFiveExp 1 2 3 hrel
  have hcardQ : Nat.card (↥A ⧸ Subgroup.center ↥A) = 25920 :=
    (Nat.card_congr φ.toEquiv).trans natCard_R3_diagF3_five_one
  have hcardA : Nat.card ↥A = Nat.card (Subgroup.center ↥A) *
      Nat.card (↥A ⧸ Subgroup.center ↥A) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥A), Nat.mul_comm]
  have hcardQne : Nat.card (↥A ⧸ Subgroup.center ↥A) ≠ 1 := by rw [hcardQ]; norm_num
  have hcardK5 : ExcRow.K5.ord ≤ Nat.card ↥A := by
    have hK : ExcRow.K5.ord = 2 * 25920 := by decide
    rw [hcardA, hcardQ, hK]
    exact Nat.mul_le_mul_right 25920 (zkg_two_le_natCard_center hp hn hneg)
  have hMIso : ModelIso p .K5 A := modelIso_kFive hAt hrelGL hcardK5 (htrefl 0) hone
  obtain ⟨f, hf⟩ := hMIso
  have hcardA51840 : Nat.card ↥A = 51840 := by
    have h : Nat.card ↥A = Nat.card (model .K5) := (Nat.card_congr f.toEquiv).symm
    rw [h, card_model_kFive]
    decide
  have hcen : Nat.card (Subgroup.center ↥A) = 2 := by
    have h : Nat.card (Subgroup.center ↥A) * 25920 = 2 * 25920 := by
      rw [← hcardQ, ← hcardA, hcardA51840, hcardQ]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  exact Family.exc .K5 hp3 hdeg hcardA51840 hcen (zkg_dMax hgen h3 hcardQne) hone
    (fun _ => ⟨f, hf⟩)

theorem family_of_mulEquiv_R3_six_one
    (hp : p ≠ 2) (hp3 : p ≠ 3)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 6 1))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 6 1)) : Family p A := by
  classical
  have hone : OneClass p A := oneClass_of_orderOf_mul_le_three hp hgen hirr h3
  obtain ⟨d₀, hd₀, hinj₀, hcomm₀, hprod₀⟩ := exists_frame_D3_diagF3_six_one
  obtain ⟨hdeg, hneg⟩ := zkg_frame_data hp hirr hn (by norm_num) φ hφ hd₀ hinj₀ hcomm₀ hprod₀
  obtain ⟨r, hrD3, hrel, hgenr⟩ := exists_hsSixRel_D3_diagF3_six_one
  change (∀ i j, (r i * r j) ^ kSixExp i j = 1) ∧
    (r 2 * r 1 * r 2 * r 3) ^ 3 = 1 at hrel
  obtain ⟨t, htrefl, htmk, hAt⟩ := zkg_lift_tuple hgen hirr hn hone φ hφ hrD3 hgenr
  have hrelGL : HSSixRel fun i => (t i : U ≃ₗ[ZMod p] U) :=
    zkg_lift_rel hirr hn htrefl htmk kSixExp 1 2 3 hrel
  have hcardQ : Nat.card (↥A ⧸ Subgroup.center ↥A) = Nat.card (R3 (diagF3 6 1)) :=
    Nat.card_congr φ.toEquiv
  have hcardA : Nat.card ↥A = Nat.card (Subgroup.center ↥A) *
      Nat.card (↥A ⧸ Subgroup.center ↥A) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥A), Nat.mul_comm]
  have hcardQne : Nat.card (↥A ⧸ Subgroup.center ↥A) ≠ 1 := by
    rw [hcardQ]; have h := le_natCard_R3_diagF3_six_one; omega
  have h6le : 6 ≤ Nat.card (Subgroup.center ↥A) :=
    Nat.le_of_dvd (by have := zkg_two_le_natCard_center hp hn hneg; omega)
      (zkg_six_dvd_natCard_center hp hp3 hirr hn hdeg hneg φ hφ)
  have hcardK6 : ExcRow.K6.ord ≤ Nat.card ↥A := by
    have hK : ExcRow.K6.ord = 6 * 6531840 := by decide
    rw [hcardA, hK]
    exact Nat.mul_le_mul h6le (by rw [hcardQ]; exact le_natCard_R3_diagF3_six_one)
  have hMIso : ModelIso p .K6 A := modelIso_kSix hAt hrelGL hcardK6 (htrefl 0) hone
  obtain ⟨f, hf⟩ := hMIso
  have hcardA6 : Nat.card ↥A = 39191040 := by
    have h : Nat.card ↥A = Nat.card (model .K6) := (Nat.card_congr f.toEquiv).symm
    rw [h, card_model_kSix]
    decide
  have hcen : Nat.card (Subgroup.center ↥A) = 6 := by
    have hprod : Nat.card (Subgroup.center ↥A) * Nat.card (↥A ⧸ Subgroup.center ↥A) =
        6 * 6531840 := by
      rw [← hcardA, hcardA6]
    have hQle : 6531840 ≤ Nat.card (↥A ⧸ Subgroup.center ↥A) := by
      rw [hcardQ]; exact le_natCard_R3_diagF3_six_one
    have hle : Nat.card (Subgroup.center ↥A) * 6531840 ≤ 6 * 6531840 := by
      rw [← hprod]; exact Nat.mul_le_mul_left _ hQle
    have hZle : Nat.card (Subgroup.center ↥A) ≤ 6 :=
      Nat.le_of_mul_le_mul_right hle (by norm_num)
    omega
  exact Family.exc .K6 hp3 hdeg hcardA6 hcen (zkg_dMax hgen h3 hcardQne) hone (fun _ => ⟨f, hf⟩)

end CFSG.StandardType.ZS
