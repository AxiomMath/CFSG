module

public import CFSG.RankThree.PerfectCover.HeisenbergDilation
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeFixedCommutator

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

variable {E : Type*} [Group E]

theorem perfect_central_prime_kernel_abelian_radical_dilation_trivial' [Finite E]
    [Group.IsPerfect E] {p : ℕ} [Fact p.Prime] (C : Subgroup E) (hCZ : C ≤ center E)
    (hCp : IsPGroup p C) (P : Sylow p E) (R V : Subgroup E) (hRP : R ≤ P)
    (hRab : IsMulCommutative R) (hCR : C ≤ R) {W : Type*} [Group W] (π : R →* W)
    (_hπ : Function.Surjective π) (hπker : π.ker = C.subgroupOf R)
    (hW : IsElementaryAbelian p W) (_hVP : V ≤ P)
    (hRn : (P : Subgroup E) ≤ normalizer (R : Set E)) (hRV : R ⊓ V = ⊥)
    (hRVP : R ⊔ V = P) (a : E) (_haP : a ∈ normalizer (P : Set E))
    (haR : a ∈ normalizer (R : Set E)) (haV : a ∈ centralizer (V : Set E))
    (hacop : Nat.Coprime (orderOf a) p) (ℓ : (ZMod p)ˣ) (hℓ : ℓ ≠ 1)
    (hact : ∀ x y : R, (y : E) = a * x * a⁻¹ → π y = π x ^ (ℓ : ZMod p).val) :
    C = ⊥ := by
  classical
  have hVR : V ≤ normalizer (R : Set E) := (le_sup_right.trans hRVP.le).trans hRn
  have hfixC : ∀ r : R, a * r * a⁻¹ = r → (r : E) ∈ C := by
    intro r hr
    have h := hact r r hr.symm
    have hpow : π r ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p W) _
    have hne : (((ℓ : ZMod p).val : ℕ) : ZMod p) ≠ 1 := by
      rw [ZMod.natCast_zmod_val]
      exact fun h1 => hℓ (Units.ext h1)
    have h1 : π r = 1 := eq_one_of_pow_eq_self ⟨1, by rw [pow_one, hpow]⟩ h.symm hne
    have hker : r ∈ π.ker := h1
    rw [hπker] at hker
    exact hker
  set Q : Subgroup E := zpowers a ⊔ V with hQ
  have hQN : Q ≤ normalizer (R : Set E) := sup_le ((zpowers_le).mpr haR) hVR
  have hQR : ∀ q ∈ Q, ∀ r ∈ R, q * r * q⁻¹ ∈ R := fun q hq r hr =>
    (mem_normalizer_iff.mp (hQN hq) r).mp hr
  have haQ : a ∈ Q := mem_sup_left (mem_zpowers a)
  have hQa : Q ≤ centralizer ({a} : Set E) := by
    refine sup_le ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haV v hv)
  let : CommGroup R := { (inferInstance : Group R) with mul_comm := hRab.is_comm.comm }
  let f : Q → Additive R → Additive R := fun q x =>
    Additive.ofMul ⟨(q : E) * (x.toMul : E) * (q : E)⁻¹, hQR q q.2 _ x.toMul.2⟩
  have hf : ∀ q x, ((Additive.toMul (f q x) : R) : E) = (q : E) * (x.toMul : E) * (q : E)⁻¹ :=
    fun _ _ => rfl
  have hext : ∀ x y : Additive R,
      ((Additive.toMul x : R) : E) = ((Additive.toMul y : R) : E) → x = y :=
    fun x y h => Additive.toMul.injective (Subtype.ext h)
  let act : DistribMulAction Q (Additive R) :=
    { smul := f
      one_smul := fun x => hext _ _ (by
        change ((Additive.toMul (f 1 x) : R) : E) = _
        rw [hf]
        simp)
      mul_smul := fun q q' x => hext _ _ (by
        change ((Additive.toMul (f (q * q') x) : R) : E) = ((Additive.toMul (f q (f q' x)) : R) : E)
        rw [hf, hf, hf, Subgroup.coe_mul, mul_inv_rev]
        group)
      smul_zero := fun q => hext _ _ (by
        change ((Additive.toMul (f q 0) : R) : E) = _
        rw [hf]
        simp)
      smul_add := fun q x y => hext _ _ (by
        change ((Additive.toMul (f q (x + y)) : R) : E) =
          ((Additive.toMul (f q x + f q y) : R) : E)
        rw [hf, toMul_add, toMul_add, Subgroup.coe_mul, Subgroup.coe_mul, hf, hf]
        group) }
  have hsmul : ∀ (q : Q) (x : Additive R),
      ((Additive.toMul (q • x) : R) : E) = (q : E) * (x.toMul : E) * (q : E)⁻¹ := fun _ _ => rfl
  set a' : Q := ⟨a, haQ⟩ with ha'
  set A : Subgroup Q := zpowers a' with hA
  have ha'center : a' ∈ center Q := by
    rw [mem_center_iff]
    intro q
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hQa q.2))
  have hAnormal : A.Normal := normal_of_le_center ((zpowers_le).mpr ha'center)
  have hRpg : IsPGroup p R := P.isPGroup'.to_le hRP
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (Additive R)) := by
    rw [hA, Nat.card_zpowers, ha', Subgroup.orderOf_mk]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRpg
    rw [show Nat.card (Additive R) = Nat.card R from Nat.card_congr Additive.toMul, hk]
    exact hacop.pow_right k
  obtain ⟨hcompl, hinv⟩ := abelian_coprime_fixed_commutator_decomposition A hcop
  set Dadd := coprimeCommutator A (Additive R) with hDadd
  set Cadd := coprimeFixed A (Additive R) with hCadd
  have hfixed : ∀ r : R, Additive.ofMul r ∈ Cadd ↔ (r : E) ∈ C := by
    intro r
    constructor
    · intro hr
      have h := congrArg (fun x : Additive R => ((Additive.toMul x : R) : E))
        (mem_coprimeFixed.mp hr a' (mem_zpowers a'))
      exact hfixC r h
    · intro hr g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hsmul, toMul_ofMul]
      have hz := mem_center_iff.mp (hCZ hr) ((a' ^ n : Q) : E)
      rw [hz, mul_assoc, mul_inv_cancel, mul_one]
  set D : Subgroup E := (AddSubgroup.toSubgroup' Dadd).map R.subtype with hD
  have hmemD : ∀ e : E, e ∈ D ↔ ∃ h : e ∈ R, Additive.ofMul (⟨e, h⟩ : R) ∈ Dadd := by
    intro e
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.2, (AddSubgroup.mem_toSubgroup' Dadd d).mp hd⟩
    · rintro ⟨h, hd⟩
      exact ⟨⟨e, h⟩, (AddSubgroup.mem_toSubgroup' Dadd _).mpr hd, rfl⟩
  have hDR : D ≤ R := map_subtype_le _
  have hCD : C ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heC, heD⟩
    obtain ⟨h, hd⟩ := (hmemD e).mp heD
    have hc : Additive.ofMul (⟨e, h⟩ : R) ∈ Cadd := (hfixed ⟨e, h⟩).mpr heC
    have h0 : Additive.ofMul (⟨e, h⟩ : R) ∈ Dadd ⊓ Cadd := ⟨hd, hc⟩
    rw [hcompl.inf_eq_bot, AddSubgroup.mem_bot] at h0
    have h1 : (⟨e, h⟩ : R) = 1 := by simpa using congrArg Additive.toMul h0
    exact (mem_bot).mpr (congrArg Subtype.val h1)
  have hRCD : ∀ r ∈ R, ∃ d ∈ D, ∃ c ∈ C, d * c = r := by
    intro r hr
    have hmem : Additive.ofMul (⟨r, hr⟩ : R) ∈ Dadd ⊔ Cadd := by
      rw [hcompl.sup_eq_top]
      exact AddSubgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hmem
    refine ⟨((Additive.toMul y : R) : E), (hmemD _).mpr ⟨(Additive.toMul y).2, by simpa using hy⟩,
      ((Additive.toMul z : R) : E), (hfixed _).mp (by simpa using hz), ?_⟩
    have h := congrArg (fun x : Additive R => ((Additive.toMul x : R) : E)) hyz
    simpa using h
  have hconj : ∀ v ∈ V, ∀ e ∈ D, v * e * v⁻¹ ∈ D := by
    intro v hv e he
    obtain ⟨h, hd⟩ := (hmemD e).mp he
    have h1 := (hinv hAnormal ⟨v, mem_sup_right hv⟩).1 _ hd
    have heq : (⟨v, mem_sup_right hv⟩ : Q) • Additive.ofMul (⟨e, h⟩ : R) =
        Additive.ofMul (⟨v * e * v⁻¹, hQR v (mem_sup_right hv) e h⟩ : R) := hext _ _ rfl
    exact (hmemD _).mpr ⟨hQR v (mem_sup_right hv) e h, heq ▸ h1⟩
  have hVD : V ≤ normalizer (D : Set E) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro e
    refine ⟨hconj v hv e, fun he => ?_⟩
    have := hconj v⁻¹ (V.inv_mem hv) _ he
    simpa [mul_assoc] using this
  set K : Subgroup E := D ⊔ V with hK
  have hKmul : (K : Set E) = (D : Set E) * (V : Set E) :=
    coe_mul_of_right_le_normalizer_left D V hVD
  have hCK : C ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro k ⟨hkC, hkK⟩
    have hk : k ∈ (D : Set E) * (V : Set E) := hKmul ▸ hkK
    obtain ⟨d, hd, v, hv, rfl⟩ := Set.mem_mul.mp hk
    have hvR : v ∈ R := by
      have : d⁻¹ * (d * v) ∈ R := R.mul_mem (R.inv_mem (hDR hd)) (hCR hkC)
      simpa using this
    have hv1 : v = 1 := by
      have : v ∈ R ⊓ V := ⟨hvR, hv⟩
      rwa [hRV, mem_bot] at this
    subst hv1
    rw [mul_one] at hkC ⊢
    have : d ∈ C ⊓ D := ⟨hkC, hd⟩
    rwa [hCD] at this
  have hPK : ∀ x ∈ (P : Subgroup E), ∃ k ∈ K, ∃ c ∈ C, k * c = x := by
    intro x hx
    rw [← hRVP] at hx
    have hx' : x ∈ (R : Set E) * (V : Set E) :=
      (coe_mul_of_right_le_normalizer_left R V hVR) ▸ hx
    obtain ⟨r, hr, v, hv, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨d, hd, c, hc, rfl⟩ := hRCD r hr
    refine ⟨d * v, mul_mem_sup hd hv, c, hc, ?_⟩
    rw [mul_assoc, mem_center_iff.mp (hCZ hc) v, ← mul_assoc]
  have hcommK : ⁅(P : Subgroup E), (P : Subgroup E)⁆ ≤ K := by
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨k, hk, c, hc, rfl⟩ := hPK x hx
    obtain ⟨k', hk', c', hc', rfl⟩ := hPK y hy
    rw [CFSG.SectionRank.commutatorElement_mul_mem_center k k' (hCZ hc) (hCZ hc')]
    exact commutator_le_self K (commutator_mem_commutator hk hk')
  have htrans := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P C hCZ hCp
  rw [map_subtype_commutator] at htrans
  rw [eq_bot_iff, ← hCK]
  exact le_inf le_rfl (htrans.trans hcommK)

theorem perfect_central_prime_kernel_abelian_radical_dilation_trivial [Finite E]
    [Group.IsPerfect E] {p : ℕ} [Fact p.Prime] (C : Subgroup E) [C.Normal] (hCZ : C ≤ center E)
    (hCp : IsPGroup p C) (P : Sylow p E) (R V : Subgroup E) (hRP : R ≤ P)
    (hRab : IsMulCommutative R) (hCR : C ≤ R)
    (hRC : IsElementaryAbelian p (R ⧸ C.subgroupOf R)) (hVP : V ≤ P)
    (hRn : (P : Subgroup E) ≤ normalizer (R : Set E)) (hRV : R ⊓ V = ⊥)
    (hRVP : R ⊔ V = P) (a : E) (haP : a ∈ normalizer (P : Set E))
    (haR : a ∈ normalizer (R : Set E)) (haV : a ∈ centralizer (V : Set E))
    (hacop : Nat.Coprime (orderOf a) p) (ℓ : (ZMod p)ˣ) (hℓ : ℓ ≠ 1)
    (hact : ∀ x y : R, (y : E) = a * x * a⁻¹ →
      (y : R ⧸ C.subgroupOf R) = (x : R ⧸ C.subgroupOf R) ^ (ℓ : ZMod p).val) :
    C = ⊥ :=
  perfect_central_prime_kernel_abelian_radical_dilation_trivial' C hCZ hCp P R V hRP hRab hCR
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hRC hVP hRn
    hRV hRVP a haP haR haV hacop ℓ hℓ hact

end CFSG.RankThree.PerfectCover
