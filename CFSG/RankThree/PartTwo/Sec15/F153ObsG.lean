module

public import CFSG.RankThree.PartTwo.Sec15.F153ObsCore
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofHJ
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompHatA6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.NoOrderNine
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153Obs

open Subgroup

section ObsWD1

theorem oPrimeResidualOf_subgroupOf {G : Type*} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (H K : Subgroup G) (hHK : H ≤ K) :
    CFSG.GH74.GLS.oPrimeResidualOf p (H.subgroupOf K) =
      (CFSG.GH74.GLS.oPrimeResidualOf p H).subgroupOf K := by
  have hcl : Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, x ^ p ^ k = 1} ≤ K :=
    (Subgroup.closure_le K).mpr fun x hx => hHK hx.1
  refine Subgroup.map_injective K.subtype_injective ?_
  rw [CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure,
    CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure, MonoidHom.map_closure,
    Subgroup.map_subgroupOf_eq_of_le hcl]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxH, k, hk⟩, rfl⟩
    exact ⟨hxH, k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨hyH, k, hk⟩
    exact ⟨⟨y, hHK hyH⟩, ⟨hyH, k, Subtype.ext (by simpa using hk)⟩, rfl⟩

end ObsWD1

section ObsWD2

theorem pCore_map_conj_eq {M : Type*} [Group M] (p : ℕ) (Y : Subgroup M) {g : M}
    (hg : g ∈ Subgroup.normalizer (Y : Set M)) :
    ((CFSG.pCore p ↥Y).map Y.subtype).map (MulAut.conj g).toMonoidHom =
      (CFSG.pCore p ↥Y).map Y.subtype := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have key := CFSG.pCore_map_iso p (Y.equivMapOfInjective (MulAut.conj g).toMonoidHom hinj)
  have h2 : ((CFSG.pCore p ↥Y).map Y.subtype).map (MulAut.conj g).toMonoidHom =
      (CFSG.pCore p ↥(Y.map (MulAut.conj g).toMonoidHom)).map
        (Y.map (MulAut.conj g).toMonoidHom).subtype := by
    rw [← key, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hY : Subgroup.map (MulAut.conj g).toMonoidHom Y = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
  rw [h2, hY]

theorem le_map_pCore_of_normalizer {M : Type*} [Group M] {p : ℕ} {P X : Subgroup M}
    (hPX : P ≤ X) (hXP : X ≤ Subgroup.normalizer (P : Set M)) (hP : IsPGroup p P) :
    P ≤ (CFSG.pCore p ↥X).map X.subtype := by
  have hn : (P.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).2 hXP
  have hp : IsPGroup p (P.subgroupOf X) := IsPGroup.comap_subtype hP
  have hle : P.subgroupOf X ≤ CFSG.pCore p ↥X := le_sSup ⟨hn, hp⟩
  intro x hx
  exact Subgroup.mem_map.2 ⟨⟨x, hPX hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem pCore_subgroupOf_eq {M : Type*} [Group M] [Finite M] (X Y : Subgroup M) [X.Normal]
    (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set M)) :
    (CFSG.pCore 2 M).subgroupOf Y = CFSG.pCore 2 ↥Y := by
  have hBn : ((CFSG.pCore 2 ↥X).map X.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hBle : (CFSG.pCore 2 ↥X).map X.subtype ≤ CFSG.pCore 2 M :=
    le_sSup ⟨hBn, (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype⟩
  have hPX : (CFSG.pCore 2 ↥Y).map Y.subtype ≤ X :=
    (Subgroup.map_subtype_le (CFSG.pCore 2 ↥Y)).trans hYX
  have hXP : X ≤ Subgroup.normalizer
      (((CFSG.pCore 2 ↥Y).map Y.subtype : Subgroup M) : Set M) :=
    fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.2 (pCore_map_conj_eq 2 Y (hXY hx))
  have hPB : (CFSG.pCore 2 ↥Y).map Y.subtype ≤ (CFSG.pCore 2 ↥X).map X.subtype :=
    le_map_pCore_of_normalizer hPX hXP
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype)
  apply le_antisymm
  · have hn : ((CFSG.pCore 2 M).subgroupOf Y).Normal :=
      Subgroup.Normal.subgroupOf (CFSG.pCore_normal (p := 2) (G := M)) Y
    have hp : IsPGroup 2 ((CFSG.pCore 2 M).subgroupOf Y) :=
      IsPGroup.comap_subtype (CFSG.pCore_isPGroup (p := 2) (G := M))
    exact le_sSup ⟨hn, hp⟩
  · intro y hy
    exact Subgroup.mem_subgroupOf.2 (hBle (hPB (Subgroup.mem_map_of_mem Y.subtype hy)))

end ObsWD2

section ObsWD3b

theorem three_dvd_card_of_quasisimple {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    3 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  by_contra h3
  have hcop : Nat.Coprime 3 (Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have himg : Y.subtype '' {h : ↥Y | ∃ k : ℕ, h ^ 3 ^ k = 1} =
      {x : G | x ∈ Y ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} := by
    ext x
    constructor
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨y.2, k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
    · rintro ⟨hx, k, hk⟩
      exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, hk])⟩, rfl⟩
  have hmap : (Subgroup.closure {h : ↥Y | ∃ k : ℕ, h ^ 3 ^ k = 1}).map Y.subtype = Y := by
    rw [MonoidHom.map_closure, himg]
    exact (CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure 3 Y).symm.trans hY3.symm
  have hinj : Function.Injective Y.subtype := Subtype.val_injective
  have htop : Subgroup.closure {h : ↥Y | ∃ k : ℕ, h ^ 3 ^ k = 1} = ⊤ := by
    refine Subgroup.map_injective hinj ?_
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hS : ∀ h : ↥Y, (∃ k : ℕ, h ^ 3 ^ k = 1) → h ∈ CFSG.pCore 2 ↥Y := by
    rintro h ⟨k, hk⟩
    have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) h) ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hk, map_one]
    have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) h) ∣
        Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
      orderOf_dvd_natCard _
    have hc : Nat.Coprime (3 ^ k) (Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
      Nat.Coprime.pow_left k hcop
    have hg : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) h) ∣
        Nat.gcd (3 ^ k) (Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) := Nat.dvd_gcd h1 h2
    rw [hc.gcd_eq_one] at hg
    have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) h) = 1 := Nat.dvd_one.mp hg
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y) h).mp (orderOf_eq_one_iff.mp hord)
  have hle : Subgroup.closure {h : ↥Y | ∃ k : ℕ, h ^ 3 ^ k = 1} ≤ CFSG.pCore 2 ↥Y := by
    rw [Subgroup.closure_le]
    intro h hh
    exact hS h hh
  have htriv : ∀ x : ↥Y ⧸ CFSG.pCore 2 ↥Y, x = 1 := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.eq_one_iff]
    rw [htop] at hle
    exact hle (Subgroup.mem_top h)
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [htriv x, htriv y]

end ObsWD3b

section ObsWD5b

theorem pCore_map_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H] [Finite K] (p : ℕ) (hp : p.Prime)
    (e : H ≃* K) : (CFSG.pCore p H).map e.toMonoidHom = CFSG.pCore p K :=
  CFSG.pCore_map_iso p e

noncomputable def quotientPCoreEquiv {H K : Type*} [Group H] [Group K] [Finite H] [Finite K] (p : ℕ) (hp : p.Prime)
    (e : H ≃* K) : (H ⧸ CFSG.pCore p H) ≃* (K ⧸ CFSG.pCore p K) :=
  QuotientGroup.congr (CFSG.pCore p H) (CFSG.pCore p K) e (pCore_map_mulEquiv p hp e)

end ObsWD5b

section ObsWD8

theorem card_inf_centralizer_eq_card_center {Q : Type*} [Group Q] [Finite Q] (K : Subgroup Q) :
    Nat.card (K ⊓ Subgroup.centralizer (K : Set Q) : Subgroup Q) = Nat.card (Subgroup.center ↥K) := by
  have key : ∀ z : Subgroup.center ↥K, ((z : K) : Q) ∈ K ⊓ Subgroup.centralizer (K : Set Q) := by
    intro z
    refine Subgroup.mem_inf.2 ⟨(z : K).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hz := (Subgroup.mem_center_iff.1 z.2) ⟨h, SetLike.mem_coe.1 hh⟩
    have hz' := congrArg Subtype.val hz
    simpa using hz'
  refine Nat.card_congr (Equiv.ofBijective (fun z : Subgroup.center ↥K =>
    (⟨((z : K) : Q), key z⟩ : ↥(K ⊓ Subgroup.centralizer (K : Set Q)))) ⟨?_, ?_⟩).symm
  · intro a b hab
    have h1 : ((a : K) : Q) = ((b : K) : Q) := by
      have h2 := congrArg Subtype.val hab
      exact h2
    exact Subtype.ext (Subtype.ext h1)
  · intro y
    have hyK : (y : Q) ∈ K := (Subgroup.mem_inf.1 y.2).1
    have hyC : (y : Q) ∈ Subgroup.centralizer (K : Set Q) := (Subgroup.mem_inf.1 y.2).2
    have hw : (⟨(y : Q), hyK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_iff.1 hyC) (g : Q) g.2
    exact ⟨⟨⟨(y : Q), hyK⟩, hw⟩, Subtype.ext rfl⟩

private theorem mem_center_iff_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (x : H) : x ∈ Subgroup.center H ↔ e x ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    obtain ⟨g, rfl⟩ := e.surjective y
    show e g * e x = e x * e g
    rw [← map_mul e, ← map_mul e, h g]
  · intro h g
    apply e.injective
    rw [map_mul e, map_mul e]
    exact h (e g)

theorem card_center_eq_of_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (e : H ≃* K) : Nat.card (Subgroup.center H) = Nat.card (Subgroup.center K) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun z : Subgroup.center H => (⟨e (z : H), (mem_center_iff_of_mulEquiv e (z : H)).1 z.2⟩ :
      Subgroup.center K)) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : e (a : H) = e (b : H) := congrArg Subtype.val hab
    exact Subtype.ext (e.injective h1)
  · intro y
    refine ⟨⟨e.symm (y : K), (mem_center_iff_of_mulEquiv e (e.symm (y : K))).2 ?_⟩,
      Subtype.ext (e.apply_symm_apply (y : K))⟩
    rw [e.apply_symm_apply]
    exact y.2

private theorem map_center_eq_center {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (Subgroup.center H).map e.toMonoidHom = Subgroup.center K := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_center_iff_of_mulEquiv e x).1 hx
  · intro hy
    refine ⟨e.symm y, (mem_center_iff_of_mulEquiv e (e.symm y)).2 ?_, e.apply_symm_apply y⟩
    rw [e.apply_symm_apply]
    exact hy

noncomputable def quotientCenterEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (H ⧸ Subgroup.center H) ≃* (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr (Subgroup.center H) (Subgroup.center K) e (map_center_eq_center e)

end ObsWD8

section ObsW1a

theorem qsLike_map_of_subgroupOf_eq {M : Type*} [Group M] [Finite M] (N Y : Subgroup M) [N.Normal]
    (hYN : N.subgroupOf Y = CFSG.pCore 2 ↥Y)
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    CFSG.RankThree.PartTwo.Sec15.F153Obs.QSLike (Y.map (QuotientGroup.mk' N)) ∧
      Nonempty (↥(Y.map (QuotientGroup.mk' N)) ≃* (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
  have hker : ((QuotientGroup.mk' N).comp Y.subtype).ker = CFSG.pCore 2 ↥Y := by
    rw [← hYN]
    ext x
    simp [Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : ((QuotientGroup.mk' N).comp Y.subtype).range = Y.map (QuotientGroup.mk' N) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
      exact Subgroup.mem_map.mpr ⟨y.1, y.2, rfl⟩
    · intro hx
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
      exact MonoidHom.mem_range.mpr ⟨⟨m, hm⟩, rfl⟩
  let e : ↥(Y.map (QuotientGroup.mk' N)) ≃* (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    ((MulEquiv.subgroupCongr hrange).symm.trans
      (QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' N).comp Y.subtype)).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have hKq : CFSG.IsQuasisimple ↥(Y.map (QuotientGroup.mk' N)) :=
    CFSG.IsQuasisimple.of_mulEquiv e hq
  obtain ⟨hperf, hsimp, -⟩ := hKq
  haveI := hperf
  haveI := hsimp
  set K : Subgroup (M ⧸ N) := Y.map (QuotientGroup.mk' N)
  have htop : Subgroup.map K.subtype ⊤ = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomm : Subgroup.map K.subtype (commutator ↥K) = ⁅K, K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, htop]
  have hK1 : ⁅K, K⁆ = K := by
    rw [← hcomm, Group.IsPerfect.commutator_eq_top, htop]
  have hKo : CFSG.Open.IsQuasisimple ↥K := ⟨Group.IsPerfect.commutator_eq_top, hsimp⟩
  refine ⟨⟨hK1, fun H hHK hHn => ?_⟩, ⟨e⟩⟩
  haveI := hHn
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKo
    (H.subgroupOf K) with hle | hcase
  · right
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hxK : (⟨x, hHK hx⟩ : ↥K) ∈ H.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
    have hc := Subgroup.mem_center_iff.mp (hle hxK) ⟨k, hk⟩
    exact congrArg Subtype.val hc
  · left
    exact le_antisymm hHK (Subgroup.subgroupOf_eq_top.mp hcase)

end ObsW1a

section ObsW1b

open Subgroup CFSG.RankThree.PartTwo.Sec15.F153Obs

theorem exists_noncentral_of_coprime_center {M : Type*} [Group M] [Finite M] (N Y A : Subgroup M)
    [N.Normal] (hN : (Nat.card N).Coprime 3)
    (hA : ∀ a ∈ A, a ^ 3 = 1)
    (hmax : ∀ x : M, orderOf x = 3 → x ∈ Subgroup.centralizer (A : Set M) → x ∈ A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set M))
    (hK : QSLike (Y.map (QuotientGroup.mk' N)))
    (h3K : 3 ∣ Nat.card (Y.map (QuotientGroup.mk' N)))
    (hZ : ¬ 3 ∣ Nat.card ((Y.map (QuotientGroup.mk' N)) ⊓ Subgroup.centralizer
      ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) : Subgroup (M ⧸ N))) :
    ∃ y ∈ A, QuotientGroup.mk' N y ∈ Y.map (QuotientGroup.mk' N) ∧
      QuotientGroup.mk' N y ∉
        Subgroup.centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) := by
  set π := QuotientGroup.mk' N
  have hA3 : IsPGroup 3 A := fun ⟨a, ha⟩ => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA a ha)⟩
  have hAbar3 : IsPGroup 3 (A.map π) := hA3.map π
  have hAbarK : A.map π ≤ Subgroup.normalizer ((Y.map π : Subgroup (M ⧸ N)) : Set (M ⧸ N)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨a * y * a⁻¹, ((Subgroup.mem_normalizer_iff.mp (hAY ha)) y).mp hy, by simp [π]⟩
    · rintro ⟨y, hy, hyk⟩
      refine ⟨a⁻¹ * y * a, ?_, ?_⟩
      · have := ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAY ha))) y).mp hy
        simpa [mul_assoc] using this
      · have : π a * k * (π a)⁻¹ = π y := hyk.symm
        have hk : k = (π a)⁻¹ * π y * π a := by rw [← this]; group
        rw [hk]; simp [π]
  obtain ⟨x, hxK, hx3, hxZ, hxA⟩ :=
    exists_fixed_noncentral_of_coprime_center (Y.map π) (A.map π) hK.1 hK.2 h3K hZ hAbar3 hAbarK
  obtain ⟨y, hyA, hyx⟩ := lift_of_maximal N hN A hA3 hmax x hx3
    (fun a ha => (hxA (π a) ⟨a, ha, rfl⟩))
  have hyx' : π y = x := hyx
  exact ⟨y, hyA, hyx' ▸ hxK, hyx' ▸ hxZ⟩

end ObsW1b

section ObsW1c

open CFSG.RankThree.PartTwo.Sec15.F153Obs

private def conjRestr {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H ≃* H where
  toFun h := ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg h.1).mp h.2⟩
  invFun h := ⟨g⁻¹ * h * g, (Subgroup.mem_normalizer_iff''.mp hg h.1).mp h.2⟩
  left_inv h := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' h₁ h₂ := Subtype.ext (by simp [mul_assoc])

private theorem conjRestr_pow_three {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hg3 : g ^ 3 = 1) :
    (conjRestr H g hg : MulAut H) ^ 3 = 1 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [pow_three]
  show g * (g * (g * (h : G) * g⁻¹) * g⁻¹) * g⁻¹ = (h : G)
  calc g * (g * (g * (h : G) * g⁻¹) * g⁻¹) * g⁻¹ = (g * (g * g)) * (h : G) * (g * (g * g))⁻¹ := by
        group
    _ = g ^ 3 * (h : G) * (g ^ 3)⁻¹ := by rw [pow_three]
    _ = (h : G) := by rw [hg3]; simp

private theorem isPerfect_of_comm_eq {Q : Type*} [Group Q] (K : Subgroup Q) (hK : ⁅K, K⁆ = K) :
    Group.IsPerfect K := by
  refine ⟨?_⟩
  have htop : (⊤ : Subgroup K).map K.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  apply Subgroup.map_injective (f := K.subtype) Subtype.val_injective
  show Subgroup.map K.subtype ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ =
    Subgroup.map K.subtype ⊤
  rw [Subgroup.map_commutator, htop, hK]

section Cover

variable {T : Type*} [Group T]

private theorem cover_cube_center (hZ : Nat.card (Subgroup.center T) = 3) {z : T}
    (hz : z ∈ Subgroup.center T) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := Subgroup.center T) (x := ⟨z, hz⟩)
  rw [hZ] at h
  have h' := congrArg Subtype.val h
  simpa using h'

private theorem cover_orderOf_three (hZ : Nat.card (Subgroup.center T) = 3)
    (e : T ⧸ Subgroup.center T ≃* alternatingGroup (Fin 6)) {k : T}
    (hk : k ∉ Subgroup.center T) (hk3 : k ^ 3 ∈ Subgroup.center T) : orderOf k = 3 := by
  have h9 : k ^ 9 = 1 := by
    have h := cover_cube_center hZ hk3
    rw [← pow_mul] at h
    exact h
  have hdvd : orderOf k ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one h9
  have hne1 : orderOf k ≠ 1 := by
    intro h1
    apply hk
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hne9 : orderOf k ≠ 9 :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.orderOf_ne_nine_tripleA6 hZ e k
  obtain ⟨i, hi, hki⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases i
  · rw [pow_zero] at hki
    exact absurd hki hne1
  · rw [pow_one] at hki
    exact hki
  · exact absurd hki hne9

private theorem cover_centralizer_pow_nine (hZ : Nat.card (Subgroup.center T) = 3)
    (e : T ⧸ Subgroup.center T ≃* alternatingGroup (Fin 6)) {t : T}
    (ht : t ∉ Subgroup.center T) (ht3 : t ^ 3 ∈ Subgroup.center T) {g : T}
    (hg : g * t = t * g) : g ^ 9 ∈ Subgroup.center T := by
  have hmk3 : QuotientGroup.mk' (Subgroup.center T) (t ^ 3) = 1 :=
    (QuotientGroup.eq_one_iff (t ^ 3)).mpr ht3
  have ht1 : QuotientGroup.mk' (Subgroup.center T) t ≠ 1 := fun h =>
    ht ((QuotientGroup.eq_one_iff t).mp h)
  have hτ3 : (e (QuotientGroup.mk' (Subgroup.center T) t)) ^ 3 = 1 := by
    have h : (e (QuotientGroup.mk' (Subgroup.center T) t)) ^ 3 =
        e (QuotientGroup.mk' (Subgroup.center T) (t ^ 3)) := by
      simp [map_pow]
    rw [h, hmk3, map_one]
  have hτ1 : e (QuotientGroup.mk' (Subgroup.center T) t) ≠ 1 := fun h =>
    ht1 (e.injective (by rw [h, map_one]))
  have hmk : QuotientGroup.mk' (Subgroup.center T) t * QuotientGroup.mk' (Subgroup.center T) g =
      QuotientGroup.mk' (Subgroup.center T) g * QuotientGroup.mk' (Subgroup.center T) t := by
    rw [← map_mul, ← map_mul, hg]
  have hcC : e (QuotientGroup.mk' (Subgroup.center T) g) ∈
      Subgroup.centralizer ({e (QuotientGroup.mk' (Subgroup.center T) t)} :
        Set (alternatingGroup (Fin 6))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← map_mul e, ← map_mul e, hmk]
  have hpow : (e (QuotientGroup.mk' (Subgroup.center T) g)) ^ 9 = 1 := by
    have h := pow_card_eq_one'
      (G := Subgroup.centralizer ({e (QuotientGroup.mk' (Subgroup.center T) t)} :
        Set (alternatingGroup (Fin 6)))) (x := ⟨_, hcC⟩)
    rw [CFSG.Quasithin.H13.S126C.card_centralizer_alt6_three hτ3 hτ1] at h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
    exact h'
  have hg9 : QuotientGroup.mk' (Subgroup.center T) (g ^ 9) = 1 := by
    apply e.injective
    have h : e (QuotientGroup.mk' (Subgroup.center T) (g ^ 9)) =
        (e (QuotientGroup.mk' (Subgroup.center T) g)) ^ 9 := by
      simp [map_pow]
    rw [h, hpow, map_one]
  exact (QuotientGroup.eq_one_iff (g ^ 9)).mp hg9

private theorem exists_noncentral_of_cover (hZ : Nat.card (Subgroup.center T) = 3)
    (e : T ⧸ Subgroup.center T ≃* alternatingGroup (Fin 6)) :
    ∃ k : T, k ∉ Subgroup.center T ∧ k ^ 3 ∈ Subgroup.center T := by
  have h01 : (0 : Fin 6) ≠ 1 := by decide
  have h12 : (1 : Fin 6) ≠ 2 := by decide
  have hp : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h12]
    norm_num
  have hp3 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have hp1 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ≠ 1 := by decide
  obtain ⟨τ0, hτ3, hτ1⟩ : ∃ τ0 : alternatingGroup (Fin 6), τ0 ^ 3 = 1 ∧ τ0 ≠ 1 :=
    ⟨⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2, hp⟩, Subtype.ext hp3,
      fun h => hp1 (congrArg Subtype.val h)⟩
  obtain ⟨k, hk⟩ : ∃ k : T, QuotientGroup.mk' (Subgroup.center T) k = e.symm τ0 :=
    QuotientGroup.mk_surjective _
  have hek : e (QuotientGroup.mk' (Subgroup.center T) k) = τ0 := by
    rw [hk, MulEquiv.apply_symm_apply]
  refine ⟨k, ?_, ?_⟩
  · intro hkZ
    apply hτ1
    have hk1 : QuotientGroup.mk' (Subgroup.center T) k = 1 :=
      (QuotientGroup.eq_one_iff k).mpr hkZ
    rw [← hek, hk1, map_one]
  · have h3 : e (QuotientGroup.mk' (Subgroup.center T) (k ^ 3)) = 1 := by
      rw [map_pow, map_pow, hek, hτ3]
    exact (QuotientGroup.eq_one_iff (k ^ 3)).mp (e.map_eq_one_iff.mp h3)

end Cover

private theorem exists_cover_of_not_cent {G : Type*} [Group G] (H : Subgroup G) [Group.IsPerfect H]
    (hZ : Nat.card (Subgroup.center H) = 3)
    (e : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 6))
    {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) (hg3 : g ^ 3 = 1)
    (hgH : g ∉ Subgroup.centralizer (H : Set G)) :
    ∃ t : H, t ∉ Subgroup.center H ∧ t ^ 3 ∈ Subgroup.center H ∧
      ∀ k : H, g * (k : G) * g⁻¹ = (t : G) * (k : G) * (t : G)⁻¹ := by
  have hσ3 : (conjRestr H g hg : MulAut H) ^ (3 ^ 1) = 1 := by
    rw [pow_one]
    exact conjRestr_pow_three H g hg hg3
  obtain ⟨t, ht⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Item2110Res3Proof.exists_eq_conj_of_tripleCover e hσ3
  have happ : ∀ k : H, g * (k : G) * g⁻¹ = (t : G) * (k : G) * (t : G)⁻¹ := by
    intro k
    have h : (conjRestr H g hg : MulAut H) k = (MulAut.conj t : MulAut H) k := by
      rw [ht]
    have h' := congrArg Subtype.val h
    exact h'
  have hσ3' : (MulAut.conj t : MulAut H) ^ 3 = 1 := by
    rw [← ht]
    exact conjRestr_pow_three H g hg hg3
  refine ⟨t, ?_, ?_, happ⟩
  · intro htc
    apply hgH
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hcomm : h * (t : G) = (t : G) * h :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp htc ⟨h, hh⟩)
    have hc : (t : G) * h * (t : G)⁻¹ = h := by
      rw [← hcomm, mul_inv_cancel_right]
    have hgh : g * h * g⁻¹ = (t : G) * h * (t : G)⁻¹ := happ ⟨h, hh⟩
    rw [hc] at hgh
    exact (mul_inv_eq_iff_eq_mul.mp hgh).symm
  · have hc : MulAut.conj (t ^ 3) = 1 := by
      rw [map_pow]
      exact hσ3'
    rw [Subgroup.mem_center_iff]
    intro k
    have hk : (t ^ 3 : H) * k * (t ^ 3)⁻¹ = k := by
      have h : MulAut.conj (t ^ 3) k = (1 : MulAut H) k := by rw [hc]
      exact h
    exact (mul_inv_eq_iff_eq_mul.mp hk).symm

private theorem mk_mem_normalizer_map {M : Type*} [Group M] (N Y A : Subgroup M) [N.Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set M)) {a : M} (ha : a ∈ A) :
    QuotientGroup.mk' N a ∈
      Subgroup.normalizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a * y * a⁻¹, ((Subgroup.mem_normalizer_iff.mp (hAY ha)) y).mp hy, by simp⟩
  · rintro ⟨y, hy, hyk⟩
    refine ⟨a⁻¹ * y * a, ?_, ?_⟩
    · have h := ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAY ha))) y).mp hy
      simpa [mul_assoc] using h
    · rw [map_mul, map_mul, map_inv, hyk]
      group

private theorem mem_center_iff_mem_centralizer {G : Type*} [Group G] (H : Subgroup G) (k : H) :
    k ∈ Subgroup.center H ↔ (k : G) ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, hx⟩)
  · intro h x
    exact Subtype.ext (h x.1 x.2)

private theorem exists_good_elt {M : Type*} [Group M] [Finite M] (N Y A : Subgroup M) [N.Normal]
    (hA : ∀ a ∈ A, a ^ 3 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA27 : Nat.card A = 27)
    (hAY : A ≤ Subgroup.normalizer (Y : Set M))
    (hK : CFSG.RankThree.PartTwo.Sec15.F153Obs.QSLike (Y.map (QuotientGroup.mk' N)))
    (hZ3 : Nat.card (Subgroup.center ↥(Y.map (QuotientGroup.mk' N))) = 3)
    (e : ↥(Y.map (QuotientGroup.mk' N)) ⧸ Subgroup.center ↥(Y.map (QuotientGroup.mk' N)) ≃*
      alternatingGroup (Fin 6))
    (hgen : ∀ y ∈ Y, y ∈ ⨆ (Q : Subgroup M) (_ : Q ≤ Y ∧ A ≤ Subgroup.normalizer (Q : Set M) ∧
      (Nat.card Q).Coprime 3), Q) :
    ∃ x : M ⧸ N, x ∈ Y.map (QuotientGroup.mk' N) ∧ orderOf x = 3 ∧
      (∀ a ∈ A, Commute x (QuotientGroup.mk' N a)) ∧
      x ∉ Subgroup.centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpA : 3 ≤ Nat.card A := by rw [hA27]; norm_num
  have hAcomm : IsMulCommutative ↥A := ⟨⟨fun a b => Subtype.ext (hAc a.1 a.2 b.1 b.2)⟩⟩
  have hAel : CFSG.Open.IsElemAbelian 3 A := by
    unfold CFSG.Open.IsElemAbelian
    exact ⟨hAcomm, fun x hx => hA x hx⟩
  have hperf : Group.IsPerfect ↥(Y.map (QuotientGroup.mk' N)) :=
    isPerfect_of_comm_eq _ hK.1
  have hPlaw : ∀ a ∈ A, QuotientGroup.mk' N a ∈
      Subgroup.normalizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) :=
    fun a ha => mk_mem_normalizer_map N Y A hAY ha
  have hg3 : ∀ a ∈ A, (QuotientGroup.mk' N a) ^ 3 = 1 := fun a ha => by
    rw [← map_pow, hA a ha, map_one]
  by_cases hI : ∃ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 3 A,
      ∀ b ∈ B, QuotientGroup.mk' N b ∈ Subgroup.centralizer
        ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N))
  · obtain ⟨B, hB, hBP⟩ := hI
    obtain ⟨hBA, hcardA⟩ := hB
    have hcardB : Nat.card B = 9 := by omega
    by_cases hAP : ∀ a ∈ A, QuotientGroup.mk' N a ∈ Subgroup.centralizer
        ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N))
    ·
      obtain ⟨k, hkZ, hk3⟩ := exists_noncentral_of_cover hZ3 e
      refine ⟨(k : M ⧸ N), k.2, ?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_coe]
        exact cover_orderOf_three hZ3 e hkZ hk3
      · intro a ha
        exact (Subgroup.mem_centralizer_iff.mp (hAP a ha)) _ k.2
      · intro hc
        exact hkZ ((mem_center_iff_mem_centralizer _ k).mpr hc)
    ·
      push Not at hAP
      obtain ⟨a, haA, haP⟩ := hAP
      obtain ⟨t, htZ, ht3, hσ⟩ :=
        exists_cover_of_not_cent _ hZ3 e (hPlaw a haA) (hg3 a haA) haP
      have hx3 : orderOf (t : M ⧸ N) = 3 := by
        rw [Subgroup.orderOf_coe]
        exact cover_orderOf_three hZ3 e htZ ht3
      have hxC : (t : M ⧸ N) ∉ Subgroup.centralizer
          ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) :=
        fun hc => htZ ((mem_center_iff_mem_centralizer _ t).mpr hc)
      set C : Subgroup M := ((Subgroup.centralizer ({(t : M ⧸ N)} : Set (M ⧸ N))).comap
        (QuotientGroup.mk' N)) ⊓ A with hCdef
      have hCA : C ≤ A := inf_le_right
      have hBC : B ≤ C := by
        intro b hb
        refine Subgroup.mem_inf.mpr ⟨?_, hBA hb⟩
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (Subgroup.mem_centralizer_iff.mp (hBP b hb)) _ t.2
      have haC : a ∈ C := by
        refine Subgroup.mem_inf.mpr ⟨?_, haA⟩
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have h1 := hσ t
        rw [mul_inv_cancel_right] at h1
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
      have hCeq : C = A := by
        have hdvd : Nat.card C ∣ 27 := by
          rw [← hA27]
          exact Subgroup.card_dvd_of_le hCA
        have h9 : 9 ∣ Nat.card C := by
          rw [← hcardB]
          exact Subgroup.card_dvd_of_le hBC
        have hle : Nat.card C ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
        have hcases : ∀ n < 28, n ∣ 27 → 9 ∣ n → n = 9 ∨ n = 27 := by decide
        rcases hcases (Nat.card C) (by omega) hdvd h9 with h | h
        · exfalso
          have hBC' : B = C := Subgroup.eq_of_le_of_card_ge hBC (by omega)
          have haB : a ∈ B := by
            rw [hBC']
            exact haC
          exact haP (hBP a haB)
        · exact Subgroup.eq_of_le_of_card_ge hCA (by omega)
      refine ⟨(t : M ⧸ N), t.2, hx3, ?_, hxC⟩
      intro a' ha'
      have ha'C : a' ∈ C := by
        rw [hCeq]
        exact ha'
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_comap.mp (Subgroup.mem_inf.mp ha'C).1) _ (Set.mem_singleton _)
  ·
    push Not at hI
    exfalso
    have hQN : ∀ Q : Subgroup M, Q ≤ Y → A ≤ Subgroup.normalizer (Q : Set M) →
        (Nat.card Q).Coprime 3 → Q ≤ N := by
      intro Q hQY hAQ hQc
      have hcov := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
        Nat.prime_three hAel hpA hAQ hQc.symm
      refine le_trans (le_of_eq hcov.symm) (iSup₂_le fun B hB => ?_)
      rintro x ⟨hxQ, hxC⟩
      obtain ⟨b, hbB, hbP⟩ := hI B hB
      have hbA : b ∈ A := hB.1 hbB
      obtain ⟨t, htZ, ht3, hσ⟩ :=
        exists_cover_of_not_cent _ hZ3 e (hPlaw b hbA) (hg3 b hbA) hbP
      have hcomm : b * x = x * b := (Subgroup.mem_centralizer_iff.mp hxC) b hbB
      have hcommK : QuotientGroup.mk' N b * QuotientGroup.mk' N x =
          QuotientGroup.mk' N x * QuotientGroup.mk' N b := by
        rw [← map_mul, ← map_mul, hcomm]
      have hxK : QuotientGroup.mk' N x ∈ Y.map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ (hQY hxQ)
      have hσx : QuotientGroup.mk' N b * QuotientGroup.mk' N x * (QuotientGroup.mk' N b)⁻¹ =
          (t : M ⧸ N) * QuotientGroup.mk' N x * (t : M ⧸ N)⁻¹ :=
        hσ ⟨QuotientGroup.mk' N x, hxK⟩
      have hl : QuotientGroup.mk' N b * QuotientGroup.mk' N x * (QuotientGroup.mk' N b)⁻¹ =
          QuotientGroup.mk' N x := by
        rw [hcommK, mul_inv_cancel_right]
      rw [hl] at hσx
      have htx : (t : M ⧸ N) * QuotientGroup.mk' N x = QuotientGroup.mk' N x * (t : M ⧸ N) := by
        calc (t : M ⧸ N) * QuotientGroup.mk' N x
            = ((t : M ⧸ N) * QuotientGroup.mk' N x * (t : M ⧸ N)⁻¹) * (t : M ⧸ N) := by group
          _ = QuotientGroup.mk' N x * (t : M ⧸ N) := by rw [← hσx]
      have hgt : (⟨QuotientGroup.mk' N x, hxK⟩ : ↥(Y.map (QuotientGroup.mk' N))) * t =
          t * ⟨QuotientGroup.mk' N x, hxK⟩ := Subtype.ext htx.symm
      have h9 := cover_centralizer_pow_nine hZ3 e htZ ht3 hgt
      have h27 : (⟨QuotientGroup.mk' N x, hxK⟩ : ↥(Y.map (QuotientGroup.mk' N))) ^ 27 = 1 := by
        have h3 := cover_cube_center hZ3 h9
        rw [← pow_mul] at h3
        exact h3
      have h27' : (QuotientGroup.mk' N x) ^ 27 = 1 := by
        have h' := congrArg Subtype.val h27
        simpa using h'
      have hdvdN : orderOf (QuotientGroup.mk' N x) ∣ 27 := orderOf_dvd_of_pow_eq_one h27'
      have hxord : orderOf x ∣ Nat.card Q := by
        have h := orderOf_dvd_natCard (⟨x, hxQ⟩ : Q)
        rw [Subgroup.orderOf_mk] at h
        exact h
      have hdvdQ : orderOf (QuotientGroup.mk' N x) ∣ Nat.card Q :=
        (orderOf_map_dvd (QuotientGroup.mk' N) x).trans hxord
      have hcop1 : Nat.Coprime (orderOf (QuotientGroup.mk' N x)) 3 :=
        Nat.Coprime.coprime_dvd_left hdvdQ hQc
      have hcop27 : Nat.Coprime (orderOf (QuotientGroup.mk' N x)) 27 :=
        Nat.Coprime.pow_right 3 hcop1
      have hord1 : orderOf (QuotientGroup.mk' N x) = 1 :=
        Nat.Coprime.eq_one_of_dvd hcop27 hdvdN
      have hmk1 : QuotientGroup.mk' N x = 1 := orderOf_eq_one_iff.mp hord1
      exact (QuotientGroup.eq_one_iff x).mp hmk1
    have hYN : Y ≤ N := by
      intro y hy
      exact (iSup₂_le fun Q hQ => hQN Q hQ.1 hQ.2.1 hQ.2.2) (hgen y hy)
    have hnt : Nontrivial (Subgroup.center ↥(Y.map (QuotientGroup.mk' N))) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ3]; norm_num)
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center ↥(Y.map (QuotientGroup.mk' N)))
    obtain ⟨y, hyY, hyz⟩ := Subgroup.mem_map.mp (z : ↥(Y.map (QuotientGroup.mk' N))).2
    apply hz
    refine Subtype.ext (Subtype.ext ?_)
    rw [← hyz]
    exact (QuotientGroup.eq_one_iff y).mpr (hYN hyY)

theorem exists_noncentral_of_tripleA6 {M : Type*} [Group M] [Finite M] (N Y A : Subgroup M)
    [N.Normal] (hN : (Nat.card N).Coprime 3)
    (hA : ∀ a ∈ A, a ^ 3 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA27 : Nat.card A = 27)
    (hmax : ∀ x : M, orderOf x = 3 → x ∈ Subgroup.centralizer (A : Set M) → x ∈ A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set M))
    (hK : CFSG.RankThree.PartTwo.Sec15.F153Obs.QSLike (Y.map (QuotientGroup.mk' N)))
    (hZ3 : Nat.card (Subgroup.center ↥(Y.map (QuotientGroup.mk' N))) = 3)
    (e : ↥(Y.map (QuotientGroup.mk' N)) ⧸ Subgroup.center ↥(Y.map (QuotientGroup.mk' N)) ≃*
      alternatingGroup (Fin 6))
    (hgen : ∀ y ∈ Y, y ∈ ⨆ (Q : Subgroup M) (_ : Q ≤ Y ∧ A ≤ Subgroup.normalizer (Q : Set M) ∧
      (Nat.card Q).Coprime 3), Q) :
    ∃ y ∈ A, QuotientGroup.mk' N y ∈ Y.map (QuotientGroup.mk' N) ∧
      QuotientGroup.mk' N y ∉ Subgroup.centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)) := by
  have hA3 : IsPGroup 3 A := fun ⟨a, ha⟩ =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA a ha)⟩
  obtain ⟨x, hxK, hx3, hxA, hxC⟩ := exists_good_elt N Y A hA hAc hA27 hAY hK hZ3 e hgen
  obtain ⟨y, hyA, hy⟩ := lift_of_maximal N hN A hA3 hmax x hx3 hxA
  have hy' : QuotientGroup.mk' N y = x := hy
  exact ⟨y, hyA, by rw [hy']; exact hxK, by rw [hy']; exact hxC⟩

end ObsW1c

section ObsG

open Subgroup CFSG.RankThree.PartTwo.Sec15.F153Obs

variable {G : Type*} [Group G] [Finite G]

theorem le_normalizer_subgroupOf (P Y S : Subgroup G)
    (hS : S ≤ Subgroup.normalizer (Y : Set G)) :
    S.subgroupOf P ≤ Subgroup.normalizer ((Y.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have := (Subgroup.mem_normalizer_iff.mp (hS hs)) (z : G)
  simpa [Subgroup.mem_subgroupOf] using this

theorem mem_iSup_subgroupOf (P Y A : Subgroup G) (hYP : Y ≤ P)
    (hgen : ∀ y ∈ Y, y ∈ ⨆ (Q : Subgroup G) (_ : Q ≤ Y ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      (Nat.card Q).Coprime 3), Q) :
    ∀ y ∈ Y.subgroupOf P, y ∈ ⨆ (Q : Subgroup ↥P) (_ : Q ≤ Y.subgroupOf P ∧
      A.subgroupOf P ≤ Subgroup.normalizer (Q : Set ↥P) ∧ (Nat.card Q).Coprime 3), Q := by
  intro y hy
  have hyG := hgen (y : G) hy
  set T : Subgroup ↥P := ⨆ (Q : Subgroup ↥P) (_ : Q ≤ Y.subgroupOf P ∧
      A.subgroupOf P ≤ Subgroup.normalizer (Q : Set ↥P) ∧ (Nat.card Q).Coprime 3), Q
  have hle : (⨆ (Q : Subgroup G) (_ : Q ≤ Y ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      (Nat.card Q).Coprime 3), Q) ≤ T.map P.subtype := by
    refine iSup₂_le fun Q hQ => ?_
    intro q hq
    have hqP : q ∈ P := hYP (hQ.1 hq)
    refine ⟨⟨q, hqP⟩, ?_, rfl⟩
    refine (le_iSup₂ (f := fun (Q' : Subgroup ↥P) (_ : Q' ≤ Y.subgroupOf P ∧
      A.subgroupOf P ≤ Subgroup.normalizer (Q' : Set ↥P) ∧ (Nat.card Q').Coprime 3) => Q')
      (Q.subgroupOf P) ⟨fun z hz => hQ.1 hz, le_normalizer_subgroupOf P Q A hQ.2.1, ?_⟩) ?_
    · have : Nat.card (Q.subgroupOf P) = Nat.card Q :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun z hz => hYP (hQ.1 hz))).toEquiv
      rw [this]; exact hQ.2.2
    · exact hq
  obtain ⟨y', hy', hyy'⟩ := hle hyG
  have : y' = y := Subtype.ext hyy'
  exact this ▸ hy'

theorem normalizes_of_coprime_invariant_inG (X Y A R : Subgroup G) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hA : ∀ a ∈ A, a ^ 3 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA27 : Nat.card A = 27)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hmax : ∀ x : G, orderOf x = 3 → x ∈ Subgroup.centralizer (A : Set G) → x ∈ A)
    (hcase : ¬ 3 ∣ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∨
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)))
    (hgen : ∀ y ∈ Y, y ∈ ⨆ (Q : Subgroup G) (_ : Q ≤ Y ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      (Nat.card Q).Coprime 3), Q)
    (h3 : ∀ E : Subgroup G, E ≤ X → (∀ e ∈ E, e ^ 3 = 1) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E ≤ 27)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hR : (Nat.card R).Coprime 3)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    R ≤ Subgroup.normalizer (Y : Set G) := by
  set P := Subgroup.normalizer (X : Set G) with hPdef
  have hXP : X ≤ P := Subgroup.le_normalizer
  have hYP : Y ≤ P := hYX.trans hXP
  haveI hXn : (X.subgroupOf P).Normal := Subgroup.normal_in_normalizer
  set N : Subgroup ↥P := CFSG.pCore 2 ↥P with hNdef
  have hN : (Nat.card N).Coprime 3 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 N := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (by norm_num)
  have hYX' : Y.subgroupOf P ≤ X.subgroupOf P := fun z hz => hYX hz
  have hXY' := le_normalizer_subgroupOf P Y X hXY
  have hY3' : Y.subgroupOf P = CFSG.GH74.GLS.oPrimeResidualOf 3 (Y.subgroupOf P) := by
    rw [oPrimeResidualOf_subgroupOf 3 Nat.prime_three Y P hYP, ← hY3]
  let eY : ↥(Y.subgroupOf P) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYP
  let qY := quotientPCoreEquiv 2 Nat.prime_two eY
  have hq' : CFSG.IsQuasisimple (↥(Y.subgroupOf P) ⧸ CFSG.pCore 2 ↥(Y.subgroupOf P)) :=
    CFSG.IsQuasisimple.of_mulEquiv qY hq
  have hYN := pCore_subgroupOf_eq (X.subgroupOf P) (Y.subgroupOf P) hYX' hXY'
  obtain ⟨hK, ⟨eK⟩⟩ := qsLike_map_of_subgroupOf_eq N (Y.subgroupOf P) hYN hq'
  let fK := eK.trans qY
  have hAP : A ≤ P := hAX
  have hA' : ∀ a ∈ A.subgroupOf P, a ^ 3 = 1 := fun a ha => Subtype.ext (by simpa using hA a ha)
  have hAc' : ∀ a ∈ A.subgroupOf P, ∀ b ∈ A.subgroupOf P, a * b = b * a :=
    fun a ha b hb => Subtype.ext (by simpa using hAc a ha b hb)
  have hA27' : Nat.card (A.subgroupOf P) = 27 := by
    rw [← hA27]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
  have hmax' : ∀ x : ↥P, orderOf x = 3 → x ∈ Subgroup.centralizer ((A.subgroupOf P : Subgroup ↥P) : Set ↥P) →
      x ∈ A.subgroupOf P := by
    intro x hx3 hxc
    rw [Subgroup.mem_subgroupOf]
    apply hmax (x : G) (by rw [Subgroup.orderOf_coe]; exact hx3)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := (Subgroup.mem_centralizer_iff.mp hxc) ⟨a, hAP ha⟩ (by simpa [Subgroup.mem_subgroupOf] using ha)
    simpa using congrArg Subtype.val this
  have hAY' := le_normalizer_subgroupOf P Y A hAY
  have hAR' := le_normalizer_subgroupOf P R A hAR
  have hR' : (Nat.card (R.subgroupOf P)).Coprime 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv]; exact hR
  have h3' : ∀ E : Subgroup ↥P, E ≤ X.subgroupOf P → (∀ e ∈ E, e ^ 3 = 1) →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ 27 := by
    intro E hEX hE3 hEc
    have := h3 (E.map P.subtype) (by rintro _ ⟨e, he, rfl⟩; exact hEX he)
      (by rintro _ ⟨e, he, rfl⟩; simpa using congrArg Subtype.val (hE3 e he))
      (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩; simpa using congrArg Subtype.val (hEc a ha b hb))
    rwa [Subgroup.card_map_of_injective P.subtype_injective] at this
  obtain ⟨y, hyA, hyK, hyZ⟩ : ∃ y ∈ A.subgroupOf P,
      QuotientGroup.mk' N y ∈ (Y.subgroupOf P).map (QuotientGroup.mk' N) ∧
      QuotientGroup.mk' N y ∉ Subgroup.centralizer
        (((Y.subgroupOf P).map (QuotientGroup.mk' N) : Subgroup (↥P ⧸ N)) : Set (↥P ⧸ N)) := by
    rcases hcase with hZ | ⟨hZ3, ⟨eA6⟩⟩
    · refine exists_noncentral_of_coprime_center N (Y.subgroupOf P) (A.subgroupOf P)
        hN hA' hmax' hAY' hK ?_ ?_
      · rw [Nat.card_congr fK.toEquiv]
        exact three_dvd_card_of_quasisimple Y hY3 hq
      · rw [card_inf_centralizer_eq_card_center, card_center_eq_of_mulEquiv fK]
        exact hZ
    · exact exists_noncentral_of_tripleA6 N (Y.subgroupOf P) (A.subgroupOf P) hN hA' hAc' hA27'
        hmax' hAY' hK ((card_center_eq_of_mulEquiv fK).trans hZ3)
        ((quotientCenterEquiv fK).trans eA6) (mem_iSup_subgroupOf P Y A hYP hgen)
  have hcore := normalizes_of_coprime_invariant N (X.subgroupOf P) (Y.subgroupOf P) (A.subgroupOf P)
    (R.subgroupOf P) hN hYX' hXY' hY3' hK hA' hAY' y hyA hyK hyZ h3' hR' hAR'
  intro r hr
  have hrP : r ∈ P := hRX hr
  have hr' : (⟨r, hrP⟩ : ↥P) ∈ R.subgroupOf P := by simpa [Subgroup.mem_subgroupOf] using hr
  have hn := hcore hr'
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro g
  by_cases hg : g ∈ P
  · have := hn ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hgY; exact absurd (hYP hgY) hg
    · intro hgY
      exfalso; apply hg
      have h1 : r * g * r⁻¹ ∈ P := hYP hgY
      have : g = r⁻¹ * (r * g * r⁻¹) * r := by group
      rw [this]
      exact P.mul_mem (P.mul_mem (P.inv_mem hrP) h1) hrP

end ObsG

end CFSG.RankThree.PartTwo.Sec15.F153Obs
