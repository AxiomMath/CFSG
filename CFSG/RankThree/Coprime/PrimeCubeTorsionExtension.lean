module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG
open scoped IsMulCommutative commutatorElement

section Maschke

theorem exists_isCompl_invariant_subgroup_of_coprime {p : ℕ} [Fact p.Prime]
    {A G : Type*} [Group A] [Fintype A] [Group G] [IsElementaryAbelian p G]
    [MulDistribMulAction A G] (hA : ¬ p ∣ Fintype.card A) (U : Subgroup G)
    (hU : ∀ a : A, ∀ g : G, g ∈ U → a • g ∈ U) :
    ∃ W : Subgroup G, IsCompl U W ∧ ∀ a : A, ∀ g : G, g ∈ W → a • g ∈ W := by
  classical
  let e : Subgroup G ≃o Submodule (ZMod p) (Additive G) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  let rho := Theory.Representation.ofElementaryAbelianAction (A := A) (G := G) (p := p)
  have hUmod : ∀ a : A, ∀ v ∈ e U, rho a v ∈ e U := by
    intro a v hv
    change Additive.toMul v ∈ U at hv
    change Additive.toMul (rho a v) ∈ U
    simpa [rho] using hU a (Additive.toMul v) hv
  have hUinv : e U ∈ rho.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact hUmod a
  let Upack : rho.invtSubmodule := ⟨e U, hUinv⟩
  let instAdd : AddCommGroup rho.asModule := Representation.instAddCommGroupAsModule rho
  let : AddCommGroup rho.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod p) A) rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  let : Module (MonoidAlgebra (ZMod p) A) rho.asModule := instMod
  have : NeZero (Fintype.card A : ZMod p) := by
    constructor
    intro hzero
    exact hA ((ZMod.natCast_eq_zero_iff (Fintype.card A) p).1 hzero)
  let Umod : @Submodule (MonoidAlgebra (ZMod p) A) rho.asModule _
      instAdd.toAddCommMonoid instMod :=
    rho.mapSubmodule Upack
  obtain ⟨Wmod, hUWmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    (ZMod p) inferInstance A inferInstance inferInstance rho.asModule
      instAdd instMod inferInstance Umod
  let Wpack : rho.invtSubmodule := rho.mapSubmodule.symm Wmod
  have hcompl_pack : IsCompl Upack Wpack :=
    (rho.mapSubmodule.isCompl_iff).2 (by simpa [Umod, Wpack] using hUWmod)
  have hcompl : IsCompl (e U) (Wpack : Submodule (ZMod p) (Additive G)) := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Upack] using congrArg Subtype.val hcompl_pack.1
    · simpa [Upack] using congrArg Subtype.val hcompl_pack.2
  refine ⟨e.symm Wpack, ?_, ?_⟩
  · apply e.isCompl_iff.mpr
    simpa using hcompl
  · intro a g hg
    have hgmod : Additive.ofMul g ∈ (Wpack : Submodule (ZMod p) (Additive G)) := by
      simpa [e] using hg
    have hmem := (Representation.mem_invtSubmodule (ρ := rho)).1 Wpack.2 a
    have hsmul := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (rho a)).1 hmem _ hgmod
    simpa [e, rho] using hsmul

end Maschke


section Aut

theorem card_le_of_isPGroup_mulAut {p : ℕ} [hp : Fact p.Prime] {T : Type*} [Group T] [Finite T]
    (hexp : ∀ x : T, x ^ p = 1) (hcard : Nat.card T = p ^ 2)
    (Q : Subgroup (MulAut T)) (hQ : IsPGroup p Q) : Nat.card Q ≤ p := by
  classical
  have hp1 := hp.out.one_lt
  have hfix := hQ.card_modEq_card_fixedPoints T
  have hF0 : Nat.card (MulAction.fixedPoints Q T) % p = 0 := by
    rw [Nat.ModEq, hcard] at hfix
    rw [← hfix]
    simp [Nat.pow_mod]
  have h1 : (1 : T) ∈ MulAction.fixedPoints Q T := fun q => by
    change (q : MulAut T) 1 = 1
    exact map_one _
  obtain ⟨v, hvF, hv1⟩ : ∃ v ∈ MulAction.fixedPoints Q T, v ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : MulAction.fixedPoints Q T ⊆ {1} := fun x hx => h x hx
    have hcardF : Nat.card (MulAction.fixedPoints Q T) ≤ 1 := by
      calc Nat.card (MulAction.fixedPoints Q T) ≤ Nat.card ({1} : Set T) :=
            Nat.card_mono (Set.toFinite _) hsub
        _ = 1 := by simp
    have hpos : 0 < Nat.card (MulAction.fixedPoints Q T) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have := Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero hF0)
    omega
  have hqv : ∀ q : Q, (q : MulAut T) v = v := fun q => hvF q
  set L := zpowers v with hL
  have hLcard : Nat.card L = p := by
    rw [hL, Nat.card_zpowers, orderOf_eq_prime (hexp v) hv1]
  have hqL : ∀ q : Q, ∀ x ∈ L, (q : MulAut T) x ∈ L := by
    rintro q _ ⟨k, rfl⟩
    rw [map_zpow, hqv]
    exact zpow_mem (mem_zpowers v) k
  let _ : MulAction.QuotientAction Q L :=
    ⟨fun q {a a'} h => by
      change ((q : MulAut T) a)⁻¹ * (q : MulAut T) a' ∈ L
      rw [← map_inv, ← map_mul]
      exact hqL q _ h⟩
  have hfix2 := hQ.card_modEq_card_fixedPoints (T ⧸ L)
  have hQcard : Nat.card (T ⧸ L) = p := by
    have h := L.card_eq_card_quotient_mul_card_subgroup
    rw [hcard, hLcard, sq] at h
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos h.symm
  have hallfix : ∀ q : Q, ∀ x : T, x⁻¹ * (q : MulAut T) x ∈ L := by
    have hF2 : Nat.card (MulAction.fixedPoints Q (T ⧸ L)) % p = 0 := by
      rw [Nat.ModEq, hQcard, Nat.mod_self] at hfix2
      exact hfix2.symm
    have hmk1 : ((1 : T) : T ⧸ L) ∈ MulAction.fixedPoints Q (T ⧸ L) := fun q => by
      change ((((q : MulAut T) 1) : T) : T ⧸ L) = _
      rw [map_one]
    have hpos : 0 < Nat.card (MulAction.fixedPoints Q (T ⧸ L)) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨_, hmk1⟩⟩, inferInstance⟩
    have hge := Nat.le_of_dvd hpos (Nat.dvd_of_mod_eq_zero hF2)
    have huniv : MulAction.fixedPoints Q (T ⧸ L) = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, hQcard, ← Nat.card_coe_set_eq]
      exact hge
    intro q x
    have hx : (x : T ⧸ L) ∈ MulAction.fixedPoints Q (T ⧸ L) := huniv ▸ Set.mem_univ _
    have h := hx q
    change ((((q : MulAut T) x) : T) : T ⧸ L) = (x : T ⧸ L) at h
    exact QuotientGroup.eq.mp h.symm
  obtain ⟨u, huL⟩ : ∃ u : T, u ∉ L := by
    by_contra h
    push Not at h
    have hLtop : L = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [hLtop, Subgroup.card_top, hcard] at hLcard
    have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
    rw [pow_one] at this
    omega
  have hgen : closure ({u, v} : Set T) = ⊤ := by
    have hle : L < closure ({u, v} : Set T) := by
      refine lt_of_le_of_ne (zpowers_le.mpr (subset_closure (by simp))) fun h => huL ?_
      rw [h]
      exact subset_closure (by simp)
    have hlt := Subgroup.card_lt_of_lt hle
    rw [hLcard] at hlt
    have hdvd := Subgroup.card_subgroup_dvd_card (closure ({u, v} : Set T))
    rw [hcard] at hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rw [hk'] at hlt
    have hk2 : k = 2 := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h
      · rw [h, pow_zero] at hlt; omega
      · rw [h, pow_one] at hlt; omega
      · exact h
    rw [← Subgroup.card_eq_iff_eq_top, hk', hk2, hcard]
  let f : Q → L := fun q => ⟨u⁻¹ * (q : MulAut T) u, hallfix q u⟩
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    have hu : (q₁ : MulAut T) u = (q₂ : MulAut T) u := by
      have := congrArg Subtype.val h
      simpa [f] using this
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hhom : (q₁ : MulAut T).toMonoidHom = (q₂ : MulAut T).toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_dense hgen ?_
      rintro y (rfl | rfl)
      · exact hu
      · change (q₁ : MulAut T) y = (q₂ : MulAut T) y
        rw [hqv, hqv]
    exact DFunLike.congr_fun hhom x
  calc Nat.card Q ≤ Nat.card L := Nat.card_le_card_of_injective f hf
    _ = p := hLcard

end Aut


section Cube

variable {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P] [Finite P]

theorem prime_cube_facts {S : Subgroup P} (hScard : Nat.card S = p ^ 3)
    (hSnc : ∃ a b : S, a * b ≠ b * a) :
    Nat.card ((center S).map S.subtype) = p ∧ ⁅S, S⁆ = (center S).map S.subtype ∧
      ∀ T : Subgroup P, T ≤ S → Nat.card T = p ^ 2 →
        (center S).map S.subtype ≤ T ∧ (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
          ∀ s ∈ S, (∀ t ∈ T, s * t = t * s) → s ∈ T := by
  obtain ⟨hcomm, hZcard, -, -, -, hT, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (S := S) hScard hSnc
  refine ⟨by rw [card_map_of_injective S.subtype_injective, hZcard], ?_, ?_⟩
  · rw [← hcomm, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro T hTS hTcard
    have hT' : Nat.card (T.subgroupOf S) = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv, hTcard]
    obtain ⟨hZT, -, hTab, hTcent⟩ := hT (T.subgroupOf S) hT'
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hZT hz
    · intro x hx y hy
      exact congrArg Subtype.val (hTab ⟨x, hTS hx⟩ hx ⟨y, hTS hy⟩ hy)
    · intro s hs hst
      have hmem : (⟨s, hs⟩ : S) ∈ centralizer (T.subgroupOf S : Set S) := by
        rw [mem_centralizer_iff]
        intro t ht
        exact Subtype.ext (hst t ht).symm
      rw [hTcent] at hmem
      exact hmem

omit hp [Finite P] in
theorem omega₁_centralizer_eq_center {S : Subgroup P} (hSmem : ∀ x : P, x ^ p = 1 → x ∈ S)
    (hSexp : ∀ x ∈ S, x ^ p = 1) :
    (omega₁ (centralizer (S : Set P)) (p := p)).map (centralizer (S : Set P)).subtype =
      (center S).map S.subtype := by
  apply le_antisymm
  · rw [omega₁, omega, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : P) ^ p = 1 := by
      have h : y ^ (p ^ 1) = 1 := hy
      rw [pow_one] at h
      exact congrArg Subtype.val h
    rw [SetLike.mem_coe, mem_map_center_iff]
    exact ⟨hSmem _ hy', fun l hl => mem_centralizer_iff.mp y.2 l hl⟩
  · intro z hz
    rw [mem_map_center_iff] at hz
    have hzC : z ∈ centralizer (S : Set P) := mem_centralizer_iff.mpr hz.2
    refine ⟨⟨z, hzC⟩, subset_closure ?_, rfl⟩
    change (⟨z, hzC⟩ : centralizer (S : Set P)) ^ (p ^ 1) = 1
    rw [pow_one]
    exact Subtype.ext (hSexp z hz.1)

theorem isCyclic_centralizer {S : Subgroup P} (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hSmem : ∀ x : P, x ^ p = 1 → x ∈ S) (hSexp : ∀ x ∈ S, x ^ p = 1)
    (hZ : Nat.card ((center S).map S.subtype) = p) : IsCyclic (centralizer (S : Set P)) := by
  by_contra hnc
  have : Fact (IsPGroup p (centralizer (S : Set P))) := ⟨hP.to_subgroup _⟩
  obtain ⟨E, -, hEcard, hE⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hEle : E.map (centralizer (S : Set P)).subtype ≤ (center S).map S.subtype := by
    rw [← omega₁_centralizer_eq_center hSmem hSexp]
    exact Subgroup.map_mono elementaryAbelian_le_omega₁
  have h := Subgroup.card_le_of_le hEle
  rw [card_map_of_injective (subtype_injective _), hEcard, hZ] at h
  have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  rw [pow_one] at this
  omega

end Cube


section Supplement

theorem smul_mem_of_characteristic {A P : Type*} [Group A] [Group P] [MulDistribMulAction A P]
    (K : Subgroup P) [hK : K.Characteristic] (a : A) {x : P} (hx : x ∈ K) : a • x ∈ K := by
  have h := hK.fixed (MulDistribMulAction.toMulAut A P a)
  have hx' : x ∈ K.comap (MulDistribMulAction.toMulAut A P a).toMonoidHom := by
    rw [h]
    exact hx
  exact hx'

theorem isCyclic_of_forall_pow_eq_one_mem {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (hp2 : p ≠ 2) (hP : IsPGroup p P) (H Z : Subgroup P) (hZ : Nat.card Z ≤ p)
    (hHZ : ∀ x ∈ H, x ^ p = 1 → x ∈ Z) : IsCyclic H := by
  by_contra hnc
  have : Fact (IsPGroup p H) := ⟨hP.to_subgroup _⟩
  obtain ⟨E, -, hEcard, hE⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hEle : E.map H.subtype ≤ Z := by
    rintro _ ⟨e, he, rfl⟩
    refine hHZ _ e.2 ?_
    have := hE
    have h := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
    change (e : P) ^ p = 1
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  have h := Subgroup.card_le_of_le hEle
  rw [card_map_of_injective (subtype_injective _), hEcard] at h
  have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  rw [pow_one] at this
  omega

theorem exists_invariant_supplement_of_coprime {p : ℕ} [hp : Fact p.Prime] {A P : Type*}
    [Group A] [Finite A] [Group P] [MulDistribMulAction A P] (hA : ¬ p ∣ Nat.card A)
    (B C T : Subgroup P) (hCB : C ≤ B)
    (hBinv : ∀ a : A, ∀ x ∈ B, a • x ∈ B) (hCinv : ∀ a : A, ∀ x ∈ C, a • x ∈ C)
    (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ C) (hpow : ∀ x ∈ B, x ^ p ∈ C) :
    ∃ X : Subgroup P, (∀ a : A, ∀ x ∈ X, a • x ∈ X) ∧ C ≤ X ∧ X ≤ B ∧ B ≤ T ⊔ X ∧
      T ⊓ X ≤ C := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  have hA' : ¬ p ∣ Fintype.card A := by rwa [← Nat.card_eq_fintype_card]
  have hBI : IsInvariant A P B :=
    ⟨fun a g => ⟨hBinv a g, fun h => by simpa using hBinv a⁻¹ _ h⟩⟩
  let N : Subgroup B := C.subgroupOf B
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : P) ∈ C := hn
    show ((g * n * g⁻¹ : B) : P) ∈ C
    have h := hcomm g g.2 n n.2
    have heq : ((g * n * g⁻¹ : B) : P) = ((g : P) * n * (g : P)⁻¹ * (n : P)⁻¹) * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact C.mul_mem h hn'
  have hNI : IsInvariant A B N :=
    ⟨fun a g => ⟨fun h => hCinv a g h, fun h => by
      have h' := hCinv a⁻¹ _ h
      change a⁻¹ • a • (g : P) ∈ C at h'
      rw [inv_smul_smul] at h'
      exact h'⟩⟩
  let _ : MulAction.QuotientAction A N := quotientAction_of_isInvariant (A := A) (G := B) N hNI
  let _ : MulDistribMulAction A (B ⧸ N) := quotientMulDistribMulAction (A := A) (G := B) N hNI
  have hVcomm : ∀ x y : B ⧸ N, x * y = y * x := by
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (((x * y)⁻¹ * (y * x) : B) : P) ∈ C
    have heq : (((x * y)⁻¹ * (y * x) : B) : P) =
        (y : P)⁻¹ * (x : P)⁻¹ * ((y : P)⁻¹)⁻¹ * ((x : P)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact hcomm _ (B.inv_mem y.2) _ (B.inv_mem x.2)
  have hVpow : ∀ x : B ⧸ N, x ^ p = 1 := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    show ((x ^ p : B) : P) ∈ C
    rw [Subgroup.coe_pow]
    exact hpow _ x.2
  have hVea : IsElementaryAbelian p (B ⧸ N) :=
    { toIsMulCommutative := ⟨⟨hVcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hVpow }
  have hsmul : ∀ (a : A) (b : B), a • QuotientGroup.mk' N b = QuotientGroup.mk' N (a • b) :=
    fun a b => MulAction.Quotient.smul_coe (H := N) a b
  let U : Subgroup (B ⧸ N) := (T.subgroupOf B).map (QuotientGroup.mk' N)
  have hUinv : ∀ a : A, ∀ v : B ⧸ N, v ∈ U → a • v ∈ U := by
    rintro a _ ⟨t, ht, rfl⟩
    exact ⟨a • t, hTinv a t ht, (hsmul a t).symm⟩
  obtain ⟨W, hUW, hWinv⟩ :=
    exists_isCompl_invariant_subgroup_of_coprime (p := p) (A := A) (G := B ⧸ N) hA' U hUinv
  have hmk1 : ∀ n : B, n ∈ N → QuotientGroup.mk' N n = 1 := fun n hn => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hn
  refine ⟨(W.comap (QuotientGroup.mk' N)).map B.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro a _ ⟨b, hb, rfl⟩
    refine ⟨a • b, ?_, rfl⟩
    change QuotientGroup.mk' N (a • b) ∈ W
    rw [← hsmul]
    exact hWinv a _ hb
  · intro c hc
    refine ⟨⟨c, hCB hc⟩, ?_, rfl⟩
    change QuotientGroup.mk' N ⟨c, hCB hc⟩ ∈ W
    rw [hmk1 _ hc]
    exact W.one_mem
  · rintro _ ⟨b, -, rfl⟩
    exact b.2
  · intro b hb
    have hmem : QuotientGroup.mk' N ⟨b, hb⟩ ∈ U ⊔ W := by
      rw [hUW.sup_eq_top]
      exact mem_top _
    obtain ⟨_, ⟨t, ht, rfl⟩, w, hw, huw⟩ := Subgroup.mem_sup.mp hmem
    obtain ⟨b₁, rfl⟩ := QuotientGroup.mk'_surjective N w
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at huw
    have hb₁n : b₁ * ((t * b₁)⁻¹ * ⟨b, hb⟩) ∈ W.comap (QuotientGroup.mk' N) := by
      change QuotientGroup.mk' N (b₁ * ((t * b₁)⁻¹ * ⟨b, hb⟩)) ∈ W
      rw [map_mul, hmk1 _ huw, mul_one]
      exact hw
    have hbeq : b = (t : P) * ((b₁ * ((t * b₁)⁻¹ * ⟨b, hb⟩) : B) : P) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hbeq]
    exact mul_mem_sup (show (t : P) ∈ T from ht) ⟨_, hb₁n, rfl⟩
  · rintro _ ⟨hxT, ⟨b, hb, rfl⟩⟩
    have h1 : QuotientGroup.mk' N b ∈ U ⊓ W := ⟨⟨b, hxT, rfl⟩, hb⟩
    rw [hUW.inf_eq_bot, Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
    exact h1

end Supplement

section Main

open scoped Pointwise

theorem prime_cube_torsion_cyclic_extension_alternative {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) {A : Type*} [Group A] [Finite A]
    [MulDistribMulAction A P] (hA : Nat.Coprime (Nat.card A) p)
    (hScard : Nat.card (omega₁ P (p := p)) = p ^ 3)
    (hSexp : ∀ x ∈ omega₁ P (p := p), x ^ p = 1)
    (hSnc : ∃ x ∈ omega₁ P (p := p), ∃ y ∈ omega₁ P (p := p), x * y ≠ y * x) :
    let S := omega₁ P (p := p)
    let Z := (center S).map S.subtype
    let C := centralizer (S : Set P)
    let T := ⁅S, (⊤ : Subgroup P)⁆
    (IsCyclic C ∧ (omega₁ C (p := p)).map C.subtype = Z) ∧
      ((S : Set P) * (C : Set P) = Set.univ ∨
        ∃ X : Subgroup P, (∀ a : A, ∀ x ∈ X, a • x ∈ X) ∧ IsCyclic X ∧
          (∀ a : A, ∀ t ∈ T, a • t ∈ T) ∧ T.Normal ∧ Nat.card T = p ^ 2 ∧ Z ≤ T ∧ T ≤ S ∧
          C ≤ X ∧ (S : Set P) * (X : Set P) = Set.univ ∧ ⁅T, X⁆ = ⊥ ∧ ¬ ⁅S, X⁆ ≤ Z) := by
  intro S Z C T
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hSmem : ∀ x : P, x ^ p = 1 → x ∈ S := fun x hx =>
    subset_closure (show x ^ (p ^ 1) = 1 by rwa [pow_one])
  have hSnc' : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hSnc
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  obtain ⟨hZcard, hcommZ, hTfacts⟩ := prime_cube_facts (S := S) hScard hSnc'
  have hZcard' : Nat.card Z = p := hZcard
  have hcommZ' : ⁅S, S⁆ = Z := hcommZ
  have hSchar : S.Characteristic := omega₁_characteristic P
  have hCchar : C.Characteristic := by
    change (centralizer (S : Set P)).Characteristic
    infer_instance
  have hTchar : T.Characteristic := by
    change (⁅S, (⊤ : Subgroup P)⁆).Characteristic
    infer_instance
  have hSn : S.Normal := inferInstance
  have hZn : Z.Normal := by
    rw [← hcommZ']
    infer_instance
  refine ⟨⟨isCyclic_centralizer hp2 hP hSmem hSexp hZcard,
    omega₁_centralizer_eq_center hSmem hSexp⟩, ?_⟩
  by_cases hTZ : T ≤ Z
  ·
    left
    obtain ⟨-, -, -, -, -, -, hinner⟩ :=
      CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (S := S) hScard hSnc'
    rw [Set.eq_univ_iff_forall]
    intro x
    have hα : ∀ s : S, s⁻¹ * MulAut.conjNormal x s ∈ center S := by
      intro s
      have h1 : ((s⁻¹ * MulAut.conjNormal x s : S) : P) ∈ Z := by
        apply hTZ
        have heq : ((s⁻¹ * MulAut.conjNormal x s : S) : P) = ⁅(s : P)⁻¹, x⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
            commutatorElement_def, inv_inv]
          group
        rw [heq]
        exact Subgroup.commutator_mem_commutator (S.inv_mem s.2) (mem_top x)
      exact (Subgroup.mem_map_iff_mem S.subtype_injective).mp h1
    obtain ⟨g, hg⟩ := hinner (MulAut.conjNormal x) hα
    have hgx : (g : P)⁻¹ * x ∈ C := by
      rw [mem_centralizer_iff]
      intro s hs
      have h := congrArg (fun φ : MulAut S => ((φ ⟨s, hs⟩ : S) : P)) hg
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      calc s * ((g : P)⁻¹ * x) = (g : P)⁻¹ * ((g : P) * s * (g : P)⁻¹) * x := by group
        _ = (g : P)⁻¹ * (x * s * x⁻¹) * x := by rw [h]
        _ = (g : P)⁻¹ * x * s := by group
    exact ⟨g, g.2, (g : P)⁻¹ * x, hgx, by group⟩
  · right
    have hTS : T ≤ S := Subgroup.commutator_le_left S ⊤
    have hZT : Z ≤ T := by
      rw [← hcommZ']
      exact Subgroup.commutator_mono le_rfl le_top
    have hTne : T ≠ S := by
      intro hTSeq
      obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hP.isNilpotent
      have hle : ∀ k, S ≤ (⊤ : Subgroup P).lowerCentralSeries k := by
        intro k
        induction k with
        | zero => exact le_top
        | succ k ih =>
          rw [Subgroup.lowerCentralSeries_succ]
          calc S = T := hTSeq.symm
            _ ≤ _ := Subgroup.commutator_mono ih le_rfl
      have hSbot : S = ⊥ := le_bot_iff.mp (hn ▸ hle n)
      have h3 := hScard
      change Nat.card S = p ^ 3 at h3
      rw [hSbot, Subgroup.card_bot] at h3
      have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp1
      omega
    have hTcard : Nat.card T = p ^ 2 := by
      have hdvd : Nat.card T ∣ p ^ 3 := hScard ▸ Subgroup.card_dvd_of_le hTS
      obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have hk' : k ≠ 3 := by
        rintro rfl
        exact hTne (Subgroup.eq_of_le_of_card_ge hTS (by rw [hk]; exact hScard.le))
      have hZTne : Z ≠ T := fun h => hTZ (h ▸ le_rfl)
      have hlt : p < Nat.card T := by
        rw [← hZcard']
        exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hZT hZTne)
      have hk2 : 2 ≤ k := by
        by_contra hk2
        rw [not_le] at hk2
        interval_cases k
        · rw [hk, pow_zero] at hlt
          omega
        · rw [hk, pow_one] at hlt
          omega
      rw [hk, show k = 2 by omega]
    obtain ⟨-, -, hTcent⟩ := hTfacts T hTS hTcard
    have hTn : T.Normal := inferInstance
    set B : Subgroup P := centralizer (T : Set P) with hB
    have hBchar : B.Characteristic := by
      rw [hB]
      infer_instance
    have hCB : C ≤ B := Subgroup.centralizer_le hTS
    have hSB : ¬ S ≤ B := by
      intro hSB
      apply hTne
      refine le_antisymm hTS fun s hs => hTcent s hs fun t ht => ?_
      exact ((mem_centralizer_iff.mp (hSB hs)) t ht).symm
    let φ : P →* MulAut T := MulAut.conjNormal
    have hker : φ.ker = B := by
      ext x
      rw [MonoidHom.mem_ker, hB, mem_centralizer_iff]
      constructor
      · intro h t ht
        have h1 : x * t * x⁻¹ = t := by
          have := congrArg Subtype.val (DFunLike.congr_fun h ⟨t, ht⟩)
          simpa [φ] using this
        calc t * x = x * t * x⁻¹ * x := by rw [h1]
          _ = x * t := by group
      · intro h
        refine MulEquiv.ext fun t => Subtype.ext ?_
        have h1 := h t t.2
        simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply]
        calc x * (t : P) * x⁻¹ = (t : P) * x * x⁻¹ := by rw [h1]
          _ = t := by group
    have hTexp : ∀ x : T, x ^ p = 1 := fun x =>
      Subtype.ext (by simpa using hSexp _ (hTS x.2))
    have hrange : Nat.card φ.range ≤ p :=
      card_le_of_isPGroup_mulAut hTexp hTcard φ.range
        (hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
    have hidxle : B.index ≤ p := by
      rw [← hker, Subgroup.index_ker]
      exact hrange
    have hBne : B ≠ ⊤ := fun h => hSB (h ▸ le_top)
    obtain ⟨n, hn⟩ := hP.index B
    have hidx : B.index = p := by
      have hn1 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero, Subgroup.index_eq_one] at hn
        exact hBne hn
      have hn2 : n ≤ 1 := by
        by_contra h
        have h1 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos (by omega)
        have h2 : p < p ^ 2 := by nlinarith
        omega
      rw [hn, show n = 1 by omega, pow_one]
    have hBS : B ⊔ S = ⊤ := by
      have hdvd : (B ⊔ S).index ∣ B.index := Subgroup.index_dvd_of_le le_sup_left
      rw [hidx] at hdvd
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact Subgroup.index_eq_one.mp h
      · exfalso
        have h1 := Subgroup.card_mul_index (B ⊔ S)
        have h2 := Subgroup.card_mul_index B
        rw [h] at h1
        rw [hidx] at h2
        have hcard : Nat.card (B ⊔ S : Subgroup P) = Nat.card B :=
          Nat.eq_of_mul_eq_mul_right hp.pos (h1.trans h2.symm)
        have heq : B = B ⊔ S := Subgroup.eq_of_le_of_card_ge le_sup_left hcard.le
        exact hSB (le_sup_right.trans heq.symm.le)
    have hTB0 : ⁅T, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
    have hBST : ⁅B, S⁆ ≤ T := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl le_top
    have hSBT : ⁅S, B⁆ ≤ T := Subgroup.commutator_mono le_rfl le_top
    have h3 : ⁅⁅B, B⁆, S⁆ = ⊥ := by
      apply Subgroup.commutator_commutator_eq_bot_of_rotate
      · exact le_bot_iff.mp ((Subgroup.commutator_mono hBST le_rfl).trans hTB0.le)
      · exact le_bot_iff.mp ((Subgroup.commutator_mono hSBT le_rfl).trans hTB0.le)
    have hBBC' : ⁅B, B⁆ ≤ C := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
    have hBBC : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ C := fun x hx y hy => by
      rw [← commutatorElement_def]
      exact hBBC' (Subgroup.commutator_mem_commutator hx hy)
    have hBpow : ∀ b ∈ B, b ^ p ∈ C := by
      intro b hb
      rw [mem_centralizer_iff]
      intro s hs
      obtain ⟨t, ht⟩ : ∃ t, t = b * s * b⁻¹ * s⁻¹ := ⟨_, rfl⟩
      have htT : t ∈ T := hBST (by
        rw [ht, ← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator hb hs)
      have hbt : Commute b t := (mem_centralizer_iff.mp hb t htT).symm
      have hbs : b * s * b⁻¹ = t * s := by
        rw [ht]
        group
      have hconj : ∀ k : ℕ, b ^ k * s * (b ^ k)⁻¹ = t ^ k * s := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc b ^ (k + 1) * s * (b ^ (k + 1))⁻¹ = b * (b ^ k * s * (b ^ k)⁻¹) * b⁻¹ := by
                group
            _ = b * (t ^ k * s) * b⁻¹ := by rw [ih]
            _ = b * t ^ k * b⁻¹ * (b * s * b⁻¹) := by group
            _ = t ^ k * (t * s) := by rw [(hbt.pow_right k).eq, mul_inv_cancel_right, hbs]
            _ = t ^ (k + 1) * s := by rw [pow_succ, mul_assoc]
      have htp : t ^ p = 1 := hSexp t (hTS htT)
      have h := hconj p
      rw [htp, one_mul] at h
      calc s * b ^ p = b ^ p * s * (b ^ p)⁻¹ * b ^ p := by rw [h]
        _ = b ^ p * s := by group
    have hBinv : ∀ a : A, ∀ x ∈ B, a • x ∈ B := fun a x hx => smul_mem_of_characteristic B a hx
    have hCinv : ∀ a : A, ∀ x ∈ C, a • x ∈ C := fun a x hx => smul_mem_of_characteristic C a hx
    have hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T := fun a x hx => smul_mem_of_characteristic T a hx
    have hA' : ¬ p ∣ Nat.card A := (Nat.Prime.coprime_iff_not_dvd hp).mp hA.symm
    obtain ⟨X, hXinv, hCX, hXB, hBTX, hTXC⟩ :=
      exists_invariant_supplement_of_coprime hA' B C T hCB hBinv hCinv hTinv hBBC hBpow
    have hSX : S ⊔ X = ⊤ := by
      rw [eq_top_iff, ← hBS]
      exact sup_le (hBTX.trans (sup_le_sup_right hTS X)) le_sup_left
    have hXZ : ∀ x ∈ X, x ^ p = 1 → x ∈ Z := by
      intro x hx hxp
      have hxS := hSmem x hxp
      have hxT : x ∈ T := hTcent x hxS fun t ht => ((mem_centralizer_iff.mp (hXB hx)) t ht).symm
      have hxC : x ∈ C := hTXC ⟨hxT, hx⟩
      exact mem_map_center_iff.mpr ⟨hxS, fun l hl => mem_centralizer_iff.mp hxC l hl⟩
    refine ⟨X, hXinv, isCyclic_of_forall_pow_eq_one_mem hp2 hP X Z hZcard'.le hXZ, hTinv, hTn,
      hTcard, hZT, hTS, hCX, ?_, ?_, ?_⟩
    · rw [← Subgroup.normal_mul, hSX, Subgroup.coe_top]
    · rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXB
    ·
      intro hSXZ
      apply hTZ
      let q : P →* P ⧸ Z := QuotientGroup.mk' Z
      let K : Subgroup P := (centralizer ((S.map q : Subgroup (P ⧸ Z)) : Set (P ⧸ Z))).comap q
      have hq : ∀ s g : P, ⁅s, g⁆ ∈ Z ↔ q s * q g = q g * q s := fun s g => by
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← MonoidHom.mem_ker,
          QuotientGroup.ker_mk']
      have hK : ∀ g : P, (∀ s ∈ S, ⁅s, g⁆ ∈ Z) → g ∈ K := by
        intro g hg
        rw [Subgroup.mem_comap, mem_centralizer_iff]
        rintro _ ⟨s, hs, rfl⟩
        exact (hq s g).mp (hg s hs)
      have hSK : S ≤ K := fun g hg => hK g fun s hs => by
        rw [← hcommZ']
        exact Subgroup.commutator_mem_commutator hs hg
      have hXK : X ≤ K := fun g hg => hK g fun s hs =>
        hSXZ (Subgroup.commutator_mem_commutator hs hg)
      have hKtop : K = ⊤ := eq_top_iff.mpr (hSX ▸ sup_le hSK hXK)
      rw [Subgroup.commutator_le]
      intro s hs g _
      have hgK : g ∈ K := hKtop ▸ mem_top g
      rw [Subgroup.mem_comap, mem_centralizer_iff] at hgK
      exact (hq s g).mpr (hgK (q s) ⟨s, hs, rfl⟩)

end Main

end CFSG.RankThree.Coprime
