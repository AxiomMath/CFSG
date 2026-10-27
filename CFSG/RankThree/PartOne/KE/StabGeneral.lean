module

public import CFSG.RankThree.PartOne.KE.SigmaPerX

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (charVal charVal_smul charVal_single)
open scoped Matrix Polynomial Pointwise

section Stabilizer

variable {τ : Tag} {L : Type} [Field L]

theorem rootCharStabilizer_subset_closure_of_fixed
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q)
    {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ} (ha : a ∈ fixedCharTuples M Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1)
    (hdual : ∀ z : Fin τ.rank → ZMod p, z ≠ 0 →
      (M.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = (q : ZMod p) • z →
        dualWeylStabilizer z ≤ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) :
    rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    exact ha1 (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  have hord0 : orderOf (a i0) = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hap i0)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hi0
    · exact h
  have hprim : IsPrimitiveRoot ((a i0 : Lˣ) : L) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hord0)
  have hexp : ∀ i, ∃ n : ℕ, a i = (a i0) ^ n := fun i => by
    have hi : ((a i : Lˣ) : L) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  have hker : ∀ l l' : Fin τ.rank → ℤ, rootChar a l = rootChar a l' ↔
      charVal (fun i => (e i : ZMod p)) l = charVal (fun i => (e i : ZMod p)) l' :=
    fun l l' => rootChar_eq_rootChar_iff hord0 e a he l l'
  have hz0 : (fun i => (e i : ZMod p)) ≠ 0 := by
    intro hz
    apply ha1
    funext i
    have h1 : (e i : ZMod p) = 0 := congrFun hz i
    rw [he i]
    have : p ∣ e i := (ZMod.natCast_eq_zero_iff _ _).1 h1
    obtain ⟨m, hm⟩ := this
    rw [hm, pow_mul, ← hord0, pow_orderOf_eq_one, one_pow]
    rfl
  have heig : (M.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ (fun i => (e i : ZMod p)) =
      (q : ZMod p) • (fun i => (e i : ZMod p)) := by
    funext j
    have hcq : rootChar a (M *ᵥ Pi.single j 1) = rootChar a ((q : ℤ) • (Pi.single j 1 :
        Fin τ.rank → ℤ)) := by
      rw [mem_fixedCharTuples_iff.1 ha (Pi.single j 1), CTTorus.map_units_eq_pow hFr,
        rootChar_zsmul, zpow_natCast]
    have h1 := (hker _ _).1 hcq
    rw [charVal_smul, charVal_single] at h1
    have h3 : ∀ i, (M *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ)) i = M i j := fun i => by
      rw [Matrix.mulVec_single_one]
      rfl
    have h2 : charVal (fun i => (e i : ZMod p)) (M *ᵥ Pi.single j 1) =
        ((M.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ fun i => (e i : ZMod p)) j := by
      simp only [charVal, h3]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    rw [h2] at h1
    simpa using h1
  intro w hw
  have hmem : w ∈ dualWeylStabilizer (fun i => (e i : ZMod p)) := fun y =>
    (rootChar_eq_rootChar_iff hord0 e a he (w • y) y).1 (hw y)
  have hmem' := hdual _ hz0 heig hmem
  have hker' : rootKernel (fun i => (e i : ZMod p)) = rootCharKernel a := by
    ext α
    have h := rootChar_eq_rootChar_iff hord0 e a he α 0
    rw [rootChar_zero] at h
    have h0 : charVal (fun i => (e i : ZMod p)) (0 : Fin τ.rank → ℤ) = 0 := by simp [charVal]
    rw [h0] at h
    exact and_congr_right fun _ => h.symm
  rw [hker'] at hmem'
  exact hmem'

end Stabilizer

section Centralizer

variable {τ : Tag} {L : Type} [Field L]

theorem toralCentralizer_le_sup_rootSpan_of_stab {a : Fin τ.rank → Lˣ}
    (hstab : rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    (hSn : ∀ α ∈ S, -α ∈ S) (hker : rootCharKernel a ⊆ S) :
    toralCentralizer τ L a ≤ torusGroup τ L ⊔ rootSpan τ L S := by
  classical
  set Q := rootSpan τ L S with hQ
  set H := torusGroup τ L with hH
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ L a).2.2.2]
  refine sup_le (sup_le le_sup_left ?_) ?_
  · exact (rootSpan_mono hker).trans le_sup_right
  ·
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hwcl := hstab hw
    let N := monomialSubgroup τ L
    let π := weylQuotientHom τ L
    let Wsub : Subgroup (WeylGroup τ) := ((H ⊔ Q).subgroupOf N).map π
    have hgen : ∀ α ∈ S, rootReflection α ∈ Wsub := by
      intro α hα
      have hαr := hS α hα
      obtain ⟨hmem, hπ⟩ := (exceptional_Lang_root_rank_one_torus_transport τ L hαr).2.2.1 1
      refine ⟨⟨rootWeylSL2 τ L α 1, hmem⟩, ?_, hπ⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_sup_right ?_
      exact rootRankOneGroup_le_rootSpan hαr hα (hSn α hα) ⟨_, rfl⟩
    have hclW : Subgroup.closure {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} ≤ Wsub := by
      rw [Subgroup.closure_le]
      rintro _ ⟨α, hα, rfl⟩
      exact hgen α (hker hα)
    obtain ⟨m, hm, hmπ⟩ := hclW hwcl
    have hcanN : canonicalRep (coxeterSystem τ) L w ∈ N := canonicalRep_mem_monomialSubgroup L w
    obtain ⟨ρ, -, hρ, -, -, hρker⟩ := (Weyl_normalizer_quotient τ L).2.1
    have hρπ : ∀ g : N, ρ g = π g := fun g =>
      (hρ g).unique (mapsRootLines_weylQuotientHom g)
    have hcan : π ⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ = w :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)
    have hker1 : (⟨canonicalRep (coxeterSystem τ) L w, hcanN⟩ * m⁻¹ : N) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρπ, hρπ, hcan, hmπ, mul_inv_cancel]
    rw [hρker, Subgroup.mem_subgroupOf] at hker1
    have hker2 : canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹ ∈ H := hker1
    have hmQ : (m : ModGL τ L) ∈ H ⊔ Q := hm
    have hc : canonicalRep (coxeterSystem τ) L w =
        (canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹) * (m : ModGL τ L) := by group
    have h3 : (canonicalRep (coxeterSystem τ) L w * (m : ModGL τ L)⁻¹) * (m : ModGL τ L) ∈
        H ⊔ Q := mul_mem (Subgroup.mem_sup_left hker2) hmQ
    rw [← hc] at h3
    exact h3


theorem mem_torus_mul_rootSpan_of_commute_of_stab {a : Fin τ.rank → Lˣ}
    (hstab : rootCharStabilizer a ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    (hSn : ∀ α ∈ S, -α ∈ S) (hker : rootCharKernel a ⊆ S) {y : ModGL τ L}
    (hy : y ∈ adjointGroup τ L) (hcomm : y * rootDiagUnit τ a = rootDiagUnit τ a * y) :
    y ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L S : Set (ModGL τ L)) := by
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootSpan hS)]
  refine toralCentralizer_le_sup_rootSpan_of_stab hstab hS hSn hker ?_
  exact ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩

end Centralizer

section Embedding

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

theorem sigma_embedding_data_of_stab {τ : Tag} {C : Type} [Group C] {L : Type} [Field L] {ι' : Type}
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hιC : ∀ y, ι y ∈ adjointGroup τ L)
    (Φ : ModGL τ L →* ModGL τ L) (hιΦ : ∀ y, Φ (ι y) = ι y) (n g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf n Φ → rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (P : ι' → Subgroup (ModGL τ L)) (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan τ L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints n Φ) (hPadj : ∀ i, P i ≤ adjointGroup τ L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S)
    {x : C} (hx : orderOf x = p) (c : C)
    (hc : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g0⁻¹ * ι (c * x * c⁻¹) * g0 →
      rootCharKernel a ⊆ S) :
    ∃ ψ : Subgroup.centralizer ({x} : Set C) →* ModGL τ L, Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup τ L ⊔ rootSpan τ L S) ∧
      (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup τ L) ∧
      (∀ i, P i ≤ ψ.range) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
        ∀ v ∈ V, ψ v ∈ subtorusSigma n Φ S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Z := subtorusSigma n Φ S with hZdef
  set Q := rootSpan τ L S with hQdef
  set H := torusGroup τ L with hHdef
  set D := Subgroup.centralizer ({x} : Set C) with hD
  let ψ : D →* ModGL τ L :=
    ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp (MulAut.conj c).toMonoidHom)).comp D.subtype
  have hψ : ∀ y : D, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0 := fun y => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    have h1 := mul_right_cancel (mul_left_cancel hab)
    have h2 := hι h1
    have h3 : (a : C) = b := by
      have := congrArg (fun z => c⁻¹ * z * c) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hψmem : ∀ y : D, ψ y ∈ adjointGroup τ L := fun y => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg0C) (hιC _)) hg0C
  have hψfix : ∀ y : D, n * Φ (ψ y) * n⁻¹ = ψ y := fun y => by
    rw [hψ, map_mul, map_mul, map_inv, hg0, hιΦ]
    group
  have hxD : x ∈ D := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xD : D := ⟨x, hxD⟩ with hxDdef
  set h : ModGL τ L := ψ xD with hh
  have hhZ : h ∈ Z := by
    have := (mem_subtorusImage_iff ι g0 Z (c * x * c⁻¹)).1 hc
    rw [hh, hψ]
    exact this
  have hψx : h = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hψ xD
  have hordh : orderOf h = p := by
    rw [hh, orderOf_injective ψ hψinj xD, ← Subgroup.orderOf_coe]
    exact hx
  have hHh : h ∈ H := (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf n Φ S hhZ)).1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hHh
  have hord' : orderOf (rootDiagUnit τ a) = p := by rw [← ha]; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hord'
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hord'
  have hker := hkerZ a (ha.symm.trans hψx)
  have hcommh : ∀ y : D, ψ y * rootDiagUnit τ a = rootDiagUnit τ a * ψ y := fun y => by
    rw [← ha, hh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hHQ : ∀ y : D, ψ y ∈ H ⊔ Q := fun y => by
    have := mem_torus_mul_rootSpan_of_commute_of_stab
      (hstab a hap ha1 (by rw [← ha]; exact subtorusSigma_le_twistedTorusOf n Φ S hhZ))
      hS hSn hker (hψmem y) (hcommh y)
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootSpan hS)] at this
  set Rs := twistedFixedPoints n Φ with hRs
  have hPψ : ∀ i, P i ≤ ψ.range := by
    intro i u hu
    have huR : n * Φ u * n⁻¹ = u := hPR i hu
    set P' : Subgroup (ModGL τ L) := (P i).map (MulAut.conj g0).toMonoidHom with hP'
    have hP'adj : P' ≤ adjointGroup τ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact mul_mem (mul_mem hg0C (hPadj i hv)) (inv_mem hg0C)
    have hP'fix : ∀ w ∈ P', Φ w = w := by
      rintro _ ⟨v, hv, rfl⟩
      have hvR : n * Φ v * n⁻¹ = v := hPR i hv
      change Φ (g0 * v * g0⁻¹) = g0 * v * g0⁻¹
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * n * Φ v * (g0 * n)⁻¹ = g0 * (n * Φ v * n⁻¹) * g0⁻¹ := by group
        _ = g0 * v * g0⁻¹ := by rw [hvR]
    have hPperf : ⁅P i, P i⁆ = P i := Subgroup.isPerfect_iff.1 (hPq i).1
    have hP'perf : ⁅P', P'⁆ = P' := by
      rw [hP', ← Subgroup.map_commutator, hPperf]
    have hmem : g0 * u * g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hu
    have hPfini : Finite (P i) := hPfin i
    have hP'fin : Finite P' := Finite.of_surjective
      ((MulAut.conj g0).toMonoidHom.subgroupMap (P i))
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective (P i))
    obtain ⟨y', hy'⟩ := hperf P' hP'fin hP'adj hP'fix hP'perf hmem
    have hιx' : ι (c * x * c⁻¹) = g0 * h * g0⁻¹ := by
      rw [hψx]
      group
    have huh : u * h = h * u := Subgroup.mem_centralizer_iff.1 hhZ.2 u (hPQ i hu)
    have hcomm' : y' * (c * x * c⁻¹) = (c * x * c⁻¹) * y' := by
      apply hι
      rw [map_mul ι y' (c * x * c⁻¹), map_mul ι (c * x * c⁻¹) y', hy', hιx']
      calc g0 * u * g0⁻¹ * (g0 * h * g0⁻¹) = g0 * (u * h) * g0⁻¹ := by group
        _ = g0 * (h * u) * g0⁻¹ := by rw [huh]
        _ = g0 * h * g0⁻¹ * (g0 * u * g0⁻¹) := by group
    have hyD : c⁻¹ * y' * c ∈ D := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc c⁻¹ * y' * c * x = c⁻¹ * (y' * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y') * c := by rw [hcomm']
        _ = x * (c⁻¹ * y' * c) := by group
    refine ⟨⟨c⁻¹ * y' * c, hyD⟩, ?_⟩
    rw [hψ]
    change g0⁻¹ * ι (c * (c⁻¹ * y' * c) * c⁻¹) * g0 = u
    rw [show c * (c⁻¹ * y' * c) * c⁻¹ = y' by group, hy']
    group
  have hnorm : ∀ i, ∀ d : D, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i := fun i d u hu =>
    hPnorm i (ψ d) (hHQ d) (hψfix d) u hu
  have hcent : ∀ d : D, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z := fun d hd =>
    hPcent (ψ d) (hHQ d) (hψfix d) hd
  refine ⟨ψ, hψinj, hψ, hHQ, hψfix, hψmem, hPψ, fun V hVn hVs v hv => ?_⟩
  have hle := solvable_normal_le_of_embedding_family ψ hψinj P Z hPψ hPq hnorm hcent V
  exact hle hv


end Embedding

end CFSG.RankThree.PartOne.KE
