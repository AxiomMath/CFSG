module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ToralDescent
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ToralBlocks

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.ToralFinish

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.PartOne.KE

open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

open CFSG.StandardType.F4ExplicitPos.ToralBlocks

open CFSG.StandardType.F4ExplicitPos.ToralDescent

theorem conj_pow_eq_one_F4 {G : Type*} [Group G] (c : G) {x : G} {p : ℕ} (hx : x ^ p = 1) :
    (c * x * c⁻¹) ^ p = 1 := by
  rw [conj_pow, hx, mul_one, mul_inv_cancel]

theorem rootDiagUnit_pow_F4 {L : Type} [Field L] (a : Fin Tag.F4.rank → Lˣ) (p : ℕ) :
    rootDiagUnit Tag.F4 (a ^ p) = rootDiagUnit Tag.F4 a ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ k ih => rw [pow_succ, pow_succ, rootDiagUnit_mul, ih]

theorem mem_kernelWeylGroup_one_F4 {w : WeylGroup Tag.F4} :
    w ∈ kernelWeylGroup (1 : Multiplicative (Fin Tag.F4.rank → ℤ) →* Unit) := by
  have hle : Subgroup.closure (Set.range (simple Tag.F4)) ≤
      kernelWeylGroup (1 : Multiplicative (Fin Tag.F4.rank → ℤ) →* Unit) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨1, i, ⟨isRoot_single Tag.F4 i, rfl⟩, by group⟩
  rw [(coxeterSystem Tag.F4).subgroup_closure_range_simple] at hle
  exact hle (Subgroup.mem_top w)

theorem weylQuotientHom_pow_eq_one_F4
    {L : Type} [Field L] {n : ModGL Tag.F4 L}
    (hn : n ∈ monomialSubgroup Tag.F4 L) {p : ℕ} (hp : n ^ p = 1) :
    weylQuotientHom Tag.F4 L ⟨n, hn⟩ ^ p = 1 := by
  have e : (⟨n, hn⟩ : monomialSubgroup Tag.F4 L) ^ p = 1 := Subtype.ext (by simpa using hp)
  rw [← map_pow, e, map_one]

theorem weylQuotientHom_torus_mul_F4
    {L : Type} [Field L] {k : ModGL Tag.F4 L}
    (hk : k ∈ torusGroup Tag.F4 L) (w : WeylGroup Tag.F4)
    (hn : k * canonicalRep (coxeterSystem Tag.F4) L w ∈ monomialSubgroup Tag.F4 L) :
    weylQuotientHom Tag.F4 L ⟨_, hn⟩ = w :=
  weylQuotientHom_eq (by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w))

theorem monomialToralAt_three_F4 :
    MonomialToralAt Tag.F4 3 :=
  monomialToralAt_three_of_block_F4 CFSG.StandardType.F4ExplicitPos.ToralBlocks.a2BlockToral_F4

theorem exists_conj_mem_torusGroup_of_mem_monomial_F4
    {L : Type} [Field L] [IsAlgClosed L]
    (hL : ringChar L ≠ 3) {n : ModGL Tag.F4 L} (hn : n ∈ monomialSubgroup Tag.F4 L)
    (hp : n ^ 3 = 1) :
    ∃ g ∈ adjointGroup Tag.F4 L, g * n * g⁻¹ ∈ torusGroup Tag.F4 L := by
  obtain ⟨g, hg, hgn⟩ := monomialToralAt_three_F4 L hL Unit 1 n hn mem_kernelWeylGroup_one_F4
    (weylQuotientHom_pow_eq_one_F4 hn hp)
  exact ⟨g, rootSpan_le_adjointGroup L _ hg, hgn⟩

theorem exists_conj_mem_torusGroup_of_mem_monomial_centralizer_F4
    {L : Type} [Field L]
    [IsAlgClosed L] (hL : ringChar L ≠ 3) {a : Fin Tag.F4.rank → Lˣ}
    (hstab : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    {n : ModGL Tag.F4 L} (hn : n ∈ monomialSubgroup Tag.F4 L)
    (hna : rootDiagUnit Tag.F4 a * n = n * rootDiagUnit Tag.F4 a) (hp : n ^ 3 = 1) :
    ∃ g ∈ adjointGroup Tag.F4 L, rootDiagUnit Tag.F4 a * g = g * rootDiagUnit Tag.F4 a ∧
      g * n * g⁻¹ ∈ torusGroup Tag.F4 L := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom Tag.F4 L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul_F4 hk w hn
  have hw : w ∈ rootCharStabilizer a := by
    rw [← conj_canonicalRep_eq_iff]
    have hdk : rootDiagUnit Tag.F4 a * k = k * rootDiagUnit Tag.F4 a :=
      rootDiagUnit_mul_comm_of_mem_torusGroup a hk
    have h1 : rootDiagUnit Tag.F4 a * canonicalRep (coxeterSystem Tag.F4) L w =
        canonicalRep (coxeterSystem Tag.F4) L w * rootDiagUnit Tag.F4 a := by
      have e1 : rootDiagUnit Tag.F4 a * canonicalRep (coxeterSystem Tag.F4) L w =
          k⁻¹ * (rootDiagUnit Tag.F4 a * (k * canonicalRep (coxeterSystem Tag.F4) L w)) := by
        rw [← mul_assoc (rootDiagUnit Tag.F4 a) k, hdk]
        group
      rw [e1, hna]
      group
    rw [h1, mul_inv_cancel_right]
  have hwS : weylQuotientHom Tag.F4 L ⟨_, hn⟩ ∈ kernelWeylGroup (rootCharHom3 a) := by
    rw [hπ]
    exact hstab hw
  obtain ⟨g, hg, hgn⟩ := monomialToralAt_three_F4 L hL Lˣ (rootCharHom3 a) _ hn hwS
    (weylQuotientHom_pow_eq_one_F4 hn hp)
  have hgc : g ∈ Subgroup.centralizer {rootDiagUnit Tag.F4 a} :=
    rootSpan_le_centralizer a (fun _ h => h) hg
  refine ⟨g, rootSpan_le_adjointGroup L _ hg, ?_, hgn⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm

theorem mem_torusGroup_of_monomial_pow_eq_one_F4
    {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup Tag.F4)) {L : Type} [Field L] {n : ModGL Tag.F4 L}
    (hn : n ∈ monomialSubgroup Tag.F4 L) (hnp : n ^ p = 1) : n ∈ torusGroup Tag.F4 L := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom Tag.F4 L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul_F4 hk w hn
  have hw : w ^ p = 1 := by rw [← hπ]; exact weylQuotientHom_pow_eq_one_F4 hn hnp
  have hw1 : w = 1 := by
    by_contra hne
    have h1 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hw
    have h2 : orderOf w = p :=
      ((Nat.dvd_prime hp).1 h1).resolve_left (fun h => hne (orderOf_eq_one_iff.1 h))
    apply hW
    rw [← h2]
    exact orderOf_dvd_natCard w
  rw [hw1, canonicalRep_one, mul_one]
  exact hk

theorem exists_conj_torusGroup_of_pow_eq_one_three_F4
    {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {x : ModGL Tag.F4 L} (hx : x ∈ adjointGroup Tag.F4 L) (hxp : x ^ 3 = 1) :
    ∃ g ∈ adjointGroup Tag.F4 L, g⁻¹ * x * g ∈ torusGroup Tag.F4 L := by
  have hB : Subgroup.zpowers x ≤ adjointGroup Tag.F4 L := Subgroup.zpowers_le.2 hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hxp⟩
  have hBfin : (Subgroup.zpowers x : Set (ModGL Tag.F4 L)).Finite :=
    Set.finite_coe_iff.1 (finite_zpowers.2 hfin)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hexp : ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  obtain ⟨c, hc, hcB⟩ :=
    exists_conj_le_monomial_bar_zmod2 (p := 3) halg (by norm_num : (3 : ℕ) ≠ 2) hB hBfin hexp
  have hmonx : c * x * c⁻¹ ∈ monomialSubgroup Tag.F4 L := hcB x (Subgroup.mem_zpowers x)
  have hpow : (c * x * c⁻¹) ^ 3 = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
  have hL : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  obtain ⟨g', hg', hg't⟩ := exists_conj_mem_torusGroup_of_mem_monomial_F4 hL hmonx hpow
  refine ⟨(g' * c)⁻¹, inv_mem (mul_mem hg' hc), ?_⟩
  rw [inv_inv]
  have e : g' * c * x * (g' * c)⁻¹ = g' * (c * x * c⁻¹) * g'⁻¹ := by group
  rw [e]
  exact hg't

theorem exists_conj_le_torusGroup_of_plane_three_F4
    {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    (hstab : ∀ a : Fin Tag.F4.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    {A : Subgroup (ModGL Tag.F4 L)} (hA : A ≤ adjointGroup Tag.F4 L)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hexp : ∀ x ∈ A, x ^ 3 = 1) (hcard : Nat.card A = 3 ^ 2) :
    ∃ C ∈ adjointGroup Tag.F4 L, ∀ x ∈ A, C * x * C⁻¹ ∈ torusGroup Tag.F4 L := by
  classical
  have hLp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hAfin : (A : Set (ModGL Tag.F4 L)).Finite := Set.toFinite _
  obtain ⟨x₀, hx₀A, hx₀1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < 3 ^ 2 := by norm_num
    omega
  obtain ⟨c₁, hc₁, hc₁N⟩ :=
    exists_conj_le_monomial_bar_zmod2 (p := 3) halg (by norm_num : (3 : ℕ) ≠ 2) hA hAfin hexp
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial_F4 hLp (hc₁N x₀ hx₀A)
    (conj_pow_eq_one_F4 c₁ (hexp x₀ hx₀A))
  set c := g * c₁ with hcdef
  have hcC : c ∈ adjointGroup Tag.F4 L := mul_mem hg hc₁
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  have hda : c * x₀ * c⁻¹ = rootDiagUnit Tag.F4 a := by
    rw [← ha, hcdef]
    group
  have hap : ∀ i, a i ^ 3 = 1 := by
    have h : rootDiagUnit Tag.F4 (a ^ 3) = rootDiagUnit Tag.F4 1 := by
      rw [rootDiagUnit_pow_F4, rootDiagUnit_one, ← hda, conj_pow_eq_one_F4 c (hexp x₀ hx₀A)]
    intro i
    have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
    simpa using this
  set A' := A.map (MulAut.conj c).toMonoidHom with hA'
  have hA'mem : ∀ x ∈ A, c * x * c⁻¹ ∈ A' := fun x hx => ⟨x, hx, rfl⟩
  have hA'C : A' ≤ adjointGroup Tag.F4 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hA hx)) (inv_mem hcC)
  have hA'fin : (A' : Set (ModGL Tag.F4 L)).Finite := Set.Finite.image _ hAfin
  have hA'a : ∀ y ∈ A', rootDiagUnit Tag.F4 a * y = y * rootDiagUnit Tag.F4 a := by
    rintro _ ⟨x, hx, rfl⟩
    change rootDiagUnit Tag.F4 a * (c * x * c⁻¹) = c * x * c⁻¹ * rootDiagUnit Tag.F4 a
    rw [← hda]
    calc c * x₀ * c⁻¹ * (c * x * c⁻¹) = c * (x₀ * x) * c⁻¹ := by group
      _ = c * (x * x₀) * c⁻¹ := by rw [hcomm x₀ hx₀A x hx]
      _ = c * x * c⁻¹ * (c * x₀ * c⁻¹) := by group
  have hA'exp : ∀ y ∈ A', y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one_F4 c (hexp x hx)
  obtain ⟨z, hz, hzd, hzN⟩ :=
    exists_conj_le_monomial_centralizer_bar_zmod2 (p := 3) halg a (by norm_num : (3 : ℕ) ≠ 2)
      hA'C hA'fin hA'a hA'exp
  have hx₀ord : orderOf x₀ = 3 := orderOf_eq_prime (hexp x₀ hx₀A) hx₀1
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y ∈ A, y ∉ Subgroup.zpowers x₀ := by
    by_contra h
    push Not at h
    have heq : A = Subgroup.zpowers x₀ :=
      le_antisymm (fun y hy => h y hy) ((Subgroup.zpowers_le).2 hx₀A)
    rw [heq, Nat.card_zpowers, hx₀ord] at hcard
    have : 3 < 3 ^ 2 := by norm_num
    omega
  set n' := z * (c * y₀ * c⁻¹) * z⁻¹ with hn'
  have hn'N : n' ∈ monomialSubgroup Tag.F4 L := hzN _ (hA'mem y₀ hy₀A)
  have hn'a : rootDiagUnit Tag.F4 a * n' = n' * rootDiagUnit Tag.F4 a := by
    have h1 := hA'a _ (hA'mem y₀ hy₀A)
    have hzd' : rootDiagUnit Tag.F4 a * z⁻¹ = z⁻¹ * rootDiagUnit Tag.F4 a := by
      calc rootDiagUnit Tag.F4 a * z⁻¹ = z⁻¹ * (z * rootDiagUnit Tag.F4 a) * z⁻¹ := by group
        _ = z⁻¹ * (rootDiagUnit Tag.F4 a * z) * z⁻¹ := by rw [hzd]
        _ = z⁻¹ * rootDiagUnit Tag.F4 a := by group
    calc rootDiagUnit Tag.F4 a * n' =
          (rootDiagUnit Tag.F4 a * z) * (c * y₀ * c⁻¹) * z⁻¹ := by rw [hn']; group
      _ = z * (rootDiagUnit Tag.F4 a * (c * y₀ * c⁻¹)) * z⁻¹ := by rw [hzd]; group
      _ = z * (c * y₀ * c⁻¹) * (rootDiagUnit Tag.F4 a * z⁻¹) := by rw [h1]; group
      _ = n' * rootDiagUnit Tag.F4 a := by rw [hzd', hn']; group
  have hn'p : n' ^ 3 = 1 := conj_pow_eq_one_F4 z (hA'exp _ (hA'mem y₀ hy₀A))
  obtain ⟨g', hg', hg'd, hg'n⟩ :=
    exists_conj_mem_torusGroup_of_mem_monomial_centralizer_F4 hLp (hstab a hap) hn'N hn'a hn'p
  set C := g' * z * c with hCdef
  have hCC : C ∈ adjointGroup Tag.F4 L := mul_mem (mul_mem hg' hz) hcC
  refine ⟨C, hCC, ?_⟩
  set S := A ⊓ (torusGroup Tag.F4 L).comap (MulAut.conj C).toMonoidHom with hS
  have hx₀S : x₀ ∈ S := by
    refine ⟨hx₀A, ?_⟩
    change C * x₀ * C⁻¹ ∈ torusGroup Tag.F4 L
    have e : C * x₀ * C⁻¹ = g' * (z * rootDiagUnit Tag.F4 a * z⁻¹) * g'⁻¹ := by
      rw [← hda, hCdef]
      group
    have hzd'' : z * rootDiagUnit Tag.F4 a * z⁻¹ = rootDiagUnit Tag.F4 a := by
      rw [← hzd, mul_inv_cancel_right]
    have hg'd' : g' * rootDiagUnit Tag.F4 a * g'⁻¹ = rootDiagUnit Tag.F4 a := by
      rw [← hg'd, mul_inv_cancel_right]
    rw [e, hzd'', hg'd']
    exact ha ▸ hgn
  have hy₀S : y₀ ∈ S := by
    refine ⟨hy₀A, ?_⟩
    change C * y₀ * C⁻¹ ∈ torusGroup Tag.F4 L
    have e : C * y₀ * C⁻¹ = g' * n' * g'⁻¹ := by
      rw [hCdef, hn']
      group
    rw [e]
    exact hg'n
  have hle : Subgroup.zpowers x₀ ≤ S := (Subgroup.zpowers_le).2 hx₀S
  have hlt : Subgroup.zpowers x₀ < S := lt_of_le_of_ne hle fun h => hy₀ (h ▸ hy₀S)
  have : Finite S := Finite.of_injective (Subgroup.inclusion (inf_le_left : S ≤ A))
    (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hx₀ord] at h1
  have h2 : Nat.card S ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
  rw [hcard] at h2
  have h3 : Nat.card S = 3 ^ 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    interval_cases k
    · rw [hk', pow_zero] at h1
      omega
    · rw [hk', pow_one] at h1
      omega
    · exact hk'
  have hSA : S = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcard])
  intro x hx
  rw [← hSA] at hx
  exact hx.2

theorem isToralSubgroup_of_not_dvd_weyl_F4
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : ¬ p ∣ Nat.card (WeylGroup Tag.F4))
    {A : Subgroup (ModGL Tag.F4 L)} (hA : A ≤ adjointGroup Tag.F4 L) (hfin : Finite A)
    (hel : IsElemAbelian p A) : IsToralSubgroup Tag.F4 L A := by
  have : Fact p.Prime := ⟨hp⟩
  have hAfin : (A : Set (ModGL Tag.F4 L)).Finite := Set.toFinite _
  obtain ⟨c, hc, hcN⟩ := exists_conj_le_monomial_bar_zmod2 (L := L) halg hp2 hA hAfin hel.2
  refine ⟨c⁻¹, inv_mem hc, fun x hx => ?_⟩
  rw [inv_inv]
  exact mem_torusGroup_of_monomial_pow_eq_one_F4 hp hW (hcN x hx)
    (conj_pow_eq_one_F4 c (hel.2 x hx))

end CFSG.StandardType.F4ExplicitPos.ToralFinish
end

end
