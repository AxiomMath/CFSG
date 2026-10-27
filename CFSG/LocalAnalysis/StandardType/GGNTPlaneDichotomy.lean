module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Helpers

private theorem ntp_weyl_mem_stab
    {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hna : rootDiagUnit τ a * n = n * rootDiagUnit τ a) :
    weylQuotientHom τ L ⟨n, hn⟩ ∈ rootCharStabilizerSubgroup a := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom τ L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul hk w hn
  rw [hπ, mem_rootCharStabilizerSubgroup]
  rw [← conj_canonicalRep_eq_iff]
  have hdk : rootDiagUnit τ a * k = k * rootDiagUnit τ a :=
    rootDiagUnit_mul_comm_of_mem_torusGroup a hk
  have h1 : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w =
      canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ a := by
    have e1 : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w =
        k⁻¹ * (rootDiagUnit τ a * (k * canonicalRep (coxeterSystem τ) L w)) := by
      rw [← mul_assoc (rootDiagUnit τ a) k, hdk]
      group
    rw [e1, hna]
    group
  rw [h1, mul_inv_cancel_right]

private theorem ntp_toral_of_weyl_mem_kernel
    {τ : Tag} {p : ℕ}
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ p)
    {a : Fin τ.rank → Lˣ} {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hna : rootDiagUnit τ a * n = n * rootDiagUnit τ a) (hp : n ^ p = 1)
    (hker : weylQuotientHom τ L ⟨n, hn⟩ ∈ kernelReflectionGroup a) :
    ∃ g ∈ adjointGroup τ L, rootDiagUnit τ a * g = g * rootDiagUnit τ a ∧
      g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  obtain ⟨g, hg, hgn⟩ := hmon L hL Lˣ
    (CFSG.HardMathSupport.Timmesfeld.Steinberg.rootCharHom3 a) _ hn hker
    (weylQuotientHom_pow_eq_one hn hp)
  have hgc : g ∈ Subgroup.centralizer {rootDiagUnit τ a} :=
    rootSpan_le_centralizer a (fun _ h => h) hg
  refine ⟨g, rootSpan_le_adjointGroup L _ hg, ?_, hgn⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm

end Helpers

theorem plane_nontoral_normal_form
    {τ : Tag} {p : ℕ} [hp : Fact p.Prime]
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ p) [CharP L ℓ] (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1)
    (hcard : Nat.card A = p ^ 2)
    (hnt : ¬ ∃ C ∈ adjointGroup τ L, ∀ x ∈ A, C * x * C⁻¹ ∈ torusGroup τ L)
    {x₀ : ModGL τ L} (hx₀ : x₀ ∈ A) (hx₀1 : x₀ ≠ 1) :
    ∃ C ∈ adjointGroup τ L, ∃ a : Fin τ.rank → Lˣ, ∃ n : ModGL τ L,
      (∀ i, a i ^ p = 1) ∧ C * x₀ * C⁻¹ = rootDiagUnit τ a ∧
      A.map (MulAut.conj C).toMonoidHom = Subgroup.zpowers (rootDiagUnit τ a) ⊔ Subgroup.zpowers n ∧
      ∃ hn : n ∈ monomialSubgroup τ L, n ^ p = 1 ∧ rootDiagUnit τ a * n = n * rootDiagUnit τ a ∧
        weylQuotientHom τ L ⟨n, hn⟩ ∈ rootCharStabilizerSubgroup a ∧
        weylQuotientHom τ L ⟨n, hn⟩ ∉ kernelReflectionGroup a := by
  classical
  have hp1 := hp.out.one_lt
  have hLp : ringChar L ≠ p := by rw [ringChar.eq L ℓ]; exact hℓ
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hAfin : (A : Set (ModGL τ L)).Finite := Set.toFinite _
  obtain ⟨c₁, hc₁, hc₁N⟩ := exists_conj_le_monomial_bar hℓ halg hA hAfin hexp
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLp (hc₁N x₀ hx₀)
    (conj_pow_eq_one' c₁ (hexp x₀ hx₀))
  set c := g * c₁ with hcdef
  have hcC : c ∈ adjointGroup τ L := mul_mem hg hc₁
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  have hda : c * x₀ * c⁻¹ = rootDiagUnit τ a := by
    rw [← ha, hcdef]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ← hda, conj_pow_eq_one' c (hexp x₀ hx₀)]
    intro i
    have := congrFun (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h) i
    simpa using this
  set A' := A.map (MulAut.conj c).toMonoidHom with hA'
  have hA'mem : ∀ x ∈ A, c * x * c⁻¹ ∈ A' := fun x hx => ⟨x, hx, rfl⟩
  have hA'C : A' ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hA hx)) (inv_mem hcC)
  have hA'fin : (A' : Set (ModGL τ L)).Finite := Set.Finite.image _ hAfin
  have hA'a : ∀ y ∈ A', rootDiagUnit τ a * y = y * rootDiagUnit τ a := by
    rintro _ ⟨x, hx, rfl⟩
    change rootDiagUnit τ a * (c * x * c⁻¹) = c * x * c⁻¹ * rootDiagUnit τ a
    rw [← hda]
    calc c * x₀ * c⁻¹ * (c * x * c⁻¹) = c * (x₀ * x) * c⁻¹ := by group
      _ = c * (x * x₀) * c⁻¹ := by rw [hcomm x₀ hx₀ x hx]
      _ = c * x * c⁻¹ * (c * x₀ * c⁻¹) := by group
  have hA'exp : ∀ y ∈ A', y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c (hexp x hx)
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ halg a hA'C hA'fin hA'a
    hA'exp
  have hx₀ord : orderOf x₀ = p := orderOf_eq_prime (hexp x₀ hx₀) hx₀1
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y ∈ A, y ∉ Subgroup.zpowers x₀ := by
    by_contra h
    push Not at h
    have heq : A = Subgroup.zpowers x₀ :=
      le_antisymm (fun y hy => h y hy) ((Subgroup.zpowers_le).2 hx₀)
    rw [heq, Nat.card_zpowers, hx₀ord] at hcard
    have : p < p ^ 2 := by nlinarith
    omega
  set n' := z * (c * y₀ * c⁻¹) * z⁻¹ with hn'
  have hn'N : n' ∈ monomialSubgroup τ L := hzN _ (hA'mem y₀ hy₀A)
  have hn'a : rootDiagUnit τ a * n' = n' * rootDiagUnit τ a := by
    have h1 := hA'a _ (hA'mem y₀ hy₀A)
    have hzd' : rootDiagUnit τ a * z⁻¹ = z⁻¹ * rootDiagUnit τ a := by
      calc rootDiagUnit τ a * z⁻¹ = z⁻¹ * (z * rootDiagUnit τ a) * z⁻¹ := by group
        _ = z⁻¹ * (rootDiagUnit τ a * z) * z⁻¹ := by rw [hzd]
        _ = z⁻¹ * rootDiagUnit τ a := by group
    calc rootDiagUnit τ a * n' = (rootDiagUnit τ a * z) * (c * y₀ * c⁻¹) * z⁻¹ := by
          rw [hn']; group
      _ = z * (rootDiagUnit τ a * (c * y₀ * c⁻¹)) * z⁻¹ := by rw [hzd]; group
      _ = z * (c * y₀ * c⁻¹) * (rootDiagUnit τ a * z⁻¹) := by rw [h1]; group
      _ = n' * rootDiagUnit τ a := by rw [hzd', hn']; group
  have hn'p : n' ^ p = 1 := conj_pow_eq_one' z (hA'exp _ (hA'mem y₀ hy₀A))
  set C₀ := z * c with hC₀def
  have hC₀C : C₀ ∈ adjointGroup τ L := mul_mem hz hcC
  have hC₀x₀ : C₀ * x₀ * C₀⁻¹ = rootDiagUnit τ a := by
    calc C₀ * x₀ * C₀⁻¹ = z * (c * x₀ * c⁻¹) * z⁻¹ := by rw [hC₀def]; group
      _ = z * rootDiagUnit τ a * z⁻¹ := by rw [hda]
      _ = rootDiagUnit τ a := by rw [← hzd]; group
  have hC₀y₀ : C₀ * y₀ * C₀⁻¹ = n' := by
    rw [hC₀def, hn']
    group
  have hstab : weylQuotientHom τ L ⟨n', hn'N⟩ ∈ rootCharStabilizerSubgroup a :=
    ntp_weyl_mem_stab hn'N hn'a
  have hnotker : weylQuotientHom τ L ⟨n', hn'N⟩ ∉ kernelReflectionGroup a := by
    intro hker
    obtain ⟨g', hg', hg'd, hg'n⟩ := ntp_toral_of_weyl_mem_kernel hmon hLp hn'N hn'a hn'p hker
    set C' := g' * C₀ with hC'def
    have hC'C : C' ∈ adjointGroup τ L := mul_mem hg' hC₀C
    have hC'x₀ : C' * x₀ * C'⁻¹ ∈ torusGroup τ L := by
      have e : C' * x₀ * C'⁻¹ = g' * rootDiagUnit τ a * g'⁻¹ := by
        rw [← hC₀x₀, hC'def, hC₀def]
        group
      have hg'd' : g' * rootDiagUnit τ a * g'⁻¹ = rootDiagUnit τ a := by
        rw [← hg'd, mul_inv_cancel_right]
      rw [e, hg'd']
      exact ha ▸ hgn
    have hC'y₀ : C' * y₀ * C'⁻¹ ∈ torusGroup τ L := by
      have e : C' * y₀ * C'⁻¹ = g' * n' * g'⁻¹ := by
        rw [← hC₀y₀, hC'def, hC₀def]
        group
      rw [e]
      exact hg'n
    set S := A ⊓ (torusGroup τ L).comap (MulAut.conj C').toMonoidHom with hS
    have hx₀S : x₀ ∈ S := by
      refine ⟨hx₀, ?_⟩
      change C' * x₀ * C'⁻¹ ∈ torusGroup τ L
      exact hC'x₀
    have hy₀S : y₀ ∈ S := by
      refine ⟨hy₀A, ?_⟩
      change C' * y₀ * C'⁻¹ ∈ torusGroup τ L
      exact hC'y₀
    have hle : Subgroup.zpowers x₀ ≤ S := (Subgroup.zpowers_le).2 hx₀S
    have hlt : Subgroup.zpowers x₀ < S := lt_of_le_of_ne hle fun h => hy₀ (h ▸ hy₀S)
    have : Finite S := Finite.of_injective (Subgroup.inclusion (inf_le_left : S ≤ A))
      (Subgroup.inclusion_injective _)
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, hx₀ord] at h1
    have h2 : Nat.card S ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
    rw [hcard] at h2
    have h3 : Nat.card S = p ^ 2 := by
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 h2
      interval_cases k
      · rw [hk', pow_zero] at h1
        omega
      · rw [hk', pow_one] at h1
        omega
      · exact hk'
    have hSA : S = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcard])
    exact hnt ⟨C', hC'C, fun x hx => by
      rw [← hSA] at hx
      exact hx.2⟩
  have hmap : A.map (MulAut.conj C₀).toMonoidHom =
      Subgroup.zpowers (rootDiagUnit τ a) ⊔ Subgroup.zpowers n' := by
    let T : Subgroup (ModGL τ L) :=
      Subgroup.zpowers (rootDiagUnit τ a) ⊔ Subgroup.zpowers n'
    have hle1 : A.map (MulAut.conj C₀).toMonoidHom ≤ T := by
      set S := A ⊓ T.comap (MulAut.conj C₀).toMonoidHom with hS
      have hx₀S : x₀ ∈ S := by
        refine ⟨hx₀, ?_⟩
        change C₀ * x₀ * C₀⁻¹ ∈ T
        rw [hC₀x₀]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      have hy₀S : y₀ ∈ S := by
        refine ⟨hy₀A, ?_⟩
        change C₀ * y₀ * C₀⁻¹ ∈ T
        rw [hC₀y₀]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      have hle : Subgroup.zpowers x₀ ≤ S := (Subgroup.zpowers_le).2 hx₀S
      have hlt : Subgroup.zpowers x₀ < S := lt_of_le_of_ne hle fun h => hy₀ (h ▸ hy₀S)
      have : Finite S := Finite.of_injective (Subgroup.inclusion (inf_le_left : S ≤ A))
        (Subgroup.inclusion_injective _)
      have h1 := Subgroup.card_lt_of_lt hlt
      rw [Nat.card_zpowers, hx₀ord] at h1
      have h2 : Nat.card S ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
      rw [hcard] at h2
      have h3 : Nat.card S = p ^ 2 := by
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 h2
        interval_cases k
        · rw [hk', pow_zero] at h1
          omega
        · rw [hk', pow_one] at h1
          omega
        · exact hk'
      have hSA : S = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcard])
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.mp (hSA.symm ▸ hx).2
    have hge1 : T ≤ A.map (MulAut.conj C₀).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact ⟨x₀, hx₀, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hC₀x₀⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨y₀, hy₀A, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hC₀y₀⟩
    exact le_antisymm hle1 hge1
  exact ⟨C₀, hC₀C, a, n', hap, hC₀x₀, hmap, hn'N, hn'p, hn'a, hstab, hnotker⟩

end CFSG.StandardType.NTPlane

end
