module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

theorem eq_top_of_normal_order_three {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K)
    (f : K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) (hR : IsPGroup 2 f.ker)
    {N : Subgroup K} [N.Normal] {b : K} (hbN : b ∈ N) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) :
    N = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hfb : f b ≠ 1 := by
    intro hfb1
    obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hR) ⟨b, MonoidHom.mem_ker.mpr hfb1⟩
    have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hbk
    rw [hord] at h3
    have h32 := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at h32
  haveI hNf : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hNf_top : N.map f = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
    · exfalso
      have hmem : f b ∈ N.map f := Subgroup.mem_map_of_mem f hbN
      rw [h, Subgroup.mem_bot] at hmem
      exact hfb hmem
    · exact h
  have hcover : ∀ k : K, ∃ n ∈ N, n⁻¹ * k ∈ f.ker := by
    intro k
    have hk : f k ∈ N.map f := by
      rw [hNf_top]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hfn⟩ := Subgroup.mem_map.mp hk
    refine ⟨n, hn, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfn, inv_mul_cancel]
  have hQ2 : IsPGroup 2 (K ⧸ N) := by
    refine hR.of_surjective ((QuotientGroup.mk' N).comp f.ker.subtype) ?_
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨n, hn, hr⟩ := hcover k
    refine ⟨⟨n⁻¹ * k, hr⟩, ?_⟩
    have hn1 : (QuotientGroup.mk' N n : K ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    show QuotientGroup.mk' N (n⁻¹ * k) = QuotientGroup.mk' N k
    rw [map_mul, map_inv, hn1, inv_one, one_mul]
  have hnil : Group.IsNilpotent (K ⧸ N) := hQ2.isNilpotent
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hnil
  rw [eq_top_iff]
  intro k _
  exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)

theorem exists_restrict_hom_of_map_eq {V K : Type} [Group V] [Group K] (φ : K →* MulAut V)
    (P : Subgroup V) (hP : ∀ k : K, P.map (MulEquiv.toMonoidHom (φ k)) = P) :
    ∃ ψ : K →* MulAut P, ∀ (k : K) (x : P), ((ψ k x : P) : V) = φ k (x : V) := by
  refine ⟨MonoidHom.mk' (fun k => (MulEquiv.subgroupMap (φ k) P).trans
    (MulEquiv.subgroupCongr (hP k))) fun a b => ?_, fun k x => rfl⟩
  refine MulEquiv.ext fun x => Subtype.ext ?_
  show φ (a * b) (x : V) = φ a (φ b (x : V))
  rw [map_mul, MulAut.mul_apply]

theorem card_le_sq_of_isElemAbelian_subgroup {V : Type} [Group V] (P : Subgroup V) (r : ℕ)
    (hrank : ∀ E : Subgroup V, CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2)
    (E : Subgroup P) (hE : CFSG.Assembly.IsElemAbelian r E) : Nat.card E ≤ r ^ 2 := by
  obtain ⟨hcomm, hexp⟩ : IsMulCommutative E ∧ ∀ x ∈ E, x ^ r = 1 := hE
  have hE' : CFSG.Assembly.IsElemAbelian r (E.map P.subtype) := by
    show IsMulCommutative (E.map P.subtype) ∧ ∀ x ∈ E.map P.subtype, x ^ r = 1
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hexp y hy, map_one]
  have hcard : Nat.card (E.map P.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective (f := P.subtype) Subtype.val_injective
  have h1 := hrank _ hE'
  rw [hcard] at h1
  exact h1

theorem pCore_eq_bot_of_not_dvd_card {V : Type} [Group V] [Finite V] {q : ℕ} [Fact q.Prime]
    (hq : ¬ q ∣ Nat.card V) : CFSG.pCore q V = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := q) (G := V))
  have hdvd : Nat.card (CFSG.pCore q V) ∣ Nat.card V := Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd
  rw [Subgroup.eq_bot_iff_card]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [hn, h0, pow_zero]
  · exact absurd (dvd_trans (dvd_pow_self q hpos.ne') hdvd) hq

theorem fixes_fitting_of_fixes_pCore {V K : Type} [Group V] [Finite V] [Group K]
    (φ : K →* MulAut V) (hfix : ∀ q : ℕ, q.Prime → ∀ k : K, ∀ x ∈ CFSG.pCore q V, φ k x = x)
    (k : K) : ∀ x ∈ CFSG.fittingSubgroup V, φ k x = x := by
  intro x hx
  rw [CFSG.fitting_eq_sup_pCore V] at hx
  refine Subgroup.iSup_induction (C := fun y => φ k y = y)
    (fun p : (Nat.card V).primeFactors.attach => CFSG.pCore p.1.1 V) hx ?_ ?_ ?_
  · intro p y hy
    exact hfix p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) k y hy
  · exact map_one (φ k)
  · intro a b ha hb
    have ha' : φ k a = a := ha
    have hb' : φ k b = b := hb
    show φ k (a * b) = a * b
    rw [map_mul, ha', hb']

theorem fitting_delta_central {V : Type} [Group V]
    (hcent : Subgroup.centralizer (CFSG.fittingSubgroup V : Set V) ≤ CFSG.fittingSubgroup V)
    (α : MulAut V) (hα : ∀ y ∈ CFSG.fittingSubgroup V, α y = y) (v : V) :
    v⁻¹ * α v ∈ CFSG.fittingSubgroup V ∧
      ∀ y ∈ CFSG.fittingSubgroup V, y * (v⁻¹ * α v) = (v⁻¹ * α v) * y := by
  have hFn : (CFSG.fittingSubgroup V).Normal := inferInstance
  have hcomm : ∀ y ∈ CFSG.fittingSubgroup V, v⁻¹ * α v * y = y * (v⁻¹ * α v) := by
    intro y hy
    have hconj : v * y * v⁻¹ ∈ CFSG.fittingSubgroup V := hFn.conj_mem y hy v
    have h1 : α (v * y * v⁻¹) = v * y * v⁻¹ := hα _ hconj
    have h2 : α (v * y * v⁻¹) = α v * y * (α v)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hα y hy]
    have h3 : α v * y * (α v)⁻¹ = v * y * v⁻¹ := h2.symm.trans h1
    calc v⁻¹ * α v * y = v⁻¹ * (α v * y * (α v)⁻¹) * α v := by group
      _ = v⁻¹ * (v * y * v⁻¹) * α v := by rw [h3]
      _ = y * (v⁻¹ * α v) := by group
  have hmem : v⁻¹ * α v ∈ Subgroup.centralizer (CFSG.fittingSubgroup V : Set V) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm y hy).symm
  exact ⟨hcent hmem, fun y hy => (hcomm y hy).symm⟩

theorem mulAut_comm_of_fixes_fitting {V : Type} [Group V]
    (hcent : Subgroup.centralizer (CFSG.fittingSubgroup V : Set V) ≤ CFSG.fittingSubgroup V)
    (α β : MulAut V) (hα : ∀ y ∈ CFSG.fittingSubgroup V, α y = y)
    (hβ : ∀ y ∈ CFSG.fittingSubgroup V, β y = y) : α * β = β * α := by
  ext v
  rw [MulAut.mul_apply, MulAut.mul_apply]
  obtain ⟨hδa, hδa_c⟩ := fitting_delta_central hcent α hα v
  obtain ⟨hδb, _⟩ := fitting_delta_central hcent β hβ v
  have e1 : α (β v) = v * ((v⁻¹ * α v) * (v⁻¹ * β v)) := by
    calc α (β v) = α (v * (v⁻¹ * β v)) := by rw [mul_inv_cancel_left]
      _ = α v * (v⁻¹ * β v) := by rw [map_mul, hα _ hδb]
      _ = v * (v⁻¹ * α v) * (v⁻¹ * β v) := by rw [mul_inv_cancel_left]
      _ = v * ((v⁻¹ * α v) * (v⁻¹ * β v)) := mul_assoc _ _ _
  have e2 : β (α v) = v * ((v⁻¹ * β v) * (v⁻¹ * α v)) := by
    calc β (α v) = β (v * (v⁻¹ * α v)) := by rw [mul_inv_cancel_left]
      _ = β v * (v⁻¹ * α v) := by rw [map_mul, hβ _ hδa]
      _ = v * (v⁻¹ * β v) * (v⁻¹ * α v) := by rw [mul_inv_cancel_left]
      _ = v * ((v⁻¹ * β v) * (v⁻¹ * α v)) := mul_assoc _ _ _
  have hcomm_δ : (v⁻¹ * α v) * (v⁻¹ * β v) = (v⁻¹ * β v) * (v⁻¹ * α v) :=
    (hδa_c _ hδb).symm
  rw [e1, e2, hcomm_δ]

theorem fixes_pCore_of_five_le {V : Type} [Group V] [Finite V]
    (hQ : ∀ (Q : Type) [Group Q] [Finite Q] (r : ℕ), r.Prime → 5 ≤ r → IsPGroup r Q →
      (∀ E : Subgroup Q, CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2) →
      ∀ E : Subgroup (MulAut Q), (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) → (∀ e ∈ E, e ^ 3 = 1) →
        Nat.card E = 9 → ∀ h : MulAut Q, (∀ e ∈ E, h * e * h⁻¹ = e⁻¹) → False)
    (hrank : ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ E : Subgroup V, CFSG.Assembly.IsElemAbelian r E →
      Nat.card E ≤ r ^ 2)
    {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K)
    (f : K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) (hR : IsPGroup 2 f.ker)
    (B : Subgroup K) (hB9 : Nat.card B = 9) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hB3 : ∀ b ∈ B, b ^ 3 = 1) (h : K) (hinv : ∀ b ∈ B, h * b * h⁻¹ = b⁻¹)
    (φ : K →* MulAut V) (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ∀ k : K, ∀ x ∈ CFSG.pCore r V, φ k x = x := by
  have hP : ∀ k : K, (CFSG.pCore r V).map (MulEquiv.toMonoidHom (φ k)) = CFSG.pCore r V :=
    fun k => Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore r V).Characteristic) (φ k)
  obtain ⟨ψ, hψ⟩ := exists_restrict_hom_of_map_eq φ (CFSG.pCore r V) hP
  have hPgrp : IsPGroup r (CFSG.pCore r V) := CFSG.pCore_isPGroup
  have hPrank : ∀ E : Subgroup (CFSG.pCore r V), CFSG.Assembly.IsElemAbelian r E →
      Nat.card E ≤ r ^ 2 :=
    fun E hE => card_le_sq_of_isElemAbelian_subgroup (CFSG.pCore r V) r (hrank r hr hr5) E hE
  have hker : ∃ b ∈ B, b ≠ 1 ∧ ψ b = 1 := by
    by_contra hne
    push Not at hne
    let ψB : B →* MulAut (CFSG.pCore r V) := ψ.comp B.subtype
    have hinj : Function.Injective ψB := by
      rw [injective_iff_map_eq_one]
      intro b hb
      by_contra hb1
      exact hne b.1 b.2 (fun h1 => hb1 (Subtype.ext h1)) hb
    have hcardE : Nat.card ψB.range = 9 := by
      have := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      rw [hB9] at this
      exact this.symm
    have hcomm' : ∀ e ∈ ψB.range, ∀ e' ∈ ψB.range, e * e' = e' * e := by
      intro e he e' he'
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp he
      obtain ⟨b', rfl⟩ := MonoidHom.mem_range.mp he'
      show ψ b.1 * ψ b'.1 = ψ b'.1 * ψ b.1
      rw [← map_mul, ← map_mul, hBc b.1 b.2 b'.1 b'.2]
    have hexp' : ∀ e ∈ ψB.range, e ^ 3 = 1 := by
      intro e he
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp he
      show ψ b.1 ^ 3 = 1
      rw [← map_pow, hB3 b.1 b.2, map_one]
    have hinv' : ∀ e ∈ ψB.range, ψ h * e * (ψ h)⁻¹ = e⁻¹ := by
      intro e he
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp he
      have h1 := congrArg ψ (hinv b.1 b.2)
      simp only [map_mul, map_inv] at h1
      exact h1
    exact hQ ↥(CFSG.pCore r V) r hr hr5 hPgrp hPrank ψB.range hcomm' hexp' hcardE (ψ h) hinv'
  obtain ⟨b, hbB, hb1, hψb⟩ := hker
  have hkerTop : ψ.ker = ⊤ :=
    eq_top_of_normal_order_three hKp f hf hR (MonoidHom.mem_ker.mpr hψb) hb1 (hB3 b hbB)
  intro k x hx
  have hk : k ∈ ψ.ker := by
    rw [hkerTop]
    exact Subgroup.mem_top k
  have hψk : ψ k = 1 := MonoidHom.mem_ker.mp hk
  have h1 := hψ k ⟨x, hx⟩
  rw [hψk, MulAut.one_apply] at h1
  exact h1.symm

theorem eq_one_of_A6_act_solvable
    (hQ : ∀ (Q : Type) [Group Q] [Finite Q] (r : ℕ), r.Prime → 5 ≤ r → IsPGroup r Q →
      (∀ E : Subgroup Q, CFSG.Assembly.IsElemAbelian r E → Nat.card E ≤ r ^ 2) →
      ∀ E : Subgroup (MulAut Q), (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) → (∀ e ∈ E, e ^ 3 = 1) →
        Nat.card E = 9 → ∀ h : MulAut Q, (∀ e ∈ E, h * e * h⁻¹ = e⁻¹) → False)
    {V : Type} [Group V] [Finite V] (hVs : Group.IsSolvable V) (hV3 : ¬ 3 ∣ Nat.card V)
    (hV2 : CFSG.pCore 2 V = ⊥)
    (hrank : ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ E : Subgroup V, CFSG.Assembly.IsElemAbelian r E →
      Nat.card E ≤ r ^ 2)
    {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K)
    (f : K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) (hR : IsPGroup 2 f.ker)
    (B : Subgroup K) (hB9 : Nat.card B = 9) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hB3 : ∀ b ∈ B, b ^ 3 = 1) (h : K) (hinv : ∀ b ∈ B, h * b * h⁻¹ = b⁻¹)
    (φ : K →* MulAut V) : φ = 1 := by
  have hfixq : ∀ q : ℕ, q.Prime → ∀ k : K, ∀ x ∈ CFSG.pCore q V, φ k x = x := by
    intro q hq k x hx
    by_cases hq5 : 5 ≤ q
    · exact fixes_pCore_of_five_le hQ hrank hKp f hf hR B hB9 hBc hB3 h hinv φ q hq hq5 k x hx
    · push Not at hq5
      have h2or3 : q = 2 ∨ q = 3 := by
        have h4 : q ≠ 4 := fun h4 => by
          subst h4
          norm_num at hq
        have h0 : q ≠ 0 := hq.ne_zero
        have h1 : q ≠ 1 := hq.ne_one
        omega
      rcases h2or3 with rfl | rfl
      · rw [hV2, Subgroup.mem_bot] at hx
        rw [hx, map_one]
      · haveI : Fact (Nat.Prime 3) := ⟨hq⟩
        rw [pCore_eq_bot_of_not_dvd_card hV3, Subgroup.mem_bot] at hx
        rw [hx, map_one]
  have hfix : ∀ k : K, ∀ x ∈ CFSG.fittingSubgroup V, φ k x = x :=
    fun k => fixes_fitting_of_fixes_pCore φ hfixq k
  have hcent := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hVs
  have hcomm : ∀ k k' : K, φ k * φ k' = φ k' * φ k := fun k k' =>
    mulAut_comm_of_fixes_fitting hcent (φ k) (φ k') (hfix k) (hfix k')
  have hker : ∀ g : K, φ g = 1 := by
    intro g
    have hg : g ∈ commutator K := by
      rw [hKp.commutator_eq_top]
      exact Subgroup.mem_top g
    have hle : commutator K ≤ φ.ker := by
      refine Subgroup.commutator_le.mpr ?_
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm g₁ g₂
    exact MonoidHom.mem_ker.mp (hle hg)
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  exact hker g

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
