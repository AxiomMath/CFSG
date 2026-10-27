module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Diag

variable {G : Type} [Group G]

@[expose] def ggDiagProd (y : G) : ℕ → G → G
  | 0, _ => 1
  | n + 1, k => k * (y * ggDiagProd y n k * y⁻¹)

@[simp] theorem ggDiagProd_zero (y k : G) : ggDiagProd y 0 k = 1 := rfl

theorem ggDiagProd_succ (y : G) (n : ℕ) (k : G) :
    ggDiagProd y (n + 1) k = k * (y * ggDiagProd y n k * y⁻¹) := rfl

theorem ggDiagProd_succ' (y : G) (n : ℕ) (k : G) :
    ggDiagProd y (n + 1) k = ggDiagProd y n k * (y ^ n * k * (y ^ n)⁻¹) := by
  induction n with
  | zero => simp [ggDiagProd_succ]
  | succ n ih =>
    calc ggDiagProd y (n + 1 + 1) k = k * (y * ggDiagProd y (n + 1) k * y⁻¹) := rfl
      _ = k * (y * (ggDiagProd y n k * (y ^ n * k * (y ^ n)⁻¹)) * y⁻¹) := by rw [ih]
      _ = (k * (y * ggDiagProd y n k * y⁻¹)) * (y ^ (n + 1) * k * (y ^ (n + 1))⁻¹) := by
          rw [pow_succ']; group
      _ = ggDiagProd y (n + 1) k * (y ^ (n + 1) * k * (y ^ (n + 1))⁻¹) := rfl

@[simp] theorem ggDiagProd_one (y : G) (n : ℕ) : ggDiagProd y n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ggDiagProd_succ, ih]; group

theorem ggDiagProd_conj {y c : G} (hc : c * y = y * c) (n : ℕ) (k : G) :
    c * ggDiagProd y n k * c⁻¹ = ggDiagProd y n (c * k * c⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ggDiagProd_succ, ggDiagProd_succ, ← ih]
    have h1 : c * (y * ggDiagProd y n k * y⁻¹) * c⁻¹ = y * (c * ggDiagProd y n k * c⁻¹) * y⁻¹ :=
      calc c * (y * ggDiagProd y n k * y⁻¹) * c⁻¹
          = (c * y) * ggDiagProd y n k * (c * y)⁻¹ := by group
        _ = (y * c) * ggDiagProd y n k * (y * c)⁻¹ := by rw [hc]
        _ = y * (c * ggDiagProd y n k * c⁻¹) * y⁻¹ := by group
    calc c * (k * (y * ggDiagProd y n k * y⁻¹)) * c⁻¹
        = (c * k * c⁻¹) * (c * (y * ggDiagProd y n k * y⁻¹) * c⁻¹) := by group
      _ = (c * k * c⁻¹) * (y * (c * ggDiagProd y n k * c⁻¹) * y⁻¹) := by rw [h1]

variable {K : Subgroup G} {y : G} {p : ℕ}

theorem ggDiagProd_conj_mem_centralizer
    (hc : ∀ m, 1 ≤ m → m < p → ∀ k ∈ K,
      y ^ m * k * (y ^ m)⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    ∀ n m, 1 ≤ m → m + n ≤ p → ∀ k ∈ K,
      y ^ m * ggDiagProd y n k * (y ^ m)⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  intro n
  induction n with
  | zero => intro m _ _ k _; simp
  | succ n ih =>
    intro m hm hmn k hk
    have h1 := hc m hm (by omega) k hk
    have h2 := ih (m + 1) (by omega) (by omega) k hk
    have : y ^ m * ggDiagProd y (n + 1) k * (y ^ m)⁻¹ =
        (y ^ m * k * (y ^ m)⁻¹) * (y ^ (m + 1) * ggDiagProd y n k * (y ^ (m + 1))⁻¹) := by
      rw [ggDiagProd_succ, pow_succ]; group
    rw [this]
    exact Subgroup.mul_mem _ h1 h2

theorem ggDiagProd_mul
    (hc : ∀ m, 1 ≤ m → m < p → ∀ k ∈ K,
      y ^ m * k * (y ^ m)⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    ∀ n ≤ p, ∀ k ∈ K, ∀ k' ∈ K,
      ggDiagProd y n (k * k') = ggDiagProd y n k * ggDiagProd y n k' := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro hn k hk k' hk'
    have hcent := ggDiagProd_conj_mem_centralizer hc n 1 le_rfl (by omega) k hk
    rw [pow_one] at hcent
    have hcomm : k' * (y * ggDiagProd y n k * y⁻¹) = (y * ggDiagProd y n k * y⁻¹) * k' :=
      Subgroup.mem_centralizer_iff.mp hcent k' hk'
    rw [ggDiagProd_succ, ggDiagProd_succ, ggDiagProd_succ, ih (by omega) k hk k' hk']
    calc k * k' * (y * (ggDiagProd y n k * ggDiagProd y n k') * y⁻¹)
        = k * (k' * (y * ggDiagProd y n k * y⁻¹)) * (y * ggDiagProd y n k' * y⁻¹) := by group
      _ = k * ((y * ggDiagProd y n k * y⁻¹) * k') * (y * ggDiagProd y n k' * y⁻¹) := by
          rw [hcomm]
      _ = k * (y * ggDiagProd y n k * y⁻¹) * (k' * (y * ggDiagProd y n k' * y⁻¹)) := by group

theorem ggDiagProd_conj_self (hp : 1 ≤ p) (hyp : y ^ p = 1)
    (hc : ∀ m, 1 ≤ m → m < p → ∀ k ∈ K,
      y ^ m * k * (y ^ m)⁻¹ ∈ Subgroup.centralizer (K : Set G)) {k : G} (hk : k ∈ K) :
    y * ggDiagProd y p k * y⁻¹ = ggDiagProd y p k := by
  have h1 : ggDiagProd y (p + 1) k = ggDiagProd y p k * k := by
    rw [ggDiagProd_succ', hyp]; group
  have h2 : ggDiagProd y (p + 1) k = k * (y * ggDiagProd y p k * y⁻¹) := ggDiagProd_succ y p k
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hcent := ggDiagProd_conj_mem_centralizer hc q 1 le_rfl (by omega) k hk
  rw [pow_one] at hcent
  have hcomm : k * (y * ggDiagProd y q k * y⁻¹) = (y * ggDiagProd y q k * y⁻¹) * k :=
    Subgroup.mem_centralizer_iff.mp hcent k hk
  have h3 : ggDiagProd y (q + 1) k * k = k * ggDiagProd y (q + 1) k := by
    rw [ggDiagProd_succ, mul_assoc, ← hcomm]
  exact mul_left_cancel (h2.symm.trans (h1.trans h3))

theorem ggDiagProd_mem_iSup {k : G} (hk : k ∈ K) :
    ∀ n ≤ p, ggDiagProd y n k ∈
      ⨆ (i : ℕ) (_ : i < p), K.map (MulAut.conj (y ^ i)).toMonoidHom := by
  intro n
  induction n with
  | zero => intro _; exact Subgroup.one_mem _
  | succ n ih =>
    intro hn
    rw [ggDiagProd_succ']
    refine Subgroup.mul_mem _ (ih (by omega)) ?_
    refine (le_iSup₂ (f := fun (i : ℕ) (_ : i < p) => K.map (MulAut.conj (y ^ i)).toMonoidHom)
      n (by omega)) ?_
    exact ⟨k, hk, rfl⟩

end Diag

section Component

variable {G : Type} [Group G]

theorem mem_normalizer_of_mem_normalizer_map_conj_pow {K : Subgroup G} {y : G} (i : ℕ)
    (h : y ∈ Subgroup.normalizer
      ((K.map (MulAut.conj (y ^ i)).toMonoidHom : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro g
  have key : ∀ x : G, x ∈ K ↔ y ^ i * x * (y ^ i)⁻¹ ∈ K.map (MulAut.conj (y ^ i)).toMonoidHom := by
    intro x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp [mul_assoc]
  rw [key g, key (y * g * y⁻¹), h (y ^ i * g * (y ^ i)⁻¹)]
  have : y * (y ^ i * g * (y ^ i)⁻¹) * y⁻¹ = y ^ i * (y * g * y⁻¹) * (y ^ i)⁻¹ := by
    group
  rw [this]

theorem ggMem_normalizer_of_pow_mem {p : ℕ} (hp : p.Prime) {K : Subgroup G} {y : G}
    (hyp : y ^ p = 1) {m : ℕ} (hm1 : 1 ≤ m) (hmp : m < p)
    (hmem : y ^ m ∈ Subgroup.normalizer (K : Set G)) : y ∈ Subgroup.normalizer (K : Set G) := by
  have hndvd : ¬ p ∣ m := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd).symm
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hy : y = (y ^ m) ^ a := by
    rw [← pow_mul, ← Nat.div_add_mod (m * a) p, ha, pow_add, pow_mul, hyp, one_pow, one_mul,
      pow_one]
  rw [hy]
  exact Subgroup.pow_mem _ hmem a

variable [Finite G]

theorem exists_diagonal_component {p : ℕ} (hp : p.Prime) {H K : Subgroup G} {y : G}
    (hK : IsComponentOf K H) (hyH : y ∈ H) (hyp : y ^ p = 1)
    (hyK : y ∉ Subgroup.normalizer (K : Set G)) :
    ∃ Δ : Subgroup G, IsComponentOf Δ (H ⊓ Subgroup.centralizer {y}) ∧
      ∀ K' : Subgroup G, IsComponentOf K' H → y ∈ Subgroup.normalizer (K' : Set G) →
        Δ ≤ Subgroup.centralizer (K' : Set G) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hKi : ∀ i : ℕ, IsComponentOf (K.map (MulAut.conj (y ^ i)).toMonoidHom) H := fun i => by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK (y ^ i)
    have e : H.map (MulAut.conj (y ^ i)).toMonoidHom = H :=
      CFSG.LocalAnalysis.ComponentInitial.conjSub_eq_of_mem_normalizer
        (Subgroup.le_normalizer (H.pow_mem hyH i))
    rwa [e] at h1
  have hc : ∀ m, 1 ≤ m → m < p → ∀ k ∈ K,
      y ^ m * k * (y ^ m)⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    intro m hm1 hmp k hk
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute (hKi m) hK with h | h
    · exact absurd (ggMem_normalizer_of_pow_mem hp hyp hm1 hmp (mem_normalizer_of_map_conj_eq h))
        hyK
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ⟨k, hk, rfl⟩
  let φ : ↥K →* G :=
    { toFun := fun k => ggDiagProd y p k
      map_one' := ggDiagProd_one y p
      map_mul' := fun a b => ggDiagProd_mul hc p le_rfl a a.2 b b.2 }
  have hφ : ∀ k : ↥K, φ k = ggDiagProd y p k := fun _ => rfl
  have hnontriv : ∃ k : ↥K, φ k ≠ 1 := by
    by_contra hall
    push Not at hall
    apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hK.2.2
    intro k hk
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hcent := ggDiagProd_conj_mem_centralizer hc q 1 le_rfl (by omega) k hk
    rw [pow_one] at hcent
    have h1 : ggDiagProd y p k = 1 := hall ⟨k, hk⟩
    rw [hq, ggDiagProd_succ] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ hcent
  have hΔq : CFSG.Assembly.IsQuasisimple ↥φ.range := by
    have hKn := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      hK.2.2
    obtain ⟨k, hk⟩ := hnontriv
    have := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := φ.rangeRestrict) hKn
      φ.rangeRestrict_surjective ⟨k, fun h => hk (by simpa using congrArg Subtype.val h)⟩
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr this
  have hΔy : φ.range ≤ Subgroup.centralizer {y} := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφ]
    have := ggDiagProd_conj_self hp1 hyp hc k.2
    calc ggDiagProd y p k * y = (y * ggDiagProd y p k * y⁻¹) * y := by rw [this]
      _ = y * ggDiagProd y p k := by group
  set N := ⨆ (i : ℕ) (_ : i < p), K.map (MulAut.conj (y ^ i)).toMonoidHom with hN
  have hΔN : φ.range ≤ N := by
    rintro _ ⟨k, rfl⟩
    exact ggDiagProd_mem_iSup k.2 p le_rfl
  have hNK : N ≤ Subgroup.normalizer (K : Set G) := by
    refine iSup₂_le fun i hi => ?_
    rintro _ ⟨k, hk, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : (MulAut.conj (y ^ 0)).toMonoidHom k = k := by simp
      rw [this]
      exact Subgroup.le_normalizer hk
    · exact Subgroup.centralizer_le_normalizer _ (hc i hi0 hi k hk)
  have hcomp_cent : ∀ K' : Subgroup G, IsComponentOf K' H →
      (∀ i, i < p → K' ≠ K.map (MulAut.conj (y ^ i)).toMonoidHom) →
        N ≤ Subgroup.centralizer (K' : Set G) := by
    intro K' hK' hne
    refine iSup₂_le fun i hi => ?_
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK' (hKi i) with h | h
    · exact absurd h (hne i hi)
    · exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  have hNE : N ≤ LargeEvenLayer H := iSup₂_le fun i _ => le_largeEvenLayer (hKi i)
  have hEN : LargeEvenLayer H ≤ Subgroup.normalizer (N : Set G) := by
    refine sSup_le fun K' hK' => ?_
    by_cases hex : ∃ i, i < p ∧ K' = K.map (MulAut.conj (y ^ i)).toMonoidHom
    · obtain ⟨i, hi, rfl⟩ := hex
      exact (le_iSup₂ (f := fun (i : ℕ) (_ : i < p) => K.map (MulAut.conj (y ^ i)).toMonoidHom)
        i hi).trans Subgroup.le_normalizer
    · push Not at hex
      have := hcomp_cent K' hK' hex
      rw [Subgroup.le_centralizer_iff] at this
      exact this.trans (Subgroup.centralizer_le_normalizer _)
  have hEH : LargeEvenLayer H ≤ H := largeEvenLayer_le H
  have hHE : H ≤ Subgroup.normalizer (LargeEvenLayer H : Set G) := by
    intro h hh
    have key : ∀ g ∈ H,
        (LargeEvenLayer H).map (MulAut.conj g).toMonoidHom ≤ LargeEvenLayer H := by
      intro g hg
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun K' hK' => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK' g
      have e : H.map (MulAut.conj g).toMonoidHom = H :=
        CFSG.LocalAnalysis.ComponentInitial.conjSub_eq_of_mem_normalizer
          (Subgroup.le_normalizer hg)
      rw [e] at h1
      exact le_largeEvenLayer h1
    exact CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_le (key h hh)
      (key h⁻¹ (H.inv_mem hh))
  have hNsn : IsSubnormal N H := by
    refine IsSubnormal.step hNE ?_ (ggIsSubnormal_of_normal hEH ?_)
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNE]; exact hEN
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEH]; exact hHE
  have hsub := ggIsSubnormal_inf hNsn (Subgroup.centralizer {y})
  have hΔle : φ.range ≤ N ⊓ Subgroup.centralizer {y} := le_inf hΔN hΔy
  have hΔn : (φ.range.subgroupOf (N ⊓ Subgroup.centralizer {y})).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΔle]
    rintro _ c ⟨k, rfl⟩ hc'
    obtain ⟨hcN, hcy⟩ := Subgroup.mem_inf.mp hc'
    have hcy' : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hcy
    have hck : c * (k : G) * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hNK hcN) _).mp k.2
    exact ⟨⟨_, hck⟩, by rw [hφ, hφ]; exact (ggDiagProd_conj hcy' p k).symm⟩
  refine ⟨φ.range, ⟨hΔle.trans (inf_le_inf_right _ (hNE.trans hEH)),
    IsSubnormal.step hΔle hΔn hsub, hΔq⟩, fun K' hK' hyK' => ?_⟩
  have hne : ∀ i, i < p → K' ≠ K.map (MulAut.conj (y ^ i)).toMonoidHom := by
    rintro i - rfl
    exact hyK (mem_normalizer_of_mem_normalizer_map_conj_pow i hyK')
  exact hΔN.trans (hcomp_cent K' hK' hne)

end Component

end CFSG.StandardType
