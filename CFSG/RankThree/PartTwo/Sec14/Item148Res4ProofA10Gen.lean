module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofTenTools
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofA10

public section

namespace CFSG.RankThree.PartTwo.Sec14

open Equiv

namespace Item148Res4

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem isThreeCycle_of_seven_dvd {σ : Perm (Fin 10)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer {σ})) : σ.IsThreeCycle := by
  obtain ⟨k, hk1, hk3, hsum, hcard⟩ := card_centralizer_perm_ten_of_pow_three h3 h1
  have hmem : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have hdvd : n ∣ 3 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h3)
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hk : k = 1 := by
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
    · exact h
    · rw [hcard, h] at h7
      norm_num [Nat.factorial] at h7
    · rw [hcard, h] at h7
      norm_num [Nat.factorial] at h7
  have hc : Multiset.card σ.cycleType = 1 := by
    have h' : (Multiset.replicate (Multiset.card σ.cycleType) 3).sum = 3 * 1 := by
      rw [← hrep, hsum, hk]
    rw [Multiset.sum_replicate, smul_eq_mul] at h'
    omega
  rw [Equiv.Perm.IsThreeCycle, hrep, hc]
  rfl

theorem apply_mem_support_iff_of_commute {σ τ : Perm α} (h : Commute σ τ) (i : α) :
    τ i ∈ σ.support ↔ i ∈ σ.support := by
  rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support]
  have e : σ (τ i) = τ (σ i) := by
    rw [← Equiv.Perm.mul_apply, h.eq, Equiv.Perm.mul_apply]
  rw [e]
  exact τ.injective.ne_iff

theorem apply_eq_of_isPerfect {σ : Perm α} (hσ : σ.support.card ≤ 4)
    {K : Subgroup (Perm α)} (hKσ : K ≤ Subgroup.centralizer {σ}) (hK : Group.IsPerfect ↥K)
    {k : Perm α} (hk : k ∈ K) {i : α} (hi : i ∈ σ.support) : k i = i := by
  have hcomm : ∀ g : ↥K, Commute σ (g : Perm α) := fun g =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKσ g.2)).symm
  set ρ : ↥K →* Perm {x // x ∈ σ.support} :=
    { toFun := fun g => (g : Perm α).subtypePerm (apply_mem_support_iff_of_commute (hcomm g))
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl } with hρ
  have hsolv : Group.IsSolvable (Perm {x // x ∈ σ.support}) := by
    refine Equiv.Perm.isSolvable ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hσ
  have hRp : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
  have hRs : Group.IsSolvable ↥ρ.range := inferInstance
  have hR : ρ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥ρ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable ↥ρ.range hRs
  have h1 : ρ ⟨k, hk⟩ = 1 := by
    have : ρ ⟨k, hk⟩ ∈ ρ.range := ⟨_, rfl⟩
    rwa [hR, Subgroup.mem_bot] at this
  have h2 := congrArg (fun π : Perm {x // x ∈ σ.support} => (π ⟨i, hi⟩ : α)) h1
  exact h2

theorem disjoint_support_of_commute {σ τ : Perm α} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hc : Commute σ τ) (hnot : τ ∉ Subgroup.zpowers σ) : Disjoint σ.support τ.support := by
  rw [Finset.disjoint_left]
  intro i hiσ hiτ
  apply hnot
  have hiσ' : σ i ≠ i := Equiv.Perm.mem_support.mp hiσ
  have hiτ' : τ i ≠ i := Equiv.Perm.mem_support.mp hiτ
  have hτi : τ i ∈ σ.support := (apply_mem_support_iff_of_commute hc i).mpr hiσ
  obtain ⟨m, hm⟩ := hσ.exists_pow_eq hiσ' (Equiv.Perm.mem_support.mp hτi)
  refine ⟨(m : ℤ), ?_⟩
  have hρc : Commute σ ((σ ^ m)⁻¹ * τ) :=
    ((Commute.pow_right (Commute.refl σ) m).inv_right).mul_right hc
  have hρi : ((σ ^ m)⁻¹ * τ) i = i := by
    rw [Equiv.Perm.mul_apply, ← hm, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  have hρ1 : (σ ^ m)⁻¹ * τ = 1 := by
    ext j
    rw [Equiv.Perm.one_apply]
    by_cases hj : σ j = j
    ·
      have hτj : τ j = j := by
        by_contra hτj
        obtain ⟨l, hl⟩ := hτ.exists_pow_eq hiτ' hτj
        have hpres : (τ ^ l) i ∈ σ.support :=
          (apply_mem_support_iff_of_commute (Commute.pow_right hc l) i).mpr hiσ
        rw [hl] at hpres
        exact (Equiv.Perm.mem_support.mp hpres) hj
      have hσmj : (σ ^ m) j = j := by
        have := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hj m
        exact this
      rw [Equiv.Perm.mul_apply, hτj, Equiv.Perm.inv_eq_iff_eq, hσmj]
    · obtain ⟨l, hl⟩ := hσ.exists_pow_eq hiσ' hj
      have hcl : Commute (σ ^ l) ((σ ^ m)⁻¹ * τ) := Commute.pow_left hρc l
      rw [← hl, ← Equiv.Perm.mul_apply, ← hcl.eq, Equiv.Perm.mul_apply, hρi]
  have : τ = σ ^ m := by
    have := congrArg (fun g => σ ^ m * g) hρ1
    simpa [mul_assoc] using this
  show σ ^ (m : ℤ) = τ
  rw [this, zpow_natCast]

theorem card_le_of_forall_apply_eq (S : Finset α) (H : Subgroup (Perm α))
    (hH : ∀ h ∈ H, ∀ i ∈ S, h i = i) :
    Nat.card H ≤ (Fintype.card α - S.card).factorial := by
  have hpres : ∀ h : ↥H, ∀ x, (h : Perm α) x ∉ S ↔ x ∉ S := by
    intro h x
    constructor
    · intro hx hxS
      exact hx (by rw [hH h h.2 x hxS]; exact hxS)
    · intro hx hxS
      apply hx
      have h1 := hH h h.2 _ hxS
      have h2 : (h : Perm α) x = x := (h : Perm α).injective h1
      rwa [h2] at hxS
  set f : ↥H → Perm {x // x ∉ S} := fun h => (h : Perm α).subtypePerm (hpres h) with hf
  have hfinj : Function.Injective f := by
    intro g h hgh
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ S
    · rw [hH g g.2 x hx, hH h h.2 x hx]
    · have := congrArg (fun π : Perm {x // x ∉ S} => (π ⟨x, hx⟩ : α)) hgh
      exact this
  have hcard := Nat.card_le_card_of_injective f hfinj
  rw [Nat.card_eq_fintype_card (α := Perm {x // x ∉ S}), Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_coe] at hcard
  exact hcard

end Perm

theorem kf148A10Gen_holds :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* alternatingGroup (Fin 10)) →
      ∀ (E K M : Subgroup X) (x : X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
        x ∈ E → x ≠ 1 → K ≤ Subgroup.centralizer ({x} : Set X) →
        Nonempty (↥K ≃* alternatingGroup (Fin 7)) → K ≤ M →
        Subgroup.normalizer (E : Set X) ≤ Subgroup.normalizer (M : Set X) → M = ⊤ := by
  intro X _ _ ⟨φ⟩ E K M x hE hE27 hxE hx1 hKx ⟨ψ⟩ hKM hNM
  classical
  set ι : X →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp φ.toMonoidHom with hιdef
  have hιinj : Function.Injective ι :=
    (alternatingGroup (Fin 10)).subtype_injective.comp φ.injective
  have : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hXs : IsSimpleGroup X := φ.isSimpleGroup
  have hX : Nat.card X = 1814400 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hK7 : Nat.card K = 2520 := by
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hKp : Group.IsPerfect ↥K := by
    have : Group.IsPerfect (alternatingGroup (Fin 7)) := by
      rw [Group.isPerfect_def]
      exact commutator_alternatingGroup_eq_top
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  have hx3 : x ^ 3 = 1 := hE.2 x hxE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hirr := kf148A10Irred_holds X ⟨φ⟩ E hE hE27
  obtain ⟨n, hnN, hnx⟩ : ∃ n ∈ Subgroup.normalizer (E : Set X),
      n * x * n⁻¹ ∉ Subgroup.zpowers x := by
    by_contra hall
    push Not at hall
    set F := (Subgroup.zpowers x).subgroupOf E with hF
    have hFinv : ∀ θ ∈ Sec4.autIn ⊤ E, F.map θ.toMonoidHom = F := by
      intro θ hθ
      obtain ⟨g, hgN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hθ
      have hle : F.map (E.normalizerMonoidHom ⟨g, hgN⟩).toMonoidHom ≤ F := by
        rintro _ ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [Subgroup.mem_subgroupOf]
        change g * (y : X) * g⁻¹ ∈ Subgroup.zpowers x
        rw [← hk]
        have : g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := by
          rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
        rw [this]
        exact Subgroup.zpow_mem _ (hall g hgN) k
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    rcases hirr F hFinv with hb | ht
    · apply hx1
      have : (⟨x, hxE⟩ : ↥E) ∈ F := by
        rw [hF, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_zpowers x
      rw [hb, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · have hEx : E ≤ Subgroup.zpowers x := by
        intro y hy
        have : (⟨y, hy⟩ : ↥E) ∈ F := ht ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      have h1 := Subgroup.card_le_of_le hEx
      rw [hE27, Nat.card_zpowers, orderOf_eq_prime hx3 hx1] at h1
      omega
  set σ := ι x with hσ
  set x' := n * x * n⁻¹ with hx'
  set σ' := ι x' with hσ'
  have hx'E : x' ∈ E := (Subgroup.mem_normalizer_iff.mp hnN x).mp hxE
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hx3, map_one]
  have hσ1 : σ ≠ 1 := fun h => hx1 (hιinj (h.trans (map_one ι).symm))
  have hKC : K.map ι ≤ Subgroup.centralizer {σ} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hσ, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hKx hk)]
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer {σ}) := by
    have h1 := Subgroup.card_dvd_of_le hKC
    rw [Subgroup.card_map_of_injective hιinj, hK7] at h1
    exact (show 7 ∣ 2520 by norm_num).trans h1
  have hσc : σ.IsThreeCycle := isThreeCycle_of_seven_dvd hσ3 hσ1 h7
  have hσ'c : σ'.IsThreeCycle := by
    have : σ' = ι n * σ * (ι n)⁻¹ := by rw [hσ', hx', map_mul, map_mul, map_inv]
    rw [this, Equiv.Perm.IsThreeCycle, Equiv.Perm.cycleType_conj]
    exact hσc
  have hcomm : Commute σ σ' := by
    show σ * σ' = σ' * σ
    rw [hσ, hσ', ← map_mul, ← map_mul, hEc x hxE x' hx'E]
  have hnot : σ' ∉ Subgroup.zpowers σ := by
    rintro ⟨m, hm⟩
    apply hnx
    have : ι (x ^ m) = ι x' := by rw [map_zpow]; exact hm
    rw [← hιinj this]
    exact Subgroup.zpow_mem_zpowers x m
  have hdisj := disjoint_support_of_commute hσc.isCycle hσ'c.isCycle hcomm hnot
  set Kn := K.map (MulAut.conj n).toMonoidHom with hKn
  have hKnp : Group.IsPerfect ↥Kn := Group.IsPerfect.map _
  have hKnC : Kn.map ι ≤ Subgroup.centralizer {σ'} := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hσ', ← map_mul, ← map_mul]
    congr 1
    change n * k * n⁻¹ * (n * x * n⁻¹) = n * x * n⁻¹ * (n * k * n⁻¹)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKx hk)
    calc n * k * n⁻¹ * (n * x * n⁻¹) = n * (k * x) * n⁻¹ := by group
      _ = n * (x * k) * n⁻¹ := by rw [this]
      _ = n * x * n⁻¹ * (n * k * n⁻¹) := by group
  have hKmp : Group.IsPerfect ↥(K.map ι) := Group.IsPerfect.map _
  have hKnmp : Group.IsPerfect ↥(Kn.map ι) := Group.IsPerfect.map _
  have hfix : ∀ k ∈ K ⊓ Kn, ∀ i ∈ σ.support ∪ σ'.support, ι k i = i := by
    intro k hk i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact apply_eq_of_isPerfect (by rw [hσc.card_support]; norm_num) hKC hKmp
        ⟨k, hk.1, rfl⟩ hi
    · exact apply_eq_of_isPerfect (by rw [hσ'c.card_support]; norm_num) hKnC hKnmp
        ⟨k, hk.2, rfl⟩ hi
  have hS6 : (σ.support ∪ σ'.support).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hσc.card_support, hσ'c.card_support]
  have hint : Nat.card ↥(K ⊓ Kn) ≤ 24 := by
    have h1 := card_le_of_forall_apply_eq (σ.support ∪ σ'.support) ((K ⊓ Kn).map ι)
      (by rintro _ ⟨k, hk, rfl⟩ i hi; exact hfix k hk i hi)
    rw [Subgroup.card_map_of_injective hιinj, hS6, Fintype.card_fin] at h1
    simpa [Nat.factorial] using h1
  have hKnM : Kn ≤ M := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNM hnN) k).mp (hKM hk)
  set Lg := K ⊔ Kn with hLg
  have hLM : Lg ≤ M := sup_le hKM hKnM
  have hKn7 : Nat.card Kn = 2520 := by
    rw [hKn, Subgroup.card_map_of_injective (MulAut.conj n).injective, hK7]
  have hr1 := Subgroup.relIndex_mul_card Kn K
  have hr2 := Subgroup.relIndex_mul_card Kn Lg
  have hKnL : Kn ⊓ Lg = Kn := inf_of_le_left le_sup_right
  rw [hKnL, hKn7] at hr2
  have hle : Kn.relIndex K ≤ Kn.relIndex Lg := by
    refine Subgroup.relIndex_le_of_le_right le_sup_left ?_
    intro h0
    rw [h0, zero_mul] at hr2
    exact (Nat.card_pos (α := Lg)).ne' hr2.symm
  have hcomm' : Kn ⊓ K = K ⊓ Kn := inf_comm _ _
  rw [hcomm', hK7] at hr1
  have hrel : 105 ≤ Kn.relIndex K := by
    by_contra hlt
    push Not at hlt
    have : Kn.relIndex K * Nat.card ↥(K ⊓ Kn) ≤ 104 * 24 :=
      Nat.mul_le_mul (by omega) hint
    omega
  have hLcard : 264600 ≤ Nat.card Lg := by
    rw [← hr2]
    nlinarith
  have hMcard : 264600 ≤ Nat.card M := hLcard.trans (Subgroup.card_le_of_le hLM)
  have hidx : M.index ≤ 6 := by
    have h1 := Subgroup.index_mul_card M
    rw [hX] at h1
    nlinarith
  have : M.FiniteIndex := Subgroup.finiteIndex_of_finite
  have hcore := Subgroup.index_normalCore_dvd_factorial_index (H := M)
  have h6 : M.index.factorial ∣ 720 :=
    (Nat.factorial_dvd_factorial hidx).trans (by norm_num [Nat.factorial])
  have hNn : M.normalCore.Normal := Subgroup.normalCore_normal M
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with hb | ht
  · exfalso
    rw [hb, Subgroup.index_bot, hX] at hcore
    have := Nat.le_of_dvd (by norm_num) (hcore.trans h6)
    omega
  · exact top_le_iff.mp (ht ▸ Subgroup.normalCore_le M)

end Item148Res4

end CFSG.RankThree.PartTwo.Sec14
