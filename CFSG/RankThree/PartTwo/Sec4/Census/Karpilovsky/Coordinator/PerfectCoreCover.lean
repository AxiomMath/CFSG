module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover

open Subgroup
open scoped commutatorElement

set_option synthInstance.maxSize 2000 in
theorem mem_of_mul_closed_of_transitive_of_involution : ∀ s : Finset (Equiv.Perm (Fin 3)),
    (∀ x ∈ s, ∀ y ∈ s, x * y ∈ s) → (∀ a b : Fin 3, ∃ g ∈ s, g a = b) →
    (∃ g ∈ s, g ≠ 1 ∧ g * g = 1) → ∀ g, g ∈ s := by decide

theorem exists_surjective_perm_three {Q : Type*} [Group Q] [Finite Q]
    (hgen : Subgroup.closure {x : Q | x * x = 1} = ⊤) (h3 : 3 ∣ Nat.card Q)
    (h12 : Nat.card Q ∣ 12) : ∃ φ : Q →* Equiv.Perm (Fin 3), Function.Surjective φ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hidx : (P : Subgroup Q).index = 3 := by
    have h1 := (P : Subgroup Q).card_mul_index
    have h2 : ¬ 2 ∣ (P : Subgroup Q).index := P.not_dvd_index
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    rw [hk] at h1
    have h4 : 3 ∣ (P : Subgroup Q).index := by
      have : 3 ∣ 2 ^ k * (P : Subgroup Q).index := h1 ▸ h3
      exact (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left this
    have h5 : (P : Subgroup Q).index ∣ 12 := (Subgroup.index_dvd_card _).trans h12
    have h6 : (P : Subgroup Q).index ≤ 12 := Nat.le_of_dvd (by norm_num) h5
    generalize (P : Subgroup Q).index = n at h2 h4 h5 h6 ⊢
    interval_cases n <;> omega
  let e : (Q ⧸ (P : Subgroup Q)) ≃ Fin 3 := (Finite.equivFin _).trans (finCongr hidx)
  let φ : Q →* Equiv.Perm (Fin 3) :=
    (e.permCongrHom : Equiv.Perm (Q ⧸ (P : Subgroup Q)) →* Equiv.Perm (Fin 3)).comp
      (MulAction.toPermHom Q (Q ⧸ (P : Subgroup Q)))
  have hφ : ∀ q x, φ q x = e (q • e.symm x) := by
    intro q x
    simp [φ, Equiv.permCongr_apply]
  refine ⟨φ, fun g => ?_⟩
  have hs := mem_of_mul_closed_of_transitive_of_involution (Finset.univ.filter fun g => g ∈ φ.range)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  have htrans : ∀ a b : Fin 3, ∃ g ∈ φ.range, g a = b := by
    intro a b
    obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q (e.symm a) (e.symm b)
    exact ⟨φ q, ⟨q, rfl⟩, by rw [hφ, hq, Equiv.apply_symm_apply]⟩
  have hinv : ∃ g ∈ φ.range, g ≠ 1 ∧ g * g = 1 := by
    by_contra hcon
    push Not at hcon
    have hsq : ∀ t : Q, t * t = 1 → φ t = 1 := by
      intro t ht
      by_contra h1
      exact hcon (φ t) ⟨t, rfl⟩ h1 (by rw [← map_mul, ht, map_one])
    have hker : φ.ker = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      intro t ht
      exact hsq t ht
    obtain ⟨g', ⟨q, rfl⟩, hg'⟩ := htrans 0 1
    have h1 : φ q = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top q)
    rw [h1] at hg'
    exact absurd hg' (by decide)
  exact hs (fun x hx y hy => φ.range.mul_mem hx hy) htrans hinv g

theorem exists_perfect_normal_map_eq_top {F X : Type*} [Group F] [Finite F] [Group X]
    [Group.IsPerfect X] (θ : F →* X) (hθ : Function.Surjective θ) :
    ∃ E : Subgroup F, E.Normal ∧ Group.IsPerfect E ∧ E.map θ = ⊤ := by
  classical
  obtain ⟨m, n, hmn, hEq⟩ : ∃ m n : ℕ, m < n ∧ derivedSeries F m = derivedSeries F n := by
    obtain ⟨m, n, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => derivedSeries F k)
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact ⟨m, n, h', h⟩
    · exact ⟨n, m, h', h.symm⟩
  refine ⟨derivedSeries F m, derivedSeries_normal F m, ?_, ?_⟩
  · rw [Subgroup.isPerfect_iff, ← derivedSeries_succ]
    exact le_antisymm (derivedSeries_antitone F m.le_succ)
      (hEq.le.trans (derivedSeries_antitone F hmn))
  · rw [map_derivedSeries_eq hθ m]
    exact Group.IsPerfect.derivedSeries_eq_top X m

theorem mem_of_pow_eq_one_of_coprime_index {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    {n : ℕ} (hn : n.Coprime H.index) {y : G} (hy : y ^ n = 1) : y ∈ H := by
  have h1 : (y : G ⧸ H) ^ n = 1 := by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one]
  have h2 : (y : G ⧸ H) ^ H.index = 1 := pow_card_eq_one'
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [hn.gcd_eq_one, pow_one] at h3
  exact (QuotientGroup.eq_one_iff y).1 h3

theorem mem_of_pow_three_eq_one {F : Type*} [Group F] [Finite F]
    (hgen : Subgroup.closure {x : F | x * x = 1} = ⊤)
    (hS3 : ∀ φ : F →* Equiv.Perm (Fin 3), ¬ Function.Surjective φ)
    (E : Subgroup F) [E.Normal] (hE : E.index ∣ 12) {z : F} (hz : z ^ 3 = 1) : z ∈ E := by
  by_cases h3 : 3 ∣ E.index
  · exfalso
    have hgenQ : Subgroup.closure {x : F ⧸ E | x * x = 1} = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hy : y ∈ Subgroup.closure {x : F | x * x = 1} := hgen ▸ Subgroup.mem_top y
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' E) hy
      rw [MonoidHom.map_closure] at this
      refine Subgroup.closure_mono ?_ this
      rintro _ ⟨t, ht, rfl⟩
      simp only [Set.mem_ofPred_eq] at ht ⊢
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ht, QuotientGroup.mk_one]
    obtain ⟨ψ, hψ⟩ := exists_surjective_perm_three hgenQ h3 hE
    exact hS3 (ψ.comp (QuotientGroup.mk' E)) (hψ.comp (QuotientGroup.mk'_surjective E))
  · exact mem_of_pow_eq_one_of_coprime_index E
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3) hz

theorem commute_of_normal_zpowers_of_isPerfect {P : Type*} [Group P] [Group.IsPerfect P]
    {u : P} (hn : (zpowers u).Normal) (k : P) : Commute k u := by
  let ρ : P →* (ZMod (Nat.card (zpowers u)))ˣ :=
    (IsCyclic.mulAutMulEquiv (zpowers u)).toMonoidHom.comp
      (MulAut.conjNormal (H := zpowers u))
  have hker : ρ.ker = ⊤ := by
    have h := Abelianization.commutator_subset_ker ρ
    rwa [Group.IsPerfect.commutator_eq_top, top_le_iff] at h
  have h1 : ρ k = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top _)
  have h2 : (MulAut.conjNormal (H := zpowers u) k) = 1 :=
    (IsCyclic.mulAutMulEquiv (zpowers u)).injective (by simpa [ρ] using h1)
  have h3 := MulAut.conjNormal_apply (H := zpowers u) k ⟨u, Subgroup.mem_zpowers u⟩
  rw [h2] at h3
  have h4 : u = k * u * k⁻¹ := h3
  calc k * u = (k * u * k⁻¹) * k := by group
    _ = u * k := by rw [← h4]

theorem commute_of_mem_of_normal_zpowers_of_isPerfect {F : Type*} [Group F] (E : Subgroup F)
    [Group.IsPerfect E] {z : F} (hz : z ∈ E) (hn : (zpowers z).Normal) {e : F} (he : e ∈ E) :
    Commute e z := by
  have hsub : (zpowers z).subgroupOf E = zpowers (⟨z, hz⟩ : E) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext (by simpa using hk)⟩,
      fun ⟨k, hk⟩ => ⟨k, by simpa using congrArg Subtype.val hk⟩⟩
  have hn' : (zpowers (⟨z, hz⟩ : E)).Normal := hsub ▸ hn.subgroupOf E
  exact congrArg Subtype.val (commute_of_normal_zpowers_of_isPerfect hn' ⟨e, he⟩)

theorem commutatorElement_mul_comm_of_card_dvd_twelve {A : Type*} [Group A] [Finite A]
    (h12 : Nat.card A ∣ 12) (h3 : 3 ∣ Nat.card (center A)) (a b x : A) :
    ⁅a, b⁆ * x = x * ⁅a, b⁆ := by
  obtain ⟨m, hm⟩ := h3
  have hq4 : Nat.card (A ⧸ center A) ∣ 4 := by
    rw [(center A).card_eq_card_quotient_mul_card_subgroup, hm] at h12
    have : 3 * (Nat.card (A ⧸ center A) * m) ∣ 3 * 4 := by
      convert h12 using 1
      ring
    exact (Dvd.intro _ rfl).trans (Nat.dvd_of_mul_dvd_mul_left (by norm_num) this)
  have hqpos : 0 < Nat.card (A ⧸ center A) := Nat.card_pos
  have hcomm : ∀ u v : A ⧸ center A, u * v = v * u := by
    have hle : Nat.card (A ⧸ center A) ≤ 4 := Nat.le_of_dvd (by norm_num) hq4
    generalize hq : Nat.card (A ⧸ center A) = q at hq4 hqpos hle
    interval_cases q
    · intro u v
      have := (Nat.card_eq_one_iff_unique.1 hq).1
      exact Subsingleton.elim _ _
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := isCyclic_of_prime_card hq
      intro u v
      exact IsCyclic.isMulCommutative.is_comm.comm u v
    · omega
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
        (by rw [hq]; norm_num)).is_comm.comm
  have hc : ⁅a, b⁆ ∈ center A := by
    rw [← QuotientGroup.eq_one_iff]
    have := map_commutatorElement (QuotientGroup.mk' (center A)) a b
    simp only [QuotientGroup.mk'_apply] at this
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  exact (Subgroup.mem_center_iff.1 hc x).symm

theorem ker_le_center_of_commutator_central {E X : Type*} [Group E] [Finite E] [Group X]
    [IsSimpleGroup X] [Group.IsPerfect E] (π : E →* X) (hπ : Function.Surjective π)
    (hbig : (Nat.card π.ker).factorial < Nat.card X)
    (hab : ∀ a b x : π.ker, ⁅a, b⁆ * x = x * ⁅a, b⁆) : π.ker ≤ center E := by
  classical
  set ρ : E →* MulAut π.ker := MulAut.conjNormal with hρ
  have : (ρ.ker.map π).Normal := (ρ.normal_ker).map π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π) with h | h
  · exfalso
    have hle : ρ.ker ≤ π.ker := by
      intro c hc
      have : π c ∈ ρ.ker.map π := Subgroup.mem_map_of_mem π hc
      rwa [h, Subgroup.mem_bot] at this
    have h1 : π.ker.index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hle
    have h2 : π.ker.index = Nat.card X := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top]
    have h3 : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
    have h4 : Nat.card ρ.range ≤ (Nat.card π.ker).factorial := by
      calc Nat.card ρ.range ≤ Nat.card (MulAut π.ker) := Nat.card_le_card_of_injective
              (fun x => (x : MulAut π.ker)) Subtype.val_injective
        _ ≤ Nat.card (Equiv.Perm π.ker) :=
            Nat.card_le_card_of_injective (fun g : MulAut π.ker => g.toEquiv)
              MulEquiv.toEquiv_injective
        _ = (Nat.card π.ker).factorial := Nat.card_perm
    have h5 : Nat.card X ≤ ρ.ker.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (h2 ▸ h1)
    omega
  · have hcomm : ∀ e e' : E, ⁅e, e'⁆ ∈ ρ.ker := by
      have hsplit : ∀ e : E, ∃ c ∈ ρ.ker, ∃ a : π.ker, e = c * a := by
        intro e
        have : π e ∈ ρ.ker.map π := h ▸ Subgroup.mem_top _
        obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 this
        refine ⟨c, hc, ⟨c⁻¹ * e, ?_⟩, by simp⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
      intro e e'
      obtain ⟨c, hc, a, rfl⟩ := hsplit e
      obtain ⟨c', hc', a', rfl⟩ := hsplit e'
      rw [MonoidHom.mem_ker, map_commutatorElement, map_mul, map_mul, MonoidHom.mem_ker.1 hc,
        MonoidHom.mem_ker.1 hc', one_mul, one_mul]
      have hin : ∀ a : π.ker, ρ (a : E) = MulAut.conj a := by
        intro a
        ext x
        simp [hρ, MulAut.conjNormal_apply]
      rw [hin, hin, ← map_commutatorElement]
      ext x
      have := hab a a' x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [this, mul_inv_cancel_right]
    have htop : (⊤ : Subgroup E) ≤ ρ.ker := by
      rw [← Group.IsPerfect.commutator_eq_top (G := E), commutator_def]
      exact Subgroup.commutator_le.2 fun e _ e' _ => hcomm e e'
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : ρ g = 1 := MonoidHom.mem_ker.1 (htop (Subgroup.mem_top g))
    have h2 := congrArg (fun φ : MulAut π.ker => (φ ⟨a, ha⟩ : E)) h1
    simp only [hρ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h2]

theorem mem_zpowers_pow_of_pow_three_eq_one {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K ∣ 12) {g : K} (h6 : 6 ∣ orderOf g) {y : K} (hy : y ^ 3 = 1) :
    y ∈ zpowers (g ^ (orderOf g / 3)) := by
  have hdvd : orderOf g ∣ 12 := (orderOf_dvd_natCard g).trans hK
  have hopos : 0 < orderOf g := orderOf_pos g
  have hmem : y ∈ zpowers g := by
    have hidx := (zpowers g).card_mul_index
    rw [Nat.card_zpowers] at hidx
    have hle : orderOf g ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    have hKle : Nat.card K ≤ 12 := Nat.le_of_dvd (by norm_num) hK
    have hipos : 0 < (zpowers g).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hcases : (zpowers g).index = 1 ∨ (zpowers g).index = 2 := by
      have : orderOf g * (zpowers g).index ≤ 12 := hidx ▸ hKle
      have h6' : 6 ≤ orderOf g := Nat.le_of_dvd hopos h6
      have : (zpowers g).index ≤ 2 := by nlinarith
      omega
    rcases hcases with h | h
    · rw [Subgroup.index_eq_one.1 h]
      exact Subgroup.mem_top y
    · have := Subgroup.normal_of_index_eq_two h
      exact mem_of_pow_eq_one_of_coprime_index _ (by rw [h]; norm_num) hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  obtain ⟨t, ht⟩ : ∃ t, orderOf g = 3 * t := by
    obtain ⟨c, hc⟩ := h6
    exact ⟨2 * c, by omega⟩
  have hdiv : ((orderOf g : ℕ) : ℤ) ∣ k * 3 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul]
    simpa using hy
  rw [ht] at hdiv
  have hkt : (t : ℤ) ∣ k := by
    have : (3 : ℤ) * t ∣ 3 * k := by
      convert hdiv using 1 <;> push_cast <;> ring
    exact Int.dvd_of_mul_dvd_mul_left (by norm_num) this
  obtain ⟨m, hm⟩ := hkt
  have : orderOf g / 3 = t := by omega
  rw [this, hm, zpow_mul, zpow_natCast]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m

theorem normal_zpowers_pow_div_three {F X : Type*} [Group F] [Finite F] [Group X] (θ : F →* X)
    (hK : Nat.card θ.ker ∣ 12) {g : F} (hg : g ∈ θ.ker) (hg6 : 6 ∣ orderOf g) :
    (zpowers (g ^ (orderOf g / 3))).Normal := by
  let gK : θ.ker := ⟨g, hg⟩
  have hgK : orderOf gK = orderOf g := Subgroup.orderOf_mk g hg
  set z : F := g ^ (orderOf g / 3) with hzdef
  have hz3ord : orderOf z = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' (dvd_trans (by norm_num) hg6)
  have hz3 : z ^ 3 = 1 := by simpa [hz3ord] using pow_orderOf_eq_one z
  have hzK : z ∈ θ.ker := θ.ker.pow_mem hg _
  refine ⟨fun n hn f => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hy : f * z * f⁻¹ ∈ zpowers z := by
    have hyK : f * z * f⁻¹ ∈ θ.ker := (MonoidHom.normal_ker θ).conj_mem z hzK f
    have hy3 : (⟨f * z * f⁻¹, hyK⟩ : θ.ker) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [conj_pow, hz3]
      simp
    have := mem_zpowers_pow_of_pow_three_eq_one hK (g := gK) (by rwa [hgK]) hy3
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    simpa [gK, hgK, hzdef] using congrArg Subtype.val hk
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hy k

theorem card_ker_eq_card_ker_comp_subtype_mul_index {F X : Type*} [Group F] [Finite F] [Group X]
    (θ : F →* X) (E : Subgroup F) (hE : Function.Surjective (θ.comp E.subtype)) :
    Nat.card θ.ker = Nat.card (θ.comp E.subtype).ker * E.index := by
  have hθ : Function.Surjective θ := Function.Surjective.of_comp hE
  have : Finite X := Finite.of_surjective θ hθ
  have h1 := Subgroup.card_ker_mul_card_of_surjective hθ
  have h2 := Subgroup.card_ker_mul_card_of_surjective hE
  have h3 := E.card_mul_index
  have : Nat.card θ.ker * Nat.card X =
      (Nat.card (θ.comp E.subtype).ker * E.index) * Nat.card X := by
    rw [h1, ← h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this

theorem three_dvd_card_center_ker {E X : Type*} [Group E] [Finite E] [Group X] (π : E →* X)
    {z : E} (hz : π z = 1) (hord : orderOf z = 3) (hcomm : ∀ e : E, e * z = z * e) :
    3 ∣ Nat.card (center π.ker) := by
  have hzA : z ∈ π.ker := hz
  have hcentral : (⟨z, hzA⟩ : π.ker) ∈ center π.ker :=
    Subgroup.mem_center_iff.2 fun a => Subtype.ext (hcomm a.1)
  have := orderOf_dvd_natCard (⟨_, hcentral⟩ : center π.ker)
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord] at this

theorem exists_perfect_central_cover_three_dvd {F X : Type} [Group F] [Finite F] [Group X]
    [IsSimpleGroup X] [Group.IsPerfect X] (θ : F →* X) (hθ : Function.Surjective θ)
    (hgen : Subgroup.closure {x : F | x * x = 1} = ⊤)
    (hS3 : ∀ φ : F →* Equiv.Perm (Fin 3), ¬ Function.Surjective φ)
    (hK : Nat.card θ.ker ∣ 12) (hbig : (12 : ℕ).factorial < Nat.card X)
    {g : F} (hg : g ∈ θ.ker) (hg6 : 6 ∣ orderOf g) :
    ∃ (E : Type) (_ : Group E) (_ : Finite E) (_ : Group.IsPerfect E) (π : E →* X),
      Function.Surjective π ∧ π.ker ≤ center E ∧ 3 ∣ Nat.card π.ker := by
  classical
  have hZn := normal_zpowers_pow_div_three θ hK hg hg6
  set z : F := g ^ (orderOf g / 3) with hzdef
  have hz3ord : orderOf z = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' (dvd_trans (by norm_num) hg6)
  have hz3 : z ^ 3 = 1 := by simpa [hz3ord] using pow_orderOf_eq_one z
  have hzK : z ∈ θ.ker := θ.ker.pow_mem hg _
  obtain ⟨E, hEn, hEp, hEmap⟩ := exists_perfect_normal_map_eq_top θ hθ
  let π : E →* X := θ.comp E.subtype
  have hπ : Function.Surjective π := fun x => by
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 (hEmap ▸ Subgroup.mem_top x : x ∈ E.map θ)
    exact ⟨⟨e, he⟩, rfl⟩
  have hcardK := card_ker_eq_card_ker_comp_subtype_mul_index θ E hπ
  have hindex : E.index ∣ 12 := (Dvd.intro_left _ hcardK.symm).trans hK
  have hA12 : Nat.card π.ker ∣ 12 := (Dvd.intro _ hcardK.symm).trans hK
  have hzE : z ∈ E := mem_of_pow_three_eq_one hgen hS3 E hindex hz3
  have hzcomm : ∀ e ∈ E, e * z = z * e :=
    fun e he => (commute_of_mem_of_normal_zpowers_of_isPerfect E hzE hZn he).eq
  have h3C : 3 ∣ Nat.card (center π.ker) :=
    three_dvd_card_center_ker π (z := ⟨z, hzE⟩) hzK ((Subgroup.orderOf_mk z hzE).trans hz3ord)
      fun e => Subtype.ext (hzcomm e.1 e.2)
  have hbig' : (Nat.card π.ker).factorial < Nat.card X :=
    lt_of_le_of_lt (Nat.factorial_le (Nat.le_of_dvd (by norm_num) hA12)) hbig
  exact ⟨E, inferInstance, inferInstance, hEp, π, hπ,
    ker_le_center_of_commutator_central π hπ hbig'
      (commutatorElement_mul_comm_of_card_dvd_twelve hA12 h3C),
    h3C.trans (Subgroup.card_subgroup_dvd_card _)⟩

theorem exists_involution_lift {E X : Type*} [Group E] [Group X] (π : E →* X)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) {x : X} (hx : x * x = 1) :
    ∃ t : E, π t = x ∧ t * t = 1 := by
  obtain ⟨s, rfl⟩ := hπ x
  set n := Nat.card π.ker with hn
  have hss : s * s ∈ π.ker := by rwa [MonoidHom.mem_ker, map_mul]
  have h1 : (⟨s * s, hss⟩ : π.ker) ^ n = 1 := pow_card_eq_one'
  have h2 : (s * s) ^ n = 1 := by simpa using congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := hodd
  refine ⟨s ^ n, ?_, ?_⟩
  · have hx2 : π s ^ 2 = 1 := by rwa [sq]
    rw [map_pow, hk, pow_succ, pow_mul, hx2, one_pow, one_mul]
  · rw [← pow_add, ← two_mul, pow_mul, sq, h2]

theorem eq_of_involution_lift {E X : Type*} [Group E] [Group X] (π : E →* X)
    (hc : π.ker ≤ center E) (hodd : Odd (Nat.card π.ker)) {t t' : E} (ht : t * t = 1)
    (ht' : t' * t' = 1) (h : π t = π t') : t = t' := by
  have ha : t⁻¹ * t' ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hsq : (t⁻¹ * t') * (t⁻¹ * t') = 1 := by
    have h2 : t' * t' = t * t * ((t⁻¹ * t') * (t⁻¹ * t')) :=
      calc t' * t' = t * (t⁻¹ * t') * (t * (t⁻¹ * t')) := by group
        _ = t * ((t⁻¹ * t') * t) * (t⁻¹ * t') := by group
        _ = t * (t * (t⁻¹ * t')) * (t⁻¹ * t') := by
          rw [Subgroup.mem_center_iff.1 (hc ha) t]
        _ = t * t * ((t⁻¹ * t') * (t⁻¹ * t')) := by group
    rw [ht', ht, one_mul] at h2
    exact h2.symm
  set a : π.ker := ⟨t⁻¹ * t', ha⟩
  have h2 : orderOf a ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [sq] using hsq))
  have h4 : orderOf a ∣ Nat.gcd 2 (Nat.card π.ker) := Nat.dvd_gcd h2 (orderOf_dvd_natCard a)
  rw [Nat.coprime_two_left.2 hodd] at h4
  exact inv_mul_eq_one.1 (congrArg Subtype.val (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)))

theorem commutatorElement_mul_mul_of_mem_center {Y : Type*} [Group Y] {a b z w : Y}
    (hz : z ∈ center Y) (hw : w ∈ center Y) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
  have h2 : z * (b * w) * z⁻¹ = b * w := by rw [← hz' (b * w)]; group
  rw [h1, h2]
  have h3 : a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
  have h4 : w * a⁻¹ * w⁻¹ = a⁻¹ := by rw [← hw' a⁻¹]; group
  rw [h3, h4]

theorem surjective_of_perfect_of_central_ker {F E X : Type*} [Group F] [Group E] [Group X]
    [Group.IsPerfect E] (π : E →* X) (hc : π.ker ≤ center E) (ψ : F →* E)
    (h : Function.Surjective (π.comp ψ)) : Function.Surjective ψ := by
  have hsplit : ∀ e : E, ∃ f : F, ∃ a ∈ center E, e = ψ f * a := by
    intro e
    obtain ⟨f, hf⟩ := h (π e)
    refine ⟨f, (ψ f)⁻¹ * e, hc ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    simp only [MonoidHom.comp_apply] at hf
    rw [hf, inv_mul_cancel]
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := E),
    commutator_def]
  refine Subgroup.commutator_le.2 fun e _ e' _ => ?_
  obtain ⟨f, a, ha, rfl⟩ := hsplit e
  obtain ⟨f', a', ha', rfl⟩ := hsplit e'
  rw [commutatorElement_mul_mul_of_mem_center ha ha', ← map_commutatorElement]
  exact ⟨_, rfl⟩

theorem card_ker_dvd_card_ker_comp {F E X : Type*} [Group F] [Finite F] [Group E] [Group X]
    (ψ : F →* E) (π : E →* X) (hψ : Function.Surjective ψ) (hπ : Function.Surjective π) :
    Nat.card π.ker ∣ Nat.card (π.comp ψ).ker := by
  have : Finite E := Finite.of_surjective ψ hψ
  have : Finite X := Finite.of_surjective π hπ
  have hπψ : Function.Surjective (π.comp ψ) := hπ.comp hψ
  have h1 := Subgroup.card_ker_mul_card_of_surjective hπψ
  have h2 := Subgroup.card_ker_mul_card_of_surjective hψ
  have h3 := Subgroup.card_ker_mul_card_of_surjective hπ
  have hXpos : 0 < Nat.card X := Nat.card_pos
  refine ⟨Nat.card ψ.ker, ?_⟩
  have : Nat.card (π.comp ψ).ker * Nat.card X =
      (Nat.card π.ker * Nat.card ψ.ker) * Nat.card X := by
    rw [h1, ← h2, ← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hXpos this

theorem card_dvd_three_of_isPGroup_of_card_dvd_twelve {A : Type*} [Group A] [Finite A]
    (hA : IsPGroup 3 A) (h12 : Nat.card A ∣ 12) : Nat.card A ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn] at h12 ⊢
  rcases n with _ | _ | n
  · simp
  · simp
  · exfalso
    have : 9 ∣ 3 ^ (n + 2) := by
      rw [pow_add]; exact Dvd.intro_left _ rfl
    have := this.trans h12
    omega

theorem isPerfect_of_isSimpleGroup_of_not_prime {G : Type*} [Group G] [IsSimpleGroup G]
    (hp : ¬ (Nat.card G).Prime) : Group.IsPerfect G := by
  refine Group.isPerfect_def.2 ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h1 | h1
  · exfalso
    have : IsMulCommutative G := ⟨⟨fun a b => by
      have hmem : ⁅a, b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rwa [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem⟩⟩
    exact hp ((Group.is_simple_iff_prime_card (α := G)).1 inferInstance)
  · exact h1

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover
