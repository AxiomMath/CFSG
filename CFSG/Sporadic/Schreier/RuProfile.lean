module

public import CFSG.Sporadic.Schreier.RuCheckProfile
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.Sporadic.SchreierLemmas.FrattiniCoset

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem orderOf_quot_eq_eight {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (y : G) :
    orderOf (y : G ⧸ N) = 8 ↔ y ^ 8 ∈ N ∧ y ^ 4 ∉ N := by
  have e : ∀ k, (y : G ⧸ N) ^ k = 1 ↔ y ^ k ∈ N := fun k => by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    refine ⟨(e 8).1 (h ▸ pow_orderOf_eq_one _), fun h4 => ?_⟩
    have := orderOf_dvd_of_pow_eq_one ((e 4).2 h4)
    rw [h] at this
    norm_num at this
  · rintro ⟨h8, h4⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := (y : G ⧸ N))
      (fun h => h4 ((e 4).1 (by simpa using h))) (by simpa using (e 8).2 h8)
    simpa using this

theorem exists_of_all2_false {n : ℕ} {L : Array Level} {p : Array ℕ → Bool}
    (h : all2 n L p = false) :
    ∃ a < L[0]!.pts.size, ∃ b < L[1]!.pts.size, p (prod2A n L a b) = false := by
  have h' : ¬ (all2 n L p = true) := by
    rw [h]
    exact Bool.false_ne_true
  rw [all2, allLt_iff] at h'
  simp only [not_forall] at h'
  obtain ⟨a, ha, h2⟩ := h'
  rw [allLt_iff] at h2
  simp only [not_forall] at h2
  obtain ⟨b, hb, h3⟩ := h2
  exact ⟨a, ha, b, hb, Bool.eq_false_iff.2 h3⟩

@[expose] def ruResFS :
    ruS →* Equiv.Perm (Fin 1920) := ruResF.comp (Subgroup.inclusion ruS_leC)

theorem ruResFS_injective :
    Function.Injective ruResFS :=
  ruResF_injective.comp (Subgroup.inclusion_injective ruS_leC)

theorem ruResFS_apply
    (y : ruS) : ruResFS y = ruResFPerm y := by
  rw [ruResFPerm_of_mem (ruS_leC y.2)]
  rfl

theorem rep_ruSF'
    {j : ℕ} (hj : j < 4) : Rep 1920 (ruSF j) (ruResFS (ruSGenS j)) := by
  rw [ruResFS_apply]
  exact rep_ruSF hj

@[expose] def ruTvS (v : ℕ) : ruS :=
  ruSGenS 0 ^ (v % 2) * ruSGenS 2 ^ (v / 2 % 2) * ruSGenS 3 ^ (v / 4 % 2)

theorem rep_ruTv
    (v : ℕ) : Rep 1920 (ruTv v) (ruResFS (ruTvS v)) := by
  rw [ruTvS, map_mul, map_mul, map_pow, map_pow, map_pow]
  exact rep_compA (rep_compA (rep_powA (rep_ruSF' (by norm_num)) _)
    (rep_powA (rep_ruSF' (by norm_num)) _)) (rep_powA (rep_ruSF' (by norm_num)) _)

theorem ruResFS_mem_chainR
    {r : ruS} (hr : r ∈ ruRS) :
    ruResFS r ∈ ruChainR.originalSubgroup := by
  rw [ruChainR_sub, ruResFS_apply, ruResFPerm_of_mem (ruS_leC r.2)]
  exact ⟨⟨r, ruS_leC r.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hr), rfl⟩

theorem exists_of_mem_chainR
    {g : Equiv.Perm (Fin 1920)} (hg : g ∈ ruChainR.originalSubgroup) :
    ∃ r : ruS, r ∈ ruRS ∧ ruResFS r = g := by
  rw [ruChainR_sub] at hg
  obtain ⟨⟨x, hxC⟩, hx, rfl⟩ := hg
  have hxR : x ∈ ruR := Subgroup.mem_subgroupOf.1 hx
  refine ⟨⟨x, ruR_leS hxR⟩, Subgroup.mem_subgroupOf.2 hxR, ?_⟩
  rfl

abbrev ruZS : Subgroup ruS := Subgroup.center ruS

theorem mem_zpowers_ruZ
    {x : Equiv.Perm (Fin 4060)} :
    x ∈ Subgroup.zpowers ruZ ↔ x = 1 ∨ x = ruZ := by
  constructor
  · rintro ⟨k, rfl⟩
    show ruZ ^ k = 1 ∨ ruZ ^ k = ruZ
    rw [← zpow_mod_orderOf, orderOf_ruZ]
    have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases this with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_ruZS_iff
    (y : ruS) : y ∈ ruZS ↔ (y : Equiv.Perm (Fin 4060)) = 1 ∨
    (y : Equiv.Perm (Fin 4060)) = ruZ := by
  rw [← mem_zpowers_ruZ, ← center_ruS]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y', hy', he⟩
    rwa [← Subtype.ext he]

theorem rep_ruZF :
    Rep 1920 ruZF (ruResFS ⟨ruZ, ruZ_memS⟩) := by
  rw [ruResFS_apply]
  exact rep_ruResF rep_ruZ ruZ_memC

theorem ruIsZF_iff
    {t : Array ℕ} {y : ruS} (ht : Rep 1920 t (ruResFS y)) :
    ruIsZF t = true ↔ y ∈ ruZS := by
  rw [mem_ruZS_iff, ruIsZF, Bool.or_eq_true]
  have e1 : eqA 1920 t (idA 1920) = true ↔ ruResFS y = ruResFS 1 := by
    rw [map_one]
    exact eqA_iff ht rep_idA
  have e2 : eqA 1920 t ruZF = true ↔ ruResFS y = ruResFS ⟨ruZ, ruZ_memS⟩ := eqA_iff ht rep_ruZF
  rw [e1, e2, ruResFS_injective.eq_iff, ruResFS_injective.eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem ruOrd8F_iff
    {t : Array ℕ} {y : ruS} (ht : Rep 1920 t (ruResFS y)) :
    ruOrd8F t = true ↔ orderOf (y : ruS ⧸ ruZS) = 8 := by
  rw [orderOf_quot_eq_eight]
  have h2 : Rep 1920 (compA 1920 t t) (ruResFS (y ^ 2)) := by
    rw [pow_two, map_mul]
    exact rep_compA ht ht
  have h4 : Rep 1920 (compA 1920 (compA 1920 t t) (compA 1920 t t)) (ruResFS (y ^ 4)) := by
    rw [show y ^ 4 = y ^ 2 * y ^ 2 by rw [← pow_add], map_mul]
    exact rep_compA h2 h2
  have h8 : Rep 1920 (compA 1920 (compA 1920 (compA 1920 t t) (compA 1920 t t))
      (compA 1920 (compA 1920 t t) (compA 1920 t t))) (ruResFS (y ^ 8)) := by
    rw [show y ^ 8 = y ^ 4 * y ^ 4 by rw [← pow_add], map_mul]
    exact rep_compA h4 h4
  simp only [ruOrd8F, Bool.and_eq_true, Bool.not_eq_true']
  rw [ruIsZF_iff h8, ← Bool.not_eq_true, ruIsZF_iff h4]

theorem ruTvS_label
    (v : ℕ) (hv : v < 8) :
    ruLabelEquiv (QuotientGroup.mk (ruTvS v)) = Multiplicative.ofAdd (ruBitVec v) := by
  have e : ∀ j < 4, ruLabelEquiv (QuotientGroup.mk (ruSGenS j)) =
      Multiplicative.ofAdd (ruBitVec (ruQuotientBits.getD j 0)) := fun j hj => ruLabelEquiv_apply hj
  rw [ruTvS, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
    QuotientGroup.mk_pow, QuotientGroup.mk_pow, map_mul, map_mul, map_pow, map_pow, map_pow,
    e 0 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), ← ofAdd_nsmul, ← ofAdd_nsmul,
    ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_add]
  congr 1
  interval_cases v <;> decide

theorem exists_ruTvS
    (c : RuQ) : ∃ v < 8, c = QuotientGroup.mk (ruTvS v) := by
  obtain ⟨w, hw⟩ : ∃ w, ruLabelEquiv c = Multiplicative.ofAdd w := ⟨_, rfl⟩
  have hall : ∀ w : Fin 3 → ZMod 2, ∃ v < 8, ruBitVec v = w := by decide
  obtain ⟨v, hv8, rfl⟩ := hall w
  refine ⟨v, hv8, ruLabelEquiv.injective ?_⟩
  rw [hw, ruTvS_label v hv8]

theorem ruTvS_one_ne
    {v : ℕ} (hv : v < 8) (h : (QuotientGroup.mk (ruTvS v) : RuQ) ≠ 1) :
    v ≠ 0 := by
  rintro rfl
  apply h
  simp [ruTvS]

theorem mem_coset_iff
    (v : ℕ) (y : ruS) :
    (y : RuQ) = QuotientGroup.mk (ruTvS v) ↔ ∃ r ∈ ruRS, y = ruTvS v * r := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    refine ⟨(ruTvS v)⁻¹ * y, ?_, by group⟩
    have := ruRS.inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  · rintro ⟨r, hr, rfl⟩
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact ruRS.inv_mem hr

theorem getD_of_map_range_eight {f : ℕ → Bool} {l : List Bool} (h : (List.range 8).map f = l)
    (v : ℕ) (hv : v < 8) : f v = l.getD v false := by
  subst h
  simp [hv]

theorem ruCoset4_order
    {y : ruS} (hy : (y : RuQ) = QuotientGroup.mk (ruTvS 4)) :
    orderOf (y : ruS ⧸ ruZS) = 8 := by
  obtain ⟨r, hr, rfl⟩ := (mem_coset_iff 4 y).1 hy
  have hall : all2 1920 (rawLevels 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase))
      (fun g => ruOrd8F (compA 1920 (ruTv 4) g)) = true :=
    getD_of_map_range_eight ruProfile_check 4 (by norm_num)
  have h := ruChainR_check.1
  have hb : ruChainR.baseCount = 2 := rfl
  have key := chain_forall_of_all2 (ruChain_arrays h) (by norm_num : 0 < 4) h
    (le_of_eq hb.symm) (fun i hi hi' => by
      have : i < 2 := lt_of_lt_of_eq hi' hb
      omega)
    (P := fun g => ∀ y : ruS, ruResFS y = ruResFS (ruTvS 4) * g →
      orderOf (y : ruS ⧸ ruZS) = 8)
    (fun t g ht hp y hy => (ruOrd8F_iff (hy ▸ rep_compA (rep_ruTv 4) ht)).1 hp)
    hall (ruResFS r) (ruResFS_mem_chainR hr)
  exact key _ (map_mul _ _ _)

theorem ruCoset_not_order
    {v : ℕ} (hv : v < 8) (h0 : v ≠ 0) (h4 : v ≠ 4) :
    ∃ y : ruS, (y : RuQ) = QuotientGroup.mk (ruTvS v) ∧ orderOf (y : ruS ⧸ ruZS) ≠ 8 := by
  have hfalse : all2 1920 (rawLevels 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase))
      (fun g => ruOrd8F (compA 1920 (ruTv v) g)) = false := by
    refine (getD_of_map_range_eight ruProfile_check v hv).trans ?_
    interval_cases v <;> simp_all
  obtain ⟨a, ha, b, hb, hp⟩ := exists_of_all2_false hfalse
  have h := ruChainR_check.1
  have hA : ChainArrays ruChainR ((ruField1920 4).extract 0 5) (ruField1920 4)
      (ruBaseArr 1920 ruRBase) (ruWordsArr 5 7 ruRDerivations) := ruChain_arrays h
  have hb2 : 2 ≤ ruChainR.baseCount := le_of_eq rfl
  have hrep := chain_rep_prod2A hA h hb2 ha hb
  have hmem := ruChainR.originalSubgroup.mul_mem (chain_levT_mem_original hA (by norm_num) h
    (by omega) ha) (chain_levT_mem_original hA (by norm_num) h (by omega) hb)
  obtain ⟨r, hr, hre⟩ := exists_of_mem_chainR hmem
  refine ⟨ruTvS v * r, (mem_coset_iff v _).2 ⟨r, hr, rfl⟩, fun hord => ?_⟩
  have hrep' : Rep 1920 (compA 1920 (ruTv v) (prod2A 1920
      (rawLevels 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase)) a b))
      (ruResFS (ruTvS v * r)) := by
    rw [map_mul, hre]
    exact rep_compA (rep_ruTv v) hrep
  rw [(ruOrd8F_iff hrep').2 hord] at hp
  exact Bool.noConfusion hp

theorem card_ruZS :
    Nat.card ruZS = 2 := by
  have h := center_ruS
  have hc : Nat.card ((Subgroup.center ruS).map ruS.subtype) = Nat.card ruZS :=
    Subgroup.card_map_of_injective ruS.subtype_injective
  rw [← hc, h, Nat.card_zpowers, orderOf_ruZ]

theorem ruZS_le :
    ruZS ≤ ruRS := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  rcases (mem_ruZS_iff x).1 hx with h | h
  · rw [h]
    exact ruR.one_mem
  · rw [h]
    exact ruZ_memR

abbrev ruRZ :
    Subgroup (ruS ⧸ ruZS) := ruRS.map (QuotientGroup.mk' ruZS)

theorem card_ruRZ :
    Nat.card ruRZ = 1024 := by
  let f := (QuotientGroup.mk' ruZS).comp ruRS.subtype
  have hker : f.ker = ruZS.subgroupOf ruRS := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have h := card_ker_mul_card_range f
  rw [hker, card_subgroupOf_of_le ruZS_le, card_ruZS, card_ruRS, MonoidHom.range_comp,
    Subgroup.range_subtype] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (h.trans (by norm_num))

theorem card_coset
    (c : RuQ) :
    Nat.card {x : ruS ⧸ ruZS // ∃ y : ruS, (y : RuQ) = c ∧ (y : ruS ⧸ ruZS) = x} = 1024 := by
  obtain ⟨v, -, rfl⟩ := exists_ruTvS c
  set t := ruTvS v
  let e : ruRZ → {x : ruS ⧸ ruZS // ∃ y : ruS, (y : RuQ) = QuotientGroup.mk t ∧
      (y : ruS ⧸ ruZS) = x} := fun u => ⟨(t : ruS ⧸ ruZS) * u, by
    obtain ⟨r, hr, hu⟩ := u.2
    refine ⟨t * r, (mem_coset_iff v _).2 ⟨r, hr, rfl⟩, ?_⟩
    rw [QuotientGroup.mk_mul, ← hu]
    rfl⟩
  have hbij : Function.Bijective e := by
    refine ⟨fun u u' h => Subtype.ext (mul_left_cancel (congrArg Subtype.val h)), ?_⟩
    rintro ⟨x, y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (mem_coset_iff v y).1 hy
    exact ⟨⟨(r : ruS ⧸ ruZS), r, hr, rfl⟩, Subtype.ext (QuotientGroup.mk_mul _ _ _).symm⟩
  rw [← Nat.card_eq_of_bijective e hbij, card_ruRZ]

theorem ruUnique_coset :
    ∃! c : RuQ, c ≠ 1 ∧
    ∀ y : ruS, (y : RuQ) = c → orderOf (y : ruS ⧸ ruZS) = 8 := by
  refine ⟨QuotientGroup.mk (ruTvS 4), ⟨?_, fun y hy => ruCoset4_order hy⟩, ?_⟩
  · intro h
    have := congrArg ruLabelEquiv h
    rw [ruTvS_label 4 (by norm_num), map_one] at this
    exact absurd (congrArg Multiplicative.toAdd this) (by decide)
  · rintro c ⟨hc1, hc⟩
    obtain ⟨v, hv, rfl⟩ := exists_ruTvS c
    have h0 := ruTvS_one_ne hv hc1
    by_contra h4
    have hv4 : v ≠ 4 := fun h => h4 (by rw [h])
    obtain ⟨y, hy, hord⟩ := ruCoset_not_order hv h0 hv4
    exact hord (hc y hy)

theorem quot_transfer {G : Type*} [Group G] {N M : Subgroup G} [N.Normal] [M.Normal] (h : N = M)
    (P : ∀ (K : Subgroup G) [K.Normal], Prop) (hN : P N) : P M := by
  subst h
  exact hN

theorem AT_Ru_Sylow_order_profile_automorphisms :
    (Subgroup.center ruS).map ruS.subtype = Subgroup.zpowers ruZ ∧
    Nat.card (ruS ⧸ ruR.subgroupOf ruS) = 8 ∧
    (∃! c : ruS ⧸ ruR.subgroupOf ruS, c ≠ 1 ∧ ∀ y : ruS,
      (y : ruS ⧸ ruR.subgroupOf ruS) = c → orderOf (y : ruS ⧸ Subgroup.center ruS) = 8) ∧
    (∀ c : ruS ⧸ ruR.subgroupOf ruS, Nat.card {x : ruS ⧸ Subgroup.center ruS //
      ∃ y : ruS, (y : ruS ⧸ ruR.subgroupOf ruS) = c ∧
        (y : ruS ⧸ Subgroup.center ruS) = x} = 1024) ∧
    Group.IsSolvable (MulAut ruS) := by
  refine ⟨center_ruS, card_ruQ, ruUnique_coset, card_coset, ?_⟩
  have helem : CFSG.IsElementaryAbelian 2 (ruS ⧸ commutator ruS) :=
    quot_transfer ruRS_eq_commutator (fun K _ => CFSG.IsElementaryAbelian 2 (ruS ⧸ K)) ruQ_elem
  have hcard : Nat.card (ruS ⧸ commutator ruS) = 8 :=
    quot_transfer ruRS_eq_commutator (fun K _ => Nat.card (ruS ⧸ K) = 8) card_ruQ
  have huniq : ∃! c : ruS ⧸ commutator ruS, c ≠ 1 ∧
      ∀ y : ruS, (y : ruS ⧸ commutator ruS) = c → orderOf (y : ruS ⧸ ruZS) = 8 :=
    quot_transfer ruRS_eq_commutator (fun K _ => ∃! c : ruS ⧸ K, c ≠ 1 ∧
      ∀ y : ruS, (y : ruS ⧸ K) = c → orderOf (y : ruS ⧸ ruZS) = 8) ruUnique_coset
  exact CFSG.Sporadic.SchreierLemmas.characteristic_Frattini_coset_automorphisms isPGroup_ruS
    ruZS helem hcard huniq

end CFSG.Sporadic.RuSchreier
