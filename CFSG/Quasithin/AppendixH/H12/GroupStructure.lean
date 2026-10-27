module

public import CFSG.Quasithin.AppendixH.H12.GroupPerm
public import CFSG.Quasithin.AppendixH.H12.GroupHat
public import CFSG.Quasithin.AppendixH.H12.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

open scoped commutatorElement

set_option maxRecDepth 200000 in
private theorem alt6_not_comm : ∃ a b : ↥(alternatingGroup (Fin 6)), a * b ≠ b * a := by
  decide

theorem structure_M {Γ : Type*} [Group Γ] [Finite Γ] {M Q : Subgroup Γ} {ω : Γ}
    (hMcard : Nat.card M ≤ 17280) (hQM : Q ≤ M) (hQcard : 16 ≤ Nat.card Q)
    (hωM : ω ∈ M) (hω3 : orderOf ω = 3) (hωc : ∀ m ∈ M, m * ω = ω * m) (hωQ : ω ∉ Q)
    (p : ↥M →* Equiv.Perm (Fin 6))
    (hpQ : ∀ q (hq : q ∈ Q), p ⟨q, hQM hq⟩ = 1) (hpω : p ⟨ω, hωM⟩ = 1)
    (hrange : 360 ≤ Nat.card p.range)
    (hcomm : ∃ a ∈ M, ∃ b ∈ M, ω⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ Q) :
    Nat.card Q = 16 ∧ pCoreOf 2 M = Q ∧
      IsExtHatOf M (pCoreOf 2 M) ↥(alternatingGroup (Fin 6)) := by
  let K : Subgroup Γ := Q ⊔ Subgroup.zpowers ω
  have hQK : Q ≤ K := le_sup_left
  have hZleK : Subgroup.zpowers ω ≤ K := by
    change Subgroup.zpowers ω ≤ Q ⊔ Subgroup.zpowers ω
    rw [Subgroup.sup_eq_closure]
    exact fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hωK : ω ∈ K := hZleK (Subgroup.mem_zpowers ω)
  have hKM : K ≤ M := sup_le hQM (Subgroup.zpowers_le.mpr hωM)
  have hcommQω : ∀ q ∈ Q, Commute q ω := fun q hq => hωc q (hQM hq)
  have hcommQz : ∀ q ∈ Q, ∀ z ∈ Subgroup.zpowers ω, q * z = z * q := by
    intro q hq z hz
    obtain ⟨k, rfl⟩ := (Subgroup.mem_zpowers_iff).mp hz
    exact (hcommQω q hq).zpow_right k
  have hω3pow : ω ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simpa [hω3] using pow_orderOf_eq_one ω
  have hdisj : Q ⊓ Subgroup.zpowers ω = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxQ, hxz⟩ := hx
    by_cases hx1 : x = 1
    · exact hx1
    · exfalso
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hxz
      have hx3 : x ^ 3 = 1 := by
        rw [← hk, ← zpow_natCast]
        calc (ω ^ k) ^ (3 : ℤ) = ω ^ (k * 3) := (zpow_mul ω k 3).symm
          _ = ω ^ (3 * k) := by rw [mul_comm]
          _ = (ω ^ (3 : ℤ)) ^ k := zpow_mul ω 3 k
          _ = 1 := by rw [hω3pow]; simp
      have hdvd3 : orderOf x ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr hx3
      have horderx : orderOf x = 3 := by
        rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf x) hdvd3 with h | h
        · exact absurd ((orderOf_eq_one_iff).mp h) hx1
        · exact h
      have hle : Subgroup.zpowers x ≤ Subgroup.zpowers ω := Subgroup.zpowers_le_of_mem hxz
      have heq : Subgroup.zpowers x = Subgroup.zpowers ω :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, horderx, hω3])
      exact hωQ (Subgroup.zpowers_le_of_mem hxQ (heq ▸ Subgroup.mem_zpowers ω))
  have hprod : ∀ x ∈ K, ∃ q ∈ Q, ∃ z ∈ Subgroup.zpowers ω, q * z = x := by
    intro x hx
    let φ : ↥Q × ↥(Subgroup.zpowers ω) →* Γ :=
      { toFun := fun a => (a.1 : Γ) * (a.2 : Γ)
        map_one' := by
          show (1 : Γ) * (1 : Γ) = 1
          rw [one_mul]
        map_mul' := by
          intro a b
          rw [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Subgroup.coe_mul]
          have h := hcommQz b.1 b.1.2 a.2 a.2.2
          calc (↑a.1 : Γ) * ↑b.1 * (↑a.2 * ↑b.2)
              = (↑a.1 : Γ) * ↑b.1 * ↑a.2 * ↑b.2 := by group
            _ = (↑a.1 : Γ) * (↑b.1 * ↑a.2) * ↑b.2 := by group
            _ = (↑a.1 : Γ) * (↑a.2 * ↑b.1) * ↑b.2 := by rw [h]
            _ = (↑a.1 : Γ) * ↑a.2 * (↑b.1 * ↑b.2) := by group }
    have hφrange : φ.range = K := by
      apply le_antisymm
      · rintro y ⟨⟨q, z⟩, rfl⟩
        exact Subgroup.mul_mem_sup q.2 z.2
      · apply sup_le
        · intro q hq
          exact ⟨(⟨q, hq⟩, 1), by
            change ((⟨q, hq⟩ : ↥Q) : Γ) * ((1 : ↥(Subgroup.zpowers ω)) : Γ) = q
            rw [Subgroup.coe_one, mul_one]⟩
        · intro z hz
          exact ⟨(1, ⟨z, hz⟩), by
            change ((1 : ↥Q) : Γ) * ((⟨z, hz⟩ : ↥(Subgroup.zpowers ω)) : Γ) = z
            rw [Subgroup.coe_one, one_mul]⟩
    have hxrange : x ∈ φ.range := by rw [hφrange]; exact hx
    rw [MonoidHom.mem_range] at hxrange
    obtain ⟨⟨q, z⟩, hqz⟩ := hxrange
    exact ⟨q, q.2, z, z.2, hqz⟩
  have hcardK_ge : Nat.card Q * 3 ≤ Nat.card K := by
    have hψinj : Function.Injective
        (fun a : ↥Q × ↥(Subgroup.zpowers ω) =>
          (⟨(a.1 : Γ) * (a.2 : Γ), Subgroup.mul_mem_sup a.1.2 a.2.2⟩ : ↥K)) := by
      intro a b hab
      have heq : (a.1 : Γ) * (a.2 : Γ) = (b.1 : Γ) * (b.2 : Γ) := by
        simpa using congrArg Subtype.val hab
      have h1 : (b.1 : Γ)⁻¹ * (a.1 : Γ) = (b.2 : Γ) * (a.2 : Γ)⁻¹ := by
        have h := congrArg (fun t : Γ => (b.1 : Γ)⁻¹ * t * (a.2 : Γ)⁻¹) heq
        simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
      have hmem : (b.1 : Γ)⁻¹ * (a.1 : Γ) ∈ Q ⊓ Subgroup.zpowers ω := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Q.mul_mem (Q.inv_mem b.1.2) a.1.2
        · rw [h1]
          exact Subgroup.mul_mem _ b.2.2 (Subgroup.inv_mem _ a.2.2)
      rw [hdisj, Subgroup.mem_bot] at hmem
      have ha1 : (b.1 : Γ) = a.1 := inv_mul_eq_one.mp hmem
      have hb2 : (b.2 : Γ) = a.2 := by
        have h : (b.2 : Γ) * (a.2 : Γ)⁻¹ = 1 := h1 ▸ hmem
        exact mul_inv_eq_one.mp h
      exact Prod.ext (Subtype.ext ha1.symm) (Subtype.ext hb2.symm)
    have := Nat.card_le_card_of_injective _ hψinj
    rwa [Nat.card_prod, Nat.card_zpowers, hω3] at this
  let E : Subgroup ↥M := K.subgroupOf M
  have hEdecomp : E = Q.subgroupOf M ⊔ (Subgroup.zpowers ω).subgroupOf M := by
    show (Q ⊔ Subgroup.zpowers ω).subgroupOf M = _
    rw [Subgroup.subgroupOf_sup hQM (Subgroup.zpowers_le.mpr hωM)]
  have hQker : Q.subgroupOf M ≤ p.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    have hqQ : (q : Γ) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have := hpQ q.val hqQ
    simpa using this
  have hZker : (Subgroup.zpowers ω).subgroupOf M ≤ p.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzZ : (z : Γ) ∈ Subgroup.zpowers ω := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hzZ
    have hzω : z = (⟨ω, hωM⟩ : ↥M) ^ k := by
      apply Subtype.ext
      exact hk.symm
    calc p z = p ((⟨ω, hωM⟩ : ↥M) ^ k) := by rw [hzω]
      _ = (p ⟨ω, hωM⟩) ^ k := MonoidHom.map_zpow p _ k
      _ = 1 := by rw [hpω]; simp
  have hEker : E ≤ p.ker := by
    rw [hEdecomp]
    exact sup_le hQker hZker
  have hcardE : Nat.card E = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have ha : 48 ≤ Nat.card E := by
    rw [hcardE]
    calc (48 : ℕ) = 16 * 3 := by norm_num
      _ ≤ Nat.card Q * 3 := Nat.mul_le_mul_right 3 hQcard
      _ ≤ Nat.card K := hcardK_ge
  have hM' : Nat.card M ≤ 48 * 360 := by
    rw [show (48 : ℕ) * 360 = 17280 by norm_num]; exact hMcard
  obtain ⟨hEeq, hcardE', hrange'⟩ :=
    ker_eq_of_counts p E hEker (a := 48) (b := 360) ha hrange hM'
  have hcardQ : Nat.card Q = 16 := by
    have h1 : Nat.card Q * 3 ≤ 48 := by
      rw [← hcardE, hcardE'] at hcardK_ge
      exact hcardK_ge
    omega
  have hRangeA6 : p.range = alternatingGroup (Fin 6) :=
    eq_alternatingGroup_of_card p.range (by rw [hrange']; norm_num)
  have hq16 : ∀ q ∈ Q, q ^ 16 = 1 := by
    intro q hq
    haveI : Fintype ↥Q := Fintype.ofFinite _
    have h := pow_card_eq_one (x := (⟨q, hq⟩ : ↥Q))
    rw [show Fintype.card ↥Q = 16 by rw [← Nat.card_eq_fintype_card, hcardQ]] at h
    simpa using congrArg Subtype.val h
  have hchar : ∀ x ∈ K, x ^ 16 = 1 ↔ x ∈ Q := by
    intro x hx
    constructor
    · intro hx16
      obtain ⟨q, hq, z, hz, hxz⟩ := hprod x hx
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hz
      have hcq : Commute q (ω ^ k) := (hcommQω q hq).zpow_right k
      have hx16val : (q * ω ^ k) ^ 16 = ω ^ k := by
        rw [hcq.mul_pow, hq16 q hq, one_mul, ← zpow_natCast]
        calc (ω ^ k) ^ (16 : ℤ) = ω ^ (k * 16) := (zpow_mul ω k 16).symm
          _ = ω ^ (16 * k) := by rw [mul_comm]
          _ = ω ^ k := by
            have h : (16 : ℤ) * k = k + 3 * (5 * k) := by ring
            rw [h, zpow_add, zpow_mul, hω3pow]; simp
      have hxqk : x = q * ω ^ k := by rw [← hxz, ← hk]
      rw [hxqk] at hx16 ⊢
      have hωk1 : ω ^ k = 1 := by rw [← hx16val]; exact hx16
      rw [hωk1, mul_one]
      exact hq
    · intro hxQ
      exact hq16 x hxQ
  have hKnorm : (K.subgroupOf M).Normal := by
    rw [show K.subgroupOf M = E from rfl, hEeq]
    exact MonoidHom.normal_ker p
  have hQnormal_M : (Q.subgroupOf M).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnK : (n : Γ) ∈ K := hQK hn
    have hn16 : (n : Γ) ^ 16 = 1 := (hchar n hnK).mpr hn
    have hconjK : ((g : Γ) * n * (g : Γ)⁻¹) ∈ K := by
      have : (g * n * g⁻¹) ∈ K.subgroupOf M :=
        hKnorm.conj_mem n (Subgroup.mem_subgroupOf.mpr hnK) g
      exact Subgroup.mem_subgroupOf.mp this
    have hconj16 : ((g : Γ) * n * (g : Γ)⁻¹) ^ 16 = 1 := by
      rw [conj_pow, hn16]
      group
    exact (hchar _ hconjK).mp hconj16
  have hPGQ : IsPGroup 2 Q := IsPGroup.of_card (n := 4) (by rw [hcardQ]; norm_num)
  have hPGQsub : IsPGroup 2 (Q.subgroupOf M) :=
    hPGQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  have hQ_le_pcore : Q.subgroupOf M ≤ pCore 2 ↥M := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (Q.subgroupOf M)
      (le_iSup_of_le hQnormal_M (le_iSup_of_le hPGQsub le_rfl))
  have hSimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
  have hncA6 : ∃ a b : ↥(alternatingGroup (Fin 6)), a * b ≠ b * a := alt6_not_comm
  let qmap : ↥M →* ↥(alternatingGroup (Fin 6)) :=
    p.codRestrict (alternatingGroup (Fin 6)) (fun x => by
      rw [← hRangeA6]; exact ⟨x, rfl⟩)
  have hqmapker : qmap.ker = p.ker := MonoidHom.ker_codRestrict p _ _
  have hqmapsurj : Function.Surjective qmap := by
    intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ p.range := by rw [hRangeA6]; exact y.2
    rcases hy with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hleQ : pCore 2 ↥M ≤ Q.subgroupOf M := by
    have hPnorm : (pCore 2 ↥M).Normal := pCore_normal
    have hPp : IsPGroup 2 (pCore 2 ↥M) := pCore_isPGroup
    have hmapnorm : ((pCore 2 ↥M).map qmap).Normal := hPnorm.map qmap hqmapsurj
    have hmapP : IsPGroup 2 ((pCore 2 ↥M).map qmap) := IsPGroup.map hPp qmap
    haveI := hSimple
    have hbot := normal_pGroup_eq_bot_of_simple hncA6 _ hmapnorm hmapP
    have hle : pCore 2 ↥M ≤ qmap.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have hleK : pCore 2 ↥M ≤ K.subgroupOf M := by
      rw [show K.subgroupOf M = E from rfl, hEeq, ← hqmapker]
      exact hle
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxK : (x : Γ) ∈ K := Subgroup.mem_subgroupOf.mp (hleK hx)
    have hdiv : Nat.card ↥(pCore 2 ↥M) ∣ 48 := by
      have h := Subgroup.card_subgroup_dvd_card ((pCore 2 ↥M).subgroupOf (K.subgroupOf M))
      have hcong : Nat.card ↥((pCore 2 ↥M).subgroupOf (K.subgroupOf M)) =
          Nat.card ↥(pCore 2 ↥M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleK).toEquiv
      have hE48 : Nat.card ↥(K.subgroupOf M) = 48 := by
        show Nat.card ↥E = 48
        exact hcardE'
      rw [hcong, hE48] at h
      exact h
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hPp
    have h16 : Nat.card ↥(pCore 2 ↥M) ∣ 16 := by
      rw [hm] at hdiv ⊢
      have hcop : Nat.Coprime (2 ^ m) 3 :=
        Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)
      have h : 2 ^ m ∣ 16 * 3 := by rwa [show (16 : ℕ) * 3 = 48 by norm_num]
      exact Nat.Coprime.dvd_of_dvd_mul_right hcop h
    have hxord : orderOf x ∣ 16 := (Subgroup.orderOf_dvd_natCard (pCore 2 ↥M) hx).trans h16
    have hx16 : (x : Γ) ^ 16 = 1 := by
      have h := (orderOf_dvd_iff_pow_eq_one).mp hxord
      simpa using congrArg Subtype.val h
    exact (hchar x.val hxK).mp hx16
  have hpcore : pCoreOf 2 M = Q := by
    apply le_antisymm
    · show (pCore 2 ↥M).map M.subtype ≤ Q
      rw [← Subgroup.map_subgroupOf_eq_of_le hQM]
      exact Subgroup.map_mono hleQ
    · show Q ≤ (pCore 2 ↥M).map M.subtype
      rw [← Subgroup.map_subgroupOf_eq_of_le hQM]
      exact Subgroup.map_mono hQ_le_pcore
  let N : Subgroup ↥M := Q.subgroupOf M
  letI : N.Normal := hQnormal_M
  let Y := ↥M ⧸ N
  let ωbar : Y := QuotientGroup.mk' N ⟨ω, hωM⟩
  have hle_qmap : N ≤ qmap.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show p x = 1
    have hxQ : (x : Γ) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    have := hpQ x.val hxQ
    simpa using this
  let pBar : Y →* ↥(alternatingGroup (Fin 6)) := QuotientGroup.lift N qmap hle_qmap
  have hpBar_surj : Function.Surjective pBar :=
    QuotientGroup.lift_surjective_of_surjective N qmap hqmapsurj hle_qmap
  have hpBar_ker : pBar.ker = Subgroup.zpowers ωbar := by
    have hker : pBar.ker = (K.subgroupOf M).map (QuotientGroup.mk' N) := by
      rw [QuotientGroup.ker_lift]
      rw [hqmapker, show K.subgroupOf M = E from rfl, hEeq]
    rw [hker]
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hxK : (x : Γ) ∈ K := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨q, hq, z, hz, hxz⟩ := hprod x.val hxK
      obtain ⟨i, hi⟩ := (Subgroup.mem_zpowers_iff).mp hz
      have hzM : (z : Γ) ∈ M := hKM (hZleK hz)
      have hxprod : x = (⟨q, hQM hq⟩ : ↥M) * ⟨z, hzM⟩ := by
        apply Subtype.ext
        exact hxz.symm
      rw [hxprod, map_mul]
      have hqmk : QuotientGroup.mk' N ⟨q, hQM hq⟩ = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hq)
      rw [hqmk, one_mul]
      have hzmk : QuotientGroup.mk' N ⟨z, hzM⟩ = ωbar ^ i := by
        have heqz : (⟨z, hzM⟩ : ↥M) = (⟨ω, hωM⟩ : ↥M) ^ i := by
          apply Subtype.ext
          exact hi.symm
        rw [heqz, map_zpow]
      rw [hzmk]
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map.mpr ⟨⟨ω, hωM⟩, Subgroup.mem_subgroupOf.mpr hωK, rfl⟩
  have hωbar_ne : ωbar ≠ 1 := by
    intro h
    have h1 : QuotientGroup.mk' N (⟨ω, hωM⟩ : ↥M) = 1 := by
      change ωbar = 1
      exact h
    rw [QuotientGroup.mk'_apply] at h1
    have h2 : (⟨ω, hωM⟩ : ↥M) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact hωQ (Subgroup.mem_subgroupOf.mp h2)
  have hωbar3 : ωbar ^ 3 = 1 := by
    have hω3pow' : (⟨ω, hωM⟩ : ↥M) ^ 3 = 1 := by
      apply Subtype.ext
      simpa [hω3] using pow_orderOf_eq_one ω
    calc ωbar ^ 3 = (QuotientGroup.mk' N ⟨ω, hωM⟩) ^ 3 := rfl
      _ = QuotientGroup.mk' N ((⟨ω, hωM⟩ : ↥M) ^ 3) := (map_pow _ _ 3).symm
      _ = QuotientGroup.mk' N 1 := by rw [hω3pow']
      _ = 1 := map_one _
  have horderωbar : orderOf ωbar = 3 := orderOf_eq_prime hωbar3 hωbar_ne
  have hωbar_center : ωbar ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N y
    change QuotientGroup.mk' N m * QuotientGroup.mk' N ⟨ω, hωM⟩ =
      QuotientGroup.mk' N ⟨ω, hωM⟩ * QuotientGroup.mk' N m
    have heq : (m * ⟨ω, hωM⟩ : ↥M) = ⟨ω, hωM⟩ * m := by
      apply Subtype.ext
      exact hωc m m.2
    rw [← map_mul, ← map_mul, heq]
  have hωcomm : ωbar ∈ commutator Y := by
    obtain ⟨a, ha, b, hb, hab⟩ := hcomm
    let abar : Y := QuotientGroup.mk' N ⟨a, ha⟩
    let bbar : Y := QuotientGroup.mk' N ⟨b, hb⟩
    have hcommel : ⁅abar, bbar⁆ = ωbar := by
      have hxM : (⟨ω, hωM⟩⁻¹ * (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) : ↥M) ∈ N :=
        Subgroup.mem_subgroupOf.mpr (by simpa using hab)
      have h1 : QuotientGroup.mk' N
          (⟨ω, hωM⟩⁻¹ * (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) : ↥M) = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr hxM
      have h2 : QuotientGroup.mk' N
          (⟨ω, hωM⟩⁻¹ * (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) : ↥M) =
          ωbar⁻¹ * ⁅abar, bbar⁆ := by
        rw [commutatorElement_def]
        simp only [map_mul, map_inv]
        rfl
      rw [h2] at h1
      exact (inv_mul_eq_one.mp h1).symm
    rw [← hcommel]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hperfA6 : Group.IsPerfect ↥(alternatingGroup (Fin 6)) :=
    Group.isPerfect_def.mpr
      (commutator_alternatingGroup_eq_top (by norm_num : 5 ≤ Nat.card (Fin 6)))
  have hperf : Group.IsPerfect Y :=
    isPerfect_of_central_cover pBar hpBar_surj hperfA6 ωbar hpBar_ker hωcomm
  haveI : Fintype Y := Fintype.ofFinite _
  let e : Y ≃ Fin (Fintype.card Y) := Fintype.equivFin Y
  letI : Mul (Fin (Fintype.card Y)) := e.symm.mul
  letI : Group (Fin (Fintype.card Y)) := e.symm.group
  let e0 : Fin (Fintype.card Y) ≃* Y :=
    { toEquiv := e.symm
      map_mul' := by
        intro x y
        change e.symm (e (e.symm x * e.symm y)) = e.symm x * e.symm y
        rw [Equiv.symm_apply_apply] }
  let ω0 : Fin (Fintype.card Y) := e0.symm ωbar
  let pBar0 : Fin (Fintype.card Y) →* ↥(alternatingGroup (Fin 6)) :=
    pBar.comp e0.toMonoidHom
  have hpBar0_surj : Function.Surjective pBar0 := hpBar_surj.comp e0.surjective
  have horderω0 : orderOf ω0 = 3 := by
    change orderOf (e0.symm ωbar) = 3
    rw [MulEquiv.orderOf_eq, horderωbar]
  have hω0_center : ω0 ∈ Subgroup.center (Fin (Fintype.card Y)) := by
    rw [← Subgroup.map_center_eq (f := e0.symm)]
    exact Subgroup.mem_map.mpr ⟨ωbar, hωbar_center, rfl⟩
  have hpBar0_ker : pBar0.ker = Subgroup.zpowers ω0 := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hex : e0 x ∈ Subgroup.zpowers ωbar := by
        rw [← hpBar_ker, MonoidHom.mem_ker]
        exact hx
      rw [Subgroup.mem_zpowers_iff] at hex ⊢
      obtain ⟨i, hi⟩ := hex
      refine ⟨i, ?_⟩
      apply e0.injective
      rw [map_zpow, show e0 ω0 = ωbar from e0.apply_symm_apply ωbar]
      exact hi
    · intro hx
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      change pBar (e0 (ω0 ^ i)) = 1
      have hωbarker : pBar ωbar = 1 := by
        rw [← MonoidHom.mem_ker, hpBar_ker]
        exact Subgroup.mem_zpowers ωbar
      rw [map_zpow, map_zpow, show e0 ω0 = ωbar from e0.apply_symm_apply ωbar,
        hωbarker, one_zpow]
  have hperf0 : Group.IsPerfect (Fin (Fintype.card Y)) := by
    haveI := hperf
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hIsHat0 : IsHat (Fin (Fintype.card Y)) ↥(alternatingGroup (Fin 6)) :=
    isHat_of_central_cover pBar0 hpBar0_surj hSimple hncA6 ω0 horderω0 hω0_center
      hpBar0_ker hperf0
  let f : ↥M →* Fin (Fintype.card Y) := e0.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf_surj : Function.Surjective f :=
    e0.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hf_ker : f.ker = N := by
    change (e0.symm.toMonoidHom.comp (QuotientGroup.mk' N)).ker = N
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N) e0.symm.toMonoidHom e0.symm.injective,
      QuotientGroup.ker_mk']
  refine ⟨hcardQ, hpcore, ?_⟩
  refine ⟨?_, Fin (Fintype.card Y), inferInstance, f, hf_surj, ?_, hIsHat0⟩
  · rw [hpcore]; exact hQM
  · rw [hf_ker, hpcore]

theorem structure_S5 {Γ : Type*} [Group Γ] [Finite Γ] {X R : Subgroup Γ}
    (hXcard : Nat.card X ≤ 1920) (hRX : R ≤ X) (hRcard : 16 ≤ Nat.card R)
    (p : ↥X →* Equiv.Perm (Fin 5)) (hpR : ∀ r (hr : r ∈ R), p ⟨r, hRX hr⟩ = 1)
    (hrange : 120 ≤ Nat.card p.range) :
    Nat.card R = 16 ∧ IsPGroup 2 R ∧ pCoreOf 2 X = R ∧
      IsExtOf X (pCoreOf 2 X) (Equiv.Perm (Fin 5)) := by
  let E : Subgroup ↥X := R.subgroupOf X
  have hcardE : Nat.card E = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
  have hEker : E ≤ p.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxR : (x : Γ) ∈ R := (Subgroup.mem_subgroupOf).mp hx
    have := hpR x.val hxR
    simpa using this
  have hX' : Nat.card X ≤ 16 * 120 := by
    rw [show (16:ℕ) * 120 = 1920 by norm_num]; exact hXcard
  obtain ⟨hEeq, hcardE', hrange'⟩ :=
    ker_eq_of_counts p E hEker (a := 16) (b := 120) (by rw [hcardE]; exact hRcard) hrange hX'
  have hcardR : Nat.card R = 16 := by rw [← hcardE, hcardE']
  have hPG : IsPGroup 2 R := IsPGroup.of_card (n := 4) (by rw [hcardR]; norm_num)
  have hRangeTop : p.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrange', Nat.card_perm]
    norm_num
  have hsurj : Function.Surjective p := MonoidHom.range_eq_top.mp hRangeTop
  have hpcore : pCoreOf 2 X = R := by
    apply le_antisymm
    ·
      have hPnorm : (pCore 2 ↥X).Normal := pCore_normal
      have hPp : IsPGroup 2 (pCore 2 ↥X) := pCore_isPGroup
      have hmapnorm : ((pCore 2 ↥X).map p).Normal := hPnorm.map p hsurj
      have hmapP : IsPGroup 2 ((pCore 2 ↥X).map p) := IsPGroup.map hPp p
      have hbot := perm5_normal_two_eq_bot _ hmapnorm hmapP
      have hle : pCore 2 ↥X ≤ p.ker := (Subgroup.map_eq_bot_iff _).mp hbot
      have hle' : pCore 2 ↥X ≤ E := by rw [hEeq]; exact hle
      show (pCore 2 ↥X).map X.subtype ≤ R
      rw [← Subgroup.map_subgroupOf_eq_of_le hRX]
      exact Subgroup.map_mono hle'
    ·
      have hEnorm : E.Normal := by rw [hEeq]; exact MonoidHom.normal_ker p
      have hEP : IsPGroup 2 E :=
        IsPGroup.of_card (n := 4) (by rw [hcardE']; norm_num)
      have hle_pcore : E ≤ pCore 2 ↥X := by
        rw [CFSG.pCore_eq_iSup]
        exact le_iSup_of_le E (le_iSup_of_le hEnorm (le_iSup_of_le hEP le_rfl))
      have hmap := Subgroup.map_mono (f := X.subtype) hle_pcore
      rw [Subgroup.map_subgroupOf_eq_of_le hRX] at hmap
      exact hmap
  refine ⟨hcardR, hPG, hpcore, ?_⟩
  refine ⟨?_, p, hsurj, ?_⟩
  · rw [hpcore]; exact hRX
  · rw [hpcore]; exact hEeq.symm

theorem structure_A5 {Γ : Type*} [Group Γ] [Finite Γ] {X R : Subgroup Γ}
    (hXcard : Nat.card X ≤ 960) (hRX : R ≤ X) (hRcard : 16 ≤ Nat.card R)
    (p : ↥X →* Equiv.Perm (Fin 5)) (hpR : ∀ r (hr : r ∈ R), p ⟨r, hRX hr⟩ = 1)
    (hrange : 60 ≤ Nat.card p.range) :
    Nat.card R = 16 ∧ IsPGroup 2 R ∧ pCoreOf 2 X = R ∧
      IsExtOf X (pCoreOf 2 X) ↥(alternatingGroup (Fin 5)) := by
  let E : Subgroup ↥X := R.subgroupOf X
  have hcardE : Nat.card E = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
  have hEker : E ≤ p.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxR : (x : Γ) ∈ R := (Subgroup.mem_subgroupOf).mp hx
    have := hpR x.val hxR
    simpa using this
  have hX' : Nat.card X ≤ 16 * 60 := by
    rw [show (16:ℕ) * 60 = 960 by norm_num]; exact hXcard
  obtain ⟨hEeq, hcardE', hrange'⟩ :=
    ker_eq_of_counts p E hEker (a := 16) (b := 60) (by rw [hcardE]; exact hRcard) hrange hX'
  have hcardR : Nat.card R = 16 := by rw [← hcardE, hcardE']
  have hPG : IsPGroup 2 R := IsPGroup.of_card (n := 4) (by rw [hcardR]; norm_num)
  have hRangeA5 : p.range = alternatingGroup (Fin 5) :=
    eq_alternatingGroup_of_card p.range (by rw [hrange']; norm_num)
  let q : ↥X →* ↥(alternatingGroup (Fin 5)) :=
    p.codRestrict (alternatingGroup (Fin 5)) (fun x => by
      rw [← hRangeA5]; exact ⟨x, rfl⟩)
  have hqker : q.ker = p.ker := MonoidHom.ker_codRestrict p _ _
  have hqsurj : Function.Surjective q := by
    intro y
    have hy : (y : Equiv.Perm (Fin 5)) ∈ p.range := by rw [hRangeA5]; exact y.2
    rcases hy with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hpcore : pCoreOf 2 X = R := by
    apply le_antisymm
    · have hPnorm : (pCore 2 ↥X).Normal := pCore_normal
      have hPp : IsPGroup 2 (pCore 2 ↥X) := pCore_isPGroup
      have hmapnorm : ((pCore 2 ↥X).map q).Normal := hPnorm.map q hqsurj
      have hmapP : IsPGroup 2 ((pCore 2 ↥X).map q) := IsPGroup.map hPp q
      have hnc : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a := by decide
      have hbot := normal_pGroup_eq_bot_of_simple hnc _ hmapnorm hmapP
      have hle : pCore 2 ↥X ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hbot
      have hle' : pCore 2 ↥X ≤ E := by rw [hEeq, ← hqker]; exact hle
      show (pCore 2 ↥X).map X.subtype ≤ R
      rw [← Subgroup.map_subgroupOf_eq_of_le hRX]
      exact Subgroup.map_mono hle'
    · have hEnorm : E.Normal := by rw [hEeq]; exact MonoidHom.normal_ker p
      have hEP : IsPGroup 2 E :=
        IsPGroup.of_card (n := 4) (by rw [hcardE']; norm_num)
      have hle_pcore : E ≤ pCore 2 ↥X := by
        rw [CFSG.pCore_eq_iSup]
        exact le_iSup_of_le E (le_iSup_of_le hEnorm (le_iSup_of_le hEP le_rfl))
      have hmap := Subgroup.map_mono (f := X.subtype) hle_pcore
      rw [Subgroup.map_subgroupOf_eq_of_le hRX] at hmap
      exact hmap
  refine ⟨hcardR, hPG, hpcore, ?_⟩
  refine ⟨?_, q, hqsurj, ?_⟩
  · rw [hpcore]; exact hRX
  · rw [hpcore]; exact hqker.trans hEeq.symm

end CFSG.Quasithin.AppendixH.H12
