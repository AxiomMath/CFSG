module

public import CFSG.RankThree.Transfer.WeaklyClosed

public section

namespace CFSG.RankThree.Transfer.WCP

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.RankThree.Transfer (smul_eq_iff_mem)

variable {G : Type*} [Group G] [Finite G]

section FixVal

variable {A : Type*} [CommGroup A] (N : Subgroup G) (a : G) (φ : ↥N →* A)

noncomputable def fixVal (c : G ⧸ N) : A :=
  haveI := Classical.dec (c.out⁻¹ * a * c.out ∈ N)
  if h : c.out⁻¹ * a * c.out ∈ N then φ ⟨_, h⟩ else 1

theorem map_conj_eq (n z : ↥N) : φ (n⁻¹ * z * n) = φ z := by
  rw [map_mul, map_mul, map_inv]
  exact inv_mul_cancel_comm _ _

theorem fixVal_smul {q : G} (hq : q * a = a * q) (c : G ⧸ N) :
    fixVal N a φ (q • c) = fixVal N a φ c := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ↥N, (q • c).out = q * c.out * n := by
    have h1 : ((q * c.out : G) : G ⧸ N) = q • c := by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']
    have h2 : ((q • c).out : G ⧸ N) = ((q * c.out : G) : G ⧸ N) := by
      rw [QuotientGroup.out_eq', h1]
    rw [QuotientGroup.eq] at h2
    refine ⟨⟨_, N.inv_mem h2⟩, ?_⟩
    simp [mul_assoc]
  have hconj : (q • c).out⁻¹ * a * (q • c).out =
      (n : G)⁻¹ * (c.out⁻¹ * a * c.out) * (n : G) := by
    rw [hn]
    have : q⁻¹ * a * q = a := by
      calc q⁻¹ * a * q = q⁻¹ * (q * a) := by rw [hq, mul_assoc]
        _ = a := by group
    calc (q * c.out * ↑n)⁻¹ * a * (q * c.out * ↑n)
        = (↑n)⁻¹ * (c.out⁻¹ * (q⁻¹ * a * q) * c.out) * ↑n := by group
      _ = _ := by rw [this]
  unfold fixVal
  by_cases hmem : c.out⁻¹ * a * c.out ∈ N
  · have hmem' : (q • c).out⁻¹ * a * (q • c).out ∈ N := by
      rw [hconj]
      exact N.mul_mem (N.mul_mem (N.inv_mem n.2) hmem) n.2
    rw [dif_pos hmem, dif_pos hmem']
    have e : (⟨(q • c).out⁻¹ * a * (q • c).out, hmem'⟩ : ↥N) = n⁻¹ * ⟨_, hmem⟩ * n :=
      Subtype.ext hconj
    rw [e, map_conj_eq]
  · have hmem' : (q • c).out⁻¹ * a * (q • c).out ∉ N := by
      rw [hconj]
      intro h
      apply hmem
      have := N.mul_mem (N.mul_mem n.2 h) (N.inv_mem n.2)
      simpa [mul_assoc] using this
    rw [dif_neg hmem, dif_neg hmem']

theorem prod_orbit_fixVal [Fintype (G ⧸ N)]
    [DecidableEq (Quotient (MulAction.orbitRel (Subgroup.zpowers a) (G ⧸ N)))] {p : ℕ}
    (hp : p.Prime) (ha : a ^ p = 1)
    (q : Quotient (MulAction.orbitRel (Subgroup.zpowers a) (G ⧸ N))) :
    φ ⟨q.out.out⁻¹ * a ^ Function.minimalPeriod (a • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem N a q.out⟩ =
      ∏ c : {c : G ⧸ N // Quotient.mk _ c = q}, fixVal N a φ c := by
  have hq : ∀ c : G ⧸ N, Quotient.mk (MulAction.orbitRel (Subgroup.zpowers a) (G ⧸ N)) c = q ↔
      c ∈ MulAction.orbit (Subgroup.zpowers a) q.out := by
    intro c
    rw [← MulAction.orbitRel_apply,
      ← Quotient.eq (r := MulAction.orbitRel (Subgroup.zpowers a) (G ⧸ N)), Quotient.out_eq]
  have hperp : Function.IsPeriodicPt (a • ·) p q.out := by
    show (a • ·)^[p] q.out = q.out
    simp [smul_iterate, ha]
  rcases (Nat.dvd_prime hp).1 hperp.minimalPeriod_dvd with h1 | h2
  ·
    have hfix : a • q.out = q.out := Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1
    have hmem : q.out.out⁻¹ * a * q.out.out ∈ N := (smul_eq_iff_mem N a q.out).1 hfix
    have hstab : ∀ x : ↥(Subgroup.zpowers a), x • q.out = q.out := by
      intro x
      have : Subgroup.zpowers a ≤ MulAction.stabilizer G q.out :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfix)
      exact MulAction.mem_stabilizer_iff.1 (this x.2)
    rw [Fintype.prod_eq_single ⟨q.out, Quotient.out_eq q⟩]
    · show _ = fixVal N a φ q.out
      unfold fixVal
      rw [dif_pos hmem]
      exact congrArg φ (Subtype.ext (by simp [h1]))
    · rintro ⟨c, hc⟩ hne
      exfalso
      apply hne
      obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.1 ((hq c).1 hc)
      exact Subtype.ext (hx.symm.trans (hstab x))
  ·
    have hnfix : a • q.out ≠ q.out := by
      intro h
      have h1 : Function.minimalPeriod (a • ·) q.out = 1 :=
        (Function.minimalPeriod_eq_one_iff_isFixedPt (f := (a • ·)) (x := q.out)).2 h
      have := hp.two_le
      omega
    have hL : φ ⟨q.out.out⁻¹ * a ^ Function.minimalPeriod (a • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem N a q.out⟩ = 1 :=
      (congrArg φ (Subtype.ext (by simp [h2, ha]))).trans (map_one φ)
    refine hL.trans (Fintype.prod_eq_one _ fun ⟨c, hc⟩ => ?_).symm
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.1 ((hq c).1 hc)
    have hxa : (x : G) * a = a * x := by
      obtain ⟨x, hx'⟩ := x
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
      exact ((Commute.self_zpow a k).symm).eq
    have hnc : ¬ (c.out⁻¹ * a * c.out ∈ N) := by
      rw [← smul_eq_iff_mem]
      intro h
      apply hnfix
      rw [← hx, Subgroup.smul_def] at h
      have h' : (x : G) • (a • q.out) = (x : G) • q.out := by
        rw [smul_smul, hxa, ← smul_smul]
        exact h
      exact MulAction.injective (x : G) h'
    show fixVal N a φ c = 1
    unfold fixVal
    rw [dif_neg hnc]

theorem transfer_eq_prod_fixVal [Fintype (G ⧸ N)] {p : ℕ} (hp : p.Prime) (ha : a ^ p = 1) :
    φ.transfer a = ∏ c : G ⧸ N, fixVal N a φ c := by
  classical
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers a) (G ⧸ N))) :=
    Fintype.ofFinite _
  refine (MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot φ a).trans ?_
  rw [← Fintype.prod_fiberwise
    (fun c : G ⧸ N => Quotient.mk (MulAction.orbitRel (Subgroup.zpowers a) (G ⧸ N)) c)
    (fixVal N a φ)]
  exact Fintype.prod_congr _ _ (prod_orbit_fixVal N a φ hp ha)

theorem fixVal_one (ha : a ∈ N) : fixVal N a φ ((1 : G) : G ⧸ N) = φ ⟨a, ha⟩ := by
  have h0 : ((1 : G) : G ⧸ N).out ∈ N := by
    simpa using N.inv_mem (QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ N)))
  have hmem : ((1 : G) : G ⧸ N).out⁻¹ * a * ((1 : G) : G ⧸ N).out ∈ N :=
    N.mul_mem (N.mul_mem (N.inv_mem h0) ha) h0
  unfold fixVal
  rw [dif_pos hmem]
  have e : (⟨_, hmem⟩ : ↥N) = (⟨_, h0⟩ : ↥N)⁻¹ * ⟨a, ha⟩ * ⟨_, h0⟩ := Subtype.ext rfl
  rw [e, map_conj_eq]

theorem fixVal_pow {p : ℕ} (ha : a ^ p = 1) (c : G ⧸ N) : fixVal N a φ c ^ p = 1 := by
  unfold fixVal
  split_ifs with h
  · rw [← map_pow]
    have e : (⟨c.out⁻¹ * a * c.out, h⟩ : ↥N) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show (c.out⁻¹ * a * c.out) ^ p = 1
      rw [show c.out⁻¹ * a * c.out = c.out⁻¹ * a * (c.out⁻¹)⁻¹ by rw [inv_inv], conj_pow, ha,
        mul_one, mul_inv_cancel]
    rw [e, map_one]
  · exact one_pow p

end FixVal

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_conj_mem_sylow {N T : Subgroup G} (S : Sylow p G) (hSN : (S : Subgroup G) ≤ N)
    (hTN : T ≤ N) (hT : IsPGroup p T) : ∃ n ∈ N, ∀ t ∈ T, n⁻¹ * t * n ∈ (S : Subgroup G) := by
  haveI : Finite (Sylow p G) := S.finite_of_finiteIndex
  have hT' : IsPGroup p (T.subgroupOf N) := hT.comap_subtype
  obtain ⟨R, hR⟩ := hT'.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N (S.subtype hSN) R
  refine ⟨n, n.2, fun t ht => ?_⟩
  have h1 : (⟨t, hTN ht⟩ : N) ∈ (R : Subgroup N) :=
    hR (by simpa [Subgroup.mem_subgroupOf] using ht)
  rw [← hn] at h1
  simp [Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  exact h1

theorem eq_one_of_forall_smul_eq {Q : Subgroup G} (S : Sylow p G) (hQS : Q ≤ S)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G))
    (hwc : ∀ g : G, conjSubgroup g Q ≤ S → conjSubgroup g Q = Q)
    (c : G ⧸ Subgroup.normalizer (Q : Set G)) (hc : ∀ q ∈ Q, q • c = c) :
    c = ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) := by
  have h1 : ∀ q ∈ Q, c.out⁻¹ * q * c.out ∈ Subgroup.normalizer (Q : Set G) :=
    fun q hq => (smul_eq_iff_mem _ q c).1 (hc q hq)
  have hTN : conjSubgroup c.out⁻¹ Q ≤ Subgroup.normalizer (Q : Set G) := by
    intro y hy
    rw [mem_conjSubgroup, inv_inv] at hy
    simpa [mul_assoc] using h1 _ hy
  have hT : IsPGroup p (conjSubgroup c.out⁻¹ Q) :=
    (S.isPGroup'.to_le hQS).map (MulAut.conj c.out⁻¹).toMonoidHom
  obtain ⟨n, hnN, hn⟩ := exists_conj_mem_sylow S hSN hTN hT
  have hle : conjSubgroup (c.out * n)⁻¹ Q ≤ S := by
    intro y hy
    rw [mem_conjSubgroup, inv_inv] at hy
    have ht : n * y * n⁻¹ ∈ conjSubgroup c.out⁻¹ Q := by
      rw [mem_conjSubgroup, inv_inv]
      simpa [mul_assoc] using hy
    simpa [mul_assoc] using hn _ ht
  have hEq := hwc _ hle
  have hxn : c.out * n ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := SetLike.ext_iff.1 hEq h
    rw [mem_conjSubgroup, inv_inv] at this
    exact this.symm
  have hx : c.out ∈ Subgroup.normalizer (Q : Set G) := by
    simpa using Subgroup.mul_mem _ hxn (Subgroup.inv_mem _ hnN)
  calc c = ((c.out : G) : G ⧸ Subgroup.normalizer (Q : Set G)) := (QuotientGroup.out_eq' c).symm
    _ = ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) :=
        QuotientGroup.eq.2 (by simpa using Subgroup.inv_mem _ hx)

theorem prod_fixVal_eq_fixVal_one {Q N : Subgroup G} [Fintype (G ⧸ N)] (hQp : IsPGroup p Q)
    (hQN : Q ≤ N) (hfix : ∀ c : G ⧸ N, (∀ q ∈ Q, q • c = c) → c = ((1 : G) : G ⧸ N))
    {A : Type*} [CommGroup A] (φ : ↥N →* A) {a : G} (hcomm : ∀ q ∈ Q, q * a = a * q)
    (ha : a ^ p = 1) :
    ∏ c : G ⧸ N, fixVal N a φ c = fixVal N a φ ((1 : G) : G ⧸ N) := by
  classical
  set f : G ⧸ N → A := fixVal N a φ with hfdef
  set c₁ : G ⧸ N := ((1 : G) : G ⧸ N)
  have hc₁ : ∀ q : ↥Q, (q : G) • c₁ = c₁ := fun q => by
    show (q : G) • ((1 : G) : G ⧸ N) = ((1 : G) : G ⧸ N)
    rw [MulAction.Quotient.smul_coe]
    exact QuotientGroup.eq.2 (by simpa using N.inv_mem (hQN q.2))
  have hcount : ∀ v : A, ((Finset.univ : Finset (G ⧸ N)).filter (fun c => f c = v)).card ≡
      (if f c₁ = v then 1 else 0) [MOD p] := by
    intro v
    let Y : SubMulAction ↥Q (G ⧸ N) :=
      { carrier := {c | f c = v}
        smul_mem' := fun q c hc => by
          show f ((q : G) • c) = v
          rw [hfdef, fixVal_smul N a φ (hcomm q q.2)]
          exact hc }
    have hmod : Nat.card Y ≡ Nat.card (MulAction.fixedPoints ↥Q Y) [MOD p] :=
      hQp.card_modEq_card_fixedPoints Y
    have hcard : Nat.card Y = ((Finset.univ : Finset (G ⧸ N)).filter (fun c => f c = v)).card := by
      show Nat.card {c : G ⧸ N // f c = v} = _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfp : ∀ y : Y, y ∈ MulAction.fixedPoints ↥Q Y → (y : G ⧸ N) = c₁ := by
      intro y hy
      refine hfix (y : G ⧸ N) fun q hq => ?_
      have h2 := congrArg (fun z : Y => (z : G ⧸ N)) (MulAction.mem_fixedPoints.1 hy ⟨q, hq⟩)
      simpa [SubMulAction.val_smul, Subgroup.smul_def] using h2
    have hfpc : Nat.card (MulAction.fixedPoints ↥Q Y) = if f c₁ = v then 1 else 0 := by
      split_ifs with h1
      · have hmem1 : c₁ ∈ Y := h1
        let y1 : Y := ⟨_, hmem1⟩
        have hy1 : y1 ∈ MulAction.fixedPoints ↥Q Y := by
          rw [MulAction.mem_fixedPoints]
          intro q
          exact Subtype.ext (by rw [SubMulAction.val_smul, Subgroup.smul_def]; exact hc₁ q)
        haveI : Nonempty (MulAction.fixedPoints ↥Q Y) := ⟨⟨y1, hy1⟩⟩
        haveI : Subsingleton (MulAction.fixedPoints ↥Q Y) :=
          ⟨fun ⟨y, hy⟩ ⟨z, hz⟩ => Subtype.ext (Subtype.ext ((hfp y hy).trans (hfp z hz).symm))⟩
        exact Nat.card_unique
      · haveI : IsEmpty (MulAction.fixedPoints ↥Q Y) :=
          ⟨fun ⟨y, hy⟩ => h1 (by rw [← hfp y hy]; exact y.2)⟩
        exact Nat.card_of_isEmpty
    rw [← hcard, ← hfpc]
    exact hmod
  have hprod := Finset.prod_comp (s := (Finset.univ : Finset (G ⧸ N))) (fun v : A => v) f
  rw [hprod]
  have hterm : ∀ v ∈ (Finset.univ : Finset (G ⧸ N)).image f,
      v ^ ((Finset.univ : Finset (G ⧸ N)).filter (fun c => f c = v)).card = if f c₁ = v then v else 1 := by
    intro v hv
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hv
    have hvp : f c ^ p = 1 := fixVal_pow N a φ ha c
    have hc := hcount (f c)
    unfold Nat.ModEq at hc
    rw [pow_eq_pow_mod _ hvp, hc]
    split_ifs with h
    · rw [Nat.one_mod_eq_one.mpr hp.out.one_lt.ne', pow_one]
    · rw [Nat.zero_mod, pow_zero]
  rw [Finset.prod_congr rfl hterm, Finset.prod_ite_eq]
  rw [if_pos (Finset.mem_image_of_mem f (Finset.mem_univ c₁))]

theorem transfer_apply_of_weaklyClosed {Q : Subgroup G} (S : Sylow p G) (hQS : Q ≤ S)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G))
    (hwc : ∀ g : G, conjSubgroup g Q ≤ S → conjSubgroup g Q = Q)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {A : Type*} [CommGroup A]
    (φ : ↥(Subgroup.normalizer (Q : Set G)) →* A) {a : G} (ha : a ∈ Q) (hap : a ^ p = 1) :
    φ.transfer a = φ ⟨a, Subgroup.le_normalizer ha⟩ := by
  haveI : Fintype (G ⧸ Subgroup.normalizer (Q : Set G)) := Fintype.ofFinite _
  refine (transfer_eq_prod_fixVal _ a φ hp.out hap).trans ?_
  refine (prod_fixVal_eq_fixVal_one (S.isPGroup'.to_le hQS) Subgroup.le_normalizer
    (fun c hc => eq_one_of_forall_smul_eq S hQS hSN hwc c hc) φ
    (fun q hq => hQab q hq a ha) hap).trans ?_
  exact fixVal_one _ a φ (Subgroup.le_normalizer ha)

theorem mem_commutator_of_weaklyClosed {Q : Subgroup G} (S : Sylow p G) (hQS : Q ≤ S)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G))
    (hwc : ∀ g : G, conjSubgroup g Q ≤ S → conjSubgroup g Q = Q)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {a : G} (ha : a ∈ Q) (hap : a ^ p = 1)
    (haG : a ∈ commutator G) :
    (⟨a, Subgroup.le_normalizer ha⟩ : ↥(Subgroup.normalizer (Q : Set G))) ∈
      commutator ↥(Subgroup.normalizer (Q : Set G)) := by
  have h := transfer_apply_of_weaklyClosed S hQS hSN hwc hQab
    (Abelianization.of : ↥(Subgroup.normalizer (Q : Set G)) →* _) ha hap
  have h1 : (Abelianization.of : ↥(Subgroup.normalizer (Q : Set G)) →* _).transfer a = 1 :=
    Abelianization.commutator_subset_ker _ haG
  rw [h1] at h
  rw [← Abelianization.ker_of]
  exact h.symm

end CFSG.RankThree.Transfer.WCP
