module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Equiv

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private def centerOf (Q : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Q ⊓ Subgroup.centralizer (Q : Set (Perm Ω))

private theorem isPretransitive_of_normal_ne_bot {K N : Subgroup (Perm Ω)}
    (hK : MulAction.IsMultiplyPretransitive K Ω 2) (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) (hNne : N ≠ ⊥) :
    MulAction.IsPretransitive N Ω := by
  haveI : MulAction.IsPreprimitive K Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive hK
  haveI : MulAction.IsQuasiPreprimitive K Ω := inferInstance
  haveI : (N.subgroupOf K).Normal := hN
  have hfix : MulAction.fixedPoints (N.subgroupOf K) Ω ≠ Set.univ := by
    intro huniv
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNne
    have ha_ne : (a : Perm Ω) ≠ 1 := fun h1 => ha (Subtype.ext h1)
    have hx : ∃ x : Ω, (a : Perm Ω) x ≠ x := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact ha_ne (Equiv.ext hc)
    obtain ⟨x, hx⟩ := hx
    have hmem : x ∈ MulAction.fixedPoints (N.subgroupOf K) Ω := by
      rw [huniv]; trivial
    have hcon := (MulAction.mem_fixedPoints.mp hmem)
      (⟨⟨(a : Perm Ω), hNK a.2⟩, a.2⟩ : N.subgroupOf K)
    exact hx hcon
  haveI : MulAction.IsPretransitive (N.subgroupOf K) Ω :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := N.subgroupOf K) hfix
  exact MulAction.IsPretransitive.of_smul_eq
    (fun c : N.subgroupOf K => (⟨(c : K), Subgroup.mem_subgroupOf.mp c.2⟩ : N))
    (by intro c x; rfl)

private theorem card_le_card_of_normal_ne_bot (hΩ : Fintype.card Ω = 8)
    {K N : Subgroup (Perm Ω)} (hK : MulAction.IsMultiplyPretransitive K Ω 2)
    (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal) (hNne : N ≠ ⊥) :
    Nat.card Ω ≤ Nat.card N := by
  haveI : MulAction.IsPretransitive N Ω :=
    isPretransitive_of_normal_ne_bot hK hNK hN hNne
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩ]; norm_num)
  let x : Ω := Classical.arbitrary Ω
  have hx : (MulAction.stabilizer N x).index = Nat.card Ω :=
    MulAction.index_stabilizer_of_transitive N x
  have hdvd : Nat.card Ω ∣ Nat.card N := by
    rw [← hx]
    exact Subgroup.index_dvd_card _
  haveI : Nonempty N := ⟨⟨1, N.one_mem⟩⟩
  exact Nat.le_of_dvd Nat.card_pos hdvd

private theorem normal_centerOf {Q K : Subgroup (Perm Ω)} (hQK : Q ≤ K)
    (hQ : (Q.subgroupOf K).Normal) : ((centerOf Q).subgroupOf K).Normal := by
  change ((Q ⊓ Subgroup.centralizer (Q : Set (Perm Ω))).subgroupOf K).Normal
  rw [Subgroup.normal_subgroupOf_iff (inf_le_left.trans hQK)]
  intro z k hz hk
  obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hz
  refine ⟨(Subgroup.normal_subgroupOf_iff hQK).mp hQ z k hzQ hk, ?_⟩
  change k * z * k⁻¹ ∈ Subgroup.centralizer (Q : Set (Perm Ω))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : k⁻¹ * y * k ∈ Q :=
    (Subgroup.normal_subgroupOf_iff hQK).mp hQ y k⁻¹ hy (K.inv_mem hk)
  have hcomm : (k⁻¹ * y * k) * z = z * (k⁻¹ * y * k) :=
    (Subgroup.mem_centralizer_iff.mp hzC) _ hy'
  calc y * (k * z * k⁻¹) = k * ((k⁻¹ * y * k) * z) * k⁻¹ := by group
    _ = k * (z * (k⁻¹ * y * k)) * k⁻¹ := by rw [hcomm]
    _ = (k * z * k⁻¹) * y := by group

private theorem eq_one_of_mem_Q_of_smul_eq {Q Z : Subgroup (Perm Ω)} {x : Ω}
    (hZtrans : MulAction.IsPretransitive Z Ω)
    (hZc : Z ≤ Subgroup.centralizer (Q : Set (Perm Ω)))
    {q : Perm Ω} (hq : q ∈ Q) (hfix : q • x = x) : q = 1 := by
  have hcomm : ∀ w : Z, q * (w : Perm Ω) = (w : Perm Ω) * q := fun w =>
    (Subgroup.mem_centralizer_iff.mp (hZc w.2)) q hq
  have hfixall : ∀ y : Ω, q • y = y := by
    intro y
    obtain ⟨w, hw⟩ := MulAction.exists_smul_eq Z x y
    calc q • y = q • (w • x) := by rw [hw]
      _ = q • ((w : Perm Ω) • x) := by rw [MulAction.subgroup_smul_def]
      _ = (q * (w : Perm Ω)) • x := (mul_smul q (w : Perm Ω) x).symm
      _ = ((w : Perm Ω) * q) • x := by rw [hcomm w]
      _ = (w : Perm Ω) • (q • x) := mul_smul (w : Perm Ω) q x
      _ = (w : Perm Ω) • x := by rw [hfix]
      _ = w • x := by rw [MulAction.subgroup_smul_def]
      _ = y := hw
  exact Equiv.ext fun y => by simpa [Equiv.Perm.smul_def] using hfixall y

theorem isElemAbelian_of_isMultiplyPretransitive (hΩ : Fintype.card Ω = 8)
    {K Q : Subgroup (Perm Ω)} (hK : MulAction.IsMultiplyPretransitive K Ω 2) (hQK : Q ≤ K)
    (hQ : (Q.subgroupOf K).Normal) (hQ2 : IsPGroup 2 Q)
    (hCQ : K ⊓ Subgroup.centralizer (Q : Set (Perm Ω)) ≤ Q) :
    IsElemAbelian 2 Q ∧ Nat.card Q = 8 := by
  have hcardΩ : Nat.card Ω = 8 := by rw [Nat.card_eq_fintype_card, hΩ]
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    have hKbot : K = ⊥ := by
      have hCtop : Subgroup.centralizer (Q : Set (Perm Ω)) = ⊤ := by
        simp [hQbot]
      have hle : K ≤ (⊥ : Subgroup (Perm Ω)) := by
        calc K = K ⊓ ⊤ := (inf_top_eq K).symm
          _ = K ⊓ Subgroup.centralizer (Q : Set (Perm Ω)) := by rw [hCtop]
          _ ≤ Q := hCQ
          _ = ⊥ := hQbot
      exact le_bot_iff.mp hle
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp (by rw [hΩ]; norm_num)
    have hK2 := hK
    rw [MulAction.is_two_pretransitive_iff] at hK2
    obtain ⟨g, hgx, _⟩ := hK2 hxy (Ne.symm hxy)
    have hg1 : (g : Perm Ω) = 1 := by
      have : (g : Perm Ω) ∈ (⊥ : Subgroup (Perm Ω)) := hKbot ▸ g.2
      exact Subgroup.mem_bot.mp this
    have hgx' : (g : Perm Ω) • x = y := by
      rw [← MulAction.subgroup_smul_def]
      exact hgx
    rw [hg1, one_smul] at hgx'
    exact hxy hgx'
  let Z : Subgroup (Perm Ω) := centerOf Q
  have hZQ : Z ≤ Q := inf_le_left
  have hZK : Z ≤ K := hZQ.trans hQK
  have hZc : Z ≤ Subgroup.centralizer (Q : Set (Perm Ω)) := inf_le_right
  have hZnorm : (Z.subgroupOf K).Normal := normal_centerOf hQK hQ
  have hZne : Z ≠ ⊥ := by
    haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
    haveI : Nontrivial (Subgroup.center Q) := hQ2.center_nontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : Subgroup.center Q)
    have hmem : ((a : Q) : Perm Ω) ∈ Z := by
      refine Subgroup.mem_inf.mpr ⟨(a : Q).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext_iff.mp ((Subgroup.mem_center_iff.mp a.2) ⟨y, hy⟩)
    have hne : ((a : Q) : Perm Ω) ≠ 1 := by
      intro h1
      exact ha (Subtype.ext (Subtype.ext h1))
    intro hbot
    rw [hbot] at hmem
    exact hne (Subgroup.mem_bot.mp hmem)
  have hZtrans : MulAction.IsPretransitive Z Ω :=
    isPretransitive_of_normal_ne_bot hK hZK hZnorm hZne
  haveI := hZtrans
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩ]; norm_num)
  let x : Ω := Classical.arbitrary Ω
  have hstabZ : MulAction.stabilizer Z x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzfix : z • x = x := MulAction.mem_stabilizer_iff.mp hz
    have hzQ : (z : Perm Ω) ∈ Q := (Subgroup.mem_inf.mp z.2).1
    have hzfix' : (z : Perm Ω) • x = x := by
      rwa [← MulAction.subgroup_smul_def]
    exact Subtype.ext (eq_one_of_mem_Q_of_smul_eq hZtrans hZc hzQ hzfix')
  have hZcard : Nat.card Z = 8 := by
    have hx : (MulAction.stabilizer Z x).index = Nat.card Ω :=
      MulAction.index_stabilizer_of_transitive Z x
    rw [hstabZ, Subgroup.index_bot] at hx
    exact hx.trans hcardΩ
  have hinj : Function.Injective (fun q : Q => q • x) := by
    intro q q' h
    change q • x = q' • x at h
    have h1 : (q⁻¹ * q') • x = x := by
      rw [mul_smul, ← h]
      rw [← mul_smul, inv_mul_cancel, one_smul]
    have hfix' : ((q⁻¹ * q' : Q) : Perm Ω) • x = x := by
      rwa [← MulAction.subgroup_smul_def]
    have h2 : ((q⁻¹ * q' : Q) : Perm Ω) = 1 :=
      eq_one_of_mem_Q_of_smul_eq hZtrans hZc (q⁻¹ * q').2 hfix'
    exact inv_mul_eq_one.mp (Subtype.ext h2)
  have hcardQ_le : Nat.card Q ≤ 8 := by
    have hle := Nat.card_le_card_of_injective (fun q : Q => q • x) hinj
    rwa [hcardΩ] at hle
  have hZQeq : Z = Q := by
    refine Subgroup.eq_of_le_of_card_ge (H := Z) (K := Q) hZQ ?_
    rw [hZcard]
    exact hcardQ_le
  have hQcard : Nat.card Q = 8 := by rw [← hZQeq, hZcard]
  have hQcomm : IsMulCommutative Q :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      ((le_of_eq hZQeq.symm).trans hZc)
  have hQfcard : Nat.card Q = 8 := hQcard
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (G := Q) (by rw [hQfcard]; norm_num)
  have hg2 : g ^ 2 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hgne : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    omega
  let sq : Q →* Q :=
    { toFun := fun q => q ^ 2
      map_one' := by simp
      map_mul' := fun a b => by
        have h : Commute a b := isMulCommutative_iff.mp hQcomm a b
        exact h.mul_pow 2 }
  let Φ : Subgroup (Perm Ω) := sq.range.map Q.subtype
  have hΦK : Φ ≤ K := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.mp hy
    exact hQK z.2
  have hΦnorm : (Φ.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΦK]
    intro y k hy hk
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hz
    have hq' : k * (q : Perm Ω) * k⁻¹ ∈ Q :=
      (Subgroup.normal_subgroupOf_iff hQK).mp hQ (q : Perm Ω) k q.2 hk
    refine Subgroup.mem_map.mpr ⟨sq ⟨k * (q : Perm Ω) * k⁻¹, hq'⟩,
      MonoidHom.mem_range.mpr ⟨⟨k * (q : Perm Ω) * k⁻¹, hq'⟩, rfl⟩, ?_⟩
    show ((k * (q : Perm Ω) * k⁻¹) ^ 2 : Perm Ω) = k * (q : Perm Ω) ^ 2 * k⁻¹
    rw [pow_two, pow_two]
    group
  have hΦ4 : Nat.card Φ ≤ 4 := by
    have hgker : g ∈ sq.ker := by
      rw [MonoidHom.mem_ker]
      exact hg2
    have hker_ne : sq.ker ≠ ⊥ := by
      intro hbot
      have : g ∈ (⊥ : Subgroup Q) := hbot ▸ hgker
      exact hgne (Subgroup.mem_bot.mp this)
    have hker2 : 2 ≤ Nat.card sq.ker := by
      have := (Subgroup.one_lt_card_iff_ne_bot (H := sq.ker)).mpr hker_ne
      omega
    have hcardker := Subgroup.card_ker_mul_card_range sq
    have hrange4 : Nat.card sq.range ≤ 4 := by
      have h2 : 2 * Nat.card sq.range ≤ Nat.card sq.ker * Nat.card sq.range :=
        Nat.mul_le_mul_right _ hker2
      rw [hcardker, hQcard] at h2
      omega
    have hmap := Subgroup.card_map_of_injective (K := sq.range) Q.subtype_injective
    show Nat.card (sq.range.map Q.subtype) ≤ 4
    rw [hmap]
    exact hrange4
  have hexp : ∀ y ∈ Q, y ^ 2 = 1 := by
    intro y hy
    by_cases hΦbot : Φ = ⊥
    · have hyΦ : y ^ 2 ∈ Φ := by
        refine Subgroup.mem_map.mpr ⟨sq ⟨y, hy⟩,
          MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩, ?_⟩
        rfl
      rw [hΦbot] at hyΦ
      exact Subgroup.mem_bot.mp hyΦ
    · exfalso
      have h8le : 8 ≤ Nat.card Φ := by
        have h := card_le_card_of_normal_ne_bot hΩ hK hΦK hΦnorm hΦbot
        rwa [hcardΩ] at h
      omega
  exact ⟨⟨hQcomm, hexp⟩, hQcard⟩

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
