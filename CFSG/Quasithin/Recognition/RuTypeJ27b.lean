module

public import CFSG.Quasithin.Recognition.RuTypeJ27a
public import CFSG.Quasithin.Recognition.RuTypeM10
public import CFSG.Quasithin.Background.I4Recognition

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

theorem ofAdd_one_pow_odd {n : ℕ} (hn : ¬ 2 ∣ n) :
    (Multiplicative.ofAdd (1 : ZMod 2)) ^ n = Multiplicative.ofAdd 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  rw [pow_succ, pow_mul, show (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 by decide, one_pow,
    one_mul]

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem fel_pow_four : M.fel ^ 4 = 1 := by
  rw [fel, ← map_pow, SD16C.f_pow_four, map_one]

theorem fel_pow_mem_SB_iff (k : ℕ) : M.fel ^ k ∈ M.SB ↔ k % 2 = 0 := by
  have h4 : M.fel ^ k = M.fel ^ (k % 4) := by
    conv_lhs => rw [← Nat.mod_add_div k 4, pow_add, pow_mul, M.fel_pow_four, one_pow, mul_one]
  rw [h4, fel, ← map_pow, M.κ_mem_SB_iff]
  have h := SD16C.f_pow_mem_SBC_iff ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩
  simp only at h
  rw [h]
  omega

theorem conj_fel_pow_mem_SB_iff {a : G} (haB : a ∈ M.GB) {k : ℕ}
    (h : a⁻¹ * M.fel ^ k * a ∈ M.TB) : a⁻¹ * M.fel ^ k * a ∈ M.SB ↔ k % 2 = 0 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have hfk : M.fel ^ (2 * m) = M.z ^ m := by rw [pow_mul, pow_two, M.fel_sq]
    constructor
    · intro _
      omega
    · intro _
      apply M.mem_SB_of_sq h
      rw [hfk]
      calc a⁻¹ * M.z ^ m * a * (a⁻¹ * M.z ^ m * a) = a⁻¹ * (M.z ^ m * M.z ^ m) * a := by group
        _ = 1 := by rw [← pow_add, ← two_mul, pow_mul, M.z_sq, one_pow]; group
  · constructor
    · intro hS
      exfalso
      have hff : M.fel ^ (2 * m + 1) * M.fel ^ (2 * m + 1) = M.z := by
        rw [← pow_add, show 2 * m + 1 + (2 * m + 1) = 4 * m + 2 by ring, pow_add, pow_mul,
          M.fel_pow_four, one_pow, one_mul, pow_two, M.fel_sq]
      have hy2 : a⁻¹ * M.fel ^ (2 * m + 1) * a * (a⁻¹ * M.fel ^ (2 * m + 1) * a) =
          a⁻¹ * M.z * a := by
        rw [← hff]
        group
      rcases M.sq_of_mem_SB hS with h1 | h1
      · rw [hy2] at h1
        apply M.z_ne_one
        calc M.z = a * (a⁻¹ * M.z * a) * a⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · rw [hy2] at h1
        have haH : a ∈ ruH M.T := by
          rw [M.mem_H_iff_comm]
          calc M.z * a = a * (a⁻¹ * M.z * a) := by group
            _ = a * M.z := by rw [h1]
        obtain ⟨t, ht, b, hb, rfl⟩ := M.CHB_eq_mul ⟨haH, haB⟩
        set w := t⁻¹ * M.fel ^ (2 * m + 1) * t
        have hwT : w ∈ M.TB := mul_mem (mul_mem (inv_mem ht) (pow_mem M.fel_mem_TB _)) ht
        have hbw : b * w = w * b := by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          have hc : Commute (M.bel : G) w := M.bel_comm_CHB (M.TB_le_CHB hwT)
          exact (hc.zpow_left n).eq
        have hyw : (t * b)⁻¹ * M.fel ^ (2 * m + 1) * (t * b) = w := by
          calc (t * b)⁻¹ * M.fel ^ (2 * m + 1) * (t * b) = b⁻¹ * (w * b) := by
                simp only [w]; group
            _ = b⁻¹ * (b * w) := by rw [hbw]
            _ = w := by group
        rw [hyw] at hS
        have hfS : M.fel ^ (2 * m + 1) ∈ M.SB := by
          have := M.conj_mem_SB ht hS
          rwa [show t * w * t⁻¹ = M.fel ^ (2 * m + 1) by simp only [w]; group] at this
        have := (M.fel_pow_mem_SB_iff _).mp hfS
        omega
    · intro hk
      omega

@[expose] noncomputable def TBequiv : SD16C ≃* M.TB :=
  (MonoidHom.ofInjective M.κ_injective).trans (MulEquiv.subgroupCongr M.κ_range)

theorem TBequiv_apply (p : SD16C) : ((M.TBequiv p : M.TB) : G) = M.κ p := rfl

@[expose] noncomputable def parT : M.TB →* Multiplicative (ZMod 2) :=
  SD16C.parity.comp M.TBequiv.symm.toMonoidHom

theorem parT_eq_one_iff (t : M.TB) : M.parT t = 1 ↔ (t : G) ∈ M.SB := by
  obtain ⟨p, rfl⟩ := M.TBequiv.surjective t
  show SD16C.parity (M.TBequiv.symm (M.TBequiv p)) = 1 ↔ _
  rw [MulEquiv.symm_apply_apply, SD16C.parity_eq_one_iff, TBequiv_apply, M.κ_mem_SB_iff]

theorem parT_eq_iff (s t : M.TB) :
    M.parT s = M.parT t ↔ ((s : G) ∈ M.SB ↔ (t : G) ∈ M.SB) := by
  rw [← M.parT_eq_one_iff, ← M.parT_eq_one_iff]
  generalize M.parT s = a
  generalize M.parT t = b
  revert a b
  decide

noncomputable abbrev TX : Subgroup M.GB := M.TB.subgroupOf M.GB

@[expose] noncomputable def parX : M.TX →* Multiplicative (ZMod 2) :=
  M.parT.comp (Subgroup.subgroupOfEquivOfLe M.TB_le_GB).toMonoidHom

theorem parX_eq_iff (s t : M.TX) :
    M.parX s = M.parX t ↔ (((s : M.GB) : G) ∈ M.SB ↔ ((t : M.GB) : G) ∈ M.SB) :=
  M.parT_eq_iff _ _

@[expose] noncomputable def Vtr : M.GB →* Multiplicative (ZMod 2) := MonoidHom.transfer M.parX

noncomputable abbrev fX : M.GB := ⟨M.fel, M.TB_le_GB M.fel_mem_TB⟩

noncomputable abbrev zX : M.GB := ⟨M.z, M.TB_le_GB (M.SB_le_TB M.z_mem_SB)⟩

theorem Vtr_fel : M.Vtr M.fX = Multiplicative.ofAdd 1 := by
  have h := transfer_eq_pow_of_forall M.parX (g := M.fX) (show M.fX ∈ M.TX from M.fel_mem_TB)
    (by
      intro k a ha
      refine (M.parX_eq_iff _ _).mpr ?_
      have ha' : (a : G)⁻¹ * M.fel ^ k * a ∈ M.TB := ha
      show (a : G)⁻¹ * M.fel ^ k * a ∈ M.SB ↔ M.fel ^ k ∈ M.SB
      rw [M.fel_pow_mem_SB_iff]
      exact M.conj_fel_pow_mem_SB_iff a.2 ha')
  refine h.trans ?_
  have hpf : M.parX ⟨M.fX, M.fel_mem_TB⟩ = Multiplicative.ofAdd 1 := by
    show M.parT ⟨M.fel, M.fel_mem_TB⟩ = _
    have e : (⟨M.fel, M.fel_mem_TB⟩ : M.TB) = M.TBequiv SD16C.f := Subtype.ext rfl
    rw [e]
    show SD16C.parity (M.TBequiv.symm (M.TBequiv SD16C.f)) = _
    rw [MulEquiv.symm_apply_apply, SD16C.parity_f]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (congrArg (fun y => y ^ M.TX.index) hpf).trans (ofAdd_one_pow_odd M.TBsyl.not_dvd_index)

theorem Vtr_z : M.Vtr M.zX = 1 := by
  have e : M.zX = M.fX * M.fX := Subtype.ext M.fel_sq.symm
  rw [e, map_mul, M.Vtr_fel]
  decide

theorem Vtr_of_sq {x : M.GB} (hx2 : x ^ 2 = 1) : M.Vtr x = 1 := by
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
  · have hx2' : (x : G) ^ 2 = 1 := by
      have := congrArg Subtype.val hx2
      simpa using this
    obtain ⟨g, hg, hgx⟩ := M.lemma_J27_9 x.2 hx2' (fun h => hx1 (Subtype.ext h))
    have e : x = ⟨g, hg⟩ * M.zX * ⟨g, hg⟩⁻¹ := Subtype.ext hgx.symm
    rw [e, map_mul, map_mul, map_inv, M.Vtr_z, mul_one]
    exact mul_inv_cancel _

noncomputable abbrev NX : Subgroup M.GB := M.Vtr.ker

theorem fX_not_mem_NX : M.fX ∉ M.NX := by
  rw [MonoidHom.mem_ker, M.Vtr_fel]
  decide

theorem NX_index : M.NX.index = 2 := by
  rw [Subgroup.index_ker]
  have hsurj : Function.Surjective M.Vtr := by
    intro y
    rcases (by decide : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1) y
      with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨_, M.Vtr_fel⟩
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

theorem mem_NX_of_sq {x : M.GB} (hx2 : x ^ 2 = 1) : x ∈ M.NX := M.Vtr_of_sq hx2

theorem pow_three_of_mem_B {b : G} (hb : b ∈ M.B) : b ^ 3 = 1 := by
  have h := Subgroup.orderOf_dvd_natCard M.B hb
  rw [M.card_B] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

theorem B_le_GB : M.B ≤ M.GB := M.B_le_CHB.trans M.CHB_le_GB

theorem mem_NX_of_mem_B {b : G} (hb : b ∈ M.B) : (⟨b, M.B_le_GB hb⟩ : M.GB) ∈ M.NX := by
  rw [MonoidHom.mem_ker]
  have h3 : (M.Vtr ⟨b, M.B_le_GB hb⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, M.B_le_GB hb⟩ : M.GB) ^ 3 = 1 := Subtype.ext (by
      simpa using M.pow_three_of_mem_B hb)
    rw [this, map_one]
  generalize M.Vtr ⟨b, M.B_le_GB hb⟩ = y at h3
  revert y
  decide

theorem mem_NX_of_mem_SB {s : G} (hs : s ∈ M.SB) :
    (⟨s, M.TB_le_GB (M.SB_le_TB hs)⟩ : M.GB) ∈ M.NX := by
  obtain ⟨a, b, ha, hb, ha2, hb2, rfl⟩ := M.SB_prod_inv hs
  have e : (⟨a * b, M.TB_le_GB (M.SB_le_TB hs)⟩ : M.GB) =
      ⟨a, M.TB_le_GB ha⟩ * ⟨b, M.TB_le_GB hb⟩ := rfl
  rw [e]
  refine mul_mem (M.mem_NX_of_sq (Subtype.ext ?_)) (M.mem_NX_of_sq (Subtype.ext ?_))
  · show a ^ 2 = 1
    rw [pow_two, ha2]
  · show b ^ 2 = 1
    rw [pow_two, hb2]

theorem mem_SB_of_mem_NX {t : G} (ht : t ∈ M.TB) (htN : (⟨t, M.TB_le_GB ht⟩ : M.GB) ∈ M.NX) :
    t ∈ M.SB := by
  by_contra htS
  have h1 := M.mul_fel_inv_mem_SB ht htS
  apply M.fX_not_mem_NX
  have h2 := M.mem_NX_of_mem_SB h1
  have e : M.fX = (⟨t * M.fel⁻¹, M.TB_le_GB (M.SB_le_TB h1)⟩ : M.GB)⁻¹ *
      ⟨t, M.TB_le_GB ht⟩ := Subtype.ext (by
    show M.fel = (t * M.fel⁻¹)⁻¹ * t
    group)
  rw [e]
  exact mul_mem (inv_mem h2) htN

theorem exists_NX_conj_z {x : M.GB} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ n ∈ M.NX, n * M.zX * n⁻¹ = x := by
  have hx2' : (x : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hx2
    simpa using this
  obtain ⟨g, hg, hgx⟩ := M.lemma_J27_9 x.2 hx2' (fun h => hx1 (Subtype.ext h))
  have hfz : M.fel * M.z = M.z * M.fel :=
    (M.Z_comm_H M.z_mem_Z (M.TB_le_CHB M.fel_mem_TB).1).symm
  by_cases hgN : (⟨g, hg⟩ : M.GB) ∈ M.NX
  · exact ⟨⟨g, hg⟩, hgN, Subtype.ext hgx⟩
  · refine ⟨⟨g, hg⟩ * M.fX⁻¹, ?_, Subtype.ext ?_⟩
    · exact (Subgroup.mul_mem_iff_of_index_two M.NX_index).mpr
        (iff_of_false hgN (fun h => M.fX_not_mem_NX (by simpa using inv_mem h)))
    · show g * M.fel⁻¹ * M.z * (g * M.fel⁻¹)⁻¹ = x
      calc g * M.fel⁻¹ * M.z * (g * M.fel⁻¹)⁻¹ = g * (M.fel⁻¹ * (M.z * M.fel)) * g⁻¹ := by
            group
        _ = g * (M.fel⁻¹ * (M.fel * M.z)) * g⁻¹ := by rw [hfz]
        _ = g * M.z * g⁻¹ := by group
        _ = x := hgx

instance BX_normal : (M.B.subgroupOf M.GB).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have e : ((g * x * g⁻¹ : M.GB) : G) = x := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [← (Subgroup.mem_centralizer_iff.mp g.2) x hx]
      group
    rw [e]
    exact hx⟩

abbrev XQ : Type := M.GB ⧸ M.B.subgroupOf M.GB

noncomputable abbrev NQ : Subgroup M.XQ := M.NX.map (QuotientGroup.mk' (M.B.subgroupOf M.GB))

instance NQ_normal : M.NQ.Normal :=
  Subgroup.Normal.map (MonoidHom.normal_ker _) _ (QuotientGroup.mk'_surjective _)

theorem BX_le_NX : M.B.subgroupOf M.GB ≤ M.NX := fun b hb => by
  have := M.mem_NX_of_mem_B (Subgroup.mem_subgroupOf.mp hb)
  exact this

theorem NQ_index : M.NQ.index = 2 :=
  (Subgroup.index_map_eq M.NX (QuotientGroup.mk'_surjective (M.B.subgroupOf M.GB))
    (by rw [QuotientGroup.ker_mk']; exact M.BX_le_NX)).trans M.NX_index

theorem exists_lift_sq {u : M.XQ} (hu : u ^ 2 = 1) :
    ∃ x : M.GB, x ^ 2 = 1 ∧ (x : M.XQ) = u := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
  have hy2 : y ^ 2 ∈ M.B.subgroupOf M.GB := by
    rw [← QuotientGroup.eq_one_iff]
    exact hu
  have hy6 : (y ^ 2) ^ 3 = 1 := Subtype.ext (by
    simpa using M.pow_three_of_mem_B (Subgroup.mem_subgroupOf.mp hy2))
  refine ⟨y ^ 3, ?_, ?_⟩
  · rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hy6]
  · rw [QuotientGroup.mk_pow, pow_succ, hu, one_mul]

theorem mem_NQ_of_sq {u : M.XQ} (hu : u ^ 2 = 1) : u ∈ M.NQ := by
  obtain ⟨x, hx2, rfl⟩ := M.exists_lift_sq hu
  exact ⟨x, M.mem_NX_of_sq hx2, rfl⟩

theorem z_not_mem_B : M.z ∉ M.B := by
  intro h
  have h3 := M.pow_three_of_mem_B h
  apply M.z_ne_one
  calc M.z = M.z ^ 3 * (M.z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, M.z_sq]; group

noncomputable abbrev zQ : M.NQ :=
  ⟨(M.zX : M.XQ), ⟨M.zX, M.mem_NX_of_sq (Subtype.ext (by simpa using M.z_sq)), rfl⟩⟩

theorem orderOf_zQ : orderOf M.zQ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (Subtype.ext ?_) ?_
  · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show ((M.zX : M.GB) : M.XQ) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have : ((M.zX ^ 2 : M.GB) : G) = 1 := by simpa using M.z_sq
    rw [this]
    exact one_mem _
  · intro h
    apply M.z_not_mem_B
    have h1 : ((M.zX : M.GB) : M.XQ) = 1 := congrArg Subtype.val h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1

theorem isConj_zQ {u : M.NQ} (hu : orderOf u = 2) : IsConj M.zQ u := by
  have hu2 : (u : M.XQ) ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa using congrArg Subtype.val this
  obtain ⟨x, hx2, hxu⟩ := M.exists_lift_sq hu2
  have hx1 : x ≠ 1 := by
    rintro rfl
    have : u = 1 := Subtype.ext (by rw [← hxu]; simp)
    rw [this, orderOf_one] at hu
    norm_num at hu
  obtain ⟨n, hn, hnx⟩ := M.exists_NX_conj_z hx2 hx1
  refine isConj_iff.mpr ⟨⟨(n : M.XQ), ⟨n, hn, rfl⟩⟩, Subtype.ext ?_⟩
  show (n : M.XQ) * (M.zX : M.XQ) * (n : M.XQ)⁻¹ = u
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hnx, hxu]

theorem nonempty_centralizer_zQ :
    Nonempty (Subgroup.centralizer ({M.zQ} : Set M.NQ) ≃* DihedralGroup 4) := by
  classical
  have hmemN : ∀ s : M.SB, (⟨s, M.TB_le_GB (M.SB_le_TB s.2)⟩ : M.GB) ∈ M.NX :=
    fun s => M.mem_NX_of_mem_SB s.2
  let ψ0 : M.SB →* M.NQ :=
    { toFun := fun s => ⟨((⟨s, M.TB_le_GB (M.SB_le_TB s.2)⟩ : M.GB) : M.XQ), ⟨_, hmemN s, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψc : ∀ s : M.SB, ψ0 s ∈ Subgroup.centralizer ({M.zQ} : Set M.NQ) := by
    intro s
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show ((⟨s, _⟩ * M.zX : M.GB) : M.XQ) = ((M.zX * ⟨s, _⟩ : M.GB) : M.XQ)
    congr 1
    exact Subtype.ext ((M.Z_comm_H M.z_mem_Z (M.TB_le_CHB (M.SB_le_TB s.2)).1).symm)
  let ψ : M.SB →* Subgroup.centralizer ({M.zQ} : Set M.NQ) := ψ0.codRestrict _ hψc
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h1 : ((⟨s, M.TB_le_GB (M.SB_le_TB s.2)⟩ : M.GB) : M.XQ) = 1 :=
      congrArg (fun c : Subgroup.centralizer ({M.zQ} : Set M.NQ) => ((c : M.NQ) : M.XQ)) hs
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (M.TB_inf_B _ (M.SB_le_TB s.2) h1)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨⟨u, n, hn, rfl⟩, hc⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hc' : ((n * M.zX : M.GB) : M.XQ) = ((M.zX * n : M.GB) : M.XQ) := congrArg Subtype.val hc
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc'
    have hb : ((n : G) * M.z)⁻¹ * (M.z * n) ∈ M.B := hc'
    generalize hbdef : ((n : G) * M.z)⁻¹ * (M.z * n) = b at hb
    have hbz : b * M.z = M.z * b := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← hk]
      exact ((Commute.zpow_left (M.Z_comm_H M.z_mem_Z M.bel_mem_H).symm k)).eq
    have hnzn : (n : G)⁻¹ * M.z * n = M.z * b := by rw [← hbdef]; group
    have hb2 : b ^ 2 = 1 := by
      have h1 : ((n : G)⁻¹ * M.z * n) ^ 2 = 1 := by
        rw [pow_two]
        calc (n : G)⁻¹ * M.z * n * ((n : G)⁻¹ * M.z * n) = (n : G)⁻¹ * (M.z * M.z) * n := by
              group
          _ = 1 := by rw [M.z_mul_self]; group
      rw [hnzn] at h1
      have h2 : (M.z * b) ^ 2 = M.z ^ 2 * b ^ 2 := by
        rw [pow_two, pow_two, pow_two]
        calc M.z * b * (M.z * b) = M.z * (b * M.z) * b := by group
          _ = M.z * (M.z * b) * b := by rw [hbz]
          _ = M.z * M.z * (b * b) := by group
      rw [h2, M.z_sq, one_mul] at h1
      exact h1
    have hb1 : b = 1 := by
      calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
        _ = 1 := by rw [M.pow_three_of_mem_B hb, hb2]; group
    have hnz : M.z * n = (n : G) * M.z := by
      calc M.z * n = (n : G) * ((n : G)⁻¹ * M.z * n) := by group
        _ = (n : G) * M.z := by rw [hnzn, hb1, mul_one]
    have hnH : (n : G) ∈ ruH M.T := M.mem_H_iff_comm.mpr hnz
    obtain ⟨t, ht, b', hb', hnt⟩ := M.CHB_eq_mul ⟨hnH, n.2⟩
    have htN : (⟨t, M.TB_le_GB ht⟩ : M.GB) ∈ M.NX := by
      have e : (⟨t, M.TB_le_GB ht⟩ : M.GB) = n * (⟨b', M.B_le_GB hb'⟩ : M.GB)⁻¹ :=
        Subtype.ext (by
          show t = (n : G) * b'⁻¹
          rw [hnt]
          group)
      rw [e]
      exact mul_mem hn (inv_mem (M.mem_NX_of_mem_B hb'))
    have htS := M.mem_SB_of_mem_NX ht htN
    refine ⟨⟨t, htS⟩, Subtype.ext (Subtype.ext ?_)⟩
    show ((⟨t, _⟩ : M.GB) : M.XQ) = ((n : M.GB) : M.XQ)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show t⁻¹ * (n : G) ∈ M.B
    rw [hnt, show t⁻¹ * (t * b') = b' by group]
    exact hb'
  obtain ⟨e⟩ := M.nonempty_SB_dihedral
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm.trans e⟩

theorem lemma_J27_2
    :
    Nonempty ((↥M.GB ⧸ M.B.subgroupOf M.GB) ≃* A6Models.m10) := by
  have hinv : ∀ u v : M.NQ, orderOf u = 2 → orderOf v = 2 → IsConj u v :=
    fun u v hu hv => (M.isConj_zQ hu).symm.trans (M.isConj_zQ hv)
  have hinvX : ∀ x : M.XQ, x ^ 2 = 1 → x ∈ M.NQ := fun x hx => M.mem_NQ_of_sq hx
  rcases I4.lemma_I_4_1_two M.NQ hinv M.orderOf_zQ M.nonempty_centralizer_zQ with h | h
  · obtain ⟨e⟩ := h
    exact (false_of_psl32 M.NQ M.NQ_index hinvX e).elim
  · obtain ⟨e⟩ := h
    exact nonempty_mulEquiv_m10 M.NQ M.NQ_index hinvX e

end RuDataM

end CFSG.Quasithin.RuType
