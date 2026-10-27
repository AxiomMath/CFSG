module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Package
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec4.Item434Kit

private theorem mul_comm_of_mem {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}
    {B₂ : Subgroup G} (hB₂ : B2Package b z B₂) {x y : G} (hx : x ∈ B₂) (hy : y ∈ B₂) :
    x * y = y * x := by
  exact congrArg Subtype.val (hB₂.abel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem bpow_comm_mem {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G}
    (hB₂ : B2Package b z B₂) (m : ℕ) {x : G} (hx : x ∈ B₂) :
    b ^ m * x * (b ^ m)⁻¹ * x⁻¹ ∈ bOne z := by
  have hS := h.settingCore
  induction m with
  | zero => simp
  | succ m ih =>
    have hid : b ^ (m + 1) * x * (b ^ (m + 1))⁻¹ * x⁻¹ =
        b * (b ^ m * x * (b ^ m)⁻¹ * x⁻¹) * b⁻¹ * (b * x * b⁻¹ * x⁻¹) := by
      rw [pow_succ']
      group
    rw [hid]
    have hc : b * (b ^ m * x * (b ^ m)⁻¹ * x⁻¹) * b⁻¹ ∈ bOne z := by
      have hcomm : (b ^ m * x * (b ^ m)⁻¹ * x⁻¹) * b =
          b * (b ^ m * x * (b ^ m)⁻¹ * x⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hS.tor_le_cen ih)
      rwa [show b * (b ^ m * x * (b ^ m)⁻¹ * x⁻¹) * b⁻¹ =
        (b ^ m * x * (b ^ m)⁻¹ * x⁻¹) from by rw [← hcomm]; group]
    exact (bOne z).mul_mem hc (hB₂.comm x hx)

private theorem bzpow_comm_mem {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G}
    (hB₂ : B2Package b z B₂) (i : ℤ) {x : G} (hx : x ∈ B₂) :
    b ^ i * x * (b ^ i)⁻¹ * x⁻¹ ∈ bOne z := by
  have hS := h.settingCore
  have hmod : b ^ i = b ^ (i % 3).toNat := by
    rw [← zpow_mod_orderOf b i, hS.ord]
    rw [← zpow_natCast]
    congr 1
    exact (Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))).symm
  rw [hmod]
  exact bpow_comm_mem h hB₂ (i % 3).toNat hx

private theorem commMap_mul {G : Type} [Group G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}
    {B₂ : Subgroup G} (hB₂ : B2Package b z B₂) {g x y : G}
    (hxy : x * y = y * x) (hgy : g * y * g⁻¹ ∈ B₂) (hx : x ∈ B₂) :
    g * (x * y) * g⁻¹ * (x * y)⁻¹ =
      (g * x * g⁻¹ * x⁻¹) * (g * y * g⁻¹ * y⁻¹) := by
  have hvb : x⁻¹ * (g * y * g⁻¹) = (g * y * g⁻¹) * x⁻¹ :=
    mul_comm_of_mem hB₂ (B₂.inv_mem hx) hgy
  have hwi : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by rw [← mul_inv_rev, hxy, mul_inv_rev]
  calc g * (x * y) * g⁻¹ * (x * y)⁻¹
      = g * (x * y) * g⁻¹ * (y⁻¹ * x⁻¹) := by rw [mul_inv_rev]
    _ = g * (x * y) * g⁻¹ * (x⁻¹ * y⁻¹) := by rw [hwi]
    _ = g * x * g⁻¹ * ((g * y * g⁻¹) * x⁻¹) * y⁻¹ := by group
    _ = g * x * g⁻¹ * (x⁻¹ * (g * y * g⁻¹)) * y⁻¹ := by rw [← hvb]
    _ = (g * x * g⁻¹ * x⁻¹) * (g * y * g⁻¹ * y⁻¹) := by group

private theorem c_mem_normalizer_bOne {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {z : Fin 3 → ↥L} {τ c : G} (hτc : TauC z τ c) :
    c ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
  apply GGFF.mem_nor_of_closure (S := Set.range (GGFF.zs z))
  rintro s ⟨i, rfl⟩
  fin_cases i
  · show c * GGFF.zs z 0 * c⁻¹ ∈ Subgroup.closure (Set.range (GGFF.zs z))
    rw [hτc.cyc₀]; exact Subgroup.subset_closure ⟨1, rfl⟩
  · show c * GGFF.zs z 1 * c⁻¹ ∈ Subgroup.closure (Set.range (GGFF.zs z))
    rw [hτc.cyc₁]; exact Subgroup.subset_closure ⟨2, rfl⟩
  · show c * GGFF.zs z 2 * c⁻¹ ∈ Subgroup.closure (Set.range (GGFF.zs z))
    rw [hτc.cyc₂]; exact Subgroup.subset_closure ⟨0, rfl⟩

private theorem c_nor_B2 {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} {B₂ : Subgroup G} {τ c : G} (hB₂ : B2Package b z B₂)
    (hτc : TauC z τ c) : ∀ x ∈ B₂, c * x * c⁻¹ ∈ B₂ :=
  hB₂.D_nor c ⟨hτc.c_mem, c_mem_normalizer_bOne hτc⟩

private theorem zpowers_b_le_nor_B2 {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} {B₂ : Subgroup G} (hB₂ : B2Package b z B₂) :
    Subgroup.zpowers b ≤ Subgroup.normalizer (B₂ : Set G) :=
  Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype hB₂.b_nor)

private theorem zpowers_c_le_nor_B2 {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} {B₂ : Subgroup G} {τ c : G} (hB₂ : B2Package b z B₂)
    (hτc : TauC z τ c) :
    Subgroup.zpowers c ≤ Subgroup.normalizer (B₂ : Set G) :=
  Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype (c_nor_B2 hB₂ hτc))

private theorem Q_le_nor_B2 {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} {B₂ : Subgroup G} {τ c : G} (hB₂ : B2Package b z B₂)
    (hτc : TauC z τ c) :
    Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (B₂ : Set G) :=
  sup_le (zpowers_b_le_nor_B2 hB₂) (zpowers_c_le_nor_B2 hB₂ hτc)

private theorem q_nor_B2 {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} {B₂ : Subgroup G} {τ c : G} (hB₂ : B2Package b z B₂)
    (hτc : TauC z τ c) {q : G} (hq : q ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c) :
    ∀ x ∈ B₂, q * x * q⁻¹ ∈ B₂ := fun x hx =>
  (Subgroup.mem_normalizer_iff.mp (Q_le_nor_B2 hB₂ hτc hq) x).mp hx

private theorem decomp_sup {G : Type} [Group G] [Finite G] {b c q : G} (hbc : Commute b c)
    (hq : q ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c) :
    ∃ i j : ℤ, q = b ^ i * c ^ j := by
  have hle : Subgroup.zpowers b ≤
      Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute (c ^ k) b := (hbc.symm).zpow_left k
    rw [show b * c ^ k * b⁻¹ = c ^ k from by rw [← hcomm.eq]; group]
    exact Subgroup.zpow_mem_zpowers c k
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul] at hq
  obtain ⟨x, hx, y, hy, hxy⟩ := hq
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ⟨i, j, hxy.symm⟩

private theorem wreathFacts_c {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {τ c : G} (hτc : TauC z τ c) :
    WreathFacts (GGFF.zs z) c := by
  have hS := h.settingCore
  have hvinj : Function.Injective (vecElt (GGFF.zs z)) :=
    GGFF.vecElt_injective hS.zs_pow hS.zs_comm hS.inj'
  have hz01 : GGFF.zs z 0 ≠ GGFF.zs z 1 := by
    intro h01
    have hmem : vecElt (GGFF.zs z) (Pi.single 0 1) = vecElt (GGFF.zs z) (Pi.single 1 1) := by
      rw [vecElt_single_one, vecElt_single_one, h01]
    have heq := hvinj hmem
    have h0 := congrFun heq 0
    simp at h0
  refine
    { pow_z := hS.zs_pow
      comm_z := hS.zs_comm
      inj := hS.inj'
      pow_t := hτc.c_cube
      conj0 := hτc.cyc₀
      conj1 := hτc.cyc₁
      conj2 := hτc.cyc₂
      t_ne := ?_ }
  intro v hv
  have hc_notin : c ∉ GGFF.tor (GGFF.zs z) := by
    intro hc
    have hccomm : c * GGFF.zs z 0 = GGFF.zs z 0 * c := by
      exact congrArg Subtype.val
        (((GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).1.is_comm).comm
          (⟨c, hc⟩ : ↥(GGFF.tor (GGFF.zs z)))
          ⟨GGFF.zs z 0, Subgroup.subset_closure ⟨0, rfl⟩⟩)
    have h10 : GGFF.zs z 1 = GGFF.zs z 0 := by
      rw [← hτc.cyc₀, hccomm]
      group
    exact hz01 h10.symm
  exact hc_notin (hv ▸ GGFF.vecElt_mem_tor (GGFF.zs z) v)

private theorem mem_zpowers_w_of_commute {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {τ c : G}
    (hτc : TauC z τ c) {y : G} (hy : y ∈ bOne z) (hcomm : y * c = c * y) :
    y ∈ Subgroup.zpowers (vecElt (GGFF.zs z) ![1, 1, 1]) := by
  have hS := h.settingCore
  have hf := wreathFacts_c h hτc
  obtain ⟨v, rfl⟩ := hS.mem_torG.mp hy
  have hcomm' : vecElt (GGFF.zs z) v * c ^ (1 : ℕ) = c ^ (1 : ℕ) * vecElt (GGFF.zs z) v := by
    simpa using hcomm
  have hconst := eq_of_commute hf (j := 1) (by decide) hcomm'
  exact vecElt_mem_zpowers_of_const hf hconst.1 hconst.2

private theorem centralizer_c_bound {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {τ c : G}
    (hτc : TauC z τ c) :
    Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({c} : Set G)) ≤ 3 := by
  have hS := h.settingCore
  have hle : bOne z ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.zpowers (vecElt (GGFF.zs z) ![1, 1, 1]) := by
    rintro y ⟨hyB, hyC⟩
    exact mem_zpowers_w_of_commute h hτc hyB (Subgroup.mem_centralizer_singleton_iff.mp hyC)
  have hw3 : (vecElt (GGFF.zs z) ![1, 1, 1]) ^ 3 = 1 :=
    (GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).2 _
      (GGFF.vecElt_mem_tor (GGFF.zs z) ![1, 1, 1])
  have hcard_w : Nat.card ↥(Subgroup.zpowers (vecElt (GGFF.zs z) ![1, 1, 1])) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hw3
  exact (Subgroup.card_le_of_le hle).trans hcard_w

private theorem centralizer_cinv_eq {G : Type} [Group G] {c : G} :
    Subgroup.centralizer ({c⁻¹} : Set G) = Subgroup.centralizer ({c} : Set G) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hcy : c * y = y * c := by
      calc c * y = c * (y * c⁻¹) * c := by group
        _ = c * (c⁻¹ * y) * c := by rw [h]
        _ = y * c := by group
    exact hcy.symm
  · intro h
    have hcy : c⁻¹ * y = y * c⁻¹ := by
      calc c⁻¹ * y = c⁻¹ * (y * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * y) * c⁻¹ := by rw [h]
        _ = y * c⁻¹ := by group
    exact hcy.symm

private theorem centralizer_cpow_bound {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {τ c : G}
    (hτc : TauC z τ c) {j : ℤ} (hj : c ^ j ≠ 1) :
    Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({c ^ j} : Set G)) ≤ 3 := by
  have hc_ne : c ≠ 1 := by intro hc; exact hj (by rw [hc, one_zpow])
  have hord : orderOf c = 3 := orderOf_eq_prime hτc.c_cube hc_ne
  rcases GGFF.eq_or_eq_inv_of_mem_zpowers (b := c) (x := c ^ j) hord
      (Subgroup.zpow_mem_zpowers c j) hj with hd | hd
  · rw [hd]; exact centralizer_c_bound h hτc
  · rw [hd, centralizer_cinv_eq]; exact centralizer_c_bound h hτc

private theorem key_bound {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hτc : TauC z τ c) {q : G}
    (hq : q ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c)
    (hqnb : q ∉ Subgroup.zpowers b) :
    Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) ≤ 3 ^ 2 := by
  have hS := h.settingCore
  have hbc : Commute b c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hτc.c_mem)).symm
  obtain ⟨i, j, hqij⟩ := decomp_sup hbc hq
  have hcj_ne : c ^ j ≠ 1 := by
    intro hcj
    apply hqnb
    rw [hqij, hcj, mul_one]
    exact Subgroup.zpow_mem_zpowers b i
  have hbOne_bound : Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({q} : Set G)) ≤ 3 := by
    have hsub : bOne z ⊓ Subgroup.centralizer ({q} : Set G) ≤
        bOne z ⊓ Subgroup.centralizer ({c ^ j} : Set G) := by
      rintro y ⟨hyB, hyC⟩
      refine ⟨hyB, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hyq : y * q = q * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hybi : y * b ^ i = b ^ i * y :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hS.tor_le_cen hyB)) i).eq
      have h1 : y * q = b ^ i * (y * c ^ j) := by rw [hqij, ← mul_assoc, hybi]; group
      have h2 : q * y = b ^ i * (c ^ j * y) := by rw [hqij]; group
      rw [h1, h2] at hyq
      exact mul_left_cancel hyq
    exact (Subgroup.card_le_of_le hsub).trans (centralizer_cpow_bound h hτc hcj_ne)
  let C : Subgroup G := B₂ ⊓ Subgroup.centralizer ({q} : Set G)
  let Φ : ↥C →* ↥(bOne z) :=
    { toFun := fun v => ⟨b * (v : G) * b⁻¹ * (v : G)⁻¹, hB₂.comm (v : G) v.2.1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun v w => Subtype.ext
        (commMap_mul hB₂ (mul_comm_of_mem hB₂ v.2.1 w.2.1)
          (hB₂.b_nor (w : G) w.2.1) v.2.1) }
  have hker_bound : Nat.card ↥Φ.ker ≤ 3 := by
    have hle : (Φ.ker).map C.subtype ≤ bOne z ⊓ Subgroup.centralizer ({q} : Set G) := by
      rintro x ⟨v, hv, rfl⟩
      have h1 : Φ v = 1 := MonoidHom.mem_ker.mp hv
      have h2 : b * (v : G) * b⁻¹ * (v : G)⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : b * (v : G) * b⁻¹ = (v : G) := mul_inv_eq_one.mp h2
      have hcomm : (v : G) * b = b * (v : G) := by
        calc (v : G) * b = (b * (v : G) * b⁻¹) * b := by rw [h3]
          _ = b * (v : G) := by group
      exact ⟨hB₂.fix _ v.2.1 hcomm, v.2.2⟩
    have hcard : Nat.card ↥((Φ.ker).map C.subtype) = Nat.card ↥Φ.ker :=
      Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective
    calc Nat.card ↥Φ.ker = Nat.card ↥((Φ.ker).map C.subtype) := hcard.symm
      _ ≤ Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({q} : Set G)) :=
            Subgroup.card_le_of_le hle
      _ ≤ 3 := hbOne_bound
  have hrange_bound : Nat.card ↥Φ.range ≤ 3 := by
    have hle : (Φ.range).map (bOne z).subtype ≤
        bOne z ⊓ Subgroup.centralizer ({q} : Set G) := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hy
      have hyv : (y : G) = b * (v : G) * b⁻¹ * (v : G)⁻¹ :=
        (congrArg Subtype.val hv).symm
      have hqb : Commute b q := by
        rw [hqij]
        exact ((Commute.refl b).zpow_right i).mul_right (hbc.zpow_right j)
      have hqv : Commute q (v : G) :=
        (Subgroup.mem_centralizer_singleton_iff.mp v.2.2).symm
      have hqall : Commute q (b * (v : G) * b⁻¹ * (v : G)⁻¹) :=
        ((hqb.symm.mul_right hqv).mul_right hqb.symm.inv_right).mul_right hqv.inv_right
      refine ⟨y.2, ?_⟩
      show (y : G) ∈ Subgroup.centralizer ({q} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff, hyv]
      exact hqall.eq.symm
    have hcard : Nat.card ↥((Φ.range).map (bOne z).subtype) = Nat.card ↥Φ.range :=
      Subgroup.card_map_of_injective (f := (bOne z).subtype) (bOne z).subtype_injective
    calc Nat.card ↥Φ.range = Nat.card ↥((Φ.range).map (bOne z).subtype) := hcard.symm
      _ ≤ Nat.card ↥(bOne z ⊓ Subgroup.centralizer ({q} : Set G)) :=
            Subgroup.card_le_of_le hle
      _ ≤ 3 := hbOne_bound
  have hkr := Subgroup.card_ker_mul_card_range Φ
  calc Nat.card ↥C = Nat.card ↥Φ.ker * Nat.card ↥Φ.range := hkr.symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker_bound hrange_bound
    _ = 3 ^ 2 := by norm_num

theorem card_commutator_le_iff {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hτc : TauC z τ c) {q : G}
    (hq : q ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c) :
    Nat.card ↥(Subgroup.closure {r : G | ∃ x ∈ B₂, r = q * x * q⁻¹ * x⁻¹}) ≤ 3 ^ 3 ↔
      q ∈ Subgroup.zpowers b := by
  constructor
  · intro hcard
    by_contra hqnb
    let Ψ : ↥B₂ →* G :=
      { toFun := fun x => q * (x : G) * q⁻¹ * (x : G)⁻¹
        map_one' := by simp
        map_mul' := fun x y =>
          commMap_mul hB₂ (mul_comm_of_mem hB₂ x.2 y.2)
            (q_nor_B2 hB₂ hτc hq (y : G) y.2) x.2 }
    have hrange_eq : Ψ.range = Subgroup.closure {r : G | ∃ x ∈ B₂, r = q * x * q⁻¹ * x⁻¹} := by
      apply le_antisymm
      · rintro r ⟨x, rfl⟩
        exact Subgroup.subset_closure ⟨(x : G), x.2, rfl⟩
      · rw [Subgroup.closure_le]
        rintro r ⟨x, hx, rfl⟩
        exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
    have hker_le' : Nat.card ↥Ψ.ker ≤ 3 ^ 2 := by
      have hle : (Ψ.ker).map B₂.subtype ≤ B₂ ⊓ Subgroup.centralizer ({q} : Set G) := by
        rintro x ⟨v, hv, rfl⟩
        have h1 : q * (v : G) * q⁻¹ * (v : G)⁻¹ = 1 := MonoidHom.mem_ker.mp hv
        have h2 : q * (v : G) * q⁻¹ = (v : G) := mul_inv_eq_one.mp h1
        have hcomm : (v : G) * q = q * (v : G) := by
          calc (v : G) * q = (q * (v : G) * q⁻¹) * q := by rw [h2]
            _ = q * (v : G) := by group
        exact ⟨v.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
      have hcard : Nat.card ↥((Ψ.ker).map B₂.subtype) = Nat.card ↥Ψ.ker :=
        Subgroup.card_map_of_injective (f := B₂.subtype) B₂.subtype_injective
      calc Nat.card ↥Ψ.ker = Nat.card ↥((Ψ.ker).map B₂.subtype) := hcard.symm
        _ ≤ Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) := Subgroup.card_le_of_le hle
        _ ≤ 3 ^ 2 := key_bound h hB₂ hτc hq hqnb
    have hrange_le : Nat.card ↥Ψ.range ≤ 3 ^ 3 := by rw [hrange_eq]; exact hcard
    have hkr := Subgroup.card_ker_mul_card_range Ψ
    have hbad : ¬ (3 ^ 6 ≤ 3 ^ 2 * 3 ^ 3) := by norm_num
    exact hbad (by rw [← hB₂.card, ← hkr]; exact Nat.mul_le_mul hker_le' hrange_le)
  · intro hqb
    have hle : Subgroup.closure {r : G | ∃ x ∈ B₂, r = q * x * q⁻¹ * x⁻¹} ≤ bOne z := by
      rw [Subgroup.closure_le]
      rintro r ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hqb
      rw [← hi]
      exact bzpow_comm_mem h hB₂ i hx
    calc Nat.card ↥(Subgroup.closure {r : G | ∃ x ∈ B₂, r = q * x * q⁻¹ * x⁻¹})
        ≤ Nat.card ↥(bOne z) := Subgroup.card_le_of_le hle
      _ = 27 := h.settingCore.card_torG
      _ = 3 ^ 3 := by norm_num

theorem card_centralizer_le {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hτc : TauC z τ c) {q : G}
    (hq : q ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c) (hq1 : q ≠ 1) :
    Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) ≤ 3 ^ 3 := by
  by_cases hqb : q ∈ Subgroup.zpowers b
  · have hS := h.settingCore
    have hle : B₂ ⊓ Subgroup.centralizer ({q} : Set G) ≤ bOne z := by
      rintro y ⟨hyB, hyC⟩
      apply hB₂.fix y hyB
      have hyq : y * q = q * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      have hb_q : b ∈ Subgroup.zpowers q := by
        rcases GGFF.eq_or_eq_inv_of_mem_zpowers hS.ord hqb hq1 with hbq | hbq
        · rw [hbq]; exact Subgroup.mem_zpowers b
        · rw [hbq]; simp
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb_q
      rw [← hk]
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hyC) k).eq
    calc Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) ≤ Nat.card ↥(bOne z) :=
          Subgroup.card_le_of_le hle
      _ = 27 := hS.card_torG
      _ ≤ 3 ^ 3 := by norm_num
  · calc Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) ≤ 3 ^ 2 :=
          key_bound h hB₂ hτc hq hqb
      _ ≤ 3 ^ 3 := by norm_num

end CFSG.StandardType.FF81.PropOne

end
