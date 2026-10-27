module

public import CFSG.Quasithin.MS93.S5ACand
public import CFSG.Quasithin.MS93.S32Basic
public import CFSG.Quasithin.MS93.M15Lift

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {S : Subgroup G} {x : G} {p q : ℕ} (hpq : Nat.Coprime p q)
    (hp : x ^ p ∈ S) (hq : x ^ q ∈ S) : x ∈ S := by
  have h := Nat.gcd_eq_gcd_ab p q
  rw [hpq.gcd_eq_one, Nat.cast_one] at h
  have e : x = (x ^ p) ^ (Nat.gcdA p q) * (x ^ q) ^ (Nat.gcdB p q) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact S.mul_mem (S.zpow_mem hp _) (S.zpow_mem hq _)

theorem mem_L_of_odd (h : PUHyp M T L) {m : G} (hm : m ∈ M) {n : ℕ} (hn : Odd n)
    (hmn : m ^ n = 1) : m ∈ L := by
  obtain ⟨e, he⟩ := h.exists_pow_mem_L hm
  have hcop : Nat.Coprime (2 ^ e) n := Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hn)
  exact mem_of_pow_mem_of_coprime hcop he (by rw [hmn]; exact L.one_mem)

theorem mem_of_two_odd {S : Subgroup G} {x : G}
    (h2 : ∀ y : G, (∃ e : ℕ, y ^ 2 ^ e = 1) → y ∈ Subgroup.zpowers x → y ∈ S)
    (hodd : ∀ y : G, (∃ n : ℕ, Odd n ∧ y ^ n = 1) → y ∈ Subgroup.zpowers x → y ∈ S) :
    x ∈ S := by
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have h1 : x ^ m ∈ S := h2 _ ⟨e, by rw [← pow_mul, mul_comm, ← he, pow_orderOf_eq_one]⟩
    (Subgroup.npow_mem_zpowers x m)
  have h3 : x ^ 2 ^ e ∈ S := hodd _ ⟨m, hm, by rw [← pow_mul, ← he, pow_orderOf_eq_one]⟩
    (Subgroup.npow_mem_zpowers x _)
  have hcop : Nat.Coprime m (2 ^ e) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hm)
  exact mem_of_pow_mem_of_coprime hcop h1 h3

namespace IsSp4Data

variable (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
include hd h

theorem mem_pCoreOf_of_mem_kerG {t : G} (ht : t ∈ kerG a) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1) :
    t ∈ pCoreOf 2 M := by
  refine h.mem_pCoreOf_of_rel (le_normalizer_kerG a) (hd.not_le_kerG h) (kerG_le a ht) ht2
    fun l hl => ?_
  have hl' : l * t⁻¹ * l⁻¹ ∈ kerG a :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_kerG a (h.L_le hl)) _).1
      ((kerG a).inv_mem ht)
  rw [commutatorElement_def]
  have e : t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) := by group
  rw [e]
  exact (kerG a).mul_mem ht hl'

theorem commutator_kerG_le : ⁅kerG a, L⁆ ≤ pCoreOf 2 L :=
  h.commutator_le_pCoreOf_of_not_le (kerG_le a) (le_normalizer_kerG a) (hd.not_le_kerG h)

theorem commutator_Z0q_kerG_le :
    ⁅Z0q M T, kerG a⁆ ≤ Subgroup.centralizer (L : Set G) := by
  have hU : kerG a ≤ Subgroup.centralizer (Uq M T L : Set G) :=
    Sp4L.kerM_le_centralizer h hd.nat
  have h1 : ⁅⁅kerG a, L⁆, Z0q M T⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (h.commutator_le_pCoreOf_M (kerG_le a) (le_normalizer_kerG a)
      (hd.not_le_kerG h)).trans h.pCoreOf_le_centralizer_Z0q
  have h2 : ⁅⁅L, Z0q M T⁆, kerG a⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (Subgroup.mem_centralizer_iff.1 (hU hn) u hu).symm
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at h3

theorem kerG_le_centralizer_Z0q : kerG a ≤ Subgroup.centralizer (Z0q M T : Set G) := by
  intro x hx
  refine mem_of_two_odd (S := Subgroup.centralizer (Z0q M T : Set G)) (fun y hy2 hyx => ?_)
    (fun y ⟨n, hn, hyn⟩ hyx => ?_)
  · have hyN : y ∈ kerG a := Subgroup.zpowers_le.2 hx hyx
    exact h.pCoreOf_le_centralizer_Z0q (hd.mem_pCoreOf_of_mem_kerG h hyN hy2)
  · have hyN : y ∈ kerG a := Subgroup.zpowers_le.2 hx hyx
    have hyL : y ∈ L := mem_L_of_odd h (kerG_le a hyN) hn hyn
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    set c := ⁅z, y⁆ with hc
    have hcL : c ∈ Subgroup.centralizer (L : Set G) :=
      hd.commutator_Z0q_kerG_le h (Subgroup.commutator_mem_commutator hz hyN)
    have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.1 hcL y hyL
    have hcZ : c ∈ Z0q M T := by
      have hyz : y * z⁻¹ * y⁻¹ ∈ Z0q M T :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_Z0q M T (kerG_le a hyN)) _).1
          ((Z0q M T).inv_mem hz)
      rw [hc, commutatorElement_def]
      have e : z * y * z⁻¹ * y⁻¹ = z * (y * z⁻¹ * y⁻¹) := by group
      rw [e]
      exact (Z0q M T).mul_mem hz hyz
    have hc2 : c * c = 1 := by
      have := (h.isElemAbelian_Z0q).2 c hcZ
      simpa [pow_two] using this
    have e1 : y * z * y⁻¹ = c⁻¹ * z := by
      rw [hc, commutatorElement_def]
      group
    have hconj : ∀ j : ℕ, y ^ j * z * y⁻¹ ^ j = c⁻¹ ^ j * z := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hcy' : Commute y (c⁻¹ ^ j) := ((Commute.inv_right hcy).pow_right j)
        calc y ^ (j + 1) * z * y⁻¹ ^ (j + 1) = y * (y ^ j * z * y⁻¹ ^ j) * y⁻¹ := by group
          _ = y * (c⁻¹ ^ j * z) * y⁻¹ := by rw [ih]
          _ = (y * c⁻¹ ^ j) * z * y⁻¹ := by group
          _ = (c⁻¹ ^ j * y) * z * y⁻¹ := by rw [hcy'.eq]
          _ = c⁻¹ ^ j * (y * z * y⁻¹) := by group
          _ = c⁻¹ ^ j * (c⁻¹ * z) := by rw [e1]
          _ = c⁻¹ ^ (j + 1) * z := by group
    have hn' := hconj n
    rw [hyn, inv_pow, hyn, inv_one, one_mul, mul_one] at hn'
    have hcn : c⁻¹ ^ n = 1 := by
      have := congrArg (· * z⁻¹) hn'
      simpa using this.symm
    obtain ⟨r, rfl⟩ := hn
    have hc1 : c = 1 := by
      have e2 : c⁻¹ ^ (2 * r + 1) = c⁻¹ := by
        rw [pow_succ, pow_mul, sq, ← mul_inv_rev, hc2, inv_one, one_pow, one_mul]
      rw [e2] at hcn
      exact inv_eq_one.1 hcn
    rw [hc, commutatorElement_eq_one_iff_mul_comm] at hc1
    exact hc1

theorem centralizer_Z0q_le_kerG {m : G} (hm : m ∈ M)
    (hmZ : m ∈ Subgroup.centralizer (Z0q M T : Set G)) : m ∈ kerG a := by
  refine (mem_kerG a).2 ⟨hm, eq_one_of_isSumOfNaturalModulesVia hd.nat fun v hv => ?_⟩
  show m * v * m⁻¹ = v
  rw [← Subgroup.mem_centralizer_iff.1 hmZ v (Uq_le_Z0q h.L_le hv), mul_inv_cancel_right]

theorem exists_mul_of_mem_kerG {x : G} (hx : x ∈ kerG a) :
    ∃ q ∈ pCoreOf 2 M, ∃ z ∈ L ⊓ kerG a, x = q * z := by
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have h1 : x ^ m ∈ pCoreOf 2 M := hd.mem_pCoreOf_of_mem_kerG h ((kerG a).pow_mem hx m)
    ⟨e, by rw [← pow_mul, mul_comm, ← he, pow_orderOf_eq_one]⟩
  have h3 : x ^ 2 ^ e ∈ L ⊓ kerG a :=
    ⟨mem_L_of_odd h (kerG_le a ((kerG a).pow_mem hx _)) hm
      (by rw [← pow_mul, ← he, pow_orderOf_eq_one]), (kerG a).pow_mem hx _⟩
  have hcop : Nat.Coprime m (2 ^ e) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hm)
  have hg := Nat.gcd_eq_gcd_ab m (2 ^ e)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hg
  refine ⟨(x ^ m) ^ (Nat.gcdA m (2 ^ e)), (pCoreOf 2 M).zpow_mem h1 _,
    (x ^ 2 ^ e) ^ (Nat.gcdB m (2 ^ e)), (L ⊓ kerG a).zpow_mem h3 _, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]

theorem L_le_of_imSp_le {H : Subgroup G} (hQH : pCoreOf 2 M ≤ H)
    (hLH : imSp a L ≤ imSp a H) : L ≤ H := by
  have hO : pCoreOf 2 L ≤ pCoreOf 2 M :=
    pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer
  have hOL : pCoreOf 2 L ≤ L := pCoreOf_le' L
  have hcomm := hd.commutator_kerG_le h
  have hdec : ∀ l ∈ L, ∃ y ∈ L ⊓ H, ∃ z ∈ L ⊓ kerG a, l = y * z := by
    intro l hl
    obtain ⟨y, hyH, hyM, hya⟩ := mem_imSp.1 (hLH (mem_imSp.2 ⟨l, hl, h.L_le hl, rfl⟩))
    have hn : y⁻¹ * l ∈ kerG a := by
      refine (mem_kerG a).2 ⟨M.mul_mem (M.inv_mem hyM) (h.L_le hl), ?_⟩
      have e : (⟨y⁻¹ * l, M.mul_mem (M.inv_mem hyM) (h.L_le hl)⟩ : ↥M) =
          (⟨y, hyM⟩ : ↥M)⁻¹ * ⟨l, h.L_le hl⟩ := rfl
      rw [e, map_mul, map_inv, hya, inv_mul_cancel]
    obtain ⟨q, hq, z, hz, he⟩ := hd.exists_mul_of_mem_kerG h hn
    refine ⟨y * q, ⟨?_, H.mul_mem hyH (hQH hq)⟩, z, hz, ?_⟩
    · have : y * q = l * z⁻¹ := by
        calc y * q = y * (q * z) * z⁻¹ := by group
          _ = y * (y⁻¹ * l) * z⁻¹ := by rw [he]
          _ = l * z⁻¹ := by group
      rw [this]
      exact L.mul_mem hl (L.inv_mem hz.1)
    · calc l = y * (y⁻¹ * l) := by group
        _ = y * (q * z) := by rw [he]
        _ = y * q * z := by group
  set K : Subgroup G := L ⊓ H with hK
  have hOK : pCoreOf 2 L ≤ K := le_inf hOL (hO.trans hQH)
  have hKn : ∀ l ∈ L, ∀ x ∈ K, l * x * l⁻¹ ∈ K := by
    intro l hl x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hdec l hl
    have hzx : z * x * z⁻¹ ∈ K := by
      have hc : ⁅z, x⁆ ∈ pCoreOf 2 L := hcomm (Subgroup.commutator_mem_commutator hz.2 hx.1)
      have e : z * x * z⁻¹ = ⁅z, x⁆ * x := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact K.mul_mem (hOK hc) hx
    have e : y * z * x * (y * z)⁻¹ = y * (z * x * z⁻¹) * y⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem hy hzx) (K.inv_mem hy)
  have hKn' : (K.subgroupOf L).Normal :=
    ⟨fun x hx l => Subgroup.mem_subgroupOf.2 (hKn l l.2 x (Subgroup.mem_subgroupOf.1 hx))⟩
  have hLK : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := hdec l₁ hl₁
    obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := hdec l₂ hl₂
    let π := QuotientGroup.mk' (K.subgroupOf L)
    have hπK : ∀ (y : G) (hy : y ∈ K), π ⟨y, hy.1⟩ = 1 := fun y hy =>
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hy)
    have hz12 : ⁅z₁, z₂⁆ ∈ K := hOK (hcomm (Subgroup.commutator_mem_commutator hz₁.2 hz₂.1))
    have e1 : (⟨⁅y₁ * z₁, y₂ * z₂⁆, Subgroup.commutator_mem_commutator (L.mul_mem hy₁.1 hz₁.1)
        (L.mul_mem hy₂.1 hz₂.1) |> fun h' => h.perfect ▸ h'⟩ : ↥L) =
        ⁅(⟨y₁, hy₁.1⟩ : ↥L) * ⟨z₁, hz₁.1⟩, (⟨y₂, hy₂.1⟩ : ↥L) * ⟨z₂, hz₂.1⟩⁆ := rfl
    have e2 : (⟨⁅z₁, z₂⁆, hz12.1⟩ : ↥L) = ⁅(⟨z₁, hz₁.1⟩ : ↥L), ⟨z₂, hz₂.1⟩⁆ := rfl
    have h1 : π ⟨⁅y₁ * z₁, y₂ * z₂⁆, Subgroup.commutator_mem_commutator (L.mul_mem hy₁.1 hz₁.1)
        (L.mul_mem hy₂.1 hz₂.1) |> fun h' => h.perfect ▸ h'⟩ = 1 := by
      rw [e1, map_commutatorElement, map_mul, map_mul, hπK y₁ hy₁, hπK y₂ hy₂, one_mul, one_mul,
        ← map_commutatorElement, ← e2, hπK _ hz12]
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  intro l hl
  have hl' : l ∈ ⁅L, L⁆ := by rw [h.perfect]; exact hl
  exact (hLK hl').2

theorem eq_of_imSp_eq {H : Subgroup G} (hHM : H ≤ M) (hQH : pCoreOf 2 M ≤ H)
    (hHa : imSp a M ≤ imSp a H) : H = M := by
  have hLH := hd.L_le_of_imSp_le h hQH ((imSp_mono a h.L_le).trans hHa)
  refine le_antisymm hHM fun m hm => ?_
  obtain ⟨y, hyH, hyM, hya⟩ := mem_imSp.1 (hHa (mem_imSp.2 ⟨m, hm, hm, rfl⟩))
  have hn : y⁻¹ * m ∈ kerG a := by
    refine (mem_kerG a).2 ⟨M.mul_mem (M.inv_mem hyM) hm, ?_⟩
    have e : (⟨y⁻¹ * m, M.mul_mem (M.inv_mem hyM) hm⟩ : ↥M) = (⟨y, hyM⟩ : ↥M)⁻¹ * ⟨m, hm⟩ := rfl
    rw [e, map_mul, map_inv, hya, inv_mul_cancel]
  obtain ⟨q, hq, z, hz, he⟩ := hd.exists_mul_of_mem_kerG h hn
  have : m = y * (q * z) := by rw [← he]; group
  rw [this]
  exact H.mul_mem hyH (H.mul_mem (hQH hq) (hLH hz.1))

theorem card_imSp_of_isPGroup {E : Subgroup G} (hE2 : IsPGroup 2 E) (hEM : E ≤ M) :
    Nat.card (imSp a E) = (pCoreOf 2 M).relIndex E := by
  rw [card_imSp_eq_relIndex a hEM, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (pCoreOf 2 M)]
  congr 1
  refine le_antisymm (fun x hx => ⟨?_, hx.2⟩) (fun x hx => ⟨hd.pCoreOf_le_kerG h hx.1, hx.2⟩)
  obtain ⟨e, he⟩ := hE2 ⟨x, hx.2⟩
  exact hd.mem_pCoreOf_of_mem_kerG h hx.1 ⟨e, by simpa using congrArg Subtype.val he⟩

end IsSp4Data

end S5

end CFSG.Quasithin.MS93
