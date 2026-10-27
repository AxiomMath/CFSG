module

public import CFSG.ClassicalInvolution.AschTight.S19MSylow
public import CFSG.Quasithin.Background.E2TwoProofDefs

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution
open scoped commutatorElement MatrixGroups

variable {K : Type} [Group K]

theorem fix_of_perfect {z : K} {L : Subgroup K} [Group.IsPerfect L]
    (hLz : L ≤ Subgroup.centralizer ({z} : Set K)) (v : MulAut K)
    (hv : ∀ x ∈ L, v x * x⁻¹ ∈ Subgroup.zpowers z) : ∀ x ∈ L, v x = x := by
  have hcz : ∀ x ∈ L, ∀ c ∈ Subgroup.zpowers z, c * x⁻¹ = x⁻¹ * c := by
    intro x hx c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h1 : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp (hLz hx)
    exact (h1.symm.zpow_left n).inv_right
  let δ : L →* Subgroup.zpowers z :=
    { toFun := fun x => ⟨v x * (x : K)⁻¹, hv x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change v ((x : K) * y) * ((x : K) * y)⁻¹ = v x * (x : K)⁻¹ * (v y * (y : K)⁻¹)
        rw [map_mul, mul_inv_rev]
        calc v x * v y * ((y : K)⁻¹ * (x : K)⁻¹) = v x * ((v y * (y : K)⁻¹) * (x : K)⁻¹) := by
              group
          _ = v x * ((x : K)⁻¹ * (v y * (y : K)⁻¹)) := by rw [hcz x x.2 _ (hv y y.2)]
          _ = v x * (x : K)⁻¹ * (v y * (y : K)⁻¹) := by group) }
  have hker : commutator L ≤ δ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (δ a).2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (δ b).2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, zpow_mul_comm]
  intro x hx
  have h1 : δ ⟨x, hx⟩ = 1 := hker (by rw [Group.IsPerfect.commutator_eq_top]; trivial)
  have h2 : v x * x⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

theorem exists_not_comm_of_sylow {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {z : K} {L : Subgroup K} (hL : IsClassicalSL2 F L z) (T : Sylow 2 L) :
    ∃ a ∈ (T : Subgroup L), ∃ b ∈ (T : Subgroup L), a * b ≠ b * a := by
  obtain ⟨e⟩ := hL.nonempty_mulEquiv
  let T' : Sylow 2 SL(2, F) := T.comapOfInjective e.symm.toMonoidHom e.symm.injective (by
    rw [MonoidHom.range_eq_top_of_surjective _ e.symm.surjective]
    exact le_top)
  obtain ⟨n, hn, ⟨ψ⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd T'
  set α := ψ.symm (QuaternionGroup.a 1) with hα
  set β := ψ.symm (QuaternionGroup.xa 0) with hβ
  refine ⟨e.symm α, α.2, e.symm β, β.2, fun h => ?_⟩
  have h1 : α * β = β * α := by
    apply Subtype.ext
    apply e.symm.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h
  have h2 : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (n - 2))) * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
    apply ψ.symm.injective
    rw [map_mul, map_mul]
    exact h1
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at h2
  have h3 : ((2 : ℕ) : ZMod (2 * 2 ^ (n - 2))) = 0 := by
    push_cast
    linear_combination -h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have h4 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 := Nat.le_of_dvd (by norm_num) h3
  omega

variable [Finite K]

theorem le_zpowers_of_normalized {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {z : K} {L : Subgroup K} (hL : IsClassicalSL2 F L z)
    (hC : ∀ c ∈ Subgroup.centralizer (L : Set K), ∀ k : ℕ, c ^ 2 ^ k = 1 →
      c ∈ Subgroup.zpowers z)
    {Q : Subgroup K} (hQz : Q ≤ Subgroup.centralizer ({z} : Set K)) (hQ2 : IsPGroup 2 Q)
    (hQn : Subgroup.centralizer ({z} : Set K) ≤ Subgroup.normalizer (Q : Set K)) :
    Q ≤ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := hL.isPerfect h4
  obtain ⟨e⟩ := hL.nonempty_mulEquiv
  have hQL : ∀ x ∈ Q, x ∈ L → x ∈ Subgroup.zpowers z := by
    intro x hxQ hxL
    have hN : (Q.subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.mp (hQn (hL.le_centralizer g.2)) n).mp hn
      simpa using this⟩
    have hx : (⟨x, hxL⟩ : L) ∈ Q.subgroupOf L := Subgroup.mem_subgroupOf.mpr hxQ
    rcases hL.normal_cases h4 _ hN with h | h | h
    · rw [h, Subgroup.mem_bot] at hx
      rw [show x = 1 from congrArg Subtype.val hx]
      exact Subgroup.one_mem _
    · rw [h, mem_center_iff_of_equiv_sl2 e, mem_center_sl2_iff] at hx
      rcases hx with h1 | h1
      · have h2 : (⟨x, hxL⟩ : L) = 1 := e.injective (by rw [h1, map_one])
        rw [show x = 1 from congrArg Subtype.val h2]
        exact Subgroup.one_mem _
      · have h2 : orderOf x = 2 := by
          rw [← Subgroup.orderOf_mk x hxL, ← MulEquiv.orderOf_eq e, h1]
          exact sl2_orderOf_neg_one hodd
        rw [hL.eq_of_orderOf_eq_two hodd hxL h2]
        exact Subgroup.mem_zpowers z
    ·
      exfalso
      have hLQ : L ≤ Q := fun l hl => by
        have : (⟨l, hl⟩ : L) ∈ Q.subgroupOf L := by rw [h]; trivial
        exact Subgroup.mem_subgroupOf.mp this
      have hz1 : (⟨z, hL.mem⟩ : L) ≠ 1 := fun h1 => by
        have := hL.orderOf_eq_two
        rw [show z = 1 from congrArg Subtype.val h1, orderOf_one] at this
        omega
      have : Nontrivial L := ⟨⟨_, _, hz1⟩⟩
      exact Group.IsPerfect.not_isNilpotent L (hQ2.to_le hLQ).isNilpotent
  intro g hg
  have hfix := fix_of_perfect hL.le_centralizer (MulAut.conj g) fun x hx => by
    rw [MulAut.conj_apply]
    refine hQL _ ?_ ?_
    · have h1 : x * g⁻¹ * x⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQn (hL.le_centralizer hx)) _).mp (Q.inv_mem hg)
      have := Q.mul_mem hg h1
      simpa [mul_assoc] using this
    · have h1 : g * x * g⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hL.centralizer_le_normalizer (hQz hg)) x).mp hx
      exact L.mul_mem h1 (L.inv_mem hx)
  have hgL : g ∈ Subgroup.centralizer (L : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hfix x hx
    rw [MulAut.conj_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  obtain ⟨k, hk⟩ := hQ2 ⟨g, hg⟩
  exact hC g hgL k (by simpa using congrArg Subtype.val hk)

theorem zOf_eq_zpowers {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {z : K} {L : Subgroup K} (hL : IsClassicalSL2 F L z)
    (hC : ∀ c ∈ Subgroup.centralizer (L : Set K), ∀ k : ℕ, c ^ 2 ^ k = 1 →
      c ∈ Subgroup.zpowers z)
    (hS : ∀ y ∈ Subgroup.centralizer ({z} : Set K), ∀ a ∈ L, ∀ b ∈ L, a * b ≠ b * a →
      y * a = a * y → y * b = b * y → y ∈ Subgroup.centralizer (L : Set K))
    (S : Sylow 2 K) (hz : z ∈ E2P.zOf (S : Subgroup K)) :
    E2P.zOf (S : Subgroup K) = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hz)
  have hSz : (S : Subgroup K) ≤ Subgroup.centralizer ({z} : Set K) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 s hs)
  obtain ⟨T, hT⟩ := Disconnected.AschTight.S19M.exists_sylow_inf_of_le_normalizer
    hL.le_centralizer hL.centralizer_le_normalizer (S.subtype hSz)
  rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSz] at hT
  have hTmem : ∀ a ∈ (T : Subgroup L), (a : K) ∈ L ⊓ (S : Subgroup K) := fun a ha => by
    rw [← hT]
    exact ⟨a, ha, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_comm_of_sylow hodd hL T
  have haS := (hTmem a ha).2
  have hbS := (hTmem b hb).2
  have hya : y * a = a * y := (Subgroup.mem_centralizer_iff.mp hy.2 a haS).symm
  have hyb : y * b = b * y := (Subgroup.mem_centralizer_iff.mp hy.2 b hbS).symm
  have hab' : (a : K) * b ≠ b * a := fun h => hab (Subtype.ext (by simpa using h))
  have hyL := hS y (hSz hy.1) a a.2 b b.2 hab' hya hyb
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hy.1⟩
  exact hC y hyL k (by simpa using congrArg Subtype.val hk)

end CFSG.Quasithin.Ch3E213M.OLA
