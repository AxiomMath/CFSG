module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Iface
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Fix
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.Quasithin.L3Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem pCore_le_center_of_quasisimple {Γ : Type*} [Group Γ] [Finite Γ]
    (hq : CFSG.Open.IsQuasisimple Γ) : CFSG.pCore 2 Γ ≤ Subgroup.center Γ := by
  obtain ⟨hcomm, hsimple⟩ := hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 Γ
  set π := QuotientGroup.mk' (Subgroup.center Γ)
  have hnorm : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · intro x hx
    have hmem : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exfalso
    have h2 : IsPGroup 2 (Γ ⧸ Subgroup.center Γ) := by
      intro y
      have hy : y ∈ N.map π := h ▸ Subgroup.mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := Γ) ⟨x, hx⟩
      refine ⟨n, ?_⟩
      have hx1 : x ^ 2 ^ n = 1 := congrArg Subtype.val hn
      rw [← map_pow, hx1, map_one]
    have : Group.IsPerfect Γ := ⟨hcomm⟩
    have := hsimple.toNontrivial
    exact Group.IsPerfect.not_isNilpotent (Γ ⧸ Subgroup.center Γ) h2.isNilpotent

theorem exists_lift_odd_order {Γ : Type*} [Group Γ] [Finite Γ] (N : Subgroup Γ) [N.Normal]
    {z : Γ ⧸ N} (hz : Odd (orderOf z)) :
    ∃ x : Γ, Odd (orderOf x) ∧ (x : Γ ⧸ N) = z := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos b).ne'
  have hcop : Nat.Coprime (2 ^ k) (orderOf (b : Γ ⧸ N)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hz)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (A4.mem_zpowers_pow_of_coprime hcop)
  refine ⟨(b ^ 2 ^ k) ^ j, ?_, ?_⟩
  · have hpow : ((b ^ 2 ^ k) ^ j) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, ← hkm,
        pow_orderOf_eq_one, one_zpow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · rw [QuotientGroup.mk_zpow, QuotientGroup.mk_pow]
    exact hj

theorem eq_one_of_central_quotient {Γ : Type*} [Group Γ] (hperf : commutator Γ = ⊤)
    (α : MulAut Γ) (h : ∀ l : Γ, l⁻¹ * α l ∈ Subgroup.center Γ) : α = 1 := by
  let g : Γ →* Subgroup.center Γ :=
    { toFun := fun l => ⟨l⁻¹ * α l, h l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hb : b⁻¹ * (a⁻¹ * α a) = (a⁻¹ * α a) * b⁻¹ :=
          Subgroup.mem_center_iff.mp (h a) b⁻¹
        calc (a * b)⁻¹ * α (a * b) = (b⁻¹ * (a⁻¹ * α a)) * α b := by
              rw [map_mul, mul_inv_rev]
              group
          _ = (a⁻¹ * α a) * (b⁻¹ * α b) := by rw [hb]; group) }
  have hker : commutator Γ ≤ g.ker := Abelianization.commutator_subset_ker g
  rw [hperf] at hker
  ext l
  have hl : g l = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top l))
  have hl' : l⁻¹ * α l = 1 := congrArg Subtype.val hl
  have : α l = l := by
    have := mul_eq_one_iff_eq_inv.mp hl'
    simpa using this.symm
  simpa using this

theorem centralizes_of_model_alt2 (hM : L3ModelAut) {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (_hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    (hL : IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) (hP : IsSylowTwoOf P L) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) :
    ∀ l ∈ L, v * l = l * v := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥L := CFSG.pCore 2 ↥L
  let φ : (↥L ⧸ N) ≃* projectiveSL 3 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  let α : MulAut ↥L := conjAct L ⟨v, hv⟩
  have hNα : N.map (α : ↥L →* ↥L) = N :=
    Subgroup.characteristic_iff_map_eq.mp (CFSG.pCore_characteristic (p := 2) (G := ↥L)) α
  let β : MulAut (↥L ⧸ N) := QuotientGroup.congr N N α hNα
  let Q : Sylow 2 (↥L ⧸ N) :=
    (A4.toSylow hP).mapSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hNP : N ≤ P.subgroupOf L :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).le_sylow_of_normal (A4.toSylow hP)
  have hQ : ∀ y : ↥L, (y : ↥L ⧸ N) ∈ (Q : Subgroup (↥L ⧸ N)) ↔ y ∈ P.subgroupOf L := by
    intro y
    change (y : ↥L ⧸ N) ∈ (P.subgroupOf L).map (QuotientGroup.mk' N) ↔ _
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have hmem : y'⁻¹ * y ∈ N := QuotientGroup.eq.mp hyy'
      have := (P.subgroupOf L).mul_mem hy' (hNP hmem)
      simpa using this
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hfix : ∀ z ∈ Subgroup.normalizer ((Q : Subgroup (↥L ⧸ N)) : Set (↥L ⧸ N)),
      Odd (orderOf z) → β z = z := by
    intro z hz hzo
    obtain ⟨x, hxo, rfl⟩ := exists_lift_odd_order N hzo
    have hxN : x ∈ Subgroup.normalizer (((A4.toSylow hP : Sylow 2 ↥L) : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.mp hz (y : ↥L ⧸ N)
      change y ∈ P.subgroupOf L ↔ x * y * x⁻¹ ∈ P.subgroupOf L
      rw [← hQ y, ← hQ (x * y * x⁻¹)]
      exact h1
    have hfx := conjAct_fix_of_odd hP hv hc hxN hxo
    change QuotientGroup.congr N N α hNα (x : ↥L ⧸ N) = (x : ↥L ⧸ N)
    rw [QuotientGroup.congr_mk]
    exact congrArg (QuotientGroup.mk (s := N)) hfx
  have hβ : β = 1 := hM K 2 le_rfl hK _ φ Q β hfix
  have hcen : ∀ l : ↥L, l⁻¹ * α l ∈ Subgroup.center ↥L := fun l => by
    have h1 : β (l : ↥L ⧸ N) = (l : ↥L ⧸ N) := by rw [hβ]; rfl
    have h2 : ((α l : ↥L) : ↥L ⧸ N) = (l : ↥L ⧸ N) := h1
    exact pCore_le_center_of_quasisimple hq (QuotientGroup.eq.mp h2.symm)
  have hα : α = 1 := eq_one_of_central_quotient hq.1 α hcen
  intro l hl
  have h1 : α ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [hα]; rfl
  have h2 := congrArg (fun x : ↥L => (x : G)) h1
  have h3 : v * l * v⁻¹ = l := h2
  calc v * l = (v * l * v⁻¹) * v := by group
    _ = l * v := by rw [h3]

end CFSG.Quasithin.L3Aut
