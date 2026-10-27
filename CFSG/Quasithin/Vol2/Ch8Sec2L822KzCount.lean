module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

@[expose] def M11Sub144O2_kz : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) →
    ∀ U : Subgroup Q, Nat.card U = 144 → CFSG.pCore 2 ↥U = ⊥

@[expose] noncomputable def kzImage_kz {G : Type} [Group G] (H K : Subgroup G) :
    Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp
    (Subgroup.inclusion (inf_le_right : H ⊓ K ≤ K))).range)

theorem dvd_144_of_dvd_72_mul_pow_kz (k : ℕ) {n : ℕ} (h1 : n ∣ 72 * 2 ^ k) (h2 : n ∣ 7920) :
    n ∣ 144 := by
  have h3 : n ∣ Nat.gcd (72 * 2 ^ k) 7920 := Nat.dvd_gcd h1 h2
  refine h3.trans ?_
  cases k with
  | zero => norm_num
  | succ j =>
    have e1 : 72 * 2 ^ (j + 1) = 144 * 2 ^ j := by ring
    have e2 : (7920 : ℕ) = 144 * 55 := by norm_num
    rw [e1, e2, Nat.gcd_mul_left, (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 55)).gcd_eq_one,
      mul_one]


theorem false_of_kzImage_card_kz {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hH : (pCoreOf 2 H).relIndex H = 72)
    (hQ : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 7920)
    (hM : ∀ U : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), Nat.card U = 144 → CFSG.pCore 2 ↥U = ⊥)
    (h16 : 16 ∣ Nat.card (kzImage_kz H K)) (h9 : 9 ∣ Nat.card (kzImage_kz H K)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOn : ∀ h ∈ H, ∀ x ∈ pCoreOf 2 H, h * x * h⁻¹ ∈ pCoreOf 2 H := by
    intro h hh x hx
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) x).mp hx
  have hOp : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  obtain ⟨k, hk⟩ := hOp.exists_card_eq
  have hOH : ((pCoreOf 2 H).subgroupOf H).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hOn (g : G) g.2 x hx⟩
  let A : Subgroup G := H ⊓ K
  let g : ↥A →* ↥H ⧸ (pCoreOf 2 H).subgroupOf H :=
    (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H)).comp
      (Subgroup.inclusion (inf_le_left : H ⊓ K ≤ H))
  let f : ↥A →* ↥K ⧸ CFSG.pCore 2 ↥K :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion (inf_le_right : H ⊓ K ≤ K))
  have hrange : f.range = kzImage_kz H K := rfl
  rw [← hrange] at h16 h9
  have hcard : Nat.card f.range = 144 := by
    have hHc : Nat.card ↥H = 72 * 2 ^ k := by
      have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 H) (K := H)
      rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 H), hH, hk] at h1
      exact h1.symm
    have hA : Nat.card ↥A ∣ Nat.card ↥H := Subgroup.card_dvd_of_le (inf_le_left : H ⊓ K ≤ H)
    have hd1 : Nat.card f.range ∣ 72 * 2 ^ k := by
      rw [← hHc]
      exact (Subgroup.card_range_dvd f).trans hA
    have hd2 : Nat.card f.range ∣ 7920 := by
      rw [← hQ]
      exact Subgroup.card_subgroup_dvd_card _
    have hd3 : Nat.card f.range ∣ 144 := dvd_144_of_dvd_72_mul_pow_kz k hd1 hd2
    have hd4 : 144 ∣ Nat.card f.range := by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 16 9) h16 h9
      simpa using this
    exact Nat.dvd_antisymm hd3 hd4
  have hgk : g.ker.index ≤ 72 := by
    rw [Subgroup.index_ker]
    have h1 := Subgroup.card_le_card_group g.range
    have h2 : Nat.card (↥H ⧸ (pCoreOf 2 H).subgroupOf H) = 72 := by
      rw [← Subgroup.index_eq_card]
      exact hH
    omega
  have hkerP : IsPGroup 2 g.ker := by
    intro x
    have hxO : ((x : ↥A) : G) ∈ pCoreOf 2 H := by
      have hx1 : g x = 1 := (MonoidHom.mem_ker).mp x.2
      have hx2 := (QuotientGroup.eq_one_iff _).mp hx1
      rw [Subgroup.mem_subgroupOf] at hx2
      exact hx2
    obtain ⟨n, hn⟩ := hOp ⟨((x : ↥A) : G), hxO⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hker : g.ker ≤ f.ker := by
    have hRn : (g.ker.map f.rangeRestrict).Normal :=
      Subgroup.Normal.map inferInstance f.rangeRestrict (MonoidHom.rangeRestrict_surjective f)
    have hRp : IsPGroup 2 (g.ker.map f.rangeRestrict) := hkerP.map f.rangeRestrict
    have hle := CFSG.LieType.BorelTits.le_pCore 2 hRn hRp
    have hMr : CFSG.pCore 2 ↥f.range = ⊥ := hM f.range hcard
    rw [hMr] at hle
    intro x hx
    have hmem : f.rangeRestrict x ∈ g.ker.map f.rangeRestrict := Subgroup.mem_map_of_mem _ hx
    have h1 := Subgroup.mem_bot.mp (hle hmem)
    rw [MonoidHom.mem_ker]
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hle : f.ker.index ≤ g.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have h144 : f.ker.index = 144 := by
    rw [Subgroup.index_ker, hcard]
  omega

end CFSG.Quasithin.H13
