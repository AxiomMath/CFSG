module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosurePComp
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

variable {G : Type} [Group G]

theorem forall_ggAutomizer_apply_eq_iff {X Bs : Subgroup G} (b : ↥Bs) :
    (∀ φ ∈ ggAutomizer X Bs, φ b = b) ↔
      ∀ n ∈ X, n ∈ Subgroup.normalizer (Bs : Set G) → n * (b : G) * n⁻¹ = b := by
  constructor
  · intro h n hnX hnB
    have h1 := h (ggConjAut Bs hnB) (ggConjAut_mem_ggAutomizer hnX hnB)
    have h2 := congrArg Subtype.val h1
    simpa [ggConjAut_apply] using h2
  · intro h φ hφ
    obtain ⟨n, hnX, hnB, hnφ⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hnφ b, h n hnX hnB]

private theorem mem_centralizer_of_le_centralizer_singleton_of_mem_zpowers
    {X : Subgroup G} {z b : G} (hX : X ≤ Subgroup.centralizer ({z} : Set G))
    (hb : b ∈ Subgroup.zpowers z) : b ∈ Subgroup.centralizer (X : Set G) := by
  have hz : z ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp (hX hx)) z (Set.mem_singleton z)).symm
  exact (Subgroup.zpowers_le.mpr hz) hb

section Step

variable [Finite G]

theorem commutator_self_eq_of_largeEvenStdSub {p : ℕ} {B L D J : Subgroup G} {x : G}
    (hDJ : LargeEvenStdSub p B x L D J) : ⁅J, J⁆ = J := by
  have hq : CFSG.Assembly.IsQuasisimple J := hDJ.1.2.2.2.2.2.1.2.2
  have : Group.IsPerfect J := ⟨hq.1⟩
  exact Subgroup.commutator_eq_self

theorem mul_mul_inv_eq_of_commutator_le {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) {b : G} (hb : b ∈ Bs)
    (hc : ⁅X, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p X) {n : G} (hnX : n ∈ X)
    (hnB : n ∈ Subgroup.normalizer (Bs : Set G)) : n * b * n⁻¹ = b := by
  have hc_mem : n * b * n⁻¹ * b⁻¹ ∈ ⁅X, Subgroup.zpowers b⁆ :=
    Subgroup.commutator_mem_commutator (H₁ := X) (H₂ := Subgroup.zpowers b) hnX
      (Subgroup.mem_zpowers b)
  have hcB : n * b * n⁻¹ * b⁻¹ ∈ Bs :=
    Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp hnB b).mp hb) (Bs.inv_mem hb)
  have hmem : n * b * n⁻¹ * b⁻¹ ∈ Bs ⊓ LargeEvenPPrimeCoreOf p X :=
    ⟨hcB, hc hc_mem⟩
  rw [inf_largeEvenPPrimeCoreOf_eq_bot hBs X] at hmem
  have h1 : n * b * n⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  rwa [mul_inv_eq_one] at h1

theorem mem_zpowers_of_commutator_le {p : ℕ} [Fact p.Prime] {B Bs X : Subgroup G} {z : G}
    (hB : GGBstar p B Bs)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers z)
    {b : G} (hbB : b ∈ B) (hc : ⁅X, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p X) :
    b ∈ Subgroup.zpowers z := by
  refine hfix ⟨b, hB.1 hbB⟩ ?_
  rw [forall_ggAutomizer_apply_eq_iff (X := X) (Bs := Bs)]
  intro n hnX hnB
  exact mul_mul_inv_eq_of_commutator_le hB.2.1 (hB.1 hbB) hc hnX hnB

theorem largeEvenSHat_of_ggAutomizer_fixed_le_zpowers {p : ℕ} [Fact p.Prime] {B Bs X : Subgroup G}
    {z : G} (hBmax : LargeEvenIsBmax p B) (hB : GGBstar p B Bs) (hzB : z ∈ B) (hz1 : z ≠ 1)
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers z) :
    LargeEvenSHat p B z X := by
  refine ⟨hBmax, hzB, hz1, hX.1, hX, fun b => ⟨?_, ?_⟩⟩
  · rintro ⟨hbB, -, hc⟩
    exact mem_zpowers_of_commutator_le hB hfix hbB hc
  · intro hb
    have hbX : b ∈ Subgroup.centralizer (X : Set G) :=
      mem_centralizer_of_le_centralizer_singleton_of_mem_zpowers hX.1 hb
    refine ⟨(Subgroup.zpowers_le.mpr hzB) hb, ?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer (X : Set G) hbX
    · have hbot : ⁅X, Subgroup.zpowers b⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          ((Subgroup.le_centralizer_iff).mp (Subgroup.zpowers_le.mpr hbX))
      rw [hbot]
      exact bot_le

theorem largeEvenNeighbor_of_ggAutomizer_fixed_le_zpowers {p : ℕ} [Fact p.Prime]
    {B Bs X D J : Subgroup G} {x z : G} (hB : GGBstar p B Bs) (hxB : x ∈ B)
    (hxz : x ∉ Subgroup.zpowers z) (hD : D = Subgroup.closure {x, z})
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X) (hJX : J ≤ X)
    (hJ : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers z) :
    LargeEvenNeighbor p x z X D J := by
  refine ⟨hD, le_iSup_conj_pLayer_of_pComponent hX hJX hJ hpJ, ?_⟩
  intro hle
  exact hxz (mem_zpowers_of_commutator_le hB hfix hxB hle)

theorem ggNbr_of_ggAutomizer_fixed_le_zpowers {p : ℕ} [Fact p.Prime] {B Bs X D J : Subgroup G}
    {x z : G} (hBmax : LargeEvenIsBmax p B) (hB : GGBstar p B Bs) (hxB : x ∈ B) (hzB : z ∈ B)
    (hz1 : z ≠ 1) (hxz : x ∉ Subgroup.zpowers z) (hD : D = Subgroup.closure {x, z})
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X) (hJX : J ≤ X)
    (hJ : ⁅J, J⁆ = J) (hpJ : p ∣ Nat.card J)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers z) :
    GGNbr p B x D J z X := by
  exact ⟨largeEvenSHat_of_ggAutomizer_fixed_le_zpowers hBmax hB hzB hz1 hX hfix,
    largeEvenNeighbor_of_ggAutomizer_fixed_le_zpowers hB hxB hxz hD hX hJX hJ hpJ hfix⟩

theorem largeEvenIsNeighborOf_of_ggAutomizer_fixed_le_zpowers {p : ℕ} [Fact p.Prime]
    {B Bs X D J L : Subgroup G} {x z : G} (hBmax : LargeEvenIsBmax p B) (hB : GGBstar p B Bs)
    (hxB : x ∈ B) (hzB : z ∈ B) (hz1 : z ≠ 1) (hxz : x ∉ Subgroup.zpowers z)
    (hD : D = Subgroup.closure {x, z}) (hDJ : LargeEvenStdSub p B x L D J)
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X) (hJX : J ≤ X)
    (hpJ : p ∣ Nat.card J)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers z) :
    LargeEvenIsNeighborOf p B x L z X := by
  exact ⟨largeEvenSHat_of_ggAutomizer_fixed_le_zpowers hBmax hB hzB hz1 hX hfix,
    D, J, hDJ,
    largeEvenNeighbor_of_ggAutomizer_fixed_le_zpowers hB hxB hxz hD hX hJX
      (commutator_self_eq_of_largeEvenStdSub hDJ) hpJ hfix⟩

theorem le_ggG0_of_ggAutomizer_fixed_le_zpowers {p : ℕ} [Fact p.Prime] {B Bs X D J L : Subgroup G}
    {x z : G} (hBmax : LargeEvenIsBmax p B) (hB : GGBstar p B Bs) (hxB : x ∈ B) (hzB : z ∈ B)
    (hz1 : z ≠ 1) (hxz : x ∉ Subgroup.zpowers z) (hD : D = Subgroup.closure {x, z})
    (hDJ : LargeEvenStdSub p B x L D J)
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X) (hJX : J ≤ X)
    (hpJ : p ∣ Nat.card J)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers z) :
    X ≤ ggG0 p B x L D J := by
  exact le_ggG0_of_ggNbr (L := L)
    (ggNbr_of_ggAutomizer_fixed_le_zpowers hBmax hB hxB hzB hz1 hxz hD hX hJX
      (commutator_self_eq_of_largeEvenStdSub hDJ) hpJ hfix)

end Step

end CFSG.StandardType
