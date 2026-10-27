module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofWire

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

open Res611Res4 ThreeLocalSporProof
open scoped Pointwise

namespace Res611Res7

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_invariant {L E T : Subgroup G}
    (hθodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)))
    (hE : IsPGroup 3 E) (hT : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set G))
    (hETL : E ⊔ T ≤ Subgroup.normalizer (L : Set G))
    {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hP : IsPGroup 3 P)
    (hinv : E ⊔ T ≤ invG L P) :
    ∃ R : Subgroup G, R ≤ L ∧ IsPGroup 3 R ∧ E ⊔ T ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ x ∈ P, ∃ r : L, (r : G) ∈ R ∧ (r : L ⧸ aschbacherSolvableCore 3 L) = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 L with hθL
  set N := inSubgroup (aschbacherSolvableCore 3) L with hNdef
  set Phat : Subgroup G := (P.comap (QuotientGroup.mk' θL)).map L.subtype with hPhat
  have hmemP : ∀ y : L, (y : G) ∈ Phat ↔ (y : L ⧸ θL) ∈ P := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [← Subtype.ext hyy']
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hPhatL : Phat ≤ L := Subgroup.map_subtype_le _
  have hmemN : ∀ y : L, (y : G) ∈ N ↔ y ∈ θL := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [← Subtype.ext hyy']
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hNP : N ≤ Phat := by
    rintro _ ⟨y, hy, rfl⟩
    change (y : G) ∈ Phat
    rw [hmemP, (QuotientGroup.eq_one_iff y).mpr hy]
    exact P.one_mem
  have hPN : Phat ≤ Subgroup.normalizer (N : Set G) := hPhatL.trans (le_normalizer_theta L)
  have hP3 : ∀ x ∈ Phat, ∃ k : ℕ, x ^ 3 ^ k ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    change ∃ k : ℕ, (y : G) ^ 3 ^ k ∈ N
    obtain ⟨k, hk⟩ := hP ⟨_, hy⟩
    refine ⟨k, ?_⟩
    have h1 : ((y ^ 3 ^ k : L) : L ⧸ θL) = 1 := by
      rw [QuotientGroup.mk_pow]
      simpa using congrArg Subtype.val hk
    have h2 := (hmemN (y ^ 3 ^ k)).mpr ((QuotientGroup.eq_one_iff _).mp h1)
    simpa using h2
  have hESP : E ⊔ T ≤ Subgroup.normalizer (Phat : Set G) := by
    intro g hg
    obtain ⟨hgL, hstab⟩ := mem_invG_iff.mp (hinv hg)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g * (y : G) * g⁻¹ ∈ Phat
      have h1 : g * (y : G) * g⁻¹ = ((L.normalizerMonoidHom ⟨g, hgL⟩ y : L) : G) := rfl
      rw [h1, hmemP]
      exact (hstab (y : L ⧸ θL)).mpr hy
    · intro hx
      have hxL : x ∈ L := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hgL) _).mp (hPhatL hx)
        simpa [mul_assoc] using h1
      have h2 : ((L.normalizerMonoidHom ⟨g, hgL⟩ ⟨x, hxL⟩ : L) : G) ∈ Phat := hx
      rw [hmemP] at h2
      exact (hmemP ⟨x, hxL⟩).mpr ((hstab _).mp h2)
  have hESN : E ⊔ T ≤ Subgroup.normalizer (N : Set G) :=
    hETL.trans (normalizer_le_normalizer_theta L)
  obtain ⟨hNsol, hN3⟩ := theta_solvable_and_not_dvd L
  obtain ⟨R, hRP, hR3, hRN, hcov⟩ :=
    exists_invariant_threeLift hNsol hθodd hN3 hNP hPN hP3 hE hT hET hESP hESN
  refine ⟨R, hRP.trans hPhatL, hR3, hRN, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨r, hr, hrN⟩ := hcov y ((hmemP y).mpr hx)
  have hrL : r ∈ L := hPhatL (hRP hr)
  refine ⟨⟨r, hrL⟩, hr, ?_⟩
  rw [QuotientGroup.eq, ← hmemN]
  simpa using hrN

theorem inf_centralizer_le_of_mulEquiv {X Xb : Type*} [Group X] [Group Xb] [Finite X]
    (e : X ≃* Xb)
    (hXb : ∀ z : Xb, orderOf z = 3 → IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set Xb)))
    {Y : Subgroup X} (hY : CFSG.Assembly.IsElemAbelian 3 Y) (hY1 : Y ≠ ⊥) :
    Subgroup.centralizer (Y : Set X) ⊓
        Subgroup.centralizer
          (inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) : Set X) ≤
      inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  exact inf_centralizer_le_of_isCharacteristicP
    (isCharacteristicP_centralizer_of_surjective e.toMonoidHom e.surjective
      (by rw [hker]; exact bot_le) (by rw [hker]; exact IsPGroup.of_bot) hXb hY
      (by rw [hker]; exact fun h => hY1 (le_bot_iff.mp h)))

end Res611Res7

open Res611Res7

section Certs

theorem Res611Res7.inf_centralizer_le_of_case23 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {A : Subgroup G} {d : G}
    (h23 : (A ≤ K ∧ ∃ (N : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) (_ : N.Normal),
          N = ((Subgroup.zpowers d).subgroupOf K).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) ∧
          (Nonempty ((K ⧸ aschbacherSolvableCore 3 K) ⧸ N ≃* projSU 4 3 1) ∨
            Nonempty ((K ⧸ aschbacherSolvableCore 3 K) ⧸ N ≃* Blueprint.NativeSporadic.McL))) ∨
        (A = Subgroup.zpowers d ⊔ (A ⊓ K) ∧ d ∉ K ∧
          (Blueprint.ChevalleyExceptionalModel (K ⧸ aschbacherSolvableCore 3 K) .G2 3 1 ∨
            Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* Blueprint.NativeSporadic.McL) ∨
            Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 4 (GaloisField 3 1)) ∨
            Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSU 4 3 1))))
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {Y : Subgroup (K ⧸ aschbacherSolvableCore 3 K)} (hY : CFSG.Assembly.IsElemAbelian 3 Y)
    (hY9 : A ≤ K → 9 ≤ Nat.card Y) (hY1 : Y ≠ ⊥) :
    Subgroup.centralizer (Y : Set (K ⧸ aschbacherSolvableCore 3 K)) ⊓
        Subgroup.centralizer (inSubgroup (CFSG.pCore 3)
          (Subgroup.centralizer (Y : Set (K ⧸ aschbacherSolvableCore 3 K))) :
            Set (K ⧸ aschbacherSolvableCore 3 K)) ≤
      inSubgroup (CFSG.pCore 3) (Subgroup.centralizer (Y : Set (K ⧸ aschbacherSolvableCore 3 K)))
      := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h23 with ⟨hAK, N, hNn, hNdef, hiso⟩ | ⟨-, -, hiso⟩
  ·
    have hc3 : IsPGroup 3 (Subgroup.zpowers d) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1, pow_one])
    have hNcard : Nat.card N = 3 := by
      rw [hNdef, card_map_mk_of_isPGroup hc3 (Subgroup.zpowers_le.mpr (hAK hdA)),
        Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
    exact ks611CentChar3_holds _ (Or.inl ⟨N, hNn, hNcard, hiso⟩) Y hY (hY9 hAK)
  · rcases hiso with hG | hMc | hL4 | hU4
    · obtain ⟨F, _, _, _, ⟨e⟩⟩ := exists_mulEquiv_G2 hG
      exact inf_centralizer_le_of_mulEquiv e centCharThree_adjointGroup_G2 hY hY1
    · obtain ⟨e⟩ := hMc
      exact inf_centralizer_le_of_mulEquiv (e.trans CFSG.Sporadic.Schreier.mclPermEquiv)
        centCharThree_mclP hY hY1
    · obtain ⟨e⟩ := hL4
      exact inf_centralizer_le_of_mulEquiv e kCentCharThreeL43_holds hY hY1
    · obtain ⟨e⟩ := hU4
      exact inf_centralizer_le_of_mulEquiv e kCentCharThreeU43_holds hY hY1

end Certs

end CFSG.RankThree.PartTwo.Sec6
