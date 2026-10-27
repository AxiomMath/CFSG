module

public import CFSG.Quasithin.Vol2.Ch10SecCConj
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13

variable {G : Type} [Group G]

variable [Finite G]

omit [Finite G] in
theorem conjugate_props {L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (g : G) :
    ⁅CFSG.conjugate L g, CFSG.conjugate L g⁆ = CFSG.conjugate L g ∧
      IsSimpleGroup (↥(CFSG.conjugate L g) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L g)) ∧
      (pCoreOf 2 (CFSG.conjugate L g)).relIndex (CFSG.conjugate L g) =
        (pCoreOf 2 L).relIndex L :=
  ⟨commutator_map_eq _ hL, isSimpleGroup_quot_map _ hsimp, relIndex_pCoreOf_map L _⟩

theorem pCoreOf_le_centralizer_of_subnormal {T L I X : Subgroup G}
    (hR : IsPrimeReduced 2 ((fsuVM T L I).subgroupOf (fsuM T L)))
    (hVM : fsuVM T L I ≤ fsuM T L) (hX : IsSubnormal X (fsuM T L)) :
    pCoreOf 2 X ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  refine (A4.pCoreOf_le_of_subnormal 2 hX).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  have hc := pCore_le_centralizer_of_isPrimeReduced hR hy
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have := hc ⟨v, hVM hv⟩ hv
  exact congrArg Subtype.val this

omit [Finite G] in
theorem commutator_le_left_of_le_normalizer {X Y : Subgroup G}
    (h : Y ≤ Subgroup.normalizer (X : Set G)) : ⁅X, Y⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have hb' : b * a⁻¹ * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (h hb) _).mp (X.inv_mem ha)
  have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
  rw [this]
  exact X.mul_mem ha hb'

omit [Finite G] in
theorem mem_centralizer_sup {X Y : Subgroup G} {x : G} (hX : x ∈ Subgroup.centralizer (X : Set G))
    (hY : x ∈ Subgroup.centralizer (Y : Set G)) :
    x ∈ Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have hle : X ⊔ Y ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact (Subgroup.mem_centralizer_iff.mp hX a ha).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact (Subgroup.mem_centralizer_iff.mp hY a ha).symm
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) x rfl).symm

omit [Finite G] in
theorem mem_centralizer_iff_le {X : Subgroup G} {x : G} :
    x ∈ Subgroup.centralizer (X : Set G) ↔ X ≤ Subgroup.centralizer ({x} : Set G) := by
  constructor
  · intro h a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact (Subgroup.mem_centralizer_iff.mp h a ha).symm
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (h ha) x rfl).symm

theorem exists_odd_prime_dvd_card {Q : Type*} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    (hnab : ∃ a b : Q, a * b ≠ b * a) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card Q := by
  by_contra hno
  push Not at hno
  have hcard : Nat.card Q = 2 ^ (Nat.card Q).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdv => by
      by_contra h2; exact hno _ hd h2 hdv
  have h2 : IsPGroup 2 Q := IsPGroup.of_card hcard
  have : Nontrivial Q := hs.toNontrivial
  have hZ := h2.center_nontrivial
  have hZtop : Subgroup.center Q = ⊤ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (Subgroup.center Q) inferInstance with
        h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hZ)
    · exact h
  obtain ⟨a, b, hab⟩ := hnab
  have ha : a ∈ Subgroup.center Q := hZtop ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ha b).symm

omit [Finite G] in
theorem nonabelian_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem le_of_le_fsuL0_of_le_centralizer {T L I B A K : Subgroup G} {x : G}
    (hL : ⁅L, L⁆ = L) (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hBA : fsuL0 T L = B ⊔ A) (hBn : fsuL0 T L ≤ Subgroup.normalizer (B : Set G))
    (hAn : fsuL0 T L ≤ Subgroup.normalizer (A : Set G))
    (hA : ∃ s, A = CFSG.conjugate L s) (hK : ∃ g, K = CFSG.conjugate L g)
    (hOA : pCoreOf 2 A ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    (hx : x ∈ fsuVM T L I) (hBx : B ≤ Subgroup.centralizer ({x} : Set G))
    (hxA : x ∉ Subgroup.centralizer (A : Set G))
    (hKL0 : K ≤ fsuL0 T L) (hKx : K ≤ Subgroup.centralizer ({x} : Set G)) : K ≤ B := by
  obtain ⟨s, rfl⟩ := hA
  obtain ⟨g, rfl⟩ := hK
  obtain ⟨hAp, hAs, hAi⟩ := conjugate_props hL hsimp s
  obtain ⟨hKp, hKs, hKi⟩ := conjugate_props hL hsimp g
  refine le_of_le_sup_of_le_centralizer (A := CFSG.conjugate L s) (L := B) (x := x)
    (hBA.symm.le.trans hBn) (hBA.symm.le.trans hAn) hAp hAs hKp hKs (hKi.trans hAi.symm) hBx
    ?_ (fun h => hxA (mem_centralizer_iff_le.mpr h)) (hKL0.trans hBA.le) hKx
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  exact Subgroup.mem_centralizer_iff.mp (hOA hy) x hx

end CFSG.Quasithin.Vol2.Ch10.SecC
