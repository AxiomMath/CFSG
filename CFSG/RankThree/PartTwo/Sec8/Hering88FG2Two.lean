module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FSmall
public import CFSG.RankThree.PartTwo.Sec8.Hering88FG2Perm
public import Certificates.Certificate799300
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLinkFacts
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofG2Two

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.Quasithin CFSG.Blueprint.Chevalley

theorem u33Arr_eq : u33Arr = CFSG.Quasithin.u33Gens := rfl

theorem u33Pt_eq (k : Fin 5) (x : Fin 28) : u33Pt k x = u33Img k x := by
  have h := u33Gens_rep k x
  rw [← u33Arr_eq] at h
  unfold u33Pt
  rw [h]
  exact Fin.ext (Nat.mod_eq_of_lt (u33Img k x).2)

theorem pairOrbit_sound (K : ℕ) :
    ∀ pq ∈ pairOrbit K, ∃ h ∈ u33PresHom.range, h 0 = pq.1 ∧ h 1 = pq.2 := by
  induction K with
  | zero =>
    intro pq hpq
    have : pq = (0, 1) := by simpa [pairOrbit] using hpq
    subst this
    exact ⟨1, one_mem _, rfl, rfl⟩
  | succ K ih =>
    intro pq hpq
    rw [pairOrbit, Function.iterate_succ_apply'] at hpq
    rw [pairStep, Finset.mem_union] at hpq
    rcases hpq with hpq | hpq
    · exact ih pq hpq
    · rw [Finset.mem_biUnion] at hpq
      obtain ⟨k, -, hk⟩ := hpq
      rw [Finset.mem_image] at hk
      obtain ⟨rs, hrs, rfl⟩ := hk
      obtain ⟨h, hh, h0, h1⟩ := ih rs hrs
      refine ⟨u33Img k * h, mul_mem ⟨PresentedGroup.of k, u33PresHom_of k⟩ hh, ?_, ?_⟩
      · simp only [Equiv.Perm.mul_apply, h0, u33Pt_eq]
      · simp only [Equiv.Perm.mul_apply, h1, u33Pt_eq]

theorem u33_two_trans :
    ∀ p q : Fin 28, p ≠ q → ∃ h ∈ u33PresHom.range, h 0 = p ∧ h 1 = q := by
  have hproof : u33TwoTransOK () = true := Certificates.certificate799300
  have hcheck := u33TwoTransOK_sound hproof
  intro p q hpq
  exact pairOrbit_sound 9 (p, q) (hcheck p q hpq)

theorem u33_no_comm_three_seven
    {g t : U33G} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (ht7 : t ^ 7 = 1)
    (ht1 : t ≠ 1) : g * t ≠ t * g := by
  have hcard : Nat.card u33PresHom.range = 6048 := by
    rw [range_u33PresHom]
    exact card_u33Perm
  have hinj := u33PresHom_injective
  intro hcomm
  refine no_comm_three_seven hcard u33_two_trans (MonoidHom.mem_range.mpr ⟨g, rfl⟩) ?_ ?_
    (MonoidHom.mem_range.mpr ⟨t, rfl⟩) ?_ ?_ (by rw [← map_mul, ← map_mul, hcomm])
  · rw [← map_pow, hg3, map_one]
  · exact fun h => hg1 (hinj (h.trans (map_one _).symm))
  · rw [← map_pow, ht7, map_one]
  · exact fun h => ht1 (hinj (h.trans (map_one _).symm))

theorem isSolvable_centralizer_u33
    {g : U33G} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set U33G)) := by
  haveI : Finite U33G := Nat.finite_of_card_ne_zero (by rw [card_u33Pres]; norm_num)
  set C := Subgroup.centralizer ({g} : Set U33G) with hC
  have hdvd : Nat.card C ∣ 6048 := by
    rw [← card_u33Pres]
    exact Subgroup.card_subgroup_dvd_card C
  have h7 : ¬ 7 ∣ Nat.card C := by
    intro h7
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 7 h7
    have ht7 : (t : U33G) ^ 7 = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht] at this
      exact congrArg Subtype.val this
    have ht1 : (t : U33G) ≠ 1 := by
      intro h1
      have : t = 1 := Subtype.ext h1
      rw [this, orderOf_one] at ht
      omega
    have hcomm : (t : U33G) * g = g * (t : U33G) :=
      Subgroup.mem_centralizer_singleton_iff.mp t.2
    exact u33_no_comm_three_seven hg3 hg1 ht7 ht1 hcomm.symm
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card C).primeFactors ⊆ {2, 3} := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ 6048 := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    have hp7 : p ≠ 7 := fun h => h7 (h ▸ Nat.dvd_of_mem_primeFactors hp)
    have h6048 : (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 := by norm_num
    rw [h6048] at hpd
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with h | h
    · rcases (Nat.Prime.dvd_mul hpp).mp h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h)
        simp [this]
      · have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow h)
        simp [this]
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h) hp7
  exact (Finset.card_le_card hsub).trans (by decide)

theorem isSolvable_centralizer_of_commutator {Q : Type*} [Group Q] {g : Q} (hg : g ∈ commutator Q)
    (h : Group.IsSolvable ↥(Subgroup.centralizer ({(⟨g, hg⟩ : commutator Q)} :
      Set (commutator Q)))) : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set Q)) := by
  set C := Subgroup.centralizer ({g} : Set Q) with hC
  set C₁ := Subgroup.centralizer ({(⟨g, hg⟩ : commutator Q)} : Set (commutator Q)) with hC₁
  have hmem : ∀ x : C₁, ((x : commutator Q) : Q) ∈ C := by
    intro x
    have := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val this
  let f : C₁ →* C :=
    ((commutator Q).subtype.comp C₁.subtype).codRestrict C fun x => hmem x
  let φ : C →* Abelianization Q := Abelianization.of.comp C.subtype
  haveI : Group.IsSolvable (Abelianization Q) := inferInstance
  refine solvable_of_ker_le_range f φ ?_
  intro x hx
  have hxD : (x : Q) ∈ commutator Q := by
    rw [← Abelianization.ker_of]
    exact hx
  have hxC₁ : (⟨(x : Q), hxD⟩ : commutator Q) ∈ C₁ := by
    rw [hC₁, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.2
  exact ⟨⟨⟨(x : Q), hxD⟩, hxC₁⟩, Subtype.ext rfl⟩

section G2Two


theorem g2TwoCentThreeSolvable_holds :
    G2TwoCentThreeSolvable := by
  intro K _ _ hK g hg3 hg1
  obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK
  obtain ⟨F₀⟩ := Item812Res8.nonempty_commutator_g2_two_equiv hK (Subgroup.topEquiv.trans E)
  let F : ↥(commutator ↥(adjointGroup .G2 K)) ≃* U33G := F₀
  have hidx : (commutator ↥(adjointGroup .G2 K)).index = 2 :=
    Item8KFacts2Proof.index_commutator_g2_two hK
  haveI : (commutator ↥(adjointGroup .G2 K)).Normal := Subgroup.commutator_normal ⊤ ⊤
  have hgD : g ∈ commutator ↥(adjointGroup .G2 K) :=
    Item8KFacts2Proof.mem_of_pow_three_of_not_dvd_index (by rw [hidx]; omega) hg3
  refine isSolvable_centralizer_of_commutator hgD ?_
  set g' : commutator ↥(adjointGroup .G2 K) := ⟨g, hgD⟩ with hg'
  have hu3 : F g' ^ 3 = 1 := by
    rw [← map_pow]
    have : g' ^ 3 = 1 := Subtype.ext (by simpa [hg'] using hg3)
    rw [this, map_one]
  have hu1 : F g' ≠ 1 := fun h =>
    hg1 (congrArg Subtype.val (F.injective (h.trans (map_one F).symm)))
  haveI hs := isSolvable_centralizer_u33 hu3 hu1
  let f : ↥(Subgroup.centralizer ({g'} : Set (commutator ↥(adjointGroup .G2 K)))) →*
      ↥(Subgroup.centralizer ({F g'} : Set U33G)) :=
    (F.toMonoidHom.comp (Subgroup.centralizer ({g'} : Set _)).subtype).codRestrict _ fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp x.2
      show F x * F g' = F g' * F x
      rw [← map_mul, ← map_mul, this]
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro x y hxy
  have h1 : F (x : commutator ↥(adjointGroup .G2 K)) = F (y : commutator ↥(adjointGroup .G2 K)) :=
    congrArg Subtype.val hxy
  exact Subtype.ext (F.injective h1)

end G2Two

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
