module

public import CFSG.GroupTheory.SolvableFactorizedHall
public import CFSG.LocalAnalysis.ABGTheoremB.V5Tools
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

private theorem s1611e3_factorization_prime_pow_mul {p : ℕ} (hp : p.Prime) (k m : ℕ)
    (hm : ¬ p ∣ m) (hm0 : m ≠ 0) : (p ^ k * m).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow_self hp]
  simp [Nat.factorization_eq_zero_of_not_dvd hm]

private theorem s1611e3_eq_two_pow_mul_three_pow (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by
  have h32 : (Nat.factorization 3) 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have h23 : (Nat.factorization 2) 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  apply Nat.eq_of_factorization_eq hn (by positivity)
  intro p
  by_cases hp : p.Prime
  · by_cases h2 : p = 2
    · subst h2
      simp [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_two.factorization, h32]
    · by_cases h3 : p = 3
      · subst h3
        simp [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_three.factorization, h23]
      · have hnd : ¬ p ∣ n := fun hd => by
          rcases h p hp hd with rfl | rfl
          · exact h2 rfl
          · exact h3 rfl
        have h0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
        rw [h0]
        have h2' : (Nat.factorization 2) p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd
            (fun hd => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
        have h3' : (Nat.factorization 3) p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd
            (fun hd => h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
        simp [Nat.factorization_mul, Nat.factorization_pow, h2', h3']
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem s1611e3_mul_eq_of_card {G : Type} [Group G] [Finite G]
    {A T Y : Subgroup G} (hAY : A ≤ Y) (hTY : T ≤ Y) (hAT : A ⊓ T = ⊥)
    (hcard : Nat.card A * Nat.card T = Nat.card Y) :
    (A : Set G) * (T : Set G) = (Y : Set G) := by
  have hsub : (A : Set G) * (T : Set G) ⊆ (Y : Set G) := by
    rintro _ ⟨a, ha, t, ht, rfl⟩
    exact Y.mul_mem (hAY ha) (hTY ht)
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2) ((A : Set G) ×ˢ (T : Set G)) := by
    rintro ⟨a, t⟩ ⟨ha, ht⟩ ⟨a', t'⟩ ⟨ha', ht'⟩ h
    simp only at h
    have h1 : a'⁻¹ * a = t' * t⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * t) * t⁻¹ := by group
        _ = a'⁻¹ * (a' * t') * t⁻¹ := by rw [h]
        _ = t' * t⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ A ⊓ T :=
      ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ T.mul_mem ht' (T.inv_mem ht)⟩
    rw [hAT, Subgroup.mem_bot] at h2
    have hae : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [h2, mul_one]
    have hte : t = t' := by
      rw [hae] at h
      exact mul_left_cancel h
    rw [hae, hte]
  have hncard : ((A : Set G) * (T : Set G)).ncard = (Y : Set G).ncard := by
    rw [← Set.image_mul_prod, hinj.ncard_image, Set.ncard_prod, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcard
  exact Set.eq_of_subset_of_ncard_le hsub hncard.ge (Set.toFinite _)

theorem s1611e3_lift_three {H Q : Type} [Group H] [Finite H] [Group Q] (f : H →* Q)
    (hf : Function.Surjective f) (h3 : ¬ 3 ∣ Nat.card ↥f.ker) {S : Subgroup H}
    (hS2 : IsPGroup 2 ↥S) (hSK : CFSG.Quasithin.IsSylowIn 2 (S ⊓ f.ker) f.ker)
    {Xbar : Subgroup Q} (hX3 : IsPGroup 3 ↥Xbar) (hXnc : ¬ IsCyclic ↥Xbar)
    (hXexp : ∀ x ∈ Xbar, x ^ 3 = 1)
    (hperm : (Xbar : Set Q) * (S.map f : Set Q) = (S.map f : Set Q) * (Xbar : Set Q)) :
    ∃ X : Subgroup H, IsPGroup 3 ↥X ∧ ¬ IsCyclic ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      (X : Set H) * (S : Set H) = (S : Set H) * (X : Set H) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite Q := Finite.of_surjective f hf
  set K : Subgroup H := f.ker with hK
  haveI hKnormal : K.Normal := by rw [hK]; exact f.normal_ker
  set Q₀ : Subgroup H := S ⊓ K with hQ₀
  set Wbar : Subgroup Q := Xbar ⊔ S.map f with hWbar
  have hWbar_coe : (Wbar : Set Q) = (Xbar : Set Q) * (S.map f : Set Q) :=
    CFSG.ABGTheoremB.V56.coe_sup_of_permutable hperm
  have hQ0S : Q₀ ≤ S := by rw [hQ₀]; exact inf_le_left
  have hQ0K : Q₀ ≤ K := by rw [hQ₀]; exact inf_le_right
  have hSK' : IsSylowIn 2 Q₀ K := by rw [hQ₀]; exact hSK
  have hS_norm : S ≤ normalizer (Q₀ : Set H) := by
    rw [hQ₀]
    have h1 : S ≤ normalizer (S : Set H) ⊓ normalizer (K : Set H) :=
      le_inf Subgroup.le_normalizer (Subgroup.le_normalizer_of_normal (H := K))
    exact h1.trans Subgroup.inf_normalizer_le_normalizer_inf
  set Y : Subgroup H := Wbar.comap f ⊓ normalizer (Q₀ : Set H) with hY
  have hS_Y : S ≤ Y := by
    rw [hY]
    exact le_inf
      (fun s hs => Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem f hs)))
      hS_norm
  have hfr : normalizer (Q₀ : Set H) ⊔ K = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (p := 2) (N := K) hSK'.toSylow
    rwa [IsSylowIn.coe_toSylow, Subgroup.map_subgroupOf_eq_of_le hQ0K] at h
  have huniv : (Set.univ : Set H) = (normalizer (Q₀ : Set H) : Set H) * (K : Set H) := by
    rw [← Subgroup.coe_top, ← hfr, Subgroup.mul_normal]
  have hYle : Y ≤ Wbar.comap f := by rw [hY]; exact inf_le_left
  have hWbar_le_fY : Wbar ≤ Y.map f := by
    intro w hw
    have hw' : w ∈ (Xbar : Set Q) * (S.map f : Set Q) := by rw [← hWbar_coe]; exact hw
    obtain ⟨x, hx, s, hs, rfl⟩ := hw'
    obtain ⟨s₀, hs₀, hs₀f⟩ := Subgroup.mem_map.mp hs
    obtain ⟨y, hy⟩ := hf x
    have hyW : y * s₀ ∈ Wbar.comap f := by
      rw [Subgroup.mem_comap, map_mul, hy, hs₀f]
      exact Wbar.mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hs)
    have hmem : y * s₀ ∈ (Set.univ : Set H) := trivial
    rw [huniv] at hmem
    obtain ⟨n, hn, k, hk, hnk⟩ := hmem
    have hk1 : f k = 1 := MonoidHom.mem_ker.mp (hK ▸ hk)
    have hnW : n ∈ Wbar.comap f := by
      rw [Subgroup.mem_comap]
      have h1 : f n * f k = f (y * s₀) := by
        rw [← map_mul]
        exact congrArg f hnk
      rw [hk1, mul_one] at h1
      rw [h1]; exact Subgroup.mem_comap.mp hyW
    refine Subgroup.mem_map.mpr ⟨n, ?_, ?_⟩
    · rw [hY]; exact ⟨hnW, hn⟩
    · have h1 : f n = f (y * s₀) := by
        have h2 : f n * f k = f (y * s₀) := by
          rw [← map_mul]
          exact congrArg f hnk
        rw [hk1, mul_one] at h2
        exact h2
      rw [h1, map_mul, hy, hs₀f]
  have hfY : Y.map f = Wbar := by
    refine le_antisymm ?_ hWbar_le_fY
    calc Y.map f ≤ (Wbar.comap f).map f := Subgroup.map_mono hYle
      _ = Wbar := Subgroup.map_comap_eq_self_of_surjective hf Wbar
  have hK_le_comap : K ≤ Wbar.comap f := by
    intro k hk
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp (hK ▸ hk)]
    exact Wbar.one_mem
  have hYinfK : Y ⊓ K = K ⊓ normalizer (Q₀ : Set H) := by
    rw [hY]
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_comap]
    constructor
    · rintro ⟨⟨-, hxN⟩, hxK⟩; exact ⟨hxK, hxN⟩
    · rintro ⟨hxK, hxN⟩; exact ⟨⟨hK_le_comap hxK, hxN⟩, hxK⟩
  set Nb : Subgroup H := Y ⊓ K with hNb
  have hNbY : Nb ≤ Y := hNb.le.trans inf_le_left
  have hNbK : Nb ≤ K := hNb.le.trans inf_le_right
  have hQ0Nb : Q₀ ≤ Nb := by rw [hNb]; exact le_inf (hQ0S.trans hS_Y) hQ0K
  have hNb_norm : Nb ≤ normalizer (Q₀ : Set H) := by
    rw [hNb]; exact inf_le_left.trans (by rw [hY]; exact inf_le_right)
  haveI : (Q₀.subgroupOf Nb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0Nb).2 hNb_norm
  have hQ0Nb_p : IsPGroup 2 (Q₀.subgroupOf Nb) := hSK'.isPGroup.comap_subtype
  haveI := hQ0Nb_p.isNilpotent
  have hdvd : Q₀.relIndex Nb ∣ Q₀.relIndex K :=
    ⟨Nb.relIndex K, (Subgroup.relIndex_mul_relIndex (H := Q₀) (K := Nb) (L := K) hQ0Nb hNbK).symm⟩
  have hoddNb : ¬ 2 ∣ Q₀.relIndex Nb := fun h2 => hSK'.not_dvd_relIndex (h2.trans hdvd)
  have hodd' : Odd (Q₀.relIndex Nb) :=
    Nat.not_even_iff_odd.mp (fun he => hoddNb (even_iff_two_dvd.mp he))
  have hcard_quot : Nat.card (↥Nb ⧸ (Q₀.subgroupOf Nb)) = Q₀.relIndex Nb := by
    rw [show Q₀.relIndex Nb = (Q₀.subgroupOf Nb).index from rfl, Subgroup.index_eq_card]
  have hodd_card : Odd (Nat.card (↥Nb ⧸ (Q₀.subgroupOf Nb))) := by
    rw [hcard_quot]; exact hodd'
  haveI : Group.IsSolvable (↥Nb ⧸ (Q₀.subgroupOf Nb)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd_card
  haveI hNbsolv : Group.IsSolvable ↥Nb :=
    Group.isSolvable_of_subgroup_quotient (Q₀.subgroupOf Nb)
  have h3Nb : ¬ 3 ∣ Nat.card ↥Nb :=
    fun h => h3 (h.trans (Subgroup.card_dvd_of_le hNbK))
  haveI hNbsub : Group.IsSolvable ↥(Nb.subgroupOf Y) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNbY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNbY).symm.surjective
  have hdisj_ws : Xbar ⊓ S.map f = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Xbar (S.map f) hX3 (hS2.map f))
  have hWbar_card : Nat.card ↥Wbar = Nat.card ↥Xbar * Nat.card ↥(S.map f) :=
    CFSG.ABGTheoremB.V56.card_sup_of_permutable hperm hdisj_ws
  obtain ⟨a, ha⟩ := hX3.exists_card_eq
  obtain ⟨b, hb⟩ := (hS2.map f).exists_card_eq
  haveI hWbarsolv : Group.IsSolvable ↥Wbar :=
    TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_three Nat.prime_two
      (by rw [hWbar_card, ha, hb])
  let g : ↥Y →* ↥Wbar :=
    (f.comp Y.subtype).codRestrict Wbar
      (fun y => Subgroup.mem_comap.mp (Subgroup.mem_inf.mp y.2).1)
  have hgker : g.ker = Nb.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      rw [Subgroup.mem_subgroupOf, hNb, Subgroup.mem_inf]
      refine ⟨y.2, ?_⟩
      have h2 : f (y : H) = 1 := congrArg Subtype.val h1
      rw [hK]; exact MonoidHom.mem_ker.mpr h2
    · intro h1
      rw [Subgroup.mem_subgroupOf, hNb, Subgroup.mem_inf] at h1
      apply Subtype.ext
      show f (y : H) = 1
      exact MonoidHom.mem_ker.mp (hK ▸ h1.2)
  have hgsurj : Function.Surjective g := by
    intro w
    have hw : (w : Q) ∈ Y.map f := by rw [hfY]; exact w.2
    obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp hw
    exact ⟨⟨y, hy⟩, Subtype.ext hyf⟩
  haveI : Group.IsSolvable ↥g.ker := hgker.symm ▸ hNbsub
  haveI hYsolv : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])
  have hY_card2 : Nat.card ↥Y = Nat.card ↥Wbar * Nat.card ↥Nb := by
    have h1 := Subgroup.card_ker_mul_card_range g
    have hker : Nat.card ↥g.ker = Nat.card ↥Nb := by
      rw [hgker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNbY).toEquiv
    have hrange : g.range = ⊤ := g.range_eq_top_of_surjective hgsurj
    rw [hker, hrange, Subgroup.card_top] at h1
    rw [← h1]; ring
  set d : ℕ := Q₀.relIndex Nb with hd
  have hNb_card : Nat.card ↥Nb = d * Nat.card ↥Q₀ := by
    have h := Subgroup.relIndex_mul_card (H := Q₀) (K := Nb)
    rw [inf_of_le_left hQ0Nb] at h
    exact h.symm
  have hQ0rel : Q₀.relIndex S = Nat.card ↥(S.map f) := by
    rw [hQ₀, show S ⊓ K = K ⊓ S from inf_comm S K, Subgroup.inf_relIndex_right, hK,
      Subgroup.relIndex_ker]
  have hS_card : Nat.card ↥S = Nat.card ↥(S.map f) * Nat.card ↥Q₀ := by
    have h1 := Subgroup.relIndex_mul_card (H := Q₀) (K := S)
    rw [inf_of_le_left hQ0S, hQ0rel] at h1
    exact h1.symm
  have hY_decomp : Nat.card ↥Y = Nat.card ↥S * (Nat.card ↥Xbar * d) := by
    rw [hY_card2, hWbar_card, hNb_card, hS_card]
    ring
  have hd_ne0 : d ≠ 0 := by
    intro h0
    have := hNb_card
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this
  have hXbar_odd : Odd (Nat.card ↥Xbar) := by rw [ha]; exact Odd.pow (by norm_num : Odd 3)
  have hd_odd : Odd d := Nat.not_even_iff_odd.mp (fun he => hoddNb (even_iff_two_dvd.mp he))
  have hnot2 : ¬ 2 ∣ Nat.card ↥Xbar * d := fun hh =>
    (Nat.not_even_iff_odd.mpr (hXbar_odd.mul hd_odd)) (even_iff_two_dvd.mpr hh)
  have hS2Y_card : Nat.card ↥S = 2 ^ (Nat.card ↥Y).factorization 2 := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have hm_ne : Nat.card ↥Xbar * d ≠ 0 := mul_ne_zero (Nat.card_pos.ne') hd_ne0
    have hkey : (Nat.card ↥Y).factorization 2 = k := by
      rw [hY_decomp, hk,
        s1611e3_factorization_prime_pow_mul Nat.prime_two k _ hnot2 hm_ne]
    rw [hkey, ← hk]
  have hS2Y : IsSylowIn 2 S Y := isSylowIn_of_card_eq hS_Y hS2Y_card
  have hd_dvd_Nb : d ∣ Nat.card ↥Nb := by rw [hNb_card]; exact dvd_mul_right d _
  have hd_dvd_K : d ∣ Nat.card ↥K := hd_dvd_Nb.trans (Subgroup.card_dvd_of_le hNbK)
  have h3d : ¬ 3 ∣ d := fun hh => h3 (hh.trans hd_dvd_K)
  have hWbar_fact3 : (Nat.card ↥Wbar).factorization 3 = a := by
    rw [hWbar_card, ha, hb, s1611e3_factorization_prime_pow_mul Nat.prime_three a _ ?_ ?_]
    · intro hh
      have h1 := Nat.prime_three.dvd_of_dvd_pow hh
      norm_num at h1
    · exact pow_ne_zero b (by norm_num)
  have hY_fact3 : (Nat.card ↥Y).factorization 3 = a := by
    have h1 : (Nat.card ↥Y).factorization 3 =
        (Nat.card ↥Wbar).factorization 3 + (Nat.card ↥Nb).factorization 3 := by
      rw [hY_card2, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply]
    rw [h1, hWbar_fact3, Nat.factorization_eq_zero_of_not_dvd h3Nb, add_zero]
  set SY : Subgroup ↥Y := S.subgroupOf Y with hSY
  have hSYcard_eq : Nat.card ↥SY = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_Y).toEquiv
  have hSY_pi : IsPiSubgroup (fun q : Nat.Primes => q.val = 2 ∨ q.val = 3) SY := by
    intro q hq
    left
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have hq' : q.val ∣ 2 ^ k := by rw [← hk, ← hSYcard_eq]; exact hq
    exact (Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).mp (q.2.dvd_of_dvd_pow hq')
  obtain ⟨H23, hH23hall, hSH23⟩ :=
    SolvableHall.solvable_hall_containment hYsolv
      (fun q : Nat.Primes => q.val = 2 ∨ q.val = 3) SY hSY_pi
  have hH23prime : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥H23 → p = 2 ∨ p = 3 := by
    intro p hp hpdvd
    exact hH23hall.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hpdvd
  have hH23_card : Nat.card ↥H23 =
      2 ^ (Nat.card ↥H23).factorization 2 * 3 ^ (Nat.card ↥H23).factorization 3 :=
    s1611e3_eq_two_pow_mul_three_pow _ (Nat.card_pos.ne') hH23prime
  have hfac2 : (Nat.card ↥H23).factorization 2 = (Nat.card ↥Y).factorization 2 :=
    hH23hall.factorization_eq_card_of_mem Nat.prime_two (Or.inl rfl)
  have hfac3 : (Nat.card ↥H23).factorization 3 = (Nat.card ↥Y).factorization 3 :=
    hH23hall.factorization_eq_card_of_mem Nat.prime_three (Or.inr rfl)
  have hSYcard : Nat.card ↥SY = 2 ^ (Nat.card ↥H23).factorization 2 := by
    rw [hSYcard_eq, hS2Y_card, hfac2]
  have hSYsyl : IsSylowIn 2 SY H23 := isSylowIn_of_card_eq hSH23 hSYcard
  obtain ⟨T0⟩ : Nonempty (Sylow 3 ↥H23) := Sylow.nonempty
  set X1Y : Subgroup ↥Y := (T0 : Subgroup ↥H23).map H23.subtype with hX1Y
  have hX1Ycard : Nat.card ↥X1Y = 3 ^ (Nat.card ↥H23).factorization 3 := by
    rw [hX1Y, Subgroup.card_map_of_injective H23.subtype_injective, Sylow.card_eq_multiplicity]
  have hX1Ysyl : IsSylowIn 3 X1Y H23 :=
    isSylowIn_of_card_eq (Subgroup.map_subtype_le _) hX1Ycard
  have hdisj_X1S : X1Y ⊓ SY = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X1Y SY
      hX1Ysyl.isPGroup hSYsyl.isPGroup)
  have hcard_prod : Nat.card ↥X1Y * Nat.card ↥SY = Nat.card ↥H23 := by
    rw [hX1Ycard, hSYcard]
    rw [Nat.mul_comm (3 ^ (Nat.card ↥H23).factorization 3)
      (2 ^ (Nat.card ↥H23).factorization 2)]
    exact hH23_card.symm
  have hprod1 : (X1Y : Set ↥Y) * (SY : Set ↥Y) = (H23 : Set ↥Y) :=
    s1611e3_mul_eq_of_card (Subgroup.map_subtype_le _) hSH23 hdisj_X1S hcard_prod
  have hprod2 : (SY : Set ↥Y) * (X1Y : Set ↥Y) = (H23 : Set ↥Y) :=
    s1611e3_mul_eq_of_card hSH23 (Subgroup.map_subtype_le _) (by rw [inf_comm]; exact hdisj_X1S)
      (by rw [mul_comm]; exact hcard_prod)
  set X : Subgroup H := X1Y.map Y.subtype with hX
  have hXle : X ≤ Y := Subgroup.map_subtype_le _
  have hXcoe : (X : Set H) = Y.subtype '' (X1Y : Set ↥Y) := rfl
  have hScoe : (S : Set H) = Y.subtype '' (SY : Set ↥Y) := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hS_Y hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  have hXS : (X : Set H) * (S : Set H) = (S : Set H) * (X : Set H) := by
    rw [hXcoe, hScoe, ← Set.image_mul, ← Set.image_mul, hprod1, hprod2]
  have hX3p : IsPGroup 3 X := hX1Ysyl.isPGroup.map Y.subtype
  have hH23fact3 : (Nat.card ↥H23).factorization 3 = a := by rw [hfac3, hY_fact3]
  have hX_card : Nat.card ↥X = 3 ^ a := by
    have h1 : Nat.card ↥X = Nat.card ↥X1Y := (Nat.card_congr
      (Subgroup.equivMapOfInjective X1Y Y.subtype Y.subtype_injective).toEquiv).symm
    rw [h1, hX1Ycard, hH23fact3]
  have hXK : X ⊓ K = ⊥ := by
    have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥K) := by
      rw [hX_card]
      have hCK : Nat.Coprime 3 (Nat.card ↥K) :=
        (Nat.prime_three.coprime_iff_not_dvd).mpr h3
      exact hCK.pow_left a
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  let fX : X →* X.map f :=
    (f.comp X.subtype).codRestrict (X.map f) (fun x => Subgroup.mem_map_of_mem f x.2)
  have hfXinj : Function.Injective fX := by
    intro p q hpq
    have h1 : f (p : H) = f (q : H) := congrArg Subtype.val hpq
    have hmem : (p : H)⁻¹ * q ∈ X ⊓ K := by
      refine ⟨X.mul_mem (X.inv_mem p.2) q.2, ?_⟩
      rw [hK]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h1, inv_mul_cancel])
    rw [hXK, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem)
  have hfXsurj : Function.Surjective fX := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  let eX : X ≃* X.map f := MulEquiv.ofBijective fX ⟨hfXinj, hfXsurj⟩
  have hXf_le : X.map f ≤ Wbar := by
    calc X.map f ≤ Y.map f := Subgroup.map_mono hXle
      _ = Wbar := hfY
  have hXf_card : Nat.card ↥(X.map f) = Nat.card ↥X :=
    (Nat.card_congr eX.toEquiv).symm
  have hXf_syl : IsSylowIn 3 (X.map f) Wbar := by
    refine isSylowIn_of_card_eq hXf_le ?_
    rw [hXf_card, hX_card, hWbar_fact3]
  have hXbar_le_W : Xbar ≤ Wbar := by rw [hWbar]; exact le_sup_left
  have hXbar_syl : IsSylowIn 3 Xbar Wbar := by
    refine isSylowIn_of_card_eq hXbar_le_W ?_
    rw [ha, hWbar_fact3]
  haveI : Finite (Sylow 3 ↥Wbar) :=
    Finite.of_injective (fun S : Sylow 3 ↥Wbar => (S : Set ↥Wbar))
      (fun S T h => Sylow.ext (by ext x; exact Set.ext_iff.mp h x))
  let eSyl : ((X.map f).subgroupOf Wbar) ≃* (Xbar.subgroupOf Wbar) :=
    Sylow.equiv hXf_syl.toSylow hXbar_syl.toSylow
  let e : X ≃* Xbar :=
    eX.trans ((Subgroup.subgroupOfEquivOfLe hXf_le).symm.trans
      (eSyl.trans (Subgroup.subgroupOfEquivOfLe hXbar_le_W)))
  have hXexpFin : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : X) ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      simpa using hXexp (e ⟨x, hx⟩ : Q) (e ⟨x, hx⟩).2
    simpa using congrArg (fun z : X => (z : H)) h1
  have hXncFin : ¬ IsCyclic ↥X := by
    intro hcyc
    letI := hcyc
    exact hXnc (isCyclic_of_surjective e.toMonoidHom e.surjective)
  exact ⟨X, hX3p, hXncFin, hXexpFin, hXS⟩

private theorem s1611e3_permutes_subgroupOf {G : Type} [Group G] {A B N : Subgroup G}
    (hA : A ≤ N) (hB : B ≤ N) (h : Permutes A B) :
    Permutes (A.subgroupOf N) (B.subgroupOf N) := by
  unfold Permutes at h ⊢
  ext x
  rw [Set.mem_mul, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have ha' : (a : G) ∈ A := ha
    have hb' : (b : G) ∈ B := hb
    have hx : (x : G) ∈ (B : Set G) * (A : Set G) := by
      rw [← h]
      exact ⟨(a : G), ha', (b : G), hb', by simpa using congrArg Subtype.val hab⟩
    obtain ⟨b', hb', a', ha', hbax⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr
      ⟨⟨b', hB hb'⟩, Subgroup.mem_subgroupOf.mpr hb', ⟨a', hA ha'⟩,
        Subgroup.mem_subgroupOf.mpr ha', Subtype.ext hbax⟩
  · rintro ⟨b, hb, a, ha, hba⟩
    have ha' : (a : G) ∈ A := ha
    have hb' : (b : G) ∈ B := hb
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [h]
      exact ⟨(b : G), hb', (a : G), ha', by simpa using congrArg Subtype.val hba⟩
    obtain ⟨a', ha', b', hb', habx⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr
      ⟨⟨a', hA ha'⟩, Subgroup.mem_subgroupOf.mpr ha', ⟨b', hB hb'⟩,
        Subgroup.mem_subgroupOf.mpr hb', Subtype.ext habx⟩

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_case9_lift_three (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Hyp125 D V₀ V) (hnd : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V))
    {Xbar : Subgroup (MulAut (Vtil V₀ V hV))} (hXM : Xbar ≤ Mbar D.M V₀ V hV)
    (hX3 : IsPGroup 3 ↥Xbar) (hXnc : ¬ IsCyclic ↥Xbar) (hXexp : ∀ x ∈ Xbar, x ^ 3 = 1)
    (hperm : Permutes Xbar (barSub V₀ V hV D.T)) :
    ∃ X : Subgroup G, X ≤ D.M ∧ IsPGroup 3 ↥X ∧ ¬ IsCyclic ↥X ∧ (∀ x ∈ X, x ^ 3 = 1) ∧
      Permutes X D.T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let cT : Subgroup G := F11.CTilde D.M V₀ V
  have hCT_le_M : cT ≤ D.M := fun g hg =>
    ((mem_cTilde_iff hV h.pairFacts.le_normalizer).1 hg).1
  let f : ↥D.M →* ↥Mb := MonoidHom.codRestrict
    ((actTil V₀ V hV).comp (Subgroup.inclusion hM)) Mb (fun m => by
      have h1 : actTil V₀ V hV (Subgroup.inclusion hM m) ∈ barSub V₀ V hV D.M :=
        actTil_mem_barSub V₀ V hV m.2 (hM m.2)
      simpa [Mb, Mbar] using h1)
  have hker : f.ker = cT.subgroupOf D.M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      refine (mem_cTilde_iff hV h.pairFacts.le_normalizer).2 ⟨m.2, hM m.2, ?_⟩
      have h2 : (f m : ↥Mb).val = 1 := congrArg Subtype.val h1
      change actTil V₀ V hV (Subgroup.inclusion hM m) = 1
      simpa [f] using h2
    · intro h1
      obtain ⟨-, h2, h3⟩ := (mem_cTilde_iff hV h.pairFacts.le_normalizer).1 h1
      apply Subtype.ext
      show actTil V₀ V hV (Subgroup.inclusion hM m) = 1
      have h4 : (⟨m.1, h2⟩ : stabTil V₀ V) = Subgroup.inclusion hM m := Subtype.ext rfl
      rw [← h4]
      exact h3
  have h3' : ¬ 3 ∣ Nat.card ↥f.ker := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT_le_M).toEquiv]
    exact hnd
  have hCT_normal : (cT.subgroupOf D.M).Normal := hker ▸ (inferInstance : f.ker.Normal)
  have hM_norm_CT : D.M ≤ normalizer (cT : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCT_le_M).1 hCT_normal
  have hCT_syl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ cT) cT :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hCT_le_M hM_norm_CT
  have hf : Function.Surjective f := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg, hgx⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
    refine ⟨⟨(g : G), hg⟩, Subtype.ext ?_⟩
    show actTil V₀ V hV (Subgroup.inclusion hM ⟨(g : G), hg⟩) = φ
    have h4 : Subgroup.inclusion hM ⟨(g : G), hg⟩ = g := Subtype.ext rfl
    rw [h4, hgx]
  have hS2 : IsPGroup 2 (D.T.subgroupOf D.M) := D.sylowM.isPGroup.comap_subtype (K := D.M)
  have hSK : IsSylowIn 2 ((D.T.subgroupOf D.M) ⊓ f.ker) f.ker := by
    rw [hker]
    have hA : (D.T.subgroupOf D.M) ⊓ cT.subgroupOf D.M = (D.T ⊓ cT).subgroupOf D.M := by
      ext m
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hA]
    refine isSylowIn_of_card_eq (fun m hm => (Subgroup.mem_inf.mp hm).2) ?_
    rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hCT_le_M : D.T ⊓ cT ≤ D.M)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCT_le_M).toEquiv]
    exact hCT_syl.card_eq
  let Xb : Subgroup ↥Mb := Xbar.subgroupOf Mb
  have hSf : (D.T.subgroupOf D.M).map f = (barSub V₀ V hV D.T).subgroupOf Mb := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine Subgroup.mem_subgroupOf.2 ?_
      refine (mem_barSub V₀ V hV D.T (f m).val).2
        ⟨Subgroup.inclusion hM m, ?_, rfl⟩
      simpa using (Subgroup.mem_subgroupOf.mp hm)
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨g, hg, hgx⟩ := (mem_barSub V₀ V hV D.T (x : MulAut (Vtil V₀ V hV))).1 hx
      refine ⟨⟨(g : G), D.sylowM.le hg⟩, Subgroup.mem_subgroupOf.mpr hg, ?_⟩
      apply Subtype.ext
      show actTil V₀ V hV (Subgroup.inclusion hM ⟨(g : G), D.sylowM.le hg⟩) =
        (x : MulAut (Vtil V₀ V hV))
      have h4 : Subgroup.inclusion hM ⟨(g : G), D.sylowM.le hg⟩ = g := Subtype.ext rfl
      rw [h4, hgx]
  have hX3' : IsPGroup 3 ↥Xb :=
    hX3.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  have hXnc' : ¬ IsCyclic ↥Xb := fun hcyc =>
    hXnc ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hXM)).mp hcyc)
  have hXexp' : ∀ x ∈ Xb, x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    exact hXexp (x : MulAut (Vtil V₀ V hV)) (Subgroup.mem_subgroupOf.mp hx)
  have hperm' : Permutes Xb ((D.T.subgroupOf D.M).map f) := by
    rw [hSf]
    exact s1611e3_permutes_subgroupOf hXM (barSub_mono V₀ V hV D.sylowM.le) hperm
  obtain ⟨X', hX'3, hX'nc, hX'exp, hX'perm⟩ :=
    s1611e3_lift_three f hf h3' hS2 hSK hX3' hXnc' hXexp' hperm'
  refine ⟨X'.map D.M.subtype, Subgroup.map_subtype_le _, hX'3.map D.M.subtype, ?_, ?_, ?_⟩
  · intro hcyc
    letI := hcyc
    have h1 : IsCyclic ↥X' :=
      (MulEquiv.isCyclic
        (Subgroup.equivMapOfInjective X' D.M.subtype D.M.subtype_injective)).mpr hcyc
    exact hX'nc h1
  · rintro x ⟨x', hx', rfl⟩
    have h1 : ((x' : ↥D.M)) ^ 3 = 1 := hX'exp x' hx'
    show ((x' : ↥D.M) : G) ^ 3 = 1
    simpa using congrArg (fun z : ↥D.M => (z : G)) h1
  · have hDT : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) = (D.T : Set G) :=
      congrArg (fun H : Subgroup G => (H : Set G))
        (Subgroup.map_subgroupOf_eq_of_le D.sylowM.le)
    have hXcoe : (X'.map D.M.subtype : Set G) = D.M.subtype '' (X' : Set ↥D.M) := rfl
    have hScoe : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) =
        D.M.subtype '' (D.T.subgroupOf D.M : Set ↥D.M) := rfl
    show (X'.map D.M.subtype : Set G) * (D.T : Set G) =
      (D.T : Set G) * (X'.map D.M.subtype : Set G)
    rw [hXcoe, ← hDT, hScoe, ← Set.image_mul, ← Set.image_mul, hX'perm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
