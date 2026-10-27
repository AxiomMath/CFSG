module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.GH74.GLS.IVK.Proofs2.GHInvQuasi

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

namespace Hering129HLift

theorem exists_centralizer_rep {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {t g : Y} (ht : t ^ 3 = 1) (hgt : g⁻¹ * t * g * t⁻¹ ∈ N) :
    ∃ c : Y, g⁻¹ * c ∈ N ∧ c * t = t * c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A : Subgroup Y := Subgroup.zpowers t
  have hA : IsPGroup 3 A := by
    have : Nat.card A ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one ht
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card A ∣ 3 ^ 1 by simpa using this)
    exact IsPGroup.of_card (n := k) hk'
  let α : A →* MulAut Y := (MulAut.conj : Y →* MulAut Y).comp A.subtype
  have hα : ∀ (a : A) (x : Y), α a x = (a : Y) * x * (a : Y)⁻¹ := fun a x => rfl
  have hcomm : ∀ a : A, QuotientGroup.mk (s := N) (a : Y) * QuotientGroup.mk g =
      QuotientGroup.mk g * QuotientGroup.mk (a : Y) := by
    rintro ⟨a, ha⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h1 : (QuotientGroup.mk (s := N) t) * QuotientGroup.mk g =
        QuotientGroup.mk g * QuotientGroup.mk t := by
      have h2 : (QuotientGroup.mk (s := N) (g⁻¹ * t * g * t⁻¹)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hgt
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
      have h3 : (QuotientGroup.mk (s := N) g)⁻¹ * QuotientGroup.mk t * QuotientGroup.mk g =
          QuotientGroup.mk t := by
        calc _ = ((QuotientGroup.mk (s := N) g)⁻¹ * QuotientGroup.mk t * QuotientGroup.mk g *
              (QuotientGroup.mk t)⁻¹) * QuotientGroup.mk t := by group
          _ = QuotientGroup.mk t := by rw [h2, one_mul]
      calc QuotientGroup.mk (s := N) t * QuotientGroup.mk g
          = QuotientGroup.mk g * ((QuotientGroup.mk g)⁻¹ * QuotientGroup.mk t *
              QuotientGroup.mk g) := by group
        _ = _ := by rw [h3]
    have h4 : Commute (QuotientGroup.mk (s := N) t) (QuotientGroup.mk g) := h1
    have := (h4.zpow_left m).eq
    simpa [QuotientGroup.mk_zpow] using this
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA α N hN
    g).2 (fun a x hx => by
      rw [hα]
      have h5 : QuotientGroup.mk (s := N) (g⁻¹ * x) = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h5
      have h6 : QuotientGroup.mk (s := N) x = QuotientGroup.mk g := by
        have := congrArg (fun z => QuotientGroup.mk (s := N) g * z) h5
        simpa using this
      apply (QuotientGroup.eq_one_iff _).mp
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h6, hcomm a]
      group)
  refine ⟨c, hc, ?_⟩
  have := hfix ⟨t, Subgroup.mem_zpowers t⟩
  rw [hα] at this
  simp only at this
  calc c * t = (t * c * t⁻¹) * t := by rw [this]
    _ = t * c := by group

theorem map_centralizer_eq {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {t : Y} (ht : t ^ 3 = 1) :
    (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer ({(QuotientGroup.mk' N t)} : Set (Y ⧸ N)) := by
  ext w
  induction w using QuotientGroup.induction_on with
  | H z =>
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyz⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      rw [← hyz]
      change (QuotientGroup.mk' N y) * (QuotientGroup.mk' N t) =
        (QuotientGroup.mk' N t) * (QuotientGroup.mk' N y)
      rw [← map_mul, ← map_mul, hy]
    · intro hz
      rw [Subgroup.mem_centralizer_singleton_iff] at hz
      have h1 : z⁻¹ * t * z * t⁻¹ ∈ N := by
        rw [← QuotientGroup.eq_one_iff]
        have : (QuotientGroup.mk' N z) * (QuotientGroup.mk' N t) =
            (QuotientGroup.mk' N t) * (QuotientGroup.mk' N z) := hz
        change (QuotientGroup.mk' N) (z⁻¹ * t * z * t⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc (QuotientGroup.mk' N z)⁻¹ * QuotientGroup.mk' N t * QuotientGroup.mk' N z *
            (QuotientGroup.mk' N t)⁻¹
            = (QuotientGroup.mk' N z)⁻¹ * (QuotientGroup.mk' N z * QuotientGroup.mk' N t) *
              (QuotientGroup.mk' N t)⁻¹ := by rw [this]; group
          _ = 1 := by group
      obtain ⟨c, hc, hct⟩ := exists_centralizer_rep N hN ht h1
      refine ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr hct, ?_⟩
      change QuotientGroup.mk' N c = QuotientGroup.mk z
      exact (QuotientGroup.eq.mpr hc).symm

theorem mem_of_mul_mem_of_pow_three {H : Type} [Group H] (X : Subgroup H) [X.Normal]
    {n x c : H} (hx : x ∈ X) (hc : c = n * x) (hc3 : c ^ 3 = 1)
    (hn : ∃ k : ℕ, n ^ (2 ^ k) = 1) : c ∈ X := by
  obtain ⟨k, hk⟩ := hn
  have h1 : (QuotientGroup.mk' X n) ^ 3 = 1 := by
    have : QuotientGroup.mk' X c = QuotientGroup.mk' X n := by
      have hx1 : QuotientGroup.mk' X x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hc, map_mul, hx1, mul_one]
    rw [← this, ← map_pow, hc3, map_one]
  have h2 : (QuotientGroup.mk' X n) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have h3 : orderOf (QuotientGroup.mk' X n) ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  have h4 : Nat.gcd 3 (2 ^ k) = 1 := by
    have : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    exact this
  rw [h4] at h3
  have h5 : QuotientGroup.mk' X n = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hnX : n ∈ X := (QuotientGroup.eq_one_iff n).mp h5
  rw [hc]
  exact X.mul_mem hnX hx

theorem solvable_normal_le_center {Q : Type} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] (hM : Group.IsSolvable M) : M ≤ Subgroup.center Q := by
  haveI := hM
  obtain ⟨hperf, hsimple, hnonab⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  haveI : (M.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (M.map π) with h | h
  · intro m hm
    have : π m ∈ M.map π := Subgroup.mem_map_of_mem π hm
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff m).mp this
  · exfalso
    let f : M →* Q ⧸ Subgroup.center Q := π.comp M.subtype
    have hf : Function.Surjective f := by
      intro w
      have : w ∈ M.map π := by rw [h]; trivial
      obtain ⟨m, hm, rfl⟩ := this
      exact ⟨⟨m, hm⟩, rfl⟩
    haveI : Group.IsSolvable (Q ⧸ Subgroup.center Q) := solvable_of_surjective hf
    haveI : Group.IsPerfect Q := hperf
    haveI : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
    exact Group.IsPerfect.not_isSolvable _ ‹_›


theorem isQuasisimple_quot_theta {X Q : Type} [Group X] [Finite X] [Group Q]
    (hX : Group.IsPerfect X) (φ : X →* Q) (hφ : Function.Surjective φ)
    (hQ : CFSG.IsQuasisimple Q) (hker : φ.ker ≤ aschbacherSolvableCore 3 X) :
    CFSG.IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθsol, hθchar, -, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 X with hθ
  haveI : θ.Characteristic := hθchar
  haveI : θ.Normal := inferInstance
  haveI := hθsol
  haveI : (θ.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hsolv : Group.IsSolvable (θ.map φ) := solvable_of_surjective (φ.subgroupMap_surjective θ)
  have hZ : θ.map φ ≤ Subgroup.center Q := solvable_normal_le_center hQ _ hsolv
  have hθle : θ ≤ (Subgroup.center Q).comap φ := fun x hx => hZ (Subgroup.mem_map_of_mem φ hx)
  let ρ : X ⧸ θ →* Q ⧸ Subgroup.center Q := QuotientGroup.map θ (Subgroup.center Q) φ hθle
  have hρ : Function.Surjective ρ := by
    intro w
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := hφ q
    exact ⟨QuotientGroup.mk x, rfl⟩
  haveI : Group.IsPerfect X := hX
  haveI : Group.IsPerfect (X ⧸ θ) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective θ)
  have hcen : ρ.ker ≤ Subgroup.center (X ⧸ θ) := by
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [MonoidHom.mem_ker] at hw
    change (QuotientGroup.mk (φ x) : Q ⧸ Subgroup.center Q) = 1 at hw
    have hx : φ x ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).mp hw
    rw [Subgroup.mem_center_iff]
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    have hxy : φ y * φ x = φ x * φ y := Subgroup.mem_center_iff.mp hx (φ y)
    have hmem : (y * x)⁻¹ * (x * y) ∈ θ := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hxy]
      group
    exact QuotientGroup.eq.mpr hmem
  exact GH74.GLS.IVK.GHInv.isQuasisimple_of_perfect_cover inferInstance ρ hρ hQ.2.1 hQ.2.2 hcen

theorem center_eq_bot_of_simple {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem center_sq_quot_theta {X Q : Type} [Group X] [Finite X] [Group Q]
    (φ : X →* Q) (hφ : Function.Surjective φ) (hQ : CFSG.IsQuasisimple Q)
    (hker : φ.ker ≤ aschbacherSolvableCore 3 X) (hQ2 : ∀ z ∈ Subgroup.center Q, z ^ 2 = 1) :
    ∀ w ∈ Subgroup.center (X ⧸ aschbacherSolvableCore 3 X), w ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθsol, hθchar, -, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  set θ := aschbacherSolvableCore 3 X with hθ
  haveI : θ.Characteristic := hθchar
  haveI : θ.Normal := inferInstance
  haveI := hθsol
  haveI : (θ.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hsolv : Group.IsSolvable (θ.map φ) := solvable_of_surjective (φ.subgroupMap_surjective θ)
  have hZ : θ.map φ ≤ Subgroup.center Q := solvable_normal_le_center hQ _ hsolv
  have hθle : θ ≤ (Subgroup.center Q).comap φ := fun x hx => hZ (Subgroup.mem_map_of_mem φ hx)
  let ρ : X ⧸ θ →* Q ⧸ Subgroup.center Q := QuotientGroup.map θ (Subgroup.center Q) φ hθle
  have hρ : Function.Surjective ρ := by
    intro w
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := hφ q
    exact ⟨QuotientGroup.mk x, rfl⟩
  intro w hw
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  have h1 : ρ (QuotientGroup.mk x) ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := by
    rw [Subgroup.mem_center_iff]
    intro v
    obtain ⟨u, rfl⟩ := hρ v
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw u]
  rw [center_eq_bot_of_simple hQ.2.1 hQ.2.2, Subgroup.mem_bot] at h1
  have h2 : φ x ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : x ^ 2 ∈ θ := by
    apply hker
    rw [MonoidHom.mem_ker, map_pow]
    exact hQ2 _ h2
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr h3

end Hering129HLift

end CFSG.RankThree.PartTwo.Sec12
