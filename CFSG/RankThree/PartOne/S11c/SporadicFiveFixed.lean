module

public import CFSG.RankThree.PartOne.S11c.HNProps
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit
public import CFSG.RankThree.PartOne.KS.NoPlane
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.Blueprint.NativeSporadic (Carrier IsSporadic SporadicRep)

@[expose] def NoFiveFixedPSU3 (A : Type) [Group A] : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* A) → ∀ Λ : Subgroup (MulAut T), IsElementaryAbelian 5 Λ → Nat.card Λ = 5 ^ 2 →
      ∀ β ∈ Λ, ∀ K : Subgroup T, FiveFixedPSU3 β K → False

@[expose] def Co1FiveFixed : Prop := NoFiveFixedPSU3 (Carrier .Co1)

@[expose] def LyFiveFixed : Prop := NoFiveFixedPSU3 (Carrier .Ly)

theorem commute_of_conj_fixed {T : Type} [Group T] {b : T} {K : Subgroup T}
    (hK : ∀ x ∈ K, MulAut.conj b x = x) : ∀ x ∈ K, b * x = x * b := by
  intro x hx
  have h := hK x hx
  rw [MulAut.conj_apply] at h
  calc b * x = (b * x * b⁻¹) * b := by group
    _ = x * b := by rw [h]

theorem noFiveFixedPSU3_of_bad {A : Type} [Group A]
    (hinner : ∀ (T : Type) [Group T] [Finite T], T ≃* A → ∀ α : MulAut T, α ^ 5 = 1 →
      ∃ b : T, MulAut.conj b = α)
    (hbad : ∀ (T : Type) [Group T] [Finite T], T ≃* A → ∀ b : T, orderOf b = 5 →
      ∀ K : Subgroup T, (∀ x ∈ K, b * x = x * b) → Nat.card K ≠ 126000) :
    NoFiveFixedPSU3 A := by
  intro T _ _ hs hnab ⟨eT⟩ Λ _ _ β _ K hfix
  obtain ⟨hord, ⟨hKle, -⟩, hmodel⟩ := hfix
  have hβ5 : β ^ 5 = 1 := by rw [← hord]; exact pow_orderOf_eq_one β
  obtain ⟨b, hb⟩ := hinner T eT β hβ5
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    have := hs
    exact conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab)
  have hbord : orderOf b = 5 := by
    have h1 := orderOf_injective (MulAut.conj : T →* MulAut T) hinj b
    rw [hb] at h1
    rw [← h1]
    exact hord
  have hKc : ∀ x ∈ K, b * x = x * b := by
    refine commute_of_conj_fixed fun x hx => ?_
    rw [hb]
    exact hKle hx
  exact hbad T eT b hbord K hKc (CFSG.RankThree.Classical.unitary_three_five_model K hmodel).1

theorem noFiveFixedPSU3_of_twoPart {A : Type} [Group A] {k : ℕ} (hk : k < 16)
    (hinner : ∀ (T : Type) [Group T] [Finite T], T ≃* A → ∀ α : MulAut T, α ^ 5 = 1 →
      ∃ b : T, MulAut.conj b = α)
    (hcent : ∀ (T : Type) [Group T] [Finite T], T ≃* A → CentralizerTwoPartLe T 5 k) :
    NoFiveFixedPSU3 A := by
  refine noFiveFixedPSU3_of_bad hinner ?_
  intro T _ _ eT b hb K hKc hcard
  have h16 : 2 ^ 4 ∣ Nat.card K := by rw [hcard]; norm_num
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 2 h16
  have hS2 : IsPGroup 2 S := IsPGroup.of_card hS
  have hS'2 : IsPGroup 2 (S.map K.subtype) := hS2.map K.subtype
  have hS'card : Nat.card (S.map K.subtype) = 16 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hS]
    norm_num
  have hS'le : S.map K.subtype ≤ centralizer ({b} : Set T) := by
    rintro _ ⟨y, _, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hKc (y : T) y.2).symm
  have := hcent T eT b hb (S.map K.subtype) hS'2 hS'le
  omega

theorem noFiveFixedPSU3_of_not_sq_dvd {A : Type} [Group A]
    (h : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
      T ≃* A → ¬ 5 ^ 2 ∣ Nat.card (MulAut T)) : NoFiveFixedPSU3 A := by
  intro T _ _ hs hnab ⟨eT⟩ Λ _ hΛ _ _ _ _
  have := hs
  have hdvd := Subgroup.card_subgroup_dvd_card Λ
  rw [hΛ] at hdvd
  exact h T hnab eT hdvd

theorem noFiveFixedPSU3_of_noPlaneAut {A : Type} [Group A] (h : NoPlaneAut A) :
    NoFiveFixedPSU3 A :=
  noFiveFixedPSU3_of_not_sq_dvd fun T _ _ _ hnab eT =>
    h T hnab ⟨eT⟩ 5 Nat.prime_five (by norm_num)

section Model

variable {A : Type} [Group A] {M : Type*} [Group M] [Finite M] {P R : Subgroup M}

omit [Finite M] in
theorem noFiveFixedPSU3_of_data (hPR : P ≤ R) (e : A ≃* P) {k : ℕ} (hk : k < 16)
    (hinner : ∀ (T : Type) [Group T] [Finite T], T ≃* A → ∀ α : MulAut T, α ^ 5 = 1 →
      ∃ b : T, MulAut.conj b = α)
    (hb : ∀ y ∈ P, orderOf y = 5 → ∀ R2 : Subgroup M, IsPGroup 2 R2 →
      R2 ≤ R ⊓ centralizer ({y} : Set M) → Nat.card R2 ≤ k) : NoFiveFixedPSU3 A :=
  noFiveFixedPSU3_of_twoPart hk hinner
    (fun _ _ _ eT => centralizerTwoPartLe_of_native (P.subtype.comp (eT.trans e).toMonoidHom)
      (P.subtype_injective.comp (eT.trans e).injective) (fun t => ((eT.trans e) t).2) hPR hb)

theorem noFiveFixedPSU3_of_model (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P)
    (e : A ≃* P) {k : ℕ} (hk : k < 16)
    (hb : ∀ y ∈ P, orderOf y = 5 → ∀ R2 : Subgroup M, IsPGroup 2 R2 →
      R2 ≤ R ⊓ centralizer ({y} : Set M) → Nat.card R2 ≤ k) : NoFiveFixedPSU3 A :=
  noFiveFixedPSU3_of_data h.le e hk
    (fun T _ _ eT α hα =>
      exists_inner_of_pow_eq_one h hidx Nat.prime_five (by norm_num) (eT.trans e) α hα) hb

theorem noFiveFixedPSU3_of_model_card (h : AutModel P R) (hidx : Nat.card R ≤ 2 * Nat.card P)
    (e : A ≃* P)
    (hb : ∀ y ∈ P, orderOf y = 5 → ∀ R2 : Subgroup M, R2 ≤ R ⊓ centralizer ({y} : Set M) →
      Nat.card R2 ≠ 126000) : NoFiveFixedPSU3 A :=
  noFiveFixedPSU3_of_bad
    (fun T _ _ eT α hα =>
      exists_inner_of_pow_eq_one h hidx Nat.prime_five (by norm_num) (eT.trans e) α hα)
    (fun T _ _ eT b hbo K hKc hcard => by
      let φ : T →* M := P.subtype.comp (eT.trans e).toMonoidHom
      have hφ : Function.Injective φ := P.subtype_injective.comp (eT.trans e).injective
      have hle : K.map φ ≤ R ⊓ centralizer ({φ b} : Set M) := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨h.le ((eT.trans e) x).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← map_mul, ← map_mul, hKc x hx]
      exact hb (φ b) ((eT.trans e) b).2 (by rw [orderOf_injective φ hφ, hbo]) (K.map φ) hle
        (by rw [Subgroup.card_map_of_injective hφ]; exact hcard))

end Model

theorem card_ne_of_lines_cent {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R Q : Subgroup M} (hPR : P ≤ R) {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i))) {N : ℕ}
    (hrep : ∀ j, ∃ i, (∃ g ∈ R, centralizer ({xs j} : Set M) =
        centralizer ({g * xs i * g⁻¹} : Set M)) ∧
      ∀ R2 : Subgroup M, R2 ≤ R ⊓ centralizer ({xs i} : Set M) → Nat.card R2 ≠ N) :
    ∀ y ∈ P, orderOf y = p → ∀ R2 : Subgroup M, R2 ≤ R ⊓ centralizer ({y} : Set M) →
      Nat.card R2 ≠ N := by
  intro y hyP hord R2 hle
  obtain ⟨g, hgP, j, hcent⟩ := exists_conj_line hp hSyl hlines hyP hord
  obtain ⟨i, ⟨g', hg'R, hg'⟩, hgood⟩ := hrep j
  have hcR : g * g' ∈ R := R.mul_mem (hPR hgP) hg'R
  let R3 : Subgroup M := R2.map (MulAut.conj (g * g')⁻¹).toMonoidHom
  have hR3le : R3 ≤ R ⊓ centralizer ({xs i} : Set M) := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrR, hrC⟩ := hle hr
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · show (g * g')⁻¹ * r * (g * g')⁻¹⁻¹ ∈ R
      exact R.mul_mem (R.mul_mem (R.inv_mem hcR) hrR) (by simpa using hcR)
    · have hrC' : r ∈ centralizer ({y} : Set M) := hrC
      have hyr : r * y = y * r := Subgroup.mem_centralizer_singleton_iff.mp hrC'
      have h1 : (g⁻¹ * r * g) ∈ centralizer ({g⁻¹ * y * g} : Set M) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g⁻¹ * r * g) * (g⁻¹ * y * g) = g⁻¹ * (r * y) * g := by group
          _ = g⁻¹ * (y * r) * g := by rw [hyr]
          _ = (g⁻¹ * y * g) * (g⁻¹ * r * g) := by group
      rw [hcent, hg', Subgroup.mem_centralizer_singleton_iff] at h1
      show ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹) * xs i = xs i * ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹)
      calc ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹) * xs i
          = g'⁻¹ * ((g⁻¹ * r * g) * (g' * xs i * g'⁻¹)) * g' := by group
        _ = g'⁻¹ * ((g' * xs i * g'⁻¹) * (g⁻¹ * r * g)) * g' := by rw [h1]
        _ = xs i * ((g * g')⁻¹ * r * (g * g')⁻¹⁻¹) := by group
  have hcard : Nat.card R3 = Nat.card R2 :=
    Subgroup.card_map_of_injective (MulAut.conj (g * g')⁻¹).injective
  rw [← hcard]
  exact hgood R3 hR3le

structure FiveFixedInputs : Prop where
  m11 : NoFiveFixedPSU3 (Carrier .M11)
  m12 : NoFiveFixedPSU3 (Carrier .M12)
  m22 : NoFiveFixedPSU3 (Carrier .M22)
  m23 : NoFiveFixedPSU3 (Carrier .M23)
  m24 : NoFiveFixedPSU3 (Carrier .M24)
  j1 : NoFiveFixedPSU3 (Carrier .J1)
  j2 : NoFiveFixedPSU3 (Carrier .J2)
  j3 : NoFiveFixedPSU3 (Carrier .J3)
  j4 : NoFiveFixedPSU3 (Carrier .J4)
  hs : NoFiveFixedPSU3 (Carrier .HS)
  mcl : NoFiveFixedPSU3 (Carrier .McL)
  he : NoFiveFixedPSU3 (Carrier .He)
  ru : NoFiveFixedPSU3 (Carrier .Ru)
  suz : NoFiveFixedPSU3 (Carrier .Suz)
  on : NoFiveFixedPSU3 (Carrier .ONan)
  co1 : Co1FiveFixed
  co2 : NoFiveFixedPSU3 (Carrier .Co2)
  co3 : NoFiveFixedPSU3 (Carrier .Co3)
  ly : LyFiveFixed
  th : NoFiveFixedPSU3 (Carrier .Th)
  fi22 : SectionsForceEvenRankFour (Carrier .Fi22)
  fi23 : SectionsForceEvenRankFour (Carrier .Fi23)
  fi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime)
  b : SectionsForceEvenRankFour (Carrier .B)
  m : SimplePresentationMSectionsForceEvenRankFour

theorem fiveFixedSporadicOnlyHN_of_inputs (h : FiveFixedInputs) : FiveFixedSporadicOnlyHN := by
  intro H _ _ hH X hX Λ hΛ hΛc β hβ K hK hspor
  obtain ⟨s, ⟨e⟩⟩ := hspor
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
  have hnab := hX.2.2
  have hrank : CFSG.Assembly.evenRank H ≤ 3 := by
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    exact hH
  have byLocal : NoFiveFixedPSU3 (Carrier s) → IsSporadic (X ⧸ Subgroup.center X) .HN :=
    fun hs => (hs _ hsimple hnab ⟨e⟩ Λ hΛ hΛc β hβ K hK).elim
  have bySection : SectionsForceEvenRankFour (Carrier s) →
      IsSporadic (X ⧸ Subgroup.center X) .HN := fun hsec => by
    have h4 := hsec H X (Subgroup.center X) ⟨e⟩
    omega
  cases s
  · exact byLocal h.m11
  · exact byLocal h.m12
  · exact byLocal h.m22
  · exact byLocal h.m23
  · exact byLocal h.m24
  · exact byLocal h.j1
  · exact byLocal h.j2
  · exact byLocal h.j3
  · exact byLocal h.j4
  · exact byLocal h.hs
  · exact byLocal h.mcl
  · exact byLocal h.he
  · exact byLocal h.ru
  · exact byLocal h.suz
  · exact byLocal h.on
  · exact byLocal h.co1
  · exact byLocal h.co2
  · exact byLocal h.co3
  · exact bySection h.fi22
  · exact bySection h.fi23
  · exact bySection h.fi24
  · exact ⟨e⟩
  · exact byLocal h.ly
  · exact byLocal h.th
  · exact bySection h.b
  · have h4 := h.m H X (Subgroup.center X) (X ⧸ Subgroup.center X) hnab ⟨MulEquiv.refl _⟩ ⟨e⟩
    omega

end CFSG.RankThree.PartOne.HNRed
