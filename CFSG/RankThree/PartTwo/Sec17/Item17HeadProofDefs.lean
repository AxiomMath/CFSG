module

public import CFSG.RankThree.PartTwo.Sec17.Item17TailData
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofFour
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

section Statement168

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def omega168 (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Set (Subgroup G) :=
  {V | V = inSubgroup (oResidual 2) (deltaZero A LB V) ∧ V ∈ scriptY A ∧
    ∀ Y₃ ∈ scriptY3 A LB, V ≤ Y₃ → Y₃ ∈ scriptYs A LB}

@[expose] noncomputable def Item168 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  (scriptY0 A LB = ∅ → scriptY3 A LB = scriptYs A LB ∧
      ∃ n : ℕ, 2 < n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) →
    ∀ V ∈ omega168 A LB, ∀ Y ∈ scriptY3 A LB, V ≤ Y →
      ∃ N ∈ scriptY1Star A LB, (∀ Y₃ ∈ scriptY3 A LB, Y ≤ Y₃ → Y₃ ≤ N) ∧
        ∀ S ∈ scriptQPiStar A LB N (piOf 2),
          S ∈ scriptQPiStar A LB ⊤ (piOf 2) ∧ (∀ Y₁ ∈ scriptY1 A LB, S ≤ Y₁ → Y₁ ≤ N) ∧
            delta A LB (Subgroup.normalizer (S : Set G)) ≤ N ∧
            Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) ≤
              Subgroup.normalizer (N : Set G)

end Statement168

@[expose] def Claim1718 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ∀ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
        w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) →
          oPrimeResidualOf 3 ((S ⊓ Y₀) ⊔ (S ⊓ Y₀).map (MulAut.conj w).toMonoidHom) ≠ ⊥

@[expose] def Claim1719W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
        w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
          w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G)

@[expose] def Claim1715Meets : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → MeetsY4 A (lB A) L Y₀

@[expose] def Claim1715Prime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e →
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e → e = 1

@[expose] def Claim1715A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      TransOmegaThree A c → A ≤ Y₀

@[expose] def KFact174 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ X : Subgroup G, X = delta A (lB A) X → ¬ 3 ∣ Nat.card X →
      ¬ Group.IsSolvable X → ∃ K ∈ thetaComponentsIn X, ∃ n : ℕ,
        CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n

@[expose] def Claim174 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ X : Subgroup G, X = delta A (lB A) X → ¬ 3 ∣ Nat.card X →
      ∀ K ∈ thetaComponentsIn X,
        (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
        ∀ Y ∈ scriptY1Star A (lB A), ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G) →
          ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2),
            ∃ Y' ∈ scriptY1 A (lB A), K ≤ Y' ∧ S ≤ Y'

end CFSG.RankThree.PartTwo.Sec17

namespace CFSG.RankThree.PartTwo.Sec17.HeadProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

section Conj

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem map_oPrimeResidualOf (φ : G ≃* G) (p : ℕ) (X : Subgroup G) :
    (oPrimeResidualOf p X).map φ.toMonoidHom = oPrimeResidualOf p (X.map φ.toMonoidHom) := by
  rw [oPrimeResidualOf_eq_closure, oPrimeResidualOf_eq_closure, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow] at hk
    exact φ.injective (hk.trans φ.map_one.symm)

theorem map_conj_delta_le {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) (Y : Subgroup G) :
    (delta A (lB A) Y).map (MulAut.conj g).toMonoidHom ≤
      delta A (lB A) (Y.map (MulAut.conj g).toMonoidHom) := by
  rw [delta, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun Q hQ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_delta (rank3II_14_4_5 (isNaturalFamily_lB A) hg hQ.1) (Subgroup.map_mono hQ.2)

theorem map_conj_delta {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) (Y : Subgroup G) :
    (delta A (lB A) Y).map (MulAut.conj g).toMonoidHom =
      delta A (lB A) (Y.map (MulAut.conj g).toMonoidHom) := by
  refine le_antisymm (map_conj_delta_le hg Y) ?_
  have h := map_conj_delta_le (inv_mem hg) (Y.map (MulAut.conj g).toMonoidHom)
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
  have h' := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h
  rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h'

omit [Finite G] in
theorem map_conj_mem_scriptY {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY A) : Y.map (MulAut.conj g).toMonoidHom ∈ scriptY A := by
  refine ⟨fun htop => hY.1 ?_, ?_⟩
  · have h := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) htop
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one,
      Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h
  · calc A = A.map (MulAut.conj g).toMonoidHom := (Late.map_conj_eq_of_mem_normalizer hg).symm
      _ ≤ (Subgroup.normalizer (Y : Set G)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hY.2
      _ = _ := Subgroup.map_equiv_normalizer_eq Y (MulAut.conj g)

theorem map_conj_mem_scriptY3 {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY3 A (lB A)) :
    Y.map (MulAut.conj g).toMonoidHom ∈ scriptY3 A (lB A) := by
  obtain ⟨⟨hYY, hO2⟩, hYΔ⟩ := hY
  refine ⟨⟨map_conj_mem_scriptY hg hYY, ?_⟩, ?_⟩
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact fun h => hO2 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h)
  · rw [← map_conj_delta hg, ← hYΔ]

theorem map_conj_mem_scriptY1 {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY1 A (lB A)) :
    Y.map (MulAut.conj g).toMonoidHom ∈ scriptY1 A (lB A) :=
  ⟨map_conj_mem_scriptY3 hg hY.1, by
    rw [← map_oPrimeResidualOf, hY.2, Subgroup.map_bot]⟩

theorem map_conj_mem_scriptY3Star {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY3Star A (lB A)) :
    Y.map (MulAut.conj g).toMonoidHom ∈ scriptY3Star A (lB A) :=
  maximal_map_conj (W := Subgroup.normalizer (A : Set G))
    (fun _ hS _ hw => map_conj_mem_scriptY3 hw hS) hY hg

theorem map_conj_mem_scriptY1Star {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY1Star A (lB A)) :
    Y.map (MulAut.conj g).toMonoidHom ∈ scriptY1Star A (lB A) :=
  maximal_map_conj (W := Subgroup.normalizer (A : Set G))
    (fun _ hS _ hw => map_conj_mem_scriptY1 hw hS) hY hg

theorem map_conj_mem_scriptQPi {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y Q : Subgroup G} {π : Set Nat.Primes} (hQ : Q ∈ scriptQPi A (lB A) Y π) :
    Q.map (MulAut.conj g).toMonoidHom ∈
      scriptQPi A (lB A) (Y.map (MulAut.conj g).toMonoidHom) π :=
  ⟨⟨rank3II_14_4_5 (isNaturalFamily_lB A) hg hQ.1.1, Subgroup.map_mono hQ.1.2⟩,
    fun q hq => hQ.2 q (by rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hq)⟩

theorem map_conj_mem_scriptQPiStar {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y Q : Subgroup G} {π : Set Nat.Primes} (hQ : Q ∈ scriptQPiStar A (lB A) Y π) :
    Q.map (MulAut.conj g).toMonoidHom ∈
      scriptQPiStar A (lB A) (Y.map (MulAut.conj g).toMonoidHom) π := by
  refine ⟨map_conj_mem_scriptQPi hg hQ.prop, fun R hR hle => ?_⟩
  have hR' := map_conj_mem_scriptQPi (inv_mem hg) hR
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one] at hR'
  have hQR : Q ≤ R.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one] at this
  have hRQ := hQ.2 hR' hQR
  have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hRQ
  rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at this

end Conj

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_prime {Q K : Subgroup G}
    (h : ∀ r : ℕ, r.Prime → ∃ R : Subgroup G, R ≤ Q ⊓ K ∧
      Nat.card R = r ^ (Nat.card Q).factorization r) : Q ≤ K := by
  have hdvd : Nat.card Q ∣ Nat.card (Q ⊓ K : Subgroup G) := by
    rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
    intro r hr
    obtain ⟨R, hRle, hRcard⟩ := h r hr
    have := Subgroup.card_dvd_of_le hRle
    rw [hRcard] at this
    exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp this
  have hle := Nat.le_of_dvd Nat.card_pos hdvd
  have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q ⊓ K ≤ Q) hle
  exact heq ▸ inf_le_right

theorem exists_invariant_sylow {A Q : Subgroup G} (hA : IsPGroup 3 A)
    (hQ : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) {r : ℕ} (hr : r.Prime) :
    ∃ R : Subgroup G, R ≤ Q ∧ IsPGroup r R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      Nat.card R = r ^ (Nat.card Q).factorization r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 r
    hA hQ (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ))
  refine ⟨(S : Subgroup Q).map Q.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _,
    fun a ha => ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [← hS ⟨a, ha⟩]
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, Sylow.card_eq_multiplicity]

theorem le_of_forall_invariant_pGroup {A Q K : Subgroup G} (hA : IsPGroup 3 A)
    (hQ : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (h : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, R ≤ Q → IsPGroup r R →
      A ≤ Subgroup.normalizer (R : Set G) → R ≤ K) : Q ≤ K := by
  refine le_of_forall_prime fun r hr => ?_
  obtain ⟨R, hRQ, hRr, hAR, hcard⟩ := exists_invariant_sylow hA hQ hAQ hr
  exact ⟨R, le_inf hRQ (h r hr R hRQ hRr hAR), hcard⟩

theorem le_of_commutator_le {p : ℕ} (hp : p.Prime) {B R K : Subgroup G} (hB : IsPGroup p B)
    (hR : ¬ p ∣ Nat.card R) (hBR : B ≤ Subgroup.normalizer (R : Set G)) (h1 : ⁅R, B⁆ ≤ K)
    (h2 : R ⊓ Subgroup.centralizer (B : Set G) ≤ K) : R ≤ K := by
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization p hp B
    R hB hR hBR]
  exact sup_le h1 h2

end Coprime

section FourGroups

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_card_four {U : Subgroup G} (hU4 : Nat.card U = 4) {a b c d : G} (ha : a ∈ U)
    (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ∀ v ∈ U, v = a ∨ v = b ∨ v = c ∨ v = d := by
  classical
  intro v hv
  by_contra hne
  push Not at hne
  obtain ⟨hva, hvb, hvc, hvd⟩ := hne
  set s : Finset G := {a, b, c, d, v} with hs
  have hscard : s.card = 5 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair hvd.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hcd, hvc.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hbc, hbd, hvb.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac, had, hva.symm⟩
  have hsub : (s : Set G) ⊆ (U : Set G) := by
    intro x hx
    simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [ha, hb, hc, hd, hv]
  have hle : (s : Set G).ncard ≤ (U : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hscard, ← Nat.card_coe_set_eq] at hle
  change 5 ≤ Nat.card U at hle
  omega

theorem exists_fpf_of_fourGroupsMinus {A U : Subgroup G} (hA : ∀ a ∈ A, a ^ 3 = 1)
    (hU : U ∈ fourGroupsMinus A) : ∃ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ = u → u = 1 := by
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := hU.1.1.2.2
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hU.1.2.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hU2 : ∀ x ∈ U, x ^ 2 = 1 := hU.1.2.1.2
  have hU4 : Nat.card U = 4 := hU.1.2.2
  have hinv : ∀ x ∈ U, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2 x hx)
  obtain ⟨a, haA, u₀, hu₀U, hau₀⟩ : ∃ a ∈ A, ∃ u₀ ∈ U, a * u₀ * a⁻¹ ≠ u₀ := by
    by_contra hall
    push Not at hall
    have hAC : A ≤ Subgroup.centralizer (U : Set G) := fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := hall a ha u hu
      calc u * a = a * u * a⁻¹ * a := by rw [this]
        _ = a * u := by group
    have hbot : ⁅U, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hAC
    rw [← hU.2] at hbot
    rw [hbot, Subgroup.card_bot] at hU4
    omega
  refine ⟨a, haA, fun u hu hau => ?_⟩
  by_contra hu1
  have ha3 : a ^ 3 = 1 := hA a haA
  have hu₀1 : u₀ ≠ 1 := fun h => hau₀ (by rw [h]; group)
  have hu₀u : u₀ ≠ u := fun h => hau₀ (h ▸ hau)
  set v := a * u₀ * a⁻¹ with hv
  have hvU : v ∈ U := (Subgroup.mem_normalizer_iff.mp (hAU haA) u₀).mp hu₀U
  have hconj_inj : ∀ x y : G, a * x * a⁻¹ = a * y * a⁻¹ → x = y := fun x y h => by
    simpa using h
  have hv1 : v ≠ 1 := fun h => hu₀1 (hconj_inj _ _ (h.trans (by group)))
  have hvu : v ≠ u := fun h => hu₀u (hconj_inj _ _ (h.trans hau.symm))
  have huu₀U : u * u₀ ∈ U := U.mul_mem hu hu₀U
  have huu₀1 : u * u₀ ≠ 1 := fun h => hu₀u (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hinv u hu])
  have huu₀u : u * u₀ ≠ u := fun h => hu₀1 (by
    have := congrArg (u⁻¹ * ·) h
    simpa using this)
  have huu₀u₀ : u * u₀ ≠ u₀ := fun h => hu1 (by
    have := congrArg (· * u₀⁻¹) h
    simpa using this)
  have hvuu₀ : v = u * u₀ := by
    rcases mem_of_card_four hU4 U.one_mem hu hu₀U huu₀U (Ne.symm hu1) hu₀1.symm huu₀1.symm hu₀u.symm
      huu₀u.symm huu₀u₀.symm v hvU with h | h | h | h
    · exact absurd h hv1
    · exact absurd h hvu
    · exact absurd h hau₀
    · exact h
  have h2 : a * (u * u₀) * a⁻¹ = u₀ := by
    calc a * (u * u₀) * a⁻¹ = (a * u * a⁻¹) * (a * u₀ * a⁻¹) := by group
      _ = u * (u * u₀) := by rw [hau, ← hv, hvuu₀]
      _ = u₀ := by rw [← mul_assoc, ← sq, hU2 u hu, one_mul]
  have h4 : a * (a * u₀ * a⁻¹) * a⁻¹ = u₀ := by
    rw [← hv, hvuu₀]
    exact h2
  have h5 : a ^ 3 * u₀ * (a ^ 3)⁻¹ = a * u₀ * a⁻¹ := by
    calc a ^ 3 * u₀ * (a ^ 3)⁻¹ = a * (a * (a * u₀ * a⁻¹) * a⁻¹) * a⁻¹ := by
          rw [show a ^ 3 = a * a * a by rw [pow_three, ← mul_assoc]]
          group
      _ = a * u₀ * a⁻¹ := by rw [h4]
  rw [ha3, one_mul, inv_one, mul_one] at h5
  exact hau₀ h5.symm

theorem le_pCoreOf_two_of_fourGroupsMinus {A X U : Subgroup G} (hA : ∀ a ∈ A, a ^ 3 = 1)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : Group.IsSolvable X)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup G, E ≤ X →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ x ∈ E, x ^ q = 1) → Nat.card E ≤ q ^ 2)
    (hU : U ∈ fourGroupsMinus A) (hUX : U ≤ X) : U ≤ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨a, haA, hfpf⟩ := exists_fpf_of_fourGroupsMinus hA hU
  set σ : MulAut X := X.normalizerMonoidHom ⟨a, hAX haA⟩ with hσ
  have hσx : ∀ x : X, ((σ x : X) : G) = a * x * a⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨a, hAX haA⟩ x
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := hU.1.1.2.2
  set U' : Subgroup X := U.subgroupOf X with hU'
  have hU'c : ∀ x ∈ U', ∀ y ∈ U', x * y = y * x := fun x hx y hy => Subtype.ext
    (show (x : G) * y = y * x from
      congrArg Subtype.val (hU.1.2.1.1.is_comm.comm ⟨(x : G), hx⟩ ⟨(y : G), hy⟩))
  have hU'2 : ∀ x ∈ U', x ^ 2 = 1 := fun x hx => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hU.1.2.1.2 (x : G) hx)
  have hU'4 : Nat.card U' = 4 := by
    rw [hU', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv]
    exact hU.1.2.2
  have hσU' : ∀ x ∈ U', σ x ∈ U' := by
    intro x hx
    rw [hU', Subgroup.mem_subgroupOf, hσx]
    exact (Subgroup.mem_normalizer_iff.mp (hAU haA) x).mp hx
  have hfpf' : ∀ x ∈ U', σ x = x → x = 1 := by
    intro x hx h
    apply Subtype.ext
    rw [Subgroup.coe_one]
    exact hfpf x hx (by rw [← hσx, h])
  have hrank' : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup X,
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ q = 1) → Nat.card E ≤ q ^ 2 := by
    intro q hq hq2 E hEc hEq
    have h := hrank q hq hq2 (E.map X.subtype) (Subgroup.map_subtype_le _) ?_ ?_
    · rwa [Subgroup.card_map_of_injective X.subtype_injective] at h
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hEc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEq x hx, map_one]
  have hle := HeadProof.le_pCore_two_of_fpf hX hrank' σ hU'c hU'2 hU'4 hσU' hfpf'
  intro x hx
  change x ∈ (CFSG.Open.pCore 2 X).map X.subtype
  exact ⟨⟨x, hUX hx⟩, hle hx, rfl⟩

end FourGroups

section Rank

variable {G : Type} [Group G] [Finite G]

theorem card_le_sq_of_pCoreOf_ne_bot (hG : TheoremFourHyp G) {X : Subgroup G}
    (hX2 : CFSG.Open.pCoreOf 2 X ≠ ⊥) (hX3 : ¬ 3 ∣ Nat.card X) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup G, E ≤ X →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ x ∈ E, x ^ q = 1) → Nat.card E ≤ q ^ 2 := by
  intro q hq hq2 E hEX hEc hEq
  have : Fact q.Prime := ⟨hq⟩
  have hEp : IsPGroup q E := fun x => ⟨1, Subtype.ext (by simpa using hEq x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  by_cases hq3 : q = 3
  · subst hq3
    have hk0 : k = 0 := by
      by_contra hk0
      apply hX3
      have h1 : 3 ∣ Nat.card E := by
        rw [hk]
        exact dvd_pow_self 3 hk0
      exact h1.trans (Subgroup.card_dvd_of_le hEX)
    rw [hk, hk0]
    norm_num
  have hq3' : 3 < q := by
    have := hq.two_le
    omega
  set K := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) with hK
  have hK2 : CFSG.Assembly.IsTwoLocal K :=
    ⟨_, hX2, CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X, rfl⟩
  have hEK : E ≤ K := hEX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hEab : CFSG.Assembly.IsElemAbelian q E :=
    ⟨⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩, hEq⟩
  have hbdd1 : BddAbove {k | ∃ F : Subgroup G, F ≤ K ∧ CFSG.Assembly.IsElemAbelian q F ∧
      Nat.card F = q ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro j ⟨F, -, -, hj⟩
    have h1 : j < q ^ j := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    change j ≤ Nat.card G
    omega
  have hk1 : k ≤ CFSG.Assembly.pRank q K := le_csSup hbdd1 ⟨E, hEK, hEab, hk⟩
  have hbdd2 : BddAbove {j | ∃ H : Subgroup G, CFSG.Assembly.IsTwoLocal H ∧
      CFSG.Assembly.pRank q H = j} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    refine csSup_le' ?_
    rintro j ⟨F, -, -, hj⟩
    have h1 : j < q ^ j := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    change j ≤ Nat.card G
    omega
  have hk2 : CFSG.Assembly.pRank q K ≤ CFSG.Assembly.RankThreeEven.localRank q G :=
    le_csSup hbdd2 ⟨K, hK2, rfl⟩
  have hk3 := hG.localRank_lt q hq hq3'
  rw [hk]
  exact Nat.pow_le_pow_right hq.pos (by omega)

end Rank

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem isE27_of_std (h : Sec17Std G A c L Y₀) : IsE27 A :=
  isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE

theorem pow_three_of_std (h : Sec17Std G A c L Y₀) {a : G} (ha : a ∈ A) : a ^ 3 = 1 :=
  h.toSec13Data.isElemAbelian.2 a ha

theorem centralizer_le_M (h : Sec17Std G A c L Y₀) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
  (Subgroup.centralizer_le_normalizer _).trans h.normalizer_le

theorem centralizer_c_le_M (h : Sec17Std G A c L Y₀) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) :=
  (centralizer_singleton_le_normalizer_zpowers c).trans h.normalizer_c_le

theorem le_M_of_mem_scriptQPi_two (h : Sec17Std G A c L Y₀) {R : Subgroup G}
    (hR : R ∈ scriptQPi A (lB A) ⊤ (piOf 2)) : R ≤ Subgroup.normalizer (Y₀ : Set G) := by
  obtain ⟨S, hRS, hS⟩ := Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hR
  exact hRS.trans (h.qStar_le S hS)

theorem M_ne_top (h : Sec17Std G A c L Y₀) : Subgroup.normalizer (Y₀ : Set G) ≠ ⊤ := by
  intro htop
  have hY₀ := h.mem_y0Star.prop
  have : IsSimpleGroup G := h.isSimpleGroup
  rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with h0 | h1
  · apply hY₀.2.2
    rw [eq_bot_iff, ← h0]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀
  · exact hY₀.2.1.1 h1

theorem mem_scriptY1_of_not_le_M (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G} (hY : Y ∈ scriptY3 A (lB A))
    (hM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)) :
    Y ∈ scriptY1 A (lB A) ∧ Group.IsSolvable Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  have hYs : Group.IsSolvable ↥Y := by
    by_contra hns
    exact hM ((h166 Y₀ h.mem_y0Star).2 Y hY hns)
  have hYsc : Y ∈ scriptY A := hY.1.1
  have hYΔ : Y = delta A (lB A) Y := hY.2
  obtain ⟨hdelta, -, -⟩ := rank3II_14_5_lB hA hbot hYsc.2
  set R := pPrimeCoreOf 3 Y with hR
  set C' := xA A ⊓ Y with hC'
  have hDR : deltaZero A (lB A) Y ≤ R :=
    item148Solvable_of_mem_partTwoF h.mem_partTwoF Y hYsc hYs
  have hYRC : Y ≤ C' ⊔ R := by
    calc Y = delta A (lB A) Y := hYΔ
      _ = deltaZero A (lB A) Y ⊔ C' := hdelta
      _ ≤ R ⊔ C' := sup_le_sup_right hDR _
      _ = C' ⊔ R := sup_comm _ _
  have hC'R : C' ≤ Subgroup.normalizer (R : Set G) :=
    inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    have hdvd := h3.trans ((Subgroup.card_dvd_of_le hYRC).trans (card_sup_dvd_card_mul hC'R))
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
        (h1.trans (Subgroup.card_dvd_of_le inf_le_left))
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y) h1
  refine ⟨⟨hY, ?_⟩, hYs⟩
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_eq_bot_iff]
  rintro x ⟨hxY, k, hk⟩
  have hdvd : orderOf (⟨x, hxY⟩ : Y) ∣ Nat.gcd (3 ^ k) (Nat.card Y) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk)))
      (orderOf_dvd_natCard _)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)), Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact congrArg Subtype.val hdvd

theorem exists_pGroup_not_le_M (h : Sec17Std G A c L Y₀) {Q : Subgroup G}
    (hQ : Q ∈ scriptQ A (lB A)) (hQM : ¬ Q ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ ∃ R : Subgroup G, R ≤ Q ∧ IsPGroup r R ∧
      A ≤ Subgroup.normalizer (R : Set G) ∧ ¬ R ≤ Subgroup.normalizer (Y₀ : Set G) := by
  by_contra hall
  push Not at hall
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.2.1
  apply hQM
  refine le_of_forall_invariant_pGroup (isE27_of_std h).isPGroup hQ3 hQ.1.2.2
    fun r hr R hRQ hRr hAR => ?_
  by_cases hr2 : r = 2
  · subst hr2
    exact le_M_of_mem_scriptQPi_two h ⟨⟨mem_scriptQ_of_le hQ hRQ hAR, le_top⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hRr⟩
  by_cases hr3 : r = 3
  · subst hr3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hR1 : R = ⊥ := by
      rcases hRr.card_eq_or_dvd with h1 | h3
      · exact Subgroup.card_eq_one.mp h1
      · exact absurd (h3.trans (Subgroup.card_dvd_of_le hRQ)) hQ3
    rw [hR1]
    exact bot_le
  exact hall r hr hr2 hr3 R hRQ hRr hAR

theorem exists_scriptQZero_not_le_M (h : Sec17Std G A c L Y₀) {Q : Subgroup G}
    (hQ : Q ∈ scriptQ A (lB A)) (hQM : ¬ Q ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ ∃ R : Subgroup G, R ≤ Q ∧ IsPGroup r R ∧
      R ∈ scriptQZero A (lB A) ∧ ¬ R ≤ Subgroup.normalizer (Y₀ : Set G) := by
  obtain ⟨r, hr, hr2, hr3, R, hRQ, hRr, hAR, hRM⟩ := exists_pGroup_not_le_M h hQ hQM
  have : Fact r.Prime := ⟨hr⟩
  have hA3 : IsPGroup 3 A := (isE27_of_std h).isPGroup
  have hR3 : ¬ 3 ∣ Nat.card R := by
    intro h3
    rcases hRr.card_eq_or_dvd with h1 | hr'
    · rw [h1] at h3
      omega
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRr
      rw [hk] at h3
      exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hcomm : ⁅R, A⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.mp hAR
  have hAcomm : A ≤ Subgroup.normalizer ((⁅R, A⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.normalizer_commutator_ge_left A R
  refine ⟨r, hr, hr2, hr3, ⁅R, A⁆, hcomm.trans hRQ, hRr.to_le hcomm,
    ⟨mem_scriptQ_of_le hQ (hcomm.trans hRQ) hAcomm,
      (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three A
        R hA3 hR3 hAR).symm⟩, fun hle => hRM ?_⟩
  exact le_of_commutator_le Nat.prime_three hA3 hR3 hAR hle
    (inf_le_right.trans (centralizer_le_M h))

theorem mem_omega168_of (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) {R : Subgroup G} (hRr : IsPGroup r R) (hR0 : R ∈ scriptQZero A (lB A))
    (hRM : ¬ R ≤ Subgroup.normalizer (Y₀ : Set G)) : R ∈ omega168 A (lB A) := by
  have : Fact r.Prime := ⟨hr⟩
  have hΔ : deltaZero A (lB A) R = R := le_antisymm (deltaZero_le R) (le_deltaZero hR0 le_rfl)
  refine ⟨?_, ⟨fun htop => ?_, hR0.1.1.2.2⟩, fun Y₃ hY₃ hRY => ?_⟩
  · rw [hΔ, inSubgroup_oResidual_eq_closure]
    refine le_antisymm ?_ (Subgroup.closure_le _ |>.mpr fun x hx => hx.1)
    intro x hx
    apply Subgroup.subset_closure
    refine ⟨hx, ?_⟩
    obtain ⟨k, hk⟩ := hRr (⟨x, hx⟩ : R)
    have hdvd : orderOf x ∣ r ^ k := by
      rw [← Subgroup.orderOf_mk (ha := hx)]
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp hdvd
    rw [hj]
    exact Nat.Coprime.pow_left j ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  ·
    have hc3 := h.toSec13Data.orderOf_eq
    obtain ⟨k, hk⟩ := hRr (⟨c, htop ▸ Subgroup.mem_top c⟩ : R)
    have hdvd : orderOf c ∣ r ^ k := by
      rw [← Subgroup.orderOf_mk (ha := htop ▸ Subgroup.mem_top c)]
      exact orderOf_dvd_of_pow_eq_one hk
    rw [hc3] at hdvd
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)).symm
  · have hM' : ¬ Y₃ ≤ Subgroup.normalizer (Y₀ : Set G) := fun hle => hRM (hRY.trans hle)
    exact mem_scriptY1_of_not_le_M h h166 hbot hY₃ hM'

theorem item168_premise (h : Sec17Std G A c L Y₀) :
    scriptY0 A (lB A) = ∅ → scriptY3 A (lB A) = scriptYs A (lB A) ∧
      ∃ n : ℕ, 2 < n ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := fun h0 =>
  ((Set.eq_empty_iff_forall_notMem.mp h0) Y₀ h.mem_y0Star.prop).elim

theorem exists_omega168_le (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G} (hY : Y ∈ scriptY3 A (lB A))
    (hM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)) : ∃ V ∈ omega168 A (lB A), V ≤ Y := by
  obtain ⟨Q, hQ, hQM⟩ : ∃ Q ∈ collectionIn (scriptQ A (lB A)) Y,
      ¬ Q ≤ Subgroup.normalizer (Y₀ : Set G) := by
    by_contra hall
    push Not at hall
    exact hM (hY.2.le.trans (sSup_le hall))
  obtain ⟨r, hr, hr2, hr3, R, hRQ, hRr, hR0, hRM⟩ := exists_scriptQZero_not_le_M h hQ.1 hQM
  exact ⟨R, mem_omega168_of h h166 hbot hr hr2 hr3 hRr hR0 hRM, hRQ.trans hQ.2⟩

theorem mem_qStar_top_of_item168 (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY3 A (lB A)) (hM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G))
    (hmax : ∀ N ∈ scriptY1 A (lB A), Y ≤ N → N = Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
  obtain ⟨V, hV, hVY⟩ := exists_omega168_le h h166 hbot hY hM
  obtain ⟨N, hN, hYN, hNS⟩ := h168 (item168_premise h) V hV Y hY hVY
  have hNY : N = Y := hmax N hN.prop (hYN Y hY le_rfl)
  subst hNY
  exact (hNS S hS).1

end Std

end CFSG.RankThree.PartTwo.Sec17.HeadProof
