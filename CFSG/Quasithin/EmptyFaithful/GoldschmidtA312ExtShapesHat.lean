module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
public import CFSG.Quasithin.Background.A312SporGen

public section

namespace CFSG.Quasithin.A312ExtShapes

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin

theorem normal_card_three_le_center {Q : Type} [Group Q] [Finite Q] (hQ : commutator Q = ⊤)
    (K : Subgroup Q) [K.Normal] (hK : Nat.card K = 3) : K ≤ Subgroup.center Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic K := isCyclic_of_prime_card hK
  have hAut : Nat.card (MulAut K) = 2 := by
    rw [IsCyclic.card_mulAut, hK, Nat.totient_prime Nat.prime_three]
  have hcycAut : IsCyclic (MulAut K) := isCyclic_of_prime_card hAut
  let _ : CommGroup (MulAut K) := IsCyclic.commGroup
  let φ : Q →* MulAut K := MulAut.conjNormal
  have hker : commutator Q ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hQ] at hker
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : φ g = 1 := hker (Subgroup.mem_top g)
  have h2 := congrArg (fun a : MulAut K => ((a ⟨k, hk⟩ : K) : Q)) h1
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc g * k = g * k * g⁻¹ * g := by group
    _ = k * g := by rw [h2]

theorem isHat_of_central_cover {Q : Type} [Group Q] [Finite Q] (hQ : commutator Q = ⊤)
    (σ : Q →* alternatingGroup (Fin 6)) (hσ : Function.Surjective σ) (hker : Nat.card σ.ker = 3) :
    IsHat Q (alternatingGroup (Fin 6)) := by
  have hsimple := Seven.alt6_simple
  obtain ⟨a, b, hab⟩ := Seven.alt6_nonabelian
  have hKle : σ.ker ≤ Subgroup.center Q := normal_card_three_le_center hQ σ.ker hker
  have hcen : Subgroup.center Q = σ.ker := by
    refine le_antisymm (fun z hz => ?_) hKle
    have hz' : σ z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨g, rfl⟩ := hσ h
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) g]
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 6))) with
      h | h
    · rw [h, Subgroup.mem_bot] at hz'
      exact hz'
    · exfalso
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  let e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientKerEquivOfSurjective σ hσ)
  have hnabQ : ∃ x y : Q ⧸ Subgroup.center Q, x * y ≠ y * x :=
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact ⟨⟨Group.isPerfect_def.mpr hQ, e.isSimpleGroup, hnabQ⟩, by rw [hcen]; exact hker, ⟨e⟩⟩

theorem isExt_e2_hat6 {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤) (V : Subgroup A)
    [V.Normal] (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ x ∈ V, x * x = 1)
    (hVcard : Nat.card V = 2 ^ 6) (π : A →* alternatingGroup (Fin 6))
    (hπ : Function.Surjective π) (hVπ : V ≤ π.ker) (hker : Nat.card π.ker = 3 * Nat.card V) :
    IsExt A (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) := by
  let σ : A ⧸ V →* alternatingGroup (Fin 6) := QuotientGroup.lift V π hVπ
  have hσ : Function.Surjective σ := fun a => by
    obtain ⟨x, rfl⟩ := hπ a
    exact ⟨(x : A ⧸ V), rfl⟩
  have : Group.IsPerfect A := Group.isPerfect_def.mpr hA
  have : Group.IsPerfect (A ⧸ V) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)
  have hperf : commutator (A ⧸ V) = ⊤ := Group.isPerfect_def.mp inferInstance
  have hcardA : Nat.card A = Nat.card (A ⧸ V) * Nat.card V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  have hcardA' : Nat.card A = Nat.card (alternatingGroup (Fin 6)) * Nat.card π.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv] at h1
  have hcardQ : Nat.card (A ⧸ V) = Nat.card (alternatingGroup (Fin 6)) * Nat.card σ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσ).toEquiv] at h1
  have hkerσ : Nat.card σ.ker = 3 := by
    have hpos : 0 < Nat.card (alternatingGroup (Fin 6)) * Nat.card V := by
      have := Nat.card_pos (α := alternatingGroup (Fin 6))
      have := Nat.card_pos (α := V)
      positivity
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card (alternatingGroup (Fin 6)) * Nat.card V * Nat.card σ.ker
        = Nat.card (A ⧸ V) * Nat.card V := by rw [hcardQ]; ring
      _ = Nat.card (alternatingGroup (Fin 6)) * (3 * Nat.card V) := by
        rw [← hcardA, hcardA', hker]
      _ = Nat.card (alternatingGroup (Fin 6)) * Nat.card V * 3 := by ring
  have hE2 : IsE2 6 ↥V :=
    PermLat.isElemAbelianOfRank_of_card (fun a b => Subtype.ext (hVc a.1 a.2 b.1 b.2))
      (fun a => Subtype.ext (hVsq a.1 a.2)) hVcard
  exact ⟨V, inferInstance, hE2, isHat_of_central_cover hperf σ hσ hkerσ⟩

theorem isExt_e2_hat6_of_lFamily {G : Type} [Group G] [Finite G] {T B Z A : Subgroup G}
    (hB : B ∈ lFamily T) (hZ : B ⊔ T = Z) (hAZ : A ≤ Z) (hcomm : ⁅Z, Z⁆ ≤ A)
    (hperf : ⁅A, A⁆ = A) (V : Subgroup ↥A) [V.Normal]
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ x ∈ V, x * x = 1)
    (hVcard : Nat.card V = 2 ^ 6) (π : ↥A →* alternatingGroup (Fin 6))
    (hπ : Function.Surjective π) (hVπ : V ≤ π.ker) (hker : Nat.card π.ker = 3 * Nat.card V) :
    IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) := by
  have := Seven.alt6_simple
  have hAperf : commutator ↥A = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
  have hsolv : Group.IsSolvable π.ker := by
    refine A312S.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 6) (b := 1)
      ?_
    rw [hker, hVcard]
    norm_num
  exact isExt_of_eq_subgroup
    (eq_of_perfect_simple_quotient hB hZ hAZ hcomm hperf Seven.alt6_nonabelian π hπ hsolv).symm
    (fun V W _ _ e h => IsE2.of_mulEquiv e h) (fun V W _ _ e h => IsHat.of_mulEquiv e h)
    (isExt_e2_hat6 hAperf V hVc hVsq hVcard π hπ hVπ hker)

end CFSG.Quasithin.A312ExtShapes
