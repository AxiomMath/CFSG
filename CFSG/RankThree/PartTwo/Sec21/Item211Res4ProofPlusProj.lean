module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcRed
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofProj
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusCore
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projImage)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item228Census3Proof (projRestrict IsCentData projRestrict_surjective projRestrict_eq_iff
  projRestrict_eq_one_iff exists_lift_cube centralizer_projRestrict scalar_eq_one_iff)

variable {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]

@[expose] def SL2Datum (G : Subgroup (GL n K)) (A : GL n K) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (p : ℕ), p.Prime ∧ 5 ≤ p ∧ Nat.card F = p ∧
    ∃ φ : SL(2, F) →* GL n K, IsCentData G A φ ∧ (ProjGenLinGroup.mk.comp φ).ker = ⊥ ∧
      ∀ B ∈ G, B ^ 3 = 1 → B * A = A * B → ∃ (j : ℕ) (S : SL(2, F)), B = A ^ j * φ S

@[expose] def PSL2Datum (G : Subgroup (GL n K)) (A : GL n K) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), 4 ≤ Nat.card F ∧ (2 : F) ≠ 0 ∧ (3 : F) ≠ 0 ∧
    (∃ c : F, 3 * c ^ 2 = 1) ∧
    ∃ φ : SL(2, F) →* GL n K, IsCentData G A φ ∧
      (ProjGenLinGroup.mk.comp φ).ker = Subgroup.center SL(2, F) ∧
      ∀ B ∈ G, B ^ 3 = 1 → B * A = A * B → ∃ (j : ℕ) (S : SL(2, F)), B = A ^ j * φ S

@[expose] noncomputable def iotaOf (G : Subgroup (GL n K)) {S : Type} [Group S]
    (φ : S →* GL n K) (hφ : ∀ s, φ s ∈ G) : S →* MulAut (projImage G) :=
  (MulAut.conj : projImage G →* MulAut (projImage G)).comp
    ((projRestrict G).comp (φ.codRestrict G hφ))

theorem iotaOf_apply (G : Subgroup (GL n K)) {S : Type} [Group S] (φ : S →* GL n K)
    (hφ : ∀ s, φ s ∈ G) (s : S) :
    iotaOf G φ hφ s = MulAut.conj (projRestrict G ⟨φ s, hφ s⟩) :=
  rfl

theorem iotaOf_eq_one_iff (G : Subgroup (GL n K)) (hZ : Subgroup.center (projImage G) = ⊥)
    {S : Type} [Group S] (φ : S →* GL n K) (hφ : ∀ s, φ s ∈ G) (s : S) :
    iotaOf G φ hφ s = 1 ↔ s ∈ (ProjGenLinGroup.mk.comp φ).ker := by
  rw [iotaOf_apply, ← map_one (MulAut.conj : projImage G →* MulAut (projImage G)),
    (Item211Lie2Proof.conj_injective' hZ).eq_iff, MonoidHom.mem_ker, MonoidHom.comp_apply,
    ← Subtype.coe_inj]
  rfl

section Lift

variable [Nonempty n]

theorem commute_of_projRestrict_commute (G : Subgroup (GL n K))
    (hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar n u ∈ G → u ^ 3 = 1 → u = 1) {A B : G}
    (hA3 : A ^ 3 = 1)
    (h : projRestrict G B * projRestrict G A = projRestrict G A * projRestrict G B) :
    (B : GL n K) * A = A * B := by
  have hB : B ∈ Subgroup.centralizer ({A} : Set G) := by
    have hmem : projRestrict G B ∈ Subgroup.centralizer ({projRestrict G A} : Set (projImage G)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr h
    rw [centralizer_projRestrict G A hA3 hZ3] at hmem
    obtain ⟨B', hB', hBB'⟩ := hmem
    obtain ⟨u, hu⟩ := (projRestrict_eq_iff G).mp hBB'
    have hc : ∀ x : GL n K, Commute x (GeneralLinearGroup.scalar n u) := fun x =>
      Subgroup.mem_center_iff.mp (by
        rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩) x
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hB'
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have e1 := congrArg Subtype.val hB'
    simp only [Subgroup.coe_mul] at e1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu]
    calc (B' : GL n K) * GeneralLinearGroup.scalar n u * A =
        (B' : GL n K) * A * GeneralLinearGroup.scalar n u := by
          rw [mul_assoc, (hc (A : GL n K)).eq.symm, ← mul_assoc]
      _ = A * B' * GeneralLinearGroup.scalar n u := by rw [e1]
      _ = A * (B' * GeneralLinearGroup.scalar n u) := by group
  have := Subgroup.mem_centralizer_singleton_iff.mp hB
  exact congrArg Subtype.val this

end Lift

theorem bridge [Finite K] [Nonempty n] (G : Subgroup (GL n K))
    (hZ : Subgroup.center (projImage G) = ⊥)
    (hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar n u ∈ G → u ^ 4 = 1) {A : G} (hA3 : A ^ 3 = 1)
    {S : Type} [Group S] (φ : S →* GL n K) (hφ : IsCentData G A φ)
    (hdec : ∀ B ∈ G, B ^ 3 = 1 → B * A = A * B → ∃ (j : ℕ) (s : S), B = A ^ j * φ s)
    {D : Subgroup (MulAut (projImage G))}
    (hDi : D ≤ (MulAut.conj : projImage G →* MulAut (projImage G)).range)
    (hDe : IsElemAbelian 3 D) (hdD : MulAut.conj (projRestrict G A) ∈ D) :
    (∀ s, iotaOf G φ hφ.1 s ∈ (MulAut.conj : projImage G →* MulAut (projImage G)).range ⊓
      Subgroup.centralizer ({MulAut.conj (projRestrict G A)} : Set (MulAut (projImage G)))) ∧
    (∀ g ∈ (MulAut.conj : projImage G →* MulAut (projImage G)).range ⊓
      Subgroup.centralizer ({MulAut.conj (projRestrict G A)} : Set (MulAut (projImage G))),
      ∀ h ∈ (MulAut.conj : projImage G →* MulAut (projImage G)).range ⊓
      Subgroup.centralizer ({MulAut.conj (projRestrict G A)} : Set (MulAut (projImage G))),
        g * h * g⁻¹ * h⁻¹ ∈ (iotaOf G φ hφ.1).range) ∧
    (∀ x ∈ D, ∃ (k : ℤ) (s : S), x = MulAut.conj (projRestrict G A) ^ k * iotaOf G φ hφ.1 s) := by
  classical
  have hinj := Item211Lie2Proof.conj_injective' hZ
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar n u ∈ G → u ^ 3 = 1 → u = 1 := fun u hu h3 => by
    calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
      _ = 1 := by rw [hZ4 u hu, h3, inv_one, one_mul]
  have hφG : ∀ s, (⟨φ s, hφ.1 s⟩ : G) * A = A * ⟨φ s, hφ.1 s⟩ := fun s =>
    Subtype.ext (hφ.2.1 s)
  refine ⟨fun s => ?_, fun g hg h hh => ?_, fun x hx => ?_⟩
  ·
    refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, iotaOf_apply, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, hφG]
  ·
    obtain ⟨⟨y1, rfl⟩, hy1⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨⟨y2, rfl⟩, hy2⟩ := Subgroup.mem_inf.mp hh
    have hc1 : y1 ∈ Subgroup.centralizer ({projRestrict G A} : Set (projImage G)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hinj (by rw [map_mul, map_mul]; exact Subgroup.mem_centralizer_singleton_iff.mp hy1))
    have hc2 : y2 ∈ Subgroup.centralizer ({projRestrict G A} : Set (projImage G)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hinj (by rw [map_mul, map_mul]; exact Subgroup.mem_centralizer_singleton_iff.mp hy2))
    rw [centralizer_projRestrict G A hA3 hZ3] at hc1 hc2
    obtain ⟨g1, hg1, rfl⟩ := hc1
    obtain ⟨g2, hg2, rfl⟩ := hc2
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg1 hg2
    obtain ⟨s, hs⟩ := hφ.2.2 g1 g1.2 g2 g2.2 (congrArg Subtype.val hg1)
      (congrArg Subtype.val hg2)
    refine ⟨s, ?_⟩
    rw [iotaOf_apply]
    have e : (⟨φ s, hφ.1 s⟩ : G) = g1 * g2 * g1⁻¹ * g2⁻¹ := Subtype.ext hs
    rw [e]
    simp only [map_mul, map_inv]
  ·
    obtain ⟨yx, rfl⟩ := hDi hx
    have hyx3 : yx ^ 3 = 1 := hinj (by rw [map_pow, hDe.2 _ hx, map_one])
    by_cases hyx1 : yx = 1
    · refine ⟨0, 1, ?_⟩
      rw [hyx1, map_one, map_one, zpow_zero, one_mul]
    have hord : orderOf yx = 3 := orderOf_eq_prime hyx3 hyx1
    obtain ⟨B, hBy, hB3, -⟩ := exists_lift_cube G hZ4 yx hord
    have hcomm : projRestrict G B * projRestrict G A = projRestrict G A * projRestrict G B := by
      rw [hBy]
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hDe.1.is_comm.comm ⟨_, hx⟩ ⟨_, hdD⟩)
    have hBA := commute_of_projRestrict_commute G hZ3 hA3 hcomm
    have hB3' : (B : GL n K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hB3, Subgroup.coe_one]
    obtain ⟨j, s, hjs⟩ := hdec B B.2 hB3' hBA
    refine ⟨j, s, ?_⟩
    have e : B = A ^ j * ⟨φ s, hφ.1 s⟩ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
      exact hjs)
    rw [← hBy, e, map_mul, map_mul, map_pow, map_pow, iotaOf_apply, zpow_natCast]

theorem conj_mem_range_conj {X : Type*} [Group X] (τ : MulAut X) {x : MulAut X}
    (hx : x ∈ (MulAut.conj : X →* MulAut X).range) :
    τ * x * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨τ y, (Item211Lie2Proof.mul_conj_mul_inv' τ y).symm⟩

theorem excPlusFor_projImage [Finite K] [Nonempty n] (G : Subgroup (GL n K))
    (hZ : Subgroup.center (projImage G) = ⊥)
    (hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar n u ∈ G → u ^ 4 = 1)
    (hdata : ∀ A : G, A ^ 3 = 1 → A ≠ 1 → SL2Datum G (A : GL n K) ∨ PSL2Datum G (A : GL n K)) :
    Item211Lie2Proof.ExcPlusFor (projImage G) := by
  intro D hDi hDe hD9 d hdD hd1 T _ hTD
  classical
  have : Finite (projImage G) := Item228Census3Proof.finite_projImage G
  have : Finite (MulAut (projImage G)) :=
    Finite.of_injective (fun f : MulAut (projImage G) => (f : projImage G → projImage G))
      (fun f g h => MulEquiv.ext (congrFun h))
  have hinj := Item211Lie2Proof.conj_injective' hZ
  obtain ⟨yd, rfl⟩ := hDi hdD
  have hyd3 : yd ^ 3 = 1 := hinj (by rw [map_pow, hDe.2 _ hdD, map_one])
  have hyd1 : yd ≠ 1 := fun h => hd1 (by rw [h, map_one])
  obtain ⟨A, hAy, hA3, hA1⟩ := exists_lift_cube G hZ4 yd (orderOf_eq_prime hyd3 hyd1)
  have hA3' : (A : GL n K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA1' : A ≠ 1 := hA1
  subst hAy
  have hTI : ∀ t ∈ T, ∀ x ∈ (MulAut.conj : projImage G →* MulAut (projImage G)).range,
      t * x * t⁻¹ ∈ (MulAut.conj : projImage G →* MulAut (projImage G)).range :=
    fun t _ x hx => conj_mem_range_conj t hx
  rcases hdata A hA3 hA1' with ⟨F, _, _, p, hp, hp5, hF, φ, hφ, hker, hdec⟩ |
    ⟨F, _, _, hF4, h2, h3, ⟨c, hc⟩, φ, hφ, hker, hdec⟩
  · obtain ⟨hιC, hcomm, hDdec⟩ := bridge G hZ hZ4 hA3 φ hφ hdec hDi hDe hdD
    have hF' : Nat.card F = p := hF
    have : Fact p.Prime := ⟨hp⟩
    have h2' : (2 : F) ≠ 0 := by
      have : CharP F p := by
        have := Fintype.ofFinite F
        exact charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hF'])
      intro h
      have := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have h3' : (3 : F) ≠ 0 := by
      have : CharP F p := by
        have := Fintype.ofFinite F
        exact charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hF'])
      intro h
      have := (CharP.cast_eq_zero_iff F p 3).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hι : Function.Injective (iotaOf G φ hφ.1) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro s hs
      rw [MonoidHom.mem_ker, iotaOf_eq_one_iff G hZ, hker] at hs
      exact hs
    exact excPlus_of_sl2Block hp hp5 hF' h2' h3' (iotaOf G φ hφ.1) hι hDe hD9 hdD
      (hDi.trans le_rfl) hιC hcomm hDdec hTD hTI
  · obtain ⟨hιC, hcomm, hDdec⟩ := bridge G hZ hZ4 hA3 φ hφ hdec hDi hDe hdD
    have hιker : ∀ s, iotaOf G φ hφ.1 s = 1 ↔ s = 1 ∨ s = -1 := fun s => by
      rw [iotaOf_eq_one_iff G hZ, hker]
      refine ⟨Item211Lie2Proof.eq_one_or_eq_neg_one_of_mem_center, ?_⟩
      rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_center_iff.mpr fun g => (neg_one_mul_comm g).symm
    exact excPlus_of_psl2Block hF4 h2 h3 hc (iotaOf G φ hφ.1) hιker hDe hdD hDi hιC hcomm hDdec
      hTD hTI

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
