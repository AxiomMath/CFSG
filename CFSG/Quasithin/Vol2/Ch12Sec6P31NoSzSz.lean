module

public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Blueprint

section Center

variable {Y : Type*} [Group Y]

theorem odd_card_center_of_normal [Finite Y]
    (hO2 : ∀ M : Subgroup Y, M.Normal → IsPGroup 2 M → M = ⊥) (N : Subgroup Y) [hN : N.Normal] :
    Odd (Nat.card ↥(Subgroup.center ↥N)) := by
  let Z : Subgroup Y :=
    { carrier := {y | y ∈ N ∧ (∀ n ∈ N, Commute n y) ∧ y ^ 2 = 1}
      one_mem' := ⟨N.one_mem, fun n _ => Commute.one_right n, one_pow 2⟩
      mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1,
        fun n hn => (ha.2.1 n hn).mul_right (hb.2.1 n hn), by
          rw [(hb.2.1 a ha.1).mul_pow 2, ha.2.2, hb.2.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, fun n hn => (ha.2.1 n hn).inv_right, by
          rw [inv_pow, ha.2.2, inv_one]⟩ }
  haveI hZn : Z.Normal := by
    refine ⟨fun z hz g => ⟨hN.conj_mem z hz.1 g, fun n hn => ?_, ?_⟩⟩
    · have hn' : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
      have h1 : g⁻¹ * n * g * z = z * (g⁻¹ * n * g) := hz.2.1 _ hn'
      show n * (g * z * g⁻¹) = (g * z * g⁻¹) * n
      calc n * (g * z * g⁻¹) = g * ((g⁻¹ * n * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
        _ = (g * z * g⁻¹) * n := by group
    · show (g * z * g⁻¹) ^ 2 = 1
      rw [conj_pow, hz.2.2]
      simp
  have hZ2 : IsPGroup 2 Z := by
    intro a
    refine ⟨1, Subtype.ext ?_⟩
    simpa using a.2.2.2
  have hZbot := hO2 Z hZn hZ2
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥N) := by
    rcases Nat.even_or_odd (Nat.card ↥(Subgroup.center ↥N)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥N)) 2 h2
  have hz2 : (((z : ↥N) : Y)) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz] at h1
    have h3 := congrArg (fun w : ↥(Subgroup.center ↥N) => ((w : ↥N) : Y)) h1
    simpa using h3
  have hzZ : ((z : ↥N) : Y) ∈ Z := by
    refine ⟨(z : ↥N).2, fun n hn => ?_, hz2⟩
    have h4 := Subgroup.mem_center_iff.1 z.2 ⟨n, hn⟩
    have h5 := congrArg (fun w : ↥N => (w : Y)) h4
    exact h5
  rw [hZbot, Subgroup.mem_bot] at hzZ
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hzZ)
  rw [hz1, orderOf_one] at hz
  omega

end Center

section Suzuki

variable {Y : Type} [Group Y]

theorem suzukiModel_of_normal [Finite Y]
    (hO2 : ∀ M : Subgroup Y, M.Normal → IsPGroup 2 M → M = ⊥) (N : Subgroup Y) [N.Normal]
    [Group.IsPerfect ↥N] {n : ℕ} (hSz : SuzukiModel (↥N ⧸ Subgroup.center ↥N) 2 n) :
    SuzukiModel ↥N 2 n := by
  obtain ⟨h2, a, ha, K', hF, hFin, hn, hK', ⟨α⟩⟩ := hSz
  have hK'' : Nat.card K' = 2 ^ (2 * a + 1) := hn ▸ hK'
  let e := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup (a := a) hK''
  let α' : (↥N ⧸ Subgroup.center ↥N) ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    α.trans e
  let π : ↥N →* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    α'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥N))
  have hπ : Function.Surjective π := α'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥N := CFSG.SectionRank.center_eq_ker_of_mulEquiv α'
  have hZodd := odd_card_center_of_normal hO2 N
  have hZ := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) π hπ hker.le
    (hker ▸ hZodd)
  rw [hker] at hZ
  exact ⟨h2, a, ha, K', hF, hFin, hn, hK',
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans α⟩⟩

end Suzuki

end CFSG.Quasithin.H13.P31Sz
