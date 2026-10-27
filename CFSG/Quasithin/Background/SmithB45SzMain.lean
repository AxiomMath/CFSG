module

public import CFSG.Quasithin.Background.SmithB45SzRow
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def SzNaturalOfSmallDisplacement : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ L : Subgroup (MulAut W), Group.IsPerfect ↥L →
        (∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* suzukiGroup a K) →
        (∃ t ∈ L, t * t = 1 ∧ t ≠ 1 ∧
          (fixV (Subgroup.zpowers t)).index ≤ 2 ^ (2 * (2 * a + 1))) →
        BinaryNaturalSz L ⊤ ⊥ (2 * a + 1)

namespace B45Sz

variable {V : Type} [CommGroup V] [Finite V]

theorem b4Hyp_data {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) :
    Nontrivial V ∧ Group.IsPerfect ↥L ∧
      (∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      L ≤ G ∧ G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  refine ⟨?_, hHyp.2.2.1.1, Bridge.TypeList.irr_of_isIrrSec hHyp.2.2.2,
    (FFC.b4hyp_data hHyp).1, B42L2.le_normalizer_of_b4Hyp hHyp⟩
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hHyp.2.2.2.1
  exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩

theorem exists_small_involution
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) {a : ℕ}
    (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : ↥L ⧸ Subgroup.center ↥L ≃* suzukiGroup a K) {A : Subgroup (MulAut V)} (hA : IsA2 G A)
    (hAV : Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A)) :
    ∃ t ∈ L, t * t = 1 ∧ t ≠ 1 ∧ (fixV (Subgroup.zpowers t)).index ≤ 2 ^ (2 * (2 * a + 1)) := by
  obtain ⟨hnt, hperf, hirr, hLG, hGN⟩ := b4Hyp_data hHyp
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨-, hbij, hP, -, -⟩ := Setup.Family.suzuki_irreducible_normalizer_excludes a ha hK V hV'
    L hperf hirr α
  have hAL : A ≤ L := hP A hA.isElemAbelian2.isPGroup (hA.1.trans hGN)
  let θ : ↥L →* suzukiGroup a K := α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hθ : Function.Injective θ := hbij.1
  have hcardA : Nat.card A ≤ 2 ^ (2 * a + 1) := by
    have h1 := Setup.Family.suzuki_exponent_two_card_le hK ((A.subgroupOf L).map θ) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have : x * x = 1 := Subtype.ext (by
        have := hA.isElemAbelian2.2 _ (Subgroup.mem_subgroupOf.mp hx)
        simpa [sq] using this)
      rw [this, map_one])
    rw [Subgroup.card_map_of_injective hθ] at h1
    have h2 : Nat.card (A.subgroupOf L) = Nat.card A := by
      rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hAL]
    omega
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA.ne_bot
  refine ⟨t, hAL t.2, by simpa [sq] using hA.isElemAbelian2.2 _ t.2,
    fun h => ht1 (Subtype.ext h), ?_⟩
  have hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ (fixV A).index :=
    Subgroup.index_antitone (fun v hv y hy => hv y ((Subgroup.zpowers_le).mpr t.2 hy))
  have hci := (fixV A).card_mul_index
  have hpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  have hAidx : (fixV A).index ≤ Nat.card A ^ 2 := by
    rw [← hci] at hAV
    rw [mul_comm (Nat.card A ^ 2)] at hAV
    exact Nat.le_of_mul_le_mul_left hAV hpos
  calc (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ Nat.card A ^ 2 := hidx.trans hAidx
    _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left hcardA 2
    _ = 2 ^ (2 * (2 * a + 1)) := by rw [← pow_mul, mul_comm]

end B45Sz

open B45Sz in
theorem asB45Sz_of_natural
    (hnat : SzNaturalOfSmallDisplacement) : AsB45Sz := by
  intro V _ _ hV G L hHyp hT _ h2
  obtain ⟨f, -, -, -, a, ha, K, _, _, rfl, hK, ⟨α⟩⟩ := hT
  obtain ⟨hnt, hperf, hirr, hLG, hGN⟩ := b4Hyp_data hHyp
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp h2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hsmall := exists_small_involution hV hHyp ha hK α hA hAV
  have hnatL := hnat a ha K hK V (fun v => by rw [← pow_two]; exact hV v) L hperf hirr ⟨α⟩ hsmall
  obtain ⟨hq, hqh⟩ := qOf_qhatOf_eq_two hLG hGN hnatL
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨2 * a + 1, hnatL, hq, hqh⟩))))

end CFSG.Quasithin
