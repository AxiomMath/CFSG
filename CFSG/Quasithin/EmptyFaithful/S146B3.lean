module

public import CFSG.Quasithin.EmptyFaithful.S146B0
public import CFSG.Quasithin.EmptyFaithful.S146G1
public import CFSG.Quasithin.EmptyFaithful.S146A1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Group G] [Finite G] in
private theorem comap_pCore_congr' (p : ℕ) {X : Type} [Group X] (N N' : Subgroup X) [N.Normal]
    [N'.Normal] (h : N = N') :
    (CFSG.pCore p (X ⧸ N)).comap (QuotientGroup.mk' N) =
      (CFSG.pCore p (X ⧸ N')).comap (QuotientGroup.mk' N') := by
  subst h
  rfl

omit [Finite G] in
theorem mem_pCore_of_mem_oTwoPIn {q : ℕ} {H : Subgroup G} {x : G} (hx : x ∈ H)
    (h : x ∈ oTwoPIn q H) :
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨x, hx⟩ : OTwoQuot H) ∈
      CFSG.pCore q (OTwoQuot H) := by
  unfold oTwoPIn preimageModTwoCore at h
  rw [comap_pCore_congr' q (X := ↥H) (CFSG.pCore 2 ↥H) (CFSG.Open.pCore 2 ↥H)
    (CFSG.pCore_eq_open ↥H 2)] at h
  obtain ⟨y, hy, hyx⟩ := h
  have : y = ⟨x, hx⟩ := Subtype.ext hyx
  rwa [this] at hy

theorem pCore_oTwoQuot_eq_bot_of_oddCore {H : Subgroup G} (h : OddCoreModTwoTrivial H) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) : CFSG.pCore q (OTwoQuot H) = ⊥ := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set π : ↥H →* OTwoQuot H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set N' : Subgroup (OTwoQuot H) := CFSG.pCore q (OTwoQuot H) with hN'
  have hNn : N'.Normal := CFSG.BaerSuzuki.Helpers.pCore_normal q
  have hNp : IsPGroup q ↥N' := CFSG.BaerSuzuki.Helpers.pCore_isPGroup q
  set P : Subgroup G := preimH H N' with hP
  have hPH : P ≤ H := preimH_le H N'
  have hQP : pCoreOf 2 H ≤ P := pCoreOf_le_preimH H N'
  have hPn : (P.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr normalizer_preimH
  have hker : (⊥ : Subgroup (OTwoQuot H)).comap π = CFSG.Open.pCore 2 ↥H := QuotientGroup.ker_mk' _
  have hrel : (pCoreOf 2 H).relIndex P = Nat.card N' := by
    have hQ : pCoreOf 2 H = (CFSG.Open.pCore 2 ↥H).map H.subtype := rfl
    have hY : P = (N'.comap π).map H.subtype := rfl
    have h1 := Subgroup.relIndex_comap (⊥ : Subgroup (OTwoQuot H)) π (N'.comap π)
    rw [hker] at h1
    have hrel0 : (CFSG.Open.pCore 2 ↥H).relIndex (N'.comap π) = Nat.card N' := by
      rw [h1, Subgroup.relIndex_bot_left, Subgroup.map_comap_eq_self_of_surjective hπs]
    rw [hQ, hY, Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective]
    exact hrel0
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hodd : Odd ((pCoreOf 2 H).relIndex P) := by
    rw [hrel, hk]
    exact (hq.odd_of_ne_two hq2).pow
  have hPQ : P ≤ pCoreOf 2 H := h P hPH hPn hQP hodd
  refine eq_bot_iff.mpr fun n hn => ?_
  obtain ⟨y, rfl⟩ := hπs n
  have hyP : (y : G) ∈ P := mem_preimH.mpr ⟨y.2, hn⟩
  obtain ⟨z, hz, hzy⟩ := hPQ hyP
  have hzy' : z = y := Subtype.ext hzy
  rw [Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, ← hzy']
  exact (QuotientGroup.eq_one_iff _).mpr hz


theorem solvRad_le_pCoreOf_of_oddCore {H : Subgroup G} (h : OddCoreModTwoTrivial H) :
    solvRad H ≤ pCoreOf 2 H := by
  by_contra hne
  obtain ⟨q, hq, hq2, x, hxX, hxq, hxQ⟩ := exists_mem_oTwoPIn_of_solvable (solvRad_le H)
    (solvRad_normal H) (solvRad_isSolvable H) hne
  have hxH : x ∈ H := solvRad_le H hxX
  have h1 := mem_pCore_of_mem_oTwoPIn hxH hxq
  rw [pCore_oTwoQuot_eq_bot_of_oddCore h hq hq2, Subgroup.mem_bot, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  exact hxQ ⟨_, h1, rfl⟩

theorem solvRad_eq_pCoreOf_of_mem_cComp {H K : Subgroup G} (h : OddCoreModTwoTrivial H)
    (hK : K ∈ cComp H) : solvRad K = pCoreOf 2 K := by
  refine le_antisymm ?_ ?_
  · have h1 : solvRad K ≤ solvRad H := solvRad_le_solvRad_of_subnormal (subnormal_of_mem_cComp hK)
    have h2 : solvRad K ≤ pCoreOf 2 H := h1.trans (solvRad_le_pCoreOf_of_oddCore h)
    have h3 : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
      intro k hk
      exact F7.mem_normalizer_inf (Subgroup.le_normalizer hk)
        (le_normalizer_pCoreOf 2 H (le_of_mem_cComp hK hk))
    exact (le_inf (solvRad_le K) h2).trans h3
  · have : Group.IsSolvable ↥(pCoreOf 2 K) := by
      have hp : IsPGroup 2 ↥(pCoreOf 2 K) := pCoreOf_isPGroup 2 K
      have : Group.IsNilpotent ↥(pCoreOf 2 K) := hp.isNilpotent
      infer_instance
    exact le_solvRad (pCoreOf_le 2 K) (normal_pCoreOf_subgroupOf K) this

theorem stage14619_proof : Stage14619 := by
  intro G _ _ T M S hB H hH
  refine ⟨hB H hH, fun K hK => ?_⟩
  have hs := (cComp_structure hK).2.1.1
  have heq : (pCoreOf 2 K).subgroupOf K = (solvRad K).subgroupOf K := by
    rw [solvRad_eq_pCoreOf_of_mem_cComp (hB H hH) hK]
  let e : KBar K ≃* ↥K ⧸ (solvRad K).subgroupOf K := QuotientGroup.quotientMulEquivOfEq heq
  have := hs
  exact e.isSimpleGroup

end CFSG.Quasithin
