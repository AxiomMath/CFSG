module

public import CFSG.Quasithin.EmptyFaithful.S151WJ0
public import CFSG.Quasithin.EmptyFaithful.S151ZN
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S151ZC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Fin257
open scoped commutatorElement Pointwise

section Transport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {X : Type} [Group X] [Finite X]
  (α : ↥L →* X)

omit [Finite G] in
theorem pre_card (hα : Function.Surjective α) (Q : Subgroup X) :
    Nat.card ↥(pre α Q) = Nat.card ↥Q * Nat.card α.ker := by
  have h1 : Nat.card ↥(pre α Q) = Nat.card ↥(Q.comap α) := by
    unfold pre
    exact Subgroup.card_map_of_injective L.subtype_injective
  rw [h1]
  have h2 := Subgroup.card_mul_index (Q.comap α)
  rw [Subgroup.index_comap_of_surjective Q hα] at h2
  have h3 := Subgroup.card_ker_mul_card_of_surjective hα
  have h4 := Subgroup.card_mul_index Q
  have hpos : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card ↥(Q.comap α) * Q.index = Nat.card ↥L := h2
    _ = Nat.card α.ker * Nat.card X := h3.symm
    _ = Nat.card α.ker * (Nat.card ↥Q * Q.index) := by rw [h4]
    _ = Nat.card ↥Q * Nat.card α.ker * Q.index := by ring

omit [Finite G] [Finite X] in
theorem pre_map_eq {B M : Subgroup G} (hkerB : α.ker ≤ B.subgroupOf L) (hBM : B ≤ M)
    (hML : M ≤ L) : pre α ((M.subgroupOf L).map α) = M := by
  ext x
  rw [mem_pre]
  constructor
  · rintro ⟨hxL, m, hm, hmx⟩
    have hk : m⁻¹ * ⟨x, hxL⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
    have hkM : m⁻¹ * ⟨x, hxL⟩ ∈ M.subgroupOf L := hBM (hkerB hk)
    have : (⟨x, hxL⟩ : ↥L) = m * (m⁻¹ * ⟨x, hxL⟩) := by group
    have hxM : (⟨x, hxL⟩ : ↥L) ∈ M.subgroupOf L := by
      rw [this]
      exact (M.subgroupOf L).mul_mem hm hkM
    exact hxM
  · intro hx
    exact ⟨hML hx, ⟨x, hML hx⟩, hx, rfl⟩

end Transport

theorem rank2Lat_of_data {G : Type} [Group G] [Finite G] {L B : Subgroup G} (hB : IsSylowTwoOf B L)
    {X : Type} [Group X] [Finite X] (α : ↥L →* X) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (hD : Rank2Data ((B.subgroupOf L).map α)) :
    L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup X := (B.subgroupOf L).map α with hDdef
  have hker2 : IsPGroup 2 α.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hkerB : α.ker ≤ B.subgroupOf L := by
    obtain ⟨P₀, hP₀⟩ := FLc.exists_sylow_of_isSylowTwoOf hB
    have hKP : CFSG.pCore 2 ↥L ≤ (P₀ : Subgroup ↥L) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).le_sylow_of_normal P₀
    rw [hker, ← hP₀]
    exact hKP
  have hBpre : pre α D = B := pre_map_eq α hkerB le_rfl hB.1
  obtain ⟨hselfN, Q₁, Q₂, hne, hm₁, hm₂, hD₁, hD₂, hc₁, hc₂, hch₁, hch₂, honly⟩ := hD
  have hNB : L ⊓ Subgroup.normalizer (B : Set G) ≤ B := by
    have h1 := pre_normalizer hα D
    rw [hBpre] at h1
    rw [← h1, ← hBpre]
    exact pre_mono hselfN
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hmax_of : ∀ M : Subgroup G, IsMaxSubgroupIn L M → B ≤ M →
      IsMaxSubgroupIn ⊤ ((M.subgroupOf L).map α) ∧ D ≤ (M.subgroupOf L).map α := by
    intro M hM hBM
    have hML : M ≤ L := hM.1.le
    have hpre := pre_map_eq α hkerB hBM hML
    refine ⟨⟨?_, fun K hMK _ => ?_⟩, ?_⟩
    · rw [← pre_lt_iff hα, hpre, pre_top]
      exact hM.1
    · have h1 : pre α ((M.subgroupOf L).map α) < pre α K := (pre_lt_iff hα).mpr hMK
      rw [hpre] at h1
      have h2 : pre α K = L := hM.2 _ h1 (pre_le_K K)
      exact pre_injective hα (h2.trans (pre_top (π := α)).symm)
    · rw [← pre_le_iff hα, hpre, hBpre]
      exact hBM
  have build : ∀ (Y Z : Subgroup X), IsMaxSubgroupIn ⊤ Z → D ≤ Z → Y ≠ Z →
      (∀ K : Subgroup X, IsMaxSubgroupIn ⊤ K → D ≤ K → K = Y ∨ K = Z) →
      Nat.card ↥Z = 3 * Nat.card ↥D → CharTwo Z → OtherPar L B (pre α Y) (pre α Z) := by
    intro Y Z hZ hZD hYZ hY hcZ hchZ
    have hBZ : B ≤ pre α Z := by
      rw [← hBpre]
      exact pre_mono hZD
    have hcardB : Nat.card ↥B = Nat.card ↥D * Nat.card α.ker := by
      rw [← hBpre]
      exact pre_card α hα D
    refine ⟨⟨?_, fun K' hZK' hK'L => ?_⟩, hBZ, ?_, ?_, ?_, ?_, ?_⟩
    · have h0 := (pre_lt_iff hα).mpr hZ.1
      rwa [pre_top] at h0
    · have hBK' : B ≤ K' := hBZ.trans hZK'.le
      have hpre := pre_map_eq α hkerB hBK' hK'L
      have h1 : pre α Z < pre α ((K'.subgroupOf L).map α) := by rw [hpre]; exact hZK'
      have h2 := (pre_lt_iff hα).mp h1
      have h3 := hZ.2 _ h2 le_top
      rw [h3, pre_top] at hpre
      exact hpre.symm
    · intro heq
      exact hYZ (pre_injective hα heq.symm)
    · intro K hK hBK
      obtain ⟨hKm, hKD⟩ := hmax_of K hK hBK
      have hpre := pre_map_eq α hkerB hBK hK.1.le
      rcases hY _ hKm hKD with h | h
      · left
        rw [← hpre, h]
      · right
        rw [← hpre, h]
    · rw [pre_card α hα Z, hcZ, hcardB]
      ring
    · intro hPN
      have hPB : pre α Z ≤ B := (le_inf (pre_le_K Z) hPN).trans hNB
      have h1 := Subgroup.card_le_of_le hPB
      rw [pre_card α hα Z, hcZ, hcardB] at h1
      have : 0 < Nat.card ↥D * Nat.card α.ker := hcardB ▸ hBpos
      nlinarith
    ·
      intro x hxP hx3 hle
      have hxL : x ∈ L := pre_le_K Z hxP
      set x₀ : ↥L := ⟨x, hxL⟩ with hx₀
      have hxZ : α x₀ ∈ Z := (mem_pre.mp hxP).2
      have hx3' : x ^ 3 = 1 := by simpa [hx3] using pow_orderOf_eq_one x
      have hax3 : α x₀ ^ 3 = 1 := by
        rw [← map_pow]
        have : x₀ ^ 3 = 1 := Subtype.ext hx3'
        rw [this, map_one]
      have hax1 : α x₀ ≠ 1 := by
        intro h1
        have h2 : x₀ ∈ CFSG.pCore 2 ↥L := by
          rw [← hker]
          exact h1
        have h3 : x ∈ pCoreOf 2 L := zn_mem_pCoreOf.mpr ⟨hxL, h2⟩
        exact zb_not_mem_of_orderOf_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) h3 hx3
      have hax : orderOf (α x₀) = 3 := orderOf_eq_prime hax3 hax1
      have hcomm : ∀ v ∈ pCoreOf 2 Z, α x₀ * v = v * α x₀ := by
        intro v hv
        obtain ⟨k, rfl⟩ := hα v
        have hk : (k : G) ∈ pCoreOf 2 (pre α Z) := by
          rw [pCoreOf_pre hα hker2]
          exact mem_pre_of_mem k hv
        have h1 : ⁅(k : G), x⁆ ∈ ⁅pCoreOf 2 (pre α Z), Subgroup.zpowers x⁆ :=
          Subgroup.commutator_mem_commutator hk (Subgroup.mem_zpowers x)
        obtain ⟨hz, hzO⟩ := zn_mem_pCoreOf.mp (hle h1)
        have h3 : α ⟨⁅(k : G), x⁆, hz⟩ = 1 := by
          have : (⟨⁅(k : G), x⁆, hz⟩ : ↥L) ∈ α.ker := by
            rw [hker]
            exact hzO
          exact this
        have h4 : (⟨⁅(k : G), x⁆, hz⟩ : ↥L) = ⁅k, x₀⁆ := rfl
        rw [h4, map_commutatorElement] at h3
        exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
      have hmem : α x₀ ∈ pCoreOf 2 Z :=
        hchZ ⟨hxZ, Subgroup.mem_centralizer_iff.mpr fun v hv => (hcomm v hv).symm⟩
      exact zb_not_mem_of_orderOf_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Z) hmem hax
  refine ⟨hNB, fun M' hM' hBM' => ?_⟩
  obtain ⟨hYm, hYD⟩ := hmax_of M' hM' hBM'
  have hM'eq := pre_map_eq α hkerB hBM' hM'.1.le
  rcases honly _ hYm hYD with hY | hY
  · refine ⟨pre α Q₂, ?_⟩
    rw [← hM'eq, hY]
    exact build Q₁ Q₂ hm₂ hD₂ hne honly hc₂ hch₂
  · refine ⟨pre α Q₁, ?_⟩
    rw [← hM'eq, hY]
    exact build Q₂ Q₁ hm₁ hD₁ hne.symm (fun K hK hKD => (honly K hK hKD).symm) hc₁ hch₁

theorem wj_sylow_of_top {X : Type} [Group X] [Finite X] {P : Subgroup X} (h : IsSylowTwoOf P ⊤) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ P.index := by
    have h2 := h.2.2
    change ¬ 2 ∣ P.relIndex ⊤ at h2
    rwa [Subgroup.relIndex_top_right] at h2
  exact ⟨h.2.1.toSylow hi, h.2.1.toSylow_coe hi⟩

theorem wj_map_conj_map_conj_inv {X : Type} [Group X] (g : X) (U : Subgroup X) :
    (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id X := by
    ext x
    simp [MulAut.conj_apply]
    group
  rw [this, Subgroup.map_id]

theorem rank2Lat_of_sylow_data {G : Type} [Group G] [Finite G] {L B : Subgroup G}
    (hB : IsSylowTwoOf B L) {X : Type} [Group X] [Finite X] (α : ↥L →* X)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) {D₀ : Subgroup X}
    (hD₀ : IsSylowTwoOf D₀ ⊤) (hdata : Rank2Data D₀) :
    L ⊓ Subgroup.normalizer (B : Set G) ≤ B ∧
      ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := FLc.exists_sylow_of_isSylowTwoOf hB
  let Q : Sylow 2 X := Sylow.mapSurjective (f := α) hα P₀
  have hQ : (Q : Subgroup X) = (B.subgroupOf L).map α := by
    rw [← hP₀]
    exact Sylow.coe_mapSurjective (f := α) hα P₀
  obtain ⟨S₀, hS₀⟩ := wj_sylow_of_top hD₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ Q
  have hgS : (Q : Subgroup X) = (MulAut.conj g) • (S₀ : Subgroup X) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hDg : (B.subgroupOf L).map α = D₀.map (MulAut.conj g).toMonoidHom := by
    rw [← hQ, hgS, hS₀]
    rfl
  let α' : ↥L →* X := (MulAut.conj g⁻¹).toMonoidHom.comp α
  have hα' : Function.Surjective α' := (MulAut.conj g⁻¹).surjective.comp hα
  have hker' : α'.ker = CFSG.pCore 2 ↥L := by
    rw [← hker]
    ext x
    simp only [α', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hD' : (B.subgroupOf L).map α' = D₀ := by
    have : (B.subgroupOf L).map α' = ((B.subgroupOf L).map α).map (MulAut.conj g⁻¹).toMonoidHom :=
      (Subgroup.map_map _ _ _).symm
    rw [this, hDg, wj_map_conj_map_conj_inv]
  exact rank2Lat_of_data hB α' hα' hker' (hD' ▸ hdata)

end CFSG.Quasithin
