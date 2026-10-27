module

public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Defs
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Transport

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits Module

private theorem finite_statedSL_five_zmod_two : Finite ↥(StatedSL 5 (ZMod 2)) :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Open.StatedAPI.card_statedSL_five_zmod_two]; norm_num)

theorem factKv12617L52_of_leaves (h1 : LeafCentralizer) (h2 : LeafFive) (h3 : LeafTwoElt)
    (h4 : LeafCardPCore) (h5 : LeafOuter) (h7 : LeafNormR) : FactKv12617L52 := by
  intro Γ _ _ Y K T T₀ B R hconf hiso
  obtain ⟨e⟩ := hiso
  have hY0 : Y ⊓ Subgroup.centralizer (K : Set Γ) = ⊥ := h1 Γ Y K T T₀ B R hconf
  obtain ⟨hKY, hYN, -, hT, -, -, hBlt, hT₀T, hT₀4, hT₀B, hBcomm, hBiso, hR0, hRc, -, hKR⟩ :=
    hconf
  have hBK : B ≤ K := hBlt.le
  have hZK : pCoreOf 2 B ≤ K := (pCoreOf_le 2 B).trans hBK
  have hcardZ : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hfin : Finite ↥(StatedSL 5 (ZMod 2)) := finite_statedSL_five_zmod_two
  have hB'comm := Transport.commutator_map_subgroupOf e hBK hBcomm
  have hB'iso := Transport.quasithinO2QuotientIso_map e hBK hBiso
  have hpc := Transport.pCoreOf_map_subgroupOf e 2 hBK
  have hKcard : Nat.card ↥K = 9999360 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_five_zmod_two]
  have hK10 : 2 ^ 10 ∣ Nat.card ↥K := by
    rw [hKcard]
    norm_num
  obtain ⟨hT₀2, hT₀8⟩ := KG12617Lie.two_pow_le_card hKY hYN hT hT₀T hT₀4 hK10
  rcases h4 (ZMod 2) hcardZ _ hB'comm hB'iso with h16 | ⟨h16, hdim⟩
  ·
    have hbot : pCoreOf 2 ((B.subgroupOf K).map e.toMonoidHom) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ h16
    have hcomm : ⁅pCoreOf 2 ((B.subgroupOf K).map e.toMonoidHom),
        (B.subgroupOf K).map e.toMonoidHom⁆ = ⊥ := by
      rw [hbot, Subgroup.commutator_bot_left]
    have hS2 : IsPGroup 2 ↥(((T₀ ⊓ K).subgroupOf K).map e.toMonoidHom) :=
      hT₀2.of_equiv (Transport.transportEquiv (B := T₀ ⊓ K) e inf_le_right)
    have hS8 : 2 ^ 8 ≤ Nat.card ↥(((T₀ ⊓ K).subgroupOf K).map e.toMonoidHom) := by
      rw [← Nat.card_congr (Transport.transportEquiv (B := T₀ ⊓ K) e inf_le_right).toEquiv]
      norm_num at hT₀8 ⊢
      omega
    have hS'N : ((T₀ ⊓ K).subgroupOf K).map e.toMonoidHom ≤
        Subgroup.normalizer
          (((B.subgroupOf K).map e.toMonoidHom : Subgroup ↥(StatedSL 5 (ZMod 2))) :
            Set ↥(StatedSL 5 (ZMod 2))) := by
      intro s hs
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hs
      rw [Transport.mem_normalizer_map_iff e hBK]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hT₀B (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
    exact KG12618.factKv12618L52_holds _ _ hB'comm hB'iso hcomm hS2 hS8 hS'N
  ·
    rw [hpc] at hdim
    have hRK : R ≤ K := by
      intro r hr
      obtain ⟨hrT, -, hrZ, -⟩ := mem_centralizerSection.1 (hRc hr)
      exact h5 Γ (ZMod 2) hcardZ Y K hKY hYN hY0 e (pCoreOf 2 B) hZK hdim r (hT.1 hrT) hrZ
    obtain ⟨x, hxB', hx5⟩ := h2 (StatedSL 5 (ZMod 2)) _ hB'iso
    have hcU : ∀ u ∈ pCoreOf 2 ((B.subgroupOf K).map e.toMonoidHom), u * x = x * u → u = 1 := by
      intro u hu hux
      obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 ((B.subgroupOf K).map e.toMonoidHom) ⟨u, hu⟩
      have hm' := congrArg Subtype.val hm
      rw [Subgroup.coe_pow] at hm'
      exact h3 (ZMod 2) hcardZ x u hx5 ⟨m, hm'⟩ hux.symm
    have hh2 : ∀ d : ↥(StatedSL 5 (ZMod 2)), (∃ k : ℕ, d ^ 2 ^ k = 1) → d * x = x * d →
        d = 1 :=
      fun d hd hdx => h3 (ZMod 2) hcardZ x d hx5 hd hdx.symm
    have hR'le : (R.subgroupOf K).map e.toMonoidHom ≤
        pCoreOf 2 ((B.subgroupOf K).map e.toMonoidHom) := by
      intro s hs
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hs
      have hkR : (k : Γ) ∈ R := Subgroup.mem_subgroupOf.1 hk
      obtain ⟨hkT, -, hkZ, hkc⟩ := mem_centralizerSection.1 (hRc hkR)
      have hk2 : ∃ j : ℕ, e.toMonoidHom k ^ 2 ^ j = 1 := by
        obtain ⟨j, hj⟩ := hT.2.1 ⟨(k : Γ), hkT⟩
        refine ⟨j, ?_⟩
        have hk1 : k ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
        rw [← map_pow, hk1, map_one]
      have hcN : e.toMonoidHom k ∈
          Subgroup.normalizer (pCoreOf 2 ((B.subgroupOf K).map e.toMonoidHom) :
            Set ↥(StatedSL 5 (ZMod 2))) := by
        rw [Transport.pCoreOf_map_subgroupOf e 2 hBK, Transport.mem_normalizer_map_iff e hZK]
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
        exact hkZ
      have hcB : ∀ b ∈ (B.subgroupOf K).map e.toMonoidHom,
          b * e.toMonoidHom k * b⁻¹ * (e.toMonoidHom k)⁻¹ ∈
            pCoreOf 2 ((B.subgroupOf K).map e.toMonoidHom) := by
        intro b hb
        obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hb
        have hw : e.toMonoidHom j * e.toMonoidHom k * (e.toMonoidHom j)⁻¹ *
            (e.toMonoidHom k)⁻¹ = e.toMonoidHom (j * k * j⁻¹ * k⁻¹) := by
          simp only [map_mul, map_inv]
        rw [hw, Transport.pCoreOf_map_subgroupOf e 2 hBK]
        apply Subgroup.mem_map_of_mem
        rw [Subgroup.mem_subgroupOf]
        simpa using hkc (j : Γ) (Subgroup.mem_subgroupOf.1 hj)
      exact mem_of_two_elt (le_normalizer_pCoreOf 2 ((B.subgroupOf K).map e.toMonoidHom))
        (pCoreOf_isPGroup 2 ((B.subgroupOf K).map e.toMonoidHom)) hxB' hcU hh2 hk2 hcN hcB
    have hR'0 : (R.subgroupOf K).map e.toMonoidHom ≠ ⊥ := by
      intro hbot
      apply hR0
      have hsub : R.subgroupOf K = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).1 hbot
      have h' := Subgroup.map_subgroupOf_eq_of_le hRK
      rw [hsub, Subgroup.map_bot] at h'
      exact h'.symm
    have hnorm : Subgroup.normalizer
        (((R.subgroupOf K).map e.toMonoidHom : Subgroup ↥(StatedSL 5 (ZMod 2))) :
          Set ↥(StatedSL 5 (ZMod 2))) ≤
        Subgroup.normalizer
          (((B.subgroupOf K).map e.toMonoidHom : Subgroup ↥(StatedSL 5 (ZMod 2))) :
            Set ↥(StatedSL 5 (ZMod 2))) := by
      intro s hs
      rw [Transport.mem_normalizer_map_iff e hBK]
      have hmem : ((e.symm s : ↥K) : Γ) ∈ K ⊓ Subgroup.normalizer (R : Set Γ) :=
        ⟨(e.symm s).2, (Transport.mem_normalizer_map_iff e hRK s).1 hs⟩
      exact hKR hmem
    exact h7 (ZMod 2) hcardZ _ _ hB'comm hB'iso h16 hR'0 hR'le hnorm

end CFSG.Quasithin.H13.KG12617L52
