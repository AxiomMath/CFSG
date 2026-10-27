module

public import CFSG.RankThree.GF2n.Tim81.Sec4.NAbBeta
public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Bound
public import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzCommComm

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.QuasithinUnique.Setup.X7
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem conjSubgroup_xOf_eq_self_of_mem {y : G} (hy : y ∈ H) :
    conjSubgroup y (Tim79a.xOf V H) = Tim79a.xOf V H :=
  conjSubgroup_eq_self_iff.mpr (Tim79a.H_le_normalizer_xOf V H hy)

theorem conjSubgroup_kOf_eq_self_of_mem {y : G} (hy : y ∈ H) :
    conjSubgroup y (kOf V H) = kOf V H :=
  conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hy)

private theorem commutator_zpowers_le_range_commutatorElementHom
    {P : Subgroup G} (hZA : V ≤ Subgroup.centralizer (P : Set G))
    (hPP : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ V)
    {α : G} (hαP : α ∈ P) {A : Subgroup G} (hA : A ≤ P) :
    ⁅A, Subgroup.zpowers α⁆ ≤
      (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA
        (fun q hq => hPP α hαP q hq)).range.map V.subtype := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haP : a ∈ P := hA ha
  have hbP : b ∈ P := (Subgroup.zpowers_le.mpr hαP) hb
  have hcomm : ⁅a, α⁆ ∈
      (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA
        (fun q hq => hPP α hαP q hq)).range.map V.subtype := by
    have hinv : ⁅a, α⁆ = ⁅α, a⁆⁻¹ := (commutatorElement_inv α a).symm
    rw [hinv]
    refine (Subgroup.map V.subtype
      (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA
        (fun q hq => hPP α hαP q hq)).range).inv_mem ?_
    have hmemS : CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA
        (fun q hq => hPP α hαP q hq) (⟨a, haP⟩ : ↥P) ∈
        (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA
          (fun q hq => hPP α hαP q hq)).range :=
      ⟨(⟨a, haP⟩ : ↥P), rfl⟩
    have hmem : V.subtype (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA
        (fun q hq => hPP α hαP q hq) (⟨a, haP⟩ : ↥P)) ∈
        (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA
          (fun q hq => hPP α hαP q hq)).range.map V.subtype :=
      Subgroup.mem_map_of_mem V.subtype hmemS
    simpa [CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom_apply] using hmem
  have hb' : ⁅a, b⁆ ∈ Subgroup.zpowers ⁅a, α⁆ := by
    have hbP' : (⟨b, hbP⟩ : ↥P) ∈ Subgroup.zpowers (⟨α, hαP⟩ : ↥P) := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨n, by ext; simp⟩
    have hmem : CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom a hZA
        (fun q hq => hPP a haP q hq) (⟨b, hbP⟩ : ↥P) ∈
        Subgroup.map (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom a hZA
          (fun q hq => hPP a haP q hq)) (Subgroup.zpowers (⟨α, hαP⟩ : ↥P)) :=
      Subgroup.mem_map_of_mem
        (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom a hZA
          (fun q hq => hPP a haP q hq)) hbP'
    rw [MonoidHom.map_zpowers] at hmem
    have hmemG : V.subtype (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom a hZA
        (fun q hq => hPP a haP q hq) (⟨b, hbP⟩ : ↥P)) ∈
        (Subgroup.zpowers (CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom a hZA
          (fun q hq => hPP a haP q hq) (⟨α, hαP⟩ : ↥P))).map V.subtype :=
      Subgroup.mem_map_of_mem V.subtype hmem
    simpa [CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom_apply] using hmemG
  exact (Subgroup.zpowers_le.mpr hcomm) hb'

theorem subW_map_repW_sub_le {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    {X : Type} [Group X] (ψ : HBar V H ≃* X) {A B : Subgroup G}
    {b : G} (hb : b ∈ H)
    (hcomm : ⁅A, Subgroup.zpowers b⁆ ≤ B) :
    (subW hW A).map (repW hW ψ (ψ (piK V H ⟨b, hb⟩)) - 1) ≤ subW hW B := by
  rintro v ⟨u, hu, rfl⟩
  have hAu : ((toW hW u : ↥(Tim79a.xOf V H)) : G) ∈ A := hu
  have hcoe : repW hW ψ (ψ (piK V H ⟨b, hb⟩)) u =
      ofW hW (conjH V H ⟨b, hb⟩ (toW hW u)) := by
    rw [repW_apply_piK]
  rw [LinearMap.sub_apply, Module.End.one_apply, hcoe]
  change ofW hW (conjH V H ⟨b, hb⟩ (toW hW u)) - ofW hW (toW hW u) ∈ subW hW B
  have hsub : ofW hW (conjH V H ⟨b, hb⟩ (toW hW u)) - ofW hW (toW hW u) =
      ofW hW (conjH V H ⟨b, hb⟩ (toW hW u) * (toW hW u)⁻¹) := by
    rw [sub_eq_add_neg, ← ofW_inv, ← ofW_mul]
  rw [hsub, mem_subW_iff]
  have hcoe2 : ((conjH V H ⟨b, hb⟩ (toW hW u) * (toW hW u)⁻¹ :
      ↥(Tim79a.xOf V H)) : G) = ⁅b, (toW hW u : G)⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, conjH_apply_coe, commutatorElement_def]
  rw [hcoe2]
  have hmem : ⁅(toW hW u : G), b⁆ ∈ ⁅A, Subgroup.zpowers b⁆ :=
    Subgroup.commutator_mem_commutator hAu (Subgroup.mem_zpowers b)
  have hinv : ⁅b, (toW hW u : G)⁆ = ⁅(toW hW u : G), b⁆⁻¹ :=
    (commutatorElement_inv (toW hW u : G) b).symm
  rw [hinv]
  exact B.inv_mem (hcomm hmem)

namespace RootHyp

theorem commutator_le_inf_conj_of_commutator_inf_conj_kOf_eq_bot
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥)
    {X : Subgroup G} (hXP : X ≤ conjSubgroup h₀ (Pc M V))
    (hXK : ⁅X, conjSubgroup h₀ (Pc M V) ⊓ kOf V H⁆ = ⊥) :
    ⁅X, conjSubgroup h₀ (Pc M V)⁆ ≤ conjSubgroup h₀ V ⊓ W₀ := by
  classical
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hyinv : y⁻¹ ∈ H := H.inv_mem hyH
  have hX'P : conjSubgroup y⁻¹ X ≤ Pc M V := by
    have hle : conjSubgroup y⁻¹ X ≤ conjSubgroup y⁻¹ (conjSubgroup y (Pc M V)) := by
      rw [← hPy]
      exact Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hXP
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hle
  have hX'K : ⁅conjSubgroup y⁻¹ X, Pc M V ⊓ kOf V H⁆ = ⊥ := by
    have h := congrArg (conjSubgroup y⁻¹) hXK
    have hL : conjSubgroup y⁻¹ ⁅X, conjSubgroup h₀ (Pc M V) ⊓ kOf V H⁆ =
        ⁅conjSubgroup y⁻¹ X,
          conjSubgroup y⁻¹ (conjSubgroup h₀ (Pc M V) ⊓ kOf V H)⁆ := by
      change Subgroup.map (MulAut.conj y⁻¹).toMonoidHom
          ⁅X, conjSubgroup h₀ (Pc M V) ⊓ kOf V H⁆ =
        ⁅Subgroup.map (MulAut.conj y⁻¹).toMonoidHom X,
          Subgroup.map (MulAut.conj y⁻¹).toMonoidHom
            (conjSubgroup h₀ (Pc M V) ⊓ kOf V H)⁆
      exact Subgroup.map_commutator X (conjSubgroup h₀ (Pc M V) ⊓ kOf V H)
        (MulAut.conj y⁻¹).toMonoidHom
    rw [hL, hPy, conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one, conjSubgroup_kOf_eq_self_of_mem hyinv, conjSubgroup_bot] at h
    exact h
  have hmain := RootHyp.commutator_le_inf_of_commutator_inf_kOf_eq_bot h hPH hVH hH hnM hK
    hnab hL hW₀ hN hW₀ne hX'P hX'K
  have hconj := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hmain
  change conjSubgroup y ⁅conjSubgroup y⁻¹ X, Pc M V⁆ ≤ conjSubgroup y (V ⊓ W₀) at hconj
  have hcomm : conjSubgroup y ⁅conjSubgroup y⁻¹ X, Pc M V⁆ =
      ⁅X, conjSubgroup y (Pc M V)⁆ := by
    calc conjSubgroup y ⁅conjSubgroup y⁻¹ X, Pc M V⁆
        = ⁅conjSubgroup y (conjSubgroup y⁻¹ X), conjSubgroup y (Pc M V)⁆ := by
          change Subgroup.map (MulAut.conj y).toMonoidHom
              ⁅conjSubgroup y⁻¹ X, Pc M V⁆ =
            ⁅Subgroup.map (MulAut.conj y).toMonoidHom (conjSubgroup y⁻¹ X),
              Subgroup.map (MulAut.conj y).toMonoidHom (Pc M V)⁆
          exact Subgroup.map_commutator (conjSubgroup y⁻¹ X) (Pc M V)
            (MulAut.conj y).toMonoidHom
      _ = ⁅X, conjSubgroup y (Pc M V)⁆ := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  rw [hcomm] at hconj
  calc ⁅X, conjSubgroup h₀ (Pc M V)⁆
      = ⁅X, conjSubgroup y (Pc M V)⁆ := by rw [hPy]
    _ ≤ conjSubgroup y (V ⊓ W₀) := hconj
    _ = conjSubgroup y V ⊓ conjSubgroup y W₀ := by rw [conjSubgroup_inf]
    _ = conjSubgroup y V ⊓ W₀ := by
        rw [conjSubgroup_eq_self_iff.mpr (hN hyH)]
    _ = conjSubgroup h₀ V ⊓ W₀ := by rw [← hVy]

theorem commutator_inf_conj_Pc_conj_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hW₀ne : W₀ ≠ ⊥) :
    ⁅Pc M V ⊓ conjSubgroup h₀ (Pc M V), conjSubgroup h₀ (Pc M V)⁆ ≤
      conjSubgroup h₀ V ⊓ W₀ := by
  refine RootHyp.commutator_le_inf_conj_of_commutator_inf_conj_kOf_eq_bot h hPH hVH hH hnM hK
    hnab hL hW₀ hN hW₀ne inf_le_right ?_
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  have haP : a ∈ Pc M V := ha.1
  have haPy : a ∈ conjSubgroup h₀ (Pc M V) := ha.2
  have hbP : b ∈ conjSubgroup h₀ (Pc M V) := hb.1
  have hbK : b ∈ kOf V H := hb.2
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2' : IsPGroup 2 (conjSubgroup h₀ (Pc M V)) :=
    hP2.map (MulAut.conj h₀).toMonoidHom
  have hV' : ⁅a, b⁆ ∈ conjSubgroup h₀ V := by
    have hphi := commutatorElement_mem_inSubgroup_frattini hP2' haPy hbP
    have hle : inSubgroup frattini (conjSubgroup h₀ (Pc M V)) ≤ conjSubgroup h₀ V :=
      RootHyp.frattini_conj_le hP2 h.toHyp.frattini_Pc_le h₀
    exact hle hphi
  have hP : ⁅a, b⁆ ∈ Pc M V := by
    have hbM : b ∈ M := kOf_le_M h hbK
    have hbN : b ∈ Subgroup.normalizer (Pc M V : Set G) := h.toHyp.le_normalizer_Pc hbM
    have h1 : b * a⁻¹ * b⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp hbN (a⁻¹)).mp ((Pc M V).inv_mem haP)
    have he : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact (Pc M V).mul_mem haP h1
  have hmem : ⁅a, b⁆ ∈ conjSubgroup h₀ V ⊓ Pc M V := Subgroup.mem_inf.mpr ⟨hV', hP⟩
  rw [RootHyp.conjSubgroup_inf_Pc_eq_bot h hH hnM] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem exists_minimal_normalized_le_inf_commutator
    (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) :
    ∃ W₀ : Subgroup G, W₀ ≤ Tim79a.xOf V H ⊓ ⁅kOf V H, kOf V H⁆ ∧ W₀ ≠ ⊥ ∧
      H ≤ Subgroup.normalizer (W₀ : Set G) ∧
      ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
        H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀ := by
  classical
  set K' : Subgroup G := ⁅kOf V H, kOf V H⁆ with hK'
  have hVK'_ne : V ⊓ K' ≠ ⊥ := RootHyp.inf_commutator_kOf_ne_bot h hPH hK hnab
  have hne : Tim79a.xOf V H ⊓ K' ≠ ⊥ := by
    intro hbot
    apply hVK'_ne
    rw [eq_bot_iff]
    intro x hx
    have hxW : x ∈ Tim79a.xOf V H := le_xOf_self V H hx.1
    have hmem : x ∈ Tim79a.xOf V H ⊓ K' := Subgroup.mem_inf.mpr ⟨hxW, hx.2⟩
    rwa [hbot] at hmem
  have hN : H ≤ Subgroup.normalizer (Tim79a.xOf V H ⊓ K' : Subgroup G) := by
    intro z hz
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_inf,
      conjSubgroup_xOf_eq_self_of_mem hz]
    have hzK' : conjSubgroup z K' = K' := by
      rw [hK']
      calc conjSubgroup z ⁅kOf V H, kOf V H⁆
          = ⁅conjSubgroup z (kOf V H), conjSubgroup z (kOf V H)⁆ :=
            Subgroup.map_commutator _ _ (MulAut.conj z).toMonoidHom
        _ = ⁅kOf V H, kOf V H⁆ := by rw [conjSubgroup_kOf_eq_self_of_mem hz]
    rw [hzK']
  exact exists_minimal_normalized_le (H := H) (E := Tim79a.xOf V H ⊓ K') hne hN

private theorem exists_alpha_not_mem_kOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥) :
    ∃ c ∈ Subgroup.centralizer (V : Set G), ∃ x ∈ Pc M V ⊓ W₀,
      ∃ α : G, α = MulAut.conj c x ∧ α ∈ Pc M V ∧ α ∈ H ∧ α ≠ 1 ∧
        α ∉ kOf V H := by
  obtain ⟨E, hEdef, hE_le_P, hE_notK, hP_eq⟩ :=
    RootHyp.exists_beta_decomposition h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  obtain ⟨c, hc, x, hx, hαK⟩ : ∃ c ∈ Subgroup.centralizer (V : Set G),
      ∃ x ∈ Pc M V ⊓ W₀, MulAut.conj c x ∉ kOf V H := by
    by_contra hcon
    push Not at hcon
    apply hE_notK
    rw [hEdef]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨c, hc, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact hcon c hc x hx
  set α : G := MulAut.conj c x with hα
  have hαP : α ∈ Pc M V := by
    have hcM : c ∈ M := h.centralizer_le_M hc
    have hcx : conjSubgroup c (Pc M V) = Pc M V :=
      conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hcM)
    rw [hα]
    exact hcx ▸ conj_mem_conjSubgroup c hx.1
  have hαH : α ∈ H := hPH hαP
  have hα1 : α ≠ 1 := by
    intro h1
    apply hαK
    rw [h1]
    exact (kOf V H).one_mem
  exact ⟨c, hc, x, hx, α, hα, hαP, hαH, hα1, hαK⟩

private theorem card_inf_kOf_le_card_inf_centralizer
    (h : RootHyp M V) {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    {c x α : G} (hc : c ∈ Subgroup.centralizer (V : Set G))
    (hx : x ∈ Pc M V ⊓ W₀) (hα : α = MulAut.conj c x) :
    Nat.card ↥(Pc M V ⊓ kOf V H) ≤
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G)) := by
  classical
  have hle : conjSubgroup c (Pc M V ⊓ kOf V H) ≤
      Pc M V ⊓ Subgroup.centralizer ({α} : Set G) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have hkP : k ∈ Pc M V := hk.1
    have hkK : k ∈ kOf V H := hk.2
    have hcM : c ∈ M := h.centralizer_le_M hc
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hcx : conjSubgroup c (Pc M V) = Pc M V :=
        conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hcM)
      change MulAut.conj c k ∈ Pc M V
      rw [← hcx]
      exact conj_mem_conjSubgroup c hkP
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hα]
      have hxW : x ∈ Tim79a.xOf V H := hW₀ hx.2
      have hkx : k * x = x * k :=
        (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hkK).2 x hxW).symm
      calc MulAut.conj c k * MulAut.conj c x
            = c * (k * x) * c⁻¹ := by
              simp only [CFSG.CGT.Timmesfeld75.conjSubgroup, MulAut.conj_apply]
              group
          _ = c * (x * k) * c⁻¹ := by rw [hkx]
          _ = MulAut.conj c x * MulAut.conj c k := by
              simp only [CFSG.CGT.Timmesfeld75.conjSubgroup, MulAut.conj_apply]
              group
  calc Nat.card ↥(Pc M V ⊓ kOf V H)
      = Nat.card ↥(conjSubgroup c (Pc M V ⊓ kOf V H)) :=
        (card_conjSubgroup c (Pc M V ⊓ kOf V H)).symm
    _ ≤ Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G)) :=
        Nat.card_le_card_of_injective
          (fun y : ↥(conjSubgroup c (Pc M V ⊓ kOf V H)) =>
            (⟨y.1, hle y.2⟩ : ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G))))
          (fun y z hyz => Subtype.ext (congrArg (fun t => t.1) hyz))

private theorem card_range_commutatorElementHom_map_le
    (hPH : Pc M V ≤ H) {α : G}
    (hZA : V ≤ Subgroup.centralizer (Pc M V : Set G))
    (hxV : ∀ q ∈ Pc M V, ⁅α, q⁆ ∈ V)
    (hcardK_le : Nat.card ↥(Pc M V ⊓ kOf V H) ≤
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G))) :
    Nat.card ((CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA hxV).range.map
      V.subtype) ≤ Nat.card (imgK V H (Pc M V)) := by
  let φ : ↥(Pc M V) →* ↥V :=
    CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA hxV
  have hφcard : Nat.card φ.range *
      Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G)) = Nat.card (Pc M V) := by
    have hcard := Subgroup.card_ker_mul_card_range φ
    rw [CFSG.LocalAnalysis.EvenBN.Common.ker_commutatorElementHom] at hcard
    have hker : Nat.card
        ↥((Pc M V ⊓ Subgroup.centralizer ({α} : Set G)).subgroupOf (Pc M V)) =
        Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Pc M V ⊓ Subgroup.centralizer ({α} : Set G) ≤ Pc M V)).toEquiv
    rw [hker, mul_comm] at hcard
    exact hcard
  have hcardRange_le : Nat.card (φ.range.map V.subtype) ≤
      Nat.card (imgK V H (Pc M V)) := by
    have h1' : Nat.card (φ.range.map V.subtype) *
        Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G)) =
        Nat.card (Pc M V) := by
      rw [Subgroup.card_map_of_injective (f := V.subtype) V.subtype_injective]
      exact hφcard
    have h2 := card_imgK_mul_card_inf (V := V) (H := H) (X := Pc M V) hPH
    have h3 : Nat.card (φ.range.map V.subtype) *
        Nat.card ↥(Pc M V ⊓ kOf V H) ≤
        Nat.card (imgK V H (Pc M V)) * Nat.card ↥(Pc M V ⊓ kOf V H) := by
      calc Nat.card (φ.range.map V.subtype) *
            Nat.card ↥(Pc M V ⊓ kOf V H)
          ≤ Nat.card (φ.range.map V.subtype) *
              Nat.card ↥(Pc M V ⊓ Subgroup.centralizer ({α} : Set G)) :=
            Nat.mul_le_mul_left _ hcardK_le
        _ = Nat.card (Pc M V) := h1'
        _ = Nat.card (imgK V H (Pc M V)) * Nat.card ↥(Pc M V ⊓ kOf V H) := h2.symm
    exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos
  exact hcardRange_le

private theorem card_range_commutatorElementHom_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    {c x α : G} (hc : c ∈ Subgroup.centralizer (V : Set G))
    (hx : x ∈ Pc M V ⊓ W₀) (hα : α = MulAut.conj c x)
    (hZA : V ≤ Subgroup.centralizer (Pc M V : Set G))
    (hxV : ∀ q ∈ Pc M V, ⁅α, q⁆ ∈ V) :
    Nat.card ((CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA hxV).range.map
      V.subtype) ≤ Nat.card (imgK V H (Pc M V)) := by
  exact card_range_commutatorElementHom_map_le hPH hZA hxV
    (card_inf_kOf_le_card_inf_centralizer h hW₀ hc hx hα)

private theorem card_range_commutatorElementHom_le_two_pow
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    {c x α : G} (hc : c ∈ Subgroup.centralizer (V : Set G))
    (hx : x ∈ Pc M V ⊓ W₀) (hα : α = MulAut.conj c x)
    (hZA : V ≤ Subgroup.centralizer (Pc M V : Set G))
    (hxV : ∀ q ∈ Pc M V, ⁅α, q⁆ ∈ V)
    {a : ℕ} (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hcard : Fintype.card F = 2 ^ (2 * a + 1))
    (ψ : HBar V H ≃* CFSG.Blueprint.suzukiGroup a F) :
    Nat.card ((CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA hxV).range.map
      V.subtype) ≤ 2 ^ (2 * a + 1) := by
  have hcardRange_le := card_range_commutatorElementHom_le h hPH
    hW₀ hc hx hα hZA hxV
  have hPbarCard : Nat.card (imgK V H (Pc M V)) = 2 ^ (2 * a + 1) := by
    have h := (imgK_map_sz h hPH hVH hH hnM hcard ψ).1
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, h]
  rw [← hPbarCard]
  exact hcardRange_le

private theorem card_commutator_W0_P_zpowers_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {α : G} (hαP : α ∈ Pc M V)
    (hZA : V ≤ Subgroup.centralizer (Pc M V : Set G))
    (hxV : ∀ q ∈ Pc M V, ⁅α, q⁆ ∈ V)
    (hPP : ∀ a ∈ Pc M V, ∀ b ∈ Pc M V, ⁅a, b⁆ ∈ V)
    {a : ℕ}
    (hRangeCard : Nat.card
      ((CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA hxV).range.map
        V.subtype) ≤ 2 ^ (2 * a + 1)) :
    Nat.card (⁅⁅W₀, Pc M V⁆, Subgroup.zpowers α⁆ : Subgroup G) ≤ 2 ^ (2 * a + 1) := by
  let φ : ↥(Pc M V) →* ↥V :=
    CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom α hZA hxV
  set A : Subgroup G := ⁅W₀, Pc M V⁆ with hA
  have hA_le_P : A ≤ Pc M V := by
    rw [hA]
    exact (RootHyp.commutator_W0_Pc_le h hPH hVH hW₀ hN).trans inf_le_left
  set B : Subgroup G := ⁅A, Subgroup.zpowers α⁆ with hB
  have hB_le_V : B ≤ V := by
    rw [hB]
    exact (Subgroup.commutator_mono hA_le_P (Subgroup.zpowers_le.mpr hαP)).trans
      (Subgroup.commutator_le.mpr hPP)
  have hB_le_range : B ≤ φ.range.map V.subtype := by
    simpa [φ] using
      commutator_zpowers_le_range_commutatorElementHom hZA hPP hαP hA_le_P
  exact (Nat.card_le_card_of_injective
    (fun y : ↥B =>
      (⟨y.1, hB_le_range y.2⟩ : ↥(φ.range.map V.subtype)))
    (fun y z hyz => Subtype.ext (congrArg (fun t => t.1) hyz))).trans hRangeCard

private theorem card_commSub_map_le
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {α : G} (hαP : α ∈ Pc M V) (hαH : α ∈ H)
    (hPP : ∀ a ∈ Pc M V, ∀ b ∈ Pc M V, ⁅a, b⁆ ∈ V)
    {a : ℕ} (F : Type) [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* CFSG.Blueprint.suzukiGroup a F)
    (hBCard : Nat.card (⁅⁅W₀, Pc M V⁆, Subgroup.zpowers α⁆ : Subgroup G) ≤ 2 ^ (2 * a + 1)) :
    Nat.card ((commSub (subRepW hW ψ hW₀ hN)
      ((imgK V H (Pc M V)).map ψ.toMonoidHom)).map
      ((subRepW hW ψ hW₀ hN) (ψ (piK V H ⟨α, hαH⟩)) - 1)) ≤ 2 ^ (2 * a + 1) := by
  classical
  let X₀ : Submodule (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) :=
    subW hW W₀
  let ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a F) X₀ :=
    subRepW hW ψ hW₀ hN
  let T : Subgroup ↥(CFSG.Blueprint.suzukiGroup a F) :=
    (imgK V H (Pc M V)).map ψ.toMonoidHom
  let xbar : ↥(CFSG.Blueprint.suzukiGroup a F) := ψ (piK V H ⟨α, hαH⟩)
  set A : Subgroup G := ⁅W₀, Pc M V⁆ with hA
  have hA_le_P : A ≤ Pc M V := by
    rw [hA]
    exact (RootHyp.commutator_W0_Pc_le h hPH hVH hW₀ hN).trans inf_le_left
  have hA_le_W : A ≤ Tim79a.xOf V H := by
    rw [hA]
    exact (RootHyp.commutator_W0_Pc_le h hPH hVH hW₀ hN).trans (inf_le_right.trans hW₀)
  set B : Subgroup G := ⁅A, Subgroup.zpowers α⁆ with hB
  have hB_le_V : B ≤ V := by
    rw [hB]
    exact (Subgroup.commutator_mono hA_le_P (Subgroup.zpowers_le.mpr hαP)).trans
      (Subgroup.commutator_le.mpr hPP)
  have hB_le_W : B ≤ Tim79a.xOf V H := hB_le_V.trans (le_xOf_self V H)
  have hcommSub : (commSub ρ T).map X₀.subtype = subW hW A := by
    simpa [X₀, ρ, T, A] using commSub_subRepW (hW := hW) (ψ := ψ) hW₀ hN hPH
  have hmap1 : ((commSub ρ T).map (ρ xbar - 1)).map X₀.subtype =
      (subW hW A).map (repW hW ψ xbar - 1) := by
    rw [← Submodule.map_comp]
    change (commSub ρ T).map ((repW hW ψ xbar - 1).comp X₀.subtype) =
      (subW hW A).map (repW hW ψ xbar - 1)
    rw [Submodule.map_comp, hcommSub]
  have hcardEq : Nat.card ((commSub ρ T).map (ρ xbar - 1)) =
      Nat.card ((subW hW A).map (repW hW ψ xbar - 1)) := by
    have h := Nat.card_congr (Submodule.equivMapOfInjective X₀.subtype
      (Submodule.subtype_injective X₀) ((commSub ρ T).map (ρ xbar - 1))).toEquiv
    rw [h, hmap1]
  have hcardLe : Nat.card ((commSub ρ T).map (ρ xbar - 1)) ≤ 2 ^ (2 * a + 1) := by
    rw [hcardEq]
    have h1 : Nat.card ((subW hW A).map (repW hW ψ xbar - 1)) ≤ Nat.card (subW hW B) :=
      Nat.card_le_card_of_injective
        (fun y : ↥((subW hW A).map (repW hW ψ xbar - 1)) =>
          (⟨y.1, subW_map_repW_sub_le (hW := hW) ψ hαH
            (le_of_eq hB.symm) y.2⟩ : ↥(subW hW B)))
        (fun y z hyz => Subtype.ext (congrArg (fun t => t.1) hyz))
    calc Nat.card ((subW hW A).map (repW hW ψ xbar - 1))
        ≤ Nat.card (subW hW B) := h1
      _ = Nat.card B := natCard_subW hW hB_le_W
      _ ≤ 2 ^ (2 * a + 1) := hBCard
  exact hcardLe

private theorem suzuki_contradiction
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (a : ℕ) (F : Type) [Field F] [Fintype F] [CharP F 2] (ha : 1 ≤ a)
    (hcard : Fintype.card F = 2 ^ (2 * a + 1))
    (ψ : HBar V H ≃* CFSG.Blueprint.suzukiGroup a F)
    {α : G} (hαP : α ∈ Pc M V) (hαH : α ∈ H) (hαK : α ∉ kOf V H)
    (hcardLe : Nat.card ((commSub (subRepW hW ψ hW₀ hN)
      ((imgK V H (Pc M V)).map ψ.toMonoidHom)).map
      ((subRepW hW ψ hW₀ hN) (ψ (piK V H ⟨α, hαH⟩)) - 1)) ≤ 2 ^ (2 * a + 1)) :
    False := by
  classical
  let X₀ : Submodule (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW)) :=
    subW hW W₀
  let ρ : Representation (ZMod 2) ↥(CFSG.Blueprint.suzukiGroup a F) X₀ :=
    subRepW hW ψ hW₀ hN
  let T : Subgroup ↥(CFSG.Blueprint.suzukiGroup a F) :=
    (imgK V H (Pc M V)).map ψ.toMonoidHom
  let xbar : ↥(CFSG.Blueprint.suzukiGroup a F) := ψ (piK V H ⟨α, hαH⟩)
  haveI : Fact ρ.IsIrreducible := ⟨isIrreducible_subRepW hW ψ hW₀ hN hW₀ne hmin⟩
  have hnt := exists_apply_subRepW_ne_one h hPH hH hnM ψ hW₀ hN hW₀ne
  obtain ⟨-, g, -, hgT, -, -⟩ := imgK_map_sz h hPH hVH hH hnM hcard ψ
  have hxT : xbar ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (Sec2.szZ a F) := by
    rw [← hgT]
    exact Subgroup.mem_map.mpr ⟨piK V H ⟨α, hαH⟩,
      Subgroup.mem_map.mpr ⟨⟨α, hαH⟩, Subgroup.mem_subgroupOf.mpr hαP, rfl⟩, rfl⟩
  have hx1 : xbar ≠ 1 := by
    intro h1
    apply hαK
    have h2 : piK V H ⟨α, hαH⟩ = 1 := ψ.injective (by simpa [xbar] using h1)
    exact (piK_eq_one_iff (V := V) (H := H) ⟨α, hαH⟩).mp h2
  have hKcard : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  rcases isSzNatural_or_two_pow_lt_card_commSub_map (K := F) hKcard ha ρ hnt g hxT hx1 with
    hnat | hbig
  · exact RootHyp.not_isSzNatural_subRepW h hPH hVH hH hnM hcard ψ hW₀ hN hW₀ne hnat
  · rw [← hgT] at hbig
    exact absurd hcardLe (not_le.mpr hbig)

theorem isEmpty_hBar_equiv_suzuki_of_nonabelian
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀)
    (a : ℕ) (F : Type) [Field F] [Fintype F] [CharP F 2] (ha : 1 ≤ a)
    (hcard : Fintype.card F = 2 ^ (2 * a + 1)) :
    IsEmpty (HBar V H ≃* CFSG.Blueprint.suzukiGroup a F) := by
  classical
  refine ⟨fun ψ => ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, x, hx, α, hα, hαP, hαH, hα1, hαK⟩ :=
    exists_alpha_not_mem_kOf h hPH hVH hH hnM hK hnab hL hW₀ hN hW₀ne
  have hPP : ∀ a ∈ Pc M V, ∀ b ∈ Pc M V, ⁅a, b⁆ ∈ V := by
    intro a ha b hb
    exact h.toHyp.frattini_Pc_le
      (commutatorElement_mem_inSubgroup_frattini
        ((inSubgroup_pCore_two M).1.to_le inf_le_left) ha hb)
  have hZA : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp hp.2 z hz).symm
  have hxV : ∀ q ∈ Pc M V, ⁅α, q⁆ ∈ V := fun q hq => hPP α hαP q hq
  have hRangeCard :=
    card_range_commutatorElementHom_le_two_pow h hPH hVH hH hnM
      hW₀ hc hx hα hZA hxV F hcard ψ
  have hBCard :=
    card_commutator_W0_P_zpowers_le h hPH hVH hW₀ hN hαP hZA hxV hPP hRangeCard
  have hcardLe := card_commSub_map_le hW h hPH hVH hW₀ hN hαP hαH hPP F ψ hBCard
  exact suzuki_contradiction hW h hPH hVH hH hnM hW₀ hN hW₀ne hmin a F ha hcard ψ
    hαP hαH hαK hcardLe

theorem exists_sl2_of_nonabelian
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (CFSG.Quasithin.IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x)
    (hL : IsL2OrSz V H)
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2),
      4 ≤ Fintype.card F ∧ Nonempty (HBar V H ≃* SL(2, F)) := by
  have hL' := hL
  rcases hL with ⟨F, hField, hFintype, hCharP, h4, hψ⟩ |
    ⟨a, F, hField, hFintype, hCharP, ha, hcard, hψ⟩
  · exact ⟨F, hField, hFintype, hCharP, h4, hψ⟩
  · letI := hField
    letI := hFintype
    letI := hCharP
    obtain ⟨ψ⟩ := hψ
    exact (isEmpty_hBar_equiv_suzuki_of_nonabelian h hPH hVH hH hnM hK hnab hL'
      hW₀ hN hW₀ne hmin a F ha hcard).elim ψ

end RootHyp

end CFSG.RankThree.GF2n.Tim81
