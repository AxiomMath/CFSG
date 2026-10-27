module

public import CFSG.RankThree.GF2n.Stroth80.Sec101SLPt
public import CFSG.RankThree.GF2n.Stroth80.Sec111Norm
public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GF2n.Stroth80.Sec101Roots

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec10Hyp.exists_Rt_ne {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) :
    ∃ t ∈ LB M Q B, t ∉ Q ∧ SLlike hc t ∧ Rt M (LB M Q B) t ≠ LB M Q B := by
  obtain ⟨t, ht, htQ, hsl⟩ := H.ex
  refine ⟨t, ht, htQ, hsl, fun hR => ?_⟩
  obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
  have hle : Vt M (LB M Q B) B Z t ≤ B ⊔ Z := by
    refine sec39_Vt_le le_sup_right fun k hk hT => ?_
    have h1 : LB M Q (conjSubgroup k B) ≤ LB M Q B := hR ▸ hc.LB_conj_le_Rt hk hT
    have h2 : LB M Q (conjSubgroup k B) = LB M Q B :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hc.LB_conj hk, card_conjSubgroup])
    exact le_sup_left.trans
      ((IsRootB.LB_eq_iff H ((IsRootB.self (M := M)).conj hk) IsRootB.self).mp h2).le
  have hcard := Subgroup.card_le_of_le hle
  rw [SLMNat.card_Vt hslm, hc.card_sup_Z, ((IsRootB.self (M := M)).isZConjugate hc).card_eq]
    at hcard
  have hq := hc.hyp.q4
  have h3 : Nat.card Z ^ 2 < Nat.card Z ^ (m + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  rw [sq] at h3
  exact absurd hcard (not_le.mpr h3)

theorem Ctx.exists_kerX (hc : Ctx M Q Z B) (X : Subgroup G) :
    ∃ KX : Subgroup G, ∀ g, g ∈ KX ↔
      g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧ ∀ x ∈ X, ⁅x, g⁆ ∈ Z := by
  refine ⟨{ carrier := {g | g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧ ∀ x ∈ X, ⁅x, g⁆ ∈ Z}
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨(M ⊓ Subgroup.normalizer (X : Set G)).mul_mem ha hb, fun x hx => ?_⟩
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (hax x hx)
      ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha.1) _).mp (hbx x hx))
  · exact ⟨(M ⊓ Subgroup.normalizer (X : Set G)).one_mem, fun x _ => by
      rw [commutatorElement_one_right]; exact Z.one_mem⟩
  · rintro a ⟨ha, hax⟩
    refine ⟨(M ⊓ Subgroup.normalizer (X : Set G)).inv_mem ha, fun x hx => ?_⟩
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem ha.1)) _).mp
      (Z.inv_mem (hax x hx))

private theorem kerX_contains_Q (hc : Ctx M Q Z B) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) {KX : Subgroup G}
    (hKX : ∀ g, g ∈ KX ↔ g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, ⁅x, g⁆ ∈ Z) :
    Q ≤ KX := by
  intro q hq
  refine (hKX q).mpr ⟨⟨hc.hyp.Q_normal.1 hq, ?_⟩, fun x hx => ?_⟩
  · exact Subgroup.mem_normalizer_fintype fun x hx => by
      rw [show q * x * q⁻¹ = ⁅q, x⁆ * x by rw [commutatorElement_def]; group]
      exact X.mul_mem (hX.Z_le (Smith81.comm_mem_Z hc.hyp hq (hX.le_Q hx))) hx
  · exact Smith81.comm_mem_Z hc.hyp (hX.le_Q hx) hq

private theorem normalizer_inf_le_normalizer_kerX (hc : Ctx M Q Z B) {X : Subgroup G}
    {KX : Subgroup G}
    (hKX : ∀ g, g ∈ KX ↔ g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, ⁅x, g⁆ ∈ Z) :
    M ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (KX : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun k hk => (hKX _).mpr ⟨?_, fun x hx => ?_⟩
  · have hk' := ((hKX k).mp hk).1
    exact (M ⊓ Subgroup.normalizer (X : Set G)).mul_mem
      ((M ⊓ Subgroup.normalizer (X : Set G)).mul_mem hg hk')
      ((M ⊓ Subgroup.normalizer (X : Set G)).inv_mem hg)
  · have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg.2) x).mp hx
    have h1 := ((hKX k).mp hk).2 _ hx'
    have e : ⁅x, g * k * g⁻¹⁆ = g * ⁅g⁻¹ * x * g⁻¹⁻¹, k⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg.1) _).mp h1

private theorem kerX_le_normalizer_LB (hc : Ctx M Q Z B) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hBX : B ≤ X) {KX : Subgroup G}
    (hKX : ∀ g, g ∈ KX ↔ g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, ⁅x, g⁆ ∈ Z) :
    KX ≤ Subgroup.normalizer (LB M Q B : Set G) := by
  intro k hk
  have hk' := (hKX k).mp hk
  have hkBZ : k ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun y hy => by
      rw [show k * y * k⁻¹ = ⁅y, k⁆⁻¹ * y by rw [commutatorElement_def]; group]
      exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right
        (Z.inv_mem (hk'.2 y (sup_le hBX hX.Z_le hy)))) hy
  exact hc.mem_normalizer_LB_of_normalizer hk'.1.1 hkBZ

private theorem kerX_le_normalizer_inf_LB_kerX (hc : Ctx M Q Z B) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hBX : B ≤ X) {KX : Subgroup G}
    (hKX : ∀ g, g ∈ KX ↔ g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, ⁅x, g⁆ ∈ Z) :
    KX ≤ Subgroup.normalizer ((LB M Q B ⊓ KX : Subgroup G) : Set G) := by
  intro k hk
  have hkL : k ∈ Subgroup.normalizer (LB M Q B : Set G) :=
    kerX_le_normalizer_LB hc hX hBX hKX hk
  refine Subgroup.mem_normalizer_fintype fun p hp => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hkL p).mp hp.1
  · exact KX.mul_mem (KX.mul_mem hk hp.2) (KX.inv_mem hk)

private theorem bar_inf_kerX_le_pCore [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {X : Subgroup G} (hX : IsClique101 M Q Z B X) (hBX : B ≤ X) {KX : Subgroup G}
    (hKX : ∀ g, g ∈ KX ↔ g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, ⁅x, g⁆ ∈ Z) :
    bar M Q (LB M Q B ⊓ KX) ≤
      inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) := by
  have hQK : Q ≤ KX := kerX_contains_Q hc hX hKX
  have hKN : KX ≤ M ⊓ Subgroup.normalizer (X : Set G) := fun g hg => ((hKX g).mp hg).1
  have hKM : KX ≤ M := hKN.trans inf_le_left
  have hNK : M ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (KX : Set G) :=
    normalizer_inf_le_normalizer_kerX hc hKX
  have hKP : KX ≤ Subgroup.normalizer ((LB M Q B ⊓ KX : Subgroup G) : Set G) :=
    kerX_le_normalizer_inf_LB_kerX hc hX hBX hKX
  have hQP : Q ≤ LB M Q B ⊓ KX := le_inf le_sup_left hQK
  have hPM : LB M Q B ⊓ KX ≤ M := inf_le_left.trans hc.LB_le_M
  have hKbar : bar M Q KX ≤ bar M Q (M ⊓ Subgroup.normalizer (X : Set G)) :=
    Subgroup.map_mono fun x hx => hKN hx
  have hNbar : bar M Q (M ⊓ Subgroup.normalizer (X : Set G)) ≤
      Subgroup.normalizer (bar M Q KX : Set (Mbar M Q)) :=
    bar_le_normalizer_of_le_normalizer hQK hKM inf_le_left hNK
  have hPbar : bar M Q (LB M Q B ⊓ KX) ≤ bar M Q KX :=
    Subgroup.map_mono fun x hx => (inf_le_right : LB M Q B ⊓ KX ≤ KX) hx
  have hKPbar : bar M Q KX ≤ Subgroup.normalizer (bar M Q (LB M Q B ⊓ KX) : Set (Mbar M Q)) :=
    bar_le_normalizer_of_le_normalizer hQP hPM hKM hKP
  have hP2 : IsPGroup 2 (bar M Q (LB M Q B ⊓ KX)) :=
    (CFSG.Open.IsElemAbelian.isPGroup hc.isElemAbelian_bar_LB).to_le
      (Subgroup.map_mono fun x hx => (inf_le_left : LB M Q B ⊓ KX ≤ LB M Q B) hx)
  have hPO : bar M Q (LB M Q B ⊓ KX) ≤ inSubgroup (pCore 2) (bar M Q KX) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore hP2 hPbar hKPbar
  have hKO : inSubgroup (pCore 2) (bar M Q KX) ≤
      inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_mono hKbar hNbar
  exact hPO.trans hKO

private theorem exists_mem_LB_kerX_not_mem_Q (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X) (hBX : B ≤ X)
    {KX : Subgroup G}
    (hKX : ∀ g, g ∈ KX ↔ g ∈ M ⊓ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, ⁅x, g⁆ ∈ Z) :
    ∃ t, t ∈ LB M Q B ∧ t ∉ Q ∧ t ∈ KX := by
  obtain ⟨t, htB, htQ, -, hR⟩ := H.exists_Rt_ne
  have hcomm := IsSaturated101.comm_mem_Z h34 H hX hsat IsRootB.self hBX htB htQ hR
  refine ⟨t, htB, htQ, (hKX t).mpr ⟨⟨hc.LB_le_M htB, ?_⟩, hcomm⟩⟩
  exact Subgroup.mem_normalizer_fintype fun x hx => by
    rw [show t * x * t⁻¹ = ⁅x, t⁆⁻¹ * x by rw [commutatorElement_def]; group]
    exact X.mul_mem (hX.Z_le (Z.inv_mem (hcomm x hx))) hx

theorem IsSaturated101.bar_LB_inf_pCore_ne_bot (h34 : Stroth34Statement)
    [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) (hsat : IsSaturated101 M Q Z B X) (hBX : B ≤ X) :
    bar M Q (LB M Q B) ⊓ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) ≠
      ⊥ := by
  obtain ⟨KX, hKX⟩ := hc.exists_kerX X
  have hP := bar_inf_kerX_le_pCore hc hX hBX hKX
  obtain ⟨t, htB, htQ, htK⟩ := exists_mem_LB_kerX_not_mem_Q h34 H hX hsat hBX hKX
  have htM : t ∈ M := hc.LB_le_M htB
  have htP : QuotientGroup.mk' (Q.subgroupOf M) ⟨t, htM⟩ ∈ bar M Q (LB M Q B ⊓ KX) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨htB, htK⟩)
  intro hbot
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨t, htM⟩ ∈
      bar M Q (LB M Q B) ⊓ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) :=
    ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htB), hP htP⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact htQ (Subgroup.mem_subgroupOf.mp hmem)

end CFSG.RankThree.GF2n.Stroth80
