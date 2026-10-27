module

public import CFSG.RankThree.GF2n.Tim79a34BigModel
public import CFSG.RankThree.GF2n.Tim79a34BigGammaBasic
import CFSG.RankThree.GF2n.Tim79a34BigB
import CFSG.RankThree.GF2n.Tim79a34BigIWProof
import CFSG.RankThree.GF2n.Tim79a34BigNaturalProof
import CFSG.RankThree.GF2n.Tim79a34BigPAct
import CFSG.RankThree.GF2n.Tim79a34BigRoot
import CFSG.RankThree.GF2n.Tim79a34BigWCentral
import CFSG.RankThree.GF2n.Tim79a34SpRadLine
import CFSG.GroupTheory.ChiefSectionPGroup
import CFSG.GroupTheory.SupMulCommutative
import CFSG.GroupTheory.SteinbergCBFTCores
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

theorem forall_eq_smul_or_forall_mem_of_root_invariant {n : ℕ} {F : Type} [Field F]
    {a : Fin n ⊕ Fin n → F} (S : AddSubgroup (Fin n ⊕ Fin n → F)) (haS : ∀ l : F, l • a ∈ S)
    (hSa : ∀ u ∈ S, CaseM.spForm a u = 0)
    (hinv : ∀ c : Fin n ⊕ Fin n → F, CaseM.spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      ∀ μ : F, μ ≠ 0 → ∀ u ∈ S, u + (μ * CaseM.spForm c u) • c ∈ S) :
    (∀ u ∈ S, ∃ l : F, u = l • a) ∨ ∀ u, CaseM.spForm a u = 0 → u ∈ S := by
  by_cases hfin : ∀ u ∈ S, ∃ l : F, u = l • a
  · exact Or.inl hfin
  · right
    push Not at hfin
    obtain ⟨s, hsS, hsf⟩ := hfin
    have has : CaseM.spForm a s = 0 := hSa s hsS
    obtain ⟨c₀, hc₀a, hc₀s⟩ := exists_perp_spForm_ne_zero (a := a) (w := s) hsf
    have hc₀s' : CaseM.spForm c₀ s ≠ 0 := fun h0 =>
      hc₀s (by rw [CaseM.spForm_comm (u := c₀) (v := s), h0, neg_zero])
    have hkind : ∀ u : Fin n ⊕ Fin n → F, CaseM.spForm a u = 0 →
        CaseM.spForm u s ≠ 0 → u ∈ S := by
      intro u hau hus
      have huF : ∀ l : F, u ≠ l • a := by
        intro l hl
        apply hus
        rw [hl, spForm_smul_left', has, mul_zero]
      have hmem := hinv u hau huF (CaseM.spForm u s)⁻¹ (inv_ne_zero hus) s hsS
      have hcalc : s + ((CaseM.spForm u s)⁻¹ * CaseM.spForm u s) • u = s + u := by
        rw [inv_mul_cancel₀ hus, one_smul]
      rw [hcalc] at hmem
      have hsub := S.sub_mem hmem hsS
      simpa using hsub
    intro u hau
    rcases eq_or_ne u 0 with hu0 | hu0
    · rw [hu0]
      simpa using haS 0
    · by_cases hus : CaseM.spForm u s = 0
      · have h1 : u + c₀ ∈ S := by
          refine hkind (u + c₀) ?_ ?_
          · rw [spForm_add_right, hau, hc₀a, add_zero]
          · simpa [spForm_add_left, hus] using hc₀s'
        have h2 : c₀ ∈ S := hkind c₀ hc₀a hc₀s'
        have hsub := S.sub_mem h1 h2
        simpa using hsub
      · exact hkind u hau hus

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

private theorem gammaIrr_addSubgroup [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {S : Subgroup G} (hAS : V ⊓ wOf V H ≤ S) (hSP : S ≤ P ⊓ wOf V H)
    (hR : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ s ∈ S, r * s * r⁻¹ ∈ S) :
    ∃ S' : AddSubgroup (Fin n ⊕ Fin n → GaloisField 2 f),
      (∀ u, u ∈ S' ↔ ψG u ∈ S) ∧
      (∀ l : GaloisField 2 f, l • a ∈ S') ∧
      (∀ u ∈ S', CaseM.spForm a u = 0) ∧
      (∀ c : Fin n ⊕ Fin n → GaloisField 2 f, CaseM.spForm a c = 0 →
        (∀ l : GaloisField 2 f, c ≠ l • a) → ∀ μ : GaloisField 2 f, μ ≠ 0 →
        ∀ u ∈ S', u + (μ * CaseM.spForm c u) • c ∈ S') := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hIW : cPbar V H P ≤ wOf V H := bigIWStatement_holds G M V Q P H h hZ
  have hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0 :=
    (bigPLocalStatement_holds G M V Q P H h hZ hIW hf Φ ψ hNat a T ha hT hTV).1
  have hroot := bigRootElement_holds bigPLocalStatement_holds G M V Q P H h hZ hIW hf Φ ψ hNat
    a T ha hT hTV
  let S' : AddSubgroup (Fin n ⊕ Fin n → GaloisField 2 f) :=
    { carrier := {u | ψG u ∈ S}
      zero_mem' := by
        show ψG (0 : Fin n ⊕ Fin n → GaloisField 2 f) ∈ S
        rw [bigRW_psi_zero]
        exact S.one_mem
      add_mem' := by
        intro u v hu hv
        show ψG (u + v) ∈ S
        rw [← bigRW_psi_mul]
        exact S.mul_mem hu hv
      neg_mem' := by
        intro u hu
        show ψG (-u) ∈ S
        have hneg : ψG (-u) = (ψG u)⁻¹ := by
          show ((Additive.toMul (ψ (-u)) : ↥(wOf V H)) : G) = _
          rw [map_neg, toMul_neg]
          rfl
        rw [hneg]
        exact S.inv_mem hu }
  have hmemS' : ∀ u, u ∈ S' ↔ ψG u ∈ S := fun u => Iff.rfl
  refine ⟨S', hmemS', ?_, ?_, ?_⟩
  · intro l
    exact (hmemS' _).mpr (hAS (Subgroup.mem_inf.mpr
      ⟨bigB_psi_smul_mem hVH hNat ha hT hTV l, (Additive.toMul (ψ (l • a))).2⟩))
  · intro u hu
    exact (hiff u).mp (Subgroup.mem_inf.mp (hSP ((hmemS' u).mp hu))).1
  · intro c hca hcl μ hμ u hu
    obtain ⟨r, hr, hact⟩ := hroot c μ hca hcl hμ
    have hmem : ψG (u + (μ * CaseM.spForm c u) • c) ∈ S := by
      have h1 : r * ψG u * r⁻¹ ∈ S := hR r hr (ψG u) ((hmemS' u).mp hu)
      rwa [hact u] at h1
    exact (hmemS' _).mpr hmem

theorem BigEndHyp.eq_or_eq_of_rootInvariant [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {S : Subgroup G} (hAS : V ⊓ wOf V H ≤ S)
    (hSP : S ≤ P ⊓ wOf V H)
    (hR : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ s ∈ S, r * s * r⁻¹ ∈ S) :
    S = V ⊓ wOf V H ∨ S = P ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨S', hmemS', haS, hSa, hinv⟩ :=
    gammaIrr_addSubgroup h hZ hf hNat ha hT hTV hAS hSP hR
  rcases forall_eq_smul_or_forall_mem_of_root_invariant S' haS hSa hinv with hfin | hall
  · left
    refine le_antisymm ?_ hAS
    intro s hs
    obtain ⟨u, rfl⟩ := bigB_exists_psi (ψ := ψ) (Subgroup.mem_inf.mp (hSP hs)).2
    obtain ⟨l, rfl⟩ := hfin u ((hmemS' u).mpr hs)
    exact Subgroup.mem_inf.mpr
      ⟨bigB_psi_smul_mem hVH hNat ha hT hTV l, (Additive.toMul (ψ (l • a))).2⟩
  · right
    have hIW : cPbar V H P ≤ wOf V H := bigIWStatement_holds G M V Q P H h hZ
    have hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0 :=
      (bigPLocalStatement_holds G M V Q P H h hZ hIW hf Φ ψ hNat a T ha hT hTV).1
    refine le_antisymm hSP ?_
    intro s hs
    obtain ⟨u, rfl⟩ := bigB_exists_psi (ψ := ψ) (Subgroup.mem_inf.mp hs).2
    exact (hmemS' u).mp (hall u ((hiff u).mp (Subgroup.mem_inf.mp hs).1))

theorem BigEndHyp.eq_bot_or_eq_wOf_of_xOf_invariant [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {S : Subgroup G} (hSW : S ≤ wOf V H)
    (hX : ∀ x ∈ xOf V H, ∀ s ∈ S, x * s * x⁻¹ ∈ S) : S = ⊥ ∨ S = wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨n, f, Φ, ψ, hn2, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨⟨s, hsS⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    obtain ⟨u, rfl⟩ := bigB_exists_psi (ψ := ψ) (hSW hsS)
    have hu0 : u ≠ 0 := by
      intro h0
      apply hs1
      apply Subtype.ext
      show ψG u = 1
      rw [h0, bigRW_psi_zero]
    refine le_antisymm hSW ?_
    intro w hw
    obtain ⟨v, rfl⟩ := bigB_exists_psi (ψ := ψ) hw
    by_cases hv0 : v = 0
    · rw [hv0, bigRW_psi_zero]
      exact S.one_mem
    · obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero hu0 hv0
      obtain ⟨x, hx⟩ := xToXbar_surjective hVH (Φ g)
      have hgx : Φ.symm (xToXbar hVH x) = g := by
        rw [hx]
        exact Φ.symm_apply_apply g
      have key := hNat.equiv x u
      rw [hgx, hg] at key
      have hmem : (x : G) * ψG u * (x : G)⁻¹ ∈ S := hX x x.2 (ψG u) hsS
      rwa [← key] at hmem

theorem BigEndHyp.not_le_normalizer_P_inf_wOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) :
    ¬ M ≤ Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G) := by
  intro hN
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hPM : P ≤ M := hc.P_le_Q.trans hc.Q_le_M
  let U : Subgroup G := V ⊔ (P ⊓ wOf V H)
  have hVab : IsMulCommutative ↥V := hc.maxAb.prop.2.2
  have hPWab : IsMulCommutative ↥(P ⊓ wOf V H) :=
    ⟨⟨fun a b => Subtype.ext (hc.wOf_isElemAbelian.comm
      (Subgroup.mem_inf.mp a.2).2 (Subgroup.mem_inf.mp b.2).2)⟩⟩
  have hcomm : ∀ a ∈ V, ∀ b ∈ P ⊓ wOf V H, a * b = b * a := fun a ha b hb =>
    hc.commute_of_mem_P (Subgroup.mem_inf.mp hb).1 ha
  have hUab : IsMulCommutative ↥U :=
    CFSG.GroupTheory.isMulCommutative_sup_of_elementwise_commute hcomm hVab hPWab
  have hUM : U ≤ M := sup_le hc.maxAb.prop.1 (inf_le_left.trans hPM)
  have hMU : M ≤ Subgroup.normalizer (U : Set G) := by
    intro m hm
    have hmV : m ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hm
    have hmPW : m ∈ Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G) := hN hm
    have hVeq : conjSubgroup m V = V := mem_normalizer_iff_conjSubgroup_eq.mp hmV
    have hPWeq : conjSubgroup m (P ⊓ wOf V H) = P ⊓ wOf V H :=
      mem_normalizer_iff_conjSubgroup_eq.mp hmPW
    refine mem_normalizer_iff_conjSubgroup_eq.mpr ?_
    show conjSubgroup m (V ⊔ (P ⊓ wOf V H)) = V ⊔ (P ⊓ wOf V H)
    rw [conjSubgroup_sup_eq_sup, hVeq, hPWeq]
  have hUV : U ≤ V := hc.maxAb.le_of_ge ⟨hUM, hMU, hUab⟩ le_sup_left
  have hPWleV : P ⊓ wOf V H ≤ V := le_sup_right.trans hUV
  have hAle : V ⊓ wOf V H ≤ P ⊓ wOf V H :=
    le_inf (inf_le_left.trans hc.V_le_P) inf_le_right
  have hne : P ⊓ wOf V H ≠ V ⊓ wOf V H :=
    (ne_of_lt (BigEndHyp.inf_wOf_lt_P_inf_wOf h hZ)).symm
  exact hne (le_antisymm (le_inf hPWleV inf_le_right) hAle)

private theorem mem_commutator_sup_inf_of_conj [Finite G] {M V Q P H : Subgroup G}
    (hc : MinCex M V Q P H) (hQW : ∀ x ∈ Q, conjSubgroup x (wOf V H) = wOf V H) :
    ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
      ∀ s ∈ ⁅P ⊓ wOf V H, Q⁆ ⊔ (V ⊓ wOf V H),
        r * s * r⁻¹ ∈ ⁅P ⊓ wOf V H, Q⁆ ⊔ (V ⊓ wOf V H) := by
  intro r hr s hs
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨hrX, hrC⟩ := Subgroup.mem_inf.mp hr
  have hrM : r ∈ M := by
    rw [← hc.normalizer_eq]
    exact Subgroup.centralizer_le_normalizer (V : Set G) hrC
  have hrP : conjSubgroup r P = P :=
    mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_P hrM)
  have hrQ : conjSubgroup r Q = Q := by
    apply mem_normalizer_iff_conjSubgroup_eq.mp
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.2 hrM
  have hrV : conjSubgroup r V = V := by
    apply mem_normalizer_iff_conjSubgroup_eq.mp
    rw [hc.normalizer_eq]
    exact hrM
  have hrW : conjSubgroup r (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H (xOf_le_H hVH hrX))
  have hcomm : conjSubgroup r ⁅P ⊓ wOf V H, Q⁆ = ⁅P ⊓ wOf V H, Q⁆ := by
    change (⁅P ⊓ wOf V H, Q⁆ : Subgroup G).map (MulAut.conj r).toMonoidHom = _
    rw [Subgroup.map_commutator]
    change ⁅conjSubgroup r (P ⊓ wOf V H), conjSubgroup r Q⁆ = _
    rw [conjSubgroup_inf, hrP, hrW, hrQ]
  have hSm : conjSubgroup r (⁅P ⊓ wOf V H, Q⁆ ⊔ (V ⊓ wOf V H)) =
      ⁅P ⊓ wOf V H, Q⁆ ⊔ (V ⊓ wOf V H) := by
    rw [conjSubgroup_sup_eq_sup, hcomm, conjSubgroup_inf, hrV, hrW]
  have hmem : r * s * r⁻¹ ∈
      conjSubgroup r (⁅P ⊓ wOf V H, Q⁆ ⊔ (V ⊓ wOf V H)) := by
    rw [mem_conjSubgroup]
    have e : r⁻¹ * (r * s * r⁻¹) * r = s := by group
    rwa [e]
  rwa [hSm] at hmem

theorem BigEndHyp.commutator_mem_inf_of_mem_P_inf_wOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQW : ∀ x ∈ Q, conjSubgroup x (wOf V H) = wOf V H) {u x : G} (hu : u ∈ P ⊓ wOf V H)
    (hx : x ∈ Q) : ⁅u, x⁆ ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hAne : V ⊓ wOf V H ≠ P ⊓ wOf V H :=
    ne_of_lt (BigEndHyp.inf_wOf_lt_P_inf_wOf h hZ)
  have hXQ : P ⊓ wOf V H ≤ Q := inf_le_left.trans hc.P_le_Q
  have hQ2 : IsPGroup 2 Q := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).1
  have hQM : Q ≤ M := hc.Q_le_M
  have hQX : Q ≤ Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G) := by
    intro y hy
    exact mem_normalizer_inf (hc.M_le_normalizer_P (hQM hy))
      (mem_normalizer_iff_conjSubgroup_eq.mpr (hQW y hy))
  have hQV : Q ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) := by
    intro y hy
    exact mem_normalizer_inf (hc.Q_le_normalizer_V hy)
      (mem_normalizer_iff_conjSubgroup_eq.mpr (hQW y hy))
  have hVX : V ⊓ wOf V H ≤ P ⊓ wOf V H :=
    le_inf (inf_le_left.trans hc.V_le_P) inf_le_right
  have hlt := CFSG.GroupTheory.commutator_sup_lt_of_isPGroup (p := 2) hXQ hQ2 hQX hQV hVX hAne
  let Sm : Subgroup G := ⁅P ⊓ wOf V H, Q⁆ ⊔ (V ⊓ wOf V H)
  have hSle : Sm ≤ P ⊓ wOf V H := le_of_lt hlt
  have hSne : Sm ≠ P ⊓ wOf V H := ne_of_lt hlt
  have hRinv : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
      ∀ s ∈ Sm, r * s * r⁻¹ ∈ Sm := mem_commutator_sup_inf_of_conj hc hQW
  have hmain := h.eq_or_eq_of_rootInvariant hZ le_sup_right hSle hRinv
  have hSmA : Sm = V ⊓ wOf V H := by
    rcases hmain with h | h
    · exact h
    · exact absurd h hSne
  have hmem : ⁅u, x⁆ ∈ Sm := by
    show ⁅u, x⁆ ∈ ⁅P ⊓ wOf V H, Q⁆ ⊔ (V ⊓ wOf V H)
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu hx)
  rwa [hSmA] at hmem

end CFSG.RankThree.GF2n.Tim79a
