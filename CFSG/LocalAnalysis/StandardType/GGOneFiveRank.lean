module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped Pointwise

@[expose] def GGBstarSylowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp p B x L → GGSixHypPre p B Bs x L D J →
    ∀ P : Subgroup G, P ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) → IsPGroup p P → Bs ≤ P →
      (∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) → IsPGroup p Q →
        P ≤ Q → Q = P) →
      ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E →
        Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs)

variable {G : Type} [Group G]

theorem isElemAbelian_map_conj {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (E.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map h _

variable [Finite G]

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ q ∈ Q, q ∈ Subgroup.normalizer (P : Set G) ∧ q ∉ P := by
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hPQ.not_ge fun q hq => (Subgroup.subgroupOf_eq_top.mp h) hq
  obtain ⟨q, hqN, hqP⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨q, q.2, ?_, hqP⟩
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have := (Subgroup.mem_normalizer_iff.mp hqN ⟨k, hPQ.le hk⟩).mp hk
    exact this
  · intro hk
    have hkQ : k ∈ Q := by
      have := Q.mul_mem (Q.mul_mem (Q.inv_mem q.2) (hPQ.le hk)) q.2
      simpa [mul_assoc] using this
    exact (Subgroup.mem_normalizer_iff.mp hqN ⟨k, hkQ⟩).mpr hk

theorem isMaxPSubgroup_of_normalizer_le {p : ℕ} [Fact p.Prime] {M P : Subgroup G}
    (hmax : ∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → P ≤ Q → Q = P)
    (hN : Subgroup.normalizer (P : Set G) ≤ M) :
    ∀ Q : Subgroup G, IsPGroup p Q → P ≤ Q → Q = P := by
  intro Q hQ hPQ
  by_contra hne
  obtain ⟨q, hqQ, hqN, hqP⟩ :=
    exists_mem_normalizer_not_mem hQ (lt_of_le_of_ne hPQ (Ne.symm hne))
  have hR : Q ⊓ Subgroup.normalizer (P : Set G) = P :=
    hmax _ (inf_le_right.trans hN) (hQ.to_le inf_le_left) (le_inf hPQ Subgroup.le_normalizer)
  exact hqP (hR ▸ ⟨hqQ, hqN⟩)

theorem ggBstarRankInput_of_sylowUnique (h : GGBstarSylowUniqueInput) : GGBstarRankInput := by
  intro G _ _ p B Bs x L D J hI hpre
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  set M := Subgroup.normalizer (ggG0 p B x L D J : Set G) with hMdef
  have hBs := hpre.1
  have hNBsM : Subgroup.normalizer (Bs : Set G) ≤ M := hpre.2.2.2.2
  have hBsM : Bs ≤ M := Subgroup.le_normalizer.trans hNBsM
  have hBsp : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBs.2.1.2 b b.2)⟩
  obtain ⟨Q, hQ⟩ := (hBsp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  set P : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hPdef
  have hPM : P ≤ M := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := Q.isPGroup'.map M.subtype
  have hBsP : Bs ≤ P := fun b hb => ⟨⟨b, hBsM hb⟩, hQ hb, rfl⟩
  have hmaxM : ∀ R : Subgroup G, R ≤ M → IsPGroup p R → P ≤ R → R = P := by
    intro R hRM hRp hPR
    have hRp' : IsPGroup p (R.subgroupOf M) :=
      hRp.comap_of_injective M.subtype M.subtype_injective
    have hQR : (Q : Subgroup ↥M) ≤ R.subgroupOf M := fun q hq => hPR ⟨q, hq, rfl⟩
    have hRQ := Q.is_maximal' hRp' hQR
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, hRQ]
  have hUni := h G p B Bs x L D J hI hpre P hPM hPp hBsP hmaxM
  have hNP : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Bs : Set G) := by
    intro n hn
    rw [mem_normalizer_iff_map_conj]
    have hle : Bs.map (MulAut.conj n).toMonoidHom ≤ P := by
      rw [← map_conj_eq_of_mem_normalizer hn]
      exact Subgroup.map_mono hBsP
    exact (hUni _ hle (isElemAbelian_map_conj hBs.2.1 n)).2
      (Subgroup.card_map_of_injective (MulAut.conj n).injective)
  have hmaxG := isMaxPSubgroup_of_normalizer_le hmaxM (hNP.trans hNBsM)
  let PS : Sylow p G := ⟨P, hPp, fun {R} hR hPR => hmaxG R hR hPR⟩
  have hbound : ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E ≤ Nat.card Bs := by
    intro E hE
    have hEp : IsPGroup p E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
    obtain ⟨S, hS⟩ := hEp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS S
    have hEle : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
      rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ ((g • PS : Sylow p G) : Subgroup G) := by
        rw [hg]
        exact hS he
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at he'
      obtain ⟨y, hy, rfl⟩ := he'
      have hy' : y ∈ P := hy
      simpa [MulAut.smul_def, mul_assoc] using hy'
    have := (hUni _ hEle (isElemAbelian_map_conj hE g⁻¹)).1
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at this
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hBsp
  have hub : ∀ k ∈ {k | ∃ E : Subgroup G, E ≤ (⊤ : Subgroup G) ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k}, k ≤ m := by
    rintro k ⟨E, -, hE, hEk⟩
    have h1 := hbound E hE
    rw [hEk, hm] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  have hset : CFSG.Open.pRank p (⊤ : Subgroup G) = m := by
    unfold CFSG.Open.pRank
    exact le_antisymm (csSup_le ⟨m, Bs, le_top, hBs.2.1, hm⟩ hub)
      (le_csSup ⟨m, hub⟩ ⟨Bs, le_top, hBs.2.1, hm⟩)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup G),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup G), hset, hm]

end CFSG.StandardType
