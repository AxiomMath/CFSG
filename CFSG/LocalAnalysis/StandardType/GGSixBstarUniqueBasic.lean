module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveRank
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

@[expose] def GGNoOffender (p : ℕ) (N Bs : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ N → E ≤ Subgroup.normalizer (Bs : Set G) → IsElemAbelian p E →
    E ≤ Subgroup.centralizer (Bs : Set G) ∨
      Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E <
        Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G)

theorem GGNoOffender.mono {p : ℕ} {N N' Bs : Subgroup G} (h : GGNoOffender p N Bs)
    (hN : N' ≤ N) : GGNoOffender p N' Bs :=
  fun E hE => h E (hE.trans hN)

theorem le_centralizer_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    E ≤ Subgroup.centralizer (E : Set G) := by
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact TableB.IsElemAbelian.comm hE hy he

variable [Finite G]

theorem card_le_of_noOffender {p : ℕ} {N Bs E : Subgroup G}
    (hΩ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNO : GGNoOffender p N Bs) (hEN : E ≤ N) (hEB : E ≤ Subgroup.normalizer (Bs : Set G))
    (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs) := by
  rcases hNO E hEN hEB hE with hC | hlt
  · have hle : E ≤ Bs := fun e he => hΩ e (hC he) (hE.2 e he)
    exact ⟨Subgroup.card_le_of_le hle, fun hcard => Subgroup.eq_of_le_of_card_ge hle hcard.ge⟩
  · have hle : E ⊓ Subgroup.centralizer (Bs : Set G) ≤
        Bs ⊓ Subgroup.centralizer (E : Set G) := fun e he =>
      ⟨hΩ e he.2 (hE.2 e he.1), le_centralizer_of_isElemAbelian hE he.1⟩
    have h1 := Subgroup.card_le_of_le hle
    have hlt' : Nat.card E < Nat.card Bs := by
      by_contra hcon
      rw [not_lt] at hcon
      have h2 := Nat.mul_le_mul h1 hcon
      have h3 : Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) ≤
          Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E := by
        rw [mul_comm]
        exact h2
      omega
    exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩

theorem le_normalizer_of_noOffender {p : ℕ} (hp : p.Prime) {N Bs S : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hΩ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNO : GGNoOffender p N Bs) (hSN : S ≤ N) (hS : IsPGroup p S) (hBsS : Bs ≤ S) :
    S ≤ Subgroup.normalizer (Bs : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hlt : S ⊓ Subgroup.normalizer (Bs : Set G) < S :=
    lt_of_le_of_ne inf_le_left fun h => hne (h ▸ inf_le_right)
  obtain ⟨s, hsS, hsN, hsNB⟩ := exists_mem_normalizer_not_mem hS hlt
  have hsB : s ∉ Subgroup.normalizer (Bs : Set G) := fun h => hsNB ⟨hsS, h⟩
  set E := Bs.map (MulAut.conj s).toMonoidHom with hEdef
  have hBsle : Bs ≤ S ⊓ Subgroup.normalizer (Bs : Set G) := le_inf hBsS Subgroup.le_normalizer
  have hEle : E ≤ S ⊓ Subgroup.normalizer (Bs : Set G) := by
    rw [hEdef, ← map_conj_eq_of_mem_normalizer hsN]
    exact Subgroup.map_mono hBsle
  have hEcard : Nat.card E = Nat.card Bs :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hEq := (card_le_of_noOffender hΩ hNO (hEle.trans (inf_le_left.trans hSN))
    (hEle.trans inf_le_right) (isElemAbelian_map_conj hBs s)).2 hEcard
  exact hsB (mem_normalizer_iff_map_conj.mpr hEq)

theorem unique_of_noOffender {p : ℕ} (hp : p.Prime) {N Bs S : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hΩ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNO : GGNoOffender p N Bs) (hSN : S ≤ N) (hS : IsPGroup p S) (hBsS : Bs ≤ S)
    {E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs) :=
  card_le_of_noOffender hΩ hNO (hES.trans hSN)
    (hES.trans (le_normalizer_of_noOffender hp hBs hΩ hNO hSN hS hBsS)) hE

omit [Finite G] in
theorem exists_maximal_pSubgroup {p : ℕ} (hp : p.Prime) {N Q : Subgroup G} (hQN : Q ≤ N)
    (hQ : IsPGroup p Q) :
    ∃ P : Subgroup G, P ≤ N ∧ IsPGroup p P ∧ Q ≤ P ∧
      ∀ R : Subgroup G, R ≤ N → IsPGroup p R → P ≤ R → R = P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := (hQ.comap_of_injective N.subtype N.subtype_injective).exists_le_sylow
  refine ⟨(S : Subgroup ↥N).map N.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map N.subtype,
    fun q hq => ⟨⟨q, hQN hq⟩, hS hq, rfl⟩, fun R hRN hRp hPR => ?_⟩
  have hRp' : IsPGroup p (R.subgroupOf N) :=
    hRp.comap_of_injective N.subtype N.subtype_injective
  have hSR : (S : Subgroup ↥N) ≤ R.subgroupOf N := fun s hs => hPR ⟨s, hs, rfl⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hRN, S.is_maximal' hRp' hSR]

theorem card_mul_card_le_card_sup_mul (E C : Subgroup G) :
    Nat.card E * Nat.card C ≤ Nat.card (E ⊔ C : Subgroup G) * Nat.card (C ⊓ E : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card C E
  have h2 := Subgroup.relIndex_mul_card C (E ⊔ C)
  rw [inf_eq_left.mpr (le_sup_right : C ≤ E ⊔ C)] at h2
  have : C.IsFiniteRelIndex (E ⊔ C) := Subgroup.isFiniteRelIndex_of_finiteIndex
  have h3 : C.relIndex E ≤ C.relIndex (E ⊔ C) :=
    Subgroup.relIndex_le_of_le_right le_sup_left Subgroup.relIndex_ne_zero
  calc Nat.card E * Nat.card C = C.relIndex E * Nat.card (C ⊓ E : Subgroup G) * Nat.card C := by
        rw [h1]
    _ ≤ C.relIndex (E ⊔ C) * Nat.card (C ⊓ E : Subgroup G) * Nat.card C :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
    _ = Nat.card (E ⊔ C : Subgroup G) * Nat.card (C ⊓ E : Subgroup G) := by
        rw [← h2]
        ring

theorem noOffender_of_unique {p : ℕ} (hp : p.Prime) {N Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ N)
    (hU : ∀ P : Subgroup G, P ≤ N → IsPGroup p P → Bs ≤ P →
      (∀ Q : Subgroup G, Q ≤ N → IsPGroup p Q → P ≤ Q → Q = P) →
      ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E →
        Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs)) :
    GGNoOffender p N Bs := by
  intro E hEN hEB hE
  have hQp : IsPGroup p (E ⊔ Bs : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (TableB.isPGroup_of_isElemAbelian hE)
      (TableB.isPGroup_of_isElemAbelian hBs) hEB
  obtain ⟨P, hPN, hPp, hQP, hmax⟩ := exists_maximal_pSubgroup hp (sup_le hEN hBsN) hQp
  set C := Bs ⊓ Subgroup.centralizer (E : Set G) with hCdef
  have hCel : IsElemAbelian p C := TableB.isElemAbelian_mono hBs inf_le_left
  have hFel : IsElemAbelian p (E ⊔ C) := TableB.isElemAbelian_sup hE hCel fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp hc.2 a ha
  have hFP : E ⊔ C ≤ P :=
    sup_le (le_sup_left.trans hQP) ((inf_le_left.trans le_sup_right).trans hQP)
  obtain ⟨hFle, hFeq⟩ := hU P hPN hPp (le_sup_right.trans hQP) hmax _ hFP hFel
  rcases hFle.lt_or_eq with hlt | heq
  · right
    have hCE : C ⊓ E ≤ E ⊓ Subgroup.centralizer (Bs : Set G) := fun c hc =>
      ⟨hc.2, le_centralizer_of_isElemAbelian hBs hc.1.1⟩
    have h1 := card_mul_card_le_card_sup_mul E C
    have h2 := Subgroup.card_le_of_le hCE
    have hpos : 0 < Nat.card (C ⊓ E : Subgroup G) := Nat.card_pos
    have h3 : Nat.card (E ⊔ C : Subgroup G) * Nat.card (C ⊓ E : Subgroup G) <
        Nat.card Bs * Nat.card (C ⊓ E : Subgroup G) := Nat.mul_lt_mul_of_pos_right hlt hpos
    have h4 := Nat.mul_le_mul_left (Nat.card Bs) h2
    rw [mul_comm (Nat.card C)]
    omega
  · left
    have hEBs : E ≤ Bs := (hFeq heq) ▸ le_sup_left
    exact hEBs.trans (le_centralizer_of_isElemAbelian hBs)

end CFSG.StandardType
