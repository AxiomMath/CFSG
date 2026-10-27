module

public import CFSG.RankThree.S4Free.Stellmacher33Bridge
import CFSG.RankThree.S4Free.Stellmacher32
import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.RankThree.S4Free.Stellmacher24Ext
public import CFSG.RankThree.S4Free.Stellmacher34Core

public section

namespace CFSG.RankThree.S4Free.Stell34

open Subgroup CFSG.Blueprint
open CFSG.RankThree.S4Free.Stell33 (LCfgCore oTwoSub)
open scoped commutatorElement Pointwise

namespace SzCfg

variable {Λ : Type*} [Group Λ] [Finite Λ] {T W R : Subgroup Λ} {a : ℕ} {K : Type} [Field K]
  [Finite K] {φ : Λ →* suzukiGroup a K}

theorem le_oTwo_of_commutator_le (h : SzCfg T W R φ) (hR : R = oTwo Λ) {Q : Subgroup Λ}
    [Q.Normal] (hQ : ⁅Q, Q⁆ ≤ oTwo Λ) : Q ≤ oTwo Λ := by
  obtain ⟨-, hnt, hs⟩ := CFSG.LieType.Ree.suzuki_simple h.one_le h.card_K
  haveI := hs
  have hQn : (Q.map φ).Normal := (inferInstance : Q.Normal).map φ h.surjective
  rcases hQn.eq_bot_or_eq_top with h1 | h1
  · rw [← hR, ← h.ker_eq]
    exact (Subgroup.map_eq_bot_iff Q).mp h1
  · exfalso
    have h2 : (⁅Q, Q⁆).map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, h.ker_eq, hR]
      exact hQ
    rw [Subgroup.map_commutator, h1, ← _root_.commutator_def,
      (CFSG.LieType.Ree.suzuki_perfect h.one_le h.card_K).1] at h2
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (suzukiGroup a K)
    have hx : x ∈ (⊥ : Subgroup (suzukiGroup a K)) := h2 ▸ mem_top x
    have hy : y ∈ (⊥ : Subgroup (suzukiGroup a K)) := h2 ▸ mem_top y
    rw [mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)

end SzCfg

section Host

variable {G : Type*} [Group G] [Finite G]

theorem subgroupOf_map_conj {L Q : Subgroup G} (hQL : Q ≤ L) (x : L) :
    (Q.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf L =
      (Q.subgroupOf L).map (MulAut.conj x).toMonoidHom := by
  ext y
  simp only [mem_subgroupOf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨q, hq, hqy⟩
    refine ⟨⟨q, hQL hq⟩, hq, Subtype.ext ?_⟩
    simpa using hqy
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, by simp⟩

theorem szCfg_of_isL24Sz {T W L : Subgroup G} (hT : IsPGroup 2 T)
    (hW : CFSG.Open.IsElemAbelian 2 W) (hWT : W ≤ T) (hTW : T ≤ normalizer (W : Set G))
    (hL : Stell.IsL24Sz T (normalizer (W : Set G)) W L) :
    ∃ (R : Subgroup L) (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (φ : L →* suzukiGroup a K), SzCfg (T.subgroupOf L) (W.subgroupOf L) R φ := by
  obtain ⟨R, hRn, hOR, hodd, a, ha, K, _, _, hK, ⟨e⟩⟩ := hL.suzuki
  have hWL : W ≤ L := hL.le
  have hN : normalizer ((W.subgroupOf L : Subgroup L) : Set L) =
      (normalizer (W : Set G)).subgroupOf L := (subgroupOf_normalizer_eq hWL).symm
  refine ⟨R, a, K, inferInstance, inferInstance, e.toMonoidHom.comp (QuotientGroup.mk' R), ?_⟩
  refine
    { isPGroup_T := hT.comap_subtype
      not_dvd_index := hL.not_dvd_relIndex
      elemAb := ?_
      W_le_T := fun x hx => hWT hx
      T_le_normalizer := ?_
      normalizer_ne_top := ?_
      sup_conj := ?_
      oTwo_le := hOR
      not_dvd_relIndex := hodd
      one_le := ha
      card_K := hK
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective R)
      ker_eq := ?_ }
  · refine Stell.isElemAbelian_of_map L.subtype_injective ?_
    rw [subgroupOf_map_subtype, inf_of_le_left hWL]
    exact hW
  · rw [hN]
    exact fun x hx => hTW hx
  · rw [hN]
    intro htop
    apply hL.not_le
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ (normalizer (W : Set G)).subgroupOf L := htop ▸ mem_top _
    exact this
  · intro x hx
    rw [hN] at hx
    have hx' : (x : G) ∉ normalizer (W : Set G) := hx
    have hsup := hL.sup_conj x x.2 hx'
    have h1 := congrArg (fun Q : Subgroup G => Q.subgroupOf L) hsup
    have hWxL : W.map (MulAut.conj (x : G)).toMonoidHom ≤ L := by
      rintro _ ⟨w, hw, rfl⟩
      exact L.mul_mem (L.mul_mem x.2 (hWL hw)) (L.inv_mem x.2)
    rwa [subgroupOf_sup hWL hWxL, subgroupOf_map_conj hWL, subgroupOf_self] at h1
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Host

section Centralizer

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_map_conj {W : Subgroup G} {p x : G}
    (hp : x⁻¹ * p * x ∈ normalizer (W : Set G)) :
    p ∈ normalizer ((W.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  rw [Stell33.mem_map_conj_iff, Stell33.mem_map_conj_iff]
  have e : x⁻¹ * (p * y * p⁻¹) * x = (x⁻¹ * p * x) * (x⁻¹ * y * x) * (x⁻¹ * p * x)⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.mp hp _

theorem comm_mem_oTwoSub {T W L : Subgroup G} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    (hTW : T ≤ normalizer (W : Set G)) (hWL : W ≤ L) {x : G} (hxL : x ∈ L)
    (hsup : W ⊔ W.map (MulAut.conj x).toMonoidHom = L) {p : G} (hp : p ∈ oTwo G) {l : G}
    (hl : l ∈ L) : ⁅p, l⁆ ∈ oTwoSub L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPT : oTwo G ≤ T := by
    have h1 := (Stell.oTwo_isPGroup G).le_sylow_of_normal (hT.toSylow hTi)
    rwa [IsPGroup.toSylow_coe] at h1
  have hPL : oTwo G ⊓ L ≤ oTwoSub L := by
    refine Stell33.le_oTwoSub inf_le_right ?_ ((Stell.oTwo_isPGroup G).to_le inf_le_left)
    refine Stell33.le_normalizer_of_forall_conj_mem fun g hg y hy => ?_
    exact ⟨(inferInstance : (oTwo G).Normal).conj_mem _ hy.1 g,
      L.mul_mem (L.mul_mem hg hy.2) (L.inv_mem hg)⟩
  let C : Subgroup G :=
    { carrier := {l | l ∈ L ∧ ∀ q ∈ oTwo G, ⁅q, l⁆ ∈ oTwoSub L}
      one_mem' := ⟨L.one_mem, fun q _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
      mul_mem' := by
        rintro l₁ l₂ ⟨h₁L, h₁⟩ ⟨h₂L, h₂⟩
        refine ⟨L.mul_mem h₁L h₂L, fun q hq => ?_⟩
        have e : ⁅q, l₁ * l₂⁆ = ⁅q, l₁⁆ * (l₁ * ⁅q, l₂⁆ * l₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (h₁ q hq) ((mem_normalizer_iff.mp
          (Stell33.le_normalizer_oTwoSub L h₁L) _).mp (h₂ q hq))
      inv_mem' := by
        rintro l ⟨hlL, hl⟩
        refine ⟨L.inv_mem hlL, fun q hq => ?_⟩
        have e : ⁅q, l⁻¹⁆ = l⁻¹ * ⁅q, l⁆⁻¹ * l⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (mem_normalizer_iff.mp (Stell33.le_normalizer_oTwoSub L (L.inv_mem hlL)) _).mp
          (inv_mem (hl q hq)) }
  have hWC : W ≤ C := by
    intro w hw
    refine ⟨hWL hw, fun q hq => hPL ⟨?_, ?_⟩⟩
    · have := (inferInstance : (oTwo G).Normal).conj_mem _ (inv_mem hq) w
      rw [commutatorElement_def, show q * w * q⁻¹ * w⁻¹ = q * (w * q⁻¹ * w⁻¹) by group]
      exact mul_mem hq this
    · rw [commutatorElement_def]
      have := (mem_normalizer_iff.mp (hTW (hPT hq)) w).mp hw
      exact L.mul_mem (hWL this) (L.inv_mem (hWL hw))
  have hWxC : W.map (MulAut.conj x).toMonoidHom ≤ C := by
    intro w hw
    have hwL : w ∈ L := hsup ▸ mem_sup_right hw
    refine ⟨hwL, fun q hq => hPL ⟨?_, ?_⟩⟩
    · have := (inferInstance : (oTwo G).Normal).conj_mem _ (inv_mem hq) w
      rw [commutatorElement_def, show q * w * q⁻¹ * w⁻¹ = q * (w * q⁻¹ * w⁻¹) by group]
      exact mul_mem hq this
    · have hqx : x⁻¹ * q * x ∈ normalizer (W : Set G) := by
        refine hTW (hPT ?_)
        have := (inferInstance : (oTwo G).Normal).conj_mem _ hq x⁻¹
        rwa [inv_inv] at this
      have hqN := mem_normalizer_map_conj hqx
      rw [commutatorElement_def]
      have h1 := (mem_normalizer_iff.mp hqN w).mp hw
      have h1L : q * w * q⁻¹ ∈ L := hsup ▸ mem_sup_right h1
      exact L.mul_mem h1L (L.inv_mem hwL)
  have hLC : L ≤ C := by
    rw [← hsup]
    exact sup_le hWC hWxC
  exact (hLC hl).2 p hp

theorem commutator_le_oTwoSub {T W L : Subgroup G} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    (hTW : T ≤ normalizer (W : Set G)) (hWL : W ≤ L) {x : G} (hxL : x ∈ L)
    (hsup : W ⊔ W.map (MulAut.conj x).toMonoidHom = L)
    (hCG : centralizer (oTwo G : Set G) ≤ oTwo G) :
    ⁅L ⊓ centralizer (oTwoSub L : Set G), L ⊓ centralizer (oTwoSub L : Set G)⁆ ≤ oTwoSub L := by
  set Kc := L ⊓ centralizer (oTwoSub L : Set G) with hKc
  have h1 : ⁅oTwo G, Kc⁆ ≤ oTwoSub L := by
    rw [commutator_le]
    intro p hp k hk
    exact comm_mem_oTwoSub hT hTi hTW hWL hxL hsup hp hk.1
  have h2 : ⁅⁅oTwo G, Kc⁆, Kc⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (commutator_mono h1 le_rfl).trans ?_
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
    intro o ho
    rw [mem_centralizer_iff]
    intro k hk
    exact ((mem_centralizer_iff.mp hk.2) o ho).symm
  have h3 : ⁅⁅Kc, oTwo G⁆, Kc⁆ = ⊥ := by rw [commutator_comm Kc]; exact h2
  have h4 : ⁅⁅Kc, Kc⁆, oTwo G⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h3 h2
  have h5 : ⁅Kc, Kc⁆ ≤ oTwo G := by
    rw [commutator_eq_bot_iff_le_centralizer] at h4
    exact h4.trans hCG
  have h6 : ⁅Kc, Kc⁆ ≤ L := (commutator_le_self Kc).trans inf_le_left
  have hPL : oTwo G ⊓ L ≤ oTwoSub L := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine Stell33.le_oTwoSub inf_le_right ?_ ((Stell.oTwo_isPGroup G).to_le inf_le_left)
    refine Stell33.le_normalizer_of_forall_conj_mem fun g hg y hy => ?_
    exact ⟨(inferInstance : (oTwo G).Normal).conj_mem _ hy.1 g,
      L.mul_mem (L.mul_mem hg hy.2) (L.inv_mem hg)⟩
  exact (le_inf h5 h6).trans hPL

theorem centralizer_oTwo_le_of_isL24Sz {T W L : Subgroup G}
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hTW : T ≤ normalizer (W : Set G))
    (hL : Stell.IsL24Sz T (normalizer (W : Set G)) W L)
    (hCG : centralizer (oTwo G : Set G) ≤ oTwo G) {R : Subgroup L} {a : ℕ} {K : Type}
    [Field K] [Finite K] {φ : L →* suzukiGroup a K}
    (h : SzCfg (T.subgroupOf L) (W.subgroupOf L) R φ) (hR : R = oTwo L) :
    centralizer (oTwo L : Set L) ≤ oTwo L := by
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp hL.not_le
  have hsup := hL.sup_conj x hxL hxM
  have hK := commutator_le_oTwoSub hT hTi hTW hL.le hxL hsup hCG
  refine h.le_oTwo_of_commutator_le hR ?_
  have hmap : (centralizer (oTwo L : Set L)).map L.subtype ≤
      L ⊓ centralizer (oTwoSub L : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨q.2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨o, ho, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hq o ho)
  have h1 : (⁅centralizer (oTwo L : Set L), centralizer (oTwo L : Set L)⁆).map L.subtype ≤
      (oTwo L).map L.subtype := by
    rw [map_commutator]
    exact (commutator_mono hmap hmap).trans hK
  exact (map_le_map_iff_of_injective L.subtype_injective).mp h1

end Centralizer

end CFSG.RankThree.S4Free.Stell34
