module

public import CFSG.RankThree.GF2n.Tim79a34BigEnd
import CFSG.RankThree.GF2n.Tim79a34TwBound
import CFSG.RankThree.GF2n.Tim79a34BigDirectGroup
public import CFSG.RankThree.GF2n.Tim79aSec33Base

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem BigEndHyp.mem_inf_wOf_of_centralizes_P (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {b : G}
    (hb : b ∈ wOf V H ⊔ cPbar V H P)
    (hbP : b ∈ Subgroup.centralizer (P : Set G)) : b ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hbV : b ∈ V := by
    have h := hbP
    rw [hc.centralizer_P_eq] at h
    exact h
  have hbH : b ∈ H := hc.V_le_H hbV
  have hIcX : wOf V H ⊔ cPbar V H P ≤ cX V H :=
    sup_le (twb_wOf_le_cX hc.V_le_H) inf_le_right
  have hbX : b ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hbV
  have hzc : (⟨piBar V H ⟨b, hbH⟩,
      mem_barOf_iff.mpr ⟨⟨b, hbH⟩, hbX, rfl⟩⟩ : Xbar V H) ∈
      Subgroup.center (Xbar V H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, hxX, hxg⟩ := mem_barOf_iff.mp g.2
    have hW : ((⁅(⟨b, hbH⟩ : ↥H), x⁆ : ↥H) : G) ∈ wOf V H := (hIcX hb).2 x hxX
    have h1 : piBar V H ⁅(⟨b, hbH⟩ : ↥H), x⁆ = 1 := (piBar_eq_one_iff _).mpr hW
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    apply Subtype.ext
    show (g : Hbar V H) * piBar V H ⟨b, hbH⟩ = piBar V H ⟨b, hbH⟩ * (g : Hbar V H)
    rw [← hxg]
    exact h1.symm
  rw [hZ, Subgroup.mem_bot] at hzc
  have h2 : piBar V H ⟨b, hbH⟩ = 1 := congrArg Subtype.val hzc
  exact Subgroup.mem_inf.mpr ⟨hbV, (piBar_eq_one_iff _).mp h2⟩

theorem BigEndHyp.sup_cPbar_inf_V (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) :
    (wOf V H ⊔ cPbar V H P) ⊓ V = V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  refine le_antisymm ?_ ?_
  · intro b hb
    obtain ⟨hbI, hbV⟩ := Subgroup.mem_inf.mp hb
    refine h.mem_inf_wOf_of_centralizes_P hZ hbI ?_
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (hc.commute_of_mem_P hp hbV).symm
  · intro b hb
    obtain ⟨hbV, hbW⟩ := Subgroup.mem_inf.mp hb
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hbW, hbV⟩

theorem BigEndHyp.commutator_mem_inf_of_mem_P (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {b r : G}
    (hb : b ∈ (wOf V H ⊔ cPbar V H P) ⊓ P) (hr : r ∈ P) :
    ⁅b, r⁆ ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hbI : b ∈ wOf V H ⊔ cPbar V H P := (Subgroup.mem_inf.mp hb).1
  have hbP : b ∈ P := (Subgroup.mem_inf.mp hb).2
  have hrH : r ∈ H := hc.PleH hr
  have hPconj : conjSubgroup r P = P :=
    mem_normalizer_iff_conjSubgroup_eq.mp (Subgroup.le_normalizer hr)
  have hcXconj : conjSubgroup r (cX V H) = cX V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_cX V H hrH)
  have hcPconj : conjSubgroup r (cPbar V H P) = cPbar V H P := by
    change conjSubgroup r (P ⊓ cX V H) = P ⊓ cX V H
    rw [conjSubgroup_inf_eq_inf, hPconj, hcXconj]
  have hWconj : conjSubgroup r (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp (H_le_normalizer_wOf V H hrH)
  have hIconj : conjSubgroup r (wOf V H ⊔ cPbar V H P) =
      wOf V H ⊔ cPbar V H P := by
    rw [conjSubgroup_sup_eq_sup, hWconj, hcPconj]
  have hnorm : r ∈ Subgroup.normalizer ((wOf V H ⊔ cPbar V H P : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr hIconj
  have hconj : r * b⁻¹ * r⁻¹ ∈ wOf V H ⊔ cPbar V H P :=
    (Subgroup.mem_normalizer_iff.mp hnorm b⁻¹).mp
      ((wOf V H ⊔ cPbar V H P).inv_mem hbI)
  have hmemI : ⁅b, r⁆ ∈ wOf V H ⊔ cPbar V H P := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using (wOf V H ⊔ cPbar V H P).mul_mem hbI hconj
  have hmemV : ⁅b, r⁆ ∈ V := hc.commutator_mem_V_of_mem_P hbP hr
  have hIV : ⁅b, r⁆ ∈ (wOf V H ⊔ cPbar V H P) ⊓ V := ⟨hmemI, hmemV⟩
  rwa [h.sup_cPbar_inf_V hZ] at hIV

theorem BigEndHyp.centralizes_of_commute_of_isTI (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {D : Subgroup G} (hDP : D ≤ P)
    (hDV : D ⊓ V = ⊥)
    (hTI : ∀ m ∈ M, conjSubgroup m D ⊓ D ≠ ⊥ → conjSubgroup m D = D)
    {b d₀ : G} (hb : b ∈ (wOf V H ⊔ cPbar V H P) ⊓ P) (hd₀ : d₀ ∈ D) (hd₀1 : d₀ ≠ 1)
    (hcomm : b * d₀ = d₀ * b) : b ∈ Subgroup.centralizer (D : Set G) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hbP : b ∈ P := (Subgroup.mem_inf.mp hb).2
  have hbM : b ∈ M := bigDirect_P_le_M hc hbP
  have hconj : d₀ ∈ conjSubgroup b D := by
    rw [mem_conjSubgroup]
    have h1 : b⁻¹ * d₀ * b = d₀ := by
      rw [mul_assoc, ← hcomm]
      group
    rwa [h1]
  have hne : conjSubgroup b D ⊓ D ≠ ⊥ := by
    intro hbot
    have hmem : d₀ ∈ conjSubgroup b D ⊓ D := ⟨hconj, hd₀⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd₀1 hmem
  have heq : conjSubgroup b D = D := hTI b hbM hne
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hmemD : ⁅b, d⁆ ∈ D := by
    have h1 : b * d * b⁻¹ ∈ conjSubgroup b D := by
      rw [mem_conjSubgroup]
      have h2 : b⁻¹ * (b * d * b⁻¹) * b = d := by group
      rwa [h2]
    rw [heq] at h1
    rw [commutatorElement_def]
    exact D.mul_mem h1 (D.inv_mem hd)
  have hmemA : ⁅b, d⁆ ∈ V ⊓ wOf V H :=
    h.commutator_mem_inf_of_mem_P hZ hb (hDP hd)
  have hmem : ⁅b, d⁆ ∈ D ⊓ V := ⟨hmemD, hmemA.1⟩
  rw [hDV, Subgroup.mem_bot] at hmem
  exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm

noncomputable def BigEndHyp.commPairHom (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {K : Subgroup G}
    (hK : K ≤ (wOf V H ⊔ cPbar V H P) ⊓ P) {d₀ : G} (hd₀ : d₀ ∈ P) :
    ↥K →* ↥(V ⊓ wOf V H) :=
  { toFun := fun b =>
      ⟨⁅(b : G), d₀⁆, h.commutator_mem_inf_of_mem_P hZ (hK b.2) hd₀⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro b₁ b₂
      apply Subtype.ext
      change ⁅(b₁ : G) * (b₂ : G), d₀⁆ = ⁅(b₁ : G), d₀⁆ * ⁅(b₂ : G), d₀⁆
      have h₁ : (b₁ : G) ∈ wOf V H ⊔ cPbar V H P := (hK b₁.2).1
      have hc₂ : ⁅(b₂ : G), d₀⁆ ∈ wOf V H ⊔ cPbar V H P :=
        Subgroup.mem_sup_left
          (h.commutator_mem_inf_of_mem_P hZ (hK b₂.2) hd₀).2
      have hc₁ : ⁅(b₁ : G), d₀⁆ ∈ wOf V H ⊔ cPbar V H P :=
        Subgroup.mem_sup_left
          (h.commutator_mem_inf_of_mem_P hZ (hK b₁.2) hd₀).2
      have hconj : (b₁ : G) * ⁅(b₂ : G), d₀⁆ * ((b₁ : G))⁻¹ = ⁅(b₂ : G), d₀⁆ := by
        rw [h.concl.2.2.comm h₁ hc₂]
        group
      rw [commutatorElement_mul_left_eq_conj_mul, hconj]
      exact (h.concl.2.2.comm hc₁ hc₂).symm }

theorem BigEndHyp.commPairHom_ker (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {D K : Subgroup G} (hDP : D ≤ P)
    (hDV : D ⊓ V = ⊥)
    (hTI : ∀ m ∈ M, conjSubgroup m D ⊓ D ≠ ⊥ → conjSubgroup m D = D)
    (hK : K ≤ (wOf V H ⊔ cPbar V H P) ⊓ P) {d₀ : G} (hd₀ : d₀ ∈ D) (hd₀1 : d₀ ≠ 1) :
    (h.commPairHom (K := K) (d₀ := d₀) hZ hK (hDP hd₀)).ker =
      (K ⊓ Subgroup.centralizer (D : Set G)).subgroupOf K := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hb
    refine ⟨b.2, ?_⟩
    have hb0 : (b : G) * d₀ = d₀ * (b : G) := by
      have h' := congrArg Subtype.val hb
      change ⁅(b : G), d₀⁆ = 1 at h'
      rw [commutatorElement_eq_one_iff_mul_comm] at h'
      exact h'
    exact h.centralizes_of_commute_of_isTI hZ hDP hDV hTI (hK b.2) hd₀ hd₀1 hb0
  · intro hb
    obtain ⟨-, hbC⟩ := Subgroup.mem_inf.mp hb
    apply Subtype.ext
    change ⁅(b : G), d₀⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hbC d₀ hd₀).symm

theorem BigEndHyp.relIndex_centralizer_le (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {D K : Subgroup G} (hDP : D ≤ P)
    (hDV : D ⊓ V = ⊥)
    (hTI : ∀ m ∈ M, conjSubgroup m D ⊓ D ≠ ⊥ → conjSubgroup m D = D)
    (hK : K ≤ (wOf V H ⊔ cPbar V H P) ⊓ P) :
    (K ⊓ Subgroup.centralizer (D : Set G)).relIndex K ≤ qBar V H := by
  have hq : 1 ≤ qBar V H := by
    rw [← h.module]
    exact Nat.card_pos
  by_cases hDbot : D = ⊥
  · subst hDbot
    have htop : Subgroup.centralizer (↑(⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset, Subgroup.coe_bot]
      exact Set.singleton_subset_iff.mpr (Subgroup.center G).one_mem
    rw [htop, inf_top_eq, Subgroup.relIndex_self]
    exact hq
  · obtain ⟨⟨d₀, hd₀D⟩, hd₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDbot
    have hd₀1' : d₀ ≠ 1 := fun h' => hd₀1 (Subtype.ext h')
    let φ : ↥K →* ↥(V ⊓ wOf V H) :=
      h.commPairHom (K := K) (d₀ := d₀) hZ hK (hDP hd₀D)
    have hker : φ.ker = (K ⊓ Subgroup.centralizer (D : Set G)).subgroupOf K := by
      change (h.commPairHom (K := K) (d₀ := d₀) hZ hK (hDP hd₀D)).ker = _
      exact h.commPairHom_ker hZ hDP hDV hTI hK hd₀D hd₀1'
    have hrel : (K ⊓ Subgroup.centralizer (D : Set G)).relIndex K =
        Nat.card ↥φ.range := by
      rw [← Subgroup.relIndex_subgroupOf (H := K ⊓ Subgroup.centralizer (D : Set G))
        (K := K) (L := K) le_rfl, Subgroup.subgroupOf_self, ← hker]
      rw [Subgroup.relIndex_ker (K := ⊤), Subgroup.map_top]
    calc (K ⊓ Subgroup.centralizer (D : Set G)).relIndex K
        = Nat.card ↥φ.range := hrel
      _ ≤ Nat.card ↥(V ⊓ wOf V H) := Subgroup.card_le_card_group (H := φ.range)
      _ = qBar V H := h.module

theorem BigEndHyp.card_inf_P_le_of_cover (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {k : ℕ} (D : Fin k → Subgroup G)
    (hDP : ∀ i, D i ≤ P) (hDV : ∀ i, D i ⊓ V = ⊥)
    (hTI : ∀ i, ∀ m ∈ M, conjSubgroup m (D i) ⊓ D i ≠ ⊥ → conjSubgroup m (D i) = D i)
    (hcover : P ≤ V ⊔ ((wOf V H ⊔ cPbar V H P) ⊓ P) ⊔ ⨆ i, D i) :
    Nat.card ↥((wOf V H ⊔ cPbar V H P) ⊓ P) ≤ qBar V H ^ k * qBar V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  set K : Subgroup G := (wOf V H ⊔ cPbar V H P) ⊓ P with hKdef
  set C : Subgroup G := (⨅ i, K ⊓ Subgroup.centralizer (D i : Set G)) ⊓ K with hCdef
  have hCK : C ≤ K := inf_le_right
  have hCA : C ≤ V ⊓ wOf V H := by
    intro b hb
    rw [hCdef] at hb
    obtain ⟨hbC, hbK⟩ := Subgroup.mem_inf.mp hb
    rw [hKdef] at hbK
    have hbD : ∀ i, b ∈ Subgroup.centralizer (D i : Set G) := fun i =>
      (Subgroup.mem_inf.mp (Subgroup.mem_iInf.mp hbC i)).2
    have hbCP : b ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxsup : x ∈ V ⊔ K ⊔ ⨆ i, D i := by
        rw [hKdef]
        exact hcover hx
      have hV : V ≤ Subgroup.centralizer ({b} : Set G) := fun v hv =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hc.commute_of_mem_P hbK.2 hv)
      have hK' : K ≤ Subgroup.centralizer ({b} : Set G) := fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (h.concl.2.2.comm hy.1 hbK.1)
      have hDs : (⨆ i, D i) ≤ Subgroup.centralizer ({b} : Set G) :=
        iSup_le fun i d hd =>
          Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hbD i) d hd)
      exact Subgroup.mem_centralizer_singleton_iff.mp
        ((sup_le (sup_le hV hK') hDs) hxsup)
    exact h.mem_inf_wOf_of_centralizes_P hZ hbK.1 hbCP
  have hcardC : Nat.card ↥C ≤ qBar V H := by
    calc Nat.card ↥C ≤ Nat.card ↥(V ⊓ wOf V H) := Subgroup.card_le_of_le hCA
      _ = qBar V H := h.module
  have hrelC : C.relIndex K ≤ qBar V H ^ k := by
    have h₁ : (⨅ i, K ⊓ Subgroup.centralizer (D i : Set G)).relIndex K
        ≤ ∏ i, (K ⊓ Subgroup.centralizer (D i : Set G)).relIndex K :=
      Subgroup.relIndex_iInf_le (L := K) _
    have h₂ : ∀ i, (K ⊓ Subgroup.centralizer (D i : Set G)).relIndex K ≤ qBar V H :=
      fun i => h.relIndex_centralizer_le hZ (hDP i) (hDV i) (hTI i) hKdef.le
    calc C.relIndex K
        = (⨅ i, K ⊓ Subgroup.centralizer (D i : Set G)).relIndex K := by
          rw [hCdef, Subgroup.inf_relIndex_right]
      _ ≤ ∏ i, (K ⊓ Subgroup.centralizer (D i : Set G)).relIndex K := h₁
      _ ≤ ∏ _ : Fin k, qBar V H := Finset.prod_le_prod fun i _ => h₂ i
      _ = qBar V H ^ k := by simp
  have hmul : C.relIndex K * Nat.card ↥C = Nat.card ↥K := by
    have h' := Subgroup.relIndex_mul_card (H := C) (K := K)
    rwa [inf_eq_left.mpr hCK] at h'
  calc Nat.card ↥K = C.relIndex K * Nat.card ↥C := hmul.symm
    _ ≤ qBar V H ^ k * qBar V H := Nat.mul_le_mul hrelC hcardC

theorem BigEndHyp.cPbar_le_wOf_of_cover (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {k : ℕ} (D : Fin k → Subgroup G)
    (hDP : ∀ i, D i ≤ P) (hDV : ∀ i, D i ⊓ V = ⊥)
    (hTI : ∀ i, ∀ m ∈ M, conjSubgroup m (D i) ⊓ D i ≠ ⊥ → conjSubgroup m (D i) = D i)
    (hcover : P ≤ V ⊔ ((wOf V H ⊔ cPbar V H P) ⊓ P) ⊔ ⨆ i, D i)
    (hPW : Nat.card ↥(P ⊓ wOf V H) = qBar V H ^ (k + 1)) :
    cPbar V H P ≤ wOf V H := by
  have hcard := h.card_inf_P_le_of_cover hZ D hDP hDV hTI hcover
  have hPW' : Nat.card ↥(P ⊓ wOf V H) = qBar V H ^ k * qBar V H := by
    rw [hPW, pow_succ]
  rw [← hPW'] at hcard
  have hle : P ⊓ wOf V H ≤ (wOf V H ⊔ cPbar V H P) ⊓ P :=
    le_inf ((inf_le_right : P ⊓ wOf V H ≤ wOf V H).trans le_sup_left) inf_le_left
  have heq : P ⊓ wOf V H = (wOf V H ⊔ cPbar V H P) ⊓ P :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  intro b hb
  have hbK : b ∈ (wOf V H ⊔ cPbar V H P) ⊓ P := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_sup_right hb
    · exact (Subgroup.mem_inf.mp hb).1
  rw [← heq] at hbK
  exact (Subgroup.mem_inf.mp hbK).2

end CFSG.RankThree.GF2n.Tim79a
