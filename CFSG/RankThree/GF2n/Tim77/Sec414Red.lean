module

public import CFSG.CGT.Timmesfeld75.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

@[expose] def Sec414InO2 {G : Type} [Group G] (V : Subgroup G) (x : G) : Prop :=
  ∃ P : Subgroup G, P ≤ V ∧ IsPGroup 2 P ∧ (∀ v ∈ V, ∀ p ∈ P, v * p * v⁻¹ ∈ P) ∧ x ∈ P

variable {G : Type} [Group G]

private theorem sec414_conj_le {T V : Subgroup G} (hTV : T ≤ V) {u : G} (hu : u ∈ V) :
    conjSubgroup u T ≤ V := by
  intro y hy
  have h := V.mul_mem (V.mul_mem hu (hTV (mem_conjSubgroup.1 hy))) (V.inv_mem hu)
  simpa [mul_assoc] using h

private theorem sec414_conj_conj (g h : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup h T) = conjSubgroup (g * h) T := by
  ext x
  simp only [mem_conjSubgroup]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

private theorem sec414_conj_sup (g : G) (S T : Subgroup G) :
    conjSubgroup g (S ⊔ T) = conjSubgroup g S ⊔ conjSubgroup g T :=
  Subgroup.map_sup S T _

private theorem sec414_card_conj (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem sec414_conj_one (T : Subgroup G) : conjSubgroup 1 T = T := by
  ext x
  simp [mem_conjSubgroup]

private theorem sec414_conj_inv_conj (g : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup g⁻¹ T) = T := by
  rw [sec414_conj_conj, mul_inv_cancel, sec414_conj_one]

private theorem sec414_conj_sup_inv (g : G) (A : Subgroup G) :
    conjSubgroup g (A ⊔ conjSubgroup g⁻¹ A) = A ⊔ conjSubgroup g A := by
  rw [sec414_conj_sup, sec414_conj_inv_conj, sup_comm]

variable [Finite G]

theorem sec414_inO2_conj {V : Subgroup G} {x : G} (g : G) (h : Sec414InO2 V x) :
    Sec414InO2 (conjSubgroup g V) (g * x * g⁻¹) := by
  obtain ⟨P, hPV, hP2, hPn, hxP⟩ := h
  refine ⟨conjSubgroup g P, Subgroup.map_mono hPV, ?_, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP2
    exact (IsPGroup.iff_card).2 ⟨n, by rw [sec414_card_conj, hn]⟩
  · intro v hv p hp
    rw [mem_conjSubgroup] at hv hp ⊢
    have h := hPn _ hv _ hp
    rwa [show g⁻¹ * (v * p * v⁻¹) * g = g⁻¹ * v * g * (g⁻¹ * p * g) * (g⁻¹ * v * g)⁻¹ by group]
  · rw [mem_conjSubgroup, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hxP

theorem sec414_inO2_pair {V : Subgroup G} {x y : G} (hx : Sec414InO2 V x)
    (hy : Sec414InO2 V y) : IsPGroup 2 ↥(Subgroup.closure ({x, y} : Set G)) := by
  obtain ⟨P, hPV, hP2, hPn, hxP⟩ := hx
  obtain ⟨Q, hQV, hQ2, hQn, hyQ⟩ := hy
  have hnorm : P ≤ Subgroup.normalizer (Q : Set G) := by
    intro p hp
    have hpV := hPV hp
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQn p hpV q hq, fun hq => ?_⟩
    have := hQn p⁻¹ (V.inv_mem hpV) _ hq
    simpa [mul_assoc] using this
  refine (hP2.to_sup_of_normal_right' hQ2 hnorm).to_le ?_
  rw [Subgroup.closure_le]
  rintro z (rfl | rfl)
  · exact Subgroup.mem_sup_left hxP
  · exact Subgroup.mem_sup_right hyQ

theorem sec414_inO2_iff {V : Subgroup G} {x : G} (hx : x ∈ V) :
    Sec414InO2 V x ↔ (⟨x, hx⟩ : ↥V) ∈ CFSG.pCore 2 ↥V := by
  constructor
  · rintro ⟨P, hPV, hP2, hPn, hxP⟩
    have hle : P.subgroupOf V ≤ CFSG.pCore 2 ↥V := by
      refine le_sSup ⟨⟨fun n hn g => ?_⟩, hP2.comap_subtype⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hPn g g.2 n hn
    exact hle (Subgroup.mem_subgroupOf.mpr hxP)
  · intro h
    refine ⟨(CFSG.pCore 2 ↥V).map V.subtype, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨q, -, rfl⟩
      exact q.2
    · exact (CFSG.pCore_isPGroup (p := 2) (G := ↥V)).map V.subtype
    · rintro v hv _ ⟨q, hq, rfl⟩
      exact ⟨⟨v, hv⟩ * q * ⟨v, hv⟩⁻¹,
        (CFSG.pCore_normal (p := 2) (G := ↥V)).conj_mem q hq ⟨v, hv⟩, rfl⟩
    · exact ⟨⟨x, hx⟩, h, rfl⟩

theorem sec414_a0_le_pCore {A A0 : Subgroup G} (hA : IsPGroup 2 A) (hA0 : A0 ≤ A)
    (hall : ∀ g : G, ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup g A) x) :
    A0 ≤ CFSG.pCore 2 G := by
  intro x hx
  refine CFSG.BaerSuzuki.baer_suzuki (p := 2) x
    (hA.to_le (Subgroup.zpowers_le.2 (hA0 hx))) fun g => ?_
  have h2 := sec414_inO2_conj g (hall g⁻¹ x hx)
  rw [sec414_conj_sup_inv] at h2
  exact sec414_inO2_pair (hall g x hx) h2

private theorem sec414_pair_iff {V : Subgroup G} (a b : V) :
    IsPGroup 2 ↥(Subgroup.closure ({a, b} : Set V)) ↔
      IsPGroup 2 ↥(Subgroup.closure ({(a : G), (b : G)} : Set G)) := by
  have h : Subgroup.closure ({(a : G), (b : G)} : Set G) =
      (Subgroup.closure ({a, b} : Set V)).map V.subtype := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [h, IsPGroup.iff_card, IsPGroup.iff_card,
    Subgroup.card_map_of_injective V.subtype_injective]

private theorem sec414_zpowers_subtype {V : Subgroup G} {x : G} (hx : x ∈ V)
    (h : IsPGroup 2 ↥(Subgroup.zpowers x)) : IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hx⟩ : ↥V)) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h
  refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers, hn]

private theorem sec414_step {A A0 : Subgroup G} (hA : IsPGroup 2 A) (hA0 : A0 ≤ A) {g : G}
    (hg : ¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup g A) x)
    (hmin : ∀ h : G, (¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup h A) x) →
      Nat.card ↥(A ⊔ conjSubgroup g A) ≤ Nat.card ↥(A ⊔ conjSubgroup h A)) :
    ∃ g' : G, (¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup g' A) x) ∧
      g' ∈ A ⊔ conjSubgroup g' A ∧ A ⊔ conjSubgroup g' A = A ⊔ conjSubgroup g A := by
  push Not at hg
  obtain ⟨x, hxA0, hxV⟩ := hg
  have hxA : x ∈ A := hA0 hxA0
  set V := A ⊔ conjSubgroup g A with hV
  have hxV' : x ∈ V := Subgroup.mem_sup_left hxA
  have hnot : (⟨x, hxV'⟩ : ↥V) ∉ CFSG.pCore 2 ↥V := fun h => hxV ((sec414_inO2_iff hxV').2 h)
  have h2el : IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hxV'⟩ : ↥V)) :=
    sec414_zpowers_subtype hxV' (hA.to_le (Subgroup.zpowers_le.2 hxA))
  obtain ⟨⟨w, hw⟩, hu⟩ : ∃ u : ↥V, ¬ IsPGroup 2
      ↥(Subgroup.closure ({(⟨x, hxV'⟩ : ↥V), u * ⟨x, hxV'⟩ * u⁻¹} : Set ↥V)) := by
    by_contra hcon
    push Not at hcon
    exact hnot (CFSG.BaerSuzuki.baer_suzuki (p := 2) _ h2el hcon)
  have hu' : ¬ IsPGroup 2 ↥(Subgroup.closure ({x, w * x * w⁻¹} : Set G)) :=
    fun h => hu ((sec414_pair_iff (V := V) _ _).2 h)
  have hle : ∀ v : G, v ∈ V → A ⊔ conjSubgroup v A ≤ V := fun v hv =>
    sup_le le_sup_left (sec414_conj_le le_sup_left hv)
  by_cases hxw : Sec414InO2 (A ⊔ conjSubgroup w A) x
  · have hbad : ¬ ∀ y ∈ A0, Sec414InO2 (A ⊔ conjSubgroup w⁻¹ A) y := by
      intro hall
      have h1 := sec414_inO2_conj w (hall x hxA0)
      rw [sec414_conj_sup_inv] at h1
      exact hu' (sec414_inO2_pair hxw h1)
    have heq : A ⊔ conjSubgroup w⁻¹ A = V :=
      Subgroup.eq_of_le_of_card_ge (hle w⁻¹ (V.inv_mem hw)) (hmin w⁻¹ hbad)
    exact ⟨w⁻¹, hbad, by rw [heq]; exact V.inv_mem hw, heq⟩
  · have hbad : ¬ ∀ y ∈ A0, Sec414InO2 (A ⊔ conjSubgroup w A) y := fun h => hxw (h x hxA0)
    have heq : A ⊔ conjSubgroup w A = V :=
      Subgroup.eq_of_le_of_card_ge (hle w hw) (hmin w hbad)
    exact ⟨w, hbad, heq ▸ hw, heq⟩

theorem sec414_exists_min_bad {A A0 : Subgroup G} (hA : IsPGroup 2 A) (hA0 : A0 ≤ A)
    (hbad : ∃ g : G, ¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup g A) x) :
    ∃ g : G, (¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup g A) x) ∧ g ∈ A ⊔ conjSubgroup g A ∧
      ∀ h : G, (¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup h A) x) →
        Nat.card ↥(A ⊔ conjSubgroup g A) ≤ Nat.card ↥(A ⊔ conjSubgroup h A) := by
  classical
  have hex : ∃ n : ℕ, ∃ g : G, (¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup g A) x) ∧
      Nat.card ↥(A ⊔ conjSubgroup g A) = n := by
    obtain ⟨g, hg⟩ := hbad
    exact ⟨_, g, hg, rfl⟩
  obtain ⟨g₀, hg₀, hcard₀⟩ := Nat.find_spec hex
  have hmin : ∀ h : G, (¬ ∀ x ∈ A0, Sec414InO2 (A ⊔ conjSubgroup h A) x) →
      Nat.card ↥(A ⊔ conjSubgroup g₀ A) ≤ Nat.card ↥(A ⊔ conjSubgroup h A) := by
    intro h hh
    rw [hcard₀]
    exact Nat.find_min' hex ⟨h, hh, rfl⟩
  obtain ⟨g', hg', hmem, heq⟩ := sec414_step hA hA0 hg₀ hmin
  refine ⟨g', hg', hmem, fun h hh => ?_⟩
  rw [heq]
  exact hmin h hh

end CFSG.RankThree.GF2n.Tim77
