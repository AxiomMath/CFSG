module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Xi
public import CFSG.Quasithin.Background.A4

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L3213

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G] {T X : Subgroup G}

theorem pCoreOf_sup_eq_inf_sectionCentralizer (hT : quasithinIsSylowTwo T) (hX : IsXi T X) :
    pCoreOf 2 (X ⊔ T) = T ⊓ sectionCentralizer X (pCoreOf 2 X) := by
  refine le_antisymm (le_inf ?_ fun r hr => ?_) (xi_inf_sectionCentralizer_le hT hX)
  · exact pCoreOf_le_of_quasithinIsSylowTwo hT (le_sup_right.trans Subgroup.le_normalizer)
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.1
  have hrX : r ∈ Subgroup.normalizer (X : Set G) := hXTN (pCoreOf_le 2 _ hr)
  refine ⟨hrX, normalizer_le_normalizer_pCoreOf 2 X hrX, fun x hx => ?_⟩
  have h1 : r * x * r⁻¹ * x⁻¹ ∈ X :=
    X.mul_mem ((Subgroup.mem_normalizer_iff.mp hrX x).mp hx) (X.inv_mem hx)
  have h2 : r * x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 (X ⊔ T) := by
    have h3 : x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 (X ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (X ⊔ T)
        (le_sup_left (b := T) hx)) r⁻¹).mp ((pCoreOf 2 _).inv_mem hr)
    have e : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 _).mul_mem hr h3
  have hle : pCoreOf 2 (X ⊔ T) ⊓ X ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right (fun y hy => ?_)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact A4.mem_normalizer_inf (le_normalizer_pCoreOf 2 (X ⊔ T) (le_sup_left (b := T) hy))
      (Subgroup.le_normalizer hy)
  exact hle ⟨h2, h1⟩

theorem isSylowIn_pCoreOf_sup (hT : quasithinIsSylowTwo T) (hX : IsXi T X) :
    IsSylowIn 2 (pCoreOf 2 (X ⊔ T)) (sectionCentralizer X (pCoreOf 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ := Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G)
  have hTN : T ≤ N₀ := fun t ht => ⟨hX.2.1 ht, normalizer_le_normalizer_pCoreOf 2 X (hX.2.1 ht)⟩
  have hTS : IsSylowIn 2 T N₀ :=
    ⟨hTN, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTN))⟩
  have hCN : sectionCentralizer X (pCoreOf 2 X) ≤ N₀ := fun g hg => ⟨hg.1, hg.2.1⟩
  have hCn : ((sectionCentralizer X (pCoreOf 2 X)).subgroupOf N₀).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact conj_mem_sectionCentralizer g.2.1 g.2.2 hn⟩
  rw [pCoreOf_sup_eq_inf_sectionCentralizer hT hX]
  exact hTS.inf_normal hCN hCn

theorem relIndex_sectionCentralizer_eq (hT : quasithinIsSylowTwo T) (hX : IsXi T X) :
    (sectionCentralizer X (pCoreOf 2 X)).relIndex
        (Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G)) =
      (sectionCentralizer X (pCoreOf 2 X)).relIndex
        (Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓
          Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ := Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G)
  set C := sectionCentralizer X (pCoreOf 2 X) with hC
  set R := pCoreOf 2 (X ⊔ T) with hR
  have hRS := isSylowIn_pCoreOf_sup hT hX
  have hCN : C ≤ N₀ := fun g hg => ⟨hg.1, hg.2.1⟩
  have hNC : ∀ g ∈ N₀, g ∈ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype fun c hc => conj_mem_sectionCentralizer hg.1 hg.2 hc
  have hfrat : ∀ g ∈ N₀, ∃ c ∈ C, c * g ∈ Subgroup.normalizer (R : Set G) := by
    intro g hg
    obtain ⟨c, hc, hcR⟩ := exists_conj_of_isSylowIn hRS (isSylowIn_map_conj hRS (hNC g hg))
    refine ⟨c⁻¹, C.inv_mem hc, Subgroup.mem_normalizer_iff.mpr fun y => ?_⟩
    have h1 := hcR (g * y * g⁻¹)
    have h2 : g * y * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom ↔ y ∈ R := by
      constructor
      · rintro ⟨z, hz, hzy⟩
        have : z = y := by
          simpa [MulAut.conj_apply] using hzy
        rwa [← this]
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [h2] at h1
    rw [h1]
    have e : c⁻¹ * (g * y * g⁻¹) * c = c⁻¹ * g * y * (c⁻¹ * g)⁻¹ := by group
    rw [e]
  have hnormal : (C.subgroupOf N₀).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact conj_mem_sectionCentralizer g.2.1 g.2.2 hn⟩
  have hsup : (N₀ ⊓ Subgroup.normalizer (R : Set G)).subgroupOf N₀ ⊔ C.subgroupOf N₀ = ⊤ := by
    refine eq_top_iff.mpr fun h _ => ?_
    obtain ⟨c, hc, hch⟩ := hfrat h h.2
    have hn : (⟨c * h, N₀.mul_mem (hCN hc) h.2⟩ : N₀) ∈
        (N₀ ⊓ Subgroup.normalizer (R : Set G)).subgroupOf N₀ :=
      Subgroup.mem_subgroupOf.mpr ⟨N₀.mul_mem (hCN hc) h.2, hch⟩
    have hc' : (⟨c⁻¹, N₀.inv_mem (hCN hc)⟩ : N₀) ∈ C.subgroupOf N₀ :=
      Subgroup.mem_subgroupOf.mpr (C.inv_mem hc)
    have := Subgroup.mul_mem_sup hc' hn
    rwa [sup_comm, show (⟨c⁻¹, N₀.inv_mem (hCN hc)⟩ : N₀) * ⟨c * h, _⟩ = h from
      Subtype.ext (by simp)] at this
  have h1 := Subgroup.relIndex_sup_right ((N₀ ⊓ Subgroup.normalizer (R : Set G)).subgroupOf N₀)
    (C.subgroupOf N₀)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf inf_le_left] at h1
  exact h1

theorem exists_pow_eq_one_not_mem_sectionCentralizer (hT : quasithinIsSylowTwo T) (hX : IsXi T X)
    {q : ℕ} [Fact q.Prime]
    (hq : q ∣ (sectionCentralizer X (pCoreOf 2 X)).relIndex
      (Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G))) :
    ∃ h : G, h ∈ Subgroup.normalizer (X : Set G) ∧
      h ∈ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) ∧
      h ∉ sectionCentralizer X (pCoreOf 2 X) ∧ ∃ b : ℕ, h ^ q ^ b = 1 := by
  rw [relIndex_sectionCentralizer_eq hT hX] at hq
  set H := Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓
    Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) with hH
  obtain ⟨Q, hQ, -⟩ := exists_isSylowIn_ge q (bot_le : (⊥ : Subgroup G) ≤ H) IsPGroup.of_bot
  by_contra hcon
  push Not at hcon
  have hQC : Q ≤ sectionCentralizer X (pCoreOf 2 X) := by
    intro h hh
    by_contra hhC
    obtain ⟨b, hb⟩ := hQ.isPGroup ⟨h, hh⟩
    have hb' : h ^ q ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hhH := hQ.le hh
    exact hcon h hhH.1.1 hhH.2 hhC b hb'
  exact hQ.not_dvd_relIndex (hq.trans (Subgroup.relIndex_dvd_of_le_left H hQC))

end CFSG.Quasithin.EmptyFaithfulMultiple.L3213
