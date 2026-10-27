module

public import CFSG.Quasithin.Vol2.Ch10SecKRPa
public import CFSG.Quasithin.Vol2.Ch10SecA312C1
public import CFSG.Quasithin.Background.A3Structure312Nonquasi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRP

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Q : Type} [Group Q]

theorem map_pCoreOf_subgroupOf {B K : Subgroup Q} (hBK : B ≤ K) :
    (pCoreOf 2 (B.subgroupOf K)).map K.subtype = pCoreOf 2 B := by
  unfold pCoreOf
  rw [Subgroup.map_map]
  have h : K.subtype.comp (B.subgroupOf K).subtype =
      B.subtype.comp (Subgroup.subgroupOfEquivOfLe hBK).toMonoidHom := by
    ext x
    rfl
  rw [h, ← Subgroup.map_map, CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hBK)]

theorem map_commutator_subgroupOf {B₁ B₂ K : Subgroup Q} (h₁ : B₁ ≤ K) (h₂ : B₂ ≤ K) :
    (⁅B₁.subgroupOf K, B₂.subgroupOf K⁆).map K.subtype = ⁅B₁, B₂⁆ := by
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left h₁, inf_of_le_left h₂]

theorem commutator_subgroupOf_le {B₁ B₂ K : Subgroup Q} (h₁ : B₁ ≤ K) (h₂ : B₂ ≤ K)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁) :
    ⁅B₁.subgroupOf K, B₂.subgroupOf K⁆ ≤ pCoreOf 2 (B₁.subgroupOf K) := by
  intro x hx
  have hx' : (x : Q) ∈ (pCoreOf 2 (B₁.subgroupOf K)).map K.subtype := by
    rw [map_pCoreOf_subgroupOf h₁]
    exact hc (by rw [← map_commutator_subgroupOf h₁ h₂]; exact ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := hx'
  rwa [← Subtype.ext hyx]

theorem commutator_subgroupOf_le' {B₁ B₂ K : Subgroup Q} (h₁ : B₁ ≤ K) (h₂ : B₂ ≤ K)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁) :
    ⁅B₁.subgroupOf K, B₂.subgroupOf K⁆ ≤ (pCoreOf 2 B₁).subgroupOf K := fun x hx =>
  hc (by rw [← map_commutator_subgroupOf h₁ h₂]; exact ⟨x, hx, rfl⟩)

theorem perfect_subgroupOf {B K : Subgroup Q} (hBK : B ≤ K) (hB : ⁅B, B⁆ = B) :
    ⁅B.subgroupOf K, B.subgroupOf K⁆ = B.subgroupOf K :=
  Subgroup.map_injective K.subtype_injective (by
    rw [map_commutator_subgroupOf hBK hBK, Subgroup.subgroupOf_map_subtype, inf_of_le_left hBK,
      hB])

theorem eq_bot_of_subgroupOf_eq_bot {B K : Subgroup Q} (hBK : B ≤ K) (h : B.subgroupOf K = ⊥) :
    B = ⊥ := by
  rw [← inf_of_le_left hBK, ← Subgroup.subgroupOf_map_subtype, h, Subgroup.map_bot]

theorem isPGroup_pCoreOf (B : Subgroup Q) : IsPGroup 2 (pCoreOf 2 B) := by
  unfold pCoreOf
  exact CFSG.pCore_isPGroup.map B.subtype

theorem le_of_subgroupOf_eq_top {B K : Subgroup Q} (h : B.subgroupOf K = ⊤) : K ≤ B :=
  fun x hx => by
    have : (⟨x, hx⟩ : ↥K) ∈ B.subgroupOf K := by rw [h]; trivial
    exact this

theorem subgroupOf_le_normalizer {S K B : Subgroup Q}
    (hN : S ≤ Subgroup.normalizer (B : Set Q)) : (S ⊓ K).subgroupOf K ≤
      Subgroup.normalizer ((B.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_subgroupOf.mp ht).1) (h : Q)

theorem false_of_quasisimple (hPC : A312PairCent) (hQ : Vol2Native.SQTKHypCat Q)
    {S K B₁ B₂ : Subgroup Q} (hS : IsSylowTwoOf S ⊤) (hK : K ∈ cComp (⊤ : Subgroup Q))
    (hB₁ : B₁ ∈ lFamily S) (hB₂ : B₂ ∈ lFamily S) (hN₁ : S ≤ Subgroup.normalizer (B₁ : Set Q))
    (hN₂ : S ≤ Subgroup.normalizer (B₂ : Set Q)) (hB₁K : B₁ ≤ K) (hB₂K : B₂ ≤ K)
    (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂) (e : ModO2 B₁ ≃* ModO2 B₂)
    (hq : CFSG.IsQuasisimple ↥K) : False := by
  have := hQ.finite
  have hKs : Vol2Native.SQTKHypCat ↥K := hQ.of_subnormal (subnormal_of_mem_cComp hK)
  obtain ⟨hT, hB₁'⟩ := A312.isSylowTwoOf_lFamily_subgroupOf hS hK hB₁K hB₁
  obtain ⟨-, hB₂'⟩ := A312.isSylowTwoOf_lFamily_subgroupOf hS hK hB₂K hB₂
  have hB₁ne : B₁ ≠ ⊥ := ne_bot_of_mem_cComp (show B₁ ∈ cComp (B₁ ⊔ S) from hB₁)
  have hB₂ne : B₂ ≠ ⊥ := ne_bot_of_mem_cComp (show B₂ ∈ cComp (B₂ ⊔ S) from hB₂)
  have hB₁p : ⁅B₁, B₁⁆ = B₁ := perfect_of_mem_cComp (show B₁ ∈ cComp (B₁ ⊔ S) from hB₁)
  have hB₂p : ⁅B₂, B₂⁆ = B₂ := perfect_of_mem_cComp (show B₂ ∈ cComp (B₂ ⊔ S) from hB₂)
  have hkey : ∀ B : Subgroup Q, ⁅B, B⁆ = B → B ≤ ⁅B₁, B₂⁆ → B = ⊥ := by
    intro B hBp hB
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (isPGroup_pCoreOf B₁).isNilpotent
    exact eq_bot_of_perfect_of_le (hB.trans (hc.trans inf_le_left)) hBp
  have hne₁ : B₁.subgroupOf K ≠ ⊤ := fun htop => hB₂ne (hkey B₂ hB₂p (by
    calc B₂ = ⁅B₂, B₂⁆ := hB₂p.symm
      _ ≤ ⁅B₁, B₂⁆ :=
        Subgroup.commutator_mono (hB₂K.trans (le_of_subgroupOf_eq_top htop)) le_rfl))
  have hne₂ : B₂.subgroupOf K ≠ ⊤ := fun htop => hB₁ne (hkey B₁ hB₁p (by
    calc B₁ = ⁅B₁, B₁⁆ := hB₁p.symm
      _ ≤ ⁅B₁, B₂⁆ :=
        Subgroup.commutator_mono le_rfl (hB₁K.trans (le_of_subgroupOf_eq_top htop))))
  have hne₁₂ : B₁.subgroupOf K ≠ B₂.subgroupOf K := by
    intro h12
    have h : B₁ = B₂ := by
      rw [Subgroup.subgroupOf_inj, inf_of_le_left hB₁K, inf_of_le_left hB₂K] at h12
      exact h12
    exact hB₁ne (hkey B₁ hB₁p (le_of_eq (by rw [← h, hB₁p])))
  have hcK : ⁅B₁.subgroupOf K, B₂.subgroupOf K⁆ ≤
      pCoreOf 2 (B₁.subgroupOf K) ⊓ pCoreOf 2 (B₂.subgroupOf K) := by
    refine le_inf (commutator_subgroupOf_le hB₁K hB₂K (hc.trans inf_le_left)) ?_
    rw [Subgroup.commutator_comm]
    refine commutator_subgroupOf_le hB₂K hB₁K ?_
    rw [Subgroup.commutator_comm]
    exact hc.trans inf_le_right
  exact hPC ↥K hq hKs.isSQTKCat hKs.o2 _ hT _ hB₁' _ hB₂' hne₁ hne₂ hne₁₂
    (subgroupOf_le_normalizer hN₁) (subgroupOf_le_normalizer hN₂) hcK
    ⟨(A312.modO2Equiv (Subgroup.subgroupOfEquivOfLe hB₁K)).trans
      (e.trans (A312.modO2Equiv (Subgroup.subgroupOfEquivOfLe hB₂K)).symm)⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.KRP
