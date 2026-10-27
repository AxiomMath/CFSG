module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A12
public import CFSG.Quasithin.Vol2.Ch10SecQ4A4
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G : Type} [Group G] {K J : Subgroup G}

theorem quot_isQuasisimple (hK : IsShort2 K) (h5 : IsAltType K 5) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  refine hK.2.2.2.1.resolve_right ?_
  obtain ⟨α, hα, hαk, -⟩ := h5
  have e := (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem exists_two_blockU (h5 : IsAltType K 5) (hZ : blockZ K = ⊥) :
    ∃ u₁ ∈ blockU K, ∃ u₂ ∈ blockU K, u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ := by
  obtain ⟨-, -, -, β, hβs, hβk, -⟩ := h5
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  have h1 : (Pi.single 0 1 + Pi.single 1 1 : Fin 5 → ZMod 2) ∈ evenWeight 5 := by
    rw [evenWeight, AddMonoidHom.mem_ker]
    decide
  have h2 : (Pi.single 2 1 + Pi.single 3 1 : Fin 5 → ZMod 2) ∈ evenWeight 5 := by
    rw [evenWeight, AddMonoidHom.mem_ker]
    decide
  obtain ⟨u₁, hu₁⟩ := hβs (Multiplicative.ofAdd ⟨_, h1⟩)
  obtain ⟨u₂, hu₂⟩ := hβs (Multiplicative.ofAdd ⟨_, h2⟩)
  have hv : ∀ (x : Fin 5 → ZMod 2) (hx : x ∈ evenWeight 5), x ≠ 0 →
      Multiplicative.ofAdd (⟨x, hx⟩ : evenWeight 5) ≠ 1 := by
    intro x hx hx0 h
    apply hx0
    have := congrArg (fun y => ((Multiplicative.toAdd y : evenWeight 5) : Fin 5 → ZMod 2)) h
    simpa using this
  refine ⟨u₁, u₁.2, u₂, u₂.2, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : u₁ = 1 := Subtype.ext h
    rw [this, map_one] at hu₁
    exact hv _ h1 (by decide) hu₁.symm
  · have : u₂ = 1 := Subtype.ext h
    rw [this, map_one] at hu₂
    exact hv _ h2 (by decide) hu₂.symm
  · have : u₁ = u₂ := Subtype.ext h
    rw [this, hu₂] at hu₁
    have := congrArg (fun y => ((Multiplicative.toAdd y : evenWeight 5) : Fin 5 → ZMod 2) 0) hu₁
    simp only [toAdd_ofAdd] at this
    revert this
    decide

theorem inf_pCoreOf_le_center (hKJ : K ≤ J) (hUQ : blockU K ⊓ pCoreOf 2 J = ⊥) :
    K ⊓ pCoreOf 2 J ≤ K ⊓ Subgroup.centralizer (K : Set G) := by
  have hPnorm : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J
  rintro x ⟨hxK, hxQ⟩
  refine ⟨hxK, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have h1 : x * k * x⁻¹ * k⁻¹ ∈ blockU K :=
    Subgroup.commutator_mem_commutator (inf_pCoreOf_le_blockQ hKJ ⟨hxK, hxQ⟩) hk
  have h2 : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 J := by
    have h3 : k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 J :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm (hKJ hk)) x⁻¹).mp (Subgroup.inv_mem _ hxQ)
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hxQ h3
  have h4 : x * k * x⁻¹ * k⁻¹ ∈ blockU K ⊓ pCoreOf 2 J := ⟨h1, h2⟩
  rw [hUQ, Subgroup.mem_bot] at h4
  have := congrArg (· * (k * x)) h4
  simp only [one_mul] at this
  rw [← this]
  group

variable {Y : Type} [Group Y]

theorem imgL_center_of_injective (f : ↥K →* Y) (hf : Function.Injective f) :
    imgL f (K ⊓ Subgroup.centralizer (K : Set G)) =
      (Subgroup.center ↥f.range).map f.range.subtype := by
  rw [map_center_eq_inf]
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_imgL f).mp hy
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨l, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 l l.2)
  · rintro y ⟨⟨x, rfl⟩, hyc⟩
    refine (mem_imgL f).mpr ⟨x, ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hyc (f ⟨l, hl⟩) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (hf this)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
