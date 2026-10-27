module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.A5

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem le_of_odd_relIndex_of_A5 {H N X : Subgroup G} (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (hodd : Odd (N.relIndex H)) (hXH : X ≤ H)
    (hX : Nonempty (X ≃* alternatingGroup (Fin 5))) : X ≤ N := by
  obtain ⟨eX⟩ := hX
  haveI := hNn
  have hdvd : N.relIndex X ∣ N.relIndex H := by
    have h := Subgroup.relIndex_dvd_index_of_normal (N.subgroupOf H) (X.subgroupOf H)
    rwa [Subgroup.relIndex_subgroupOf hXH] at h
  have hXN : ((N ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnN, hnX⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, X.mul_mem (X.mul_mem g.2 hnX) (X.inv_mem g.2)⟩
    have := hNn.conj_mem ⟨n, hXH hnX⟩ (by simpa [Subgroup.mem_subgroupOf] using hnN)
      ⟨g, hXH g.2⟩
    simpa [Subgroup.mem_subgroupOf] using this
  haveI : IsSimpleGroup X := eX.isSimpleGroup
  rcases hXN.eq_bot_or_eq_top with h | h
  · exfalso
    have hbot : N ⊓ X = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      have : (⟨x, (Subgroup.mem_inf.mp hx).2⟩ : X) ∈ (N ⊓ X).subgroupOf X := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
    have hcard := Subgroup.relIndex_mul_card (H := N) (K := X)
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_congr eX.toEquiv] at hcard
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card]; rfl
    rw [h60] at hcard
    rw [hcard] at hdvd
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat hdvd)) (by decide)
  · intro x hx
    have : (⟨x, hx⟩ : X) ∈ (N ⊓ X).subgroupOf X := by rw [h]; trivial
    rw [Subgroup.mem_subgroupOf] at this
    exact (Subgroup.mem_inf.mp this).1

theorem normal_of_simple_of_odd_relIndex {L N₀ X : Subgroup G} [hL : L.Normal] (hN₀L : N₀ ≤ L)
    (hN₀n : (N₀.subgroupOf L).Normal) (hodd : Odd (N₀.relIndex L)) (hsimp : IsSimpleGroup N₀)
    (hXL : X ≤ L) (hX : Nonempty (X ≃* alternatingGroup (Fin 5))) : N₀.Normal := by
  have hXN₀ := le_of_odd_relIndex_of_A5 hN₀L hN₀n hodd hXL hX
  refine ⟨fun n hn g => ?_⟩
  set φ : G ≃* G := MulAut.conj g
  set N₁ : Subgroup G := N₀.map φ.toMonoidHom
  have hcard : Nat.card N₁ = Nat.card N₀ :=
    Subgroup.card_map_of_injective φ.injective
  have hN₁L : N₁ ≤ L := by
    rintro _ ⟨x, hx, rfl⟩; exact hL.conj_mem x (hN₀L hx) g
  have hN₁n : (N₁.subgroupOf L).Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨g⁻¹ * l * g * y * (g⁻¹ * l * g)⁻¹, ?_, ?_⟩
    · have hl : g⁻¹ * (l : G) * g ∈ L := by
        have := hL.conj_mem _ l.2 g⁻¹; simpa using this
      have := hN₀n.conj_mem ⟨y, hN₀L hy⟩ (by simpa [Subgroup.mem_subgroupOf] using hy)
        ⟨_, hl⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxy ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxy]; group
  have hodd₁ : Odd (N₁.relIndex L) := by
    have h1 := Subgroup.relIndex_mul_card (H := N₀) (K := L)
    have h2 := Subgroup.relIndex_mul_card (H := N₁) (K := L)
    rw [inf_eq_left.mpr hN₀L] at h1
    rw [inf_eq_left.mpr hN₁L, hcard] at h2
    have hpos : 0 < Nat.card N₀ := Nat.card_pos
    have : N₁.relIndex L = N₀.relIndex L := by
      have := h1.trans h2.symm
      exact (Nat.eq_of_mul_eq_mul_right hpos this).symm
    rw [this]; exact hodd
  have hXN₁ := le_of_odd_relIndex_of_A5 hN₁L hN₁n hodd₁ hXL hX
  haveI : IsSimpleGroup N₁ := ((Subgroup.equivMapOfInjective N₀ φ.toMonoidHom φ.injective).symm.isSimpleGroup)
  have hI : ((N₀ ⊓ N₁).subgroupOf N₁).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, N₁.mul_mem (N₁.mul_mem y.2 hx1) (N₁.inv_mem y.2)⟩
    have := hN₀n.conj_mem ⟨x, hN₀L hx0⟩ (by simpa [Subgroup.mem_subgroupOf] using hx0)
      ⟨y, hN₁L y.2⟩
    simpa [Subgroup.mem_subgroupOf] using this
  obtain ⟨eX⟩ := hX
  have hne : (N₀ ⊓ N₁).subgroupOf N₁ ≠ ⊥ := by
    intro h
    have hx1 : ∃ x : X, x ≠ 1 := by
      obtain ⟨x, hx⟩ : ∃ x : alternatingGroup (Fin 5), x ≠ 1 := by decide +kernel
      exact ⟨eX.symm x, by simpa using hx⟩
    obtain ⟨x, hx⟩ := hx1
    have : (⟨x, hXN₁ x.2⟩ : N₁) ∈ (N₀ ⊓ N₁).subgroupOf N₁ := by
      rw [Subgroup.mem_subgroupOf]; exact Subgroup.mem_inf.mpr ⟨hXN₀ x.2, hXN₁ x.2⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx (Subtype.ext (congrArg Subtype.val this : (x : G) = 1))
  have htop := (hI.eq_bot_or_eq_top).resolve_left hne
  have hN₁N₀ : N₁ ≤ N₀ := by
    intro x hx
    have : (⟨x, hx⟩ : N₁) ∈ (N₀ ⊓ N₁).subgroupOf N₁ := by rw [htop]; trivial
    rw [Subgroup.mem_subgroupOf] at this
    exact (Subgroup.mem_inf.mp this).1
  have heq : N₁ = N₀ := Subgroup.eq_of_le_of_card_ge hN₁N₀ hcard.ge
  have : φ n ∈ N₁ := ⟨n, hn, rfl⟩
  rw [heq] at this
  simpa [φ, MulAut.conj_apply] using this

theorem centralizer_eq_bot_of_odd_relIndex {L N₀ : Subgroup G} [hL : L.Normal] [hN₀ : N₀.Normal]
    (hL2 : L.index = 2) (hN₀L : N₀ ≤ L) (hodd : Odd (N₀.relIndex L))
    (hZ : Subgroup.center N₀ = ⊥)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hcen : Subgroup.center G = ⊥) : Subgroup.centralizer (N₀ : Set G) = ⊥ := by
  set C := Subgroup.centralizer (N₀ : Set G)
  haveI hCn : C.Normal := inferInstance
  have hCL : C ⊓ L = ⊥ := by
    have hinf : N₀ ⊓ (C ⊓ L) = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      have h1 := Subgroup.mem_inf.mp hx
      have hx0 := h1.1
      have hxC := (Subgroup.mem_inf.mp h1.2).1
      have : (⟨x, hx0⟩ : N₀) ∈ Subgroup.center N₀ := by
        rw [Subgroup.mem_center_iff]; intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
      rw [hZ, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hdvd : N₀.relIndex (C ⊓ L) ∣ N₀.relIndex L := by
      have h := Subgroup.relIndex_dvd_index_of_normal (N₀.subgroupOf L) ((C ⊓ L).subgroupOf L)
      rwa [Subgroup.relIndex_subgroupOf inf_le_right] at h
    have hc := Subgroup.relIndex_mul_card (H := N₀) (K := C ⊓ L)
    rw [hinf, Subgroup.card_bot, mul_one] at hc
    have hodd' : Odd (Nat.card (C ⊓ L : Subgroup G)) := hc ▸ hodd.of_dvd_nat hdvd
    exact hrad _ inferInstance (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd')
  have hC2 : Nat.card C ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := C)
    rw [inf_comm, hCL, Subgroup.card_bot, mul_one] at h
    rw [← h]
    exact Nat.le_of_dvd (by norm_num) (hL2 ▸ Subgroup.relIndex_dvd_index_of_normal L C)
  rw [eq_bot_iff, ← hcen]
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro g
  have hgc : g * c * g⁻¹ ∈ C := hCn.conj_mem c hc g
  by_cases h1 : c = 1
  · rw [h1]; group
  ·
    have : g * c * g⁻¹ = c := by
      by_contra hne
      have hgc1 : g * c * g⁻¹ ≠ 1 := fun h => h1 (by
        calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group)
      have : 3 ≤ Nat.card C := by
        classical
        letI := Fintype.ofFinite C
        rw [Nat.card_eq_fintype_card]
        have : ({1, ⟨c, hc⟩, ⟨_, hgc⟩} : Finset C).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair]
          · exact fun h => hne (congrArg Subtype.val h).symm
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => h1 (congrArg Subtype.val h).symm,
              fun h => hgc1 (congrArg Subtype.val h).symm⟩
        rw [← this]; exact Finset.card_le_univ _
      omega
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [this]

end CFSG.OddTranspositions.QZ
