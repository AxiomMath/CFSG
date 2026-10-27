module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSLBasic
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType

namespace LayerFacts

theorem exists_mul_ne_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem ggIsPerfect_of_commutator_eq {L : Type*} [Group L] {H : Subgroup L} (hH : ⁅H, H⁆ = H) :
    Group.IsPerfect H := by
  rw [Group.isPerfect_def]
  apply Subgroup.map_injective H.subtype_injective
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, hH]

theorem ggCommutator_eq_of_isQuasisimple {L : Type*} [Group L] {K : Subgroup L}
    (hq : CFSG.IsQuasisimple K) : ⁅K, K⁆ = K := by
  have h := congrArg (Subgroup.map K.subtype) (Group.isPerfect_def.mp hq.1)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem odd_card_of_forall_sq_eq_one {L : Type*} [Group L] [Finite L]
    (h : ∀ x : L, x ^ 2 = 1 → x = 1) : Odd (Nat.card L) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx1 := h x (by rw [← hx]; exact pow_orderOf_eq_one x)
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

open CFSG.Assembly in
theorem ggLayer_of_core {L : Type*} [Group L] [Finite L] {G : Type*} [Group G] (ψ : L →* G)
    (hker : ψ.ker ≤ Subgroup.center L) {H : Subgroup G} {C₀ : Subgroup L}
    (hC₀H : C₀.map ψ ≤ H) (hnorm : ((C₀.map ψ).subgroupOf H).Normal)
    (hcomm : ⁅H, H⁆ ≤ C₀.map ψ) {β : Type*} (S : β → Subgroup L) (hSC : ∀ b, S b ≤ C₀)
    (hSn : ∀ b, ∀ c ∈ C₀, ∀ s ∈ S b, c * s * c⁻¹ ∈ S b) (hSq : ∀ b, CFSG.IsQuasisimple (S b))
    (hder : ∃ k, ggDer C₀ k ≤ ⨆ b, S b)
    (hZ : ∀ z ∈ ⨆ b, S b, (∀ y ∈ ⨆ b, S b, z * y = y * z) → z ^ 2 = 1 → z = 1) :
    LargeEvenLayer H = (⨆ b, S b).map ψ ∧ Odd (Nat.card (Subgroup.center ↥(LargeEvenLayer H))) ∧
      ∀ X : Subgroup G, X ≤ H → ⁅X, X⁆ = X → X ≤ LargeEvenLayer H := by
  set Ñ := ⨆ b, S b with hÑ
  have hcomp : ∀ b, IsComponentOf ((S b).map ψ) H := by
    intro b
    have hKq : CFSG.Assembly.IsQuasisimple ((S b).map ψ) := by
      refine (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_map (hSq b) ψ fun hle => ?_)
      obtain ⟨a, a', haa⟩ := exists_mul_ne_of_isQuasisimple (hSq b)
      exact haa (Subtype.ext (Subgroup.mem_center_iff.mp (hker (hle a.2)) a').symm)
    have hnormal : (((S b).map ψ).subgroupOf (C₀.map ψ)).Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨c, hc, hcg⟩ := g.2
      refine ⟨c * s * c⁻¹, hSn b c hc s hs, ?_⟩
      simp only [map_mul, map_inv, hsx, hcg, Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨(Subgroup.map_mono (hSC b)).trans hC₀H,
      IsSubnormal.step (Subgroup.map_mono (hSC b)) hnormal
        (IsSubnormal.step hC₀H hnorm (IsSubnormal.refl H)), hKq⟩
  have hÑlayer : Ñ.map ψ ≤ LargeEvenLayer H := by
    rw [hÑ, Subgroup.map_iSup]
    exact iSup_le fun b => le_sSup (hcomp b)
  obtain ⟨k, hk⟩ := hder
  have hperf : ∀ X : Subgroup G, X ≤ H → ⁅X, X⁆ = X → X ≤ Ñ.map ψ := by
    intro X hXH hX
    calc X = ggDer X (k + 1) := (ggDer_of_perfect hX _).symm
      _ ≤ ggDer H (k + 1) := ggDer_mono hXH _
      _ = ggDer ⁅H, H⁆ k := ggDer_succ' H k
      _ ≤ ggDer (C₀.map ψ) k := ggDer_mono hcomm k
      _ = (ggDer C₀ k).map ψ := (map_ggDer ψ C₀ k).symm
      _ ≤ Ñ.map ψ := Subgroup.map_mono hk
  have hlayer : LargeEvenLayer H = Ñ.map ψ := by
    refine le_antisymm (sSup_le fun K hK => hperf K hK.1 ?_) hÑlayer
    exact ggCommutator_eq_of_isQuasisimple
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK.2.2)
  refine ⟨hlayer, ?_, fun X hXH hX => (hperf X hXH hX).trans hlayer.ge⟩
  rw [hlayer]
  have hÑperf : ⁅Ñ, Ñ⁆ = Ñ := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun _ hg _ hh =>
      Ñ.mul_mem (Ñ.mul_mem (Ñ.mul_mem hg hh) (Ñ.inv_mem hg)) (Ñ.inv_mem hh))
      (iSup_le fun b => ?_)
    rw [← ggCommutator_eq_of_isQuasisimple (hSq b)]
    exact Subgroup.commutator_mono (le_iSup S b) (le_iSup S b)
  have hZodd : Odd (Nat.card (Subgroup.center ↥Ñ)) := by
    refine odd_card_of_forall_sq_eq_one fun z hz2 => ?_
    have h1 := hZ ((z : ↥Ñ) : L) (z : ↥Ñ).2 (fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩).symm)
      (by simpa using congrArg (fun t : Subgroup.center ↥Ñ => ((t : ↥Ñ) : L)) hz2)
    exact Subtype.ext (Subtype.ext h1)
  have hsurj := ψ.subgroupMap_surjective Ñ
  have hkerN : (ψ.subgroupMap Ñ).ker ≤ Subgroup.center ↥Ñ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : ψ (x : L) = 1 := by
      simpa using congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx1)) y)
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect (ggIsPerfect_of_commutator_eq hÑperf) _
    hsurj hkerN
  have hc2 : Subgroup.center ↥(Ñ.map ψ) = (Subgroup.center ↥Ñ).map (ψ.subgroupMap Ñ) := by
    rw [← hc, Subgroup.map_comap_eq_self_of_surjective hsurj]
  rw [hc2]
  exact Odd.of_dvd_nat hZodd (Subgroup.card_map_dvd _ _)

end LayerFacts

end CFSG.StandardType
