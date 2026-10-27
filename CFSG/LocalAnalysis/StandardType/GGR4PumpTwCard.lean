module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

open scoped Pointwise

theorem ggPumpTw_center_bot (hZ : GGCentreTrivialTwKnown) {G : Type} [Group G] [Finite G]
    {J : Subgroup G} {f : ℕ} (hf : 1 ≤ f) (hJlab : GGPumpTwJLab f (J ⧸ Subgroup.center J))
    (hJq : CFSG.Assembly.IsQuasisimple J) : Subgroup.center J = ⊥ := by
  have key : ∀ lab : LargeEvenLabel, GGHasLabel lab (J ⧸ Subgroup.center J) →
      LargeEvenLabelAll lab (fun R _ _ _ => ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
        Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          Subgroup.center L' = ⊥) → Subgroup.center J = ⊥ := by
    intro lab hlab hall
    obtain ⟨R, _, I, F, ⟨⟨e⟩, hP⟩⟩ := largeEvenRawDatum_exists (hall _ hlab)
    let ψ : ↥J →* R := (e : (↥J ⧸ Subgroup.center ↥J) →* R).comp
      (QuotientGroup.mk' (Subgroup.center ↥J))
    have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψk : ψ.ker ≤ Subgroup.center ↥J := by
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥J)) y = 1 := by
        apply e.injective
        rw [map_one]
        exact hy
      exact (QuotientGroup.eq_one_iff y).mp h1
    exact hP ↥J ψ hψs hψk hJq.1
  rcases hJlab with ⟨h3, hl⟩ | ⟨h3, hl⟩ | hl
  · exact key _ hl ((hZ f hf).1 h3)
  · exact key _ hl ((hZ f hf).2.1 h3)
  · exact key _ hl (hZ f hf).2.2

theorem ggPumpTw_card_ge_four (hZ : GGCentreTrivialTwKnown) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs X J : Subgroup G} {x : G} {f : ℕ} (hf : 1 ≤ f)
    (hJlab : GGPumpTwJLab f (J ⧸ Subgroup.center J)) (hJq : CFSG.Assembly.IsQuasisimple J)
    (hJX : J ≤ X) (hJx : J ≤ Subgroup.centralizer ({x} : Set G)) (hBsEA : IsElemAbelian p Bs)
    (hxk : ∃ k ∈ Bs ⊓ X, ∀ l ∈ X, x * l * x⁻¹ = k * l * k⁻¹)
    (hnot : ¬ (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X)
    (hEJ : 3 ≤ Nat.log p (Nat.card ↥(Bs ⊓ J))) : p ^ 4 ≤ Nat.card ↥(Bs ⊓ X) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hkBX, hkx⟩ := hxk
  have hkBs : k ∈ Bs := hkBX.1
  have hZJ : Subgroup.center J = ⊥ := ggPumpTw_center_bot hZ hf hJlab hJq
  have hk1 : k ≠ 1 := by
    intro hk
    apply hnot
    have hxC : x ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := hkx l hl
      rw [hk, one_mul, inv_one, mul_one] at h
      calc l * x = (x * l * x⁻¹) * x := by rw [h]
        _ = x * l := by group
    have hcomm : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      exact Subgroup.zpowers_le.mpr hxC
    rw [hcomm]
    exact bot_le
  have hkJ : ∀ j ∈ J, k * j = j * k := by
    intro j hj
    have h1 : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.mp (hJx hj)
    have h2 := hkx j (hJX hj)
    have h3 : x * j * x⁻¹ = j := by
      calc x * j * x⁻¹ = (j * x) * x⁻¹ := by rw [h1]
        _ = j := by group
    rw [h3] at h2
    calc k * j = (k * j * k⁻¹) * k := by group
      _ = j * k := by rw [← h2]
  have hkJ' : k ∉ J := by
    intro hkJmem
    have hc : (⟨k, hkJmem⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hkJ g.1 g.2).symm
    rw [hZJ, Subgroup.mem_bot] at hc
    exact hk1 (congrArg Subtype.val hc)
  have hkp : k ^ p = 1 := hBsEA.2 k hkBs
  have hord : orderOf k = p := orderOf_eq_prime hkp hk1
  have hdisj : Disjoint (Bs ⊓ J) (Subgroup.zpowers k) := by
    rw [Subgroup.disjoint_def]
    intro y hy1 hy2
    by_contra hne
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy2
    have hyp : (k ^ i) ^ p = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hkp, one_zpow]
    have hyo : orderOf (k ^ i) = p := orderOf_eq_prime hyp hne
    have hle : Subgroup.zpowers (k ^ i) ≤ Subgroup.zpowers k :=
      Subgroup.zpowers_le.mpr (Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) i)
    have heq : Subgroup.zpowers (k ^ i) = Subgroup.zpowers k := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hord]
    have hkmem : k ∈ Subgroup.zpowers (k ^ i) := by rw [heq]; exact Subgroup.mem_zpowers k
    exact hkJ' (Subgroup.zpowers_le.mpr hy1.2 hkmem)
  have hnormK : Subgroup.zpowers k ≤ Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((Bs ⊓ J : Subgroup G) : Set G))
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (hkJ j hj.2).symm
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (Bs ⊓ J)
    (Subgroup.zpowers k) hnormK hdisj
  have hsub : (Bs ⊓ J) ⊔ Subgroup.zpowers k ≤ Bs ⊓ X :=
    sup_le (inf_le_inf_left Bs hJX) (Subgroup.zpowers_le.mpr hkBX)
  have hle := Subgroup.card_le_of_le hsub
  rw [hcard, Nat.card_zpowers, hord] at hle
  have hp3J : p ^ 3 ≤ Nat.card ↥(Bs ⊓ J) := by
    have hne : Nat.card ↥(Bs ⊓ J) ≠ 0 := by
      intro h0
      have : Nat.log p (Nat.card ↥(Bs ⊓ J)) = 0 := by rw [h0, Nat.log_of_lt hp.pos]
      omega
    exact le_trans (Nat.pow_le_pow_right hp.pos hEJ) (Nat.pow_log_le_self p hne)
  calc p ^ 4 = p ^ 3 * p := by ring
    _ ≤ Nat.card ↥(Bs ⊓ J) * p := Nat.mul_le_mul_right p hp3J
    _ ≤ Nat.card ↥(Bs ⊓ X) := hle

end CFSG.StandardType

end
