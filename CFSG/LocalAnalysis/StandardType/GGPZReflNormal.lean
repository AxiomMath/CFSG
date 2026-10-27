module

public import CFSG.LocalAnalysis.StandardType.GGPZReflLift
public import CFSG.LocalAnalysis.StandardType.GGPZRankTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pzn_native_isQuasisimple {Q : Type} [Group Q]
    (h : CFSG.Assembly.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hc
  have hcomm : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
    ⟨⟨fun a b => by
      by_contra hne
      exact hc ⟨a, b, hne⟩⟩⟩
  haveI hQperf : Group.IsPerfect Q := ⟨h.1⟩
  have hbot : commutator (Q ⧸ Subgroup.center Q) = ⊥ :=
    (commutator_eq_bot_iff _).mpr hcomm
  have hperf : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective (Subgroup.center Q))
  have htriv : (⊤ : Subgroup (Q ⧸ Subgroup.center Q)) = ⊥ := by
    rw [← hperf.commutator_eq_top, hbot]
  have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := (Subgroup.eq_bot_iff_forall _).mp htriv a (Subgroup.mem_top a)
    have hb : b = 1 := (Subgroup.eq_bot_iff_forall _).mp htriv b (Subgroup.mem_top b)
    rw [ha, hb]
  haveI := h.2
  exact not_subsingleton _ hsub

theorem ggAutomizer_mem_normalizer_of_fixed_reflection
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs J X : Subgroup G} {z : ↥Bs}
    (hBs : IsElemAbelian p Bs)
    (hX : LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) X)
    (hJX : J ≤ X) (hJq : CFSG.IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (hcard : p ^ 2 ≤ Nat.card ↥(Bs ⊓ J))
    {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer ⊤ Bs)
    (htr : GGIsReflection p t) (htz : t z = z) :
    t ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs)) := by
  obtain ⟨g, -, hgBs, htg⟩ := mem_ggAutomizer_iff.mp ht
  have hgz : g * (z : G) = (z : G) * g := by
    have h1 : g * (z : G) * g⁻¹ = (z : G) := by
      simpa [htz] using (htg z).symm
    calc g * (z : G) = (g * (z : G) * g⁻¹) * g := by group
      _ = (z : G) * g := by rw [h1]
  have hgCz : g ∈ Subgroup.centralizer ({(z : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgz
  have hiff : ∀ b : ↥Bs, (g * (b : G) * g⁻¹ = (b : G)) ↔ (t b = b) := by
    intro b
    constructor
    · intro hb
      exact Subtype.ext (by rw [htg b, hb])
    · intro hb
      have h1 : ((t b : ↥Bs) : G) = (b : G) := congrArg Subtype.val hb
      rwa [htg b] at h1
  have hcardfix : Nat.card {b : ↥Bs // g * (b : G) * g⁻¹ = (b : G)} =
      Nat.card {b : ↥Bs // t b = b} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have hrefl : Nat.card {b : ↥Bs // g * (b : G) * g⁻¹ = (b : G)} * p = Nat.card ↥Bs := by
    rw [hcardfix]
    exact htr.2
  have hgX : g ∈ Subgroup.normalizer (X : Set G) :=
    ggPZ_reflLift hBs hX hJX hJq hZ hcard hgCz hrefl
  have hgXinv : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hgX
  have hgBsinv : g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.inv_mem _ hgBs
  have htg_inv : ∀ b : ↥Bs, ((t⁻¹ b : ↥Bs) : G) = g⁻¹ * (b : G) * g :=
    fun b => inv_apply_of_forall htg b
  have hconj : ∀ ψ ∈ ggAutomizer X Bs, t * ψ * t⁻¹ ∈ ggAutomizer X Bs := by
    intro ψ hψ
    obtain ⟨n, hnY, hnBs, hnψ⟩ := mem_ggAutomizer_iff.mp hψ
    refine mem_ggAutomizer_iff.mpr ⟨g * n * g⁻¹, ?_, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hgX n).mp hnY
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgBs hnBs) hgBsinv
    · intro b
      simp only [MulAut.mul_apply]
      rw [htg, hnψ, inv_apply_of_forall htg]
      group
  have hinvconj : ∀ ψ ∈ ggAutomizer X Bs, t⁻¹ * ψ * t ∈ ggAutomizer X Bs := by
    intro ψ hψ
    obtain ⟨n, hnY, hnBs, hnψ⟩ := mem_ggAutomizer_iff.mp hψ
    refine mem_ggAutomizer_iff.mpr ⟨g⁻¹ * n * g, ?_, ?_, ?_⟩
    · have hmem := (Subgroup.mem_normalizer_iff.mp hgXinv n).mp hnY
      simpa only [inv_inv] using hmem
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgBsinv hnBs) hgBs
    · intro b
      simp only [MulAut.mul_apply]
      rw [htg_inv, hnψ, htg]
      group
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    exact hconj ψ hψ
  · intro hψ
    have hmem : t⁻¹ * (t * ψ * t⁻¹) * t ∈ ggAutomizer X Bs := hinvconj _ hψ
    have heq : t⁻¹ * (t * ψ * t⁻¹) * t = ψ := by group
    rwa [heq] at hmem

theorem ggPZ_reflNormal {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs}
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) {Y : Subgroup G}
    (hY : LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y) (hJY : J ≤ Y) :
    ∀ t ∈ ggPZFixRefl p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z,
      t ∈ Subgroup.normalizer (ggAutomizer Y Bs) := by
  have hrank : 2 ≤ labJ.rank := ggPZ_rank_two h
  obtain ⟨hH, _, _, _, _, _, _, _, _, hJcard, _, _, _, _⟩ := h
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hJq : CFSG.IsQuasisimple ↥J :=
    pzn_native_isQuasisimple hH.1.2.2.1.2.2.2.2.2.1.2.2
  have hcard : p ^ 2 ≤ Nat.card ↥(Bs ⊓ J) := by
    rw [hJcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hrank
  intro t ht
  obtain ⟨htA, htr, htz⟩ := ht
  have htTop : t ∈ ggAutomizer ⊤ Bs :=
    (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)) htA
  exact ggAutomizer_mem_normalizer_of_fixed_reflection hBs hY hJY hJq hZ hcard htTop htr htz

end CFSG.StandardType

end
