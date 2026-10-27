module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBNbr
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGQ2LDatum.model_mem_fixed_iff {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs X : Subgroup G} {u : G} (M : GGQ2LDatum p Bs X u) (b : ↥Bs) :
    M.model (Additive.ofMul b) ∈ ggFixedSubmodule (p := p) M.model (ggAutomizer X Bs) ↔
      (b : G) ∈ Subgroup.zpowers u := by
  rw [M.fixed_x, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h : M.model (Additive.ofMul ((⟨u, M.hx⟩ : ↥Bs) ^ c.val)) = M.model (Additive.ofMul b) := by
      rw [ofMul_pow, map_nsmul, ← hc, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    have h' : u ^ c.val = (b : G) := by
      simpa using congrArg Subtype.val (Additive.ofMul.injective (M.model.injective h))
    exact h' ▸ (Subgroup.zpowers u).pow_mem (Subgroup.mem_zpowers u) c.val
  · rintro ⟨k, hk⟩
    refine ⟨(k : ZMod p), ?_⟩
    have hb : (⟨u, M.hx⟩ : ↥Bs) ^ k = b := Subtype.ext (by simpa using hk)
    rw [Int.cast_smul_eq_zsmul, ← map_zsmul, ← ofMul_zpow, hb]

@[expose] def GGQ2LDatum.toNbrDatum {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {u : G} (M : GGQ2LDatum p Bs X u)
    (hZ : ∀ b ∈ Bs, b ∈ ggBarCentralizer p Bs X ↔ b ∈ Subgroup.zpowers u) :
    GGQ2NbrDatum p Bs X where
  Λ := M.Λ
  coxeter := M.coxeter
  cartan := M.cartan
  V := M.V
  model := M.model
  simple := M.simple
  coroot := M.coroot
  root := M.root
  isWeyl := M.isWeyl
  isCartan := M.isCartan
  pairing := M.pairing
  simple_apply := M.simple_apply
  automizer_K := M.automizer_L
  fixed_ZK := fun b => (M.model_mem_fixed_iff b).trans (hZ b b.2).symm

theorem ggBarCentralizer_nbr_iff_of_K1 {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {D J : Subgroup G} (hK1 : GGQTwoK1 p B Bs x D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    ∀ b ∈ Bs, b ∈ ggBarCentralizer p Bs K ↔ b ∈ Subgroup.zpowers y := by
  intro b hb
  refine ⟨fun h => hK1 y K hnb b hb h.2.2, fun hby => ?_⟩
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)
  have hbK : b ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.zpowers_le.mpr hyK) hby
  refine ⟨hb, Subgroup.centralizer_le_normalizer _ hbK, ?_⟩
  rw [Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hbK)]
  exact bot_le

end CFSG.StandardType

end
