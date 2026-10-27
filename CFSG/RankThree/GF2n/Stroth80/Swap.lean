module

public import CFSG.RankThree.GF2n.Stroth80.Sec25c
public import CFSG.RankThree.GF2n.Stroth80.Sec26
public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_swap' (hc : Ctx M Q Z B) :
    ∃ n : G, conjSubgroup n Q = QB B ∧ conjSubgroup n (QB B) = Q ∧ conjSubgroup n Z = B ∧
      conjSubgroup n B = Z := by
  obtain ⟨n, h1, h2⟩ := hc.exists_swap
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  rw [hQB] at h1 h2
  have hgn : g⁻¹ * n ∈ M := by
    rw [← hc.hyp.normalizer_Z.2, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, h1,
      ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hng : n * g ∈ M := by
    rw [← hc.hyp.normalizer_Z.2, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, h2]
  have hZM : ∀ m ∈ M, conjSubgroup m Z = Z := fun m hm => by
    rw [conjSubgroup_eq_self_iff, hc.hyp.normalizer_Z.1]; exact hm
  refine ⟨n, by rw [hQB]; exact h1, by rw [hQB]; exact h2, ?_, ?_⟩
  · have : conjSubgroup n Z = conjSubgroup g (conjSubgroup (g⁻¹ * n) Z) := by
      rw [← conjSubgroup_mul]; congr 1; group
    rw [this, hZM _ hgn, hg]
  · have : conjSubgroup n B = conjSubgroup (n * g) Z := by
      rw [hg, ← conjSubgroup_mul]
    rw [this, hZM _ hng]

theorem Ctx.QB_inf_M_eq (hc : Ctx M Q Z B) :
    QB B ⊓ M = QB B ⊓ Subgroup.centralizer (Z : Set G) := by
  refine le_antisymm (fun x hx => ⟨hx.1, hc.QB_inf_M_le hx⟩) fun x hx => ⟨hx.1, ?_⟩
  have hN : Subgroup.centralizer (Z : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    apply le_normalizer_of_comm
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha b hb).symm
  rw [← hc.hyp.normalizer_Z.1]
  exact hN hx.2

theorem conjSubgroup_centralizer (g : G) (S : Subgroup G) :
    conjSubgroup g (Subgroup.centralizer (S : Set G)) =
      Subgroup.centralizer ((conjSubgroup g S : Subgroup G) : Set G) := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := h (g⁻¹ * y * g) (mem_conjSubgroup.mp hy)
    have e : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    have e' : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    rw [e, e', this]
  · intro h y hy
    have hy' : g * y * g⁻¹ ∈ conjSubgroup g S := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]; exact hy
    have := h _ hy'
    have e : y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
    have e' : (g⁻¹ * x * g) * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
    rw [e, e', this]

theorem Ctx.conj_centralizer_B (hc : Ctx M Q Z B) {n : G} (h1 : conjSubgroup n Q = QB B)
    (h3 : conjSubgroup n B = Z) :
    conjSubgroup n (Q ⊓ Subgroup.centralizer (B : Set G)) =
      QB B ⊓ Subgroup.centralizer (Z : Set G) := by
  rw [conjSubgroup_inf, conjSubgroup_centralizer, h1, h3]

theorem conjSubgroup_commutator (g : G) (H K : Subgroup G) :
    conjSubgroup g ⁅H, K⁆ = ⁅conjSubgroup g H, conjSubgroup g K⁆ :=
  Subgroup.map_commutator _ _ _

theorem conjSubgroup_sup' (g : G) (A B : Subgroup G) :
    conjSubgroup g (A ⊔ B) = conjSubgroup g A ⊔ conjSubgroup g B :=
  Subgroup.map_sup _ _ _

theorem Ctx.commutator_L0 (hc : Ctx M Q Z B) {w : ℕ} (hw : Width Q Z w) (hw2 : 2 ≤ w) :
    ⁅QB B ⊓ Subgroup.centralizer (Z : Set G), QB B ⊓ Subgroup.centralizer (Z : Set G)⁆ = B := by
  obtain ⟨n, h1, -, h3, h4⟩ := hc.exists_swap'
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have := hc.commutator_centralizer_B h hw hw2
  rw [← hc.conj_centralizer_B h1 h4, ← conjSubgroup_commutator, this, h3]

theorem Ctx.mem_center_iff_L0 (hc : Ctx M Q Z B) {y : G}
    (hy : y ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) :
    (∀ s ∈ QB B ⊓ Subgroup.centralizer (Z : Set G), y * s = s * y) ↔ y ∈ Z ⊔ B := by
  obtain ⟨n, h1, h2, h3, h4⟩ := hc.exists_swap'
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hC := hc.conj_centralizer_B h1 h4
  have hmemC : ∀ s, s ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) ↔
      n⁻¹ * s * n ∈ Q ⊓ Subgroup.centralizer (B : Set G) := fun s => by
    rw [← hC, mem_conjSubgroup]
  have hy0 : n⁻¹ * y * n ∈ Q ⊓ Subgroup.centralizer (B : Set G) := (hmemC y).mp hy
  have key := hc.mem_center_iff_centralizer_B h hy0
  have hsup : y ∈ Z ⊔ B ↔ n⁻¹ * y * n ∈ Z ⊔ B := by
    have e : conjSubgroup n (Z ⊔ B) = Z ⊔ B := by
      rw [conjSubgroup_sup', h3, h4, sup_comm]
    rw [← mem_conjSubgroup (g := n), e]
  rw [hsup, ← key]
  constructor
  · intro hs x hx
    have := hs (n * x * n⁻¹) ((hmemC _).mpr (by simpa [mul_assoc] using hx))
    have e1 : n⁻¹ * y * n * x = n⁻¹ * (y * (n * x * n⁻¹)) * n := by group
    have e2 : x * (n⁻¹ * y * n) = n⁻¹ * ((n * x * n⁻¹) * y) * n := by group
    rw [e1, e2, this]
  · intro hx s hs
    have := hx (n⁻¹ * s * n) ((hmemC s).mp hs)
    have e1 : y * s = n * ((n⁻¹ * y * n) * (n⁻¹ * s * n)) * n⁻¹ := by group
    have e2 : s * y = n * ((n⁻¹ * s * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
    rw [e1, e2, this]

theorem Ctx.mem_QB_of_comm_mem (hc : Ctx M Q Z B) {x : G}
    (hx : x ∈ Subgroup.normalizer (B : Set G)) (h : ∀ y ∈ QB B, ⁅x, y⁆ ∈ B) : x ∈ QB B := by
  obtain ⟨n, h1, -, h3, -⟩ := hc.exists_swap'
  have hx0 : n⁻¹ * x * n ∈ M := by
    rw [← hc.hyp.normalizer_Z.1, ← mem_normalizer_conj_iff, h3]; exact hx
  have := hc.hyp.centralizer_Qt _ hx0 (fun y₀ hy₀ => by
    have hy : n * y₀ * n⁻¹ ∈ QB B := by
      rw [← h1, mem_conjSubgroup]
      simpa [mul_assoc] using hy₀
    have hb := h _ hy
    rw [← h3, mem_conjSubgroup] at hb
    have e : n⁻¹ * ⁅x, n * y₀ * n⁻¹⁆ * n = ⁅n⁻¹ * x * n, y₀⁆ := by
      simp only [commutatorElement_def]; group
    rwa [e] at hb)
  rw [← h1]
  have e : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [e]
  exact ⟨_, this, rfl⟩

theorem IsA2.conj {Q Z : Subgroup G} {a : G} (h : IsA2 Q Z a) (g : G) :
    IsA2 (conjSubgroup g Q) (conjSubgroup g Z) (g * a * g⁻¹) := by
  obtain ⟨hn, haQ, ha2, hcard, hel⟩ := h
  have hcomm : conjSubgroup g ⁅Q, Subgroup.zpowers a⁆ =
      ⁅conjSubgroup g Q, Subgroup.zpowers (g * a * g⁻¹)⁆ := by
    rw [conjSubgroup_commutator]
    congr 1
    show Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.zpowers a) = _
    rw [MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_normalizer_conj_iff]
    simpa [mul_assoc] using hn
  · intro h
    apply haQ
    have := mem_conjSubgroup.mp h
    simpa [mul_assoc] using this
  · rw [mem_conjSubgroup, show g⁻¹ * (g * a * g⁻¹) ^ 2 * g = a ^ 2 by rw [pow_two, pow_two]; group]
    exact ha2
  · rw [← hcomm, ← conjSubgroup_sup', card_conjSubgroup, card_conjSubgroup]
    exact hcard
  · rw [← hcomm]
    exact CFSG.Open.IsElemAbelian.map hel (MulAut.conj g).toMonoidHom

end CFSG.RankThree.GF2n.Stroth80
