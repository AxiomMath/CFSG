module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43m
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43q
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43r

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

theorem S43_tstarCen₁_holds :
    S43_TstarCen₁ := by
  intro G _ _ b L B K b₁ b₂ h V hV _hVne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : A8Model L := a8Model_of_hyp h.hyp
  obtain ⟨s, hsN, hsb, hsb₁, hsb₂⟩ := h.mono.2.2.2.2.1
  have hs2 : s⁻¹ * b₁ * s = b := by rw [← hsb]; group
  have hKL : K ≤ L := fun x hx => by
    have : x ∈ L ⊓ Cen b₁ := by rw [← h.hK.2.2.1]; exact Subgroup.mem_sup_right hx
    exact (Subgroup.mem_inf.1 this).1
  have hK₀K : (⁅K, K⁆ : Subgroup G) ≤ K := commutator_le_self
  have hKb₁ : ∀ x ∈ K, x * b₁ = b₁ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (h.hK.2.2.2.2 hx)
  have hK₀b : (⁅K, K⁆ : Subgroup G) ≤ Cen b := fun x hx => h.hyp.hLC (hKL (hK₀K hx))
  have hK₀b₁ : (⁅K, K⁆ : Subgroup G) ≤ Cen b₁ := fun x hx => h.hK.2.2.2.2 (hK₀K hx)
  have hb₂K₀ : b₂ ∈ (⁅K, K⁆ : Subgroup G) := b₂_mem_commutator hA h
  have hXL : Opp 3 (Cen b) ≤ CenS L := X_le_cenS_L h.hyp hA
  have hVL : ∀ l ∈ L, ∀ y ∈ V, l * y * l⁻¹ = y := by
    intro l hl y hy
    rw [Subgroup.mem_centralizer_iff.1 (hXL (hV.1 hy)) l hl]
    group
  have hLN : ∀ l ∈ L, l ∈ Nor V := fun l hl =>
    FF79.L41.mem_nor_of_forall (fun y hy => by rw [hVL l hl y hy]; exact hy)
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = Op 2 (Nor V) ⊓ Cen b₁ := ⟨_, rfl⟩
  have hWmem : ∀ z, z ∈ W ↔ z ∈ Op 2 (Nor V) ∧ z ∈ Cen b₁ := fun z => by
    rw [hWdef]; exact Subgroup.mem_inf
  have hconj : ∀ g w : G, g * b₁ = b₁ * g → w * b₁ = b₁ * w →
      g * w * g⁻¹ * b₁ = b₁ * (g * w * g⁻¹) := by
    intro g w hg hw
    have hg' : g⁻¹ * b₁ = b₁ * g⁻¹ := ((show Commute g b₁ from hg).inv_left).eq
    calc g * w * g⁻¹ * b₁ = g * w * (g⁻¹ * b₁) := by group
      _ = g * w * (b₁ * g⁻¹) := by rw [hg']
      _ = g * (w * b₁) * g⁻¹ := by group
      _ = g * (b₁ * w) * g⁻¹ := by rw [hw]
      _ = (g * b₁) * w * g⁻¹ := by group
      _ = (b₁ * g) * w * g⁻¹ := by rw [hg]
      _ = b₁ * (g * w * g⁻¹) := by group
  have hWB : ∀ β ∈ B, ∀ w ∈ W, β * w * β⁻¹ ∈ W := by
    intro β hβ w hw
    obtain ⟨hwT, hwc⟩ := (hWmem w).1 hw
    refine (hWmem _).2 ⟨Tstar_B_inv hA h hV w hwT β hβ, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hconj β w (comm_of_mem h hβ (mem_b₁ h)).eq (Subgroup.mem_centralizer_singleton_iff.1 hwc))
  have hWK : ∀ k ∈ (⁅K, K⁆ : Subgroup G), ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
    intro k hk w hw
    obtain ⟨hwT, hwc⟩ := (hWmem w).1 hw
    refine (hWmem _).2 ⟨FF79.L41.Op_conj_mem (hLN k (hKL (hK₀K hk))) hwT, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hconj k w (hKb₁ k (hK₀K hk)) (Subgroup.mem_centralizer_singleton_iff.1 hwc))
  have hW2 : IsPGroup 2 W := by
    rw [hWdef]
    exact (FF79.L41.Op_isPGroup _).to_le inf_le_left
  obtain ⟨W', hW'def⟩ : ∃ W' : Subgroup G, W' = W.comap (MulAut.conj s).toMonoidHom := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ W' ↔ s * g * s⁻¹ ∈ W := fun g => by
    rw [hW'def, Subgroup.mem_comap]
    exact Iff.rfl
  have hW'2 : IsPGroup 2 W' := fun g => by
    obtain ⟨k, hk⟩ := hW2 ⟨s * (g : G) * s⁻¹, (hmem _).1 g.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h3 : s * (g : G) ^ 2 ^ k * s⁻¹ = 1 := by
      rw [← conj_pow]
      exact congrArg Subtype.val hk
    show (g : G) ^ 2 ^ k = 1
    calc (g : G) ^ 2 ^ k = s⁻¹ * (s * (g : G) ^ 2 ^ k * s⁻¹) * s := by group
      _ = 1 := by rw [h3]; group
  have hW'b : W' ≤ Cen b := by
    intro g hg
    have hg' := ((hWmem _).1 ((hmem g).1 hg)).2
    have hc : s * g * s⁻¹ * b₁ = b₁ * (s * g * s⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 hg'
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [← hs2]
    calc g * (s⁻¹ * b₁ * s) = s⁻¹ * (s * g * s⁻¹ * b₁) * s := by group
      _ = s⁻¹ * (b₁ * (s * g * s⁻¹)) * s := by rw [hc]
      _ = s⁻¹ * b₁ * s * g := by group
  have hW'B : ∀ β ∈ B, ∀ w ∈ W', β * w * β⁻¹ ∈ W' := by
    intro β hβ w hw
    rw [hmem] at hw ⊢
    have hβ' : s * β * s⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hsN β).1 hβ
    have e : s * (β * w * β⁻¹) * s⁻¹ = (s * β * s⁻¹) * (s * w * s⁻¹) * (s * β * s⁻¹)⁻¹ := by group
    rw [e]
    exact hWB _ hβ' _ hw
  have hW'K : ∀ k ∈ (⁅K, K⁆ : Subgroup G), ∀ w ∈ W',
      (s⁻¹ * k * s) * w * (s⁻¹ * k * s)⁻¹ ∈ W' := by
    intro k hk w hw
    rw [hmem] at hw ⊢
    have e : s * ((s⁻¹ * k * s) * w * (s⁻¹ * k * s)⁻¹) * s⁻¹ = k * (s * w * s⁻¹) * k⁻¹ := by
      group
    rw [e]
    exact hWK k hk _ hw
  have hWc : W' ≤ CenS B :=
    Pi_b hA h (derived_perfect h.hK.2.1) hK₀b hK₀b₁ hb₂K₀
      (fun φ hφ => derived_card h.hK.2.1 φ _ hφ) hsb hsb₁ hsb₂ hW'2 hW'b hW'B hW'K
  intro z hz
  obtain ⟨hzT, hzb₁⟩ := hz
  have hzW : z ∈ W := (hWmem z).2 ⟨hzT, hzb₁⟩
  have hz' : s⁻¹ * z * s ∈ W' := by
    rw [hmem]
    have : s * (s⁻¹ * z * s) * s⁻¹ = z := by group
    rw [this]
    exact hzW
  have hc : b₁ * (s⁻¹ * z * s) = (s⁻¹ * z * s) * b₁ :=
    Subgroup.mem_centralizer_iff.1 (hWc hz') b₁ (mem_b₁ h)
  have hzb : z * b = b * z := by
    rw [← hsb₁]
    calc z * (s * b₁ * s⁻¹) = s * ((s⁻¹ * z * s) * b₁) * s⁻¹ := by group
      _ = s * (b₁ * (s⁻¹ * z * s)) * s⁻¹ := by rw [← hc]
      _ = s * b₁ * s⁻¹ * z := by group
  exact tstar_cen_b hA h hV ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 hzb⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
