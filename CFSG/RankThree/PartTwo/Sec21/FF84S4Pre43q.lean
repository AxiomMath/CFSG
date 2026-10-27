module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43n
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43o
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43p

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}
variable {θ : ↥(Nor L) →* Perm (Fin 8)}

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem a5s_props : ∀ x ∈ a5s, x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 2 ∧ sign x = 1 := by
  unfold a5s xa xb xc xd
  decide +kernel

theorem a8d_ne_one : a8d ≠ 1 := by
  unfold a8d
  decide

theorem thG_comm {u v : G} (hu : u ∈ Nor L) (hv : v ∈ Nor L) :
    thG L θ (u * v * u⁻¹ * v⁻¹) = thG L θ u * thG L θ v * (thG L θ u)⁻¹ * (thG L θ v)⁻¹ := by
  rw [thG_mul (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv),
    thG_mul (mul_mem hu hv) (inv_mem hu), thG_mul hu hv, thG_inv hu, thG_inv hv]

theorem Pi_b (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    {K₀ : Subgroup G} (hperf : commutator ↥K₀ = ⊤)
    (hK₀b : K₀ ≤ Cen b) (hK₀b₁ : K₀ ≤ Cen b₁) (hb₂K : b₂ ∈ K₀)
    (hcard : ∀ φ : ↥K₀ →* Perm (Fin 8), φ ⟨b₂, hb₂K⟩ ≠ 1 → 60 ≤ Nat.card φ.range)
    {s : G} (hsb : s * b * s⁻¹ = b₁) (hsb₁ : s * b₁ * s⁻¹ = b) (hsb₂ : s * b₂ * s⁻¹ = b₂)
    {W : Subgroup G} (hW2 : IsPGroup 2 W) (hWb : W ≤ Cen b)
    (hWB : ∀ β ∈ B, ∀ w ∈ W, β * w * β⁻¹ ∈ W)
    (hWK : ∀ k ∈ K₀, ∀ w ∈ W, (s⁻¹ * k * s) * w * (s⁻¹ * k * s)⁻¹ ∈ W) :
    W ≤ CenS B := by
  obtain ⟨θ, hθ⟩ := exists_thM hA h
  have hs1 : s⁻¹ * b * s = b₁ := by rw [← hsb₁]; group
  have hs2 : s⁻¹ * b₁ * s = b := by rw [← hsb]; group
  have hs3 : s⁻¹ * b₂ * s = b₂ := by
    calc s⁻¹ * b₂ * s = s⁻¹ * (s * b₂ * s⁻¹) * s := by rw [hsb₂]
      _ = b₂ := by group
  have hk'b : ∀ k ∈ K₀, (s⁻¹ * k * s) * b = b * (s⁻¹ * k * s) := by
    intro k hk
    have hkb₁ : k * b₁ = b₁ * k := Subgroup.mem_centralizer_singleton_iff.1 (hK₀b₁ hk)
    rw [← hs2]
    calc s⁻¹ * k * s * (s⁻¹ * b₁ * s) = s⁻¹ * (k * b₁) * s := by group
      _ = s⁻¹ * (b₁ * k) * s := by rw [hkb₁]
      _ = s⁻¹ * b₁ * s * (s⁻¹ * k * s) := by group
  have hk'b₁ : ∀ k ∈ K₀, (s⁻¹ * k * s) * b₁ = b₁ * (s⁻¹ * k * s) := by
    intro k hk
    have hkb : k * b = b * k := Subgroup.mem_centralizer_singleton_iff.1 (hK₀b hk)
    rw [← hs1]
    calc s⁻¹ * k * s * (s⁻¹ * b * s) = s⁻¹ * (k * b) * s := by group
      _ = s⁻¹ * (b * k) * s := by rw [hkb]
      _ = s⁻¹ * b * s * (s⁻¹ * k * s) := by group
  have hk'N : ∀ k ∈ K₀, s⁻¹ * k * s ∈ Nor L := fun k hk =>
    h.hyp.hLN (Subgroup.mem_centralizer_singleton_iff.2 (hk'b k hk))
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer hb₁L
  let φ : ↥K₀ →* Perm (Fin 8) :=
    { toFun := fun k => thG L θ (s⁻¹ * (k : G) * s)
      map_one' := by
        show thG L θ (s⁻¹ * ((1 : ↥K₀) : G) * s) = 1
        rw [Subgroup.coe_one, mul_one, inv_mul_cancel]
        exact thG_one
      map_mul' := fun k₁ k₂ => by
        have e : s⁻¹ * ((k₁ * k₂ : ↥K₀) : G) * s =
            (s⁻¹ * (k₁ : G) * s) * (s⁻¹ * (k₂ : G) * s) := by
          rw [Subgroup.coe_mul]; group
        show thG L θ (s⁻¹ * ((k₁ * k₂ : ↥K₀) : G) * s) = _
        rw [e]
        exact thG_mul (hk'N _ k₁.2) (hk'N _ k₂.2) }
  have hφ : ∀ k : ↥K₀, φ k = thG L θ (s⁻¹ * (k : G) * s) := fun _ => rfl
  have hc : ∀ k : ↥K₀, φ k * a8c = a8c * φ k := by
    intro k
    rw [hφ, ← hθ.c, ← thG_mul (hk'N _ k.2) hb₁N, ← thG_mul hb₁N (hk'N _ k.2), hk'b₁ _ k.2]
  have hφb₂ : φ ⟨b₂, hb₂K⟩ = a8d := by
    rw [hφ]
    show thG L θ (s⁻¹ * b₂ * s) = a8d
    rw [hs3, hθ.d]
  have hcard' := hcard φ (by rw [hφb₂]; exact a8d_ne_one)
  have hprops := perfect_cen_c hperf φ hc
  let Qa : Subgroup (Perm (Fin 8)) := a8Kb.map (alternatingGroup (Fin 8)).subtype
  have hQa : ∀ x : Perm (Fin 8), x 0 = 0 → x 1 = 1 → x 2 = 2 → sign x = 1 → x ∈ Qa := by
    intro x h0 h1 h2 hs
    have hx : x ∈ alternatingGroup (Fin 8) := mem_alternatingGroup.2 hs
    exact ⟨⟨x, hx⟩, (mem_a8Kb_iff _).2 ⟨h0, h1, h2⟩, rfl⟩
  have hQcard : Nat.card Qa = 60 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), a8Kb_card]
  have hrle : φ.range ≤ Qa := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨h0, h1, h2, hs⟩ := hprops k
    exact hQa _ h0 h1 h2 hs
  have hreq : φ.range = Qa := Subgroup.eq_of_le_of_card_ge hrle (by rw [hQcard]; exact hcard')
  have hlist : ∀ x ∈ a5s, ∃ k : ↥K₀, φ k = x := by
    intro x hx
    obtain ⟨h0, h1, h2, hs⟩ := a5s_props x hx
    have : x ∈ φ.range := hreq ▸ hQa x h0 h1 h2 hs
    exact this
  intro u hu
  have huc : u ∈ Cen b := hWb hu
  have huN : u ∈ Nor L := h.hyp.hLN huc
  have h2el : ∀ w ∈ W, w ∈ Nor L → (thG L θ w) ^ 8 = 1 := by
    intro w hw hwN
    obtain ⟨m, hm⟩ := hW2 ⟨w, hw⟩
    have hm' : w ^ 2 ^ m = 1 := congrArg Subtype.val hm
    apply two_pow_perm8 (k := m)
    rw [← thG_pow hwN, hm']
    exact thG_one
  have hWN : ∀ w ∈ W, w ∈ Nor L := fun w hw => h.hyp.hLN (hWb hw)
  have hu8 : (thG L θ u) ^ 8 = 1 := h2el u hu huN
  have hc1 : (thG L θ u * a8c * (thG L θ u)⁻¹ * a8c⁻¹) ^ 8 = 1 := by
    have hm : u * (b₁ * u⁻¹ * b₁⁻¹) ∈ W :=
      W.mul_mem hu (hWB b₁ (mem_b₁ h) u⁻¹ (W.inv_mem hu))
    have e : u * (b₁ * u⁻¹ * b₁⁻¹) = u * b₁ * u⁻¹ * b₁⁻¹ := by group
    rw [e] at hm
    have := h2el _ hm (hWN _ hm)
    rwa [thG_comm huN hb₁N, hθ.c] at this
  have hc2 : ∀ x ∈ a5s, (thG L θ u * x * (thG L θ u)⁻¹ * x⁻¹) ^ 8 = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := hlist x hx
    have hm : u * ((s⁻¹ * (k : G) * s) * u⁻¹ * (s⁻¹ * (k : G) * s)⁻¹) ∈ W :=
      W.mul_mem hu (hWK k k.2 u⁻¹ (W.inv_mem hu))
    have e : u * ((s⁻¹ * (k : G) * s) * u⁻¹ * (s⁻¹ * (k : G) * s)⁻¹) =
        u * (s⁻¹ * (k : G) * s) * u⁻¹ * (s⁻¹ * (k : G) * s)⁻¹ := by group
    rw [e] at hm
    have := h2el _ hm (hWN _ hm)
    rwa [thG_comm huN (hk'N _ k.2), ← hφ] at this
  have hu1 : thG L θ u = 1 := kb_check _ hu8 hc1 hc2
  have huL : u ∈ CenS L := (hθ.ker u huN).1 hu1
  obtain ⟨m, hm⟩ := hW2 ⟨u, hu⟩
  have hX : u ∈ Opp 3 (Cen b) := two_elt_mem_X hA h huc huL (k := m) (congrArg Subtype.val hm)
  exact X_le_cenS_B hA h hX

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
