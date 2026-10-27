module

public import CFSG.Quasithin.Background.FFC5Exc
public import CFSG.Quasithin.Background.FFC5Res

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

section Idx

variable {V : Type} [CommGroup V]

theorem isPGroup_two_of_sq {N : Subgroup (MulAut V)} (h : ∀ n ∈ N, n ^ 2 = 1) : IsPGroup 2 ↥N := by
  intro n
  exact ⟨1, Subtype.ext (by simpa using h n n.2)⟩

theorem le_pCoreOf_of_trivial_sec [Finite V] {G N : Subgroup (MulAut V)} {X : Subgroup V}
    (hV : ∀ v : V, v ^ 2 = 1) (hNG : N ≤ G) (hGN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hX : ∀ n ∈ N, ∀ x ∈ X, n x = x) (hq : ∀ n ∈ N, ∀ v : V, n v * v⁻¹ ∈ X) :
    N ≤ pCoreOf 2 G := by
  have hsq : ∀ n ∈ N, n ^ 2 = 1 := by
    intro n hn
    ext v
    have h1 : n (n v) = n v * (n v * v⁻¹) := by
      have : n (n v) = n ((n v * v⁻¹) * v) := by congr 1; simp
      rw [this, map_mul, hX n hn _ (hq n hn v)]
      simp [mul_comm]
    have h2 : n v * (n v * v⁻¹) = v := by
      have := hV (n v * v⁻¹)
      calc n v * (n v * v⁻¹) = v * (n v * v⁻¹) ^ 2 := by
            rw [sq]; simp [mul_comm, mul_left_comm]
        _ = v := by rw [this, mul_one]
    show (n ^ 2) v = v
    rw [pow_two, MulAut.mul_apply, h1, h2]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNG ?_ (isPGroup_two_of_sq hsq)
  intro g hg
  exact Subgroup.mem_normalizer_iff.2 fun n => ⟨fun hn => by
      have := hGN g hg n hn
      simpa [mul_assoc] using this, fun hn => by
      have := hGN g⁻¹ (G.inv_mem hg) (g * n * g⁻¹) hn
      simpa [mul_assoc] using this⟩

namespace B510Data

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Data G G₁ G₂)

include h in
theorem commV_le : commV G₂ ≤ fixV G₁ := by
  refine B19.commV_le_iff.2 fun b hb v a ha => ?_
  have hw : (a : MulAut V) v * v⁻¹ ∈ commV G₁ := Subgroup.subset_closure ⟨a, ha, v, rfl⟩
  have h1 : b ((a : MulAut V) v) = (a : MulAut V) v * v⁻¹ * b v := by
    have : (a : MulAut V) v = ((a : MulAut V) v * v⁻¹) * v := by simp
    rw [this, map_mul, h.triv₁ b hb _ hw]
    simp
  have hab := congrArg (fun x : MulAut V => x v) (h.comm a ha b hb)
  simp only [MulAut.mul_apply] at hab
  show (a : MulAut V) (b v * v⁻¹) = b v * v⁻¹
  rw [map_mul, map_inv, hab, h1]
  have : (a : MulAut V) v = ((a : MulAut V) v * v⁻¹) * v := by simp
  rw [this, mul_inv, mul_assoc]
  simp [mul_comm, mul_left_comm, mul_assoc]

include h in
theorem faithful_of_idx [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 G = ⊥)
    (hidx : (commV G₁ ⊔ fixV G₁).index ≤ 2) :
    ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1 := by
  intro g hg hgv
  set X : Subgroup V := commV G₁ ⊔ fixV G₁ with hX
  set N : Subgroup (MulAut V) := G₂ ⊓ centSub (fixV G₁) with hN
  have hNG : N ≤ G := fun x hx => h.G₂_le hx.1
  have hGnorm : G₂ ≤ G := h.G₂_le
  have hGN : ∀ g' ∈ G, ∀ n ∈ N, g' * n * g'⁻¹ ∈ N := by
    intro g' hg' n hn
    refine ⟨?_, fun v hv => ?_⟩
    · have := (h.normal.conj_mem ⟨n, h.G₂_le hn.1⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn.1)
        ⟨g', hg'⟩)
      simpa [Subgroup.mem_subgroupOf] using this
    · have hv' : g'⁻¹ v ∈ fixV G₁ := (h.stab_G (G.inv_mem hg') v).2 hv
      show g' (n (g'⁻¹ v)) = v
      rw [hn.2 _ hv']
      simp
  have hXn : ∀ n ∈ N, ∀ x ∈ X, n x = x := by
    intro n hn x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul, h.triv₁ n hn.1 y hy, hn.2 z hz]
  have hq : ∀ n ∈ N, ∀ v : V, n v * v⁻¹ ∈ X := by
    intro n hn v
    by_cases hvX : v ∈ X
    · rw [hXn n hn v hvX, mul_inv_cancel]
      exact X.one_mem
    · have hidx' : X.index = 1 ∨ X.index = 2 := by
        have h0 : X.index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      rcases hidx' with h1 | h2
      · exact absurd (by rw [Subgroup.index_eq_one.1 h1]; trivial) hvX
      · rw [Subgroup.index_eq_two_iff] at h2
        obtain ⟨a, ha⟩ := h2
        have hcos : ∀ b : V, b ∉ X → b * a ∈ X := fun b hb => by
          rcases ha b with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact h1
          · exact absurd h1 hb
        have hnvX : n v ∉ X := fun hmem => hvX (by
          have h3 : n (n v) = n v := hXn n hn (n v) hmem
          have h4 : n v = v := n.injective h3
          rw [← h4]
          exact hmem)
        have h5 := X.mul_mem (hcos _ hnvX) (X.inv_mem (hcos _ hvX))
        have h6 : n v * a * (v * a)⁻¹ = n v * v⁻¹ := by
          rw [mul_inv, mul_assoc, mul_comm a, mul_assoc, inv_mul_cancel, mul_one]
        rwa [h6] at h5
  have hle : N ≤ pCoreOf 2 G := le_pCoreOf_of_trivial_sec hV hNG hGN hXn hq
  rw [hO2, le_bot_iff] at hle
  have : g ∈ N := ⟨hg, hgv⟩
  rw [hle] at this
  exact Subgroup.mem_bot.1 this

include h in
theorem toSplit (hdec : commV G₁ ⊔ fixV G₁ = ⊤) : B511Split G G₁ G₂ :=
  ⟨h.G₁_le, h.G₂_le, h.sup, h.inf, h.comm, h.triv₁, hdec⟩

include h in
theorem toFa (hf : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1) : B510Fa G G₁ G₂ :=
  ⟨h, hf⟩

end B510Data

end Idx

end FFC

end CFSG.Quasithin
