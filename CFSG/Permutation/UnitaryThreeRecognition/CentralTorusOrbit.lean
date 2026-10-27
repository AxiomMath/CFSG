module

public import CFSG.Permutation.UnitaryThreeRecognition.CentralTorusFix

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

omit hQ in
theorem card_stabilizer_le_swapFix [Finite G] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj2 : j * j = 1) {s : G} (hsa : s • a = b) (hsb : s • b = a)
    {x : Ω} (hx : j • x ≠ x) :
    Nat.card (stabilizer (Subgroup.centralizer ({j} : Set G)) x) ≤
      Nat.card (swapFix G a b s) := by
  classical
  have hab : a ≠ b := fun h => hb h.symm
  have hxjx : x ≠ j • x := fun h => hx h.symm
  obtain ⟨g, hgx, hgjx⟩ := htwo hxjx hab
  have hs'a : (g * j * g⁻¹) • a = b := by
    rw [mul_smul, mul_smul, show g⁻¹ • a = x by rw [inv_smul_eq_iff, hgx], hgjx]
  have hs'b : (g * j * g⁻¹) • b = a := by
    have h1 : g⁻¹ • b = j • x := by rw [inv_smul_eq_iff, hgjx]
    have : (g * j * g⁻¹) • b = g • (j • (j • x)) := by simp only [mul_smul, h1]
    rw [this, ← mul_smul j j x, hj2, one_smul, hgx]
  rw [swapFix_eq hsa hsb hs'a hs'b hcomm]
  have memC : ∀ c : G, c ∈ Subgroup.centralizer ({j} : Set G) ↔ c * j = j * c := by
    intro c
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  refine Nat.card_le_card_of_injective (fun c => ⟨g * (c : G) * g⁻¹, ?_⟩) ?_
  · have hcj : (c : G) * j = j * c := (memC c).mp c.1.property
    have hcx : (c : G) • x = x := c.property
    have hcjx : (c : G) • (j • x) = j • x := by rw [smul_smul, hcj, mul_smul, hcx]
    rw [mem_swapFix]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (g * (c : G) * g⁻¹) • a = a
      rw [mul_smul, mul_smul, show g⁻¹ • a = x by rw [inv_smul_eq_iff, hgx], hcx, hgx]
    · change (g * (c : G) * g⁻¹) • b = b
      rw [mul_smul, mul_smul, show g⁻¹ • b = j • x by rw [inv_smul_eq_iff, hgjx], hcjx, hgjx]
    · calc g * j * g⁻¹ * (g * (c : G) * g⁻¹) = g * (j * c) * g⁻¹ := by group
        _ = g * (c * j) * g⁻¹ := by rw [hcj]
        _ = g * (c : G) * g⁻¹ * (g * j * g⁻¹) := by group
  · intro c₁ c₂ h
    have h' : g * (c₁ : G) * g⁻¹ = g * (c₂ : G) * g⁻¹ := congrArg Subtype.val h
    have : (c₁ : G) = c₂ := by
      have := congrArg (fun y => g⁻¹ * y * g) h'
      simpa [mul_assoc] using this
    exact Subtype.ext (Subtype.ext this)

theorem exists_centralizer_smul_eq [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {x y : Ω} (hx : j • x ≠ x) (hy : j • y ≠ y) :
    ∃ c : G, c * j = j * c ∧ c • x = y := by
  classical
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  set C := Subgroup.centralizer ({j} : Set G) with hCdef
  have memC : ∀ c : G, c ∈ C ↔ c * j = j * c := by
    intro c
    simp only [hCdef, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  have hab : a ≠ b := fun h => hb h.symm
  have hgj : s * j = j * s := by
    have hmem : s * j * s⁻¹ ∈ pairStab G a b := conj_mem_pairStab hsa hsb hj
    have hsq' : s * j * s⁻¹ * (s * j * s⁻¹) = 1 := by
      calc s * j * s⁻¹ * (s * j * s⁻¹) = s * (j * j) * s⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    rcases hsq _ hmem hsq' with h | h
    · exfalso; apply hj1
      have := congrArg (fun z => s⁻¹ * z * s) h
      simpa [mul_assoc] using this
    · calc s * j = s * j * s⁻¹ * s := by group
        _ = j * s := by rw [h]
  have hC := hQ.card_centralizer hb hcomm hj hsa hgj
  have hZ := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  have hT := hQ.card_pairStab_eq_mul_swapFix hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd
    hd hQcard hΩcard hTcard hsa hs2
  rw [hZ, hT] at hC
  set q := p ^ f with hqdef
  have hq : 3 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  let M := {z : Ω // j • z ≠ z}
  have hMcard : Nat.card M = q * q * q - q := by
    let : Fintype Ω := Fintype.ofFinite Ω
    have h1 := Fintype.card_subtype_compl (fun z : Ω => j • z = z)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hQ.card_fixedPoints hb hj, hZ, hΩcard] at h1
    have hq3 : p ^ (3 * f) = q * q * q := by rw [hqdef, ← pow_two, ← pow_succ]; ring_nf
    rw [hq3] at h1
    change Nat.card M = _ at h1
    rw [h1]; omega
  have horbM : ∀ z ∈ orbit C x, j • z ≠ z := by
    rintro z ⟨c, rfl⟩
    change j • ((c : G) • x) ≠ (c : G) • x
    rw [smul_smul, ← (memC c).mp c.property, mul_smul]
    intro h
    apply hx
    have := congrArg ((c : G)⁻¹ • ·) h
    simpa using this
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup C x)
  rw [Nat.card_prod] at hos
  have hstab := card_stabilizer_le_swapFix hb htwo hcomm hj2 hsa hsb hx
  have hTspos : 0 < Nat.card (swapFix G a b s) := Nat.card_pos
  have horb_ge : q * q * q - q ≤ Nat.card (orbit C x) := by
    have h1 : (q * q * q - q) * Nat.card (swapFix G a b s) ≤
        Nat.card (orbit C x) * Nat.card (swapFix G a b s) := by
      calc (q * q * q - q) * Nat.card (swapFix G a b s)
          = (q + 1) * (q * ((q - 1) * Nat.card (swapFix G a b s))) := by
            have : q * q * q - q = (q + 1) * q * (q - 1) := by
              have := nat_cube_add_one_sub q (by omega)
              omega
            rw [this]; ring
        _ = Nat.card (orbit C x) * Nat.card (stabilizer C x) := by rw [← hC, hos]
        _ ≤ Nat.card (orbit C x) * Nat.card (swapFix G a b s) := Nat.mul_le_mul_left _ hstab
    exact Nat.le_of_mul_le_mul_right h1 hTspos
  by_contra hno
  push Not at hno
  have hyorb : y ∉ orbit C x := by
    rintro ⟨c, hc⟩
    exact hno c ((memC c).mp c.property) hc
  have hlt : Nat.card (orbit C x) < Nat.card M := by
    have hinj : Function.Injective (fun z : orbit C x => (⟨z.1, horbM z.1 z.2⟩ : M)) := by
      intro z₁ z₂ h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h
    have hnotsurj : ¬ Function.Surjective (fun z : orbit C x => (⟨z.1, horbM z.1 z.2⟩ : M)) := by
      intro hs
      obtain ⟨z, hz⟩ := hs ⟨y, hy⟩
      apply hyorb
      have : z.1 = y := congrArg Subtype.val hz
      rw [← this]; exact z.2
    let : Fintype (orbit C x) := Fintype.ofFinite _
    let : Fintype M := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_injective_not_surjective _ hinj hnotsurj
  omega

theorem commute_involution_of_commute [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {w : G} (hw : w ∈ swapFix G a b s) (hw1 : w ≠ 1) {u : G} (huQ : u ∈ Q)
    (hwu : w * u = u * w) : j * u = u * j := by
  classical
  by_contra hju
  have hwT : w ∈ pairStab G a b := (mem_swapFix.mp hw).1
  have hwx : w • (u • b) = u • b := (hQ.fixes_iff hb hwT huQ).mpr hwu
  have hjx : j • (u • b) ≠ u • b := fun h => hju ((hQ.fixes_iff hb hj huQ).mp h)
  apply hw1
  apply hfaith
  intro y
  by_cases hjy : j • y = y
  ·
    by_cases hya : y = a
    · rw [hya]; exact hwT.1
    · obtain ⟨z, hzQ, hz⟩ := hQ.exists_smul_eq hb hya
      have hzj : j * z = z * j := (hQ.fixes_iff hb hj hzQ).mp (by rw [hz]; exact hjy)
      have hwz : w * z = z * w := hQ.swapFix_commute_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq
        hpp hp hf hpodd hd hQcard hΩcard hTcard hsa hs2 hw (mem_centQ.mpr ⟨hzQ, hzj⟩)
      rw [← hz]
      exact (hQ.fixes_iff hb hwT hzQ).mpr hwz
  · obtain ⟨c, hcj, hcx⟩ := hQ.exists_centralizer_smul_eq hb htwo hfaith hcomm hj hj2 hj1 hsq
      hpp hp hf hpodd hd hQcard hΩcard hTcard hsa hs2 hjx hjy
    have hcw : c * w = w * c := hQ.commute_of_mem_centralizer hb htwo hfaith hcomm hj hj2 hj1
      hsq hpp hp hf hpodd hd hQcard hΩcard hTcard hsa hs2 hw hcj
    rw [← hcx, smul_smul, ← hcw, mul_smul, hwx]

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
