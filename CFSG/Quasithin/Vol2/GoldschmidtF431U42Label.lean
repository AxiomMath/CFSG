module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Norm
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

theorem xY_mem_P1 : xY ∈ P1 := B0_le_P1 (T_le_B0 xY_mem_T)

theorem tY_mem_P2 : tY ∈ P2 := B0_le_P2 (T_le_B0 tY_mem_T)

theorem eq_xY_of_central_involution
    {g : Y} (hg : g ∈ B0) (hc : ∀ b ∈ B0, b * g = g * b) (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    g = xY := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have hp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hT : g ∈ T := le_T_of_le_B0 ((Subgroup.zpowers_le).2 hg) hp (Subgroup.mem_zpowers g)
  exact (center_T_spec hT fun s hs => hc s (T_le_B0 hs)).resolve_left hg1

theorem label_central
    {G : Type} [Group G] {M₁ M₂ : Subgroup G} {A B : Subgroup Y} (hAB : A ⊓ B = B0)
    (f : ↥(M₁ ⊓ M₂) ≃* ↥(A ⊓ B))
    {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : z ∈ centerOf (M₁ ⊓ M₂)) :
    ((f ⟨z, hzc.1⟩ : ↥(A ⊓ B)) : Y) = xY := by
  set z₀ : ↥(M₁ ⊓ M₂) := ⟨z, hzc.1⟩ with hz₀
  have hmem : ((f z₀ : ↥(A ⊓ B)) : Y) ∈ B0 := hAB ▸ (f z₀).2
  refine eq_xY_of_central_involution hmem (fun b hb => ?_) ?_ ?_
  · have hb' : b ∈ A ⊓ B := hAB ▸ hb
    set b' : ↥(A ⊓ B) := ⟨b, hb'⟩
    obtain ⟨u, hu⟩ : ∃ u : ↥(M₁ ⊓ M₂), f u = b' := ⟨f.symm b', by simp⟩
    have hcomm : (u : G) * z = z * (u : G) := (Subgroup.mem_centralizer_iff.1 hzc.2) (u : G) u.2
    have hcomm' : u * z₀ = z₀ * u := Subtype.ext hcomm
    have := congrArg (fun w => ((f w : ↥(A ⊓ B)) : Y)) hcomm'
    simpa [hu, b'] using this
  · have h : z₀ * z₀ = 1 := Subtype.ext (by rw [← pow_two]; exact hz2)
    have := congrArg (fun w => ((f w : ↥(A ⊓ B)) : Y)) h
    simpa using this
  · intro h
    apply hz1
    have h1 : f z₀ = 1 := Subtype.ext h
    have h2 : z₀ = 1 := f.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2

theorem label_phi1
    {G : Type} [Group G] {M₁ M₂ : Subgroup G} (f1 : ↥M₁ ≃* ↥P1) (f12 : ↥(M₁ ⊓ M₂) ≃* ↥(P1 ⊓ P2))
    (c1 : ∀ g : ↥(M₁ ⊓ M₂), (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1) (f12 g) : ↥P1) =
      f1 (Subgroup.inclusion (inf_le_left : M₁ ⊓ M₂ ≤ M₁) g))
    {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : z ∈ centerOf (M₁ ⊓ M₂)) :
    ((f1 ⟨z, hzc.1.1⟩ : ↥P1) : Y) = xY := by
  have h := congrArg Subtype.val (c1 ⟨z, hzc.1⟩)
  exact h.symm.trans (label_central (A := P1) (B := P2) rfl f12 hz2 hz1 hzc)

theorem not_swapped
    {G : Type} [Group G] {M₁ M₂ : Subgroup G}
    (iso : (RankTwoAmalgam.ofSubgroups M₁ M₂).Iso (RankTwoAmalgam.ofSubgroups P2 P1))
    {z : G} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : z ∈ centerOf (M₁ ⊓ M₂))
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ M₁) : False := by
  let f12 : ↥(M₁ ⊓ M₂) ≃* ↥(P2 ⊓ P1) := iso.φ12
  let f2 : ↥M₂ ≃* ↥P1 := iso.φ2
  have c2 : ∀ g : ↥(M₁ ⊓ M₂), (Subgroup.inclusion (inf_le_right : P2 ⊓ P1 ≤ P1) (f12 g) : ↥P1) =
      f2 (Subgroup.inclusion (inf_le_right : M₁ ⊓ M₂ ≤ M₂) g) := iso.comm2
  have hz : ((f12 ⟨z, hzc.1⟩ : ↥(P2 ⊓ P1)) : Y) = xY :=
    label_central (A := P2) (B := P1) (by rw [inf_comm]; rfl) f12 hz2 hz1 hzc
  have hz' : ((f2 ⟨z, hzc.1.2⟩ : ↥P1) : Y) = xY :=
    (congrArg Subtype.val (c2 ⟨z, hzc.1⟩)).symm.trans hz
  have hle : M₂ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    set a : ↥P1 := f2 ⟨m, hm⟩
    set b : ↥P1 := f2 ⟨z, hzc.1.2⟩
    have ha : (a : Y) ∈ Subgroup.centralizer ({xY} : Set Y) := by
      rw [centralizer_x]
      exact a.2
    have hab : (b : Y) * (a : Y) = (a : Y) * (b : Y) := by
      rw [hz']
      exact (Subgroup.mem_centralizer_singleton_iff.1 ha).symm
    have h2 : f2 (⟨z, hzc.1.2⟩ * ⟨m, hm⟩) = f2 (⟨m, hm⟩ * ⟨z, hzc.1.2⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hab
    exact (congrArg Subtype.val (f2.injective h2)).symm
  have hM : M₁ ⊓ M₂ = M₂ := inf_eq_right.2 (hle.trans hcz)
  have h1 : Nat.card ↥(M₁ ⊓ M₂) = Nat.card ↥(P2 ⊓ P1) := Nat.card_congr f12.toEquiv
  have h2 : Nat.card ↥M₂ = Nat.card ↥P1 := Nat.card_congr f2.toEquiv
  rw [hM, h2, inf_comm, show P1 ⊓ P2 = B0 from rfl, card_P1, card_B0] at h1
  omega

end CFSG.Quasithin.H13.F431.U42
