module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.GroupTheory.CentralizerSup

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggAutomizer_conj_mem_or_commute {Bs K : Subgroup G} {y : G} (hy : y ∈ Bs)
    (hK : IsComponentOf K (Subgroup.centralizer ({y} : Set G))) {ψ : MulAut ↥Bs}
    (hψ : ψ ∈ ggAutomizer ⊤ Bs) (hψy : ψ ⟨y, hy⟩ = ⟨y, hy⟩) :
    (∀ a ∈ ggAutomizer K Bs, ψ * a * ψ⁻¹ ∈ ggAutomizer K Bs) ∨
      ∀ a ∈ ggAutomizer K Bs, ∀ b ∈ ggAutomizer K Bs,
        a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a := by
  obtain ⟨g, -, hgN, hψg⟩ := mem_ggAutomizer_iff.mp hψ
  have hgy : g * y * g⁻¹ = y := by
    have h1 : g * (⟨y, hy⟩ : ↥Bs) * g⁻¹ = (⟨y, hy⟩ : ↥Bs) := by
      rw [← hψg (⟨y, hy⟩ : ↥Bs), hψy]
    simpa using h1
  have hgC : g ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hgy' : g * y = y * g := by
      calc g * y = g * y * g⁻¹ * g := by group
        _ = y * g := by rw [hgy]
    exact hgy'.symm
  let K' := K.map (MulAut.conj g).toMonoidHom
  have hmap : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgC)
  have hK' : IsComponentOf K' (Subgroup.centralizer ({y} : Set G)) := by
    change IsComponentOf (K.map (MulAut.conj g).toMonoidHom) (Subgroup.centralizer ({y} : Set G))
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK g
    rwa [hmap] at h
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK hK' with h | h
  · left
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change K' = K
      exact h.symm
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rw [ggInduced] at ha
      obtain ⟨k, hkK, hkN, hak⟩ := ha
      refine mem_ggAutomizer_iff.mpr ⟨g * k * g⁻¹, ?_, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hgK k).mp hkK
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hkN) (Subgroup.inv_mem _ hgN)
      · intro b
        rw [MulAut.mul_apply, MulAut.mul_apply, hψg, hak, inv_apply_of_forall hψg]
        group
    | one => simp
    | mul a b ha hb iha ihb =>
      have h1 : ψ * (a * b) * ψ⁻¹ = (ψ * a * ψ⁻¹) * (ψ * b * ψ⁻¹) := by group
      rw [h1]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      have h1 : ψ * a⁻¹ * ψ⁻¹ = (ψ * a * ψ⁻¹)⁻¹ := by group
      rw [h1]
      exact Subgroup.inv_mem _ iha
  · right
    intro a ha b hb
    have hcommKK' : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
      intro k hk k' hk'
      have hle : K ≤ Subgroup.centralizer (K' : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact (Subgroup.mem_centralizer_iff.mp (hle hk) k' hk').symm
    refine Subgroup.closure_induction₂
      (p := fun x y _ _ => x * (ψ * y * ψ⁻¹) = ψ * y * ψ⁻¹ * x)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
    · rintro x y hx hy
      rw [ggInduced] at hx hy
      obtain ⟨k, hkK, hkN, hak⟩ := hx
      obtain ⟨k', hk'K, hk'N, hk'⟩ := hy
      have hgk'K' : g * k' * g⁻¹ ∈ K' := by
        rw [Subgroup.mem_map]
        exact ⟨k', hk'K, rfl⟩
      have hcomm : k * (g * k' * g⁻¹) = (g * k' * g⁻¹) * k :=
        hcommKK' k hkK _ hgk'K'
      have hcomm_inv : (g * k' * g⁻¹)⁻¹ * k⁻¹ = k⁻¹ * (g * k' * g⁻¹)⁻¹ := by
        simpa [mul_inv_rev] using congrArg Inv.inv hcomm
      ext x
      simp only [MulAut.mul_apply, hak, hψg, hk', inv_apply_of_forall hψg]
      calc k * (g * (k' * (g⁻¹ * x * g) * k'⁻¹) * g⁻¹) * k⁻¹
          = (k * (g * k' * g⁻¹)) * x * ((g * k' * g⁻¹)⁻¹ * k⁻¹) := by group
        _ = ((g * k' * g⁻¹) * k) * x * (k⁻¹ * (g * k' * g⁻¹)⁻¹) := by
          rw [hcomm, hcomm_inv]
        _ = g * (k' * (g⁻¹ * (k * x * k⁻¹) * g) * k'⁻¹) * g⁻¹ := by group
    · intro x hx
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz ihx ihy
      calc (x * y) * (ψ * z * ψ⁻¹)
          = x * (y * (ψ * z * ψ⁻¹)) := by group
        _ = x * ((ψ * z * ψ⁻¹) * y) := by rw [ihy]
        _ = (x * (ψ * z * ψ⁻¹)) * y := by group
        _ = ((ψ * z * ψ⁻¹) * x) * y := by rw [ihx]
        _ = (ψ * z * ψ⁻¹) * (x * y) := by group
    · intro y z x hy hz hx ihy ihz
      have h1 : ψ * (y * z) * ψ⁻¹ = (ψ * y * ψ⁻¹) * (ψ * z * ψ⁻¹) := by group
      rw [h1]
      calc x * ((ψ * y * ψ⁻¹) * (ψ * z * ψ⁻¹))
          = (x * (ψ * y * ψ⁻¹)) * (ψ * z * ψ⁻¹) := by group
        _ = ((ψ * y * ψ⁻¹) * x) * (ψ * z * ψ⁻¹) := by rw [ihy]
        _ = (ψ * y * ψ⁻¹) * (x * (ψ * z * ψ⁻¹)) := by group
        _ = (ψ * y * ψ⁻¹) * ((ψ * z * ψ⁻¹) * x) := by rw [ihz]
        _ = (ψ * y * ψ⁻¹) * (ψ * z * ψ⁻¹) * x := by group
    · intro x y hx hy ih
      calc x⁻¹ * (ψ * y * ψ⁻¹)
          = x⁻¹ * ((ψ * y * ψ⁻¹) * x * x⁻¹) := by group
        _ = x⁻¹ * (x * (ψ * y * ψ⁻¹) * x⁻¹) := by rw [← ih]
        _ = (ψ * y * ψ⁻¹) * x⁻¹ := by group
    · intro x y hx hy ih
      have h1 : ψ * y⁻¹ * ψ⁻¹ = (ψ * y * ψ⁻¹)⁻¹ := by group
      rw [h1]
      calc x * (ψ * y * ψ⁻¹)⁻¹
          = (ψ * y * ψ⁻¹)⁻¹ * ((ψ * y * ψ⁻¹) * x * (ψ * y * ψ⁻¹)⁻¹) := by group
        _ = (ψ * y * ψ⁻¹)⁻¹ * (x * (ψ * y * ψ⁻¹) * (ψ * y * ψ⁻¹)⁻¹) := by rw [ih]
        _ = (ψ * y * ψ⁻¹)⁻¹ * x := by group

theorem GGNbr.eq_of_mem_zpowers (hLB : GGLBalanceInput) {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (hI : GGThmIHyp p B x L) (hDJ : LargeEvenStdSub p B x L D J)
    (hpJ : p ∣ Nat.card J) {y₁ y₂ : G} {K₁ K₂ : Subgroup G} (h₁ : GGNbr p B x D J y₁ K₁)
    (h₂ : GGNbr p B x D J y₂ K₂) (hy : y₂ ∈ Subgroup.zpowers y₁) : K₁ = K₂ := by
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hy₁B : y₁ ∈ B := h₁.1.2.1
  have hy₁ne : y₁ ≠ 1 := h₁.1.2.2.1
  have hy₁p : y₁ ^ p = 1 := hS.1.1.2 y₁ hy₁B
  have hord₁ : orderOf y₁ = p := orderOf_eq_prime hy₁p hy₁ne
  have hy₂ne : y₂ ≠ 1 := h₂.1.2.2.1
  have hy₂dvd : orderOf y₂ ∣ p := by
    have hle : Subgroup.zpowers y₂ ≤ Subgroup.zpowers y₁ := Subgroup.zpowers_le.mpr hy
    have hcard := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, Nat.card_zpowers, hord₁] at hcard
  have hord₂ : orderOf y₂ = p := by
    rcases (Nat.dvd_prime hp).mp hy₂dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy₂ne
    · exact h
  have hzp : Subgroup.zpowers y₂ = Subgroup.zpowers y₁ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hord₁, hord₂]
  have hcen : Subgroup.centralizer ({y₂} : Set G) = Subgroup.centralizer ({y₁} : Set G) := by
    calc Subgroup.centralizer ({y₂} : Set G)
        = Subgroup.centralizer (Subgroup.zpowers y₂ : Set G) := by
          rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
      _ = Subgroup.centralizer (Subgroup.zpowers y₁ : Set G) := by rw [hzp]
      _ = Subgroup.centralizer ({y₁} : Set G) := by
          rw [CFSG.centralizer_zpowers_eq_centralizer_singleton]
  have hK₁ : IsComponentOf K₁ (Subgroup.centralizer ({y₂} : Set G)) := by
    rw [hcen]
    exact (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ h₁)).1
  have hK₂ : IsComponentOf K₂ (Subgroup.centralizer ({y₂} : Set G)) :=
    (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ h₂)).1
  have hJ₁ : J ≤ K₁ := le_of_ggNbr hLB hI hDJ hpJ h₁
  have hJ₂ : J ≤ K₂ := le_of_ggNbr hLB hI hDJ hpJ h₂
  by_contra hne
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK₁ hK₂ with h | h
  · exact hne h
  · have hJcomm : ⁅J, J⁆ = ⊥ := by
      have hle : ⁅J, J⁆ ≤ ⁅K₁, K₂⁆ := Subgroup.commutator_mono hJ₁ hJ₂
      rw [h] at hle
      exact le_bot_iff.mp hle
    have hJperf : ⁅J, J⁆ = J :=
      commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
    rw [hJperf] at hJcomm
    rw [hJcomm, Subgroup.card_bot] at hpJ
    exact hp.not_dvd_one hpJ

end CFSG.StandardType

end
