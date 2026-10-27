module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_le_pCoreOf_of_normalizer {A P : Subgroup G} (hP : IsPGroup 2 P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) : A ⊓ P ≤ pCoreOf 2 A := by
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ⟨fun x hx a => ?_⟩
    (hP.to_le inf_le_right)
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  refine ⟨A.mul_mem (A.mul_mem a.2 hx.1) (A.inv_mem a.2), ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hAP a.2) x).mp hx.2

theorem pCoreOf_le_sectionCentralizer_of_le {K H : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 H ≤ sectionCentralizer K (pCoreOf 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  have hgK := hHK (CFSG.LieType.BorelTits.pCoreOf_le 2 H hg)
  refine ⟨hgK, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hgK, fun k hk => ?_⟩
  have h1 : g * k * g⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hgK k).mp hk) (K.inv_mem hk)
  have h2 : g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    have h3 : k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk)) g⁻¹).mp (inv_mem hg)
    simpa [mul_assoc] using (pCoreOf 2 H).mul_mem hg h3
  exact inf_le_pCoreOf_of_normalizer (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    (fun x hx => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hx)) ⟨h1, h2⟩

theorem le_sectionCentralizer_of_le {K Y G₁ : Subgroup G} (hKG : K ≤ G₁) (hYG : Y ≤ G₁)
    (hGK : G₁ ≤ Subgroup.normalizer (K : Set G)) (hGY : G₁ ≤ Subgroup.normalizer (Y : Set G))
    (hYK : Y ≤ sectionCentralizer K (pCoreOf 2 K)) :
    K ≤ sectionCentralizer Y (pCoreOf 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro k hk
  have hkY := hGY (hKG hk)
  refine ⟨hkY, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hkY, fun y hy => ?_⟩
  have h1 : k * y * k⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hkY y).mp hy) (Y.inv_mem hy)
  have h2 : k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
    have h3 : y * k⁻¹ * y⁻¹ * k⁻¹⁻¹ ∈ pCoreOf 2 K := (hYK hy).2.2 k⁻¹ (K.inv_mem hk)
    have h4 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) _).mp h3
    simpa [mul_assoc] using h4
  exact inf_le_pCoreOf_of_normalizer (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    (fun x hx => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hGK (hYG hx)))
    ⟨h1, h2⟩

theorem mem_normalizer_sup' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply A4.mem_normalizer_of_conj_mem
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := sup_le
    (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
    (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb))
  exact fun x hx => hle hx

theorem le_pCoreOf_of_mul {G₁ K Y M₁ S : Subgroup G}
    (hdec : (G₁ : Set G) = (K : Set G) * (Y : Set G) * (M₁ : Set G)) (hKG : K ≤ G₁)
    (hYG : Y ≤ G₁) (hMG : M₁ ≤ G₁) (hSG : S ≤ G₁)
    (hGK : G₁ ≤ Subgroup.normalizer (K : Set G)) (hGY : G₁ ≤ Subgroup.normalizer (Y : Set G))
    (hS : IsPGroup 2 S) (hSK : S ≤ sectionCentralizer K (pCoreOf 2 K))
    (hSY : S ≤ sectionCentralizer Y (pCoreOf 2 Y)) (hMS : M₁ ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ pCoreOf 2 G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (K ⊔ Y) with hQ
  have hGKY : G₁ ≤ Subgroup.normalizer ((K ⊔ Y : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_sup' (hGK hg) (hGY hg)
  have hGQ : G₁ ≤ Subgroup.normalizer (Q : Set G) := fun g hg =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hGKY hg)
  have hQG : Q ≤ G₁ := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le hKG hYG)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hcore : ∀ X : Subgroup G, X ≤ K ⊔ Y → K ⊔ Y ≤ Subgroup.normalizer (X : Set G) →
      pCoreOf 2 X ≤ Q := fun X hX hXn =>
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hX)
      (fun z hz => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hXn hz))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hKQ : pCoreOf 2 K ≤ Q := hcore K le_sup_left (sup_le Subgroup.le_normalizer
    (hYG.trans hGK))
  have hYQ : pCoreOf 2 Y ≤ Q := hcore Y le_sup_right (sup_le (hKG.trans hGY)
    Subgroup.le_normalizer)
  set N := S ⊔ Q with hN
  have hN2 : IsPGroup 2 N := hS.to_sup_of_normal_right' hQ2 (hSG.trans hGQ)
  have hNG : N ≤ G₁ := sup_le hSG hQG
  have key : ∀ t : G, t ∈ Subgroup.normalizer (Q : Set G) → (∀ s ∈ S, t * s * t⁻¹ ∈ N) →
      t ∈ Subgroup.normalizer (N : Set G) := by
    intro t htQ htS
    apply A4.mem_normalizer_of_conj_mem
    have hle : N ≤ N.comap (MulAut.conj t).toMonoidHom := sup_le (fun s hs => htS s hs)
      (fun q hq => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp htQ q).mp hq))
    exact fun z hz => hle hz
  have hconj : ∀ (X : Subgroup G), pCoreOf 2 X ≤ Q → S ≤ sectionCentralizer X (pCoreOf 2 X) →
      ∀ k ∈ X, ∀ s ∈ S, k * s * k⁻¹ ∈ N := by
    intro X hXQ hSX k hk s hs
    have h1 : s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 X := (hSX hs).2.2 k hk
    have e : k * s * k⁻¹ = (s * k * s⁻¹ * k⁻¹)⁻¹ * s := by group
    rw [e]
    exact N.mul_mem (Subgroup.mem_sup_right (hXQ (inv_mem h1))) (Subgroup.mem_sup_left hs)
  have hnorm : G₁ ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    have hg' : g ∈ ((G₁ : Subgroup G) : Set G) := hg
    rw [hdec] at hg'
    obtain ⟨_, ⟨k, hk, y, hy, rfl⟩, m, hm, rfl⟩ := hg'
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact key k (hGQ (hKG hk)) (hconj K hKQ hSK k hk)
    · exact key y (hGQ (hYG hy)) (hconj Y hYQ hSY y hy)
    · exact key m (hGQ (hMG hm)) fun s hs =>
        Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hMS hm) s).mp hs)
  have hNn : (N.subgroupOf G₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).mpr hnorm
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf 2 hNG hNn hN2)

end CFSG.Quasithin.Vol2.Ch11.SecD
