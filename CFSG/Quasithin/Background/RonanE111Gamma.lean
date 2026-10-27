module

public import CFSG.Quasithin.Background.RonanE111Jsub
public import CFSG.Quasithin.Background.RonanE111Norm
public import CFSG.Quasithin.Background.RonanE111Inv
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R

variable {G : Type} [Group G] [Finite G]

theorem gamma_member {X T J : Subgroup G} (hR : E111Reduced G X T) (hJ : IsComp X J) {n : ℕ}
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω) {g : G}
    (hg : g ∈ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) {A : Subgroup G} (hAΩ : A ∈ Ω)
    (hAT : A ≤ T)
    (hV' : A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G)) ≤ T ⊓ Subgroup.normalizer (J : Set G))
    {P : Subgroup G}
    (hP : E1.IsE n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) (T ⊓ Subgroup.normalizer (J : Set G))
      (A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))) P) :
    ∃ A'' ∈ Ω, A'' ≤ T ∧
      E1.IsE n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) (T ⊓ Subgroup.normalizer (J : Set G))
        (A'' ⊓ Subgroup.normalizer (J : Set G)) P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hS
  set H : Subgroup G := J ⊔ S with hH
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hSsyl : IsSylowIn 2 S H := isSylowIn_compSup hR hJ
  have hXN : X ≤ Subgroup.normalizer (J : Set G) := hJ.le_normalizer
  have hT2 : IsPGroup 2 T := hR.2.2.2.2.2.1.2.1
  obtain ⟨j, hj, s, hs, rfl⟩ := exists_mul_of_mem_sup hSN hg
  have hsT : s ∈ T := hs.1
  have hsN : s ∈ Subgroup.normalizer (J : Set G) := hs.2
  have hAab : IsElemAbelian 2 A := hΩ.isElemAbelian A hAΩ
  have hA₁Ω : A1b.conjSub s A ∈ Ω := hΩ.conj A hAΩ s (Subgroup.mem_top s)
  have hA₁T : A1b.conjSub s A ≤ T := by
    intro y hy
    rw [A1b.mem_conjSub_iff] at hy
    have := T.mul_mem (T.mul_mem hsT (hAT hy)) (T.inv_mem hsT)
    simpa [mul_assoc] using this
  have hA₁ab : IsElemAbelian 2 (A1b.conjSub s A) := hΩ.isElemAbelian _ hA₁Ω
  have hconjN : ∀ {x : G}, x ∈ Subgroup.normalizer (J : Set G) → ∀ {B : Subgroup G},
      A1b.conjSub x (B ⊓ Subgroup.normalizer (J : Set G)) = A1b.conjSub x B ⊓ Subgroup.normalizer (J : Set G) := by
    intro x hx B
    ext y
    simp only [A1b.mem_conjSub_iff, Subgroup.mem_inf]
    refine and_congr Iff.rfl ⟨fun hy => ?_, fun hy => ?_⟩
    · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)
      simpa [mul_assoc] using this
    · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy) hx
      simpa [mul_assoc] using this
  have hV₁ : A1b.conjSub s (A ⊓ Subgroup.normalizer (J : Set G)) =
      A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G) := hconjN hsN
  have hBB : A1b.conjSub (j * s) (A ⊓ Subgroup.normalizer (J : Set G)) =
      A1b.conjSub j (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G)) := by
    rw [A1b.conjSub_mul, hV₁]
  rw [hBB] at hV' hP
  have hjS : ∀ v ∈ A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G), j * v * j⁻¹ ∈ T := fun v hv =>
    (hV' (A1b.mem_conjSub_of_mem hv)).1
  obtain ⟨Z, hZA, hZV, hZsup⟩ := exists_compl hA₁ab
    (inf_le_left : A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G) ≤ A1b.conjSub s A)
  haveI : Fintype ↥Z := Fintype.ofFinite _
  have hDS : DiagSetting X T (A1b.conjSub s A) J Z := ⟨hR, hA₁T, hA₁ab, hJ, hZA, hZV⟩
  obtain ⟨x, hxX, hxT, hxeq⟩ := norm_trick hDS hZsup hj hjS
  set A'' := A1b.conjSub x (A1b.conjSub s A) with hA''
  have hA''Ω : A'' ∈ Ω := hΩ.conj _ hA₁Ω x (Subgroup.mem_top x)
  have hxN : x ∈ Subgroup.normalizer (J : Set G) := hXN hxX
  have hV'' : A'' ⊓ Subgroup.normalizer (J : Set G) =
      A1b.conjSub x (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G)) := (hconjN hxN).symm
  refine ⟨A'', hA''Ω, hxT, ?_⟩
  rw [hV'']
  have hR2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G)) :=
    hT2.to_le (inf_le_left.trans inf_le_left)
  have hRH : T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G) ≤ H :=
    (inf_le_left.trans le_rfl).trans le_sup_right
  have hRnorm : H ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G) := by
    have hcent : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ x, x ∈ Subgroup.centralizer (J : Set G) →
        g * x * g⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
      intro g hg x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hy' : g⁻¹ * y * g ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
        simpa using this
      have h1 := hx _ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = (g * x * g⁻¹) * y := by group
    refine sup_le ?_ ?_
    · intro j' hj'
      have key : ∀ j'' ∈ J, ∀ r ∈ T ⊓ Subgroup.normalizer (J : Set G) ⊓
          Subgroup.centralizer (J : Set G), j'' * r * j''⁻¹ = r := by
        intro j'' hj'' r hr
        have := Subgroup.mem_centralizer_iff.mp hr.2 j'' hj''
        rw [this]
        group
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [key j' hj' x hx]
        exact hx
      · intro hx
        have h1 := key j'⁻¹ (Subgroup.inv_mem _ hj') _ hx
        have h2 : x = j' * x * j'⁻¹ := by simpa [mul_assoc] using h1
        rw [h2]
        exact hx
    · intro s' hs'
      have hs'T : s' ∈ T := hs'.1
      have hs'N : s' ∈ Subgroup.normalizer (J : Set G) := hs'.2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨⟨hxT, hxN⟩, hxC⟩
        exact ⟨⟨T.mul_mem (T.mul_mem hs'T hxT) (T.inv_mem hs'T),
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hs'N hxN) (Subgroup.inv_mem _ hs'N)⟩,
          hcent s' hs'N x hxC⟩
      · rintro ⟨⟨hxT, hxN⟩, hxC⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have := T.mul_mem (T.mul_mem (T.inv_mem hs'T) hxT) hs'T
          simpa [mul_assoc] using this
        · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs'N) hxN) hs'N
          simpa [mul_assoc] using this
        · have := hcent s'⁻¹ (Subgroup.inv_mem _ hs'N) _ hxC
          simpa [mul_assoc] using this
  have hRp : T ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.centralizer (J : Set G) ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRH hRnorm hR2
  have hsup : A1b.conjSub j (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G)) ⊔ pCoreOf 2 H =
      A1b.conjSub x (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G)) ⊔ pCoreOf 2 H := by
    have h1 := congrArg (fun K => K ⊔ pCoreOf 2 H) hxeq
    simp only [sup_assoc, sup_eq_right.mpr hRp] at h1
    exact h1
  have hB : A1b.conjSub j (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G)) ≤ S := hV'
  have hB' : A1b.conjSub x (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G)) ≤ S := by
    rw [← hV'']
    exact le_inf (inf_le_left.trans hxT) inf_le_right
  have hBab : IsElemAbelian 2 (A1b.conjSub j (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G))) :=
    isElemAbelian_of_le (CFSG.Open.IsElemAbelian.map hA₁ab (MulAut.conj j).toMonoidHom)
      (Subgroup.map_mono inf_le_left)
  have hB'ab : IsElemAbelian 2 (A1b.conjSub x (A1b.conjSub s A ⊓ Subgroup.normalizer (J : Set G))) :=
    isElemAbelian_of_le (CFSG.Open.IsElemAbelian.map hA₁ab (MulAut.conj x).toMonoidHom)
      (Subgroup.map_mono inf_le_left)
  exact (isE_congr_of_sup_pCore hSsyl hB hB' hBab hB'ab hsup).mp hP

end CFSG.Quasithin.RonanE111
