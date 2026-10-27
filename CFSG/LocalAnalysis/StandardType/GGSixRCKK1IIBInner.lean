module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.Open
open scoped commutatorElement

private theorem rckBI_conj_eq_self_of_mem_normalizer_zpowers {D : Type*} [Group D] {t x : D}
    (ht : t * t = 1) (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers t : Set D)) :
    x * t * x⁻¹ = t := by
  let T : Subgroup D :=
    { carrier := ({1, t} : Set D)
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · left; rw [ha, hb, mul_one]
        · right; rw [ha, hb, one_mul]
        · right; rw [ha, hb, mul_one]
        · left; rw [ha, hb, ht]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with ha | ha
        · left; rw [ha, inv_one]
        · right; rw [ha, inv_eq_of_mul_eq_one_right ht] }
  have htT : t ∈ T := by
    change t ∈ ({1, t} : Set D)
    exact Or.inr rfl
  have hmem : x * t * x⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.mp hx t).mp (Subgroup.mem_zpowers t)
  have hcases : x * t * x⁻¹ = 1 ∨ x * t * x⁻¹ = t := by
    have hle : x * t * x⁻¹ ∈ T := (Subgroup.zpowers_le.mpr htT) hmem
    change x * t * x⁻¹ ∈ ({1, t} : Set D) at hle
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hle
  rcases hcases with h1 | ht'
  · have ht1 : t = 1 := by
      have h2 : x⁻¹ * (x * t * x⁻¹) * x = t := by group
      rw [h1] at h2
      simpa using h2.symm
    rw [h1, ht1]
  · exact ht'

theorem rckK1b_of_inner {G : Type} [Group G] [Finite G] (hZ : Subgroup.center G = ⊥) (r : G)
    (hr2 : r * r = 1)
    (hI : GGRootInnerAt (MulAut.conj : G →* MulAut G).range
      ((Subgroup.zpowers r).map (MulAut.conj : G →* MulAut G)))
    (hQ : ⁅pCoreOf 2 (Subgroup.centralizer ({r} : Set G)),
      pCoreOf 2 (Subgroup.centralizer ({r} : Set G))⁆ ≤ Subgroup.zpowers r)
    (V : Subgroup G) (hV : V ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G))) :
    K1Lift.K1b r V := by
  classical
  intro Y hY2 hYfix hYnorm v hv φ hφ
  let K : Subgroup (MulAut G) := (MulAut.conj : G →* MulAut G).range
  let R : Subgroup (MulAut G) := (Subgroup.zpowers r).map (MulAut.conj : G →* MulAut G)
  let C : Subgroup G := Subgroup.centralizer ({r} : Set G)
  let Q : Subgroup G := pCoreOf 2 C
  have hconj_nat : ∀ (ψ : MulAut G) (g : G),
      MulAut.conj (ψ g) = ψ * MulAut.conj g * ψ⁻¹ := by
    intro ψ g
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    intro a b hab
    have h1 : MulAut.conj (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hmem : a * b⁻¹ ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.mpr fun x => ?_
      have h := congrArg (fun f : MulAut G => f x) h1
      have h' : (a * b⁻¹) * x * (a * b⁻¹)⁻¹ = x := by
        have h2 : MulAut.conj (a * b⁻¹) x = x := by simpa using h
        rwa [MulAut.conj_apply] at h2
      calc x * (a * b⁻¹) = ((a * b⁻¹) * x * (a * b⁻¹)⁻¹) * (a * b⁻¹) := by rw [h']
        _ = (a * b⁻¹) * x := by group
    rw [hZ] at hmem
    exact mul_inv_eq_one.mp (by simpa using hmem)
  have h1 : Y ≤ Subgroup.normalizer (K : Set (MulAut G)) := by
    intro ψ _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      change x ∈ (MulAut.conj : G →* MulAut G).range at hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨g, hg⟩ := hx
      change ψ * x * ψ⁻¹ ∈ (MulAut.conj : G →* MulAut G).range
      rw [MonoidHom.mem_range]
      exact ⟨ψ g, by rw [hconj_nat ψ g, hg]⟩
    · intro hx
      change ψ * x * ψ⁻¹ ∈ (MulAut.conj : G →* MulAut G).range at hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨g, hg⟩ := hx
      change x ∈ (MulAut.conj : G →* MulAut G).range
      rw [MonoidHom.mem_range]
      exact ⟨ψ⁻¹ g, by rw [hconj_nat ψ⁻¹ g, hg]; group⟩
  have hgenR : R = Subgroup.zpowers (MulAut.conj r) := by
    change (Subgroup.zpowers r).map (MulAut.conj : G →* MulAut G)
      = Subgroup.zpowers (MulAut.conj r)
    rw [MonoidHom.map_zpowers]
  have h2 : Y ≤ Subgroup.normalizer (R : Set (MulAut G)) := by
    intro ψ hψ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hgenR]
    rw [MonoidHom.map_zpowers]
    congr 1
    change MulAut.conj ψ (MulAut.conj r) = MulAut.conj r
    rw [MulAut.conj_apply, (hconj_nat ψ r).symm, hYfix ψ hψ]
  have h3 : K ⊓ Subgroup.normalizer (R : Set (MulAut G)) ≤
      Subgroup.normalizer (Y : Set (MulAut G)) := by
    intro k hk
    obtain ⟨hkK, hkR⟩ := Subgroup.mem_inf.mp hk
    change k ∈ (MulAut.conj : G →* MulAut G).range at hkK
    rw [MonoidHom.mem_range] at hkK
    obtain ⟨g, hg⟩ := hkK
    rw [← hg]
    apply hYnorm g
    have hgr : g * r * g⁻¹ = r := by
      have hne : MulAut.conj g ∈
          Subgroup.normalizer (Subgroup.zpowers (MulAut.conj r) : Set (MulAut G)) := by
        have hkR' : k ∈ Subgroup.normalizer
            (Subgroup.zpowers (MulAut.conj r) : Set (MulAut G)) := by
          rwa [hgenR] at hkR
        rwa [hg]
      have ht : MulAut.conj r * MulAut.conj r = 1 := by
        rw [← map_mul, hr2, map_one]
      have h := rckBI_conj_eq_self_of_mem_normalizer_zpowers ht hne
      apply hinj
      rw [← MulAut.conj_apply g r, hconj_nat (MulAut.conj g) r]
      exact h
    calc g * r = (g * r * g⁻¹) * g := by group
      _ = r * g := by rw [hgr]
  have hCK : Subgroup.centralizer (K : Set (MulAut G)) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec4.E27.centralizer_range_conj_eq_bot (X := G) hZ
  have hYleK : Y ≤ K := by
    have h' : Y ≤ K ⊔ Subgroup.centralizer (K : Set (MulAut G)) := hI Y hY2 h1 h2 h3
    rw [hCK, sup_bot_eq] at h'
    exact h'
  let Y0 : Subgroup G := Y.comap (MulAut.conj : G →* MulAut G)
  have hY0p : IsPGroup 2 Y0 := by
    change IsPGroup 2 (Y.comap (MulAut.conj : G →* MulAut G))
    exact IsPGroup.comap_of_injective hY2 (MulAut.conj : G →* MulAut G) hinj
  have hcrC : ∀ c : ↥C, (c : G) * r = r * (c : G) := fun c =>
    (Subgroup.mem_centralizer_iff.mp c.2 r (by simp)).symm
  have hY0leC : Y0 ≤ C := by
    intro x hx
    change MulAut.conj x ∈ Y at hx
    change x ∈ Subgroup.centralizer ({r} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    have hxfix : x * r * x⁻¹ = r := by
      have h := hYfix (MulAut.conj x) hx
      rwa [MulAut.conj_apply] at h
    have hxr : x * r = r * x := by
      calc x * r = (x * r * x⁻¹) * x := by group
        _ = r * x := by rw [hxfix]
    exact hxr.symm
  have hY0norm : C ≤ Subgroup.normalizer (Y0 : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      change MulAut.conj x ∈ Y at hx
      change MulAut.conj (c * x * c⁻¹) ∈ Y
      have hcn : MulAut.conj c ∈ Subgroup.normalizer (Y : Set (MulAut G)) :=
        hYnorm c (hcrC ⟨c, hc⟩)
      have hmem := (Subgroup.mem_normalizer_iff.mp hcn (MulAut.conj x)).mp hx
      have hnat : MulAut.conj (c * x * c⁻¹)
          = MulAut.conj c * MulAut.conj x * (MulAut.conj c)⁻¹ := by
        rw [← MulAut.conj_apply c x]
        exact hconj_nat (MulAut.conj c) x
      rwa [hnat]
    · intro hx
      change MulAut.conj (c * x * c⁻¹) ∈ Y at hx
      change MulAut.conj x ∈ Y
      have hcn : MulAut.conj c ∈ Subgroup.normalizer (Y : Set (MulAut G)) :=
        hYnorm c (hcrC ⟨c, hc⟩)
      have hmem := (Subgroup.mem_normalizer_iff.mp (inv_mem hcn)
        (MulAut.conj (c * x * c⁻¹))).mp hx
      have hnat : MulAut.conj (c * x * c⁻¹)
          = MulAut.conj c * MulAut.conj x * (MulAut.conj c)⁻¹ := by
        rw [← MulAut.conj_apply c x]
        exact hconj_nat (MulAut.conj c) x
      rw [hnat] at hmem
      rw [inv_inv] at hmem
      have hgoal : (MulAut.conj c)⁻¹ * (MulAut.conj c * MulAut.conj x
          * (MulAut.conj c)⁻¹) * MulAut.conj c = MulAut.conj x := by group
      rwa [hgoal] at hmem
  have hY0leQ : Y0 ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hY0leC hY0norm hY0p
  have hφK : φ ∈ K := hYleK hφ
  change φ ∈ (MulAut.conj : G →* MulAut G).range at hφK
  rw [MonoidHom.mem_range] at hφK
  obtain ⟨k, hk⟩ := hφK
  have hk0 : k ∈ Y0 := by
    change MulAut.conj k ∈ Y
    rwa [hk]
  have hkQ : k ∈ Q := hY0leQ hk0
  have hvQ : v ∈ Q := hV hv
  have hcomm : φ v * v⁻¹ = ⁅k, v⁆ := by
    rw [← hk, MulAut.conj_apply, commutatorElement_def]
  rw [hcomm]
  exact hQ (Subgroup.commutator_mem_commutator hkQ hvQ)

end CFSG.StandardType.RCKK1II
