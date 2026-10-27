module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private lemma cenB_injective {N : ℕ} {K : Type} [Field K]
    {G T : Subgroup (GL (Fin N) K)}
    (hTS : T ⊓ LargeEvenScalars (Fin N) K = ⊥) :
    Function.Injective ((LargeEvenProjMk G).comp (T.subgroupOf G).subtype) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : LargeEvenProjMk G a = LargeEvenProjMk G b := hab
  have hk : a⁻¹ * b ∈ (LargeEvenScalars (Fin N) K).subgroupOf G := by
    have h1 : LargeEvenProjMk G (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab', inv_mul_cancel]
    have hmem : a⁻¹ * b ∈ MonoidHom.ker (LargeEvenProjMk G) := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at hmem
  have hmemT : a⁻¹ * b ∈ T.subgroupOf G :=
    (T.subgroupOf G).mul_mem ((T.subgroupOf G).inv_mem ha) hb
  have hbot : ((a⁻¹ * b : ↥G) : GL (Fin N) K) ∈ (⊥ : Subgroup (GL (Fin N) K)) := by
    rw [← hTS]
    exact ⟨hmemT, hk⟩
  have hone : a⁻¹ * b = 1 := Subtype.ext (Subgroup.mem_bot.mp hbot)
  exact Subtype.ext (inv_mul_eq_one.mp hone)

private lemma cenB_isElemAbelian {N : ℕ} {K : Type} [Field K] {p : ℕ}
    {G T : Subgroup (GL (Fin N) K)} (hT : IsElemAbelian p T) :
    IsElemAbelian p ((T.subgroupOf G).map (LargeEvenProjMk G)) := by
  have : IsMulCommutative T := hT.1
  refine ⟨inferInstance, ?_⟩
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hgp : (g : GL (Fin N) K) ^ p = 1 := hT.2 _ hg
  have hgp' : g ^ p = 1 := Subtype.ext (by simpa using hgp)
  rw [← map_pow, hgp', map_one]

private lemma cenB_card_map {N : ℕ} {K : Type} [Field K]
    {G T : Subgroup (GL (Fin N) K)} (hTG : T ≤ G)
    (hTS : T ⊓ LargeEvenScalars (Fin N) K = ⊥) :
    Nat.card ((T.subgroupOf G).map (LargeEvenProjMk G)) = Nat.card T := by
  have hinj := cenB_injective (G := G) hTS
  have hE : (T.subgroupOf G).map (LargeEvenProjMk G) =
      (⊤ : Subgroup (T.subgroupOf G)).map
        ((LargeEvenProjMk G).comp (T.subgroupOf G).subtype) := by
    ext r
    constructor
    · intro hr
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hr
      exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, trivial, rfl⟩
    · intro hr
      obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hr
      exact Subgroup.mem_map.mpr ⟨k.1, k.2, rfl⟩
  rw [hE, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv

private lemma cenB_le_fix {N : ℕ} {K : Type} [Field K]
    {G T : Subgroup (GL (Fin N) K)} {x : G}
    (hTc : ∀ t ∈ T, ∀ A : GL (Fin N) K, Commute A (x : GL (Fin N) K) → Commute A t) :
    (T.subgroupOf G).map (LargeEvenProjMk G) ≤
      ggFixSub (MulAut.conj (LargeEvenProjMk G x)) := by
  intro z hz
  rw [mem_ggFixSub]
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
  rw [MulAut.conj_apply]
  have hxg : Commute (x : GL (Fin N) K) (g : GL (Fin N) K) := hTc _ hg _ (Commute.refl _)
  have hxgg : (x : ↥G) * g * (x : ↥G)⁻¹ = g := by
    refine Subtype.ext ?_
    show ((x : GL (Fin N) K) * (g : GL (Fin N) K)) * (x : GL (Fin N) K)⁻¹ =
      (g : GL (Fin N) K)
    rw [hxg.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc LargeEvenProjMk G x * LargeEvenProjMk G g * (LargeEvenProjMk G x)⁻¹
      = LargeEvenProjMk G (x * g * x⁻¹) := by simp only [map_mul, map_inv]
    _ = LargeEvenProjMk G g := by rw [hxgg]

private lemma cenB_central {N : ℕ} {K : Type} [Field K]
    {G : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)} {x : G}
    (hGS : (G : Set (GL (Fin N) K)) ⊆ S)
    (hglue : ∀ A ∈ S, A * (x : GL (Fin N) K) * A⁻¹ * (x : GL (Fin N) K)⁻¹ ∈
      LargeEvenScalars (Fin N) K → Commute A (x : GL (Fin N) K))
    {T : Subgroup (GL (Fin N) K)}
    (hTc : ∀ t ∈ T, ∀ A : GL (Fin N) K, Commute A (x : GL (Fin N) K) → Commute A t)
    {z : LargeEvenProj G} (hz : z ∈ (T.subgroupOf G).map (LargeEvenProjMk G))
    {g : LargeEvenProj G} (hg : g ∈ ggFixSub (MulAut.conj (LargeEvenProjMk G x))) :
    g * z = z * g := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
  have hsurj : Function.Surjective (LargeEvenProjMk G) :=
    QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin N) K).subgroupOf G)
  obtain ⟨h, rfl⟩ := hsurj g
  have hfix : MulAut.conj (LargeEvenProjMk G x) (LargeEvenProjMk G h) =
      LargeEvenProjMk G h := hg
  have hfix' : LargeEvenProjMk G x * LargeEvenProjMk G h * (LargeEvenProjMk G x)⁻¹ =
      LargeEvenProjMk G h := by
    simpa only [MulAut.conj_apply] using hfix
  have hscal : ((x : ↥G) * h * (x : ↥G)⁻¹ * h⁻¹ : ↥G) ∈
      (LargeEvenScalars (Fin N) K).subgroupOf G := by
    have h1 : LargeEvenProjMk G ((x : ↥G) * h * (x : ↥G)⁻¹ * h⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hfix', mul_inv_cancel]
    have hmem : ((x : ↥G) * h * (x : ↥G)⁻¹ * h⁻¹) ∈ MonoidHom.ker (LargeEvenProjMk G) :=
      MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk'] at hmem
  have hscal' : (h : GL (Fin N) K) * (x : GL (Fin N) K) * (h : GL (Fin N) K)⁻¹ *
      (x : GL (Fin N) K)⁻¹ ∈ LargeEvenScalars (Fin N) K := by
    have hinv := (LargeEvenScalars (Fin N) K).inv_mem hscal
    simpa [mul_inv_rev, mul_assoc] using hinv
  have hAx : Commute (h : GL (Fin N) K) (x : GL (Fin N) K) := hglue h (hGS h.2) hscal'
  have hhk : Commute (h : GL (Fin N) K) (k : GL (Fin N) K) := hTc _ hk h hAx
  have hhk' : h * k = k * h := Subtype.ext hhk.eq
  calc LargeEvenProjMk G h * LargeEvenProjMk G k
      = LargeEvenProjMk G (h * k) := (map_mul _ h k).symm
    _ = LargeEvenProjMk G (k * h) := by rw [hhk']
    _ = LargeEvenProjMk G k * LargeEvenProjMk G h := map_mul _ k h

private lemma cenB_psi_x_fixed {N : ℕ} {K : Type} [Field K]
    {G : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)} {x : G}
    (hnorm : ∀ A ∈ S, ∀ g ∈ G, A * g * A⁻¹ ∈ G)
    (hcen : Subgroup.center (LargeEvenProj G) = ⊥)
    {ψ : MulAut (LargeEvenProj G)}
    (hψ : ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk G) S)
    (hcomm : Commute ψ (MulAut.conj (LargeEvenProjMk G x))) :
    ψ (LargeEvenProjMk G x) = LargeEvenProjMk G x := by
  obtain ⟨A, hA, hArel⟩ := hψ
  have hψx : ψ (LargeEvenProjMk G x) =
      LargeEvenProjMk G ⟨A * (x : GL (Fin N) K) * A⁻¹, hnorm A hA x x.2⟩ :=
    hArel x ⟨A * (x : GL (Fin N) K) * A⁻¹, hnorm A hA x x.2⟩ rfl
  have hkey : ∀ r : LargeEvenProj G,
      ψ (LargeEvenProjMk G x) * ψ r * (ψ (LargeEvenProjMk G x))⁻¹ =
        LargeEvenProjMk G x * ψ r * (LargeEvenProjMk G x)⁻¹ := by
    intro r
    have h : ψ (MulAut.conj (LargeEvenProjMk G x) r) =
        MulAut.conj (LargeEvenProjMk G x) (ψ r) := by
      have h' := congrArg (fun e : MulAut (LargeEvenProj G) => e r) hcomm
      simpa only [MulAut.mul_apply] using h'
    simp only [MulAut.conj_apply, map_mul, map_inv] at h
    exact h
  have hcentral : ∀ s : LargeEvenProj G,
      s * ((LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x)) =
        ((LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x)) * s := by
    intro s
    obtain ⟨r, rfl⟩ := ψ.surjective s
    have h := hkey r
    have hc : ((LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x)) * ψ r =
        ψ r * ((LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x)) := by
      calc ((LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x)) * ψ r
          = (LargeEvenProjMk G x)⁻¹ *
              (ψ (LargeEvenProjMk G x) * ψ r * (ψ (LargeEvenProjMk G x))⁻¹) *
              ψ (LargeEvenProjMk G x) := by group
        _ = (LargeEvenProjMk G x)⁻¹ *
              (LargeEvenProjMk G x * ψ r * (LargeEvenProjMk G x)⁻¹) *
              ψ (LargeEvenProjMk G x) := by rw [h]
        _ = ψ r * ((LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x)) := by group
    exact hc.symm
  have hc : (LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x) ∈
      Subgroup.center (LargeEvenProj G) := Subgroup.mem_center_iff.mpr hcentral
  have hc1 : (LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x) = 1 := by
    rw [hcen] at hc
    exact Subgroup.mem_bot.mp hc
  calc ψ (LargeEvenProjMk G x)
      = (LargeEvenProjMk G x) *
          ((LargeEvenProjMk G x)⁻¹ * ψ (LargeEvenProjMk G x)) := by
        rw [mul_inv_cancel_left]
    _ = (LargeEvenProjMk G x) * 1 := by rw [hc1]
    _ = LargeEvenProjMk G x := mul_one _

private lemma cenB_fixed {N : ℕ} {K : Type} [Field K]
    {G : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)} {x : G}
    (hnorm : ∀ A ∈ S, ∀ g ∈ G, A * g * A⁻¹ ∈ G)
    (hcen : Subgroup.center (LargeEvenProj G) = ⊥)
    (hglue : ∀ A ∈ S, A * (x : GL (Fin N) K) * A⁻¹ * (x : GL (Fin N) K)⁻¹ ∈
      LargeEvenScalars (Fin N) K → Commute A (x : GL (Fin N) K))
    {T : Subgroup (GL (Fin N) K)}
    (hTc : ∀ t ∈ T, ∀ A : GL (Fin N) K, Commute A (x : GL (Fin N) K) → Commute A t)
    {ψ : MulAut (LargeEvenProj G)}
    (hψ : ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk G) S)
    (hcomm : Commute ψ (MulAut.conj (LargeEvenProjMk G x)))
    {z : LargeEvenProj G} (hz : z ∈ (T.subgroupOf G).map (LargeEvenProjMk G)) :
    ψ z = z := by
  have hψxx := cenB_psi_x_fixed hnorm hcen hψ hcomm
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨A, hA, hArel⟩ := hψ
  have hψx : ψ (LargeEvenProjMk G x) =
      LargeEvenProjMk G ⟨A * (x : GL (Fin N) K) * A⁻¹, hnorm A hA x x.2⟩ :=
    hArel x ⟨A * (x : GL (Fin N) K) * A⁻¹, hnorm A hA x x.2⟩ rfl
  have hxeq : LargeEvenProjMk G ⟨A * (x : GL (Fin N) K) * A⁻¹, hnorm A hA x x.2⟩ =
      LargeEvenProjMk G x := by
    rw [← hψx, hψxx]
  have hscalA : A * (x : GL (Fin N) K) * A⁻¹ * (x : GL (Fin N) K)⁻¹ ∈
      LargeEvenScalars (Fin N) K := by
    have h1 : LargeEvenProjMk G
        (⟨A * (x : GL (Fin N) K) * A⁻¹, hnorm A hA x x.2⟩ * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hxeq, mul_inv_cancel]
    have hmem : (⟨A * (x : GL (Fin N) K) * A⁻¹, hnorm A hA x x.2⟩ * x⁻¹ : ↥G) ∈
        MonoidHom.ker (LargeEvenProjMk G) := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk'] at hmem
    simpa [Subgroup.mem_subgroupOf] using hmem
  have hAx : Commute A (x : GL (Fin N) K) := hglue A hA hscalA
  have hAk : Commute A (k : GL (Fin N) K) := hTc _ hk A hAx
  have hAkeq : A * (k : GL (Fin N) K) * A⁻¹ = (k : GL (Fin N) K) := by
    rw [hAk.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc ψ (LargeEvenProjMk G k)
      = LargeEvenProjMk G ⟨A * (k : GL (Fin N) K) * A⁻¹, hnorm A hA k k.2⟩ :=
        hArel k ⟨A * (k : GL (Fin N) K) * A⁻¹, hnorm A hA k k.2⟩ rfl
    _ = LargeEvenProjMk G k := by
        rw [show (⟨A * (k : GL (Fin N) K) * A⁻¹, hnorm A hA k k.2⟩ : ↥G) = k from
          Subtype.ext hAkeq]

theorem ggK1Center_of_le {N : ℕ} {K : Type} [Field K] {p : ℕ} {D : GGKacDatum}
    {G : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)} {x : G}
    (hGS : (G : Set (GL (Fin N) K)) ⊆ S)
    (hnorm : ∀ A ∈ S, ∀ g ∈ G, A * g * A⁻¹ ∈ G)
    (hcen : Subgroup.center (LargeEvenProj G) = ⊥)
    (hglue : ∀ A ∈ S, A * (x : GL (Fin N) K) * A⁻¹ * (x : GL (Fin N) K)⁻¹ ∈
      LargeEvenScalars (Fin N) K → Commute A (x : GL (Fin N) K))
    {T : Subgroup (GL (Fin N) K)} (hTG : T ≤ G) (hT : IsElemAbelian p T)
    (hTS : T ⊓ LargeEvenScalars (Fin N) K = ⊥) (hcard : Nat.card T = p ^ D.rZ)
    (hTc : ∀ t ∈ T, ∀ A : GL (Fin N) K, Commute A (x : GL (Fin N) K) → Commute A t) :
    GGK1Center p D (LargeEvenProj G) (LargeEvenMatConjImage (LargeEvenProjMk G) S)
      (MulAut.conj (LargeEvenProjMk G x)) := by
  intro _
  refine ⟨(T.subgroupOf G).map (LargeEvenProjMk G), cenB_isElemAbelian hT, ?_, ?_, ?_, ?_⟩
  · rw [cenB_card_map hTG hTS]
    exact hcard
  · exact cenB_le_fix hTc
  · intro z hz g hg
    exact cenB_central hGS hglue hTc hz hg
  · intro ψ hψ _ hcomm z hz
    exact cenB_fixed hnorm hcen hglue hTc hψ hcomm hz

end CFSG.StandardType

end
