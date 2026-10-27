module

public import CFSG.RankThree.GF2n.Tim79a34TwDefs
public import CFSG.RankThree.GF2n.Tim79a34SpFacts
public import CFSG.RankThree.GF2n.Tim79a34TwSplit

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.LieType.Universal.Symplectic
open scoped commutatorElement

theorem tw_eq_one_of_card_two {F : Type} [Field F] (hF : Nat.card F = 2) {c : F} (hc : c ≠ 0) :
    c = 1 := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).1 hF
  by_contra h1
  have h0 : (0 : F) = y := huniq 0 zero_ne_one
  have hcy : c = y := huniq c h1
  exact hc (hcy.trans h0.symm)

theorem tw_mat_eq_spTrans_one {n : ℕ} {F : Type} [Field F] (hF : Nat.card F = 2)
    {a : Fin n ⊕ Fin n → F} {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T)
    {t : StatedSp n F} (ht : t ∈ T) (ht1 : t ≠ 1) :
    SpExtras.mat n F t = spTrans a 1 := by
  obtain ⟨c, hc⟩ := (hT.1 t).1 ht
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply ht1
    apply SpExtras.mat_injective
    rw [hc, ModelRank.spTrans_zero, map_one]
  rw [hc, tw_eq_one_of_card_two hF hc0]

theorem tw_exists_mem_of_transvection {Γ : Type} [Group Γ] {n : ℕ} {F : Type} [Field F]
    {φ : Γ →* StatedSp n F} (hsurj : Function.Surjective φ) {D : Set Γ}
    (hDc : ∀ x ∈ D, ∀ g : Γ, g * x * g⁻¹ ∈ D) {dV : Γ} (hdV : dV ∈ D)
    {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    (hmat : SpExtras.mat n F (φ dV) = spTrans a 1) :
    ∀ v : Fin n ⊕ Fin n → F, v ≠ 0 → ∃ d ∈ D, SpExtras.mat n F (φ d) = spTrans v 1 := by
  intro v hv
  obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero ha hv
  obtain ⟨x, rfl⟩ := hsurj g
  refine ⟨x * dV * x⁻¹, hDc dV hdV x, ?_⟩
  have e : φ (x * dV * x⁻¹) = φ x * φ dV * (φ x)⁻¹ := by simp only [map_mul, map_inv]
  rw [e, mat_conj_of_mat_eq hmat (φ x), hg]

theorem twistedStruct_holds (hGr : GriessSpMultiplierStatement)
    (hGrE : GriessSpMultiplierExceptionStatement) (hS : Sp62CoverLiftStatement) :
    TwistedStructStatement := by
  intro G _ _ M V Q P H hs hq h3 hnc
  obtain ⟨f, hf, hfq, hT⟩ := h3
  have hf2 : 2 ^ f = 2 ^ 1 := by rw [hfq, hq, pow_one]
  obtain rfl : f = 1 := Nat.pow_right_injective (le_refl 2) hf2
  obtain ⟨n, Φ, a, T, hn, hΦ, ha, hTa, hA⟩ :=
    exists_isTransGroup_of_transvConclusionSp_two hf hT (VZ_mem_rootClassZ V H)
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Xbar V H →* StatedSp n (GaloisField 2 1),
      ∀ x, φ₀ x = (MulEquiv.ofBijective Φ hΦ).symm (projZ V H x) :=
    ⟨(MulEquiv.ofBijective Φ hΦ).symm.toMonoidHom.comp (projZ V H), fun _ => rfl⟩
  have hkey : ∀ t : StatedSp n (GaloisField 2 1),
      (MulEquiv.ofBijective Φ hΦ).symm (Φ t) = t := fun t =>
    (MulEquiv.ofBijective Φ hΦ).symm_apply_eq.2 rfl
  have hsurj : Function.Surjective φ₀ := by
    intro g
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H)) (Φ g)
    have hy' : projZ V H y = Φ g := hy
    exact ⟨y, by rw [hφ₀, hy', hkey]⟩
  have hker : φ₀.ker = Subgroup.center (Xbar V H) := by
    ext x
    rw [MonoidHom.mem_ker, hφ₀, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨dV, hdVV, hdVD, hdVne⟩ := (hs.mc.toMinCex).exists_vy_mem_Dy hs.data
  have hdVne' : projZ V H dV ≠ 1 := hdVne
  have hmemVZ : projZ V H dV ∈ VZ V H := Subgroup.mem_map_of_mem (projZ V H) hdVV
  rw [hA] at hmemVZ
  obtain ⟨t, htT, ht⟩ := Subgroup.mem_map.1 hmemVZ
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hdVne' (by rw [← ht, map_one])
  have hdVmat : SpExtras.mat n (GaloisField 2 1) (φ₀ dV) = spTrans a 1 := by
    rw [hφ₀, ← ht, hkey]
    exact tw_mat_eq_spTrans_one hF2 hTa htT ht1
  have hDc : ∀ x ∈ Dy V H, ∀ g : Xbar V H, g * x * g⁻¹ ∈ Dy V H := by
    obtain ⟨d₀, hD⟩ := hs.data.isClass
    intro x hx g
    rw [hD] at hx ⊢
    exact (show IsConj d₀ x from hx).trans (isConj_iff.2 ⟨g, rfl⟩)
  have hD2 := tw_exists_mem_of_transvection hsurj hDc hdVD ha hdVmat
  have hinv : ∀ d ∈ Dy V H, d * d = 1 := fun d hd => by
    have h := pow_orderOf_eq_one d
    rw [hs.data.root.1 d hd] at h
    rwa [sq] at h
  have hP2 : commutator (StatedSp 2 (GaloisField 2 1)) ≠ ⊤ := statedSp_two_not_perfect hF2
  obtain ⟨hn3, z₀, hz0c, hz1, hzz, hZzp, hZinf, hZsup, hD8, -⟩ :=
    twisted_split (Dy V H) hn hs.data.isClass hinv hs.data.gen hs.degenerate φ₀ hsurj hker
      hD2 hnc hP2 hGr hGrE hS
  exact ⟨n, Φ, a, T, z₀, hn3, hΦ, ha, hTa, hA.symm, hz0c, hz1, hzz, hZzp, hZinf, hZsup,
    fun d hd => (hD8 d hd).1, fun d hd => (hD8 d hd).2⟩

end CFSG.RankThree.GF2n.Tim79a
