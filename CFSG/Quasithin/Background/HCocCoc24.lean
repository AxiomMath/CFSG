module

public import CFSG.Quasithin.Background.HCocBase
public import CFSG.Quasithin.Background.HZCoc24C

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc

@[expose] def cocA : List ℕ := [64, 96, 1777, 649, 1061, 3, 1, 844, 1396, 397, 1698]

@[expose] def cocB : List ℕ := [118, 10, 12, 2047, 24, 1908, 1010, 706, 1672, 1416, 1316]

@[expose] def cocKsWord : List ℕ :=
  [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1,
    0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]

@[expose] def cocCons : List (Option ℕ × List ℕ × List ℕ) :=
  [(none, [0, 0], [599072, 3933184, 2821168, 1976704, 0, 0, 1158448, 0, 0, 0, 0]),
    (none, [1, 1, 1], [336784, 2073488, 2525184, 0, 2730896, 0, 0, 0, 2851728, 0, 0]),
    (some 37, cocKsWord, [0, 0, 0, 0, 0, 1608592, 2993040, 3842048, 3842960, 0, 598928])]

@[expose] def cocPhi : List ℕ :=
  [77, 11, 103, 110, 0, 0, 127, 0, 0, 0, 0, 0, 80, 0, 124, 0, 0, 0, 0, 0, 0, 0]

theorem cocA_eq : matOf 11 (act11 pAArr) = cocA := by
  decide +kernel

theorem cocB_eq : matOf 11 (act11 pBArr) = cocB := by
  decide +kernel

theorem coc_lt : ∀ c ∈ cocA ++ cocB, c < 2 ^ 11 := by
  decide +kernel

theorem coc_ok : consOK 11 64 [cocA, cocB] (fun t => matOf 11 (act11 (ksC t))) cocCons = true := by
  decide +kernel

theorem coc_cert :
    matOf (2 * 11) (fun v => v ^^^ actM (w0Basis.map (packB 11 cocA cocB)) (actM cocPhi v)) =
      matOf (2 * 11) (conSum [cocA, cocB] 11 0 31 cocCons) := by
  decide +kernel

@[expose] noncomputable def rhoA : MulAut W11 := rho11 AutPerm le_rfl ⟨bridgePA, bridgePA_mem⟩

@[expose] noncomputable def rhoB : MulAut W11 := rho11 AutPerm le_rfl ⟨bridgePB, bridgePB_mem⟩

theorem actsBy_rhoA : ActsBy rhoA cocA := by
  rw [← cocA_eq]
  exact actsBy_of_xorLin (xorLin_act11 pAArr) (rho11_toW AutPerm le_rfl _ hasArr_pA)

theorem actsBy_rhoB : ActsBy rhoB cocB := by
  rw [← cocB_eq]
  exact actsBy_of_xorLin (xorLin_act11 pBArr) (rho11_toW AutPerm le_rfl _ hasArr_pB)

theorem img11_le_closure :
    img11 AutPerm ≤ Subgroup.closure {rhoA, rhoB} := by
  rw [← range_rho11_eq_img11 AutPerm le_rfl, MonoidHom.range_eq_map,
    ← CFSG.Sporadic.Mathieu.closure_pair_eq_top AutPerm_eq_closure bridgePA_mem bridgePB_mem,
    MonoidHom.map_closure, Set.image_pair]
  rfl

theorem ks_tgt (t : ℕ) (ht : t < 64) :
    ∃ ρ ∈ img11 KSp, ActsBy ρ (matOf 11 (act11 (ksC t))) :=
  ⟨rho11 AutPerm le_rfl ⟨ksP ⟨t, ht⟩, ksP_mem_autPerm _⟩, mem_img11_KSp.2 ⟨_, rfl⟩,
    actsBy_of_xorLin (xorLin_act11 _) (rho11_toW AutPerm le_rfl _ (hasArr_ksP ⟨t, ht⟩))⟩

theorem coc_std
    {δ : MulAut W11 → W11}
    (hδ : ∀ g ∈ img11 AutPerm, ∀ k ∈ img11 AutPerm, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ (img11 AutPerm) z0, δ r ∈ Subgroup.zpowers z0) :
    ∃ w ∈ vZ (img11 AutPerm) z0, ∀ g ∈ img11 AutPerm, δ g = w * (g w)⁻¹ := by
  rw [radZ_std] at hR
  rw [vZ_std]
  obtain ⟨m, hm, h⟩ := eq_inner_std hδ (p := 0) (z := 31) hR (by norm_num) (by decide)
    img11_le_closure (rho11_mem_img11 _) (rho11_mem_img11 _) actsBy_rhoA actsBy_rhoB coc_lt
    ks_tgt coc_ok w0_lt coc_cert
  exact ⟨toW 11 m, toW_mem_maskSub hm, h⟩

theorem coc_of_cocode24
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : MathieuCocode24 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) {δ : MulAut V → V} (hδ : ∀ g ∈ H, ∀ k ∈ H, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ H z, δ r ∈ Subgroup.zpowers z) :
    ∃ w ∈ vZ H z, ∀ g ∈ H, δ g = w * (g w)⁻¹ := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  refine coc_of_map e hδ hR fun δ₀ hδ₀ hR₀ => ?_
  have key : ∀ (A : Subgroup (MulAut W11)) (w : W11), A = img11 AutPerm → w = z0 →
      ∀ δ₀ : MulAut W11 → W11, (∀ g ∈ A, ∀ k ∈ A, δ₀ (g * k) = δ₀ g * g (δ₀ k)) →
        (∀ r ∈ radZ A w, δ₀ r ∈ Subgroup.zpowers w) →
          ∃ w' ∈ vZ A w, ∀ g ∈ A, δ₀ g = w' * (g w')⁻¹ := by
    rintro A w rfl rfl δ₀ hδ₀ hR₀
    exact coc_std hδ₀ hR₀
  exact key _ _ he hez δ₀ hδ₀ hR₀

end CFSG.Quasithin.H.Coc24
