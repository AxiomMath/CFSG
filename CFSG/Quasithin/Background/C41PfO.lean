module

public import CFSG.Quasithin.Background.C41PfM
public import CFSG.Quasithin.Background.C41PfG

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def C46Block : Prop :=
  ∀ (H R M L V K : Subgroup G) (n : ℕ) (α : ↥K →* alternatingGroup (Fin n)),
    C41Post H R M L V K →
    SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SmithC27.C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    SBc17.C27Alt H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
    IsShort2 K → IsAltBlockTypeWith K n α → 7 ≤ n → n ≤ 8 → InducesTransposition R K n →
    M ⊓ K = K ⊓ Subgroup.normalizer (R : Set G) →
    IsAltBlockType (conjClosure L M) (n - 2) ∧ V = blockU (conjClosure L M)

namespace C41Pf

omit [Finite G] in
theorem center_eq_bot_of_alt {K : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (α : ↥K →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hc : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz x)]
  rw [hc, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
  exact Subgroup.mem_bot.mpr h1

omit [Finite G] in
theorem oTwoZIn_le_pCoreOf {K : Subgroup G}
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) : oTwoZIn K ≤ pCoreOf 2 K := by
  rintro _ ⟨w, hw, rfl⟩
  have hw1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) w = 1 := by
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥K) w ∈ Subgroup.center _ := hw
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
  rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
  exact ⟨w, hw1, rfl⟩

theorem eq_one_or_eq_of_mem_zpowers {X : Type*} [Group X] {s y : X} (hs : orderOf s = 2)
    (hy : y ∈ Subgroup.zpowers s) : y = 1 ∨ y = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hs]
  have h0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h1 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
  rcases (show k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 by omega) with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem inf_eq_of_c27Alt {H R M L V K : Subgroup G} (hP : C41Post H R M L V K)
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) {n : ℕ} (hn : 4 ≤ n)
    (α : ↥K →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) {t : G}
    (htV : t ∈ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G))
    (hRt : autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) =
      Subgroup.zpowers (conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⟨t, htV⟩))
    (ht2 : orderOf (conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⟨t, htV⟩) = 2)
    (hMK : autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) =
      autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⊓
        Subgroup.centralizer (autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :
          Set (MulAut ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))))) :
    (K ⊔ R) ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤ R ∧
      M ⊓ K = K ⊓ Subgroup.normalizer (R : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hW
  have h := hP.hyp
  have hKH : K ≤ H := le_of_mem_cComp hP.comp
  have hNK : conjClosure L M ≤ Subgroup.normalizer (K : Set G) :=
    hP.le.trans Subgroup.le_normalizer
  have hKRN : K ⊔ R ≤ Subgroup.normalizer (W : Set G) :=
    (le_normalizer_pCoreOf 2 (K ⊔ R)).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  have hZ := center_eq_bot_of_alt hn α hα hker
  have hO2 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 K)
        (hP.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K)))
      (pCoreOf_isPGroup 2 K)
  have hKR : pCoreOf 2 (K ⊔ R) ≤ R := pCoreOf_sup_le_of_hyp h hKH hNK
  have hCR : (K ⊔ R) ⊓ Subgroup.centralizer (W : Set G) ≤ R :=
    h1.2.1.trans (sup_le hKR ((oTwoZIn_le_pCoreOf hZ).trans (hO2.trans hKR)))
  refine ⟨hCR, le_antisymm ?_ ?_⟩
  ·
    rintro x ⟨hxM, hxK⟩
    refine ⟨hxK, mem_normalizer_of_map_le ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    have hxN : x ∈ Subgroup.normalizer (W : Set G) := hKRN (Subgroup.mem_sup_left hxK)
    have hrN : r ∈ Subgroup.normalizer (W : Set G) := hKRN (Subgroup.mem_sup_right hr)
    have hx : conjAct W ⟨x, hxN⟩ ∈ autOn (M ⊓ K) W := ⟨⟨x, hxN⟩, ⟨hxM, hxK⟩, rfl⟩
    rw [hMK] at hx
    have hcomm := Subgroup.mem_centralizer_iff.mp hx.2 _ ⟨⟨r, hrN⟩, hr, rfl⟩
    have hc : conjAct W (⟨x, hxN⟩ * ⟨r, hrN⟩ * ⟨x, hxN⟩⁻¹ * ⟨r, hrN⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm, mul_inv_cancel_right,
        mul_inv_cancel]
    have hcC : x * r * x⁻¹ * r⁻¹ ∈ Subgroup.centralizer (W : Set G) := A4.conjAct_eq_one_iff.mp hc
    have hcKR : x * r * x⁻¹ * r⁻¹ ∈ K ⊔ R :=
      (K ⊔ R).mul_mem ((K ⊔ R).mul_mem ((K ⊔ R).mul_mem (Subgroup.mem_sup_left hxK)
        (Subgroup.mem_sup_right hr)) ((K ⊔ R).inv_mem (Subgroup.mem_sup_left hxK)))
        ((K ⊔ R).inv_mem (Subgroup.mem_sup_right hr))
    have := R.mul_mem (hCR ⟨hcKR, hcC⟩) hr
    simpa [MulAut.conj_apply, mul_assoc] using this
  ·
    rintro x ⟨hxK, hxR⟩
    have hxN : x ∈ Subgroup.normalizer (W : Set G) := hKRN (Subgroup.mem_sup_left hxK)
    have hxc : conjAct W ⟨x, hxN⟩ ∈ autOn K W ⊓ Subgroup.centralizer (autOn R W : Set _) := by
      refine ⟨⟨⟨x, hxN⟩, hxK, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have hr' : (r : G) ∈ R := hr
      have hxr : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxR r).mp hr'
      have hc1 : conjAct W r ∈ Subgroup.zpowers (conjAct W ⟨t, htV⟩) := hRt ▸ ⟨r, hr, rfl⟩
      have hc2 : conjAct W (⟨x, hxN⟩ * r * ⟨x, hxN⟩⁻¹) ∈
          Subgroup.zpowers (conjAct W ⟨t, htV⟩) := hRt ▸ ⟨_, hxr, rfl⟩
      rw [map_mul, map_mul, map_inv] at hc2
      rcases eq_one_or_eq_of_mem_zpowers ht2 hc1 with h0 | h0
      · rw [h0]
        group
      · rcases eq_one_or_eq_of_mem_zpowers ht2 hc2 with h3 | h3
        · exfalso
          rw [h0] at h3
          have h4 : conjAct W ⟨t, htV⟩ = 1 := by
            have := congrArg (fun y => (conjAct W ⟨x, hxN⟩)⁻¹ * y * conjAct W ⟨x, hxN⟩) h3
            simpa [mul_assoc] using this
          rw [h4, orderOf_one] at ht2
          exact absurd ht2 (by norm_num)
        · rw [h0]
          rw [h0] at h3
          have h5 := congrArg (· * conjAct W ⟨x, hxN⟩) h3
          simp only [inv_mul_cancel_right] at h5
          exact h5.symm
    rw [← hMK] at hxc
    obtain ⟨y, ⟨hyM, hyK⟩, hye⟩ := hxc
    have h2 : conjAct W (y⁻¹ * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, map_inv, hye, inv_mul_cancel]
    have h3 : (y : G)⁻¹ * x ∈ Subgroup.centralizer (W : Set G) := by
      simpa using A4.conjAct_eq_one_iff.mp h2
    have h4 : (y : G)⁻¹ * x ∈ R := hCR ⟨(K ⊔ R).mul_mem ((K ⊔ R).inv_mem
      (Subgroup.mem_sup_left hyK)) (Subgroup.mem_sup_left hxK), h3⟩
    have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
    refine ⟨?_, hxK⟩
    rw [e]
    exact M.mul_mem hyM (h.le_M h4)

omit [Finite G] in
theorem inducesTransposition_of_c27Alt {R K W : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hKW : K ≤ Subgroup.normalizer (W : Set G))
    (hRW : R ≤ Subgroup.normalizer (W : Set G))
    (hCK : K ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 K) {n : ℕ}
    (α : ↥K →* alternatingGroup (Fin n)) (hαw : IsAltBlockTypeWith K n α) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (W : Set G))
    (hRt : autOn R W = Subgroup.zpowers (conjAct W ⟨t, htV⟩))
    (ht2 : orderOf (conjAct W ⟨t, htV⟩) = 2) {σ : Equiv.Perm (Fin n)} (hσ : σ.IsSwap)
    (hconj : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹) :
    InducesTransposition R K n := by
  have hca : ∀ (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K),
      ((conjAct K g k : ↥K) : G) = g * k * (g : G)⁻¹ := fun _ _ => rfl
  have hmemK : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K :=
    fun g hg k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hfix : ∀ (s : G) (hs : s ∈ R), s ∈ Subgroup.centralizer (W : Set G) → ∀ k : ↥K,
      α ⟨s * k * s⁻¹, hmemK s (hRN hs) k k.2⟩ = α k := by
    intro s hs hsC k
    have hkN : (k : G) ∈ Subgroup.normalizer (W : Set G) := hKW k.2
    have hks : (k : G) * s⁻¹ * (k : G)⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : (k : G)⁻¹ * w * k ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hkN) w).mp hw
        simpa using this
      have h2 := Subgroup.mem_centralizer_iff.mp
        ((Subgroup.centralizer (W : Set G)).inv_mem hsC) _ hw'
      calc w * ((k : G) * s⁻¹ * (k : G)⁻¹)
          = (k : G) * (((k : G)⁻¹ * w * k) * s⁻¹) * (k : G)⁻¹ := by group
        _ = (k : G) * (s⁻¹ * ((k : G)⁻¹ * w * k)) * (k : G)⁻¹ := by rw [h2]
        _ = (k : G) * s⁻¹ * (k : G)⁻¹ * w := by group
    have hc : s * k * s⁻¹ * (k : G)⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
      have := (Subgroup.centralizer (W : Set G)).mul_mem hsC hks
      simpa [mul_assoc] using this
    have hcK : s * k * s⁻¹ * (k : G)⁻¹ ∈ K := K.mul_mem (hmemK s (hRN hs) k k.2) (K.inv_mem k.2)
    have hO := hCK ⟨hcK, hc⟩
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K] at hO
    obtain ⟨c, hcO, hce⟩ := hO
    have hc1 : α c = 1 := by
      rw [← MonoidHom.mem_ker, hαw.2.1]
      exact hcO
    have hce' : c = ⟨s * k * s⁻¹, hmemK s (hRN hs) k k.2⟩ * k⁻¹ := Subtype.ext hce
    rw [hce', map_mul, map_inv, mul_inv_eq_one] at hc1
    exact hc1
  refine ⟨hRN, α, hαw, σ, hσ, fun g hgR => ?_, ⟨⟨t, hRN htR⟩, htR, fun k => ?_⟩⟩
  · have hgW : (g : G) ∈ Subgroup.normalizer (W : Set G) := hRW hgR
    have hg1 : conjAct W ⟨g, hgW⟩ ∈ Subgroup.zpowers (conjAct W ⟨t, htV⟩) :=
      hRt ▸ ⟨⟨g, hgW⟩, hgR, rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers ht2 hg1 with h0 | h0
    · left
      intro k
      have := hfix g hgR (A4.conjAct_eq_one_iff.mp h0) k
      rw [← this]
      rfl
    · right
      intro k
      have hs : (g : G) * t⁻¹ ∈ R := R.mul_mem hgR (R.inv_mem htR)
      have hsC : (g : G) * t⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
        have h5 : conjAct W (⟨g, hgW⟩ * ⟨t, htV⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, h0, mul_inv_cancel]
        exact A4.conjAct_eq_one_iff.mp h5
      have hk' : t * k * t⁻¹ ∈ K := hmemK t (hRN htR) k k.2
      have h6 := hfix _ hs hsC ⟨t * k * t⁻¹, hk'⟩
      have h7 : (⟨(g : G) * t⁻¹ * (t * k * t⁻¹) * ((g : G) * t⁻¹)⁻¹,
          hmemK _ (hRN hs) _ hk'⟩ : ↥K) = conjAct K g k := by
        apply Subtype.ext
        rw [hca]
        group
      rw [h7] at h6
      rw [h6]
      exact hconj k k.2 hk'
  · have hk' : t * k * t⁻¹ ∈ K := hmemK t (hRN htR) k k.2
    have h7 : conjAct K ⟨t, hRN htR⟩ k = ⟨t * k * t⁻¹, hk'⟩ := Subtype.ext (hca _ k)
    rw [h7]
    exact hconj k k.2 hk'

theorem c41InspB_of (hK0 : C41KZero G) (hA3 : A3Orbits G) (hC46 : C46Block G) :
    C41InspB G := by
  intro H R M L V K hP h1 h2 hc
  have hc' := hc
  obtain ⟨⟨n, α, hn5, hn8, hshort, hαw, t, htR, htV, hRt, ht2, σ, hσ, hconj⟩, hMK⟩ := hc
  have h := hP.hyp
  have hM₀1 : conjClosure L M ≠ ⊥ := fun hb => ne_bot_of_mem_cComp h.comp
    (eq_bot_iff.mpr ((le_conjClosure L M).trans hb.le))
  have hn7 : 7 ≤ n := by
    by_contra hlt
    exact hM₀1 (eq_bot_of_alt_transposition hP.le_normalizer h1 hn5 (by omega) α hαw.1 hαw.2.1
      htR htV hσ hconj hMK hP.le (C2Nine.conjClosure_le_M h) (C2Nine.perfect_conjClosure_of_hyp h))
  obtain ⟨hCR, hMKR⟩ := inf_eq_of_c27Alt hP h1 (by omega) α hαw.1 hαw.2.1 htV hRt ht2 hMK
  have hKRN : K ⊔ R ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
    (le_normalizer_pCoreOf 2 (K ⊔ R)).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  have hCK : K ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤
      pCoreOf 2 K :=
    (inf_centralizer_le_oTwoZIn h1).trans
      (oTwoZIn_le_pCoreOf (center_eq_bot_of_alt (by omega) α hαw.1 hαw.2.1))
  have hIT := inducesTransposition_of_c27Alt hP.le_normalizer (le_sup_left.trans hKRN)
    (le_sup_right.trans hKRN) hCK α hαw htR htV hRt ht2 hσ hconj
  obtain ⟨hMb, hV⟩ := hC46 H R M L V K n α hP h1 h2 hc' hshort hαw hn7 hn8 hIT hMKR
  obtain ⟨α', hα's, hα'k, -⟩ := hMb.2
  have hn2 : n - 2 + 2 = n := by omega
  have : IsSimpleGroup (alternatingGroup (Fin (n - 2))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  let e : ModO2 (conjClosure L M) ≃* alternatingGroup (Fin (n - 2)) :=
    (QuotientGroup.quotientMulEquivOfEq hα'k.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α' hα's)
  have hS : IsSimpleGroup (ModO2 (conjClosure L M)) := e.isSimpleGroup
  refine c41Conclusion_of_case hK0 hA3 hP hS (Or.inl ⟨n - 2, by omega, hMb, hV, ?_, ?_, hMKR⟩)
  · rw [hn2]
    exact ⟨hshort, α, hαw⟩
  · rw [hn2]
    exact hIT

end C41Pf

end CFSG.Quasithin
