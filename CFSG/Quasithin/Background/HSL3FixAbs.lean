module

public import CFSG.Quasithin.Background.HSL3Fix

public section

namespace CFSG.Quasithin

namespace H

namespace SL3One

open CFSG.Open CFSG.Assembly.LowTwoRank SL3Pair
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_conj_pairSL {g : MulAut (PairMod K)} (hg : g ∈ pairNorm K) :
    (pairSL K).map (MulAut.conj g).toMonoidHom = pairSL K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    · simp [mul_assoc]

omit [Finite K] [CharP K 2] in
theorem congrHom_trans {V : Type*} [CommGroup V] (e : V ≃* PairMod K) (s : MulAut (PairMod K))
    (x : MulAut V) : congrHom (e.trans s) x = s * congrHom e x * s⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem exists_center_model {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    (hK : Nat.card K = 2) {e : V ≃* PairMod K} (he : H.map (congrHom e) = pairSL K)
    {E : Subgroup (MulAut V)} (hEH : E ≤ H) (hE2 : IsElemAbelian2 E) (hE4 : Nat.card E = 4) :
    ∃ e' : V ≃* PairMod K, H.map (congrHom e') = pairSL K ∧
      ∃ c : Fin 3 → K, c ≠ 0 ∧ IsCenterType (E.map (congrHom e')) c := by
  set E' := E.map (congrHom e) with hE'def
  have hE'SL : E' ≤ pairSL K := he ▸ Subgroup.map_mono hEH
  have hE'2 : IsElemAbelian2 E' := (isElemAbelian2_map_congrHom e).mpr hE2
  set E₀ : Subgroup (GL (Fin 3) K) := E'.comap pairHom with hE₀def
  have hrange : E' ≤ pairHom.range := fun x hx => by
    obtain ⟨γ, -, hγ⟩ := hE'SL hx
    exact ⟨γ, hγ⟩
  have hE₀card : Nat.card E₀ = 4 := by
    have h1 : E₀.map pairHom = E' := Subgroup.map_comap_eq_self hrange
    have h2 := Subgroup.card_map_of_injective (K := E₀) (pairHom_injective (K := K))
    rw [h1, hE'def, card_map_congrHom, hE4] at h2
    exact h2.symm
  have hsq : ∀ A ∈ E₀, A * A = 1 := fun A hA => pairHom_injective (by
    rw [map_mul, map_one, ← sq]
    exact hE'2.2 _ hA)
  have hcomm : ∀ A ∈ E₀, ∀ B ∈ E₀, A * B = B * A := fun A hA B hB => pairHom_injective (by
    rw [map_mul, map_mul]
    exact hE'2.1 _ hA _ hB)
  rcases center_or_axis E₀ hsq hcomm (by rw [hK, hE₀card]; norm_num) with
    ⟨c, hc, hcen⟩ | ⟨ψ, hψ, hax⟩
  · refine ⟨e, he, c, hc, fun x hx => ?_⟩
    obtain ⟨γ, -, rfl⟩ := hE'SL hx
    obtain ⟨φ, hφ, hγ⟩ := hcen γ hx
    exact ⟨φ, hφ, congrArg pairHom (Units.ext (hγ.trans (coe_trvGL hφ).symm))⟩
  · refine ⟨e.trans (swapAut K), ?_, ψ, hψ, fun x hx => ?_⟩
    · have h1 : H.map (congrHom (e.trans (swapAut K))) =
          (H.map (congrHom e)).map (MulAut.conj (swapAut K)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
      rw [h1, he, map_conj_pairSL swapAut_mem_pairNorm]
    · obtain ⟨y, hy, rfl⟩ := hx
      have hyE' : congrHom e y ∈ E' := ⟨y, hy, rfl⟩
      obtain ⟨γ, -, hγ⟩ := hE'SL hyE'
      have hγE₀ : γ ∈ E₀ := by
        change pairHom γ ∈ E'
        rw [hγ]
        exact hyE'
      obtain ⟨w, hw, hγw⟩ := hax γ hγE₀
      have hwψ : w ⬝ᵥ ψ = 0 := by
        rw [dotProduct_comm]
        exact hw
      refine ⟨w, hwψ, ?_⟩
      rw [congrHom_trans, ← hγ, swapAut_conj]
      congr 1
      apply Units.ext
      have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right (hsq γ hγE₀)
      rw [coe_dualGL, coe_trvGL, hγinv, hγw, Matrix.transpose_add, Matrix.transpose_one,
        Matrix.transpose_vecMulVec]

omit [Finite K] [CharP K 2] in
theorem apply_symm_eq {V : Type*} [CommGroup V] (e : V ≃* PairMod K) (x : MulAut V)
    (w : PairMod K) : x (e.symm w) = e.symm (congrHom e x w) := by
  rw [congrHom_apply, MulEquiv.symm_apply_apply]

omit [Finite K] [CharP K 2] in
theorem eq_map_symm_of_map_eq {V : Type*} [CommGroup V] (e : V ≃* PairMod K) {J : Subgroup V}
    {J' : Subgroup (PairMod K)} (h : J.map e.toMonoidHom = J') :
    J = J'.map e.symm.toMonoidHom := by
  ext x
  constructor
  · intro hx
    exact ⟨e x, h ▸ ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    rw [← h] at hu
    obtain ⟨j, hj, rfl⟩ := hu
    simpa using hj

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {x y : M} (hx : x * x = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]

theorem not_V₁_le_zpowers (hK : Nat.card K = 2) (c : Fin 3 → K) :
    ¬ V₁ K ≤ Subgroup.zpowers (zvec c) := by
  intro hle
  obtain ⟨u, hu0, huc⟩ : ∃ u : Fin 3 → K, u ≠ 0 ∧ u ≠ c := by
    by_contra h
    push Not at h
    have hs : ∀ i : Fin 3, (Pi.single i (1 : K) : Fin 3 → K) ≠ 0 := fun i h' => by
      simpa using congrFun h' i
    have h01 := (h _ (hs 0)).trans (h _ (hs 1)).symm
    have := congrFun h01 0
    simp at this
  have hzz : zvec c * zvec c = 1 := by
    refine Prod.ext ?_ ?_ <;> apply Multiplicative.toAdd.injective <;>
      simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, toAdd_ofAdd, Prod.fst_one,
        Prod.snd_one, toAdd_one, zvec, CharTwo.add_self_eq_zero]
  rcases eq_one_or_eq_of_mem_zpowers hzz
      (hle (mem_V₁.mpr rfl : ((Multiplicative.ofAdd u, Multiplicative.ofAdd 0) : PairMod K) ∈
        V₁ K)) with h | h
  · apply hu0
    simpa using congrArg (fun y : PairMod K => Multiplicative.toAdd y.1) h
  · apply huc
    simpa [zvec] using congrArg (fun y : PairMod K => Multiplicative.toAdd y.1) h

theorem card_fixV_le_eight_inner {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) {E : Subgroup (MulAut V)}
    (hEH : E ≤ H) (hE2 : IsElemAbelian2 E) (hE4 : Nat.card E = 4) :
    Nat.card ↥(fixV E) ≤ 8 := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e.toEquiv
  have hmem : ∀ z ∈ E, congrHom e z ∈ pairSL K := fun z hz => by
    rw [← he]
    exact ⟨z, hEH hz, rfl⟩
  have hE'N : E.map (congrHom e) ≤ pairNorm K := by
    rintro _ ⟨z, hz, rfl⟩
    exact pairSL_le_pairNorm (hmem z hz)
  have hE'S : E.map (congrHom e) ≤ pairSub K := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨γ, -, hγz⟩ := hmem z hz
    rw [← hγz, pairHom_apply]
    exact pairAut_mem_pairSub _ _
  have h := card_fixV_le_eight_of_sub hK2 hE'N ((isElemAbelian2_map_congrHom e).mpr hE2)
    (by rw [card_map_congrHom, hE4]) hE'S
  rw [fixV_map_congrHom, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at h
  exact h

theorem H4_SL3One_fix {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) {E : Subgroup (MulAut V)}
    (hEH : E ≤ H) (hE2 : IsElemAbelian2 E) (hE4 : Nat.card E = 4) :
    ∃ z : V, z ≠ 1 ∧ (z ∈ V₁ ∨ z ∈ V₁.map φ.toMonoidHom) ∧ (∀ x ∈ E, x z = z) ∧
      (∀ x ∈ E, ∀ w ∈ E3.gammaCheck 1 E, x w * w⁻¹ = 1 ∨ x w * w⁻¹ = z) ∧
      ∃ Vi Y : Subgroup V, z ∈ Vi ∧ ¬ Vi ≤ Subgroup.zpowers z ∧
        E3.gammaCheck 1 E ≤ Vi ⊔ Y ∧ Y ≠ ⊥ ∧
        (∀ J : Subgroup V, J ≤ Vi → z ∈ J → ¬ J ≤ Subgroup.zpowers z →
          (∀ h ∈ H, h z = z → ∀ v ∈ J, h v ∈ J) → J = Vi) ∧
        (∀ J : Subgroup V, J ≤ Y → J ≠ ⊥ → (∀ h ∈ H, h z = z → ∀ v ∈ J, h v ∈ J) → J = Y) ∧
        ∀ p ∈ Subgroup.normalizer (H : Set (MulAut V)), p z = z →
          (∀ v ∈ Vi, p v ∈ Vi) ∧ ∀ y ∈ Y, p y ∈ Y := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨e₀, he₀⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e₀.toEquiv
  obtain ⟨e, he, c, hc, hcen⟩ := exists_center_model hK2 he₀ hEH hE2 hE4
  set E' := E.map (congrHom e) with hE'def
  set z : V := e.symm (zvec c) with hzdef
  have hez : e z = zvec c := by rw [hzdef, MulEquiv.apply_symm_apply]
  have hxE' : ∀ x ∈ E, congrHom e x ∈ E' := fun x hx => ⟨x, hx, rfl⟩
  have hHmodel : ∀ γ ∈ StatedSL 3 K, ∃ h ∈ H, congrHom e h = pairHom γ := by
    intro γ hγ
    have : pairHom γ ∈ H.map (congrHom e) := by
      rw [he]
      exact ⟨γ, hγ, rfl⟩
    obtain ⟨h, hh, hhγ⟩ := this
    exact ⟨h, hh, hhγ⟩
  have hHz : ∀ h : MulAut V, congrHom e h (zvec c) = zvec c → h z = z := by
    intro h hh
    rw [hzdef, apply_symm_eq, hh]
  obtain ⟨π, hπ⟩ := hreal'
  have hinv₁ : Pair.IsInv H V₁ := fun l hl w hw => hπ.2.2.2.1 ⟨l, hl⟩ w hw
  have hinv₂ : Pair.IsInv H (V₁.map φ.toMonoidHom) := Pair.isInv_map hφ hinv₁
  have hmodel : ∀ {W : Subgroup V}, Pair.IsInv H W →
      Pair.IsInv (pairSL K) (W.map e.toMonoidHom) := by
    intro W hW l hl
    rw [← he] at hl
    obtain ⟨h, hh, rfl⟩ := hl
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨h w, hW h hh w hw, ?_⟩
    simp [congrHom_apply]
  have hcardV : Nat.card V = 2 ^ 6 := (Nat.card_congr e.toEquiv).trans (card_pairMod_two hK2)
  have htopbot : (⊤ : Subgroup V) ≠ ⊥ := by
    intro h
    have h1 : Nat.card (⊤ : Subgroup V) = Nat.card (⊥ : Subgroup V) := by rw [h]
    rw [Subgroup.card_top, Subgroup.card_bot, hcardV] at h1
    norm_num at h1
  have hφinj : Function.Injective φ.toMonoidHom := φ.injective
  have hφsurj : Function.Surjective φ.toMonoidHom := φ.surjective
  have hne : ∀ {W : Subgroup V}, (W = V₁ ∨ W = V₁.map φ.toMonoidHom) →
      W.map e.toMonoidHom ≠ ⊥ ∧ W.map e.toMonoidHom ≠ ⊤ := by
    intro W hW
    have hV₁0 : V₁ ≠ ⊥ := by
      intro h
      apply htopbot
      rw [← hsup, h, Subgroup.map_bot, sup_bot_eq]
    have hV₁T : V₁ ≠ ⊤ := by
      intro h
      apply htopbot
      rw [← hinf, h, Subgroup.map_top_of_surjective _ hφsurj, inf_top_eq]
    have hW0 : W ≠ ⊥ := by
      rcases hW with rfl | rfl
      · exact hV₁0
      · exact (Subgroup.map_eq_bot_iff_of_injective V₁ hφinj).not.mpr hV₁0
    have hWT : W ≠ ⊤ := by
      rcases hW with rfl | rfl
      · exact hV₁T
      · intro h
        apply hV₁T
        rw [← Subgroup.comap_map_eq_self_of_injective hφinj V₁, h, Subgroup.comap_top]
    refine ⟨(Subgroup.map_eq_bot_iff_of_injective W (f := e.toMonoidHom) e.injective).not.mpr
      hW0, fun h => hWT ?_⟩
    have h1 := eq_map_symm_of_map_eq e h
    rw [h1, Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]
  have hW : ∀ {W : Subgroup V}, (W = V₁ ∨ W = V₁.map φ.toMonoidHom) →
      W.map e.toMonoidHom = SL3Pair.V₁ K ∨ W.map e.toMonoidHom = V₂ K := by
    intro W hW
    have hinvW : Pair.IsInv H W := by
      rcases hW with rfl | rfl
      · exact hinv₁
      · exact hinv₂
    obtain ⟨h0, hT⟩ := hne hW
    rcases isInv_eq (hmodel hinvW) with h | h | h | h
    · exact absurd h h0
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hT
  have hinfe : (V₁.map e.toMonoidHom) ⊓ ((V₁.map φ.toMonoidHom).map e.toMonoidHom) = ⊥ := by
    rw [← Subgroup.map_inf V₁ (V₁.map φ.toMonoidHom) e.toMonoidHom e.injective, hinf,
      Subgroup.map_bot]
  have hzV : z ∈ V₁ ∨ z ∈ V₁.map φ.toMonoidHom := by
    have hV₁e := hW (W := V₁) (Or.inl rfl)
    have hV₂e := hW (W := V₁.map φ.toMonoidHom) (Or.inr rfl)
    have hz1 : zvec c ∈ SL3Pair.V₁ K := zvec_mem_V₁ c
    have hcases : V₁.map e.toMonoidHom = SL3Pair.V₁ K ∨
        (V₁.map φ.toMonoidHom).map e.toMonoidHom = SL3Pair.V₁ K := by
      rcases hV₁e with h | h
      · exact Or.inl h
      · rcases hV₂e with h' | h'
        · exact Or.inr h'
        · exfalso
          rw [h, h', inf_idem] at hinfe
          exact isIrr_V₂.1 hinfe
    rcases hcases with h | h
    · left
      rw [eq_map_symm_of_map_eq e h]
      exact ⟨zvec c, hz1, rfl⟩
    · right
      rw [eq_map_symm_of_map_eq e h]
      exact ⟨zvec c, hz1, rfl⟩
  have hrk : rk ↥E = 2 := by
    unfold rk
    rw [hE4, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hWc : E3.gammaCheck 1 E ≤ (wSub c).comap e.toMonoidHom := by
    unfold E3.gammaCheck
    refine iSup_le fun X => iSup_le fun hXE => iSup_le fun hX1 => ?_
    have hX0 : X ≠ ⊥ := by
      rintro rfl
      rw [mQuot_bot_eq_rk, hrk] at hX1
      omega
    intro v hv
    have hmem : e v ∈ fixV (X.map (congrHom e)) := by
      rw [fixV_map_congrHom]
      exact ⟨v, hv, rfl⟩
    exact fixV_le_wSub hcen (Subgroup.map_mono hXE)
      ((Subgroup.map_eq_bot_iff_of_injective _ (congrHom_injective e)).not.mpr hX0) hmem
  refine ⟨z, fun h => zvec_ne_one hc (by rw [← hez, h, map_one]), hzV, fun x hx => ?_,
    fun x hx w hw => ?_, (SL3Pair.V₁ K).map e.symm.toMonoidHom, (ySub c).map e.symm.toMonoidHom,
    ⟨zvec c, zvec_mem_V₁ c, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨φ', hφ', hxe⟩ := hcen _ (hxE' x hx)
    exact hHz x (by rw [hxe, trv_fix_zvec])
  ·
    have h1 := comm_wSub hK2 hcen (hxE' x hx) (hWc hw)
    have h2 : (MulAut.congr e x) (e w) = e (x w) := by
      change e (x (e.symm (e w))) = e (x w)
      rw [MulEquiv.symm_apply_apply]
    simp only [MulEquiv.coe_toMonoidHom] at h1
    rw [h2, ← map_inv, ← map_mul] at h1
    rcases h1 with h | h
    · left
      exact e.injective (by rw [h, map_one])
    · right
      exact e.injective (by rw [h, hez])
  ·
    intro h
    apply not_V₁_le_zpowers hK2 c
    intro u hu
    have h1 := h ⟨u, hu, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.symm.injective ?_⟩
    rw [map_zpow]
    exact hk
  ·
    intro w hw
    have h1 : e w ∈ SL3Pair.V₁ K ⊔ ySub c := wSub_le_sup c (hWc hw)
    have h2 : e.symm (e w) ∈ (SL3Pair.V₁ K ⊔ ySub c).map e.symm.toMonoidHom := ⟨e w, h1, rfl⟩
    rw [Subgroup.map_sup, MulEquiv.symm_apply_apply] at h2
    exact h2
  ·
    have hnt : Nontrivial {k : Fin 3 → K // c ⬝ᵥ k = 0} :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [card_orth hc, hK2]; norm_num)
    obtain ⟨⟨f, hf⟩, hf0⟩ := exists_ne (⟨0, dotProduct_zero c⟩ : {k : Fin 3 → K // c ⬝ᵥ k = 0})
    have hfne : f ≠ 0 := fun h => hf0 (Subtype.ext h)
    have hmem : ((Multiplicative.ofAdd 0, Multiplicative.ofAdd f) : PairMod K) ∈ ySub c :=
      mem_ySub.mpr ⟨by simpa using hf, rfl⟩
    intro hbot
    have h1 : e.symm (Multiplicative.ofAdd 0, Multiplicative.ofAdd f) ∈
        (ySub c).map e.symm.toMonoidHom := ⟨_, hmem, rfl⟩
    rw [hbot, Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at h1
    apply hfne
    have h2 := congrArg (fun y : PairMod K => Multiplicative.toAdd y.2) h1
    simpa using h2
  ·
    intro J hJ hzJ hJz hinvJ
    apply eq_map_symm_of_map_eq e
    refine eq_V₁_of_inv hK2 hc ?_ ⟨z, hzJ, hez⟩ ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hJ hj
      simpa using hu
    · intro h
      apply hJz
      intro j hj
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h ⟨j, hj, rfl⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective ?_⟩
      rw [map_zpow, hez]
      exact hk
    · intro γ hγ hγz x hx
      obtain ⟨j, hj, rfl⟩ := hx
      obtain ⟨h, hh, hhγ⟩ := hHmodel γ hγ
      refine ⟨h j, hinvJ h hh (hHz h (by rw [hhγ, hγz])) j hj, ?_⟩
      rw [← hhγ, congrHom_apply]
      simp
  ·
    intro J hJ hJ0 hinvJ
    apply eq_map_symm_of_map_eq e
    refine eq_ySub_of_inv hK2 hc ?_
      ((Subgroup.map_eq_bot_iff_of_injective J (f := e.toMonoidHom) e.injective).not.mpr hJ0) ?_
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hJ hj
      simpa using hu
    · intro γ hγ hγz x hx
      obtain ⟨j, hj, rfl⟩ := hx
      obtain ⟨h, hh, hhγ⟩ := hHmodel γ hγ
      refine ⟨h j, hinvJ h hh (hHz h (by rw [hhγ, hγz])) j hj, ?_⟩
      rw [← hhγ, congrHom_apply]
      simp
  ·
    intro p hp hpz
    have hpN : congrHom e p ∈ pairNorm K := by
      have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
          Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
            Set (MulAut (PairMod K))) :=
        Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
      rw [pairNorm, ← he, ← h3]
      exact ⟨p, hp, rfl⟩
    have hpz' : congrHom e p (zvec c) = zvec c := by
      rw [congrHom_apply, ← hzdef, hpz, hez]
    obtain ⟨-, hp1, hp2⟩ := mem_pairSL_of_fix hK2 hc hpN hpz'
    refine ⟨?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨_, hp1 u hu, (apply_symm_eq e p u).symm⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨_, hp2 u hu, (apply_symm_eq e p u).symm⟩

end SL3One

end H

end CFSG.Quasithin
