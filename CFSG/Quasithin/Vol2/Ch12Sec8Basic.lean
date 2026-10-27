module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Vol2.Ch12Sec8Setup
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open

section Aut

variable {V : Type*} [Group V] [Finite V]

theorem mulAut_eq_one_of_fix_of_odd (hV : Nat.card V = 4) (hsq : ∀ v : V, v * v = 1)
    {σ : MulAut V} {z : V} (hz : z ≠ 1) (hσz : σ z = z) {m : ℕ} (hm : Odd m) (hσm : σ ^ m = 1) :
    σ = 1 := by
  classical
  ext v
  rw [MulAut.one_apply]
  by_cases hv1 : v = 1
  · rw [hv1, map_one]
  by_cases hvz : v = z
  · rw [hvz, hσz]
  have hvz1 : v * z ≠ 1 := by
    intro h
    apply hvz
    have : v = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_left (hsq z)]
  have hvzz : v * z ≠ z := fun h => hv1 (by simpa using h)
  have hvzv : v * z ≠ v := fun h => hz (by simpa using h)
  have hcases : ∀ w : V, w = 1 ∨ w = z ∨ w = v ∨ w = v * z := by
    intro w
    by_contra hw
    push Not at hw
    have hcard : (({1, z, v, v * z, w} : Finset V)).card = 5 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair]
      · exact hw.2.2.2.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hvzv.symm, fun h => hw.2.2.1 h.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hvz h.symm, hvzz.symm, fun h => hw.2.1 h.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hz.symm, fun h => hv1 h.symm, hvz1.symm, fun h => hw.1 h.symm⟩
    have : Fintype V := Fintype.ofFinite V
    have hle := Finset.card_le_univ ({1, z, v, v * z, w} : Finset V)
    rw [hcard, ← Nat.card_eq_fintype_card, hV] at hle
    omega
  have hσv1 : σ v ≠ 1 := fun h => hv1 (by simpa using h)
  have hσvz : σ v ≠ z := fun h => hvz (σ.injective (h.trans hσz.symm))
  rcases hcases (σ v) with h | h | h | h
  · exact absurd h hσv1
  · exact absurd h hσvz
  · exact h
  ·
    exfalso
    have hpow : ∀ k : ℕ, (σ ^ k) v = v * z ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, h, map_pow, hσz, pow_succ']
        group
    have hzm : z ^ m = z := by
      obtain ⟨k, hk⟩ := hm
      have hz2 : z ^ 2 = 1 := by rw [sq]; exact hsq z
      rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul]
    have := hpow m
    rw [hσm, MulAut.one_apply, hzm] at this
    exact hvzv this.symm

end Aut

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

omit [Finite G] in
private theorem c1283_conjAct_coe (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : V) :
    ((conjAct V g x : V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

omit [Finite G] in
private theorem c1283_mem_centralizer_of_conjAct_eq_one {V : Subgroup G}
    {g : Subgroup.normalizer (V : Set G)} (hg : conjAct V g = 1) :
    (g : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := congrArg (fun φ : MulAut V => ((φ ⟨x, hx⟩ : V) : G)) hg
  simp only [c1283_conjAct_coe, MulAut.one_apply] at this
  calc x * (g : G) = ((g : G) * x * (g : G)⁻¹) * g := by rw [this]
    _ = g * x := by group

@[expose] def IsHz (T M L H : Subgroup G) : Prop :=
  InH (lOne L (quasithinOmegaOneCenter T) ⊔ T) H ∧
    H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) ∧ ¬ H ≤ M

namespace Hyp1281Two

theorem isTwoReducedIn (h : Hyp1281Two G T M L) :
    IsTwoReducedIn M (VZ T M) ∧ VZ T M ≤ T := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ h.inM.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtke.2.1 M h.inM.1.1 ⟨S, hSM⟩
  have hVred : IsTwoReducedIn M (VZ T M) := by
    have := isTwoReducedIn_conjClosure M S hSM hF le_rfl
    rwa [hS] at this
  refine ⟨hVred, ?_⟩
  have := le_sylow_of_isTwoReducedIn S hSM hVred
  rwa [hS] at this

theorem omegaOneCenter_ne_bot (h : Hyp1281Two G T M L) : quasithinOmegaOneCenter T ≠ ⊥ := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hne : T ≠ ⊥ := by
    intro hT
    apply h.not_le
    intro g _
    exfalso
    have hZ : quasithinOmegaOneCenter T = ⊥ := by
      rw [eq_bot_iff]
      exact (quasithinOmegaOneCenter_le_center T).trans (inf_le_left.trans hT.le)
    have hV : VZ T M = ⊥ := by
      rw [eq_bot_iff]
      refine conjClosure_le fun x _ z hz => ?_
      rw [hZ, Subgroup.mem_bot] at hz
      rw [hz, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    have h4 := h.rank_two
    rw [hV, Subgroup.card_bot] at h4
    omega
  exact quasithinOmegaOneCenter_ne_bot (hS ▸ S.isPGroup') hne

theorem not_le_centralizer (h : Hyp1281Two G T M L) :
    ¬ T ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro hTV
  obtain ⟨hVred, hVT⟩ := h.isTwoReducedIn
  have hVZ : VZ T M ≤ quasithinOmegaOneCenter T := by
    intro v hv
    apply Subgroup.subset_closure
    refine ⟨⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, hVred.2.2.1.2 v hv⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hTV ht)) v hv).symm
  have hVeq : VZ T M = quasithinOmegaOneCenter T := le_antisymm hVZ (le_conjClosure _ _)
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) :=
    h.sylow.1.to_le ((quasithinOmegaOneCenter_le_center T).trans inf_le_left)
  have hMN : M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hVeq ▸ hVred.2.1
  have hNM : Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) = M :=
    h.inM.1.2 _ ⟨_, h.omegaOneCenter_ne_bot, hZ2, rfl⟩ hMN
  exact h.not_le (hNM ▸ Subgroup.centralizer_le_normalizer _)

theorem card_omegaOneCenter (h : Hyp1281Two G T M L) :
    Nat.card (quasithinOmegaOneCenter T) = 2 := by
  have hZW : quasithinOmegaOneCenter T ≤ VZ T M ⊓ Subgroup.centralizer (T : Set G) :=
    le_inf (le_conjClosure _ _) ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)
  have hWne : VZ T M ⊓ Subgroup.centralizer (T : Set G) ≠ VZ T M := by
    intro hWV
    apply h.not_le_centralizer
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ VZ T M ⊓ Subgroup.centralizer (T : Set G) := by
      rw [hWV]
      exact hv
    exact ((Subgroup.mem_centralizer_iff.mp hv'.2) t ht).symm
  have hW2 := card_le_two_of_le_of_ne_of_card_four inf_le_left hWne h.rank_two
  have hZdvd := Subgroup.card_dvd_of_le hZW
  have hZ1 : Nat.card (quasithinOmegaOneCenter T) ≠ 1 := fun h1 =>
    h.omegaOneCenter_ne_bot (Subgroup.card_eq_one.mp h1)
  have hWpos : 0 < Nat.card ↥(VZ T M ⊓ Subgroup.centralizer (T : Set G)) := Nat.card_pos
  have hZpos : 0 < Nat.card (quasithinOmegaOneCenter T) := Nat.card_pos
  have := Nat.le_of_dvd hWpos hZdvd
  omega

theorem lOne_eq_bot (h : Hyp1281Two G T M L) : lOne L (quasithinOmegaOneCenter T) = ⊥ := by
  obtain ⟨hVred, -⟩ := h.isTwoReducedIn
  have hZ2 := h.card_omegaOneCenter
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨⟨hxL, hxN⟩, hxodd⟩ := hx
  have hxM : x ∈ M := h.le hxL
  have hxNV : x ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 hxM
  have hxC : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    normalizer_le_centralizer_of_card_two hZ2 hxN
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : quasithinOmegaOneCenter T)).mp hZ2
  obtain ⟨z, hzZ⟩ : ∃ z : quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      have := hall ⟨w, hw⟩
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this)
  have hzV : (z : G) ∈ VZ T M := le_conjClosure _ _ z.2
  set σ : MulAut (VZ T M) := conjAct (VZ T M) ⟨x, hxNV⟩ with hσ
  have hσz : σ ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
    apply Subtype.ext
    rw [hσ, c1283_conjAct_coe]
    show x * (z : G) * x⁻¹ = z
    have := (Subgroup.mem_centralizer_iff.mp hxC) z z.2
    rw [← this, mul_inv_cancel_right]
  have hσm : σ ^ orderOf x = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨x, hxNV⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ orderOf x = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hsq : ∀ v : VZ T M, v * v = 1 := fun v =>
    Subtype.ext (by simpa [sq] using hVred.2.2.1.2 v v.2)
  have hσ1 := mulAut_eq_one_of_fix_of_odd h.rank_two hsq
    (z := ⟨z, hzV⟩)
    (fun h1 => hzZ (Subtype.ext (show (z : G) = 1 from congrArg (fun w : VZ T M => (w : G)) h1)))
    hσz hxodd hσm
  have hxCV : x ∈ Subgroup.centralizer (VZ T M : Set G) :=
    c1283_mem_centralizer_of_conjAct_eq_one (g := ⟨x, hxNV⟩) hσ1
  have hxO : x ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← h.centralizer]
    exact ⟨Subgroup.mem_sup_left hxL, hxCV⟩
  obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨x, hxO⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact Subgroup.mem_bot.mpr hj
  · exfalso
    rw [hj] at hxodd
    exact (Nat.not_even_iff_odd.mpr hxodd) (by simp [pow_succ])

theorem isHz_iff (h : Hyp1281Two G T M L) {H : Subgroup G} :
    IsHz T M L H ↔
      InH T H ∧ H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) ∧ ¬ H ≤ M := by
  rw [IsHz, h.lOne_eq_bot, bot_sup_eq]

theorem isHz_normalizer (h : Hyp1281Two G T M L) :
    IsHz T M L (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) := by
  rw [h.isHz_iff]
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) :=
    h.sylow.1.to_le ((quasithinOmegaOneCenter_le_center T).trans inf_le_left)
  have hTN : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (Subgroup.le_centralizer_iff.mp
      ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨⟨hTN, ?_⟩, le_rfl, fun hle => h.not_le
    ((Subgroup.centralizer_le_normalizer _).trans hle)⟩
  intro hb
  apply h.omegaOneCenter_ne_bot
  exact le_bot_iff.mp (hb ▸ LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    Subgroup.le_normalizer le_rfl hZ2 |>.trans le_rfl)

theorem almostSpecialHyp (h : Hyp1281Two G T M L) {H : Subgroup G} (hH : IsHz T M L H) :
    AlmostSpecialHyp (VZ T M) (quasithinOmegaOneCenter T) L T H := by
  obtain ⟨hVred, hVT⟩ := h.isTwoReducedIn
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  rw [h.isHz_iff] at hH
  have hTM : T ≤ M := h.inM.2
  have hTN : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (Subgroup.le_centralizer_iff.mp
      ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hlOne : lOne L (quasithinOmegaOneCenter T) = ⊥ := h.lOne_eq_bot
  refine
    { elemAbelian := hVred.2.2.1
      ne_bot := h.omegaOneCenter_ne_bot
      le_V := le_conjClosure _ _
      oTwo_eq := h.residual.symm
      V_le_T := hVT
      T_le_normV₁ := hTN
      T_le_normV := hTM.trans hVred.2.1
      T_le_normL := hTM.trans h.normal
      sylow_LT := ?_
      H_le := hH.2.1
      lOne_sup_le := ?_
      sylow_H := ?_
      charTwo := ?_
      irred := ?_ }
  · have := isSylowTwoOf_of_sylow S (hS ▸ (le_sup_right : T ≤ L ⊔ T))
    rwa [hS] at this
  · rw [hlOne, bot_sup_eq]
    exact hH.1.1
  · have := isSylowTwoOf_of_sylow S (hS ▸ hH.1.1)
    rwa [hS] at this
  · exact charTwo_of_inH h.qtke.2.1 S (hS ▸ hH.1)
  ·
    rw [hlOne, bot_sup_eq]
    have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
    have hZ2 := h.card_omegaOneCenter
    refine ⟨lt_of_le_of_ne hZV fun heq => by
        have := h.rank_two
        rw [← heq, hZ2] at this
        omega, hTM.trans hVred.2.1, hTN, fun W hZW hWV _ => ?_⟩
    by_cases hWV' : W = VZ T M
    · exact Or.inr hWV'
    · left
      have hW2 := card_le_two_of_le_of_ne_of_card_four hWV hWV' h.rank_two
      exact (Subgroup.eq_of_le_of_card_ge hZW (by rw [hZ2]; exact hW2)).symm

theorem lemma_12_8_4_two (h : Hyp1281Two G T M L) {H : Subgroup G} (hH : IsHz T M L H) :
    tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) ≤
        omegaOneCenterOf (tildeOf (quasithinOmegaOneCenter T) (pCoreOf 2 H)) ∧
      IsTwoReducedIn (tildeOf (quasithinOmegaOneCenter T) H)
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H)) :=
  ⟨(h.almostSpecialHyp hH).G22_one.2, (h.almostSpecialHyp hH).G22_four⟩

theorem lemma_12_8_4_three (h : Hyp1281Two G T M L) {H : Subgroup G} (hH : IsHz T M L H) :
    frattiniOf (conjClosure (VZ T M) H) ≤ quasithinOmegaOneCenter T :=
  (h.almostSpecialHyp hH).G22_two

end Hyp1281Two

end CFSG.Quasithin
