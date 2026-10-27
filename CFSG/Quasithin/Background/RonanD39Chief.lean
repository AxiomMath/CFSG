module

public import CFSG.Quasithin.Background.RonanD39Count
public import CFSG.Quasithin.EmptyFaithful.S153ZQ

public section

namespace CFSG.Quasithin.RonanD39

open scoped Pointwise
open CFSG.Open CFSG.Quasithin.Z391 CFSG.QuasithinUnique

section Pull

variable {S G : Type*} [Group S] [Group G] {Q₁ Q₂ : Type*} [CommGroup Q₁] [CommGroup Q₂]
  [MulDistribMulAction S Q₁] [MulDistribMulAction G Q₂]

theorem isInv_comap_of_equivariant (θ : Q₁ →* Q₂) (τ : S → G)
    (hτ : ∀ (s : S) (x : Q₁), θ (s • x) = τ s • θ x) {J : Subgroup Q₂} (hJ : XMod.IsInv G J) :
    XMod.IsInv S (J.comap θ) := by
  intro s x hx
  show θ (s • x) ∈ J
  rw [hτ]
  exact hJ _ _ hx

theorem isIrrSec_comap_of_surj (θ : Q₁ →* Q₂) (hθ : Function.Surjective θ) (σ : G → S)
    (hσ : ∀ (g : G) (x : Q₁), θ (σ g • x) = g • θ x) {Y Z : Subgroup Q₂}
    (h : XMod.IsIrrSec G Y Z) : XMod.IsIrrSec S (Y.comap θ) (Z.comap θ) := by
  refine ⟨lt_of_le_of_ne (Subgroup.comap_mono h.1.le) fun he => h.1.ne ?_, fun J hJ hYJ hJZ => ?_⟩
  · have := congrArg (Subgroup.map θ) he
    rwa [Subgroup.map_comap_eq_self_of_surjective hθ,
      Subgroup.map_comap_eq_self_of_surjective hθ] at this
  · have hJ' : XMod.IsInv G (J.map θ) := by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨σ g • x, hJ _ x hx, hσ g x⟩
    have h1 : Y ≤ J.map θ := by
      have := Subgroup.map_mono (f := θ) hYJ
      rwa [Subgroup.map_comap_eq_self_of_surjective hθ] at this
    have h2 : J.map θ ≤ Z := by
      have := Subgroup.map_mono (f := θ) hJZ
      rwa [Subgroup.map_comap_eq_self_of_surjective hθ] at this
    have hkJ : θ.ker ≤ J := by
      refine le_trans ?_ hYJ
      intro x hx
      change θ x ∈ Y
      rw [MonoidHom.mem_ker.1 hx]
      exact Y.one_mem
    have hJeq : (J.map θ).comap θ = J := by
      rw [Subgroup.comap_map_eq, sup_eq_left.2 hkJ]
    rcases h.2 _ hJ' h1 h2 with h3 | h3
    · left
      rw [← hJeq, h3]
    · right
      rw [← hJeq, h3]

end Pull

variable {W : Type} [CommGroup W] [Finite W]

theorem chief_bound {M T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M L T L V)
    (hVT : V = orbSup T V) {A : Subgroup (MulAut W)} (hA : IsA2 M A) (hAT : A ≤ T)
    (hA3 : commSeries A 3 = ⊥) (hAr : rAV A ≤ 2)
    (hAf : ∀ a ∈ A, (∀ x ∈ L, a * x = x * a) → a = 1) (htop : orbSup T V ≠ ⊤) {r : ℚ}
    (hr : qhatOf (autSec (L ⊔ T) V (fixV L)) = (r : WithTop ℚ)) :
    ∃ n : ℕ, (∃ N : Fin (n + 1) → Subgroup W, N 0 = fixV L ∧ N (Fin.last n) = ⊤ ∧
      ∀ i : Fin n, XMod.IsInv ↥L (N i.castSucc) ∧ XMod.IsInv ↥L (N i.succ) ∧
        XMod.IsIrrSec ↥L (N i.castSucc) (N i.succ)) ∧ (n : ℚ) * r ≤ 2 := by
  have hexp := hD.hyp.exp
  have hq : CFSG.IsQuasisimple ↥L := hD.hyp.quasi
  have hTn : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    calc T ≤ Subgroup.normalizer (conjClosure L T : Set (MulAut W)) := le_normalizer_conjClosure L T
      _ = Subgroup.normalizer (L : Set (MulAut W)) := by rw [← hD.hyp.Mp_eq]
  have hGN : L ⊔ T ≤ Subgroup.normalizer (L : Set (MulAut W)) := sup_le Subgroup.le_normalizer hTn
  have hN : ∀ g ∈ L ⊔ T, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hGN hg)) l).1 hl
  have hG := n1_sup_le_stabSub_sec hD.hyp
  rw [← hVT] at hG
  have hGV : L ⊔ T ≤ stabSub V := hG.trans inf_le_left
  have hGC : L ⊔ T ≤ stabSub (V ⊓ fixV L) := hG.trans inf_le_right
  obtain ⟨-, hVcomm, hVlt, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hcommV : commV L = ⊤ := Z391.commV_eq_top hMn hVcomm hD.hyp.gen
  have hntV : ¬ L ≤ centSec V (V ⊓ fixV L) := by
    intro h
    have h1 : commSub V L ≤ V ⊓ fixV L := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact (h hx).2 w hw
    rw [hVcomm] at h1
    exact lt_irrefl _ (lt_of_lt_of_le hVlt h1)
  have hq' : (r : WithTop ℚ) = qhatOf (autSec (L ⊔ T) V (V ⊓ fixV L)) := by
    have e : (V ⊓ fixV L).subgroupOf V = (fixV L).subgroupOf V := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    have key : ∀ {U₁ U₂ : Subgroup ↥V}, U₁ = U₂ →
        qhatOf (autQuot (autSub (L ⊔ T) V) U₁) = qhatOf (autQuot (autSub (L ⊔ T) V) U₂) := by
      intro U₁ U₂ h
      subst h
      rfl
    rw [← hr]
    exact (key e).symm
  have hMpM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hTX : M ≤ Subgroup.normalizer (L : Set (MulAut W)) := hD.hyp.Mp_normal
  have hWM : ∀ t ∈ M, ∀ w ∈ (⊤ : Subgroup W), t • w ∈ (⊤ : Subgroup W) := fun _ _ _ _ => trivial
  let instQ : MulDistribMulAction ↥M (W ⧸ modFix L (⊤ : Subgroup W)) := quotAct hTX hWM
  set π : W →* (W ⧸ modFix L (⊤ : Subgroup W)) :=
    QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w) := fun g w => rfl
  have hker : π.ker = fixV L := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (fixed_eq_inf_fixV L ⊤).trans (top_inf_eq _)
  have hQ : ∀ x : W ⧸ modFix L (⊤ : Subgroup W), x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
  have hirr := (isIrr_tilde hD.hyp.irr).1
  let φ : ↥(L.subgroupOf M) → ↥L := fun l => ⟨((l : ↥M) : MulAut W), l.2⟩
  have hφ : Function.Surjective φ := fun a => ⟨⟨⟨(a : MulAut W), hMpM a.2⟩, a.2⟩, rfl⟩
  have hact : ∀ (l : ↥(L.subgroupOf M)) (x : W ⧸ modFix L (⊤ : Subgroup W)), l • x = φ l • x := by
    intro l x
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  have hVΛ : XMod.IsIrr ↥(L.subgroupOf M) (tilde L (⊤ : Subgroup W) V) :=
    Z391.isIrr_of_surj φ hφ hact hirr
  have hΛ : ∀ g : ↥M, ∀ l ∈ L.subgroupOf M, g * l * g⁻¹ ∈ L.subgroupOf M :=
    fun g l hl => hMn (g : MulAut W) g.2 (l : MulAut W) hl
  have hT : IsSylowTwoOf (T.subgroupOf M) (⊤ : Subgroup ↥M) :=
    Z391.isSylowTwoOf_subgroupOf_top hD.hyp.sylow
  have hAT₀ : A.subgroupOf M ≤ T.subgroupOf M := fun x hx => hAT hx
  have hAc : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x :=
    fun x hx y hy => Subtype.ext (hA.2.2.1 _ hx _ hy)
  have hA2' : ∀ x ∈ A.subgroupOf M, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using hA.2.2.2 (x : MulAut W) hx)
  have hVT₀ : ∀ t ∈ T.subgroupOf M,
      t • tilde L (⊤ : Subgroup W) V = tilde L (⊤ : Subgroup W) V := by
    intro t ht
    have h1 : t • tilde L (⊤ : Subgroup W) V = tilde L (⊤ : Subgroup W) ((t : MulAut W) • V) :=
      tilde_smul hTX hWM t V
    have h2 : (t : MulAut W) • V = V :=
      map_eq_of_mem_stabSub (hGV ((le_sup_right : T ≤ L ⊔ T) ht))
    rw [h1, h2]
  have hgen' : (⨆ g : ↥M, g • tilde L (⊤ : Subgroup W) V) = ⊤ := by
    have e : ∀ g : ↥M, g • tilde L (⊤ : Subgroup W) V =
        tilde L (⊤ : Subgroup W) ((g : MulAut W) • V) := fun g => tilde_smul hTX hWM g V
    rw [iSup_congr e, ← tilde_biSup M V]
    have : (⨆ y ∈ M, y • V) = ⊤ := hD.hyp.gen
    rw [this]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hne : tilde L (⊤ : Subgroup W) V ≠ ⊤ := by
    intro h
    have h1 : V ⊔ modFix L (⊤ : Subgroup W) = ⊤ := by
      rw [← comap_tilde, h, Subgroup.comap_top]
    have h2 : modFix L (⊤ : Subgroup W) = fixV L :=
      (fixed_eq_inf_fixV L ⊤).trans (top_inf_eq _)
    rw [h2] at h1
    have h3 : commSub (⊤ : Subgroup W) L = V := by
      rw [← h1, commSub_sup_fixV le_rfl, hVcomm]
    rw [← commV_eq_commSub, hcommV] at h3
    exact htop (hVT.symm.trans h3.symm)
  have hA₀A : (A.subgroupOf M).map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hrkA₀ : rk ↥(A.subgroupOf M) = rk ↥A := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv]
  have hrA : 0 < rk ↥A := hA.rk_pos
  have hA1 : A.subgroupOf M ≠ ⊥ := by
    intro h
    have : rk ↥(A.subgroupOf M) = 0 := by rw [h, rk_bot]
    omega
  have hAQ : Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≤
      2 * rk ↥(A.subgroupOf M) := by
    have hN1 := Z391.nB_top_le_rkIdx_fixV π hπsurj hπM (A.subgroupOf M)
    rw [hA₀A] at hN1
    have hN2 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by
      have h := hAr
      unfold rAV at h
      have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
      rwa [div_le_iff₀ hpos] at h
    have hN2' : rkIdx (fixV A) ≤ 2 * rk ↥A := by exact_mod_cast hN2
    rw [hrkA₀]
    omega
  have hqB : ∀ (g : ↥M) (A₁ : Subgroup ↥M), A₁ ≤ A.subgroupOf M →
      A₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ T.subgroupOf M →
      r * rk ↥A₁ ≤ (Z391.nB (A₁.map (MulAut.conj g⁻¹).toMonoidHom)
        (tilde L (⊤ : Subgroup W) V) : ℚ) := by
    intro g A₁ hA₁A hBT
    set B : Subgroup ↥M := A₁.map (MulAut.conj g⁻¹).toMonoidHom with hBdef
    set B' : Subgroup (MulAut W) := B.map M.subtype with hB'
    have hB'T : B' ≤ T := by
      rintro _ ⟨b, hb, rfl⟩
      exact hBT hb
    have hA₁' : A₁.map M.subtype ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      exact hA₁A ha
    have hB'eq : B' = (A₁.map M.subtype).map (MulAut.conj ((g : MulAut W)⁻¹)).toMonoidHom := by
      rw [hB', hBdef, Z391.map_subtype_conj]
      rfl
    have hhM : (g : MulAut W)⁻¹ ∈ M := M.inv_mem g.2
    have hmemB' : ∀ x ∈ B', ∃ a ∈ A, x = (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ := by
      intro x hx
      rw [hB'eq] at hx
      obtain ⟨y, ⟨a, ha, rfl⟩, rfl⟩ := hx
      exact ⟨(a : MulAut W), hA₁' ⟨a, ha, rfl⟩, rfl⟩
    have hB'ab : IsElemAbelian2 B' := by
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · obtain ⟨a, ha, rfl⟩ := hmemB' x hx
        obtain ⟨b, hb, rfl⟩ := hmemB' y hy
        have := hA.2.2.1 a ha b hb
        calc (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ *
              ((g : MulAut W)⁻¹ * b * ((g : MulAut W)⁻¹)⁻¹)
            = (g : MulAut W)⁻¹ * (a * b) * ((g : MulAut W)⁻¹)⁻¹ := by group
          _ = (g : MulAut W)⁻¹ * (b * a) * ((g : MulAut W)⁻¹)⁻¹ := by rw [this]
          _ = (g : MulAut W)⁻¹ * b * ((g : MulAut W)⁻¹)⁻¹ *
                ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) := by group
      · obtain ⟨a, ha, rfl⟩ := hmemB' x hx
        have := hA.2.2.2 a ha
        calc ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) ^ 2
            = (g : MulAut W)⁻¹ * (a * a) * ((g : MulAut W)⁻¹)⁻¹ := by rw [pow_two]; group
          _ = 1 := by rw [← pow_two, this]; group
    have hB'f : ∀ x ∈ B', (∀ y ∈ L, x * y = y * x) → x = 1 := by
      intro x hx hxc
      obtain ⟨a, ha, rfl⟩ := hmemB' x hx
      have ha1 : a = 1 := by
        refine hAf a ha (fun z hz => ?_)
        have hy : (g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹ ∈ L := hMn _ hhM z hz
        have e := hxc _ hy
        have e' : (g : MulAut W)⁻¹ * (a * z) * ((g : MulAut W)⁻¹)⁻¹ =
            (g : MulAut W)⁻¹ * (z * a) * ((g : MulAut W)⁻¹)⁻¹ := by
          calc (g : MulAut W)⁻¹ * (a * z) * ((g : MulAut W)⁻¹)⁻¹
              = (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ *
                  ((g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹) := by group
            _ = (g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹ *
                  ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) := e
            _ = (g : MulAut W)⁻¹ * (z * a) * ((g : MulAut W)⁻¹)⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel e')
      rw [ha1]
      group
    have hB'3 : commSeries B' 3 = ⊥ := by
      rw [hB'eq, Z391.commSeries_map_conj]
      have : commSeries (A₁.map M.subtype) 3 = ⊥ :=
        le_bot_iff.1 ((commSeries_mono hA₁' 3).trans hA3.le)
      rw [this, Subgroup.map_bot]
    have hGB' : B' ≤ L ⊔ T := hB'T.trans le_sup_right
    have hB'V : B' ≤ stabSub V := hGB'.trans hGV
    have hB'C : B' ≤ stabSub (V ⊓ fixV L) := hGB'.trans hGC
    have hf₂ : B' ⊓ centSec V (V ⊓ fixV L) = ⊥ :=
      Z391.inf_centSec_eq_bot hq le_sup_left hGB' hN hGV hGC hntV hB'f
    have hrkB' : rk ↥B' = rk ↥A₁ := by
      have h1 : rk ↥B' = rk ↥B := by
        unfold rk
        rw [hB', Subgroup.card_map_of_injective M.subtype_injective]
      rw [h1, hBdef]
      exact Z391.rk_map_conj A₁ g⁻¹
    by_cases hz : rk ↥A₁ = 0
    · rw [hz]
      simp
    · have hB'ne : B' ≠ ⊥ := by
        intro hbot
        apply hz
        rw [← hrkB', hbot, rk_bot]
      have hB'A2 : IsA2 (L ⊔ T) B' := ⟨hGB', hB'ne, hB'ab⟩
      have h1 := Z391.q_mul_rk_le hB'A2 hB'3 hB'V hB'C hf₂ hq'
      have h2 := Z391.rkIdx_fixV_autSec_le_nB π hπM B V
      rw [hker] at h2
      rw [hrkB'] at h1
      exact h1.trans (by exact_mod_cast h2)
  obtain ⟨k, hch, hk⟩ := chief_count hQ hΛ hT hAT₀ hAc hA2' hA1 hVΛ hVT₀ hgen' hne hAQ hqB
  obtain ⟨N, h0, hl, hs⟩ := hch.exists_series
  have hτ : ∀ (s : ↥L) (x : W), π (s • x) =
      (⟨⟨(s : MulAut W), hMpM s.2⟩, s.2⟩ : ↥(L.subgroupOf M)) • π x := fun _ _ => rfl
  have hσ : ∀ (l : ↥(L.subgroupOf M)) (x : W), π (φ l • x) = l • π x := fun _ _ => rfl
  refine ⟨k, ⟨fun i => (N i).comap π, ?_, ?_, fun i => ?_⟩, hk⟩
  · show (N 0).comap π = fixV L
    rw [h0, MonoidHom.comap_bot, hker]
  · show (N (Fin.last k)).comap π = ⊤
    rw [hl, Subgroup.comap_top]
  · obtain ⟨h1, h2, h3⟩ := hs i
    exact ⟨isInv_comap_of_equivariant π _ hτ h1, isInv_comap_of_equivariant π _ hτ h2,
      isIrrSec_comap_of_surj π hπsurj φ hσ h3⟩

end CFSG.Quasithin.RonanD39
