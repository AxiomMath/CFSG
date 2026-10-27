module

public import CFSG.Quasithin.MS93.S4L461A

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped Matrix commutatorElement

section Abstract

variable {S : Type*} [Group S] {F : Type} [Field F] {ρ : S →* SL3 F} {H : Subgroup S}
  {f : S → (Fin 3 → F)}

theorem exists_ker_cocycle_eq
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b)
    (hρH : ∀ g : SL3 F, ∃ a ∈ H, ρ a = g) {k₀ : S} (hk₀ : k₀ ∈ H) (hk₀1 : ρ k₀ = 1)
    (hne : f k₀ ≠ 0) (v : Fin 3 → F) : ∃ k ∈ H, ρ k = 1 ∧ f k = v := by
  by_cases hv : v = 0
  · exact ⟨1, H.one_mem, map_one ρ, by rw [hv]; exact cocycle_one hf⟩
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_e0_eq hne
  obtain ⟨g₂, hg₂⟩ := exists_mulVec_e0_eq hv
  obtain ⟨a, ha, hag⟩ := hρH (g₂ * g₁⁻¹)
  refine ⟨a * k₀ * a⁻¹, H.mul_mem (H.mul_mem ha hk₀) (H.inv_mem ha), ?_, ?_⟩
  · simp [hk₀1]
  · rw [cocycle_conj_ker hf ha hk₀ hk₀1, hag, ← hg₁, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right, hg₂]

theorem exists_coboundary_of_cocycle_of_ker [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b)
    (hρH : ∀ g : SL3 F, ∃ a ∈ H, ρ a = g) (hker : ∀ k ∈ H, ρ k = 1 → f k = 0) :
    ∃ n : Fin 3 → F, ∀ a ∈ H, f a = ((ρ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  choose pre hpreH hpre using hρH
  have hfib : ∀ a ∈ H, f (pre (ρ a)) = f a := by
    intro a ha
    have hk : a⁻¹ * pre (ρ a) ∈ H := H.mul_mem (H.inv_mem ha) (hpreH _)
    have hk1 : ρ (a⁻¹ * pre (ρ a)) = 1 := by rw [map_mul, map_inv, hpre, inv_mul_cancel]
    have := hf a ha _ hk
    rw [mul_inv_cancel_left, hker _ hk hk1, Matrix.mulVec_zero, add_zero] at this
    exact this
  set fs : SL3 F → (Fin 3 → F) := fun g => f (pre g) with hfs
  have hcoc : IsCocycle3 fs := by
    intro g₁ g₂
    have h12 : pre g₁ * pre g₂ ∈ H := H.mul_mem (hpreH g₁) (hpreH g₂)
    have := hfib _ h12
    rw [map_mul, hpre, hpre] at this
    simp only [hfs]
    rw [this, hf _ (hpreH g₁) _ (hpreH g₂), hpre]
  obtain ⟨n, hn⟩ := exists_coboundary_of_four_le hq hcoc
  refine ⟨n, fun a ha => ?_⟩
  rw [← hfib a ha]
  exact hn _

end Abstract

section Xvec

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] noncomputable def xvec {hTM : T ≤ M} {α : Vtx (puAmalgam hTM)} {F : Type} [Field F]
    {K : Subgroup (puAmalgam hTM).Universal} {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K (Uloc hTM L α) ⊥ ψ false 1)
    (x : (puAmalgam hTM).Universal) : Fin 3 → F :=
  natVecG hψ (uProj (Uloc hTM L α) (Zloc hTM L α) x)

variable (h : PUHyp M T L) (hU : IsSL3U M T L)
include h hU

theorem uloc_inf_zloc_of_isSL3U (α : Vtx (puAmalgam h.le)) :
    Uloc h.le L α ⊓ Zloc h.le L α = ⊥ := by
  rw [Uloc, Zloc, ← puTrans_inf, inf_comm, hU.2.1, puTrans, Subgroup.bot_subgroupOf, transN_bot]

theorem xm_eq_uloc_sup_zloc_of_isSL3U {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    XM _ α = Uloc h.le L α ⊔ Zloc h.le L α := by
  rw [h.xm_eq hα, Uloc, Zloc, ← puTrans_sup h.le (Uq_le h.L_le) Zq_le, sup_comm, ← hU.1]

theorem uProj_xm {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ XM (puAmalgam h.le) α) :
    uProj (Uloc h.le L α) (Zloc h.le L α) x ∈ Uloc h.le L α ∧
      (uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x ∈ Zloc h.le L α := by
  refine uProj_spec ?_
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Uloc h.le L α) (Zloc h.le L α)
    ((puTrans_le_stab h.le _ α).trans (stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) α))
  have hx' : x ∈ ((Uloc h.le L α ⊔ Zloc h.le L α : Subgroup _) : Set _) :=
    xm_eq_uloc_sup_zloc_of_isSL3U h hU hα ▸ hx
  rw [hset] at hx'
  obtain ⟨u, hu, z, hz, rfl⟩ := hx'
  exact ⟨u, hu, by simpa using hz⟩

theorem uProj_conj {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab (puAmalgam h.le) α) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ XM (puAmalgam h.le) α) :
    uProj (Uloc h.le L α) (Zloc h.le L α) (y * x * y⁻¹) =
      y * uProj (Uloc h.le L α) (Zloc h.le L α) x * y⁻¹ := by
  obtain ⟨hux, hzx⟩ := uProj_xm h hU hα hx
  have hyu := (Subgroup.mem_normalizer_iff.mp
    (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α hy) _).mp hux
  refine uProj_eq (uloc_inf_zloc_of_isSL3U h hU α) hyu ?_
  have : (y * uProj (Uloc h.le L α) (Zloc h.le L α) x * y⁻¹)⁻¹ * (y * x * y⁻¹) =
      y * ((uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x) * y⁻¹ := by
    group
  rw [this]
  exact (Subgroup.mem_normalizer_iff.mp
    (stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) α hy) _).mp hzx

variable {F : Type} [Field F] {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
  {K : Subgroup (puAmalgam h.le).Universal} {ψ : ↥K →* ↥(StatedSL 3 F)}
  (hψ : IsSumOfNaturalModulesVia K (Uloc h.le L α) ⊥ ψ false 1)
include hα

theorem xvec_mul {x y : (puAmalgam h.le).Universal} (hx : x ∈ XM (puAmalgam h.le) α)
    (hy : y ∈ XM (puAmalgam h.le) α) : xvec hψ (x * y) = xvec hψ x + xvec hψ y := by
  obtain ⟨hux, hzx⟩ := uProj_xm h hU hα hx
  obtain ⟨huy, hzy⟩ := uProj_xm h hU hα hy
  have hX := xm_eq_uloc_sup_zloc_of_isSL3U h hU hα
  have hc : uProj (Uloc h.le L α) (Zloc h.le L α) y *
      ((uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x) =
      ((uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x) *
        uProj (Uloc h.le L α) (Zloc h.le L α) y :=
    (Subgroup.mem_centralizer_iff.mp (xm_le_centralizer _ α (hX ▸ Subgroup.mem_sup_left huy))
      _ (xm_le_qv _ α (hX ▸ Subgroup.mem_sup_right hzx))).symm
  have hmem : (uProj (Uloc h.le L α) (Zloc h.le L α) x *
      uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ * (x * y) ∈ Zloc h.le L α := by
    have : (uProj (Uloc h.le L α) (Zloc h.le L α) x *
        uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ * (x * y) =
        ((uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ *
          (uProj (Uloc h.le L α) (Zloc h.le L α) y *
            ((uProj (Uloc h.le L α) (Zloc h.le L α) x)⁻¹ * x))) *
          ((uProj (Uloc h.le L α) (Zloc h.le L α) y)⁻¹ * y) := by
      rw [hc]
      group
    rw [this, inv_mul_cancel_left]
    exact Subgroup.mul_mem _ hzx hzy
  unfold xvec
  rw [uProj_eq (uloc_inf_zloc_of_isSL3U h hU α) (Subgroup.mul_mem _ hux huy) hmem,
    natVecG_mul hψ hux huy]

theorem xvec_conj (hK : K ≤ stab (puAmalgam h.le) α) (g : ↥K) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ XM (puAmalgam h.le) α) :
    xvec hψ ((g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹) =
      ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ xvec hψ x := by
  unfold xvec
  rw [uProj_conj h hU hα (hK g.2) hx, natVecG_conj hψ g (uProj_xm h hU hα hx).1]

omit hα in
theorem xvec_one : xvec hψ (1 : (puAmalgam h.le).Universal) = 0 := by
  unfold xvec
  rw [uProj_eq (uloc_inf_zloc_of_isSL3U h hU α) (Subgroup.one_mem _) (by simp), natVecG_one]

theorem xvec_comm_mul (hK : K ≤ stab (puAmalgam h.le) α) {w : (puAmalgam h.le).Universal}
    (a b : ↥K) (ha : ⁅(a : (puAmalgam h.le).Universal), w⁆ ∈ ZM (puAmalgam h.le) α)
    (hb : ⁅(b : (puAmalgam h.le).Universal), w⁆ ∈ ZM (puAmalgam h.le) α) :
    xvec hψ ⁅((a * b : ↥K) : (puAmalgam h.le).Universal), w⁆ =
      xvec hψ ⁅(a : (puAmalgam h.le).Universal), w⁆ +
        ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          xvec hψ ⁅(b : (puAmalgam h.le).Universal), w⁆ := by
  have hZX := zm_le_xm _ h.hyp20 h.critDist_pos hα
  have hrw : ⁅((a * b : ↥K) : (puAmalgam h.le).Universal), w⁆ =
      (a : (puAmalgam h.le).Universal) * ⁅(b : (puAmalgam h.le).Universal), w⁆ *
        (a : (puAmalgam h.le).Universal)⁻¹ * ⁅(a : (puAmalgam h.le).Universal), w⁆ := by
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  have hconj := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α (hK a.2)) _).mp hb
  rw [hrw, xvec_mul h hU hα hψ (hZX hconj) (hZX ha), xvec_conj h hU hα hψ hK a (hZX hb),
    add_comm]

end Xvec

section Cent

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem commutator_mem_centralizer_of_mem_qv (h20 : Hyp20 X) {α : Vtx X} (hα : IsMVtx X α)
    {w : X.Universal} {Y : Subgroup X.Universal} (hYs : Y ≤ stab X α)
    (hYw : ∀ y ∈ Y, y * w = w * y) (hQY : Qv X α ≤ Subgroup.normalizer (Y : Set X.Universal))
    {k : X.Universal} (hkQ : k ∈ Qv X α) (hkw : ⁅k, w⁆ ∈ ZM X α) :
    ⁅k, w⁆ ∈ Subgroup.centralizer (Y : Set X.Universal) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  set c := y * k * y⁻¹ * k⁻¹ with hc
  have hcY : c ∈ Y := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hQY hkQ) _).mp (Y.inv_mem hy)
    have h2 := Y.mul_mem hy h1
    rw [hc]
    simpa [mul_assoc] using h2
  have hcQ : c ∈ Qv X α := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv X α (hYs hy)) k).mp hkQ
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hkQ)
  have hcx : c * ⁅k, w⁆ = ⁅k, w⁆ * c :=
    Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv X h20 hα hkw) c hcQ
  have hcw : ⁅c, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hYw c hcY)
  have key : y * ⁅k, w⁆ * y⁻¹ = ⁅k, w⁆ := by
    have h1 : y * ⁅k, w⁆ * y⁻¹ = ⁅y * k * y⁻¹, y * w * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have h2 : y * w * y⁻¹ = w := by rw [hYw y hy, mul_inv_cancel_right]
    have h3 : y * k * y⁻¹ = c * k := by rw [hc]; group
    have h4 : ⁅c * k, w⁆ = c * ⁅k, w⁆ * c⁻¹ * ⁅c, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1, h2, h3, h4, hcw, mul_one, hcx, mul_inv_cancel_right]
  calc y * ⁅k, w⁆ = y * ⁅k, w⁆ * y⁻¹ * y := by group
    _ = ⁅k, w⁆ * y := by rw [key]

end Cent

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hU : IsSL3U M T L)
include h hU

theorem exists_ltil_toSL3_eq_flat {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {F : Type}
    [Field F] {ψ : ↥(S34F.flat h α) →* ↥(StatedSL 3 F)} (hsurj : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h α) (Uloc h.le L α) ⊥ ψ false 1) (g : SL3 F) :
    ∃ l : ↥(S34F.flat h α), (l : (puAmalgam h.le).Universal) ∈ Ltil h.le L α ∧
      toSL3 ψ l = g := by
  obtain ⟨s, rfl⟩ := toSL3_surjective hsurj g
  have hs : (s : (puAmalgam h.le).Universal) ∈
      ((Ltil h.le L α ⊔ Qv _ α : Subgroup _) : Set _) :=
    S43F.flat_eq_ltil_sup_qv h hα ▸ s.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((ltil_le_stab h α).trans (stab_le_normalizer_qv _ α))] at hs
  obtain ⟨l, hl, q, hq, hlq⟩ := hs
  have hls : l ∈ S34F.flat h α := S43F.ltil_le_flat h α hl
  have hqs : q ∈ S34F.flat h α := S43F.qv_le_flat h hα hq
  refine ⟨⟨l, hls⟩, hl, ?_⟩
  have hq1 : toSL3 ψ ⟨q, hqs⟩ = 1 := (toSL3_eq_one_iff_mem_qv_flat h hU hα hψ _).mpr hq
  have : s = ⟨l, hls⟩ * ⟨q, hqs⟩ := Subtype.ext hlq.symm
  rw [this, map_mul, hq1, mul_one]

theorem mem_uloc_sup_dloc_of_coboundary {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {F : Type} [Field F] {ψ : ↥(S34F.flat h α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h α) (Uloc h.le L α) ⊥ ψ false 1)
    {w : (puAmalgam h.le).Universal} (hwQ : w ∈ Qv _ α)
    (hwL : ∀ l ∈ Ltil h.le L α, ⁅l, w⁆ ∈ ZM (puAmalgam h.le) α) {n : Fin 3 → F}
    (hn : ∀ l : ↥(S34F.flat h α), (l : (puAmalgam h.le).Universal) ∈ Ltil h.le L α →
      xvec hψ ⁅(l : (puAmalgam h.le).Universal), w⁆ =
        ((toSL3 ψ l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n) :
    w ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
  obtain ⟨u₀, hu₀⟩ := natVec_surjective hψ n
  have hUs : Uloc h.le L α ≤ stab (puAmalgam h.le) α := puTrans_le_stab h.le _ α
  have hX := xm_eq_uloc_sup_zloc_of_isSL3U h hU hα
  have hZX := zm_le_xm _ h.hyp20 h.critDist_pos hα
  have hcomm_l : ∀ l ∈ Ltil h.le L α, ⁅l, (u₀ : (puAmalgam h.le).Universal)⁻¹ * w⁆ ∈
      Zloc h.le L α := by
    intro l hl
    have hls : l ∈ S34F.flat h α := S43F.ltil_le_flat h α hl
    have hlu : l * (u₀ : (puAmalgam h.le).Universal) * l⁻¹ ∈ Uloc h.le L α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
        (ltil_le_stab h α hl)) _).mp u₀.2
    have hU1 : ⁅l, (u₀ : (puAmalgam h.le).Universal)⁆ ∈ Uloc h.le L α := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ hlu (Subgroup.inv_mem _ u₀.2)
    obtain ⟨hpU, hpZ⟩ := uProj_xm h hU hα (hZX (hwL l hl))
    have hproj_eq : uProj (Uloc h.le L α) (Zloc h.le L α) ⁅l, w⁆ =
        ⁅l, (u₀ : (puAmalgam h.le).Universal)⁆ := by
      apply natVecG_injective hψ hpU hU1
      have h1 := hn ⟨l, hls⟩ hl
      have h2 : natVecG hψ (l * (u₀ : (puAmalgam h.le).Universal) * l⁻¹) =
          ((toSL3 ψ ⟨l, hls⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            natVecG hψ (u₀ : (puAmalgam h.le).Universal) :=
        natVecG_conj hψ ⟨l, hls⟩ u₀.2
      have h3 : natVecG hψ (u₀ : (puAmalgam h.le).Universal)⁻¹ = -n := by
        rw [natVecG_of_mem hψ (Subgroup.inv_mem _ u₀.2),
          show (⟨(u₀ : (puAmalgam h.le).Universal)⁻¹, Subgroup.inv_mem _ u₀.2⟩ :
            ↥(Uloc h.le L α)) = u₀⁻¹ from rfl, natVec_inv, hu₀]
      have h4 : natVecG hψ (u₀ : (puAmalgam h.le).Universal) = n := by
        rw [natVecG_of_mem hψ u₀.2]
        exact hu₀
      change xvec hψ ⁅l, w⁆ = _
      rw [h1, commutatorElement_def, natVecG_mul hψ hlu (Subgroup.inv_mem _ u₀.2), h2, h3, h4,
        sub_eq_add_neg]
    rw [hproj_eq] at hpZ
    have hrw : ⁅l, (u₀ : (puAmalgam h.le).Universal)⁻¹ * w⁆ =
        (u₀ : (puAmalgam h.le).Universal)⁻¹ *
          (⁅l, (u₀ : (puAmalgam h.le).Universal)⁆⁻¹ * ⁅l, w⁆) *
            ((u₀ : (puAmalgam h.le).Universal)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le (S4A.Zq_normal h) α
      (Subgroup.inv_mem _ (hUs u₀.2))) _).mp hpZ
  have hUQ : Uloc h.le L α ≤ Qv (puAmalgam h.le) α := fun u hu =>
    xm_le_qv _ α (hX ▸ Subgroup.mem_sup_left hu)
  have hw'Q : (u₀ : (puAmalgam h.le).Universal)⁻¹ * w ∈ Qv (puAmalgam h.le) α :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUQ u₀.2)) hwQ
  have hclQ : Subgroup.closure {(u₀ : (puAmalgam h.le).Universal)⁻¹ * w} ≤
      Qv (puAmalgam h.le) α := by
    rw [Subgroup.closure_le]
    rintro _ rfl
    exact hw'Q
  have hcl : ⁅Subgroup.closure {(u₀ : (puAmalgam h.le).Universal)⁻¹ * w}, Ltil h.le L α⁆ ≤
      Dloc h.le L α := by
    refine commutator_closure_le_of (fun s hs l hl => ?_)
      (hclQ.trans ((qv_le_stab _ α).trans (stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α)))
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (zloc_le_dloc h α (hcomm_l l hl))
  have hw'D : (u₀ : (puAmalgam h.le).Universal)⁻¹ * w ∈ Dloc h.le L α :=
    le_dloc_of_commutator_le h hα hclQ hcl (Subgroup.subset_closure rfl)
  have hw : w = (u₀ : (puAmalgam h.le).Universal) * ((u₀ : (puAmalgam h.le).Universal)⁻¹ * w) := by
    group
  rw [hw]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left u₀.2) (Subgroup.mem_sup_right hw'D)

theorem mem_uloc_sup_dloc_flat {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {F : Type}
    [Field F] [Finite F] [CharP F 2] {ψ : ↥(S34F.flat h α) →* ↥(StatedSL 3 F)}
    (hsurj : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h α) (Uloc h.le L α) ⊥ ψ false 1)
    {w : (puAmalgam h.le).Universal} (hwQ : w ∈ Qv _ α)
    (hwL : ∀ l ∈ Ltil h.le L α, ⁅l, w⁆ ∈ ZM (puAmalgam h.le) α)
    {Y : Subgroup (puAmalgam h.le).Universal} (hYs : Y ≤ S34F.flat h α)
    (hYw : ∀ y ∈ Y, y * w = w * y)
    (hQY : Qv (puAmalgam h.le) α ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal))
    (hY2 : IsPGroup 2 Y) (hYQ : ¬ Y ≤ Qv (puAmalgam h.le) α) :
    w ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
  set H : Subgroup ↥(S34F.flat h α) :=
    (gwSub (puAmalgam h.le) α w).comap (Subgroup.inclusion (S43F.flat_le_stab h α)) with hH
  set f : ↥(S34F.flat h α) → (Fin 3 → F) :=
    fun a => xvec hψ ⁅(a : (puAmalgam h.le).Universal), w⁆ with hfdef
  have hf : ∀ a ∈ H, ∀ b ∈ H,
      f (a * b) = f a + ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b :=
    fun a ha b hb => xvec_comm_mul h hU hα hψ (S43F.flat_le_stab h α) a b ha hb
  have hρH : ∀ g : SL3 F, ∃ a ∈ H, toSL3 ψ a = g := fun g => by
    obtain ⟨l, hl, hlg⟩ := exists_ltil_toSL3_eq_flat h hU hα hsurj hψ g
    exact ⟨l, hwL _ hl, hlg⟩
  have hYw' : ∀ y ∈ Y, ⁅y, w⁆ = 1 := fun y hy => by
    rw [commutatorElement_def, hYw y hy, mul_inv_cancel_right, mul_inv_cancel]
  have hYH : Y.subgroupOf (S34F.flat h α) ≤ H := fun y hy => by
    show ⁅((y : ↥(S34F.flat h α)) : (puAmalgam h.le).Universal), w⁆ ∈ ZM _ α
    rw [hYw' _ (Subgroup.mem_subgroupOf.mp hy)]
    exact Subgroup.one_mem _
  have hfY : ∀ y ∈ Y.subgroupOf (S34F.flat h α), f y = 0 := fun y hy => by
    show xvec hψ ⁅((y : ↥(S34F.flat h α)) : (puAmalgam h.le).Universal), w⁆ = 0
    rw [hYw' _ (Subgroup.mem_subgroupOf.mp hy)]
    exact xvec_one h hU hψ
  have hP : ∀ k ∈ H, toSL3 ψ k = 1 →
      ∃ b : ℕ, Odd b ∧ k ^ b ∈ (Qv (puAmalgam h.le) α).subgroupOf (S34F.flat h α) :=
    fun k _ hk1 => ⟨1, odd_one, by
      rw [pow_one, Subgroup.mem_subgroupOf]
      exact (toSL3_eq_one_iff_mem_qv_flat h hU hα hψ k).mp hk1⟩
  have hPY : (Qv (puAmalgam h.le) α).subgroupOf (S34F.flat h α) ≤
      Subgroup.normalizer ((Y.subgroupOf (S34F.flat h α) : Subgroup _) :
        Set ↥(S34F.flat h α)) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hQY (Subgroup.mem_subgroupOf.mp hq)) _)
  have hYρ : (Y.subgroupOf (S34F.flat h α)).map (toSL3 ψ) ≠ ⊥ := by
    intro hbot
    apply hYQ
    intro y hy
    have h1 : toSL3 ψ ⟨y, hYs hy⟩ = 1 := by
      have : toSL3 ψ ⟨y, hYs hy⟩ ∈ (Y.subgroupOf (S34F.flat h α)).map (toSL3 ψ) :=
        ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    exact (toSL3_eq_one_iff_mem_qv_flat h hU hα hψ _).mp h1
  have hY2' : IsPGroup 2 ↥(Y.subgroupOf (S34F.flat h α)) :=
    hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYs).symm
  obtain ⟨n, hn⟩ := exists_coboundary_of_cocycle hf hYH hfY hρH hP hPY hYρ hY2'
  exact mem_uloc_sup_dloc_of_coboundary h hU hα hψ hwQ hwL fun l hl => hn l (hwL _ hl)

theorem mem_uloc_sup_dloc_of_four_le {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {F : Type}
    [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    {ψ : ↥(S34F.flat h α) →* ↥(StatedSL 3 F)} (hsurj : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h α) (Uloc h.le L α) ⊥ ψ false 1)
    {w : (puAmalgam h.le).Universal} (hwQ : w ∈ Qv _ α)
    (hwL : ∀ l ∈ Ltil h.le L α, ⁅l, w⁆ ∈ ZM (puAmalgam h.le) α)
    {Y : Subgroup (puAmalgam h.le).Universal} (hYs : Y ≤ stab (puAmalgam h.le) α)
    (hYw : ∀ y ∈ Y, y * w = w * y)
    (hQY : Qv (puAmalgam h.le) α ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal))
    (hYU : ¬ Y ≤ Subgroup.centralizer (Uloc h.le L α : Set (puAmalgam h.le).Universal)) :
    w ∈ Uloc h.le L α ⊔ Dloc h.le L α := by
  have hZX := zm_le_xm _ h.hyp20 h.critDist_pos hα
  set H : Subgroup ↥(S34F.flat h α) :=
    (gwSub (puAmalgam h.le) α w).comap (Subgroup.inclusion (S43F.flat_le_stab h α)) with hH
  set f : ↥(S34F.flat h α) → (Fin 3 → F) :=
    fun a => xvec hψ ⁅(a : (puAmalgam h.le).Universal), w⁆ with hfdef
  have hf : ∀ a ∈ H, ∀ b ∈ H,
      f (a * b) = f a + ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f b :=
    fun a ha b hb => xvec_comm_mul h hU hα hψ (S43F.flat_le_stab h α) a b ha hb
  have hρH : ∀ g : SL3 F, ∃ a ∈ H, toSL3 ψ a = g := fun g => by
    obtain ⟨l, hl, hlg⟩ := exists_ltil_toSL3_eq_flat h hU hα hsurj hψ g
    exact ⟨l, hwL _ hl, hlg⟩
  have hker : ∀ k ∈ H, toSL3 ψ k = 1 → f k = 0 := by
    intro k hk hk1
    by_contra hne
    apply hYU
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k', hk'H, hk'1, hk'v⟩ :=
      exists_ker_cocycle_eq (f := f) hf hρH hk hk1 hne (natVecG hψ u)
    have hk'Q := (toSL3_eq_one_iff_mem_qv_flat h hU hα hψ k').mp hk'1
    have hk'w : ⁅((k' : ↥(S34F.flat h α)) : (puAmalgam h.le).Universal), w⁆ ∈
        ZM (puAmalgam h.le) α := hk'H
    have hxY := commutator_mem_centralizer_of_mem_qv h.hyp20 hα hYs hYw hQY hk'Q hk'w
    have hyx : y * ⁅((k' : ↥(S34F.flat h α)) : (puAmalgam h.le).Universal), w⁆ * y⁻¹ =
        ⁅((k' : ↥(S34F.flat h α)) : (puAmalgam h.le).Universal), w⁆ := by
      rw [Subgroup.mem_centralizer_iff.mp hxY y hy, mul_inv_cancel_right]
    have hpu := uProj_conj h hU hα (hYs hy) (hZX hk'w)
    rw [hyx] at hpu
    have hpe : uProj (Uloc h.le L α) (Zloc h.le L α)
        ⁅((k' : ↥(S34F.flat h α)) : (puAmalgam h.le).Universal), w⁆ = u :=
      natVecG_injective hψ (uProj_xm h hU hα (hZX hk'w)).1 hu hk'v
    rw [hpe] at hpu
    calc u * y = y * u * y⁻¹ * y := by rw [← hpu]
      _ = y * u := by group
  obtain ⟨n, hn⟩ := exists_coboundary_of_cocycle_of_ker hq hf hρH hker
  exact mem_uloc_sup_dloc_of_coboundary h hU hα hψ hwQ hwL fun l hl => hn l (hwL _ hl)

end Main

end CFSG.Quasithin.MS93.S4L
