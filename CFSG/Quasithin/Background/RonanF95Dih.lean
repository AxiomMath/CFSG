module

public import CFSG.Quasithin.Background.F9FiveStruct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem F95gens_conjAct_apply {X : Subgroup G} (n : Subgroup.normalizer (X : Set G)) (u : X) :
    ((conjAct X n u : X) : G) = (n : G) * (u : G) * (n : G)⁻¹ := rfl

theorem F95gens_conjAct_eq_one {X : Subgroup G} (n : Subgroup.normalizer (X : Set G)) :
    conjAct X n = 1 ↔ ∀ u : X, (n : G) * (u : G) = (u : G) * (n : G) := by
  constructor
  · intro hn u
    have h1 : (n : G) * (u : G) * (n : G)⁻¹ = (u : G) := by
      have := congrArg (fun φ : MulAut X => ((φ u : X) : G)) hn
      simpa [F95gens_conjAct_apply] using this
    calc (n : G) * (u : G) = (n : G) * (u : G) * (n : G)⁻¹ * (n : G) := by group
      _ = (u : G) * (n : G) := by rw [h1]
  · intro hn
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    show ((conjAct X n u : X) : G) = (u : G)
    rw [F95gens_conjAct_apply]
    calc (n : G) * (u : G) * (n : G)⁻¹ = (u : G) * (n : G) * (n : G)⁻¹ := by rw [hn u]
      _ = (u : G) := by group

theorem F95gens_toTilde_mem {V₁ H U : Subgroup G} (hH : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (x : ↥H) :
    toTilde hH x ∈ Subgroup.normalizer ((tildeOf V₁ U : Subgroup _) : Set _) :=
  secMk_mem_normalizer_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := U)
    (a := Subgroup.inclusion hH x) (hHU x.2)

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

@[expose] noncomputable def F95gensPhi (h : HypF91 T V L V₁ Vp H) :
    ↥H →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) :=
  (conjAct (tildeOf V₁ (conjClosure Vp H))).comp
    (MonoidHom.codRestrict (toTilde h.H_normalizes_V₁)
      (Subgroup.normalizer ((tildeOf V₁ (conjClosure Vp H) : Subgroup _) : Set _))
      (fun x => F95gens_toTilde_mem h.H_normalizes_V₁ (le_normalizer_conjClosure Vp H) x))

theorem F95gensPhi_apply_eq_one_iff (h : HypF91 T V L V₁ Vp H) (x : ↥H) :
    F95gensPhi h x = 1 ↔ ∀ u : ↥(tildeOf V₁ (conjClosure Vp H)),
      toTilde h.H_normalizes_V₁ x * (u : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
        (u : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) * toTilde h.H_normalizes_V₁ x := by
  unfold F95gensPhi
  rw [MonoidHom.comp_apply]
  exact F95gens_conjAct_eq_one _

theorem F95gensPhi_apply_eq (h : HypF91 T V L V₁ Vp H) (x : ↥H)
    (e : ↥(Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))))
    (he : (e : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) = toTilde h.H_normalizes_V₁ x) :
    conjAct (tildeOf V₁ (conjClosure Vp H)) e = F95gensPhi h x := by
  unfold F95gensPhi
  rw [MonoidHom.comp_apply]
  congr 1
  exact Subtype.ext he

theorem F95gensPhi_mem_autOn (h : HypF91 T V L V₁ Vp H) {I : Subgroup G} (hIH : I ≤ H) {x : ↥H}
    (hx : (x : G) ∈ I) :
    F95gensPhi h x ∈ autOn (tildeOf V₁ I) (tildeOf V₁ (conjClosure Vp H)) := by
  rw [autOn, Subgroup.mem_map]
  refine ⟨⟨toTilde h.H_normalizes_V₁ x,
    F95gens_toTilde_mem h.H_normalizes_V₁ (le_normalizer_conjClosure Vp H) x⟩, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  exact (mem_tildeOf_iff h.H_normalizes_V₁ hIH).mpr ⟨x, hx, rfl⟩

theorem F95gensPhi_eq_one_of_Q (h : HypF91 T V L V₁ Vp H) (x : ↥H)
    (hx : (x : G) ∈ pCoreOf 2 H) :
    F95gensPhi h x = 1 := by
  rw [F95gensPhi_apply_eq_one_iff]
  rintro ⟨u, hu⟩
  obtain ⟨y, hy, rfl⟩ := (mem_tildeOf_iff h.H_normalizes_V₁
    (h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H))).mp hu
  exact h.toTilde_comm_Q hx hy

theorem F95gensPhi_crux (h : HypF91 T V L V₁ Vp H) (a w : ↥H) (haa : (a : G) * (a : G) = 1)
    (hw : (w : G) ∈ pCoreOf 2 H ∨ (w : G) * (a : G) ∈ pCoreOf 2 H) :
    F95gensPhi h w = 1 ∨ F95gensPhi h w = F95gensPhi h a := by
  rcases hw with hwQ | hwQ
  · exact Or.inl (F95gensPhi_eq_one_of_Q h w hwQ)
  · refine Or.inr ?_
    have hwa : (w : G) * (a : G) ∈ H := H.mul_mem w.2 a.2
    have e : w = (⟨(w : G) * (a : G), hwa⟩ : ↥H) * a := Subtype.ext (by
      show (w : G) = ((w : G) * (a : G)) * (a : G)
      rw [mul_assoc, haa, mul_one])
    have h1 : F95gensPhi h w = F95gensPhi h ((⟨(w : G) * (a : G), hwa⟩ : ↥H) * a) :=
      congrArg (F95gensPhi h) e
    rw [h1, map_mul, F95gensPhi_eq_one_of_Q h ⟨(w : G) * (a : G), hwa⟩ hwQ, one_mul]

theorem F95gens_tildeOf_le_normalizer (h : HypF91 T V L V₁ Vp H) {X : Subgroup G}
    (hXH : X ≤ H) :
    tildeOf V₁ X ≤ Subgroup.normalizer ((tildeOf V₁ (conjClosure Vp H) : Subgroup _) : Set _) := by
  intro y hy
  obtain ⟨w, -, rfl⟩ := (mem_tildeOf_iff h.H_normalizes_V₁ hXH).mp hy
  exact F95gens_toTilde_mem h.H_normalizes_V₁ (le_normalizer_conjClosure Vp H) w

theorem F95_gens (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H)
    {a₀ : G} (ha₀V : a₀ ∈ V) (ha₀₀ : a₀ * a₀ = 1)
    (hZV : ∀ w ∈ V, w ∈ pCoreOf 2 H ∨ w * a₀ ∈ pCoreOf 2 H) (ha₀Q : a₀ ∉ pCoreOf 2 H) :
    ∃ σ τ : MulAut ↥(tildeOf V₁ (conjClosure Vp H)),
      σ ∈ autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H)) ∧
      τ ∈ autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H)) ∧
      Subgroup.closure ({σ, τ} : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) =
        autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H)) ∧
      σ * σ = 1 ∧ τ * τ = 1 ∧
      ∀ k : ℕ, (σ * τ) ^ k = 1 ↔
        ∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp,
          (a₀ * (g⁻¹ * a₀ * g)) ^ k * p * ((a₀ * (g⁻¹ * a₀ * g)) ^ k)⁻¹ * p⁻¹ ∈ V₁ := by
  have hH := h.H_normalizes_V₁
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans hQH
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have ha₀H : a₀ ∈ H := h.V_le_H ha₀V
  have hVH : V ≤ H := h.V_le_H
  have hVgH : conjSub g⁻¹ V ≤ H := h.conjSub_inv_le_H hg
  have hIH : V ⊔ conjSub g⁻¹ V ≤ H := sup_le hVH hVgH
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hVpgU : conjSub g⁻¹ Vp ≤ conjClosure Vp H := conjSub_inv_le_U hg hVpU
  have hUIU : Vp ⊔ conjSub g⁻¹ Vp ≤ conjClosure Vp H := sup_le hVpU hVpgU
  have hUIH : Vp ⊔ conjSub g⁻¹ Vp ≤ H := hUIU.trans hUH
  have hCH : centralizerMod V₁ (conjClosure Vp H) (V ⊔ conjSub g⁻¹ V) ≤ H :=
    fun y hy => hUH hy.1
  have hVN : V ≤ Subgroup.normalizer (V₁ : Set G) := h.V_le_normalizer_V₁
  have hVgN : conjSub g⁻¹ V ≤ Subgroup.normalizer (V₁ : Set G) := hVgH.trans hH
  obtain ⟨-, -, -, c4, -⟩ := h.F95_five_core hidx hV hyp5 hg hI
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : G, b₀ = g⁻¹ * a₀ * g := ⟨_, rfl⟩
  rw [← hb₀]
  have hb₀V : b₀ ∈ conjSub g⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have e : g * b₀ * g⁻¹ = a₀ := by rw [hb₀]; group
    rw [e]
    exact ha₀V
  have hb₀H : b₀ ∈ H := hVgH hb₀V
  have hb₀₀ : b₀ * b₀ = 1 := by
    have e : b₀ * b₀ = g⁻¹ * (a₀ * a₀) * g := by rw [hb₀]; group
    rw [e, ha₀₀]
    group
  have hZg : ∀ w ∈ conjSub g⁻¹ V, w ∈ pCoreOf 2 H ∨ w * b₀ ∈ pCoreOf 2 H := by
    intro w hw
    rw [mem_conjSub, inv_inv] at hw
    rcases hZV _ hw with h1 | h1
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (hQn hg) w).mpr h1)
    · refine Or.inr ((Subgroup.mem_normalizer_iff.mp (hQn hg) (w * b₀)).mpr ?_)
      have e : g * (w * b₀) * g⁻¹ = (g * w * g⁻¹) * a₀ := by rw [hb₀]; group
      rw [e]
      exact h1
  obtain ⟨σ, hσdef⟩ : ∃ σ : MulAut ↥(tildeOf V₁ (conjClosure Vp H)),
      σ = F95gensPhi h ⟨a₀, ha₀H⟩ := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : MulAut ↥(tildeOf V₁ (conjClosure Vp H)),
      τ = F95gensPhi h ⟨b₀, hb₀H⟩ := ⟨_, rfl⟩
  have hVtN : tildeOf V₁ V ≤
      Subgroup.normalizer ((tildeOf V₁ (conjClosure Vp H) : Subgroup _) : Set _) :=
    F95gens_tildeOf_le_normalizer h hVH
  have hVgtN : tildeOf V₁ (conjSub g⁻¹ V) ≤
      Subgroup.normalizer ((tildeOf V₁ (conjClosure Vp H) : Subgroup _) : Set _) :=
    F95gens_tildeOf_le_normalizer h hVgH
  have hĨ : tildeOf V₁ (V ⊔ conjSub g⁻¹ V) = tildeOf V₁ V ⊔ tildeOf V₁ (conjSub g⁻¹ V) :=
    tildeOf_sup hVN hVgN
  have hσ : σ ∈ autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H)) := by
    rw [hσdef]
    exact F95gensPhi_mem_autOn h hIH (Subgroup.mem_sup_left ha₀V)
  have hτ : τ ∈ autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H)) := by
    rw [hτdef]
    exact F95gensPhi_mem_autOn h hIH (Subgroup.mem_sup_right hb₀V)
  have hcrV : ∀ w : ↥H, (w : G) ∈ V → F95gensPhi h w = 1 ∨ F95gensPhi h w = σ := by
    intro w hw
    rw [hσdef]
    exact F95gensPhi_crux h ⟨a₀, ha₀H⟩ w ha₀₀ (hZV _ hw)
  have hcrVg : ∀ w : ↥H, (w : G) ∈ conjSub g⁻¹ V → F95gensPhi h w = 1 ∨ F95gensPhi h w = τ := by
    intro w hw
    rw [hτdef]
    exact F95gensPhi_crux h ⟨b₀, hb₀H⟩ w hb₀₀ (hZg _ hw)
  have hcl : Subgroup.closure ({σ, τ} : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) =
      autOn (tildeOf V₁ (V ⊔ conjSub g⁻¹ V)) (tildeOf V₁ (conjClosure Vp H)) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hσ
      · exact hτ
    · rw [autOn, hĨ, Subgroup.subgroupOf_sup hVtN hVgtN, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        intro e he
        rw [Subgroup.mem_subgroupOf] at he
        obtain ⟨w, hwV, hwe⟩ := (mem_tildeOf_iff hH hVH).mp he
        rw [Subgroup.mem_comap, F95gensPhi_apply_eq h w e hwe.symm]
        rcases hcrV w hwV with e' | e'
        · rw [e']
          exact Subgroup.one_mem _
        · rw [e']
          exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Subgroup.map_le_iff_le_comap]
        intro e he
        rw [Subgroup.mem_subgroupOf] at he
        obtain ⟨w, hwVg, hwe⟩ := (mem_tildeOf_iff hH hVgH).mp he
        rw [Subgroup.mem_comap, F95gensPhi_apply_eq h w e hwe.symm]
        rcases hcrVg w hwVg with e' | e'
        · rw [e']
          exact Subgroup.one_mem _
        · rw [e']
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hσσ : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have e : (⟨a₀, ha₀H⟩ : ↥H) * ⟨a₀, ha₀H⟩ = 1 := Subtype.ext ha₀₀
    rw [e, map_one]
  have hττ : τ * τ = 1 := by
    rw [hτdef, ← map_mul]
    have e : (⟨b₀, hb₀H⟩ : ↥H) * ⟨b₀, hb₀H⟩ = 1 := Subtype.ext hb₀₀
    rw [e, map_one]
  refine ⟨σ, τ, hσ, hτ, hcl, hσσ, hττ, fun k => ?_⟩
  obtain ⟨tk, htk⟩ : ∃ tk : ↥H, (tk : G) = (a₀ * b₀) ^ k :=
    ⟨⟨(a₀ * b₀) ^ k, H.pow_mem (H.mul_mem ha₀H hb₀H) k⟩, rfl⟩
  have htkI : (tk : G) ∈ V ⊔ conjSub g⁻¹ V := by
    rw [htk]
    exact (V ⊔ conjSub g⁻¹ V).pow_mem
      ((V ⊔ conjSub g⁻¹ V).mul_mem (Subgroup.mem_sup_left ha₀V)
        (Subgroup.mem_sup_right hb₀V)) k
  have hstep : (σ * τ) ^ k = F95gensPhi h tk := by
    rw [hσdef, hτdef, ← map_mul, ← map_pow]
    congr 1
    apply Subtype.ext
    simp [htk]
  rw [hstep, F95gensPhi_apply_eq_one_iff]
  constructor
  · intro hk p hp
    have hpU : p ∈ conjClosure Vp H := hUIU hp
    have hpH : p ∈ H := hUH hpU
    have hu : toTilde hH ⟨p, hpH⟩ ∈ tildeOf V₁ (conjClosure Vp H) :=
      (mem_tildeOf_iff hH hUH).mpr ⟨⟨p, hpH⟩, hpU, rfl⟩
    have hc := hk ⟨toTilde hH ⟨p, hpH⟩, hu⟩
    have hc' := (toTilde_comm_iff hH (x := tk) (y := ⟨p, hpH⟩)).mp hc
    rw [htk] at hc'
    exact hc'
  · intro hp
    have hcent : tildeOf V₁ (conjClosure Vp H) ≤
        Subgroup.centralizer
          ({toTilde hH tk} : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) := by
      rw [c4]
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨q, hq, rfl⟩ := (mem_tildeOf_iff hH hUIH).mp hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        refine (toTilde_comm_iff hH (x := tk) (y := q)).mpr ?_
        rw [htk]
        exact hp q hq
      · obtain ⟨c, hc, rfl⟩ := (mem_tildeOf_iff hH hCH).mp hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        refine (toTilde_comm_iff hH (x := tk) (y := c)).mpr ?_
        have h1 := V₁.inv_mem (hc.2.2 _ htkI)
        have e : ((c : G) * (tk : G) * (c : G)⁻¹ * (tk : G)⁻¹)⁻¹ =
            (tk : G) * (c : G) * (tk : G)⁻¹ * (c : G)⁻¹ := by group
        rwa [e] at h1
    intro u
    exact Subgroup.mem_centralizer_iff.mp (hcent u.2) _ (Set.mem_singleton _)

end HypF91

end Fin

end CFSG.Quasithin
