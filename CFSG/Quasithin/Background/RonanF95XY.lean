module

public import CFSG.Quasithin.Background.F9FiveStruct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace RonanF95XY

variable {V₁ H : Subgroup G}

theorem toTilde_eq_iff (hH : H ≤ Subgroup.normalizer (V₁ : Set G)) {x y : ↥H} :
    toTilde hH x = toTilde hH y ↔ (x : G)⁻¹ * (y : G) ∈ V₁ := by
  have e : ((x⁻¹ * y : ↥H) : G) = (x : G)⁻¹ * (y : G) := by simp
  rw [← e, ← toTilde_eq_one_iff hH, map_mul, map_inv, inv_mul_eq_one]

theorem mem_of_toTilde_mem {X : Subgroup G} (hH : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hXH : X ≤ H) (hV₁X : V₁ ≤ X) {p : G} (hpH : p ∈ H)
    (hp : toTilde hH ⟨p, hpH⟩ ∈ tildeOf V₁ X) : p ∈ X := by
  obtain ⟨x, hx, hxe⟩ := (mem_tildeOf_iff hH hXH).mp hp
  have h1 : (x : G)⁻¹ * p ∈ V₁ := (toTilde_eq_iff hH).mp hxe
  have h2 := X.mul_mem hx (hV₁X h1)
  rwa [mul_inv_cancel_left] at h2

theorem comm_mem_of_Q {Q : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (V₁ : Set G))
    {p c w : G} (c2 : c * c = 1) (hp : ∀ q ∈ Q, p * q * p⁻¹ * q⁻¹ ∈ V₁)
    (hpc : p * c * p⁻¹ * c⁻¹ ∈ V₁) (hw : w ∈ Q ∨ w * c ∈ Q) :
    p * w * p⁻¹ * w⁻¹ ∈ V₁ := by
  rcases hw with hwQ | hwQ
  · exact hp w hwQ
  · obtain ⟨q, hq, rfl⟩ : ∃ q ∈ Q, w = q * c :=
      ⟨w * c, hwQ, by rw [mul_assoc, c2, mul_one]⟩
    have e : p * (q * c) * p⁻¹ * (q * c)⁻¹ =
        (p * q * p⁻¹ * q⁻¹) * (q * (p * c * p⁻¹ * c⁻¹) * q⁻¹) := by group
    rw [e]
    exact V₁.mul_mem (hp q hq) ((Subgroup.mem_normalizer_iff.mp (hQN hq) _).mp hpc)

end RonanF95XY

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem F95_Y_sides (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) :
    tildeOf V₁ (conjSub g⁻¹ Vp) = tildeOf V₁ ⁅Vp ⊔ conjSub g⁻¹ Vp, conjSub g⁻¹ V⁆ ∧
      tildeOf V₁ (conjSub g⁻¹ Vp) =
        tildeOf V₁ (centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) (conjSub g⁻¹ V)) := by
  have hH := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hUH : conjClosure Vp H ≤ H := hUQ.trans (pCoreOf_le 2 H)
  obtain ⟨a₀, ha₀V, ha₀₀, hZV, -⟩ := h.exists_a₀ hidx hV
  have hVgH : conjSub g⁻¹ V ≤ H := h.conjSub_inv_le_H hg
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hVpgU : conjSub g⁻¹ Vp ≤ conjClosure Vp H := conjSub_inv_le_U hg hVpU
  have hVpN : Vp ≤ Subgroup.normalizer (V₁ : Set G) := hVpU.trans (hUH.trans hH)
  have hVpgN : conjSub g⁻¹ Vp ≤ Subgroup.normalizer (V₁ : Set G) :=
    hVpgU.trans (hUH.trans hH)
  have hV₁g : conjSub g⁻¹ V₁ = V₁ := F7.conjSub_eq_of_mem_normalizer (hH (H.inv_mem hg))
  have hV₁Vpg : V₁ ≤ conjSub g⁻¹ Vp := by
    have : conjSub g⁻¹ V₁ = V₁ := hV₁g
    rw [← this]
    exact conjSub_mono _ h.V₁_le_Vp
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : G, b₀ = g⁻¹ * a₀ * g := ⟨_, rfl⟩
  have hb₀V : b₀ ∈ conjSub g⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have : g * b₀ * g⁻¹ = a₀ := by rw [hb₀]; group
    rw [this]
    exact ha₀V
  have hb₀₀ : b₀ * b₀ = 1 := by
    have : b₀ * b₀ = g⁻¹ * (a₀ * a₀) * g := by rw [hb₀]; group
    rw [this, ha₀₀]; group
  have hZg : ∀ w ∈ conjSub g⁻¹ V, w ∈ pCoreOf 2 H ∨ w * b₀ ∈ pCoreOf 2 H := by
    intro w hw
    rw [mem_conjSub, inv_inv] at hw
    rcases hZV _ hw with h1 | h1
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (hQn hg) w).mpr h1)
    · refine Or.inr ((Subgroup.mem_normalizer_iff.mp (hQn hg) (w * b₀)).mpr ?_)
      have : g * (w * b₀) * g⁻¹ = (g * w * g⁻¹) * a₀ := by rw [hb₀]; group
      rw [this]
      exact h1
  have hI' : ¬ ∀ x ∈ V ⊔ conjSub (g⁻¹)⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H := by
    intro hall
    apply hI
    intro z hz
    have hzm : g * z * g⁻¹ ∈ V ⊔ conjSub (g⁻¹)⁻¹ V := by
      rw [inv_inv]
      have hmem : g * z * g⁻¹ ∈ conjSub g (V ⊔ conjSub g⁻¹ V) := by
        rw [mem_conjSub]
        have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
        rw [e]; exact hz
      rw [conjSub_sup, conjSub_inv_conjSub, sup_comm] at hmem
      exact hmem
    obtain ⟨n, hn⟩ := hall _ hzm
    refine ⟨n, ?_⟩
    have e : (g * z * g⁻¹) ^ 2 ^ n = g * z ^ 2 ^ n * g⁻¹ := conj_pow
    rw [e] at hn
    exact (Subgroup.mem_normalizer_iff.mp (hQn hg) _).mpr hn
  obtain ⟨x, hx⟩ : ∃ x : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁,
      x = toTilde hH ⟨a₀, h.V_le_H ha₀V⟩ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁,
      y = toTilde hH ⟨b₀, hVgH hb₀V⟩ := ⟨_, rfl⟩
  have hR1x : F9Lin.commSub x (tildeOf V₁ (conjClosure Vp H)) = tildeOf V₁ Vp := by
    rw [hx, h.commSub_toTilde h.V_le_H le_rfl ha₀V ha₀₀ hZV]
    exact (h.F95_2 hidx hV).2
  obtain ⟨hMg, hUVg⟩ := h.F95_conj_aux hidx hV hg
  have hR1y : F9Lin.commSub y (tildeOf V₁ (conjClosure Vp H)) = tildeOf V₁ (conjSub g⁻¹ Vp) := by
    rw [hy, h.commSub_toTilde hVgH le_rfl hb₀V hb₀₀ hZg]
    have e := tildeOf_sup_self (V₁ := V₁) (X := ⁅conjClosure Vp H, conjSub g⁻¹ V⁆)
      (hUVg.trans hVpgN)
    rw [hMg] at e
    exact e.symm
  have hR2x : F9Lin.fixSub x (tildeOf V₁ (conjClosure Vp H)) =
      tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) V) := by
    rw [hx]; exact h.fixSub_toTilde h.V_le_H le_rfl ha₀V ha₀₀ hZV
  have hR2y : F9Lin.fixSub y (tildeOf V₁ (conjClosure Vp H)) =
      tildeOf V₁ (centralizerMod V₁ (conjClosure Vp H) (conjSub g⁻¹ V)) := by
    rw [hy]; exact h.fixSub_toTilde hVgH le_rfl hb₀V hb₀₀ hZg
  have hD : centralizerMod V₁ Vp (conjSub g⁻¹ V) = V₁ := h.F95_D_eq hyp5 hg hI
  have hD' : centralizerMod V₁ (conjSub g⁻¹ Vp) V = V₁ := by
    have h1 := h.F95_D_eq hyp5 (H.inv_mem hg) hI'
    rw [inv_inv] at h1
    have h2 := congrArg (conjSub g⁻¹) h1
    rw [conjSub_centralizerMod, hV₁g, conjSub_conjSub_inv] at h2
    exact h2
  have hA : F9Lin.commSub x (tildeOf V₁ (conjClosure Vp H)) ⊓
      F9Lin.fixSub y (tildeOf V₁ (conjClosure Vp H)) = ⊥ := by
    rw [hR1x, hR2y, ← tildeOf_inf h.V₁_le_Vp]
    have e : Vp ⊓ centralizerMod V₁ (conjClosure Vp H) (conjSub g⁻¹ V) =
        centralizerMod V₁ Vp (conjSub g⁻¹ V) := by
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, hz2.2⟩
      · intro hz
        exact ⟨hz.1, hVpU hz.1, hz.2⟩
    rw [e, hD]
    exact tildeOf_eq_bot_of_le le_rfl
  have hB : F9Lin.commSub y (tildeOf V₁ (conjClosure Vp H)) ⊓
      F9Lin.fixSub x (tildeOf V₁ (conjClosure Vp H)) = ⊥ := by
    rw [hR1y, hR2x, ← tildeOf_inf hV₁Vpg]
    have e : conjSub g⁻¹ Vp ⊓ centralizerMod V₁ (conjClosure Vp H) V =
        centralizerMod V₁ (conjSub g⁻¹ Vp) V := by
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        exact ⟨hz1, hz2.2⟩
      · intro hz
        exact ⟨hz.1, hVpgU hz.1, hz.2⟩
    rw [e, hD']
    exact tildeOf_eq_bot_of_le le_rfl
  have hC : Nat.card (F9Lin.commSub x (tildeOf V₁ (conjClosure Vp H))) =
      Nat.card (F9Lin.commSub y (tildeOf V₁ (conjClosure Vp H))) := by
    rw [hR1x, hR1y, tildeOf_conjSub (hH (H.inv_mem hg))]
    exact (card_conjSub _ _).symm
  have hS : ∀ a ∈ tildeOf V₁ (conjClosure Vp H), ∀ b ∈ tildeOf V₁ (conjClosure Vp H),
      a * b = b * a := fun a ha b hb => isElemAbelian_comm h.isElemAbelian_tilde ha hb
  have hS2 : ∀ a ∈ tildeOf V₁ (conjClosure Vp H), a * a = 1 := fun a ha => by
    have := isElemAbelian_pow_eq_one h.isElemAbelian_tilde ha
    rwa [pow_two] at this
  have hxN : x ∈ Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) : Set _) := by
    rw [hx]
    exact secMk_mem_normalizer_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure Vp H) (a := Subgroup.inclusion hH ⟨a₀, h.V_le_H ha₀V⟩)
      (le_normalizer_conjClosure Vp H (h.V_le_H ha₀V))
  have hyN : y ∈ Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) : Set _) := by
    rw [hy]
    exact secMk_mem_normalizer_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure Vp H) (a := Subgroup.inclusion hH ⟨b₀, hVgH hb₀V⟩)
      (le_normalizer_conjClosure Vp H (hVgH hb₀V))
  have hxx1 : x * x = 1 := by
    have : (⟨a₀, h.V_le_H ha₀V⟩ : ↥H) * ⟨a₀, h.V_le_H ha₀V⟩ = 1 := Subtype.ext ha₀₀
    rw [hx, ← map_mul, this, map_one]
  have hyy1 : y * y = 1 := by
    have : (⟨b₀, hVgH hb₀V⟩ : ↥H) * ⟨b₀, hVgH hb₀V⟩ = 1 := Subtype.ext hb₀₀
    rw [hy, ← map_mul, this, map_one]
  have hxx : ∀ e ∈ tildeOf V₁ (conjClosure Vp H), x * x * e * (x * x)⁻¹ = e := fun e _ => by
    rw [hxx1]; simp
  have hyy : ∀ e ∈ tildeOf V₁ (conjClosure Vp H), y * y * e * (y * y)⁻¹ = e := fun e _ => by
    rw [hyy1]; simp
  obtain ⟨-, c2, c3, -, -⟩ :=
    F9Lin.two_involutions_sub hS hS2 hyN hxN hyy hxx hB hA hC.symm
  rw [hR1x, hR1y] at c2 c3
  have hP12 : tildeOf V₁ Vp ⊔ tildeOf V₁ (conjSub g⁻¹ Vp) = tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) :=
    (tildeOf_sup hVpN hVpgN).symm
  have hPY : tildeOf V₁ (conjSub g⁻¹ Vp) ⊔ tildeOf V₁ Vp = tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp) :=
    (sup_comm _ _).trans hP12
  have hUIU : Vp ⊔ conjSub g⁻¹ Vp ≤ conjClosure Vp H := sup_le hVpU hVpgU
  have hV₁UI : V₁ ≤ Vp ⊔ conjSub g⁻¹ Vp := h.V₁_le_Vp.trans le_sup_left
  have hR1yP : F9Lin.commSub y (tildeOf V₁ (Vp ⊔ conjSub g⁻¹ Vp)) =
      tildeOf V₁ ⁅Vp ⊔ conjSub g⁻¹ Vp, conjSub g⁻¹ V⁆ := by
    rw [hy]; exact h.commSub_toTilde hVgH hUIU hb₀V hb₀₀ hZg
  have e2 : (Vp ⊔ conjSub g⁻¹ Vp) ⊓ centralizerMod V₁ (conjClosure Vp H) (conjSub g⁻¹ V) =
      centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) (conjSub g⁻¹ V) := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨hz1, hz2.2⟩
    · intro hz
      exact ⟨hz.1, hUIU hz.1, hz.2⟩
  rw [hR2y, hPY, inf_comm, ← tildeOf_inf hV₁UI, e2] at c2
  rw [hPY, hR1yP] at c3
  exact ⟨c3.symm, c2.symm⟩

theorem F95_dict (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H)
    (hyp5 : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V))
    {g : G} (hg : g ∈ H)
    (hI : ¬ ∀ x ∈ V ⊔ conjSub g⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H)
    {a₀ : G} (ha₀V : a₀ ∈ V) (ha₀₀ : a₀ * a₀ = 1)
    (hZV : ∀ w ∈ V, w ∈ pCoreOf 2 H ∨ w * a₀ ∈ pCoreOf 2 H) :
    (∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, (a₀ * p * a₀⁻¹ * p⁻¹ ∈ V₁ ↔ p ∈ Vp)) ∧
    (∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, a₀ * p * a₀⁻¹ * p⁻¹ ∈ Vp) ∧
    (∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, ((g⁻¹ * a₀ * g) * p * (g⁻¹ * a₀ * g)⁻¹ * p⁻¹ ∈ V₁ ↔
        p ∈ conjSub g⁻¹ Vp)) ∧
    (∀ p ∈ Vp ⊔ conjSub g⁻¹ Vp, (g⁻¹ * a₀ * g) * p * (g⁻¹ * a₀ * g)⁻¹ * p⁻¹ ∈ conjSub g⁻¹ Vp) := by
  have hH := h.H_normalizes_V₁
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hQN : pCoreOf 2 H ≤ Subgroup.normalizer (V₁ : Set G) := hQH.trans hH
  have hUH : conjClosure Vp H ≤ H := hUQ.trans hQH
  have hVpH : Vp ≤ H := h.Vp_le_V.trans h.V_le_H
  have hVpU : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
  have hVpgU : conjSub g⁻¹ Vp ≤ conjClosure Vp H := conjSub_inv_le_U hg hVpU
  have hVpgH : conjSub g⁻¹ Vp ≤ H := hVpgU.trans hUH
  have hVgH : conjSub g⁻¹ V ≤ H := h.conjSub_inv_le_H hg
  have hUIU : Vp ⊔ conjSub g⁻¹ Vp ≤ conjClosure Vp H := sup_le hVpU hVpgU
  have hUIH : Vp ⊔ conjSub g⁻¹ Vp ≤ H := hUIU.trans hUH
  have hV₁Vpg : V₁ ≤ conjSub g⁻¹ Vp := by
    have hV₁g : conjSub g⁻¹ V₁ = V₁ := F7.conjSub_eq_of_mem_normalizer (hH (H.inv_mem hg))
    rw [← hV₁g]
    exact conjSub_mono _ h.V₁_le_Vp
  obtain ⟨-, hUV, -⟩ := h.F95_2_aux hidx hV
  have hii : ∀ p ∈ conjClosure Vp H, a₀ * p * a₀⁻¹ * p⁻¹ ∈ Vp := by
    intro p hp
    have h1 : p * a₀ * p⁻¹ * a₀⁻¹ ∈ ⁅conjClosure Vp H, V⁆ :=
      Subgroup.commutator_mem_commutator hp ha₀V
    have h2 := Vp.inv_mem (hUV h1)
    have e : (p * a₀ * p⁻¹ * a₀⁻¹)⁻¹ = a₀ * p * a₀⁻¹ * p⁻¹ := by group
    rwa [e] at h2
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : G, b₀ = g⁻¹ * a₀ * g := ⟨_, rfl⟩
  rw [← hb₀]
  have hb₀V : b₀ ∈ conjSub g⁻¹ V := by
    rw [mem_conjSub, inv_inv]
    have : g * b₀ * g⁻¹ = a₀ := by rw [hb₀]; group
    rw [this]
    exact ha₀V
  have hb₀₀ : b₀ * b₀ = 1 := by
    have : b₀ * b₀ = g⁻¹ * (a₀ * a₀) * g := by rw [hb₀]; group
    rw [this, ha₀₀]; group
  have hZg : ∀ w ∈ conjSub g⁻¹ V, w ∈ pCoreOf 2 H ∨ w * b₀ ∈ pCoreOf 2 H := by
    intro w hw
    rw [mem_conjSub, inv_inv] at hw
    rcases hZV _ hw with h1 | h1
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (hQn hg) w).mpr h1)
    · refine Or.inr ((Subgroup.mem_normalizer_iff.mp (hQn hg) (w * b₀)).mpr ?_)
      have : g * (w * b₀) * g⁻¹ = (g * w * g⁻¹) * a₀ := by rw [hb₀]; group
      rw [this]
      exact h1
  have hcj : ∀ p : G, g * (b₀ * p * b₀⁻¹ * p⁻¹) * g⁻¹ =
      a₀ * (g * p * g⁻¹) * a₀⁻¹ * (g * p * g⁻¹)⁻¹ := by
    intro p; rw [hb₀]; group
  have hT1 : tildeOf V₁ Vp = tildeOf V₁ (centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) V) :=
    (h.F95_5 hidx hV hyp5 hg hI).tilde_Vp_eq_centralizer
  have hT2 := h.F95_Y_sides hidx hV hyp5 hg hI
  have hcMV : centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) V ≤ H :=
    (centralizerMod_le_left _ _ _).trans hUIH
  have hcMVg : centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) (conjSub g⁻¹ V) ≤ H :=
    (centralizerMod_le_left _ _ _).trans hUIH
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro p hp
    have hpU : p ∈ conjClosure Vp H := hUIU hp
    have hpH : p ∈ H := hUH hpU
    constructor
    · intro hc
      have hpa : p * a₀ * p⁻¹ * a₀⁻¹ ∈ V₁ := by
        have h1 := V₁.inv_mem hc
        have e : (a₀ * p * a₀⁻¹ * p⁻¹)⁻¹ = p * a₀ * p⁻¹ * a₀⁻¹ := by group
        rwa [e] at h1
      have hpcM : p ∈ centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) V :=
        mem_centralizerMod.mpr ⟨hp, hH hpH, fun w hw =>
          RonanF95XY.comm_mem_of_Q hQN ha₀₀ (fun q hq => h.commutator_conjClosure_le p hpU q hq)
            hpa (hZV w hw)⟩
      have hmem : toTilde hH ⟨p, hpH⟩ ∈
          tildeOf V₁ (centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) V) :=
        (mem_tildeOf_iff hH hcMV).mpr ⟨⟨p, hpH⟩, hpcM, rfl⟩
      rw [← hT1] at hmem
      exact RonanF95XY.mem_of_toTilde_mem hH hVpH h.V₁_le_Vp hpH hmem
    · intro hpVp
      have hpV : p ∈ V := h.Vp_le_V hpVp
      have hc : a₀ * p = p * a₀ := isElemAbelian_comm h.elemAbelian ha₀V hpV
      have e : a₀ * p * a₀⁻¹ * p⁻¹ = 1 := by rw [hc]; group
      rw [e]
      exact V₁.one_mem
  ·
    intro p hp
    exact hii p (hUIU hp)
  ·
    intro p hp
    have hpU : p ∈ conjClosure Vp H := hUIU hp
    have hpH : p ∈ H := hUH hpU
    constructor
    · intro hc
      have hpb : p * b₀ * p⁻¹ * b₀⁻¹ ∈ V₁ := by
        have h1 := V₁.inv_mem hc
        have e : (b₀ * p * b₀⁻¹ * p⁻¹)⁻¹ = p * b₀ * p⁻¹ * b₀⁻¹ := by group
        rwa [e] at h1
      have hpcM : p ∈ centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) (conjSub g⁻¹ V) :=
        mem_centralizerMod.mpr ⟨hp, hH hpH, fun w hw =>
          RonanF95XY.comm_mem_of_Q hQN hb₀₀ (fun q hq => h.commutator_conjClosure_le p hpU q hq)
            hpb (hZg w hw)⟩
      have hmem : toTilde hH ⟨p, hpH⟩ ∈
          tildeOf V₁ (centralizerMod V₁ (Vp ⊔ conjSub g⁻¹ Vp) (conjSub g⁻¹ V)) :=
        (mem_tildeOf_iff hH hcMVg).mpr ⟨⟨p, hpH⟩, hpcM, rfl⟩
      rw [← hT2.2] at hmem
      exact RonanF95XY.mem_of_toTilde_mem hH hVpgH hV₁Vpg hpH hmem
    · intro hpg
      have hpg' : g * p * g⁻¹ ∈ Vp := by
        rw [mem_conjSub, inv_inv] at hpg
        exact hpg
      have hc : a₀ * (g * p * g⁻¹) = (g * p * g⁻¹) * a₀ :=
        isElemAbelian_comm h.elemAbelian ha₀V (h.Vp_le_V hpg')
      have h1 : a₀ * (g * p * g⁻¹) * a₀⁻¹ * (g * p * g⁻¹)⁻¹ = 1 := by rw [hc]; group
      have h2 := hcj p
      rw [h1] at h2
      have h3 : b₀ * p * b₀⁻¹ * p⁻¹ = 1 := by
        calc b₀ * p * b₀⁻¹ * p⁻¹ = g⁻¹ * (g * (b₀ * p * b₀⁻¹ * p⁻¹) * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      rw [h3]
      exact V₁.one_mem
  ·
    intro p hp
    have hpU : p ∈ conjClosure Vp H := hUIU hp
    have hpgU : g * p * g⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hg) p).mp hpU
    rw [mem_conjSub, inv_inv, hcj p]
    exact hii _ hpgU

end HypF91

end Fin

end CFSG.Quasithin
