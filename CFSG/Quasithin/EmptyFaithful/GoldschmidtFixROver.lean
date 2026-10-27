module

public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRAml
public import CFSG.Quasithin.EmptyFaithful.S152Y22

public section

namespace CFSG.Quasithin.FixR

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp X : Subgroup G}

@[expose] def sig (h : HypF91 T V L V₁ Vp X) :
    ↥X →* SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁ :=
  (secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp (Subgroup.inclusion h.H_normalizes_V₁)

omit [Finite G] in
theorem sig_apply (h : HypF91 T V L V₁ Vp X) (x : ↥X) :
    sig h x = secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, h.H_normalizes_V₁ x.2⟩ := rfl

omit [Finite G] in
theorem sig_mem_normalizer (h : HypF91 T V L V₁ Vp X) (x : ↥X) :
    sig h x ∈ Subgroup.normalizer
      (tildeOf V₁ (conjClosure Vp X) : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
  HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) (le_refl X)
    (secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨x, h.H_normalizes_V₁ x.2⟩) x.2)

@[expose] noncomputable def rho (h : HypF91 T V L V₁ Vp X) :
    ↥X →* MulAut ↥(tildeOf V₁ (conjClosure Vp X)) :=
  (conjAct (tildeOf V₁ (conjClosure Vp X))).comp
    ((sig h).codRestrict _ (sig_mem_normalizer h))

omit [Finite G] in
theorem rho_coe (h : HypF91 T V L V₁ Vp X) (x : ↥X) (w : ↥(tildeOf V₁ (conjClosure Vp X))) :
    ((rho h x w : ↥(tildeOf V₁ (conjClosure Vp X))) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) = sig h x * w * (sig h x)⁻¹ :=
  conjAct_apply_coe' _ ⟨sig h x, sig_mem_normalizer h x⟩ w

omit [Finite G] in
theorem conj_secMk_eq_iff {g u : G} (hg : g ∈ Subgroup.normalizer (V₁ : Set G))
    (hu : u ∈ Subgroup.normalizer (V₁ : Set G)) :
    secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨g, hg⟩ *
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, hu⟩ *
        (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨g, hg⟩)⁻¹ =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, hu⟩ ↔ g * u * g⁻¹ * u⁻¹ ∈ V₁ := by
  rw [← map_inv, ← map_mul, ← map_mul, secMk_eq_secMk_iff]
  show (g * u * g⁻¹)⁻¹ * u ∈ V₁ ↔ _
  have e : (g * u * g⁻¹)⁻¹ * u = u⁻¹ * (g * u * g⁻¹ * u⁻¹)⁻¹ * u⁻¹⁻¹ := by group
  rw [e, ← Subgroup.mem_normalizer_iff.mp (inv_mem hu) (g * u * g⁻¹ * u⁻¹)⁻¹, Subgroup.inv_mem_iff]

theorem rho_eq_one_iff (h : HypF91 T V L V₁ Vp X) (x : ↥X) :
    rho h x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
  rw [h.pCoreOf_eq_centralizerMod]
  have hUN : ∀ u ∈ conjClosure Vp X, u ∈ Subgroup.normalizer (V₁ : Set G) := fun u hu =>
    h.H_normalizes_V₁ (pCoreOf_le 2 X (h.conjClosure_Vp_le_pCoreOf hu))
  constructor
  · intro h1
    refine ⟨x.2, h.H_normalizes_V₁ x.2, fun u hu => ?_⟩
    have hw : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, hUN u hu⟩ ∈
        tildeOf V₁ (conjClosure Vp X) := secMk_mem_secImg hu
    have h2 := congrArg (fun a : MulAut ↥(tildeOf V₁ (conjClosure Vp X)) =>
      ((a ⟨_, hw⟩ : ↥(tildeOf V₁ (conjClosure Vp X))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) h1
    simp only [MulAut.one_apply, rho_coe, sig_apply] at h2
    exact (conj_secMk_eq_iff _ _).mp h2
  · rintro ⟨-, -, hc⟩
    refine MulEquiv.ext fun w => ?_
    obtain ⟨w', hw'⟩ := w
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw'
    apply Subtype.ext
    rw [MulAut.one_apply, rho_coe, sig_apply]
    exact (conj_secMk_eq_iff _ _).mpr (hc _ hu)

omit [Finite G] in
theorem mem_autOn_tilde_iff (h : HypF91 T V L V₁ Vp X) {Y : Subgroup G} (hY : Y ≤ X)
    {a : MulAut ↥(tildeOf V₁ (conjClosure Vp X))} :
    a ∈ autOn (tildeOf V₁ Y) (tildeOf V₁ (conjClosure Vp X)) ↔
      ∃ y : ↥X, (y : G) ∈ Y ∧ rho h y = a := by
  rw [mem_autOn_iff]
  constructor
  · rintro ⟨s, hsY, rfl⟩
    obtain ⟨x, hxY, hxs⟩ := mem_secImg.mp hsY
    refine ⟨⟨x, hY hxY⟩, hxY, ?_⟩
    have hs : (⟨sig h ⟨x, hY hxY⟩, sig_mem_normalizer h _⟩ :
        ↥(Subgroup.normalizer (tildeOf V₁ (conjClosure Vp X) :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))) = s := Subtype.ext hxs
    show conjAct _ ⟨sig h ⟨x, hY hxY⟩, sig_mem_normalizer h ⟨x, hY hxY⟩⟩ = conjAct _ s
    rw [hs]
  · rintro ⟨y, hyY, rfl⟩
    refine ⟨⟨sig h y, sig_mem_normalizer h y⟩, ?_, rfl⟩
    exact secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨y, h.H_normalizes_V₁ y.2⟩) hyY

theorem rho_comm_of_mem (h : HypF91 T V L V₁ Vp X) {x y : ↥X}
    (hc : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 X) :
    rho h x * rho h y = rho h y * rho h x := by
  have hcX : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ X := pCoreOf_le 2 X hc
  have e : x * y = (⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, hcX⟩ : ↥X) * (y * x) :=
    Subtype.ext (by simp [mul_assoc])
  have h1 : rho h ⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, hcX⟩ = 1 := (rho_eq_one_iff h _).mpr hc
  rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]

theorem mem_of_rho_comm (h : HypF91 T V L V₁ Vp X) {x y : ↥X}
    (hc : rho h x * rho h y = rho h y * rho h x) :
    (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 X := by
  have h1 : rho h (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  exact (rho_eq_one_iff h _).mp h1

theorem false_of_f9 (h98 : HypF98 T V L V₁ Vp X) (hL1 : L₁Of L V₁ = ⊥) {K : Subgroup G}
    (hTX : T ≤ X) (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hKab : ∀ k ∈ K, ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K)
    (hK25 : (pCoreOf 2 K).relIndex K = 25) (hK5 : ∀ k ∈ K, k ^ 5 ∈ pCoreOf 2 K)
    (hKer : ∀ b ∈ T, (∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 K) → b ∈ pCoreOf 2 X)
    {n : G} (hn : n ∈ X) (hn5 : ∀ k ∈ K, n ^ 5 * k * (n ^ 5)⁻¹ * k⁻¹ ∈ pCoreOf 2 K)
    (hn1 : ∃ k ∈ K, n * k * n⁻¹ * k⁻¹ ∉ pCoreOf 2 K) : False := by
  have h91 : HypF91 T V L V₁ Vp X := h98.toHypF91
  have hE : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp X)) := h91.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf V₁ (conjClosure Vp X)) := commGroupOfElemAbelian hE
  obtain ⟨-, B, hBL, hBmem⟩ := h98.F916_3
  have hBT : B ≤ T := by
    rw [hL1, bot_sup_eq] at hBL
    exact hBL.trans (pCoreOf_le 2 T)
  have hW : ∀ w : ↥(tildeOf V₁ (conjClosure Vp X)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hE.2 w w.2)
  obtain ⟨⟨hA2, hAr2⟩, -⟩ := hBmem
  have hAr := (rAV_le_two_iff hW hA2).mp hAr2
  have hKQ : pCoreOf 2 K = K ⊓ pCoreOf 2 X := S152Y.pCoreOf_eq_inf_of_normalizer hKX hXK
  have hKQX : pCoreOf 2 K ≤ pCoreOf 2 X := hKQ ▸ inf_le_right
  have hmemP : ∀ k : ↥X, (k : G) ∈ K →
      rho h91 k ∈ autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)) := fun k hk =>
    (mem_autOn_tilde_iff h91 hKX).mpr ⟨k, hk, rfl⟩
  have hPc : ∀ a ∈ autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)),
      ∀ b ∈ autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)), a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := (mem_autOn_tilde_iff h91 hKX).mp ha
    obtain ⟨y, hy, rfl⟩ := (mem_autOn_tilde_iff h91 hKX).mp hb
    exact rho_comm_of_mem h91 (hKQX (hKab _ hx _ hy))
  have hP : Nat.card (autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X))) = 25 := by
    rw [HypF91.card_autOn_tilde h91 hKX, ← hKQ]
    exact hK25
  have hP5 : ∀ κ ∈ autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)), κ ^ 5 = 1 := by
    intro κ hκ
    obtain ⟨x, hx, rfl⟩ := (mem_autOn_tilde_iff h91 hKX).mp hκ
    rw [← map_pow]
    exact (rho_eq_one_iff h91 _).mpr (hKQX (hK5 _ hx))
  have hnorm : ∀ x : ↥X, rho h91 x ∈ Subgroup.normalizer
      (autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)) :
        Set (MulAut ↥(tildeOf V₁ (conjClosure Vp X)))) := by
    intro x
    rw [Subgroup.mem_normalizer_iff]
    intro κ
    constructor
    · intro hκ
      obtain ⟨k, hk, rfl⟩ := (mem_autOn_tilde_iff h91 hKX).mp hκ
      have hk' : (x : G) * k * (x : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hXK x.2) k).mp hk
      have := hmemP (x * k * x⁻¹) hk'
      simpa [map_mul, map_inv] using this
    · intro hκ
      obtain ⟨k, hk, hkκ⟩ := (mem_autOn_tilde_iff h91 hKX).mp hκ
      have hk' : (x : G)⁻¹ * k * (x : G) ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (hXK (X.inv_mem x.2)) k).mp hk
        simpa using this
      have := hmemP (x⁻¹ * k * x) hk'
      have e : rho h91 (x⁻¹ * k * x) =
          (rho h91 x)⁻¹ * (rho h91 x * κ * (rho h91 x)⁻¹) * rho h91 x := by
        rw [map_mul, map_mul, map_inv, hkκ]
      rw [e] at this
      simpa [mul_assoc] using this
  have hAle : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp X)) ≤
      autOn (tildeOf V₁ X) (tildeOf V₁ (conjClosure Vp X)) := hA2.1
  have hBX : B ≤ X := hBT.trans hTX
  have hAN : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp X)) ≤ Subgroup.normalizer
      (autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)) :
        Set (MulAut ↥(tildeOf V₁ (conjClosure Vp X)))) := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := (mem_autOn_tilde_iff h91 hBX).mp ha
    exact hnorm x
  have hAf : ∀ a ∈ autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp X)),
      (∀ κ ∈ autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)), a * κ = κ * a) → a = 1 := by
    intro a ha hcomm
    obtain ⟨b, hbB, rfl⟩ := (mem_autOn_tilde_iff h91 hBX).mp ha
    have hbK : ∀ k ∈ K, (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro k hk
      have h1 := mem_of_rho_comm h91 (hcomm _ (hmemP ⟨k, hKX hk⟩ hk) :
        rho h91 b * rho h91 ⟨k, hKX hk⟩ = rho h91 ⟨k, hKX hk⟩ * rho h91 b)
      rw [hKQ]
      refine ⟨?_, h1⟩
      have h2 : (b : G) * k * (b : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hXK b.2) k).mp hk
      exact K.mul_mem h2 (K.inv_mem hk)
    exact (rho_eq_one_iff h91 b).mpr (hKer b (hBT hbB) hbK)
  have hxN := hnorm ⟨n, hn⟩
  have hx5 : ∀ κ ∈ autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)),
      rho h91 ⟨n, hn⟩ ^ 5 * κ = κ * rho h91 ⟨n, hn⟩ ^ 5 := by
    intro κ hκ
    obtain ⟨k, hk, rfl⟩ := (mem_autOn_tilde_iff h91 hKX).mp hκ
    rw [← map_pow]
    exact rho_comm_of_mem h91 (x := (⟨n, hn⟩ : ↥X) ^ 5) (y := k) (hKQX (hn5 k hk))
  have hx1 : ∃ κ ∈ autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X)),
      rho h91 ⟨n, hn⟩ * κ ≠ κ * rho h91 ⟨n, hn⟩ := by
    obtain ⟨k, hk, hnk⟩ := hn1
    refine ⟨rho h91 ⟨k, hKX hk⟩, hmemP ⟨k, hKX hk⟩ hk, fun hc => hnk ?_⟩
    have h1 := mem_of_rho_comm h91 hc
    rw [hKQ]
    refine ⟨?_, h1⟩
    have h2 : n * k * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hXK hn) k).mp hk
    exact K.mul_mem h2 (K.inv_mem hk)
  have hA := hA2.2.2
  have hA0 := hA2.2.1
  have hP' : Nat.card (autOn (tildeOf V₁ K) (tildeOf V₁ (conjClosure Vp X))) = 25 := hP
  exact aml_false' hW hPc hP' hP5 hA hA0 hAN hAf hAr hxN hx5 hx1

end CFSG.Quasithin.FixR
