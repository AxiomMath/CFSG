module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenSupp

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

private theorem q2cO5s_map_ggOTwoPrime_conj {G : Type*} [Group G] (w : G) (Y : Subgroup G) :
    (ggOTwoPrime Y).map (MulAut.conj w).toMonoidHom =
      ggOTwoPrime (Y.map (MulAut.conj w).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj w).toMonoidHom := (MulAut.conj w).injective
  rw [ggOTwoPrime, MonoidHom.map_closure, ggOTwoPrime]
  congr 1
  ext z
  constructor
  · rintro ⟨y, ⟨hyY, k, hk⟩, rfl⟩
    exact ⟨⟨y, hyY, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨⟨y, hyY, rfl⟩, k, hk⟩
    exact ⟨y, ⟨hyY, k, hinj (by rw [map_pow, hk, map_one])⟩, rfl⟩

private theorem q2cO5s_map_centralizer_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Set G) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e.toMonoidHom '' S) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image S e.toMonoidHom) ?_
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map]
  refine ⟨x, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro s hs
  have h1 := hy (e s) ⟨s, hs, rfl⟩
  apply e.injective
  rw [map_mul, map_mul]
  exact h1

private theorem q2cO5s_dinv_dinv {m : ℕ} {i k : Fin m} (hik : i ≠ k)
    (f : Fin m → Multiplicative (ZMod p)) : NbrOrth.dinv i k (NbrOrth.dinv i k f) = f := by
  funext j
  rw [OrthNs.dinv_apply_eq, OrthNs.dinv_apply_eq, if_neg hik, if_neg hik]
  by_cases hji : j = i
  · rw [hji, if_pos (Or.inl rfl), if_pos (Or.inl rfl), inv_inv]
  · by_cases hjk : j = k
    · rw [hjk, if_pos (Or.inr rfl), if_pos (Or.inr rfl), inv_inv]
    · have hnot : ¬ (j = i ∨ j = k) := by
        rintro (h' | h')
        · exact hji h'
        · exact hjk h'
      rw [if_neg hnot, if_neg hnot]

private theorem q2cO5s_dinv_mem_coordPos {i j k : Fin r} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) {f : Fin r → Multiplicative (ZMod p)}
    (hf : f ∈ reflFixedCoord p r i j) :
    NbrOrth.dinv j k f ∈ reflFixedCoordPos p r i j := by
  have hfij : f i = f j := by
    have h := hf
    rw [reflFixedCoord, MonoidHom.mem_ker] at h
    change f i / f j = 1 at h
    rwa [div_eq_one] at h
  have hi : NbrOrth.dinv j k f i = f i := by
    rw [OrthNs.dinv_apply_eq, if_neg hjk, if_neg (fun h => h.elim hij hik)]
  have hj : NbrOrth.dinv j k f j = (f j)⁻¹ := by
    rw [OrthNs.dinv_apply_eq, if_neg hjk, if_pos (Or.inl rfl)]
  rw [reflFixedCoordPos, MonoidHom.mem_ker]
  change NbrOrth.dinv j k f i * NbrOrth.dinv j k f j = 1
  rw [hi, hj, hfij, mul_inv_cancel]

private theorem q2cO5s_dinv_mem_coord {i j k : Fin r} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) {g : Fin r → Multiplicative (ZMod p)}
    (hg : g ∈ reflFixedCoordPos p r i j) :
    NbrOrth.dinv j k g ∈ reflFixedCoord p r i j := by
  have hgij : g i = (g j)⁻¹ := by
    have h := hg
    rw [reflFixedCoordPos, MonoidHom.mem_ker] at h
    change g i * g j = 1 at h
    exact mul_eq_one_iff_eq_inv.mp h
  have hi : NbrOrth.dinv j k g i = g i := by
    rw [OrthNs.dinv_apply_eq, if_neg hjk, if_neg (fun h => h.elim hij hik)]
  have hj : NbrOrth.dinv j k g j = (g j)⁻¹ := by
    rw [OrthNs.dinv_apply_eq, if_neg hjk, if_pos (Or.inl rfl)]
  rw [reflFixedCoord, MonoidHom.mem_ker]
  change NbrOrth.dinv j k g i / NbrOrth.dinv j k g j = 1
  rw [hi, hj, div_eq_one]
  exact hgij

theorem TBJOmData.reflFixed_map_dinv (Δ : TBJOmData Q p A r)
    {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (w : V ≃ₗ[K] V)
    (hwconj : ∀ f, w * Δ.τ f * w⁻¹ = Δ.τ (NbrOrth.dinv j k f)) :
    (Δ.reflFixed i j).map (MulAut.conj w).toMonoidHom = Δ.reflFixedPos i j := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    rw [TBJOmData.reflFixed, Subgroup.mem_map] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    refine Subgroup.mem_map.mpr ⟨NbrOrth.dinv j k f,
      q2cO5s_dinv_mem_coordPos hij hjk hik hf, ?_⟩
    have hconj : (MulAut.conj w).toMonoidHom (Δ.τ f) = w * Δ.τ f * w⁻¹ :=
      MulAut.conj_apply w (Δ.τ f)
    rw [hconj, hwconj f]
  · intro hz
    rw [TBJOmData.reflFixedPos, Subgroup.mem_map] at hz
    obtain ⟨g, hg, rfl⟩ := hz
    refine Subgroup.mem_map.mpr ⟨Δ.τ (NbrOrth.dinv j k g), ?_, ?_⟩
    · rw [TBJOmData.reflFixed, Subgroup.mem_map]
      exact ⟨NbrOrth.dinv j k g, q2cO5s_dinv_mem_coord hij hjk hik hg, rfl⟩
    · have hconj : (MulAut.conj w).toMonoidHom (Δ.τ (NbrOrth.dinv j k g)) =
          w * Δ.τ (NbrOrth.dinv j k g) * w⁻¹ := MulAut.conj_apply w _
      rw [hconj, hwconj (NbrOrth.dinv j k g), q2cO5s_dinv_dinv hjk g]

private theorem q2cO5s_mem_piece_iff_fixed (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (l : Fin r) {v : V} :
    v ∈ Δ.F.U l ↔ ∀ f : Fin r → Multiplicative (ZMod p), f l = 1 → Δ.τ f v = v := by
  constructor
  · intro hv f hfl
    rw [Δ.τ_eq]
    refine Δ.F.triv (piMul r p f) l ?_ v hv
    simp [piMul_apply, hfl]
  · intro hv
    have horm : ∀ m, m ≠ l → ∀ u ∈ Δ.F.U m, polar Q u v = 0 := by
      intro m hml u hu
      have hfl : (Pi.mulSingle m (ofAdd 1) : Fin r → Multiplicative (ZMod p)) l = 1 := by
        show Function.update (1 : Fin r → Multiplicative (ZMod p)) m (ofAdd 1) l = 1
        rw [Function.update_of_ne (Ne.symm hml)]
        rfl
      have hvv := hv _ hfl
      rw [Δ.τ_eq] at hvv
      have h0 : toAdd (piMul r p (Pi.mulSingle m (ofAdd 1))) m ≠ 0 := by
        simpa [piMul_apply] using (one_ne_zero : (1 : ZMod p) ≠ 0)
      exact (Δ.F.fix (piMul r p (Pi.mulSingle m (ofAdd 1))) v).mp hvv m h0 u hu
    obtain ⟨w, hw, hvw⟩ := Δ.exists_sum_pieces hfix v
    have hzero : ∀ m, m ≠ l → w m = 0 := by
      intro m hml
      exact TBJOmData.component_eq_zero_of_orthogonal Δ hw hvw.symm (horm m hml)
    rw [← hvw]
    rw [Finset.sum_eq_single l]
    · exact hw l
    · intro m _ hml
      exact hzero m hml
    · intro hl
      exact absurd (Finset.mem_univ l) hl

private theorem q2cO5s_piece_preserved (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) {j k : Fin r} (hjk : j ≠ k)
    {w : V ≃ₗ[K] V} (hwconj : ∀ f, w * Δ.τ f * w⁻¹ = Δ.τ (NbrOrth.dinv j k f))
    {l : Fin r} (hl : l = j ∨ l = k) :
    ∀ u ∈ Δ.F.U l, w u ∈ Δ.F.U l ∧ w⁻¹ u ∈ Δ.F.U l := by
  intro u hu
  have hgl_eq : ∀ f : Fin r → Multiplicative (ZMod p),
      NbrOrth.dinv j k f l = (f l)⁻¹ := by
    intro f
    rw [OrthNs.dinv_apply_eq, if_neg hjk]
    rcases hl with rfl | rfl
    · rw [if_pos (Or.inl rfl)]
    · rw [if_pos (Or.inr rfl)]
  constructor
  · rw [q2cO5s_mem_piece_iff_fixed Δ hfix l]
    intro f hfl
    set gcoord := NbrOrth.dinv j k f with hgcoord
    have hgl : gcoord l = 1 := by rw [hgcoord, hgl_eq f, hfl, inv_one]
    have hgfix : Δ.τ gcoord u = u := by
      rw [Δ.τ_eq]
      refine Δ.F.triv (piMul r p gcoord) l ?_ u hu
      simp [piMul_apply, hgl]
    have hτf : Δ.τ f = w * Δ.τ gcoord * w⁻¹ := by
      rw [hwconj gcoord, hgcoord, q2cO5s_dinv_dinv hjk f]
    have step : (w * Δ.τ gcoord * w⁻¹) (w u) = w u := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' w u, hgfix]
    rw [hτf]
    exact step
  · rw [q2cO5s_mem_piece_iff_fixed Δ hfix l]
    intro f hfl
    set gcoord := NbrOrth.dinv j k f with hgcoord
    have hgl : gcoord l = 1 := by rw [hgcoord, hgl_eq f, hfl, inv_one]
    have hgfix : Δ.τ gcoord u = u := by
      rw [Δ.τ_eq]
      refine Δ.F.triv (piMul r p gcoord) l ?_ u hu
      simp [piMul_apply, hgl]
    have h1 : w (Δ.τ f (w⁻¹ u)) = u := by
      calc w (Δ.τ f (w⁻¹ u)) = (w * Δ.τ f * w⁻¹) u := by
              rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        _ = Δ.τ gcoord u := by rw [hwconj f, ← hgcoord]
        _ = u := hgfix
    exact w.injective (by rw [h1,
      CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply' w u])

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem ggOTwoPrime_orthCentralizer_map_conj (w : V ≃ₗ[K] V) (hwΩ : w ∈ orthDerived Q)
    (H H' : Subgroup (V ≃ₗ[K] V))
    (hH : H.map (MulAut.conj w).toMonoidHom = H') :
    (ggOTwoPrime (Subgroup.centralizer (H : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q)).map
        (MulAut.conj w).toMonoidHom =
      ggOTwoPrime (Subgroup.centralizer (H' : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q) := by
  have hΩ : (orthDerived Q).map (MulAut.conj w).toMonoidHom = orthDerived Q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hconj : (MulAut.conj w).toMonoidHom x = w * x * w⁻¹ := MulAut.conj_apply w x
      rw [hconj]
      exact (orthDerived Q).mul_mem ((orthDerived Q).mul_mem hwΩ hx)
        ((orthDerived Q).inv_mem hwΩ)
    · intro hy
      refine ⟨w⁻¹ * y * w, (orthDerived Q).mul_mem
        ((orthDerived Q).mul_mem ((orthDerived Q).inv_mem hwΩ) hy) hwΩ, ?_⟩
      have hconj : (MulAut.conj w).toMonoidHom (w⁻¹ * y * w) =
          w * (w⁻¹ * y * w) * w⁻¹ := MulAut.conj_apply w _
      rw [hconj]
      group
  have hcent : (Subgroup.centralizer (H : Set (V ≃ₗ[K] V))).map
      (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer (H' : Set (V ≃ₗ[K] V)) := by
    rw [q2cO5s_map_centralizer_mulEquiv (MulAut.conj w)
      (H : Set (V ≃ₗ[K] V))]
    rw [← Subgroup.coe_map (MulAut.conj w).toMonoidHom H, hH]
  have hY : (Subgroup.centralizer (H : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q).map
      (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer (H' : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj w).injective, hcent, hΩ]
  rw [q2cO5s_map_ggOTwoPrime_conj w
    (Subgroup.centralizer (H : Set (V ≃ₗ[K] V)) ⊓ orthDerived Q), hY]

theorem TBJOmData.rankOne_map_dinv (Δ : TBJOmData Q p A r)
    {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (w : V ≃ₗ[K] V)
    (hwΩ : w ∈ orthDerived Q)
    (hwconj : ∀ f, w * Δ.τ f * w⁻¹ = Δ.τ (NbrOrth.dinv j k f)) :
    (Δ.rankOne i j).map (MulAut.conj w).toMonoidHom = Δ.rankOnePos i j := by
  exact ggOTwoPrime_orthCentralizer_map_conj w hwΩ _ _
    (Δ.reflFixed_map_dinv hij hjk hik w hwconj)

theorem TBJOmData.reflFixed_map_dinv_self (Δ : TBJOmData Q p A r)
    {i j : Fin r} (hij : i ≠ j) (w : V ≃ₗ[K] V)
    (hwconj : ∀ f, w * Δ.τ f * w⁻¹ = Δ.τ (NbrOrth.dinv i j f)) :
    (Δ.reflFixed i j).map (MulAut.conj w).toMonoidHom = Δ.reflFixed i j := by
  have hcoord : ∀ f : Fin r → Multiplicative (ZMod p),
      NbrOrth.dinv i j f ∈ reflFixedCoord p r i j ↔ f ∈ reflFixedCoord p r i j := by
    intro f
    have hi : NbrOrth.dinv i j f i = (f i)⁻¹ := by
      rw [OrthNs.dinv_apply_eq, if_neg hij, if_pos (Or.inl rfl)]
    have hj : NbrOrth.dinv i j f j = (f j)⁻¹ := by
      rw [OrthNs.dinv_apply_eq, if_neg hij, if_pos (Or.inr rfl)]
    simp only [reflFixedCoord, MonoidHom.mem_ker, MonoidHom.div_apply]
    change (NbrOrth.dinv i j f i / NbrOrth.dinv i j f j = 1) ↔ f i / f j = 1
    rw [hi, hj, div_eq_one, div_eq_one, _root_.inv_inj]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨f, hf, rfl⟩ := hy
    exact ⟨NbrOrth.dinv i j f, (hcoord f).mpr hf, (hwconj f).symm⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨Δ.τ (NbrOrth.dinv i j f), ⟨NbrOrth.dinv i j f, (hcoord f).mpr hf, rfl⟩, ?_⟩
    change w * Δ.τ (NbrOrth.dinv i j f) * w⁻¹ = Δ.τ f
    rw [hwconj, q2cO5s_dinv_dinv hij]

theorem TBJOmData.rankOne_map_dinv_self (Δ : TBJOmData Q p A r)
    {i j : Fin r} (hij : i ≠ j) (w : V ≃ₗ[K] V) (hwΩ : w ∈ orthDerived Q)
    (hwconj : ∀ f, w * Δ.τ f * w⁻¹ = Δ.τ (NbrOrth.dinv i j f)) :
    (Δ.rankOne i j).map (MulAut.conj w).toMonoidHom = Δ.rankOne i j := by
  exact ggOTwoPrime_orthCentralizer_map_conj w hwΩ _ _
    (Δ.reflFixed_map_dinv_self hij w hwconj)

theorem TBJOmData.exists_dinv_conj (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ∃ w ∈ orthDerived Q, (∀ l, l ≠ j → l ≠ k → ∀ u ∈ Δ.F.U l, w u = u) ∧
      (∀ l, ∀ u ∈ Δ.F.U l, w u ∈ Δ.F.U l ∧ w⁻¹ u ∈ Δ.F.U l) ∧
      Δ.rankOnePos i j = (Δ.rankOne i j).map (MulAut.conj w).toMonoidHom := by
  classical
  obtain ⟨w, hwΩ, hwfix, hwconj⟩ := Δ.dinvMove j k hjk
  have hwfix' : ∀ l, l ≠ j → l ≠ k → ∀ u ∈ Δ.F.U l, w u = u := by
    intro l hlj hlk u hu
    exact hwfix u (fun u' hu' => Δ.F.orth j l (Ne.symm hlj) u' hu' u hu)
      (fun u' hu' => Δ.F.orth k l (Ne.symm hlk) u' hu' u hu)
  have hpres : ∀ l, ∀ u ∈ Δ.F.U l, w u ∈ Δ.F.U l ∧ w⁻¹ u ∈ Δ.F.U l := by
    intro l u hu
    by_cases hlj : l = j
    · subst hlj
      exact q2cO5s_piece_preserved Δ hfix hjk hwconj (Or.inl rfl) u hu
    · by_cases hlk : l = k
      · subst hlk
        exact q2cO5s_piece_preserved Δ hfix hjk hwconj (Or.inr rfl) u hu
      · have hwu : w u = u := hwfix' l hlj hlk u hu
        have hw'u : w⁻¹ u = u := by
          calc w⁻¹ u = w⁻¹ (w u) := by rw [hwu]
            _ = u := CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' w u
        exact ⟨by rw [hwu]; exact hu, by rw [hw'u]; exact hu⟩
  refine ⟨w, hwΩ, hwfix', hpres, ?_⟩
  exact (Δ.rankOne_map_dinv hij hjk hik w hwΩ hwconj).symm

theorem TBJOmData.fixes_outside_rankOne (Δ : TBJOmData Q p A r) (h2 : Δ.RankOneModel)
    {i j : Fin r} (hij : i ≠ j) :
    ∀ x ∈ Δ.rankOne i j, ∀ l, l ≠ i → l ≠ j → ∀ u ∈ Δ.F.U l, x u = u := by
  obtain ⟨⟨θ, -, hrange, hfixed⟩, -⟩ := h2 i j hij
  intro x hx l hli hlj u hu
  rw [← hrange] at hx
  exact hfixed x hx l hli hlj u hu

theorem TBJOmData.fixes_outside_rankOnePos (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (hr : 3 ≤ r) (h2 : Δ.RankOneModel)
    {i j : Fin r} (hij : i ≠ j) :
    ∀ y ∈ Δ.rankOnePos i j, ∀ l, l ≠ i → l ≠ j → ∀ u ∈ Δ.F.U l, y u = u := by
  classical
  have hcard : ({i, j} : Finset (Fin r)).card < (Finset.univ : Finset (Fin r)).card := by
    have h1 : ({i, j} : Finset (Fin r)).card ≤ 2 := by
      calc ({i, j} : Finset (Fin r)).card = (insert i ({j} : Finset (Fin r))).card := rfl
        _ ≤ ({j} : Finset (Fin r)).card + 1 := Finset.card_insert_le i _
        _ = 2 := by simp
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_singleton] at hk
  have hki : k ≠ i := fun h => hk (Or.inl h)
  have hkj : k ≠ j := fun h => hk (Or.inr h)
  obtain ⟨w, -, -, hpres, hwconj⟩ :=
    Δ.exists_dinv_conj hfix hij (Ne.symm hkj) (Ne.symm hki)
  intro y hy l hli hlj u hu
  rw [hwconj] at hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hw'u : w⁻¹ u ∈ Δ.F.U l := (hpres l u hu).2
  have hxw : x (w⁻¹ u) = w⁻¹ u :=
    Δ.fixes_outside_rankOne h2 hij x hx l hli hlj (w⁻¹ u) hw'u
  have hconj : (MulAut.conj w).toMonoidHom x = w * x * w⁻¹ := MulAut.conj_apply w x
  rw [hconj, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxw,
    CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply' w u]

end OrthTorus

end CFSG.StandardType

end
