module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneD4Frame
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmModel

public section

namespace CFSG.StandardType

namespace RootPlaneD4

open Module QuadraticMap Multiplicative NoOffOm SUTB CFSG.Assembly RootPlaneOm
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.ClassicalGroups.Orthogonal

section Blocks

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem four_blocks {r : ℕ} {U : Fin r → Submodule K (Fin d → K)}
    (hUnd : ∀ i, NondegOn (polB Q) (U i)) (hUne : ∀ i, U i ≠ ⊥)
    (horth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polB Q u v = 0) (hd : d ≤ 8)
    (ι : Fin 4 → Fin r) (hι : Function.Injective ι) :
    (∀ k, finrank K (U (ι k)) = 2) ∧ (U (ι 0) ⊔ U (ι 1)) ⊔ (U (ι 2) ⊔ U (ι 3)) = ⊤ := by
  have hB : ∀ v, polB Q v v = 0 := fun v => OrdPNsOm.polar_self_charTwo v
  have h2 : ∀ a, 2 ≤ finrank K (U a) := fun a => two_le_finrank hB (hUnd a) (hUne a)
  have hsupnd : ∀ a b, a ≠ b → NondegOn (polB Q) (U a ⊔ U b) := fun a b hab =>
    nondegOn_sup (hUnd a) (hUnd b) fun u hu v hv => ⟨horth b a (Ne.symm hab) u hu v hv,
      horth a b hab v hv u hu⟩
  have hfr2 : ∀ a b, a ≠ b → finrank K ↥(U a ⊔ U b) = finrank K (U a) + finrank K (U b) := by
    intro a b hab
    have hinf : U a ⊓ U b = ⊥ := (Submodule.eq_bot_iff _).mpr fun v hv =>
      hUnd a v hv.1 fun n hn => horth a b hab n hn v hv.2
    have h := Submodule.finrank_sup_add_finrank_inf_eq (U a) (U b)
    rwa [hinf, finrank_bot, add_zero] at h
  have hne : ∀ k l : Fin 4, k ≠ l → ι k ≠ ι l := fun k l hkl h => hkl (hι h)
  set X := U (ι 0) ⊔ U (ι 1) with hX
  set Y := U (ι 2) ⊔ U (ι 3) with hY
  have hXY : ∀ x ∈ X, ∀ y ∈ Y, polB Q x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add, LinearMap.add_apply]
    rw [horth _ _ (hne 0 2 (by decide)) a ha a' ha', horth _ _ (hne 0 3 (by decide)) a ha b' hb',
      horth _ _ (hne 1 2 (by decide)) b hb a' ha', horth _ _ (hne 1 3 (by decide)) b hb b' hb']
    simp
  have hinfXY : X ⊓ Y = ⊥ := (Submodule.eq_bot_iff _).mpr fun v hv =>
    hsupnd _ _ (hne 0 1 (by decide)) v hv.1 fun n hn => hXY n hn v hv.2
  have hfrXY := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [hinfXY, finrank_bot, add_zero, hfr2 _ _ (hne 0 1 (by decide)),
    hfr2 _ _ (hne 2 3 (by decide))] at hfrXY
  have hle : finrank K ↥(X ⊔ Y) ≤ d := by
    have := Submodule.finrank_le (X ⊔ Y)
    rwa [Module.finrank_fin_fun] at this
  have h20 := h2 (ι 0)
  have h21 := h2 (ι 1)
  have h22 := h2 (ι 2)
  have h23 := h2 (ι 3)
  have e0 : finrank K (U (ι 0)) = 2 := by omega
  have e1 : finrank K (U (ι 1)) = 2 := by omega
  have e2 : finrank K (U (ι 2)) = 2 := by omega
  have e3 : finrank K (U (ι 3)) = 2 := by omega
  refine ⟨fun k => ?_, Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)⟩
  fin_cases k
  all_goals first | exact e0 | exact e1 | exact e2 | exact e3

theorem eq_four (hnd : Q.polarBilin.Nondegenerate) {r : ℕ} (hr : 4 ≤ r)
    {U : Fin r → Submodule K (Fin d → K)} (hUnd : ∀ i, NondegOn (polB Q) (U i))
    (hUne : ∀ i, U i ≠ ⊥) (horth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polB Q u v = 0)
    (hd : d ≤ 8) : r = 4 := by
  by_contra hr4
  set ι : Fin 4 → Fin r := fun k => ⟨k, by omega⟩ with hι
  have hιinj : Function.Injective ι := fun a b h => Fin.ext (by
    have := congrArg Fin.val h
    simpa [hι] using this)
  obtain ⟨-, htop⟩ := four_blocks hUnd hUne horth hd ι hιinj
  set j : Fin r := ⟨4, by omega⟩ with hj
  have hjne : ∀ k, ι k ≠ j := fun k h => by
    have := congrArg Fin.val h
    simp only [hι, hj] at this
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hUne j)
  have hk : ∀ k, u ∈ (U (ι k)).orthogonalBilin (polB Q) := fun k =>
    Submodule.mem_orthogonalBilin.mpr fun m hm => horth (ι k) j (hjne k) m hm u hu
  have hu' : u ∈ ((U (ι 0) ⊔ U (ι 1)) ⊔ (U (ι 2) ⊔ U (ι 3))).orthogonalBilin (polB Q) :=
    mem_orth_sup_iff.mpr ⟨mem_orth_sup_iff.mpr ⟨hk 0, hk 1⟩, mem_orth_sup_iff.mpr ⟨hk 2, hk 3⟩⟩
  rw [htop] at hu'
  exact hu0 (hnd.2 u fun w => (Submodule.mem_orthogonalBilin.mp hu') w Submodule.mem_top)

omit [CharP K 2] in
theorem exists_sum_eq {U : Fin 4 → Submodule K (Fin d → K)}
    (htop : (U 0 ⊔ U 1) ⊔ (U 2 ⊔ U 3) = ⊤) (v : Fin d → K) :
    ∃ x : Fin 4 → Fin d → K, (∀ i, x i ∈ U i) ∧ v = ∑ i, x i := by
  have hv : v ∈ (U 0 ⊔ U 1) ⊔ (U 2 ⊔ U 3) := htop ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, hc, e, he, rfl⟩ := Submodule.mem_sup.mp hz
  refine ⟨![a, b, c, e], fun i => ?_, ?_⟩
  · fin_cases i
    exacts [ha, hb, hc, he]
  · simp [Fin.sum_univ_four, add_assoc]

end Blocks

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_rootPlane_d4_core (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hd : d ≤ 8)
    {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B Bs D J : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBBs : B ≤ Bs) (hcardB : p ^ 4 ≤ Nat.card B) (hDcard : Nat.card D = p ^ 2)
    (hDJ : D = B ⊓ Subgroup.centralizer (J : Set G)) (hJ : ⁅J, J⁆ = J)
    {φ : matrixDerived Q →* G} (hφ : Function.Injective φ) (hBφ : Bs ≤ φ.range)
    (hJφ : J ≤ φ.range)
    {a₀ a₁ w : Fin d → K} (ha₀ : Q a₀ = 0) (ha₁ : Q a₁ = 0) (ha : polar Q a₀ a₁ = 0)
    (hai : LinearIndependent K ![a₀, a₁]) (hw : Q w ≠ 0) (hw₀ : polar Q w a₀ = 0)
    (hw₁ : polar Q w a₁ = 0) :
    ∃ g : matrixDerived Q, ∀ e ∈ D, ∀ X : matrixDerived Q, (∃ c : K, ∀ y,
        glin (X : GL (Fin d) K) y = y + (c * polar Q y a₁) • a₀ - (c * polar Q y a₀) • a₁) →
      e * φ (g * X * g⁻¹) = φ (g * X * g⁻¹) * e := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hA := genMax_of_orth hnd hT hp hp2 hBs hSC φ hφ hBφ
  obtain ⟨r, ι₀, U, hinj, hrange, hUnd, hUne, horth, hfix, hinv⟩ := exists_blockFrame hA
  have hι₀A : ∀ s, ι₀ s ∈ (Bs.comap φ).map (matrixDerived Q).subtype := fun s =>
    hrange ▸ ⟨s, rfl⟩
  have hι₀Γ : ∀ s, ι₀ s ∈ matrixDerived Q := fun s => hA.le (hι₀A s)
  set ι₁ : Multiplicative (Fin r → ZMod p) →* matrixDerived Q := ι₀.codRestrict _ hι₀Γ with hι₁
  have hι₁v : ∀ s, ((ι₁ s : matrixDerived Q) : GL (Fin d) K) = ι₀ s := fun s => rfl
  have hι₁inj : Function.Injective ι₁ := fun s t h => hinj (by rw [← hι₁v, ← hι₁v, h])
  have hι₁B : ∀ s, φ (ι₁ s) ∈ Bs := by
    intro s
    obtain ⟨Y, hY, hYs⟩ := hι₀A s
    have hYι : Y = ι₁ s := Subtype.ext hYs
    rw [← hYι]
    exact hY
  have hBι : ∀ b ∈ Bs, ∃ t, φ (ι₁ t) = b := by
    intro b hb
    obtain ⟨Y, rfl⟩ := hBφ hb
    have hYA : (Y : GL (Fin d) K) ∈ ι₀.range := by rw [hrange]; exact ⟨Y, hb, rfl⟩
    obtain ⟨t, ht⟩ := hYA
    exact ⟨t, congrArg φ (Subtype.ext ht)⟩
  have hφι : Function.Injective (φ.comp ι₁) := hφ.comp hι₁inj
  have hBeq : Bs = (φ.comp ι₁).range := by
    ext b
    constructor
    · intro hb
      obtain ⟨t, rfl⟩ := hBι b hb
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact hι₁B t
  have hcardBs : Nat.card Bs = p ^ r := by
    rw [hBeq, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφι,
      Subgroup.card_top, Nat.card_congr
        (Multiplicative.toAdd : Multiplicative (Fin r → ZMod p) ≃ (Fin r → ZMod p)),
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have : Finite Bs := Nat.finite_of_card_ne_zero (by rw [hcardBs]; exact pow_ne_zero _ hp.ne_zero)
  have hr : 4 ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).mp
    (hcardB.trans (hcardBs ▸ Subgroup.card_le_of_le hBBs))
  obtain rfl : r = 4 := eq_four hnd hr hUnd hUne horth hd
  obtain ⟨hdim, htop⟩ := four_blocks hUnd hUne horth hd id Function.injective_id
  have hiso : ∀ s v, Q (glin (ι₀ s) v) = Q v := fun s v => by
    rw [glin_apply, ← matrixLinearEquiv_apply]
    exact (mem_matrixIsometries_iff Q (ι₀ s)).mp (matrixDerived_le_isometries Q (hι₀Γ s)) v
  have hF : Frame4 Q p ι₀ U :=
    { nd := hUnd
      ne := hUne
      orth := horth
      fix := fun s v => hfix (toAdd s) v
      inv := fun s i u hu => hinv (toAdd s) i u hu
      iso := hiso
      dim := hdim
      span := exists_sum_eq htop }
  have hBBs' : B = Bs := Subgroup.eq_of_le_of_card_ge hBBs (by rw [hcardBs]; exact hcardB)
  set S : Subgroup (Multiplicative (Fin 4 → ZMod p)) := D.comap (φ.comp ι₁) with hS
  have hDB : D ≤ Bs := by
    rw [← hBBs', hDJ]
    exact inf_le_left
  have hDS : ∀ e ∈ D, ∃ s ∈ S, φ (ι₁ s) = e := fun e he => by
    obtain ⟨s, hs⟩ := hBι e (hDB he)
    refine ⟨s, ?_, hs⟩
    change φ (ι₁ s) ∈ D
    rw [hs]
    exact he
  have hDC : ∀ e ∈ D, ∀ j ∈ J, j * e = e * j := fun e he => by
    rw [hDJ] at he
    exact Subgroup.mem_centralizer_iff.mp he.2
  obtain ⟨w₁, w₂, hQw₁, hQw₂, hpw, hwi, hmat⟩ : ∃ w₁ w₂ : Fin d → K, Q w₁ = 0 ∧ Q w₂ = 0 ∧
      polar Q w₁ w₂ = 0 ∧ LinearIndependent K ![w₁, w₂] ∧ ∀ s ∈ S, ∃ α β γ δ : K,
        glin (ι₀ s) w₁ = α • w₁ + β • w₂ ∧ glin (ι₀ s) w₂ = γ • w₁ + δ • w₂ ∧
          α * δ - β * γ = 1 := by
    by_cases hpos : ∃ k l : Fin 4, k ≠ l ∧ ∀ s ∈ S, ∃ t : K,
        (∀ u ∈ U k, glin (ι₀ s) (glin (ι₀ s) u) = t • glin (ι₀ s) u + u) ∧
          ∀ v ∈ U l, glin (ι₀ s) (glin (ι₀ s) v) = t • glin (ι₀ s) v + v
    · obtain ⟨k, l, hkl, hm⟩ := hpos
      by_cases hk : ∀ s ∈ S, toAdd s k = 0
      · obtain ⟨ak, hak, bk, hbk, al, hal, bl, hbl, h1, h2, h3, h4⟩ := exists_pair_of_charSum hp
          hp2 (hF.nd k) (hF.nd l) (hF.dim k) (hF.dim l) (hF.orth k l hkl)
          (hF.charSum_modEq hp k) (hF.charSum_modEq hp l)
        refine ⟨ak + al, bk + bl, h1, h2, h3, h4, fun s hs => ⟨1, 0, 0, 1, ?_, ?_, by ring⟩⟩
        all_goals
          have hsl : toAdd s l = 0 := by
            obtain ⟨t, htk, htl⟩ := hm s hs
            obtain rfl := hF.eq_zero_of_sqRel (hk s hs) htk
            exact hF.toAdd_eq_zero_of_sq hp hp2 fun v hv => by
              rw [htl v hv, zero_smul, zero_add]
        · rw [map_add, hF.apply_eq_self (hk s hs) hak, hF.apply_eq_self hsl hal]
          simp
        · rw [map_add, hF.apply_eq_self (hk s hs) hbk, hF.apply_eq_self hsl hbl]
          simp
      · push Not at hk
        obtain ⟨s₀, hs₀, hs₀k⟩ := hk
        exact hF.exists_pair_of_matched hp hp2 hkl hm hs₀ hs₀k
    · exfalso
      have hJ₀ : ⁅J.comap φ, J.comap φ⁆ = J.comap φ := by
        apply Subgroup.map_injective hφ
        rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hJφ, hJ]
      set H : Subgroup (GL (Fin d) K) := (J.comap φ).map (matrixDerived Q).subtype with hH
      have hHH : ⁅H, H⁆ = H := by rw [hH, ← Subgroup.map_commutator, hJ₀]
      have hHS : ∀ h ∈ H, ∀ s ∈ S, h * ι₀ s = ι₀ s * h := by
        rintro _ ⟨j₀, hj₀, rfl⟩ s hs
        have h1 := hDC _ hs (φ j₀) hj₀
        have h2 : j₀ * ι₁ s = ι₁ s * j₀ := hφ (by rw [map_mul, map_mul]; exact h1)
        exact congrArg Subtype.val h2
      obtain ⟨k₀, hk₀⟩ := hF.exists_commute_of_not_matched
        (fun k l hkl hP => hpos ⟨k, l, hkl, hP⟩) hHH hHS
      set ev : Multiplicative (Fin 4 → ZMod p) →* Multiplicative (ZMod p) :=
        AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => ZMod p) k₀) with hev
      have hev_apply : ∀ s, toAdd (ev s) = toAdd s k₀ := fun s => rfl
      have hsurj : Function.Surjective ev := fun y => ⟨ofAdd (Pi.single k₀ (toAdd y)), by
        apply toAdd.injective
        rw [hev_apply, toAdd_ofAdd, Pi.single_eq_same]⟩
      have hcard_ker : Nat.card ev.ker = p ^ 3 := by
        have h1 := Subgroup.card_mul_index ev.ker
        rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
          Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
          Nat.card_zmod, Nat.card_congr
            (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod p) ≃ (Fin 4 → ZMod p)),
          Nat.card_fun, Nat.card_zmod, Nat.card_fin, show p ^ 4 = p ^ 3 * p by ring] at h1
        exact Nat.eq_of_mul_eq_mul_right hp.pos h1
      have hle : ev.ker.map (φ.comp ι₁) ≤ D := by
        rintro _ ⟨s, hs, rfl⟩
        have hs0 : toAdd s k₀ = 0 := by rw [← hev_apply, MonoidHom.mem_ker.mp hs, toAdd_one]
        rw [hDJ]
        refine ⟨by rw [hBBs']; exact hι₁B s, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
        obtain ⟨j₀, rfl⟩ := hJφ hj
        have h1 := hk₀ _ ⟨j₀, hj, rfl⟩ s hs0
        have h2 : j₀ * ι₁ s = ι₁ s * j₀ := Subtype.ext h1
        change φ j₀ * φ (ι₁ s) = φ (ι₁ s) * φ j₀
        rw [← map_mul, ← map_mul, h2]
      have : Finite D :=
        Nat.finite_of_card_ne_zero (by rw [hDcard]; exact pow_ne_zero 2 hp.ne_zero)
      have h3 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_map_of_injective hφι, hcard_ker, hDcard] at h3
      exact absurd ((Nat.pow_le_pow_iff_right hp.one_lt).mp h3) (by norm_num)
  obtain ⟨g, hg₁, hg₂⟩ := exists_conj_pair hnd hT (matAct Q) matAct_range ha₀ ha₁ ha hai hQw₁
    hQw₂ hpw hwi hw hw₀ hw₁
  refine ⟨g, fun e he X ⟨c, hX⟩ => ?_⟩
  obtain ⟨s, hs, rfl⟩ := hDS e he
  have ha₁₀ : polar Q a₁ (c • a₀) = 0 := by
    rw [polar_smul_right, QuadraticMap.polar_comm Q a₁ a₀, ha, smul_zero]
  have hXe : matAct Q X = eichler Q a₁ (c • a₀) := by
    refine LinearEquiv.ext fun y => ?_
    rw [matAct_apply, hX y, eichler_apply ha₁ ha₁₀ y, QuadraticMap.map_smul, ha₀, smul_zero,
      zero_mul, add_zero, polar_smul_right, smul_eq_mul, smul_smul, mul_comm (polar Q y a₁) c]
  have hconj : matAct Q (g * X * g⁻¹) = eichler Q w₂ (c • w₁) := by
    rw [map_mul, map_mul, map_inv, hXe, eichler_conj (matAct_mem_orth g), map_smul, hg₁, hg₂]
  obtain ⟨α, β, γ, δ, h₁, h₂, hdet⟩ := hmat s hs
  have hcomm := commute_eichler (matAct_mem_orth (ι₁ s)) hQw₁ hQw₂ hpw
    (by rw [matAct_apply, hι₁v]; exact h₁) (by rw [matAct_apply, hι₁v]; exact h₂) hdet c
  have h1 : ι₁ s * (g * X * g⁻¹) = (g * X * g⁻¹) * ι₁ s :=
    matAct_injective (by
      rw [map_mul (matAct Q) (ι₁ s) (g * X * g⁻¹), map_mul (matAct Q) (g * X * g⁻¹) (ι₁ s),
        hconj]
      exact hcomm)
  rw [← map_mul, ← map_mul, h1]

end Core

section Spin

open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {d : ℕ}

theorem exists_rootPlane_spin_d4 (e : ι ≃ Fin d) {Q₀ : QuadraticForm K (ι → K)}
    (hR : (spinMatrix Q₀).range = CFSG.Assembly.LowTwoRank.StatedOmega ⇑Q₀)
    (hπ : Function.Bijective (AutOm.spinModel e Q₀ hR))
    (hnd : (reindexQuadraticForm e Q₀).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧
      ∀ x ∈ T, reindexQuadraticForm e Q₀ x = 0)
    (hd : d ≤ 8) {N : ℕ} (F : HypFrame Q₀ N) {i j : Fin N} (hij : i ≠ j) (s t : Bool)
    {G : Type} [Group G] {ψ : spinGroup Q₀ →* G} (hψ : Function.Injective ψ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B Bs D J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBBs : B ≤ Bs) (hcardB : p ^ 4 ≤ Nat.card B) (hDcard : Nat.card D = p ^ 2)
    (hDJ : D = B ⊓ Subgroup.centralizer (J : Set G)) (hJ : ⁅J, J⁆ = J)
    (hBψ : Bs ≤ ψ.range) (hJψ : J ≤ ψ.range) :
    ∃ u : spinGroup Q₀, D ≤ Subgroup.centralizer ((((F.longRoot hij s t).range.map
        (MulAut.conj u).toMonoidHom).map ψ : Subgroup G) : Set G) ∧
      orderOf (ψ (u * F.longRoot hij s t (.ofAdd 1) * u⁻¹)) = 2 := by
  set π := AutOm.spinModel e Q₀ hR with hπdef
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : matrixDerived (reindexQuadraticForm e Q₀) →* G := ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφπ : ∀ x, φ (π x) = ψ x := fun x => by
    simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact congrArg ψ (πe.symm_apply_apply x)
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨π x, hφπ x⟩
  set R := reindexVectorEquiv (K := K) e with hRdef
  obtain ⟨a, hQa, haux⟩ := F.exists_aux i j
  have hai : LinearIndependent K ![R (F.vec i s), R (F.vec j t)] := by
    have h := (F.linearIndependent_vec_pair hij s t).map' R.toLinearMap R.ker
    convert h using 1
    funext k
    fin_cases k <;> rfl
  obtain ⟨g, hcent⟩ := exists_rootPlane_d4_core hnd hT hd hp hp2 hBs hSC hBBs hcardB hDcard
    hDJ hJ hφinj (hφrange ▸ hBψ) (hφrange ▸ hJψ) (a₀ := R (F.vec i s)) (a₁ := R (F.vec j t))
    (w := R a) (by rw [reindex_apply, F.map_vec]) (by rw [reindex_apply, F.map_vec])
    (by rw [polar_reindex, F.polar_vec_of_ne hij]) hai
    (by rw [reindex_apply]; exact hQa.ne_zero)
    (by rw [polar_reindex, QuadraticMap.polar_comm]; exact (haux s).1)
    (by rw [polar_reindex, QuadraticMap.polar_comm]; exact (haux t).2)
  set u := πe.symm g with hu
  have hπu : π u = g := πe.apply_symm_apply g
  have hψconj : ∀ z, ψ (u * z * u⁻¹) = φ (g * π z * g⁻¹) := fun z => by
    rw [← hφπ (u * z * u⁻¹), map_mul π, map_mul π, map_inv π, hπu]
  refine ⟨u, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩
    change ψ (u * F.longRoot hij s t c * u⁻¹) * y = y * ψ (u * F.longRoot hij s t c * u⁻¹)
    rw [hψconj]
    exact (hcent y hy (π (F.longRoot hij s t c))
      ⟨toAdd c, glin_spinModel_longRoot e hR F hij s t (toAdd c)⟩).symm
  · rw [orderOf_injective ψ hψ, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ ?_
    · rw [_root_.sq, ← map_mul, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
    · intro h1
      have h2 := congrArg (fun z => spinAction Q₀ z (F.vec j (!t))) h1
      simp only [map_one, LinearEquiv.coe_one, id_eq] at h2
      rw [F.spinAction_longRoot, F.polar_not_vec, F.polar_vec_of_ne hij.symm, mul_zero,
        zero_smul, sub_zero, one_mul, one_smul, add_eq_left] at h2
      have h3 := F.polar_vec_not i s
      rw [h2, QuadraticMap.polar_zero_left] at h3
      exact zero_ne_one h3

end Spin

end RootPlaneD4

end CFSG.StandardType
