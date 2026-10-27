module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Crd
public import CFSG.Quasithin.Vol2.Ch4Sec3C136One

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_centerOf {X : Subgroup G} {g c : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hc : c ∈ centerOf X) : g * c * g⁻¹ ∈ centerOf X := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg c).mp hc.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro y hy
  have hy' : g⁻¹ * y * g ∈ X := by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (X : Set G)).inv_mem hg) y).mp hy
    simpa using h1
  have h2 := Subgroup.mem_centralizer_iff.mp hc.2 _ hy'
  calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h2]
    _ = g * c * g⁻¹ * y := by group

theorem le_normalizer_centerOf {X H : Subgroup G} (h : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer (centerOf X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact fun hc => conj_mem_centerOf (h hg) hc
  · intro hc
    have h1 := conj_mem_centerOf (Subgroup.normalizer (X : Set G) |>.inv_mem (h hg)) hc
    simpa [mul_assoc] using h1

variable {G₀ L : Subgroup G} {F : Type} [Field F] {α : ↥L →* ↥(StatedSL 3 F)}

@[expose] def cnj {U : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (u : ↥U) :
    ↥U :=
  ⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg u).mp u.2⟩

theorem coe_cnj {U : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (u : ↥U) :
    ((cnj hg u : ↥U) : G) = g * u * g⁻¹ := rfl

theorem cnj_mul_left {U : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hh : h ∈ Subgroup.normalizer (U : Set G)) (u : ↥U) :
    cnj (Subgroup.mul_mem _ hg hh) u = cnj hg (cnj hh u) :=
  Subtype.ext (by simp only [coe_cnj]; group)

theorem cnj_mul {U : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) (u v : ↥U) :
    cnj hg (u * v) = cnj hg u * cnj hg v :=
  Subtype.ext (by simp only [coe_cnj, Subgroup.coe_mul]; group)

theorem cnj_one {U : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    cnj hg (1 : ↥U) = 1 :=
  Subtype.ext (by simp [coe_cnj])

theorem commute_of_mem_pCoreOf [Finite G] [CharP F 2] (hα : IsModO2Surj L α) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G))
    (hU : IsSumOfNaturalModulesVia L (centerOf (c134Q G₀ L)) ⊥ α false 1) {t u : G}
    (ht : t ∈ pCoreOf 2 G₀) (hu : u ∈ centerOf (c134Q G₀ L)) : t * u = u * t := by
  classical
  set Q := c134Q G₀ L with hQ
  set U := centerOf Q with hUdef
  have hGU : G₀ ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_centerOf (le_normalizer_c134Q hGL)
  have htN : t ∈ Subgroup.normalizer (U : Set G) := hGU (pCoreOf_le 2 G₀ ht)
  let eq : ↥U ≃ (Fin 1 → Fin 3 → F) := Equiv.ofBijective (crd hU) ⟨crd_injective hU,
    crd_surjective hU⟩
  have heq : ∀ v, eq v = crd hU v := fun v => rfl
  have hcrd1 : ∀ v : ↥U, crd hU v = fun _ => crd hU v 0 := fun v => by
    funext i
    rw [Subsingleton.elim i 0]
  let elt : (Fin 3 → F) → ↥U := fun x => eq.symm (fun _ => x)
  have hcrd_elt : ∀ x, crd hU (elt x) 0 = x := fun x => by
    rw [← heq, Equiv.apply_symm_apply]
  have helt_crd : ∀ v : ↥U, elt (crd hU v 0) = v := fun v => by
    apply eq.injective
    rw [Equiv.apply_symm_apply, heq, ← hcrd1]
  have helt_add : ∀ x y, elt (x + y) = elt x * elt y := fun x y => by
    apply eq.injective
    rw [Equiv.apply_symm_apply, heq, crd_mul, ← heq, ← heq, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    rfl
  have hconjL : ∀ (g : ↥L) (v : ↥U), crd hU (cnj (hGU (hLG g.2)) v) 0 =
      ((slNat α g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ crd hU v 0 := by
    intro g v
    rw [crd_conj_false hU g v _ rfl]
    rfl
  have hcomm : ∀ (g : ↥L) (v : ↥U), cnj htN (cnj (hGU (hLG g.2)) v) =
      cnj (hGU (hLG g.2)) (cnj htN v) := by
    intro g v
    apply Subtype.ext
    simp only [coe_cnj]
    have hc : ⁅t, (g : G)⁆ ∈ Q := Subgroup.commutator_mem_commutator ht g.2
    have hw : (g : G) * (t * v * t⁻¹) * (g : G)⁻¹ ∈ U :=
      (cnj (hGU (hLG g.2)) (cnj htN v)).2
    have h1 := Subgroup.mem_centralizer_iff.mp hw.2 _ hc
    rw [commutatorElement_def] at h1
    calc t * (↑g * ↑v * (↑g)⁻¹) * t⁻¹ =
          (t * ↑g * t⁻¹ * (↑g)⁻¹) * (↑g * (t * ↑v * t⁻¹) * (↑g)⁻¹) *
            (t * ↑g * t⁻¹ * (↑g)⁻¹)⁻¹ := by group
      _ = ↑g * (t * ↑v * t⁻¹) * (↑g)⁻¹ := by rw [h1]; group
  let φ : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun x => crd hU (cnj htN (elt x)) 0
      map_zero' := by
        have h0 : elt 0 = 1 := by
          rw [← helt_crd 1, crd_one]
          rfl
        rw [h0, cnj_one, crd_one]
        rfl
      map_add' := fun x y => by
        rw [helt_add, cnj_mul, crd_mul]
        rfl }
  have hφ : ∀ x, φ x = crd hU (cnj htN (elt x)) 0 := fun x => rfl
  obtain ⟨c, hc⟩ := exists_smul_of_commute φ (by
    intro i j hij b x
    obtain ⟨g, hg⟩ := slNat_surjective hα.1 (Matrix.SpecialLinearGroup.transvection hij b)
    have he : elt ((Matrix.SpecialLinearGroup.transvection hij b :
        Matrix (Fin 3) (Fin 3) F) *ᵥ x) = cnj (hGU (hLG g.2)) (elt x) := by
      rw [← helt_crd (cnj _ (elt x)), hconjL, hcrd_elt, hg]
    rw [hφ, hφ, he, hcomm, hconjL, hg])
  have hsc : ∀ v : ↥U, crd hU (cnj htN v) 0 = c • crd hU v 0 := fun v => by
    have := hc (crd hU v 0)
    rw [hφ, helt_crd] at this
    exact this
  have hpow : ∀ (m : ℕ) (v : ↥U),
      crd hU (cnj (Subgroup.pow_mem _ htN m) v) 0 = c ^ m • crd hU v 0 := by
    intro m
    induction m with
    | zero =>
      intro v
      have h1 : cnj (Subgroup.pow_mem _ htN 0) v = v := Subtype.ext (by simp [coe_cnj])
      rw [h1, pow_zero, one_smul]
    | succ m ih =>
      intro v
      have h1 : cnj (Subgroup.pow_mem _ htN (m + 1)) v =
          cnj htN (cnj (Subgroup.pow_mem _ htN m) v) :=
        Subtype.ext (by simp only [coe_cnj]; rw [pow_succ']; group)
      rw [h1, hsc, ih, smul_smul, pow_succ']
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 G₀) ⟨t, ht⟩
  have htm : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hcm : c ^ 2 ^ m = 1 := by
    have h1 := hpow (2 ^ m) (elt (Pi.single 0 1))
    have h2 : cnj (Subgroup.pow_mem _ htN (2 ^ m)) (elt (Pi.single 0 1)) = elt (Pi.single 0 1) :=
      Subtype.ext (by simp [coe_cnj, htm])
    rw [h2, hcrd_elt] at h1
    have h3 := congrFun h1 0
    simp at h3
    exact h3.symm
  have hc1 : c = 1 := by
    have h1 : (c - 1) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, hcm, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)
  have h1 : cnj htN ⟨u, hu⟩ = ⟨u, hu⟩ := by
    apply crd_injective hU
    rw [hcrd1 (cnj htN _), hcrd1 ⟨u, hu⟩, hsc, hc1, one_smul]
  have h2 : t * u * t⁻¹ = u := congrArg Subtype.val h1
  calc t * u = t * u * t⁻¹ * t := by group
    _ = u * t := by rw [h2]

theorem centralizer_c134Q_eq_centerOf [Finite G] {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hcc : c * c ≠ 1) (hα : IsModO2Surj L α) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅L, L⁆ = L)
    (hU : IsSumOfNaturalModulesVia L (centerOf (c134Q G₀ L)) ⊥ α false 1)
    (hCL : G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    G₀ ⊓ Subgroup.centralizer (c134Q G₀ L : Set G) = centerOf (c134Q G₀ L) := by
  set Q := c134Q G₀ L with hQ
  set U := centerOf Q with hUdef
  set V := G₀ ⊓ Subgroup.centralizer (Q : Set G) with hV
  have hOO : pCoreOf 2 L ≤ pCoreOf 2 G₀ :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLG)
      (hGL.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hOLQ : ⁅pCoreOf 2 L, L⁆ ≤ Q := Subgroup.commutator_mono hOO le_rfl
  have hGQ : G₀ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_c134Q hGL
  have hGV : G₀ ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (mem_normalizer_centralizer_of_mem (hGQ hg))
  have hQG : Q ≤ G₀ := (c134Q_le hGL).trans hLG
  have hUQ : U ≤ Q := inf_le_left
  have hVG : V ≤ G₀ := inf_le_left
  have hVL : V ⊓ L ≤ pCoreOf 2 L := by
    rintro x ⟨hxV, hxL⟩
    have hxU : x ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.centralizer_le (fun y hy => hUQ hy) hxV.2
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ α.ker := map_eq_one_of_mem_centralizer hU one_ne_zero hxU
    rw [hα.2] at h1
    exact (mem_pCoreOf_iff' ⟨x, hxL⟩).mpr h1
  have hVLQ : ⁅V, L⁆ ≤ Q := by
    have h1 : ⁅V, L⁆ ≤ pCoreOf 2 L :=
      (le_inf (commutator_le_left_of_le_normalizer (hLG.trans hGV))
        (commutator_le_right_of_le_normalizer (hVG.trans hGL))).trans hVL
    rw [commutator_eq_commutator_commutator_of_perfect' hperf (hVG.trans hGL)]
    exact (Subgroup.commutator_mono h1 le_rfl).trans hOLQ
  have hVLU : ⁅V, L⁆ ≤ U := fun x hx =>
    ⟨hVLQ hx, (commutator_le_left_of_le_normalizer (hLG.trans hGV) hx).2⟩
  have hvK : ∀ v ∈ V, ∀ g ∈ L, v⁻¹ * (g * v * g⁻¹) ∈ U := by
    intro v hv g hg
    have h1 : ⁅v⁻¹, g⁆ ∈ ⁅V, L⁆ := Subgroup.commutator_mem_commutator (V.inv_mem hv) hg
    have e : ⁅v⁻¹, g⁆ = v⁻¹ * (g * v * g⁻¹) := by
      simp only [commutatorElement_def, inv_inv]; group
    rw [e] at h1
    exact hVLU h1
  have hvker : ∀ v ∈ V, ∀ a : ↥L, α a = 1 → (a : G) * v = v * a := by
    intro v hv a ha
    have haO : (a : G) ∈ pCoreOf 2 L := by
      have h2 : a ∈ α.ker := ha
      rw [hα.2] at h2
      exact (mem_pCoreOf_iff' a).mpr h2
    have haU : ∀ q ∈ U, q * (a : G) = a * q := fun q hq => by
      have h := conj_eq_of_isSumOfNaturalModulesVia hU ha hq
      calc q * (a : G) = (a : G) * q * (a : G)⁻¹ * a := by rw [h]
        _ = a * q := by group
    have hvQ : ∀ q ∈ Q, q * v = v * q := fun q hq => Subgroup.mem_centralizer_iff.mp hv.2 q hq
    obtain ⟨w, hw⟩ : ∃ w, w = v * a * v⁻¹ * (a : G)⁻¹ := ⟨_, rfl⟩
    have hwC : w ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
      obtain ⟨q₁, hq₁U, hgv⟩ : ∃ q₁ ∈ U, g * v * g⁻¹ = v * q₁ :=
        ⟨v⁻¹ * (g * v * g⁻¹), hvK v hv g hg, by group⟩
      obtain ⟨q₂, hq₂Q, hga⟩ : ∃ q₂ ∈ Q, g * (a : G) * g⁻¹ = a * q₂ := by
        refine ⟨(a : G)⁻¹ * (g * a * g⁻¹), ?_, by group⟩
        have h1 : ⁅(a : G)⁻¹, g⁆ ∈ ⁅pCoreOf 2 L, L⁆ :=
          Subgroup.commutator_mem_commutator ((pCoreOf 2 L).inv_mem haO) hg
        have e : ⁅(a : G)⁻¹, g⁆ = (a : G)⁻¹ * (g * a * g⁻¹) := by
          simp only [commutatorElement_def, inv_inv]; group
        rw [e] at h1
        exact hOLQ h1
      have h12 : q₁ * q₂ = q₂ * q₁ := (Subgroup.mem_centralizer_iff.mp hq₁U.2 q₂ hq₂Q).symm
      have h1a : q₁ * (a : G) = a * q₁ := haU q₁ hq₁U
      have h2v : q₂ * v⁻¹ = v⁻¹ * q₂ := by
        calc q₂ * v⁻¹ = v⁻¹ * (v * q₂) * v⁻¹ := by group
          _ = v⁻¹ * (q₂ * v) * v⁻¹ := by rw [hvQ q₂ hq₂Q]
          _ = v⁻¹ * q₂ := by group
      have key : g * w * g⁻¹ = w := by
        calc g * w * g⁻¹ =
              (g * v * g⁻¹) * (g * a * g⁻¹) * (g * v * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ := by
              rw [hw]; group
          _ = (v * q₁) * (a * q₂) * (v * q₁)⁻¹ * (a * q₂)⁻¹ := by rw [hgv, hga]
          _ = v * (q₁ * a) * q₂ * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by group
          _ = v * (a * q₁) * q₂ * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by rw [h1a]
          _ = v * a * (q₁ * q₂) * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by group
          _ = v * a * (q₂ * q₁) * q₁⁻¹ * v⁻¹ * q₂⁻¹ * (a : G)⁻¹ := by rw [h12]
          _ = v * a * (q₂ * v⁻¹) * q₂⁻¹ * (a : G)⁻¹ := by group
          _ = v * a * (v⁻¹ * q₂) * q₂⁻¹ * (a : G)⁻¹ := by rw [h2v]
          _ = w := by rw [hw]; group
      calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [key]
    have hw1 : w = 1 := by
      have h : w ∈ G₀ ⊓ Subgroup.centralizer (L : Set G) := by
        refine ⟨?_, hwC⟩
        rw [hw]
        exact G₀.mul_mem (G₀.mul_mem (G₀.mul_mem hv.1 (hLG a.2)) (G₀.inv_mem hv.1))
          (G₀.inv_mem (hLG a.2))
      rw [hCL] at h
      exact Subgroup.mem_bot.mp h
    calc (a : G) * v = (v * a * v⁻¹ * (a : G)⁻¹)⁻¹ * (v * a) := by group
      _ = v * a := by rw [← hw, hw1, inv_one, one_mul]
  refine le_antisymm (fun v hv => ?_) (fun x hx => ⟨hQG hx.1, hx.2⟩)
  obtain ⟨n₁, hn₁U, hvn⟩ :=
    exists_mul_mem_centralizer_of_natural hc0 hc1 hcc hα.1 hU (hvker v hv) (hvK v hv)
  have h1 : v * n₁ ∈ G₀ ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨G₀.mul_mem hv.1 (hQG (hUQ hn₁U)), hvn⟩
  rw [hCL] at h1
  have h3 : v = n₁⁻¹ := eq_inv_of_mul_eq_one_left (Subgroup.mem_bot.mp h1)
  rw [h3]
  exact U.inv_mem hn₁U

end CFSG.Quasithin.H13.Ch4.C135

end
