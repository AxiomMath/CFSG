module

public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.RankThree.PartOne.LIT.RankAbstract

public section

namespace CFSG.RankThree.PartOne.LIT

open Module

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem card_linearEquiv_eq (n : ℕ) (hn : finrank K V = n) :
    Nat.card (V ≃ₗ[K] V) = ∏ i : Fin n, (Nat.card K ^ n - Nat.card K ^ (i : ℕ)) := by
  have : Fintype K := Fintype.ofFinite K
  let b : Basis (Fin n) K V := Module.finBasisOfFinrankEq K V hn
  let e : GL (Fin n) K ≃* (V ≃ₗ[K] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field n, Nat.card_eq_fintype_card]

theorem not_dvd_natCard_of_natCast_ne_zero {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    ¬ p ∣ Nat.card K := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨c, hc, m, hcp, hcard⟩ := FiniteField.card' K
  have := hc
  rw [Nat.card_eq_fintype_card, hcard] at h
  have hpc : p = c := (Nat.prime_dvd_prime_iff_eq hp hcp).mp (hp.dvd_of_dvd_pow h)
  apply hpK
  rw [hpc]
  exact CharP.cast_eq_zero K c

theorem exists_dvd_pow_sub_one_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {g : V ≃ₗ[K] V} (hg1 : g ≠ 1) (hgp : g ^ p = 1) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ finrank K V ∧ p ∣ Nat.card K ^ i - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hdvd : p ∣ Nat.card (V ≃ₗ[K] V) := hord ▸ orderOf_dvd_natCard g
  rw [card_linearEquiv_eq (finrank K V) rfl] at hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have hin : (i : ℕ) < finrank K V := i.2
  have hsplit : Nat.card K ^ finrank K V - Nat.card K ^ (i : ℕ) =
      Nat.card K ^ (i : ℕ) * (Nat.card K ^ (finrank K V - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hin.le]
  rw [hsplit] at hi
  rcases hp.dvd_mul.mp hi with h | h
  · exact absurd (hp.dvd_of_dvd_pow h) (not_dvd_natCard_of_natCast_ne_zero hp hpK)
  · exact ⟨finrank K V - i, by omega, by omega, h⟩

omit [Finite K] in
theorem finrank_fixedSpace_pos {x : V ≃ₗ[K] V} {v : V} (hv0 : v ≠ 0) (hxv : x v = v) :
    0 < finrank K (fixedSpace x) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩

omit [Finite K] in
theorem finrank_commSpace_pos {x : V ≃ₗ[K] V} (hx1 : x ≠ 1) : 0 < finrank K (commSpace x) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  by_contra hcon
  have hcon' : ∀ w : commSpace x, w = 0 := fun w => by_contra fun hw => hcon ⟨w, hw⟩
  apply hx1
  apply LinearEquiv.ext
  intro y
  have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
  have h2 : x y - y = 0 := congrArg Subtype.val (hcon' ⟨x y - y, hy⟩)
  simpa [sub_eq_zero] using h2

theorem card_le_pow_div_aux {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1) :
    ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = n → ∀ (E : Subgroup (X ≃ₗ[K] X)),
      (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ p = 1) →
      Nat.card E ≤ p ^ (n / d) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn E hcomm hexp
  have : Finite X := Module.finite_of_finite K
  have : Finite (X ≃ₗ[K] X) :=
    Finite.of_injective (fun f : X ≃ₗ[K] X => (f : X → X)) DFunLike.coe_injective
  have : Fact p.Prime := ⟨hp⟩
  have hexpE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp a a.2)
  have hpg : IsPGroup p E := fun a => ⟨1, by rw [pow_one]; exact hexpE a⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hle : Nat.card E ≤ p := by
      rw [hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    rcases Nat.lt_or_ge (Nat.card E) 2 with h2 | h2
    · calc Nat.card E ≤ 1 := by omega
        _ ≤ p ^ (n / d) := Nat.one_le_pow _ _ hp.pos
    · have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨g, hg1⟩ := exists_ne (1 : E)
      obtain ⟨i, hi1, hin, hdvd⟩ := exists_dvd_pow_sub_one_of_pow_eq_one hp hpK
        (g := (g : X ≃ₗ[K] X)) (fun h => hg1 (Subtype.ext h)) (hexp g g.2)
      have hdi : d ≤ i := by
        by_contra h
        exact hdiv i hi1 (not_le.mp h) hdvd
      have hpos : 1 ≤ n / d := Nat.div_pos (by omega) hd
      calc Nat.card E ≤ p := hle
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (n / d) := Nat.pow_le_pow_right hp.pos hpos
  · have hbig : p ^ 2 ≤ Nat.card E := by
      rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2
    obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hp hpK E hcomm hexp hbig
    have hc := isCompl_fixedSpace_commSpace hpK (hexp x hxE)
    have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
    have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
      fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
    have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
      fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    have hUpos := finrank_fixedSpace_pos hv0 hxv
    have hWpos := finrank_commSpace_pos hx1
    let ρ : E →* (X ≃ₗ[K] X) := E.subtype
    let ρU := restrictAction ρ (fixedSpace x) hUinv
    let ρW := restrictAction ρ (commSpace x) hWinv
    let EU : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) := ρU.range
    let EW : Subgroup (commSpace x ≃ₗ[K] commSpace x) := ρW.range
    have : Finite EU := Finite.of_surjective ρU.rangeRestrict ρU.rangeRestrict_surjective
    have : Finite EW := Finite.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective
    have hcommU : ∀ g ∈ EU, ∀ h ∈ EU, g * h = h * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ρU (Subtype.ext (hcomm a a.2 b b.2))
    have hcommW : ∀ g ∈ EW, ∀ h ∈ EW, g * h = h * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ρW (Subtype.ext (hcomm a a.2 b b.2))
    have hexpU : ∀ g ∈ EU, g ^ p = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, hexpE a, map_one]
    have hexpW : ∀ g ∈ EW, g ^ p = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, hexpE a, map_one]
    have hIU := ih (finrank K (fixedSpace x)) (by omega) (fixedSpace x) rfl EU hcommU hexpU
    have hIW := ih (finrank K (commSpace x)) (by omega) (commSpace x) rfl EW hcommW hexpW
    have hinj : Function.Injective
        (fun g : E => ((⟨ρU g, g, rfl⟩ : EU), (⟨ρW g, g, rfl⟩ : EW))) := by
      intro g h hgh
      simp only [Prod.mk.injEq] at hgh
      obtain ⟨h1, h2⟩ := hgh
      have h1' : ρU g = ρU h := congrArg Subtype.val h1
      have h2' : ρW g = ρW h := congrArg Subtype.val h2
      apply Subtype.ext
      apply LinearEquiv.ext
      intro y
      have hfun : (g : X ≃ₗ[K] X).toLinearMap = (h : X ≃ₗ[K] X).toLinearMap := by
        apply ext_of_isCompl hc
        · intro u hu
          exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
            ((congrArg Subtype.val (LinearEquiv.congr_fun h1' ⟨u, hu⟩)).trans
              (restrictAction_apply ρ (fixedSpace x) hUinv h ⟨u, hu⟩))
        · intro w hw
          exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
            ((congrArg Subtype.val (LinearEquiv.congr_fun h2' ⟨w, hw⟩)).trans
              (restrictAction_apply ρ (commSpace x) hWinv h ⟨w, hw⟩))
      exact LinearMap.congr_fun hfun y
    have hle : Nat.card E ≤ Nat.card EU * Nat.card EW := by
      rw [← Nat.card_prod]
      exact Nat.card_le_card_of_injective _ hinj
    calc Nat.card E ≤ Nat.card EU * Nat.card EW := hle
      _ ≤ p ^ (finrank K (fixedSpace x) / d) * p ^ (finrank K (commSpace x) / d) :=
        Nat.mul_le_mul hIU hIW
      _ = p ^ (finrank K (fixedSpace x) / d + finrank K (commSpace x) / d) :=
        (pow_add _ _ _).symm
      _ ≤ p ^ (n / d) := by
        refine Nat.pow_le_pow_right hp.pos ?_
        have : finrank K (fixedSpace x) / d + finrank K (commSpace x) / d ≤
            (finrank K (fixedSpace x) + finrank K (commSpace x)) / d :=
          Nat.div_add_div_le_add_div
        rwa [hsum, hn] at this

theorem card_le_pow_div {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1)
    (E : Subgroup (V ≃ₗ[K] V)) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ p = 1) : Nat.card E ≤ p ^ (finrank K V / d) :=
  card_le_pow_div_aux hp hpK hd hdiv (finrank K V) V rfl E hcomm hexp

theorem card_le_of_det_eq_one_dim_two {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hV : finrank K V = 2) (E : Subgroup (V ≃ₗ[K] V))
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1)
    (hdet : ∀ g ∈ E, LinearMap.det (g : V →ₗ[K] V) = 1) : Nat.card E ≤ p := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  have : Fact p.Prime := ⟨hp⟩
  have hexpE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp a a.2)
  have hpg : IsPGroup p E := fun a => ⟨1, by rw [pow_one]; exact hexpE a⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  by_contra hlt
  rw [not_le] at hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    have h1 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at h1
    omega
  have hbig : p ^ 2 ≤ Nat.card E := by
    rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hp hpK E hcomm hexp hbig
  have hc := isCompl_fixedSpace_commSpace hpK (hexp x hxE)
  have hUinv : ∀ u ∈ fixedSpace x, (x : V →ₗ[K] V) u ∈ fixedSpace x :=
    fun u hu => map_mem_fixedSpace rfl hu
  have hWinv : ∀ w ∈ commSpace x, (x : V →ₗ[K] V) w ∈ commSpace x :=
    fun w hw => map_mem_commSpace rfl hw
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hUpos := finrank_fixedSpace_pos hv0 hxv
  have hWpos := finrank_commSpace_pos hx1
  have hW1 : finrank K (commSpace x) = 1 := by omega
  have hdetx := det_eq_mul_of_isCompl hc (x : V →ₗ[K] V) hUinv hWinv
  have hU1 : (x : V →ₗ[K] V).restrict hUinv = LinearMap.id :=
    LinearMap.ext fun u => Subtype.ext (mem_fixedSpace.mp u.2)
  rw [hU1, LinearMap.det_id, one_mul, hdet x hxE] at hdetx
  have hW : (x : V →ₗ[K] V).restrict hWinv = LinearMap.id :=
    eq_id_of_det_eq_one_of_finrank_eq_one hW1 _ hdetx.symm
  apply hx1
  apply LinearEquiv.ext
  intro y
  have hfun : (x : V →ₗ[K] V) = LinearMap.id := by
    apply ext_of_isCompl hc
    · intro u hu
      exact mem_fixedSpace.mp hu
    · intro w hw
      exact congrArg Subtype.val (LinearMap.congr_fun hW ⟨w, hw⟩)
  exact LinearMap.congr_fun hfun y

theorem card_le_pow_div_gl {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {d : ℕ} (hd : 0 < d)
    (hdiv : ∀ i : ℕ, 0 < i → i < d → ¬ p ∣ Nat.card K ^ i - 1)
    (E : Subgroup (GL ι K)) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ p = 1) : Nat.card E ≤ p ^ (Fintype.card ι / d) := by
  have h := card_le_pow_div hp hpK hd hdiv (E.map (glAut ι K)) (map_glAut_comm hcomm)
    (map_glAut_exp hexp)
  rwa [card_map_glAut, Module.finrank_fintype_fun_eq_card] at h

theorem card_le_of_det_eq_one_gl_two {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ}
    (hp : p.Prime) (hpK : (p : K) ≠ 0) (hι : Fintype.card ι = 2)
    (E : Subgroup (GL ι K)) (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ p = 1) (hdet : ∀ g ∈ E, (g : Matrix ι ι K).det = 1) :
    Nat.card E ≤ p := by
  have h := card_le_of_det_eq_one_dim_two hp hpK
    (by rw [Module.finrank_fintype_fun_eq_card, hι]) (E.map (glAut ι K)) (map_glAut_comm hcomm)
    (map_glAut_exp hexp) (by
      rintro _ ⟨a, ha, rfl⟩
      rw [det_glAut]
      exact hdet a ha)
  rwa [card_map_glAut] at h

end CFSG.RankThree.PartOne.LIT
