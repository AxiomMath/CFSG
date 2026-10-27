module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.K133.Count
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneLines
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix CFSG CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.K133

section LemmaA

variable {K : Type} [Field K]

theorem exists_fixed_in_of_plane {V : Type*} [AddCommGroup V] [Module K V]
    {P : Type*} [Group P] [Fintype P] {p : ℕ} (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (ρ : P →* LinearMap.GeneralLinearGroup K V) (U : Submodule K V) (hU : U ≠ ⊥)
    (hstab : ∀ x : P, ∀ u ∈ U, act ρ x u ∈ U) :
    ∃ x : P, x ≠ 1 ∧ ∃ v ∈ U, v ≠ 0 ∧ act ρ x v = v := by
  classical
  by_contra hcon
  push Not at hcon
  have hfix : ∀ (L : Subgroup P), L ≠ ⊥ → ∀ v ∈ U, sumOp ρ L v = 0 := by
    intro L hL v hv
    obtain ⟨⟨y, hyL⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hL
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hmem : sumOp ρ L v ∈ U := by
      unfold sumOp
      rw [LinearMap.sum_apply]
      exact U.sum_mem fun x _ => hstab x v hv
    have h1 : act ρ y (sumOp ρ L v) = sumOp ρ L v := by
      have := congrArg (fun f : Module.End K V => f v) (mul_sumOp ρ hyL)
      simpa using this
    by_contra h0
    exact hcon y hy1' _ hmem h0 h1
  have hp1 : p ≠ 1 := hP.prime.one_lt.ne'
  have hsum : ∀ v ∈ U, (∑ L ∈ lines p P, sumOp ρ L) v = 0 := by
    intro v hv
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun L hL => ?_
    have hLc : Nat.card L = p := mem_lines.1 hL
    have hLb : L ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hLc
      exact hp1 hLc.symm
    exact hfix L hLb v hv
  have htop : ∀ v ∈ U, sumOp ρ ⊤ v = 0 := by
    have hTb : (⊤ : Subgroup P) ≠ ⊥ := by
      intro h
      have h1 : Nat.card (⊤ : Subgroup P) = 1 := by rw [h, Subgroup.card_bot]
      rw [Subgroup.card_top, hP.card] at h1
      have : p ^ 2 ≠ 1 := by
        have := hP.prime.one_lt
        exact (Nat.one_lt_pow (by norm_num) this).ne'
      exact this h1
    exact fun v hv => hfix ⊤ hTb v hv
  have key := hP.sum_lines_sumOp ρ
  obtain ⟨v, hvU, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have h1 := congrArg (fun f : Module.End K V => f v) key
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
  rw [hsum v hvU, htop v hvU, add_zero] at h1
  exact hv ((smul_eq_zero.1 h1.symm).resolve_left hpK)

end LemmaA

section Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_fixed_in_of_plane_matrix {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (P : Subgroup (GL ι K)) [Finite P] (hPe : IsElementaryAbelian p P) (hc : Nat.card P = p ^ 2)
    (U : Submodule K (ι → K)) (hU : U ≠ ⊥)
    (hstab : ∀ h ∈ P, ∀ u ∈ U, (h : Matrix ι ι K) *ᵥ u ∈ U) :
    ∃ x ∈ P, x ≠ 1 ∧ ∃ v ∈ U, v ≠ 0 ∧ (x : Matrix ι ι K) *ᵥ v = v := by
  classical
  have : Fintype P := Fintype.ofFinite P
  let ρ : ↥P →* LinearMap.GeneralLinearGroup K (ι → K) :=
    (Matrix.GeneralLinearGroup.toLin :
      GL ι K ≃* LinearMap.GeneralLinearGroup K (ι → K)).toMonoidHom.comp P.subtype
  have hρ : ∀ (x : ↥P) (v : ι → K), act ρ x v = ((x : GL ι K) : Matrix ι ι K) *ᵥ v :=
    fun x v => rfl
  have hpow : ∀ x : ↥P, x ^ p = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x
  have hplane : IsPlane p ↥P := ⟨hp, hc, hpow⟩
  obtain ⟨x, hx1, v, hvU, hv0, hxv⟩ := exists_fixed_in_of_plane hplane hpK ρ U hU
    (fun x u hu => by rw [hρ]; exact hstab x x.2 u hu)
  refine ⟨x, x.2, fun h => hx1 (Subtype.ext h), v, hvU, hv0, ?_⟩
  rw [hρ] at hxv
  exact hxv

theorem exists_plane_avoiding {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (E : Subgroup G) [Finite E]
    (hE : IsElementaryAbelian p E) (hc : Nat.card E = p ^ 3) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1) :
    ∃ F : Subgroup G, F ≤ E ∧ Nat.card F = p ^ 2 ∧ x ∉ F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl p ↥E (Subgroup.zpowers (⟨x, hxE⟩ : ↥E))
  have hpow : ∀ y : ↥E, y ^ p = 1 := fun y =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) y
  have hord : orderOf (⟨x, hxE⟩ : ↥E) = p :=
    orderOf_eq_prime (hpow _) (fun h => hx1 (congrArg Subtype.val h))
  have hxC : (⟨x, hxE⟩ : ↥E) ∉ C := by
    intro h
    have h1 : (⟨x, hxE⟩ : ↥E) ∈ Subgroup.zpowers (⟨x, hxE⟩ : ↥E) ⊓ C := ⟨Subgroup.mem_zpowers _, h⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at h1
    exact hx1 (congrArg Subtype.val h1)
  have hcomm : ∀ y ∈ C, y * (⟨x, hxE⟩ : ↥E) = (⟨x, hxE⟩ : ↥E) * y := fun y _ =>
    hE.is_comm.comm y _
  have hcard := card_sup_zpowers (Y := C) hp hord hcomm hxC
  have hsup : C ⊔ Subgroup.zpowers (⟨x, hxE⟩ : ↥E) = ⊤ := by
    rw [sup_comm]; exact hC.sup_eq_top
  rw [hsup, Subgroup.card_top, hc] at hcard
  have hCc : Nat.card C = p ^ 2 := by
    have h2 : p ^ 3 = p ^ 2 * p := by ring
    rw [h2] at hcard
    exact (Nat.eq_of_mul_eq_mul_right hp.pos hcard).symm
  refine ⟨C.map E.subtype, Subgroup.map_subtype_le C, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hCc]
  · rintro ⟨y, hy, hyx⟩
    exact hxC (by
      have : y = ⟨x, hxE⟩ := Subtype.ext hyx
      rw [← this]; exact hy)

@[expose] def fixSubG (x : GL ι K) : Submodule K (ι → K) where
  carrier := {v | (x : Matrix ι ι K) *ᵥ v = v}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change _ *ᵥ a = a at ha
    change _ *ᵥ b = b at hb
    change _ *ᵥ (a + b) = a + b
    rw [mulVec_add, ha, hb]
  smul_mem' := fun c a ha => by
    change _ *ᵥ a = a at ha
    change _ *ᵥ (c • a) = c • a
    rw [mulVec_smul, ha]

@[expose] def vecStab (v : ι → K) : Subgroup (GL ι K) where
  carrier := {h | (h : Matrix ι ι K) *ᵥ v = v}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change (a : Matrix ι ι K) *ᵥ v = v at ha
    change (b : Matrix ι ι K) *ᵥ v = v at hb
    change ((a * b : GL ι K) : Matrix ι ι K) *ᵥ v = v
    rw [Units.val_mul, ← mulVec_mulVec, hb, ha]
  inv_mem' := fun {a} ha => by
    change (a : Matrix ι ι K) *ᵥ v = v at ha
    change ((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v = v
    have h1 : ((a⁻¹ : GL ι K) : Matrix ι ι K) * (a : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
        = ((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((a : Matrix ι ι K) *ᵥ v) := by rw [ha]
      _ = v := by rw [mulVec_mulVec, h1, one_mulVec]

theorem exists_plane_fixed [Nonempty ι] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (E : Subgroup (GL ι K)) [Finite E] (hE : IsElementaryAbelian p E) (hc : Nat.card E = p ^ 3) :
    ∃ P : Subgroup (GL ι K), P ≤ E ∧ Nat.card P = p ^ 2 ∧ ∃ v : ι → K, v ≠ 0 ∧
      ∀ h ∈ P, (h : Matrix ι ι K) *ᵥ v = v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ y : ↥E, y ^ p = 1 := fun y =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) y
  have hdvd : p ^ 2 ∣ Nat.card E := by rw [hc]; exact pow_dvd_pow p (by norm_num)
  obtain ⟨Q₁, hQ₁⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) p hdvd
  set P₁ : Subgroup (GL ι K) := Q₁.map E.subtype with hP₁def
  have hP₁le : P₁ ≤ E := Subgroup.map_subtype_le Q₁
  have hP₁c : Nat.card P₁ = p ^ 2 := by
    rw [hP₁def, Subgroup.card_map_of_injective E.subtype_injective, hQ₁]
  have hP₁fin : Finite P₁ := Nat.finite_of_card_ne_zero (by rw [hP₁c]; exact pow_ne_zero 2 hp.ne_zero)
  have hP₁e : IsElementaryAbelian p P₁ := CFSG.IsElementaryAbelian.of_le hE hP₁le
  have htop : (⊤ : Submodule K (ι → K)) ≠ ⊥ := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (Submodule.ne_bot_iff _).2 ⟨fun _ => 1, trivial, fun h => one_ne_zero (congrFun h i)⟩
  obtain ⟨x₁, hx₁P, hx₁1, v₁, -, hv₁0, hxv₁⟩ := exists_fixed_in_of_plane_matrix hp hpK P₁ hP₁e hP₁c
    ⊤ htop (fun _ _ _ _ => trivial)
  have hx₁E : x₁ ∈ E := hP₁le hx₁P
  have hx₁pow : x₁ ^ p = 1 := by
    have := congrArg Subtype.val (hpow ⟨x₁, hx₁E⟩)
    simpa using this
  have hord₁ : orderOf x₁ = p := orderOf_eq_prime hx₁pow hx₁1
  obtain ⟨F, hFE, hFc, hx₁F⟩ := exists_plane_avoiding hp E hE hc hx₁E hx₁1
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hFc]; exact pow_ne_zero 2 hp.ne_zero)
  have hFe : IsElementaryAbelian p F := CFSG.IsElementaryAbelian.of_le hE hFE
  have hU₁ : fixSubG x₁ ≠ ⊥ := fun h => hv₁0 (by
    have : v₁ ∈ fixSubG x₁ := hxv₁
    rw [h] at this
    exact (Submodule.mem_bot K).1 this)
  have hstab : ∀ h ∈ F, ∀ u ∈ fixSubG x₁, (h : Matrix ι ι K) *ᵥ u ∈ fixSubG x₁ := by
    intro h hh u hu
    have hcomm : x₁ * h = h * x₁ :=
      congrArg Subtype.val (hE.is_comm.comm ⟨x₁, hx₁E⟩ ⟨h, hFE hh⟩)
    have hu' : (x₁ : Matrix ι ι K) *ᵥ u = u := hu
    show (x₁ : Matrix ι ι K) *ᵥ ((h : Matrix ι ι K) *ᵥ u) = (h : Matrix ι ι K) *ᵥ u
    rw [mulVec_mulVec, ← Units.val_mul, hcomm, Units.val_mul, ← mulVec_mulVec, hu']
  obtain ⟨x₂, hx₂F, hx₂1, v, hvU, hv0, hx₂v⟩ :=
    exists_fixed_in_of_plane_matrix hp hpK F hFe hFc (fixSubG x₁) hU₁ hstab
  have hx₂E : x₂ ∈ E := hFE hx₂F
  have hx₂pow : x₂ ^ p = 1 := by
    have := congrArg Subtype.val (hpow ⟨x₂, hx₂E⟩)
    simpa using this
  have hord₂ : orderOf x₂ = p := orderOf_eq_prime hx₂pow hx₂1
  have hcomm12 : ∀ y ∈ Subgroup.zpowers x₁, y * x₂ = x₂ * y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h12 : x₁ * x₂ = x₂ * x₁ :=
      congrArg Subtype.val (hE.is_comm.comm ⟨x₁, hx₁E⟩ ⟨x₂, hx₂E⟩)
    exact (Commute.zpow_left (show Commute x₁ x₂ from h12) n).eq
  have : Finite (Subgroup.zpowers x₁) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord₁]; exact hp.ne_zero)
  have hx₂notin : x₂ ∉ Subgroup.zpowers x₁ := by
    intro hmem
    have hle : Subgroup.zpowers x₂ ≤ Subgroup.zpowers x₁ := Subgroup.zpowers_le.2 hmem
    have heq : Subgroup.zpowers x₂ = Subgroup.zpowers x₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord₁, hord₂])
    apply hx₁F
    have : x₁ ∈ Subgroup.zpowers x₂ := by rw [heq]; exact Subgroup.mem_zpowers x₁
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
    rw [← hn]
    exact F.zpow_mem hx₂F n
  refine ⟨Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂,
    sup_le (Subgroup.zpowers_le.2 hx₁E) (Subgroup.zpowers_le.2 hx₂E), ?_, v, hv0, ?_⟩
  · rw [card_sup_zpowers hp hord₂ hcomm12 hx₂notin, Nat.card_zpowers, hord₁]
    ring
  · have hst : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤ vecStab v :=
      sup_le (Subgroup.zpowers_le.2 (by
          show (x₁ : Matrix ι ι K) *ᵥ v = v
          have : v ∈ fixSubG x₁ := hvU
          exact this))
        (Subgroup.zpowers_le.2 hx₂v)
    intro h hh
    exact hst hh

end Matrix

section Descent

variable {K : Type} [Field K] {ι : Type}

@[expose] def vmap (σ : K ≃+* K) (v : ι → K) : ι → K := fun i => σ (v i)

theorem vmap_add (σ : K ≃+* K) (u v : ι → K) : vmap σ (u + v) = vmap σ u + vmap σ v := by
  funext i; simp [vmap]

theorem vmap_vmap (σ τ : K ≃+* K) (v : ι → K) : vmap σ (vmap τ v) = vmap (σ * τ) v := by
  funext i; simp [vmap]

theorem vmap_one (v : ι → K) : vmap (1 : K ≃+* K) v = v := by
  funext i; simp [vmap]

theorem vmap_sum (σ : K ≃+* K) {α : Type*} (s : Finset α) (f : α → ι → K) :
    vmap σ (∑ a ∈ s, f a) = ∑ a ∈ s, vmap σ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext i; simp [vmap]
  | insert a s has ih => rw [Finset.sum_insert has, Finset.sum_insert has, vmap_add, ih]

theorem exists_fixed_of_stable {p : ℕ} (hp : p.Prime) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (W : Submodule K (ι → K)) (hW : ∀ w ∈ W, vmap σ w ∈ W) (hne : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ vmap σ w = w := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hWi : ∀ (i : ℕ), ∀ w ∈ W, vmap (σ ^ i) w ∈ W := by
    intro i
    induction i with
    | zero => intro w hw; rw [pow_zero, vmap_one]; exact hw
    | succ i ih =>
      intro w hw
      have := hW _ (ih w hw)
      rwa [vmap_vmap, ← pow_succ'] at this
  let χ : Fin p → (K →* K) := fun i => ((σ ^ (i : ℕ) : K ≃+* K) : K →+* K).toMonoidHom
  have hχinj : Function.Injective χ := by
    intro a b hab
    have h1 : (σ ^ (a : ℕ) : K ≃+* K) = σ ^ (b : ℕ) := by
      ext x
      have := DFunLike.congr_fun hab x
      simpa [χ] using this
    have := (pow_injOn_Iio_orderOf (x := σ)) (by rw [hσ]; exact a.2) (by rw [hσ]; exact b.2) h1
    exact Fin.ext this
  have hind : LinearIndependent K (fun i : Fin p => (χ i : K → K)) :=
    (linearIndependent_monoidHom K K).comp χ hχinj
  have hex : ∃ l : K, ∑ i : Fin p, (σ ^ (i : ℕ)) (v j) * (σ ^ (i : ℕ)) l ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : ∑ i : Fin p, (σ ^ (i : ℕ)) (v j) • (χ i : K → K) = 0 := by
      funext l
      simpa [χ] using h l
    have h0 := Fintype.linearIndependent_iff.1 hind _ hsum ⟨0, hp.pos⟩
    exact hj (by simpa using h0)
  obtain ⟨l, hl⟩ := hex
  refine ⟨∑ i : Fin p, vmap (σ ^ (i : ℕ)) (l • v), ?_, ?_, ?_⟩
  · exact W.sum_mem fun i _ => hWi i _ (W.smul_mem l hvW)
  · intro h0
    apply hl
    have := congrFun h0 j
    simp only [vmap, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.zero_apply, map_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [vmap_sum]
    simp only [vmap_vmap]
    have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    set u : ι → K := l • v with hu
    have h1 : ∑ i : Fin p, vmap (σ * σ ^ (i : ℕ)) u = ∑ i : Fin p, vmap (σ ^ (i : ℕ)) u := by
      rw [Fin.sum_univ_eq_sum_range (fun i => vmap (σ * σ ^ i) u) p,
        Fin.sum_univ_eq_sum_range (fun i => vmap (σ ^ i) u) p]
      have h2 : ∀ i, σ * σ ^ i = σ ^ (i + 1) := fun i => (pow_succ' σ i).symm
      simp only [h2]
      have e1 := Finset.sum_range_succ (fun i => vmap (σ ^ i) u) p
      have e2 := Finset.sum_range_succ' (fun i => vmap (σ ^ i) u) p
      simp only [hσp, pow_zero, vmap_one] at e1 e2
      exact add_right_cancel (e2.symm.trans e1)
    exact h1

end Descent

end CFSG.RankThree.PartOne.K133C
