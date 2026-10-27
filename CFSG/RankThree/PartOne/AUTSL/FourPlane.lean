module

public import CFSG.RankThree.PartOne.AUTSL.FourTns

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.AUTSL.Four

open Matrix Equiv CFSG.RankThree.PartOne.KF1514B
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

abbrev PV (K : Type) [Field K] : Type := (Fin 3 → (Fin 2 → K)) × (Fin 2 → K)

@[expose] def Qp (b c : K) (v : PV K) : K :=
  (∑ x, minusTailForm K b c (v.1 x)) + v.2 0 * v.2 1

@[expose] noncomputable def mvEquiv (g : GL (Fin 2) K) : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K))
    (Matrix.toLin' ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, LinearMap.id_apply])
    (LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, LinearMap.id_apply])

@[expose] noncomputable def diagEquiv (t : Fin 3 → GL (Fin 2) K) : PV K ≃ₗ[K] PV K :=
  (LinearEquiv.piCongrRight fun x => mvEquiv (t x)).prodCongr (LinearEquiv.refl K (Fin 2 → K))

theorem diagEquiv_apply (t : Fin 3 → GL (Fin 2) K) (v : PV K) :
    diagEquiv t v = (fun x => (t x : Matrix (Fin 2) (Fin 2) K).mulVec (v.1 x), v.2) := rfl

@[expose] noncomputable def diagHom : (Fin 3 → GL (Fin 2) K) →* (PV K ≃ₗ[K] PV K) where
  toFun := diagEquiv
  map_one' := LinearEquiv.ext fun v => by
    simp only [diagEquiv_apply, Pi.one_apply, Units.val_one, Matrix.one_mulVec]
    rfl
  map_mul' s t := LinearEquiv.ext fun v => by
    simp only [diagEquiv_apply, LinearEquiv.mul_apply, Pi.mul_apply, Units.val_mul,
      Matrix.mulVec_mulVec]

theorem diagHom_injective : Function.Injective (diagHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  funext x
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : (diagEquiv t ((Pi.single x (Pi.single j (1 : K)) : Fin 3 → Fin 2 → K),
        (0 : Fin 2 → K))).1 x i =
      ((Pi.single x (Pi.single j (1 : K)) : Fin 3 → Fin 2 → K), (0 : Fin 2 → K)).1 x i :=
    congrArg (fun e : PV K ≃ₗ[K] PV K => (e ((Pi.single x (Pi.single j (1 : K)) :
      Fin 3 → Fin 2 → K), (0 : Fin 2 → K))).1 x i) ht
  simp only [diagEquiv_apply, Matrix.mulVec_single_one, Pi.single_eq_same] at h
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h

@[expose] def Oq (b c : K) : Subgroup (PV K ≃ₗ[K] PV K) where
  carrier := {g | ∀ v, Qp b c (g v) = Qp b c v}
  one_mem' := fun v => rfl
  mul_mem' := fun {g h} hg hh v => by
    show Qp b c (g (h v)) = Qp b c v
    rw [hg, hh]
  inv_mem' := fun {g} hg v => by
    have := hg (g.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

theorem mem_Oq {g : PV K ≃ₗ[K] PV K} : g ∈ Oq b c ↔ ∀ v, Qp b c (g v) = Qp b c v := Iff.rfl

section Torsion

variable {p : ℕ}

variable (b c) in
@[expose] def Tp (p : ℕ) : Subgroup (GL (Fin 2) K) where
  carrier := {g | g ∈ Tns b c ∧ g ^ p = 1}
  one_mem' := ⟨one_mem _, one_pow _⟩
  mul_mem' := by
    rintro g h ⟨hg, hgp⟩ ⟨hh, hhp⟩
    exact ⟨mul_mem hg hh, by
      rw [Commute.mul_pow (comm_of_mem_Tns hg hh), hgp, hhp, one_mul]⟩
  inv_mem' := by
    rintro g ⟨hg, hgp⟩
    exact ⟨inv_mem hg, by rw [inv_pow, hgp, inv_one]⟩

theorem card_Tp (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) : Nat.card (Tp b c p) = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype (Tns b c) := Fintype.ofFinite _
  have : IsCyclic (Tns b c) := isCyclic_Tns
  apply le_antisymm
  ·
    have h1 : Nat.card (Tp b c p) ≤ Nat.card {a : Tns b c // a ^ p = 1} := by
      refine Nat.card_le_card_of_injective (fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩) ?_
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : {a : Tns b c // a ^ p = 1} => (z.1 : GL (Fin 2) K)) hxy)
    have h2 : Nat.card {a : Tns b c // a ^ p = 1} ≤ p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact IsCyclic.card_pow_eq_one_le hp.pos
    exact h1.trans h2
  ·
    have hdvd : p ∣ Fintype.card (Tns b c) := by
      rw [← Nat.card_eq_fintype_card, card_Tns]
      exact hpq
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hdvd
    have hgp : ((g : Tns b c) : GL (Fin 2) K) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
    have hle : Subgroup.zpowers ((g : Tns b c) : GL (Fin 2) K) ≤ Tp b c p := by
      rw [Subgroup.zpowers_le]
      exact ⟨g.2, hgp⟩
    have hord : orderOf ((g : Tns b c) : GL (Fin 2) K) = p := by
      rw [Subgroup.orderOf_coe, hg]
    calc p = Nat.card (Subgroup.zpowers ((g : Tns b c) : GL (Fin 2) K)) := by
          rw [Nat.card_zpowers, hord]
      _ ≤ Nat.card (Tp b c p) := Subgroup.card_le_of_le hle

end Torsion

section Torus

variable {p : ℕ}

variable (b c p) in
abbrev Pt : Type := Fin 3 → ↥(Tp b c p)

@[expose] def tg (t : Pt b c p) (x : Fin 3) : GL (Fin 2) K := ((t x : Tp b c p) : GL (Fin 2) K)

theorem tg_mem_Tns (t : Pt b c p) (x : Fin 3) : tg t x ∈ Tns b c := (t x).2.1

@[simp] theorem tg_one (x : Fin 3) : tg (1 : Pt b c p) x = 1 := rfl

@[simp] theorem tg_mul (s t : Pt b c p) (x : Fin 3) : tg (s * t) x = tg s x * tg t x := rfl

@[simp] theorem tg_inv (t : Pt b c p) (x : Fin 3) : tg t⁻¹ x = (tg t x)⁻¹ := rfl

variable (b c p) in
@[expose] noncomputable def dh : Pt b c p →* (PV K ≃ₗ[K] PV K) where
  toFun t := diagEquiv (tg t)
  map_one' := by
    show diagHom (tg (1 : Pt b c p)) = 1
    rw [show tg (1 : Pt b c p) = 1 from funext fun x => rfl, map_one]
  map_mul' s t := by
    show diagHom (tg (s * t)) = diagHom (tg s) * diagHom (tg t)
    rw [show tg (s * t) = tg s * tg t from funext fun x => rfl, map_mul]

theorem dh_apply (t : Pt b c p) : dh b c p t = diagEquiv (tg t) := rfl

theorem dh_injective : Function.Injective (dh (K := K) b c p) := by
  intro s t hst
  have h : tg s = tg t := diagHom_injective hst
  funext x
  exact Subtype.ext (congrFun h x)

variable (b c p) in
@[expose] noncomputable def E0 : Subgroup (PV K ≃ₗ[K] PV K) := (dh b c p).range

variable (b c p) in
@[expose] noncomputable def lineSub (x : Fin 3) : Subgroup (PV K ≃ₗ[K] PV K) :=
  ((dh b c p).comp (MonoidHom.mulSingle (fun _ : Fin 3 => ↥(Tp b c p)) x)).range

variable (b c p) in
@[expose] def linePt (x : Fin 3) : Subgroup (Pt b c p) :=
  (MonoidHom.mulSingle (fun _ : Fin 3 => ↥(Tp b c p)) x).range

theorem lineSub_eq_map (x : Fin 3) : lineSub b c p x = (linePt b c p x).map (dh b c p) :=
  MonoidHom.range_comp _ _

theorem lineSub_le_E0 (x : Fin 3) : lineSub b c p x ≤ E0 b c p := by
  rw [lineSub_eq_map]
  exact Subgroup.map_le_range _ _

theorem card_Pt (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) : Nat.card (Pt b c p) = p ^ 3 := by
  rw [Nat.card_pi, Fin.prod_univ_three, card_Tp hp hpq]
  ring

theorem card_E0 (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) : Nat.card (E0 b c p) = p ^ 3 := by
  rw [E0, Nat.card_congr (MonoidHom.ofInjective (dh_injective (K := K) (b := b) (c := c)
    (p := p))).toEquiv.symm, card_Pt hp hpq]

theorem card_lineSub (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) (x : Fin 3) :
    Nat.card (lineSub b c p x) = p := by
  have hinj : Function.Injective ((dh b c p).comp (MonoidHom.mulSingle
      (fun _ : Fin 3 => ↥(Tp b c p)) x)) :=
    (dh_injective (K := K) (b := b) (c := c) (p := p)).comp
      (show Function.Injective (MonoidHom.mulSingle (fun _ : Fin 3 => ↥(Tp b c p)) x) from
        Pi.mulSingle_injective (M := fun _ : Fin 3 => ↥(Tp b c p)) x)
  rw [lineSub, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact card_Tp hp hpq

end Torus

section Lines

variable {p : ℕ}

theorem iSup_linePt : ⨆ x, linePt b c p x = ⊤ := by
  refine eq_top_iff.2 fun t _ => ?_
  have h : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) := by
    funext x
    fin_cases x <;> simp [Pi.mul_apply]
  rw [h]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact Subgroup.mem_iSup_of_mem 0 ⟨t 0, rfl⟩
  · exact Subgroup.mem_iSup_of_mem 1 ⟨t 1, rfl⟩
  · exact Subgroup.mem_iSup_of_mem 2 ⟨t 2, rfl⟩

theorem inf_linePt (x : Fin 3) :
    linePt b c p x ⊓ ⨆ y, ⨆ (_ : y ≠ x), linePt b c p y = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨⟨g, rfl⟩, ht⟩
  have hle : (⨆ y, ⨆ (_ : y ≠ x), linePt b c p y) ≤ (Pi.evalMonoidHom (fun _ : Fin 3 =>
      ↥(Tp b c p)) x).ker := by
    refine iSup₂_le fun y hy => ?_
    rintro _ ⟨h, rfl⟩
    show (Pi.mulSingle y h : Fin 3 → ↥(Tp b c p)) x = 1
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => ↥(Tp b c p)) (Ne.symm hy) h
  have h1 := hle ht
  have hg : g = 1 := by
    have : (Pi.mulSingle x g : Fin 3 → ↥(Tp b c p)) x = 1 := h1
    simpa using this
  subst hg
  show (MonoidHom.mulSingle (fun _ : Fin 3 => ↥(Tp b c p)) x) 1 = 1
  exact map_one _

theorem iSup_lineSub : ⨆ x, lineSub b c p x = E0 b c p := by
  simp only [lineSub_eq_map]
  rw [← Subgroup.map_iSup, iSup_linePt, E0, MonoidHom.range_eq_map]

theorem inf_lineSub (x : Fin 3) :
    lineSub b c p x ⊓ ⨆ y, ⨆ (_ : y ≠ x), lineSub b c p y = ⊥ := by
  have h : (⨆ y, ⨆ (_ : y ≠ x), linePt b c p y).map (dh b c p) =
      ⨆ y, ⨆ (_ : y ≠ x), (linePt b c p y).map (dh b c p) := by
    simp only [Subgroup.map_iSup]
  simp only [lineSub_eq_map]
  rw [← h, ← Subgroup.map_inf_eq _ _ _ dh_injective, inf_linePt, Subgroup.map_bot]

end Lines

section Fix

variable {p : ℕ}

attribute [local instance] Classical.propDecidable

theorem card_fixPlane {g : GL (Fin 2) K} (hg : g ∈ Tns b c) :
    Nat.card {a : Fin 2 → K // (g : Matrix (Fin 2) (Fin 2) K).mulVec a = a} =
      if g = 1 then Nat.card K ^ 2 else 1 := by
  by_cases h1 : g = 1
  · subst h1
    have hall : ∀ a : Fin 2 → K, ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec a = a :=
      fun a => by simp
    simp only [↓reduceIte]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  · simp only [h1, ↓reduceIte]
    have hzero : ∀ a : {a : Fin 2 → K // (g : Matrix (Fin 2) (Fin 2) K).mulVec a = a},
        a.1 = 0 := fun a => Tns_fix hg h1 a.2
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun x y => Subtype.ext ((hzero x).trans (hzero y).symm)⟩,
      ⟨⟨0, by simp⟩⟩⟩

@[expose] def fixEquiv (t : Fin 3 → GL (Fin 2) K) :
    {v : PV K // diagEquiv t v = v} ≃
      (∀ x : Fin 3, {a : Fin 2 → K // (t x : Matrix (Fin 2) (Fin 2) K).mulVec a = a}) ×
        (Fin 2 → K) where
  toFun v := (fun x => ⟨v.1.1 x, congrFun (congrArg Prod.fst v.2) x⟩, v.1.2)
  invFun a := ⟨((fun x => (a.1 x).1, a.2) : PV K), Prod.ext (funext fun x => (a.1 x).2) rfl⟩
  left_inv _ := Subtype.ext (Prod.ext rfl rfl)
  right_inv _ := Prod.ext (funext fun _ => Subtype.ext rfl) rfl

theorem card_fix (t : Fin 3 → GL (Fin 2) K) (ht : ∀ x, t x ∈ Tns b c) :
    Nat.card {v : PV K // diagEquiv t v = v} =
      (∏ x, (if t x = 1 then Nat.card K ^ 2 else 1)) * Nat.card K ^ 2 := by
  rw [Nat.card_congr (fixEquiv t), Nat.card_prod, Nat.card_pi, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  congr 1
  exact Finset.prod_congr rfl fun x _ => card_fixPlane (ht x)

@[expose] noncomputable def n1 (t : Pt b c p) : ℕ := (Finset.univ.filter fun x => t x = 1).card

theorem card_fix_pt (t : Pt b c p) :
    Nat.card {v : PV K // dh b c p t v = v} = Nat.card K ^ (2 * n1 t + 2) := by
  have h := card_fix (tg t) (tg_mem_Tns t)
  show Nat.card {v : PV K // diagEquiv (tg t) v = v} = _
  rw [h]
  have h1 : (∏ x, (if tg t x = 1 then Nat.card K ^ 2 else 1)) = (Nat.card K ^ 2) ^ n1 t := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    simp [n1, tg, OneMemClass.coe_eq_one]
  rw [h1, ← pow_mul, ← pow_add]

end Fix

section Mono

variable {p : ℕ}

attribute [local instance] Classical.propDecidable

theorem eq_of_mem_of_card_prime {G : Type*} [Group G] {H H' : Subgroup G} (hp : p.Prime)
    (hH : Nat.card H = p) (hH' : Nat.card H' = p) {u : G} (hu : u ∈ H) (hu' : u ∈ H')
    (hu1 : u ≠ 1) : H = H' := by
  have key : ∀ {L : Subgroup G}, Nat.card L = p → u ∈ L → Subgroup.zpowers u = L := by
    intro L hL huL
    have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; exact hp.ne_zero)
    have hord : orderOf u = p := by
      have hd : orderOf u ∣ p := by
        have := Subgroup.orderOf_dvd_natCard L huL
        rwa [hL] at this
      rcases (Nat.dvd_prime hp).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hu1
      · exact h
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 huL) ?_
    rw [Nat.card_zpowers, hord, hL]
  exact (key hH hu).symm.trans (key hH' hu')

theorem card_fix_conj (z e : PV K ≃ₗ[K] PV K) :
    Nat.card {v : PV K // (z * e * z⁻¹) v = v} = Nat.card {v : PV K // e v = v} := by
  refine Nat.card_congr ⟨fun v => ⟨z.symm v.1, ?_⟩, fun v => ⟨z v.1, ?_⟩, ?_, ?_⟩
  · have h := v.2
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv] at h
    have h2 := congrArg z.symm h
    simpa using h2
  · simp [LinearEquiv.mul_apply, LinearEquiv.coe_inv, v.2]
  · intro v
    apply Subtype.ext
    simp
  · intro v
    apply Subtype.ext
    simp

theorem lineSub_ne (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {x y : Fin 3} (hxy : x ≠ y) :
    lineSub b c p x ≠ lineSub b c p y := by
  intro h
  have h2 : lineSub b c p y ≤ ⨆ z, ⨆ (_ : z ≠ y), lineSub b c p z := by
    rw [← h]
    exact le_iSup₂_of_le x hxy le_rfl
  have h1 := inf_lineSub (K := K) (b := b) (c := c) (p := p) y
  rw [inf_eq_left.2 h2] at h1
  have h3 := card_lineSub (K := K) (b := b) (c := c) hp hpq y
  rw [h1, Subgroup.card_bot] at h3
  exact hp.one_lt.ne h3

theorem line_conj (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {z : PV K ≃ₗ[K] PV K}
    (hz : ∀ e ∈ E0 b c p, z * e * z⁻¹ ∈ E0 b c p) (x : Fin 3) :
    ∃ j, (lineSub b c p x).map (MulAut.conj z).toMonoidHom = lineSub b c p j := by
  have hnt : Nontrivial (Tp b c p) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [card_Tp hp hpq]; exact hp.one_lt)
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : Tp b c p)
  set t : Pt b c p := Pi.mulSingle x g₀ with ht
  have ht1 : t ≠ 1 := fun h => hg₀ (by simpa [ht] using congrFun h x)
  have hn1 : n1 t = 2 := by
    have : (Finset.univ.filter fun y : Fin 3 => t y = 1) = Finset.univ.erase x := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp [ht, hg₀]
      · simp [ht, hy]
    rw [n1, this, Finset.card_erase_of_mem (Finset.mem_univ x)]
    simp
  obtain ⟨t', ht'⟩ := hz (dh b c p t) ⟨t, rfl⟩
  have hcard := card_fix_conj z (dh b c p t)
  rw [← ht', card_fix_pt, card_fix_pt] at hcard
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hn1' : n1 t' = 2 := by
    have := Nat.pow_right_injective hq hcard
    omega
  obtain ⟨j, hj⟩ : ∃ j, ∀ y, y ≠ j → t' y = 1 := by
    unfold n1 at hn1'
    obtain ⟨a, b', hab, hfil⟩ := Finset.card_eq_two.1 hn1'
    obtain ⟨j, hj⟩ := (by decide : ∀ a b : Fin 3, a ≠ b →
      ∃ j, ∀ y, y ≠ j → y = a ∨ y = b) a b' hab
    refine ⟨j, fun y hy => ?_⟩
    have hy' : y ∈ Finset.univ.filter fun y : Fin 3 => t' y = 1 := by
      rw [hfil]
      rcases hj y hy with h | h <;> simp [h]
    exact (Finset.mem_filter.1 hy').2
  have ht'eq : t' = Pi.mulSingle j (t' j) := by
    funext y
    by_cases hy : y = j
    · subst hy
      simp
    · rw [Pi.mulSingle_eq_of_ne hy, hj y hy]
  have hmem : z * dh b c p t * z⁻¹ ∈ lineSub b c p j := by
    rw [← ht', ht'eq]
    exact ⟨t' j, rfl⟩
  have hne : z * dh b c p t * z⁻¹ ≠ 1 := by
    intro h
    have h1 : dh b c p t = 1 := by
      have h' := congrArg (fun w => z⁻¹ * w * z) h
      simpa [mul_assoc] using h'
    exact ht1 (dh_injective (h1.trans (map_one _).symm))
  refine ⟨j, eq_of_mem_of_card_prime hp ?_ (card_lineSub hp hpq j) ?_ hmem hne⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj z).injective]
    exact card_lineSub hp hpq x
  · exact ⟨dh b c p t, ⟨g₀, rfl⟩, rfl⟩

theorem exists_perm (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {z : PV K ≃ₗ[K] PV K}
    (hz : ∀ e ∈ E0 b c p, z * e * z⁻¹ ∈ E0 b c p) :
    ∃ π : Perm (Fin 3), ∀ i, (lineSub b c p i).map (MulAut.conj z).toMonoidHom =
      lineSub b c p (π i) := by
  choose f hf using line_conj hp hpq hz
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have h1 : (lineSub b c p x).map (MulAut.conj z).toMonoidHom =
        (lineSub b c p y).map (MulAut.conj z).toMonoidHom := by rw [hf x, hf y, hxy]
    exact lineSub_ne hp hpq hne (Subgroup.map_injective (MulAut.conj z).injective h1)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

end Mono

end Model

end CFSG.RankThree.PartOne.AUTSL.Four
