module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Transport
public import CFSG.Quasithin.H13.A6S13827b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace A6Nrm

open A6Coc

theorem exists_perm_heart (φ : AltHeart 6 →+ AltHeart 6)
    (hφinj : Function.Injective φ) (ψ : Γ →* Γ)
    (hφψ : ∀ (x : Γ) (y : AltHeart 6),
      φ (heartAct 6 (x : Perm (Fin 6)) y) = heartAct 6 (ψ x : Perm (Fin 6)) (φ y)) :
    ∃ σ : Perm (Fin 6), (∀ x : Γ, (ψ x : Perm (Fin 6)) = σ * x * σ⁻¹) ∧
      ∀ y, φ y = heartAct 6 σ y := by
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  have hfix : ∀ x : Γ, fixCount (ψ x : Perm (Fin 6)) = fixCount (x : Perm (Fin 6)) := by
    intro x
    rw [fixCount_eq, fixCount_eq]
    let e : {y : AltHeart 6 // heartAct 6 (x : Perm (Fin 6)) y = y} ≃
        {y : AltHeart 6 // heartAct 6 (ψ x : Perm (Fin 6)) y = y} :=
      { toFun := fun y => ⟨φ y.1, by rw [← hφψ, y.2]⟩
        invFun := fun z => ⟨Function.surjInv hφsurj z.1,
          hφinj (by rw [hφψ, Function.surjInv_eq hφsurj]; exact z.2)⟩
        left_inv := fun y => Subtype.ext (hφinj (Function.surjInv_eq hφsurj _))
        right_inv := fun z => Subtype.ext (Function.surjInv_eq hφsurj _) }
    exact (Nat.card_congr e).symm
  obtain ⟨ha3, hafix, hb5, hab4, hab3⟩ := rels_ab
  have hrel : ∀ (x : Γ) (n : ℕ), (x : Perm (Fin 6)) ^ n = 1 →
      (ψ x : Perm (Fin 6)) ^ n = 1 := by
    intro x n hx
    have hx' : x ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx)
    rw [← Subgroup.coe_pow, ← map_pow, hx', map_one]
    rfl
  obtain ⟨σ, hσa, hσb⟩ := Certificates.certificate7093 (ψ aL) (ψ bL)
    ⟨hrel aL 3 ha3, by rw [hfix]; exact hafix, hrel bL 5 hb5,
      by
        have := hrel (aL * bL) 4 hab4
        rwa [map_mul, Subgroup.coe_mul] at this,
      by
        have := hrel (aL ^ 2 * bL ^ 2) 3
          (by rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]; exact hab3)
        rwa [map_mul, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow,
          Subgroup.coe_pow] at this⟩
  have hψσ : ∀ x : Γ, (ψ x : Perm (Fin 6)) = σ * x * σ⁻¹ := by
    have key : (alternatingGroup (Fin 6)).subtype.comp ψ =
        (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 6)).subtype := by
      refine MonoidHom.eq_of_eqOn_dense closure_ab ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · show (ψ aL : Perm (Fin 6)) = σ * aP * σ⁻¹
        exact hσa.symm
      · show (ψ bL : Perm (Fin 6)) = σ * bP * σ⁻¹
        exact hσb.symm
    intro x
    exact DFunLike.congr_fun key x
  let χ : AltHeart 6 →+ AltHeart 6 := (heartAct 6 σ⁻¹).comp φ
  have hχ : ∀ (x : Γ) (y : AltHeart 6),
      χ (heartAct 6 (x : Perm (Fin 6)) y) = heartAct 6 (x : Perm (Fin 6)) (χ y) := by
    intro x y
    show heartAct 6 σ⁻¹ (φ (heartAct 6 (x : Perm (Fin 6)) y)) =
      heartAct 6 (x : Perm (Fin 6)) (heartAct 6 σ⁻¹ (φ y))
    rw [hφψ, hψσ, ← heartAct_mul, ← heartAct_mul,
      show σ⁻¹ * (σ * (x : Perm (Fin 6)) * σ⁻¹) = (x : Perm (Fin 6)) * σ⁻¹ by group]
  have hσχ : ∀ y, heartAct 6 σ (χ y) = φ y := by
    intro y
    show heartAct 6 σ (heartAct 6 σ⁻¹ (φ y)) = φ y
    rw [← heartAct_mul, mul_inv_cancel, heartAct_one]
  let M : Vec4 →+ Vec4 := eps.comp (χ.comp epsInvHom)
  have hMact : ∀ (x : Γ) (v : Vec4),
      M (act (x : Perm (Fin 6)) v) = act (x : Perm (Fin 6)) (M v) := by
    intro x v
    show eps (χ (epsInv (act x v))) = act x (eps (χ (epsInv v)))
    have e : epsInv (act (x : Perm (Fin 6)) v) = heartAct 6 (x : Perm (Fin 6)) (epsInv v) := by
      apply eps_injective
      rw [eps_epsInv, eps_heartAct, eps_epsInv]
    rw [e, hχ, eps_heartAct]
  rcases schur M (hMact aL) (hMact bL) with h0 | hid
  · exfalso
    have h1 : eps (χ (epsInv e₀)) = 0 := by
      have : M e₀ = 0 := by rw [h0]; rfl
      exact this
    have h2 : χ (epsInv e₀) = 0 := eps_injective (by rw [map_zero]; exact h1)
    have h3 : φ (epsInv e₀) = 0 := by rw [← hσχ, h2, map_zero]
    have h4 : epsInv e₀ = 0 := hφinj (by rw [h3, map_zero])
    have h5 := eps_epsInv e₀
    rw [h4, map_zero] at h5
    exact e₀_ne_zero h5.symm
  · refine ⟨σ, hψσ, fun y => ?_⟩
    have h1 : eps (χ (epsInv (eps y))) = eps y := by
      have : M (eps y) = eps y := by rw [hid]; rfl
      exact this
    rw [epsInv_eps] at h1
    rw [← hσχ, eps_injective h1]

theorem fix_ab : ∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 → vp aP y = y → vp bP y = y →
    y = 0 ∨ y = onesV := by
  decide +kernel

@[expose] def duadPerm : Fin 5 → Perm (Fin 6) :=
  ![1, swap 0 1 * swap 1 2, swap 0 2 * swap 1 3, swap 0 3 * swap 1 4, swap 0 4 * swap 1 5]

theorem duadPerm_facts : ∀ k : Fin 5, Perm.sign (duadPerm k) = 1 ∧
    vp (duadPerm k) (wt2v 0 1) = wt2v k.castSucc k.succ := by
  decide +kernel

theorem duad_decomp : ∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 →
    y = y 0 • wt2v 0 1 + (y 0 + y 1) • wt2v 1 2 + (y 0 + y 1 + y 2) • wt2v 2 3 +
      (y 0 + y 1 + y 2 + y 3) • wt2v 3 4 + (y 0 + y 1 + y 2 + y 3 + y 4) • wt2v 4 5 := by
  decide +kernel

theorem ones_eq : onesV = wt2v 0 1 + wt2v 2 3 + wt2v 4 5 := by decide

theorem wt2v_mem (i j : Fin 6) (hij : i < j) : wt2v i j ∈ evenWeight 6 :=
  mem_ev_of_sum_zero (wt2v_facts.1 i j hij)

theorem exists_perm_even
    (φ : ↥(evenWeight 6) →+ ↥(evenWeight 6)) (hφinj : Function.Injective φ) (ψ : Γ →* Γ)
    (hψs : Function.Surjective ψ)
    (hφψ : ∀ (x : Γ) (y : ↥(evenWeight 6)),
      φ (permWeight 6 (x : Perm (Fin 6)) y) = permWeight 6 (ψ x : Perm (Fin 6)) (φ y)) :
    ∃ σ : Perm (Fin 6), (∀ x : Γ, (ψ x : Perm (Fin 6)) = σ * x * σ⁻¹) ∧
      ∀ y, φ y = permWeight 6 σ y := by
  have hfix1 : ∀ x : Γ, permWeight 6 (ψ x : Perm (Fin 6)) (φ onesE) = φ onesE := by
    intro x
    rw [← hφψ]
    congr 1
  have hφ1 : φ onesE = onesE := by
    obtain ⟨a', ha'⟩ := hψs aL
    obtain ⟨b', hb'⟩ := hψs bL
    have h1 := hfix1 a'
    have h2 := hfix1 b'
    rw [ha'] at h1
    rw [hb'] at h2
    rcases fix_ab _ (sum_eq_zero (φ onesE)) (congrArg Subtype.val h1)
      (congrArg Subtype.val h2) with h | h
    · exfalso
      have h0 : φ onesE = φ 0 := by rw [map_zero]; exact Subtype.ext h
      have := hφinj h0
      have h5 := congrArg (fun y : ↥(evenWeight 6) => (y : Fin 6 → ZMod 2) 0) this
      exact absurd h5 (by decide)
    · exact Subtype.ext h
  have hcw : ∀ y ∈ constWeight 6, φ y ∈ constWeight 6 := by
    intro y hy
    have hy' : (y : Fin 6 → ZMod 2) = 0 ∨ (y : Fin 6 → ZMod 2) = onesV :=
      (constWeight_iff _).1 hy
    rcases hy' with h | h
    · have : y = 0 := Subtype.ext h
      rw [this, map_zero]
      exact (constWeight 6).zero_mem
    · have : y = onesE := Subtype.ext h
      rw [this, hφ1]
      exact (constWeight_iff _).2 (Or.inr rfl)
  let φb : AltHeart 6 →+ AltHeart 6 := QuotientAddGroup.map _ _ φ hcw
  have hφb : ∀ y, φb (QuotientAddGroup.mk y) = QuotientAddGroup.mk (φ y) := fun _ => rfl
  have hφbinj : Function.Injective φb := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hφb, mk_eq_zero_iff] at hz
    rw [mk_eq_zero_iff]
    rcases hz with h | h
    · left
      have : φ y = φ 0 := by rw [map_zero]; exact Subtype.ext h
      rw [hφinj this]
      rfl
    · right
      have : φ y = φ onesE := by rw [hφ1]; exact Subtype.ext h
      rw [hφinj this]
      rfl
  have hφbψ : ∀ (x : Γ) (z : AltHeart 6),
      φb (heartAct 6 (x : Perm (Fin 6)) z) = heartAct 6 (ψ x : Perm (Fin 6)) (φb z) := by
    intro x z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [heartAct_mk, hφb, hφb, heartAct_mk, hφψ]
  obtain ⟨σ, hψσ, hφσ⟩ := exists_perm_heart φb hφbinj ψ hφbψ
  refine ⟨σ, hψσ, fun y => ?_⟩
  set χ : ↥(evenWeight 6) →+ ↥(evenWeight 6) := (permWeightHom 6 σ⁻¹).comp φ with hχ
  have hχapp : ∀ y, χ y = permWeight 6 σ⁻¹ (φ y) := fun _ => rfl
  have hχmod : ∀ y, (QuotientAddGroup.mk (χ y) : AltHeart 6) = QuotientAddGroup.mk y := by
    intro y
    have h1 := hφσ (QuotientAddGroup.mk y)
    rw [hφb, heartAct_mk] at h1
    have h2 : (QuotientAddGroup.mk (χ y) : AltHeart 6) =
        heartAct 6 σ⁻¹ (QuotientAddGroup.mk (φ y)) := rfl
    rw [h2, h1, ← heartAct_mk, ← heartAct_mul, inv_mul_cancel, heartAct_one]
  have hχA : ∀ (x : Γ) y, χ (permWeight 6 (x : Perm (Fin 6)) y) =
      permWeight 6 (x : Perm (Fin 6)) (χ y) := by
    intro x y
    apply Subtype.ext
    funext i
    rw [hχapp, hχapp, hφψ, hψσ]
    show (φ y : Fin 6 → ZMod 2) ((σ * (x : Perm (Fin 6)) * σ⁻¹)⁻¹ (σ⁻¹⁻¹ i)) =
      (φ y : Fin 6 → ZMod 2) (σ⁻¹⁻¹ ((x : Perm (Fin 6))⁻¹ i))
    simp [Perm.mul_apply]
  have hχ1 : χ onesE = onesE := by
    rw [hχapp, hφ1]
    rfl
  have hdef : ∀ y, (χ y : Fin 6 → ZMod 2) = y ∨ (χ y : Fin 6 → ZMod 2) = y + onesV :=
    fun y => (mk_eq_mk_iff _ _).1 (hχmod y)
  have hdefA : ∀ (x : Γ) y, (χ y : Fin 6 → ZMod 2) = y →
      (χ (permWeight 6 (x : Perm (Fin 6)) y) : Fin 6 → ZMod 2) =
        permWeight 6 (x : Perm (Fin 6)) y := by
    intro x y h
    rw [hχA]
    show (fun i => (χ y : Fin 6 → ZMod 2) ((x : Perm (Fin 6))⁻¹ i)) =
      fun i => (y : Fin 6 → ZMod 2) ((x : Perm (Fin 6))⁻¹ i)
    rw [h]
  set e01 : ↥(evenWeight 6) := ⟨wt2v 0 1, wt2v_mem 0 1 (by decide)⟩ with he01
  set e23 : ↥(evenWeight 6) := ⟨wt2v 2 3, wt2v_mem 2 3 (by decide)⟩ with he23
  set e45 : ↥(evenWeight 6) := ⟨wt2v 4 5, wt2v_mem 4 5 (by decide)⟩ with he45
  have hconj : ∀ (k : Fin 5) (w : ↥(evenWeight 6)),
      (w : Fin 6 → ZMod 2) = wt2v k.castSucc k.succ →
      ((χ w : Fin 6 → ZMod 2) = w ↔ (χ e01 : Fin 6 → ZMod 2) = e01) := by
    intro k w hw
    obtain ⟨hs, hv⟩ := duadPerm_facts k
    set x : Γ := ⟨duadPerm k, by rw [Perm.mem_alternatingGroup]; exact hs⟩ with hx
    have hxw : permWeight 6 (x : Perm (Fin 6)) e01 = w := Subtype.ext (by
      rw [hw, ← hv]
      rfl)
    have hxw' : permWeight 6 ((x⁻¹ : Γ) : Perm (Fin 6)) w = e01 := by
      rw [← hxw]
      apply Subtype.ext
      funext i
      show (e01 : Fin 6 → ZMod 2) ((x : Perm (Fin 6))⁻¹ ((((x⁻¹ : Γ) : Perm (Fin 6)))⁻¹ i)) =
        (e01 : Fin 6 → ZMod 2) i
      simp
    constructor
    · intro h
      have := hdefA x⁻¹ w h
      rwa [hxw'] at this
    · intro h
      have := hdefA x e01 h
      rwa [hxw] at this
  have he01 : (χ e01 : Fin 6 → ZMod 2) = e01 := by
    rcases hdef e01 with h | h
    · exact h
    exfalso
    have h23 : (χ e23 : Fin 6 → ZMod 2) = e23 + onesV := by
      rcases hdef e23 with h' | h'
      · have := (hconj 2 e23 rfl).1 h'
        rw [this] at h
        exact absurd (congrArg (fun v => v 0) h) (by decide)
      · exact h'
    have h45 : (χ e45 : Fin 6 → ZMod 2) = e45 + onesV := by
      rcases hdef e45 with h' | h'
      · have := (hconj 4 e45 rfl).1 h'
        rw [this] at h
        exact absurd (congrArg (fun v => v 0) h) (by decide)
      · exact h'
    have hsum : onesE = e01 + e23 + e45 := Subtype.ext ones_eq
    have h1 := congrArg Subtype.val hχ1
    rw [hsum, map_add, map_add] at h1
    simp only [AddSubgroup.coe_add] at h1
    rw [h, h23, h45] at h1
    exact absurd (congrArg (fun v => v 0) h1) (by decide)
  have hduad : ∀ (k : Fin 5) (w : ↥(evenWeight 6)), (w : Fin 6 → ZMod 2) =
      wt2v k.castSucc k.succ → χ w = w :=
    fun k w hw => Subtype.ext ((hconj k w hw).2 he01)
  have hpart : ∀ (k : Fin 5) (c : ZMod 2), ∃ u : ↥(evenWeight 6),
      (u : Fin 6 → ZMod 2) = c • wt2v k.castSucc k.succ ∧ χ u = u := by
    intro k c
    rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) c with h | h
    · exact ⟨0, by rw [h, zero_smul]; rfl, map_zero χ⟩
    · exact ⟨⟨wt2v k.castSucc k.succ, wt2v_mem _ _ Fin.castSucc_lt_succ⟩,
        by rw [h, one_smul], hduad k _ rfl⟩
  have hχid : χ y = y := by
    have hd := duad_decomp (y : Fin 6 → ZMod 2) (sum_eq_zero y)
    obtain ⟨u0, hu0, hχ0⟩ := hpart 0 ((y : Fin 6 → ZMod 2) 0)
    obtain ⟨u1, hu1, hχ1'⟩ := hpart 1 ((y : Fin 6 → ZMod 2) 0 + (y : Fin 6 → ZMod 2) 1)
    obtain ⟨u2, hu2, hχ2⟩ := hpart 2 ((y : Fin 6 → ZMod 2) 0 + (y : Fin 6 → ZMod 2) 1 +
      (y : Fin 6 → ZMod 2) 2)
    obtain ⟨u3, hu3, hχ3⟩ := hpart 3 ((y : Fin 6 → ZMod 2) 0 + (y : Fin 6 → ZMod 2) 1 +
      (y : Fin 6 → ZMod 2) 2 + (y : Fin 6 → ZMod 2) 3)
    obtain ⟨u4, hu4, hχ4⟩ := hpart 4 ((y : Fin 6 → ZMod 2) 0 + (y : Fin 6 → ZMod 2) 1 +
      (y : Fin 6 → ZMod 2) 2 + (y : Fin 6 → ZMod 2) 3 + (y : Fin 6 → ZMod 2) 4)
    have hy : y = u0 + u1 + u2 + u3 + u4 := by
      apply Subtype.ext
      simp only [AddSubgroup.coe_add]
      rw [hu0, hu1, hu2, hu3, hu4]
      exact hd
    rw [hy, map_add, map_add, map_add, map_add, hχ0, hχ1', hχ2, hχ3, hχ4]
  have : φ y = permWeight 6 σ (χ y) := by
    apply Subtype.ext
    funext i
    show (φ y : Fin 6 → ZMod 2) i = (φ y : Fin 6 → ZMod 2) (σ⁻¹⁻¹ (σ⁻¹ i))
    simp
  rw [this, hχid]

theorem act_faithful : ∀ σ : Perm (Fin 6), (∀ v : Vec4, act σ v = v) → σ = 1 := by
  decide +kernel

theorem vp_faithful : ∀ σ : Perm (Fin 6), (∀ i j : Fin 6, i < j → vp σ (wt2v i j) = wt2v i j) →
    σ = 1 := by
  decide +kernel

structure Model (M : Type) [AddGroup M] where
  act : Perm (Fin 6) → M →+ M
  act_mul : ∀ σ τ y, act (σ * τ) y = act σ (act τ y)
  act_one : ∀ y, act 1 y = y
  faithful : ∀ σ, (∀ y, act σ y = y) → σ = 1
  nrm : ∀ φ : M →+ M, Function.Injective φ → ∀ ψ : Γ →* Γ, Function.Surjective ψ →
    (∀ (x : Γ) y, φ (act (x : Perm (Fin 6)) y) = act (ψ x : Perm (Fin 6)) (φ y)) →
    ∃ σ : Perm (Fin 6), ∀ y, φ y = act σ y

@[expose] noncomputable def heartModel : Model (AltHeart 6) where
  act σ := heartAct 6 σ
  act_mul := heartAct_mul
  act_one := heartAct_one
  faithful σ h := act_faithful σ fun v => by
    rw [← eps_epsInv v, ← eps_heartAct, h]
  nrm φ hφ ψ _ h := by
    obtain ⟨σ, -, hσ⟩ := exists_perm_heart φ hφ ψ h
    exact ⟨σ, hσ⟩

@[expose] noncomputable def evenModel :
    Model ↥(evenWeight 6) where
  act σ := permWeightHom 6 σ
  act_mul σ τ y := Subtype.ext (by
    funext i
    show (y : Fin 6 → ZMod 2) ((σ * τ)⁻¹ i) = (y : Fin 6 → ZMod 2) (τ⁻¹ (σ⁻¹ i))
    simp [Perm.mul_apply])
  act_one y := Subtype.ext (by
    funext i
    show (y : Fin 6 → ZMod 2) ((1 : Perm (Fin 6))⁻¹ i) = (y : Fin 6 → ZMod 2) i
    simp)
  faithful σ h := vp_faithful σ fun i j hij => by
    have := congrArg Subtype.val (h ⟨wt2v i j, wt2v_mem i j hij⟩)
    exact this
  nrm φ hφ ψ hψ h := by
    obtain ⟨σ, -, hσ⟩ := exists_perm_even φ hφ ψ hψ h
    exact ⟨σ, hσ⟩


end A6Nrm

end CFSG.Quasithin.H13.A6
