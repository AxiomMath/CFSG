module

public import CFSG.Quasithin.Vol2.Ch3B513NBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

theorem mem_commV_of_commute {H : Subgroup (MulAut W)} {a : MulAut W}
    (ha : ∀ h ∈ H, a * h = h * a) {v : W} (hv : v ∈ commV H) : a v ∈ commV H := by
  have hle : commV H ≤ (commV H).comap a.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨h, hh, w, rfl⟩
    show a (h w * w⁻¹) ∈ commV H
    rw [map_mul, map_inv, ← MulAut.mul_apply, ha h hh, MulAut.mul_apply]
    exact Subgroup.subset_closure ⟨h, hh, a w, rfl⟩
  exact hle hv

theorem cmHom_mem_commV {H : Subgroup (MulAut W)} {a : MulAut W} (ha : a ∈ H) (v : W) :
    cmHom a v ∈ commV H :=
  Subgroup.subset_closure ⟨a, ha, v, rfl⟩

theorem commV_mono {H K : Subgroup (MulAut W)} (h : H ≤ K) : commV H ≤ commV K :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ => ⟨x, h hx, v, hv⟩

theorem commute_of_fix_commV {H : Subgroup (MulAut W)}
    (hfix : ∀ h ∈ H, ∀ v ∈ commV H, h v = v) {x y : MulAut W} (hx : x ∈ H) (hy : y ∈ H) :
    x * y = y * x := by
  ext w
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have ex : x w = w * cmHom x w := by rw [cmHom_apply, mul_comm, inv_mul_cancel_right]
  have ey : y w = w * cmHom y w := by rw [cmHom_apply, mul_comm, inv_mul_cancel_right]
  rw [ex, ey, map_mul, map_mul, hfix x hx _ (cmHom_mem_commV hy w),
    hfix y hy _ (cmHom_mem_commV hx w), ex, ey]
  ac_rfl

variable [Finite W]

theorem card_subgroup_two_pow (hW : ∀ w : W, w ^ 2 = 1) (S : Subgroup W) :
    ∃ j, Nat.card S = 2 ^ j :=
  (isPGroup_two_subgroup hW S).exists_card_eq

theorem card_map_cmHom_sq_le (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W} (ha : a ^ 2 = 1)
    (Y : Subgroup W) (hY : ∀ y ∈ Y, a y ∈ Y) :
    Nat.card ↥(Y.map (cmHom a)) ^ 2 ≤ Nat.card Y := by
  set f : ↥Y →* W := (cmHom a).comp Y.subtype with hf
  have hrange : f.range = Y.map (cmHom a) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card f.range * Nat.card f.ker = Nat.card Y := by
    rw [← Subgroup.index_ker, Subgroup.index_mul_card]
  have hle : Nat.card f.range ≤ Nat.card f.ker := by
    have hmem : ∀ y : ↥Y, f y ∈ Y := fun y =>
      Y.mul_mem (hY _ y.2) (Y.inv_mem y.2)
    let g : ↥f.range → ↥f.ker := fun z => ⟨⟨z, by
      obtain ⟨y, hy⟩ := z.2
      rw [← hy]
      exact hmem y⟩, by
      obtain ⟨y, hy⟩ := z.2
      rw [MonoidHom.mem_ker]
      show cmHom a (z : W) = 1
      rw [← hy]
      exact cmHom_cmHom ha hW _⟩
    have hinj : Function.Injective g := by
      intro z₁ z₂ h
      apply Subtype.ext
      have := congrArg (fun t : ↥f.ker => ((t : ↥Y) : W)) h
      exact this
    exact Nat.card_le_card_of_injective g hinj
  rw [← hrange, pow_two]
  calc Nat.card f.range * Nat.card f.range ≤ Nat.card f.range * Nat.card f.ker :=
        Nat.mul_le_mul_left _ hle
    _ = Nat.card Y := hcard

omit [Finite W] in
theorem isSolvable_of_case2 {G : Subgroup (MulAut W)} (h : B56Case2 G) : Group.IsSolvable ↥G := by
  obtain ⟨⟨e⟩, -, -⟩ := h
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

@[expose] def inv6 : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem inv6_ne_one : inv6 ≠ 1 := by
  intro h
  have := congrArg (fun σ : ↥(alternatingGroup (Fin 6)) => (σ : Equiv.Perm (Fin 6)) 0) h
  revert this
  decide

theorem inv6_sq : inv6 ^ 2 = 1 := by
  apply Subtype.ext
  show (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) ^ 2 = 1
  decide

theorem hasGood_of_case4 (hW : ∀ w : W, w ^ 2 = 1) {G : Subgroup (MulAut W)} (h : B56Case4 G) :
    HasGood G := by
  obtain ⟨G₁, G₂, t, hG, -, hcomm, ⟨e⟩, -, hsup, -, hdir, hcard1, -⟩ := h
  set a : MulAut W := (e.symm inv6 : MulAut W) with ha_def
  have haG₁ : a ∈ G₁ := (e.symm inv6).2
  have haG : a ∈ G := by
    rw [hG]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left haG₁)
  have ha1 : a ≠ 1 := by
    intro h1
    apply inv6_ne_one
    have : e.symm inv6 = 1 := Subtype.ext h1
    rw [← e.symm.map_one] at this
    exact e.symm.injective this
  have ha2 : a ^ 2 = 1 := by
    have : (e.symm inv6) ^ 2 = 1 := by rw [← map_pow, inv6_sq, map_one]
    exact congrArg Subtype.val this
  refine HasGood.of_zpowers hW haG ha1 ha2 ?_
  set V₁ := commV G₁
  set V₂ := commV G₂
  have hV₁inv : ∀ y ∈ V₁, a y ∈ V₁ := fun y hy => by
    have : a y = cmHom a y * y := by rw [cmHom_apply, inv_mul_cancel_right]
    rw [this]
    exact V₁.mul_mem (cmHom_mem_commV haG₁ y) hy
  have hrange : (cmHom a).range ≤ V₁.map (cmHom a) := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ fixV G ⊔ (V₁ ⊔ V₂) := by rw [hsup]; trivial
    obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup.1 hw
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.1 hu
    have hca : cmHom a c = 1 := by rw [cmHom_apply, hc a haG, mul_inv_cancel]
    have hv₂a : cmHom a v₂ = 1 := by
      have h1 : cmHom a v₂ ∈ V₁ := cmHom_mem_commV haG₁ v₂
      have h2 : cmHom a v₂ ∈ V₂ := V₂.mul_mem
        (mem_commV_of_commute (fun b hb => hcomm a haG₁ b hb) hv₂) (V₂.inv_mem hv₂)
      have h3 : cmHom a v₂ ∈ V₁ ⊓ V₂ := ⟨h1, h2⟩
      rw [hdir.2, Subgroup.mem_bot] at h3
      exact h3
    refine ⟨v₁, hv₁, ?_⟩
    rw [map_mul, map_mul, hca, hv₂a, one_mul, mul_one]
  have hsq := card_map_cmHom_sq_le hW ha2 V₁ hV₁inv
  obtain ⟨j, hj⟩ := card_subgroup_two_pow hW (V₁.map (cmHom a))
  have hV₁32 : Nat.card V₁ ≤ 2 ^ 5 := by
    rcases hcard1 with h4 | h5
    · rw [h4]; norm_num
    · rw [h5]
  have hj2 : j ≤ 2 := by
    by_contra hj3
    push Not at hj3
    have : 2 ^ (2 * j) ≤ 2 ^ 5 := by
      rw [pow_mul', ← hj]
      exact hsq.trans hV₁32
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    omega
  calc Nat.card (commV (Subgroup.zpowers a)) ≤ Nat.card ↥(V₁.map (cmHom a)) :=
        Subgroup.card_le_of_le ((commV_zpowers_le_range a).trans hrange)
    _ = 2 ^ j := hj
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
    _ = 4 := by norm_num

@[expose] def tr01 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def tr10 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide⟩

theorem tr01_sq : tr01 ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem tr01_ne_one : tr01 ≠ 1 := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) =>
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1) h
  revert this
  decide

theorem tr_not_comm : tr01 * tr10 ≠ tr10 * tr01 := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) =>
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0) h
  revert this
  decide

theorem hasGood_of_case5 (hW : ∀ w : W, w ^ 2 = 1) {G : Subgroup (MulAut W)} (h : B56Case5 G) :
    HasGood G := by
  obtain ⟨G₁, G₂, hG, -, -, -, ⟨e⟩, hcard1, -⟩ := h
  set ε := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).trans e.symm with hε
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 le_rfl
  set a : MulAut W := (ε tr01 : MulAut W) with ha_def
  have haG₁ : a ∈ G₁ := (ε tr01).2
  have haG : a ∈ G := hG ▸ Subgroup.mem_sup_left haG₁
  have ha1 : a ≠ 1 := by
    intro h1
    apply tr01_ne_one
    have : ε tr01 = 1 := Subtype.ext h1
    rw [← ε.map_one] at this
    exact ε.injective this
  have ha2 : a ^ 2 = 1 := by
    have : (ε tr01) ^ 2 = 1 := by rw [← map_pow, tr01_sq, map_one]
    exact congrArg Subtype.val this
  refine HasGood.of_zpowers hW haG ha1 ha2 ?_
  set V₁ := commV G₁
  have hmove : ∃ v ∈ V₁, a v ≠ v := by
    by_contra hcon
    push Not at hcon
    let N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      { carrier := {g | ∀ v ∈ V₁, ((ε g : ↥G₁) : MulAut W) v = v}
        one_mem' := fun v _ => by rw [map_one]; rfl
        mul_mem' := fun {g h} hg hh v hv => by
          rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply, hh v hv, hg v hv]
        inv_mem' := fun {g} hg v hv => by
          have h1 := hg v hv
          calc ((ε g⁻¹ : ↥G₁) : MulAut W) v
              = ((ε g : ↥G₁) : MulAut W)⁻¹ (((ε g : ↥G₁) : MulAut W) v) := by
                rw [h1, map_inv, Subgroup.coe_inv]
            _ = v := MulAut.inv_apply_self _ _ v }
    have hNnormal : N.Normal := by
      refine ⟨fun g hg k v hv => ?_⟩
      have hkv : ((ε k⁻¹ : ↥G₁) : MulAut W) v ∈ V₁ := by
        have : ((ε k⁻¹ : ↥G₁) : MulAut W) v = cmHom (ε k⁻¹ : ↥G₁) v * v := by
          rw [cmHom_apply, inv_mul_cancel_right]
        rw [this]
        exact V₁.mul_mem (cmHom_mem_commV (ε k⁻¹).2 v) hv
      show ((ε (k * g * k⁻¹) : ↥G₁) : MulAut W) v = v
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply, MulAut.mul_apply,
        hg _ hkv, ← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have htr : tr01 ∈ N := fun v hv => hcon v hv
    have hNtop : N = ⊤ := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple N hNnormal with hbot | htop
      · exact absurd (hbot ▸ htr : tr01 ∈ (⊥ : Subgroup _)) (by
          rw [Subgroup.mem_bot]; exact tr01_ne_one)
      · exact htop
    have hfix : ∀ x ∈ G₁, ∀ v ∈ V₁, x v = v := by
      intro x hx v hv
      obtain ⟨g, hg⟩ := ε.surjective ⟨x, hx⟩
      have : g ∈ N := hNtop ▸ Subgroup.mem_top g
      have := this v hv
      rw [hg] at this
      exact this
    apply tr_not_comm
    apply ε.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact commute_of_fix_commV hfix (ε tr01).2 (ε tr10).2
  obtain ⟨v, hv, hav⟩ := hmove
  have hle : commV (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers a) ⊓ V₁ :=
    le_inf (commV_zpowers_le_fixV ha2 hW) (commV_mono (Subgroup.zpowers_le.2 haG₁))
  have hlt : fixV (Subgroup.zpowers a) ⊓ V₁ < V₁ := by
    refine lt_of_le_of_ne inf_le_right fun heq => hav ?_
    have hv' : v ∈ fixV (Subgroup.zpowers a) ⊓ V₁ := by rw [heq]; exact hv
    exact hv'.1 a (Subgroup.mem_zpowers a)
  have hdvd : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ V₁) ∣ Nat.card V₁ :=
    Subgroup.card_dvd_of_le inf_le_right
  have hlt' : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ V₁) < Nat.card V₁ :=
    Subgroup.card_lt_of_lt hlt
  rw [hcard1] at hdvd hlt'
  have h4 : Nat.card ↥(fixV (Subgroup.zpowers a) ⊓ V₁) ≤ 4 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hk] at hlt' ⊢
    have : k < 3 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt'
    interval_cases k <;> norm_num
  exact (Subgroup.card_le_of_le hle).trans h4

end CFSG.Quasithin.B513N
