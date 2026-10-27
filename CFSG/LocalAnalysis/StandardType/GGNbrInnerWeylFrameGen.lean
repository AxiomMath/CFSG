module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameNoLine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

section SplitSL2

variable {K : Type} [Field K]

theorem splitDiagHSL_mul (a b : Kˣ) : HSL a * HSL b = HSL (a * b) := by
  apply SL2_ext <;> simp [coe_HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem splitDiagHSL_one : HSL (1 : Kˣ) = (1 : SL2 K) := by
  apply SL2_ext <;> simp [coe_HSL]

theorem splitDiagHSL_pow (a : Kˣ) (m : ℕ) : (HSL a : SL2 K) ^ m = HSL (a ^ m) := by
  induction m with
  | zero => simp [splitDiagHSL_one]
  | succ m ih => rw [pow_succ, ih, splitDiagHSL_mul, ← pow_succ]

theorem splitDiagHSL_inv (a : Kˣ) : (HSL a : SL2 K)⁻¹ = HSL a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [splitDiagHSL_mul, mul_inv_cancel, splitDiagHSL_one]

theorem splitWSL_conj_HSL (a : Kˣ) : (WSL : SL2 K) * HSL a * WSL⁻¹ = HSL a⁻¹ := by
  have h1 : (WSL : SL2 K) * HSL a = HSL a⁻¹ * WSL := by
    apply SL2_ext <;> simp [coe_WSL, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

end SplitSL2

theorem exists_order_p_inverting_sl2_split {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    ∃ s n : SL2 K, orderOf s = p ∧ n * s * n⁻¹ = s⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨μ, hμo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hμp : μ ^ p = 1 := by rw [← hμo]; exact pow_orderOf_eq_one μ
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hμo
    exact hp.ne_one hμo.symm
  refine ⟨HSL μ, WSL, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [splitDiagHSL_pow, hμp, splitDiagHSL_one]
    · intro h
      have h00 := congrArg (fun x : SL2 K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
      exact hμ1 (Units.ext (by simpa [coe_HSL] using h00))
  · rw [splitWSL_conj_HSL, splitDiagHSL_inv]

section FrameScale

variable {p N : ℕ}

@[expose] def frameScaleCoord (u : ZMod p) (i : Fin N) :
    (Fin N → Multiplicative (ZMod p)) →* (Fin N → Multiplicative (ZMod p)) where
  toFun f j := if j = i then (f j) ^ u.val else f j
  map_one' := by
    funext j
    simp only [Pi.one_apply]
    split_ifs
    · exact one_pow _
    · rfl
  map_mul' f g := by
    funext j
    simp only [Pi.mul_apply]
    split_ifs
    · rw [mul_pow]
    · rfl

theorem frameScaleCoord_apply (u : ZMod p) (i : Fin N)
    (f : Fin N → Multiplicative (ZMod p)) (j : Fin N) :
    frameScaleCoord u i f j = if j = i then (f j) ^ u.val else f j :=
  rfl

theorem frameScaleCoord_mulSingle (u : ZMod p) (i j : Fin N) (a : Multiplicative (ZMod p)) :
    frameScaleCoord u i (Pi.mulSingle j a) =
      Pi.mulSingle j (if j = i then a ^ u.val else a) := by
  funext k
  rw [frameScaleCoord_apply]
  by_cases hkj : k = j
  · subst hkj
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hkj, Pi.mulSingle_eq_of_ne hkj]
    split_ifs
    · exact one_pow _
    · rfl

theorem frameScaleCoord_ofAdd [NeZero p] (u : ZMod p) (i : Fin N) (v : Fin N → ZMod p) :
    frameScaleCoord u i (fun j => Multiplicative.ofAdd (v j)) =
      fun j => Multiplicative.ofAdd ((Function.update v i (u * v i)) j) := by
  funext j
  rw [frameScaleCoord_apply]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, Function.update_self, ← ofAdd_nsmul]
    congr 1
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  · rw [if_neg hji, Function.update_of_ne hji]

end FrameScale

theorem exists_frameTorus_of_commutingFrames {G₀ : Type} [Group G₀] {p N : ℕ} (hp : p.Prime)
    (u : ZMod p) (s n : G₀) (hs : orderOf s = p) (hn : n * s * n⁻¹ = s ^ u.val)
    (hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center G₀)) {R : Type} [Group R]
    (ρ : Fin N → G₀ →* R) (hρ : ∀ i, Function.Injective (ρ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B)) :
    ∃ (e : Multiplicative (Fin N → ZMod p) →* R) (m : Fin N → R),
      Function.Injective e ∧
      (∀ (i : Fin N) (a : ZMod p), e (Multiplicative.ofAdd (Pi.single i a)) = ρ i (s ^ a.val)) ∧
      ∀ (i : Fin N) (v : Fin N → ZMod p),
        m i * e (Multiplicative.ofAdd v) * (m i)⁻¹ =
          e (Multiplicative.ofAdd (Function.update v i (u * v i))) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hs_pow : s ^ p = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hpow : ∀ i : Fin N, (ρ i s) ^ p = 1 := fun i => by
    rw [← map_pow, hs_pow, map_one]
  let coord : Fin N → Multiplicative (ZMod p) →* R := fun i => TableBSymp.zmodPowHom (hpow i)
  have coord_apply : ∀ (i : Fin N) (a : Multiplicative (ZMod p)),
      coord i a = ρ i (s ^ (Multiplicative.toAdd a).val) := fun i a => by
    change TableBSymp.zmodPowHom (hpow i) a = ρ i (s ^ (Multiplicative.toAdd a).val)
    rw [TableBSymp.zmodPowHom_apply, map_pow]
  have coord_inj : ∀ i, Function.Injective (coord i) := fun i => by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hto : orderOf (ρ i s) = p := by
      rw [orderOf_injective _ (hρ i), hs]
    exact (TableBSymp.zmodPowHom_eq_one_iff (hpow i) hto).mp ha
  have coord_comm : Pairwise fun i j : Fin N => ∀ a b, Commute (coord i a) (coord j b) := by
    intro i j hij a b
    rw [coord_apply, coord_apply]
    exact hc i j hij _ _
  let ePi : (Fin N → Multiplicative (ZMod p)) →* R := MonoidHom.noncommPiCoprod coord coord_comm
  let e : Multiplicative (Fin N → ZMod p) →* R :=
    ePi.comp (MulEquiv.piMultiplicative fun _ : Fin N => ZMod p).toMonoidHom
  have e_apply : ∀ v : Fin N → ZMod p, e (.ofAdd v) = ePi (fun j => .ofAdd (v j)) := fun v => rfl
  have coord_indep : iSupIndep fun i => (coord i).range := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := hx
    have hle : (⨆ (j) (_ : j ≠ i), (coord j).range) ≤
        Subgroup.centralizer (Set.range (ρ i)) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨B, rfl⟩ := hy
      rw [coord_apply]
      exact (hc i j (fun h => hj h.symm) B (s ^ (Multiplicative.toAdd b).val)).eq
    have hcen := hle hx'
    have hs_center : s ^ (Multiplicative.toAdd a).val ∈ Subgroup.center G₀ := by
      rw [Subgroup.mem_center_iff]
      intro B
      have h1 := Subgroup.mem_centralizer_iff.mp hcen (ρ i B) ⟨B, rfl⟩
      rw [coord_apply] at h1
      have h2 : ρ i (B * s ^ (Multiplicative.toAdd a).val) =
          ρ i (s ^ (Multiplicative.toAdd a).val * B) := by
        rw [map_mul, map_mul]
        exact h1
      exact hρ i h2
    have hs_one : s ^ (Multiplicative.toAdd a).val = 1 :=
      (Subgroup.disjoint_def.mp hZ) (Subgroup.npow_mem_zpowers s _) hs_center
    have hdvd : p ∣ (Multiplicative.toAdd a).val := by
      have := orderOf_dvd_of_pow_eq_one hs_one
      rwa [hs] at this
    have hval0 : (Multiplicative.toAdd a).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have ha1 : a = 1 := by
      rw [← ofAdd_toAdd a, (ZMod.val_eq_zero (Multiplicative.toAdd a)).mp hval0, ofAdd_zero]
    rw [ha1, map_one]
  have ePi_inj : Function.Injective ePi :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep coord coord_indep coord_inj
  have e_inj : Function.Injective e :=
    ePi_inj.comp (MulEquiv.piMultiplicative fun _ : Fin N => ZMod p).injective
  have reflGen_conj_coord : ∀ (i j : Fin N) (a : Multiplicative (ZMod p)),
      ρ i n * coord j a * (ρ i n)⁻¹ = coord j (if j = i then a ^ u.val else a) := by
    intro i j a
    split_ifs with hji
    · subst hji
      rw [map_pow, coord_apply, ← map_pow, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [← conj_pow, hn, ← pow_mul, ← pow_mul, mul_comm]
    · rw [coord_apply,
        (hc i j (fun h => hji h.symm) n (s ^ (Multiplicative.toAdd a).val)).eq,
        mul_inv_cancel_right]
  have reflGen_conj_ePi : ∀ (i : Fin N) (f : Fin N → Multiplicative (ZMod p)),
      ρ i n * ePi f * (ρ i n)⁻¹ = ePi (frameScaleCoord u i f) := by
    intro i f
    have h : (MulAut.conj (ρ i n)).toMonoidHom.comp ePi = ePi.comp (frameScaleCoord u i) :=
      MonoidHom.pi_ext fun j a => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ePi,
          MonoidHom.noncommPiCoprod_mulSingle, frameScaleCoord_mulSingle]
        exact reflGen_conj_coord i j a
    have h1 := congrArg (fun φ => φ f) h
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  have reflGen_conj_e : ∀ (i : Fin N) (v : Fin N → ZMod p),
      ρ i n * e (.ofAdd v) * (ρ i n)⁻¹ = e (.ofAdd (Function.update v i (u * v i))) := by
    intro i v
    rw [e_apply, e_apply, reflGen_conj_ePi, frameScaleCoord_ofAdd]
  have e_single : ∀ (i : Fin N) (a : ZMod p),
      e (.ofAdd (Pi.single i a)) = ρ i (s ^ a.val) := by
    intro i a
    rw [e_apply]
    have hfun : (fun j => Multiplicative.ofAdd
          (Pi.single (M := fun _ : Fin N => ZMod p) i a j)) =
        Pi.mulSingle (M := fun _ : Fin N => Multiplicative (ZMod p)) i
          (Multiplicative.ofAdd a) := by
      funext j
      exact (Pi.mulSingle_multiplicativeOfAdd_eq (M := fun _ : Fin N => ZMod p) i a j).symm
    rw [hfun, MonoidHom.noncommPiCoprod_mulSingle, coord_apply, toAdd_ofAdd]
  exact ⟨e, fun i => ρ i n, e_inj, e_single, reflGen_conj_e⟩

section FrameScaleNormalizer

variable {R : Type} [Group R] [Finite R]

theorem frameScale_mem_normalizer_range {p N : ℕ} (u : ZMod p)
    (e : Multiplicative (Fin N → ZMod p) →* R) (m : Fin N → R)
    (hm : ∀ (i : Fin N) (v : Fin N → ZMod p),
      m i * e (.ofAdd v) * (m i)⁻¹ = e (.ofAdd (Function.update v i (u * v i))))
    (i : Fin N) :
    m i ∈ Subgroup.normalizer (e.range : Set R) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, rfl⟩ := hx
    rw [← ofAdd_toAdd w]
    refine ⟨Multiplicative.ofAdd (Function.update w.toAdd i (u * w.toAdd i)), ?_⟩
    change e (Multiplicative.ofAdd (Function.update w.toAdd i (u * w.toAdd i))) =
      m i * e (Multiplicative.ofAdd w.toAdd) * (m i)⁻¹
    exact (hm i w.toAdd).symm
  · rw [Subgroup.card_map_of_injective (MulAut.conj (m i)).injective]

end FrameScaleNormalizer

theorem ggSCNoLine_of_sylowTorus_frameGen {G₀ : Type} [Group G₀] {p N : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (u : ZMod p) (hu : u ≠ 1) (s n : G₀) (hs : orderOf s = p)
    (hn : n * s * n⁻¹ = s ^ u.val) (hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center G₀))
    {R : Type} [Group R] [Finite R] (hT : SylowTorus R p N) (ρ : Fin N → G₀ →* R)
    (hρ : ∀ i, Function.Injective (ρ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B))
    (hmove : ∀ i : Fin N, ∃ j : Fin N, j ≠ i ∧ ∃ (g : R) (t : ZMod p), t ≠ 0 ∧
      g * ρ i s * g⁻¹ = ρ j (s ^ t.val)) (r : ℕ) : GGSCNoLine p r R := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e, m, he_inj, he_single, hm_conj⟩ :=
    exists_frameTorus_of_commutingFrames hp u s n hs hn hZ ρ hρ hc
  let E : Subgroup R := e.range
  have hE : IsElemAbelian p E := by
    change IsElemAbelian p e.range
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · obtain ⟨v, hv⟩ := a.2
      obtain ⟨w, hw⟩ := b.2
      show (a : R) * (b : R) = (b : R) * (a : R)
      rw [← hv, ← hw, ← map_mul, ← map_mul]
      congr 1
      exact mul_comm v w
    · obtain ⟨v, hv⟩ := hx
      rw [← hv, ← map_pow, ← ofAdd_toAdd v, ← ofAdd_nsmul,
        ZModModule.char_nsmul_eq_zero, ofAdd_zero, map_one]
  have hcardE : Nat.card E = p ^ N := by
    change Nat.card e.range = p ^ N
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective he_inj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  have hmN : ∀ i, m i ∈ Subgroup.normalizer (E : Set R) := fun i =>
    frameScale_mem_normalizer_range u e m hm_conj i
  intro E₁ hE₁ _ _ hsc e₁ he₁ he₁ne
  obtain ⟨c, hcE⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT hE hcardE hE₁ hsc
  set e₀ : R := c⁻¹ * e₁ * c with he₀def
  have he₀E : e₀ ∈ E := by
    have he₁' : e₁ ∈ E.map (MulAut.conj c).toMonoidHom := by rw [← hcE]; exact he₁
    obtain ⟨x, hxE, hx⟩ := Subgroup.mem_map.mp he₁'
    rw [he₀def, ← hx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c⁻¹ * (c * x * c⁻¹) * c = x from by group]
    exact hxE
  have he₀ne : e₀ ≠ 1 := by
    intro h
    apply he₁ne
    have he₁eq : e₁ = c * e₀ * c⁻¹ := by rw [he₀def]; group
    rw [he₁eq, h]
    simp
  have he₀range : e₀ ∈ e.range := he₀E
  obtain ⟨w, hw⟩ := he₀range
  let v : Fin N → ZMod p := w.toAdd
  have he₀v : e₀ = e (.ofAdd v) := by
    rw [← hw, ← ofAdd_toAdd w]
  have hv0 : v ≠ 0 := by
    intro hv
    apply he₀ne
    rw [he₀v, hv, ofAdd_zero, map_one]
  have core : ∃ g₀ ∈ Subgroup.normalizer (E : Set R),
      g₀ * e₀ * g₀⁻¹ ∉ Subgroup.zpowers e₀ := by
    by_cases htwo : ∃ i j : Fin N, i ≠ j ∧ v i ≠ 0 ∧ v j ≠ 0
    · obtain ⟨i, j, hij, hvi, hvj⟩ := htwo
      refine ⟨m i, hmN i, ?_⟩
      rw [he₀v, hm_conj i v]
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hk' : e (.ofAdd (k • v)) = e (.ofAdd (Function.update v i (u * v i))) := by
        rw [← hk, ← map_zpow, ← ofAdd_zsmul]
      have hveq : k • v = Function.update v i (u * v i) := he_inj hk'
      have hj_eq : (k : ZMod p) * v j = v j := by
        have h := congrFun hveq j
        rw [Pi.smul_apply, Function.update_of_ne (Ne.symm hij)] at h
        rwa [zsmul_eq_mul] at h
      have hk1 : (k : ZMod p) = 1 := by
        refine mul_right_cancel₀ hvj ?_
        rw [one_mul]
        exact hj_eq
      have hi_eq : v i = u * v i := by
        have h := congrFun hveq i
        rw [Pi.smul_apply, Function.update_self, zsmul_eq_mul, hk1, one_mul] at h
        exact h
      have hzero : (u - 1) * v i = 0 := by
        rw [sub_one_mul, ← hi_eq, sub_self]
      have hu1 : u - 1 ≠ 0 := fun h => hu (sub_eq_zero.mp h)
      rcases mul_eq_zero.mp hzero with h | h
      · exact hu1 h
      · exact hvi h
    · push Not at htwo
      obtain ⟨i, hvi⟩ : ∃ i : Fin N, v i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (funext fun j => h j)
      have hv_single : v = Pi.single i (v i) := by
        funext j
        by_cases hji : j = i
        · subst hji; rw [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hji]
          exact (htwo i j (Ne.symm hji)) hvi
      have he₀i : e₀ = ρ i (s ^ (v i).val) := by
        rw [he₀v]
        conv_lhs => rw [hv_single]
        rw [he_single]
      have he₀single : e₀ = e (.ofAdd (Pi.single i (v i))) := by
        rw [he₀v]
        conv_lhs => rw [hv_single]
      obtain ⟨j, hji, g, t, ht, hgt⟩ := hmove i
      have hg₀ : g * e₀ * g⁻¹ = e (.ofAdd (Pi.single j (t * v i))) := by
        have h1 : g * e₀ * g⁻¹ = ρ j (s ^ (t.val * (v i).val)) := by
          rw [he₀i, map_pow, ← conj_pow, hgt, ← map_pow, ← pow_mul]
        have hexp : s ^ (t.val * (v i).val) = s ^ (t * (v i)).val := by
          rw [pow_eq_pow_iff_modEq, hs]
          exact (ZMod.natCast_eq_natCast_iff _ _ p).mp (by
            simp only [Nat.cast_mul, ZMod.natCast_zmod_val])
        rw [h1, hexp, he_single]
      obtain ⟨P, hEP, hPcomm, hPΩ⟩ :=
        exists_sylow_of_sylowTorus_elemAbelian hp hT hE hcardE
      have he₀P : e₀ ∈ (P : Subgroup R) := hEP he₀E
      have hgy : e (.ofAdd (Pi.single j (t * v i))) ∈ (P : Subgroup R) := hEP ⟨_, rfl⟩
      obtain ⟨n', hnP, hnconj⟩ :=
        exists_mem_normalizer_conj_of_commutative_sylow P hPcomm he₀P hgy hg₀
      have hnE : n' ∈ Subgroup.normalizer (E : Set R) :=
        ggFrame_mem_normalizer_of_le_and_pow_eq_one hEP hE.2 hPΩ hnP
      refine ⟨n', hnE, ?_⟩
      rw [hnconj]
      intro hmem
      rw [he₀single] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hk' : e (.ofAdd (k • Pi.single i (v i))) =
          e (.ofAdd (Pi.single j (t * v i))) := by
        rw [← hk, ← map_zpow, ← ofAdd_zsmul]
      have hveq : k • Pi.single i (v i) = Pi.single j (t * v i) := he_inj hk'
      have hthis := congrFun hveq j
      rw [Pi.smul_apply, Pi.single_eq_of_ne hji, smul_zero, Pi.single_eq_same] at hthis
      exact (mul_ne_zero ht hvi) hthis.symm
  obtain ⟨g₀, hg₀N, hg₀not⟩ := core
  refine ⟨c * g₀ * c⁻¹, ?_, ?_⟩
  · have hmem : c * g₀ * c⁻¹ ∈
        (Subgroup.normalizer (E : Set R)).map (MulAut.conj c).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨g₀, hg₀N, by simp [MulAut.conj_apply]⟩
    rw [Subgroup.map_equiv_normalizer_eq E (MulAut.conj c)] at hmem
    rwa [← hcE] at hmem
  · have he₁eq : e₁ = c * e₀ * c⁻¹ := by rw [he₀def]; group
    have hge : c * g₀ * c⁻¹ * e₁ * (c * g₀ * c⁻¹)⁻¹ =
        c * (g₀ * e₀ * g₀⁻¹) * c⁻¹ := by
      rw [he₁eq]; group
    rw [hge, he₁eq]
    intro hmem
    exact hg₀not ((ggFrame_mem_zpowers_conj_iff c (g₀ * e₀ * g₀⁻¹) e₀).mp hmem)

end CFSG.StandardType

end
