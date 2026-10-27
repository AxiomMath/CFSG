module

public import CFSG.Quasithin.Recognition.F112Crit.L2Sixteen

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G}

theorem le_three_of_dvd_seven {f : ℕ} (hf : 2 * (f - 1) ≤ 9 - 1) (h : 3 ≤ f → f - 2 ∣ 9 - 2) :
    f ≤ 3 := by
  by_contra hlt
  have h7 := h (by omega)
  have h4 : 4 ≤ f := by omega
  have h5 : f ≤ 5 := by omega
  interval_cases f <;> revert h7 <;> decide

variable [Finite G]

open T723

theorem exists_crit_config (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) {L : Subgroup G}
    (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) (hb : Even (critB G₀ G₁ G₂ Z))
    (hb4 : 4 ≤ critB G₀ G₁ G₂ Z) :
    ∃ (α' α₁ α₂ : CosetGeom G₀ G₁ G₂) (z : G), vtype α' = false ∧ vtype α₂ = false ∧
      z ∈ Z ∧ z ∈ stab α' ∧ α₁ ∈ nbrs α₂ ∧ Wv Z α' ≤ stab α₂ ∧ Wv Z α₂ ≤ stab α' ∧
      2 ^ ((Nat.card (nbrs α') - Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ}) / 2) ≤
        2 * (Wv Z α' ⊓ stab α₁).relIndex (Wv Z α') ∧
      2 * (Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ} - 1) ≤ Nat.card (nbrs α') - 1 := by
  have hG := hc.amalgam.gen
  obtain ⟨α', hdist, hnZ⟩ := exists_dist_eq_critB hc
  have hα' : vtype α' = false := CosetGeom.vtype_eq_false_of_even hG (by rw [hdist]; exact hb)
  obtain ⟨z, hzZ, hzn⟩ := SetLike.not_le_iff_exists.mp hnZ
  set b := critB G₀ G₁ G₂ Z with hbdef
  obtain ⟨β, hβ, hβd⟩ := CosetGeom.exists_adj_dist_eq hG (α := γ₀ G₀ G₁ G₂) (δ := α')
    (d := b - 1) (by rw [hdist]; omega)
  have hzβ : z ∈ ballStab 1 β := lt_critB_imp hc (by rw [hβd]; omega) hzZ
  have hzβ' : z ∈ stab β := CosetGeom.ballStab_le_stab 1 β hzβ
  have hzα' : z ∈ stab α' :=
    CosetGeom.mem_ballStab.mp hzβ α'
      (by rw [CosetGeom.dist_comm]; exact (CosetGeom.dist_eq_one_iff_adj.mpr hβ).le)
  obtain ⟨α₁, hα₁, hα₁d⟩ := CosetGeom.exists_adj_dist_eq hG (α := α') (δ := γ₀ G₀ G₁ G₂)
    (d := b - 1) (by rw [CosetGeom.dist_comm, hdist]; omega)
  obtain ⟨α₂, hα₂, hα₂d⟩ := CosetGeom.exists_adj_dist_eq hG (α := α') (δ := α₁) (d := b - 2)
    (by rw [hα₁d]; omega)
  have hvα₂ : vtype α₂ = false := by
    have h := (CosetGeom.vtype_eq_iff_even_dist hG α' α₂).mpr
      (by rw [hα₂d]; obtain ⟨k, hk⟩ := hb; exact ⟨k - 1, by omega⟩)
    rw [hα'] at h
    exact h.symm
  have hW : Wv Z α' ≤ stab α₂ :=
    Wv_le_stab hc hα' (by rw [CosetGeom.dist_comm, hα₂d]; omega)
      (by rw [CosetGeom.dist_comm, hα₂d]; omega)
  have hW₂ : Wv Z α₂ ≤ stab α' := Wv_le_stab hc hvα₂ (by rw [hα₂d]; omega) (by rw [hα₂d]; omega)
  have hel : IsElemAbelian 2 (Wv Z α') := isElemAbelian_Wv hc hb4 hα'
  haveI : IsMulCommutative ↥(Wv Z α') := hel.1
  obtain ⟨X₁, h₁⟩ :=
    exists_isLocalReg_of_vtype hloc (vtype_eq_true_of_mem_nbrs CosetGeom.vtype_γ₀ hα₁)
  have hup := card_commSubgroup_le_two_mul_relIndex hc h₁ hα₁ hα₂
    (fun v hv => by rw [← pow_two]; exact hel.2 v hv) hW hzZ (stab_le_normalizer_Wv hc α' hzα')
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hα'
  have hL' : BenderLocal α' (conjSub (g : G) L) := by
    rw [hg]
    exact hL.smul g
  exact ⟨α', α₁, α₂, z, hα', hvα₂, hzZ, hzα', CosetGeom.mem_nbrs_symm hα₂, hW, hW₂,
    (T723.lower_bound hc hloc hp hb4 hα' hL' hβ hzZ hzα').trans hup,
    T723.fixed_bound hG hL' hβ hzα' hzβ' hzn⟩

theorem false_of_three_points (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) (hb4 : 4 ≤ critB G₀ G₁ G₂ Z)
    {α α' : CosetGeom G₀ G₁ G₂} (hα : vtype α = false) (hα' : vtype α' = false)
    {L : Subgroup G} (hL : BenderLocal α L) (hW' : Wv Z α' ≤ stab α) (hW : Wv Z α ≤ stab α')
    {ω : ↥(nbrs α)} {a b : ↥(stab α)} (ha : (a : G) ∈ Wv Z α') (hb : (b : G) ∈ Wv Z α')
    (h1 : a • ω ≠ ω) (h2 : b • ω ≠ ω) (h3 : b • ω ≠ a • ω) : False := by
  classical
  obtain ⟨ω, hω⟩ := ω
  have hWab : IsElemAbelian 2 (Wv Z α) := isElemAbelian_Wv hc hb4 hα
  haveI : IsMulCommutative ↥(Wv Z α) := hWab.1
  haveI : Fact (stab α ≤ Subgroup.normalizer (Wv Z α : Set G)) := ⟨stab_le_normalizer_Wv hc α⟩
  have h2M := ConjAut.add_self_eq_zero (Wv Z α) fun v hv => by rw [← pow_two]; exact hWab.2 v hv
  obtain ⟨U, hUL, hU2, -, hUtrans, -, -⟩ := exists_unipotentH hL hω
  set ω₀ : ↥(nbrs α) := ⟨ω, hω⟩ with hω₀
  obtain ⟨hV, hstab, hK⟩ := avg_inputs hc hloc hp hα hL
  have htrans := exists_mem_smul_eq hL
  have hW'ab : IsElemAbelian 2 (Wv Z α') := isElemAbelian_Wv hc hb4 hα'
  haveI : IsMulCommutative ↥(Wv Z α') := hW'ab.1
  set P : Subgroup ↥(stab α) := (Wv Z α').subgroupOf (stab α) with hPdef
  have hP : IsPGroup 2 P := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    show ((x : ↥(stab α)) : G) ^ 2 ^ 1 = 1
    rw [pow_one]
    exact hW'ab.2 _ x.2
  have hPL : P ≤ Subgroup.normalizer
      ((L.subgroupOf (stab α) : Subgroup ↥(stab α)) : Set ↥(stab α)) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro l
    exact Subgroup.mem_normalizer_iff.mp (hL.normal x.2) (l : G)
  obtain ⟨X, c, hXL, -, hcK, hcX, hcfix, hcP, hlast⟩ :=
    PermBound.exists_avg_of_isPGroup (H := ↥(stab α)) (Ω := ↥(nbrs α))
      (M := Additive ↥(Wv Z α)) h2M (subgroupOf_odd_gen hL.le_stab hL.odd_gen) htrans
      (odd_card_nbrs hc hα) (fun μ => Vmod Z (Wv Z α) μ.1) hV (iSup_Vmod_eq_top α) hstab hP hPL
      hK ω₀
  obtain ⟨d, hd1, hdc, hdP⟩ := PermBound.exists_d htrans ω₀ (S := (P : Set ↥(stab α)))
    (fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (hPL hx) l).mp hl) hXL hcfix hcP
  have hquad : ∀ x y : ↥(stab α), (x : G) ∈ Wv Z α' → (y : G) ∈ Wv Z α' →
      ∀ m : Additive ↥(Wv Z α), x • (y • m - m) = y • m - m := by
    intro x y hx hy m
    have hm : ((Additive.toMul m : ↥(Wv Z α)) : G) ∈ stab α' := hW (Additive.toMul m).2
    have hcom : (y : G) * ((Additive.toMul m : ↥(Wv Z α)) : G) * (y : G)⁻¹ *
        ((Additive.toMul m : ↥(Wv Z α)) : G)⁻¹ ∈ Wv Z α' := by
      have h := (Wv Z α').mul_mem hy ((Subgroup.mem_normalizer_iff.mp
        (stab_le_normalizer_Wv hc α' hm) _).mp ((Wv Z α').inv_mem hy))
      simpa only [mul_assoc] using h
    have hval : ((Additive.toMul (y • m - m) : ↥(Wv Z α)) : G) =
        (y : G) * ((Additive.toMul m : ↥(Wv Z α)) : G) * (y : G)⁻¹ *
          ((Additive.toMul m : ↥(Wv Z α)) : G)⁻¹ := by
      rw [← div_eq_mul_inv]
      rfl
    rw [ConjAut.eq_iff_val]
    show (x : G) * ((Additive.toMul (y • m - m) : ↥(Wv Z α)) : G) * (x : G)⁻¹ = _
    rw [hval, setLike_mul_comm hx hcom, mul_inv_cancel_right]
  have hab : ((a * b : ↥(stab α)) : G) ∈ Wv Z α' := (Wv Z α').mul_mem ha hb
  have hsum : d ω₀ + d (a • ω₀) + d (b • ω₀) + d ((a * b) • ω₀) ∈ X := by
    have hq := hquad a b ha hb (d ω₀)
    rw [smul_sub, smul_smul] at hq
    have hQ : (b • d ω₀ - d ω₀) - ((a * b) • d ω₀ - a • d ω₀) = 0 := by
      rw [hq, sub_self]
    have e : d ω₀ + d (a • ω₀) + d (b • ω₀) + d ((a * b) • ω₀) =
        -((b • d ω₀ - d ω₀) - ((a * b) • d ω₀ - a • d ω₀)) -
          ((a * b) • d ω₀ - d ((a * b) • ω₀)) + (a • d ω₀ - d (a • ω₀)) +
          (b • d ω₀ - d (b • ω₀)) + (d (a • ω₀) + d (a • ω₀)) + (d (b • ω₀) + d (b • ω₀)) := by
      abel
    rw [e, hQ, h2M (d (a • ω₀)), h2M (d (b • ω₀)), neg_zero, zero_sub, add_zero, add_zero]
    exact X.add_mem (X.add_mem (X.neg_mem (hdP (a * b) hab _)) (hdP a ha _)) (hdP b hb _)
  have hainv : a * a = 1 :=
    Subtype.ext (by show (a : G) * a = 1; rw [← pow_two]; exact hW'ab.2 _ ha)
  have hbinv : b * b = 1 :=
    Subtype.ext (by show (b : G) * b = 1; rw [← pow_two]; exact hW'ab.2 _ hb)
  have habc : a * b = b * a := Subtype.ext (setLike_mul_comm ha hb)
  have h4 : (a * b) • ω₀ ≠ ω₀ := by
    intro h
    apply h3
    calc b • ω₀ = a • ((a * b) • ω₀) := by rw [smul_smul, ← mul_assoc, hainv, one_mul]
      _ = a • ω₀ := by rw [h]
  have h5 : (a * b) • ω₀ ≠ a • ω₀ := by
    intro h
    apply h2
    calc b • ω₀ = a • ((a * b) • ω₀) := by rw [smul_smul, ← mul_assoc, hainv, one_mul]
      _ = a • (a • ω₀) := by rw [h]
      _ = ω₀ := by rw [smul_smul, hainv, one_smul]
  have h6 : (a * b) • ω₀ ≠ b • ω₀ := by
    intro h
    apply h1
    calc a • ω₀ = b • ((a * b) • ω₀) := by rw [habc, smul_smul, ← mul_assoc, hbinv, one_mul]
      _ = b • (b • ω₀) := by rw [h]
      _ = ω₀ := by rw [smul_smul, hbinv, one_smul]
  haveI := Fintype.ofFinite ↥(nbrs α)
  have hodd : Odd (Fintype.card ↥(nbrs α)) := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_card_nbrs hc hα
  have hn3 : b • ω₀ ∉ ({(a * b) • ω₀} : Finset ↥(nbrs α)) := by
    rw [Finset.mem_singleton]
    exact fun h => h6 h.symm
  have hn2 : a • ω₀ ∉ ({b • ω₀, (a * b) • ω₀} : Finset ↥(nbrs α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h3 h.symm, fun h => h5 h.symm⟩
  have hn1 : ω₀ ∉ ({a • ω₀, b • ω₀, (a * b) • ω₀} : Finset ↥(nbrs α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h1 h.symm, fun h => h2 h.symm, fun h => h4 h.symm⟩
  have hcard : ({ω₀, a • ω₀, b • ω₀, (a * b) • ω₀} : Finset ↥(nbrs α)).card = 4 := by
    rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
      Finset.card_insert_of_notMem hn3, Finset.card_singleton]
  refine PermBound.sum_not_mem h2M htrans hodd hUL hU2 hUtrans hXL hcK hcX hlast hd1 hdc
    (B := {ω₀, a • ω₀, b • ω₀, (a * b) • ω₀}) ⟨ω₀, Finset.mem_insert_self _ _⟩
    ⟨2, hcard.trans rfl⟩ ?_
  rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3, Finset.sum_singleton,
    ← add_assoc, ← add_assoc]
  exact hsum

theorem card_nbrs_γ₀_ne_nine (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hloc : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p = 3 ∨ p = 5) {L M : Subgroup G}
    (hL : BenderLocal (γ₀ G₀ G₁ G₂) L) (hT : TorusLocal (γ₀ G₀ G₁ G₂) M)
    (hb : Even (critB G₀ G₁ G₂ Z)) (hb4 : 4 ≤ critB G₀ G₁ G₂ Z) :
    Nat.card (nbrs (γ₀ G₀ G₁ G₂)) ≠ 9 := by
  classical
  intro h9
  obtain ⟨α', α₁, α₂, z, hα', hvα₂, hzZ, hzα', hα₁α₂, hW, hW₂, hlow, hf⟩ :=
    exists_crit_config hc hloc hp hL hb hb4
  have hN : Nat.card (nbrs α') = 9 := (card_nbrs_eq hc hα').trans h9
  rw [hN] at hlow hf
  have hf3 : Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ} ≤ 3 := by
    refine le_three_of_dvd_seven hf fun h3 => ?_
    obtain ⟨ω₀, μ₀, ν₀, hω₀, hμ₀, hν₀, h01, h02, h12⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite {δ | δ ∈ nbrs α' ∧ z ∈ stab δ})).mp
        (by rw [← Nat.card_coe_set_eq]; omega)
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hα'
    have hT' : TorusLocal α' (conjSub (g : G) M) := by
      rw [hg]
      exact hT.smul g
    have h := hT'.card_fixed_sub_two_dvd hzα' hω₀ hμ₀ hν₀ h01 h02 h12
    rwa [hN] at h
  have h3 : 3 ≤ (9 - Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ}) / 2 := by omega
  have h8 : 8 ≤ 2 ^ ((9 - Nat.card {δ | δ ∈ nbrs α' ∧ z ∈ stab δ}) / 2) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h3)
  have hidx : 2 < (Wv Z α' ⊓ stab α₁).relIndex (Wv Z α') := by omega
  have hWG₀ : Wv Z α' ≤ G₀ := hW.trans (CosetGeom.stab_le α₂)
  letI : MulAction ↥(Wv Z α') (CosetGeom G₀ G₁ G₂) :=
    MulAction.compHom _ (Subgroup.inclusion hWG₀)
  have hsm : ∀ g : ↥(Wv Z α'), g • α₁ = (⟨(g : G), hWG₀ g.2⟩ : ↥G₀) • α₁ := fun g => rfl
  have hstabW : MulAction.stabilizer ↥(Wv Z α') α₁ =
      (Wv Z α' ⊓ stab α₁).subgroupOf (Wv Z α') := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsm]
    exact ⟨fun hg => ⟨g.2, CosetGeom.mem_stab_of_smul_eq hg⟩,
      fun hg => CosetGeom.smul_eq_of_mem_stab hg.2⟩
  have horb : 2 < (MulAction.orbit ↥(Wv Z α') α₁).ncard := by
    rw [← MulAction.index_stabilizer, hstabW]
    exact hidx
  obtain ⟨_, _, _, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩, ⟨g₃, rfl⟩, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite (MulAction.orbit ↥(Wv Z α') α₁))).mp horb
  have hmem : ∀ g : ↥(Wv Z α'), g • α₁ ∈ nbrs α₂ := fun g => by
    rw [hsm]
    exact IsLocalReg.smul_mem_nbrs (g := ⟨(g : G), hWG₀ g.2⟩) hα₁α₂ (hW g.2)
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hvα₂
  have hL₂ : BenderLocal α₂ (conjSub (g : G) L) := by
    rw [hg]
    exact hL.smul g
  let w : ↥(Wv Z α') → ↥(stab α₂) := fun x => ⟨x, hW x.2⟩
  have key : ∀ x y : ↥(Wv Z α'),
      w (y * x⁻¹) • (⟨x • α₁, hmem x⟩ : ↥(nbrs α₂)) = ⟨y • α₁, hmem y⟩ := by
    intro x y
    apply Subtype.ext
    show (y * x⁻¹) • x • α₁ = y • α₁
    rw [smul_smul, inv_mul_cancel_right]
  refine false_of_three_points hc hloc hp hb4 hvα₂ hα' hL₂ hW hW₂ (ω := ⟨g₁ • α₁, hmem g₁⟩)
    (a := w (g₂ * g₁⁻¹)) (b := w (g₃ * g₁⁻¹)) (g₂ * g₁⁻¹).2 (g₃ * g₁⁻¹).2 ?_ ?_ ?_
  · rw [key]
    exact fun h => h12 (congrArg Subtype.val h).symm
  · rw [key]
    exact fun h => h13 (congrArg Subtype.val h).symm
  · rw [key, key]
    exact fun h => h23 (congrArg Subtype.val h).symm

end CFSG.Quasithin.F112Crit

end
