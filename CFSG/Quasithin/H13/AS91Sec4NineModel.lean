module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeStd

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.Nine

open Subgroup CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.Coc24
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6

@[expose] def t1Arr : Array ℕ := wArr [lzXArr, lzYArr] [0, 1, 1, 0, 1, 1]

@[expose] def t2Arr : Array ℕ := wArr [lzXArr, lzYArr] [1, 0, 0, 1, 1, 0, 1, 0]

@[expose] def tau1 : Equiv.Perm (Fin 24) := wPerm [lzX, lzY] [0, 1, 1, 0, 1, 1]

@[expose] def tau2 : Equiv.Perm (Fin 24) := wPerm [lzX, lzY] [1, 0, 0, 1, 1, 0, 1, 0]

theorem hasArr_tau1 : HasArr tau1 t1Arr :=
  hasArr_wPerm (hasArr_getD₂ hasArr_lzX hasArr_lzY) _

theorem hasArr_tau2 : HasArr tau2 t2Arr :=
  hasArr_wPerm (hasArr_getD₂ hasArr_lzX hasArr_lzY) _

theorem wPerm_lz_mem (w : List ℕ) : wPerm [lzX, lzY] w ∈ Lz := by
  refine wPerm_mem (fun p hp => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact lzX_mem_Lz
  · exact lzY_mem_Lz

theorem tau1_mem_Lz : tau1 ∈ Lz := wPerm_lz_mem _

theorem tau2_mem_Lz : tau2 ∈ Lz := wPerm_lz_mem _

theorem tau1_comm : tau1 * r0 = r0 * tau1 := by
  have h := hasArr_mul hasArr_tau1 hasArr_r0
  rw [show cArr t1Arr r0Arr = cArr r0Arr t1Arr by decide +kernel] at h
  exact perm_eq_of_hasArr h (hasArr_mul hasArr_r0 hasArr_tau1)

theorem tau2_comm : tau2 * r0 = r0 * tau2 := by
  have h := hasArr_mul hasArr_tau2 hasArr_r0
  rw [show cArr t2Arr r0Arr = cArr r0Arr t2Arr by decide +kernel] at h
  exact perm_eq_of_hasArr h (hasArr_mul hasArr_r0 hasArr_tau2)

@[expose] noncomputable def tau1Aut : MulAut W11 :=
  rho11 AutPerm le_rfl ⟨tau1, Lz_le tau1_mem_Lz⟩

@[expose] noncomputable def tau2Aut : MulAut W11 :=
  rho11 AutPerm le_rfl ⟨tau2, Lz_le tau2_mem_Lz⟩

theorem toW11_inv (m : ℕ) : (toW 11 m)⁻¹ = toW 11 m :=
  inv_eq_of_mul_eq_one_right (by rw [← toW_xor, Nat.xor_self, toW_zero])

theorem rho11_mem_img11_of_mem {Γ : Subgroup (Equiv.Perm (Fin 24))} {σ : Equiv.Perm (Fin 24)}
    (hσ : σ ∈ Γ) (hσA : σ ∈ AutPerm) : rho11 AutPerm le_rfl ⟨σ, hσA⟩ ∈ img11 Γ :=
  ⟨⟨σ, hσA⟩, Subgroup.mem_subgroupOf.2 hσ, rfl⟩

theorem img11_le_of_le {A B : Subgroup (Equiv.Perm (Fin 24))} (h : A ≤ B) : img11 A ≤ img11 B :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem tau1Aut_mem_Lz : tau1Aut ∈ img11 Lz := rho11_mem_img11_of_mem tau1_mem_Lz _

theorem tau2Aut_mem_Lz : tau2Aut ∈ img11 Lz := rho11_mem_img11_of_mem tau2_mem_Lz _

theorem tau1Aut_comm : tau1Aut * r0Aut = r0Aut * tau1Aut := by
  rw [tau1Aut, r0Aut, ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext tau1_comm)

theorem tau2Aut_comm : tau2Aut * r0Aut = r0Aut * tau2Aut := by
  rw [tau2Aut, r0Aut, ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext tau2_comm)

theorem r0Aut_v1 : r0Aut (toW 11 13) = toW 11 13 := by
  rw [r0Aut, rho11_toW AutPerm le_rfl ⟨r0, r0_mem_AutPerm⟩ hasArr_r0 13,
    show act11 r0Arr 13 = 13 by decide +kernel]

theorem r0Aut_v2 : r0Aut (toW 11 740) = toW 11 740 := by
  rw [r0Aut, rho11_toW AutPerm le_rfl ⟨r0, r0_mem_AutPerm⟩ hasArr_r0 740,
    show act11 r0Arr 740 = 740 by decide +kernel]

theorem tau_comm_prod :
    tau1Aut (toW 11 13) * (toW 11 13)⁻¹ * (tau2Aut (toW 11 740) * (toW 11 740)⁻¹) = z0 := by
  rw [tau1Aut, tau2Aut, rho11_toW AutPerm le_rfl ⟨tau1, Lz_le tau1_mem_Lz⟩ hasArr_tau1 13,
    rho11_toW AutPerm le_rfl ⟨tau2, Lz_le tau2_mem_Lz⟩ hasArr_tau2 740, toW11_inv, toW11_inv, ← toW_xor, ← toW_xor,
    ← toW_xor, show (act11 t1Arr 13 ^^^ 13) ^^^ (act11 t2Arr 740 ^^^ 740) = 31 by decide +kernel]

theorem img11_KSp_mul_self {k : MulAut W11} (hk : k ∈ img11 KSp) : k * k = 1 := by
  obtain ⟨σ, hσ, rfl⟩ := hk
  obtain ⟨c, hc⟩ := mem_KSp_iff.1 (Subgroup.mem_subgroupOf.1 hσ)
  rw [← map_mul]
  have h1 : σ * σ = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ← hc, ksP_mul_self]
    rfl)
  rw [h1, map_one]

theorem r0_conj_mem_KSp (σ : ↥AutPerm) (hσK : (σ : Equiv.Perm (Fin 24)) ∈ KSp) :
    r0 * (σ : Equiv.Perm (Fin 24)) * r0⁻¹ ∈ KSp := by
  have hn := Lz_le_normalizer_KSp r0_mem_Lz
  exact (mem_normalizer_iff.1 hn _).1 hσK

theorem r0_conj_mem_subgroupOf (σ : ↥AutPerm) (hc : r0 * (σ : Equiv.Perm (Fin 24)) * r0⁻¹ ∈ KSp) :
    (⟨r0, r0_mem_AutPerm⟩ * σ * ⟨r0, r0_mem_AutPerm⟩⁻¹ : ↥AutPerm) ∈ KSp.subgroupOf AutPerm :=
  Subgroup.mem_subgroupOf.2 hc

theorem rho11_r0_conj (σ : ↥AutPerm) :
    rho11 AutPerm le_rfl (⟨r0, r0_mem_AutPerm⟩ * σ * ⟨r0, r0_mem_AutPerm⟩⁻¹) =
      r0Aut * rho11 AutPerm le_rfl σ * r0Aut⁻¹ := by
  rw [map_mul, map_mul, map_inv, r0Aut]

theorem r0Aut_conj_mem {k : MulAut W11} (hk : k ∈ img11 KSp) :
    r0Aut * k * r0Aut⁻¹ ∈ img11 KSp := by
  obtain ⟨σ, hσ, rfl⟩ := hk
  have hσK : (σ : Equiv.Perm (Fin 24)) ∈ KSp := Subgroup.mem_subgroupOf.1 hσ
  exact ⟨_, r0_conj_mem_subgroupOf σ (r0_conj_mem_KSp σ hσK), rho11_r0_conj σ⟩

theorem r0Aut_pow_conj_mem (j : ℕ) {k : MulAut W11} (hk : k ∈ img11 KSp) :
    r0Aut ^ j * k * (r0Aut ^ j)⁻¹ ∈ img11 KSp := by
  induction j generalizing k with
  | zero => simpa using hk
  | succ j ih =>
    have h := r0Aut_conj_mem (ih hk)
    have e : r0Aut ^ (j + 1) * k * (r0Aut ^ (j + 1))⁻¹ =
        r0Aut * (r0Aut ^ j * k * (r0Aut ^ j)⁻¹) * r0Aut⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [e]
    exact h

theorem eq_one_of_r0Aut_pow_comm
    {j : ℕ} (hj : j = 1 ∨ j = 2) {k : MulAut W11} (hk : k ∈ img11 KSp)
    (hc : r0Aut ^ j * k * (r0Aut ^ j)⁻¹ = k) : k = 1 := by
  by_contra hk1
  apply r0Aut_fpf hk hk1
  rcases hj with rfl | rfl
  · simpa using hc
  · have h3 := r0Aut_pow_three
    calc r0Aut * k * r0Aut⁻¹ = r0Aut * (r0Aut ^ 2 * k * (r0Aut ^ 2)⁻¹) * r0Aut⁻¹ := by rw [hc]
      _ = r0Aut ^ 3 * k * (r0Aut ^ 3)⁻¹ := by group
      _ = k := by rw [h3]; group

theorem exists_conj_r0
    {σ : MulAut W11} (hσ : σ ∈ img11 KSp ⊔ zpowers r0Aut) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    ∃ g ∈ img11 KSp, ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ σ = g * r0Aut ^ j * g⁻¹ := by
  haveI : Finite (MulAut W11) :=
    Finite.of_injective (fun f : MulAut W11 => (⇑f : W11 → W11)) fun f g h => MulEquiv.ext (congrFun h)
  have hnorm : zpowers r0Aut ≤ normalizer ((img11 KSp : Subgroup (MulAut W11)) : Set _) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_fintype fun n hn => r0Aut_conj_mem hn
  have hmem : σ ∈ ((img11 KSp : Set (MulAut W11)) * (zpowers r0Aut : Set (MulAut W11))) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hσ
  obtain ⟨k, hk, r, hr, hkr⟩ := Set.mem_mul.1 hmem
  have hr' : r ∈ (Finset.range (orderOf r0Aut)).image (r0Aut ^ ·) :=
    mem_zpowers_iff_mem_range_orderOf.1 hr
  rw [orderOf_r0Aut] at hr'
  obtain ⟨j, hj, hjr⟩ := Finset.mem_image.1 hr'
  have hj3 : j < 3 := Finset.mem_range.1 hj
  have hσeq : σ = k * r0Aut ^ j := by rw [← hkr, ← hjr]
  clear hkr hjr hr hr' hmem hσ
  subst hσeq
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | hj12 | hj12
  · exfalso
    apply h1
    have hkk := img11_KSp_mul_self hk
    rw [pow_zero, mul_one] at h3 ⊢
    calc k = k ^ 3 * (k * k)⁻¹ := by group
      _ = 1 := by rw [h3, hkk]; group
  all_goals
    set K := img11 KSp
    let f : ↥K → ↥K := fun g => ⟨g * (r0Aut ^ j * g⁻¹ * (r0Aut ^ j)⁻¹),
      K.mul_mem g.2 (r0Aut_pow_conj_mem j (K.inv_mem g.2))⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have e1 : (a : MulAut W11) * (r0Aut ^ j * (a : MulAut W11)⁻¹ * (r0Aut ^ j)⁻¹) =
          b * (r0Aut ^ j * (b : MulAut W11)⁻¹ * (r0Aut ^ j)⁻¹) := congrArg Subtype.val hab
      have hm : (b : MulAut W11)⁻¹ * a ∈ K := K.mul_mem (K.inv_mem b.2) a.2
      have hc : r0Aut ^ j * ((b : MulAut W11)⁻¹ * a) * (r0Aut ^ j)⁻¹ =
          (b : MulAut W11)⁻¹ * a := by
        calc r0Aut ^ j * ((b : MulAut W11)⁻¹ * a) * (r0Aut ^ j)⁻¹
            = (b : MulAut W11)⁻¹ * ((b : MulAut W11) * (r0Aut ^ j * (b : MulAut W11)⁻¹ *
                (r0Aut ^ j)⁻¹))⁻¹⁻¹ * ((a : MulAut W11) * (r0Aut ^ j * (a : MulAut W11)⁻¹ *
                (r0Aut ^ j)⁻¹))⁻¹ * a := by group
          _ = (b : MulAut W11)⁻¹ * a := by rw [← e1]; group
      have h1' := eq_one_of_r0Aut_pow_comm (by omega) hm hc
      exact Subtype.ext (inv_mul_eq_one.1 h1').symm
    obtain ⟨g, hg⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨k, hk⟩
    have hgk : (g : MulAut W11) * (r0Aut ^ j * (g : MulAut W11)⁻¹ * (r0Aut ^ j)⁻¹) = k :=
      congrArg Subtype.val hg
    refine ⟨g, g.2, j, by omega, ?_⟩
    rw [← hgk]
    group

theorem fix_z0_of_mem_KSp {g : MulAut W11} (hg : g ∈ img11 KSp) : g z0 = z0 :=
  mem_centSub_zpowers.1 (img11_Lz_le_centSub (img11_le_of_le KSp_le_Lz hg))

theorem exists_comm_witness
    {σ : MulAut W11}
    (hσ : σ ∈ CFSG.EvenSporadicStandard.TwoFi22.O23In
      (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)))
    (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    ∃ τ₁ ∈ img11 AutPerm, ∃ τ₂ ∈ img11 AutPerm, ∃ v₁ v₂ : W11,
      τ₁ * σ = σ * τ₁ ∧ τ₂ * σ = σ * τ₂ ∧ τ₁ z0 = z0 ∧ τ₂ z0 = z0 ∧ σ v₁ = v₁ ∧ σ v₂ = v₂ ∧
      τ₁ v₁ * v₁⁻¹ * (τ₂ v₂ * v₂⁻¹) = z0 := by
  have hσ' : σ ∈ img11 KSp ⊔ zpowers r0Aut := (Subgroup.ext_iff.1 O23In_Sz_eq σ).1 hσ
  obtain ⟨g, hg, j, -, rfl⟩ := exists_conj_r0 hσ' h3 h1
  have hgA : g ∈ img11 AutPerm := img11_le_of_le (KSp_le_Lz.trans Lz_le) hg
  have hgz : g z0 = z0 := fix_z0_of_mem_KSp hg
  have hgz' : g⁻¹ z0 = z0 := by
    conv_lhs => rw [← hgz]
    exact MulAut.inv_apply_self _ _ z0
  have hτ1 : tau1Aut ∈ img11 AutPerm := img11_le_of_le Lz_le tau1Aut_mem_Lz
  have hτ2 : tau2Aut ∈ img11 AutPerm := img11_le_of_le Lz_le tau2Aut_mem_Lz
  have hz1 : tau1Aut z0 = z0 := mem_centSub_zpowers.1 (img11_Lz_le_centSub tau1Aut_mem_Lz)
  have hz2 : tau2Aut z0 = z0 := mem_centSub_zpowers.1 (img11_Lz_le_centSub tau2Aut_mem_Lz)
  have hc1 : tau1Aut * r0Aut ^ j = r0Aut ^ j * tau1Aut := ((Commute.pow_right tau1Aut_comm j)).eq
  have hc2 : tau2Aut * r0Aut ^ j = r0Aut ^ j * tau2Aut := ((Commute.pow_right tau2Aut_comm j)).eq
  have hfix : ∀ (v : W11), r0Aut v = v → ∀ n : ℕ, (r0Aut ^ n) v = v := by
    intro v hv n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hv]
  have hv1 := hfix _ r0Aut_v1 j
  have hv2 := hfix _ r0Aut_v2 j
  refine ⟨g * tau1Aut * g⁻¹, mul_mem (mul_mem hgA hτ1) (inv_mem hgA),
    g * tau2Aut * g⁻¹, mul_mem (mul_mem hgA hτ2) (inv_mem hgA), g (toW 11 13), g (toW 11 740),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc g * tau1Aut * g⁻¹ * (g * r0Aut ^ j * g⁻¹) = g * (tau1Aut * r0Aut ^ j) * g⁻¹ := by group
      _ = g * (r0Aut ^ j * tau1Aut) * g⁻¹ := by rw [hc1]
      _ = g * r0Aut ^ j * g⁻¹ * (g * tau1Aut * g⁻¹) := by group
  · calc g * tau2Aut * g⁻¹ * (g * r0Aut ^ j * g⁻¹) = g * (tau2Aut * r0Aut ^ j) * g⁻¹ := by group
      _ = g * (r0Aut ^ j * tau2Aut) * g⁻¹ := by rw [hc2]
      _ = g * r0Aut ^ j * g⁻¹ * (g * tau2Aut * g⁻¹) := by group
  · rw [MulAut.mul_apply, MulAut.mul_apply, hgz', hz1, hgz]
  · rw [MulAut.mul_apply, MulAut.mul_apply, hgz', hz2, hgz]
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hv1]
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hv2]
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, MulAut.mul_apply,
      MulAut.mul_apply, MulAut.inv_apply_self, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul, tau_comm_prod, hgz]

theorem exists_equiv_std {V : Type*} [CommGroup V]
    {L : Subgroup (MulAut V)} {e : V ≃* W11}
    (he : L.map (CFSG.Quasithin.H.congrHom e) = img11 AutPerm) {x : V} (hx : x ≠ 1)
    (horb : Nat.card ↥(MulAction.orbit ↥L x) = 1771) :
    ∃ e' : V ≃* W11, L.map (CFSG.Quasithin.H.congrHom e') = img11 AutPerm ∧ e' x = z0 := by
  open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch in
  have hcard : Nat.card ↥(MulAction.orbit ↥(img11 AutPerm) (e x)) = 1771 := by
    rw [← he, card_orbit_map_congrHom, horb]
  have hex : e x ∈ MulAction.orbit ↥(img11 AutPerm) z0 := by
    open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair in
    rw [orbit_eq]
    refine ⟨fun h => hx (e.injective (h.trans (map_one e).symm)), fun hD => ?_⟩
    have hsub : MulAction.orbit ↥(img11 AutPerm) (e x) ⊆ Duad := by
      rintro _ ⟨g, rfl⟩
      exact apply_mem_Duad g.2 hD
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_Duad, ← Nat.card_coe_set_eq, hcard] at hle
    omega
  obtain ⟨g, hg⟩ := hex
  have hgi : ((g⁻¹ : ↥(img11 AutPerm)) : MulAut W11) (e x) = z0 := by
    rw [← hg]
    exact inv_smul_smul g z0
  refine ⟨e.trans ((g⁻¹ : ↥(img11 AutPerm)) : MulAut W11), ?_, hgi⟩
  exact CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.map_congrHom_trans_of_mem he
    (g⁻¹ : ↥(img11 AutPerm)).2

end CFSG.Quasithin.H13.AS91.Nine
