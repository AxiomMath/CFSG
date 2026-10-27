module

public import CFSG.Quasithin.H13.U3SixUnique
public import CFSG.Quasithin.H13.U3Basic
public import Certificates.Certificate17004
public import Certificates.Certificate16950
public import CFSG.Sporadic.Schreier.J4SSylowBase


public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

section General

variable {G : Type*} [Group G]

theorem relIndex_sup_eq_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm

theorem card_sup_zpowers_of_involution [Finite G] {H : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (H : Set G)) (hd2 : d * d = 1) (hdH : d ∉ H) :
    Nat.card (Subgroup.zpowers d ⊔ H : Subgroup G) = Nat.card H * 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd1 : d ≠ 1 := fun h => hdH (h ▸ H.one_mem)
  have hord : orderOf d = 2 := orderOf_eq_prime (by rw [pow_two, hd2]) hd1
  have hZ : Nat.card (Subgroup.zpowers d) = 2 := by rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers d ≤ Subgroup.normalizer (H : Set G) := Subgroup.zpowers_le.2 hd
  have hinf : H ⊓ Subgroup.zpowers d = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxH, hxd⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxd
    have hk : d ^ k = d ^ (k % 2) := by
      rw [← zpow_mod_orderOf, hord]
      norm_num
    rw [hk] at hxH ⊢
    have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk2 with h | h
    · rw [h, zpow_zero]
    · rw [h, zpow_one] at hxH
      exact absurd hxH hdH
  have h1 := Subgroup.relIndex_mul_card H (Subgroup.zpowers d)
  rw [hinf, Subgroup.card_bot, mul_one, hZ] at h1
  rw [← card_mul_relIndex (le_sup_right : H ≤ Subgroup.zpowers d ⊔ H),
    relIndex_sup_eq_of_le_normalizer hle, h1]

end General

noncomputable abbrev J6 : Subgroup (GL (Fin 6) (ZMod 2)) := rho6.range

theorem card_J6
    : Nat.card J6 = 6048 := by
  rw [← card_u33G]
  exact Nat.card_congr (MonoidHom.ofInjective rho6_injective).toEquiv.symm

theorem coe_rho6_wordElem (w : List (Fin 5)) :
    ((rho6 (wordElem w) : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      colMat (wordMat w) := by
  induction w with
  | nil => simp [wordElem, wordMat, colMat_id6]
  | cons i w ih =>
    rw [wordElem, List.map_cons, List.prod_cons, map_mul, Units.val_mul, rho6_gen]
    change colMat (u6c i) * ((rho6 (wordElem w) : GL (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)) = _
    rw [ih]
    simp only [wordMat, List.map_cons, List.foldr_cons, colMat_mul6]

theorem mem_list_of_closure {G : Type*} [Group G] [Finite G]
    (f : G →* Matrix (Fin 6) (Fin 6) (ZMod 2)) {S : Set G} {gens : List (List ℕ)}
    (hS : ∀ g ∈ S, ∃ c ∈ gens, f g = colMat c) {es : List (List ℕ)} (h1 : id6 ∈ es)
    (hcl : ∀ e ∈ es, ∀ c ∈ gens, mul6 e c ∈ es) :
    ∀ g ∈ Subgroup.closure S, ∃ e ∈ es, f g = colMat e := by
  intro g hg
  have hg' : g ∈ Submonoid.closure S := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hg
  clear hg
  induction hg' using Submonoid.closure_induction_right with
  | one => exact ⟨id6, h1, by rw [map_one, colMat_id6]⟩
  | mul_right x _ z hz ih =>
    obtain ⟨e, he, hfe⟩ := ih
    obtain ⟨c, hc, hfc⟩ := hS z hz
    exact ⟨mul6 e c, hcl e he c hc, by rw [map_mul, hfe, hfc, colMat_mul6]⟩

theorem tc_closed : id6 ∈ tc ∧ ∀ e ∈ tc, ∀ c ∈ [u6c 0, u6c 1, u6c 2], mul6 e c ∈ tc :=
  Certificates.certificate17004.1

noncomputable abbrev rhoT
    : Subgroup (GL (Fin 6) (ZMod 2)) := u33Data.T.map rho6

theorem card_rhoT
    : Nat.card rhoT = 32 := by
  rw [Subgroup.card_map_of_injective rho6_injective, u33_card_T]

theorem mem_tc_of_mem_T
    (t : U33G) (ht : t ∈ u33Data.T) :
    ∃ e ∈ tc, ((rho6 t : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e := by
  refine mem_list_of_closure ((Units.coeHom _).comp rho6) (gens := [u6c 0, u6c 1, u6c 2]) ?_
    tc_closed.1 tc_closed.2 t ht
  rintro g (rfl | rfl | rfl)
  · exact ⟨u6c 0, by simp, by rw [MonoidHom.comp_apply, rho6_abs.1]; rfl⟩
  · exact ⟨u6c 1, by simp, by rw [MonoidHom.comp_apply, rho6_abs.2.1]; rfl⟩
  · exact ⟨u6c 2, by simp, by rw [MonoidHom.comp_apply, rho6_abs.2.2.1]; rfl⟩

theorem dc_mul_self : mul6 dc dc = id6 :=
  Certificates.certificate17004.2.1

@[expose] def dGL : GL (Fin 6) (ZMod 2) :=
  ⟨colMat dc, colMat dc, by rw [← colMat_mul6, dc_mul_self, colMat_id6],
    by rw [← colMat_mul6, dc_mul_self, colMat_id6]⟩

theorem dGL_inv : dGL⁻¹ = dGL :=
  Units.ext rfl

theorem dGL_mul_self : dGL * dGL = 1 := by
  apply Units.ext
  rw [Units.val_mul]
  change colMat dc * colMat dc = 1
  rw [← colMat_mul6, dc_mul_self, colMat_id6]

theorem dc_conj : ∀ i : Fin 5, mul6 (mul6 dc (u6c i)) dc = wordMat (dWords i) :=
  Certificates.certificate17004.2.2.1

theorem dGL_conj
    (i : Fin 5) : dGL * rho6 (u33GenPG i) * dGL⁻¹ = rho6 (wordElem (dWords i)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, rho6_gen, dGL_inv, coe_rho6_wordElem, ← dc_conj i,
    colMat_mul6, colMat_mul6]
  rfl

theorem dGL_conj_mem_J6
    (g : U33G) : dGL * rho6 g * dGL⁻¹ ∈ J6 := by
  let φ : U33G →* GL (Fin 6) (ZMod 2) := (MulAut.conj dGL).toMonoidHom.comp rho6
  have hφ : ∀ g, φ g = dGL * rho6 g * dGL⁻¹ := fun _ => rfl
  have hle : Subgroup.closure ({u33Data.a, u33Data.b, u33Data.s, u33Data.x, u33Data.y} :
      Set U33G) ≤ J6.comap φ := by
    rw [Subgroup.closure_le]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
    rcases hh with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, (dGL_conj 0).symm⟩
    · exact ⟨_, (dGL_conj 1).symm⟩
    · exact ⟨_, (dGL_conj 2).symm⟩
    · exact ⟨_, (dGL_conj 3).symm⟩
    · exact ⟨_, (dGL_conj 4).symm⟩
  rw [u33Data.gen] at hle
  exact hle (Subgroup.mem_top g)

theorem dGL_mem_normalizer_J6
    : dGL ∈ Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨g, rfl⟩
    exact dGL_conj_mem_J6 g
  · intro hh
    obtain ⟨g, hg⟩ := hh
    have h1 := dGL_conj_mem_J6 g
    rw [hg, dGL_inv, ← mul_assoc, ← mul_assoc, dGL_mul_self, one_mul, mul_assoc, dGL_mul_self,
      mul_one] at h1
    exact h1

theorem dGL_mem_normalizer_rhoT
    : dGL ∈ Subgroup.normalizer (rhoT : Set (GL (Fin 6) (ZMod 2))) := by
  have hconj : ∀ t ∈ u33Data.T, dGL * rho6 t * dGL⁻¹ ∈ rhoT := by
    intro t ht
    let φ : U33G →* GL (Fin 6) (ZMod 2) := (MulAut.conj dGL).toMonoidHom.comp rho6
    have hφ : ∀ g, φ g = dGL * rho6 g * dGL⁻¹ := fun _ => rfl
    have hle : u33Data.T ≤ rhoT.comap φ := by
      refine (Subgroup.closure_le _).2 ?_
      intro h hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
      have hmem : ∀ w : List (Fin 5), (∀ k ∈ w, k ∈ ([0, 1, 2] : List (Fin 5))) →
          wordElem w ∈ u33Data.T := by
        intro w hw'
        refine list_prod_mem fun x hx => ?_
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        have := hw' k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl
        · exact u33Data.a_mem_T
        · exact u33Data.b_mem_T
        · exact u33Data.s_mem_T
      rcases hh with rfl | rfl | rfl
      · rw [show dGL * rho6 u33Data.a * dGL⁻¹ = rho6 (wordElem (dWords 0)) from dGL_conj 0]
        exact ⟨_, hmem _ (by decide), rfl⟩
      · rw [show dGL * rho6 u33Data.b * dGL⁻¹ = rho6 (wordElem (dWords 1)) from dGL_conj 1]
        exact ⟨_, hmem _ (by decide), rfl⟩
      · rw [show dGL * rho6 u33Data.s * dGL⁻¹ = rho6 (wordElem (dWords 2)) from dGL_conj 2]
        exact ⟨_, hmem _ (by decide), rfl⟩
    exact hle ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact hconj t ht
  · intro hh
    obtain ⟨t, ht, hth⟩ := hh
    have h1 := hconj t ht
    rw [hth, dGL_inv, ← mul_assoc, ← mul_assoc, dGL_mul_self, one_mul, mul_assoc, dGL_mul_self,
      mul_one] at h1
    exact h1

theorem dc_not_mem_tc : dc ∉ tc :=
  Certificates.certificate17004.2.2.2.1

theorem dGL_not_mem_rhoT
    : dGL ∉ rhoT := by
  rintro ⟨t, ht, hdt⟩
  obtain ⟨e, he, hte⟩ := mem_tc_of_mem_T t ht
  rw [hdt] at hte
  have hcan : ∀ e ∈ tc, canon6 e = true := Certificates.certificate16950
  have h1 : dc = e := colMat_injective (by decide) (hcan e he) hte
  exact dc_not_mem_tc (h1 ▸ he)

noncomputable abbrev S0
    : Subgroup (GL (Fin 6) (ZMod 2)) := Subgroup.zpowers dGL ⊔ rhoT

theorem card_S0
    : Nat.card S0 = 64 := by
  rw [card_sup_zpowers_of_involution dGL_mem_normalizer_rhoT dGL_mul_self dGL_not_mem_rhoT,
    card_rhoT]

theorem rhoT_le_J6 :
    rhoT ≤ J6 := by
  rintro _ ⟨t, -, rfl⟩
  exact ⟨t, rfl⟩

theorem dGL_not_mem_J6
    : dGL ∉ J6 := by
  intro hd
  have hle : S0 ≤ J6 := sup_le (Subgroup.zpowers_le.2 hd) rhoT_le_J6
  have h := Subgroup.card_dvd_of_le hle
  rw [card_S0, card_J6] at h
  norm_num at h

theorem fixed_abs_only : ∀ c < 64, vapp (u6c 0) c = c → vapp (u6c 1) c = c → vapp (u6c 2) c = c →
    c = 0 ∨ c = 15 :=
  Certificates.certificate17004.2.2.2.2

theorem eq_one_of_commute_J6
    {g : GL (Fin 6) (ZMod 2)} (hg : ∀ h ∈ J6, h * g = g * h) : g = 1 := by
  set M := (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hM
  have hcomm : ∀ (h : U33G) (v : W6), (rho6 h : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ (M *ᵥ v) =
      M *ᵥ ((rho6 h : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) := by
    intro h v
    have h1 := congrArg Units.val (hg (rho6 h) ⟨h, rfl⟩)
    rw [Units.val_mul, Units.val_mul, ← hM] at h1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1]
  obtain ⟨c, hc, hcv⟩ := exists_vecOf (M *ᵥ vecOf 15)
  have hgen : ∀ i : Fin 5, i ≠ 4 → vapp (u6c i) c = c := by
    intro i hi4
    have h1 := hcomm (u33GenPG i) (vecOf 15)
    rw [rho6_gen] at h1
    change colMat (u6c i) *ᵥ (M *ᵥ vecOf 15) = M *ᵥ (colMat (u6c i) *ᵥ vecOf 15) at h1
    rw [colMat_mulVec_vecOf (u6c i) 15, ← hcv, colMat_mulVec_vecOf] at h1
    rw [u6c_w0 i hi4, ← hcv] at h1
    exact vecOf_injective (vapp_u6c_lt i c) hc h1
  have hc15 : c = 15 := by
    rcases fixed_abs_only c hc (hgen 0 (by decide)) (hgen 1 (by decide)) (hgen 2 (by decide))
      with h0 | h15
    · exfalso
      rw [h0, vecOf_zero] at hcv
      have h1 : (g⁻¹ : GL (Fin 6) (ZMod 2)) *ᵥ (M *ᵥ vecOf 15) = vecOf 15 := by
        rw [Matrix.mulVec_mulVec, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [← hcv, Matrix.mulVec_zero] at h1
      have h2 : vecOf 15 = vecOf 0 := by rw [vecOf_zero]; exact h1.symm
      exact absurd (vecOf_injective (by norm_num) (by norm_num) h2) (by norm_num)
    · exact h15
  rw [hc15] at hcv
  have hfixall : ∀ v : W6, M *ᵥ v = v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, Matrix.mulVec_zero]
    · have hv1 : Multiplicative.ofAdd v ≠ 1 := fun h => hv (congrArg Multiplicative.toAdd h)
      obtain ⟨h, hh⟩ := psiW_transitive _ hv1
      rw [w0, psiW_apply] at hh
      have hv' : v = (rho6 h : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ vecOf 15 :=
        (congrArg Multiplicative.toAdd hh).symm
      rw [hv', ← hcomm, ← hcv]
  apply Units.ext
  rw [Units.val_one, ← hM]
  ext i j
  have h1 := hfixall (Pi.single j 1)
  rw [Matrix.mulVec_single_one] at h1
  have h2 := congrFun h1 i
  simp only [Matrix.col_apply] at h2
  rw [h2, Matrix.one_apply]
  simp only [Pi.single_apply]

theorem card_normalizer_J6_le :
    Nat.card (Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2)))) ≤ 12096 := by
  set N := Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2)))
  have hinj : Function.Injective J6.normalizerMonoidHom := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_commute_J6 hn)
  have : Finite (MulAut J6) := Finite.of_injective (fun f : MulAut J6 => (f : J6 → J6))
    fun f g h => MulEquiv.ext (congrFun h)
  calc Nat.card N ≤ Nat.card (MulAut J6) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (MulAut U33G) :=
        Nat.card_congr (MulAut.congr (MonoidHom.ofInjective rho6_injective).symm).toEquiv
    _ ≤ 12096 := card_mulAut_u33Pres_le

noncomputable abbrev N6
    : Subgroup (GL (Fin 6) (ZMod 2)) := Subgroup.zpowers dGL ⊔ J6

theorem card_N6
    : Nat.card N6 = 12096 := by
  rw [card_sup_zpowers_of_involution dGL_mem_normalizer_J6 dGL_mul_self dGL_not_mem_J6, card_J6]

theorem normalizer_J6_eq
    : Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) = N6 := by
  have hle : N6 ≤ Subgroup.normalizer (J6 : Set (GL (Fin 6) (ZMod 2))) :=
    sup_le (Subgroup.zpowers_le.2 dGL_mem_normalizer_J6) Subgroup.le_normalizer
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_N6]; exact card_normalizer_J6_le)).symm

theorem S0_le_N6 :
    S0 ≤ N6 :=
  sup_le le_sup_left (rhoT_le_J6.trans le_sup_right)

end CFSG.Quasithin.H13.U3
