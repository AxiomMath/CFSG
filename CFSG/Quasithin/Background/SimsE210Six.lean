module

import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.RonanE211Six
public import CFSG.Quasithin.Vol2.E2NinePullback
public import CFSG.Quasithin.Vol2.E2TenSevenPair
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SimsE210

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6
  CFSG.Quasithin.Ch3E213M CFSG.Quasithin.Ch3E213M.P6E CFSG.Quasithin.RonanE27
  CFSG.Quasithin.RonanE211 CFSG.Quasithin.E2

open scoped commutatorElement

namespace Six

theorem comm_of_involutions_central {Q : Type*} [Group Q] {L V₀ T₀ : Subgroup Q} [L.Normal]
    (hL : ∀ x ∈ L, x * x = 1 → ∀ y ∈ L, x * y = y * x)
    (hV₀ : ∀ v ∈ V₀, v * v = 1) (hT : T₀ ≤ Subgroup.normalizer (V₀ : Set Q))
    (hVZ : ∀ v ∈ V₀, v ∈ L → (∀ y ∈ L, v * y = y * v) → v = 1) :
    ∀ v ∈ V₀, ∀ t ∈ T₀ ⊓ L, v * t = t * v := by
  intro v hv t ht
  have hc : v * t * v⁻¹ * t⁻¹ ∈ V₀ := by
    have h1 : t * v⁻¹ * t⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 (hT ht.1) v⁻¹).1 (V₀.inv_mem hv)
    have := V₀.mul_mem hv h1
    simpa [mul_assoc] using this
  have hcL : v * t * v⁻¹ * t⁻¹ ∈ L :=
    L.mul_mem (‹L.Normal›.conj_mem t ht.2 v) (L.inv_mem ht.2)
  have h1 := hVZ _ hc hcL (hL _ hcL (hV₀ _ hc))
  have h2 : v * t * v⁻¹ = t := mul_inv_eq_one.1 h1
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

section Generic

variable {Q R : Type*} [Group Q] [Group R]

theorem nonempty_equiv_map_of_inf_ker (f : Q →* R) (N : Subgroup Q) (h : N ⊓ f.ker = ⊥) :
    Nonempty (↥N ≃* ↥(N.map f)) := by
  refine ⟨MulEquiv.ofBijective (f.subgroupMap N) ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_,
    f.subgroupMap_surjective N⟩⟩
  have hx1 : f (x : Q) = 1 := congrArg Subtype.val hx
  have : (x : Q) ∈ N ⊓ f.ker := ⟨x.2, hx1⟩
  rw [h, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem nonempty_equiv_of_compl (f : Q →* R) (hf : Function.Surjective f) (Y₀ : Subgroup Q)
    (hinf : Y₀ ⊓ f.ker = ⊥) (hsup : Y₀ ⊔ f.ker = ⊤) : Nonempty (↥Y₀ ≃* R) := by
  refine ⟨MulEquiv.ofBijective (f.comp Y₀.subtype) ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_,
    fun r => ?_⟩⟩
  · have hx1 : f (x : Q) = 1 := hx
    have : (x : Q) ∈ Y₀ ⊓ f.ker := ⟨x.2, hx1⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subtype.ext this
  · obtain ⟨x, rfl⟩ := hf r
    have hx : x ∈ Y₀ ⊔ f.ker := hsup ▸ Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    refine ⟨⟨y, hy⟩, ?_⟩
    show f y = f (y * z)
    rw [map_mul, MonoidHom.mem_ker.1 hz, mul_one]

theorem nonempty_commutator_equiv (f : Q →* R) (hf : Function.Surjective f)
    (h : commutator Q ⊓ f.ker = ⊥) : Nonempty (↥(commutator Q) ≃* ↥(commutator R)) := by
  obtain ⟨e⟩ := nonempty_equiv_map_of_inf_ker f (commutator Q) h
  refine ⟨e.trans (MulEquiv.subgroupCongr ?_)⟩
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective f hf]

theorem mem_commutator_subgroup_iff (H : Subgroup Q) {x : Q} :
    x ∈ ⁅H, H⁆ ↔ ∃ y : H, y ∈ commutator ↥H ∧ (y : Q) = x := by
  rw [← Subgroup.map_subtype_commutator]
  exact Subgroup.mem_map

end Generic

theorem sign_eq_neg_one_of_not_mem_alt {a : P6} (ha : a ∉ alternatingGroup (Fin 6)) :
    Perm.sign a = -1 := by
  rw [Perm.mem_alternatingGroup] at ha
  rcases Int.units_eq_one_or (Perm.sign a) with h | h
  · exact absurd h ha
  · exact h

theorem mul_mem_alt {a b : P6} (ha : a ∉ alternatingGroup (Fin 6))
    (hb : b ∉ alternatingGroup (Fin 6)) : a * b ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, map_mul, sign_eq_neg_one_of_not_mem_alt ha,
    sign_eq_neg_one_of_not_mem_alt hb]
  decide

theorem inv_mul_mem_alt {a b : P6} (ha : a ∉ alternatingGroup (Fin 6))
    (hb : b ∉ alternatingGroup (Fin 6)) : a⁻¹ * b ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, map_mul, map_inv, sign_eq_neg_one_of_not_mem_alt ha,
    sign_eq_neg_one_of_not_mem_alt hb]
  decide

theorem zB_mem_Z6 : zB ∈ Z6 := zB_mem_extZ

theorem mem_Z6_of_comm {y : P6} (hy : y ∈ S06) (hr : y * rD = rD * y) (hs : y * sD = sD * y) :
    y = 1 ∨ y = zA ∨ y = zB ∨ y = zA * zB :=
  chk_zcent y (mem_S06_iff.1 hy) hr hs (Z6_comm zB_mem_Z6 hy).symm

section Q1

variable {Q : Type} [Group Q] [Finite Q]

abbrev q1 (ρ : Q →* P6) : Subgroup Q := (alternatingGroup (Fin 6)).comap ρ

theorem mem_q1 {ρ : Q →* P6} {x : Q} : x ∈ q1 ρ ↔ ρ x ∈ alternatingGroup (Fin 6) := Iff.rfl

theorem lam_sup_ker (ρ : Q →* P6) (hρs : Function.Surjective ρ) :
    ⁅q1 ρ, q1 ρ⁆ ⊔ ρ.ker = q1 ρ := by
  apply le_antisymm
  · refine sup_le (Subgroup.commutator_le_left _ _) fun x hx => ?_
    rw [mem_q1, MonoidHom.mem_ker.1 hx]
    exact one_mem _
  · intro x hx
    have hmap : ⁅q1 ρ, q1 ρ⁆.map ρ = alternatingGroup (Fin 6) := by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hρs,
        commutator_alternatingGroup_eq_self (by simp)]
    have h1 : ρ x ∈ ⁅q1 ρ, q1 ρ⁆.map ρ := by rw [hmap]; exact hx
    obtain ⟨l, hl, hlx⟩ := h1
    have h2 : l⁻¹ * x ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]
    have hx' : x = l * (l⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem_sup hl h2

theorem ker_comp_q1 (J₀ : Subgroup Q) (ρ : Q →* P6) (hρk : ρ.ker = J₀) :
    (ρ.comp (q1 ρ).subtype).ker = J₀.subgroupOf (q1 ρ) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hρk, MonoidHom.mem_ker]
  rfl

theorem range_comp_q1 (ρ : Q →* P6) (hρs : Function.Surjective ρ) :
    (ρ.comp (q1 ρ).subtype).range = alternatingGroup (Fin 6) := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro ha
    obtain ⟨x, rfl⟩ := hρs a
    exact ⟨⟨x, ha⟩, rfl⟩

theorem subgroupOf_q1_le_center (J₀ : Subgroup Q) (ρ : Q →* P6) (hJc : J₀ ≤ Subgroup.center Q) :
    J₀.subgroupOf (q1 ρ) ≤ Subgroup.center ↥(q1 ρ) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hJc (Subgroup.mem_subgroupOf.1 hx)) g)

theorem le_q1 (J₀ : Subgroup Q) (ρ : Q →* P6) (hρk : ρ.ker = J₀) : J₀ ≤ q1 ρ := fun j hj => by
  rw [mem_q1, MonoidHom.mem_ker.1 (hρk ▸ hj)]
  exact one_mem _

theorem isPGroup_subgroupOf_q1 (J₀ : Subgroup Q) (ρ : Q →* P6) (hρk : ρ.ker = J₀)
    (hJ2 : IsPGroup 2 J₀) : IsPGroup 2 ↥(J₀.subgroupOf (q1 ρ)) :=
  hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe (le_q1 J₀ ρ hρk)).symm

end Q1

section A6

variable {Q : Type} [Group Q] [Finite Q]

theorem involutions_central_of_alt_six (hKG : KGI22One) (J₀ : Subgroup Q) [J₀.Normal]
    (hJc : J₀ ≤ Subgroup.center Q) (hJ2 : IsPGroup 2 J₀) (ρ : Q →* P6) (hρk : ρ.ker = J₀)
    (hρr : ρ.range = alternatingGroup (Fin 6)) (hne : Subgroup.center (commutator Q) ≠ ⊥) :
    ∀ y ∈ commutator Q, y * y = 1 → ∀ w ∈ commutator Q, y * w = w * y := by
  have hsimp : IsSimpleGroup (Q ⧸ J₀) := altSix_simple J₀ ρ hρk hρr
  have hS : commutator (Q ⧸ J₀) = ⊤ := altSix_perfect J₀ ρ hρk hρr
  have hna : ∃ a b : Q ⧸ J₀, a * b ≠ b * a := altSix_nonabelian J₀ ρ hρk hρr
  obtain ⟨hLq, ⟨eL⟩⟩ := quasisimple_commutator J₀ hJc hS hsimp hna
  have hZ := map_center_commutator_eq J₀ hJc hS hsimp hna
  have hZ2 : IsPGroup 2 (Subgroup.center (commutator Q)) := by
    intro z
    have hzJ : ((z : commutator Q) : Q) ∈ J₀ := by
      have : ((z : commutator Q) : Q) ∈
          (Subgroup.center (commutator Q)).map (commutator Q).subtype := ⟨z, z.2, rfl⟩
      rw [hZ] at this
      exact this.2
    obtain ⟨k, hk⟩ := hJ2 ⟨_, hzJ⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun x : J₀ => (x : Q)) hk
    simpa using this
  obtain ⟨eS⟩ := (hKG (commutator Q) hLq hne hZ2).2
    ⟨eL.trans (altSixEquiv J₀ ρ hρk hρr)⟩
  have h2 : (2 : GaloisField 3 2) ≠ 0 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    intro h
    have h3 : ((2 : ℕ) : GaloisField 3 2) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField 3 2) 3] at h3
    omega
  intro y hy hyy w hw
  have hmul : eS ⟨y, hy⟩ * eS ⟨y, hy⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hy⟩ : commutator Q) * ⟨y, hy⟩ = 1 := Subtype.ext hyy
    rw [this, map_one]
  have hcomm : (⟨y, hy⟩ : commutator Q) * ⟨w, hw⟩ = ⟨w, hw⟩ * ⟨y, hy⟩ := by
    apply eS.injective
    rw [map_mul, map_mul]
    rcases sl2_eq_one_or_neg_one_of_mul_self h2 hmul with h | h
    · rw [h, one_mul, mul_one]
    · rw [h, neg_mul, mul_neg, one_mul, mul_one]
  exact congrArg Subtype.val hcomm

end A6

section Lam

variable {Q : Type} [Group Q] [Finite Q] (J₀ : Subgroup Q) [J₀.Normal] (ρ : Q →* P6)

theorem lam_center_imp (hJc : J₀ ≤ Subgroup.center Q) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = J₀) {x : Q} (hx : x ∈ ⁅q1 ρ, q1 ρ⁆)
    (hc : ∀ w ∈ ⁅q1 ρ, q1 ρ⁆, x * w = w * x) : x ∈ J₀ := by
  haveI : (J₀.subgroupOf (q1 ρ)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  have hρ₁k := ker_comp_q1 J₀ ρ hρk
  have hρ₁r := range_comp_q1 ρ hρs
  have hZ := map_center_commutator_eq (J₀.subgroupOf (q1 ρ)) (subgroupOf_q1_le_center J₀ ρ hJc)
    (altSix_perfect _ _ hρ₁k hρ₁r) (altSix_simple _ _ hρ₁k hρ₁r)
    (altSix_nonabelian _ _ hρ₁k hρ₁r)
  obtain ⟨y, hy, rfl⟩ := (mem_commutator_subgroup_iff (q1 ρ)).1 hx
  have hyZ : y ∈ (Subgroup.center (commutator ↥(q1 ρ))).map (commutator ↥(q1 ρ)).subtype := by
    refine ⟨⟨y, hy⟩, Subgroup.mem_center_iff.2 fun w => ?_, rfl⟩
    refine Subtype.ext (Subtype.ext ?_)
    exact (hc ((w : ↥(q1 ρ)) : Q)
      ((mem_commutator_subgroup_iff (q1 ρ)).2 ⟨w, w.2, rfl⟩)).symm
  rw [hZ] at hyZ
  exact hyZ.2

theorem lam_inf_eq_bot_of_center (hJc : J₀ ≤ Subgroup.center Q)
    (hcen : Subgroup.center (commutator ↥(q1 ρ)) = ⊥) : ⁅q1 ρ, q1 ρ⁆ ⊓ J₀ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxΛ, hxJ⟩
  obtain ⟨y, hy, rfl⟩ := (mem_commutator_subgroup_iff (q1 ρ)).1 hxΛ
  have hmem : (⟨y, hy⟩ : commutator ↥(q1 ρ)) ∈ Subgroup.center (commutator ↥(q1 ρ)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.1 (hJc hxJ) _))
  rw [hcen, Subgroup.mem_bot] at hmem
  have := congrArg (fun z : commutator ↥(q1 ρ) => ((z : ↥(q1 ρ)) : Q)) hmem
  exact Subgroup.mem_bot.2 this

theorem lam_involutions_central (hKG : KGI22One) (hJc : J₀ ≤ Subgroup.center Q)
    (hJ2 : IsPGroup 2 J₀) (hρs : Function.Surjective ρ) (hρk : ρ.ker = J₀)
    (hcen : Subgroup.center (commutator ↥(q1 ρ)) ≠ ⊥) :
    ∀ x ∈ ⁅q1 ρ, q1 ρ⁆, x * x = 1 → ∀ w ∈ ⁅q1 ρ, q1 ρ⁆, x * w = w * x := by
  haveI : (J₀.subgroupOf (q1 ρ)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  have key := involutions_central_of_alt_six hKG (J₀.subgroupOf (q1 ρ))
    (subgroupOf_q1_le_center J₀ ρ hJc) (isPGroup_subgroupOf_q1 J₀ ρ hρk hJ2)
    (ρ.comp (q1 ρ).subtype) (ker_comp_q1 J₀ ρ hρk) (range_comp_q1 ρ hρs) hcen
  intro x hx hxx w hw
  obtain ⟨y, hy, rfl⟩ := (mem_commutator_subgroup_iff (q1 ρ)).1 hx
  obtain ⟨w', hw', rfl⟩ := (mem_commutator_subgroup_iff (q1 ρ)).1 hw
  have := key y hy (Subtype.ext hxx) w' hw'
  exact congrArg Subtype.val this

end Lam

section Core

variable {Q : Type} [Group Q] [Finite Q]

theorem closure_involutions_eq_top {V₀ : Subgroup Q} (hV₀ : ∀ v ∈ V₀, v * v = 1) {q : Q}
    (hgen : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤) :
    Subgroup.closure {x : Q | x * x = 1} = ⊤ := by
  rw [eq_top_iff, ← hgen, sup_le_iff]
  constructor
  · exact fun x hx => Subgroup.subset_closure (hV₀ x hx)
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.subset_closure ?_
    show q * x * q⁻¹ * (q * x * q⁻¹) = 1
    have := hV₀ x hx
    calc q * x * q⁻¹ * (q * x * q⁻¹) = q * (x * x) * q⁻¹ := by group
      _ = 1 := by rw [this]; group

theorem map_gen {V₀ : Subgroup Q} {ρ : Q →* P6} (hρs : Function.Surjective ρ) {q : Q}
    (hgen : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤) :
    V₀.map ρ ⊔ (V₀.map ρ).map (MulAut.conj (ρ q)).toMonoidHom = ⊤ := by
  have h1 := congrArg (Subgroup.map ρ) hgen
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ hρs] at h1
  have h2 : (V₀.map (MulAut.conj q).toMonoidHom).map ρ =
      (V₀.map ρ).map (MulAut.conj (ρ q)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [h2] at h1
  exact h1

theorem lam_inf_eq_bot_aux (hKG : KGI22One) (hOdd : OddCoverExact P6) (J₀ : Subgroup Q)
    [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q) (ρ : Q →* P6) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = J₀) (V₀ T₀ : Subgroup Q) (hV₀ : ∀ v ∈ V₀, v * v = 1) (hVJ : V₀ ⊓ J₀ = ⊥)
    (hJT : J₀ ≤ T₀) (hVT : V₀ ≤ T₀) (hTV : T₀ ≤ Subgroup.normalizer (V₀ : Set Q))
    (hT : T₀.map ρ = S06) {q : Q} (hgen : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤) :
    ⁅q1 ρ, q1 ρ⁆ ⊓ J₀ = ⊥ := by
  by_contra hbad
  have hρJ : ∀ j ∈ J₀, ρ j = 1 := fun j hj => MonoidHom.mem_ker.1 (hρk ▸ hj)
  have hgen' := closure_involutions_eq_top hV₀ hgen
  have hJ2 : IsPGroup 2 J₀ := isPGroup_two_of_oddCoverExact J₀ hJc hOdd
    ((QuotientGroup.quotientMulEquivOfEq hρk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)) hgen'
  have hcen : Subgroup.center (commutator ↥(q1 ρ)) ≠ ⊥ := fun h =>
    hbad (lam_inf_eq_bot_of_center J₀ ρ hJc h)
  have hinv := lam_involutions_central J₀ ρ hKG hJc hJ2 hρs hρk hcen
  have hΛJ : ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ = q1 ρ := by rw [← hρk]; exact lam_sup_ker ρ hρs
  have hVL := comm_of_involutions_central (L := ⁅q1 ρ, q1 ρ⁆) hinv hV₀ hTV
    fun v hv hvΛ hvc => by
      have hvJ := lam_center_imp J₀ ρ hJc hρs hρk hvΛ hvc
      have : v ∈ V₀ ⊓ J₀ := ⟨hv, hvJ⟩
      rwa [hVJ, Subgroup.mem_bot] at this
  have hlift : ∀ a : P6, a ∈ S06 → a ∈ alternatingGroup (Fin 6) →
      ∃ l ∈ T₀ ⊓ ⁅q1 ρ, q1 ρ⁆, ρ l = a := by
    intro a ha ha6
    rw [← hT] at ha
    obtain ⟨t, ht, rfl⟩ := ha
    have htQ : t ∈ ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ := by rw [hΛJ]; exact ha6
    obtain ⟨l, hl, z, hz, hlz⟩ := Subgroup.mem_sup_of_normal_right.1 htQ
    refine ⟨l, ⟨?_, hl⟩, ?_⟩
    · have : l = t * z⁻¹ := by rw [← hlz]; group
      rw [this]
      exact T₀.mul_mem ht (T₀.inv_mem (hJT hz))
    · have := congrArg ρ hlz
      rw [map_mul, hρJ z hz, mul_one] at this
      exact this
  obtain ⟨lr, hlr, hρlr⟩ := hlift rD rD_mem_S06 (D0_le_A6 rD_mem)
  obtain ⟨ls, hls, hρls⟩ := hlift sD sD_mem_S06 (D0_le_A6 sD_mem)
  have hV'Z : ∀ v ∈ V₀, ρ v = 1 ∨ ρ v = zA ∨ ρ v = zB ∨ ρ v = zA * zB := by
    intro v hv
    have hvS : ρ v ∈ S06 := hT ▸ Subgroup.mem_map_of_mem ρ (hVT hv)
    refine mem_Z6_of_comm hvS ?_ ?_
    · rw [← hρlr, ← map_mul, ← map_mul, hVL v hv lr hlr]
    · rw [← hρls, ← map_mul, ← map_mul, hVL v hv ls hls]
  have hzA : zA ∈ V₀.map ρ := zA_mem_of_gen (by
    rintro _ ⟨v, hv, rfl⟩
    exact hV'Z v hv) (map_gen hρs hgen)
  obtain ⟨v, hv, hρv⟩ := hzA
  have hvQ₁ : v ∈ q1 ρ := by
    rw [mem_q1, hρv]
    exact D0_le_A6 (VA_le_D0 zA_mem_VA)
  have hlsQ₁ : ls ∈ q1 ρ := Subgroup.commutator_le_left _ _ hls.2
  haveI : (J₀.subgroupOf (q1 ρ)).Normal := Subgroup.Normal.subgroupOf inferInstance _
  exact hcen (center_commutator_eq_bot_of_alt_six hKG (J₀.subgroupOf (q1 ρ))
    (subgroupOf_q1_le_center J₀ ρ hJc) (isPGroup_subgroupOf_q1 J₀ ρ hρk hJ2)
    (ρ.comp (q1 ρ).subtype) (ker_comp_q1 J₀ ρ hρk) (range_comp_q1 ρ hρs)
    (v := ⟨v, hvQ₁⟩) (t := ⟨ls, hlsQ₁⟩) (Subtype.ext (hV₀ v hv)) hρv hρls
    (Subtype.ext (hVL v hv ls hls)))

theorem mem_alt_conj_iff (c x : P6) :
    c * x * c⁻¹ ∈ alternatingGroup (Fin 6) ↔ x ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, Perm.mem_alternatingGroup, map_mul, map_mul, map_inv,
    mul_right_comm, mul_inv_cancel, one_mul]

theorem lam_inf_eq_bot (hKG : KGI22One) (hOdd : OddCoverExact P6) (J₀ : Subgroup Q)
    [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q) (ρ : Q →* P6) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = J₀) (V₀ T₀ : Subgroup Q) (hV₀ : ∀ v ∈ V₀, v * v = 1) (hVJ : V₀ ⊓ J₀ = ⊥)
    (hJT : J₀ ≤ T₀) (hVT : V₀ ≤ T₀) (hTV : T₀ ≤ Subgroup.normalizer (V₀ : Set Q))
    (hSyl : IsSylowTwoOf (T₀.map ρ) ⊤) {q : Q}
    (hgen : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤) : ⁅q1 ρ, q1 ρ⁆ ⊓ J₀ = ⊥ := by
  obtain ⟨c, hc⟩ := exists_conj_of_isSylowTwoOf_top hSyl isSylowTwoOf_S06
  let ρ' : Q →* P6 := (MulAut.conj c).toMonoidHom.comp ρ
  have hρ's : Function.Surjective ρ' := (MulAut.conj c).surjective.comp hρs
  have hρ'k : ρ'.ker = J₀ := by
    rw [← hρk]
    ext x
    simp only [ρ', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hq : q1 ρ' = q1 ρ := by
    ext x
    exact mem_alt_conj_iff c (ρ x)
  have := lam_inf_eq_bot_aux hKG hOdd J₀ hJc ρ' hρ's hρ'k V₀ T₀ hV₀ hVJ hJT hVT hTV
    (by rw [← hc, Subgroup.map_map]) hgen
  rwa [hq] at this

end Core

section Structure

variable {Q : Type} [Group Q] [Finite Q]

theorem swap_not_mem_alt : swap (0 : Fin 6) 1 ∉ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_swap (by decide)]
  decide

theorem commutator_eq_lam (J₀ : Subgroup Q) [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q)
    (ρ : Q →* P6) (hρs : Function.Surjective ρ) (hρk : ρ.ker = J₀) :
    commutator Q = ⁅q1 ρ, q1 ρ⁆ := by
  apply le_antisymm
  · obtain ⟨q', hq'⟩ := hρs (swap (0 : Fin 6) 1)
    have hΛJ : ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ = q1 ρ := by rw [← hρk]; exact lam_sup_ker ρ hρs
    have hq : ∀ x : Q, x ∈ ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ ∨ q'⁻¹ * x ∈ ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ := by
      intro x
      rw [hΛJ]
      by_cases hx : ρ x ∈ alternatingGroup (Fin 6)
      · exact Or.inl hx
      · right
        rw [mem_q1, map_mul, map_inv, hq']
        exact inv_mul_mem_alt swap_not_mem_alt hx
    have hcomm := commutator_mem_of_index_two ⁅q1 ρ, q1 ρ⁆ J₀ hJc hq
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  · rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top

theorem sq_mem_commutator (hgen' : Subgroup.closure {x : Q | x * x = 1} = ⊤) :
    ∀ y : Q, y * y ∈ commutator Q :=
  sq_mem_of_gen (commutator Q) (fun x y =>
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)) hgen'

theorem exists_compl_of_odd (J₀ : Subgroup Q) [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q)
    (ρ : Q →* P6) (hρs : Function.Surjective ρ) (hρk : ρ.ker = J₀)
    (hΛ0 : ⁅q1 ρ, q1 ρ⁆ ⊓ J₀ = ⊥) {u : Q} (hu2 : u * u = 1)
    (hu : ρ u ∉ alternatingGroup (Fin 6)) : ∃ Y₀ : Subgroup Q, Y₀ ⊓ J₀ = ⊥ ∧ Y₀ ⊔ J₀ = ⊤ := by
  have hΛJ : ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ = q1 ρ := by rw [← hρk]; exact lam_sup_ker ρ hρs
  have hρJ : ∀ j ∈ J₀, ρ j = 1 := fun j hj => MonoidHom.mem_ker.1 (hρk ▸ hj)
  have hw : ∀ w ∈ Subgroup.zpowers u, w = 1 ∨ w = u := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hu2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hu2, one_zpow, one_mul]
  have hmem : ∀ x, x ∈ ⁅q1 ρ, q1 ρ⁆ ⊔ Subgroup.zpowers u ↔
      ∃ l ∈ ⁅q1 ρ, q1 ρ⁆, x = l ∨ x = l * u := by
    intro x
    rw [Subgroup.mem_sup_of_normal_left]
    constructor
    · rintro ⟨l, hl, w, hw', hlw⟩
      rcases hw w hw' with h | h
      · exact ⟨l, hl, Or.inl (by rw [← hlw, h, mul_one])⟩
      · exact ⟨l, hl, Or.inr (by rw [← hlw, h])⟩
    · rintro ⟨l, hl, h | h⟩
      · exact ⟨l, hl, 1, one_mem _, by rw [h, mul_one]⟩
      · exact ⟨l, hl, u, Subgroup.mem_zpowers u, h.symm⟩
  refine ⟨⁅q1 ρ, q1 ρ⁆ ⊔ Subgroup.zpowers u, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxY, hxJ⟩
    obtain ⟨l, hl, h | h⟩ := (hmem x).1 hxY
    · have : l ∈ ⁅q1 ρ, q1 ρ⁆ ⊓ J₀ := ⟨hl, h ▸ hxJ⟩
      rw [hΛ0, Subgroup.mem_bot] at this
      rw [h, this]
      exact one_mem _
    · exfalso
      apply hu
      have h1 : ρ l * ρ u = 1 := by rw [← map_mul, ← h]; exact hρJ _ hxJ
      have hl6 : ρ l ∈ alternatingGroup (Fin 6) := by
        have : l ∈ q1 ρ := Subgroup.commutator_le_left _ _ hl
        exact this
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ hl6
  · rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_sup_of_normal_right]
    by_cases hx : ρ x ∈ alternatingGroup (Fin 6)
    · have : x ∈ ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ := by rw [hΛJ]; exact hx
      obtain ⟨l, hl, j, hj, hlj⟩ := Subgroup.mem_sup_of_normal_right.1 this
      exact ⟨l, Subgroup.mem_sup_left hl, j, hj, hlj⟩
    · have hxu : x * u ∈ ⁅q1 ρ, q1 ρ⁆ ⊔ J₀ := by
        rw [hΛJ, mem_q1, map_mul]
        exact mul_mem_alt hx hu
      obtain ⟨l, hl, j, hj, hlj⟩ := Subgroup.mem_sup_of_normal_right.1 hxu
      refine ⟨l * u, Subgroup.mul_mem_sup hl (Subgroup.mem_zpowers u), j, hj, ?_⟩
      have hjc := Subgroup.mem_center_iff.1 (hJc hj) u
      calc l * u * j = l * (u * j) := by group
        _ = l * (j * u) := by rw [hjc]
        _ = (l * j) * u := by group
        _ = x := by rw [hlj, mul_assoc, hu2, mul_one]

theorem six_structure (hKG : KGI22One) (hOdd : OddCoverExact P6) (J₀ : Subgroup Q)
    [J₀.Normal] (hJc : J₀ ≤ Subgroup.center Q) (ρ : Q →* P6) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker = J₀) (V₀ T₀ : Subgroup Q) (hV₀ : ∀ v ∈ V₀, v * v = 1) (hVJ : V₀ ⊓ J₀ = ⊥)
    (hJT : J₀ ≤ T₀) (hVT : V₀ ≤ T₀) (hTV : T₀ ≤ Subgroup.normalizer (V₀ : Set Q))
    (hSyl : IsSylowTwoOf (T₀.map ρ) ⊤) {q : Q}
    (hgen : V₀ ⊔ V₀.map (MulAut.conj q).toMonoidHom = ⊤) :
    (∀ j ∈ J₀, j * j = 1) ∧ commutator Q ⊓ J₀ = ⊥ ∧
      ∃ Y₀ : Subgroup Q, Y₀ ⊓ J₀ = ⊥ ∧ Y₀ ⊔ J₀ = ⊤ := by
  have hΛ0 := lam_inf_eq_bot hKG hOdd J₀ hJc ρ hρs hρk V₀ T₀ hV₀ hVJ hJT hVT hTV hSyl hgen
  have hgen' := closure_involutions_eq_top hV₀ hgen
  have hcomm_eq := commutator_eq_lam J₀ hJc ρ hρs hρk
  refine ⟨fun j hj => ?_, by rw [hcomm_eq]; exact hΛ0, ?_⟩
  · have h1 : j * j ∈ ⁅q1 ρ, q1 ρ⁆ := hcomm_eq ▸ sq_mem_commutator hgen' j
    have : j * j ∈ ⁅q1 ρ, q1 ρ⁆ ⊓ J₀ := ⟨h1, J₀.mul_mem hj hj⟩
    rwa [hΛ0, Subgroup.mem_bot] at this
  ·
    obtain ⟨u, hu, hu6⟩ : ∃ u ∈ V₀, ρ u ∉ alternatingGroup (Fin 6) := by
      by_contra hno
      push Not at hno
      have hV₀le : V₀ ≤ q1 ρ := fun u hu => hno u hu
      have hconj : V₀.map (MulAut.conj q).toMonoidHom ≤ q1 ρ := by
        rintro _ ⟨v, hv, rfl⟩
        exact (inferInstance : (q1 ρ).Normal).conj_mem v (hV₀le hv) q
      have htop : q1 ρ = ⊤ := top_le_iff.1 (hgen ▸ sup_le hV₀le hconj)
      obtain ⟨x, hx⟩ := hρs (swap (0 : Fin 6) 1)
      have hxQ : x ∈ q1 ρ := htop ▸ Subgroup.mem_top x
      rw [mem_q1, hx] at hxQ
      exact swap_not_mem_alt hxQ
    exact exists_compl_of_odd J₀ hJc ρ hρs hρk hΛ0 (hV₀ u hu) hu6

end Structure

section PairLevel

variable {Γ : Type} [Group Γ] [Finite Γ] {X T M V : Subgroup Γ} {g : Γ}

theorem isSylowTwoOf_star_of (hsyl : IsSylowTwoOf T X) : IsSylowTwoOf (E2.star M X T) ⊤ := by
  have hTX : T ≤ X := hsyl.1
  have h1 : IsSylowTwoOf (T.subgroupOf X) ⊤ := by
    refine ⟨le_top, hsyl.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hTX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTX).injective, ?_⟩
    have e : ((T.subgroupOf X).subgroupOf ⊤).index = (T.subgroupOf X).index :=
      Subgroup.relIndex_top_right _
    rw [e]
    exact hsyl.2.2
  exact B6.isSylowTwoOf_map_top (E2P.starMap_surjective M X) h1

theorem exists_rho (h : E2.Pair X T M V g) [((E2.Pair.PP M V X g).subgroupOf X).Normal] :
    ∃ ρ : E2.Pair.Xbar M V X g →* E2.StarQuot M X,
      (∀ x : ↥X, ρ (E2.Pair.piX M V X g x) = QuotientGroup.mk' ((kerIn M X).subgroupOf X) x) ∧
        (∀ x : ↥X, ρ (E2.Pair.piX M V X g x) = 1 ↔ x ∈ (kerIn M X).subgroupOf X) ∧
        Function.Surjective ρ ∧ ρ.ker = E2.Pair.Jbar M V X g := by
  have hPJ : (E2.Pair.PP M V X g).subgroupOf X ≤ (kerIn M X).subgroupOf X :=
    Subgroup.subgroupOf_mono X h.P_le_J
  let ρ : E2.Pair.Xbar M V X g →* E2.StarQuot M X :=
    QuotientGroup.lift ((E2.Pair.PP M V X g).subgroupOf X)
      (QuotientGroup.mk' ((kerIn M X).subgroupOf X)) fun x hx =>
        MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff x).2 (hPJ hx))
  have hρmk : ∀ x : ↥X, ρ (E2.Pair.piX M V X g x) =
      QuotientGroup.mk' ((kerIn M X).subgroupOf X) x := fun x => rfl
  have hker : ∀ x : ↥X, ρ (E2.Pair.piX M V X g x) = 1 ↔ x ∈ (kerIn M X).subgroupOf X := by
    intro x
    rw [hρmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨ρ, hρmk, hker, fun y => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn M X).subgroupOf X) y
    exact ⟨E2.Pair.piX M V X g x, hρmk x⟩
  · ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((E2.Pair.PP M V X g).subgroupOf X) z
    rw [MonoidHom.mem_ker, hker]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * x ∈ (E2.Pair.PP M V X g).subgroupOf X := QuotientGroup.eq.1 hyx
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy (hPJ h1)

theorem map_pre_eq [((E2.Pair.PP M V X g).subgroupOf X).Normal]
    (A : Subgroup (E2.Pair.Xbar M V X g)) :
    ((E2.Pair.pre M V X g A).subgroupOf X).map
      (QuotientGroup.mk' ((E2.Pair.PP M V X g).subgroupOf X)) = A := by
  have h1 : (E2.Pair.pre M V X g A).subgroupOf X = A.comap (E2.Pair.piX M V X g) :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [h1]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) A

end PairLevel

end Six

open Six

theorem eight_six (hKG : E2.KGI22One) (hOdd : Ch3E213M.OddCoverExact (Equiv.Perm (Fin 6)))
    {Γ : Type} [Group Γ] [Finite Γ] {X T M V : Subgroup Γ} {g : Γ} (h : E2.Pair X T M V g)
    [((E2.Pair.PP M V X g).subgroupOf X).Normal] (e : E2.StarQuot M X ≃* Equiv.Perm (Fin 6)) :
    pCoreOf 2 X = kerIn M X ∧
      (∃ Y₀ E : Subgroup (↥X ⧸ (E2.Pair.PP M V X g).subgroupOf X),
        Nonempty (↥Y₀ ≃* E2.StarQuot M X) ∧ IsElemAbelian 2 E ∧
        (Y₀ ⊓ E = ⊥ ∧ Y₀ ⊔ E = ⊤ ∧
          E ≤ Subgroup.centralizer (Y₀ : Set (↥X ⧸ (E2.Pair.PP M V X g).subgroupOf X)))) ∧
      pCoreOf 2 (twoResidual X ⊔ E2.Pair.PP M V X g) = E2.Pair.PP M V X g ∧
      Nonempty (↥(((twoResidual X ⊔ E2.Pair.PP M V X g).subgroupOf X).map
          (QuotientGroup.mk' ((E2.Pair.PP M V X g).subgroupOf X)))
        ≃* ↥(⁅(⊤ : Subgroup (E2.StarQuot M X)), (⊤ : Subgroup (E2.StarQuot M X))⁆)) := by
  have hJn := h.normal_Jbar
  have hJc := h.Jbar_le_center
  obtain ⟨ρ', hρ'mk, hker, hρ's, hρ'k⟩ := exists_rho h
  let ρ : E2.Pair.Xbar M V X g →* Equiv.Perm (Fin 6) := e.toMonoidHom.comp ρ'
  have hρs : Function.Surjective ρ := e.surjective.comp hρ's
  have hρk : ρ.ker = E2.Pair.Jbar M V X g := by
    rw [← hρ'k]
    ext x
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  set T₀ : Subgroup (E2.Pair.Xbar M V X g) :=
    (T.subgroupOf X).map (E2.Pair.piX M V X g) ⊔ E2.Pair.Jbar M V X g with hT₀
  have hVJ : E2.Pair.Vbar M V X g ⊓ E2.Pair.Jbar M V X g = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hv, hj⟩
    obtain ⟨⟨v, hvX⟩, hvV, rfl⟩ := hv
    have h1 : ρ' (E2.Pair.piX M V X g ⟨v, hvX⟩) = 1 := by
      have : E2.Pair.piX M V X g ⟨v, hvX⟩ ∈ ρ'.ker := hρ'k ▸ hj
      exact this
    have h2 : v ∈ kerIn M X := Subgroup.mem_subgroupOf.1 ((hker _).1 h1)
    have h3 : v ∈ E2.Pair.PP M V X g :=
      Subgroup.mem_sup_left ⟨h2, Subgroup.mem_subgroupOf.1 hvV⟩
    have h4 : (⟨v, hvX⟩ : ↥X) ∈ (E2.Pair.PP M V X g).subgroupOf X := Subgroup.mem_subgroupOf.2 h3
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).2 h4
  have hVT' : E2.Pair.Vbar M V X g ≤ T₀ := by
    refine le_trans ?_ le_sup_left
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X h.le_T)
  have hTV' : T₀ ≤ Subgroup.normalizer (E2.Pair.Vbar M V X g : Set (E2.Pair.Xbar M V X g)) := by
    refine sup_le ?_ (hJc.trans (Subgroup.center_le_normalizer _))
    have h1 : (T.subgroupOf X) ≤
        Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.1 (h.normal_T (Subgroup.mem_subgroupOf.1 ht)) (x : Γ)
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
  have hmap' : T₀.map ρ' = E2.star M X T := by
    have hcomp : ρ'.comp (E2.Pair.piX M V X g) =
        QuotientGroup.mk' ((kerIn M X).subgroupOf X) := MonoidHom.ext hρ'mk
    rw [hT₀, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (le_of_eq hρ'k.symm), sup_bot_eq,
      Subgroup.map_map, hcomp]
    rfl
  have hSyl : IsSylowTwoOf (T₀.map ρ) ⊤ := by
    have : T₀.map ρ = (T₀.map ρ').map e.toMonoidHom := by
      rw [Subgroup.map_map]
    rw [this, hmap']
    exact isSylowTwoOf_map_mulEquiv e (isSylowTwoOf_star_of h.sylow)
  obtain ⟨hJexp, hcomm0, Y₀, hYinf, hYsup⟩ := six_structure hKG hOdd (E2.Pair.Jbar M V X g) hJc ρ
    hρs hρk (E2.Pair.Vbar M V X g) T₀ h.Vbar_sq hVJ le_sup_right hVT' hTV' hSyl
    h.top_eq_Vbar_sup_conj.symm
  have hcomm6 : commutator (Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) :=
    alternatingGroup.commutator_perm_eq (by simp)
  obtain ⟨eC⟩ := nonempty_commutator_equiv ρ hρs (by rw [hρk]; exact hcomm0)
  have eA := eC.trans (MulEquiv.subgroupCongr hcomm6)
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimp : IsSimpleGroup ↥(commutator (E2.Pair.Xbar M V X g)) := MulEquiv.isSimpleGroup eA
  have hperf : Group.IsPerfect ↥(commutator (E2.Pair.Xbar M V X g)) :=
    ⟨commutator_eq_top_of_mulEquiv' eA commutator_alt_six⟩
  have hsq : ∀ x : E2.Pair.Xbar M V X g, x * x ∈ commutator (E2.Pair.Xbar M V X g) :=
    sq_mem_commutator (closure_involutions_eq_top h.Vbar_sq h.top_eq_Vbar_sup_conj.symm)
  have hH := h.oTwoUpper_sup_P_eq hperf hsq
  have hP2 : IsPGroup 2 (E2.Pair.PP M V X g) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hJ2 : IsPGroup 2 (kerIn M X) := by
    intro j
    have hjX : (j : Γ) ∈ X := kerIn_le.trans h.le_X j.2
    have hjj := hJexp (E2.Pair.piX M V X g ⟨j, hjX⟩)
      ⟨⟨j, hjX⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hjj
    obtain ⟨k, hk⟩ := hP2 ⟨_, hjj⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one] at hk'
    rw [SubmonoidClass.coe_pow, pow_succ', pow_mul, pow_two, OneMemClass.coe_one]
    exact hk'
  have hE : IsElemAbelian 2 (E2.Pair.Jbar M V X g) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (Subgroup.mem_center_iff.1 (hJc a.2) b).symm
    · rw [pow_two]
      exact hJexp x hx
  have hcent : E2.Pair.Jbar M V X g ≤
      Subgroup.centralizer (Y₀ : Set (↥X ⧸ (E2.Pair.PP M V X g).subgroupOf X)) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subgroup.mem_center_iff.1 (hJc hj) y
  obtain ⟨eY⟩ := nonempty_equiv_of_compl ρ' hρ's Y₀ (by rw [hρ'k]; exact hYinf)
    (by rw [hρ'k]; exact hYsup)
  rw [F6.twoResidual_eq_oTwoUpper, hH]
  refine ⟨le_antisymm h.pCoreOf_le_kerIn (h.le_pCoreOf_of_le_kerIn hJ2 le_rfl),
    ⟨Y₀, E2.Pair.Jbar M V X g, ⟨eY⟩, hE, hYinf, hYsup, hcent⟩,
    h.pCoreOf_pre_eq hsimp hperf, ?_⟩
  rw [map_pre_eq]
  obtain ⟨eC'⟩ := nonempty_commutator_equiv ρ' hρ's (by rw [hρ'k]; exact hcomm0)
  exact ⟨eC'⟩

end CFSG.Quasithin.SimsE210
