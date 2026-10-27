module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3L30
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3Nat

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53Mod
open Equiv

theorem s3_invol_conj : ∀ σ : Perm (Fin 3), σ ≠ 1 → σ * σ = 1 → ∃ g, σ = g * s3t * g⁻¹ := by
  decide +kernel

theorem s3_d_eq : ∃ g : Perm (Fin 3), s3d = g * s3t * g⁻¹ * s3t := by decide +kernel

theorem card_zpowers_invol {σ : Perm (Fin 3)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) :
    Nat.card (Subgroup.zpowers σ) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) h1]

theorem exists_zpowers_of_card_two (E : Subgroup (Perm (Fin 3))) (h : Nat.card E = 2) :
    ∃ σ, σ ≠ 1 ∧ σ * σ = 1 ∧ E = Subgroup.zpowers σ := by
  obtain ⟨x, hx, huniq⟩ := (Nat.card_eq_two_iff' (1 : E)).mp h
  have hx2 : x * x = 1 := by
    by_contra hne
    have := huniq (x * x) hne
    exact hx (by simpa using this)
  refine ⟨x.1, fun h1 => hx (Subtype.ext h1), by simpa using congrArg Subtype.val hx2, ?_⟩
  symm
  refine eq_of_le_of_ne_bot_of_card_eq_two ?_ h ?_
  · rw [Subgroup.zpowers_le]; exact x.2
  · intro hb
    apply hx
    have : x.1 ∈ Subgroup.zpowers x.1 := Subgroup.mem_zpowers _
    rw [hb, Subgroup.mem_bot] at this
    exact Subtype.ext this

variable (M : Model 3)

theorem exists_act_s3t_ne (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤) :
    ∃ w, M.act s3t w ≠ w := by
  by_contra hcon
  push Not at hcon
  apply hA
  obtain ⟨g, hg⟩ := s3_d_eq
  have hd : ∀ w, M.act s3d w = w := by
    intro w
    conv_lhs => rw [hg]
    simp only [act_mul_apply, hcon, act_act_inv]
  rw [eq_top_iff]
  intro x _
  rw [alternatingGroup_three]
  exact (mem_fixW_zpowers M).mpr (hd x)

theorem s3_idx_conj (g a : Perm (Fin 3)) : idx M (g * a * g⁻¹) = idx M a := by
  have : Subgroup.zpowers (g * a * g⁻¹) =
      (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  unfold idx
  rw [this]
  have h1 := Subgroup.card_mul_index (fixW M ((Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom))
  have h2 := Subgroup.card_mul_index (fixW M (Subgroup.zpowers a))
  rw [card_fixW_conj] at h1
  have hpos : 0 < Nat.card (fixW M (Subgroup.zpowers a)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

theorem idx_invol (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤)
    (hidx : (fixW M S3Syl).index ≤ 2) {σ : Perm (Fin 3)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) :
    (fixW M (Subgroup.zpowers σ)).index = 2 := by
  obtain ⟨g, rfl⟩ := s3_invol_conj σ h1 h2
  have h3 : idx M (g * s3t * g⁻¹) = idx M s3t := s3_idx_conj M g s3t
  unfold idx at h3
  rw [h3]
  have h4 : (fixW M (Subgroup.zpowers s3t)).index ≠ 1 := by
    intro h
    obtain ⟨w, hw⟩ := exists_act_s3t_ne M hA
    apply hw
    have : w ∈ fixW M (Subgroup.zpowers s3t) := by rw [Subgroup.index_eq_one.mp h]; trivial
    exact (mem_fixW_zpowers M).mp this
  have h5 : (fixW M (Subgroup.zpowers s3t)).index ≤ 2 := hidx
  have h6 : 0 < (fixW M (Subgroup.zpowers s3t)).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  omega

theorem commW_mono {B C : Subgroup (Perm (Fin 3))} (h : B ≤ C) (U : Subgroup M.W) :
    commW M B U ≤ commW M C U := by
  unfold commW
  exact Subgroup.closure_mono fun w ⟨b, hb, u, hu, e⟩ => ⟨b, h hb, u, hu, e⟩

theorem s3_decomp (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤)
    (hidx : (fixW M S3Syl).index ≤ 2) :
    ∃ R : Subgroup M.W, R = commW M ⊤ ⊤ ∧ IsCompl R (fixW M ⊤) ∧ Nat.card R = 4 := by
  obtain ⟨hU, hcompl, ⟨e⟩, hfix⟩ := s3_lemma30 M hA hidx
  rw [hfix] at hcompl
  have hR : commW M (alternatingGroup (Fin 3)) ⊤ = commW M ⊤ ⊤ := by
    refine le_antisymm (commW_mono M le_top _) ?_
    unfold commW
    rw [Subgroup.closure_le]
    rintro w ⟨b, hb, u, hu, rfl⟩
    have hu' : u ∈ commW M (alternatingGroup (Fin 3)) ⊤ ⊔ fixW M ⊤ := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨r, hr, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu'
    have hc' : M.act b c = c := hc b (Subgroup.mem_top _)
    rw [map_mul, hc', SetLike.mem_coe]
    have : M.act b r * c * (r * c)⁻¹ = M.act b r * r⁻¹ := by
      rw [mul_inv_rev, mul_comm c⁻¹ r⁻¹, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    rw [this]
    exact Subgroup.mul_mem _ (hU b (Subgroup.mem_top _) r hr) (Subgroup.inv_mem _ hr)
  refine ⟨commW M (alternatingGroup (Fin 3)) ⊤, hR, hcompl, ?_⟩
  have := Nat.card_congr e.toMulEquiv.toEquiv
  rw [nat3_card] at this
  exact this

theorem commW_invol_card (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤)
    (hidx : (fixW M S3Syl).index ≤ 2) {σ : Perm (Fin 3)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) :
    Nat.card (commW M (Subgroup.zpowers σ) ⊤) = 2 := by
  rw [← bf1 M σ]; exact idx_invol M hA hidx h1 h2

theorem fixW_zpowers_sup_zpowers (v : M.W) {σ τ : Perm (Fin 3)}
    (hσ : v ∈ fixW M (Subgroup.zpowers σ)) (hτ : v ∈ fixW M (Subgroup.zpowers τ)) :
    v ∈ fixW M (Subgroup.zpowers σ ⊔ Subgroup.zpowers τ) := by
  rw [Subgroup.sup_eq_closure, mem_fixW_closure]
  rintro s (hs | hs)
  · exact hσ s hs
  · exact hτ s hs

theorem commW_invol_ne (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤)
    (hidx : (fixW M S3Syl).index ≤ 2) {σ τ : Perm (Fin 3)} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) (hne : Subgroup.zpowers σ ≠ Subgroup.zpowers τ)
    {R : Subgroup M.W} (hR : R = commW M ⊤ ⊤) (hcompl : IsCompl R (fixW M ⊤)) :
    commW M (Subgroup.zpowers σ) ⊤ ≠ commW M (Subgroup.zpowers τ) ⊤ := by
  intro heq
  have hc := commW_invol_card M hA hidx hσ1 hσ2
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hc]; norm_num))
  have hvσ : v.1 ∈ fixW M (Subgroup.zpowers σ) := commW_le_fixW_of_sq M hσ2 v.2
  have hvτ : v.1 ∈ fixW M (Subgroup.zpowers τ) := by
    have : v.1 ∈ commW M (Subgroup.zpowers τ) ⊤ := heq ▸ v.2
    exact commW_le_fixW_of_sq M hτ2 this
  have hcard : ∀ {ρ : Perm (Fin 3)}, ρ ≠ 1 → ρ * ρ = 1 → Nat.card (Subgroup.zpowers ρ) = 2 :=
    fun h1 h2 => card_zpowers_invol h1 h2
  have htop : Subgroup.zpowers σ ⊔ Subgroup.zpowers τ = ⊤ :=
    CFSG.Quasithin.F53.perm3_sup_eq_top _ _ (hcard hσ1 hσ2) (hcard hτ1 hτ2) hne
  have hvfix : v.1 ∈ fixW M ⊤ := by
    have := fixW_zpowers_sup_zpowers M v.1 hvσ hvτ
    rwa [htop] at this
  have hvR : v.1 ∈ R := by
    rw [hR]
    exact commW_mono M le_top ⊤ v.2
  have := Subgroup.disjoint_def.mp hcompl.disjoint hvR hvfix
  exact hv1 (Subtype.ext this)

theorem commW_invol_sup (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤)
    (hidx : (fixW M S3Syl).index ≤ 2) {σ τ : Perm (Fin 3)} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) (hne : Subgroup.zpowers σ ≠ Subgroup.zpowers τ)
    {R : Subgroup M.W} (hR : R = commW M ⊤ ⊤) (hcompl : IsCompl R (fixW M ⊤))
    (hR4 : Nat.card R = 4) :
    commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤ = R := by
  have hP := commW_invol_card M hA hidx hσ1 hσ2
  have hQ := commW_invol_card M hA hidx hτ1 hτ2
  have hPR : commW M (Subgroup.zpowers σ) ⊤ ≤ R := hR ▸ commW_mono M le_top ⊤
  have hQR : commW M (Subgroup.zpowers τ) ⊤ ≤ R := hR ▸ commW_mono M le_top ⊤
  have hle : commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤ ≤ R := sup_le hPR hQR
  have hne' := commW_invol_ne M hA hidx hσ1 hσ2 hτ1 hτ2 hne hR hcompl
  have hdvd : Nat.card ↥(commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤) ∣ 4 :=
    hR4 ▸ Subgroup.card_dvd_of_le hle
  have hPd : 2 ∣ Nat.card ↥(commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤) :=
    hP ▸ Subgroup.card_dvd_of_le le_sup_left
  have hne2 : Nat.card ↥(commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤) ≠ 2 := by
    intro h
    apply hne'
    have h1 : commW M (Subgroup.zpowers σ) ⊤ =
        commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤ :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    have h2 : commW M (Subgroup.zpowers τ) ⊤ =
        commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤ :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
    rw [h1, ← h2]
  have h4 : Nat.card ↥(commW M (Subgroup.zpowers σ) ⊤ ⊔ commW M (Subgroup.zpowers τ) ⊤) = 4 := by
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨c, hc⟩ := hPd
    rw [hc] at hdvd hne2 hle4 ⊢
    have : c ≤ 2 := by omega
    interval_cases c <;> omega
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

end F53Mod

namespace F53
open Equiv CFSG.Quasithin.F53Mod

variable {G : Type} [Group G] [Finite G]

section ZModel

variable (X Z : Subgroup G)

@[expose] def conjAct (hN : X ≤ Subgroup.normalizer (Z : Set G)) : ↥X →* MulAut ↥Z where
  toFun x :=
    { toFun := fun z => ⟨(x : G) * z * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN x.2) z).mp z.2⟩
      invFun := fun z => ⟨(x : G)⁻¹ * z * (x : G), by
        have := (Subgroup.mem_normalizer_iff.mp (hN (X.inv_mem x.2)) z).mp z.2
        simpa using this⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun z => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun z => Subtype.ext (by simp)
  map_mul' := fun a b => MulEquiv.ext fun z => Subtype.ext (by simp [mul_assoc])

abbrev commGroupOfElem (hZ : IsElemAbelian 2 Z) : CommGroup ↥Z :=
  { (inferInstance : Group ↥Z) with
    mul_comm := fun a b => Subtype.ext (isElemAbelian_comm hZ a.2 b.2) }

variable {X Z}

@[expose] noncomputable def zModel (hN : X ≤ Subgroup.normalizer (Z : Set G)) (hZ : IsElemAbelian 2 Z)
    (ψ : ↥X →* Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥X, ψ x = 1 → ∀ z ∈ Z, (x : G) * z * (x : G)⁻¹ = z) : Model 3 where
  W := ↥Z
  grp := commGroupOfElem Z hZ
  fin := inferInstance
  act := MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
    ⟨conjAct X Z hN, fun x hx => by
      refine MulEquiv.ext fun z => Subtype.ext ?_
      exact hker x hx z z.2⟩
  sq := fun w => by
    have := isElemAbelian_pow_eq_one hZ w.2
    apply Subtype.ext
    show (w : G) * w = 1
    simpa [pow_two] using this

theorem coe_zModel_act (hN : X ≤ Subgroup.normalizer (Z : Set G)) (hZ : IsElemAbelian 2 Z)
    (ψ : ↥X →* Perm (Fin 3)) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥X, ψ x = 1 → ∀ z ∈ Z, (x : G) * z * (x : G)⁻¹ = z) (x : ↥X)
    (w : ↥Z) :
    ((show ↥Z from (zModel hN hZ ψ hψ hker).act (ψ x) w : ↥Z) : G) =
      (x : G) * (w : ↥Z) * (x : G)⁻¹ := by
  show ((MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
    ⟨conjAct X Z hN, _⟩) (ψ x) w : G) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

end ZModel

structure ZData (G : Type) [Group G] where
  X : Subgroup G
  Z : Subgroup G
  le : Z ≤ X
  ψ : ↥X →* Perm (Fin 3)
  normal : X ≤ Subgroup.normalizer (Z : Set G)
  elem : IsElemAbelian 2 Z
  surj : Function.Surjective ψ
  ker : ∀ x : ↥X, ψ x = 1 → ∀ z ∈ Z, (x : G) * z * (x : G)⁻¹ = z

namespace ZData

variable (D : ZData G)

@[expose] noncomputable def M : Model 3 := zModel D.normal D.elem D.ψ D.surj D.ker

abbrev val (w : D.M.W) : G := ((show ↥D.Z from w : ↥D.Z) : G)

abbrev ofMem (z : G) (hz : z ∈ D.Z) : D.M.W := (⟨z, hz⟩ : ↥D.Z)

theorem val_ofMem (z : G) (hz : z ∈ D.Z) : D.val (D.ofMem z hz) = z := rfl

theorem val_mul (a b : D.M.W) : D.val (a * b) = D.val a * D.val b := rfl

theorem val_inv (a : D.M.W) : D.val a⁻¹ = (D.val a)⁻¹ := rfl

theorem val_injective : Function.Injective D.val := fun _ _ h => Subtype.ext h

theorem val_mem (w : D.M.W) : D.val w ∈ D.Z := (show ↥D.Z from w).2

theorem act_val (x : ↥D.X) (w : D.M.W) :
    D.val (D.M.act (D.ψ x) w) = (x : G) * D.val w * (x : G)⁻¹ :=
  coe_zModel_act D.normal D.elem D.ψ D.surj D.ker x w

theorem mem_fixW_iff {K : Subgroup G} (hK : K ≤ D.X) (w : D.M.W) :
    w ∈ fixW D.M ((K.subgroupOf D.X).map D.ψ) ↔ ∀ k ∈ K, k * D.val w = D.val w * k := by
  constructor
  · intro h k hk
    have := h (D.ψ ⟨k, hK hk⟩) ⟨⟨k, hK hk⟩, hk, rfl⟩
    have h2 := congrArg D.val this
    rw [D.act_val] at h2
    calc k * D.val w = (k * D.val w * k⁻¹) * k := by group
      _ = D.val w * k := by rw [h2]
  · rintro h _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ K := hy
    apply D.val_injective
    rw [D.act_val y w]
    calc (y : G) * D.val w * (y : G)⁻¹ = (D.val w * (y : G)) * (y : G)⁻¹ := by rw [h _ hy']
      _ = D.val w := by group

@[expose] noncomputable def valHom : D.M.W →* G := D.Z.subtype

theorem valHom_apply (w : D.M.W) : D.valHom w = D.val w := rfl

theorem valHom_injective : Function.Injective D.valHom := D.val_injective

theorem map_valHom_commW {K : Subgroup G} (hK : K ≤ D.X) :
    (commW D.M ((K.subgroupOf D.X).map D.ψ) ⊤).map D.valHom = ⁅D.Z, K⁆ := by
  apply le_antisymm
  · refine Subgroup.map_le_iff_le_comap.mpr ?_
    unfold commW
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨b, ⟨y, hy, rfl⟩, u, -, rfl⟩
    have hy' : (y : G) ∈ K := hy
    have h1 := Subgroup.commutator_mem_commutator hy' (D.val_mem u)
    rw [Subgroup.commutator_comm] at h1
    show D.val (D.M.act (D.ψ y) u * u⁻¹) ∈ ⁅D.Z, K⁆
    rw [D.val_mul, D.val_inv, D.act_val y u]
    rw [commutatorElement_def] at h1
    exact h1
  · rw [Subgroup.commutator_le]
    intro z hz k hk
    have hkX : k ∈ D.X := hK hk
    let u : D.M.W := (⟨z, hz⟩ : ↥D.Z)
    let b := D.ψ ⟨k, hkX⟩
    have hb : b ∈ (K.subgroupOf D.X).map D.ψ := ⟨⟨k, hkX⟩, hk, rfl⟩
    have hc : D.M.act b u * u⁻¹ ∈ commW D.M ((K.subgroupOf D.X).map D.ψ) ⊤ :=
      Subgroup.subset_closure ⟨b, hb, u, trivial, rfl⟩
    refine Subgroup.mem_map.mpr ⟨_, Subgroup.inv_mem _ hc, ?_⟩
    rw [D.valHom_apply, D.val_inv, D.val_mul, D.val_inv, D.act_val ⟨k, hkX⟩ u, commutatorElement_def]
    have hu : D.val u = z := rfl
    rw [hu]
    group

theorem map_psi_self : (D.X.subgroupOf D.X).map D.ψ = ⊤ := by
  rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
  exact D.surj

theorem map_valHom_fixW_top :
    (fixW D.M ⊤).map D.valHom = D.Z ⊓ Subgroup.centralizer (D.X : Set G) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← D.map_psi_self] at hw
    have := (D.mem_fixW_iff le_rfl w).mp hw
    refine ⟨D.val_mem w, Subgroup.mem_centralizer_iff.mpr fun k hk => this k hk⟩
  · rintro ⟨hz, hc⟩
    refine ⟨D.ofMem g hz, ?_, rfl⟩
    rw [← D.map_psi_self]
    refine (D.mem_fixW_iff le_rfl _).mpr fun k hk => ?_
    exact Subgroup.mem_centralizer_iff.mp hc k hk

theorem map_valHom_commW_top :
    (commW D.M ⊤ ⊤).map D.valHom = ⁅D.Z, D.X⁆ := by
  have := D.map_valHom_commW (K := D.X) le_rfl
  rwa [D.map_psi_self] at this

theorem fixW_alt_ne_top (hfaith : ∀ x : ↥D.X, (∀ z ∈ D.Z, (x : G) * z * (x : G)⁻¹ = z) → D.ψ x = 1) :
    fixW D.M (alternatingGroup (Fin 3)) ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := D.surj s3d
  have hd : s3d ∈ alternatingGroup (Fin 3) := by
    rw [alternatingGroup_three]; exact Subgroup.mem_zpowers _
  have h1 : D.ψ x = 1 := by
    apply hfaith
    intro z hz
    have hw : D.ofMem z hz ∈ fixW D.M (alternatingGroup (Fin 3)) := by rw [htop]; trivial
    have := congrArg D.val (hw s3d hd)
    rw [← hx, D.act_val, D.val_ofMem] at this
    exact this
  rw [hx] at h1
  exact s3d_ne_one h1

theorem map_valHom_top : (⊤ : Subgroup D.M.W).map D.valHom = D.Z := by
  rw [← MonoidHom.range_eq_map]
  exact Subgroup.range_subtype _

theorem index_fixW (B : Subgroup (Perm (Fin 3))) :
    (fixW D.M B).index = ((fixW D.M B).map D.valHom).relIndex D.Z := by
  rw [← D.map_valHom_top, ← Subgroup.relIndex_top_right,
    Subgroup.relIndex_map_map_of_injective _ _ D.valHom_injective]

theorem map_valHom_fixW_zpowers (s : ↥D.X) :
    (fixW D.M (Subgroup.zpowers (D.ψ s))).map D.valHom =
      D.Z ⊓ Subgroup.centralizer ({(s : G)} : Set G) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := congrArg D.val ((mem_fixW_zpowers D.M).mp hw)
    rw [D.act_val] at h
    refine ⟨D.val_mem w, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    rw [Set.mem_singleton_iff] at hk
    subst hk
    calc (s : G) * D.val w = ((s : G) * D.val w * (s : G)⁻¹) * s := by group
      _ = D.val w * s := by rw [h]
  · rintro ⟨hz, hc⟩
    refine ⟨D.ofMem g hz, (mem_fixW_zpowers D.M).mpr ?_, rfl⟩
    apply D.val_injective
    rw [D.act_val, D.val_ofMem]
    have := Subgroup.mem_centralizer_iff.mp hc s rfl
    calc (s : G) * g * (s : G)⁻¹ = (g * s) * (s : G)⁻¹ := by rw [this]
      _ = g := by group

theorem fixW_S3Syl_index_le (htrans : ∃ s : ↥D.X, D.ψ s ≠ 1 ∧ D.ψ s * D.ψ s = 1 ∧
      (D.Z ⊓ Subgroup.centralizer ({(s : G)} : Set G)).relIndex D.Z ≤ 2) :
    (fixW D.M S3Syl).index ≤ 2 := by
  obtain ⟨s, hs1, hs2, hrel⟩ := htrans
  obtain ⟨g, hg⟩ := s3_invol_conj _ hs1 hs2
  have h1 : (fixW D.M S3Syl).index = idx D.M (D.ψ s) := by
    rw [hg, s3_idx_conj]; rfl
  rw [h1]
  unfold idx
  rw [D.index_fixW, D.map_valHom_fixW_zpowers]
  exact hrel

@[expose] def Faithful : Prop :=
  ∀ x : ↥D.X, (∀ z ∈ D.Z, (x : G) * z * (x : G)⁻¹ = z) → D.ψ x = 1

@[expose] def HasTransvection : Prop :=
  ∃ s : ↥D.X, D.ψ s ≠ 1 ∧ D.ψ s * D.ψ s = 1 ∧
    (D.Z ⊓ Subgroup.centralizer ({(s : G)} : Set G)).relIndex D.Z ≤ 2

variable {D}

theorem comm_decomp (hf : D.Faithful) (ht : D.HasTransvection) :
    Nat.card ↥⁅D.Z, D.X⁆ = 4 ∧
      ⁅D.Z, D.X⁆ ⊔ (D.Z ⊓ Subgroup.centralizer (D.X : Set G)) = D.Z ∧
      ⁅D.Z, D.X⁆ ⊓ (D.Z ⊓ Subgroup.centralizer (D.X : Set G)) = ⊥ := by
  obtain ⟨R, hR, hcompl, hR4⟩ := s3_decomp D.M (D.fixW_alt_ne_top hf) (D.fixW_S3Syl_index_le ht)
  have hRmap : R.map D.valHom = ⁅D.Z, D.X⁆ := by rw [hR]; exact D.map_valHom_commW_top
  refine ⟨?_, ?_, ?_⟩
  · rw [← hRmap, Subgroup.card_map_of_injective D.valHom_injective, hR4]
  · rw [← hRmap, ← D.map_valHom_fixW_top, ← Subgroup.map_sup, hcompl.sup_eq_top, D.map_valHom_top]
  · rw [← hRmap, ← D.map_valHom_fixW_top, ← Subgroup.map_inf_eq _ _ _ D.valHom_injective,
      hcompl.inf_eq_bot, Subgroup.map_bot]

theorem line_facts (hf : D.Faithful) (ht : D.HasTransvection) {K : Subgroup G} (hK : K ≤ D.X)
    (hc : Nat.card ((K.subgroupOf D.X).map D.ψ) = 2) :
    Nat.card ↥⁅D.Z, K⁆ = 2 ∧ ⁅D.Z, K⁆ ≤ ⁅D.Z, D.X⁆ ∧
      ⁅D.Z, K⁆ ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨σ, hσ1, hσ2, hKb⟩ := exists_zpowers_of_card_two _ hc
  have hA := D.fixW_alt_ne_top hf
  have hidx := D.fixW_S3Syl_index_le ht
  have hmap := (D.map_valHom_commW hK).symm
  refine ⟨?_, Subgroup.commutator_mono le_rfl hK, ?_⟩
  · rw [hmap, Subgroup.card_map_of_injective D.valHom_injective, hKb]
    exact commW_invol_card D.M hA hidx hσ1 hσ2
  · rw [hmap]
    rintro _ ⟨w, hw, rfl⟩
    rw [hKb] at hw
    have h1 : w ∈ fixW D.M ((K.subgroupOf D.X).map D.ψ) := by
      rw [hKb]; exact commW_le_fixW_of_sq D.M hσ2 hw
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    exact (D.mem_fixW_iff hK w).mp h1 k hk

theorem line_ne_sup (hf : D.Faithful) (ht : D.HasTransvection) {K K' : Subgroup G}
    (hK : K ≤ D.X) (hK' : K' ≤ D.X) (hc : Nat.card ((K.subgroupOf D.X).map D.ψ) = 2)
    (hc' : Nat.card ((K'.subgroupOf D.X).map D.ψ) = 2)
    (hne : (K.subgroupOf D.X).map D.ψ ≠ (K'.subgroupOf D.X).map D.ψ) :
    ⁅D.Z, K⁆ ≠ ⁅D.Z, K'⁆ ∧ ⁅D.Z, K⁆ ⊔ ⁅D.Z, K'⁆ = ⁅D.Z, D.X⁆ := by
  obtain ⟨σ, hσ1, hσ2, hKb⟩ := exists_zpowers_of_card_two _ hc
  obtain ⟨τ, hτ1, hτ2, hKb'⟩ := exists_zpowers_of_card_two _ hc'
  have hA := D.fixW_alt_ne_top hf
  have hidx := D.fixW_S3Syl_index_le ht
  obtain ⟨R, hR, hcompl, hR4⟩ := s3_decomp D.M hA hidx
  have hRmap : R.map D.valHom = ⁅D.Z, D.X⁆ := by rw [hR]; exact D.map_valHom_commW_top
  have hne' : Subgroup.zpowers σ ≠ Subgroup.zpowers τ := by
    rw [← hKb, ← hKb']; exact hne
  have hm := D.map_valHom_commW hK
  have hm' := D.map_valHom_commW hK'
  rw [hKb] at hm
  rw [hKb'] at hm'
  refine ⟨?_, ?_⟩
  · rw [← hm, ← hm']
    intro h
    exact commW_invol_ne D.M hA hidx hσ1 hσ2 hτ1 hτ2 hne' hR hcompl
      (Subgroup.map_injective D.valHom_injective h)
  · rw [← hm, ← hm', ← Subgroup.map_sup, commW_invol_sup D.M hA hidx hσ1 hσ2 hτ1 hτ2 hne' hR hcompl hR4,
      hRmap]

end ZData
end F53

namespace F53.Stellmacher

open CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Lv (d e : Geo H M) : Subgroup G := ⁅Zv d, Qv e⁆

@[expose] def Nv (d : Geo H M) : Subgroup G := Zv d ⊓ centerOf (stab d)

@[expose] def Z0v (d : Geo H M) : Subgroup G := ⁅Zv d, stab d⁆

section Data

variable (hA : F53Amalgam H M S) {d : Geo H M} (hv : vtype d = true) (hb : bAt d = bMin H M)

@[expose] noncomputable def psiAt : ↥(stab d) →* Perm (Fin 3) := (exists_quotHom_true hA hv).choose

include hv in
theorem psiAt_surj : Function.Surjective (psiAt hA hv) := (exists_quotHom_true hA hv).choose_spec.1

include hv in
theorem psiAt_ker (x : ↥(stab d)) : psiAt hA hv x = 1 ↔ (x : G) ∈ Qv d :=
  (exists_quotHom_true hA hv).choose_spec.2 x

@[expose] noncomputable def zData : ZData G where
  X := stab d
  Z := Zv d
  le := (Zv_le_Qv hA d).trans (pCoreOf_le 2 _)
  ψ := psiAt hA hv
  normal := stab_le_normalizer_Zv hA d
  elem := isElemAbelian_Zv hA d
  surj := psiAt_surj hA hv
  ker := fun x hx z hz => by
    have hq := (psiAt_ker hA hv x).mp hx
    have := Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA d hz).2 x hq
    calc (x : G) * z * (x : G)⁻¹ = (z * x) * (x : G)⁻¹ := by rw [this]
      _ = z := by group

include hb in
theorem zData_faithful : (zData hA hv (d := d)).Faithful := by
  intro x hx
  have hx : ∀ z ∈ Zv d, (x : G) * z * (x : G)⁻¹ = z := hx
  show psiAt hA hv x = 1
  refine (psiAt_ker hA hv x).mpr ?_
  rw [← centralizer_Zv_eq_Qv_of_bAt hA hb]
  refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have := hx z hz
  exact (mul_inv_eq_iff_eq_mul.mp this).symm

end Data

section Partner

variable (hA : F53Amalgam H M S) {d d' : Geo H M} (hv : vtype d = true)
  (hb : bAt d = bMin H M) (hd' : IsCritPair₁ d d') (hcomm : ⁅Zv d, Zv d'⁆ ≠ ⊥)

include hA hb hd' in
theorem exists_critData_of_pair : ∃ β : Geo H M, IsCritData d β d' := by
  have hbpos := bMin_pos hA
  obtain ⟨β, hβ, hdist⟩ := exists_adj_dist_eq hA.amalgam.gen (α := d') (δ := d)
    (d := bMin H M - 1) (by rw [CosetGeom.dist_comm, hd'.2]; omega)
  refine ⟨β, hβ, hb, hd'.2, ?_, hd'.1⟩
  rw [CosetGeom.dist_comm] at hdist
  omega

include hA hv hb hd' hcomm in
theorem zData_hasTransvection (h113a : Hss113aAt H M) :
    (zData hA hv (d := d)).HasTransvection := by
  obtain ⟨β, hc⟩ := exists_critData_of_pair hA hb hd'
  obtain ⟨hb', hZ'⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hnle : ¬ Zv d' ≤ Qv d := not_le_Qv_of_comm_ne hA hcomm
  obtain ⟨s, hs, hsQ⟩ := Set.not_subset.mp hnle
  let sx : ↥(stab d) := ⟨s, hZ' hs⟩
  have hZ2 : IsPGroup 2 (Zv d') := (pCoreOf_isPGroup 2 (stab d')).to_le (Zv_le_Qv hA d')
  refine ⟨sx, ?_, ?_, ?_⟩
  · intro h; exact hsQ ((psiAt_ker hA hv sx).mp h)
  · have hs2 : sx * sx = 1 := Subtype.ext (by
      have := (isElemAbelian_Zv hA d').2 s hs
      simpa [pow_two] using this)
    show psiAt hA hv sx * psiAt hA hv sx = 1
    rw [← map_mul, hs2, map_one]
  · have h113 := h113a d d' hd' hcomm
    have hcard : Nat.card (((Zv d').subgroupOf (stab d)).map (psiAt hA hv)) =
        (Zv d' ⊓ Qv d).relIndex (Zv d') := by
      rw [card_map_subgroupOf_eq (psiAt hA hv) (psiAt_ker hA hv) hZ', Subgroup.inf_relIndex_left]
    have hle2 : (Zv d' ⊓ Qv d).relIndex (Zv d') ≤ 2 := by
      rw [← hcard]
      exact perm3_card_le_two_of_isPGroup _ (isPGroup_map_subgroupOf _ hZ2)
    have hsub : Zv d ⊓ Qv d' ≤ Zv d ⊓ Subgroup.centralizer ({s} : Set G) := by
      refine inf_le_inf_left _ ?_
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA d' hs).2) x hx).symm
    have hdvd := Subgroup.relIndex_dvd_of_le_left (Zv d) hsub
    have hpos : (Zv d ⊓ Qv d').relIndex (Zv d) ≠ 0 := Subgroup.index_ne_zero_of_finite
    show (Zv d ⊓ Subgroup.centralizer ({s} : Set G)).relIndex (Zv d) ≤ 2
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd
    omega

end Partner

theorem Nv_eq (hA : F53Amalgam H M S) (d : Geo H M) :
    Nv d = Zv d ⊓ Subgroup.centralizer (stab d : Set G) := by
  have hle : Zv d ≤ stab d := (Zv_le_Qv hA d).trans (pCoreOf_le 2 _)
  ext x
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, hle h1, h3⟩

section Lines

variable (hA : F53Amalgam H M S) {d : Geo H M} (hv : vtype d = true)
  (hb : bAt d = bMin H M)

omit [Finite G] in
theorem nbr_adj {e : Geo H M} (he : e ∈ nbrs d) : (graph (H ⊔ M) H M).Adj d e := he

include hA in
theorem Qv_le_stab_of_nbr {e : Geo H M} (he : e ∈ nbrs d) : Qv e ≤ stab d :=
  Qv_le_stab_of_mem_nbrs hA (show d ∈ nbrs e from (nbr_adj he).symm)

omit [Finite G] in
theorem le_centralizer_sup {L A B : Subgroup G} (hA : L ≤ Subgroup.centralizer (A : Set G))
    (hB : L ≤ Subgroup.centralizer (B : Set G)) : L ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro z hz
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro h (hh | hh)
  · exact Subgroup.mem_centralizer_iff.mp (hA hz) h hh
  · exact Subgroup.mem_centralizer_iff.mp (hB hz) h hh

include hA in
theorem comm_Zv_le {K : Subgroup G} (hK : K ≤ stab d) : ⁅Zv d, K⁆ ≤ Zv d := by
  rw [Subgroup.commutator_le]
  intro z hz k hk
  have h1 : (k : G) * z⁻¹ * (k : G)⁻¹ ∈ Zv d :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA d (hK hk)) _).mp ((Zv d).inv_mem hz)
  rw [commutatorElement_def]
  have : z * k * z⁻¹ * k⁻¹ = z * (k * z⁻¹ * k⁻¹) := by group
  rw [this]
  exact (Zv d).mul_mem hz h1

variable (h28 : Hss28At H M) (hb2 : 2 ≤ bMin H M) {e : Geo H M} (he : e ∈ nbrs d)

include hA hv hb h28 hb2 he in
theorem map_psi_Qv_eq_edge :
    ((Qv e).subgroupOf (stab d)).map (psiAt hA hv) =
      ((stab d ⊓ stab e).subgroupOf (stab d)).map (psiAt hA hv) := by
  have hQe := Qv_le_stab_of_nbr hA he
  have hQd : Qv d ≤ stab d := pCoreOf_le 2 _
  have h28' := h28 hb2 d e (nbr_adj he) hb
  rw [← h28', Subgroup.subgroupOf_sup hQd hQe, Subgroup.map_sup]
  have : ((Qv d).subgroupOf (stab d)).map (psiAt hA hv) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    exact (psiAt_ker hA hv x).mpr hx
  rw [this, bot_sup_eq]

include hA hv hb h28 hb2 he in
theorem card_psi_Qv :
    Nat.card (((Qv e).subgroupOf (stab d)).map (psiAt hA hv)) = 2 := by
  rw [map_psi_Qv_eq_edge hA hv hb h28 hb2 he,
    card_map_subgroupOf_eq (psiAt hA hv) (psiAt_ker hA hv) inf_le_left]
  exact relIndex_Qv_inf_true hA he hv

include hA hv in
theorem map_psi_edge_ne {e e' : Geo H M} (he : e ∈ nbrs d) (he' : e' ∈ nbrs d) (hne : e ≠ e') :
    ((stab d ⊓ stab e).subgroupOf (stab d)).map (psiAt hA hv) ≠
      ((stab d ⊓ stab e').subgroupOf (stab d)).map (psiAt hA hv) := by
  have hkerE : ∀ {ν : Geo H M}, ν ∈ nbrs d →
      (psiAt hA hv).ker ≤ ((stab d ⊓ stab ν).subgroupOf (stab d)) :=
    fun hν x hx => Qv_le_edge hA hν ((psiAt_ker hA hv x).mp hx)
  intro h
  apply inf_stab_ne_of_ne hA he he' hne
  have h1 := congrArg (Subgroup.comap (psiAt hA hv)) h
  rw [Subgroup.comap_map_eq_self (hkerE he), Subgroup.comap_map_eq_self (hkerE he')] at h1
  rw [Subgroup.subgroupOf_inj] at h1
  simpa using h1

variable (hf : (zData hA hv (d := d)).Faithful) (ht : (zData hA hv (d := d)).HasTransvection)

include hA hv hb h28 hb2 he hf ht in
theorem Lv_facts_of : Nat.card ↥(Lv d e) = 2 ∧ Lv d e ≤ Z0v d ∧
    Lv d e ≤ Subgroup.centralizer (Qv e : Set G) :=
  ZData.line_facts (D := zData hA hv) hf ht (K := Qv e) (Qv_le_stab_of_nbr hA he)
    (card_psi_Qv hA hv hb h28 hb2 he)

include hA hv hb h28 hb2 he hf ht in
theorem Lv_le_center_of : Lv d e ≤ centerOf (stab d ⊓ stab e) := by
  obtain ⟨-, -, hQe⟩ := Lv_facts_of hA hv hb h28 hb2 he hf ht
  have hLZ : Lv d e ≤ Zv d := comm_Zv_le hA (Qv_le_stab_of_nbr hA he)
  have h28' := h28 hb2 d e (nbr_adj he) hb
  refine le_inf ((hLZ.trans (Zv_le_Qv hA d)).trans (Qv_le_inf hA he)) ?_
  rw [← h28']
  exact le_centralizer_sup (hLZ.trans ((Zv_le_centerOf_Qv hA d).trans inf_le_right)) hQe

include hA hv hb h28 hb2 he hf ht in
theorem Lv_le_Zv_inf_of : Lv d e ≤ Zv d ⊓ Zv e := by
  have hLZ : Lv d e ≤ Zv d := comm_Zv_le hA (Qv_le_stab_of_nbr hA he)
  refine le_inf hLZ ?_
  have hc := Lv_le_center_of hA hv hb h28 hb2 he hf ht
  refine le_trans (fun x hx => ?_) (omegaOneCenter_le_Zv hA he).2.2
  apply Subgroup.subset_closure
  exact ⟨hc hx, (isElemAbelian_Zv hA d).2 x (hLZ hx)⟩

include hA hv hb h28 hb2 he hf ht in
theorem Lv_ne_sup_of {e' : Geo H M} (he' : e' ∈ nbrs d) (hne : e ≠ e') :
    Lv d e ≠ Lv d e' ∧ Lv d e ⊔ Lv d e' = Z0v d :=
  ZData.line_ne_sup (D := zData hA hv) hf ht (K := Qv e) (K' := Qv e')
    (Qv_le_stab_of_nbr hA he) (Qv_le_stab_of_nbr hA he')
    (card_psi_Qv hA hv hb h28 hb2 he) (card_psi_Qv hA hv hb h28 hb2 he')
    (by
      show ((Qv e).subgroupOf (stab d)).map (psiAt hA hv) ≠ ((Qv e').subgroupOf (stab d)).map (psiAt hA hv)
      rw [map_psi_Qv_eq_edge hA hv hb h28 hb2 he, map_psi_Qv_eq_edge hA hv hb h28 hb2 he']
      exact map_psi_edge_ne hA hv he he' hne)

include hA hv hb hf ht in
theorem Z0v_decomp_of : Nat.card ↥(Z0v d) = 4 ∧ Z0v d ⊔ Nv d = Zv d ∧ Z0v d ⊓ Nv d = ⊥ := by
  rw [Nv_eq hA]
  exact ZData.comm_decomp (D := zData hA hv) hf ht

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_forall_comm {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ∀ w ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, w = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro x y ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
        calc a1 * b1 * (a2 * b2) = a1 * (b1 * a2) * b2 := by group
          _ = a1 * (a2 * b1) * b2 := by rw [← h a2 ha2 b1 hb1]
          _ = a1 * a2 * (b1 * b2) := by group
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have := h a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [this]
          _ = a⁻¹ * b⁻¹ := by group }
  have : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact fun w hw => this hw

include hA hv hb h28 hb2 he hf ht in
theorem Zv_inf_Zv_eq_of : Zv d ⊓ Zv e = Lv d e ⊔ Nv d := by
  obtain ⟨hcard, hLZ0, -⟩ := Lv_facts_of hA hv hb h28 hb2 he hf ht
  obtain ⟨h4, hsup, -⟩ := Z0v_decomp_of hA hv hb hf ht
  have hLle := Lv_le_Zv_inf_of hA hv hb h28 hb2 he hf ht
  have hNZ : Nv d ≤ Zv d := inf_le_left
  have hNle : Nv d ≤ Zv d ⊓ Zv e := by
    refine le_inf hNZ ?_
    refine le_trans (fun x hx => ?_) (((omegaOneCenter_le_Zv hA he).1).trans
      (omegaOneCenter_le_Zv hA he).2.2)
    apply Subgroup.subset_closure
    exact ⟨hx.2, (isElemAbelian_Zv hA d).2 x hx.1⟩
  have hZ0Z : Z0v d ≤ Zv d := comm_Zv_le hA le_rfl
  have hne : ¬ Zv d ≤ Zv e := by
    intro hle
    have : Lv d e = ⊥ := by
      rw [Lv, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hle.trans ((Zv_le_centerOf_Qv hA e).trans inf_le_right)
    rw [this, Subgroup.card_bot] at hcard
    omega
  apply le_antisymm _ (sup_le hLle hNle)
  intro x hx
  have hxZ : x ∈ Z0v d ⊔ Nv d := hsup ▸ hx.1
  obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_of_mem_sup_of_forall_comm (fun a ha b hb =>
    isElemAbelian_comm (isElemAbelian_Zv hA d) (hZ0Z ha) (hNZ hb)) x hxZ
  have hnS : n ∈ Zv d ⊓ Zv e := hNle hn
  have haS : a ∈ Zv d ⊓ Zv e := by
    have := (Zv d ⊓ Zv e).mul_mem hx ((Zv d ⊓ Zv e).inv_mem hnS)
    simpa using this
  have haL : a ∈ Lv d e := by
    have hLT : Lv d e ≤ (Zv d ⊓ Zv e) ⊓ Z0v d := le_inf hLle hLZ0
    have hTZ0 : (Zv d ⊓ Zv e) ⊓ Z0v d ≤ Z0v d := inf_le_right
    have hdvd : Nat.card ↥((Zv d ⊓ Zv e) ⊓ Z0v d) ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le hTZ0
    have h2 : 2 ∣ Nat.card ↥((Zv d ⊓ Zv e) ⊓ Z0v d) := hcard ▸ Subgroup.card_dvd_of_le hLT
    have hc : Nat.card ↥((Zv d ⊓ Zv e) ⊓ Z0v d) = 2 ∨ Nat.card ↥((Zv d ⊓ Zv e) ⊓ Z0v d) = 4 := by
      have hle4 := Nat.le_of_dvd (by norm_num) hdvd
      obtain ⟨c, hc⟩ := h2
      rw [hc] at hdvd hle4 ⊢
      have : c ≤ 2 := by omega
      interval_cases c <;> simp_all
    rcases hc with hc | hc
    · have : Lv d e = (Zv d ⊓ Zv e) ⊓ Z0v d := Subgroup.eq_of_le_of_card_ge hLT (by omega)
      rw [this]; exact ⟨haS, ha⟩
    · exfalso
      have heq : (Zv d ⊓ Zv e) ⊓ Z0v d = Z0v d :=
        Subgroup.eq_of_le_of_card_ge hTZ0 (by omega)
      apply hne
      calc Zv d = Z0v d ⊔ Nv d := hsup.symm
        _ ≤ Zv d ⊓ Zv e := sup_le (heq ▸ inf_le_left) hNle
        _ ≤ Zv e := inf_le_right
  exact (Lv d e ⊔ Nv d).mul_mem (Subgroup.mem_sup_left haL) (Subgroup.mem_sup_right hn)

omit [Finite G] in
theorem smul_mem_nbrs {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab d) {e : Geo H M} (he : e ∈ nbrs d) :
    g • e ∈ nbrs d := by
  have hd : g • d = d := smul_eq_of_mem_stab hg
  have := (smul_adj g).mpr (nbr_adj he)
  rw [hd] at this
  exact this

include hA hv hb h28 hb2 hf ht in
theorem comm_eq_Lv_of {β d' : Geo H M} (hc : IsCritData d β d') (hcomm : ⁅Zv d, Zv d'⁆ ≠ ⊥) :
    ⁅Zv d, Zv d'⁆ = Lv d β := by
  obtain ⟨hb', -⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hZ'Q : Zv d' ≤ Qv β := by
    refine Zv_le_Qv_of_dist_lt ?_
    rw [CosetGeom.dist_comm, hb']
    have := hc.dist_eq'
    omega
  have hle : ⁅Zv d, Zv d'⁆ ≤ Lv d β := Subgroup.commutator_mono le_rfl hZ'Q
  exact eq_of_le_of_ne_bot_of_card_eq_two hle
    (Lv_facts_of hA hv hb h28 hb2 hc.adj hf ht).1 hcomm

end Lines

section Public

variable (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h113a : Hss113aAt H M)
  (hb2 : 2 ≤ bMin H M) {d : Geo H M} (hv : vtype d = true) (hb : bAt d = bMin H M)
  {d' : Geo H M} (hd' : IsCritPair₁ d d') (hcomm : ⁅Zv d, Zv d'⁆ ≠ ⊥)
  {e : Geo H M} (he : e ∈ nbrs d)

include hA h28 h113a hb2 hv hb hd' hcomm he in
theorem card_Lv : Nat.card ↥(Lv d e) = 2 :=
  (Lv_facts_of hA hv hb h28 hb2 he (zData_faithful hA hv hb)
    (zData_hasTransvection hA hv hb hd' hcomm h113a)).1

include hA h28 h113a hb2 hv hb hd' hcomm he in
theorem Lv_le_Zv_inf : Lv d e ≤ Zv d ⊓ Zv e :=
  Lv_le_Zv_inf_of hA hv hb h28 hb2 he (zData_faithful hA hv hb)
    (zData_hasTransvection hA hv hb hd' hcomm h113a)

include hA h28 h113a hb2 hv hb hd' hcomm he in
theorem Lv_ne_and_sup {e' : Geo H M} (he' : e' ∈ nbrs d) (hne : e ≠ e') :
    Lv d e ≠ Lv d e' ∧ Lv d e ⊔ Lv d e' = Z0v d :=
  Lv_ne_sup_of hA hv hb h28 hb2 he (zData_faithful hA hv hb)
    (zData_hasTransvection hA hv hb hd' hcomm h113a) he' hne

include hA h28 h113a hb2 hv hb hd' hcomm in
theorem Z0v_decomp : Nat.card ↥(Z0v d) = 4 ∧ Z0v d ⊔ Nv d = Zv d ∧ Z0v d ⊓ Nv d = ⊥ :=
  Z0v_decomp_of hA hv hb (zData_faithful hA hv hb)
    (zData_hasTransvection hA hv hb hd' hcomm h113a)

include hA h28 h113a hb2 hv hb hd' hcomm he in
theorem Zv_inf_Zv_eq : Zv d ⊓ Zv e = Lv d e ⊔ Nv d :=
  Zv_inf_Zv_eq_of hA hv hb h28 hb2 he (zData_faithful hA hv hb)
    (zData_hasTransvection hA hv hb hd' hcomm h113a)

include hA h28 h113a hb2 hv hb hd' hcomm in
theorem comm_eq_line {β : Geo H M} (hc : IsCritData d β d') :
    ⁅Zv d, Zv d'⁆ = Lv d β ∧ Nat.card ↥⁅Zv d, Zv d'⁆ = 2 := by
  have hq := comm_eq_Lv_of hA hv hb h28 hb2 (zData_faithful hA hv hb)
    (zData_hasTransvection hA hv hb hd' hcomm h113a) hc hcomm
  exact ⟨hq, hq ▸ card_Lv hA h28 h113a hb2 hv hb hd' hcomm hc.adj⟩

end Public

end F53.Stellmacher

end CFSG.Quasithin
