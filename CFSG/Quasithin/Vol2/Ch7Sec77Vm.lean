module

public import CFSG.Quasithin.Vol2.Ch7Sec77Model

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair
open scoped IsMulCommutative commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] def vmFac : Subgroup (StdMod (Fin 3) (ZMod 2)) where
  carrier := {x | Multiplicative.toAdd x 0 = 0}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [ha, hb]
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp [ha]

@[expose] def pairVm : Subgroup (PairMod (ZMod 2)) := vmFac.prod vmFac

theorem mem_pairVm {p : PairMod (ZMod 2)} : p ∈ pairVm ↔ InVm (vp p) := Iff.rfl

theorem card_pairVm : Nat.card pairVm = 16 := by
  have h : (pairVm : Set (PairMod (ZMod 2))) = pv '' (↑(Finset.univ.filter
      (fun q : Vec × Vec => InVm q)) : Set (Vec × Vec)) := by
    ext p
    constructor
    · intro hp
      have hp' : InVm (vp p) := hp
      exact ⟨vp p, by simpa using hp', rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' : InVm x := by simpa using hx
      exact hx'
  calc Nat.card pairVm = (pairVm : Set (PairMod (ZMod 2))).ncard := Nat.card_coe_set_eq _
    _ = 16 := by
      rw [h, Set.ncard_image_of_injective _ pv_injective, Set.ncard_coe_finset, vm_card]

theorem mul_self_pair (p : PairMod (ZMod 2)) : p * p = 1 := by
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  apply vp_injective
  refine Prod.ext ?_ ?_
  · funext i
    exact h2 _
  · funext i
    exact h2 _

theorem rho_th0_three (p : PairMod (ZMod 2)) :
    SL3One.rho th0 (SL3One.rho th0 (SL3One.rho th0 p)) = p := by
  have h : (SL3One.rho th0) ^ 3 = 1 := by rw [← map_pow, th0_pow_three, map_one]
  calc SL3One.rho th0 (SL3One.rho th0 (SL3One.rho th0 p)) = ((SL3One.rho th0) ^ 3) p := by
        rw [pow_three]; rfl
    _ = p := by rw [h]; rfl

theorem rho_mem_pairVm {p : PairMod (ZMod 2)} (hp : p ∈ pairVm) : SL3One.rho th0 p ∈ pairVm := by
  rw [mem_pairVm, vp_rho, dact_th0]
  exact ⟨vm_th0 _ hp.1, dvm_th0 _ hp.2⟩

theorem exists_pairVm {p : PairMod (ZMod 2)} (hp : p ∈ pairVm) :
    ∃ q ∈ pairVm, q * SL3One.rho th0 q = p := by
  obtain ⟨v₁, hv₁, h₁⟩ := vm_surj _ hp.1
  obtain ⟨v₂, hv₂, h₂⟩ := dvm_surj _ hp.2
  refine ⟨pv (v₁, v₂), ⟨hv₁, hv₂⟩, vp_injective ?_⟩
  refine Prod.ext ?_ ?_
  · change Multiplicative.toAdd (pv (v₁, v₂)).1 + Multiplicative.toAdd (SL3One.rho th0
      (pv (v₁, v₂))).1 = Multiplicative.toAdd p.1
    rw [rho_fst, add_comm]
    exact h₁
  · change Multiplicative.toAdd (pv (v₁, v₂)).2 + Multiplicative.toAdd (SL3One.rho th0
      (pv (v₁, v₂))).2 = Multiplicative.toAdd p.2
    rw [rho_snd, dact_th0, add_comm]
    exact h₂

abbrev a1 : PairMod (ZMod 2) := pv (e1, 0)

abbrev b1 : PairMod (ZMod 2) := pv (0, e1)

theorem a1_ne_one : a1 ≠ 1 := by
  intro h
  have h1 : (vp a1).1 0 = (vp (1 : PairMod (ZMod 2))).1 0 := by rw [h]
  exact absurd h1 (by decide)

theorem a1_mem_V₁ : a1 ∈ V₁ (ZMod 2) := ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩

theorem rho_th0_a1 : SL3One.rho th0 a1 = a1 := by
  apply vp_injective
  rw [vp_rho, dact_th0]
  refine Prod.ext ?_ ?_
  · exact (fix_th0 e1).mpr (Or.inr rfl)
  · change th0d *ᵥ (0 : Vec) = 0
    exact Matrix.mulVec_zero _

theorem rho_th0_b1 : SL3One.rho th0 b1 = b1 := by
  apply vp_injective
  rw [vp_rho, dact_th0]
  refine Prod.ext ?_ ?_
  · change act th0 (0 : Vec) = 0
    exact Matrix.mulVec_zero _
  · exact (dfix_th0 e1).mpr (Or.inr rfl)

theorem exists_fix_mul_vm (p : PairMod (ZMod 2)) :
    ∃ p0 pm, SL3One.rho th0 p0 = p0 ∧ pm ∈ pairVm ∧ p = p0 * pm := by
  set x := (vp p).1
  set y := (vp p).2
  refine ⟨pv (x 0 • e1, y 0 • e1), pv (x - x 0 • e1, y - y 0 • e1), ?_, ?_, ?_⟩
  · apply vp_injective
    rw [vp_rho, dact_th0]
    refine Prod.ext ?_ ?_
    · change (th0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (x 0 • e1) = x 0 • e1
      rw [Matrix.mulVec_smul, show (th0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1 = e1 from
        (fix_th0 e1).mpr (Or.inr rfl)]
    · change th0d *ᵥ (y 0 • e1) = y 0 • e1
      rw [Matrix.mulVec_smul, (dfix_th0 e1).mpr (Or.inr rfl)]
  · refine ⟨?_, ?_⟩
    · change (x - x 0 • e1) 0 = 0
      simp
    · change (y - y 0 • e1) 0 = 0
      simp
  · apply vp_injective
    change (x, y) = (x 0 • e1 + (x - x 0 • e1), y 0 • e1 + (y - y 0 • e1))
    exact Prod.ext (add_sub_cancel _ _).symm (add_sub_cancel _ _).symm

namespace Setup

variable (S : Setup T L I)
include S

structure Coord (θ : G) (e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)) : Prop where
  mem : θ ∈ L
  odd : Odd (orderOf θ)
  he : (autI S.hV (fsuL0 T L)).map (congrHom e) = pairSL (ZMod 2)
  heI : (intSub S.hV I).map e.toMonoidHom = V₁ (ZMod 2)
  hθ : congrHom e (convI S.hV ⟨θ, S.L_le_normalizer_V mem⟩) = SL3One.rho th0

theorem exists_coord {θ : G} (hθL : θ ∈ L)
    (hθ3 : θ ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G))
    (hθ1 : θ ∉ Subgroup.centralizer (fsuV T I : Set G)) :
    ∃ θ' e, S.Coord θ' e ∧ ∀ v ∈ fsuV T I, v ∈ Subgroup.centralizer ({θ'} : Set G) ↔
      v ∈ Subgroup.centralizer ({θ} : Set G) := by
  obtain ⟨θ', hθ'L, hodd, hfix, hθ'N, e, he, -, heI, hθe⟩ := S.exists_model_th0 hθL hθ3 hθ1
  exact ⟨θ', e, ⟨hθ'L, hodd, he, heI, hθe⟩, hfix⟩

@[expose] def vec (e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)) (p : PairMod (ZMod 2)) : G :=
  E3.valHom S.hV (e.symm p)

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)}

theorem vec_mem (p : PairMod (ZMod 2)) : S.vec e p ∈ fsuV T I := (e.symm p).val_mem

theorem vec_mul (p q : PairMod (ZMod 2)) : S.vec e (p * q) = S.vec e p * S.vec e q := by
  rw [vec, vec, vec, map_mul, map_mul]

theorem vec_one : S.vec e 1 = 1 := by rw [vec, map_one, map_one]

theorem vec_inv_eq (p : PairMod (ZMod 2)) : (S.vec e p)⁻¹ = S.vec e p :=
  inv_eq_of_mul_eq_one_right (by rw [← vec_mul, mul_self_pair, vec_one])

theorem vec_injective : Function.Injective (S.vec e) := fun _ _ h =>
  e.symm.injective (E3.valHom_injective S.hV h)

theorem e_vec (p : PairMod (ZMod 2)) : e (IntMod.mk S.hV ⟨S.vec e p, vec_mem p⟩) = p :=
  e.apply_symm_apply p

theorem vec_e {w : G} (hw : w ∈ fsuV T I) : S.vec e (e (IntMod.mk S.hV ⟨w, hw⟩)) = w := by
  rw [vec, MulEquiv.symm_apply_apply]
  rfl

theorem exists_vec {w : G} (hw : w ∈ fsuV T I) : ∃ p, S.vec e p = w := ⟨_, vec_e hw⟩

theorem conj_vec {x : G} (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (p : PairMod (ZMod 2)) :
    x * S.vec e p * x⁻¹ = S.vec e (congrHom e (convI S.hV ⟨x, hx⟩) p) := by
  have h : congrHom e (convI S.hV ⟨x, hx⟩) p = e (convI S.hV ⟨x, hx⟩ (e.symm p)) := rfl
  rw [h, vec, vec, MulEquiv.symm_apply_apply, E3.valHom_apply, E3.valHom_apply,
    convI_apply_val]

theorem vec_mem_centralizer_iff {x : G} (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (p : PairMod (ZMod 2)) : S.vec e p ∈ Subgroup.centralizer ({x} : Set G) ↔
      congrHom e (convI S.hV ⟨x, hx⟩) p = p := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← (vec_injective (S := S) (e := e)).eq_iff,
    ← conj_vec hx]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    calc S.vec e p * x = x * S.vec e p * x⁻¹ * x := by rw [h]
      _ = x * S.vec e p := by group

theorem mem_centralizer_vec_iff {x : G} (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G))
    (p : PairMod (ZMod 2)) : x ∈ Subgroup.centralizer ({S.vec e p} : Set G) ↔
      congrHom e (convI S.hV ⟨x, hx⟩) p = p := by
  rw [← vec_mem_centralizer_iff hx, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

variable {θ : G}

theorem conj_vec_th (hc : S.Coord θ e) (p : PairMod (ZMod 2)) :
    θ * S.vec e p * θ⁻¹ = S.vec e (SL3One.rho th0 p) := by
  rw [conj_vec (S.L_le_normalizer_V hc.mem), hc.hθ]
  rfl

theorem conj_vec_th_inv (hc : S.Coord θ e) (p : PairMod (ZMod 2)) :
    θ⁻¹ * S.vec e p * θ = S.vec e (SL3One.rho th0 (SL3One.rho th0 p)) := by
  calc θ⁻¹ * S.vec e p * θ = θ⁻¹ * (θ * S.vec e (SL3One.rho th0 (SL3One.rho th0 p)) * θ⁻¹) * θ :=
        by rw [conj_vec_th hc, rho_th0_three]
    _ = S.vec e (SL3One.rho th0 (SL3One.rho th0 p)) := by group

variable (S) in
@[expose] def vm (e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)) : Subgroup G :=
  (pairVm.comap e.toMonoidHom).map (E3.valHom S.hV)

theorem vec_mem_vm {p : PairMod (ZMod 2)} (hp : p ∈ pairVm) : S.vec e p ∈ S.vm e :=
  ⟨e.symm p, by simpa using hp, rfl⟩

theorem mem_vm_iff {w : G} : w ∈ S.vm e ↔ ∃ p ∈ pairVm, S.vec e p = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e x, hx, ?_⟩
    rw [vec, MulEquiv.symm_apply_apply]
  · rintro ⟨p, hp, rfl⟩
    exact vec_mem_vm hp

theorem vm_le : S.vm e ≤ fsuV T I := E3.map_valHom_le S.hV _

theorem card_vm : Nat.card (S.vm e) = 16 := by
  rw [vm, Subgroup.card_map_of_injective (E3.valHom_injective S.hV), ← card_pairVm]
  exact Nat.card_congr
    { toFun := fun x => ⟨e x, x.2⟩
      invFun := fun y => ⟨e.symm y, by simp [y.2]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }

theorem mem_normalizer_vm (hc : S.Coord θ e) : θ ∈ Subgroup.normalizer (S.vm e : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hw
    rw [conj_vec_th hc]
    exact vec_mem_vm (rho_mem_pairVm hp)
  · intro hw
    obtain ⟨p, hp, hpw⟩ := mem_vm_iff.mp hw
    have h : w = θ⁻¹ * S.vec e p * θ := by rw [hpw]; group
    rw [h, conj_vec_th_inv hc]
    exact vec_mem_vm (rho_mem_pairVm (rho_mem_pairVm hp))

theorem commutator_vm (hc : S.Coord θ e) : ⁅S.vm e, Subgroup.zpowers θ⁆ = S.vm e := by
  have hN : Subgroup.zpowers θ ≤ Subgroup.normalizer (S.vm e : Set G) :=
    (Subgroup.zpowers_le).mpr (mem_normalizer_vm hc)
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro v hv g hg
    have hgv : g * v⁻¹ * g⁻¹ ∈ S.vm e :=
      (Subgroup.mem_normalizer_iff.mp (hN hg) _).mp ((S.vm e).inv_mem hv)
    have h : ⁅v, g⁆ = v * (g * v⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [h]
    exact (S.vm e).mul_mem hv hgv
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hw
    obtain ⟨q, hq, rfl⟩ := exists_pairVm hp
    have hinv : (S.vec e q)⁻¹ = S.vec e q := vec_inv_eq q
    have h : S.vec e (q * SL3One.rho th0 q) = ⁅S.vec e q, θ⁆ := by
      calc S.vec e (q * SL3One.rho th0 q) = S.vec e q * (θ * S.vec e q * θ⁻¹) := by
            rw [vec_mul, conj_vec_th hc]
        _ = S.vec e q * (θ * (S.vec e q)⁻¹ * θ⁻¹) := by rw [hinv]
        _ = ⁅S.vec e q, θ⁆ := by rw [commutatorElement_def]; group
    rw [h]
    exact Subgroup.commutator_mem_commutator (vec_mem_vm hq) (Subgroup.mem_zpowers θ)

theorem vec_a1_mem (hc : S.Coord θ e) : S.vec e a1 ∈ I := by
  have ha : a1 ∈ (intSub S.hV I).map e.toMonoidHom := by
    rw [hc.heI]
    exact a1_mem_V₁
  obtain ⟨x, hx, hxa⟩ := ha
  have hx' : x = e.symm a1 := by
    rw [← hxa]
    exact (e.symm_apply_apply x).symm
  rw [hx'] at hx
  exact hx

theorem vec_a1_ne_one : S.vec e a1 ≠ 1 := fun h => a1_ne_one (vec_injective (h.trans vec_one.symm))

theorem vec_mem_V0 (hc : S.Coord θ e) {p : PairMod (ZMod 2)} (hp : SL3One.rho th0 p = p) :
    S.vec e p ∈ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) := by
  refine ⟨vec_mem p, (vec_mem_centralizer_iff (S.L_le_normalizer_V hc.mem) p).mpr ?_⟩
  rw [hc.hθ]
  exact hp

theorem vec_a1_mem_V0 (hc : S.Coord θ e) :
    S.vec e a1 ∈ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :=
  vec_mem_V0 hc rho_th0_a1

theorem vec_b1_mem_V0 (hc : S.Coord θ e) :
    S.vec e b1 ∈ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :=
  vec_mem_V0 hc rho_th0_b1

theorem exists_V0_mul_vm (hc : S.Coord θ e) {w : G} (hw : w ∈ fsuV T I) :
    ∃ a ∈ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G), ∃ b ∈ S.vm e, w = a * b := by
  obtain ⟨p, rfl⟩ := exists_vec (S := S) (e := e) hw
  obtain ⟨p0, pm, h₀, hm, rfl⟩ := exists_fix_mul_vm p
  exact ⟨S.vec e p0, vec_mem_V0 hc h₀, S.vec e pm, vec_mem_vm hm, vec_mul _ _⟩

theorem centralizer_inf_vm_le_H0 (hc : S.Coord θ e) :
    Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) :
      Set G) ⊓ Subgroup.centralizer (S.vm e : Set G) ≤ fsuM T L := by
  rintro g ⟨hg₀, hgm⟩
  refine S.centralizer_le_fsuM (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_V0_mul_vm hc hw
  have h1 := Subgroup.mem_centralizer_iff.mp hg₀ a ha
  have h2 := Subgroup.mem_centralizer_iff.mp hgm b hb
  calc a * b * g = a * (b * g) := mul_assoc _ _ _
    _ = a * g * b := by rw [h2, mul_assoc]
    _ = g * (a * b) := by rw [h1, mul_assoc]

theorem centralizer_inf_vm_le_H1 (hr : (2 : ℕ∞) < rParam (fsuV T I)) {Z : Subgroup G}
    (hZ : Z ≤ fsuV T I) :
    Subgroup.centralizer (Z : Set G) ⊓ Subgroup.centralizer (S.vm e : Set G) ≤ fsuM T L := by
  rintro g ⟨hgZ, hgm⟩
  set A := Z ⊔ S.vm e with hA
  have hAV : A ≤ fsuV T I := sup_le hZ vm_le
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := by
    have hle : A ≤ Subgroup.centralizer ({g} : Set G) := sup_le
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hgZ v hv))
      (fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hgm v hv))
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
  by_contra hgM
  have hCA : ¬ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    fun h => hgM (S.hNM (h hgA))
  have h1 : rParam (fsuV T I) ≤ (mQuot (fsuV T I) A : ℕ∞) := by
    unfold rParam
    exact iInf₂_le A ⟨hAV, hCA⟩
  have h4 : mQuot (fsuV T I) (S.vm e) = 2 := by
    have h5 := card_eq_two_pow_mul S.isPGroup_fsuV (vm_le (S := S) (e := e))
    rw [S.card_fsuV, card_vm] at h5
    have h6 : 2 ^ mQuot (fsuV T I) (S.vm e) = 2 ^ 2 :=
      Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 16) (h5.symm.trans (by norm_num))
    exact Nat.pow_right_injective (le_refl 2) h6
  have h2 : mQuot (fsuV T I) A ≤ 2 := h4 ▸ mQuot_mono (V := fsuV T I) le_sup_right
  have h8 : 2 < mQuot (fsuV T I) A := by exact_mod_cast hr.trans_le h1
  omega

end Setup

end CFSG.Quasithin.H13.Sec77
