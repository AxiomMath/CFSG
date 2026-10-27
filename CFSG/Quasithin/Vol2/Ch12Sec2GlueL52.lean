module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Background.JonesParshallCurtisClassify

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L52

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

theorem classify_small
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {ρ : Representation (ZMod 2) G5 W} (hρ : IsSimpleRep ρ)
    (hdim : Module.finrank (ZMod 2) W ≤ 9) :
    (∀ g w, ρ g w = w) ∨ ∃ κ : G5 ≃* G5, ∃ β : W ≃ₗ[ZMod 2] (Fin 5 → ZMod 2),
      ∀ g w, β (ρ g w) = natRep (κ g) (β w) := by
  have := hρ.1
  obtain ⟨y, hy, hy0⟩ := exists_fixU_ne ρ
  by_cases hall : ∀ s, Th ρ s y = 0
  · left
    obtain ⟨β, hβ⟩ := iso_of_type hρ triv_simple hy hy0 (triv_fixU 1) one_ne_zero
      fun s => iff_of_true (hall s) (triv_type s)
    intro g w
    apply β.injective
    rw [hβ, Representation.trivial_apply]
  · right
    push Not at hall
    obtain ⟨s, hs⟩ := hall
    have hother : ∀ t, t ≠ s → Th ρ t y = 0 := fun t hts => by
      by_contra ht
      have := eleven_le_finrank' hρ hy hy0 hts ht hs
      omega
    have hJ := type_of_unique hs hother
    rcases (by decide : ∀ s : Fin 4, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) s with rfl | rfl | rfl | rfl
    · obtain ⟨β, hβ⟩ := iso_of_type hρ natRep_simple hy hy0 e0_mem_fixU e0_ne
        fun t => (hJ t).trans (natRep_type t).symm
      exact ⟨MulEquiv.refl _, β, hβ⟩
    · exfalso
      obtain ⟨β, -⟩ := iso_of_type hρ wedge_simple hy hy0 e01_mem_fixU e01_ne
        fun t => (hJ t).trans (wedge_type t).symm
      have h := β.finrank_eq
      rw [Module.finrank_fin_fun] at h
      omega
    · exfalso
      obtain ⟨β, -⟩ := iso_of_type hρ wedgeTw_simple hy hy0 e01_mem_fixU_tw e01_ne
        fun t => (hJ t).trans (wedgeTw_type t).symm
      have h := β.finrank_eq
      rw [Module.finrank_fin_fun] at h
      omega
    · obtain ⟨β, hβ⟩ := iso_of_type hρ natTw_simple hy hy0 e0_mem_fixU_tw e0_ne
        fun t => (hJ t).trans (natTw_type t).symm
      exact ⟨twistα, β, hβ⟩

theorem neg_vec_eq_self (m : Fin 5 → ZMod 2) : -m = m :=
  funext fun i => ZMod.neg_eq_self_mod_two (m i)

theorem muF2_five_apply (s : G5) (v : Fin 5 → ZMod 2) :
    muF2 5 s v = (s : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v := by
  rw [← Matrix.smul_eq_mulVec, ← Matrix.SpecialLinearGroup.smul_def]
  rfl

theorem zb_of_mulEquiv
    {Γ : Type*} [Group Γ] (κ : Γ ≃* G5) (x : Γ → (Fin 5 → ZMod 2))
    (hx : ∀ g h, x (g * h) = x g + ((κ g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ x h) :
    ∃ m, ∀ g, x g = ((κ g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ m + m := by
  let e : Γ ≃* G5 := κ.trans (invTransposeSL 5 (ZMod 2))
  have he : ∀ g, ((e g : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      ((κ g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ := fun g => by
    rw [MulEquiv.trans_apply, invTransposeSL_coe, map_inv]
  have hy : (fun s => x (e.symm s)) ∈ Z1A (muF2 5) := by
    intro s t
    obtain ⟨g, rfl⟩ := e.surjective s
    obtain ⟨h, rfl⟩ := e.surjective t
    show x (e.symm (e g * e h)) = x (e.symm (e g)) + muF2 5 (e g) (x (e.symm (e h)))
    rw [← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply, hx, muF2_five_apply, he]
  have hZB : Z1A (muF2 5) = B1A (muF2 5) := Z1A_eq_B1A_five
  rw [hZB] at hy
  obtain ⟨m, hm⟩ := hy
  refine ⟨m, fun g => ?_⟩
  have h1 := congrFun hm (e g)
  rw [coboundaryA_apply, MulEquiv.symm_apply_apply, muF2_five_apply, he] at h1
  rw [← h1, sub_eq_add_neg, neg_vec_eq_self]

theorem val_nsmul_one (y : ZMod 2) : (y.val : ℕ) • (1 : ZMod 2) = y := by
  revert y
  decide

theorem zadd_self (u : ZMod 2) : u + u = 0 := by
  revert u
  decide

theorem zcocycle (p t r : ZMod 2) : p + t = r + t + (p + r) := by
  revert p t r
  decide

theorem zswap (p q r t : ZMod 2) (h : p + q = r + t) : p + r = q + t := by
  revert p q r t
  decide

theorem exists_invariant_form
    {Γ : Type*} [Group Γ] {A Q : Type*} [AddCommGroup A]
    [AddCommGroup Q] (ρA : Γ →* AddMonoid.End A)
    (π : A →+ Q) (hπ : Function.Surjective π)
    (hfix : ∀ g a, π a = 0 → ρA g a = a)
    (β : Q ≃+ (Fin 5 → ZMod 2)) (κ : Γ ≃* G5)
    (hβ : ∀ g a, β (π (ρA g a)) = ((κ g : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ β (π a))
    (a : A →+ ZMod 2) :
    ∃ a' : A →+ ZMod 2, (∀ g v, a' (ρA g v) = a' v) ∧ ∀ v, π v = 0 → a' v = a v := by
  classical
  have hs : ∀ i : Fin 5, ∃ s : A, β (π s) = Pi.single i 1 := fun i => by
    obtain ⟨q, hq⟩ := β.surjective (Pi.single i 1)
    obtain ⟨s, rfl⟩ := hπ q
    exact ⟨s, hq⟩
  choose s hs using hs
  let c : Γ → A →+ ZMod 2 := fun g => AddMonoidHom.mk' (fun v => a (ρA g⁻¹ v) + a v)
    (fun u v => by simp only [map_add]; abel)
  have hc : ∀ g v, c g v = a (ρA g⁻¹ v) + a v := fun _ _ => rfl
  have hc0 : ∀ g v, π v = 0 → c g v = 0 := fun g v hv => by
    rw [hc, hfix g⁻¹ v hv, zadd_self]
  let x : Γ → Fin 5 → ZMod 2 := fun g i => c g (s i)
  have hcx : ∀ g v, c g v = x g ⬝ᵥ β (π v) := fun g v => by
    set y := β (π v) with hy
    let v' : A := ∑ i, (y i).val • s i
    have hv' : β (π v') = y := by
      simp only [v', map_sum, map_nsmul, hs]
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, val_nsmul_one]
    have hdiff : π (v + v') = 0 := by
      apply β.injective
      rw [map_add, map_add, hv', ← hy, map_zero]
      funext j
      exact zadd_self (y j)
    have h1 := hc0 g _ hdiff
    rw [map_add] at h1
    have h1' : c g v = c g v' := by
      have := zswap (c g v) (c g v') 0 0 (by rw [h1, zero_add])
      simpa using this
    rw [h1']
    simp only [v', map_sum, map_nsmul, dotProduct, x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nsmul_eq_mul, mul_comm, ← val_nsmul_one (y i), nsmul_eq_mul, mul_one]
    simp
  have hxz : ∀ g h, x (g * h) = x g + ((κ g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ
      x h := fun g h => by
    funext i
    have e1 : c (g * h) (s i) = c g (s i) + c h (ρA g⁻¹ (s i)) := by
      rw [hc, hc, hc, _root_.mul_inv_rev, map_mul]
      change a (ρA h⁻¹ (ρA g⁻¹ (s i))) + a (s i) = a (ρA g⁻¹ (s i)) + a (s i) +
        (a (ρA h⁻¹ (ρA g⁻¹ (s i))) + a (ρA g⁻¹ (s i)))
      exact zcocycle _ _ _
    have e2 : c h (ρA g⁻¹ (s i)) =
        (((κ g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ x h) i := by
      rw [hcx, hβ, hs, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_single, mul_one]
    show c (g * h) (s i) = c g (s i) + _
    rw [e1, e2]
  obtain ⟨m, hm⟩ := zb_of_mulEquiv κ x hxz
  let φ : A →+ ZMod 2 :=
    { toFun := fun v => m ⬝ᵥ β (π v)
      map_zero' := by simp
      map_add' := fun u v => by simp [dotProduct_add] }
  have hφ : ∀ v, φ v = m ⬝ᵥ β (π v) := fun _ => rfl
  refine ⟨AddMonoidHom.mk' (fun v => a v + φ v) (fun u v => by simp only [map_add]; abel),
    fun g v => ?_, fun v hv => ?_⟩
  · have h1 : a (ρA g v) + a v = x g⁻¹ ⬝ᵥ β (π v) := by
      have := hcx g⁻¹ v
      rw [hc, inv_inv] at this
      exact this
    have h2 : φ (ρA g v) + φ v = (((κ g : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ m + m) ⬝ᵥ
        β (π v) := by
      rw [hφ, hφ, hβ, dotProduct_mulVec, ← Matrix.mulVec_transpose, add_dotProduct]
    have h3 := hm g⁻¹
    rw [inv_inv] at h3
    have h4 : a (ρA g v) + a v = φ (ρA g v) + φ v := by rw [h1, h2, h3]
    simp only [AddMonoidHom.mk'_apply]
    exact zswap _ _ _ _ h4
  · simp [hφ, hv]

section Quotient

variable {V : Type} [CommGroup V] (H : Subgroup (MulAut V))

abbrev modTwo (hsq : ∀ v : V, v ^ 2 = 1) : Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (fun a => by
    rw [two_nsmul]
    have h := hsq (Additive.toMul a)
    rw [pow_two] at h
    exact congrArg Additive.ofMul h)

theorem fixV_le_comap (h : MulAut V) (hh : h ∈ H) :
    fixV H ≤ (fixV H).comap h.toMonoidHom := fun w hw => by
  show h w ∈ fixV H
  rw [hw h hh]
  exact hw

@[expose] def qAct (h : ↥H) : V ⧸ fixV H →* V ⧸ fixV H :=
  QuotientGroup.map (fixV H) (fixV H) (h : MulAut V).toMonoidHom (fixV_le_comap H h h.2)

theorem qAct_mk (h : ↥H) (v : V) :
    qAct H h (QuotientGroup.mk v) = QuotientGroup.mk ((h : MulAut V) v) :=
  QuotientGroup.map_mk _ _ _ _ v

theorem qAct_one : qAct H 1 = MonoidHom.id _ := by
  ext v
  rfl

theorem qAct_mul (a b : ↥H) : qAct H (a * b) = (qAct H a).comp (qAct H b) := by
  ext v
  rfl

@[expose] def muQ {Γ : Type*} [Group Γ] (θ : Γ ≃* ↥H) :
    Γ →* AddMonoid.End (Additive (V ⧸ fixV H)) where
  toFun g := (qAct H (θ g)).toAdditive
  map_one' := by rw [map_one, qAct_one]; rfl
  map_mul' a b := by rw [map_mul, qAct_mul]; rfl

@[expose] def muA {Γ : Type*} [Group Γ] (θ : Γ ≃* ↥H) : Γ →* AddMonoid.End (Additive V) where
  toFun g := ((θ g : MulAut V).toMonoidHom).toAdditive
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl

theorem muQ_mk {Γ : Type*} [Group Γ] (θ : Γ ≃* ↥H) (g : Γ) (v : V) :
    muQ H θ g (Additive.ofMul (QuotientGroup.mk v)) =
      Additive.ofMul (QuotientGroup.mk (((θ g : ↥H) : MulAut V) v)) :=
  congrArg Additive.ofMul (qAct_mk H (θ g) v)

theorem muA_ofMul {Γ : Type*} [Group Γ] (θ : Γ ≃* ↥H) (g : Γ) (v : V) :
    muA H θ g (Additive.ofMul v) = Additive.ofMul (((θ g : ↥H) : MulAut V) v) := rfl

theorem isSimpleRep_quot [Module (ZMod 2) (Additive (V ⧸ fixV H))] (θ : G5 ≃* ↥H)
    (hnt : fixV H ≠ ⊤)
    (hirr : ∀ W : Subgroup V, fixV H ≤ W → (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) →
      W = fixV H ∨ W = ⊤) :
    IsSimpleRep (repOfEnd (muQ H θ)) := by
  have hsurj : ∀ q : Additive (V ⧸ fixV H), ∃ v : V,
      Additive.ofMul (QuotientGroup.mk v : V ⧸ fixV H) = q := fun q => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨v, by rw [hv]; rfl⟩
  refine ⟨?_, fun W' hW' => ?_⟩
  · obtain ⟨v, hv⟩ : ∃ v : V, v ∉ fixV H := by
      by_contra hc
      exact hnt (eq_top_iff.mpr fun v _ => not_not.mp (not_exists.mp hc v))
    refine ⟨⟨Additive.ofMul (QuotientGroup.mk v : V ⧸ fixV H), 0, fun h => hv ?_⟩⟩
    exact (QuotientGroup.eq_one_iff v).mp (Additive.ofMul.injective h)
  · let W : Subgroup V :=
      { carrier := {v | Additive.ofMul (QuotientGroup.mk v : V ⧸ fixV H) ∈ W'}
        one_mem' := by
          show Additive.ofMul (QuotientGroup.mk (1 : V) : V ⧸ fixV H) ∈ W'
          rw [QuotientGroup.mk_one, ofMul_one]
          exact W'.zero_mem
        mul_mem' := fun {a b} ha hb => by
          show Additive.ofMul (QuotientGroup.mk (a * b) : V ⧸ fixV H) ∈ W'
          rw [QuotientGroup.mk_mul, ofMul_mul]
          exact W'.add_mem ha hb
        inv_mem' := fun {a} ha => by
          show Additive.ofMul (QuotientGroup.mk a⁻¹ : V ⧸ fixV H) ∈ W'
          rw [QuotientGroup.mk_inv, ofMul_inv]
          exact W'.neg_mem ha }
    have hmem : ∀ v : V, v ∈ W ↔ Additive.ofMul (QuotientGroup.mk v : V ⧸ fixV H) ∈ W' :=
      fun _ => Iff.rfl
    have hfW : fixV H ≤ W := fun v hv => by
      rw [hmem, (QuotientGroup.eq_one_iff v).mpr hv, ofMul_one]
      exact W'.zero_mem
    have hHW : ∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W := fun h hh w hw => by
      have h1 := hW' (θ.symm ⟨h, hh⟩) _ ((hmem w).mp hw)
      change muQ H θ (θ.symm ⟨h, hh⟩) _ ∈ W' at h1
      rw [muQ_mk, MulEquiv.apply_symm_apply] at h1
      exact (hmem _).mpr h1
    rcases hirr W hfW hHW with h | h
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨v, rfl⟩ := hsurj q
      have hv : v ∈ W := (hmem v).mpr hq
      rw [h] at hv
      rw [Submodule.mem_bot, (QuotientGroup.eq_one_iff v).mpr hv, ofMul_one]
    · right
      rw [eq_top_iff]
      intro q _
      obtain ⟨v, rfl⟩ := hsurj q
      exact (hmem v).mp (h ▸ Subgroup.mem_top v)

theorem finrank_quot_le [Finite V] [Module (ZMod 2) (Additive (V ⧸ fixV H))]
    (hV : Nat.card V = 2 ^ 10) (hne : fixV H ≠ ⊥) :
    Module.finrank (ZMod 2) (Additive (V ⧸ fixV H)) ≤ 9 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (fixV H)
  have h2 : 1 < Nat.card (fixV H) := by rw [Subgroup.one_lt_card_iff_ne_bot]; exact hne
  have h4 := FiniteField.pow_finrank_eq_natCard 2 (Additive (V ⧸ fixV H))
  have h3 : Nat.card (Additive (V ⧸ fixV H)) = Nat.card (V ⧸ fixV H) := rfl
  rw [h3] at h4
  have h5 : Nat.card (V ⧸ fixV H) ≤ 2 ^ 9 := by
    rw [hV] at h1
    by_contra hc
    push Not at hc
    have : 2 ^ 9 * 2 < Nat.card (V ⧸ fixV H) * Nat.card (fixV H) :=
      Nat.mul_lt_mul_of_lt_of_le hc h2 (by norm_num)
    omega
  rw [← h4] at h5
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h5

end Quotient

theorem false_of_natural
    {V : Type} [CommGroup V] (H : Subgroup (MulAut V))
    (hsq : ∀ v : V, v ^ 2 = 1) [Module (ZMod 2) (Additive (V ⧸ fixV H))] (θ : G5 ≃* ↥H)
    (hcomm : commV H = ⊤) (hne : fixV H ≠ ⊥) (κ : G5 ≃* G5)
    (β : Additive (V ⧸ fixV H) ≃ₗ[ZMod 2] (Fin 5 → ZMod 2))
    (hβ : ∀ g q, β (repOfEnd (muQ H θ) g q) = natRep (κ g) (β q)) : False := by
  let _ : Module (ZMod 2) (Additive V) := modTwo hsq
  obtain ⟨w₀, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hw₀0 : Additive.ofMul (w₀ : V) ≠ 0 := fun h =>
    hw₀1 (Subtype.ext (Additive.ofMul.injective h))
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hw₀0
  let π : Additive V →+ Additive (V ⧸ fixV H) := (QuotientGroup.mk' (fixV H)).toAdditive
  have hπ : ∀ v : V, π (Additive.ofMul v) = Additive.ofMul (QuotientGroup.mk v) := fun _ => rfl
  have hπs : Function.Surjective π := fun q => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨Additive.ofMul v, by rw [hπ, hv]; rfl⟩
  have hπ0 : ∀ a, π a = 0 → Additive.toMul a ∈ fixV H := fun a ha =>
    (QuotientGroup.eq_one_iff _).mp (Additive.ofMul.injective ha)
  have hfix : ∀ g a, π a = 0 → muA H θ g a = a := fun g a ha =>
    congrArg Additive.ofMul (hπ0 a ha (θ g : MulAut V) (θ g).2)
  have hβ' : ∀ g a, β.toAddEquiv (π (muA H θ g a)) =
      ((κ g : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ β.toAddEquiv (π a) := fun g a => by
    have h := hβ g (π a)
    rw [natRep_apply] at h
    exact h
  obtain ⟨a', ha'inv, ha'eq⟩ := exists_invariant_form (muA H θ) π hπs hfix β.toAddEquiv κ hβ'
    f.toAddMonoidHom
  let S : Subgroup V :=
    { carrier := {v | a' (Additive.ofMul v) = 0}
      one_mem' := by
        show a' (Additive.ofMul 1) = 0
        rw [ofMul_one, map_zero]
      mul_mem' := fun {u v} hu hv => by
        show a' (Additive.ofMul (u * v)) = 0
        rw [ofMul_mul, map_add]
        rw [show a' (Additive.ofMul u) = 0 from hu, show a' (Additive.ofMul v) = 0 from hv,
          add_zero]
      inv_mem' := fun {u} hu => by
        show a' (Additive.ofMul u⁻¹) = 0
        rw [ofMul_inv, map_neg, show a' (Additive.ofMul u) = 0 from hu, neg_zero] }
  have hS : commV H ≤ S := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    show a' (Additive.ofMul (x v * v⁻¹)) = 0
    have h1 : muA H θ (θ.symm ⟨x, hx⟩) (Additive.ofMul v) = Additive.ofMul (x v) := by
      rw [muA_ofMul, MulEquiv.apply_symm_apply]
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, ← h1, ha'inv, add_neg_cancel]
  have hw : (w₀ : V) ∈ S := hS (hcomm ▸ Subgroup.mem_top _)
  have hw' : a' (Additive.ofMul (w₀ : V)) = f (Additive.ofMul (w₀ : V)) :=
    ha'eq _ (by rw [hπ, (QuotientGroup.eq_one_iff _).mpr w₀.2, ofMul_one])
  exact hf (hw'.symm.trans hw)

end CFSG.Quasithin.H13.L52

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
  CFSG.Quasithin.H13.L52

theorem l52TenFixedPointFree
    : L52TenFixedPointFree := by
  intro V _ _ hsq hV H hH hcomm hirr
  obtain ⟨θ₀⟩ := hH
  by_contra hne
  have hsqQ : ∀ q : V ⧸ fixV H, q ^ 2 = 1 := fun q => by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]
  let _ : Module (ZMod 2) (Additive (V ⧸ fixV H)) := modTwo hsqQ
  have hnt : fixV H ≠ ⊤ := fun htop => by
    have hc : commV H = ⊥ := by
      rw [eq_bot_iff, commV, Subgroup.closure_le]
      rintro _ ⟨x, hx, v, rfl⟩
      have hv : v ∈ fixV H := by rw [htop]; exact Subgroup.mem_top v
      rw [hv x hx, mul_inv_cancel]
      exact Subgroup.one_mem _
    rw [hcomm] at hc
    have h1 : Nat.card (⊤ : Subgroup V) = Nat.card (⊥ : Subgroup V) := by rw [hc]
    rw [Subgroup.card_top, Subgroup.card_bot, hV] at h1
    norm_num at h1
  let θ : G5 ≃* ↥H := θ₀.symm
  have hsimple := isSimpleRep_quot H θ hnt hirr
  have hdim := finrank_quot_le H hV hne
  rcases classify_small hsimple hdim with htriv | ⟨κ, β, hβ⟩
  · apply hnt
    rw [eq_top_iff, ← hcomm, commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    have h1 := htriv (θ.symm ⟨x, hx⟩) (Additive.ofMul (QuotientGroup.mk v))
    change muQ H θ (θ.symm ⟨x, hx⟩) _ = _ at h1
    rw [muQ_mk, MulEquiv.apply_symm_apply] at h1
    have h2 := QuotientGroup.eq.mp (Additive.ofMul.injective h1)
    have h3 := (fixV H).inv_mem h2
    rwa [mul_inv_rev, inv_inv, mul_comm] at h3
  · exact false_of_natural H hsq θ hcomm hne κ β hβ

end CFSG.Quasithin.H13
