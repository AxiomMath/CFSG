module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6L3
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.Background.B4L3Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Quasithin CFSG.Quasithin.L3 CFSG.Assembly.LowTwoRank

theorem zpow_eq_one_or_self {M : Type*} [Group M] {a : M} (ha : a ^ 2 = 1) (k : ℤ) :
    a ^ k = 1 ∨ a ^ k = a := by
  have hainv : a⁻¹ = a := by
    rw [pow_two] at ha
    exact inv_eq_of_mul_eq_one_right ha
  induction k using Int.induction_on with
  | zero => left; rw [zpow_zero]
  | succ i ih =>
    rw [zpow_add_one]
    rcases ih with h | h
    · right; rw [h, one_mul]
    · left; rw [h, ← pow_two, ha]
  | pred i ih =>
    rw [zpow_sub_one, hainv]
    rcases ih with h | h
    · right; rw [h, one_mul]
    · left; rw [h, ← pow_two, ha]

variable {V : Type*} [CommGroup V]

theorem exists_of_mem_commV_zpowers {a : MulAut V} (ha : a ^ 2 = 1) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers a)) : ∃ u : V, a u * u⁻¹ = w := by
  let φ : V →* V :=
    { toFun := fun u => a u * u⁻¹
      map_one' := by simp
      map_mul' := fun u u' => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hle : commV (Subgroup.zpowers a) ≤ φ.range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨b, hb, u, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rcases zpow_eq_one_or_self ha k with hk | hk
    · exact ⟨1, by simp [φ, hk]⟩
    · exact ⟨u, by simp [φ, hk]⟩
  obtain ⟨u, hu⟩ := hle hw
  exact ⟨u, hu⟩

variable [Finite V]

theorem cocycle_cob (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16) {G : Subgroup (MulAut V)}
    (hnat : BinaryNaturalSL G ⊤ (fixV G) 3 1) (hind : IsIndecompModule G) (D : L3Data G ⊤ (fixV G))
    (f : Γ → V) (hf : ∀ γ η, f (γ * η) = f γ * D.rho γ (f η)) :
    ∃ w : V, ∀ γ, f γ = D.rho γ w * w⁻¹ := by
  classical
  obtain ⟨-, -, -, hFF⟩ := B4_8_2 hV hcard hnat hind
  let b : V → Vec := fun u => Multiplicative.toAdd (D.β ⟨u, Subgroup.mem_top u⟩)
  have hb_mul : ∀ u u', b (u * u') = b u + b u' := by
    intro u u'
    have : (⟨u * u', Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) =
        ⟨u, Subgroup.mem_top _⟩ * ⟨u', Subgroup.mem_top _⟩ := rfl
    simp only [b, this, map_mul, toAdd_mul]
  have hb_inv : ∀ u, b u⁻¹ = - b u := by
    intro u
    have : (⟨u⁻¹, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = (⟨u, Subgroup.mem_top _⟩)⁻¹ := rfl
    show Multiplicative.toAdd (D.β ⟨u⁻¹, Subgroup.mem_top _⟩) = _
    rw [this, map_inv, toAdd_inv]
  have hb_rho : ∀ γ u, b (D.rho γ u) = act γ (b u) := by
    intro γ u
    have h := D.β_rho γ u (Subgroup.mem_top u) (Subgroup.mem_top _)
    show Multiplicative.toAdd (D.β ⟨D.rho γ u, Subgroup.mem_top _⟩) = _
    rw [h, toAdd_ofAdd]
  have hb_ker : ∀ u, b u = 0 ↔ u ∈ fixV G := by
    intro u
    rw [← D.ker_β ⟨u, Subgroup.mem_top u⟩]
    constructor
    · intro h
      exact Multiplicative.toAdd.injective (by simpa [b] using h)
    · intro h
      simp [b, h]
  have hb_surj : ∀ w' : Vec, ∃ u : V, b u = w' := by
    intro w'
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w')
    exact ⟨u, by simp [b, hu]⟩
  have hf1 : f 1 = 1 := by
    have h := hf 1 1
    rw [mul_one, map_one, MulAut.one_apply] at h
    exact (mul_eq_left.mp h.symm)
  have hcim : ∀ x : Γ, IsInvol x → b (f x) ∈ cim x := by
    intro x hx
    have ha2 : D.rho x ^ 2 = 1 := by rw [pow_two, ← map_mul, hx.1, map_one]
    have ha1 : D.rho x ≠ 1 := fun h => hx.2 (D.rho_injective (h.trans (map_one _).symm))
    have h' : D.rho x (f x) = f x := by
      have h := hf x x
      rw [hx.1, hf1] at h
      have h2 : D.rho x (f x) = (f x)⁻¹ := eq_inv_of_mul_eq_one_right h.symm
      rw [h2]
      have := hV (f x)
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_right this
    have hfix : f x ∈ fixV (Subgroup.zpowers (D.rho x)) := by
      rintro c hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      rcases zpow_eq_one_or_self ha2 k with hk | hk
      · rw [hk]; rfl
      · rw [hk]; exact h'
    rw [← (hFF _ (D.rho_mem x) ha1 ha2).1] at hfix
    obtain ⟨u, hu⟩ := exists_of_mem_commV_zpowers ha2 hfix
    rw [← hu, hb_mul, hb_inv, hb_rho]
    simp only [cim, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨b u, by rw [sub_eq_add_neg]⟩
  obtain ⟨w', h12, h23, h31⟩ := gens_cob _ (hcim x12 x12_invol) _ (hcim x23 x23_invol) _
    (hcim x31 x31_invol)
  obtain ⟨w, hw⟩ := hb_surj w'
  set f' : Γ → V := fun γ => f γ * (D.rho γ w * w⁻¹)⁻¹ with hf'def
  have hf' : ∀ γ η, f' (γ * η) = f' γ * D.rho γ (f' η) := by
    intro γ η
    simp only [hf'def, hf γ η, map_mul, MulAut.mul_apply, map_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hf'1 : f' 1 = 1 := by simp [hf'def, hf1]
  have hbf' : ∀ γ, b (f' γ) = b (f γ) - (act γ w' - w') := by
    intro γ
    simp only [hf'def, hb_mul, hb_inv, hb_rho, hw]
    abel
  have hβall : ∀ γ, b (f' γ) = 0 := by
    let S : Subgroup Γ :=
      { carrier := {γ | b (f' γ) = 0}
        mul_mem' := fun {a c} ha hc => by
          change b (f' (a * c)) = 0
          rw [hf' a c, hb_mul, hb_rho, show b (f' c) = 0 from hc, show b (f' a) = 0 from ha,
            act_zero, add_zero]
        one_mem' := by
          change b (f' 1) = 0
          rw [hf'1]
          exact (hb_ker 1).2 (Subgroup.one_mem _)
        inv_mem' := fun {a} ha => by
          change b (f' a⁻¹) = 0
          have h1 := hf' a a⁻¹
          rw [mul_inv_cancel, hf'1] at h1
          have h2 := congrArg b h1
          rw [hb_mul, hb_rho, show b (f' a) = 0 from ha, zero_add,
            (hb_ker 1).2 (Subgroup.one_mem _)] at h2
          have := congrArg (act a⁻¹) h2.symm
          rwa [act_inv_act, act_zero] at this }
    have hS : Subgroup.closure ({x12, x23, x31} : Set Γ) ≤ S := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      change b (f' x) = 0
      rw [hbf']
      rcases hx with rfl | rfl | rfl
      · rw [h12, sub_self]
      · rw [h23, sub_self]
      · rw [h31, sub_self]
    rw [closure_gens] at hS
    intro γ
    exact hS (Subgroup.mem_top γ)
  have hfixG : ∀ γ, f' γ ∈ fixV G := fun γ => (hb_ker _).1 (hβall γ)
  let φ : Γ →* V :=
    { toFun := f'
      map_one' := hf'1
      map_mul' := fun a c => by
        change f' (a * c) = f' a * f' c
        rw [hf' a c, (hfixG c) _ (D.rho_mem a)] }
  obtain ⟨hsimple, a, c, hac⟩ := isSimpleGroup_sl_zmod_two (m := 3) le_rfl
  have hker : φ.ker = ⊤ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple φ.ker (MonoidHom.normal_ker φ)
      with h | h
    · exfalso
      apply hac
      apply (MonoidHom.ker_eq_bot_iff φ).mp h
      rw [map_mul, map_mul, mul_comm]
    · exact h
  refine ⟨w, fun γ => ?_⟩
  have hγ : φ γ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_top γ
  have : f' γ = 1 := hγ
  simp only [hf'def] at this
  exact (mul_inv_eq_one.mp this)

end N1246

end CFSG.Quasithin.H13
