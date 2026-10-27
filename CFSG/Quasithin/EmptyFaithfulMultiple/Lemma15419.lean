module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements2
public import CFSG.Quasithin.Background.Equivariance
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G]

private theorem commutator_le_left_of_le_normalizer {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  have hk' : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hK hk) h⁻¹).mp (H.inv_mem hh)
  have e : h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) := by group
  rw [commutatorElement_def, e]
  exact H.mul_mem hh hk'

theorem eq_one_of_conj_eq_mul_of_odd_orderOf {x w d : G} (hx : Odd (orderOf x))
    (hxd : x * d = d * x) (hd : d * d = 1) (h : x * w * x⁻¹ = d * w) : d = 1 := by
  have key : ∀ k : ℕ, x ^ k * w * (x ^ k)⁻¹ = d ^ k * w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hxdk : x * d ^ k = d ^ k * x := ((Commute.pow_right hxd k) : _)
      calc x ^ (k + 1) * w * (x ^ (k + 1))⁻¹ = x * (x ^ k * w * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * d ^ k * w * x⁻¹ := by rw [ih]; group
        _ = d ^ k * (x * w * x⁻¹) := by rw [hxdk]; group
        _ = d ^ (k + 1) * w := by rw [h, pow_succ]; group
  have h1 := key (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h1
  obtain ⟨m, hm⟩ := hx
  rw [hm, pow_succ, pow_mul, sq, hd, one_pow, one_mul] at h1
  exact h1

theorem mem_centralizer_of_card_eq_four {W : Subgroup G} (hW : Nat.card W = 4)
    (hW2 : ∀ w ∈ W, w * w = 1) {x c : G} (hxW : x ∈ Subgroup.normalizer (W : Set G))
    (hx : Odd (orderOf x)) (hcW : c ∈ W) (hc1 : c ≠ 1) (hxc : x * c = c * x) :
    x ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  set H := Subgroup.zpowers c
  have hHC : H ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hxc
  have hHW : H ≤ W := Subgroup.zpowers_le.mpr hcW
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 c hcW) hc1
  have hH : Nat.card H = 2 := by rw [Nat.card_zpowers, hc2]
  have hidx : H.relIndex W = 2 := by
    have := Subgroup.relIndex_mul_relIndex ⊥ H W bot_le hHW
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hH, hW] at this
    omega
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_eq_two_iff.mp hidx
  have hcomm : ∀ y ∈ H, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hHC hy) x rfl)
  have hw' : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxW w).mp hw
  have hd : x * w * x⁻¹ * w⁻¹ ∈ H := by
    by_cases hwH : w ∈ H
    · have e : x * w * x⁻¹ * w⁻¹ = 1 := by rw [hcomm w hwH]; group
      rw [e]
      exact H.one_mem
    · have hw'H : x * w * x⁻¹ ∉ H := by
        intro h
        apply hwH
        have e : w = x⁻¹ * ((x * w * x⁻¹) * x) := by group
        rw [e, ← hcomm _ h, ← mul_assoc, inv_mul_cancel, one_mul]
        exact h
      have h1 : w * a ∈ H := by
        rcases ha w hw with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hwH
      have h2 : x * w * x⁻¹ * a ∈ H := by
        rcases ha _ hw' with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hw'H
      have e : x * w * x⁻¹ * w⁻¹ = (x * w * x⁻¹ * a) * (w * a)⁻¹ := by group
      rw [e]
      exact H.mul_mem h2 (H.inv_mem h1)
  have hdd := hW2 _ (W.mul_mem hw' (W.inv_mem hw))
  have h1 := eq_one_of_conj_eq_mul_of_odd_orderOf (w := w) hx (hcomm _ hd) hdd (by group)
  rw [mul_inv_eq_one] at h1
  calc w * x = x * w * x⁻¹ * x := by rw [h1]
    _ = x * w := by group

theorem commutator_inf_centralizer_eq_bot_of_card_eq_four {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hA : A = oTwoUpper A)
    (h4 : Nat.card (⁅V, A⁆ : Subgroup G) = 4) :
    ⁅V, A⁆ ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  rcases Subgroup.bot_or_exists_ne_one (⁅V, A⁆ ⊓ Subgroup.centralizer (A : Set G)) with h | h
  · exact h
  exfalso
  obtain ⟨c, ⟨hcW, hcA⟩, hc1⟩ := h
  set W := (⁅V, A⁆ : Subgroup G) with hWdef
  have hWV : W ≤ V := commutator_le_left_of_le_normalizer hAV
  have hW2 : ∀ w ∈ W, w * w = 1 := fun w hw => by rw [← sq]; exact hV.2 w (hWV hw)
  have hodd : ∀ x ∈ A, Odd (orderOf x) → x ∈ Subgroup.centralizer (V : Set G) := by
    intro x hxA hx
    have hxW : x ∈ Subgroup.normalizer (W : Set G) :=
      A4.mem_normalizer_commutator (hAV hxA) (Subgroup.le_normalizer hxA)
    have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcA x hxA
    have hxCW := mem_centralizer_of_card_eq_four h4 hW2 hxW hx hcW hc1 hxc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hdW : x * v * x⁻¹ * v⁻¹ ∈ W := by
      rw [hWdef, Subgroup.commutator_comm, ← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hxA hv
    have hxd : x * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * x :=
      (Subgroup.mem_centralizer_iff.mp hxCW _ hdW).symm
    have h1 := eq_one_of_conj_eq_mul_of_odd_orderOf (w := v) hx hxd (hW2 _ hdW) (by group)
    rw [mul_inv_eq_one] at h1
    calc v * x = x * v * x⁻¹ * x := by rw [h1]
      _ = x * v := by group
  have hAC : A ≤ Subgroup.centralizer (V : Set G) := by
    rw [hA]
    exact (Subgroup.closure_le _).mpr fun x hx => hodd x hx.1 hx.2
  have hbot : W = ⊥ := by
    rw [hWdef, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAC
  rw [hbot, Subgroup.card_bot] at h4
  omega

theorem mem_centralizer_of_card_eq_two {F : Subgroup G} (hF : Nat.card F = 2) {u : G}
    (hu : u ∈ Subgroup.normalizer (F : Set G)) : u ∈ Subgroup.centralizer (F : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  by_cases hf1 : f = 1
  · rw [hf1, one_mul, mul_one]
  have huf : u * f * u⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hu f).mp hf
  have huf1 : u * f * u⁻¹ ≠ 1 := fun h => hf1 (by
    calc f = u⁻¹ * (u * f * u⁻¹) * u := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  have e1 : (⟨u * f * u⁻¹, huf⟩ : F) = y := hy _ (fun h => huf1 (congrArg Subtype.val h))
  have e2 : (⟨f, hf⟩ : F) = y := hy _ (fun h => hf1 (congrArg Subtype.val h))
  have e : u * f * u⁻¹ = f := congrArg Subtype.val (e1.trans e2.symm)
  calc f * u = u * f * u⁻¹ * u := by rw [e]
    _ = u * f := by group

theorem exists_ne_one_mem_centralizer_of_isPGroup [Finite G] {S V : Subgroup G}
    (hS : IsPGroup 2 S) (hSV : S ≤ Subgroup.normalizer (V : Set G)) (hV : 2 ∣ Nat.card V) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S V :=
    { smul := fun s v => ⟨(s : G) * v * (s : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hSV s.2) v).mp v.2⟩
      one_smul := fun v => Subtype.ext (by
        change ((1 : S) : G) * (v : G) * ((1 : S) : G)⁻¹ = v
        simp)
      mul_smul := fun a b v => Subtype.ext (by
        change ((a * b : S) : G) * v * ((a * b : S) : G)⁻¹ =
          (a : G) * ((b : G) * v * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]) }
  have h1 : (1 : V) ∈ MulAction.fixedPoints S V := fun s => Subtype.ext (by
    change (s : G) * 1 * (s : G)⁻¹ = 1
    simp)
  obtain ⟨v, hv, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hV h1
  refine ⟨v, v.2, fun h => hne (Subtype.ext h.symm), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h : (s : G) * v * s⁻¹ = v := congrArg Subtype.val (hv ⟨s, hs⟩)
  exact mul_inv_eq_iff_eq_mul.mp h

end General

section SixTwo

variable {G : Type*} [Group G] {T M X X₁ X₂ : Subgroup G}

theorem IsSixTwoData.symm (h : IsSixTwoData T M X X₁ X₂) : IsSixTwoData T M X X₂ X₁ := by
  obtain ⟨hX, hO₁, hO₂, hi₁, hi₂, hVX, hVinf, hc₁, hc₂, hJ₁, hJ₂, hS₁, hS₂, ⟨t, ht, ht₂⟩, hidx,
    hN₁, hN₂⟩ := h
  refine ⟨hX.trans (sup_comm _ _), hO₂, hO₁, hi₂, hi₁, hVX.trans (sup_comm _ _),
    (inf_comm _ _).trans hVinf, hc₂,
    hc₁, hJ₂, hJ₁, hS₂, hS₁, ⟨t⁻¹, T.inv_mem ht, ?_⟩, hidx, hN₂, hN₁⟩
  rw [ht₂, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv]
  constructor
  · intro hx
    exact ⟨x, hx, by group⟩
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    group

theorem commutator_le_centralizer_of_sixTwoData (h : IsSixTwoData T M X X₁ X₂)
    (hXV : X ≤ Subgroup.normalizer (VZ T M : Set G)) :
    ⁅VZ T M, X₂⁆ ≤ Subgroup.centralizer (X₁ : Set G) := by
  obtain ⟨hX, -, -, -, -, -, hVinf, -, -, -, -, -, -, -, -, -, hN₂⟩ := h
  have hX₁X : X₁ ≤ X := hX ▸ le_sup_left
  have hX₂X : X₂ ≤ X := hX ▸ le_sup_right
  have hX₁N : X₁ ≤ Subgroup.normalizer ((⁅VZ T M, X₂⁆ : Subgroup G) : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hXV (hX₁X hx)) (hN₂ (hX₁X hx))
  have h1 : ⁅⁅VZ T M, X₂⁆, X₁⁆ ≤ ⁅VZ T M, X₂⁆ := commutator_le_left_of_le_normalizer hX₁N
  have h2 : ⁅⁅VZ T M, X₂⁆, X₁⁆ ≤ ⁅VZ T M, X₁⁆ :=
    Subgroup.commutator_mono (commutator_le_left_of_le_normalizer (hX₂X.trans hXV)) le_rfl
  have h3 : ⁅⁅VZ T M, X₂⁆, X₁⁆ = ⊥ := le_bot_iff.mp (hVinf ▸ le_inf h2 h1)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

theorem commutator_inf_centralizer_eq_bot_of_sixTwoData (hV : IsElemAbelian 2 (VZ T M))
    (hXV : X ≤ Subgroup.normalizer (VZ T M : Set G)) (h : IsSixTwoData T M X X₁ X₂) :
    ⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (X₁ : Set G) = ⊥ := by
  obtain ⟨hX, hO₁, -, -, -, -, -, hc₁, -⟩ := h
  exact commutator_inf_centralizer_eq_bot_of_card_eq_four hV ((hX ▸ le_sup_left).trans hXV) hO₁
    hc₁

theorem commutator_inf_centralizer_eq_of_sixTwoData (hV : IsElemAbelian 2 (VZ T M))
    (hXV : X ≤ Subgroup.normalizer (VZ T M : Set G)) (h : IsSixTwoData T M X X₁ X₂) :
    ⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (X₁ : Set G) = ⁅VZ T M, X₂⁆ := by
  have hfix := commutator_inf_centralizer_eq_bot_of_sixTwoData hV hXV h
  have hC := commutator_le_centralizer_of_sixTwoData h hXV
  obtain ⟨hX, -, -, -, -, hVX, -⟩ := h
  have hX₁X : X₁ ≤ X := hX ▸ le_sup_left
  have hX₂X : X₂ ≤ X := hX ▸ le_sup_right
  have hcomm := isMulCommutative_subgroup_iff.mp hV.1
  refine le_antisymm ?_ (le_inf (Subgroup.commutator_mono le_rfl hX₂X) hC)
  rintro v ⟨hv, hvC⟩
  have hN : ⁅VZ T M, X₂⁆ ≤ Subgroup.normalizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a (commutator_le_left_of_le_normalizer (hX₁X.trans hXV) ha) b
      (commutator_le_left_of_le_normalizer (hX₂X.trans hXV) hb)
  have hv' : v ∈ ((⁅VZ T M, X₁⁆ ⊔ ⁅VZ T M, X₂⁆ : Subgroup G) : Set G) := hVX ▸ hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hv'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hv'
  have haC : a ∈ Subgroup.centralizer (X₁ : Set G) := by
    have e : a = a * b * b⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hvC (Subgroup.inv_mem _ (hC hb))
  have ha1 : a = 1 := by
    have hmem : a ∈ ⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (X₁ : Set G) := ⟨ha, haC⟩
    rwa [hfix, Subgroup.mem_bot] at hmem
  rw [ha1, one_mul]
  exact hb

end SixTwo

section Fixed

variable {G : Type*} [Group G]

private theorem thompsonJ_le_self (T : Subgroup G) : thompsonJ T ≤ T :=
  iSup₂_le fun _ hA => hA.1

private theorem eOf_le_centerOf (T : Subgroup G) : eOf T ≤ centerOf (thompsonJ T) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

private theorem eOf_comm {T : Subgroup G} {a b : G} (ha : a ∈ eOf T) (hb : b ∈ eOf T) :
    a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp (eOf_le_centerOf T ha).2 b (eOf_le_centerOf T hb).1).symm

private theorem eOf_le_baum (T : Subgroup G) : eOf T ≤ baum T := fun _ he =>
  ⟨thompsonJ_le_self T (eOf_le_centerOf T he).1,
    Subgroup.mem_centralizer_iff.mpr fun _ hf => eOf_comm hf he⟩

variable {T M X X₁ X₂ : Subgroup G}

theorem card_commutator_inf_centralizer_baum_le_four
    (hE : eOf T = eCentOf T X ⊔ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)))
    (hEinf : eCentOf T X ⊓ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥)
    (hidx : (eCentOf T X).relIndex (eOf T) = 4) :
    Nat.card (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) ≤ 4 := by
  have hCE : ⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G) ≤ eOf T := hE ▸ le_sup_right
  have h1 := Subgroup.relIndex_le_of_le_right (H := eCentOf T X) hCE (by rw [hidx]; norm_num)
  rw [← Subgroup.inf_relIndex_right, hEinf, Subgroup.relIndex_bot_left, hidx] at h1
  exact h1

variable [Finite G]

private theorem omegaOneCenter_le_eOf (T : Subgroup G) : quasithinOmegaOneCenter T ≤ eOf T := by
  rw [eOf, ← (omegaOne_centralizer_thompsonJ T).1]
  refine Subgroup.closure_mono ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  exact ⟨⟨hzT, Subgroup.centralizer_le (thompsonJ_le_self T) hzC⟩, hz2⟩

private theorem relIndex_ne_zero_of_finite (H K : Subgroup G) : H.relIndex K ≠ 0 := fun h =>
  (Nat.card_pos (α := K)).ne' (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_card H K))

theorem card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData (hT : IsPGroup 2 T)
    (hTM : T ≤ M)
    (hE : eOf T = eCentOf T X ⊔ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)))
    (hEinf : eCentOf T X ⊓ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥)
    (h : IsSixTwoData T M X X₁ X₂) :
    Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) = 2 := by
  obtain ⟨hX, -, -, -, -, -, hVinf, hc₁, hc₂, -, -, hS₁, hS₂, -, hidx, -, -⟩ := h
  have hST : baum T ≤ T := inf_le_left
  have hS2 : IsPGroup 2 (baum T) := hT.to_le hST
  have hSV : baum T ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hST.trans (hTM.trans (le_normalizer_conjClosure _ _))
  have hne : ∀ A : Subgroup G, baum T ≤ Subgroup.normalizer (A : Set G) →
      Nat.card (⁅VZ T M, A⁆ : Subgroup G) = 4 →
      ⁅VZ T M, A⁆ ⊓ Subgroup.centralizer (baum T : Set G) ≠ ⊥ := by
    intro A hSA h4 hbot
    obtain ⟨c, hc, hc1, hcS⟩ := exists_ne_one_mem_centralizer_of_isPGroup hS2
      (fun s hs => A4.mem_normalizer_commutator (hSV hs) (hSA hs)) (by rw [h4]; norm_num)
    have hmem : c ∈ ⁅VZ T M, A⁆ ⊓ Subgroup.centralizer (baum T : Set G) := ⟨hc, hcS⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hC₁ := hne X₁ hS₁ hc₁
  have hC₂ := hne X₂ hS₂ hc₂
  have hC4 := card_commutator_inf_centralizer_baum_le_four hE hEinf hidx
  have hC₁C : ⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) ≤
      ⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G) :=
    inf_le_inf_right _ (Subgroup.commutator_mono le_rfl (hX ▸ le_sup_left))
  have hC₂C : ⁅VZ T M, X₂⁆ ⊓ Subgroup.centralizer (baum T : Set G) ≤
      ⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G) :=
    inf_le_inf_right _ (Subgroup.commutator_mono le_rfl (hX ▸ le_sup_right))
  have hdvd : Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) ∣
      4 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_left : ⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) ≤ ⁅VZ T M, X₁⁆)
    rwa [hc₁] at this
  have h1 : Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) ≠ 1 :=
    fun h => hC₁ (Subgroup.card_eq_one.mp h)
  have h4 : Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) ≠ 4 := by
    intro h4
    have heq := Subgroup.eq_of_le_of_card_ge hC₁C (by rw [h4]; exact hC4)
    apply hC₂
    rw [eq_bot_iff, ← hVinf]
    exact le_inf ((hC₂C.trans heq.ge).trans inf_le_left) inf_le_left
  have hle4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) :=
    Nat.card_pos
  interval_cases hn : Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G)
  · exact absurd rfl h1
  · rfl
  · norm_num at hdvd
  · exact absurd rfl h4

theorem relIndex_eOf_inf_centralizer_le_two_of_sixTwoData (hT : IsPGroup 2 T) (hTM : T ≤ M)
    (hXM : X ≤ M)
    (hE : eOf T = eCentOf T X ⊔ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)))
    (hEinf : eCentOf T X ⊓ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥)
    (h : IsSixTwoData T M X X₁ X₂) :
    (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)).relIndex (eOf T) ≤ 2 := by
  have hXV : X ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hXM.trans (le_normalizer_conjClosure _ _)
  have hcard₂ := card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData hT hTM hE hEinf h.symm
  have hC₂X₁ := commutator_le_centralizer_of_sixTwoData h hXV
  obtain ⟨hX, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, -, -⟩ := h
  set EX := eCentOf T X
  set C := ⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)
  set C₂ := ⁅VZ T M, X₂⁆ ⊓ Subgroup.centralizer (baum T : Set G)
  have hC₂ne : C₂ ≠ ⊥ := fun hb => by rw [hb, Subgroup.card_bot] at hcard₂; omega
  have hEXE : EX ≤ eOf T := hE ▸ le_sup_left
  have hCE : C ≤ eOf T := hE ▸ le_sup_right
  have hC₂C : C₂ ≤ C := inf_le_inf_right _ (Subgroup.commutator_mono le_rfl (hX ▸ le_sup_right))
  have hEXC : EX ≤ Subgroup.centralizer (X₁ : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (hX ▸ le_sup_left : X₁ ≤ X))
  have hle : EX ⊔ C₂ ≤ eOf T ⊓ Subgroup.centralizer (X₁ : Set G) :=
    sup_le (le_inf hEXE hEXC) (le_inf (hC₂C.trans hCE) (inf_le_left.trans hC₂X₁))
  have hk1 : EX.relIndex (EX ⊔ C₂) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle'
    apply hC₂ne
    rw [eq_bot_iff, ← hEinf]
    exact le_inf (le_sup_right.trans hle') hC₂C
  have hk0 := relIndex_ne_zero_of_finite EX (EX ⊔ C₂)
  have htower := Subgroup.relIndex_mul_relIndex EX (EX ⊔ C₂) (eOf T) le_sup_left
    (hle.trans inf_le_left)
  rw [hidx] at htower
  have hm : (EX ⊔ C₂).relIndex (eOf T) ≤ 2 := by
    have h2 : 2 * (EX ⊔ C₂).relIndex (eOf T) ≤ EX.relIndex (EX ⊔ C₂) * (EX ⊔ C₂).relIndex (eOf T) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  exact (Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero_of_finite _ _)).trans hm

theorem e_eq_centralizer_sup_of_sixTwoData (hT : IsPGroup 2 T) (hTM : T ≤ M) (hXM : X ≤ M)
    (hV : IsElemAbelian 2 (VZ T M))
    (hE : eOf T = eCentOf T X ⊔ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)))
    (hEinf : eCentOf T X ⊓ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥)
    (h : IsSixTwoData T M X X₁ X₂) :
    eOf T = (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)) ⊔
        (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)) ∧
      (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)) ⊓
        (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥ ∧
      Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) = 2 := by
  have hXV : X ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hXM.trans (le_normalizer_conjClosure _ _)
  have hcard := card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData hT hTM hE hEinf h
  have hfix := commutator_inf_centralizer_eq_bot_of_sixTwoData hV hXV h
  have hH2 := relIndex_eOf_inf_centralizer_le_two_of_sixTwoData hT hTM hXM hE hEinf h
  set H := eOf T ⊓ Subgroup.centralizer (X₁ : Set G)
  set C₁ := ⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)
  have hC₁ne : C₁ ≠ ⊥ := fun hb => by rw [hb, Subgroup.card_bot] at hcard; omega
  have hinf : H ⊓ C₁ = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    exact le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_right)
  have hC₁E : C₁ ≤ eOf T :=
    (inf_le_inf_right _ (Subgroup.commutator_mono le_rfl (h.1 ▸ le_sup_left))).trans
      (hE ▸ le_sup_right)
  have hk1 : H.relIndex (H ⊔ C₁) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    apply hC₁ne
    rw [eq_bot_iff, ← hinf]
    exact le_inf (le_sup_right.trans hle) le_rfl
  have hk0 := relIndex_ne_zero_of_finite H (H ⊔ C₁)
  have htower := Subgroup.relIndex_mul_relIndex H (H ⊔ C₁) (eOf T) le_sup_left
    (sup_le inf_le_left hC₁E)
  have h1 : (H ⊔ C₁).relIndex (eOf T) = 1 := by
    have hk := relIndex_ne_zero_of_finite (H ⊔ C₁) (eOf T)
    by_contra hne
    have h2 : 2 * 2 ≤ H.relIndex (H ⊔ C₁) * (H ⊔ C₁).relIndex (eOf T) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  exact ⟨le_antisymm (Subgroup.relIndex_eq_one.mp h1) (sup_le inf_le_left hC₁E), hinf, hcard⟩

theorem relIndex_eOf_inf_centralizer_eq_two_of_sixTwoData (hT : IsPGroup 2 T) (hTM : T ≤ M)
    (hXM : X ≤ M) (hV : IsElemAbelian 2 (VZ T M))
    (hE : eOf T = eCentOf T X ⊔ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)))
    (hEinf : eCentOf T X ⊓ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥)
    (h : IsSixTwoData T M X X₁ X₂) :
    (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)).relIndex (eOf T) = 2 := by
  obtain ⟨hsup, hinf, hcard⟩ := e_eq_centralizer_sup_of_sixTwoData hT hTM hXM hV hE hEinf h
  have hH2 := relIndex_eOf_inf_centralizer_le_two_of_sixTwoData hT hTM hXM hE hEinf h
  have h0 := relIndex_ne_zero_of_finite (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)) (eOf T)
  have h1 : (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)).relIndex (eOf T) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    have hC : ⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact le_inf ((le_sup_right.trans hsup.ge).trans hle) le_rfl
    rw [hC, Subgroup.card_bot] at hcard
    omega
  omega

omit [Finite G] in
theorem omegaOneCenter_inf_commutator_eq_bot_of_sixTwoData (hTM : T ≤ M)
    (h : IsSixTwoData T M X X₁ X₂) : quasithinOmegaOneCenter T ⊓ ⁅VZ T M, X₁⁆ = ⊥ := by
  obtain ⟨-, -, -, -, -, -, hVinf, -, -, -, -, -, -, ⟨t, ht, ht₂⟩, -, -, -⟩ := h
  have htV : t ∈ Subgroup.normalizer (VZ T M : Set G) :=
    hTM.trans (le_normalizer_conjClosure _ _) ht
  have hmap : (⁅VZ T M, X₁⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom = ⁅VZ T M, X₂⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer htV, ← ht₂]
  rw [eq_bot_iff, ← hVinf]
  rintro z ⟨hzZ, hzV⟩
  refine ⟨hzV, ?_⟩
  have hzC : z ∈ Subgroup.centralizer (T : Set G) :=
    ((Subgroup.closure_le _).mpr fun _ hw => hw.1 :
      quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G)) hzZ |>.2
  have htz : t * z * t⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzC t ht, mul_inv_cancel_right]
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hzV
  rw [hmap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htz] at hmem
  exact hmem

theorem le_centralizer_commutator_inf_centralizer_baum_of_sixTwoData (hT : IsPGroup 2 T)
    (hTM : T ≤ M) (hXM : X ≤ M) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hV : IsElemAbelian 2 (VZ T M))
    (hE : eOf T = eCentOf T X ⊔ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)))
    (hEinf : eCentOf T X ⊓ (⁅VZ T M, X⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥)
    (h : IsSixTwoData T M X X₁ X₂) :
    T ⊓ Subgroup.normalizer (X₁ : Set G) ≤
        Subgroup.centralizer
          ((⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) : Set G) ∧
      T ⊓ Subgroup.normalizer (X₁ : Set G) ≤
        Subgroup.centralizer
          ((⁅VZ T M, X₂⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) : Set G) := by
  have hXV : X ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hXM.trans (le_normalizer_conjClosure _ _)
  have hcard₁ := card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData hT hTM hE hEinf h
  have hcard₂ := card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData hT hTM hE hEinf h.symm
  have hV₂ := commutator_inf_centralizer_eq_of_sixTwoData hV hXV h
  have key : ∀ u ∈ T ⊓ Subgroup.normalizer (X₁ : Set G),
      u ∈ Subgroup.normalizer (Subgroup.centralizer (baum T : Set G) : Set G) ∧
        u ∈ Subgroup.normalizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) ∧
        u ∈ Subgroup.normalizer ((⁅VZ T M, X₂⁆ : Subgroup G) : Set G) := by
    intro u hu
    have huV : u ∈ Subgroup.normalizer (VZ T M : Set G) :=
      hTM.trans (le_normalizer_conjClosure _ _) hu.1
    have huS : u ∈ Subgroup.normalizer (baum T : Set G) :=
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)) hu.1
    have huC₁ : u ∈ Subgroup.normalizer (Subgroup.centralizer (X₁ : Set G) : Set G) :=
      normalizer_le_normalizer_of_map_mulEquiv
        (F := fun Y => Subgroup.centralizer (Y : Set G)) centralizer_map_mulEquiv X₁ hu.2
    refine ⟨normalizer_le_normalizer_of_map_mulEquiv
      (F := fun Y => Subgroup.centralizer (Y : Set G)) centralizer_map_mulEquiv _ huS,
      A4.mem_normalizer_commutator huV hu.2, ?_⟩
    rw [← hV₂]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨A4.mem_normalizer_commutator huV (hTX hu.1), huC₁⟩
  refine ⟨fun u hu => mem_centralizer_of_card_eq_two hcard₁ ?_,
    fun u hu => mem_centralizer_of_card_eq_two hcard₂ ?_⟩
  · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨(key u hu).2.1, (key u hu).1⟩
  · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨(key u hu).2.2, (key u hu).1⟩

end Fixed

theorem isElemAbelian_VZ_of_inM {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (hM : InM T M) : IsElemAbelian 2 (VZ T M) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hM.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hyp.qtke.2.1 M hM.1.1 ⟨S, hSM⟩
  exact (conjClosure_le_centerOf_pCoreOf M S hSM hF (Z := quasithinOmegaOneCenter T)
    (by rw [hS])).2

theorem e_eq_centralizer_sup_of_stmt15412 {G : Type} [Group G] [Finite G]
    {T M X X₁ X₂ : Subgroup G} (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (hM : InM T M) (hX : IsYFamily T X) (hXM : X ≤ M) (h : IsSixTwoData T M X X₁ X₂) :
    eOf T = (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)) ⊔
        (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)) ∧
      (eOf T ⊓ Subgroup.centralizer (X₁ : Set G)) ⊓
        (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥ ∧
      Nat.card (⁅VZ T M, X₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) = 2 := by
  obtain ⟨-, -, -, -, -, ⟨-, -, hE, hEinf⟩, -, -⟩ := (h12 M hM).2 X hX hXM
  exact e_eq_centralizer_sup_of_sixTwoData hyp.sylow.1 hM.2 hXM (isElemAbelian_VZ_of_inM hyp hM)
    hE hEinf h

theorem not_le_of_sixTwoData {G : Type*} [Group G] {T M M' W W₁ W₂ L : Subgroup G}
    (hM : InM T M) (hne : M ≠ M') (hU : IsUniqueM (W ⊔ T) M')
    (hd : IsSixTwoData T M' W W₁ W₂) (hL : L = W₁ ∨ L = W₂) : ¬ L ≤ M := by
  intro hLM
  obtain ⟨hW, -, -, -, -, -, -, -, -, -, -, -, -, ⟨t, ht, ht₂⟩, -, -, -⟩ := hd
  have htM : t ∈ M := hM.2 ht
  have hW₁ : W₁ ≤ M := by
    rcases hL with rfl | rfl
    · exact hLM
    · intro w hw
      have hw' : t * w * t⁻¹ ∈ M := hLM (by rw [ht₂]; exact ⟨w, hw, rfl⟩)
      have e : w = t⁻¹ * (t * w * t⁻¹) * t := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem htM) hw') htM
  have hW₂ : W₂ ≤ M := by
    rw [ht₂]
    rintro _ ⟨w, hw, rfl⟩
    exact M.mul_mem (M.mul_mem htM (hW₁ hw)) (M.inv_mem htM)
  exact hne (hU.2 M ⟨hM.1, sup_le (hW ▸ sup_le hW₁ hW₂) hM.2⟩)

theorem stmt15419_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (hnot : ¬ IsLThreeTwoOrASix G)
    (h8 : Stmt1548 G T) (h12 : Stmt15412 G T) (h14 : Stmt15414 G T) : Stmt15419 G T := by
  intro s
  have hT : IsPGroup 2 T := hyp.sylow.1
  have hZ4 : Nat.card (quasithinOmegaOneCenter T) = 4 := (h14 hnot).2
  obtain ⟨hM₁X, -, hU₁, -, -, ⟨-, -, hE₁, hE₁inf⟩, -, -⟩ := (h12 s.M₁ s.inM₁).2 s.X s.famX s.le_X
  obtain ⟨-, -, hU₂, -, -, ⟨-, -, hE₂, hE₂inf⟩, -, -⟩ := (h12 s.M₂ s.inM₂).2 s.Y s.famY s.le_Y
  have hTM₁ : T ≤ s.M₁ := s.inM₁.2
  have hTM₂ : T ≤ s.M₂ := s.inM₂.2
  have hV₁ab := isElemAbelian_VZ_of_inM hyp s.inM₁
  have hTX : T ≤ Subgroup.normalizer (s.X : Set G) := hTM₁.trans hM₁X
  obtain ⟨B₁, hd₁⟩ : ∃ B, IsSixTwoData T s.M₁ s.X s.L₁ B := by
    rcases s.choice₁ with h | h
    · exact ⟨s.X₂, by rw [h]; exact s.dataX⟩
    · exact ⟨s.X₁, by rw [h]; exact s.dataX.symm⟩
  obtain ⟨B₂, hd₂⟩ : ∃ B, IsSixTwoData T s.M₂ s.Y s.L₂ B := by
    rcases s.choice₂ with h | h
    · exact ⟨s.Y₂, by rw [h]; exact s.dataY⟩
    · exact ⟨s.Y₁, by rw [h]; exact s.dataY.symm⟩
  have hT₀F₁ : s.T₀ ≤ Subgroup.centralizer
      ((⁅VZ T s.M₁, s.L₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) : Subgroup G) : Set G) := by
    have hT₀ : s.T₀ ≤ T ⊓ Subgroup.normalizer (s.X₁ : Set G) := fun u hu => ⟨hu.1.1, hu.2⟩
    obtain ⟨c₁, c₂⟩ := le_centralizer_commutator_inf_centralizer_baum_of_sixTwoData hT hTM₁ s.le_X
      hTX hV₁ab hE₁ hE₁inf s.dataX
    rcases s.choice₁ with h | h
    · rw [h]
      exact hT₀.trans c₁
    · rw [h]
      exact hT₀.trans c₂
  have hrel₁ := relIndex_eOf_inf_centralizer_le_two_of_sixTwoData hT hTM₁ s.le_X hE₁ hE₁inf hd₁
  have hrel₂ := relIndex_eOf_inf_centralizer_le_two_of_sixTwoData hT hTM₂ s.le_Y hE₂ hE₂inf hd₂
  have hfix := commutator_inf_centralizer_eq_bot_of_sixTwoData hV₁ab
    (s.le_X.trans (le_normalizer_conjClosure _ _)) hd₁
  have hcard := card_commutator_inf_centralizer_baum_eq_two_of_sixTwoData hT hTM₁ hE₁ hE₁inf hd₁
  have hZV := omegaOneCenter_inf_commutator_eq_bot_of_sixTwoData hTM₁ hd₁
  have hF₁E : ⁅VZ T s.M₁, s.L₁⁆ ⊓ Subgroup.centralizer (baum T : Set G) ≤ eOf T :=
    (inf_le_inf_right _ (Subgroup.commutator_mono le_rfl (hd₁.1 ▸ le_sup_left))).trans
      (hE₁ ▸ le_sup_right)
  have hS₀ : baum T ≤ s.T₀ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSY, -⟩ := s.dataY
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSX, -⟩ := s.dataX
    exact le_inf (le_inf inf_le_left hSY) hSX
  have hL₂ : ¬ s.L₂ ≤ s.M₁ := not_le_of_sixTwoData s.inM₁ s.ne hU₂ s.dataY s.choice₂
  have hL₁ : ¬ s.L₁ ≤ s.M₂ := not_le_of_sixTwoData s.inM₂ s.ne.symm hU₁ s.dataX s.choice₁
  set EI := eOf T ⊓ Subgroup.centralizer (s.T₀ : Set G)
  set E₀ := EI ⊓ (Subgroup.centralizer (s.L₁ : Set G) ⊓ Subgroup.centralizer (s.L₂ : Set G))
    with hE₀
  set F₁ := ⁅VZ T s.M₁, s.L₁⁆ ⊓ Subgroup.centralizer (baum T : Set G)
  have hrel : ∀ L : Subgroup G, (eOf T ⊓ Subgroup.centralizer (L : Set G)).relIndex (eOf T) ≤ 2 →
      (Subgroup.centralizer (L : Set G)).relIndex EI ≤ 2 := by
    intro L hL
    rw [Subgroup.inf_relIndex_left] at hL
    exact (Subgroup.relIndex_le_of_le_right inf_le_left (relIndex_ne_zero_of_finite _ _)).trans hL
  have hE₀I : E₀.relIndex EI ≤ 4 := by
    rw [hE₀, Subgroup.inf_relIndex_left]
    exact Subgroup.relIndex_inf_le.trans (Nat.mul_le_mul (hrel _ hrel₁) (hrel _ hrel₂))
  have hF₁I : F₁ ≤ EI := le_inf hF₁E (Subgroup.le_centralizer_iff.mp hT₀F₁)
  have hF₁ne : F₁ ≠ ⊥ := fun hb => by rw [hb, Subgroup.card_bot] at hcard; omega
  have hF₁E₀ : F₁ ⊓ E₀ = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    exact le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have hk1 : E₀.relIndex (E₀ ⊔ F₁) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    apply hF₁ne
    rw [eq_bot_iff, ← hF₁E₀]
    exact le_inf le_rfl (le_sup_right.trans hle)
  have hk0 := relIndex_ne_zero_of_finite E₀ (E₀ ⊔ F₁)
  have htower := Subgroup.relIndex_mul_relIndex E₀ (E₀ ⊔ F₁) EI le_sup_left
    (sup_le inf_le_left hF₁I)
  have hH2 : (E₀ ⊔ F₁).relIndex EI ≤ 2 := by
    have h2 : 2 * (E₀ ⊔ F₁).relIndex EI ≤ E₀.relIndex (E₀ ⊔ F₁) * (E₀ ⊔ F₁).relIndex EI :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hZI : quasithinOmegaOneCenter T ≤ EI :=
    le_inf (omegaOneCenter_le_eOf T)
      (Subgroup.le_centralizer_iff.mp ((inf_le_left.trans inf_le_left).trans h8.ge))
  have hZH : quasithinOmegaOneCenter T ⊓ (E₀ ⊔ F₁) ≠ ⊥ := by
    intro hbot
    have h1 : (quasithinOmegaOneCenter T ⊓ (E₀ ⊔ F₁)).relIndex (quasithinOmegaOneCenter T) ≤ 2 := by
      rw [Subgroup.inf_relIndex_left]
      exact (Subgroup.relIndex_le_of_le_right hZI (relIndex_ne_zero_of_finite _ _)).trans hH2
    rw [hbot, Subgroup.relIndex_bot_left, hZ4] at h1
    omega
  have hE₀C : E₀ ≤ eOf T ⊓ Subgroup.centralizer (s.I : Set G) := by
    refine le_inf (inf_le_left.trans inf_le_left) (Subgroup.le_centralizer_iff.mpr ?_)
    have h₁ : s.L₁ ≤ Subgroup.centralizer (E₀ : Set G) :=
      Subgroup.le_centralizer_iff.mp (inf_le_right.trans inf_le_left)
    have h₂ : s.L₂ ≤ Subgroup.centralizer (E₀ : Set G) :=
      Subgroup.le_centralizer_iff.mp (inf_le_right.trans inf_le_right)
    have h₀ : s.T₀ ≤ Subgroup.centralizer (E₀ : Set G) :=
      Subgroup.le_centralizer_iff.mp (inf_le_left.trans inf_le_right)
    exact sup_le (sup_le h₁ h₀) (sup_le h₂ h₀)
  have hE₀ne : E₀ ≠ ⊥ := by
    intro hbot
    apply hZH
    rw [hbot, bot_sup_eq, eq_bot_iff, ← hZV]
    exact inf_le_inf_left _ inf_le_left
  have hCne : eOf T ⊓ Subgroup.centralizer (s.I : Set G) ≠ ⊥ := fun hb =>
    hE₀ne (le_bot_iff.mp (hb ▸ hE₀C))
  have hCI : eOf T ⊓ Subgroup.centralizer (s.I : Set G) ≤ s.I :=
    inf_le_left.trans ((eOf_le_baum T).trans (hS₀.trans (le_sup_right.trans le_sup_left)))
  have hCcen : eOf T ⊓ Subgroup.centralizer (s.I : Set G) ≤ centerOf s.I := le_inf hCI inf_le_right
  refine ⟨hCne, hCcen, ?_, hL₂, hL₁, ?_⟩
  ·
    intro hbot
    apply hCne
    rw [eq_bot_iff, ← hbot]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCI ?_
      (hT.to_le (inf_le_left.trans ((eOf_le_baum T).trans inf_le_left)))
    exact (Subgroup.le_centralizer_iff.mp inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)
  · intro hbot
    apply hZH
    rw [eq_bot_iff, ← hbot]
    exact inf_le_inf_left _ (sup_le_sup (hE₀C.trans hCcen) inf_le_left)

end CFSG.Quasithin.EmptyFaithfulMultiple
