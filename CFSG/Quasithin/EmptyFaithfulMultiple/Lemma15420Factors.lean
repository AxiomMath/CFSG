module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15419
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem commutator_le_of_le_normalizer {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  have hk' : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hK hk) h⁻¹).mp (H.inv_mem hh)
  have e : h * k * h⁻¹ * k⁻¹ = h * (k * h⁻¹ * k⁻¹) := by group
  rw [commutatorElement_def, e]
  exact H.mul_mem hh hk'

theorem mul_comm_of_sq_eq_one {U : Subgroup G} (hU2 : ∀ u ∈ U, u * u = 1) {a b : G}
    (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a := by
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hU2 _ (U.mul_mem ha hb))
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hU2 _ ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hU2 _ hb)
  rw [← hab, mul_inv_rev, ha', hb']

theorem le_commutator_of_card_eq_four [Finite G] {U V W : Subgroup G} (hU : Nat.card U = 4)
    (hU2 : ∀ u ∈ U, u * u = 1) (hUV : U ≤ V) {w : G} (hw : w ∈ W) (hodd : Odd (orderOf w))
    (hwN : w ∈ Subgroup.normalizer (U : Set G)) (hwC : w ∉ Subgroup.centralizer (U : Set G)) :
    U ≤ ⁅V, W⁆ := by
  have hmem : ∀ u : U, (u : G) * w * (u : G)⁻¹ * w⁻¹ ∈ U := by
    intro u
    have h1 : w * (u : G)⁻¹ * w⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hwN _).mp (U.inv_mem u.2)
    have e : (u : G) * w * (u : G)⁻¹ * w⁻¹ = u * (w * (u : G)⁻¹ * w⁻¹) := by group
    rw [e]
    exact U.mul_mem u.2 h1
  let f : U → U := fun u => ⟨(u : G) * w * (u : G)⁻¹ * w⁻¹, hmem u⟩
  have hinj : Function.Injective f := by
    intro u u' huu
    have h : (u : G) * w * (u : G)⁻¹ * w⁻¹ = (u' : G) * w * (u' : G)⁻¹ * w⁻¹ :=
      congrArg Subtype.val huu
    by_contra hne
    have hc1 : (u' : G)⁻¹ * u ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      calc (u : G) = u' * ((u' : G)⁻¹ * u) := by group
        _ = u' := by rw [h1, mul_one]
    have hcU : (u' : G)⁻¹ * u ∈ U := U.mul_mem (U.inv_mem u'.2) u.2
    have h2 : (u : G) * w * (u : G)⁻¹ = (u' : G) * w * (u' : G)⁻¹ := by
      simpa using congrArg (· * w) h
    have hcomm : w * ((u' : G)⁻¹ * u) = ((u' : G)⁻¹ * u) * w := by
      calc w * ((u' : G)⁻¹ * u) = (u' : G)⁻¹ * ((u' : G) * w * (u' : G)⁻¹) * u := by group
        _ = (u' : G)⁻¹ * ((u : G) * w * (u : G)⁻¹) * u := by rw [h2]
        _ = ((u' : G)⁻¹ * u) * w := by group
    exact hwC (mem_centralizer_of_card_eq_four hU hU2 hwN hodd hcU hc1 hcomm)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro x hx
  obtain ⟨u, hu⟩ := hsurj ⟨x, hx⟩
  have hx' : x = (u : G) * w * (u : G)⁻¹ * w⁻¹ := (congrArg Subtype.val hu).symm
  rw [hx', ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (hUV u.2) hw

theorem inf_centralizer_commutator_le_pCoreOf [Finite G] {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hA : A = oTwoUpper A)
    (hi : (pCoreOf 2 A).relIndex A = 3) (h4 : Nat.card (⁅V, A⁆ : Subgroup G) = 4) :
    A ⊓ Subgroup.centralizer ((⁅V, A⁆ : Subgroup G) : Set G) ≤ pCoreOf 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := (⁅V, A⁆ : Subgroup G) with hWdef
  set Q := pCoreOf 2 A with hQdef
  set C := A ⊓ Subgroup.centralizer (W : Set G) with hCdef
  have hWV : W ≤ V := commutator_le_of_le_normalizer hAV
  have hW2 : ∀ w ∈ W, w * w = 1 := fun w hw => by rw [← sq]; exact hV.2 w (hWV hw)
  have hQA : Q ≤ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    A4.mem_normalizer_commutator (hAV ha) (Subgroup.le_normalizer ha)
  by_contra hle
  have hB : A ≤ Q ⊔ C := by
    have hQB : Q ≤ Q ⊔ C := le_sup_left
    have hBA : Q ⊔ C ≤ A := sup_le hQA inf_le_left
    have hm := Subgroup.relIndex_mul_relIndex Q (Q ⊔ C) A hQB hBA
    rw [hi] at hm
    have hdvd : Q.relIndex (Q ⊔ C) ∣ 3 := Dvd.intro _ hm
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd) with h1 | h3
    · exfalso
      apply hle
      have : Q ⊔ C ≤ Q := Subgroup.relIndex_eq_one.mp h1
      exact le_sup_right.trans this
    · rw [h3] at hm
      have h1 : (Q ⊔ C).relIndex A = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp h1
  have hodd : ∀ x ∈ A, Odd (orderOf x) → x ∈ Subgroup.centralizer (W : Set G) := by
    intro x hxA hx
    have hxB : x ∈ ((Q ⊔ C : Subgroup G) : Set G) := hB hxA
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q C (inf_le_left.trans hAQ)] at hxB
    obtain ⟨q, hq, c, hc, rfl⟩ := Set.mem_mul.mp hxB
    have hqA : q ∈ A := hQA hq
    have hqW : Subgroup.zpowers q ≤ Subgroup.normalizer (W : Set G) :=
      (Subgroup.zpowers_le).mpr (hAW hqA)
    have hcard : 2 ∣ Nat.card W := by rw [h4]; norm_num
    obtain ⟨w₀, hw₀, hw₀1, hw₀C⟩ :=
      exists_ne_one_mem_centralizer_of_isPGroup (hQ2.to_le (Subgroup.zpowers_le.mpr hq)) hqW hcard
    have hqw : q * w₀ = w₀ * q :=
      Subgroup.mem_centralizer_iff.mp hw₀C q (Subgroup.mem_zpowers q)
    have hcw : c * w₀ = w₀ * c := (Subgroup.mem_centralizer_iff.mp hc.2 w₀ hw₀).symm
    have hxw : q * c * w₀ = w₀ * (q * c) := by
      rw [mul_assoc, hcw, ← mul_assoc, hqw, mul_assoc]
    exact mem_centralizer_of_card_eq_four h4 hW2 (hAW hxA) hx hw₀ hw₀1 hxw
  have hAC : A ≤ Subgroup.centralizer (W : Set G) := by
    rw [hA]
    exact (Subgroup.closure_le _).mpr fun x hx => hodd x hx.1 hx.2
  have hbot := commutator_inf_centralizer_eq_bot_of_card_eq_four hV hAV hA h4
  rw [← hWdef, inf_eq_left.mpr (Subgroup.le_centralizer_iff.mp hAC)] at hbot
  rw [hbot, Subgroup.card_bot] at h4
  omega


theorem mem_of_odd_of_mem_centralizer [Finite G] {V X₁ X₂ : Subgroup G}
    (hV : IsElemAbelian 2 V) (hX₂V : X₂ ≤ Subgroup.normalizer (V : Set G))
    (hO₁ : X₁ = oTwoUpper X₁) (hO₂ : X₂ = oTwoUpper X₂)
    (hi₂ : (pCoreOf 2 X₂).relIndex X₂ = 3) (hc₂ : Nat.card (⁅V, X₂⁆ : Subgroup G) = 4)
    (hN : X₂ ≤ Subgroup.normalizer (X₁ : Set G))
    (hC : X₁ ≤ Subgroup.centralizer ((⁅V, X₂⁆ : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ X₁ ⊔ X₂) (hyo : Odd (orderOf y))
    (hyC : y ∈ Subgroup.centralizer ((⁅V, X₂⁆ : Subgroup G) : Set G)) : y ∈ X₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy' : y ∈ ((X₁ ⊔ X₂ : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X₁ X₂ hN] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hy'
  have hbC : b ∈ Subgroup.centralizer ((⁅V, X₂⁆ : Subgroup G) : Set G) := by
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hC ha)) hyC
  have hbQ : b ∈ pCoreOf 2 X₂ :=
    inf_centralizer_commutator_le_pCoreOf hV hX₂V hO₂ hi₂ hc₂ ⟨hb, hbC⟩
  have hQN : pCoreOf 2 X₂ ≤ Subgroup.normalizer (X₁ : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 X₂).trans hN
  have hO := Ch1Sec3.oTwoUpper_sup_eq_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X₂) hQN hO₁
  have hmem : a * b ∈ pCoreOf 2 X₂ ⊔ X₁ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hbQ)
  rw [← hO]
  exact mem_oTwoUpper_of_odd hmem hyo

theorem le_or_le_of_card_commutator_eq_four [Finite G] {V X X₁ X₂ W : Subgroup G}
    (hV : IsElemAbelian 2 V) (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hX : X = X₁ ⊔ X₂)
    (hO₁ : X₁ = oTwoUpper X₁) (hO₂ : X₂ = oTwoUpper X₂)
    (hi₁ : (pCoreOf 2 X₁).relIndex X₁ = 3) (hi₂ : (pCoreOf 2 X₂).relIndex X₂ = 3)
    (hVinf : ⁅V, X₁⁆ ⊓ ⁅V, X₂⁆ = ⊥) (hc₁ : Nat.card (⁅V, X₁⁆ : Subgroup G) = 4)
    (hc₂ : Nat.card (⁅V, X₂⁆ : Subgroup G) = 4)
    (hN₁ : X ≤ Subgroup.normalizer (X₁ : Set G)) (hN₂ : X ≤ Subgroup.normalizer (X₂ : Set G))
    (hWX : W ≤ X) (hW : W = oTwoUpper W) (hW4 : Nat.card (⁅V, W⁆ : Subgroup G) = 4) :
    W ≤ X₁ ∨ W ≤ X₂ := by
  have hX₁X : X₁ ≤ X := hX ▸ le_sup_left
  have hX₂X : X₂ ≤ X := hX ▸ le_sup_right
  set V₁ := (⁅V, X₁⁆ : Subgroup G) with hV₁def
  set V₂ := (⁅V, X₂⁆ : Subgroup G) with hV₂def
  have hV₁V : V₁ ≤ V := commutator_le_of_le_normalizer (hX₁X.trans hXV)
  have hV₂V : V₂ ≤ V := commutator_le_of_le_normalizer (hX₂X.trans hXV)
  have hV₁2 : ∀ v ∈ V₁, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v (hV₁V hv)
  have hV₂2 : ∀ v ∈ V₂, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v (hV₂V hv)
  have hXN₁ : X ≤ Subgroup.normalizer (V₁ : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hXV hx) (hN₁ hx)
  have hXN₂ : X ≤ Subgroup.normalizer (V₂ : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hXV hx) (hN₂ hx)
  have hC₁ : X₁ ≤ Subgroup.centralizer (V₂ : Set G) := by
    have h1 : ⁅V₂, X₁⁆ ≤ V₂ := commutator_le_of_le_normalizer (hX₁X.trans hXN₂)
    have h2 : ⁅V₂, X₁⁆ ≤ V₁ := Subgroup.commutator_mono hV₂V le_rfl
    have h3 : ⁅V₂, X₁⁆ = ⊥ := le_bot_iff.mp (hVinf ▸ le_inf h2 h1)
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  have hC₂ : X₂ ≤ Subgroup.centralizer (V₁ : Set G) := by
    have h1 : ⁅V₁, X₂⁆ ≤ V₁ := commutator_le_of_le_normalizer (hX₂X.trans hXN₁)
    have h2 : ⁅V₁, X₂⁆ ≤ V₂ := Subgroup.commutator_mono hV₁V le_rfl
    have h3 : ⁅V₁, X₂⁆ = ⊥ := le_bot_iff.mp (hVinf ▸ le_inf h1 h2)
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  have key : (∀ w ∈ W, Odd (orderOf w) → w ∈ Subgroup.centralizer (V₂ : Set G)) ∨
      (∀ w ∈ W, Odd (orderOf w) → w ∈ Subgroup.centralizer (V₁ : Set G)) := by
    by_contra h
    push Not at h
    obtain ⟨⟨w, hw, hwo, hwC⟩, ⟨w', hw', hwo', hwC'⟩⟩ := h
    have h2 : V₂ ≤ ⁅V, W⁆ :=
      le_commutator_of_card_eq_four hc₂ hV₂2 hV₂V hw hwo (hXN₂ (hWX hw)) hwC
    have h1 : V₁ ≤ ⁅V, W⁆ :=
      le_commutator_of_card_eq_four hc₁ hV₁2 hV₁V hw' hwo' (hXN₁ (hWX hw')) hwC'
    have e2 : V₂ = ⁅V, W⁆ := Subgroup.eq_of_le_of_card_ge h2 (by rw [hW4, hc₂])
    have e1 : V₁ = ⁅V, W⁆ := Subgroup.eq_of_le_of_card_ge h1 (by rw [hW4, hc₁])
    have e : V₁ = V₂ := e1.trans e2.symm
    rw [e, inf_idem] at hVinf
    rw [hVinf, Subgroup.card_bot] at hc₂
    omega
  rcases key with h | h
  · left
    rw [hW]
    refine (Subgroup.closure_le _).mpr fun w hw => ?_
    have hwX : w ∈ X₁ ⊔ X₂ := hX ▸ hWX hw.1
    exact mem_of_odd_of_mem_centralizer hV (hX₂X.trans hXV) hO₁ hO₂ hi₂ hc₂ (hX₂X.trans hN₁) hC₁
      hwX hw.2 (h w hw.1 hw.2)
  · right
    rw [hW]
    refine (Subgroup.closure_le _).mpr fun w hw => ?_
    have hwX : w ∈ X₂ ⊔ X₁ := by rw [sup_comm]; exact hX ▸ hWX hw.1
    exact mem_of_odd_of_mem_centralizer hV (hX₁X.trans hXV) hO₂ hO₁ hi₁ hc₁ (hX₁X.trans hN₂) hC₂
      hwX hw.2 (h w hw.1 hw.2)

theorem map_conj_eq_or_eq [Finite G] {V X X₁ X₂ : Subgroup G}
    (hV : IsElemAbelian 2 V) (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hX : X = X₁ ⊔ X₂)
    (hO₁ : X₁ = oTwoUpper X₁) (hO₂ : X₂ = oTwoUpper X₂)
    (hi₁ : (pCoreOf 2 X₁).relIndex X₁ = 3) (hi₂ : (pCoreOf 2 X₂).relIndex X₂ = 3)
    (hVinf : ⁅V, X₁⁆ ⊓ ⁅V, X₂⁆ = ⊥) (hc₁ : Nat.card (⁅V, X₁⁆ : Subgroup G) = 4)
    (hc₂ : Nat.card (⁅V, X₂⁆ : Subgroup G) = 4)
    (hN₁ : X ≤ Subgroup.normalizer (X₁ : Set G)) (hN₂ : X ≤ Subgroup.normalizer (X₂ : Set G))
    (hcard : Nat.card X₂ = Nat.card X₁) {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) :
    X₁.map (MulAut.conj g).toMonoidHom = X₁ ∨ X₁.map (MulAut.conj g).toMonoidHom = X₂ := by
  set φ := MulAut.conj g with hφ
  have hX₁X : X₁ ≤ X := hX ▸ le_sup_left
  have hWX : X₁.map φ.toMonoidHom ≤ X := by
    rw [← map_conj_eq_of_mem_normalizer hgX]
    exact Subgroup.map_mono hX₁X
  have hWO : X₁.map φ.toMonoidHom = oTwoUpper (X₁.map φ.toMonoidHom) := by
    rw [oTwoUpper_map, ← hO₁]
  have hW4 : Nat.card (⁅V, X₁.map φ.toMonoidHom⁆ : Subgroup G) = 4 := by
    have e : ⁅V, X₁.map φ.toMonoidHom⁆ = (⁅V, X₁⁆ : Subgroup G).map φ.toMonoidHom := by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hgV]
    rw [e, card_map_mulEquiv, hc₁]
  have hcW : Nat.card (X₁.map φ.toMonoidHom) = Nat.card X₁ := card_map_mulEquiv φ X₁
  rcases le_or_le_of_card_commutator_eq_four hV hXV hX hO₁ hO₂ hi₁ hi₂ hVinf hc₁ hc₂ hN₁ hN₂ hWX
    hWO hW4 with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hcW]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hcW, hcard]))

end CFSG.Quasithin.EmptyFaithfulMultiple
