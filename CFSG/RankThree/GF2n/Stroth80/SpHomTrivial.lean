module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.Quasithin.Background.E6ElevenSinger
public import CFSG.Quasithin.Background.MS09.Theorem46
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open

section Torus

open Matrix

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem spHomTriv_torus_mulVec_single {K : Type} [Field K] {m : ℕ} (i : Fin m) (a : Kˣ) :
    (((torusHom (Pi.mulSingle i a) : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ Pi.single (Sum.inl i) 1 =
      (a : K) • Pi.single (Sum.inl i) 1 := by
  rw [coe_torusHom, diagonal_mulVec_single, ← Pi.single_smul']
  simp only [smul_eq_mul, mul_one, Sum.elim_inl, Pi.mulSingle_eq_same]

open CFSG.RankThree.SubgroupLists in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem torus_conj_spTrans {K : Type} [Field K] {m : ℕ} (i : Fin m) (l : Kˣ) (k : ℕ) (c : K) :
    (((torusHom (Pi.mulSingle i l) ^ k : StatedSp m K) : GL (Fin m ⊕ Fin m) K)) *
      spTrans (Pi.single (Sum.inl i) 1) c *
      (((torusHom (Pi.mulSingle i l) ^ k : StatedSp m K) : GL (Fin m ⊕ Fin m) K))⁻¹ =
    spTrans (Pi.single (Sum.inl i) 1) ((l : K) ^ (2 * k) * c) := by
  have hpow : (torusHom (Pi.mulSingle i l) ^ k : StatedSp m K) =
      torusHom (Pi.mulSingle i (l ^ k)) := by
    rw [← map_pow, ← Pi.mulSingle_pow]
  have hg : ((torusHom (Pi.mulSingle i l) ^ k : StatedSp m K) : GL (Fin m ⊕ Fin m) K) ∈
      StatedSp m K := (torusHom (Pi.mulSingle i l) ^ k : StatedSp m K).2
  rw [conj_spTrans hg, hpow, spHomTriv_torus_mulVec_single, Units.val_pow_eq_pow_val, spTrans_smul]
  congr 1
  ring

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem torus_pow_card_sub_one {K : Type} [Field K] [Finite K] {m : ℕ} (i : Fin m) (l : Kˣ) :
    (torusHom (Pi.mulSingle i l) ^ (Nat.card K - 1) : StatedSp m K) = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hl : l ^ (Nat.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ l.ne_zero
  rw [← map_pow, ← Pi.mulSingle_pow, hl, Pi.mulSingle_one, map_one]

theorem spHomTriv_transitive_of_orderOf {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {f : ℕ} (hf : 1 ≤ f) (hcard : Nat.card W ≤ 2 ^ f)
    (c : MulAut W) (hc : orderOf c = 2 ^ f - 1) {w₁ w₂ : W} (h₁ : w₁ ≠ 1) (h₂ : w₂ ≠ 1) :
    ∃ k : ℕ, (c ^ k) w₁ = w₂ := by
  classical
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hXcard : Nat.card ↥(Subgroup.zpowers c) = 2 ^ f - 1 := by
    rw [Nat.card_zpowers, hc]
  have hXc : IsCyclic ↥(Subgroup.zpowers c) := inferInstance
  have hXo : Odd (Nat.card ↥(Subgroup.zpowers c)) := by
    rw [hXcard]
    have he : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd (by omega) he odd_one
  have hSinv : ∀ x ∈ Subgroup.zpowers c, ∀ s ∈ (⊤ : Subgroup W), x s ∈ (⊤ : Subgroup W) :=
    fun _ _ _ _ => Subgroup.mem_top _
  have hS1 : (⊤ : Subgroup W) ≠ ⊥ := by
    intro h0
    apply h₁
    have hmem : w₁ ∈ (⊤ : Subgroup W) := Subgroup.mem_top w₁
    rw [h0] at hmem
    exact Subgroup.mem_bot.1 hmem
  obtain ⟨hle, hrel⟩ := CFSG.Quasithin.E6.relIndex_centSub_le hW hXc hXo hSinv hS1
  have hcent : ∀ x : MulAut W, x ∈ CFSG.Quasithin.centSub (⊤ : Subgroup W) → x = 1 := by
    intro x hx
    ext u
    exact hx u (Subgroup.mem_top u)
  have hbot : Subgroup.zpowers c ⊓ CFSG.Quasithin.centSub (⊤ : Subgroup W) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨_, hx⟩
    exact Subgroup.mem_bot.2 (hcent x hx)
  rw [hbot, Subgroup.relIndex_bot_left, Subgroup.card_top] at hle hrel
  have hEq : Nat.card ↥(Subgroup.zpowers c) = Nat.card W - 1 := by omega
  have hfix : ∀ x ∈ Subgroup.zpowers c, (x : MulAut W) w₁ = w₁ → x = 1 := by
    intro x hx hxw
    exact hcent x (hrel hEq w₁ (Subgroup.mem_top w₁) h₁ x hx hxw)
  have hT : Nat.card ↥(((⊤ : Subgroup W) : Set W) \ {1}) = Nat.card W - 1 := by
    rw [CFSG.Quasithin.E6.card_diff_one', Subgroup.card_top]
  have hne : ∀ x : MulAut W, x w₁ ≠ 1 := by
    intro x hx1
    apply h₁
    have h2 : x w₁ = x 1 := by
      rw [map_one]
      exact hx1
    exact (x : MulAut W).injective h2
  have hmemT : ∀ x : MulAut W, x w₁ ∈ ((⊤ : Subgroup W) : Set W) \ {1} :=
    fun x => ⟨Subgroup.mem_top _, fun h => hne x h⟩
  obtain ⟨F, hF⟩ : ∃ F : ↥(Subgroup.zpowers c) → ↥(((⊤ : Subgroup W) : Set W) \ {1}),
      ∀ x : ↥(Subgroup.zpowers c), ((F x : W)) = (x : MulAut W) w₁ :=
    ⟨fun x => ⟨(x : MulAut W) w₁, hmemT x⟩, fun x => rfl⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    have h1 : (x : MulAut W) w₁ = (y : MulAut W) w₁ :=
      (hF x).symm.trans ((congrArg Subtype.val hxy).trans (hF y))
    have hmem : (y : MulAut W)⁻¹ * (x : MulAut W) ∈ Subgroup.zpowers c :=
      (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem y.2) x.2
    have hfixz : (y : MulAut W)⁻¹ * (x : MulAut W) = 1 := by
      apply hfix _ hmem
      rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
    apply Subtype.ext
    exact (inv_mul_eq_one.1 hfixz).symm
  have hcardeq : Nat.card ↥(Subgroup.zpowers c) =
      Nat.card ↥(((⊤ : Subgroup W) : Set W) \ {1}) := by
    rw [hT, hEq]
  have hbij := (Nat.bijective_iff_injective_and_card F).2 ⟨hinj, hcardeq⟩
  obtain ⟨x, hx⟩ := hbij.2 ⟨w₂, Subgroup.mem_top w₂, fun h => h₂ h⟩
  have hxw : (x : MulAut W) w₁ = w₂ := (hF x).symm.trans (congrArg Subtype.val hx)
  have hfin : IsOfFinOrder c := orderOf_pos_iff.1 (by rw [hc]; omega)
  have hmem : (x : MulAut W) ∈ Submonoid.powers c :=
    (hfin.mem_powers_iff_mem_zpowers).2 x.2
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 hmem
  exact ⟨k, by rw [hk]; exact hxw⟩

end Torus

section Hom

open CFSG.RankThree.SubgroupLists

noncomputable def spHomTriv_tau {m : ℕ} {K : Type} [Field K] (i : Fin m) (c : K) :
    ↥(StatedSp m K) :=
  ⟨spTrans (Pi.single (Sum.inl i) 1) c, spTrans_mem_statedSp _ c⟩

theorem spHomTriv_tau_mul {m : ℕ} {K : Type} [Field K] (i : Fin m) (c d : K) :
    spHomTriv_tau i (c + d) = spHomTriv_tau i c * spHomTriv_tau i d :=
  Subtype.ext (spTrans_add _ c d).symm

theorem spHomTriv_tau_zero {m : ℕ} {K : Type} [Field K] (i : Fin m) :
    spHomTriv_tau i (0 : K) = 1 :=
  Subtype.ext (spTrans_zero _)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
noncomputable def spHomTriv_h {m : ℕ} {K : Type} [Field K] (i : Fin m) (l : Kˣ) :
    ↥(StatedSp m K) :=
  torusHom (Pi.mulSingle i l)

theorem spHomTriv_conj {m : ℕ} {K : Type} [Field K] (i : Fin m) (l : Kˣ) (k : ℕ) (c : K) :
    spHomTriv_h i l ^ k * spHomTriv_tau i c * (spHomTriv_h i l ^ k)⁻¹ =
      spHomTriv_tau i (((l ^ (2 * k) : Kˣ) : K) * c) := by
  apply Subtype.ext
  rw [Units.val_pow_eq_pow_val]
  exact torus_conj_spTrans i l k c

theorem spHomTriv_conj_one {m : ℕ} {K : Type} [Field K] (i : Fin m) (l : Kˣ) (c : K) :
    spHomTriv_h i l * spHomTriv_tau i c * (spHomTriv_h i l)⁻¹ =
      spHomTriv_tau i (((l ^ 2 : Kˣ) : K) * c) := by
  have h := spHomTriv_conj i l 1 c
  rw [pow_one (spHomTriv_h i l), Nat.mul_one 2] at h
  exact h

theorem spHomTriv_h_pow {m : ℕ} {K : Type} [Field K] [Finite K] (i : Fin m) (l : Kˣ) :
    spHomTriv_h i l ^ (Nat.card K - 1) = 1 :=
  torus_pow_card_sub_one i l

theorem spHomTriv_card (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  refine ⟨n, ?_, ?_⟩
  · have := n.pos
    omega
  · rw [Nat.card_eq_fintype_card, hn]

theorem spHomTriv_gen_sq {G : Type} [Group G] [Finite G] [IsCyclic G]
    (hodd : Odd (Nat.card G)) :
    ∃ g : G, (∀ u : G, ∃ k : ℕ, g ^ (2 * k) = u) ∧ orderOf g = Nat.card G := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨g, fun u => ?_, hord⟩
  obtain ⟨j, hj⟩ :=
    (Submonoid.mem_powers_iff _ _).1 ((hfin.mem_powers_iff_mem_zpowers).2 (hg u))
  obtain ⟨t, ht⟩ := hodd
  refine ⟨j * (t + 1), ?_⟩
  have h2 : 2 * (j * (t + 1)) = Nat.card G * j + j := by
    rw [ht]
    ring
  rw [h2, pow_add, pow_mul, ← hord, pow_orderOf_eq_one, one_pow, one_mul, hj]

noncomputable def spHomTriv_tauHom {m : ℕ} {K : Type} [Field K] (i : Fin m) :
    Multiplicative K →* ↥(StatedSp m K) where
  toFun x := spHomTriv_tau i (Multiplicative.toAdd x)
  map_one' := spHomTriv_tau_zero i
  map_mul' x y := spHomTriv_tau_mul i (Multiplicative.toAdd x) (Multiplicative.toAdd y)

theorem spHomTriv_fixed {m : ℕ} {K : Type} [Field K] [CharP K 2] {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hW1 : ∃ w : W, w ≠ 1) (π : ↥(StatedSp m K) →* MulAut W)
    (i : Fin m) : ∃ w : W, w ≠ 1 ∧ ∀ c : K, π (spHomTriv_tau i c) w = w := by
  have hK2 : ∀ x : Multiplicative K, x ^ 2 = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, CharTwo.add_self_eq_zero]
  have hN : IsPGroup 2 ↥((spHomTriv_tauHom (K := K) i).range) := fun g => by
    obtain ⟨x, hx⟩ := (MonoidHom.mem_range (f := spHomTriv_tauHom (K := K) i)).1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hx, ← map_pow, hK2 x, map_one]
  have hV1 : (⊤ : Subgroup W) ≠ ⊥ := by
    intro h
    obtain ⟨w, hw⟩ := hW1
    have hmem : w ∈ (⊤ : Subgroup W) := Subgroup.mem_top w
    rw [h, Subgroup.mem_bot] at hmem
    exact hw hmem
  have hfix := CFSG.Quasithin.MS09.Th46.exists_fix_ne_one (ρ := π) hW hN hV1
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ CFSG.Quasithin.MS09.Mod.fixIn π (spHomTriv_tauHom (K := K) i).range ⊤,
      w ≠ 1 := by
    by_contra hcon
    exact hfix ((Subgroup.eq_bot_iff_forall _).2 fun x hx =>
      Classical.byContradiction fun hx1 => hcon ⟨x, hx, hx1⟩)
  refine ⟨w, hw1, fun c => ?_⟩
  have hmem := (CFSG.Quasithin.MS09.Mod.mem_fixIn (ρ := π)).1 hw
  exact hmem.2 (spHomTriv_tau i c)
    ((MonoidHom.mem_range (f := spHomTriv_tauHom (K := K) i)).2 ⟨Multiplicative.ofAdd c, rfl⟩)

theorem spHomTriv_inj {m : ℕ} {K : Type} [Field K] [CharP K 2] {W : Type} [CommGroup W]
    (π : ↥(StatedSp m K) →* MulAut W) (i : Fin m) (l : Kˣ)
    (hl : ∀ u : Kˣ, ∃ k : ℕ, l ^ (2 * k) = u)
    (hbad : ∃ c₀ : K, π (spHomTriv_tau i c₀) ≠ 1) (c₁ c₂ : K)
    (h : π (spHomTriv_tau i c₁) = π (spHomTriv_tau i c₂)) : c₁ = c₂ := by
  obtain ⟨c₀, hc₀⟩ := hbad
  have hsq : spHomTriv_tau i c₂ * spHomTriv_tau i c₂ = 1 := by
    rw [← spHomTriv_tau_mul, CharTwo.add_self_eq_zero, spHomTriv_tau_zero]
  have hd0 : c₁ + c₂ = 0 := by
    by_contra hd
    have hsum : π (spHomTriv_tau i (c₁ + c₂)) = 1 := by
      rw [spHomTriv_tau_mul, map_mul, h, ← map_mul, hsq, map_one]
    have hall : ∀ c : K, π (spHomTriv_tau i c) = 1 := by
      intro c
      by_cases hc : c = 0
      · rw [hc, spHomTriv_tau_zero, map_one]
      obtain ⟨k, hk⟩ := hl (Units.mk0 (c * (c₁ + c₂)⁻¹) (mul_ne_zero hc (inv_ne_zero hd)))
      have hcK : ((l ^ (2 * k) : Kˣ) : K) * (c₁ + c₂) = c := by
        rw [hk, Units.val_mk0, mul_assoc, inv_mul_cancel₀ hd, mul_one]
      rw [← hcK, ← spHomTriv_conj, map_mul, map_mul, map_inv, hsum, mul_one, mul_inv_cancel]
    exact hc₀ (hall c₀)
  calc c₁ = c₁ + (c₂ + c₂) := by rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (c₁ + c₂) + c₂ := by ring
    _ = c₂ := by rw [hd0, zero_add]

theorem spHomTriv_orderOf_y0 {m : ℕ} {K : Type} [Field K] [Finite K] {W : Type} [CommGroup W]
    (π : ↥(StatedSp m K) →* MulAut W) (i : Fin m) (l : Kˣ)
    (hlord : orderOf l = Nat.card K - 1) (hodd : Odd (Nat.card K - 1))
    (hinj : ∀ c₁ c₂ : K, π (spHomTriv_tau i c₁) = π (spHomTriv_tau i c₂) → c₁ = c₂) :
    orderOf (π (spHomTriv_h i l)) = Nat.card K - 1 := by
  have hpow : π (spHomTriv_h i l) ^ (Nat.card K - 1) = 1 := by
    rw [← map_pow, spHomTriv_h_pow, map_one]
  have hdvd : orderOf (π (spHomTriv_h i l)) ∣ Nat.card K - 1 :=
    orderOf_dvd_of_pow_eq_one hpow
  have hyd : π (spHomTriv_h i l ^ orderOf (π (spHomTriv_h i l))) = 1 := by
    rw [map_pow]
    exact pow_orderOf_eq_one _
  have htau : π (spHomTriv_tau i (((l ^ (2 * orderOf (π (spHomTriv_h i l))) : Kˣ) : K) * 1)) =
      π (spHomTriv_tau i 1) := by
    rw [← spHomTriv_conj, map_mul, map_mul, map_inv, hyd, one_mul, inv_one, mul_one]
  have hl2 : l ^ (2 * orderOf (π (spHomTriv_h i l))) = 1 :=
    Units.ext (by simpa using hinj _ _ htau)
  have hdl : orderOf l ∣ 2 * orderOf (π (spHomTriv_h i l)) :=
    orderOf_dvd_of_pow_eq_one hl2
  rw [hlord] at hdl
  have hcop : Nat.Coprime (Nat.card K - 1) 2 := Nat.coprime_two_right.2 hodd
  have hdvd2 : Nat.card K - 1 ∣ orderOf (π (spHomTriv_h i l)) :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop hdl
  exact Nat.dvd_antisymm hdvd hdvd2

theorem spHomTriv_inv {m : ℕ} {K : Type} [Field K] {W : Type} [CommGroup W]
    (π : ↥(StatedSp m K) →* MulAut W) (i : Fin m) (l : Kˣ) (hlpow : l ^ (Nat.card K - 1) = 1)
    (hq2 : 2 ≤ Nat.card K) (w : W) (hw : ∀ c : K, π (spHomTriv_tau i c) w = w) (c : K) :
    π (spHomTriv_tau i c) (π (spHomTriv_h i l) w) = π (spHomTriv_h i l) w := by
  have h1 : l ^ 2 * l ^ (2 * (Nat.card K - 2)) = 1 := by
    rw [← pow_add, show 2 + 2 * (Nat.card K - 2) = (Nat.card K - 1) * 2 by omega, pow_mul,
      hlpow, one_pow]
  have h2 : ((l ^ 2 : Kˣ) : K) * ((l ^ (2 * (Nat.card K - 2)) : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, h1, Units.val_one]
  have hc : ((l ^ 2 : Kˣ) : K) * (((l ^ (2 * (Nat.card K - 2)) : Kˣ) : K) * c) = c := by
    rw [← mul_assoc, h2, one_mul]
  have hconj : spHomTriv_h i l * spHomTriv_tau i (((l ^ (2 * (Nat.card K - 2)) : Kˣ) : K) * c) *
      (spHomTriv_h i l)⁻¹ = spHomTriv_tau i c := by
    rw [spHomTriv_conj_one, hc]
  have hcomm : spHomTriv_tau i c * spHomTriv_h i l =
      spHomTriv_h i l * spHomTriv_tau i (((l ^ (2 * (Nat.card K - 2)) : Kˣ) : K) * c) := by
    rw [← hconj]
    group
  have hmap := congrArg (⇑π) hcomm
  rw [map_mul, map_mul] at hmap
  have happ := congrArg (fun φ : MulAut W => φ w) hmap
  simp only [MulAut.mul_apply] at happ
  rw [hw (((l ^ (2 * (Nat.card K - 2)) : Kˣ) : K) * c)] at happ
  exact happ

theorem spHomTriv_key {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type}
    [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hWq : Nat.card W ≤ Nat.card K)
    (π : ↥(StatedSp m K) →* MulAut W) (i : Fin m) : ∀ c : K, π (spHomTriv_tau i c) = 1 := by
  obtain ⟨f, hf1, hKf⟩ := spHomTriv_card K
  have hq2 : 2 ≤ Nat.card K := by
    rw [hKf]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hodd : Odd (Nat.card K - 1) := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    refine ⟨2 ^ g - 1, ?_⟩
    have hpos : 0 < 2 ^ g := by positivity
    rw [hKf, pow_succ]
    omega
  obtain ⟨l, hl, hlord⟩ := spHomTriv_gen_sq (G := Kˣ) (by rw [Nat.card_units]; exact hodd)
  have hlord' : orderOf l = Nat.card K - 1 := hlord.trans (Nat.card_units K)
  have hlpow : l ^ (Nat.card K - 1) = 1 := by
    rw [← hlord']
    exact pow_orderOf_eq_one l
  by_contra hcon
  obtain ⟨c₀, hc₀⟩ := not_forall.1 hcon
  have hinj : ∀ c₁ c₂ : K, π (spHomTriv_tau i c₁) = π (spHomTriv_tau i c₂) → c₁ = c₂ :=
    fun c₁ c₂ h => spHomTriv_inj π i l hl ⟨c₀, hc₀⟩ c₁ c₂ h
  have hord : orderOf (π (spHomTriv_h i l)) = Nat.card K - 1 :=
    spHomTriv_orderOf_y0 π i l hlord' hodd hinj
  have hW1 : ∃ w : W, w ≠ 1 := by
    by_contra hcon'
    have hsub : ∀ w : W, w = 1 := fun w => Classical.byContradiction fun hw => hcon' ⟨w, hw⟩
    apply hc₀
    ext w
    exact (hsub _).trans (hsub _).symm
  obtain ⟨w₁, hw₁, hfix⟩ := spHomTriv_fixed hW hW1 π i
  have hpow : ∀ k : ℕ, ∀ c : K,
      π (spHomTriv_tau i c) ((π (spHomTriv_h i l) ^ k) w₁) = (π (spHomTriv_h i l) ^ k) w₁ := by
    intro k
    induction k with
    | zero =>
      intro c
      simpa using hfix c
    | succ k ih =>
      intro c
      rw [pow_succ', MulAut.mul_apply]
      exact spHomTriv_inv π i l hlpow hq2 _ ih c
  have hall : ∀ w : W, ∀ c : K, π (spHomTriv_tau i c) w = w := by
    intro w c
    by_cases hw : w = 1
    · rw [hw, map_one]
    obtain ⟨k, hk⟩ := spHomTriv_transitive_of_orderOf hW hf1 (hWq.trans hKf.le)
      (π (spHomTriv_h i l)) (by rw [hord, hKf]) hw₁ hw
    rw [← hk]
    exact hpow k c
  apply hc₀
  ext w
  exact hall w c₀

theorem spHomTriv_transvection {m : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    (π : ↥(StatedSp m K) →* G) (i : Fin m) (hτ : ∀ c : K, π (spHomTriv_tau i c) = 1)
    (a : Fin m ⊕ Fin m → K) (c : K) :
    π ⟨spTrans a c, spTrans_mem_statedSp a c⟩ = 1 := by
  by_cases ha : a = 0
  · subst ha
    have h1 : (⟨spTrans 0 c, spTrans_mem_statedSp 0 c⟩ : ↥(StatedSp m K)) = 1 :=
      Subtype.ext (spTrans_zero_vec c)
    rw [h1, map_one]
  · have he : (Pi.single (Sum.inl i) (1 : K) : Fin m ⊕ Fin m → K) ≠ 0 := by
      intro h
      have h' := congrFun h (Sum.inl i)
      simp at h'
    obtain ⟨A, hA, hAe⟩ := CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq he ha
    have hconj : A * spTrans (Pi.single (Sum.inl i) (1 : K)) c * A⁻¹ = spTrans a c := by
      rw [conj_spTrans hA, hAe]
    have hsub : (⟨spTrans a c, spTrans_mem_statedSp a c⟩ : ↥(StatedSp m K)) =
        (⟨A, hA⟩ : ↥(StatedSp m K)) * spHomTriv_tau i c * (⟨A, hA⟩ : ↥(StatedSp m K))⁻¹ :=
      Subtype.ext hconj.symm
    rw [hsub, map_mul, map_mul, map_inv, hτ, mul_one, mul_inv_cancel]

theorem spHomTriv_eq_one_of_gen {m : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    (π : ↥(StatedSp m K) →* G)
    (h : ∀ (a : Fin m ⊕ Fin m → K) (c : K), π ⟨spTrans a c, spTrans_mem_statedSp a c⟩ = 1) :
    π = 1 := by
  let S : Subgroup (GL (Fin m ⊕ Fin m) K) := (π.ker).map (StatedSp m K).subtype
  have hS : Subgroup.closure {g | ∃ (a : Fin m ⊕ Fin m → K) (c : K), g = spTrans a c} ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨spTrans a c, spTrans_mem_statedSp a c⟩, MonoidHom.mem_ker.2
      (h a c), rfl⟩
  have hle : StatedSp m K ≤ S :=
    (statedSp_eq_closure_spTrans (n := m) (K := K)).le.trans hS
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.one_apply]
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hle x.2)
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx']
  exact MonoidHom.mem_ker.1 hz

theorem spHomTriv_hom_trivial {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hWq : Nat.card W ≤ Nat.card K) (π : ↥(StatedSp m K) →* MulAut W) : π = 1 := by
  apply spHomTriv_eq_one_of_gen
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    intro a c
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    have h1 : (⟨spTrans 0 c, spTrans_mem_statedSp 0 c⟩ : ↥(StatedSp 0 K)) = 1 :=
      Subtype.ext (spTrans_zero_vec c)
    rw [h1, map_one]
  · intro a c
    exact spHomTriv_transvection π ⟨0, hm⟩ (spHomTriv_key hW hWq π ⟨0, hm⟩) a c

theorem hom_statedSp_to_mulAut_trivial {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {Y : Type} [AddCommGroup Y] [Finite Y] (hY2 : ∀ y : Y, y + y = 0)
    (hYq : Nat.card Y ≤ Nat.card K) (π : ↥(StatedSp m K) →* MulAut (Multiplicative Y)) :
    π = 1 := by
  have hW : ∀ w : Multiplicative Y, w ^ 2 = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, hY2]
  exact spHomTriv_hom_trivial hW hYq π

theorem hom_statedSp_to_addAut_trivial {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {Y : Type} [AddCommGroup Y] [Finite Y] (hY2 : ∀ y : Y, y + y = 0)
    (hYq : Nat.card Y ≤ Nat.card K) (π : ↥(StatedSp m K) →* Multiplicative (AddAut Y)) :
    π = 1 := by
  have h := hom_statedSp_to_mulAut_trivial hY2 hYq
    ((MulAutMultiplicative Y).symm.toMonoidHom.comp π)
  refine MonoidHom.ext fun g => ?_
  have hg : (MulAutMultiplicative Y).symm (π g) = 1 :=
    congrArg (fun φ : ↥(StatedSp m K) →* MulAut (Multiplicative Y) => φ g) h
  rw [MonoidHom.one_apply]
  have h1 : (MulAutMultiplicative Y).symm 1 = 1 := map_one _
  exact (MulAutMultiplicative Y).symm.injective (hg.trans h1.symm)

end Hom

end CFSG.RankThree.GF2n.Stroth80
