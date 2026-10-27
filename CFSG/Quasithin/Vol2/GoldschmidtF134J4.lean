module

public import CFSG.Quasithin.Vol2.GoldschmidtF134J4Core
public import CFSG.Sporadic.J4.QTOutAuto

public section

namespace CFSG.Quasithin.F134

open CFSG.Blueprint CFSG.Quasithin.P134 CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.F134.J4E9

theorem orderThree_j4 :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4) := by
  rintro X _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv]
  show 3 ∣ Nat.card NativeSporadic.J4
  rw [CFSG.Sporadic.J4.card_J4]
  norm_num

theorem center_J_eq_bot :
    Subgroup.center J = ⊥ := by
  have hF := j4Facts
  have hM := hF.mat
  have : IsSimpleGroup J := isSimpleGroup_J hF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : J, a * b = b * a := fun a b => by
      have hb : b ∈ Subgroup.center J := by
        rw [h]
        exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
    have hPn : P0.Normal := ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by rw [hcomm g n]; group
      rw [this]
      exact hn⟩
    have := hPn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P0 with h0 | h0
    · have := card_P0 hM hF
      rw [h0, Subgroup.card_bot] at this
      norm_num at this
    · have := card_P0 hM hF
      rw [h0, Subgroup.card_top, card_J hF] at this
      norm_num at this

theorem exists_inner_of_mem_T
    {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    [L.Normal] (hcfg : E9Config L P T) (Φ : ↥L ≃* ↥J) (hΦ : ∀ y : ↥L, Φ y ∈ P0 ↔ (y : A) ∈ T)
    {t : A} (ht : t ∈ T) :
    ∃ k ∈ P0, ∀ y : ↥L, Φ (MulAut.conjNormal (H := L) t y) = k * Φ y * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := j4Facts
  have hM := hF.mat
  let α : MulAut ↥J := Φ.symm.trans ((MulAut.conjNormal (H := L) t).trans Φ)
  have hα : ∀ x : ↥J, α x = Φ (MulAut.conjNormal (H := L) t (Φ.symm x)) := fun x => rfl
  have hαP : ∀ x ∈ P0, α x ∈ P0 := by
    intro x hx
    rw [hα, hΦ, MulAut.conjNormal_apply]
    have hxT : ((Φ.symm x : ↥L) : A) ∈ T := (hΦ _).mp (by simpa using hx)
    exact T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht)
  obtain ⟨k, hk⟩ := aut_of_maps_P0 hF α hαP
  have hk' : ∀ y : ↥L, Φ (MulAut.conjNormal (H := L) t y) = k * Φ y * k⁻¹ := by
    intro y
    have := hk (Φ y)
    rw [hα, MulEquiv.symm_apply_apply] at this
    exact this
  obtain ⟨m, hm⟩ := hcfg.sylow.2.1 ⟨t, ht⟩
  have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hpow : ∀ n : ℕ, ∀ z : ↥L,
      Φ (MulAut.conjNormal (H := L) (t ^ n) z) = k ^ n * Φ z * (k ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, map_mul, MulAut.mul_apply, ih, hk', pow_succ]
      group
  have hkm : k ^ 2 ^ m ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := hpow (2 ^ m) (Φ.symm x)
    rw [htm, map_one, MulAut.one_apply, MulEquiv.apply_symm_apply] at h1
    calc x * k ^ 2 ^ m = (k ^ 2 ^ m * x * (k ^ 2 ^ m)⁻¹) * k ^ 2 ^ m := by rw [← h1]
      _ = k ^ 2 ^ m * x := by group
  rw [center_J_eq_bot, Subgroup.mem_bot] at hkm
  have hkN : k ∈ Subgroup.normalizer ((P0 : Subgroup J) : Set J) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [← hk z, maps_P0_iff α hαP z]
  let S : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  have hkp : IsPGroup 2 (Subgroup.zpowers k) :=
    IsPGroup.of_card_dvd_pow (n := m) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hkm)
  have hkS : k ∈ (S : Subgroup J) := by
    have h1 : Subgroup.zpowers k ≤ Subgroup.normalizer ((S : Subgroup J) : Set J) :=
      Subgroup.zpowers_le.mpr hkN
    have h2 : S ∈ MulAction.fixedPoints (Subgroup.zpowers k) (Sylow 2 J) :=
      (Subgroup.zpowers k).sylow_mem_fixedPoints_iff.mpr h1
    exact (hkp.sylow_mem_fixedPoints_iff.mp h2) (Subgroup.mem_zpowers k)
  exact ⟨k, hkS, hk'⟩

theorem noE9Config_j4 :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := j4Facts.mat
  have hF := j4Facts
  have := hcfg.normal
  let ψ : ↥L ≃* J := e.trans (seedEquiv hM)
  have hP0p : IsPGroup 2 P0 := IsPGroup.of_card (card_P0 hM hF)
  obtain ⟨φ, hφ, -, hφs, hTφ⟩ := E9Config.exists_model_conj hcfg (G := ⊤) (T₀ := P0)
    (φ₀ := MulEquiv.toMonoidHom ψ) ψ.injective (fun x => Subgroup.mem_top _)
    (fun y _ => ⟨ψ.symm y, ψ.apply_symm_apply y⟩) le_top hP0p
  let Φ : ↥L ≃* J := MulEquiv.ofBijective φ ⟨hφ, fun y => hφs y (Subgroup.mem_top y)⟩
  have hΦφ : ∀ y, Φ y = φ y := fun y => rfl
  have hS := E9Config.isSylowTwoOf_inf hcfg
  have hT0p : IsPGroup 2 (((T ⊓ L).subgroupOf L).map φ) :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map φ
  have hT0P0 : ((T ⊓ L).subgroupOf L).map φ = P0 := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hT0p
    have hdvd : Nat.card (((T ⊓ L).subgroupOf L).map φ) ∣ Nat.card J :=
      Subgroup.card_subgroup_dvd_card _
    rw [card_J hF, hj, show (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 by norm_num]
      at hdvd
    have h2 : 2 ^ j ∣ 2 ^ 21 :=
      (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 41377816699065)).dvd_of_dvd_mul_right
        hdvd
    have hle : Nat.card (((T ⊓ L).subgroupOf L).map φ) ≤ 2 ^ 21 := by
      rw [hj]
      exact Nat.le_of_dvd (by positivity) h2
    exact (Subgroup.eq_of_le_of_card_ge hTφ (by rw [card_P0 hM hF]; exact hle)).symm
  have hΦP0 : ∀ y : ↥L, Φ y ∈ P0 ↔ (y : A) ∈ T := by
    intro y
    rw [← hT0P0, hΦφ, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have : x = y := hφ hxy
      rw [← this]
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    · intro hy
      exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hy, y.2⟩, rfl⟩
  have hΦP : ∀ y : ↥L, Φ y ∈ (P.subgroupOf L).map φ ↔ (y : A) ∈ P := by
    intro y
    rw [hΦφ, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have : x = y := hφ hxy
      rw [← this]
      exact Subgroup.mem_subgroupOf.mp hx
    · intro hy
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  set Pt : Subgroup J := (P.subgroupOf L).map φ with hPtdef
  have hPtcard : Nat.card Pt = 9 := by
    rw [hPtdef, Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  have hPt3 : ∀ x ∈ Pt, x ^ 3 = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow]
    have : p ^ 3 = 1 := Subtype.ext (by simpa using hcfg.exp p (Subgroup.mem_subgroupOf.mp hp))
    rw [this, map_one]
  have hmul : ∀ s ∈ P0, ∀ x ∈ Pt, ∃ y ∈ Pt, ∃ s' ∈ P0, s * x = y * s' := by
    intro s hs x hx
    rw [← hT0P0] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y, hy, s₁, hs₁, he⟩ := E9Config.mul_inf hcfg (s₀ : A)
      (Subgroup.mem_subgroupOf.mp hs₀) (x₀ : A) (Subgroup.mem_subgroupOf.mp hx₀)
    refine ⟨φ ⟨y, hcfg.le hy⟩, ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, φ ⟨s₁, hs₁.2⟩, ?_, ?_⟩
    · rw [← hT0P0]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hs₁, rfl⟩
    · rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext he)
  have hK : Nat.card ↥(Pt ⊔ P0) = 9 * 2 ^ 21 := by
    rw [card_sup_eq_of_mul hPtcard hP0p hmul, card_P0 hM hF]
  obtain ⟨U, hUPt, hU1, hUPt', hUnorm⟩ := exists_normalized hPtcard hPt3 hK
  let Ũ : Subgroup A := (U.comap φ).map L.subtype
  have hŨmem : ∀ x : A, x ∈ Ũ ↔ ∃ y : ↥L, Φ y ∈ U ∧ (y : A) = x := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, Subgroup.mem_comap.mp hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, Subgroup.mem_comap.mpr hy, rfl⟩
  have hŨP : Ũ ≤ P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hŨmem x).mp hx
    exact (hΦP y).mp (hUPt hy)
  have hŨ1 : Ũ ≠ ⊥ := by
    intro h
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := U)).mp hU1
    obtain ⟨y, rfl⟩ := Φ.surjective u
    have hy : (y : A) ∈ Ũ := (hŨmem _).mpr ⟨y, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at hy
    have hy1 : y = 1 := Subtype.ext hy
    have hΦy : Φ y = 1 := by rw [hy1]; exact map_one Φ
    exact hu1 (Subtype.ext hΦy)
  have hŨP' : Ũ ≠ P := by
    intro h
    apply hUPt'
    refine le_antisymm hUPt (fun u hu => ?_)
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu
    have hpP : (p : A) ∈ P := Subgroup.mem_subgroupOf.mp hp
    rw [← h] at hpP
    obtain ⟨y, hy, hyp⟩ := (hŨmem _).mp hpP
    have : y = p := Subtype.ext hyp
    subst this
    exact hy
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (Ũ : Set A) := by
    intro t ht
    obtain ⟨k, hkP0, hk⟩ := exists_inner_of_mem_T hcfg Φ hΦP0 ht.1
    have hkN : k ∈ Subgroup.normalizer (Pt : Set J) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      obtain ⟨y, rfl⟩ := Φ.surjective z
      rw [← hk y, hΦP, hΦP, MulAut.conjNormal_apply]
      exact Subgroup.mem_normalizer_iff.mp ht.2 _
    have hkU := hUnorm k hkP0 hkN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (hŨmem x).mp hx
      refine (hŨmem _).mpr ⟨MulAut.conjNormal (H := L) t y, ?_, by rw [MulAut.conjNormal_apply]⟩
      rw [hk y]
      exact (Subgroup.mem_normalizer_iff.mp hkU _).mp hy
    · intro hx
      obtain ⟨y', hy', hy'x⟩ := (hŨmem _).mp hx
      let y : ↥L := (MulAut.conjNormal (H := L) t).symm y'
      have hyx : (y : A) = x := by
        rw [MulAut.conjNormal_symm_apply, hy'x]
        group
      have hy'y : MulAut.conjNormal (H := L) t y = y' := MulEquiv.apply_symm_apply _ _
      refine (hŨmem x).mpr ⟨y, ?_, hyx⟩
      have h1 := hk y
      rw [hy'y] at h1
      have h2 : k * Φ y * k⁻¹ ∈ U := h1 ▸ hy'
      exact (Subgroup.mem_normalizer_iff.mp hkU _).mpr h2
  rcases hcfg.irred Ũ hŨP hnorm with h | h
  · exact hŨ1 h
  · exact hŨP' h

end CFSG.Quasithin.F134

namespace CFSG.Quasithin.P134

open CFSG.Blueprint

theorem facts134E9_j4 :
    OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4)) ∧
      NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4) :=
  ⟨F134.orderThree_j4, F134.noE9Config_j4⟩

end CFSG.Quasithin.P134
