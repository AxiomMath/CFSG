module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W]

private theorem gf2_Core_maschke_zmod {p : ℕ} [Fact p.Prime] {D : Type*} [Group D] [Finite D]
    (hD : Nat.Coprime p (Nat.card D)) {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : Representation (ZMod p) D M) (N : Submodule (ZMod p) M)
    (hN : ∀ d, ∀ x ∈ N, ρ d x ∈ N) :
    ∃ N' : Submodule (ZMod p) M, (∀ d, ∀ x ∈ N', ρ d x ∈ N') ∧ IsCompl N N' := by
  have : NeZero (Nat.card D : ZMod p) :=
    ⟨fun h => ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hD) ((ZMod.natCast_eq_zero_iff _ _).1 h)⟩
  obtain ⟨σ', hσ'⟩ := ComplementedLattice.exists_isCompl
    (⟨N, fun d _ hx => hN d _ hx⟩ : Subrepresentation ρ)
  refine ⟨σ'.toSubmodule, fun d x hx => σ'.apply_mem_toSubmodule d hx, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hσ' ⊢
  exact ⟨congrArg Subrepresentation.toSubmodule hσ'.1,
    congrArg Subrepresentation.toSubmodule hσ'.2⟩

private theorem gf2_Core_maschke_commGroup {p : ℕ} [Fact p.Prime] {D Q : Type*} [Group D]
    [Finite D] [CommGroup Q] (hD : Nat.Coprime p (Nat.card D)) (hQ : ∀ x : Q, x ^ p = 1)
    (ρ : D →* MulAut Q) (B : Subgroup Q) (hB : ∀ d, ∀ x ∈ B, ρ d x ∈ B) :
    ∃ C : Subgroup Q, (∀ d, ∀ x ∈ C, ρ d x ∈ C) ∧ B ⊓ C = ⊥ ∧ B ⊔ C = ⊤ := by
  let : Module (ZMod p) (Additive Q) :=
    AddCommGroup.zmodModule (n := p) fun x => Additive.toMul.injective (hQ (Additive.toMul x))
  let ρ' : Representation (ZMod p) D (Additive Q) :=
    { toFun := fun d => (AddMonoidHom.mk'
        (fun x : Additive Q => Additive.ofMul (ρ d (Additive.toMul x)))
        (fun x y => by simp)).toZModLinearMap p
      map_one' := by
        ext x
        simp
      map_mul' := fun s t => by
        ext x
        simp }
  obtain ⟨N', hN', hcompl⟩ := gf2_Core_maschke_zmod hD ρ'
    (AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup B)) (fun d x hx => hB d _ hx)
  refine ⟨{ carrier := {x | Additive.ofMul x ∈ N'}
            mul_mem' := fun {a b} ha hb => N'.add_mem ha hb
            one_mem' := N'.zero_mem
            inv_mem' := fun {a} ha => N'.neg_mem ha }, fun d x hx => hN' d _ hx, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    exact Additive.ofMul.injective (Submodule.disjoint_def.1 hcompl.disjoint _ hx.1 hx.2)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1
      (hcompl.sup_eq_top ▸ Submodule.mem_top (x := Additive.ofMul x))
    have hx : x = Additive.toMul y * Additive.toMul z := Additive.ofMul.injective hyz.symm
    rw [hx]
    exact Subgroup.mul_mem_sup hy hz

section Odd

variable [Finite W]

theorem exists_stableUnder_compl_of_odd (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) {U : Subgroup W} (hU : StableUnder X U) :
    ∃ P : Subgroup W, StableUnder X P ∧ U ⊓ P = ⊥ ∧ U ⊔ P = ⊤ := by
  haveI : Finite (MulAut W) := Finite.of_injective (fun e : MulAut W => (e : W → W))
    (fun _ _ h => MulEquiv.ext (congrFun h))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card X) := Nat.coprime_two_left.mpr hX
  obtain ⟨P, hP, hinf, hsup⟩ := gf2_Core_maschke_commGroup (p := 2) (D := ↥X) (Q := W)
    hcop hW X.subtype U (fun d x hx => hU d d.2 x hx)
  exact ⟨P, fun x hx w hw => hP ⟨x, hx⟩ w hw, hinf, hsup⟩

theorem eq_bot_of_trivial_on_irrSet (hW : ∀ w : W, w ^ 2 = 1) {X H : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) (hH : QuadTrivial H) (hN : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hI : ∀ I ∈ irrSet H, ∀ x ∈ X, ∀ w ∈ I, x w = w)
    (hC : ∀ x ∈ X, ∀ w ∈ fixV H, x w = w) : X = ⊥ := by
  set R : Subgroup W := commSub ⊤ X with hR
  have hRX : StableUnder H R :=
    stableUnder_commSub hN (fun _ _ _ _ => Subgroup.mem_top _)
  have hbot' : R ⊓ fixV X = ⊥ := by
    rw [hR, inf_comm]
    exact CFSG.Quasithin.EmptyFaithfulMultiple.L15412.fixV_inf_commSub_eq_bot hW hX
  have hcommR : commSub R H = ⊥ := by
    by_contra hne
    obtain ⟨I, hIirr, hIR⟩ := exists_mem_irrSet_le hH hRX hne
    have hIfix : I ≤ fixV X := fun w hw => mem_fixV.mpr (fun x hx => hI I hIirr x hx w hw)
    have hIbot : I = ⊥ := by
      apply le_antisymm _ bot_le
      rw [← hbot']
      exact fun w hw => ⟨hIR hw, hIfix hw⟩
    exact ne_bot_of_mem_irrSet hIirr hIbot
  have hRleH : R ≤ fixV H := commSub_eq_bot_iff.mp hcommR
  have hRleX : R ≤ fixV X := fun w hw => mem_fixV.mpr (fun x hx => hC x hx w (hRleH hw))
  have hRbot : R = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hbot']
    exact fun w hw => ⟨hw, hRleX hw⟩
  have hRbot' : commSub ⊤ X = ⊥ := by rw [← hR]; exact hRbot
  have htop : (⊤ : Subgroup W) ≤ fixV X := commSub_eq_bot_iff.mp hRbot'
  refine (Subgroup.eq_bot_iff_forall X).mpr fun x hx => ?_
  exact MulEquiv.ext fun w => by
    rw [MulAut.one_apply]
    exact mem_fixV.mp (htop (Subgroup.mem_top w)) x hx

theorem iSup_irrSet_sup_fixV_eq_top_of_odd (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    (hH : Odd (Nat.card H)) : (⨆ I ∈ irrSet H, I) ⊔ fixV H = ⊤ := by
  have hn : ∀ y ∈ H, ∀ h ∈ H, y * h * y⁻¹ ∈ H :=
    fun y hy h hh => H.mul_mem (H.mul_mem hy hh) (H.inv_mem hy)
  have hU₀ : StableUnder H (⨆ I ∈ irrSet H, I) := stableUnder_iSup_irrSet hn
  have hfix : StableUnder H (fixV H) := fun x hx w hw => by
    rw [mem_fixV.mp hw x hx]
    exact hw
  have hU₁ : StableUnder H ((⨆ I ∈ irrSet H, I) ⊔ fixV H) := stableUnder_sup hU₀ hfix
  obtain ⟨P, hP, hinf, hsup⟩ := exists_stableUnder_compl_of_odd hW hH hU₁
  by_cases hPH : commSub P H = ⊥
  · have hPle : P ≤ fixV H := commSub_eq_bot_iff.mp hPH
    have hPbot : P = ⊥ := by
      apply le_antisymm _ bot_le
      rw [← hinf]
      exact fun w hw => ⟨Subgroup.mem_sup_right (hPle hw), hw⟩
    rw [hPbot, sup_bot_eq] at hsup
    exact hsup
  · exfalso
    obtain ⟨I, hIirr, hIP⟩ := exists_mem_irrSet_le (quadTrivial_of_odd hW hH) hP hPH
    have hIle : I ≤ (⨆ I ∈ irrSet H, I) ⊔ fixV H :=
      le_trans (le_iSup₂_of_le I hIirr le_rfl) le_sup_left
    have hIbot : I = ⊥ := by
      apply le_antisymm _ bot_le
      rw [← hinf]
      exact fun w hw => ⟨hIle hw, hIP hw⟩
    exact ne_bot_of_mem_irrSet hIirr hIbot

end Odd

theorem iSup_irrSet_eq_top_of_sup_fixV_eq_top {Y H : Subgroup (MulAut W)}
    (hind : IsIndivisible Y) (hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) (hne : H ≠ ⊥)
    (h : (⨆ I ∈ irrSet H, I) ⊔ fixV H = ⊤) : (⨆ I ∈ irrSet H, I) = ⊤ := by
  have hU : StableUnder Y (⨆ I ∈ irrSet H, I) := stableUnder_iSup_irrSet hn
  have hC : StableUnder Y (fixV H) := stableUnder_fixV hn
  rcases hind _ _ hU hC h with htop | htop
  · exact htop
  · exfalso
    apply hne
    refine (Subgroup.eq_bot_iff_forall H).mpr fun h' hh' => ?_
    exact MulEquiv.ext fun w => by
      rw [MulAut.one_apply]
      have hw : w ∈ fixV H := by rw [htop]; exact Subgroup.mem_top w
      exact mem_fixV.mp hw h' hh'

section O2

variable [Finite W]

theorem odd_card_of_abelian_normal {Y M : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hMY : M ≤ Y) (hMn : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M)
    (hab : ∀ m ∈ M, ∀ n ∈ M, m * n = n * m) : Odd (Nat.card M) := by
  haveI : Finite (MulAut W) := Finite.of_injective (fun e : MulAut W => (e : W → W))
    (fun _ _ h => MulEquiv.ext (congrFun h))
  haveI : Nonempty ↥M := ⟨⟨1, M.one_mem⟩⟩
  haveI : Finite ↥M := inferInstance
  obtain ⟨k, m, hmodd, hcard⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := ↥M)).ne'
  let P : Subgroup (MulAut W) :=
    { carrier := {x | x ∈ M ∧ x ^ (2 ^ k) = 1}
      one_mem' := ⟨M.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
        refine ⟨M.mul_mem hxM hyM, ?_⟩
        rw [Commute.mul_pow (hab x hxM y hyM) (2 ^ k), hx, hy, mul_one]
      inv_mem' := by
        rintro x ⟨hxM, hx⟩
        exact ⟨M.inv_mem hxM, by rw [inv_pow, hx, inv_one]⟩ }
  have hP₂ : IsPGroup 2 ↥P := by
    intro g
    exact ⟨k, Subtype.ext (by simpa using g.2.2)⟩
  have hPn : (P.subgroupOf Y).Normal := by
    refine ⟨fun a ha b => Subgroup.mem_subgroupOf.mpr ?_⟩
    have haP : (a : MulAut W) ∈ P := Subgroup.mem_subgroupOf.mp ha
    refine ⟨hMn b b.2 a haP.1, ?_⟩
    have hconj : ((b : MulAut W) * (a : MulAut W) * (b : MulAut W)⁻¹) ^ (2 ^ k) = 1 := by
      rw [conj_pow, haP.2, mul_one, mul_inv_cancel]
    exact hconj
  have hPbot : P = ⊥ := hO P (fun x hx => hMY hx.1) hPn hP₂
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hcard, hk0, pow_zero, one_mul]
    exact hmodd
  · exfalso
    have h2dvd : 2 ∣ Nat.card M := by
      rw [hcard]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 hkpos.ne') m
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2 h2dvd
    have hxpow : (x : MulAut W) ^ (2 ^ k) = 1 := by
      have h1 : x ^ (2 ^ k) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (by rw [hxord]; exact dvd_pow_self 2 hkpos.ne')
      simpa using congrArg (fun y : ↥M => (y : MulAut W)) h1
    have hxP : (x : MulAut W) ∈ P := ⟨x.2, hxpow⟩
    have hx1 : (x : MulAut W) = 1 := by
      rw [hPbot] at hxP
      exact Subgroup.mem_bot.mp hxP
    have hx1' : x = 1 := Subtype.ext (by simpa using hx1)
    rw [hx1', orderOf_one] at hxord
    exact absurd hxord (by norm_num)

theorem exists_odd_orderOf_of_normal_ne_bot {Y N : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hNY : N ≤ Y) (hNn : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hne : N ≠ ⊥) :
    ∃ x ∈ N, x ≠ 1 ∧ Odd (orderOf x) := by
  haveI : Finite (MulAut W) := Finite.of_injective (fun e : MulAut W => (e : W → W))
    (fun _ _ h => MulEquiv.ext (congrFun h))
  haveI : Nonempty ↥N := ⟨⟨1, N.one_mem⟩⟩
  haveI : Finite ↥N := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn' : (N.subgroupOf Y).Normal :=
    ⟨fun a ha b => Subgroup.mem_subgroupOf.mpr (hNn b b.2 a (Subgroup.mem_subgroupOf.mp ha))⟩
  have hnotP : ¬ IsPGroup 2 ↥N := fun hP => hne (hO N hNY hNn' hP)
  obtain ⟨k, m, hmodd, hcard⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := ↥N)).ne'
  have hm_ne_one : m ≠ 1 := by
    intro hm1
    apply hnotP
    rw [IsPGroup.iff_card]
    exact ⟨k, by rw [hcard, hm1, mul_one]⟩
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm_ne_one
  have hpodd : Odd p := Odd.of_dvd_nat hmodd hpm
  have hpdvd : p ∣ Nat.card N := by
    rw [hcard]
    exact dvd_mul_of_dvd_right hpm (2 ^ k)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpdvd
  refine ⟨(x : MulAut W), x.2, ?_, ?_⟩
  · intro hx1
    have hx1' : x = 1 := Subtype.ext (by simpa using hx1)
    rw [hx1', orderOf_one] at hxord
    exact hp.ne_one hxord.symm
  · rw [Subgroup.orderOf_coe, hxord]
    exact hpodd

end O2

end CFSG.LocalAnalysis.WeakClosure81
