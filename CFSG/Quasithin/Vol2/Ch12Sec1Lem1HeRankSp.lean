module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeRankAO
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporHS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem twoRankLtSix_of_bound {X : Type} [Group X] {r : ℕ} (hr : r ≤ 5)
    (h : ∀ B : Subgroup X, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r) : TwoRankLtSix X := by
  intro E hE
  have h1 := h E (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => by rw [← sq]; exact hE.2 x hx)
  exact lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem hyperplane_facts :
    (∀ b : Fin 5 → ZMod 2, b ≠ 0 →
      (Finset.univ.filter fun v : Fin 5 → ZMod 2 => ∑ i, b i * v i = 0).card = 16) ∧
    ∀ b b' : Fin 5 → ZMod 2, b ≠ 0 → b' ≠ 0 → b ≠ b' →
      ∃ v : Fin 5 → ZMod 2, ¬ ((∑ i, b i * v i = 0) ↔ (∑ i, b' i * v i = 0)) := by
  decide

theorem exists_hyperplanes {G : Type} [Group G] [Finite G] (E : Subgroup G)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = 32) :
    ∃ H : {b : Fin 5 → ZMod 2 // b ≠ 0} → Subgroup G, Function.Injective H ∧
      ∀ b, H b ≤ E ∧ Nat.card (H b) = 16 := by
  classical
  let _ : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (hcomm _ a.2 _ b.2) }
  let _ : Module (ZMod 2) (Additive ↥E) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    exact Subtype.ext (hsq _ (Additive.toMul x).2)
  have hfin : Module.finrank (ZMod 2) (Additive ↥E) = 5 := by
    let _ : Fintype (Additive ↥E) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive ↥E)
    rw [ZMod.card] at h
    have h32 : Fintype.card (Additive ↥E) = 2 ^ 5 := by
      rw [← Nat.card_eq_fintype_card, show Nat.card (Additive ↥E) = Nat.card ↥E from rfl, hcard]
      norm_num
    rw [h32] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive ↥E ≃ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hfin, Module.finrank_fin_fun])
  let f : ∀ x ∈ E, Fin 5 → ZMod 2 := fun x hx => e (Additive.ofMul ⟨x, hx⟩)
  let H : {b : Fin 5 → ZMod 2 // b ≠ 0} → Subgroup G := fun b =>
    { carrier := {x | ∃ hx : x ∈ E, ∑ i, b.1 i * f x hx i = 0}
      one_mem' := ⟨E.one_mem, by
        show ∑ i, b.1 i * e (Additive.ofMul 1) i = 0
        rw [ofMul_one, map_zero]
        simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
        refine ⟨E.mul_mem hx hy, ?_⟩
        have : f (x * y) (E.mul_mem hx hy) = f x hx + f y hy := by
          show e (Additive.ofMul (⟨x, hx⟩ * ⟨y, hy⟩)) = _
          rw [ofMul_mul, map_add]
        rw [this]
        simp [mul_add, Finset.sum_add_distrib, hx0, hy0]
      inv_mem' := by
        rintro x ⟨hx, hx0⟩
        have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
        rw [hinv]
        exact ⟨hx, hx0⟩ }
  have hmem : ∀ b x, x ∈ H b ↔ ∃ hx : x ∈ E, ∑ i, b.1 i * f x hx i = 0 := fun _ _ => Iff.rfl
  refine ⟨H, ?_, fun b => ⟨fun x hx => ((hmem b x).mp hx).1, ?_⟩⟩
  · intro b b' hbb'
    by_contra hne
    have hne' : b.1 ≠ b'.1 := fun h => hne (Subtype.ext h)
    obtain ⟨v, hv⟩ := hyperplane_facts.2 b.1 b'.1 b.2 b'.2 hne'
    set x : G := ((Additive.toMul (e.symm v) : ↥E) : G) with hxdef
    have hxE : x ∈ E := (Additive.toMul (e.symm v)).2
    have hfx : f x hxE = v := by
      show e (Additive.ofMul ⟨x, hxE⟩) = v
      have : (⟨x, hxE⟩ : ↥E) = Additive.toMul (e.symm v) := rfl
      rw [this, ofMul_toMul, LinearEquiv.apply_symm_apply]
    have h1 : x ∈ H b ↔ x ∈ H b' := by rw [hbb']
    rw [hmem, hmem] at h1
    apply hv
    constructor
    · intro h
      obtain ⟨hx', h'⟩ := h1.mp ⟨hxE, by rw [hfx]; exact h⟩
      rw [hfx] at h'
      exact h'
    · intro h
      obtain ⟨hx', h'⟩ := h1.mpr ⟨hxE, by rw [hfx]; exact h⟩
      rw [hfx] at h'
      exact h'
  ·
    have hbij : ↥(H b) ≃ {v : Fin 5 → ZMod 2 // ∑ i, b.1 i * v i = 0} :=
      { toFun := fun x => ⟨f x ((hmem b x).mp x.2).1, ((hmem b x).mp x.2).2⟩
        invFun := fun v => ⟨((Additive.toMul (e.symm v.1) : ↥E) : G),
          (Additive.toMul (e.symm v.1)).2, by
            show ∑ i, b.1 i * e (Additive.ofMul (Additive.toMul (e.symm v.1))) i = 0
            rw [ofMul_toMul, LinearEquiv.apply_symm_apply]
            exact v.2⟩
        left_inv := fun x => by
          apply Subtype.ext
          show ((Additive.toMul (e.symm (e (Additive.ofMul ⟨(x : G), _⟩))) : ↥E) : G) = x
          rw [LinearEquiv.symm_apply_apply, toMul_ofMul]
        right_inv := fun v => by
          apply Subtype.ext
          show e (Additive.ofMul ⟨((Additive.toMul (e.symm v.1) : ↥E) : G), _⟩) = v.1
          have : (⟨((Additive.toMul (e.symm v.1) : ↥E) : G), (Additive.toMul (e.symm v.1)).2⟩ :
            ↥E) = Additive.toMul (e.symm v.1) := rfl
          rw [this, ofMul_toMul, LinearEquiv.apply_symm_apply] }
    rw [Nat.card_congr hbij, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hyperplane_facts.1 b.1 b.2


theorem natCard_nonzero_vec : Nat.card {b : Fin 5 → ZMod 2 // b ≠ 0} = 31 := by
  rw [Nat.card_eq_fintype_card]
  decide

open CFSG.QuasithinUnique.A5.Kc3SporHS CFSG.Sporadic.Schreier in
theorem hsP_no_E32
    (E : Subgroup ↥hsP)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = 32) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, Ek, hcardR, hclass⟩ := hs_e16
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 9) (by rw [hcardR]; norm_num)
  have hidx : ¬ 2 ∣ R.index := by
    have h := R.card_mul_index
    rw [hcardR, card_hsP] at h
    omega
  let S : Sylow 2 ↥hsP := IsPGroup.toSylow hR2 hidx
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)
  obtain ⟨P, hEP⟩ := hE2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥hsP S P
  have hPR : (P : Subgroup ↥hsP) = R.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.toSubmonoid_inj.mp rfl
  set E' : Subgroup ↥hsP := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'R : E' ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : x ∈ (P : Subgroup ↥hsP) := hEP hx
    rw [hPR] at hxP
    obtain ⟨r', hr', rfl⟩ := hxP
    have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom r') = r' := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    exact hr'
  have hE'comm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  have hE'card : Nat.card E' = 32 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  obtain ⟨H, hHinj, hH⟩ := exists_hyperplanes E' hE'comm hE'sq hE'card
  have hk : ∀ b, ∃ k < 8, H b = Ek k := fun b => by
    obtain ⟨k, hk, hk'⟩ := hclass (H b) ((hH b).1.trans hE'R)
      ⟨fun x hx y hy => hE'comm x ((hH b).1 hx) y ((hH b).1 hy),
        fun x hx => hE'sq x ((hH b).1 hx)⟩ (hH b).2
    exact ⟨k, hk, hk'⟩
  choose k hk8 hkeq using hk
  have hinj : Function.Injective (fun b => (⟨k b, hk8 b⟩ : Fin 8)) := by
    intro b b' h
    apply hHinj
    rw [hkeq b, hkeq b']
    exact congrArg Ek (congrArg Fin.val h)
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [natCard_nonzero_vec, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  omega

open CFSG.QuasithinUnique.A5.Kc3SporHS CFSG.Sporadic.Schreier in
theorem twoRankLtSix_hsP :
    TwoRankLtSix ↥hsP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E hE
  by_contra hge
  push Not at hge
  obtain ⟨k, hk⟩ := (CFSG.GH74.SmallRanks.isPGroup_two_of_isElemAbelian hE).exists_card_eq
  have hk6 : 6 ≤ k := by
    rw [hk] at hge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 (n := 5)
    (by rw [hk]; exact Nat.pow_dvd_pow 2 (by omega))
  apply hsP_no_E32 (K.map E.subtype)
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact congrArg Subtype.val (hE.1.is_comm.comm a b)
  · rintro _ ⟨a, -, rfl⟩
    rw [← sq]
    exact hE.2 _ a.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    norm_num

theorem heInspRankSpor_holds :
    HeInspRankSpor := by
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact twoRankLtSix_of_bound (X := ↥NativeSporadic.M11) (r := 2) (by norm_num)
      CFSG.QuasithinUnique.Setup.X1.m11_elemAbelian_le
  · exact twoRankLtSix_of_bound (X := ↥NativeSporadic.M12) (r := 3) (by norm_num)
      CFSG.QuasithinUnique.Setup.X1.m12_rank_le
  · exact twoRankLtSix_of_bound (X := ↥NativeSporadic.M22) (r := 4) (by norm_num)
      CFSG.QuasithinUnique.Setup.X1.m22_rank_le
  · exact twoRankLtSix_of_bound (X := ↥NativeSporadic.M23) (r := 4) (by norm_num)
      CFSG.QuasithinUnique.Setup.X1.m23_rank_le
  · exact (twoRankLtSix_of_bound (r := 3) (by norm_num)
      CFSG.QuasithinUnique.Setup.X1.walterJ1_elemAbelian_le).of_mulEquiv
      CFSG.Walter.walterJ1EquivNative.symm
  · refine (twoRankLtSix_of_bound (X := ↥CFSG.Sporadic.Schreier.j2P) (r := 4) (by norm_num)
      ?_).of_mulEquiv CFSG.Sporadic.Schreier.j2PermEquiv
    intro B hc hs2
    have h1 := CFSG.QuasithinUnique.Bridge.J2Excl.j2_rank_R
      (B.map (Subgroup.inclusion CFSG.QuasithinUnique.Bridge.J2Excl.j2P_le_R))
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hc a ha b hb])
      (by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_mul, hs2 a ha, map_one])
    rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)] at h1
  · exact twoRankLtSix_hsP.of_mulEquiv CFSG.QuasithinUnique.A5.Kc3SporHS.hsEquiv

end CFSG.Quasithin.H13
