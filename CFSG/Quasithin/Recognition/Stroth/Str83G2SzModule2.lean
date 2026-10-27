module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2SzModule
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedUpper
public import CFSG.RankThree.GF2n.Tim78S48PhaseNum

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules CFSG.CGT.Timmesfeld75
open scoped Matrix MatrixGroups Pointwise

private theorem suzukiT_eq_zpowers_of_generator {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {l : Kˣ} (hl : ∀ m : Kˣ, m ∈ Subgroup.zpowers l) :
    suzukiT a K = Subgroup.zpowers (suzukiDElt a K l) := by
  let Dh : Kˣ →* ↥(suzukiGroup a K) :=
    { toFun := suzukiDElt a K
      map_one' := suzukiDElt_one
      map_mul' := fun x y => (suzukiDElt_mul x y).symm }
  have hDh : ∀ m, Dh m = suzukiDElt a K m := fun m => rfl
  ext t
  rw [← SetLike.mem_coe, coe_suzukiT]
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hl m)
    have hz := map_zpow Dh l n
    rw [hDh, hDh] at hz
    rw [hz]
    exact Subgroup.zpow_mem_zpowers (suzukiDElt a K l) n
  · intro ht
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ht
    refine ⟨l ^ n, ?_⟩
    have hz := map_zpow Dh l n
    rw [hDh] at hz
    exact hz.trans hn

theorem fixedSub_suzukiZ0_inf_suzukiT_eq_bot {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) (↥(suzukiGroup a K)) M)
    (Nsub : Subrepresentation ρ) (hNnat : IsSzNatural Nsub.toRepresentation)
    (hQ : ∀ g (m : M), ρ g m - m ∈ Nsub.toSubmodule)
    (hcent : fixedSub ρ ⊤ = ⊥) :
    fixedSub ρ (suzukiZ0 a K) ⊓ fixedSub ρ (suzukiT a K) = ⊥ := by
  obtain ⟨l, hlgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hT : suzukiT a K = Subgroup.zpowers (suzukiDElt a K l) :=
    suzukiT_eq_zpowers_of_generator hK hlgen
  have hord : orderOf l = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hlgen
  have hcardK : Nat.card Kˣ = 2 ^ (2 * a + 1) - 1 := by rw [Nat.card_units, hK]
  have hgt : 1 < Nat.card Kˣ := by
    rw [hcardK]
    have h2 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hl1 : l ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hNfix : Nsub.toRepresentation.fixedSubspace (suzukiT a K) = ⊥ := by
    rw [hT, Representation.fixedSubspace, ← fixedSub_eq_invariants]
    exact isSzNatural_suzukiDElt_fixedSub_eq_bot hK Nsub.toRepresentation hNnat hl1
  have hCD : fixedSub ρ (suzukiT a K) ⊓ Nsub.toSubmodule = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwD, hwN⟩ := Submodule.mem_inf.mp hw
    have hfix : (⟨w, hwN⟩ : Nsub.toSubmodule) ∈
        Nsub.toRepresentation.fixedSubspace (suzukiT a K) := by
      rw [Representation.fixedSubspace, Representation.mem_invariants]
      intro d
      exact Subtype.ext (mem_fixedSub.mp hwD (d : ↥(suzukiGroup a K)) d.2)
    rw [hNfix] at hfix
    simpa using hfix
  have hwD : ∀ m : Kˣ, suzukiDElt a K m * suzukiWElt a K =
      suzukiWElt a K * suzukiDElt a K m⁻¹ := by
    intro m
    calc suzukiDElt a K m * suzukiWElt a K
        = (suzukiWElt a K * suzukiWElt a K) * suzukiDElt a K m * suzukiWElt a K := by
          rw [suzukiWElt_mul_self]; group
      _ = suzukiWElt a K * (suzukiWElt a K * suzukiDElt a K m * suzukiWElt a K) := by group
      _ = suzukiWElt a K * suzukiDElt a K m⁻¹ := by rw [suzukiWElt_D_W hK m]
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨hcA, hcD⟩ := Submodule.mem_inf.mp hc
  have hcwD : ρ (suzukiWElt a K) c ∈ fixedSub ρ (suzukiT a K) := by
    rw [mem_fixedSub]
    intro d hd
    obtain ⟨m, rfl⟩ := (mem_suzukiT_iff).1 hd
    rw [← Module.End.mul_apply, ← map_mul, hwD]
    have hcinv : ρ (suzukiDElt a K m⁻¹) c = c := by
      have h := mem_fixedSub.mp hcD _ (suzukiDElt_mem_suzukiT a K m)
      calc ρ (suzukiDElt a K m⁻¹) c
          = ρ (suzukiDElt a K m⁻¹) (ρ (suzukiDElt a K m) c) := by rw [h]
        _ = ρ (suzukiDElt a K m⁻¹ * suzukiDElt a K m) c := by
            rw [map_mul, Module.End.mul_apply]
        _ = ρ 1 c := by rw [← suzukiDElt_inv, inv_mul_cancel]
        _ = c := by rw [map_one, Module.End.one_apply]
    rw [map_mul, Module.End.mul_apply, hcinv]
  have hNmem : ρ (suzukiWElt a K) c + c ∈ Nsub.toSubmodule := by
    have h := hQ (suzukiWElt a K) c
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm] using h
  have hNmemD : ρ (suzukiWElt a K) c + c ∈ fixedSub ρ (suzukiT a K) := by
    rw [mem_fixedSub]
    intro d hd
    rw [map_add, mem_fixedSub.mp hcwD d hd, mem_fixedSub.mp hcD d hd]
  have hone : ρ (suzukiWElt a K) c + c = 0 := by
    have hmem : ρ (suzukiWElt a K) c + c ∈
        fixedSub ρ (suzukiT a K) ⊓ Nsub.toSubmodule :=
      Submodule.mem_inf.mpr ⟨hNmemD, hNmem⟩
    rw [hCD] at hmem
    simpa using hmem
  have hcw : ρ (suzukiWElt a K) c = c := by
    have h : ρ (suzukiWElt a K) c = -c := eq_neg_of_add_eq_zero_left hone
    rwa [ZModModule.neg_eq_self] at h
  have hcAw : c ∈ fixedSub ρ (szZ a K) := by
    have hsz : szZ a K =
        CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (suzukiZ0 a K) := rfl
    rw [hsz, mem_fixedSub]
    intro z hz
    have hza : (suzukiWElt a K)⁻¹ * z * suzukiWElt a K ∈ suzukiZ0 a K :=
      CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hz
    set a₀ : ↥(suzukiGroup a K) := (suzukiWElt a K)⁻¹ * z * suzukiWElt a K with ha
    have hz_eq : z = suzukiWElt a K * a₀ * (suzukiWElt a K)⁻¹ := by
      rw [ha]; group
    rw [hz_eq]
    have hWinv : (suzukiWElt a K)⁻¹ = suzukiWElt a K := suzukiWElt_inv
    calc ρ (suzukiWElt a K * a₀ * (suzukiWElt a K)⁻¹) c
        = ρ (suzukiWElt a K) (ρ a₀ (ρ ((suzukiWElt a K)⁻¹) c)) := by
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      _ = ρ (suzukiWElt a K) (ρ a₀ (ρ (suzukiWElt a K) c)) := by rw [hWinv]
      _ = ρ (suzukiWElt a K) (ρ a₀ c) := by rw [hcw]
      _ = ρ (suzukiWElt a K) c := by rw [mem_fixedSub.mp hcA a₀ hza]
      _ = c := hcw
  let S : Subgroup ↥(suzukiGroup a K) :=
    { carrier := {g | ρ g c = c}
      mul_mem' := fun {g h} hg hh => by
        show ρ (g * h) c = c
        have hg' : ρ g c = c := hg
        have hh' : ρ h c = c := hh
        rw [map_mul, Module.End.mul_apply, hh', hg']
      one_mem' := by
        show ρ (1 : ↥(suzukiGroup a K)) c = c
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {g} hg => by
        show ρ g⁻¹ c = c
        have hg' : ρ g c = c := hg
        calc ρ g⁻¹ c = ρ g⁻¹ (ρ g c) := by rw [hg']
          _ = c := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
  have hA : suzukiZ0 a K ≤ S := by
    intro z hz
    exact mem_fixedSub.mp hcA z hz
  have hAw : szZ a K ≤ S := by
    intro z hz
    exact mem_fixedSub.mp hcAw z hz
  have htop : (⊤ : Subgroup ↥(suzukiGroup a K)) ≤ S := by
    rw [← suzukiZ0_sup_szZ_eq_top ha hK]
    exact sup_le hA hAw
  have hcTop : c ∈ fixedSub ρ ⊤ := by
    rw [mem_fixedSub]
    intro g _
    exact htop (Subgroup.mem_top g)
  rw [hcent] at hcTop
  simpa using hcTop

theorem lemmaNat_sz {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ρ : Representation (ZMod 2) (↥(suzukiGroup a K)) M)
    (Nsub : Subrepresentation ρ) (hNnat : IsSzNatural Nsub.toRepresentation)
    (hQ : ∀ g (m : M), ρ g m - m ∈ Nsub.toSubmodule)
    (hcent : fixedSub ρ ⊤ = ⊥) :
    fixedSub ρ (suzukiZ0 a K) ≤ Nsub.toSubmodule := by
  classical
  let D : Subgroup ↥(suzukiGroup a K) := suzukiT a K
  have hCD : fixedSub ρ (suzukiZ0 a K) ⊓ fixedSub ρ D = ⊥ :=
    fixedSub_suzukiZ0_inf_suzukiT_eq_bot ha hK ρ Nsub hNnat hQ hcent
  have hcardD : Nat.card D = Nat.card Kˣ := by
    rw [show Nat.card D = Nat.card (suzukiT a K) from rfl, (suzuki_borel_structure hK).2.2.1,
      Nat.card_units, hK]
  have hodd : Odd (Nat.card D) := hcardD ▸ odd_card_units hK
  obtain ⟨k, hk⟩ := hodd
  have hcast : (Nat.card D : ZMod 2) = 1 := by
    rw [hk]
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  have hDA : D ≤ Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) :=
    (suzukiT_le_suzukiB a K).trans (suzukiB_le_normalizer_suzukiZ0 hK)
  haveI : Finite ↥(suzukiGroup a K) := (suzuki_simple ha hK).1
  letI : Fintype D := Fintype.ofFinite D
  intro c hc
  let πc : M := ∑ d : D, ρ (d : ↥(suzukiGroup a K)) c
  have hπD : πc ∈ fixedSub ρ D := by
    rw [mem_fixedSub]
    intro d hd
    change ρ d πc = πc
    rw [show πc = ∑ e : D, ρ (e : ↥(suzukiGroup a K)) c from rfl, map_sum]
    have hcongr : (∑ e : D, ρ d (ρ (e : ↥(suzukiGroup a K)) c)) =
        ∑ e : D, ρ (d * (e : ↥(suzukiGroup a K))) c := by
      exact Finset.sum_congr rfl fun e _ => by
        rw [← Module.End.mul_apply, ← map_mul]
    rw [hcongr]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨d, hd⟩ : D))
      (fun e : D => ρ (d * (e : ↥(suzukiGroup a K))) c)
      (fun e : D => ρ (e : ↥(suzukiGroup a K)) c)
      (fun e => rfl)
  have hπA : πc ∈ fixedSub ρ (suzukiZ0 a K) := by
    rw [mem_fixedSub]
    intro a₁ ha₁
    change ρ a₁ πc = πc
    rw [show πc = ∑ e : D, ρ (e : ↥(suzukiGroup a K)) c from rfl, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hdA : (d : ↥(suzukiGroup a K))⁻¹ * a₁ * (d : ↥(suzukiGroup a K)) ∈
        suzukiZ0 a K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hDA (D.inv_mem d.2)) a₁).mp ha₁
    calc ρ a₁ (ρ (d : ↥(suzukiGroup a K)) c)
        = ρ (a₁ * (d : ↥(suzukiGroup a K))) c := by
          rw [← Module.End.mul_apply, ← map_mul]
      _ = ρ ((d : ↥(suzukiGroup a K)) *
            ((d : ↥(suzukiGroup a K))⁻¹ * a₁ * (d : ↥(suzukiGroup a K)))) c := by
          rw [show a₁ * (d : ↥(suzukiGroup a K)) =
            (d : ↥(suzukiGroup a K)) *
              ((d : ↥(suzukiGroup a K))⁻¹ * a₁ * (d : ↥(suzukiGroup a K))) by group]
      _ = ρ (d : ↥(suzukiGroup a K))
            (ρ ((d : ↥(suzukiGroup a K))⁻¹ * a₁ * (d : ↥(suzukiGroup a K))) c) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (d : ↥(suzukiGroup a K)) c := by rw [mem_fixedSub.mp hc _ hdA]
  have hπzero : πc = 0 := by
    have hmem : πc ∈ fixedSub ρ (suzukiZ0 a K) ⊓ fixedSub ρ D :=
      Submodule.mem_inf.mpr ⟨hπA, hπD⟩
    rw [hCD] at hmem
    simpa using hmem
  have hsmul : (Fintype.card D) • c = c := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) (Nat.card D) c, hcast, one_smul]
  have hsum : c + πc = ∑ d : D, (c + ρ (d : ↥(suzukiGroup a K)) c) := by
    rw [show πc = ∑ d : D, ρ (d : ↥(suzukiGroup a K)) c from rfl,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hsmul]
  have hNsum : ∑ d : D, (c + ρ (d : ↥(suzukiGroup a K)) c) ∈ Nsub.toSubmodule := by
    apply Nsub.toSubmodule.sum_mem
    intro d _
    have h := Nsub.toSubmodule.neg_mem (hQ (d : ↥(suzukiGroup a K)) c)
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm] using h
  have hcN : c + πc ∈ Nsub.toSubmodule := by
    rw [hsum]
    exact hNsum
  rw [hπzero, add_zero] at hcN
  exact hcN

private theorem wElt_conj_torusElt {F : Type} [Field F] [CharP F 2] (a : Fˣ) :
    (wElt : Matrix.SpecialLinearGroup (Fin 2) F) * torusElt a * wElt = torusElt a⁻¹ := by
  apply sl2_ext
  all_goals
    sl2_simp
    try rw [CharTwo.neg_eq]
    try simp [inv_inv]
    try ring

private theorem wElt_mul_self {F : Type} [Field F] [CharP F 2] :
    (wElt : Matrix.SpecialLinearGroup (Fin 2) F) * wElt = 1 := by
  apply sl2_ext
  all_goals
    sl2_simp
    try rw [CharTwo.neg_eq]
    try simp

private theorem torusElt_mul_wElt {F : Type} [Field F] [CharP F 2] (m : Fˣ) :
    (torusElt m : Matrix.SpecialLinearGroup (Fin 2) F) * wElt = wElt * torusElt m⁻¹ := by
  have h := wElt_conj_torusElt m
  calc torusElt m * wElt
      = (wElt * wElt) * torusElt m * wElt := by rw [wElt_mul_self]; group
    _ = wElt * (wElt * torusElt m * wElt) := by group
    _ = wElt * torusElt m⁻¹ := by rw [h]

private theorem torus_eq_zpowers_of_generator {F : Type} [Field F] {a : Fˣ}
    (ha : ∀ m : Fˣ, m ∈ Subgroup.zpowers a) :
    torus F = Subgroup.zpowers (torusElt a) := by
  let Dh : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := torusElt
      map_one' := torusElt_one
      map_mul' := fun x y => torusElt_mul x y }
  have hDh : ∀ m, Dh m = torusElt m := fun m => rfl
  ext t
  constructor
  · intro ht
    obtain ⟨m, rfl⟩ := mem_torus_iff.1 ht
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (ha m)
    have hz := map_zpow Dh a n
    rw [hDh, hDh] at hz
    rw [hz]
    exact Subgroup.zpow_mem_zpowers (torusElt a) n
  · intro ht
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ht
    refine mem_torus_iff.2 ⟨a ^ n, ?_⟩
    have hz := map_zpow Dh a n
    rw [hDh] at hz
    exact hn.symm.trans hz.symm

private theorem fixedSub_torus_sl2_eq_bot {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 3 ≤ Nat.card F) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) W)
    (hρ : IsNaturalModule ρ) :
    fixedSub ρ (torus F) = ⊥ := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hord : orderOf a = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers ha
  have hgt : 1 < Nat.card Fˣ := by rw [hcard]; omega
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hT : torus F = Subgroup.zpowers (torusElt a) := torus_eq_zpowers_of_generator ha
  rw [hT, Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨φ, hφ⟩ := hρ
  have hfix : ρ (torusElt a) w = w := mem_fixedSub.mp hw _ (Subgroup.mem_zpowers _)
  have h1 : (torusElt a : Matrix (Fin 2) (Fin 2) F) *ᵥ (φ w) = φ w := by
    have := hφ (torusElt a) w
    rw [hfix] at this
    exact this.symm
  have hv : φ w = ![(φ w) 0, (φ w) 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv] at h1
  rw [CFSG.RankThree.GF2n.Tim78.torusElt_mulVec] at h1
  have hfun : φ w = ![a * (φ w) 0, a⁻¹ * (φ w) 1] := hv.trans h1.symm
  have hv0 : (φ w) 0 = 0 := by
    have h := congrFun hfun 0
    simp only [Matrix.cons_val_zero] at h
    have h' : ((a : F) - 1) * (φ w) 0 = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (fun h0 => ha1 (Units.ext h0)))
  have hv1 : (φ w) 1 = 0 := by
    have h := congrFun hfun 1
    simp at h
    have h' : ((a : F)⁻¹ - 1) * (φ w) 1 = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left
      (sub_ne_zero.mpr (fun h0 => ha1 (Units.ext (inv_eq_one.mp h0))))
  have hz : φ w = 0 := by
    ext i
    fin_cases i
    · simpa using hv0
    · simpa using hv1
  exact φ.injective (by rw [hz, map_zero])

theorem fixedSub_utri_inf_torus_eq_bot {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 3 ≤ Nat.card F) {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) M)
    (Nsub : Subrepresentation ρ) (hNnat : IsNaturalModule Nsub.toRepresentation)
    (hQ : ∀ g (m : M), ρ g m - m ∈ Nsub.toSubmodule)
    (hcent : fixedSub ρ ⊤ = ⊥) :
    fixedSub ρ (utri F) ⊓ fixedSub ρ (torus F) = ⊥ := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hT : torus F = Subgroup.zpowers (torusElt a) := torus_eq_zpowers_of_generator ha
  have hNfix : Nsub.toRepresentation.fixedSubspace (torus F) = ⊥ := by
    rw [hT, Representation.fixedSubspace, ← fixedSub_eq_invariants, ← hT]
    exact fixedSub_torus_sl2_eq_bot hF Nsub.toRepresentation hNnat
  have hCD : fixedSub ρ (torus F) ⊓ Nsub.toSubmodule = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwD, hwN⟩ := Submodule.mem_inf.mp hw
    have hfix : (⟨w, hwN⟩ : Nsub.toSubmodule) ∈
        Nsub.toRepresentation.fixedSubspace (torus F) := by
      rw [Representation.fixedSubspace, Representation.mem_invariants]
      intro d
      exact Subtype.ext (mem_fixedSub.mp hwD (d : Matrix.SpecialLinearGroup (Fin 2) F) d.2)
    rw [hNfix] at hfix
    simpa using hfix
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨hcA, hcD⟩ := Submodule.mem_inf.mp hc
  have hcwD : ρ wElt c ∈ fixedSub ρ (torus F) := by
    rw [mem_fixedSub]
    intro d hd
    obtain ⟨m, rfl⟩ := mem_torus_iff.1 hd
    rw [← Module.End.mul_apply, ← map_mul, torusElt_mul_wElt]
    have hcinv : ρ (torusElt m⁻¹) c = c := by
      have h := mem_fixedSub.mp hcD _ (torusElt_mem_torus m)
      calc ρ (torusElt m⁻¹) c
          = ρ (torusElt m⁻¹) (ρ (torusElt m) c) := by rw [h]
        _ = ρ (torusElt m⁻¹ * torusElt m) c := by rw [map_mul, Module.End.mul_apply]
        _ = ρ 1 c := by rw [← torusElt_mul, inv_mul_cancel, torusElt_one]
        _ = c := by rw [map_one, Module.End.one_apply]
    rw [map_mul, Module.End.mul_apply, hcinv]
  have hNmem : ρ wElt c + c ∈ Nsub.toSubmodule := by
    have h := hQ wElt c
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self] using h
  have hNmemD : ρ wElt c + c ∈ fixedSub ρ (torus F) := by
    rw [mem_fixedSub]
    intro d hd
    rw [map_add, mem_fixedSub.mp hcwD d hd, mem_fixedSub.mp hcD d hd]
  have hone : ρ wElt c + c = 0 := by
    have hmem : ρ wElt c + c ∈ fixedSub ρ (torus F) ⊓ Nsub.toSubmodule :=
      Submodule.mem_inf.mpr ⟨hNmemD, hNmem⟩
    rw [hCD] at hmem
    simpa using hmem
  have hcw : ρ wElt c = c := by
    have h : ρ wElt c = -c := eq_neg_of_add_eq_zero_left hone
    rwa [ZModModule.neg_eq_self] at h
  have hcw_inv : (wElt : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ = wElt :=
    inv_eq_of_mul_eq_one_right wElt_mul_self
  have hcAw : c ∈ fixedSub ρ (ltri F) := by
    have hsz : ltri F = CFSG.CGT.Timmesfeld75.conjSubgroup wElt (utri F) :=
      conjSubgroup_wElt_utri.symm
    rw [hsz, mem_fixedSub]
    intro z hz
    have hza : (wElt : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ * z * wElt ∈ utri F :=
      CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hz
    set a₀ : Matrix.SpecialLinearGroup (Fin 2) F :=
      (wElt : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ * z * wElt with ha₀
    have hz_eq : z = wElt * a₀ * (wElt : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ := by
      rw [ha₀]; group
    rw [hz_eq]
    calc ρ (wElt * a₀ * (wElt : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹) c
        = ρ wElt (ρ a₀ (ρ ((wElt : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹) c)) := by
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      _ = ρ wElt (ρ a₀ (ρ wElt c)) := by rw [hcw_inv]
      _ = ρ wElt (ρ a₀ c) := by rw [hcw]
      _ = ρ wElt c := by rw [mem_fixedSub.mp hcA a₀ hza]
      _ = c := hcw
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | ρ g c = c}
      mul_mem' := fun {g h} hg hh => by
        show ρ (g * h) c = c
        have hg' : ρ g c = c := hg
        have hh' : ρ h c = c := hh
        rw [map_mul, Module.End.mul_apply, hh', hg']
      one_mem' := by
        show ρ (1 : Matrix.SpecialLinearGroup (Fin 2) F) c = c
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {g} hg => by
        show ρ g⁻¹ c = c
        have hg' : ρ g c = c := hg
        calc ρ g⁻¹ c = ρ g⁻¹ (ρ g c) := by rw [hg']
          _ = c := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
  have hA : utri F ≤ S := by
    intro z hz
    exact mem_fixedSub.mp hcA z hz
  have hAw : ltri F ≤ S := by
    intro z hz
    exact mem_fixedSub.mp hcAw z hz
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ S := by
    rw [← utri_sup_ltri]
    exact sup_le hA hAw
  have hcTop : c ∈ fixedSub ρ ⊤ := by
    rw [mem_fixedSub]
    intro g _
    exact htop (Subgroup.mem_top g)
  rw [hcent] at hcTop
  simpa using hcTop

theorem lemmaNat_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 3 ≤ Nat.card F) {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) M)
    (Nsub : Subrepresentation ρ) (hNnat : IsNaturalModule Nsub.toRepresentation)
    (hQ : ∀ g (m : M), ρ g m - m ∈ Nsub.toSubmodule)
    (hcent : fixedSub ρ ⊤ = ⊥) :
    fixedSub ρ (utri F) ≤ Nsub.toSubmodule := by
  classical
  have hCD : fixedSub ρ (utri F) ⊓ fixedSub ρ (torus F) = ⊥ :=
    fixedSub_utri_inf_torus_eq_bot hF ρ Nsub hNnat hQ hcent
  have hcardD : Nat.card (torus F) = Nat.card Fˣ := by
    rw [card_torus, Nat.card_units]
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcardF⟩ := FiniteField.card F 2
  have hcardFn : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcardF
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units, hcardFn]
    have hn : 0 < (n : ℕ) := by
      by_contra hn0
      have h1 : 2 ^ (n : ℕ) = 1 := by rw [show (n : ℕ) = 0 by omega, pow_zero]
      rw [h1] at hcardFn
      omega
    have heven : Even (2 ^ (n : ℕ)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) heven (by norm_num)
  obtain ⟨k, hk⟩ := hcardD.symm ▸ hodd
  have hcast : (Nat.card (torus F) : ZMod 2) = 1 := by
    rw [hk]
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  have hDA : torus F ≤
      Subgroup.normalizer (utri F : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [normalizer_utri]
    exact torus_le_borel
  let D : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := torus F
  have hCD' : fixedSub ρ (utri F) ⊓ fixedSub ρ D = ⊥ := hCD
  have hcardD' : Nat.card D = Nat.card Fˣ := hcardD
  letI : Fintype D := Fintype.ofFinite D
  intro c hc
  let πc : M := ∑ d : D, ρ (d : Matrix.SpecialLinearGroup (Fin 2) F) c
  have hπD : πc ∈ fixedSub ρ D := by
    rw [mem_fixedSub]
    intro d hd
    change ρ d πc = πc
    rw [show πc = ∑ e : D, ρ (e : Matrix.SpecialLinearGroup (Fin 2) F) c from rfl, map_sum]
    have hcongr : (∑ e : D, ρ d (ρ (e : Matrix.SpecialLinearGroup (Fin 2) F) c)) =
        ∑ e : D, ρ (d * (e : Matrix.SpecialLinearGroup (Fin 2) F)) c := by
      exact Finset.sum_congr rfl fun e _ => by
        rw [← Module.End.mul_apply, ← map_mul]
    rw [hcongr]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨d, hd⟩ : D))
      (fun e : D => ρ (d * (e : Matrix.SpecialLinearGroup (Fin 2) F)) c)
      (fun e : D => ρ (e : Matrix.SpecialLinearGroup (Fin 2) F) c)
      (fun e => rfl)
  have hπA : πc ∈ fixedSub ρ (utri F) := by
    rw [mem_fixedSub]
    intro a₁ ha₁
    change ρ a₁ πc = πc
    rw [show πc = ∑ e : D, ρ (e : Matrix.SpecialLinearGroup (Fin 2) F) c from rfl, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hdA : (d : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ * a₁ *
        (d : Matrix.SpecialLinearGroup (Fin 2) F) ∈ utri F := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hDA (D.inv_mem d.2)) a₁).mp ha₁
    calc ρ a₁ (ρ (d : Matrix.SpecialLinearGroup (Fin 2) F) c)
        = ρ (a₁ * (d : Matrix.SpecialLinearGroup (Fin 2) F)) c := by
          rw [← Module.End.mul_apply, ← map_mul]
      _ = ρ ((d : Matrix.SpecialLinearGroup (Fin 2) F) *
            ((d : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ * a₁ *
              (d : Matrix.SpecialLinearGroup (Fin 2) F))) c := by
          rw [show a₁ * (d : Matrix.SpecialLinearGroup (Fin 2) F) =
            (d : Matrix.SpecialLinearGroup (Fin 2) F) *
              ((d : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ * a₁ *
                (d : Matrix.SpecialLinearGroup (Fin 2) F)) by group]
      _ = ρ (d : Matrix.SpecialLinearGroup (Fin 2) F)
            (ρ ((d : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ * a₁ *
              (d : Matrix.SpecialLinearGroup (Fin 2) F)) c) := by
          rw [map_mul, Module.End.mul_apply]
      _ = ρ (d : Matrix.SpecialLinearGroup (Fin 2) F) c := by rw [mem_fixedSub.mp hc _ hdA]
  have hπzero : πc = 0 := by
    have hmem : πc ∈ fixedSub ρ (utri F) ⊓ fixedSub ρ D :=
      Submodule.mem_inf.mpr ⟨hπA, hπD⟩
    rw [hCD'] at hmem
    simpa using hmem
  have hsmul : (Fintype.card D) • c = c := by
    rw [← Nat.card_eq_fintype_card]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) (Nat.card D) c]
    have hcastD : (Nat.card D : ZMod 2) = 1 := by
      rw [hcardD', ← hcardD]; exact hcast
    rw [hcastD, one_smul]
  have hsum : c + πc = ∑ d : D, (c + ρ (d : Matrix.SpecialLinearGroup (Fin 2) F) c) := by
    rw [show πc = ∑ d : D, ρ (d : Matrix.SpecialLinearGroup (Fin 2) F) c from rfl,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hsmul]
  have hNsum : ∑ d : D, (c + ρ (d : Matrix.SpecialLinearGroup (Fin 2) F) c) ∈
      Nsub.toSubmodule := by
    apply Nsub.toSubmodule.sum_mem
    intro d _
    have h := Nsub.toSubmodule.neg_mem (hQ (d : Matrix.SpecialLinearGroup (Fin 2) F) c)
    simpa [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm] using h
  have hcN : c + πc ∈ Nsub.toSubmodule := by
    rw [hsum]
    exact hNsum
  rw [hπzero, add_zero] at hcN
  exact hcN

end CFSG.Quasithin.Stroth
