module

public import CFSG.Quasithin.SteinbergBSPGroupFixedSpace

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

variable {X : Type*} [Group X]

@[instance_reducible] private noncomputable def cgOfComm {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := hc }

@[instance_reducible] private noncomputable def emOfExp (p : ℕ) [NeZero p] {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) (hp : ∀ a : A, a ^ p = 1) :
    letI := cgOfComm hc
    Module (ZMod p) (Additive A) :=
  letI := cgOfComm hc
  AddCommMonoid.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hp _

section Linear

variable {p : ℕ} [Fact p.Prime] {U : Subgroup X} [U.Normal]

theorem le_centralizer_of_le_centralizer_fix [Finite X] {P L : Subgroup X}
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUp : ∀ a ∈ U, a ^ p = 1) (hP : IsPGroup p P)
    (hLperf : ⁅L, L⁆ = L) (hPL : ⁅P, L⁆ ≤ Subgroup.centralizer (U : Set X))
    (hLW : L ≤ Subgroup.centralizer
      ((U ⊓ Subgroup.centralizer (P : Set X) : Subgroup X) : Set X)) :
    L ≤ Subgroup.centralizer (U : Set X) := by
  classical
  have hc : ∀ a b : U, a * b = b * a := fun a b => Subtype.ext (hUc a a.2 b b.2)
  have hpz : ∀ a : U, a ^ p = 1 := fun a => Subtype.ext (by simpa using hUp a a.2)
  let _ := cgOfComm hc
  let _ := emOfExp p hc hpz
  have : Finite (Additive U) := inferInstanceAs (Finite U)
  have : FiniteDimensional (ZMod p) (Additive U) := Module.Finite.of_finite
  let ρf : X → (Additive U ≃ₗ[ZMod p] Additive U) := fun x =>
    (MulEquiv.toAdditive (MulAut.conjNormal x : MulAut U)).toLinearEquiv
      (ZMod.map_smul (MulEquiv.toAdditive (MulAut.conjNormal x : MulAut U)))
  have hρf : ∀ (x : X) (a : Additive U),
      ρf x a = Additive.ofMul ((MulAut.conjNormal x : MulAut U) (Additive.toMul a)) :=
    fun _ _ => rfl
  let ρ : X →* (Additive U ≃ₗ[ZMod p] Additive U) :=
    { toFun := ρf
      map_one' := LinearEquiv.ext fun a => by
        rw [hρf, map_one]
        rfl
      map_mul' := fun g h => LinearEquiv.ext fun a => by
        rw [hρf, map_mul]
        rfl }
  have hρ : ∀ (x : X) (a : Additive U), ((Additive.toMul (ρ x a) : U) : X) =
      x * (Additive.toMul a : U) * x⁻¹ := fun x a => by
    change (((MulAut.conjNormal x : MulAut U) (Additive.toMul a) : U) : X) = _
    rw [MulAut.conjNormal_apply]
  have hρ1 : ∀ c ∈ Subgroup.centralizer (U : Set X), ρ c = 1 := fun c hc' =>
    LinearEquiv.ext fun a => by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hρ, (Subgroup.mem_centralizer_iff.1 hc' _ (Additive.toMul a).2).symm,
        mul_inv_cancel_right]
      rfl
  set B := P.map ρ with hB
  have hBp : IsPGroup p B := hP.map ρ
  have hkey := CFSG.Quasithin.SteinbergBS.commuting_p_group_fixed_space_kernel B hBp
  have hA : L.map ρ ≤ Subgroup.centralizer (B : Set (Additive U ≃ₗ[ZMod p] Additive U)) ⊓
      centSub (MonoidHom.id _) (fixGL B) := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      have hcomm : ⁅q, l⁆ ∈ Subgroup.centralizer (U : Set X) :=
        hPL (Subgroup.commutator_mem_commutator hq hl)
      have h1 := hρ1 _ hcomm
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : ρ q * ρ l = ρ l * ρ q := by
        calc ρ q * ρ l = (ρ q * ρ l * (ρ q)⁻¹ * (ρ l)⁻¹) * (ρ l * ρ q) := by group
          _ = ρ l * ρ q := by rw [h1, one_mul]
      exact h2
    · intro a ha
      have hfix : ∀ q ∈ P, q * (Additive.toMul a : U) = (Additive.toMul a : U) * q := by
        intro q hq
        have h1 := ha (ρ q) ⟨q, hq, rfl⟩
        have h2 := congrArg (fun e : Additive U => ((Additive.toMul e : U) : X)) h1
        simp only [MonoidHom.id_apply] at h2
        rw [hρ] at h2
        calc q * (Additive.toMul a : U) = q * (Additive.toMul a : U) * q⁻¹ * q := by group
          _ = (Additive.toMul a : U) * q := by rw [h2]
      have hmem : ((Additive.toMul a : U) : X) ∈
          (U ⊓ Subgroup.centralizer (P : Set X) : Subgroup X) :=
        ⟨(Additive.toMul a).2, Subgroup.mem_centralizer_iff.2 fun q hq => hfix q hq⟩
      have h3 := Subgroup.mem_centralizer_iff.1 (hLW hl) _ hmem
      apply Additive.toMul.injective
      apply Subtype.ext
      show ((Additive.toMul (ρ l a) : U) : X) = (Additive.toMul a : U)
      rw [hρ, ← h3, mul_inv_cancel_right]
  have hAp : IsPGroup p (L.map ρ) := hkey.to_le hA
  have hAperf : Group.IsPerfect (L.map ρ) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hLperf]
  have hA1 : L.map ρ = ⊥ := by
    have : Finite (Additive U ≃ₗ[ZMod p] Additive U) :=
      CFSG.Quasithin.SteinbergBS.finite_linearEquiv
    have : Finite (L.map ρ) := inferInstance
    have : Group.IsNilpotent (L.map ρ) := hAp.isNilpotent
    have : Group.IsSolvable (L.map ρ) := inferInstance
    by_contra hne
    have : Nontrivial (L.map ρ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable (L.map ρ) inferInstance
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hl1 : ρ l = 1 := by
    have : ρ l ∈ L.map ρ := ⟨l, hl, rfl⟩
    rwa [hA1, Subgroup.mem_bot] at this
  have h1 := congrArg (fun e : Additive U => ((Additive.toMul e : U) : X))
    (LinearEquiv.congr_fun hl1 (Additive.ofMul ⟨u, hu⟩))
  simp only [hρ, toMul_ofMul, LinearEquiv.coe_one, id_eq] at h1
  calc u * l = l * u * l⁻¹ * l := by rw [h1]
    _ = l * u := by group

end Linear

theorem le_pCore_of_normal_of_isPGroup {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    (hN : N.Normal) (hp : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup ⟨hN, hp⟩

theorem linear_normal_perfect_local_reduced_module {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (L : Subgroup X) [hLn : L.Normal] (hLperf : ⁅L, L⁆ = L)
    [hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore p ↥L)]
    (_hnab : ∃ a b : ↥L ⧸ CFSG.pCore p ↥L, a * b ≠ b * a) (hXL : IsPGroup p (X ⧸ L))
    {R P U W V : Subgroup X} (hR : R = (CFSG.pCore p ↥L).map L.subtype)
    (hP : P = CFSG.pCore p X)
    (hU : ∀ x : X, x ∈ U ↔ x ∈ R ∧ (∀ r ∈ R, x * r = r * x) ∧ x ^ p = 1)
    (hW : W = U ⊓ Subgroup.centralizer (P : Set X)) (hV : V = ⁅W, L⁆) (hUL : ⁅U, L⁆ ≠ ⊥) :
    V ≠ ⊥ ∧ IsElementaryAbelian p V ∧ V.Normal ∧
      (V ≤ P ∧ V ≤ Subgroup.centralizer (P : Set X) ∧ ∀ v ∈ V, v ^ p = 1) ∧
      ⁅V, L⁆ = V ∧ L ⊓ Subgroup.centralizer (V : Set X) = R ∧
      Subgroup.centralizer (V : Set X) = P := by
  classical
  have hRL : R ≤ L := by
    rw [hR]
    exact Subgroup.map_subtype_le _
  have hRn : R.Normal := by
    rw [hR]
    refine ⟨fun r hr x => ?_⟩
    obtain ⟨r', hr', rfl⟩ := hr
    have hc := (inferInstance : (CFSG.pCore p ↥L).Characteristic).fixed (MulAut.conjNormal x)
    have h1 : r' ∈ (CFSG.pCore p ↥L).comap (MulAut.conjNormal x).toMonoidHom := by
      rw [hc]
      exact hr'
    refine ⟨_, h1, ?_⟩
    change ((MulAut.conjNormal x r' : L) : X) = _
    rw [MulAut.conjNormal_apply]
    rfl
  have hRp : IsPGroup p R := by
    rw [hR]
    exact (CFSG.pCore_isPGroup (p := p) (G := L)).map L.subtype
  have hPn : P.Normal := by
    rw [hP]
    exact CFSG.pCore_normal
  have hPp : IsPGroup p P := by
    rw [hP]
    exact CFSG.pCore_isPGroup
  have hRP : R ≤ P := by
    rw [hP]
    exact le_pCore_of_normal_of_isPGroup hRn hRp
  have hPLR : P ⊓ L ≤ R := by
    intro x hx
    have hN : ((P ⊓ L).subgroupOf L).Normal := Subgroup.Normal.subgroupOf inferInstance L
    have hNp : IsPGroup p ((P ⊓ L).subgroupOf L) :=
      (hPp.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hle := le_pCore_of_normal_of_isPGroup hN hNp
    rw [hR]
    exact ⟨⟨x, hx.2⟩, hle (show (⟨x, hx.2⟩ : L) ∈ (P ⊓ L).subgroupOf L from hx), rfl⟩
  have hcommPL : ⁅P, L⁆ ≤ R := (Subgroup.commutator_le_inf P L).trans hPLR
  have hUR : U ≤ R := fun x hx => ((hU x).1 hx).1
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    ((hU a).1 ha).2.1 b (hUR hb)
  have hUp : ∀ a ∈ U, a ^ p = 1 := fun a ha => ((hU a).1 ha).2.2
  have hRcU : R ≤ Subgroup.centralizer (U : Set X) := fun r hr =>
    Subgroup.mem_centralizer_iff.2 fun u hu => ((hU u).1 hu).2.1 r hr
  have hUn : U.Normal := by
    refine ⟨fun u hu x => (hU _).2 ⟨hRn.conj_mem u (hUR hu) x, fun r hr => ?_, ?_⟩⟩
    · have hr' : x⁻¹ * r * x ∈ R := by simpa using hRn.conj_mem r hr x⁻¹
      have h := ((hU u).1 hu).2.1 _ hr'
      calc x * u * x⁻¹ * r = x * (u * (x⁻¹ * r * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * r * x) * u) * x⁻¹ := by rw [h]
        _ = r * (x * u * x⁻¹) := by group
    · rw [conj_pow, hUp u hu, mul_one, mul_inv_cancel]
  have hWn : W.Normal := by
    rw [hW]
    exact Subgroup.normal_inf_normal _ _
  have hWU : W ≤ U := by
    rw [hW]
    exact inf_le_left
  have hWP : W ≤ Subgroup.centralizer (P : Set X) := by
    rw [hW]
    exact inf_le_right
  have hVW : V ≤ W := by
    rw [hV]
    exact Subgroup.commutator_le_left W L
  have hVn : V.Normal := by
    rw [hV]
    infer_instance
  have hVU : V ≤ U := hVW.trans hWU
  have hV1 : V ≠ ⊥ := by
    intro hV0
    rw [hV, Subgroup.commutator_eq_bot_iff_le_centralizer] at hV0
    have hLW : L ≤ Subgroup.centralizer
        ((U ⊓ Subgroup.centralizer (P : Set X) : Subgroup X) : Set X) := by
      rw [← hW]
      exact Subgroup.le_centralizer_iff.1 hV0
    have hLU := le_centralizer_of_le_centralizer_fix hUc hUp hPp hLperf
      (hcommPL.trans hRcU) hLW
    apply hUL
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.1 hLU
  have hVL : ⁅V, L⁆ = V := by
    refine le_antisymm (Subgroup.commutator_le_left V L) ?_
    set N := ⁅V, L⁆ with hN
    have : N.Normal := by rw [hN]; infer_instance
    set π := QuotientGroup.mk' N
    have h1 : ⁅⁅W.map π, L.map π⁆, L.map π⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, ← hV, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
    have h2 : ⁅⁅L.map π, W.map π⁆, L.map π⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (L.map π)]
      exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    have hLπ : ⁅L.map π, L.map π⁆ = L.map π := by
      rw [← Subgroup.map_commutator, hLperf]
    rw [hLπ, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk',
      Subgroup.commutator_comm, ← hV] at h3
    exact h3
  have hRcV : R ≤ Subgroup.centralizer (V : Set X) :=
    hRcU.trans (Subgroup.centralizer_le hVU)
  have hLV : L ⊓ Subgroup.centralizer (V : Set X) = R := by
    refine le_antisymm ?_ (le_inf hRL hRcV)
    set K := (Subgroup.centralizer (V : Set X)).subgroupOf L with hK
    have hKn : K.Normal := Subgroup.Normal.subgroupOf inferInstance L
    have hRK : CFSG.pCore p ↥L ≤ K := by
      intro r hr
      have : (r : X) ∈ R := by
        rw [hR]
        exact ⟨r, hr, rfl⟩
      exact hRcV this
    set π := QuotientGroup.mk' (CFSG.pCore p ↥L)
    have hKπn : (K.map π).Normal := Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective _)
    rcases hKπn.eq_bot_or_eq_top with h | h
    · intro x hx
      have hxK : (⟨x, hx.1⟩ : L) ∈ K := hx.2
      have : π ⟨x, hx.1⟩ ∈ K.map π := Subgroup.mem_map_of_mem π hxK
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      rw [hR]
      exact ⟨_, this, rfl⟩
    · exfalso
      have hKtop : K = ⊤ := by
        have := Subgroup.comap_map_eq π K
        rw [h, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hRK] at this
        exact this.symm
      apply hV1
      rw [← hVL, Subgroup.commutator_eq_bot_iff_le_centralizer]
      refine Subgroup.le_centralizer_iff.1 fun l hl => ?_
      have : (⟨l, hl⟩ : L) ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
      exact this
  have hPV : P ≤ Subgroup.centralizer (V : Set X) :=
    Subgroup.le_centralizer_iff.1 (hVW.trans hWP)
  have hCV : Subgroup.centralizer (V : Set X) = P := by
    refine le_antisymm ?_ hPV
    rw [hP]
    refine le_pCore_of_normal_of_isPGroup inferInstance fun c => ?_
    obtain ⟨k, hk⟩ := hXL (QuotientGroup.mk (c : X))
    have hckL : (c : X) ^ p ^ k ∈ L := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
      exact hk
    have hckR : (c : X) ^ p ^ k ∈ R := by
      rw [← hLV]
      exact ⟨hckL, Subgroup.pow_mem _ c.2 _⟩
    obtain ⟨m, hm⟩ := hRp ⟨_, hckR⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : ((c : X) ^ p ^ k) ^ p ^ m = 1 := congrArg Subtype.val hm
    rw [Subgroup.coe_pow, pow_add, pow_mul, hm', Subgroup.coe_one]
  refine ⟨hV1, ?_, hVn, ⟨hVU.trans (hUR.trans hRP), hVW.trans hWP, fun v hv => hUp v (hVU hv)⟩,
    hVL, hLV, hCV⟩
  exact
    { is_comm := ⟨fun a b => Subtype.ext (hUc a (hVU a.2) b (hVU b.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun v =>
        Subtype.ext (by simpa using hUp v (hVU v.2)) }

end CFSG.Quasithin.SteinbergBQ
