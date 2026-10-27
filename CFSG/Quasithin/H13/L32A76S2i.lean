module

public import CFSG.Quasithin.H13.L32A76S2h

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx

variable (C : Ctx G T L V H Y)
include C

theorem conj_V₁ {x v : G} (hx : x ∈ H) (hv : v ∈ fsuV1 T V) : x * v * x⁻¹ = v := by
  have h2 := C.h98.card_V₁
  have hv' : x * v * x⁻¹ ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp (C.h91.H_normalizes_V₁ hx) v).mp hv
  by_cases h1 : v = 1
  · rw [h1]; group
  obtain ⟨p, q, hpq, hpq'⟩ := Nat.card_eq_two_iff.mp h2
  have hall : ∀ z : ↥(fsuV1 T V), z = p ∨ z = q := fun z => by
    have : z ∈ ({p, q} : Set _) := hpq' ▸ Set.mem_univ z
    simpa using this
  have hne : x * v * x⁻¹ ≠ 1 := fun h => h1 (by
    have := congrArg (fun z => x⁻¹ * z * x) h
    simpa [mul_assoc] using this)
  set z₁ : ↥(fsuV1 T V) := ⟨v, hv⟩
  set z₂ : ↥(fsuV1 T V) := ⟨_, hv'⟩
  have hz₁ : z₁ ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  have hz₂ : z₂ ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have h1o := hall 1
  have hz : z₂ = z₁ := by
    rcases hall z₁ with e1 | e1 <;> rcases hall z₂ with e2 | e2 <;> rcases h1o with e0 | e0 <;>
      first
        | exact e2.trans e1.symm
        | exact absurd (e1.trans e0.symm) hz₁
        | exact absurd (e2.trans e0.symm) hz₂
  exact congrArg Subtype.val hz

theorem K_le_centralizer [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good C γ γ' g e₁ e₂ b) :
    oTwoUpper (C.Pe e₂) ≤
      Subgroup.centralizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxP, hxo⟩ := hx
  obtain ⟨hxH, hxe⟩ := (C.mem_Pe).mp hxP
  have hA : ∀ a ∈ (⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G),
      x * a * x⁻¹ = a * (a⁻¹ * (x * a * x⁻¹)) ∧ a⁻¹ * (x * a * x⁻¹) ∈ fsuV1 T V := by
    intro a ha
    refine ⟨by group, ?_⟩
    rw [D.A_eq] at ha
    obtain ⟨z, hz, rfl⟩ := ha
    have hfix : FixR.rho C.h91 ⟨x, hxH⟩ (C.piU z) = C.piU z := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxe
      rw [← hj]
      have hw : C.piU z ∈ cw e₁ := D.cw_le hz
      have h1 : ∀ n : ℕ, (e₂ ^ n) (C.piU z) = C.piU z := fun n =>
        pow_apply_eq_self (D.lines.fix₁ _ hw) n
      rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast, h1]
      · rw [zpow_neg, zpow_natCast]
        have := h1 n
        conv_lhs => rw [← this]
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have h2 := C.piU_conj ⟨x, hxH⟩ z
    rw [hfix, eq_comm, piU_eq_iff] at h2
    exact h2
  have hx2 : x ^ 2 ∈ Subgroup.centralizer
      ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨e1, hc⟩ := hA a ha
    have hcx : x * (a⁻¹ * (x * a * x⁻¹)) * x⁻¹ = a⁻¹ * (x * a * x⁻¹) := C.conj_V₁ hxH hc
    have hsq : (a⁻¹ * (x * a * x⁻¹)) * (a⁻¹ * (x * a * x⁻¹)) = 1 := by
      have h1 := pow_card_eq_one' (G := ↥(fsuV1 T V)) (x := ⟨_, hc⟩)
      rw [C.h98.card_V₁] at h1
      simpa [pow_two] using congrArg Subtype.val h1
    have h1 : x ^ 2 * a * (x ^ 2)⁻¹ = a := by
      calc x ^ 2 * a * (x ^ 2)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * (a * (a⁻¹ * (x * a * x⁻¹))) * x⁻¹ := by rw [← e1]
        _ = (x * a * x⁻¹) * (x * (a⁻¹ * (x * a * x⁻¹)) * x⁻¹) := by group
        _ = (a * (a⁻¹ * (x * a * x⁻¹))) * (a⁻¹ * (x * a * x⁻¹)) := by rw [hcx, ← e1]
        _ = a * ((a⁻¹ * (x * a * x⁻¹)) * (a⁻¹ * (x * a * x⁻¹))) := by group
        _ = a := by rw [hsq, mul_one]
    calc a * x ^ 2 = x ^ 2 * a * (x ^ 2)⁻¹ * x ^ 2 := by rw [h1]
      _ = x ^ 2 * a := by group
  have hcop : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.mpr hxo
  exact (Subgroup.zpowers_le.mpr hx2) (A4.mem_zpowers_pow_of_coprime hcop)

theorem exists_ell [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good C γ γ' g e₁ e₂ b) :
    ∃ l₀ : ↥H, (l₀ : G) ∈ l1 T L V ∧ (l₀ : G) ∉ pCoreOf 2 (l1 T L V) ∧ (l₀ : G) ^ 3 = 1 ∧
      FixR.rho C.h91 l₀ ^ 3 = 1 ∧
      (∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
        FixR.rho C.h91 l₀ * e = e * FixR.rho C.h91 l₀) ∧
      FixR.rho C.h91 l₀ * b = b * FixR.rho C.h91 l₀ ∧
      ∀ w, FixR.rho C.h91 l₀ w = w → w = 1 := by
  obtain ⟨l, hl, hlO, hl3⟩ := M76.exists_cube_not_mem C.S C.h1222 C.h1332 C.h1334
  have hlH := Setting147.l1H' C.S hl
  set l₀ : ↥H := ⟨l, hlH⟩
  have hρ3 : FixR.rho C.h91 l₀ ^ 3 = 1 := by
    rw [← map_pow, show l₀ ^ 3 = 1 from Subtype.ext (by simpa using hl3), map_one]
  refine ⟨l₀, hl, hlO, hl3, hρ3, fun e he => ?_, ?_, fun w hw =>
    M76.rho_fix_eq_one C.S C.h1222 C.h1332 C.h1334 C.h91 C.hHL hl hlO w hw⟩
  · have hc := M76.commute_of_rank_four C.sq_eq_one (fun a ha c hc => C.comm_E ha hc)
      (fun e he => C.pow_five_E he) C.card_E hρ3
      (fun e he => C.conj_mem_E (C.rho_mem_X l₀) he) D.e₁E D.lines.ne_one₁ D.lines.rk₁ he
    calc FixR.rho C.h91 l₀ * e = FixR.rho C.h91 l₀ * e * (FixR.rho C.h91 l₀)⁻¹ *
        FixR.rho C.h91 l₀ := by group
      _ = e * FixR.rho C.h91 l₀ := by rw [hc]
  · obtain ⟨u₀, hu₀, hbu⟩ := (FixR.mem_autOn_tilde_iff C.h91 (C.h98.Uγ_le_H D.s)).mp D.bB
    rw [← hbu]
    have hcomm := Setting147.comm_Uγ_l1 C.S C.h98 C.h1332 C.hHL D.s
    exact FixR.rho_comm_of_mem C.h91 (x := l₀) (y := u₀) (by
      have h1 := hcomm (Subgroup.commutator_mem_commutator hu₀ hl)
      have h2 := Subgroup.inv_mem _ h1
      rw [commutatorElement_def] at h2
      have e : ((u₀ : G) * l * (u₀ : G)⁻¹ * l⁻¹)⁻¹ = l * (u₀ : G) * l⁻¹ * (u₀ : G)⁻¹ := by group
      rw [e] at h2
      exact h2)

theorem comm_mem_V₁_of_comm [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good C γ γ' g e₁ e₂ b) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hUS : F8.Uγ V H (g : G) ≤ S) (t : ↥H) (ht : (t : G) ∈ S ⊓ C.Ne e₁)
    (hK : ∀ k : ↥H, (k : G) ∈ oTwoUpper (C.Pe e₂) →
      FixR.rho C.h91 k * FixR.rho C.h91 t = FixR.rho C.h91 t * FixR.rho C.h91 k) :
    ∀ a ∈ (⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G),
      (t : G) * a * (t : G)⁻¹ * a⁻¹ ∈ fsuV1 T V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hL := D.lines
  have hV := C.sq_eq_one
  set x := FixR.rho C.h91 t with hx
  have hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hS2 ⟨t, ht.1⟩
    refine ⟨k, ?_⟩
    rw [hx, ← map_pow]
    have : t ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  obtain ⟨z, hzK, -, -, he₂z⟩ := C.exists_mem_K hL.h5₂ hL.symm.ne_one₁ D.e₂E
  have hxe₂ : x * e₂ = e₂ * x := by
    have h1 := (hK z hzK).symm
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp he₂z
    rw [← hj]
    exact (Commute.zpow_right h1 j).eq
  have htriv₂ := trivial_of_comm hV hx2 hxe₂ hL.h5₂ (fun u hu => mem_map_commHom_of_comm hxe₂ hu)
    (map_commHom_invariant rfl (fun _ _ => Subgroup.mem_top _)) hL.symm.fpf₁
    (rk_cond_five hL.rk₂)
  obtain ⟨l₀, hl₀, hl₀O, -, hℓ3, hℓE, hℓb, hℓfix⟩ := C.exists_ell D
  set ℓ := FixR.rho C.h91 l₀ with hℓ
  have hxℓ : x * ℓ = ℓ * x := by
    have hcl : (t : G) * l₀ * (t : G)⁻¹ * (l₀ : G)⁻¹ ∈ l1 T L V := by
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hl₀)
      exact (Subgroup.mem_normalizer_iff.mp (C.hHL t.2) _).mp hl₀
    by_contra hne
    have hO : (t : G) * l₀ * (t : G)⁻¹ * (l₀ : G)⁻¹ ∉ pCoreOf 2 (l1 T L V) := by
      intro hm
      have hOQ : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 H := by
        rw [← Setting147.inf_O2H C.S C.hHL]; exact inf_le_left
      exact hne (FixR.rho_comm_of_mem C.h91 (hOQ hm))
    have hne2 : cw e₂ ≠ ⊥ := by
      intro h
      have := hL.rk₂
      rw [h, rk_bot] at this
      omega
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne2
    have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hℓe₂ : ℓ * e₂ = e₂ * ℓ := hℓE e₂ D.e₂E
    have hℓw : ℓ⁻¹ w ∈ cw e₂ := by
      have hc : ℓ⁻¹ * e₂ = e₂ * ℓ⁻¹ := by
        calc ℓ⁻¹ * e₂ = ℓ⁻¹ * (e₂ * ℓ) * ℓ⁻¹ := by group
          _ = ℓ⁻¹ * (ℓ * e₂) * ℓ⁻¹ := by rw [hℓe₂]
          _ = e₂ * ℓ⁻¹ := by group
      exact mem_map_commHom_of_comm hc hw
    have hxinv : x⁻¹ (ℓ⁻¹ w) = ℓ⁻¹ w := by
      have := htriv₂ _ hℓw
      conv_lhs => rw [← this]
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hfix : FixR.rho C.h91 (t * l₀ * t⁻¹ * l₀⁻¹) w = w := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      simp only [MulAut.mul_apply]
      rw [hxinv, show ℓ (ℓ⁻¹ w) = w by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply],
        htriv₂ w hw]
    exact hw1' (M76.rho_fix_eq_one C.S C.h1222 C.h1332 C.h1334 C.h91 C.hHL hcl hO w hfix)
  have hcwb := C.rho_mem_cw D hS2 hUS t ht
  have hℓcw : ∀ w ∈ cw b, ℓ w ∈ cw b := fun w hw => mem_map_commHom_of_comm hℓb hw
  have hℓfix' : cw b ⊓ fixV (Subgroup.zpowers ℓ) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact hℓfix w (mem_fixV_zpowers_iff.mp hw.2)
  have htrivb := trivial_of_comm hV hx2 hxℓ hℓ3 hcwb hℓcw hℓfix' (rk_cond_three D.rk_cw)
  intro a ha
  have ha' := ha
  rw [D.A_eq] at ha'
  obtain ⟨z', hz', rfl⟩ := ha'
  have h1 := C.piU_conj t z'
  rw [htrivb _ hz', eq_comm, piU_eq_iff] at h1
  have h2 : (t : G) * z' * (t : G)⁻¹ * (z' : G)⁻¹ =
      (z' : G) * ((z' : G)⁻¹ * ((t : G) * z' * (t : G)⁻¹)) * (z' : G)⁻¹ := by group
  show (t : G) * (z' : G) * (t : G)⁻¹ * (z' : G)⁻¹ ∈ fsuV1 T V
  rw [h2]
  exact (Subgroup.mem_normalizer_iff.mp (C.h91.H_normalizes_V₁ (C.UH_le_H z'.2)) _).mp h1

end Ctx

end CFSG.Quasithin.H13.L32A.S2

end
