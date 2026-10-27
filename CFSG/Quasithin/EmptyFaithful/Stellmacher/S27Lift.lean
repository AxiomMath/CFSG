module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27LiftDef
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

theorem exists_eq_act_mul_inv {n : ℕ} (M : Model n) (σ : Equiv.Perm (Fin n)) (h2 : σ ^ 2 = 1)
    (hc : idx M σ * idx M σ = Nat.card M.W) {u : M.W} (hu : M.act σ u = u) :
    ∃ m : M.W, u = M.act σ m * m⁻¹ := by
  let φ : M.W →* M.W :=
    { toFun := fun m => M.act σ m * m⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hker : φ.ker = fixW M (Subgroup.zpowers σ) := by
    ext m
    rw [MonoidHom.mem_ker, mem_fixW_zpowers]
    exact mul_inv_eq_one
  have hact2 : ∀ m, M.act σ (M.act σ m) = m := by
    intro m
    rw [← MulAut.mul_apply, ← map_mul, ← sq, h2, map_one]
    rfl
  have hrange : φ.range ≤ fixW M (Subgroup.zpowers σ) := by
    rintro _ ⟨m, rfl⟩
    rw [mem_fixW_zpowers]
    show M.act σ (M.act σ m * m⁻¹) = M.act σ m * m⁻¹
    rw [map_mul, map_inv, hact2]
    have h := inv_eq_of_mul_eq_one_right (M.sq (M.act σ m * m⁻¹))
    rwa [mul_inv_rev, inv_inv] at h
  have hN : 0 < Nat.card M.W := Nat.card_pos
  have h1 : idx M σ * Nat.card (fixW M (Subgroup.zpowers σ)) = Nat.card M.W :=
    Subgroup.index_mul_card _
  have h2' : Nat.card M.W = Nat.card (M.W ⧸ φ.ker) * Nat.card φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h3 : Nat.card (M.W ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hipos : 0 < idx M σ := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hc; omega
  have ha : Nat.card (fixW M (Subgroup.zpowers σ)) = idx M σ :=
    Nat.eq_of_mul_eq_mul_left hipos (h1.trans hc.symm)
  have hr : Nat.card φ.range = idx M σ := by
    rw [h3, show Nat.card φ.ker = idx M σ by rw [hker]; exact ha] at h2'
    exact Nat.eq_of_mul_eq_mul_right hipos (h2'.symm.trans hc.symm)
  have heq : φ.range = fixW M (Subgroup.zpowers σ) :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [ha, hr])
  have hmem : u ∈ φ.range := by rw [heq, mem_fixW_zpowers]; exact hu
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, hm.symm⟩

theorem exists_eq_act_mul_inv_of_involution {M : Model 5} (hM : M = nat ∨ M = orth)
    {σ : Equiv.Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ ^ 2 = 1)
    (hs : σ ∈ alternatingGroup (Fin 5)) {u : M.W} (hu : M.act σ u = u) :
    ∃ m : M.W, u = M.act σ m * m⁻¹ := by
  refine exists_eq_act_mul_inv M σ h2 ?_ hu
  rcases hM with rfl | rfl
  · rw [idx_nat, card_nat]
    simp [h1, h2]
  · rw [idx_orth, card_orth]
    simp [h1, h2, Equiv.Perm.mem_alternatingGroup.mp hs]

theorem secLiftFix : SecLiftFix := by
  intro G _ _ X V C hq hn hV hpc hCV hsec o ho ho2 hCo f hf hfc
  obtain ⟨M, hM, h⟩ : ∃ M : Model 5, (M = nat ∨ M = orth) ∧ IsModelSec M X C V := by
    rcases hsec with h | h
    · exact ⟨nat, Or.inl rfl, h⟩
    · exact ⟨orth, Or.inr rfl, h⟩
  have CCV : ∀ {x : G}, x ∈ C → x ∈ V := fun hx => hCV hx
  have hceq := h.cSecIn_eq_pCoreOf hq
  obtain ⟨hnC, θ, β, hθs, hθk, hsd⟩ := h
  have hoX : o ∈ X := oTwoRes_le X ho
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have h := hV.1.is_comm.comm (⟨x, hx⟩ : V) ⟨y, hy⟩
    simpa using congrArg Subtype.val h
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← sq]; exact hV.2 x hx
  have hconj : ∀ x ∈ V, o * x * o⁻¹ ∈ V := fun x hx => hsd.conj_mem hoX hx
  have hcen : ∀ y ∈ pCoreOf 2 X, ∀ x ∈ V, y * x = x * y := fun y hy x hx =>
    (Subgroup.mem_centralizer_iff.mp (hpc hy) x hx).symm
  have hsq1 : θ ⟨o, hoX⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have h1 : (⟨o, hoX⟩ : ↥X) ^ 2 = ⟨o ^ 2, X.pow_mem hoX 2⟩ := rfl
    rw [h1, mem_cSecIn_iff_of_ker hθk (X.pow_mem hoX 2) |>.mpr (hceq ▸ ho2)]
  by_cases hσ : θ ⟨o, hoX⟩ = 1
  · have hop : o ∈ pCoreOf 2 X := hceq ▸ (mem_cSecIn_iff_of_ker hθk hoX).mp hσ
    have := hcen o hop f hf
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  · have hσA : θ ⟨o, hoX⟩ ∈ alternatingGroup (Fin 5) :=
      (mem_oTwoRes_sup_iff hθs hθk hoX).mp ((le_sup_left : oTwoRes X ≤ oTwoRes X ⊔ cSecIn X C V) ho)
    have hfix : ∀ u : M.W, M.act (θ ⟨o, hoX⟩) u = u →
        ∃ m : M.W, u = M.act (θ ⟨o, hoX⟩) m * m⁻¹ := fun u hu =>
      exists_eq_act_mul_inv_of_involution hM hσ hsq1 hσA hu
    obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨f, hf⟩ : ↥V))
    have hfC : f⁻¹ * (o * f * o⁻¹) ∈ C := by
      have h1 : o * f * o⁻¹ = (o * f * o⁻¹ * f⁻¹) * f := by group
      have h2 := hcomm _ (CCV hfc) f hf
      rw [h1, h2]
      simpa using hfc
    obtain ⟨hkx, hb⟩ := hsd.equiv ⟨o, hoX⟩ u ⟨f, hf⟩ hu
    have hmk : (QuotientGroup.mk ⟨f, hf⟩ : ↥V ⧸ C.subgroupOf V) =
        QuotientGroup.mk ⟨o * f * o⁻¹, hkx⟩ :=
      QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hfC)
    have hfixed : M.act (θ ⟨o, hoX⟩) u = u := hsd.inj (hb.trans (hmk.symm.trans hu.symm))
    obtain ⟨m, hm⟩ := hfix u hfixed
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β m)
    obtain ⟨hax, hb2⟩ := hsd.beta_comm hoX hx.symm
    rw [← hm] at hb2
    have hfe : f⁻¹ * (o * (x : G) * o⁻¹ * (x : G)⁻¹) ∈ C := by
      have := QuotientGroup.eq.mp (hu.symm.trans hb2)
      exact Subgroup.mem_subgroupOf.mp this
    have hxV : (x : G) ∈ V := x.2
    have hy : o * (x : G) * o⁻¹ ∈ V := hconj _ hxV
    have hoyo : o * (o * (x : G) * o⁻¹) * o⁻¹ = (x : G) := by
      have h1 : o * (o * (x : G) * o⁻¹) * o⁻¹ = (o * o) * (x : G) * (o * o)⁻¹ := by group
      rw [h1, hcen _ (by rwa [← sq]) _ hxV]
      group
    have hoe : o * (o * (x : G) * o⁻¹ * (x : G)⁻¹) * o⁻¹ = o * (x : G) * o⁻¹ * (x : G)⁻¹ := by
      have h1 : o * (o * (x : G) * o⁻¹ * (x : G)⁻¹) * o⁻¹ =
          (o * (o * (x : G) * o⁻¹) * o⁻¹) * (o * (x : G) * o⁻¹)⁻¹ := by group
      rw [h1, hoyo]
      have hz := inv_eq_of_mul_eq_one_right
        (hsq _ (V.mul_mem hy (V.inv_mem hxV)))
      rw [mul_inv_rev, inv_inv] at hz
      exact hz
    obtain ⟨c, hcC, hfc'⟩ : ∃ c ∈ C, f = (o * (x : G) * o⁻¹ * (x : G)⁻¹) * c⁻¹ :=
      ⟨_, hfe, by group⟩
    have hoc : o * c = c * o := Subgroup.mem_centralizer_iff.mp (hCo hcC) o rfl
    have hoc' : o * c⁻¹ * o⁻¹ = c⁻¹ := by
      have := (Commute.inv_right (show Commute o c from hoc)).eq
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    rw [hfc']
    calc o * ((o * (x : G) * o⁻¹ * (x : G)⁻¹) * c⁻¹) * o⁻¹
        = (o * (o * (x : G) * o⁻¹ * (x : G)⁻¹) * o⁻¹) * (o * c⁻¹ * o⁻¹) := by group
      _ = _ := by rw [hoe, hoc']

end F53.Stellmacher

end CFSG.Quasithin
