module

public import CFSG.Sporadic.ONOddCore.QuotTauAut

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier

theorem quotHom_range_le
    {k : ℕ} (hk : k < 12) : (quotHom k).range ≤ RM := by
  rw [MonoidHom.range_eq_map, ← qGroup_closure_top, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  simp only [qGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hg with rfl | rfl
  · rw [SetLike.mem_coe, quotHom_gen hk (by norm_num)]
    exact qImgPerm_mem_RM (recK_mem hk) (by norm_num)
  · rw [SetLike.mem_coe, quotHom_gen hk (by norm_num)]
    exact qImgPerm_mem_RM (recK_mem hk) (by norm_num)

theorem mem_qGroup_of_RM
    {x : Equiv.Perm (Fin 120)} (hx : x ∈ RM) : x ∈ qGroup := by
  rw [qGroup_eq_RM]
  exact hx

@[expose] def toQ
    (x : RM) : qGroup := ⟨x, mem_qGroup_of_RM x.2⟩

@[expose] def qGroupEquiv :
    RM ≃* qGroup := MulEquiv.subgroupCongr qGroup_eq_RM.symm

@[expose] def tauHom
    (k : ℕ) : RM →* RM :=
  if hk : k < 12 then
    ((quotHom k).comp qGroupEquiv.toMonoidHom).codRestrict RM fun _ =>
      quotHom_range_le hk ⟨_, rfl⟩
  else 1

theorem tauHom_val
    {k : ℕ} (hk : k < 12) (x : RM) :
    ((tauHom k x : RM) : Equiv.Perm (Fin 120)) = quotHom k (toQ x) := by
  rw [tauHom, dite_eq_left hk]
  rfl

theorem tauHom_X
    {k : ℕ} (hk : k < 12) (x : onX) :
    ((tauHom k ⟨x, onX_le_RM x.2⟩ : RM) : Equiv.Perm (Fin 120)) =
      ((sigmaX (recK k).diag (recK k).field (recK k).graph x : onX) : Equiv.Perm (Fin 120)) := by
  rw [tauHom_val hk]
  exact quotHom_eq_sigma hk x

theorem tauHom_injective
    {k : ℕ} (hk : k < 12) : Function.Injective (tauHom k) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hc : (x : Equiv.Perm (Fin 120)) ∈
      Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    set c : Equiv.Perm (Fin 120) := x * y * (x : Equiv.Perm (Fin 120))⁻¹ * y⁻¹ with hcdef
    have hcX : c ∈ onX := mul_mem (conj_mem_X x.2 hy) (inv_mem hy)
    have hτc : tauHom k ⟨c, onX_le_RM hcX⟩ = 1 := by
      have e : (⟨c, onX_le_RM hcX⟩ : RM) = x * ⟨y, onX_le_RM hy⟩ * x⁻¹ * ⟨y, onX_le_RM hy⟩⁻¹ :=
        Subtype.ext rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hx]
      group
    have hσc := tauHom_X hk ⟨c, hcX⟩
    rw [hτc] at hσc
    have h1 : sigmaX (recK k).diag (recK k).field (recK k).graph ⟨c, hcX⟩ = 1 :=
      Subtype.ext hσc.symm
    have h2 : (⟨c, hcX⟩ : onX) = 1 := by
      rw [← map_one (sigmaX (recK k).diag (recK k).field (recK k).graph)] at h1
      exact (MulEquiv.injective _) h1
    have h3 : c = 1 := congrArg Subtype.val h2
    rw [hcdef] at h3
    calc y * x = (x * y * (x : Equiv.Perm (Fin 120))⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
      _ = x * y := by rw [h3, inv_one, one_mul]
  have h : (x : Equiv.Perm (Fin 120)) ∈ RM ⊓ Subgroup.centralizer (onX : Set _) := ⟨x.2, hc⟩
  rw [RM_inf_centralizer, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

@[expose] def tauAut
    (k : ℕ) : MulAut RM :=
  if hk : k < 12 then
    MulEquiv.ofBijective (tauHom k) (Finite.injective_iff_bijective.1 (tauHom_injective hk))
  else 1

theorem tauAut_val
    {k : ℕ} (hk : k < 12) (x : RM) :
    ((tauAut k x : RM) : Equiv.Perm (Fin 120)) = quotHom k (toQ x) := by
  rw [tauAut, dite_eq_left hk, MulEquiv.ofBijective_apply, tauHom_val hk]

theorem tauAut_eq_quotFun
    {k : ℕ} (hk : k < 12) (x : RM) :
    ((tauAut k x : RM) : Equiv.Perm (Fin 120)) = quotFun (recK k) (toQ x) := by
  rw [tauAut_val hk, quotHom_eq_quotFun hk]

theorem tauAut_gen
    {k : ℕ} (hk : k < 12) {j : ℕ} (hj : j < 2) :
    ((tauAut k ⟨qGenPerm j, qGenPerm_mem_RM hj⟩ : RM) : Equiv.Perm (Fin 120)) =
      qImgPerm (recK k) j := by
  rw [tauAut_val hk]
  exact quotHom_gen hk hj

theorem tauAut_X
    {k : ℕ} (hk : k < 12) (x : onX) :
    ((tauAut k ⟨x, onX_le_RM x.2⟩ : RM) : Equiv.Perm (Fin 120)) =
      ((sigmaX (recK k).diag (recK k).field (recK k).graph x : onX) : Equiv.Perm (Fin 120)) := by
  rw [tauAut_val hk]
  exact quotHom_eq_sigma hk x

theorem iotaR_tauAut
    {k : ℕ} (hk : k < 12) (r : RM) :
    iotaR (tauAut k r) = sigmaX (recK k).diag (recK k).field (recK k).graph * iotaR r *
      (sigmaX (recK k).diag (recK k).field (recK k).graph)⁻¹ := by
  set σ := sigmaX (recK k).diag (recK k).field (recK k).graph
  refine MulEquiv.ext fun x => Subtype.ext ?_
  set y := σ⁻¹ x
  have hy : σ y = x := by simp [y]
  rw [MulAut.mul_apply, MulAut.mul_apply, iotaR_apply]
  have hry : (r : Equiv.Perm (Fin 120)) * y * (r : Equiv.Perm (Fin 120))⁻¹ ∈ onX :=
    conj_mem_X r.2 y.2
  have e1 : ((σ (iotaR r y) : onX) : Equiv.Perm (Fin 120)) =
      ((tauAut k ⟨_, onX_le_RM hry⟩ : RM) : Equiv.Perm (Fin 120)) := by
    have := tauAut_X hk ⟨_, hry⟩
    rw [this]
    rfl
  have e2 : (⟨_, onX_le_RM hry⟩ : RM) = r * ⟨y, onX_le_RM y.2⟩ * r⁻¹ := Subtype.ext rfl
  rw [e1, e2, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [tauAut_X hk y, hy]

end CFSG.Sporadic.ONOddCore
