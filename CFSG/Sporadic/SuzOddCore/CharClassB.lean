module

public import CFSG.Sporadic.SuzOddCore.CharClassA
public import CFSG.Sporadic.SuzOddCore.GammaBound

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2

theorem exists_gP
    (i : Fin 22880) : ∃ g : suzP, (g : Equiv.Perm (Fin 22880)) 0 = i := by
  obtain ⟨g, hg, h⟩ := suzP_exists_smul 0 i
  exact ⟨⟨g, hg⟩, h⟩

@[expose] def gOf
    (i : Fin 22880) : suzP := Classical.choose (exists_gP i)

theorem gOf_spec
    (i : Fin 22880) : (gOf i : Equiv.Perm (Fin 22880)) 0 = i :=
  Classical.choose_spec (exists_gP i)

@[expose] def suzTheta3
    (i : Fin 22880) : Subgroup suzP := autMap (MulAut.conj (gOf i)) suzQP

theorem mem_suzQP_iff {x : suzP} : x ∈ suzQP ↔ (x : Equiv.Perm (Fin 22880)) ∈ suzQ :=
  Subgroup.mem_subgroupOf

theorem autMap_conj_of_zero
    {k : suzP} (hk : (k : Equiv.Perm (Fin 22880)) 0 = 0) :
    autMap (MulAut.conj k) suzQP = suzQP := by
  have hkH : (k : Equiv.Perm (Fin 22880)) ∈ suzH0 := mem_suzH0_iff.2 ⟨k.2, hk⟩
  have hn := suzH0_le_normalizer hkH
  ext x
  rw [autMap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_suzQP_iff] at hy ⊢
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hn y).1 hy
  · intro hx
    refine ⟨k⁻¹ * x * k, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [mem_suzQP_iff] at hx ⊢
    have := (Subgroup.mem_normalizer_iff''.1 hn x).1 hx
    simpa using this

theorem zero_of_autMap_conj
    {k : suzP} (hk : autMap (MulAut.conj k) suzQP = suzQP) :
    (k : Equiv.Perm (Fin 22880)) 0 = 0 := by
  have hn : (k : Equiv.Perm (Fin 22880)) ∈ suzP ⊓ Subgroup.normalizer
      (suzQ : Set (Equiv.Perm (Fin 22880))) := by
    refine ⟨k.2, Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · have hxP : x ∈ suzP := suzQ_le_suzH0.trans suzH0_le_suzP hx
      have hx' : (⟨x, hxP⟩ : suzP) ∈ suzQP := mem_suzQP_iff.2 hx
      have : MulAut.conj k ⟨x, hxP⟩ ∈ autMap (MulAut.conj k) suzQP :=
        Subgroup.mem_map_of_mem _ hx'
      rw [hk, mem_suzQP_iff] at this
      simpa [MulAut.conj_apply] using this
    · have hP : (k : Equiv.Perm (Fin 22880)) * x * (k : Equiv.Perm (Fin 22880))⁻¹ ∈ suzP :=
        suzQ_le_suzH0.trans suzH0_le_suzP hx
      have hxP : x ∈ suzP := by
        have := suzP.mul_mem (suzP.mul_mem (suzP.inv_mem k.2) hP) k.2
        simpa [mul_assoc] using this
      have hx' : MulAut.conj k ⟨x, hxP⟩ ∈ suzQP := by
        rw [mem_suzQP_iff]
        simpa [MulAut.conj_apply] using hx
      rw [← hk, autMap, Subgroup.mem_map] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      have : y = ⟨x, hxP⟩ := (MulAut.conj k).injective hyx
      rw [this, mem_suzQP_iff] at hy
      exact hy
  rw [suzP_inf_normalizer_Q] at hn
  exact (mem_suzH0_iff.1 hn).2

theorem autMap_conj_eq
    (g : suzP) :
    autMap (MulAut.conj g) suzQP = suzTheta3 ((g : Equiv.Perm (Fin 22880)) 0) := by
  set h := gOf ((g : Equiv.Perm (Fin 22880)) 0) with hdef
  have hh : (h : Equiv.Perm (Fin 22880)) 0 = (g : Equiv.Perm (Fin 22880)) 0 := gOf_spec _
  have hk : ((h⁻¹ * g : suzP) : Equiv.Perm (Fin 22880)) 0 = 0 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ← hh, perm_inv_apply_self]
  have e : g = h * (h⁻¹ * g) := by group
  rw [suzTheta3, ← hdef]
  conv_lhs => rw [e]
  rw [map_mul, autMap_mul, autMap_conj_of_zero hk]

theorem suzTheta3_zero :
    suzTheta3 0 = suzQP := by
  have := autMap_conj_eq 1
  rw [map_one, autMap_one] at this
  exact this.symm

theorem suzTheta3_equivariant
    (g : suzP) (i : Fin 22880) :
    suzTheta3 ((g : Equiv.Perm (Fin 22880)) i) = autMap (MulAut.conj g) (suzTheta3 i) := by
  have := autMap_conj_eq (g * gOf i)
  rw [map_mul, autMap_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply, gOf_spec] at this
  rw [← this]
  rfl

theorem suzTheta3_injective :
    Function.Injective suzTheta3 := by
  intro i j hij
  have h1 := congrArg (autMap (MulAut.conj (gOf j))⁻¹) hij
  rw [suzTheta3, suzTheta3, ← autMap_mul, ← autMap_mul, inv_mul_cancel, autMap_one, ← map_inv,
    ← map_mul] at h1
  have h0 := zero_of_autMap_conj h1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, gOf_spec] at h0
  have := congrArg (gOf j : Equiv.Perm (Fin 22880)) h0
  rwa [perm_apply_inv_self, gOf_spec] at this

theorem suzTheta3_mem
    (i : Fin 22880) : suzTheta3 i ∈ suzClassQ := ⟨gOf i, rfl⟩

theorem range_suzTheta3 :
    Set.range suzTheta3 = suzClassQ := by
  ext H
  constructor
  · rintro ⟨i, rfl⟩
    exact suzTheta3_mem i
  · rintro ⟨g, rfl⟩
    exact ⟨_, (autMap_conj_eq g).symm⟩

theorem suzTheta3_unique
    (θ' : Fin 22880 → Subgroup suzP) (h0 : θ' 0 = suzQP)
    (heq : ∀ (g : suzP) (i : Fin 22880),
      θ' ((g : Equiv.Perm (Fin 22880)) i) = autMap (MulAut.conj g) (θ' i)) :
    θ' = suzTheta3 := by
  funext i
  rw [← gOf_spec i, heq, h0, autMap_conj_eq, gOf_spec]

theorem commutator_eq_bot_iff {G : Type*} [Group G] {H K : Subgroup G} :
    ⁅H, K⁆ = ⊥ ↔ ∀ h ∈ H, ∀ k ∈ K, h * k = k * h := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro hle h hh k hk
    exact (Subgroup.mem_centralizer_iff.1 (hle hh) k hk).symm
  · intro h x hx
    exact Subgroup.mem_centralizer_iff.2 fun k hk => (h x hx k hk).symm

theorem commutator_autMap (α : MulAut suzP) (H K : Subgroup suzP) :
    ⁅autMap α H, autMap α K⁆ = ⊥ ↔ ⁅H, K⁆ = ⊥ := by
  rw [autMap, autMap, ← Subgroup.map_commutator]
  constructor
  · intro h
    exact (Subgroup.map_eq_bot_iff_of_injective _ α.injective).1 h
  · intro h
    rw [h, Subgroup.map_bot]

theorem conj_eq_of_order_three {G : Type*} [Group G] {z y : G} (hz : z ^ 3 = 1)
    (hy : orderOf y = 3) (h : z * y * z⁻¹ ∈ Subgroup.zpowers y) : z * y * z⁻¹ = y := by
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    norm_num at hy
  rcases mem_zpowers_three hy h with h1 | h1 | h1
  · exfalso
    apply hy1
    have := congrArg (fun w => z⁻¹ * w * z) h1
    simpa [mul_assoc] using this
  · exact h1
  · exfalso
    apply hy1
    have hc : ∀ n : ℕ, z ^ n * y * (z ^ n)⁻¹ = y ^ (2 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc z ^ (n + 1) * y * (z ^ (n + 1))⁻¹ = z * (z ^ n * y * (z ^ n)⁻¹) * z⁻¹ := by group
          _ = z * y ^ (2 ^ n) * z⁻¹ := by rw [ih]
          _ = (z * y * z⁻¹) ^ (2 ^ n) := by
            rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
          _ = y ^ (2 ^ (n + 1)) := by rw [h1, ← pow_two, ← pow_mul, pow_succ, mul_comm]
    have h3 := hc 3
    rw [hz, one_mul, inv_one, mul_one] at h3
    have : y ^ 8 = y ^ 2 := by
      rw [show 8 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hy3, one_pow, one_mul]
    have hy2 : y = y ^ 2 := by rw [← this]; simpa using h3
    have := congrArg (fun w => y⁻¹ * w) hy2
    simpa [pow_two] using this.symm

theorem suzZ_pow_three' :
    zP ^ 3 = 1 := Subtype.ext (by
  rw [SubgroupClass.coe_pow]
  exact suzZ_pow_three)

theorem mem_delta_iff_commutator
    {j : Fin 22880} (hj : j ≠ 0) :
    j ∈ suzDeltaΩ ↔ ⁅suzQP, suzTheta3 j⁆ = ⊥ := by
  set g := gOf j
  have hgj : (g : Equiv.Perm (Fin 22880)) 0 = j := gOf_spec j
  have hθ : suzTheta3 j = Subgroup.zpowers (g * zP * g⁻¹) := by
    rw [suzTheta3, suzQP_eq, autMap, MonoidHom.map_zpowers]
    rfl
  have hy : orderOf (g * zP * g⁻¹) = 3 := by
    rw [orderOf_conj_eq, ← Subgroup.orderOf_coe]
    exact orderOf_suzZ
  constructor
  · intro hjΔ
    have h0 : ((g⁻¹ * zP * g : suzP) : Equiv.Perm (Fin 22880)) 0 = 0 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hgj]
      rw [show (zP : Equiv.Perm (Fin 22880)) j = j from hjΔ.1, ← hgj, perm_inv_apply_self]
    have hfix := autMap_conj_of_zero h0
    have hn : zP * (g * zP * g⁻¹) * zP⁻¹ ∈ Subgroup.zpowers (g * zP * g⁻¹) := by
      have hmem : g⁻¹ * zP * g * zP * (g⁻¹ * zP * g)⁻¹ ∈ suzQP := by
        rw [← hfix]
        refine ⟨zP, by rw [suzQP_eq]; exact Subgroup.mem_zpowers _, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [suzQP_eq] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have e : (g * zP * g⁻¹) ^ k = g * zP ^ k * g⁻¹ := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
      rw [e, hk]
      group
    have hc := conj_eq_of_order_three suzZ_pow_three' hy hn
    rw [commutator_eq_bot_iff, hθ]
    intro a ha b hb
    rw [suzQP_eq] at ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hcomm : Commute zP (g * zP * g⁻¹) := by
      unfold Commute SemiconjBy
      calc zP * (g * zP * g⁻¹) = zP * (g * zP * g⁻¹) * zP⁻¹ * zP := by group
        _ = (g * zP * g⁻¹) * zP := by rw [hc]
    exact (hcomm.zpow_zpow m n).eq
  · intro h
    rw [commutator_eq_bot_iff, hθ] at h
    have hc := h zP (by rw [suzQP_eq]; exact Subgroup.mem_zpowers _) (g * zP * g⁻¹)
      (Subgroup.mem_zpowers _)
    have hnorm : autMap (MulAut.conj (g⁻¹ * zP * g)) suzQP = suzQP := by
      rw [suzQP_eq, autMap, MonoidHom.map_zpowers]
      congr 1
      change g⁻¹ * zP * g * zP * (g⁻¹ * zP * g)⁻¹ = zP
      have : zP * g * zP * g⁻¹ = g * zP * g⁻¹ * zP := by
        calc zP * g * zP * g⁻¹ = zP * (g * zP * g⁻¹) := by group
          _ = g * zP * g⁻¹ * zP := hc
      calc g⁻¹ * zP * g * zP * (g⁻¹ * zP * g)⁻¹ = g⁻¹ * (zP * g * zP * g⁻¹) * zP⁻¹ * g := by
            group
        _ = g⁻¹ * (g * zP * g⁻¹ * zP) * zP⁻¹ * g := by rw [this]
        _ = zP := by group
    have h0 := zero_of_autMap_conj hnorm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hgj] at h0
    have := congrArg (g : Equiv.Perm (Fin 22880)) h0
    rw [perm_apply_inv_self, hgj] at this
    exact ⟨this, hj⟩

theorem suzP_adj_iff
    {g : Equiv.Perm (Fin 22880)} (hg : g ∈ suzP) (x y : Fin 22880) :
    suzGamma.Adj (g x) (g y) ↔ suzGamma.Adj x y :=
  suzGamma_adj_map hg x y

theorem adj_iff_commutator
    {i j : Fin 22880} (hij : i ≠ j) :
    suzGamma.Adj i j ↔ ⁅suzTheta3 i, suzTheta3 j⁆ = ⊥ := by
  set h := gOf i
  have hhi : (h : Equiv.Perm (Fin 22880)) 0 = i := gOf_spec i
  set j' := (h : Equiv.Perm (Fin 22880))⁻¹ j
  have hj' : (h : Equiv.Perm (Fin 22880)) j' = j := perm_apply_inv_self _ j
  have hj'0 : j' ≠ 0 := by
    intro h0
    apply hij
    rw [← hhi, ← hj', h0]
  rw [← hhi, ← hj', suzP_adj_iff h.2, hhi, ← hj'] at *
  rw [suzTheta3_equivariant, suzTheta3_equivariant, suzTheta3_zero, commutator_autMap]
  rw [suzGamma_adj_zero]
  exact mem_delta_iff_commutator hj'0

end CFSG.Sporadic.SuzOddCore
