module

public import CFSG.Quasithin.Vol2.Asc94.HeJ1
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem mulVec_eq_self_iff (P : M2) : (∀ v : V2, P *ᵥ v = v) ↔ P = 1 := by
  constructor
  · intro h
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  · rintro rfl v
    simp

theorem card_GL2 : Nat.card GL2 = 6 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_two]

section Kernel

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} (hT : TData A A' u w m)
  (N : Subgroup G)
  (hN : ∀ n ∈ N, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ (∀ x ∈ A', n * x * n⁻¹ ∈ A'))

include hT hN

theorem TData.rho_eq_one_iff (n : N) :
    hT.rho N hN n = 1 ↔
      (∀ x ∈ A, u (n * x * (n : G)⁻¹) = u x) ∧ (∀ x ∈ A', w (n * x * (n : G)⁻¹) = w x) := by
  constructor
  · intro h
    have h1 : ((hT.rho N hN n).1 : M2) = 1 := by
      rw [h]; rfl
    have h2 : ((hT.rho N hN n).2 : M2) = 1 := by
      rw [h]; rfl
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [hT.u_conj N hN n hx, h1, Matrix.one_mulVec]
    · rw [hT.w_conj N hN n hx, h2, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩
    have e1 : ((hT.rho N hN n).1 : M2) = 1 := by
      rw [← mulVec_eq_self_iff]
      intro v
      obtain ⟨x, hx, rfl⟩ := hT.cu.surj v
      rw [← hT.u_conj N hN n hx, h1 x hx]
    have e2 : ((hT.rho N hN n).2 : M2) = 1 := by
      rw [← mulVec_eq_self_iff]
      intro v
      obtain ⟨x, hx, rfl⟩ := hT.cw.surj v
      rw [← hT.w_conj N hN n hx, h2 x hx]
    exact Prod.ext (Units.ext e1) (Units.ext e2)

end Kernel

theorem sup_induction {A A' : Subgroup G} {P : G → Prop} (hA : ∀ x ∈ A, P x)
    (hA' : ∀ x ∈ A', P x) (h1 : P 1)
    (hmul : ∀ x y, x ∈ A ⊔ A' → y ∈ A ⊔ A' → P x → P y → P (x * y))
    (hinv : ∀ x, x ∈ A ⊔ A' → P x → P x⁻¹) {x : G} (hx : x ∈ A ⊔ A') : P x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => P x) ?_ h1 ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · exact hA y hy
    · exact hA' y hy
  · intro x y hx hy hpx hpy
    rw [← Subgroup.sup_eq_closure] at hx hy
    exact hmul x y hx hy hpx hpy
  · intro x hx hpx
    rw [← Subgroup.sup_eq_closure] at hx
    exact hinv x hx hpx

section Kernel2

variable [Finite G] {A A' : Subgroup G} {u w : G → V2} {m : G → M2} (hT : TData A A' u w m)
  (N : Subgroup G)
  (hN : ∀ n ∈ N, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ (∀ x ∈ A', n * x * n⁻¹ ∈ A'))
  (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA'ab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x)
  (hAsq : ∀ x ∈ A, x * x = 1)

include hT hAab hA'ab

theorem TData.Z_central {z : G} (hz : z ∈ A ⊓ A') {x : G} (hx : x ∈ A ⊔ A') :
    x * z = z * x := by
  refine sup_induction (A := A) (A' := A') (P := fun x => x * z = z * x) ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy; exact hAab y hy z hz.1
  · intro y hy; exact hA'ab y hy z hz.2
  · simp
  · intro x y _ _ hx hy
    calc x * y * z = x * (y * z) := by group
      _ = x * (z * y) := by rw [hy]
      _ = (x * z) * y := by group
      _ = (z * x) * y := by rw [hx]
      _ = z * (x * y) := by group
  · intro x _ hx
    calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * z) * x⁻¹ := by rw [hx]
      _ = z * x⁻¹ := by group

theorem TData.Q_gen {x : G} (hx : x ∈ A ∨ x ∈ A') {a : G} (ha : a ∈ A) :
    x * a * x⁻¹ ∈ A ∧ u (x * a * x⁻¹) = u a := by
  rcases hx with hx | hx
  · have : x * a * x⁻¹ = a := by
      rw [mul_inv_eq_iff_eq_mul]; exact hAab x hx a ha
    rw [this]; exact ⟨ha, rfl⟩
  · obtain ⟨hzm, -⟩ := hT.comm a ha x hx
    have hz : (a * x * a⁻¹ * x⁻¹)⁻¹ ∈ A ⊓ A' := inv_mem hzm
    have heq : x * a * x⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ * a := by group
    rw [heq]
    refine ⟨A.mul_mem hz.1 ha, ?_⟩
    rw [hT.cu.mul _ hz.1 _ ha, (hT.cu.zero _ hz.1).mpr hz.2, zero_add]

theorem TData.J_trivial_u {x : G} (hx : x ∈ A ⊔ A') {a : G} (ha : a ∈ A) :
    x * a * x⁻¹ ∈ A ∧ u (x * a * x⁻¹) = u a := by
  have key : (∀ a ∈ A, x * a * x⁻¹ ∈ A ∧ u (x * a * x⁻¹) = u a) ∧
      (∀ a ∈ A, x⁻¹ * a * x ∈ A ∧ u (x⁻¹ * a * x) = u a) := by
    refine sup_induction (A := A) (A' := A') (P := fun x =>
      (∀ a ∈ A, x * a * x⁻¹ ∈ A ∧ u (x * a * x⁻¹) = u a) ∧
      (∀ a ∈ A, x⁻¹ * a * x ∈ A ∧ u (x⁻¹ * a * x) = u a)) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      refine ⟨fun a ha => hT.Q_gen hAab hA'ab (Or.inl hy) ha, fun a ha => ?_⟩
      have := hT.Q_gen hAab hA'ab (Or.inl (A.inv_mem hy)) ha
      simpa using this
    · intro y hy
      refine ⟨fun a ha => hT.Q_gen hAab hA'ab (Or.inr hy) ha, fun a ha => ?_⟩
      have := hT.Q_gen hAab hA'ab (Or.inr (A'.inv_mem hy)) ha
      simpa using this
    · exact ⟨fun a ha => by simp [ha], fun a ha => by simp [ha]⟩
    · intro x y _ _ hx hy
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · obtain ⟨h1, h2⟩ := hy.1 a ha
        obtain ⟨h3, h4⟩ := hx.1 _ h1
        have : x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
        rw [this]
        exact ⟨h3, by rw [h4, h2]⟩
      · obtain ⟨h1, h2⟩ := hx.2 a ha
        obtain ⟨h3, h4⟩ := hy.2 _ h1
        have : (x * y)⁻¹ * a * (x * y) = y⁻¹ * (x⁻¹ * a * x) * y := by group
        rw [this]
        exact ⟨h3, by rw [h4, h2]⟩
    · intro x _ hx
      exact ⟨by simpa using hx.2, by simpa using hx.1⟩
  exact key.1 a ha

end Kernel2

section Symm

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2}

theorem TData.m_inv (hT : TData A A' u w m) {x : G} (hx : x ∈ A ⊓ A') : m x⁻¹ = m x := by
  have h := hT.mmul x hx x⁻¹ (inv_mem hx)
  rw [mul_inv_cancel, hT.m_one] at h
  have h2 : m x + m x⁻¹ = 0 := h.symm
  have h3 : m x⁻¹ = - m x := eq_neg_of_add_eq_zero_right h2
  have : ∀ M : M2, -M = M := by
    intro M; ext i j; simp only [Matrix.neg_apply]
    have : ∀ a : ZMod 2, -a = a := by decide
    exact this _
  rw [h3, this]

theorem TData.symm (hT : TData A A' u w m) : TData A' A w u (fun x => (m x)ᵀ) where
  cu := hT.cw
  cw := hT.cu
  mmul x hx y hy := by
    rw [inf_comm] at hx hy
    simp only [hT.mmul x hx y hy, Matrix.transpose_add]
  minj x hx y hy h := by
    rw [inf_comm] at hx hy
    exact hT.minj x hx y hy (by simpa using congrArg Matrix.transpose h)
  msurj M := by
    obtain ⟨x, hx, hxm⟩ := hT.msurj Mᵀ
    exact ⟨x, by rw [inf_comm]; exact hx, by simp [hxm]⟩
  comm x hx y hy := by
    obtain ⟨hz, hm⟩ := hT.comm y hy x hx
    have hz' : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [hz']
    refine ⟨by rw [inf_comm]; exact inv_mem hz, ?_⟩
    show (m _)ᵀ = _
    rw [hT.m_inv hz, hm]
    ext i j
    simp [Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]

end Symm

structure NData {A A' : Subgroup G} (u w : G → V2) (N T : Subgroup G) : Prop where
  norm : ∀ n ∈ N, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ (∀ x ∈ A', n * x * n⁻¹ ∈ A')
  JN : A ⊔ A' ≤ N
  Aab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  A'ab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x
  Asq : ∀ x ∈ A, x * x = 1
  cent : ∀ x : G, (∀ y ∈ A ⊔ A', x * y = y * x) → x ∈ A ⊓ A'
  TN : IsSylowOf 2 T N
  Tf : ∀ t ∈ T, (∀ x ∈ A, u (t * x * t⁻¹) = u x) → (∀ y ∈ A', w (t * y * t⁻¹) = w y) →
    t ∈ A ⊔ A'
  card : Nat.card N = 36 * Nat.card ↥(A ⊔ A')

section Main

variable [Finite G] {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G}
  (hT : TData A A' u w m) (hK : NData (A := A) (A' := A') u w N T)

include hT hK

theorem TData.rho_J (x : N) (hx : (x : G) ∈ A ⊔ A') : hT.rho N hK.norm x = 1 := by
  rw [hT.rho_eq_one_iff N hK.norm]
  refine ⟨fun a ha => (hT.J_trivial_u hK.Aab hK.A'ab hx ha).2, fun a ha => ?_⟩
  have hx' : (x : G) ∈ A' ⊔ A := by rw [sup_comm]; exact hx
  exact (hT.symm.J_trivial_u hK.A'ab hK.Aab hx' ha).2

theorem TData.odd_one (c : N) (hc : hT.rho N hK.norm c = 1) (hodd : Odd (orderOf (c : G))) :
    (c : G) = 1 := by
  obtain ⟨h1, h2⟩ := (hT.rho_eq_one_iff N hK.norm c).mp hc
  have e1 : ((hT.rho N hK.norm c).1 : M2) = 1 := by rw [hc]; rfl
  have e2 : ((hT.rho N hK.norm c).2 : M2) = 1 := by rw [hc]; rfl
  set g : G := (c : G) with hg
  have hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A := (hK.norm g c.2).1
  have hgA' : ∀ x ∈ A', g * x * g⁻¹ ∈ A' := (hK.norm g c.2).2
  have hZc : ∀ z ∈ A ⊓ A', g * z * g⁻¹ = z := by
    intro z hz
    have hzz : g * z * g⁻¹ ∈ A ⊓ A' := ⟨hgA z hz.1, hgA' z hz.2⟩
    apply hT.minj _ hzz z hz
    rw [hg, hT.m_conj N hK.norm c hz, e1, e2]
    simp
  have hd : ∀ x ∈ A ⊔ A', g * x * g⁻¹ * x⁻¹ ∈ A ⊓ A' := by
    intro x hx
    refine sup_induction (A := A) (A' := A') (P := fun x => g * x * g⁻¹ * x⁻¹ ∈ A ⊓ A') ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact ⟨A.mul_mem (hgA y hy) (A.inv_mem hy),
        hT.cu.mul_inv_mem (hgA y hy) hy (h1 y hy)⟩
    · intro y hy
      exact ⟨hT.cw.mul_inv_mem (hgA' y hy) hy (h2 y hy), A'.mul_mem (hgA' y hy) (A'.inv_mem hy)⟩
    · simp
    · intro x y hxJ hyJ hdx hdy
      have hxd : x * (g * y * g⁻¹ * y⁻¹) * x⁻¹ = g * y * g⁻¹ * y⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hT.Z_central hK.Aab hK.A'ab hdy hxJ
      have : g * (x * y) * g⁻¹ * (x * y)⁻¹ =
          (g * x * g⁻¹ * x⁻¹) * (x * (g * y * g⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [this, hxd]
      exact mul_mem hdx hdy
    · intro x hxJ hdx
      have : g * x⁻¹ * g⁻¹ * x⁻¹⁻¹ = x⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * x := by group
      rw [this]
      have h3 : x⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * x = (g * x * g⁻¹ * x⁻¹)⁻¹ := by
        have hc := hT.Z_central hK.Aab hK.A'ab (inv_mem hdx) (inv_mem hxJ : x⁻¹ ∈ A ⊔ A')
        rw [hc]; group
      rw [h3]
      exact inv_mem hdx
  have hpow : ∀ x ∈ A ⊔ A', ∀ k : ℕ,
      g ^ k * x * (g ^ k)⁻¹ = (g * x * g⁻¹ * x⁻¹) ^ k * x := by
    intro x hx k
    induction k with
    | zero => simp
    | succ k ih =>
      have hdZ := hd x hx
      have h1 : g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by
        group
      rw [h1, ih]
      have hdk : g * (g * x * g⁻¹ * x⁻¹) ^ k * g⁻¹ = (g * x * g⁻¹ * x⁻¹) ^ k := by
        rw [← conj_pow, hZc _ hdZ]
      calc g * ((g * x * g⁻¹ * x⁻¹) ^ k * x) * g⁻¹
          = (g * (g * x * g⁻¹ * x⁻¹) ^ k * g⁻¹) * (g * x * g⁻¹ * x⁻¹) * x := by group
        _ = (g * x * g⁻¹ * x⁻¹) ^ k * (g * x * g⁻¹ * x⁻¹) * x := by rw [hdk]
        _ = (g * x * g⁻¹ * x⁻¹) ^ (k + 1) * x := by rw [pow_succ]
  have hcomm : ∀ x ∈ A ⊔ A', g * x = x * g := by
    intro x hx
    have hdZ := hd x hx
    have hk := hpow x hx (orderOf g)
    rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at hk
    have hdd : (g * x * g⁻¹ * x⁻¹) ^ orderOf g = 1 := by
      have := hk.symm
      rwa [mul_eq_right] at this
    have hd2 : (g * x * g⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹) = 1 := hK.Asq _ hdZ.1
    obtain ⟨j, hj⟩ := hodd
    have h5 : (g * x * g⁻¹ * x⁻¹) ^ orderOf g = g * x * g⁻¹ * x⁻¹ := by
      rw [hj, pow_succ, pow_mul, sq, hd2, one_pow, one_mul]
    rw [h5] at hdd
    have := hdd
    calc g * x = (g * x * g⁻¹ * x⁻¹) * x * g := by group
      _ = x * g := by rw [this, one_mul]
  have hgZ : g ∈ A ⊓ A' := hK.cent g (fun y hy => hcomm y hy)
  have hgg : g * g = 1 := hK.Asq g hgZ.1
  obtain ⟨j, hj⟩ := hodd
  have h6 : g ^ orderOf g = g := by rw [hj, pow_succ, pow_mul, sq, hgg, one_pow, one_mul]
  rw [pow_orderOf_eq_one] at h6
  exact h6.symm

theorem TData.ker_rho : (hT.rho N hK.norm).ker = (A ⊔ A').subgroupOf N := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hn
    obtain ⟨S, hS⟩ := hK.TN.exists_sylow_eq_subgroupOf
    haveI : (hT.rho N hK.norm).ker.Normal := MonoidHom.normal_ker _
    have hK2 : IsPGroup 2 (hT.rho N hK.norm).ker := by
      intro g
      obtain ⟨i, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd
        (n := orderOf (g : G)) (orderOf_pos (g : G)).ne'
      refine ⟨i, ?_⟩
      set h : N := (g : N) ^ (2 ^ i) with hh
      have hkh : hT.rho N hK.norm h = 1 := by
        rw [hh, map_pow]
        have : hT.rho N hK.norm (g : N) = 1 := g.2
        rw [this, one_pow]
      have hoh : orderOf (h : G) = r := by
        rw [hh, Subgroup.coe_pow, orderOf_pow_of_dvd (by positivity) (by rw [hord]; exact dvd_mul_right _ _),
          hord, Nat.mul_div_cancel_left _ (by positivity)]
      have h1 := hT.odd_one hK h hkh (by rw [hoh]; exact hr)
      apply Subtype.ext
      apply Subtype.ext
      simpa [hh] using h1
    have hnS : n ∈ (S : Subgroup N) := (hK2.le_sylow_of_normal S) (MonoidHom.mem_ker.mpr hn)
    rw [hS, Subgroup.mem_subgroupOf] at hnS
    obtain ⟨h1, h2⟩ := (hT.rho_eq_one_iff N hK.norm n).mp hn
    exact hK.Tf _ hnS h1 h2
  · intro hn
    exact hT.rho_J hK n hn

theorem TData.rho_surjective : Function.Surjective (hT.rho N hK.norm) := by
  have hker : Nat.card ↥(hT.rho N hK.norm).ker = Nat.card ↥(A ⊔ A') := by
    rw [hT.ker_rho hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.JN).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (hT.rho N hK.norm).ker
  have h2 : Nat.card (↥N ⧸ (hT.rho N hK.norm).ker) = Nat.card (hT.rho N hK.norm).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hpos : 0 < Nat.card ↥(A ⊔ A') := Nat.card_pos
  have hr : Nat.card (hT.rho N hK.norm).range = 36 := by
    rw [hK.card, h2, hker] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  have hGL : Nat.card (GL2 × GL2) = 36 := by
    rw [Nat.card_prod, card_GL2]
  have : (hT.rho N hK.norm).range = ⊤ :=
    Subgroup.eq_top_of_card_eq (hT.rho N hK.norm).range (by rw [hr, hGL])
  exact MonoidHom.range_eq_top.mp this

end Main

end CFSG.Quasithin.A94.HeJ
