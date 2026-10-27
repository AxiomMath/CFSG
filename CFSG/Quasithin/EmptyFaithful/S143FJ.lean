module

public import CFSG.Quasithin.EmptyFaithful.S143FI
public import CFSG.Quasithin.EmptyFaithful.S143EG

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Cocycle

theorem eq_one_of_odd_cocycle {Γ : Type*} [Group Γ] {x a c : Γ} (hx : Odd (orderOf x))
    (hxc : x * c = c * x) (hc : ∃ k : ℕ, c ^ (2 ^ k) = 1) (h : x * a * x⁻¹ = a * c) : c = 1 := by
  have hpow : ∀ j : ℕ, x ^ j * a * (x ^ j)⁻¹ = a * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hxcj : x * c ^ j * x⁻¹ = c ^ j := by
        have hcom : Commute x c := hxc
        rw [(hcom.pow_right j).eq]; group
      calc x ^ (j + 1) * a * (x ^ (j + 1))⁻¹ = x * (x ^ j * a * (x ^ j)⁻¹) * x⁻¹ := by
            rw [pow_succ']; group
        _ = x * (a * c ^ j) * x⁻¹ := by rw [ih]
        _ = (x * a * x⁻¹) * (x * c ^ j * x⁻¹) := by group
        _ = (a * c) * c ^ j := by rw [h, hxcj]
        _ = a * c ^ (j + 1) := by rw [pow_succ']; group
  have hn : c ^ orderOf x = 1 := by
    have := hpow (orderOf x)
    rw [pow_orderOf_eq_one] at this
    simpa using this
  obtain ⟨k, hk⟩ := hc
  have h1 : orderOf c ∣ orderOf x := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hx h1
  have : orderOf c = 1 :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd h2
  exact orderOf_eq_one_iff.mp this

end Cocycle

section CommU

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.commutator_mem_uOfL22_of_odd {x a : G} (hxH : x ∈ mcOf T) (haH : a ∈ mcOf T)
    (hx : Odd (orderOf x)) (hQ : x * a * x⁻¹ * a⁻¹ ∈ qOf T) :
    x * a * x⁻¹ * a⁻¹ ∈ uOfL22 T M := by
  have hxC := odd_mem_centralizerMod c hxH hx
  have hHU := c.hHU
  have hN : ((uOfL22 T M).subgroupOf (mcOf T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHU
  let π : ↥(mcOf T) →* ↥(mcOf T) ⧸ (uOfL22 T M).subgroupOf (mcOf T) := QuotientGroup.mk' _
  set xH : ↥(mcOf T) := ⟨x, hxH⟩ with hxHdef
  set aH : ↥(mcOf T) := ⟨a, haH⟩ with haHdef
  set cH : ↥(mcOf T) := aH⁻¹ * xH * aH * xH⁻¹ with hcHdef
  have hcG : (cH : G) = a⁻¹ * x * a * x⁻¹ := rfl
  have hcQ : (cH : G) ∈ qOf T := by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (mcOf T) ((mcOf T).inv_mem haH)) (x * a * x⁻¹ * a⁻¹)).mp hQ
    have e : a⁻¹ * (x * a * x⁻¹ * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * x * a * x⁻¹ := by group
    rw [hcG, ← e]
    exact h1
  have hrel : xH * aH * xH⁻¹ = aH * cH := by rw [hcHdef]; group
  have hπ1 : π xH * π aH * (π xH)⁻¹ = π aH * π cH := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hrel]
  have hπ2 : π xH * π cH = π cH * π xH := by
    have hcomm : xH * cH * xH⁻¹ * cH⁻¹ ∈ (uOfL22 T M).subgroupOf (mcOf T) := by
      rw [Subgroup.mem_subgroupOf]
      exact hxC.2.2 (cH : G) hcQ
    have h1 : π (xH * cH * xH⁻¹ * cH⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    calc π xH * π cH = (π xH * π cH * (π xH)⁻¹) * π xH := by group
      _ = π cH * π xH := by rw [h2]
  have hxodd : Odd (orderOf (π xH)) := by
    have h1 : Odd (orderOf xH) := by rw [hxHdef, Subgroup.orderOf_mk]; exact hx
    exact Odd.of_dvd_nat h1 (orderOf_map_dvd π xH)
  have hc2 : ∃ k : ℕ, (π cH) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (mcOf T) ⟨(cH : G), hcQ⟩
    refine ⟨k, ?_⟩
    have h1 : cH ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow, h1, map_one]
  have h3 : π cH = 1 := eq_one_of_odd_cocycle hxodd hπ2 hc2 hπ1
  have hcU : (cH : G) ∈ uOfL22 T M := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h3)
  have h4 := (Subgroup.mem_normalizer_iff.mp (hHU haH) (cH : G)).mp hcU
  have e : a * (cH : G) * a⁻¹ = x * a * x⁻¹ * a⁻¹ := by rw [hcG]; group
  rwa [e] at h4

end CommU

section TclsHom

variable {G : Type} [Group G] {Z U : Subgroup G} (hUN : U ≤ Subgroup.normalizer (Z : Set G))

@[expose] noncomputable def tclsHom : ↥U →* ↥(tildeOf Z U) where
  toFun u := tclsE hUN u.2
  map_one' := (tclsE_eq_one_iff hUN _).mpr Z.one_mem
  map_mul' a b := tclsE_mul hUN a.2 b.2

theorem tclsHom_ker_map (hZU : Z ≤ U) : (tclsHom hUN).ker.map U.subtype = Z := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (tclsE_eq_one_iff hUN u.2).mp (MonoidHom.mem_ker.mp hu)
  · intro hx
    exact ⟨⟨x, hZU hx⟩, MonoidHom.mem_ker.mpr ((tclsE_eq_one_iff hUN (hZU hx)).mpr hx), rfl⟩

end TclsHom

section Stab

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)
  {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include c hrW hrV hr2

theorem Counter.conj_mem_inf_qOf {y : ↥(mcOf T)}
    (hy : c.actK y * c.alphaOf hrW hrV hr2 = c.alphaOf hrW hrV hr2 * c.actK y)
    {b : G} (hb : b ∈ c.Ac hrW hrV hr2 ⊓ qOf T) :
    (y : G) * b * (y : G)⁻¹ ∈ c.Ac hrW hrV hr2 ⊓ qOf T := by
  have h := c.h1281
  have hUN := c.hUN
  have hHU := c.hHU
  have hHN := hHN_of T
  set B := c.Ac hrW hrV hr2 ⊓ qOf T with hB
  set α := c.alphaOf hrW hrV hr2 with hα
  have hBU : B ≤ uOfL22 T M := c.Ac_inf_qOf_le_uOfL22 hrW hrV hr2
  have hZU : quasithinOmegaOneCenter T ≤ uOfL22 T M := fun z hz =>
    (h.omegaOneCenter_le_centerOf_uOfL22 hz).1
  have hZB : quasithinOmegaOneCenter T ≤ B := fun z hz =>
    c.VZ_le_Ac_inf_qOf hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hz)
  have hα1 := c.alphaOf_ne_one hrW hrV hr2
  have hα2 := c.alphaOf_sq hrW hrV hr2
  obtain ⟨hfix, -⟩ := c.swap_facts hrW hrV hr2 (c.alphaOf_mem_T hrW hrV hr2) hα1 hα2
    (c.alphaOf_tclsE hrW hrV hr2)
  set ψ := tclsHom hUN with hψ
  set B' : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    (B.subgroupOf (uOfL22 T M)).map ψ with hB'
  have hBfix : ∀ (b' : G) (hb'U : b' ∈ uOfL22 T M), b' ∈ B → tclsE hUN hb'U ∈ autFixedSub α := by
    intro b' hb'U hb'B
    have hcomm : g * r * g⁻¹ * b' = b' * (g * r * g⁻¹) :=
      mul_comm_of_sq_eq_one (fun x hx => c.sq_Ac hrW hrV hr2 hx) (c.r1_mem_Ac hrW hrV hr2) hb'B.1
    have hconj : (g * r * g⁻¹) * b' * (g * r * g⁻¹)⁻¹ = b' := by
      calc (g * r * g⁻¹) * b' * (g * r * g⁻¹)⁻¹ = (b' * (g * r * g⁻¹)) * (g * r * g⁻¹)⁻¹ := by
            rw [hcomm]
        _ = b' := by group
    have hbU' : (g * r * g⁻¹) * b' * (g * r * g⁻¹)⁻¹ ∈ uOfL22 T M := by rw [hconj]; exact hb'U
    rw [mem_autFixedSub]
    have := actTilde_tclsE hUN hHN hHU ⟨g * r * g⁻¹, c.r1_mem_mcOf hrW hrV hr2⟩ hb'U hbU'
    exact this.trans (tclsE_congr hUN hbU' hb'U hconj)
  have hB'F : B' ≤ autFixedSub α := by
    rintro _ ⟨b₀, hb₀, rfl⟩
    exact hBfix b₀ b₀.2 (Subgroup.mem_subgroupOf.mp hb₀)
  have hB'card : Nat.card B' = 4 := by
    have h1 := card_map_mul_card_inf_ker hBU ψ
    rw [tclsHom_ker_map hUN hZU, inf_eq_right.mpr hZB, c.card_inf_qOf_Ac hrW hrV hr2,
      h.card_omegaOneCenter] at h1
    have h1' : Nat.card B' * 2 = 8 := h1
    omega
  have hFB' : B' = autFixedSub α :=
    Subgroup.eq_of_le_of_card_ge hB'F (by rw [hB'card]; exact hfix)
  have hbU : b ∈ uOfL22 T M := hBU hb
  have hyB : (y : G) * b * (y : G)⁻¹ ∈ uOfL22 T M :=
    (Subgroup.mem_normalizer_iff.mp (hHU y.2) b).mp hbU
  have hmem : tclsE hUN hyB ∈ autFixedSub α := by
    have h2 : c.actK y (tclsE hUN hbU) = tclsE hUN hyB := actTilde_tclsE hUN hHN hHU y hbU hyB
    have hb1 : tclsE hUN hbU ∈ autFixedSub α := hBfix b hbU hb
    rw [mem_autFixedSub] at hb1 ⊢
    rw [← h2]
    calc α (c.actK y (tclsE hUN hbU)) = (α * c.actK y) (tclsE hUN hbU) := rfl
      _ = (c.actK y * α) (tclsE hUN hbU) := by rw [← hy]
      _ = c.actK y (α (tclsE hUN hbU)) := rfl
      _ = c.actK y (tclsE hUN hbU) := by rw [hb1]
  rw [← hFB'] at hmem
  obtain ⟨b₀, hb₀, hb₀eq⟩ := hmem
  have hb₀B : (b₀ : G) ∈ B := Subgroup.mem_subgroupOf.mp hb₀
  have hz : (b₀ : G)⁻¹ * ((y : G) * b * (y : G)⁻¹) ∈ quasithinOmegaOneCenter T :=
    (tclsE_eq_iff hUN b₀.2 hyB).mp hb₀eq
  have e : (y : G) * b * (y : G)⁻¹ = (b₀ : G) * ((b₀ : G)⁻¹ * ((y : G) * b * (y : G)⁻¹)) := by group
  rw [e]
  exact B.mul_mem hb₀B (hZB hz)

theorem Counter.mem_Ac_of_centralizes {u a : G} (huU : u ∈ uOfL22 T M)
    (haA : a ∈ c.Ac hrW hrV hr2)
    (hcent : ∀ b ∈ c.Ac hrW hrV hr2 ⊓ qOf T, (u * a) * b = b * (u * a)) :
    u * a ∈ c.Ac hrW hrV hr2 := by
  have hu : ∀ b ∈ c.Ac hrW hrV hr2 ⊓ qOf T, u * b = b * u := by
    intro b hb
    have hab : a * b = b * a :=
      mul_comm_of_sq_eq_one (fun x hx => c.sq_Ac hrW hrV hr2 hx) haA hb.1
    have h1 := hcent b hb
    have h2 : u * b * a = b * u * a := by
      calc u * b * a = u * (b * a) := by group
        _ = u * (a * b) := by rw [hab]
        _ = (u * a) * b := by group
        _ = b * (u * a) := h1
        _ = b * u * a := by group
    exact mul_right_cancel h2
  have huW : u ∈ Hyp1281Two.wOfU T M :=
    ⟨huU, Subgroup.mem_centralizer_iff.mpr fun e he =>
      (hu e (c.VZ_le_Ac_inf_qOf hrW hrV hr2 he)).symm⟩
  have huA : u ∈ c.Ac hrW hrV hr2 := by
    by_contra hnot
    apply c.comm_ne_of_not_mem_Ac hrW hrV hr2 huW hnot
    have hrB : r ∈ c.Ac hrW hrV hr2 ⊓ qOf T := ⟨c.r_mem_Ac hrW hrV hr2, c.wOfU_le_qOf hrW⟩
    have h1 := hu r hrB
    calc r * u * r⁻¹ * u⁻¹ = (r * u) * r⁻¹ * u⁻¹ := rfl
      _ = (u * r) * r⁻¹ * u⁻¹ := by rw [h1]
      _ = 1 := by group
  exact (c.Ac hrW hrV hr2).mul_mem huA haA

theorem Counter.conj_mem_Ac_of_odd {x : ↥(mcOf T)} (hx : Odd (orderOf x))
    (hxα : c.actK x * c.alphaOf hrW hrV hr2 = c.alphaOf hrW hrV hr2 * c.actK x)
    {a : G} (ha : a ∈ c.Ac hrW hrV hr2) : (x : G) * a * (x : G)⁻¹ ∈ c.Ac hrW hrV hr2 := by
  have haH := c.Ac_le_mcOf hrW hrV hr2 ha
  have hQ : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ qOf T := by
    refine c.mem_qOf_of_actK_eq_one (x := x * ⟨a, haH⟩ * x⁻¹ * ⟨a, haH⟩⁻¹) ?_
    have hcomm : c.actK x * c.actK ⟨a, haH⟩ = c.actK ⟨a, haH⟩ * c.actK x := by
      rcases c.actK_Ac hrW hrV hr2 ha with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact hxα
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hxodd : Odd (orderOf (x : G)) := by rw [Subgroup.orderOf_coe]; exact hx
  have hU1 := c.commutator_mem_uOfL22_of_odd x.2 haH hxodd hQ
  have hxinvα : c.actK x⁻¹ * c.alphaOf hrW hrV hr2 = c.alphaOf hrW hrV hr2 * c.actK x⁻¹ := by
    rw [map_inv]
    calc (c.actK x)⁻¹ * c.alphaOf hrW hrV hr2
        = (c.actK x)⁻¹ * (c.alphaOf hrW hrV hr2 * c.actK x) * (c.actK x)⁻¹ := by group
      _ = (c.actK x)⁻¹ * (c.actK x * c.alphaOf hrW hrV hr2) * (c.actK x)⁻¹ := by rw [hxα]
      _ = c.alphaOf hrW hrV hr2 * (c.actK x)⁻¹ := by group
  have hcent : ∀ b ∈ c.Ac hrW hrV hr2 ⊓ qOf T,
      ((x : G) * a * (x : G)⁻¹ * a⁻¹ * a) * b = b * ((x : G) * a * (x : G)⁻¹ * a⁻¹ * a) := by
    intro b hb
    have hb1 : (x : G)⁻¹ * b * (x : G) ∈ c.Ac hrW hrV hr2 ⊓ qOf T := by
      have := c.conj_mem_inf_qOf hrW hrV hr2 (y := x⁻¹) hxinvα hb
      simpa using this
    have hab := mul_comm_of_sq_eq_one (fun z hz => c.sq_Ac hrW hrV hr2 hz) ha hb1.1
    calc ((x : G) * a * (x : G)⁻¹ * a⁻¹ * a) * b = (x : G) * (a * ((x : G)⁻¹ * b * (x : G))) *
          (x : G)⁻¹ := by group
      _ = (x : G) * (((x : G)⁻¹ * b * (x : G)) * a) * (x : G)⁻¹ := by rw [hab]
      _ = b * ((x : G) * a * (x : G)⁻¹ * a⁻¹ * a) := by group
  have := c.mem_Ac_of_centralizes hrW hrV hr2 hU1 ha hcent
  have e : (x : G) * a * (x : G)⁻¹ * a⁻¹ * a = (x : G) * a * (x : G)⁻¹ := by group
  rwa [e] at this

end Stab

end S143

end CFSG.Quasithin
