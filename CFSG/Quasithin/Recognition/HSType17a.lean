module

public import CFSG.Quasithin.Recognition.HSType16a
public import CFSG.Quasithin.Recognition.HSType129g
public import CFSG.Quasithin.Recognition.HSType15e

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

@[expose] def ρ3 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 5 3

theorem ρ3_conj : ρ3 * σS0 * ρ3⁻¹ = σS0 := by decide

theorem ρ3_facts : ∀ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))),
    (σ * ρ3) ^ 3 = 1 ∧ (σ * ρ3) * σS0 * (σ * ρ3)⁻¹ = σS0 ∧
      σ * ρ3 ∉ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))) := by
  decide +kernel

theorem ιS_ρ3_facts : ∀ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))),
    ∀ σ' ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))),
      (σ * ιS) * (σ' * ρ3) * (σ * ιS)⁻¹ * (σ' * ρ3)⁻¹ ∈
        ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))) := by
  decide +kernel

theorem perm_four_odd_invol_not_comm_three : ∀ σ τ : Equiv.Perm (Fin 4),
    σ * σ = 1 → Equiv.Perm.sign σ = -1 → τ * τ * τ = 1 → τ ≠ 1 → σ * τ ≠ τ * σ := by
  decide +kernel

theorem mem_zpowers_σS0_iff {σ : Equiv.Perm (Fin 6)} :
    σ ∈ Subgroup.zpowers σS0 ↔ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))) := by
  refine ⟨mem_zpowers_σS0, fun h => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _
  · exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

namespace HSSetting

namespace S6Model

variable {G : Type*} [Group G] {z s : G} {V : Subgroup G} (M : S6Model z s)

theorem eq_of_comm_of_π_eq {x : ↥(hsNB z s)} (hπx : M.π x = σS0) {a b : ↥(hsNB z s)}
    (hab : M.π a = M.π b) (hax : (a : G) * x = x * a) (hbx : (b : G) * x = x * b) : a = b := by
  have hB : ((a⁻¹ * b : ↥(hsNB z s)) : G) ∈ hsB z s :=
    (M.ker _).mp (by rw [map_mul, map_inv, hab, inv_mul_cancel])
  have hc : ((a⁻¹ * b : ↥(hsNB z s)) : G) * x = x * ((a⁻¹ * b : ↥(hsNB z s)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (a : G)⁻¹ * b * x = (a : G)⁻¹ * (x * b) := by rw [mul_assoc, hbx]
      _ = (a : G)⁻¹ * (x * a) * (a : G)⁻¹ * b := by group
      _ = (a : G)⁻¹ * (a * x) * (a : G)⁻¹ * b := by rw [hax]
      _ = x * ((a : G)⁻¹ * b) := by group
  have h1 := M.eq_one_of_mem_hsB_comm hπx hB hc
  have : a⁻¹ * b = 1 := Subtype.ext h1
  rw [inv_mul_eq_one] at this
  exact this

theorem comm_of_normalizes {x : ↥(hsNB z s)} (hx3 : orderOf (x : G) = 3) (hπx : M.π x = σS0)
    {v : ↥(hsNB z s)} (hvx : (v : G) * x * (v : G)⁻¹ ∈ Subgroup.zpowers (x : G))
    (hπv : M.π v * σS0 * (M.π v)⁻¹ = σS0) : (v : G) * x = x * v := by
  have hvx' : (v : G) * x * (v : G)⁻¹ = x := by
    rcases eq_of_mem_zpowers_three hx3 hvx with h1 | h1 | h1
    · exfalso
      have : (x : G) = 1 := by
        calc (x : G) = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * v := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hx3
      exact absurd hx3 (by decide)
    · exact h1
    · exfalso
      have e : v * x * v⁻¹ = x⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        exact h1)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, map_inv, hπx, hπv] at e'
      exact σS0_inv_ne e'.symm
  calc (v : G) * x = (v : G) * x * (v : G)⁻¹ * v := by group
    _ = x * v := by rw [hvx']

include M in
theorem exists_i_ιS [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : ↥(hsNB z s)}
    (hx3 : orderOf (x : G) = 3) (hπx : M.π x = σS0) :
    ∃ i : ↥(hsNB z s), (i : G) * i = 1 ∧ (i : G) * x * (i : G)⁻¹ = (x : G)⁻¹ ∧
      (∃ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))), M.π i = σ * ιS) ∧
        ∃ c : G, c * z * c⁻¹ = i := by
  obtain ⟨v, hvx, σ, hσ, hπv⟩ := M.exists_normalizing_lift h hsmemH hsnotK hss hg₀ x hx3 ιS
    (by rw [hπx]; exact ιS_conj)
  rw [hπx] at hσ
  have hσ' := mem_zpowers_σS0 hσ
  obtain ⟨-, -, -, hfpf, hv2, hvinv, -⟩ := ιS_facts σ hσ'
  rw [← hπv] at hfpf hv2 hvinv
  have hvx' : (v : G) * x * (v : G)⁻¹ = (x : G)⁻¹ := by
    rcases eq_of_mem_zpowers_three hx3 hvx with h1 | h1 | h1
    · exfalso
      have : (x : G) = 1 := by
        calc (x : G) = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * v := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hx3
      exact absurd hx3 (by decide)
    · exfalso
      have e : v * x * v⁻¹ = x := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact h1)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, hπx, hvinv] at e'
      exact σS0_inv_ne e'
    · exact h1
  have hv2' : (v : G) * v = 1 := by
    have hB : ((v * v : ↥(hsNB z s)) : G) ∈ hsB z s := (M.ker _).mp (by rw [map_mul, hv2])
    refine M.eq_one_of_mem_hsB_comm hπx hB ?_
    calc (v : G) * v * x = v * (v * x * (v : G)⁻¹) * (v : G)⁻¹ * (v * v) := by group
      _ = v * (x : G)⁻¹ * (v : G)⁻¹ * (v * v) := by rw [hvx']
      _ = ((v : G) * x * (v : G)⁻¹)⁻¹ * (v * v) := by group
      _ = x * (v * v) := by rw [hvx', inv_inv]
  obtain ⟨c, hc⟩ := M.conj_z_of_fpf h hsmemH hsnotK hss hv2' hfpf
  exact ⟨v, hv2', hvx', ⟨σ, hσ', hπv⟩, c, hc⟩

include M in
theorem exists_y3 [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : ↥(hsNB z s)}
    (hx3 : orderOf (x : G) = 3) (hπx : M.π x = σS0) :
    ∃ y : ↥(hsNB z s), (y : G) * x = x * y ∧ orderOf (y : G) = 3 ∧
      (y : G) ∉ Subgroup.zpowers (x : G) ∧
        ∃ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))), M.π y = σ * ρ3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hvx, σ, hσ, hπv⟩ := M.exists_normalizing_lift h hsmemH hsnotK hss hg₀ x hx3 ρ3
    (by rw [hπx, ρ3_conj]; exact Subgroup.mem_zpowers _)
  rw [hπx] at hσ
  have hσ' := mem_zpowers_σS0 hσ
  obtain ⟨hv3, hvc, hvn⟩ := ρ3_facts σ hσ'
  rw [← hπv] at hv3 hvc hvn
  have hvx' := M.comm_of_normalizes hx3 hπx hvx hvc
  have hv3' : (v : G) ^ 3 = 1 := by
    have hB : ((v ^ 3 : ↥(hsNB z s)) : G) ∈ hsB z s := (M.ker _).mp (by rw [map_pow, hv3])
    have hc : ((v ^ 3 : ↥(hsNB z s)) : G) * x = x * ((v ^ 3 : ↥(hsNB z s)) : G) := by
      rw [Subgroup.coe_pow]
      exact (Commute.pow_left (show Commute (v : G) x from hvx') 3).eq
    have := M.eq_one_of_mem_hsB_comm hπx hB hc
    rwa [Subgroup.coe_pow] at this
  have hvX : (v : G) ∉ Subgroup.zpowers (x : G) := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have e : v = x ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
    apply hvn
    rw [e, map_zpow, hπx]
    exact mem_zpowers_σS0 (Subgroup.zpow_mem_zpowers _ k)
  have hv1 : (v : G) ≠ 1 := fun h1 => hvX (h1 ▸ Subgroup.one_mem _)
  exact ⟨v, hvx', orderOf_eq_prime hv3' hv1, hvX, σ, hσ', hπv⟩

include M in
theorem conj_mem_mul_zpowers {x i y : ↥(hsNB z s)} (hπx : M.π x = σS0)
    (hix : (i : G) * x * (i : G)⁻¹ = (x : G)⁻¹)
    (hπi : ∃ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))), M.π i = σ * ιS)
    (hyx : (y : G) * x = x * y)
    (hπy : ∃ σ ∈ ({1, σS0, σS0 * σS0} : Finset (Equiv.Perm (Fin 6))), M.π y = σ * ρ3) :
    (y : G)⁻¹ * ((i : G) * y * (i : G)⁻¹) ∈ Subgroup.zpowers (x : G) := by
  obtain ⟨σ, hσ, hπi⟩ := hπi
  obtain ⟨σ', hσ', hπy⟩ := hπy
  have hm := ιS_ρ3_facts σ hσ σ' hσ'
  rw [← hπi, ← hπy] at hm
  have hm' : M.π (i * y * i⁻¹ * y⁻¹) ∈ Subgroup.zpowers σS0 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mem_zpowers_σS0_iff.mpr hm
  rw [← hπx, ← MonoidHom.map_zpowers] at hm'
  obtain ⟨xk, ⟨k, rfl⟩, hk⟩ := hm'
  have hiyx : (i : G) * y * (i : G)⁻¹ * x = x * ((i : G) * y * (i : G)⁻¹) := by
    have hix' : (i : G)⁻¹ * x * i = (x : G)⁻¹ := inv_conj_of_inverts hix
    have hyx' : (y : G) * (x : G)⁻¹ = (x : G)⁻¹ * y := by
      calc (y : G) * (x : G)⁻¹ = (x : G)⁻¹ * (x * y) * (x : G)⁻¹ := by group
        _ = (x : G)⁻¹ * (y * x) * (x : G)⁻¹ := by rw [hyx]
        _ = (x : G)⁻¹ * y := by group
    calc (i : G) * y * (i : G)⁻¹ * x = (i : G) * (y * ((i : G)⁻¹ * x * i)) * (i : G)⁻¹ := by
          group
      _ = (i : G) * (y * (x : G)⁻¹) * (i : G)⁻¹ := by rw [hix']
      _ = (i : G) * ((x : G)⁻¹ * y) * (i : G)⁻¹ := by rw [hyx']
      _ = ((i : G) * x * (i : G)⁻¹)⁻¹ * ((i : G) * y * (i : G)⁻¹) := by group
      _ = x * ((i : G) * y * (i : G)⁻¹) := by rw [hix, inv_inv]
  have hxky : ((x ^ k * y : ↥(hsNB z s)) : G) * x = x * ((x ^ k * y : ↥(hsNB z s)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
    have hcomm : (x : G) * (x : G) ^ k = (x : G) ^ k * x := (Commute.self_zpow _ _).eq
    calc (x : G) ^ k * y * x = (x : G) ^ k * (y * x) := mul_assoc _ _ _
      _ = (x : G) ^ k * (x * y) := by rw [hyx]
      _ = ((x : G) ^ k * x) * y := (mul_assoc _ _ _).symm
      _ = ((x : G) * (x : G) ^ k) * y := by rw [hcomm]
      _ = x * ((x : G) ^ k * y) := mul_assoc _ _ _
  have hπeq : M.π (i * y * i⁻¹) = M.π (x ^ k * y) := by
    have h1 : M.π (x ^ k) = M.π (i * y * i⁻¹ * y⁻¹) := hk
    calc M.π (i * y * i⁻¹) = M.π (i * y * i⁻¹ * y⁻¹) * M.π y := by
          rw [← map_mul, inv_mul_cancel_right]
      _ = M.π (x ^ k) * M.π y := by rw [h1]
      _ = M.π (x ^ k * y) := (map_mul _ _ _).symm
  have e := M.eq_of_comm_of_π_eq hπx hπeq (by simpa using hiyx) hxky
  have e' : (i : G) * y * (i : G)⁻¹ = (x : G) ^ k * y := by
    have := congrArg Subtype.val e
    simpa using this
  rw [e']
  have hyxk : (y : G)⁻¹ * ((x : G) ^ k * y) = (x : G) ^ k := by
    rw [← (Commute.zpow_right (show Commute (y : G) x from hyx) k).eq, inv_mul_cancel_left]
  rw [hyxk]
  exact Subgroup.zpow_mem_zpowers _ k

end S6Model

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem cenQuot_s5_of
    [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z) (hx3 : orderOf x = 3)
    {i : G} (hii : i * i = 1) (hix : i * x * i⁻¹ = x⁻¹) {g : G} (hgi : g * z * g⁻¹ = i)
    {y : G} (hyx : y * x = x * y) (hy3 : orderOf y = 3) (hyX : y ∉ Subgroup.zpowers x)
    (hiy : y⁻¹ * (i * y * i⁻¹) ∈ Subgroup.zpowers x) :
    Nonempty (cenQuot x ≃* Equiv.Perm (Fin 5)) := by
  rcases h.cenQuot_s4_or_s5' hxH hx3 with he4 | he
  · exfalso
    obtain ⟨e⟩ := he4
    obtain ⟨c, hc, hcc, hsc⟩ := h.exists_inner_odd hxH hx3 permFacts_four e hii hix hgi
    have hyC : y ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyx
    set yb : cenQuot x := QuotientGroup.mk (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({x} : Set G)))
    have hfix : cenConj hix yb = yb := by
      rw [cenConj_mk]
      apply (QuotientGroup.eq).mpr
      rw [mem_cenX]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, cenConjC_coe]
      have : (i * y * i⁻¹)⁻¹ * y = (y⁻¹ * (i * y * i⁻¹))⁻¹ := by group
      rw [this]
      exact (Subgroup.zpowers x).inv_mem hiy
    rw [hc] at hfix
    have hcy : c * yb = yb * c := by
      calc c * yb = c * yb * c⁻¹ * c := by group
        _ = yb * c := by rw [hfix]
    have hyb1 : yb ≠ 1 := fun h1 => hyX ((cenQuot_mk_eq_one_iff _).mp h1)
    have hyb3 : yb * yb * yb = 1 := by
      have : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, ← hy3, pow_orderOf_eq_one]; rfl)
      rw [← pow_three', ← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
    have h1 : e c * e c = 1 := by rw [← map_mul, hcc, map_one]
    have h3 : e yb * e yb * e yb = 1 := by rw [← map_mul, ← map_mul, hyb3, map_one]
    have h4 : e yb ≠ 1 := fun h0 => hyb1 (e.injective (by rw [h0, map_one]))
    exact perm_four_odd_invol_not_comm_three (e c) (e yb) h1 hsc h3 h4
      (by rw [← map_mul, ← map_mul, hcy])
  · exact he

theorem exists_three_s5
    [Finite G] (h : HSSetting z V) :
    ∃ x : G, x ∈ hsH z ∧ orderOf x = 3 ∧ Nonempty (cenQuot x ≃* Equiv.Perm (Fin 5)) ∧
      ∃ i : G, i * i = 1 ∧ i * x * i⁻¹ = x⁻¹ ∧ ∃ g : G, g * z * g⁻¹ = i := by
  obtain ⟨s, ⟨hsmemH, -⟩, hss, hsinv, g₀, hg₀⟩ := h.exists_invol_inverts_ZQ
  have hsnotK := h.not_mem_K_of_inverts hsinv
  obtain ⟨M⟩ := h.nonempty_s6Model hsmemH hsnotK hss hg₀
  obtain ⟨x, hx3, hπx, -⟩ := M.exists_x2
  obtain ⟨i, hii, hix, hπi, ci, hci⟩ := M.exists_i_ιS h hsmemH hsnotK hss hg₀ hx3 hπx
  obtain ⟨y, hyx, hy3, hyX, hπy⟩ := M.exists_y3 h hsmemH hsnotK hss hg₀ hx3 hπx
  have hiy := M.conj_mem_mul_zpowers hπx hix hπi hyx hπy
  obtain ⟨j, -, hjx, a, haj⟩ := M.exists_j h hsmemH hsnotK hss hg₀ hx3 hπx
  set x' := a⁻¹ * (x : G) * a with hx'
  have hx'H : x' ∈ hsH z := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [hx']
    calc a⁻¹ * (x : G) * a * z = a⁻¹ * ((x : G) * (a * z * a⁻¹)) * a := by group
      _ = a⁻¹ * ((x : G) * j) * a := by rw [haj]
      _ = a⁻¹ * (j * x) * a := by rw [hjx]
      _ = a⁻¹ * ((a * z * a⁻¹) * x) * a := by rw [haj]
      _ = z * (a⁻¹ * (x : G) * a) := by group
  have hconj3 : ∀ w : G, orderOf (a⁻¹ * w * a) = orderOf w := fun w => by
    rw [show a⁻¹ * w * a = MulAut.conj a⁻¹ w by simp, MulEquiv.orderOf_eq]
  have hx'3 : orderOf x' = 3 := by rw [hx', hconj3, hx3]
  set i' := a⁻¹ * (i : G) * a with hi'
  set y' := a⁻¹ * (y : G) * a with hy'
  have hi'i' : i' * i' = 1 := by
    rw [hi']
    calc a⁻¹ * (i : G) * a * (a⁻¹ * (i : G) * a) = a⁻¹ * ((i : G) * i) * a := by group
      _ = 1 := by rw [hii]; group
  have hi'x' : i' * x' * i'⁻¹ = x'⁻¹ := by
    rw [hi', hx']
    calc a⁻¹ * (i : G) * a * (a⁻¹ * (x : G) * a) * (a⁻¹ * (i : G) * a)⁻¹ =
        a⁻¹ * ((i : G) * x * (i : G)⁻¹) * a := by group
      _ = (a⁻¹ * (x : G) * a)⁻¹ := by rw [hix]; group
  have hgi' : (a⁻¹ * ci) * z * (a⁻¹ * ci)⁻¹ = i' := by
    rw [hi', ← hci]
    group
  have hy'x' : y' * x' = x' * y' := by
    rw [hy', hx']
    calc a⁻¹ * (y : G) * a * (a⁻¹ * (x : G) * a) = a⁻¹ * ((y : G) * x) * a := by group
      _ = a⁻¹ * ((x : G) * y) * a := by rw [hyx]
      _ = a⁻¹ * (x : G) * a * (a⁻¹ * (y : G) * a) := by group
  have hy'3 : orderOf y' = 3 := by rw [hy', hconj3, hy3]
  have hconjX : ∀ w : G, w ∈ Subgroup.zpowers (x : G) → a⁻¹ * w * a ∈ Subgroup.zpowers x' := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have e : a⁻¹ * (x : G) ^ k * a = (a⁻¹ * (x : G) * a) ^ k := by
      have := (conj_zpow (a := a⁻¹) (b := (x : G)) (i := k)).symm
      rwa [inv_inv] at this
    rw [hx', e]
    exact Subgroup.zpow_mem_zpowers _ k
  have hy'X : y' ∉ Subgroup.zpowers x' := by
    intro hm
    apply hyX
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    have e : (y : G) = (x : G) ^ k := by
      calc (y : G) = a * y' * a⁻¹ := by rw [hy']; group
        _ = a * x' ^ k * a⁻¹ := by rw [hk]
        _ = (a * x' * a⁻¹) ^ k := conj_zpow.symm
        _ = (x : G) ^ k := by rw [hx']; group
    rw [e]
    exact Subgroup.zpow_mem_zpowers _ k
  have hiy' : y'⁻¹ * (i' * y' * i'⁻¹) ∈ Subgroup.zpowers x' := by
    have := hconjX _ hiy
    rwa [show a⁻¹ * ((y : G)⁻¹ * ((i : G) * y * (i : G)⁻¹)) * a = y'⁻¹ * (i' * y' * i'⁻¹) by
      rw [hy', hi']; group] at this
  exact ⟨x', hx'H, hx'3, h.cenQuot_s5_of hx'H hx'3 hi'i' hi'x' hgi' hy'x' hy'3 hy'X hiy',
    i', hi'i', hi'x', _, hgi'⟩

end HSSetting

end CFSG.Quasithin.HSType
