module

public import CFSG.RankThree.Native.ONSevenCentralizers

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7

open CFSG.ONSchreier CFSG.RankThree.Native

section General

variable {G : Type*} [Group G]

theorem card_centralizer_map_equiv {H : Type*} [Group H] (e : G ≃* H) (a : G) :
    Nat.card (Subgroup.centralizer ({e a} : Set H)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  have h : Subgroup.centralizer ({e a} : Set H) =
      (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom := by
    ext y
    simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, hz, map_mul]
  rw [h, Subgroup.card_map_of_injective e.injective]

theorem card_centralizer_conj (g a : G) :
    Nat.card (Subgroup.centralizer ({g * a * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) :=
  card_centralizer_map_equiv (MulAut.conj g) a

theorem card_centralizer_subgroup_eq (K : Subgroup G) (x : K) :
    Nat.card (Subgroup.centralizer ({x} : Set K)) =
      Nat.card (Subgroup.centralizer ({(x : G)} : Set G) ⊓ K : Subgroup G) := by
  have h : (Subgroup.centralizer ({x} : Set K)).map K.subtype =
      Subgroup.centralizer ({(x : G)} : Set G) ⊓ K := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨by simpa only [Subgroup.coe_mul] using congrArg Subtype.val hz, z.2⟩
    · rintro ⟨hy, hyK⟩
      exact ⟨⟨y, hyK⟩, Subtype.ext (by simpa only [Subgroup.coe_mul] using hy), rfl⟩
  rw [← h, Subgroup.card_map_of_injective K.subtype_injective]

theorem centralizer_singleton_eq_of_zpowers_eq {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, h,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem zpowers_pow_eq_of_coprime [Finite G] {w : G} {e : ℕ} (h : Nat.Coprime (orderOf w) e) :
    Subgroup.zpowers (w ^ e) = Subgroup.zpowers w := by
  refine Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers w) e)) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow h]

end General

section Pv

theorem exists_conj_mem_onSevenQ {u : Pv} {k : ℕ} (hu : u ^ 7 ^ k = 1) :
    ∃ g : Pv, ((g * u * g⁻¹ : Pv) : Equiv.Perm (Fin N)) ∈ onSevenQ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨⟨-, ⟨S, hS⟩, -, -⟩, -⟩ := R3E_ON_full_seven_centralizer_structures
  have hp : IsPGroup 7 (Subgroup.zpowers u) := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Pv P S
  refine ⟨g, ?_⟩
  have hu' : u ∈ (P : Subgroup Pv) := hP (Subgroup.mem_zpowers u)
  have h1 : MulAut.conj g • u ∈ ((g • P : Sylow 7 Pv) : Subgroup Pv) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) (P : Subgroup Pv) hu'
  rw [hg, hS, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem card_centralizer_seven_Pv {u : Pv} (hu : orderOf u = 7) :
    Nat.card (Subgroup.centralizer ({u} : Set Pv)) = 1372 ∨
      Nat.card (Subgroup.centralizer ({u} : Set Pv)) = 49 := by
  obtain ⟨-, ⟨hlines, -⟩, hC, hlow, hhigh, htrans, hcover⟩ :=
    R3E_ON_full_seven_centralizer_structures
  have hmemP := onSeven_mem_P.2.1
  obtain ⟨g, hg⟩ := exists_conj_mem_onSevenQ (k := 1) (by rw [pow_one, ← hu, pow_orderOf_eq_one])
  set v : Pv := g * u * g⁻¹ with hvdef
  have hCuv : Nat.card (Subgroup.centralizer ({u} : Set Pv)) =
      Nat.card (Subgroup.centralizer ({v} : Set Pv)) := (card_centralizer_conj g u).symm
  have hvo : orderOf (v : Equiv.Perm (Fin N)) = 7 := by
    rw [Subgroup.orderOf_coe, hvdef]
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
    rw [← hu, ← this]
    rfl
  have hlo : ∀ i : Fin 57, orderOf (onSevenLine i) = 7 := by
    intro i
    have h1 : Subgroup.zpowers (onSevenLine i) ∈
        {H : Subgroup (Equiv.Perm (Fin N)) | H ≤ onSevenQ ∧ Nat.card H = 7} := by
      rw [hlines]
      exact ⟨i, rfl⟩
    rw [← Nat.card_zpowers]
    exact h1.2
  have hmem : Subgroup.zpowers (v : Equiv.Perm (Fin N)) ∈
      {H : Subgroup (Equiv.Perm (Fin N)) | H ≤ onSevenQ ∧ Nat.card H = 7} :=
    ⟨Subgroup.zpowers_le.mpr hg, by rw [Nat.card_zpowers, hvo]⟩
  rw [hlines] at hmem
  obtain ⟨j, hj⟩ := hmem
  obtain ⟨r, t, ht, htj⟩ := hcover j
  obtain ⟨htP, hp1, hp6, hlt, hteq⟩ := htrans r t ht
  have hjt : (⟨t.line, hlt⟩ : Fin 57) = j := Fin.ext htj
  rw [hjt] at hteq
  set τ : Pv := ⟨onSevenTransporterPerm t, htP⟩ with hτdef
  set ρ : Pv := ⟨onSevenLine (onSevenRep r), hmemP _⟩ with hρdef
  set w : Equiv.Perm (Fin N) :=
    onSevenTransporterPerm t * onSevenLine (onSevenRep r) * (onSevenTransporterPerm t)⁻¹
    with hwdef
  have hwτρ : ((τ * ρ * τ⁻¹ : Pv) : Equiv.Perm (Fin N)) = w := rfl
  have hwo : orderOf w = 7 := by
    rw [← hwτρ, Subgroup.orderOf_coe]
    have := orderOf_injective (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective ρ
    have hρo : orderOf ρ = 7 := by
      rw [← Subgroup.orderOf_coe]
      exact hlo _
    rw [← hρo, ← this]
    rfl
  have hcop : Nat.Coprime (orderOf w) t.power := by
    rw [hwo]
    refine (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 fun h => ?_
    have := Nat.le_of_dvd (by omega) h
    omega
  have hzw : Subgroup.zpowers (v : Equiv.Perm (Fin N)) = Subgroup.zpowers w := by
    have hj' : Subgroup.zpowers (onSevenLine j) = Subgroup.zpowers (v : Equiv.Perm (Fin N)) := hj
    rw [← hj', ← hteq, zpowers_pow_eq_of_coprime hcop]
  have hCvw := centralizer_singleton_eq_of_zpowers_eq hzw
  have hCρ : Nat.card (Subgroup.centralizer ({ρ} : Set Pv)) = Nat.card (onSevenC r) := by
    rw [card_centralizer_subgroup_eq, hC r]
  have hvτρ : Nat.card (Subgroup.centralizer ({v} : Set Pv)) =
      Nat.card (Subgroup.centralizer ({τ * ρ * τ⁻¹} : Set Pv)) := by
    rw [card_centralizer_subgroup_eq, card_centralizer_subgroup_eq, hwτρ, hCvw]
  rw [hCuv, hvτρ, card_centralizer_conj, hCρ]
  by_cases hr : r.val < 3
  · left
    have h1 := (hlow ⟨r.val, hr⟩).1
    have h2 : (Fin.castLE (by norm_num) (⟨r.val, hr⟩ : Fin 3) : Fin 5) = r := Fin.ext rfl
    rwa [h2] at h1
  · right
    exact hhigh r (by omega)

end Pv

section ON

theorem card_centralizer_seven_of_mulEquiv {G : Type*} [Group G] (e : G ≃* Pv) {u : G}
    (hu : orderOf u = 7) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) = 1372 ∨
      Nat.card (Subgroup.centralizer ({u} : Set G)) = 49 := by
  rw [← card_centralizer_map_equiv e u]
  exact card_centralizer_seven_Pv (by rw [MulEquiv.orderOf_eq]; exact hu)

theorem card_centralizer_seven_ON {T : Type} [Group T] (e : T ≃* CFSG.Blueprint.NativeSporadic.ON)
    {u : T} (hu : orderOf u = 7) :
    Nat.card (Subgroup.centralizer ({u} : Set T)) = 1372 ∨
      Nat.card (Subgroup.centralizer ({u} : Set T)) = 49 :=
  card_centralizer_seven_of_mulEquiv
    (e.trans (by exact onEquivPv : CFSG.Blueprint.NativeSporadic.ON ≃* Pv)) hu

end ON

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7
