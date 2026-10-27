module

public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Act
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Sp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.QuasithinUnique.Lin2.Five

variable {F : Type} [Field F]

omit [Field F] in
theorem odd_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h2 : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one

theorem exists_unit_ne_one [Finite F] (h4 : 4 ≤ Nat.card F) : ∃ a : Fˣ, a ≠ 1 := by
  have hcard : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  exact exists_ne (1 : Fˣ)

theorem fix_family {G : Type*} [Group G] (β : MulAut G) (N : Subgroup G)
    (hfix : ∀ z ∈ N, Odd (orderOf z) → β z = z) (y : F → G)
    (hadd : ∀ t t', y t * y t' = y (t + t')) (hyN : ∀ t, y t ∈ N)
    (h : G) (hhN : h ∈ N) (hodd : Odd (orderOf h)) (χ : F) (hχ : χ - 1 ≠ 0)
    (hconj : ∀ t, h * y t * h⁻¹ = y (χ * t)) (t : F) : β (y t) = y t := by
  have hy0 : y 0 = 1 := by
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact mul_eq_left.mp h0
  have hyinv : ∀ t, (y t)⁻¹ = y (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [hadd, add_neg_cancel, hy0])
  set s : F := t / (χ - 1) with hs
  have hs' : (χ - 1) * s = t := by
    rw [hs]
    field_simp
  have key : y t = h * (y s * h⁻¹ * (y s)⁻¹) := by
    have e1 : y s * h⁻¹ = h⁻¹ * y (χ * s) := by
      calc y s * h⁻¹ = h⁻¹ * (h * y s * h⁻¹) := by group
        _ = h⁻¹ * y (χ * s) := by rw [hconj s]
    rw [e1, hyinv, ← mul_assoc, mul_inv_cancel_left, hadd]
    congr 1
    rw [← hs']
    ring
  have hz : y s * h⁻¹ * (y s)⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (hyN _) (N.inv_mem hhN)) (N.inv_mem (hyN _))
  have hzo : Odd (orderOf (y s * h⁻¹ * (y s)⁻¹)) := by
    have e : y s * h⁻¹ * (y s)⁻¹ = MulAut.conj (y s) h⁻¹ := by rw [MulAut.conj_apply]
    rw [e, MulEquiv.orderOf_eq, orderOf_inv]
    exact hodd
  rw [key, map_mul, hfix h hhN hodd, hfix _ hz hzo]

theorem tauS_split (b c d : F) : tauS b c d = tauS b 0 0 * tauS 0 c 0 * tauS 0 0 d := by
  rw [tauS_mul_tauS, tauS_mul_tauS]
  simp

theorem odd_orderOf_proj_torusHom {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card F = 2 ^ n)
    (s : Fin 2 → Fˣ) : Odd (orderOf (proj 2 F (SymplecticTorusWeyl.torusHom s))) := by
  have h1 : (proj 2 F (SymplecticTorusWeyl.torusHom s)) ^ Nat.card Fˣ = 1 := by
    rw [← map_pow, ← map_pow]
    have hs : s ^ Nat.card Fˣ = 1 := by
      funext i
      simp [Pi.pow_apply, pow_card_eq_one']
    rw [hs, map_one, map_one]
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units, hK]
    exact odd_two_pow_sub_one hn
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem coords_of_torus_comm {b c d a : F} (s : Fin 2 → Fˣ)
    (h : SymplecticTorusWeyl.torusHom s * (tauS b c d * lam a) =
      (tauS b c d * lam a) * SymplecticTorusWeyl.torusHom s) :
    (s 0 : F) ^ 2 * b = b ∧ (s 0 : F) * (s 1 : F) * c = c ∧ (s 1 : F) ^ 2 * d = d ∧
      (s 0 : F) * (s 1 : F)⁻¹ * a = a := by
  rw [← mul_assoc, torusHom_mul_tauS, mul_assoc, torusHom_mul_lam, ← mul_assoc] at h
  exact tauS_mul_lam_injective (mul_right_cancel h)

variable [Finite F] [CharP F 2]

theorem eq_one_of_fixes_odd_normalizer_unip {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hfix : ∀ z ∈ Subgroup.normalizer (projUnipotent 2 F : Set (StatedProj (StatedSp 2 F))),
      Odd (orderOf z) → β z = z) : β = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card F := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨a, ha⟩ := exists_unit_ne_one (F := F) h4
  have ha1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have ha2 : (a : F) ^ 2 ≠ 1 := sq_ne_one_of_charTwo ha1
  have hUN : projUnipotent 2 F ≤
      Subgroup.normalizer (projUnipotent 2 F : Set (StatedProj (StatedSp 2 F))) :=
    Subgroup.le_normalizer
  have htorN : ∀ s : Fin 2 → Fˣ, proj 2 F (SymplecticTorusWeyl.torusHom s) ∈
      Subgroup.normalizer (projUnipotent 2 F : Set (StatedProj (StatedSp 2 F))) := by
    intro s
    rw [normalizer_projUnipotent (r := 2) (K := F) 2 (by norm_num)]
    exact ⟨SymplecticTorusWeyl.torusHom s, torus_le_borelSubgroup ⟨s, rfl⟩, rfl⟩
  have htorFix : ∀ s : Fin 2 → Fˣ, β (proj 2 F (SymplecticTorusWeyl.torusHom s)) =
      proj 2 F (SymplecticTorusWeyl.torusHom s) := fun s =>
    hfix _ (htorN s) (odd_orderOf_proj_torusHom (by omega) hK s)
  have hmemU : ∀ u ∈ unipotent 2 F, proj 2 F u ∈ projUnipotent 2 F := fun u hu => ⟨u, hu, rfl⟩
  have hF1 : ∀ t : F, β (proj 2 F (tauS t 0 0)) = proj 2 F (tauS t 0 0) := by
    refine fix_family β _ hfix (fun t => proj 2 F (tauS t 0 0)) ?_
      (fun t => hUN (hmemU _ (tauS_mem_unipotent _ _ _)))
      (proj 2 F (SymplecticTorusWeyl.torusHom ![a, 1])) (htorN _)
      (odd_orderOf_proj_torusHom (by omega) hK _) ((a : F) ^ 2) (sub_ne_zero.mpr ha2) ?_
    · intro t t'
      rw [← map_mul, tauS_mul_tauS]
      simp
    · intro t
      rw [← map_inv, ← map_mul, ← map_mul, torusHom_first_conj_tauS]
      simp
  have hF2 : ∀ t : F, β (proj 2 F (tauS 0 t 0)) = proj 2 F (tauS 0 t 0) := by
    refine fix_family β _ hfix (fun t => proj 2 F (tauS 0 t 0)) ?_
      (fun t => hUN (hmemU _ (tauS_mem_unipotent _ _ _)))
      (proj 2 F (SymplecticTorusWeyl.torusHom ![a, 1])) (htorN _)
      (odd_orderOf_proj_torusHom (by omega) hK _) (a : F) (sub_ne_zero.mpr ha1) ?_
    · intro t t'
      rw [← map_mul, tauS_mul_tauS]
      simp
    · intro t
      rw [← map_inv, ← map_mul, ← map_mul, torusHom_first_conj_tauS]
      simp
  have hF3 : ∀ t : F, β (proj 2 F (tauS 0 0 t)) = proj 2 F (tauS 0 0 t) := by
    refine fix_family β _ hfix (fun t => proj 2 F (tauS 0 0 t)) ?_
      (fun t => hUN (hmemU _ (tauS_mem_unipotent _ _ _)))
      (proj 2 F (SymplecticTorusWeyl.torusHom ![1, a])) (htorN _)
      (odd_orderOf_proj_torusHom (by omega) hK _) ((a : F) ^ 2) (sub_ne_zero.mpr ha2) ?_
    · intro t t'
      rw [← map_mul, tauS_mul_tauS]
      simp
    · intro t
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [mul_inv_eq_iff_eq_mul, torusHom_mul_tauS]
      simp
  have hF4 : ∀ t : F, β (proj 2 F (lam t)) = proj 2 F (lam t) := by
    refine fix_family β _ hfix (fun t => proj 2 F (lam t)) ?_
      (fun t => hUN (hmemU _ (lam_mem_unipotent _)))
      (proj 2 F (SymplecticTorusWeyl.torusHom ![a, 1])) (htorN _)
      (odd_orderOf_proj_torusHom (by omega) hK _) (a : F) (sub_ne_zero.mpr ha1) ?_
    · intro t t'
      rw [← map_mul, lam_mul]
    · intro t
      rw [← map_inv, ← map_mul, ← map_mul, torusHom_first_conj_lam]
  have hU : ∀ u ∈ unipotent 2 F, β (proj 2 F u) = proj 2 F u := by
    intro u hu
    obtain ⟨C, hC, a', rfl⟩ := mem_unipotent_iff.mp hu
    rw [tau_eq_tauS, tauS_split]
    simp only [map_mul, hF1, hF2, hF3, hF4]
  have hα : ∀ x, β x ∈ projUnipotent 2 F ↔ x ∈ projUnipotent 2 F :=
    mem_iff_of_forall_mem β _ (by
      rintro _ ⟨u, hu, rfl⟩
      rw [hU u hu]
      exact hmemU u hu)
  obtain ⟨l₁, l₂, σ, ε, -, -, hact, hid⟩ := exists_vAct (by omega) hK hα
  have hVfix : ∀ x : F × F, vAct l₁ l₂ σ ε x = x := by
    intro x
    have h1 := hact x
    rw [show vP x.1 x.2 = proj 2 F (tauS x.1 x.2 0) from rfl,
      hU _ (tauS_mem_unipotent _ _ _)] at h1
    have h2 := vP_injective h1.symm
    exact Prod.ext h2.1 h2.2
  obtain ⟨u, hu, hβu⟩ := hid hVfix
  have hcomm : ∀ s : Fin 2 → Fˣ, SymplecticTorusWeyl.torusHom s * u =
      u * SymplecticTorusWeyl.torusHom s := by
    intro s
    have h1 := htorFix s
    rw [hβu, MulAut.conj_apply] at h1
    have h2 : proj 2 F (u * SymplecticTorusWeyl.torusHom s * u⁻¹) =
        proj 2 F (SymplecticTorusWeyl.torusHom s) := by
      rw [map_mul, map_mul, map_inv]
      exact h1
    have h3 := proj_injective h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hu1 : u = 1 := by
    obtain ⟨C, hC, a', rfl⟩ := mem_unipotent_iff.mp hu
    rw [tau_eq_tauS] at hcomm ⊢
    obtain ⟨hb, hc, -, ha'⟩ := coords_of_torus_comm ![a, 1] (hcomm ![a, 1])
    obtain ⟨-, -, hd, -⟩ := coords_of_torus_comm ![1, a] (hcomm ![1, a])
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, inv_one,
      mul_one] at hb hc hd ha'
    have hsub : (a : F) - 1 ≠ 0 := sub_ne_zero.mpr ha1
    have hb0 : C 0 0 = 0 := by
      have : ((a : F) ^ 2 - 1) * C 0 0 = 0 := by linear_combination hb
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha2)
    have hc0 : C 0 1 = 0 := by
      have : ((a : F) - 1) * C 0 1 = 0 := by linear_combination hc
      exact (mul_eq_zero.mp this).resolve_left hsub
    have hd0 : C 1 1 = 0 := by
      have : ((a : F) ^ 2 - 1) * C 1 1 = 0 := by linear_combination hd
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha2)
    have ha0 : a' = 0 := by
      have : ((a : F) - 1) * a' = 0 := by linear_combination ha'
      exact (mul_eq_zero.mp this).resolve_left hsub
    rw [hb0, hc0, hd0, ha0, tauS_zero, lam_zero, mul_one]
  rw [hβu, hu1, map_one, map_one]

theorem eq_one_of_fixes_odd_normalizer_sp4 {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n)
    (Q : Sylow 2 (StatedProj (StatedSp 2 F))) (β : MulAut (StatedProj (StatedSp 2 F)))
    (hβ : ∀ z ∈ Subgroup.normalizer ((Q : Subgroup (StatedProj (StatedSp 2 F))) :
      Set (StatedProj (StatedSp 2 F))), Odd (orderOf z) → β z = z) : β = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnipotent (K := F) (r := 2) 2 (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 F)) U₀ Q
  have hmem : ∀ x, x ∈ (Q : Subgroup (StatedProj (StatedSp 2 F))) ↔
      g⁻¹ * x * g ∈ projUnipotent 2 F := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * (g * y * g⁻¹) * g ∈ _
      simpa [mul_assoc] using hy
    · intro h
      refine ⟨g⁻¹ * x * g, h, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  set β' : MulAut (StatedProj (StatedSp 2 F)) := (MulAut.conj g)⁻¹ * β * MulAut.conj g with hβ'
  have hfix : ∀ z ∈ Subgroup.normalizer (projUnipotent 2 F : Set (StatedProj (StatedSp 2 F))),
      Odd (orderOf z) → β' z = z := by
    intro z hz hzo
    have hzN : g * z * g⁻¹ ∈ Subgroup.normalizer ((Q : Subgroup (StatedProj (StatedSp 2 F))) :
        Set (StatedProj (StatedSp 2 F))) := by
      rw [Subgroup.mem_normalizer_iff] at hz ⊢
      intro x
      rw [hmem x, hmem (g * z * g⁻¹ * x * (g * z * g⁻¹)⁻¹)]
      have e : g⁻¹ * (g * z * g⁻¹ * x * (g * z * g⁻¹)⁻¹) * g = z * (g⁻¹ * x * g) * z⁻¹ := by
        group
      rw [e]
      exact hz _
    have hord : Odd (orderOf (g * z * g⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hzo
    have h1 := hβ _ hzN hord
    have e1 : β' z = (MulAut.conj g)⁻¹ (β (MulAut.conj g z)) := rfl
    rw [e1, MulAut.conj_apply, h1]
    simp [MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc]
  have hone : β' = 1 := eq_one_of_fixes_odd_normalizer_unip hn hK β' hfix
  calc β = MulAut.conj g * β' * (MulAut.conj g)⁻¹ := by rw [hβ']; group
    _ = 1 := by rw [hone]; group

end CFSG.Quasithin.Sp4

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem centralizes_of_centralizes_borel_sp4 {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    {n : ℕ} (hn : 2 ≤ n) (hL : IsPSp4 2 n ↥L) (hP : IsSylowTwoOf P L)
    {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) :
    ∀ l ∈ L, v * l = l * v := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨φ⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  let Q : Sylow 2 (StatedProj (StatedSp 2 K)) :=
    (A4.toSylow hP).mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hQ : (Q : Subgroup (StatedProj (StatedSp 2 K))) = (P.subgroupOf L).map φ.toMonoidHom := rfl
  let α : MulAut ↥L := conjAct L ⟨v, hv⟩
  let β : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr φ α
  have hβ : ∀ z ∈ Subgroup.normalizer ((Q : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))), Odd (orderOf z) → β z = z := by
    intro z hz hzo
    set z' : ↥L := φ.symm z with hz'
    have hzz' : φ z' = z := by simp [hz']
    have hz'N : ∀ x : ↥L, x ∈ P.subgroupOf L ↔ z' * x * z'⁻¹ ∈ P.subgroupOf L := by
      intro x
      have h := Subgroup.mem_normalizer_iff.mp hz (φ x)
      rw [hQ, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h
      simpa [hz', map_mul, map_inv] using h
    have hz'G : (z' : G) ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have hgL : g ∈ L := hP.1 hg
        have := (hz'N ⟨g, hgL⟩).mp hg
        simpa [Subgroup.mem_subgroupOf] using this
      · intro hg
        have hgL : (z' : G) * g * (z' : G)⁻¹ ∈ L := hP.1 hg
        have hgL' : g ∈ L := by
          have h1 : (z' : G)⁻¹ * ((z' : G) * g * (z' : G)⁻¹) * (z' : G) ∈ L :=
            L.mul_mem (L.mul_mem (L.inv_mem z'.2) hgL) z'.2
          simpa [mul_assoc] using h1
        exact (Subgroup.mem_subgroupOf.mp ((hz'N ⟨g, hgL'⟩).mpr (by
          simpa [Subgroup.mem_subgroupOf] using hg)))
    have hzo' : Odd (orderOf (z' : G)) := by
      rw [Subgroup.orderOf_coe, hz', MulEquiv.orderOf_eq]
      exact hzo
    have hmem : (z' : G) ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)) :=
      mem_oTwoUpper_of_odd ⟨z'.2, hz'G⟩ hzo'
    have hcomm := hc _ hmem
    have hαz : α z' = z' := by
      apply Subtype.ext
      change v * (z' : G) * v⁻¹ = (z' : G)
      rw [hcomm]
      group
    change φ (α (φ.symm z)) = z
    rw [← hz', hαz, hzz']
  have hβ1 : β = 1 := Sp4.eq_one_of_fixes_odd_normalizer_sp4 hn hK Q β hβ
  intro l hl
  have h1 : α ⟨l, hl⟩ = ⟨l, hl⟩ := by
    have := congrArg (fun γ : MulAut (StatedProj (StatedSp 2 K)) => φ.symm (γ (φ ⟨l, hl⟩))) hβ1
    simpa [β, MulAut.congr] using this
  have h2 := congrArg (fun x : ↥L => (x : G)) h1
  have h3 : v * l * v⁻¹ = l := h2
  calc v * l = (v * l * v⁻¹) * v := by group
    _ = l * v := by rw [h3]

end CFSG.Quasithin
