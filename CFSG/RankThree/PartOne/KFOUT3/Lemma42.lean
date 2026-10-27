module

public import CFSG.RankThree.PartOne.KFOUT3.LemmaF

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {K : Type} [Field K]

theorem eq_of_forall_RB {Ψ₁ Ψ₂ : MulAut (PSL3 K)} (h : ∀ b s, Ψ₁ (RB b s) = Ψ₂ (RB b s)) :
    Ψ₁ = Ψ₂ := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  let α : SL3 K →* PSL3 K := Ψ₁.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (SL3 K)))
  let β : SL3 K →* PSL3 K := Ψ₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (SL3 K)))
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) K → SL3 K)) ≤ MonoidHom.eqLocus α β := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    show Ψ₁ (QuotientGroup.mk t.toSpecialLinearGroup) = Ψ₂ (QuotientGroup.mk t.toSpecialLinearGroup)
    exact h ⟨(t.i, t.j), t.hij⟩ t.c
  have hx : y ∈ MonoidHom.eqLocus α β := by
    apply hle
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top y
  exact hx

theorem eps_false_of_iterate {ε : Bool} {m : ℕ} (hm : Odd m)
    (h : (rho (1 : Equiv.Perm (Fin 3)) ε)^[m] = id) : ε = false := by
  by_contra hε
  have hε' : ε = true := by simpa using hε
  subst hε'
  have h2 : ∀ b : Blk, rho (1 : Equiv.Perm (Fin 3)) true (rho (1 : Equiv.Perm (Fin 3)) true b) =
      b := fun b => rfl
  obtain ⟨k, rfl⟩ := hm
  have h3 : ∀ (j : ℕ) (b : Blk), (rho (1 : Equiv.Perm (Fin 3)) true)^[2 * j] b = b := by
    intro j
    induction j with
    | zero => intro b; rfl
    | succ j ih =>
      intro b
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, Function.iterate_add_apply]
      have : (rho (1 : Equiv.Perm (Fin 3)) true)^[2] b = b := h2 b
      rw [this]
      exact ih b
  have h4 := congrFun h ⟨(0, 1), by decide⟩
  rw [Function.iterate_add_apply, h3] at h4
  have h5 := congrArg (fun b : Blk => b.1.1) h4
  simp [rho] at h5

theorem commutatorElement_mul_mul_central' {H : Type*} [Group H] (a b : H) {z w : H}
    (hz : z ∈ Subgroup.center H) (hw : w ∈ Subgroup.center H) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g, z * g * z⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have h2 : ∀ g, w * g * w⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hw g, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [h1]; group
    _ = ⁅a, b⁆ := by rw [h2, commutatorElement_def]

theorem mem_centralizer_of_trivial_action {G : Type} [Group G] {J : Subgroup G}
    (hJ : Group.IsPerfect ↥J) {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : ∀ j : ↥J, (QuotientGroup.mk (jConj hg j) : ↥J ⧸ Subgroup.center ↥J) =
      QuotientGroup.mk j) : g ∈ Subgroup.centralizer (J : Set G) := by
  let F : Subgroup ↥J := MonoidHom.eqLocus (jConj hg).toMonoidHom (MonoidHom.id ↥J)
  have hcomm : ∀ a b : ↥J, ⁅a, b⁆ ∈ F := by
    intro a b
    have ha : a⁻¹ * jConj hg a ∈ Subgroup.center ↥J := QuotientGroup.eq.1 (h a).symm
    have hb : b⁻¹ * jConj hg b ∈ Subgroup.center ↥J := QuotientGroup.eq.1 (h b).symm
    have e1 : jConj hg a = a * (a⁻¹ * jConj hg a) := by group
    have e2 : jConj hg b = b * (b⁻¹ * jConj hg b) := by group
    show jConj hg ⁅a, b⁆ = ⁅a, b⁆
    rw [show jConj hg ⁅a, b⁆ = ⁅jConj hg a, jConj hg b⁆ from map_commutatorElement
      (jConj hg).toMonoidHom a b, e1, e2, commutatorElement_mul_mul_central' a b ha hb]
  have hF : F = ⊤ := by
    rw [eq_top_iff, ← hJ.commutator_eq_top]
    show ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ ≤ F
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a b
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxF : (⟨x, hx⟩ : ↥J) ∈ F := by rw [hF]; exact Subgroup.mem_top _
  have := congrArg Subtype.val (show jConj hg ⟨x, hx⟩ = ⟨x, hx⟩ from hxF)
  simp only [jConj_apply] at this
  calc x * g = (g * x * g⁻¹) * g := by rw [this]
    _ = g * x := by group

theorem jLemma42 : JLemma42 := by
  intro G _ _ p A c J h f hpf hmodel hq z hz hz3 k hk1 hk3 hact g hgN hgC hgn
  obtain ⟨n, hgn⟩ := hgn
  have hf1 : 1 ≤ f := hmodel.1.2.1
  obtain ⟨K, hKf, hKfin, hchar, hK, ζ, hζ, ι, hmaps, honto⟩ := exists_model_of_JGood h hpf hmodel
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hz' : IsZeta p ζ := IsZeta.of_orderOf h5 hζ
  have hzN : z ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.1 hz).1
  have hTz : ∀ t ∈ Tof A J, z * t * z⁻¹ ∈ Tof A J := fun t ht => by
    rw [hact t ht]
    exact Subgroup.pow_mem _ ht k
  have hTg1 : ∀ t ∈ Tof A J, g * t * g⁻¹ = t ^ 1 := fun t ht => by
    have := Subgroup.mem_centralizer_iff.1 hgC t (Tof_le A J ht)
    rw [pow_one, ← this, mul_inv_cancel_right]
  have hTg : ∀ t ∈ Tof A J, g * t * g⁻¹ ∈ Tof A J := fun t ht => by
    rw [hTg1 t ht, pow_one]
    exact ht
  have hTz' := conjAut_Tbar (Tof_le_J h) ι hmaps honto hzN hTz
  have hTg' := conjAut_Tbar (Tof_le_J h) ι hmaps honto hgN hTg
  have hactz := conjAut_action (Tof_le_J h) ι honto hzN hact
  have hactg := conjAut_action (Tof_le_J h) ι honto hgN hTg1
  obtain ⟨πz, εz, σz, cz, hcz, hformz⟩ := exists_hasForm hz' (conjAut ι hzN) hTz'
  obtain ⟨πg, εg, σg, cg, hcg, hformg⟩ := exists_hasForm hz' (conjAut ι hgN) hTg'
  have hkz : ¬ p ∣ k := not_dvd_of_pow_three_mod hk3
  have hk1' : ¬ p ∣ 1 := fun hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)
  obtain ⟨hπz, hσz⟩ := scalar_action hp hz' hcz hformz hkz hactz
  obtain ⟨hπg, hσg⟩ := scalar_action hp hz' hcg hformg hk1' hactg
  subst hπz hπg
  obtain ⟨hρz, hσz3⟩ := hformz.pow_eq_one (conjAut_pow_eq_one ι hzN hz3)
  have hΨgn : conjAut ι hgN ^ (3 ^ n) = 1 := conjAut_pow_eq_one ι hgN hgn
  obtain ⟨hρg, hσgn⟩ := hformg.pow_eq_one hΨgn
  have hεz : εz = false := eps_false_of_iterate (by decide : Odd 3) hρz
  have hεg : εg = false := eps_false_of_iterate (Odd.pow (by decide : Odd 3)) hρg
  subst hεz hεg
  have hσzζ : σz (ζ : K) = (ζ : K) ^ k := by
    rcases hσz with ⟨-, h1⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (by decide)
  have hσgζ : σg (ζ : K) = (ζ : K) ^ 1 := by
    rcases hσg with ⟨-, h1⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (by decide)
  rw [pow_one] at hσgζ
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk3
      simp at hk3
    · exact h0
  have hne : σz (ζ : K) ≠ (ζ : K) := by
    rw [hσzζ]
    intro e
    have e' : ζ ^ k = ζ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact e)
    have h3 : ζ ^ (k - 1) = 1 := by
      have : ζ ^ (k - 1) * ζ = ζ := by
        rw [← pow_succ, Nat.sub_add_cancel hk0]
        exact e'
      exact mul_eq_right.1 this
    rw [hz'.pow_eq_one_iff hp] at h3
    obtain ⟨t, ht⟩ := h3
    apply hk1
    have h6 : k = p * t + 1 := by omega
    rw [h6, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.one_lt]
  have hσg1 : σg = 1 := aut_eq_one_of_three_power hf1 hK hσz3 hne hσgn hσgζ
  subst hσg1
  have hform' : HasForm (conjAut ι hgN) id (1 : K ≃+* K) cg := by
    intro b s
    exact hformg b s
  have hcg1 : ∀ b, cg b = 1 := by
    intro b
    have h1 := hform'.pow_scalar_eq_one hΨgn b
    have hu0 : cg b ≠ 0 := hcg b
    let u : Kˣ := Units.mk0 (cg b) hu0
    have hu1 : u ^ (3 ^ n) = 1 := Units.ext (by simp [u, h1])
    have hcard : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
    have hu2 : u ^ (2 ^ f - 1) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hcop : Nat.Coprime (3 ^ n) (2 ^ f - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      have : 0 < 2 ^ f := by positivity
      omega
    have := pow_gcd_eq_one.2 ⟨hu1, hu2⟩
    rw [hcop, pow_one] at this
    exact congrArg Units.val this
  have hΨg1 : conjAut ι hgN = 1 := by
    apply eq_of_forall_RB
    intro b s
    rw [hformg b s, hcg1 b]
    simp [rho]
  apply mem_centralizer_of_trivial_action h.generic.quasisimple.1 hgN
  intro j
  have h1 := conjAut_apply ι hgN j
  rw [hΨg1, MulAut.one_apply] at h1
  exact ι.injective h1.symm

end CFSG.RankThree.PartOne.KFOUT3
