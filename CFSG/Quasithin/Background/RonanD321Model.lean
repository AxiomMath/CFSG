module

public import CFSG.Quasithin.Background.RonanD321ModelCoord
public import CFSG.Quasithin.Background.SmithD321Sym
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open SL2Model
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem exists_fixed_of_trivial (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L)
    (htriv : letI := qAct hB.hD.hyp.Mp_normal;
      ∀ y (hy : y ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W))),
        ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hy.1⟩ : ↥M) • q = q) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)),
      XMod.IsIrr ↥(L.subgroupOf M) J ∧ J ≤ tilde Mp ⊤ (commV L) ∧
      ∀ g : ↥M, (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) → g • J = J := by
  letI := qAct hB.hD.hyp.Mp_normal
  obtain ⟨K, _, _, hK, π, Ψ, hΨ, hrange, hπL, hπs⟩ := exists_coord hB h3
  obtain ⟨hN1, hNU⟩ := normalizer_hyps hB hrange hπL hπs
  have hC : ∀ c : ↥M, (∀ γ, c * π γ = π γ * c) → ∀ X, c • Ψ X = Ψ X := by
    intro c hc X
    have hcL : (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
      refine ⟨c.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      obtain ⟨γ, rfl⟩ := hπs l hl
      exact (congrArg Subtype.val (hc γ)).symm
    exact htriv _ hcL _ (by rw [← hrange]; exact ⟨X, rfl⟩)
  obtain ⟨r, hr, hfix⟩ := exists_fixed_lineSub hK hΨ _ hN1 hNU hC
  refine ⟨lineSub Ψ r, ⟨fun a q hq => ?_, ?_⟩, hrange ▸ lineSub_le_range r,
    fun g hg => hfix g (Subgroup.mem_subgroupOf.2 hg)⟩
  · obtain ⟨γ, hγ⟩ := hπs _ (Subgroup.mem_subgroupOf.1 a.2)
    have e : (a : ↥M) = π γ := Subtype.ext hγ.symm
    show (a : ↥M) • q ∈ _
    rw [e]
    exact smul_mem_lineSub hΨ γ hq
  · refine ⟨bot_lt_iff_ne_bot.2 (lineSub_ne_bot hΨ hr), fun J hJ _ hle => ?_⟩
    exact eq_bot_or_eq_lineSub hΨ (fun γ q hq => hJ ⟨π γ, hπL γ⟩ q hq) hle

theorem exists_pow_eq_one_not_mem (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L)
    (hcent : M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) {p : ℕ} (hp : p.Prime)
    {y : MulAut W} (hyM : y ∈ M) (hyL : ∀ l ∈ L, y * l = l * y) (hyk : ∃ k : ℕ, y ^ (p ^ k) = 1)
    (hyLt : y ∉ conjAutSub t L) :
    ∃ z ∈ M, (∀ l ∈ L, z * l = l * z) ∧ z ^ p = 1 ∧ z ∉ conjAutSub t L := by
  have hB' := hB.swap
  have h3' : D321Three Mp (conjAutSub t L) :=
    d321Three_conjAutSub (hB.hD.hyp.Mp_normal hB.t_mem) h3
  letI := qAct hB'.hD.hyp.Mp_normal
  obtain ⟨K, _, _, hK, π, Ψ, hΨ, hrange, hπL, hπs⟩ := exists_coord hB' h3'
  obtain ⟨hN1, hNU⟩ := normalizer_hyps hB' hrange hπL hπs
  set N := (Subgroup.normalizer
    ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W))).subgroupOf M with hNdef
  obtain ⟨s, hs⟩ := exists_semiHom hK hΨ N hN1 hNU
  have hyNL : y ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · rw [hyL h hh, mul_inv_cancel_right]
      exact hh
    · have e : y * h * y⁻¹ = h := by
        have h1 := hyL _ hh
        calc y * h * y⁻¹ = y⁻¹ * (y * (y * h * y⁻¹)) := by group
          _ = y⁻¹ * ((y * h * y⁻¹) * y) := by rw [h1]
          _ = h := by group
      rw [← e]
      exact hh
  have hyN : (⟨y, hyM⟩ : ↥M) ∈ N := Subgroup.mem_subgroupOf.2
    (mem_normalizer_iff_conjAutSub.2 (hB.conj_Lt_of_mem_normalizer hyM hyNL))
  obtain ⟨σ, A, B, -, hact, hconj⟩ := exists_form hK hΨ (hN1 _ hyN)
    (exists_conj_eq_of_inv (hN1 _ (N.inv_mem hyN))) (hNU _ hyN)
  have hσ : s ⟨_, hyN⟩ = σ := (hs _).unique hΨ.1 hact.isSemi
  set y' : ↥M := (π A)⁻¹ * ⟨y, hyM⟩ with hy'
  have hy'conj : ∀ γ, y' * π γ * y'⁻¹ = π (slMap σ γ) := by
    intro γ
    have h1 := hconj γ
    calc y' * π γ * y'⁻¹ = (π A)⁻¹ * (⟨y, hyM⟩ * π γ * (⟨y, hyM⟩ : ↥M)⁻¹) * π A := by
          rw [hy']
          group
      _ = π (slMap σ γ) := by
          rw [h1]
          group
  have hy'pow : ∀ (k : ℕ) γ, y' ^ k * π γ * (y' ^ k)⁻¹ = π (slMap (σ ^ k) γ) := by
    intro k
    induction k with
    | zero =>
      intro γ
      rw [pow_zero, pow_zero, slMap_one]
      group
    | succ k ih =>
      intro γ
      rw [pow_succ', pow_succ', slMap_mul, ← hy'conj, ← ih]
      group
  have hy'L : ∀ l ∈ L, ((y' : ↥M) : MulAut W) * l = l * (y' : MulAut W) := by
    intro l hl
    have h1 : ((π A : ↥M) : MulAut W)⁻¹ * l = l * ((π A : ↥M) : MulAut W)⁻¹ :=
      (hB.comm l hl _ ((conjAutSub t L).inv_mem (hπL A))).symm
    show ((π A : ↥M) : MulAut W)⁻¹ * y * l = l * (((π A : ↥M) : MulAut W)⁻¹ * y)
    rw [mul_assoc, hyL l hl, ← mul_assoc, h1, mul_assoc]
  have hpowL : ∀ k : ℕ, ∀ l ∈ L,
      ((y' ^ k : ↥M) : MulAut W) * l = l * ((y' ^ k : ↥M) : MulAut W) := by
    intro k l hl
    rw [Subgroup.coe_pow]
    exact Commute.pow_left (hy'L l hl) k
  have hone : ∀ k : ℕ, σ ^ k = 1 → y' ^ k = 1 := by
    intro k hk
    have hc : ((y' ^ k : ↥M) : MulAut W) ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) := by
      refine ⟨(y' ^ k).2, Subgroup.mem_centralizer_iff.2 fun m hm => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hB.exists_mul_of_mem_Mp hm
      obtain ⟨γ, rfl⟩ := hπs b hb
      have hγ : y' ^ k * π γ = π γ * y' ^ k := by
        have h1 := hy'pow k γ
        rw [hk, slMap_one] at h1
        calc y' ^ k * π γ = (y' ^ k * π γ * (y' ^ k)⁻¹) * y' ^ k := by group
          _ = π γ * y' ^ k := by rw [h1]
      have hγ' := congrArg Subtype.val hγ
      simp only [Subgroup.coe_mul] at hγ'
      rw [mul_assoc, ← hγ', ← mul_assoc, ← hpowL k a ha, mul_assoc]
    rw [hcent, Subgroup.mem_bot] at hc
    exact Subtype.ext hc
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 := hone 1 (by rw [pow_one, h1])
    rw [pow_one, hy', inv_mul_eq_one] at h2
    have h3 : ((π A : ↥M) : MulAut W) = y := congrArg Subtype.val h2
    exact hyLt (h3 ▸ hπL A)
  obtain ⟨k₀, hk₀⟩ := hyk
  have hσk : σ ^ (p ^ k₀) = 1 := by
    have h1 : (⟨⟨y, hyM⟩, hyN⟩ : ↥N) ^ (p ^ k₀) = 1 :=
      Subtype.ext (Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact hk₀))
    rw [← hσ, ← map_pow, h1, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hσk)
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by
    rcases j with _ | j'
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hσ1 hj
    · exact ⟨j', rfl⟩
  refine ⟨((y' ^ (p ^ j) : ↥M) : MulAut W), (y' ^ (p ^ j)).2, hpowL _, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← pow_mul, ← pow_succ, ← hj, hone _ (pow_orderOf_eq_one σ),
      Subgroup.coe_one]
  ·
    intro hz
    obtain ⟨δ, hδ⟩ := hπs _ hz
    have hδ' : π δ = y' ^ (p ^ j) := Subtype.ext hδ
    have hτ : σ ^ (p ^ j) = 1 := by
      refine eq_one_of_conj (σ ^ (p ^ j)) (δ : GL (Fin 2) K).isUnit fun γ => ?_
      have h1 := hy'pow (p ^ j) γ
      rw [← hδ', ← map_inv, ← map_mul, ← map_mul] at h1
      have h2 := hΨ.injective_π h1
      rw [← slm_slMap, ← h2]
      simp only [slm, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
      rw [mul_assoc, mul_assoc]
      simp
    have h4 := orderOf_dvd_of_pow_eq_one hτ
    rw [hj, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h4
    omega

end CFSG.Quasithin.RonanD321
