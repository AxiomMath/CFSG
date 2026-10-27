module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth72_mul_mem {R Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 R Q)
    (hQM : M ≤ Subgroup.normalizer (Q : Set G)) (hZM : Z0 ≤ M) {ν μ x : G} (hν : ν ∈ R)
    (hμ : ⁅μ, x⁆ ∈ Z0) (ha : ⁅ν, x⁆ ∈ Z0) :
    (⁅ν * μ, x⁆)⁻¹ * (⁅ν, x⁆ * ⁅μ, x⁆) ∈ Q := by
  have hp : ⁅ν, ⁅μ, x⁆⁆ ∈ Q := by
    have e : ⁅ν, ⁅μ, x⁆⁆ = ⁅⁅μ, x⁆, ν⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.inv_mem (hZ0.comm_mem hμ hν)
  have hm : (⁅μ, x⁆ * ⁅ν, x⁆)⁻¹ ∈ M := M.inv_mem (M.mul_mem (hZM hμ) (hZM ha))
  have hconj : (⁅μ, x⁆ * ⁅ν, x⁆)⁻¹ * ⁅ν, ⁅μ, x⁆⁆⁻¹ * (⁅μ, x⁆ * ⁅ν, x⁆)⁻¹⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQM hm) _).mp (Q.inv_mem hp)
  have hcomm : ⁅⁅ν, x⁆⁻¹, ⁅μ, x⁆⁻¹⁆ ∈ Q :=
    hZ0.comm_mem (Z0.inv_mem ha) (hZ0.le (Z0.inv_mem hμ))
  have e : (⁅ν * μ, x⁆)⁻¹ * (⁅ν, x⁆ * ⁅μ, x⁆) =
      ((⁅μ, x⁆ * ⁅ν, x⁆)⁻¹ * ⁅ν, ⁅μ, x⁆⁆⁻¹ * (⁅μ, x⁆ * ⁅ν, x⁆)⁻¹⁻¹) *
        ⁅⁅ν, x⁆⁻¹, ⁅μ, x⁆⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Q.mul_mem hconj hcomm

theorem stroth72_conj_mem {R Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 R Q)
    (hQM : M ≤ Subgroup.normalizer (Q : Set G)) (hZM : Z0 ≤ M) {ν x z : G} (hxR : x ∈ R)
    (hz : z ∈ Z0) (h : ⁅ν, x⁆⁻¹ * z ∈ Q) : ν * x * ν⁻¹ * (x * z)⁻¹ ∈ Q := by
  have hb : ⁅x, z⁻¹⁆ ∈ Q := by
    have e : ⁅x, z⁻¹⁆ = (⁅z⁻¹, x⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.inv_mem (hZ0.comm_mem (Z0.inv_mem hz) hxR)
  have e : ν * x * ν⁻¹ * (x * z)⁻¹ = z * ((⁅ν, x⁆⁻¹ * z)⁻¹ * ⁅x, z⁻¹⁆) * z⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hQM (hZM hz)) _).mp (Q.mul_mem (Q.inv_mem h) hb)

theorem stroth72_conj_mem_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hno : ¬ Conc71abcd hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g : G} (hg : g ∈ M) (hgL : g * t * g⁻¹ ∈ LB M Q B) : g * t * g⁻¹ ∈ hc.CN t := by
  by_contra hN
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hA : Conc71a hc t := by
    unfold Conc71a
    refine ⟨t, le_Rt (M := M) (LB M Q B) ht ht, fun r hr => ?_, g, hg, hgL, hN⟩
    exact hZ0.comm_mem (IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0) hr
  exact hno (Or.inl hA)

theorem stroth72_of_index (hNN : Sec7CommNStatement) (hZc : Sec7ZCardStatement)
    (hI : Step72IndexStatement) : Stroth72Statement := by
  unfold Stroth72Statement
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0 x hxL hx hxZ z hz
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hZM : Z0 ≤ M := hc.centre_le_M t hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.mp hy).1
  have hNM : hc.CN t ≤ M := fun y hy => hc.Rt_le_M t (hNR hy)
  have hQN : Q ≤ hc.CN t := fun y hy => Ctx.mem_CN.mpr
    ⟨hc.Q_le_Rt ht hy, fun v hv => hc.hyp.toHyp79.comm_mem_V hy (hc.Vt_le_Q t hv)⟩
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hxN : x ∈ hc.CN t := by
    unfold ConjMod at hx
    obtain ⟨-, g, hg, hQg⟩ := hx
    have hyL : g * t * g⁻¹ ∈ LB M Q B := by
      have h1 := (LB M Q B).mul_mem ((LB M Q B).inv_mem
        ((sec39_Q_le_LB (M := M) (Q := Q) (B := B)) hQg)) hxL
      rwa [show (x * (g * t * g⁻¹)⁻¹)⁻¹ * x = g * t * g⁻¹ by group] at h1
    have h2 : (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) ∈ hc.CN t :=
      (hc.CN t).mul_mem (hQN hQg) (stroth72_conj_mem_CN hc hs hno hZ0 hg hyL)
    rwa [show (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) = x by group] at h2
  have hcomm_mem : ∀ ν ∈ hc.CN t, ⁅ν, x⁆ ∈ Z0 := fun ν hν =>
    hNN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hν hxN)
  haveI hQ0 : (Q.subgroupOf Z0).Normal := ⟨fun n' hn' g => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hQM (hZM g.2)) (n' : G)).mp hn'⟩
  have hidx : (Q.subgroupOf Z0).index = Nat.card Z := by
    have h1 := Subgroup.card_mul_index (Q.subgroupOf Z0)
    have h2 : Nat.card ↥(Q.subgroupOf Z0) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQZ0).toEquiv
    rw [h2, hZc G M Q Z B hc n t hs Z0 hZ0] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Q)) h1
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = hc.CN t ⊓ CommQ hc.hyp.Q_normal.2 x := ⟨_, rfl⟩
  have hKN : K ≤ hc.CN t := by
    rw [hK]
    exact inf_le_left
  have hKmem : ∀ y : G, y ∈ K ↔ y ∈ hc.CN t ∧ y ∈ M ∧ ⁅y, x⁆ ∈ Q := by
    intro y
    rw [hK, Subgroup.mem_inf, mem_CommQ]
  have hIk : Nat.card Z * Nat.card ↥K ≤ Nat.card ↥(hc.CN t) := by
    rw [hK]
    exact hI G M Q Z B hc n t hs hno Z0 hZ0 x hxL hx hxZ
  obtain ⟨f, hf⟩ : ∃ f : ↥(hc.CN t) →* ↥Z0 ⧸ (Q.subgroupOf Z0), ∀ ν : ↥(hc.CN t),
      f ν = QuotientGroup.mk (⟨⁅(ν : G), x⁆, hcomm_mem (ν : G) ν.2⟩ : ↥Z0) := by
    refine ⟨MonoidHom.mk' (fun ν => QuotientGroup.mk
      (⟨⁅(ν : G), x⁆, hcomm_mem (ν : G) ν.2⟩ : ↥Z0)) ?_, fun ν => rfl⟩
    intro a b
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact stroth72_mul_mem hZ0 hQM hZM (hNR a.2) (hcomm_mem (b : G) b.2) (hcomm_mem (a : G) a.2)
  have hfker : ∀ ν : ↥(hc.CN t), ν ∈ f.ker ↔ ⁅(ν : G), x⁆ ∈ Q := by
    intro ν
    rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hker : f.ker = K.subgroupOf (hc.CN t) := by
    ext ν
    rw [hfker ν, Subgroup.mem_subgroupOf]
    exact ⟨fun h => (hKmem _).mpr ⟨ν.2, hNM ν.2, h⟩, fun h => ((hKmem _).mp h).2.2⟩
  have hcardK : Nat.card ↥f.ker = Nat.card ↥K := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  have hdiv : Nat.card ↥K * Nat.card ↥f.range = Nat.card ↥(hc.CN t) := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hcardK] at h1
    exact h1
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have hle1 : Nat.card Z ≤ Nat.card ↥f.range := by
    have h3 : Nat.card ↥K * Nat.card Z ≤ Nat.card ↥K * Nat.card ↥f.range := by
      rw [hdiv, Nat.mul_comm]
      exact hIk
    exact Nat.le_of_mul_le_mul_left h3 hpos
  have hcardQ : Nat.card (↥Z0 ⧸ (Q.subgroupOf Z0)) = Nat.card Z := hidx
  have hle2 : Nat.card ↥f.range ≤ Nat.card Z := by
    have h4 := Subgroup.card_le_card_group f.range
    rw [hcardQ] at h4
    exact h4
  have hrange : f.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcardQ]
    exact le_antisymm hle2 hle1
  have hw : (QuotientGroup.mk (⟨z, hz⟩ : ↥Z0) : ↥Z0 ⧸ (Q.subgroupOf Z0)) ∈ f.range := by
    rw [hrange]
    exact Subgroup.mem_top _
  obtain ⟨ν, hν⟩ := MonoidHom.mem_range.mp hw
  rw [hf] at hν
  have h1 : ⁅(ν : G), x⁆⁻¹ * z ∈ Q := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hν)
  exact ⟨(ν : G), ν.2, stroth72_conj_mem hZ0 hQM hZM hxR hz h1⟩

end CFSG.RankThree.GF2n.Stroth80
