module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.I.theorem_18_3
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
private theorem zpowers_inter_pgroup_eq_one (p : ℕ) [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) {c y : G} (hc : ¬ p ∣ orderOf c) (hy : y ∈ Subgroup.zpowers c)
    (hyP : y ∈ P) : y = 1 := by
  obtain ⟨j, hj⟩ := hP ⟨y, hyP⟩
  have hj' : y ^ p ^ j = 1 := congrArg Subtype.val hj
  have h1 : orderOf y ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj'
  have h2 : orderOf y ∣ orderOf c := orderOf_dvd_of_mem_zpowers hy
  have hpc : Nat.Coprime p (orderOf c) := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hc
  have h3 : Nat.Coprime (orderOf y) (orderOf c) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left j hpc)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2)

theorem B_coprime_quot (p : ℕ) [Fact p.Prime] (Q N : Subgroup G) (a : G) (hQ : IsPGroup p Q)
    (hN : N ≤ Q) (hNn : (N.subgroupOf Q).Normal) (haQ : a ∈ Nor Q) (haN : a ∈ Nor N)
    (ha : ¬ p ∣ orderOf a) :
    ∀ q ∈ Q, (∃ n ∈ N, a * q * a⁻¹ = q * n) → ∃ q' ∈ Q ⊓ Cen a, ∃ n' ∈ N, q = q' * n' := by
  rintro q hq ⟨n₁, hn₁, hqa⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = N ⊔ Subgroup.zpowers a := ⟨_, rfl⟩
  have hNW : N ≤ W := by rw [hW]; exact le_sup_left
  have hzW : Subgroup.zpowers a ≤ W := by rw [hW]; exact le_sup_right
  have haW : a ∈ W := hzW (Subgroup.mem_zpowers a)
  have hbW : n₁ * a ∈ W := W.mul_mem (hNW hn₁) haW
  have hWN : W ≤ Nor N := by
    rw [hW]
    exact sup_le (fun x hx => Subgroup.le_normalizer hx) (Subgroup.zpowers_le.2 haN)
  have hN'n : (N.subgroupOf W).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hWN g.2) n.1).1 hn⟩
  haveI := hN'n
  have hb : q⁻¹ * a * q = n₁ * a := by
    have h := mul_inv_eq_iff_eq_mul.1 hqa
    calc q⁻¹ * a * q = q⁻¹ * (a * q) := by group
      _ = q⁻¹ * (q * n₁ * a) := by rw [h]
      _ = n₁ * a := by group
  have hordb : orderOf (n₁ * a) = orderOf a := by
    rw [← hb]
    have h := orderOf_injective (MulAut.conj q⁻¹).toMonoidHom (MulAut.conj q⁻¹).injective a
    simpa [MulAut.conj_apply, inv_inv] using h
  have hdisj : ∀ c : G, ¬ p ∣ orderOf c →
      Disjoint (N.subgroupOf W) ((Subgroup.zpowers c).subgroupOf W) := by
    intro c hc
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    have h1 : (x : G) = 1 :=
      zpowers_inter_pgroup_eq_one p hQ hc (Subgroup.mem_subgroupOf.1 hx')
        (hN (Subgroup.mem_subgroupOf.1 hx))
    exact Subtype.ext h1
  have htop : ∀ M : Subgroup W, N.subgroupOf W ≤ M → (⟨a, haW⟩ : W) ∈ M → M = ⊤ := by
    intro M hNM haM
    rw [eq_top_iff]
    intro w _
    have hle : N ⊔ Subgroup.zpowers a ≤ M.map W.subtype := by
      refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.2 ?_)
      · have hxN : (⟨x, hNW hx⟩ : W) ∈ N.subgroupOf W := Subgroup.mem_subgroupOf.2 hx
        exact Subgroup.mem_map.2 ⟨⟨x, hNW hx⟩, hNM hxN, rfl⟩
      · exact Subgroup.mem_map.2 ⟨⟨a, haW⟩, haM, rfl⟩
    have hS : (w : G) ∈ M.map W.subtype := hle (hW.le w.2)
    obtain ⟨w', hw', hweq⟩ := Subgroup.mem_map.1 hS
    have : w' = w := Subtype.ext hweq
    rw [← this]
    exact hw'
  have hcomp : ∀ c : G, c ∈ W → ¬ p ∣ orderOf c →
      (⟨a, haW⟩ : W) ∈ N.subgroupOf W ⊔ (Subgroup.zpowers c).subgroupOf W →
      (N.subgroupOf W).IsComplement' ((Subgroup.zpowers c).subgroupOf W) := by
    intro c _ hc haM
    have hsup := htop (N.subgroupOf W ⊔ (Subgroup.zpowers c).subgroupOf W) le_sup_left haM
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (hdisj c hc)
    apply Set.eq_univ_of_forall
    intro w
    have hw : w ∈ N.subgroupOf W ⊔ (Subgroup.zpowers c).subgroupOf W := by
      rw [hsup]
      exact Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hw
    exact Set.mem_mul.2 ⟨y, hy, z, hz, hyz⟩
  have haH : (⟨a, haW⟩ : W) ∈ N.subgroupOf W ⊔ (Subgroup.zpowers a).subgroupOf W :=
    Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers a))
  have haK : (⟨a, haW⟩ : W) ∈ N.subgroupOf W ⊔ (Subgroup.zpowers (n₁ * a)).subgroupOf W := by
    have hu : (⟨n₁⁻¹, hNW (N.inv_mem hn₁)⟩ : W) ∈ N.subgroupOf W :=
      Subgroup.mem_subgroupOf.2 (N.inv_mem hn₁)
    have hv : (⟨n₁ * a, hbW⟩ : W) ∈ (Subgroup.zpowers (n₁ * a)).subgroupOf W :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _)
    have huv : (⟨n₁⁻¹, hNW (N.inv_mem hn₁)⟩ : W) * ⟨n₁ * a, hbW⟩ = ⟨a, haW⟩ :=
      Subtype.ext (by show n₁⁻¹ * (n₁ * a) = a; group)
    rw [← huv]
    exact (N.subgroupOf W ⊔ (Subgroup.zpowers (n₁ * a)).subgroupOf W).mul_mem
      (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv)
  have hH := hcomp a haW ha haH
  have hK := hcomp (n₁ * a) hbW (by rw [hordb]; exact ha) haK
  have hNp : IsPGroup p (N.subgroupOf Q) := hQ.to_subgroup _
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hNcard : Nat.card N = p ^ k := by
    rw [← hk]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv).symm
  have hNWcard : Nat.card (N.subgroupOf W) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNW).toEquiv
  have hquot : Nat.card (↥W ⧸ N.subgroupOf W) = orderOf a := by
    have e := hH.symm.QuotientMulEquiv
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzW).toEquiv,
      Nat.card_zpowers]
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf W)) (Nat.card (↥W ⧸ N.subgroupOf W)) := by
    rw [hquot, hNWcard, hNcard]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ha)
  obtain ⟨g, hg⟩ := CFSG.BenderSuzuki.External.huppert_I_18_3_complements_conjugate
    (N.subgroupOf W) ((Subgroup.zpowers a).subgroupOf W)
    ((Subgroup.zpowers (n₁ * a)).subgroupOf W) hcop hH hK
  have hconjK : ∀ h ∈ Subgroup.zpowers a,
      (g : G) * h * (g : G)⁻¹ ∈ Subgroup.zpowers (n₁ * a) := by
    intro h hh
    have hmem : (MulAut.conj g).toMonoidHom ⟨h, hzW hh⟩ ∈
        ((Subgroup.zpowers a).subgroupOf W).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.2 ⟨⟨h, hzW hh⟩, Subgroup.mem_subgroupOf.2 hh, rfl⟩
    rw [← hg] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  have hconjQ : ∀ k ∈ Subgroup.zpowers (n₁ * a), q * k * q⁻¹ ∈ Subgroup.zpowers a := by
    intro k hk
    rw [← hb] at hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    rw [← conj_zpow (a := q) (b := q⁻¹ * a * q)]
    rw [show q * (q⁻¹ * a * q) * q⁻¹ = a by group]
  have hgsup : g ∈ N.subgroupOf W ⊔ (Subgroup.zpowers a).subgroupOf W := by
    rw [htop _ le_sup_left haH]
    exact Subgroup.mem_top g
  obtain ⟨n₀, hn₀, s, hs, hgs⟩ : ∃ n₀ ∈ N, ∃ s ∈ Subgroup.zpowers a, n₀ * s = (g : G) := by
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hgsup
    exact ⟨y, Subgroup.mem_subgroupOf.1 hy, z, Subgroup.mem_subgroupOf.1 hz,
      congrArg Subtype.val hyz⟩
  have hxQ : q * n₀ ∈ Q := Q.mul_mem hq (hN hn₀)
  have hnorm : ∀ h ∈ Subgroup.zpowers a,
      (q * n₀) * h * (q * n₀)⁻¹ ∈ Subgroup.zpowers a := by
    intro h hh
    have hx_eq : q * n₀ = (q * (g : G)) * s⁻¹ := by
      rw [← hgs]
      group
    have hk : (g : G) * (s⁻¹ * h * s) * (g : G)⁻¹ ∈ Subgroup.zpowers (n₁ * a) :=
      hconjK _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hh) hs)
    have hconj_t : (q * (g : G)) * (s⁻¹ * h * s) * (q * (g : G))⁻¹ ∈ Subgroup.zpowers a := by
      have e : (q * (g : G)) * (s⁻¹ * h * s) * (q * (g : G))⁻¹ =
          q * ((g : G) * (s⁻¹ * h * s) * (g : G)⁻¹) * q⁻¹ := by group
      rw [e]
      exact hconjQ _ hk
    have e2 : (q * n₀) * h * (q * n₀)⁻¹ = (q * (g : G)) * (s⁻¹ * h * s) * (q * (g : G))⁻¹ := by
      rw [hx_eq]
      group
    rw [e2]
    exact hconj_t
  have hxa : (q * n₀) * a * (q * n₀)⁻¹ ∈ Subgroup.zpowers a :=
    hnorm a (Subgroup.mem_zpowers a)
  have hcZ : (q * n₀) * a * (q * n₀)⁻¹ * a⁻¹ ∈ Subgroup.zpowers a :=
    Subgroup.mul_mem _ hxa (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
  have hcQ : (q * n₀) * a * (q * n₀)⁻¹ * a⁻¹ ∈ Q := by
    have h1 : a * (q * n₀)⁻¹ * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 haQ _).1 (Q.inv_mem hxQ)
    have e : (q * n₀) * a * (q * n₀)⁻¹ * a⁻¹ = (q * n₀) * (a * (q * n₀)⁻¹ * a⁻¹) := by
      group
    rw [e]
    exact Q.mul_mem hxQ h1
  have hc1 : (q * n₀) * a * (q * n₀)⁻¹ * a⁻¹ = 1 :=
    zpowers_inter_pgroup_eq_one p hQ ha hcZ hcQ
  have hxa' : (q * n₀) * a = a * (q * n₀) := by
    calc (q * n₀) * a = ((q * n₀) * a * (q * n₀)⁻¹ * a⁻¹) * (a * (q * n₀)) := by group
      _ = a * (q * n₀) := by rw [hc1, one_mul]
  refine ⟨q * n₀, Subgroup.mem_inf.2 ⟨hxQ, ?_⟩, n₀⁻¹, N.inv_mem hn₀, by group⟩
  exact Subgroup.mem_centralizer_iff.2
    (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hxa'.symm)


end CFSG.RankThree.PartTwo.Sec21.FF84.S3
