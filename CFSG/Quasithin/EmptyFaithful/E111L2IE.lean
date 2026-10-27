module

public import CFSG.Quasithin.EmptyFaithful.E111L2ID

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

variable {G : Type} [Group G]

structure S4Data (D T R L₀ P V' : Subgroup G) : Prop where
  L_le : L₀ ≤ D
  P_le : P ≤ L₀
  V_le : V' ≤ P
  V_T : V' ≤ T
  pow3 : ∀ x ∈ P, x ^ 3 ∈ V'
  P_norm : L₀ ≤ Subgroup.normalizer (P : Set G)
  V_norm : L₀ ≤ Subgroup.normalizer (V' : Set G)
  L_sup : L₀ ≤ P ⊔ (T ⊓ L₀)
  inv : ∀ k ∈ R, A1b.conjSub k D = D →
    A1b.conjSub k L₀ = L₀ ∧ A1b.conjSub k P = P ∧ A1b.conjSub k V' = V'

theorem sSup_le_T {T A Z : Subgroup G} (hZ : Z ≤ T) :
    sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) Z) ≤ T := by
  refine sSup_le fun Z' hZ' => ?_
  obtain ⟨k, rfl⟩ := hZ'
  exact (A1b.conjSub_mono _ hZ).trans
    (conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer k.2.1)).le

section Diag

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C]
include h

theorem pow_mem_sSup [Finite G] {Z W : Subgroup G} (hZ : Z ≤ diagSub S C h.diagComm)
    (hinv : ∀ k ∈ T ⊓ Subgroup.centralizer (A : Set G),
      A1b.conjSub k (diagSub S C h.diagComm) = diagSub S C h.diagComm → A1b.conjSub k Z = Z)
    {n : ℕ} (hZW : ∀ x ∈ Z, x ^ n ∈ W) :
    ∀ y ∈ sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) Z),
      y ^ n ∈ sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) W) := by
  classical
  intro y hy
  set 𝒵 := conjFam (T ⊓ Subgroup.centralizer (A : Set G)) Z with h𝒵
  let _ : Fintype ↥𝒵 := Fintype.ofFinite _
  have hcomm : Pairwise fun i j : ↥𝒵 =>
      ∀ x y : G, x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) → Commute x y := by
    rintro ⟨_, ⟨k, rfl⟩⟩ ⟨_, ⟨k', rfl⟩⟩ hij x y hx hy
    exact conj_commute_of_ne h hZ hinv k.2 k'.2 (fun heq => hij (Subtype.ext heq)) x hx y hy
  have hr := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
  rw [← sSup_eq_iSup'] at hr
  rw [← hr] at hy
  obtain ⟨f, rfl⟩ := hy
  rw [← map_pow, Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  obtain ⟨k, hk⟩ := i.2
  have hfi : ((f i : ↥(i : Subgroup G)) : G) ∈ A1b.conjSub (k : G) Z := by
    rw [show A1b.conjSub (k : G) Z = (i : Subgroup G) from hk]
    exact (f i).2
  rw [A1b.mem_conjSub_iff] at hfi
  have h1 := hZW _ hfi
  have h2 : ((f ^ n) i : G) = (k : G) * ((k : G)⁻¹ * f i * k) ^ n * (k : G)⁻¹ := by
    have e := map_pow (MulAut.conj ((k : G)⁻¹)) (f i : G) n
    simp only [MulAut.conj_apply, inv_inv] at e
    rw [Pi.pow_apply, Subgroup.coe_pow, ← e]
    group
  rw [h2]
  exact le_sSup (conj_mem_conjFam k.2) (A1b.mem_conjSub_of_mem h1)

variable [Finite G] {L₀ P V' : Subgroup G}
  (hd : S4Data (diagSub S C h.diagComm) T (T ⊓ Subgroup.centralizer (A : Set G)) L₀ P V')
include hd

omit [Finite G] in
theorem S4Data.P_le_D : P ≤ diagSub S C h.diagComm := hd.P_le.trans hd.L_le

omit [Finite G] in
theorem S4Data.V_le_D : V' ≤ diagSub S C h.diagComm := hd.V_le.trans (S4Data.P_le_D h hd)

theorem pow_three_mem :
    ∀ y ∈ sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) P),
      y ^ 3 ∈ sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) V') :=
  pow_mem_sSup h (S4Data.P_le_D h hd) (fun k hk hD => (hd.inv k hk hD).2.1) hd.pow3

omit [Finite G] in
theorem inv_inf {k : G} (hk : k ∈ T ⊓ Subgroup.centralizer (A : Set G))
    (hD : A1b.conjSub k (diagSub S C h.diagComm) = diagSub S C h.diagComm) :
    A1b.conjSub k (T ⊓ L₀) = T ⊓ L₀ := by
  rw [← inf_conjSub_of_eq (conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hk.1)),
    (hd.inv k hk hD).1]

omit [Finite G] in
theorem K_eq :
    sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
        (T ⊓ Subgroup.centralizer (A : Set G)) =
      sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) P) ⊔
        (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) (T ⊓ L₀)) ⊔
          (T ⊓ Subgroup.centralizer (A : Set G))) := by
  set R := T ⊓ Subgroup.centralizer (A : Set G) with hR
  apply le_antisymm
  · refine sup_le (sSup_le fun Z hZ => ?_) (le_sup_right.trans le_sup_right)
    obtain ⟨k, rfl⟩ := hZ
    calc A1b.conjSub (k : G) L₀ ≤ A1b.conjSub (k : G) (P ⊔ (T ⊓ L₀)) :=
          A1b.conjSub_mono _ hd.L_sup
      _ = A1b.conjSub (k : G) P ⊔ A1b.conjSub (k : G) (T ⊓ L₀) := by
          unfold A1b.conjSub
          exact Subgroup.map_sup _ _ _
      _ ≤ _ := sup_le_sup (le_sSup (conj_mem_conjFam k.2))
          (le_sup_left.trans' (le_sSup (conj_mem_conjFam k.2)))
  · refine sup_le ((sSup_le fun Z hZ => ?_).trans le_sup_left)
      (sup_le ((sSup_le fun Z hZ => ?_).trans le_sup_left) le_sup_right)
    · obtain ⟨k, rfl⟩ := hZ
      exact (A1b.conjSub_mono _ hd.P_le).trans (le_sSup (conj_mem_conjFam k.2))
    · obtain ⟨k, rfl⟩ := hZ
      exact (A1b.conjSub_mono _ inf_le_right).trans (le_sSup (conj_mem_conjFam k.2))

theorem isSylowIn_K :
    IsSylowIn 2 (T ⊓ (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
        (T ⊓ Subgroup.centralizer (A : Set G))))
      (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
        (T ⊓ Subgroup.centralizer (A : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := T ⊓ Subgroup.centralizer (A : Set G) with hR
  set P₄ := sSup (conjFam R P) with hP₄
  set M := sSup (conjFam R V') with hM
  have hT2 : IsPGroup 2 T := h.isPGroup_T
  have hMP : M ≤ P₄ := sSup_le fun Z hZ => by
    obtain ⟨k, rfl⟩ := hZ
    exact (A1b.conjSub_mono _ hd.V_le).trans (le_sSup (conj_mem_conjFam k.2))
  have hMT : M ≤ T := sSup_le_T hd.V_T
  have hPN : P₄ ≤ Subgroup.normalizer (M : Set G) :=
    sSup_le_normalizer h (S4Data.P_le_D h hd) (S4Data.V_le_D h hd)
      (fun k hk hD => (hd.inv k hk hD).2.1) (hd.P_le.trans hd.V_norm)
  have hMn : (M.subgroupOf P₄).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMP).mpr hPN
  have h3 : IsPGroup 3 (↥P₄ ⧸ M.subgroupOf P₄) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact pow_three_mem h hd y y.2
  obtain ⟨j, hj⟩ := h3.exists_card_eq
  have hrel : M.relIndex P₄ = 3 ^ j := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hj]
  have hodd : ¬ 2 ∣ (T ⊓ P₄).relIndex P₄ := by
    intro h2
    have h4 := h2.trans (Subgroup.relIndex_dvd_of_le_left P₄ (le_inf hMT hMP))
    rw [hrel] at h4
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h4) (by norm_num)
  have hSP : IsSylowIn 2 (T ⊓ P₄) P₄ := ⟨inf_le_right, hT2.to_le inf_le_left, hodd⟩
  have hT₀T : sSup (conjFam R (T ⊓ L₀)) ⊔ R ≤ T := sup_le (sSup_le_T inf_le_left) inf_le_left
  have hT₀N : sSup (conjFam R (T ⊓ L₀)) ⊔ R ≤ Subgroup.normalizer (P₄ : Set G) :=
    sup_le (sSup_le_normalizer h (inf_le_right.trans hd.L_le) (S4Data.P_le_D h hd)
      (fun k hk hD => inv_inf h hd hk hD) (inf_le_right.trans hd.P_norm))
      (le_normalizer_conjFam R P)
  have := isSylowIn_inf_sup hT2 hT₀T hT₀N hSP
  rwa [← K_eq h hd] at this

theorem pow_two_mem_P₄ {s : G}
    (hs : s ∈ sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
      (T ⊓ Subgroup.centralizer (A : Set G))) :
    ∃ m : ℕ, s ^ 2 ^ m ∈ sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) P) := by
  set R := T ⊓ Subgroup.centralizer (A : Set G) with hR
  set P₄ := sSup (conjFam R P) with hP₄
  set T₀ := sSup (conjFam R (T ⊓ L₀)) ⊔ R with hT₀
  rw [K_eq h hd] at hs
  have hT₀N : T₀ ≤ Subgroup.normalizer (P₄ : Set G) :=
    sup_le (sSup_le_normalizer h (inf_le_right.trans hd.L_le) (S4Data.P_le_D h hd)
      (fun k hk hD => inv_inf h hd hk hD) (inf_le_right.trans hd.P_norm))
      (le_normalizer_conjFam R P)
  have hT₀2 : IsPGroup 2 ↥T₀ :=
    h.isPGroup_T.to_le (sup_le (sSup_le_T inf_le_left) inf_le_left)
  have hn : (P₄.subgroupOf (P₄ ⊔ T₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT₀N)
  have htop : P₄.subgroupOf (P₄ ⊔ T₀) ⊔ T₀.subgroupOf (P₄ ⊔ T₀) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  obtain ⟨m, hm⟩ := pow_mem_of_sup hn htop
    (hT₀2.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm) ⟨s, hs⟩
  exact ⟨m, by simpa using Subgroup.mem_subgroupOf.mp hm⟩

end Diag

end CFSG.Quasithin.E2.E22N.E111L.KMI
