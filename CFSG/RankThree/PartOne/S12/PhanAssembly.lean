module

public import CFSG.RankThree.PartOne.S12.WeylIso
public import CFSG.RankThree.PartOne.S12.ReflectionTorus
public import CFSG.RankThree.PartOne.S12.KFTransfer
import CFSG.RankThree.PartOne.S12.Sec1212Aut
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isKt_iff_of_nonexceptional {p : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G}
    (h : ¬ ∃ f' : ℕ, kExceptional p (kZero p E t) f') : IsKt p E t K ↔ K = kZero p E t := by
  unfold IsKt
  constructor
  · rintro ⟨-, h2⟩
    exact h2 h
  · intro hK
    refine ⟨fun f' hf' => absurd ⟨f', hf'⟩ h, fun _ => hK⟩

namespace PhanAssembly

section Swaps

variable {X : Type} [DecidableEq X]

theorem swap_braid {a b c : X} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  have h1 : Equiv.swap a b * Equiv.swap b c * Equiv.swap a b = Equiv.swap a c := by
    have h := Equiv.swap_apply_apply (Equiv.swap a b) b c
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
      Equiv.swap_inv] at h
    exact h.symm
  have h2 : Equiv.swap b c * Equiv.swap a b * Equiv.swap b c = Equiv.swap a c := by
    have h := Equiv.swap_apply_apply (Equiv.swap b c) a b
    rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left, Equiv.swap_inv] at h
    exact h.symm
  rw [h1, h2]

theorem swap_mul_swap_pow_three {a b c : X} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Equiv.swap a b * Equiv.swap b c) ^ 3 = 1 := by
  have hs := Equiv.swap_mul_self a b
  have ht := Equiv.swap_mul_self b c
  have hb := swap_braid hab hbc hac
  set s := Equiv.swap a b
  set t := Equiv.swap b c
  calc (s * t) ^ 3 = (s * t * s) * (t * s * t) := by rw [pow_succ, pow_succ, pow_one]; group
    _ = (t * s * t) * (t * s * t) := by rw [hb]
    _ = t * s * (t * t) * s * t := by group
    _ = t * (s * s) * t := by rw [ht]; group
    _ = 1 := by rw [hs, mul_one, ht]

theorem orderOf_swap_mul_swap_three {a b c : X} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    orderOf (Equiv.swap a b * Equiv.swap b c) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (swap_mul_swap_pow_three hab hbc hac) ?_
  intro h
  have h1 : Equiv.swap a b = Equiv.swap b c := by
    have h' := mul_eq_one_iff_eq_inv.1 h
    rwa [Equiv.swap_inv] at h'
  have h2 := congrArg (fun σ => σ a) h1
  simp only [Equiv.swap_apply_left] at h2
  rw [Equiv.swap_apply_of_ne_of_ne hab hac] at h2
  exact hab h2.symm

theorem swap_mul_swap_comm {a b c d : X} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  have h := Equiv.swap_apply_apply (Equiv.swap a b) c d
  rw [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
    Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm, Equiv.swap_inv] at h
  have hs := Equiv.swap_mul_self a b
  set s := Equiv.swap a b
  set t := Equiv.swap c d
  calc s * t = s * t * (s * s) := by rw [hs, mul_one]
    _ = (s * t * s) * s := by group
    _ = t * s := by rw [← h]

end Swaps

theorem chain_swap_facts (n : ℕ) :
    (∀ i j : Fin n, i ≠ j → (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) ≠
      Equiv.swap j.castSucc j.succ) ∧
    (∀ i j : Fin n, (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i → i ≠ j →
      (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) * Equiv.swap j.castSucc j.succ =
        Equiv.swap j.castSucc j.succ * Equiv.swap i.castSucc i.succ) ∧
    (∀ i j : Fin n, ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) →
      orderOf ((Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) *
        Equiv.swap j.castSucc j.succ) = 3) ∧
    (∀ i j : Fin n, ((Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) *
        Equiv.swap j.castSucc j.succ) ^ 6 = 1) := by
  have h1 : ∀ i j : Fin n, i ≠ j → (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) ≠
      Equiv.swap j.castSucc j.succ := by
    intro i j hij h
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    have h1 := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ i.castSucc) h
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_def] at h1
    split_ifs at h1 with h2 h3
    · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
    · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at h1 h2 h3
      omega
    · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at h1 h2 h3
      omega
  have h2 : ∀ i j : Fin n, (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i → i ≠ j →
      (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) * Equiv.swap j.castSucc j.succ =
        Equiv.swap j.castSucc j.succ * Equiv.swap i.castSucc i.succ := by
    intro i j hi hj hij
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    refine swap_mul_swap_comm ?_ ?_ ?_ ?_ <;>
      simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] <;> omega
  have h3 : ∀ i j : Fin n, ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) →
      orderOf ((Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) *
        Equiv.swap j.castSucc j.succ) = 3 := by
    intro i j hadj
    rcases hadj with h | h
    · have hbc : i.succ = j.castSucc := Fin.ext (by simp [h])
      rw [← hbc]
      refine orderOf_swap_mul_swap_three ?_ ?_ ?_ <;>
        simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] <;> omega
    · have hbc : j.succ = i.castSucc := Fin.ext (by simp [h])
      rw [← hbc, Equiv.swap_comm j.succ i.succ, Equiv.swap_comm j.castSucc j.succ]
      refine orderOf_swap_mul_swap_three ?_ ?_ ?_ <;>
        simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] <;> omega
  refine ⟨h1, h2, h3, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Equiv.swap_mul_self, one_pow]
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · have h6 : (Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ :
        Equiv.Perm (Fin (n + 1))) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ :
        Equiv.Perm (Fin (n + 1)))
      rwa [h3 i j hadj] at this
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h6, one_pow]
  · push Not at hadj
    have hc := h2 i j hadj.1 hadj.2 hij
    rw [Commute.mul_pow hc 6]
    have hs : ∀ k : Fin n, (Equiv.swap k.castSucc k.succ : Equiv.Perm (Fin (n + 1))) ^ 6 = 1 := by
      intro k
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_two, Equiv.swap_mul_self, one_pow]
    rw [hs i, hs j, one_mul]

variable {p n : ℕ} {E L : Subgroup G} (W : WeylIso p n E L)

omit [Finite G] in
theorem exists_chain : ∃ tt : Fin n → MulAut E, ∀ i, ∃ ht : tt i ∈ reflectionSet p E,
    W.ψ ⟨tt i, Subgroup.subset_closure ht⟩ = Equiv.swap i.castSucc i.succ := by
  have hsw : ∀ i : Fin n, (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))).IsSwap :=
    fun i => ⟨i.castSucc, i.succ, (Fin.castSucc_lt_succ).ne, rfl⟩
  choose tt htt using fun i : Fin n => W.surj _ (hsw i)
  exact ⟨tt, fun i => htt i⟩

omit [Finite G] in
theorem psi_mul {s t : MulAut E} (hs : s ∈ reflectionSet p E) (ht : t ∈ reflectionSet p E) :
    W.ψ ⟨s * t, mul_mem (Subgroup.subset_closure hs) (Subgroup.subset_closure ht)⟩ =
      W.ψ ⟨s, Subgroup.subset_closure hs⟩ * W.ψ ⟨t, Subgroup.subset_closure ht⟩ := by
  have : (⟨s * t, mul_mem (Subgroup.subset_closure hs) (Subgroup.subset_closure ht)⟩ :
      ↥(Subgroup.closure (reflectionSet p E))) =
      ⟨s, Subgroup.subset_closure hs⟩ * ⟨t, Subgroup.subset_closure ht⟩ := rfl
  rw [this, map_mul]

omit [Finite G] in
theorem orderOf_mul_eq {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (ht : t ∈ reflectionSet p E) :
    orderOf (s * t) = orderOf (W.ψ ⟨s, Subgroup.subset_closure hs⟩ *
      W.ψ ⟨t, Subgroup.subset_closure ht⟩) := by
  rw [← psi_mul W hs ht, MulEquiv.orderOf_eq,
    ← Subgroup.orderOf_coe (⟨s * t, _⟩ : ↥(Subgroup.closure (reflectionSet p E)))]

omit [Finite G] in
theorem mul_comm_of_swap {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (ht : t ∈ reflectionSet p E)
    (h : W.ψ ⟨s, Subgroup.subset_closure hs⟩ * W.ψ ⟨t, Subgroup.subset_closure ht⟩ =
      W.ψ ⟨t, Subgroup.subset_closure ht⟩ * W.ψ ⟨s, Subgroup.subset_closure hs⟩) :
    s * t = t * s := by
  have h1 := psi_mul W hs ht
  have h2 := psi_mul W ht hs
  have : W.ψ ⟨s * t, mul_mem (Subgroup.subset_closure hs) (Subgroup.subset_closure ht)⟩ =
      W.ψ ⟨t * s, mul_mem (Subgroup.subset_closure ht) (Subgroup.subset_closure hs)⟩ := by
    rw [h1, h2, h]
  have := congrArg Subtype.val (W.ψ.injective this)
  exact this

omit [Finite G] in
theorem pow_six_eq_one {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (ht : t ∈ reflectionSet p E)
    (h : (W.ψ ⟨s, Subgroup.subset_closure hs⟩ * W.ψ ⟨t, Subgroup.subset_closure ht⟩) ^ 6 = 1) :
    (s * t) ^ 6 = 1 := by
  have h1 : W.ψ (⟨s * t, mul_mem (Subgroup.subset_closure hs) (Subgroup.subset_closure ht)⟩ ^ 6) =
      W.ψ 1 := by
    rw [map_pow, psi_mul W hs ht, h, map_one]
  have h2 := congrArg Subtype.val (W.ψ.injective h1)
  simpa using h2

omit [Finite G] in
theorem closure_le_closure_range {tt : Fin n → MulAut E}
    (htt : ∀ i, ∃ ht : tt i ∈ reflectionSet p E,
      W.ψ ⟨tt i, Subgroup.subset_closure ht⟩ = Equiv.swap i.castSucc i.succ) :
    Subgroup.closure (reflectionSet p E) ≤ Subgroup.closure (Set.range tt) := by
  set S : Subgroup (MulAut E) := Subgroup.closure (Set.range tt) with hS
  set S' : Subgroup ↥(Subgroup.closure (reflectionSet p E)) :=
    S.subgroupOf (Subgroup.closure (reflectionSet p E)) with hS'
  have hmap : S'.map W.ψ.toMonoidHom = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n =>
        (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1)))) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    refine (Submonoid.closure_le (S := (S'.map W.ψ.toMonoidHom).toSubmonoid)).2 ?_ hσ
    rintro _ ⟨i, rfl⟩
    obtain ⟨ht, hψ⟩ := htt i
    refine ⟨⟨tt i, Subgroup.subset_closure ht⟩, ?_, hψ⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨i, rfl⟩)
  intro x hx
  have hmem : W.ψ ⟨x, hx⟩ ∈ S'.map W.ψ.toMonoidHom := by
    rw [hmap]
    trivial
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hmem
  have hyx' : y = ⟨x, hx⟩ := W.ψ.injective hyx
  rw [hyx'] at hy
  exact Subgroup.mem_subgroupOf.1 hy

@[expose] def inducedBy (E I₀ : Subgroup G) : Subgroup (MulAut E) where
  carrier := {g | ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), w ∈ I₀ ∧
    conjAut E w hw = g}
  one_mem' := ⟨1, one_mem _, one_mem _, map_one _⟩
  mul_mem' := by
    rintro _ _ ⟨w₁, hw₁, hI₁, rfl⟩ ⟨w₂, hw₂, hI₂, rfl⟩
    exact ⟨w₁ * w₂, mul_mem hw₁ hw₂, mul_mem hI₁ hI₂,
      map_mul E.normalizerMonoidHom ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩⟩
  inv_mem' := by
    rintro _ ⟨w, hw, hI, rfl⟩
    exact ⟨w⁻¹, inv_mem hw, inv_mem hI, Equivariance.conjAut_inv hw⟩

omit [Finite G] in
include W in
theorem kZero_le_iSup {f : ℕ} (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t) (hn : 0 < n)
    {tt : Fin n → MulAut E}
    (htt : ∀ i, ∃ ht : tt i ∈ reflectionSet p E,
      W.ψ ⟨tt i, Subgroup.subset_closure ht⟩ = Equiv.swap i.castSucc i.succ)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    kZero p E t ≤ ⨆ i, kZero p E (tt i) := by
  set I₀ : Subgroup G := ⨆ i, kZero p E (tt i) with hI₀
  have hTT : ∀ i, tt i ∈ inducedBy E I₀ := by
    intro i
    obtain ⟨hti, -⟩ := htt i
    obtain ⟨-, -, -, -, k, hk, hkK, hkt⟩ := hK (tt i) hti
    exact ⟨k, hk, le_iSup (fun i => kZero p E (tt i)) i hkK, hkt⟩
  have hgen : Subgroup.closure (reflectionSet p E) ≤ inducedBy E I₀ :=
    (closure_le_closure_range W htt).trans
      ((Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hTT i))
  obtain ⟨g, hg, hgt⟩ := W.exists_conj_eq (s := tt ⟨0, hn⟩) (htt ⟨0, hn⟩).1 ht
  obtain ⟨w, hw, hwI, hwg⟩ := hgen hg
  rw [← hgt, ← hwg, kZero_conj p (tt ⟨0, hn⟩) hw]
  have h0 : kZero p E (tt ⟨0, hn⟩) ≤ I₀ := le_iSup (fun i => kZero p E (tt i)) ⟨0, hn⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  exact mul_mem (mul_mem hwI (h0 hy)) (inv_mem hwI)

omit [Finite G] in
include W in
theorem lieGenerated_eq {f : ℕ} (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t) (hn : 0 < n)
    {tt : Fin n → MulAut E}
    (htt : ∀ i, ∃ ht : tt i ∈ reflectionSet p E,
      W.ψ ⟨tt i, Subgroup.subset_closure ht⟩ = Equiv.swap i.castSucc i.succ) :
    lieGenerated p E = ⨆ i, kZero p E (tt i) := by
  apply le_antisymm
  · apply sSup_le
    rintro K ⟨t, ht, hKt⟩
    rw [(isKt_iff_of_nonexceptional (hK t ht).1).1 hKt]
    exact kZero_le_iSup W hK hn htt ht
  · refine iSup_le fun i => le_sSup ⟨tt i, (htt i).1, ?_⟩
    exact (isKt_iff_of_nonexceptional (hK _ (htt i).1).1).2 rfl

omit [Finite G] in
theorem conjAut_mem_torusWeyl {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    conjAut E w hw ∈ torusWeyl E := ⟨⟨w, hw⟩, rfl⟩

omit [Finite G] in
theorem kZero_le_lieGenerated {f : ℕ} (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) : kZero p E t ≤ lieGenerated p E :=
  le_sSup ⟨t, ht, (isKt_iff_of_nonexceptional (hK t ht).1).2 rfl⟩

theorem autMovedInG_le_of_faithful {B : Subgroup G} (hd : RefFacts.ElemData p E) (hBE : B ≤ E)
    (hBinv : torusInvariant E ⊤ B)
    (hfaith : ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ B → g b = b) → g = 1)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) : autMovedInG E t ≤ B := by
  refine RefFacts.autMovedInG_le_of_nontrivial hd ht.1 hBE ?_ ?_
  · intro b hb
    obtain ⟨w, hw, hwt⟩ := WeylIso.exists_lift (WeylIso.mem_torusWeyl_of_mem_reflectionSet ht)
    rw [← hwt, Equivariance.coe_conjAut hw]
    exact hBinv w ⟨Subgroup.mem_top w, hw⟩ b hb
  · by_contra hcon
    push Not at hcon
    have h1 : t = 1 := hfaith t (WeylIso.mem_torusWeyl_of_mem_reflectionSet ht)
      (fun b hb => hcon b hb)
    have := ht.1.1
    rw [h1, orderOf_one] at this
    omega

theorem B_le_lieGenerated {f : ℕ} {B : Subgroup G} (hd : RefFacts.ElemData p E) (hBE : B ≤ E)
    (hBinv : torusInvariant E ⊤ B)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E ⊤ B' → B' = ⊥ ∨ B' = B)
    (hfaith : ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ B → g b = b) → g = 1)
    (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t) (hne : (reflectionSet p E).Nonempty) :
    B ≤ lieGenerated p E := by
  set M : Subgroup G := ⨆ (t : MulAut E) (_ : t ∈ reflectionSet p E), autMovedInG E t with hM
  have hMB : M ≤ B := iSup₂_le fun t ht => autMovedInG_le_of_faithful hd hBE hBinv hfaith ht
  have hMinv : torusInvariant E ⊤ M := by
    intro w hw b hb
    obtain ⟨-, hwN⟩ := hw
    have hle : conjBy w M ≤ M := by
      unfold conjBy
      rw [hM, Subgroup.map_iSup]
      refine iSup_le fun t => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun ht => ?_
      have h1 := Equivariance.autMovedInG_conj t hwN
      have hR : conjAut E w hwN * t * (conjAut E w hwN)⁻¹ ∈ reflectionSet p E :=
        conj_mem_reflectionSet hd.prime ht hwN
      calc Subgroup.map (MulAut.conj w).toMonoidHom (autMovedInG E t)
          = autMovedInG E (conjAut E w hwN * t * (conjAut E w hwN)⁻¹) := h1.symm
        _ ≤ M := le_iSup₂ (f := fun (t : MulAut E) (_ : t ∈ reflectionSet p E) =>
              autMovedInG E t) _ hR
    exact hle (Subgroup.mem_map_of_mem _ hb)
  have hM0 : M ≠ ⊥ := by
    obtain ⟨t, ht⟩ := hne
    intro hbot
    have h1 : autMovedInG E t ≤ M := le_iSup₂ (f := fun (t : MulAut E)
      (_ : t ∈ reflectionSet p E) => autMovedInG E t) t ht
    rw [hbot, le_bot_iff] at h1
    have h2 : Nat.card (autMovedInG E t) = p := by
      unfold autMovedInG
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      exact ht.1.2
    rw [h1, Subgroup.card_bot] at h2
    have := hd.prime.two_le
    omega
  have hMB' : M = B := by
    rcases hirr M hMB hMinv with h | h
    · exact absurd h hM0
    · exact h
  rw [← hMB']
  refine iSup₂_le fun t ht => ?_
  obtain ⟨-, -, -, hmoved, -⟩ := hK t ht
  exact hmoved.trans (kZero_le_lieGenerated hK ht)

include W in
theorem chain_package {f : ℕ} {B : Subgroup G} (hn : 0 < n) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hEel : IsElementaryAbelian p E) (hBE : B ≤ E) (hBinv : torusInvariant E ⊤ B)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E ⊤ B' → B' = ⊥ ∨ B' = B)
    (hfaith : ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ B → g b = b) → g = 1)
    (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t) :
    ∃ tt : Fin n → MulAut E, (∀ i, tt i ∈ reflectionSet p E) ∧ (∀ i j, i ≠ j → tt i ≠ tt j) ∧
      lieGenerated p E = ⨆ i, kZero p E (tt i) ∧ B ≤ lieGenerated p E ∧
      (∀ i j, i ≠ j → ¬ chainAdj i j → tt i * tt j = tt j * tt i) ∧
      (∀ i j, chainAdj i j → orderOf (tt i * tt j) = 3) ∧
      CTTorusCondition p B (fun i => kZero p E (tt i)) := by
  obtain ⟨tt, htt⟩ := exists_chain W
  obtain ⟨hdist, hcomm, hord3, hord6⟩ := chain_swap_facts n
  have hd : RefFacts.ElemData p E :=
    RefFacts.ElemData.of_isElementaryAbelian hp (by omega) hEel
  have hR : ∀ i, tt i ∈ reflectionSet p E := fun i => (htt i).1
  have hψ : ∀ i, W.ψ ⟨tt i, Subgroup.subset_closure (hR i)⟩ =
      Equiv.swap i.castSucc i.succ := fun i => by
    obtain ⟨ht, h⟩ := htt i
    exact h
  have htne : ∀ i j : Fin n, i ≠ j → tt i ≠ tt j := by
    intro i j hij h
    apply hdist i j hij
    rw [← hψ i, ← hψ j]
    simp only [h]
  have hne : (reflectionSet p E).Nonempty := ⟨tt ⟨0, hn⟩, hR _⟩
  refine ⟨tt, hR, htne, lieGenerated_eq W hK hn htt,
    B_le_lieGenerated hd hBE hBinv hirr hfaith hK hne, ?_, ?_, ?_⟩
  · intro i j hij hnadj
    have hnadj' : (i : ℕ) + 1 ≠ j ∧ (j : ℕ) + 1 ≠ i := by
      unfold chainAdj at hnadj
      push Not at hnadj
      exact ⟨hnadj.1, hnadj.2⟩
    refine mul_comm_of_swap W (hR i) (hR j) ?_
    rw [hψ i, hψ j]
    exact hcomm i j hnadj'.1 hnadj'.2 hij
  · intro i j hadj
    rw [orderOf_mul_eq W (hR i) (hR j), hψ i, hψ j]
    unfold chainAdj at hadj
    exact hord3 i j hadj
  · refine RefFacts.ctTorusCondition_of_reflections hd hBE tt (fun i => kZero p E (tt i))
      (fun i => (hR i).1) (fun i => autMovedInG_le_of_faithful hd hBE hBinv hfaith (hR i))
      (fun i => (hK (tt i) (hR i)).2.2.1) (fun i => (hK (tt i) (hR i)).2.2.2.1) ?_
    intro i j hij
    refine RefFacts.inf_autFixedInG_ne hd (hR i).1 (hR j).1
      (WeylIso.mem_torusWeyl_of_mem_reflectionSet (hR i))
      (WeylIso.mem_torusWeyl_of_mem_reflectionSet (hR j)) (htne i j hij) hBE
      (autMovedInG_le_of_faithful hd hBE hBinv hfaith (hR i))
      (autMovedInG_le_of_faithful hd hBE hBinv hfaith (hR j)) hfaith ?_
    have h6 : (tt i * tt j) ^ 6 = 1 := by
      refine pow_six_eq_one W (hR i) (hR j) ?_
      rw [hψ i, hψ j]
      exact hord6 i j
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h6)
      (Sec1212Aut.coprime_of_five_le hp hp5 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).symm

include W in
theorem phan_conclusion (hPhan : ExtPhan) (hn : 3 ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p)
    {B : Subgroup G} {f : ℕ} (hEel : IsElementaryAbelian p E) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f + 1) (hBE : B ≤ E) (hBinv : torusInvariant E ⊤ B)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E ⊤ B' → B' = ⊥ ∨ B' = B)
    (hfaith : ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ B → g b = b) → g = 1)
    (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t)
    (hP : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPair p E f s t) :
    StatedClassicalModel
      (↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E)) .PSU (n + 1) 2 f := by
  obtain ⟨tt, hR, htne, hgenEq, hBI, hcomm, hord3, htor⟩ :=
    chain_package W (by omega) hp hp5 hEel hBE hBinv hirr hfaith hK
  refine extPhan_ambient hPhan (I := lieGenerated p E) (E := B) (n := n)
    (K := fun i => kZero p E (tt i)) hn hf hp (by omega) hpf
    (Planes.isElementaryAbelian_of_le hBE hEel) hBI
    (fun i => by rw [hgenEq]; exact le_iSup (fun i => kZero p E (tt i)) i) hgenEq.symm
    (fun i => (hK (tt i) (hR i)).2.1) ?_ ?_ htor
  · intro i j hij hnadj
    exact (hP (tt i) (hR i) (tt j) (hR j) (htne i j hij)).1 (hcomm i j hij hnadj)
  · intro i j hadj
    have hij : i ≠ j := by
      intro h
      subst h
      unfold chainAdj at hadj
      omega
    exact (hP (tt i) (hR i) (tt j) (hR j) (htne i j hij)).2 (hord3 i j hadj)

include W in
theorem ctA_conclusion (hCT : ExtCurtisTitsA) (hn : 3 ≤ n) (hp : p.Prime) (hp5 : 5 ≤ p)
    {B : Subgroup G} {f : ℕ} (hEel : IsElementaryAbelian p E) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) (hBE : B ≤ E) (hBinv : torusInvariant E ⊤ B)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E ⊤ B' → B' = ⊥ ∨ B' = B)
    (hfaith : ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ B → g b = b) → g = 1)
    (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t)
    (hP : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPairL p E f s t) :
    StatedClassicalModel
        (↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E)) .PSL (n + 1) 2 f ∧
      (Nat.Coprime (n + 1) (2 ^ f - 1) →
        StatedClassicalModel ↥(lieGenerated p E) .PSL (n + 1) 2 f) := by
  obtain ⟨tt, hR, htne, hgenEq, hBI, hcomm, hord3, htor⟩ :=
    chain_package W (by omega) hp hp5 hEel hBE hBinv hirr hfaith hK
  refine extCurtisTitsA_ambient hCT (I := lieGenerated p E) (E := B) (n := n)
    (K := fun i => kZero p E (tt i)) hn hf hp hpf
    (Planes.isElementaryAbelian_of_le hBE hEel) hBI
    (fun i => by rw [hgenEq]; exact le_iSup (fun i => kZero p E (tt i)) i) hgenEq.symm
    (fun i => (hK (tt i) (hR i)).2.1) ?_ ?_ htor
  · intro i j hij hnadj
    exact (hP (tt i) (hR i) (tt j) (hR j) (htne i j hij)).1 (hcomm i j hij hnadj)
  · intro i j hadj
    have hij : i ≠ j := by
      intro h
      subst h
      unfold chainAdj at hadj
      omega
    exact (hP (tt i) (hR i) (tt j) (hR j) (htne i j hij)).2 (hord3 i j hadj)

omit [Finite G] in
theorem even_card_lieGenerated {f : ℕ} (hK : ∀ t ∈ reflectionSet p E, KFAt p E f t)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) : Even (Nat.card (lieGenerated p E)) := by
  obtain ⟨-, -, -, -, k, hk, hkK, hkt⟩ := hK t ht
  have hkI : k ∈ lieGenerated p E := kZero_le_lieGenerated hK ht hkK
  have h1 : orderOf (E.normalizerMonoidHom ⟨k, hk⟩) ∣ orderOf (⟨k, hk⟩ :
      ↥(Subgroup.normalizer (E : Set G))) := orderOf_map_dvd _ _
  rw [hkt, ht.1.1, Subgroup.orderOf_mk] at h1
  exact even_iff_two_dvd.2 (h1.trans (Subgroup.orderOf_dvd_natCard _ hkI))

end PhanAssembly

end CFSG.RankThree.PartOne
