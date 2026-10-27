module

public import CFSG.RankThree.PartOne.S12.PhanAssembly
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.ModelTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

structure Chain3 (p : ℕ) {G : Type} [Group G] (E L : Subgroup G) (t₁ t₂ t₃ : MulAut E) : Prop where
  mem₁ : t₁ ∈ reflectionSet p E
  mem₂ : t₂ ∈ reflectionSet p E
  mem₃ : t₃ ∈ reflectionSet p E
  comm₁₃ : t₁ * t₃ = t₃ * t₁
  ord₁₂ : orderOf (t₁ * t₂) = 4
  ord₂₃ : orderOf (t₂ * t₃) = 3
  gen : Subgroup.closure {t₁, t₂, t₃} = reflectionGroup p E
  cls : ∀ d ∈ reflectionSet p E, (∃ x ∈ reflectionGroup p E, x * t₁ * x⁻¹ = d) ∨
    ∃ x ∈ reflectionGroup p E, x * t₂ * x⁻¹ = d
  inL : ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
    conjAut E w hw * t₁ * (conjAut E w hw)⁻¹ ∈ torusImage E L ∧
      conjAut E w hw * t₂ * (conjAut E w hw)⁻¹ ∈ torusImage E L

@[expose] def KFKt {G : Type} [Group G] (p : ℕ) (E : Subgroup G) (f : ℕ) (t : MulAut E)
    (K : Subgroup G) : Prop :=
  IsKt p E t K ∧ (∀ K' : Subgroup G, IsKt p E t K' → K' = K) ∧
    StatedClassicalModel ↥K .PSL 2 2 f ∧
    E ⊓ Subgroup.centralizer (K : Set G) = autFixedInG E t ∧ autMovedInG E t ≤ K ∧
    ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
      k ∈ K ∧ E.normalizerMonoidHom ⟨k, hk⟩ = t

@[expose] def Node1320Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
      (RowModel p L 5 ∨ RowModel p L 7 ∨ RowModel p L 8) ∧
      Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      ∃ t₁ t₂ t₃ : MulAut E, Chain3 p E L t₁ t₂ t₃

@[expose] def KF1320Sp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f → E = A → ¬ IsLThreeTypeAt p L →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
    ∀ t₁ t₂ t₃ : MulAut E, Chain3 p E L t₁ t₂ t₃ →
      ∃ K₁ K₂ K₃ : Subgroup G, KFKt p E f t₁ K₁ ∧ KFKt p E f t₂ K₂ ∧ KFKt p E f t₃ K₃ ∧
        (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) ∧
        CentrallyLThree f ↥(K₃ ⊔ K₂) ∧ StatedClassicalModel ↥(K₂ ⊔ K₁) .PSp 2 2 f

@[expose] def KF1320U : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f → E = A → ¬ IsLThreeTypeAt p L →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
    ∀ t₁ t₂ t₃ : MulAut E, Chain3 p E L t₁ t₂ t₃ →
      ∃ K₁ K₂ K₃ : Subgroup G, KFKt p E (2 * f) t₁ K₁ ∧ KFKt p E f t₂ K₂ ∧ KFKt p E f t₃ K₃ ∧
        (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) ∧
        CentrallyLThree f ↥(K₃ ⊔ K₂) ∧ StatedClassicalModel ↥(K₂ ⊔ K₁) .PSU 4 2 f

@[expose] def KF1320L4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A → ¬ IsLThreeTypeAt p L →
    1 ≤ f → p ∣ 2 ^ f + 1 → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f →
    Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
      ∃ (r : ℕ) (F K₁ K₂ K₃ : Subgroup G), r.Prime ∧ r ∣ 2 ^ f - 1 ∧
        IsElementaryAbelian r F ∧ F ≤ lieGenerated p E ∧ K₁ ≤ lieGenerated p E ∧
        K₂ ≤ lieGenerated p E ∧ K₃ ≤ lieGenerated p E ∧
        K₁ ⊔ K₂ ⊔ K₃ = lieGenerated p E ∧
        StatedClassicalModel ↥K₁ .PSL 2 2 f ∧ StatedClassicalModel ↥K₂ .PSL 2 2 f ∧
        StatedClassicalModel ↥K₃ .PSL 2 2 (2 * f) ∧
        (K₁ ≤ Subgroup.centralizer (K₃ : Set G) ∧ K₁ ⊓ K₃ = ⊥) ∧
        CentrallyLThree f ↥(K₁ ⊔ K₂) ∧ StatedClassicalModel ↥(K₂ ⊔ K₃) .PSU 4 2 f ∧
        CTTorusCondition r F ![K₁, K₂, K₃] ∧ ¬ (F ⊓ K₂ ≤ Subgroup.centralizer (K₃ : Set G))

namespace Sec1320

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coprime_small {p N : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hN : 0 < N) (hN4 : N ≤ 4) :
    Nat.Coprime N p := by
  refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_).symm
  have := Nat.le_of_dvd hN hd
  omega

omit [Finite G] in
theorem orderOf_mul_comm_reflections {p : ℕ} {E : Subgroup G} {s t : MulAut E}
    (hs : IsAutReflection p E s) (ht : IsAutReflection p E t) :
    orderOf (t * s) = orderOf (s * t) := by
  have h : t * s = (s * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (RefFacts.mul_self_eq_one hs),
      inv_eq_of_mul_eq_one_right (RefFacts.mul_self_eq_one ht)]
  rw [h, orderOf_inv]

omit [Finite G] in
theorem transport {p : ℕ} {E : Subgroup G} {s t : MulAut E} {Ks J : Subgroup G}
    (huniq : ∀ K' : Subgroup G, IsKt p E s K' → K' = Ks) (hmov : autMovedInG E s ≤ Ks)
    (hKsJ : Ks ≤ J) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) (hwJ : w ∈ J)
    (hts : t = conjAut E w hw * s * (conjAut E w hw)⁻¹) :
    (∀ K : Subgroup G, IsKt p E t K → K ≤ J) ∧ autMovedInG E t ≤ J := by
  have hle : conjBy w Ks ≤ J := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 := J.mul_mem (J.mul_mem hwJ (hKsJ hx)) (J.inv_mem hwJ)
    simpa [MulAut.conj_apply] using h1
  subst hts
  refine ⟨fun K hK => ?_, ?_⟩
  · have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
    have h1 := isKt_conj hK hw'
    have h2 : conjAut E w⁻¹ hw' * (conjAut E w hw * s * (conjAut E w hw)⁻¹) *
        (conjAut E w⁻¹ hw')⁻¹ = s := by
      rw [Equivariance.conjAut_inv hw]
      group
    rw [h2] at h1
    have h4 : K = conjBy w Ks := by
      rw [← huniq _ h1, Equivariance.conjBy_conjBy_inv]
    rw [h4]
    exact hle
  · rw [Equivariance.autMovedInG_conj s hw]
    exact (Subgroup.map_mono hmov).trans hle

omit [Finite G] in
theorem lieGenerated_eq {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E} {f₁ f₂ f₃ : ℕ}
    {K₁ K₂ K₃ : Subgroup G} (hch : Chain3 p E L t₁ t₂ t₃) (h₁ : KFKt p E f₁ t₁ K₁)
    (h₂ : KFKt p E f₂ t₂ K₂) (h₃ : KFKt p E f₃ t₃ K₃) :
    lieGenerated p E = K₁ ⊔ K₂ ⊔ K₃ ∧
      ∀ t ∈ reflectionSet p E, autMovedInG E t ≤ K₁ ⊔ K₂ ⊔ K₃ := by
  obtain ⟨hKt₁, hu₁, -, -, hm₁, k₁, hk₁, hk₁K, hk₁t⟩ := h₁
  obtain ⟨hKt₂, hu₂, -, -, hm₂, k₂, hk₂, hk₂K, hk₂t⟩ := h₂
  obtain ⟨hKt₃, hu₃, -, -, hm₃, k₃, hk₃, hk₃K, hk₃t⟩ := h₃
  set J : Subgroup G := K₁ ⊔ K₂ ⊔ K₃ with hJ
  have hJ₁ : K₁ ≤ J := le_sup_left.trans le_sup_left
  have hJ₂ : K₂ ≤ J := le_sup_right.trans le_sup_left
  have hJ₃ : K₃ ≤ J := le_sup_right
  have hind : reflectionGroup p E ≤ PhanAssembly.inducedBy E J := by
    rw [← hch.gen]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨k₁, hk₁, hJ₁ hk₁K, hk₁t⟩
    · exact ⟨k₂, hk₂, hJ₂ hk₂K, hk₂t⟩
    · exact ⟨k₃, hk₃, hJ₃ hk₃K, hk₃t⟩
  have hkey : ∀ t ∈ reflectionSet p E, (∀ K : Subgroup G, IsKt p E t K → K ≤ J) ∧
      autMovedInG E t ≤ J := by
    intro t ht
    rcases hch.cls t ht with ⟨x, hx, hxt⟩ | ⟨x, hx, hxt⟩
    · obtain ⟨w, hw, hwJ, hwx⟩ := hind hx
      exact transport hu₁ hm₁ hJ₁ hw hwJ (by rw [hwx, hxt])
    · obtain ⟨w, hw, hwJ, hwx⟩ := hind hx
      exact transport hu₂ hm₂ hJ₂ hw hwJ (by rw [hwx, hxt])
  refine ⟨le_antisymm ?_ ?_, fun t ht => (hkey t ht).2⟩
  · refine sSup_le ?_
    rintro K ⟨t, ht, hKt⟩
    exact (hkey t ht).1 K hKt
  · exact sup_le (sup_le (le_sSup ⟨t₁, hch.mem₁, hKt₁⟩) (le_sSup ⟨t₂, hch.mem₂, hKt₂⟩))
      (le_sSup ⟨t₃, hch.mem₃, hKt₃⟩)

theorem E_le_of_moved {p : ℕ} {E J : Subgroup G} (hp : p.Prime) (hirr : torusIrreducible E)
    (hmov : ∀ t ∈ reflectionSet p E, autMovedInG E t ≤ J)
    (hne : (reflectionSet p E).Nonempty) : E ≤ J := by
  set M : Subgroup G := ⨆ (t : MulAut E) (_ : t ∈ reflectionSet p E), autMovedInG E t with hM
  have hMJ : M ≤ J := iSup₂_le hmov
  have hME : M ≤ E := iSup₂_le fun t _ => Subgroup.map_subtype_le _
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
        conj_mem_reflectionSet hp ht hwN
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
    have := hp.two_le
    omega
  rcases hirr M hME hMinv with h | h
  · exact absurd h hM0
  · rw [← h]
    exact hMJ

theorem torusCondition {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E} {f₁ f₂ f₃ : ℕ}
    {K₁ K₂ K₃ : Subgroup G} (hp : p.Prime) (hp5 : 5 ≤ p) (hEel : IsElementaryAbelian p E)
    (hch : Chain3 p E L t₁ t₂ t₃) (h₁ : KFKt p E f₁ t₁ K₁) (h₂ : KFKt p E f₂ t₂ K₂)
    (h₃ : KFKt p E f₃ t₃ K₃) : CTTorusCondition p E ![K₃, K₂, K₁] := by
  have hd : RefFacts.ElemData p E := RefFacts.ElemData.of_isElementaryAbelian hp (by omega) hEel
  have hE : ∀ t : MulAut E, autMovedInG E t ≤ E := fun t => Subgroup.map_subtype_le _
  have hfaith : ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ E → g b = b) → g = 1 :=
    fun _ _ h => MulEquiv.ext fun b => h b b.2
  have hpair : ∀ a b : MulAut E, a ∈ reflectionSet p E → b ∈ reflectionSet p E → a ≠ b →
      Nat.Coprime (orderOf (a * b)) p → E ⊓ autFixedInG E a ≠ E ⊓ autFixedInG E b :=
    fun a b ha hb hab hc => RefFacts.inf_autFixedInG_ne hd ha.1 hb.1
      (WeylIso.mem_torusWeyl_of_mem_reflectionSet ha)
      (WeylIso.mem_torusWeyl_of_mem_reflectionSet hb) hab le_rfl (hE a) (hE b) hfaith hc
  have hsymm : ∀ a b : MulAut E, a ∈ reflectionSet p E → b ∈ reflectionSet p E → a ≠ b →
      Nat.Coprime (orderOf (a * b)) p → E ⊓ autFixedInG E b ≠ E ⊓ autFixedInG E a :=
    fun a b ha hb hab hc => hpair b a hb ha hab.symm (by
      rw [orderOf_mul_comm_reflections ha.1 hb.1]
      exact hc)
  have h12 : t₁ ≠ t₂ := by
    intro h
    have := hch.ord₁₂
    rw [← h, RefFacts.mul_self_eq_one hch.mem₁.1, orderOf_one] at this
    omega
  have h23 : t₂ ≠ t₃ := by
    intro h
    have := hch.ord₂₃
    rw [← h, RefFacts.mul_self_eq_one hch.mem₂.1, orderOf_one] at this
    omega
  have h13 : t₁ ≠ t₃ := by
    intro h
    have h1 := hch.ord₂₃
    rw [← h, orderOf_mul_comm_reflections hch.mem₁.1 hch.mem₂.1, hch.ord₁₂] at h1
    omega
  have c12 : Nat.Coprime (orderOf (t₁ * t₂)) p := by
    rw [hch.ord₁₂]
    exact coprime_small hp hp5 (by norm_num) (by norm_num)
  have c23 : Nat.Coprime (orderOf (t₂ * t₃)) p := by
    rw [hch.ord₂₃]
    exact coprime_small hp hp5 (by norm_num) (by norm_num)
  have c13 : Nat.Coprime (orderOf (t₁ * t₃)) p := by
    have h2 : (t₁ * t₃) ^ 2 = 1 := by
      rw [pow_two]
      calc t₁ * t₃ * (t₁ * t₃) = t₁ * (t₃ * t₁) * t₃ := by group
        _ = t₁ * (t₁ * t₃) * t₃ := by rw [hch.comm₁₃]
        _ = (t₁ * t₁) * (t₃ * t₃) := by group
        _ = 1 := by
          rw [RefFacts.mul_self_eq_one hch.mem₁.1, RefFacts.mul_self_eq_one hch.mem₃.1, one_mul]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)
      (coprime_small hp hp5 (by norm_num) (by norm_num))
  refine RefFacts.ctTorusCondition_of_reflections hd (le_refl E) ![t₃, t₂, t₁] ![K₃, K₂, K₁]
    ?_ (fun i => hE _) ?_ ?_ ?_
  · intro i
    fin_cases i
    exacts [hch.mem₃.1, hch.mem₂.1, hch.mem₁.1]
  · intro i
    fin_cases i
    exacts [h₃.2.2.2.1, h₂.2.2.2.1, h₁.2.2.2.1]
  · intro i
    fin_cases i
    exacts [h₃.2.2.2.2.1, h₂.2.2.2.2.1, h₁.2.2.2.2.1]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hsymm t₂ t₃ hch.mem₂ hch.mem₃ h23 c23
    · exact hsymm t₁ t₃ hch.mem₁ hch.mem₃ h13 c13
    · exact hpair t₂ t₃ hch.mem₂ hch.mem₃ h23 c23
    · exact absurd rfl hij
    · exact hsymm t₁ t₂ hch.mem₁ hch.mem₂ h12 c12
    · exact hpair t₁ t₃ hch.mem₁ hch.mem₃ h13 c13
    · exact hpair t₁ t₂ hch.mem₁ hch.mem₂ h12 c12
    · exact absurd rfl hij

theorem package {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E} {f₁ f₂ f₃ : ℕ}
    {K₁ K₂ K₃ : Subgroup G} (hp : p.Prime) (hp5 : 5 ≤ p) (hEel : IsElementaryAbelian p E)
    (hirr : torusIrreducible E) (hch : Chain3 p E L t₁ t₂ t₃) (h₁ : KFKt p E f₁ t₁ K₁)
    (h₂ : KFKt p E f₂ t₂ K₂) (h₃ : KFKt p E f₃ t₃ K₃) :
    lieGenerated p E = K₃ ⊔ K₂ ⊔ K₁ ∧ E ≤ lieGenerated p E ∧
      CTTorusCondition p E ![K₃, K₂, K₁] := by
  obtain ⟨hI, hmov⟩ := lieGenerated_eq hch h₁ h₂ h₃
  refine ⟨?_, E_le_of_moved hp hirr (fun t ht => (hmov t ht).trans hI.ge) ⟨t₁, hch.mem₁⟩,
    torusCondition hp hp5 hEel hch h₁ h₂ h₃⟩
  rw [hI]
  ac_rfl

omit [Finite G] in
theorem commuting_symm {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G) ∧ A ⊓ B = ⊥) :
    B ≤ Subgroup.centralizer (A : Set G) ∧ B ⊓ A = ⊥ := by
  refine ⟨fun x hx => ?_, by rw [inf_comm]; exact h.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.1 (h.1 hy)) x hx).symm

omit [Finite G] in
theorem even_card {p : ℕ} {E : Subgroup G} {t : MulAut E} {f : ℕ} {K I : Subgroup G}
    (ht : t ∈ reflectionSet p E) (hK : KFKt p E f t K) (hKI : K ≤ I) :
    Even (Nat.card I) := by
  obtain ⟨-, -, -, -, -, k, hk, hkK, hkt⟩ := hK
  have h1 : orderOf (E.normalizerMonoidHom ⟨k, hk⟩) ∣
      orderOf (⟨k, hk⟩ : ↥(Subgroup.normalizer (E : Set G))) := orderOf_map_dvd _ _
  rw [hkt, ht.1.1, Subgroup.orderOf_mk] at h1
  exact even_iff_two_dvd.2 (h1.trans (Subgroup.orderOf_dvd_natCard _ (hKI hkK)))

open CFSG.Assembly.LowTwoRank (StatedSL StatedScalars StatedProj) in
theorem even_card_of_psl_two {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) : Even (Nat.card X) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have h2 : Even (Fintype.card K) := by
      rw [← Nat.card_eq_fintype_card, hK]
      exact Nat.even_pow.2 ⟨even_two, by omega⟩
    exact ringChar.of_eq (FiniteField.even_card_iff_char_two.2 (Nat.even_iff.1 h2))
  let T : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])
  have hTT : T * T = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hTmem : T ∈ StatedSL 2 K := Subgroup.subset_closure (by simp [T, Matrix.det_fin_two])
  have hTscal : T ∉ StatedScalars (Fin 2) K := by
    rintro ⟨μ, hμ⟩
    have h01 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) hμ
    simp [T] at h01
  let g : StatedSL 2 K := ⟨T, hTmem⟩
  let x : StatedProj (StatedSL 2 K) := QuotientGroup.mk g
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    change (QuotientGroup.mk g : StatedProj (StatedSL 2 K)) * QuotientGroup.mk g = 1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext hTT
  have hx1 : x ≠ 1 := fun hx =>
    hTscal (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff g).1 hx))
  have hord : orderOf (e.symm x) = 2 := by
    refine orderOf_eq_prime ?_ fun h' => hx1 ((MulEquiv.map_eq_one_iff e.symm).1 h')
    rw [← map_pow, hx2, map_one]
  exact even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard (e.symm x))

omit [Finite G] in
theorem moved_not_le_fixed {p : ℕ} {E : Subgroup G} (hd : RefFacts.ElemData p E)
    {t₁ t₂ : MulAut E} (h₁ : IsAutReflection p E t₁) (h₂ : IsAutReflection p E t₂)
    (hord : orderOf (t₁ * t₂) = 4) : ¬ (autMoved E t₂ ≤ autFixed E t₁) := by
  intro hle
  have hcomm := hd.comm
  let _ : CommGroup E := { (inferInstance : Group ↥E) with mul_comm := hcomm }
  have ht₁ := RefFacts.mul_self_eq_one h₁
  have ht₁t₁ : ∀ x : E, t₁ (t₁ x) = x := fun x => by
    simpa using congrArg (fun m : MulAut E => m x) ht₁
  have hfix : ∀ z ∈ autMoved E t₂, t₁ z = z := fun z hz => hle hz
  have hinv : ∀ z ∈ autMoved E t₂, t₂ z = z⁻¹ := fun z hz =>
    RefFacts.t_apply_inv_of_mem_autMoved hd h₂ hz
  have hmv : ∀ x : E, t₂ x * x⁻¹ ∈ autMoved E t₂ := fun x => Subgroup.subset_closure ⟨x, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : MulAut E, g = (t₁ * t₂) ^ 2 := ⟨_, rfl⟩
  have hgx : ∀ x : E, g x * x⁻¹ ∈ autMoved E t₂ := by
    intro x
    obtain ⟨a, ha, e1⟩ : ∃ a ∈ autMoved E t₂, t₂ x = a * x := ⟨t₂ x * x⁻¹, hmv x, by simp⟩
    obtain ⟨b, hb, e2⟩ : ∃ b ∈ autMoved E t₂, t₂ (t₁ x) = b * t₁ x :=
      ⟨t₂ (t₁ x) * (t₁ x)⁻¹, hmv _, by simp⟩
    have hga : g x = a⁻¹ * (b * x) := by
      rw [hg]
      simp only [pow_two, MulAut.mul_apply]
      rw [e1, map_mul, hfix a ha, map_mul, hinv a ha, e2, map_mul, map_mul, map_inv, hfix a ha,
        hfix b hb, ht₁t₁ x]
    rw [hga]
    have h1 : a⁻¹ * (b * x) * x⁻¹ = a⁻¹ * b := by group
    rw [h1]
    exact (autMoved E t₂).mul_mem ((autMoved E t₂).inv_mem ha) hb
  have hgz : ∀ z ∈ autMoved E t₂, g z = z := by
    intro z hz
    rw [hg]
    simp only [pow_two, MulAut.mul_apply, map_inv, hinv z hz, hfix z hz, inv_inv]
  have hpow : ∀ (k : ℕ) (x : E), (g ^ k) x = x * (g x * x⁻¹) ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      obtain ⟨c, hc, hcx⟩ : ∃ c ∈ autMoved E t₂, g x = c * x := ⟨g x * x⁻¹, hgx x, by simp⟩
      have hcdef : g x * x⁻¹ = c := by rw [hcx]; simp
      have hgc : g (c ^ k) = c ^ k := hgz _ ((autMoved E t₂).pow_mem hc k)
      rw [show g ^ (k + 1) = g * g ^ k from pow_succ' g k, MulAut.mul_apply, ih x, hcdef, map_mul,
        hgc, hcx, show c ^ (k + 1) = c * c ^ k from pow_succ' c k, mul_comm c x, mul_assoc]
  have hgp : g ^ p = 1 := by
    refine MulEquiv.ext fun x => ?_
    rw [hpow, hd.pow]
    simp
  have hg4 : (t₁ * t₂) ^ 4 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hg2 : g ^ 2 = 1 := by
    rw [hg, ← pow_mul]
    exact hg4
  have hcop : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two hd.prime).2 (Ne.symm hd.ne_two)
  have hg1 : g = 1 := by
    have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
    have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have h4 : orderOf (t₁ * t₂) ∣ 2 := orderOf_dvd_of_pow_eq_one (hg ▸ hg1)
  rw [hord] at h4
  omega

omit [Finite G] in
theorem not_le_centralizer {p : ℕ} {E L : Subgroup G} {t₁ t₂ t₃ : MulAut E} {f₁ f₂ : ℕ}
    {K₁ K₂ : Subgroup G} (hd : RefFacts.ElemData p E) (hch : Chain3 p E L t₁ t₂ t₃)
    (h₁ : KFKt p E f₁ t₁ K₁) (h₂ : KFKt p E f₂ t₂ K₂) :
    ¬ (E ⊓ K₂ ≤ Subgroup.centralizer (K₁ : Set G)) := by
  intro h
  have hmov : autMovedInG E t₂ ≤ E ⊓ K₂ := le_inf (Subgroup.map_subtype_le _) h₂.2.2.2.2.1
  have hfix : autMovedInG E t₂ ≤ autFixedInG E t₁ := by
    have h1 : autMovedInG E t₂ ≤ E ⊓ Subgroup.centralizer (K₁ : Set G) :=
      le_inf (hmov.trans inf_le_left) (hmov.trans h)
    rwa [h₁.2.2.2.1] at h1
  exact moved_not_le_fixed hd hch.mem₁.1 hch.mem₂.1 hch.ord₁₂
    ((Subgroup.map_le_map_iff_of_injective E.subtype_injective).1 hfix)

end Sec1320

theorem node1320_of_struct (hS : Node1320Struct) (hKSp : KF1320Sp) (hKU : KF1320U)
    (hKL4 : KF1320L4) (hCSp : ExtCurtisTitsCThreeSp) (hCB : ExtCurtisTitsBThree)
    (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) : Node1320 := by
  intro G _ _ p A c L E h hT hEA hnL3
  have hF12 := Sec12Facts.of_nodes h122 h122b h123 h124 h125 h
  have hF13 := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126
    h127 h128 h129 h hT
  obtain ⟨hrow, hweyl, t₁, t₂, t₃, hch⟩ := hS G p A c L E h hF12 hF13 hT hEA hnL3
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  rcases hrow with ⟨f, hf1, hpf, hmodel⟩ | ⟨f, hf1, hpf, hmodel⟩ | h8
  · have hf2 : 2 ≤ f := by
      by_contra hlt
      have hf : f = 1 := by omega
      subst hf
      have h1 := Nat.le_of_dvd (by norm_num) hpf
      norm_num at h1
      omega
    obtain ⟨K₁, K₂, K₃, hk₁, hk₂, hk₃, hcomm, hL, hU⟩ :=
      hKU G p A c L E f h hF12 hF13 hT hf1 hpf hmodel hEA hnL3 hweyl t₁ t₂ t₃ hch
    obtain ⟨hI, hEI, htor⟩ := Sec1320.package hp hp5 h.E_elem hF13.irreducible hch hk₁ hk₂ hk₃
    have hK₃I : K₃ ≤ lieGenerated p E := by rw [hI]; exact le_sup_left.trans le_sup_left
    have hK₂I : K₂ ≤ lieGenerated p E := by rw [hI]; exact le_sup_right.trans le_sup_left
    have hK₁I : K₁ ≤ lieGenerated p E := by rw [hI]; exact le_sup_right
    have hd : RefFacts.ElemData p E :=
      RefFacts.ElemData.of_isElementaryAbelian hp (by omega) h.E_elem
    have hΩ := extCurtisTitsBThree_ambient hCB hf2 hp hpf h.E_elem hEI hK₃I hK₂I hK₁I hI.symm
      hk₃.2.2.1 hk₂.2.2.1 hk₁.2.2.1 (Sec1320.commuting_symm hcomm) hL hU htor
      (Sec1320.not_le_centralizer hd hch hk₁ hk₂)
    obtain ⟨b, c', hirr, ⟨e⟩⟩ := projOmegaMinus_of_statedClassicalModel hΩ
    exact Or.inr (Or.inl ⟨f, hf1, hpf, ⟨b, c', hirr, ⟨e⟩⟩, hweyl, hEA,
      Sec1320.even_card hch.mem₁ hk₁ hK₁I⟩)
  · have hf2 : 2 ≤ f := by
      by_contra hlt
      have hf : f = 1 := by omega
      subst hf
      have h1 := Nat.le_of_dvd (by norm_num) hpf
      norm_num at h1
      omega
    obtain ⟨K₁, K₂, K₃, hk₁, hk₂, hk₃, hcomm, hL, hSp⟩ :=
      hKSp G p A c L E f h hF12 hF13 hT hf1 hpf hmodel hEA hnL3 hweyl t₁ t₂ t₃ hch
    obtain ⟨hI, hEI, htor⟩ := Sec1320.package hp hp5 h.E_elem hF13.irreducible hch hk₁ hk₂ hk₃
    have hK₃I : K₃ ≤ lieGenerated p E := by rw [hI]; exact le_sup_left.trans le_sup_left
    have hK₂I : K₂ ≤ lieGenerated p E := by rw [hI]; exact le_sup_right.trans le_sup_left
    have hK₁I : K₁ ≤ lieGenerated p E := by rw [hI]; exact le_sup_right
    have hS' := extCurtisTitsCThreeSp_ambient hCSp hf2 hp hpf h.E_elem hEI hK₃I hK₂I hK₁I hI.symm
      hk₃.2.2.1 hk₂.2.2.1 hk₁.2.2.1 (Sec1320.commuting_symm hcomm) hL hSp htor
    exact Or.inl ⟨f, hf1, hpf, projSp_of_statedClassicalModel hS', hweyl, hEA,
      Sec1320.even_card hch.mem₁ hk₁ hK₁I⟩
  · obtain ⟨f, hf1, hpf, hmodel⟩ := h8
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have hf : f = 1 := by omega
      subst hf
      have h1 := Nat.le_of_dvd (by norm_num) hpf
      norm_num at h1
      omega
    obtain ⟨r, F, K₁, K₂, K₃, hr, hrf, hFel, hFI, h₁I, h₂I, h₃I, hgen, hm₁, hm₂, hm₃, hcomm, hL,
      hU, htor, hstd⟩ := hKL4 G p A c L E f h hF12 hF13 hT hEA hnL3 hf1 hpf hmodel hweyl
    have hΩ := extCurtisTitsBThree_ambient hCB (I := lieGenerated p E) (E := F) (p := r)
      (f := f) hf2 hr hrf hFel hFI h₁I h₂I h₃I hgen hm₁ hm₂ hm₃ hcomm hL hU htor hstd
    obtain ⟨b, c', hirr, ⟨e⟩⟩ := projOmegaMinus_of_statedClassicalModel hΩ
    have heven : Even (Nat.card ↥(lieGenerated p E)) :=
      even_iff_two_dvd.2 ((even_iff_two_dvd.1 (Sec1320.even_card_of_psl_two hm₁)).trans
        (Subgroup.card_dvd_of_le h₁I))
    exact Or.inr (Or.inr ⟨f, hf1, hpf, ⟨b, c', hirr, ⟨e⟩⟩, hweyl, hEA, heven⟩)

end CFSG.RankThree.PartOne
