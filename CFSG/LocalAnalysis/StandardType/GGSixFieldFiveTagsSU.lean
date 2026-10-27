module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsSUCore

public section

namespace CFSG.StandardType

namespace FieldFiveSU

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores LayerFacts ClNonsplit
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Helpers

variable {K : Type} [Field K] {f n : ℕ}

theorem isCoreFamily_su_sub (h : UnitaryFieldData 2 f K) {A : Subgroup (GL (Fin n) K)} {β : Type}
    {S : β → Subgroup (GL (Fin n) K)}
    (hS : IsCoreFamily (adjCent A (isInvol_suAdj (n := n) h)) S) :
    IsCoreFamily ((Subgroup.centralizer (A : Set (GL (Fin n) K))).comap
      (unitarySU 2 f K n).subtype) (fun c => (S c).comap (unitarySU 2 f K n).subtype) := by
  classical
  set H₀ : Subgroup (GL (Fin n) K) :=
    adjCent A (isInvol_suAdj (n := n) h) ⊓ (Matrix.GeneralLinearGroup.det).ker with hH₀
  have hSdet : ∀ c, S c ≤ H₀ := by
    intro c
    refine le_inf (hS.1 c) ?_
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (hS.2.2.1 c)]
    exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
  have hS0 := hS.mono inf_le_left hSdet
  have hdet : ∀ g : GL (Fin n) K, g ∈ (Matrix.GeneralLinearGroup.det).ker ↔
      (g : Matrix (Fin n) (Fin n) K).det = 1 := fun g => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hle : H₀ ≤ (unitarySU 2 f K n).subtype.range := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨g, (mem_unitarySU_iff_suAdj h).mpr ⟨(Subgroup.mem_inf.mp hg1).2, (hdet g).mp hg2⟩⟩,
      rfl⟩
  have hC : H₀.comap (unitarySU 2 f K n).subtype =
      (Subgroup.centralizer (A : Set (GL (Fin n) K))).comap (unitarySU 2 f K n).subtype := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hH₀, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hx := (mem_unitarySU_iff_suAdj h).mp x.2
    exact ⟨fun hx' => hx'.1.1, fun hx' => ⟨⟨hx', hx.1⟩, (hdet _).mpr hx.2⟩⟩
  have h2 := hS0.comap (unitarySU 2 f K n).subtype (Subgroup.subtype_injective _) hle
  rwa [hC] at h2

theorem closure_pair_facts {A B : GL (Fin n) K} (hAB : A * B = B * A) (hA5 : A ^ 5 = 1)
    (hB5 : B ^ 5 = 1) :
    Subgroup.closure {A, B} ≤
        Subgroup.centralizer ((Subgroup.closure {A, B} : Subgroup (GL (Fin n) K)) :
          Set (GL (Fin n) K)) ∧
      ∀ g ∈ Subgroup.closure {A, B}, g ^ 5 = 1 := by
  have hcomm : Subgroup.closure {A, B} ≤
      Subgroup.centralizer ((Subgroup.closure {A, B} : Subgroup (GL (Fin n) K)) :
        Set (GL (Fin n) K)) := by
    rw [Subgroup.centralizer_closure, Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g' hg'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hg'
    rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
    · rfl
    · exact hAB.symm
    · exact hAB
    · rfl
  refine ⟨hcomm, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hA5
    · exact hB5
  | one => exact one_pow 5
  | mul g g' hg hg' ih ih' =>
    have hc : Commute g g' := (Subgroup.mem_centralizer_iff.mp (hcomm hg') g hg)
    rw [hc.mul_pow, ih, ih', one_mul]
  | inv g hg ih => rw [inv_pow, ih, inv_one]

end Helpers

section Induced

variable {K : Type} [Field K] [Finite K] {f n : ℕ} {G : Type} [Group G]
  {ψ : ↥(unitarySU 2 f K n) →* G}

omit [Finite K] in
theorem exists_mem_closure_pair_of_mem_closure {x y₀ : G} {A B : GL (Fin n) K}
    (hA : (x, A) ∈ SUTorus.suPairs ψ) (hB : (y₀, B) ∈ SUTorus.suPairs ψ) {e : G}
    (he : e ∈ Subgroup.closure {x, y₀}) :
    ∃ g ∈ Subgroup.closure {A, B}, (e, g) ∈ SUTorus.suPairs ψ := by
  induction he using Subgroup.closure_induction with
  | mem e he =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact ⟨A, Subgroup.subset_closure (Set.mem_insert _ _), hA⟩
    · exact ⟨B, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), hB⟩
  | one => exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _⟩
  | mul e e' he he' ih ih' =>
    obtain ⟨g, hg, hge⟩ := ih
    obtain ⟨g', hg', hge'⟩ := ih'
    refine ⟨g * g', Subgroup.mul_mem _ hg hg', ?_⟩
    have h1 := (SUTorus.suPairs ψ).mul_mem hge hge'
    rwa [Prod.mk_mul_mk] at h1
  | inv e he ih =>
    obtain ⟨g, hg, hge⟩ := ih
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    have h1 := (SUTorus.suPairs ψ).inv_mem hge
    rwa [Prod.inv_mk] at h1

omit [Finite K] in
theorem centralizer_inducedMatrices_eq (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {D : Subgroup G} {x y₀ : G} (hD : D = Subgroup.closure {x, y₀}) {A B : GL (Fin n) K}
    (hA : (x, A) ∈ SUTorus.suPairs ψ) (hB : (y₀, B) ∈ SUTorus.suPairs ψ) :
    Subgroup.centralizer (SUTorus.inducedMatrices ψ D : Set (GL (Fin n) K)) =
      Subgroup.centralizer ((Subgroup.closure {A, B} : Subgroup (GL (Fin n) K)) :
        Set (GL (Fin n) K)) := by
  obtain ⟨q, hq, hqd⟩ := exists_prime_dvd_two_pow_add_one f
  have hxD : x ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hyD : y₀ ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · refine Subgroup.centralizer_le ?_
    show Subgroup.closure {A, B} ≤ SUTorus.inducedMatrices ψ D
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact SUTorus.mem_inducedMatrices.mpr ⟨x, hxD, hA⟩
    · exact SUTorus.mem_inducedMatrices.mpr ⟨y₀, hyD, hB⟩
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro M hM
    obtain ⟨e, he, heM⟩ := SUTorus.mem_inducedMatrices.mp hM
    obtain ⟨g', hg', heg'⟩ := exists_mem_closure_pair_of_mem_closure hA hB (hD ▸ he)
    obtain ⟨c, rfl⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hn hnq hq hqd hker heg' heM
    have h1 := hg g' hg'
    rw [mul_assoc, h1, ← mul_assoc, TypeA.PGLTor.scalar_mul_comm, mul_assoc]

end Induced

section Main

theorem fieldFive_su {K : Type} [Field K] {n : ℕ} {G : Type} [Group G] [Finite G]
    (h : UnitaryFieldData 2 1 K) (hn : 4 ≤ n) {ψ : ↥(unitarySU 2 1 K n) →* G}
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K n)) {D : Subgroup G}
    (hDel : IsElemAbelian 5 D) (hDcard : Nat.card D = 5 ^ 2)
    (hDs : ∀ e ∈ D, ∃ B, (e, B) ∈ SUTorus.suPairs ψ) {x : G} (hxD : x ∈ D) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}))
    (hLmark : GGNbrClauseFiveMarking 5 x L)
    {J : Subgroup G} (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ K' : Subgroup G,
      IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ J ≤ K' ∧ 5 ∣ Nat.card K' ∧
      x ∉ Subgroup.centralizer (K' : Set G) ∧ ¬ GGNbrClauseFiveMarking 5 x K' := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hK4 : Nat.card K = 4 := by rw [h.card_eq_sq]; norm_num
  have hpK : ¬ 5 ∣ Nat.card K - 1 := by rw [hK4]; norm_num
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hx5 : x ^ 5 = 1 := hDel.2 x hxD
  have hnot : ∀ u ∈ D, ∃ v ∈ D, v ∉ Subgroup.zpowers u := by
    intro u hu
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers u from fun d hd => hall d hd)
    rw [Nat.card_zpowers, hDcard] at h1
    have h2 : orderOf u ≤ 5 := orderOf_le_of_pow_eq_one (by norm_num) (hDel.2 u hu)
    omega
  obtain ⟨u₁, hu₁D, hu₁1⟩ : ∃ u₁ ∈ D, u₁ ≠ 1 := by
    obtain ⟨v, hvD, hv⟩ := hnot 1 D.one_mem
    exact ⟨v, hvD, fun h1 => hv (by rw [h1]; exact Subgroup.one_mem _)⟩
  obtain ⟨u₂, hu₂D, hu₂⟩ := hnot u₁ hu₁D
  have hDu : D = Subgroup.closure {u₁, u₂} :=
    (ggClosure_pair_eq hp hDcard hu₁D hu₂D hu₁1 (hDel.2 u₁ hu₁D) hu₂).symm
  have hu12 : u₁ * u₂ = u₂ * u₁ :=
    congrArg Subtype.val (hDel.1.is_comm.comm (⟨u₁, hu₁D⟩ : ↥D) ⟨u₂, hu₂D⟩)
  obtain ⟨A₀, hA₀⟩ := hDs u₁ hu₁D
  obtain ⟨B₀, hB₀⟩ := hDs u₂ hu₂D
  obtain ⟨A₁, hA₁, hA₁5⟩ := exists_mem_suPairs_pow_eq_one h (by omega) hnq hker hp hpK
    (hDel.2 u₁ hu₁D) hA₀
  obtain ⟨A₂, hA₂, hA₂5⟩ := exists_mem_suPairs_pow_eq_one h (by omega) hnq hker hp hpK
    (hDel.2 u₂ hu₂D) hB₀
  have hA12 : A₁ * A₂ = A₂ * A₁ :=
    mul_comm_of_mem_suPairs h (by omega) hnq hker hp hpK hu12 hA₁ hA₂ hA₁5
  have hA₁u := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK hA₁.1 hA₁5
  have hA₂u := mem_unitaryOf_of_pow_eq_one h (by omega) hp hpK hA₂.1 hA₂5
  set AD : Subgroup (GL (Fin n) K) := Subgroup.closure {A₁, A₂} with hADdef
  obtain ⟨hADcomm, hAD5⟩ := closure_pair_facts hA12 hA₁5 hA₂5
  have hADu : AD ≤ unitaryOf (isInvol_suAdj (n := n) h) := by
    rw [hADdef, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hA₁u
    · exact hA₂u
  have hADcard : (Nat.card AD : K) ≠ 0 := FieldFiveSp.natCast_card_ne_zero_of_pow_five fun g =>
    Subtype.ext (by simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hAD5 _ g.2)
  obtain ⟨A, hAAD, hA⟩ := exists_mem_closure_pair_of_mem_closure hA₁ hA₂ (hDu ▸ hxD)
  obtain ⟨y₀, hy₀D, hy₀x⟩ := hnot x hxD
  obtain ⟨B, hBAD, hB⟩ := exists_mem_closure_pair_of_mem_closure hA₁ hA₂ (hDu ▸ hy₀D)
  have hA5 : A ^ 5 = 1 := hAD5 A hAAD
  have hB5 : B ^ 5 = 1 := hAD5 B hBAD
  have hcommAD : ∀ g ∈ AD, ∀ g' ∈ AD, g * g' = g' * g := fun g hg g' hg' =>
    Subgroup.mem_centralizer_iff.mp (hADcomm hg') g hg
  obtain ⟨c₀, hc₀⟩ := exists_add_bar_eq_one h
  obtain ⟨r, E, e, _, _, _, _, _, Φ, τ, hτ, π, hπ, Sf, hΦ, hR, -, himg, -, hSle, hSn, hder,
    hq⟩ := exists_coreData (isInvol_suAdj (n := n) h) hADcard
      (fun X hX g hg => adj_mul_comm (isInvol_suAdj (n := n) h) (hADu hg) (hX g hg))
      ⟨c₀ • 1, fun g _ => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one],
        by rw [suAdj_smul_one, ← add_smul, hc₀, one_smul]⟩
  have hΦu : Function.Injective (Units.map Φ.toMonoidHom) :=
    Units.map_injective (f := Φ.toMonoidHom) hΦ
  have hFD : IsCoreFamily (adjCent AD (isInvol_suAdj (n := n) h))
      (fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} =>
        (coreOf π hτ Sf c.1).map (Units.map Φ.toMonoidHom)) := by
    have h1 := (isCoreFamily_coreOf hτ hπ hSle hSn hder hq).map _ hΦu
    rwa [himg] at h1
  have hFD' := isCoreFamily_su_sub h hFD
  rw [← centralizer_inducedMatrices_eq h (by omega) hnq hker hDu hA₁ hA₂] at hFD'
  have hJG : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    have h1 := CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hL.2.1
      (Subgroup.centralizer (D : Set G))
    have h2 : ψ.range ⊓ Subgroup.centralizer {x} ⊓ Subgroup.centralizer (D : Set G) =
        ψ.range ⊓ Subgroup.centralizer (D : Set G) := by
      rw [inf_assoc, inf_eq_right.mpr
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxD))]
    rw [h2] at h1
    exact isComponentOf_of_isSubnormal_of_isComponentOf hJ h1
  obtain ⟨⟨c, hcπ, hSc⟩, hJeq⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker
    (map_ggSUCent_le hDs) (normal_map_ggSUCent hker) (commutator_le_map_ggSUCent hker)
    _ hFD'.1 hFD'.2.1 hFD'.2.2.1 hFD'.2.2.2.1 hJG
  set S := (coreOf π hτ Sf c).map (Units.map Φ.toMonoidHom) with hSdef
  have hSq : CFSG.IsQuasisimple S := hFD.2.2.1 ⟨c, hcπ, hSc⟩
  have hSU : S ≤ unitaryOf (isInvol_suAdj (n := n) h) :=
    (hFD.1 ⟨c, hcπ, hSc⟩).trans inf_le_right
  have hJeq' : J = (S.comap (unitarySU 2 1 K n).subtype).map ψ := hJeq
  have hcoord : ∀ g ∈ AD, ∃ a : (PiMat E e)ˣ, a ∈ unitaryOf hτ ∧
      Units.map Φ.toMonoidHom a = g ∧
        ∀ z : PiMat E e, z * (a : PiMat E e) = (a : PiMat E e) * z := by
    intro g hg
    have hgB : g ∈ adjCent AD (isInvol_suAdj (n := n) h) :=
      Subgroup.mem_inf.mpr ⟨hADcomm hg, hADu hg⟩
    rw [← himg] at hgB
    obtain ⟨a, haU, hag⟩ := hgB
    refine ⟨a, haU, hag, fun z => hΦ ?_⟩
    have h1 := (hR (Φ z)).mp ⟨z, rfl⟩ g hg
    have hag' : (g : Matrix (Fin n) (Fin n) K) = Φ (a : PiMat E e) := by rw [← hag]; rfl
    rw [map_mul, map_mul, ← hag']
    exact h1
  obtain ⟨a, haU, has, hac⟩ := hcoord A hAAD
  obtain ⟨w₀, hw₀U, hw₀s, hw₀c⟩ := hcoord B hBAD
  obtain ⟨α, hα⟩ := exists_scalar_of_central hac c
  obtain ⟨β, hβ⟩ := exists_scalar_of_central hw₀c c
  have hscal5 : ∀ (u : (PiMat E e)ˣ) (γ : E c),
      (u : PiMat E e) c = Matrix.scalar (Fin (e c)) γ → u ^ 5 = 1 → γ ^ 5 = 1 := by
    intro u γ hγ hu5
    have h1 := congrArg (fun v : (PiMat E e)ˣ => (v : PiMat E e) c) hu5
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, Units.val_one, Pi.one_apply] at h1
    rw [hγ, ← map_pow] at h1
    have i₀ : Fin (e c) := ⟨0, Nat.pos_of_ne_zero (NeZero.ne (e c))⟩
    have h2 := congrFun (congrFun h1 i₀) i₀
    simpa using h2
  have ha5 : a ^ 5 = 1 := hΦu (by rw [map_pow, has, hA5, map_one])
  have hw5 : w₀ ^ 5 = 1 := hΦu (by rw [map_pow, hw₀s, hB5, map_one])
  have hα5 := hscal5 a α hα ha5
  have hβ5 := hscal5 w₀ β hβ hw5
  have hα1 : α ≠ 1 := by
    intro hα1
    have hac1 : (a : PiMat E e) c = 1 := by rw [hα, hα1, map_one]
    have hfix := FieldFiveSp.fix_of_coord_eq_one (Φ := Φ) hτ hπ (Sf := Sf) haU hac1
    rw [has] at hfix
    obtain ⟨Kx, hKx, hJKx, -, hKxw⟩ :=
      exists_fixedCore_component_su h hn hker hA hA5 hSq hSU fun M hM => hfix M hM
    rw [← hJeq'] at hJKx
    have hLK : L = Kx := by
      rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hL hKx with h1 | h1
      · exact h1
      · exfalso
        apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ.2.2
        have hc : L ≤ Subgroup.centralizer (Kx : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
        exact ((hJ.1.trans inf_le_left).trans hc).trans (Subgroup.centralizer_le hJKx)
    exact (hKxw x A hA hA5 rfl).1 (hLK ▸ hLmark)
  have hαo : orderOf α = 5 := orderOf_eq_prime hα5 hα1
  have hprim : IsPrimitiveRoot α 5 := hαo ▸ IsPrimitiveRoot.orderOf α
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hβ5
  have hyt : (y₀ * (x ^ j)⁻¹, B * (A ^ j)⁻¹) ∈ SUTorus.suPairs ψ := by
    have h1 := (SUTorus.suPairs ψ).mul_mem hB
      ((SUTorus.suPairs ψ).inv_mem ((SUTorus.suPairs ψ).pow_mem hA j))
    rwa [Prod.pow_mk, Prod.inv_mk, Prod.mk_mul_mk] at h1
  have hyD : y₀ * (x ^ j)⁻¹ ∈ D := D.mul_mem hy₀D (D.inv_mem (D.pow_mem hxD j))
  have hy1 : y₀ * (x ^ j)⁻¹ ≠ 1 := by
    intro h1
    apply hy₀x
    rw [mul_inv_eq_one.mp h1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j
  have htAD : B * (A ^ j)⁻¹ ∈ AD := AD.mul_mem hBAD (AD.inv_mem (AD.pow_mem hAAD j))
  have ht5 : (B * (A ^ j)⁻¹) ^ 5 = 1 := hAD5 _ htAD
  have hwt : Units.map Φ.toMonoidHom (w₀ * (a ^ j)⁻¹) = B * (A ^ j)⁻¹ := by
    rw [map_mul, map_inv, map_pow, has, hw₀s]
  have hwU : w₀ * (a ^ j)⁻¹ ∈ unitaryOf hτ :=
    (unitaryOf hτ).mul_mem hw₀U ((unitaryOf hτ).inv_mem ((unitaryOf hτ).pow_mem haU j))
  have hwc : ((w₀ * (a ^ j)⁻¹ : (PiMat E e)ˣ) : PiMat E e) c = 1 := by
    have h1 : ((a ^ j : (PiMat E e)ˣ) : PiMat E e) c = (w₀ : PiMat E e) c := by
      rw [Units.val_pow_eq_pow_val, Pi.pow_apply, hα, hβ, ← map_pow, hj]
    rw [Units.val_mul, Pi.mul_apply, ← h1, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Pi.one_apply]
  have hfix := FieldFiveSp.fix_of_coord_eq_one (Φ := Φ) hτ hπ (Sf := Sf) hwU hwc
  rw [hwt] at hfix
  obtain ⟨K', hK', hJK', h5K', hK'w⟩ :=
    exists_fixedCore_component_su h hn hker hyt ht5 hSq hSU fun M hM => hfix M hM
  rw [← hJeq'] at hJK'
  have hst : A * (B * (A ^ j)⁻¹) = (B * (A ^ j)⁻¹) * A := hcommAD A hAAD _ htAD
  obtain ⟨hnm, hcentK⟩ := hK'w x A hA hA5 hst
  have hxK : x ∉ Subgroup.centralizer (K' : Set G) := by
    intro hxK
    have hfx := hcentK hxK
    have hT1 : ∀ γ ∈ coreOf π hτ Sf c, γ = 1 := by
      intro γ hγ
      have h1 := (hfx _ ⟨γ, hγ, rfl⟩).2
      have hγΦ : ((Units.map Φ.toMonoidHom γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          Φ (γ : PiMat E e) := rfl
      have hAΦ : (A : Matrix (Fin n) (Fin n) K) = Φ (a : PiMat E e) := by rw [← has]; rfl
      rw [hγΦ, hAΦ, ← map_one Φ, ← map_sub, ← map_mul] at h1
      have h2 := congrFun (hΦ h1) c
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply] at h2
      rw [hα] at h2
      have hg1 : coordHom E e c γ = 1 :=
        LinNonsplit.eq_one_of_mul_scalar_sub_one hα1 (by rw [coe_coordHom]; exact h2)
      exact coordHom_injOn hτ hπ (Subgroup.mem_inf.mp hγ).2 (Subgroup.one_mem _)
        (by rw [hg1, map_one])
    obtain ⟨a₁, a₂, haa⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hSq
    have h1 : a₁ = 1 := by
      obtain ⟨γ, hγ, hγa⟩ := a₁.2
      apply Subtype.ext
      rw [← hγa, hT1 γ hγ, map_one]
      rfl
    exact haa (by rw [h1, one_mul, mul_one])
  exact ⟨_, hyD, hy1, K', hK', hJK', h5K', hxK, hnm⟩

end Main

end FieldFiveSU

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits InnerDiagSU CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem ggFieldFiveNbrTag_PSU : GGFieldFiveNbrTag .PSU := by
  intro G _ _ n
  have hf : 1 ≤ 1 := le_rfl
  have hU : ggU .PSU n 1 =
      ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 1 hf) n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [hU]
  intro ψ G₀ hpres D hDel hDcard _ hDdiag x hxD L hL hLmark J hJ
  obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  have hn : 4 ≤ n := by
    have : 2 ≤ n / 2 := hrk
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange] at hL ⊢
  have hF : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := card_galoisField_two_mul 2 1 hf
  have h : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
    ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Finite (GaloisField 2 (2 * 1)) := h.finite
  have : CharP (GaloisField 2 (2 * 1)) 2 := h.charP
  obtain ⟨P, hP⟩ := exists_wittMatrix hF (m + 1)
  have hSU : SUid (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) (m + 1) =
      unitarySU 2 1 (GaloisField 2 (2 * 1)) (m + 1) := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  set ψ₁ := ψ.comp Φ.symm.toMonoidHom with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SUTorus.range_comp_symm ψ Φ
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 1 (GaloisField 2 (2 * 1)) (m + 1)) :=
    SUTorus.ker_comp_symm_le hker Φ
  have hpair : ∀ z : G, GGPsiInnerDiag (Unitary.rootDatum (card_galoisField_two_mul 2 1 hf)
      (m + 1)) ψ z → ∃ C, (z, C) ∈ SUTorus.suPairs ψ₁ := by
    intro z hz
    obtain ⟨A, hA, hAc⟩ := suInnerDiagConj hF hn G ψ hker z hz
    have h1 : (z⁻¹, P * A * P⁻¹) ∈ SUTorus.suPairs ψ₁ :=
      SUTorus.mem_suPairs_transfer P hP hSU hA fun u => by
        rw [inv_inv]
        exact hAc u
    refine ⟨(P * A * P⁻¹)⁻¹, ?_⟩
    have h2 := (SUTorus.suPairs ψ₁).inv_mem h1
    rwa [Prod.inv_mk, inv_inv] at h2
  rw [← hr₁] at hL ⊢
  exact FieldFiveSU.fieldFive_su h hn hker₁ hDel hDcard (fun d hd => hpair d (hDdiag d hd)) hxD
    hL hLmark hJ

theorem ggSixFieldFiveInput_of_rest_PSU (hPlus : GGFieldFiveNbrTag .POmegaPlus)
    (hMinus : GGFieldFiveNbrTag .POmegaMinus) (hE8 : GGFieldFiveNbrTag .E8)
    (hF4 : GGFieldFiveRankTag .F4) (hE6 : GGFieldFiveRankTag .E6) (hE7 : GGFieldFiveRankTag .E7)
    (hTwE6 : GGFieldFiveRankTag .twistedE6) : GGSixFieldFiveInput :=
  ggSixFieldFiveInput_of_rest ggFieldFiveNbrTag_PSU hPlus hMinus hE8 hF4 hE6 hE7 hTwE6

end Tag

end CFSG.StandardType
