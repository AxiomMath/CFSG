module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGen
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaMono

public section

namespace CFSG.StandardType

namespace NoOffOm

open Matrix Module SUTB Multiplicative

section GenPieceSet

open Classical

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

structure GenPieceSet (B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K)
    (A : Subgroup (GL (Fin d) K)) (S : Finset (GL (Fin d) K)) : Prop where
  mem : ∀ y ∈ S, y ∈ A
  ne_one : ∀ y ∈ S, y ≠ 1
  orth : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → ∀ u ∈ grng y, ∀ v ∈ grng y', B u v = 0
  cyc : ∀ y ∈ S, ∀ c ∈ A, ∃ k : ℕ, ∀ u ∈ grng y, glin c u = glin (y ^ k) u

noncomputable abbrev genPieceSpan (S : Finset (GL (Fin d) K)) : Submodule K (Fin d → K) :=
  ⨆ y ∈ S, grng y

omit [Finite K] [CharP K 2] in
theorem GenPieceSet.mono {S S' : Finset (GL (Fin d) K)} (hS : GenPieceSet B A S)
    (hS' : S' ⊆ S) : GenPieceSet B A S' where
  mem y hy := hS.mem y (hS' hy)
  ne_one y hy := hS.ne_one y (hS' hy)
  orth y hy y' hy' := hS.orth y (hS' hy) y' (hS' hy')
  cyc y hy := hS.cyc y (hS' hy)

omit [Finite K] [CharP K 2] in
theorem orth_genPieceSpan (hB : B.IsSymm) {S : Finset (GL (Fin d) K)} {y : GL (Fin d) K}
    (hS : GenPieceSet B A (insert y S)) (hyS : y ∉ S) :
    ∀ u ∈ grng y, ∀ v ∈ genPieceSpan S, B u v = 0 ∧ B v u = 0 := by
  intro u hu v hv
  have hle : genPieceSpan S ≤ LinearMap.ker (B u) := by
    refine iSup₂_le fun y' hy' => ?_
    intro w hw
    exact hS.orth y (Finset.mem_insert_self y S) y' (Finset.mem_insert_of_mem hy')
      (fun e => hyS (e ▸ hy')) u hu w hw
  have h1 : B u v = 0 := hle hv
  refine ⟨h1, ?_⟩
  rw [← hB.eq u v, h1, map_zero]

theorem GenPieceSet.nondegOn_card (hA : GenMax B Γ p A) {S : Finset (GL (Fin d) K)}
    (hS : GenPieceSet B A S) :
    NondegOn B (genPieceSpan S) ∧ S.card ≤ finrank K (genPieceSpan S) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp⟩
    have : genPieceSpan (∅ : Finset (GL (Fin d) K)) = ⊥ := by simp
    rw [this]
    exact fun _ hm _ => (Submodule.mem_bot K).mp hm
  | insert y S hyS ih =>
    obtain ⟨hX, hcard⟩ := ih (hS.mono (Finset.subset_insert y S))
    have hsp : genPieceSpan (insert y S) = genPieceSpan S ⊔ grng y := by
      rw [genPieceSpan, Finset.iSup_insert, sup_comm]
    have hyA : y ∈ A := hS.mem y (Finset.mem_insert_self y S)
    have hU : NondegOn B (grng y) := nondegOn_grng hA hyA
    have horth := orth_genPieceSpan hA.symm hS hyS
    have hX' : NondegOn B (genPieceSpan S ⊔ grng y) := SUTB.nondegOn_sup hX hU horth
    rw [hsp]
    refine ⟨hX', ?_⟩
    have hinf : genPieceSpan S ⊓ grng y = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun v hv => hX v hv.1 fun m hm => ?_
      exact (horth v hv.2 m hm).2
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (genPieceSpan S) (grng y)
    rw [hinf, finrank_bot, add_zero] at hfr
    have hpos : 0 < finrank K (grng y) := by
      rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      exact grng_ne_bot (hS.ne_one y (Finset.mem_insert_self y S))
    rw [Finset.card_insert_of_notMem hyS, hfr]
    omega

theorem GenPieceSet.exists_insert (hA : GenMax B Γ p A) {S : Finset (GL (Fin d) K)}
    (hS : GenPieceSet B A S) (hne : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ genPieceSpan S, glin c v = v) :
    ∃ y, y ∉ S ∧ GenPieceSet B A (insert y S) := by
  obtain ⟨y, hy⟩ := exists_genIsPiece hA hne
  have hyS : y ∉ S := by
    intro hyS
    apply grng_ne_bot hy.ne_one
    refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
    have hle : grng y ≤ genPieceSpan S := le_iSup₂ (f := fun y _ => grng y) y hyS
    exact eq_zero_of_mem_grng hA hy.mem hu (hy.triv u (hle hu))
  have horth := grng_orth_of_triv hA hy.mem hy.triv
  have hle : ∀ y' ∈ S, grng y' ≤ genPieceSpan S := fun y' hy' =>
    le_iSup₂ (f := fun y _ => grng y) y' hy'
  refine ⟨y, hyS, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.mem
    · exact hS.mem y' hy'
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.ne_one
    · exact hS.ne_one y' hy'
  · intro y₁ hy₁ y₂ hy₂ hne₁₂ u hu v hv
    rcases Finset.mem_insert.mp hy₁ with rfl | h₁ <;>
      rcases Finset.mem_insert.mp hy₂ with rfl | h₂
    · exact absurd rfl hne₁₂
    · exact (horth u hu v (hle y₂ h₂ hv)).1
    · exact (horth v hv u (hle y₁ h₁ hu)).2
    · exact hS.orth y₁ h₁ y₂ h₂ hne₁₂ u hu v hv
  · intro y' hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact hy.cyc
    · exact hS.cyc y' hy'

theorem exists_terminal_genPieceSet (hA : GenMax B Γ p A) :
    ∃ S, GenPieceSet B A S ∧ ∀ c ∈ A, (∀ v ∈ genPieceSpan S, glin c v = v) → c = 1 := by
  set P : ℕ → Prop := fun k => ∃ S, GenPieceSet B A S ∧ S.card = k with hP
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp, by simp, by simp⟩, rfl⟩
  have hbound : ∀ k, P k → k ≤ d := by
    rintro k ⟨S, hS, rfl⟩
    have h1 := (hS.nondegOn_card hA).2
    have h2 := Submodule.finrank_le (genPieceSpan S)
    rw [Module.finrank_fin_fun] at h2
    omega
  set m := Nat.findGreatest P d with hm
  obtain ⟨S, hS, hSm⟩ : P m := Nat.findGreatest_spec (Nat.zero_le d) hP0
  refine ⟨S, hS, fun c hc htriv => ?_⟩
  by_contra hc1
  obtain ⟨y, hyS, hyS'⟩ := hS.exists_insert hA ⟨c, hc, hc1, htriv⟩
  have hPm : P (m + 1) := ⟨_, hyS', by rw [Finset.card_insert_of_notMem hyS, hSm]⟩
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self m) (hbound _ hPm) hPm

end GenPieceSet

section GenFrame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

@[expose] def genFixOn (d : ℕ) (K : Type) [Field K] (W : Set (Fin d → K)) :
    Subgroup (GL (Fin d) K) where
  carrier := {c | ∀ u ∈ W, glin c u = u}
  mul_mem' {c c'} hc hc' u hu := by
    rw [glin_mul, Module.End.mul_apply, hc' u hu, hc u hu]
  one_mem' u _ := by rw [glin_one]; rfl
  inv_mem' {c} hc u hu := by
    have h1 := glin_inv_apply c u
    rwa [hc u hu] at h1

omit [Finite K] [CharP K 2] in
theorem mem_genFixOn {W : Set (Fin d → K)} {c : GL (Fin d) K} :
    c ∈ genFixOn d K W ↔ ∀ u ∈ W, glin c u = u :=
  Iff.rfl

omit [Finite K] in
theorem eq_zero_of_pow_fix' (hA : GenMax B Γ p A)
    {y : GL (Fin d) K} (hy : y ∈ A) {k : ℕ} (hk : ¬ p ∣ k) {u : Fin d → K}
    (hu : u ∈ grng y) (hfix : glin (y ^ k) u = u) : u = 0 := by
  have hcop : Nat.Coprime k p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hA.prime).mpr hk)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hA.prime.one_lt
  have hiter : ∀ j : ℕ, glin (y ^ (k * j)) u = u := by
    intro j
    induction j with
    | zero => rw [Nat.mul_zero, pow_zero, glin_one]; rfl
    | succ j ih => rw [Nat.mul_succ, pow_add, glin_mul, Module.End.mul_apply, hfix, ih]
  have hy1 : y ^ (k * m) = y := by
    rw [pow_eq_pow_mod (k * m) (hA.pow y hy), hm, pow_one]
  have h1 := hiter m
  rw [hy1] at h1
  exact eq_zero_of_mem_grng hA hy hu h1

theorem exists_genPieceFrame (hA : GenMax B Γ p A) :
    ∃ (r : ℕ) (ι₀ : Multiplicative (Fin r → ZMod p) →* GL (Fin d) K),
      Function.Injective ι₀ ∧ ι₀.range = A ∧
        ∀ s s' : Fin r → ZMod p,
          ((∀ v, glin (ι₀ (ofAdd s')) v = v → glin (ι₀ (ofAdd s)) v = v) ↔ SuppLE s s') := by
  classical
  have : Fact p.Prime := ⟨hA.prime⟩
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  obtain ⟨S, hS, hterm⟩ := exists_terminal_genPieceSet hA
  set r := S.card with hr
  set e : Fin r ≃ ↥S := S.equivFin.symm with he
  set y : Fin r → GL (Fin d) K := fun i => (e i : GL (Fin d) K) with hy
  have hyS : ∀ i, y i ∈ S := fun i => (e i).2
  have hyA : ∀ i, y i ∈ A := fun i => hS.mem _ (hyS i)
  have hyinj : Function.Injective y := fun i j hij => e.injective (Subtype.ext hij)
  have hyS' : ∀ z ∈ S, ∃ i, y i = z := fun z hz =>
    ⟨e.symm ⟨z, hz⟩, by simp only [hy, Equiv.apply_symm_apply]⟩
  set U : Fin r → Submodule K (Fin d → K) := fun i => grng (y i) with hU
  have hUnd : ∀ i, NondegOn (B) (U i) := fun i => nondegOn_grng hA (hyA i)
  have hUA : ∀ i, ∀ a ∈ A, ∀ u ∈ U i, glin a u ∈ U i := fun i a ha => grng_inv hA (hyA i) ha
  have hUorth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, B u v = 0 :=
    fun i j hij => hS.orth _ (hyS i) _ (hyS j) (fun e' => hij (hyinj e'))
  have hUne : ∀ i, ∃ u ∈ U i, u ≠ 0 := fun i =>
    (Submodule.ne_bot_iff _).mp (grng_ne_bot (hS.ne_one _ (hyS i)))
  have hUperp : ∀ j, ∀ u ∈ U j, u ∈ (U j).orthogonalBilin (B) → u = 0 :=
    fun j u hu hu' => hUnd j u hu fun m hm => (Submodule.mem_orthogonalBilin.mp hu') m hm
  have hUsub : ∀ i j, i ≠ j → ∀ u ∈ U j, u ∈ (U i).orthogonalBilin (B) :=
    fun i j hij u hu => Submodule.mem_orthogonalBilin.mpr fun m hm => hUorth i j hij m hm u hu
  have hb : ∀ i, ∃ g ∈ A, (∀ w ∈ U i, glin g w = glin (y i) w) ∧
      ∀ v ∈ (U i).orthogonalBilin (B), glin g v = v :=
    fun i => hA.exists_mem_restrict (hUnd i) (hUA i) (hyA i)
  choose b hbA hbon hboff using hb
  have hbpow : ∀ j (k : ℕ), ∀ u ∈ U j, glin (b j ^ k) u = glin (y j ^ k) u := by
    intro j k
    induction k with
    | zero => intro u _; rw [pow_zero, pow_zero]
    | succ k ih =>
      intro u hu
      have hyk : glin (y j ^ k) u ∈ U j := hUA j _ (A.pow_mem (hyA j) k) u hu
      rw [pow_succ', glin_mul, Module.End.mul_apply, ih u hu, hbon j _ hyk, ← Module.End.mul_apply,
        ← glin_mul, ← pow_succ']
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a c => Subtype.ext (hA.comm _ a.2 _ c.2) }
  set bA : Fin r → A := fun i => ⟨b i, hbA i⟩ with hbA'
  have hbAp : ∀ i, bA i ^ p = 1 := fun i => Subtype.ext (hA.pow _ (hbA i))
  set ι₁ : Multiplicative (Fin r → ZMod p) →* A :=
    { toFun := fun s => ∏ i, bA i ^ (toAdd s i).val
      map_one' := by simp
      map_mul' := fun s s' => by
        simp only [toAdd_mul, Pi.add_apply]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [ZMod.val_add, ← pow_eq_pow_mod _ (hbAp i), pow_add] } with hι₁
  have hι₁_apply : ∀ s, ι₁ s = ∏ i, bA i ^ (toAdd s i).val := fun s => rfl
  have hact : ∀ (s : Multiplicative (Fin r → ZMod p)) j, ∀ u ∈ U j,
      glin ((ι₁ s : A) : GL (Fin d) K) u = glin (y j ^ (toAdd s j).val) u := by
    intro s j u hu
    have hrest : (∏ i ∈ Finset.univ.erase j, bA i ^ (toAdd s i).val) ∈
        (genFixOn d K (U j : Set (Fin d → K))).comap A.subtype := by
      refine Subgroup.prod_mem _ fun i hi => Subgroup.pow_mem _ ?_ _
      exact fun w hw => hboff i w (hUsub i j (Finset.ne_of_mem_erase hi) w hw)
    have hrest' : glin ((∏ i ∈ Finset.univ.erase j, bA i ^ (toAdd s i).val : A) :
        GL (Fin d) K) u = u := hrest u hu
    rw [hι₁_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Subgroup.coe_mul, glin_mul,
      Module.End.mul_apply, hrest', SubgroupClass.coe_pow, hbpow j _ u hu]
  have hfix : ∀ (s : Multiplicative (Fin r → ZMod p)) (v : Fin d → K),
      glin ((ι₁ s : A) : GL (Fin d) K) v = v ↔
        ∀ j, toAdd s j ≠ 0 → v ∈ (U j).orthogonalBilin (B) := by
    intro s v
    constructor
    · intro hv j hj
      set g : GL (Fin d) K := ((ι₁ s : A) : GL (Fin d) K) with hg
      set k := (toAdd s j).val with hk
      have hkp : ¬ p ∣ k := by
        intro hdvd
        apply hj
        rw [← ZMod.natCast_zmod_val (toAdd s j), ← hk]
        exact (ZMod.natCast_eq_zero_iff k p).mpr hdvd
      have hmaps : ∀ x ∈ U j, (glin (y j ^ k) - 1) x ∈ U j := fun x hx =>
        (U j).sub_mem (hUA j _ (A.pow_mem (hyA j) k) x hx) hx
      set φ : Module.End K ↥(U j) := (glin (y j ^ k) - 1).restrict hmaps with hφ
      have hφinj : Function.Injective φ := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨x, hx⟩ hx0
        have h1 : (glin (y j ^ k) - 1) x = 0 := congrArg Subtype.val hx0
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
        exact Subtype.ext (eq_zero_of_pow_fix' hA (hyA j) hkp hx h1)
      have hφsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.mp hφinj
      refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
      obtain ⟨⟨x, hx⟩, hxm⟩ := hφsurj ⟨m, hm⟩
      have hm' : m = glin g x - x := by
        have h1 : (glin (y j ^ k) - 1) x = m := by
          have h2 := congrArg Subtype.val hxm
          simpa only [hφ, LinearMap.restrict_apply] using h2
        rw [← h1, LinearMap.sub_apply, Module.End.one_apply, hg, hact s j x hx]
      change B m v = 0
      rw [hm', map_sub, LinearMap.sub_apply, ← hA.iso g (ι₁ s).2 x v, hv, sub_self]
    · intro hv
      have hmem : ∀ i, bA i ^ (toAdd s i).val ∈ (genFixOn d K {v}).comap A.subtype := by
        intro i
        by_cases hi : toAdd s i = 0
        · rw [hi, ZMod.val_zero, pow_zero]
          exact Subgroup.one_mem _
        · refine Subgroup.pow_mem _ ?_ _
          intro w hw
          rw [Set.mem_singleton_iff.mp hw]
          exact hboff i v (hv i hi)
      have h1 := Subgroup.prod_mem _ fun i (_ : i ∈ Finset.univ) => hmem i
      rw [← hι₁_apply] at h1
      exact h1 v rfl
  have hinj₁ : Function.Injective ι₁ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, toAdd s j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (toAdd.injective (funext hcon))
    obtain ⟨u, hu, hu0⟩ := hUne j
    have h1 : glin ((ι₁ s : A) : GL (Fin d) K) u = u := by
      rw [hs, OneMemClass.coe_one, glin_one]
      rfl
    exact hu0 (hUperp j u hu ((hfix s u).mp h1 j hj))
  have hrange₁ : ∀ c ∈ A, ∃ s, ((ι₁ s : A) : GL (Fin d) K) = c := by
    intro c hc
    have hk : ∀ j, ∃ k : ℕ, ∀ u ∈ U j, glin c u = glin (y j ^ k) u :=
      fun j => hS.cyc _ (hyS j) c hc
    choose k hk using hk
    refine ⟨ofAdd fun j => (k j : ZMod p), ?_⟩
    set g : GL (Fin d) K := ((ι₁ (ofAdd fun j => (k j : ZMod p)) : A) :
      GL (Fin d) K) with hg
    have hgA : g ∈ A := (ι₁ _).2
    have hag : ∀ j, ∀ u ∈ U j, glin g u = glin c u := by
      intro j u hu
      rw [hg, hact _ j u hu, hk j u hu, toAdd_ofAdd, ZMod.val_natCast,
        ← pow_eq_pow_mod _ (hA.pow _ (hyA j))]
    have hle : genPieceSpan S ≤ LinearMap.ker (glin (g⁻¹ * c) - 1) := by
      refine iSup₂_le fun z hz => ?_
      obtain ⟨j, rfl⟩ := hyS' z hz
      intro u hu
      have h1 : glin g⁻¹ (glin g u) = u := by
        rw [← Module.End.mul_apply, ← glin_mul, inv_mul_cancel, glin_one]
        rfl
      rw [LinearMap.mem_ker, LinearMap.sub_apply, glin_mul, Module.End.mul_apply, ← hag j u hu, h1,
        Module.End.one_apply, sub_self]
    have hc1 : g⁻¹ * c = 1 := hterm _ (A.mul_mem (A.inv_mem hgA) hc) fun v hv =>
      sub_eq_zero.mp (hle hv)
    exact (inv_mul_eq_one.mp hc1)
  refine ⟨r, A.subtype.comp ι₁, fun s t hst => hinj₁ (Subtype.ext hst), ?_, ?_⟩
  · ext c
    constructor
    · rintro ⟨s, rfl⟩
      exact (ι₁ s).2
    · intro hc
      obtain ⟨s, hs⟩ := hrange₁ c hc
      exact ⟨s, hs⟩
  · intro s s'
    change ((∀ v, glin ((ι₁ (ofAdd s') : A) : GL (Fin d) K) v = v →
      glin ((ι₁ (ofAdd s) : A) : GL (Fin d) K) v = v) ↔ SuppLE s s')
    constructor
    · intro himp j hj
      by_contra hj'
      obtain ⟨u, hu, hu0⟩ := hUne j
      have h1 : glin ((ι₁ (ofAdd s') : A) : GL (Fin d) K) u = u := by
        refine (hfix _ u).mpr fun i hi => hUsub i j (fun hij => hi ?_) u hu
        rw [hij]
        exact hj'
      exact hu0 (hUperp j u hu ((hfix _ u).mp (himp u h1) j hj))
    · intro hsupp v hv
      exact (hfix _ v).mpr fun j hj => (hfix _ v).mp hv j (hsupp j hj)

end GenFrame

end NoOffOm

end CFSG.StandardType
