module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame

public section

namespace CFSG.StandardType

namespace RootPlaneOm

open Matrix Module SUTB Multiplicative NoOffOm

open Classical

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

theorem exists_blockFrame (hA : GenMax B Γ p A) :
    ∃ (r : ℕ) (ι₀ : Multiplicative (Fin r → ZMod p) →* GL (Fin d) K)
      (U : Fin r → Submodule K (Fin d → K)),
      Function.Injective ι₀ ∧ ι₀.range = A ∧ (∀ i, NondegOn B (U i)) ∧ (∀ i, U i ≠ ⊥) ∧
        (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, B u v = 0) ∧
        (∀ (s : Fin r → ZMod p) (v : Fin d → K),
          glin (ι₀ (ofAdd s)) v = v ↔ ∀ j, s j ≠ 0 → v ∈ (U j).orthogonalBilin B) ∧
        ∀ (s : Fin r → ZMod p) i, ∀ u ∈ U i, glin (ι₀ (ofAdd s)) u ∈ U i := by
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
  have hUne : ∀ i, U i ≠ ⊥ := fun i => grng_ne_bot (hS.ne_one _ (hyS i))
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
  have hUperp : ∀ j, ∀ u ∈ U j, u ∈ (U j).orthogonalBilin (B) → u = 0 :=
    fun j u hu hu' => hUnd j u hu fun m hm => (Submodule.mem_orthogonalBilin.mp hu') m hm
  have hinj₁ : Function.Injective ι₁ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, toAdd s j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (toAdd.injective (funext hcon))
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (hUne j)
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
  refine ⟨r, A.subtype.comp ι₁, U, fun s t hst => hinj₁ (Subtype.ext hst), ?_, hUnd, hUne,
    hUorth, fun s v => hfix (ofAdd s) v, fun s i u hu => hUA i _ (ι₁ (ofAdd s)).2 u hu⟩
  ext c
  constructor
  · rintro ⟨s, rfl⟩
    exact (ι₁ s).2
  · intro hc
    obtain ⟨s, hs⟩ := hrange₁ c hc
    exact ⟨s, hs⟩

omit [Finite K] [CharP K 2] in
theorem suppLE_of_fix {r : ℕ} {ι₀ : Multiplicative (Fin r → ZMod p) →* GL (Fin d) K}
    {U : Fin r → Submodule K (Fin d → K)} (hnd : ∀ i, NondegOn B (U i)) (hne : ∀ i, U i ≠ ⊥)
    (horth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, B u v = 0)
    (hfix : ∀ (s : Fin r → ZMod p) (v : Fin d → K),
      glin (ι₀ (ofAdd s)) v = v ↔ ∀ j, s j ≠ 0 → v ∈ (U j).orthogonalBilin B)
    {s t : Fin r → ZMod p}
    (h : ∀ v, glin (ι₀ (ofAdd s)) v = v → glin (ι₀ (ofAdd t)) v = v) :
    ∀ j, t j ≠ 0 → s j ≠ 0 := by
  intro j hj
  by_contra hsj
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (hne j)
  have h1 : glin (ι₀ (ofAdd s)) u = u := by
    refine (hfix s u).mpr fun i hi => ?_
    refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
    exact horth i j (fun hij => hi (by rw [hij]; exact hsj)) m hm u hu
  have h2 := (hfix t u).mp (h u h1) j hj
  exact hu0 (hnd j u hu fun m hm => (Submodule.mem_orthogonalBilin.mp h2) m hm)

end Frame

section Dim

variable {K : Type} [Field K] {d : ℕ} {B : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K}

theorem finrank_add_finrank_orth {W : Submodule K (Fin d → K)} (hW : NondegOn B W) :
    finrank K W + finrank K (W.orthogonalBilin B) = d := by
  have h := Submodule.finrank_add_eq_of_isCompl
    (CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hW)
  rwa [Module.finrank_fin_fun] at h

theorem two_le_finrank (hB : ∀ v, B v v = 0) {W : Submodule K (Fin d → K)} (hW : NondegOn B W)
    (hne : W ≠ ⊥) : 2 ≤ finrank K W := by
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hne
  have h1 : 1 ≤ finrank K W := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hne
  by_contra h2
  have hW1 : finrank K W = 1 := by omega
  have hu' : (⟨u, hu⟩ : W) ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hspan := (finrank_eq_one_iff_of_nonzero' (⟨u, hu⟩ : W) hu').mp hW1
  refine hu0 (hW u hu fun m hm => ?_)
  obtain ⟨c, hc⟩ := hspan ⟨m, hm⟩
  have hm' : m = c • u := (congrArg Subtype.val hc).symm
  rw [hm', map_smul, LinearMap.smul_apply, hB u, smul_zero]

theorem mem_orth_sup_iff {X Y : Submodule K (Fin d → K)} {v : Fin d → K} :
    v ∈ (X ⊔ Y).orthogonalBilin B ↔ v ∈ X.orthogonalBilin B ∧ v ∈ Y.orthogonalBilin B := by
  simp only [Submodule.mem_orthogonalBilin]
  constructor
  · intro h
    exact ⟨fun n hn => h n (Submodule.mem_sup_left hn),
      fun n hn => h n (Submodule.mem_sup_right hn)⟩
  · rintro ⟨hX, hY⟩ n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hn
    rw [map_add, LinearMap.add_apply, hX a ha, hY b hb, add_zero]

theorem exists_pair_five {r : ℕ} (hr : 4 ≤ r) {U : Fin r → Submodule K (Fin d → K)}
    (hnd : ∀ i, NondegOn B (U i)) (horth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, B u v = 0)
    (hd : 9 ≤ d) :
    ∃ i j : Fin r, i ≠ j ∧ 5 ≤ finrank K ((U i ⊔ U j).orthogonalBilin B) := by
  set i₀ : Fin r := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin r := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin r := ⟨2, by omega⟩ with hi₂
  set i₃ : Fin r := ⟨3, by omega⟩ with hi₃
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h23 : i₂ ≠ i₃ := by simp [hi₂, hi₃, Fin.ext_iff]
  have hne : ∀ a ∈ ({i₀, i₁} : Set (Fin r)), ∀ b ∈ ({i₂, i₃} : Set (Fin r)), a ≠ b := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hi₀, hi₁, hi₂, hi₃, Fin.ext_iff]
  have hsupnd : ∀ i j, i ≠ j → NondegOn B (U i ⊔ U j) := fun i j hij =>
    nondegOn_sup (hnd i) (hnd j) fun u hu v hv => ⟨horth j i (Ne.symm hij) u hu v hv,
      horth i j hij v hv u hu⟩
  have hXY : ∀ x ∈ U i₀ ⊔ U i₁, ∀ y ∈ U i₂ ⊔ U i₃, B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add, LinearMap.add_apply]
    rw [horth _ _ (hne _ (Or.inl rfl) _ (Or.inl rfl)) a ha a' ha',
      horth _ _ (hne _ (Or.inl rfl) _ (Or.inr rfl)) a ha b' hb',
      horth _ _ (hne _ (Or.inr rfl) _ (Or.inl rfl)) b hb a' ha',
      horth _ _ (hne _ (Or.inr rfl) _ (Or.inr rfl)) b hb b' hb']
    simp
  have hinf : (U i₀ ⊔ U i₁) ⊓ (U i₂ ⊔ U i₃) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
    exact hsupnd i₀ i₁ h01 v hv.1 fun n hn => hXY n hn v hv.2
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq (U i₀ ⊔ U i₁) (U i₂ ⊔ U i₃)
  rw [hinf, finrank_bot, add_zero] at hfr
  have hle : finrank K ↥((U i₀ ⊔ U i₁) ⊔ (U i₂ ⊔ U i₃)) ≤ d := by
    have := Submodule.finrank_le ((U i₀ ⊔ U i₁) ⊔ (U i₂ ⊔ U i₃))
    rwa [Module.finrank_fin_fun] at this
  have hX' := finrank_add_finrank_orth (hsupnd i₀ i₁ h01)
  have hY' := finrank_add_finrank_orth (hsupnd i₂ i₃ h23)
  by_cases h5 : 5 ≤ finrank K ((U i₀ ⊔ U i₁).orthogonalBilin B)
  · exact ⟨i₀, i₁, h01, h5⟩
  · exact ⟨i₂, i₃, h23, by omega⟩

end Dim

end RootPlaneOm

end CFSG.StandardType
