module

public import CFSG.Quasithin.H13.U3S1347S
public import CFSG.Quasithin.Background.VolIG53
public import CFSG.Quasithin.H13.U3S1347K

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

@[expose] def addRepQ {Q : Type*} [Group Q] {V : Type} [CommGroup V] (σ : Q →* MulAut V) :
    Q →* AddMonoid.End (Additive V) where
  toFun g := L32Mod.addEnd (σ g)
  map_one' := by
    ext m
    simp [L32Mod.addEnd]
    rfl
  map_mul' g h := by
    ext m
    simp [L32Mod.addEnd, map_mul]
    rfl

theorem addRepQ_apply {Q : Type*} [Group Q] {V : Type} [CommGroup V] (σ : Q →* MulAut V)
    (g : Q) (m : Additive V) :
    addRepQ σ g m = Additive.ofMul (σ g (Additive.toMul m)) := rfl

@[expose] def phiA6 : ↥(alternatingGroup (Fin 6)) →* ↥(alternatingGroup (Fin 6)) where
  toFun g := ⟨S6Out.phi g, S6Out.phi_mem_alternatingGroup g.2⟩
  map_one' := Subtype.ext (map_one S6Out.phi)
  map_mul' g h := Subtype.ext (map_mul S6Out.phi (g : Perm (Fin 6)) h)

theorem phiEquiv_symm_mem {σ : Perm (Fin 6)} (h : σ ∈ alternatingGroup (Fin 6)) :
    S6Out.phiEquiv.symm σ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, ← S6Out.sign_phi]
  show Perm.sign (S6Out.phiEquiv (S6Out.phiEquiv.symm σ)) = 1
  rw [MulEquiv.apply_symm_apply]
  exact h

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_gen {K V N : Subgroup G} {y : G}
    (hgen : V = closure (Set.range fun k : ↥K => (k : G) * y * (k : G)⁻¹))
    (hN : ∀ k : ↥K, (k : G) * y * (k : G)⁻¹ ∈ N) : V ≤ N := by
  rw [hgen, closure_le]
  rintro _ ⟨k, rfl⟩
  exact hN k

theorem exists_top_map {K V : Subgroup G} [IsMulCommutative ↥V]
    (hV2 : ∀ v ∈ V, v * v = 1) (hKV : K ≤ normalizer (V : Set G))
    (θ : ↥K →* ↥(alternatingGroup (Fin 6))) (hθ : Function.Surjective θ)
    (hθker : ∀ k : ↥K, θ k = 1 → (k : G) ∈ centralizer (V : Set G))
    {y : G} (hy : y ∈ V)
    (hgen : V = closure (Set.range fun k : ↥K => (k : G) * y * (k : G)⁻¹))
    (hfix : ∀ k : ↥K, (θ k : Perm (Fin 6)) ∈ P2sub → (k : G) * y = y * k)
    (hmove : ∃ k : ↥K, (k : G) * y ≠ y * k) :
    ∃ F : ↥V →* ↥W4, Function.Surjective F ∧
      (∀ (k : ↥K) (v : ↥V), F (conjAct V ⟨k, hKV k.2⟩ v) =
        act4 (S6Out.phiEquiv.symm (θ k)) (F v)) ∧
      ((F ⟨y, hy⟩ : ↥W4) : P6) = dv 4 5 := by
  let c : ↥K →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hKV)
  have hc : ∀ (k : ↥K) (v : ↥V), ((c k v : ↥V) : G) = k * v * (k : G)⁻¹ := fun k v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ v
  have hle : θ.ker ≤ c.ker := by
    intro k hk
    have hkC := hθker k hk
    rw [MonoidHom.mem_ker]
    ext v
    rw [hc]
    show (k : G) * v * (k : G)⁻¹ = v
    rw [← mem_centralizer_iff.1 hkC v v.2, mul_inv_cancel_right]
  let σy : ↥(alternatingGroup (Fin 6)) →* MulAut ↥V := (QuotientGroup.lift θ.ker c hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm.toMonoidHom
  have hσy : ∀ k : ↥K, σy (θ k) = c k := by
    intro k
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm (θ k) =
        (k : ↥K ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  let pre : ↥K → ↥(alternatingGroup (Fin 6)) := fun k =>
    ⟨S6Out.phiEquiv.symm (θ k), phiEquiv_symm_mem (θ k).2⟩
  have hpre : ∀ k : ↥K, phiA6 (pre k) = θ k := fun k =>
    Subtype.ext (S6Out.phiEquiv.apply_symm_apply _)
  let ρ' := addRepQ (σy.comp phiA6)
  have hρ'c : ∀ (k : ↥K) (v : ↥V), ρ' (pre k) (Additive.ofMul v) = Additive.ofMul (c k v) := by
    intro k v
    rw [addRepQ_apply, MonoidHom.comp_apply, hpre, hσy]
    rfl
  have h2 : ∀ m : Additive ↥V, m + m = 0 := by
    intro m
    have : Additive.toMul m * Additive.toMul m = 1 :=
      Subtype.ext (hV2 _ (Additive.toMul m).2)
    exact congrArg Additive.ofMul this
  have hx : ∀ g : ↥(alternatingGroup (Fin 6)), (g : Perm (Fin 6)) ∈ P1sub →
      ρ' g (Additive.ofMul ⟨y, hy⟩) = Additive.ofMul ⟨y, hy⟩ := by
    intro g hg
    obtain ⟨k, hk⟩ := hθ (phiA6 g)
    have hkP : (θ k : Perm (Fin 6)) ∈ P2sub := by
      rw [hk]
      exact S6Out.phi_P1 _ hg
    rw [addRepQ_apply, MonoidHom.comp_apply, ← hk, hσy]
    congr 1
    apply Subtype.ext
    rw [hc]
    show (k : G) * y * (k : G)⁻¹ = y
    rw [hfix k hkP, mul_inv_cancel_right]
  have hnf : ∃ g, ρ' g (Additive.ofMul ⟨y, hy⟩) ≠ Additive.ofMul ⟨y, hy⟩ := by
    obtain ⟨k, hk⟩ := hmove
    refine ⟨pre k, fun h => hk ?_⟩
    rw [hρ'c] at h
    have h1 := congrArg Subtype.val (Additive.ofMul.injective h)
    rw [hc] at h1
    have := congrArg (· * (k : G)) h1
    simpa using this
  have hspan : AddSubgroup.closure (Set.range fun g => ρ' g (Additive.ofMul ⟨y, hy⟩)) = ⊤ := by
    set N := AddSubgroup.closure (Set.range fun g => ρ' g (Additive.ofMul ⟨y, hy⟩))
    have hle' : V ≤ (AddSubgroup.toSubgroup' N).map V.subtype := by
      refine le_of_gen hgen fun k => ?_
      refine ⟨c k ⟨y, hy⟩, ?_, hc k ⟨y, hy⟩⟩
      show Additive.ofMul (c k ⟨y, hy⟩) ∈ N
      rw [← hρ'c]
      exact AddSubgroup.subset_closure ⟨pre k, rfl⟩
    refine eq_top_iff.2 fun m _ => ?_
    obtain ⟨n, hn, hnm⟩ := hle' (Additive.toMul m).2
    have : n = Additive.toMul m := Subtype.ext hnm
    rw [this] at hn
    exact hn
  obtain ⟨f, hfs, hfe⟩ := VolI.AS_I_G_5_3_top_holds (Additive ↥V) ρ' h2 _ hx hnf hspan
  let F : ↥V →* ↥W4 :=
    { toFun := fun v => Additive.toMul (f (Additive.ofMul v))
      map_one' := by simp
      map_mul' := fun v w => by simp [ofMul_mul] }
  have hF : ∀ v, F v = Additive.toMul (f (Additive.ofMul v)) := fun _ => rfl
  have hFe : ∀ (k : ↥K) (v : ↥V), F (conjAct V ⟨k, hKV k.2⟩ v) =
      act4 (S6Out.phiEquiv.symm (θ k)) (F v) := by
    intro k v
    have h1 := hfe (pre k) (Additive.ofMul v)
    rw [hρ'c] at h1
    rw [hF, hF]
    exact congrArg Additive.toMul h1
  have hFs : Function.Surjective F := fun w => by
    obtain ⟨m, hm⟩ := hfs (Additive.ofMul w)
    exact ⟨Additive.toMul m, by rw [hF]; simpa using congrArg Additive.toMul hm⟩
  refine ⟨F, hFs, hFe, ?_⟩
  have hfixF : ∀ g : ↥(alternatingGroup (Fin 6)), (g : Perm (Fin 6)) ∈ P1sub →
      act4 (g : Perm (Fin 6)) (F ⟨y, hy⟩) = F ⟨y, hy⟩ := by
    intro g hg
    have h1 := hfe g (Additive.ofMul ⟨y, hy⟩)
    rw [hx g hg] at h1
    rw [hF]
    exact (congrArg Additive.toMul h1).symm
  have ha : swap (2 : Fin 6) 3 * swap 4 5 ∈ alternatingGroup (Fin 6) :=
    Perm.mem_alternatingGroup.2 (by decide)
  have hb : swap (1 : Fin 6) 2 * swap 4 5 ∈ alternatingGroup (Fin 6) :=
    Perm.mem_alternatingGroup.2 (by decide)
  have h1 := hfixF ⟨_, ha⟩ (show swap (2 : Fin 6) 3 * swap 4 5 ∈ P1sub from
    mem_P1sub.2 (by decide))
  have h2' := hfixF ⟨_, hb⟩ (show swap (1 : Fin 6) 2 * swap 4 5 ∈ P1sub from
    mem_P1sub.2 (by decide))
  rcases fix_P1_gens _ (F ⟨y, hy⟩).2 (congrArg Subtype.val h1) (congrArg Subtype.val h2')
    with h0 | h0
  · exfalso
    have hF1 : F ⟨y, hy⟩ = 1 := Subtype.ext h0
    have hall' : V ≤ (F.ker).map V.subtype := by
      refine le_of_gen hgen fun k => ⟨c k ⟨y, hy⟩, ?_, hc k ⟨y, hy⟩⟩
      show F (c k ⟨y, hy⟩) = 1
      have := hFe k ⟨y, hy⟩
      rw [hF1, map_one] at this
      exact this
    have hall : ∀ v : ↥V, F v = 1 := by
      intro v
      obtain ⟨v', hv', hvv'⟩ := hall' v.2
      have : v' = v := Subtype.ext hvv'
      rw [← this]
      exact hv'
    obtain ⟨v, hv⟩ := hFs ⟨dv 4 5, dv_mem 4 5⟩
    rw [hall v] at hv
    exact absurd (congrArg Subtype.val hv) (by decide)
  · exact h0

omit [Finite G] in
theorem eq_of_gen {K V : Subgroup G} (hKV : K ≤ normalizer (V : Set G)) {y : G} (hy : y ∈ V)
    (hgen : V = closure (Set.range fun k : ↥K => (k : G) * y * (k : G)⁻¹))
    (s : ↥K → MulAut ↥W4) {F₁ F₂ : ↥V →* ↥W4}
    (h₁ : ∀ (k : ↥K) (v : ↥V), F₁ (conjAct V ⟨k, hKV k.2⟩ v) = s k (F₁ v))
    (h₂ : ∀ (k : ↥K) (v : ↥V), F₂ (conjAct V ⟨k, hKV k.2⟩ v) = s k (F₂ v))
    (hy₁₂ : F₁ ⟨y, hy⟩ = F₂ ⟨y, hy⟩) : F₁ = F₂ := by
  have hle : V ≤ (MonoidHom.eqLocus F₁ F₂).map V.subtype := by
    refine le_of_gen hgen fun k => ⟨conjAct V ⟨k, hKV k.2⟩ ⟨y, hy⟩, ?_,
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _⟩
    show F₁ _ = F₂ _
    rw [h₁, h₂, hy₁₂]
  refine MonoidHom.ext fun v => ?_
  obtain ⟨v', hv', hvv'⟩ := hle v.2
  have : v' = v := Subtype.ext hvv'
  rw [← this]
  exact hv'

omit [Finite G] in
theorem top_map_conj {K V : Subgroup G} (hKV : K ≤ normalizer (V : Set G))
    (θ : ↥K →* ↥(alternatingGroup (Fin 6))) {y : G} (hy : y ∈ V)
    (hgen : V = closure (Set.range fun k : ↥K => (k : G) * y * (k : G)⁻¹))
    {F : ↥V →* ↥W4}
    (hFe : ∀ (k : ↥K) (v : ↥V), F (conjAct V ⟨k, hKV k.2⟩ v) =
      act4 (S6Out.phiEquiv.symm (θ k)) (F v))
    (hFy : ((F ⟨y, hy⟩ : ↥W4) : P6) = dv 4 5)
    {t : G} (htV : t ∈ normalizer (V : Set G)) (htK : t ∈ normalizer (K : Set G))
    (hty : t * y = y * t) {τ : Perm (Fin 6)} (hτ : InD6 τ)
    (hθt : ∀ k : ↥K, ((θ ⟨t * k * t⁻¹, (mem_normalizer_iff.1 htK k).1 k.2⟩ :
      ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = τ * θ k * τ⁻¹)
    (v : ↥V) : F (conjAct V ⟨t, htV⟩ v) = act4 (S6Out.phiEquiv.symm τ) (F v) := by
  set s : MulAut ↥W4 := act4 (S6Out.phiEquiv.symm τ) with hs
  let F₂ : ↥V →* ↥W4 := (s⁻¹ : MulAut ↥W4).toMonoidHom.comp
    (F.comp (conjAct V ⟨t, htV⟩).toMonoidHom)
  have hF₂ : ∀ v, F₂ v = s⁻¹ (F (conjAct V ⟨t, htV⟩ v)) := fun _ => rfl
  have hconj : ∀ (k : ↥K) (v : ↥V), conjAct V ⟨t, htV⟩ (conjAct V ⟨k, hKV k.2⟩ v) =
      conjAct V ⟨t * k * t⁻¹, hKV ((mem_normalizer_iff.1 htK k).1 k.2)⟩
        (conjAct V ⟨t, htV⟩ v) := by
    intro k v
    apply Subtype.ext
    rw [conjAct_val, conjAct_val, conjAct_val, conjAct_val]
    group
  have h₂ : ∀ (k : ↥K) (v : ↥V), F₂ (conjAct V ⟨k, hKV k.2⟩ v) =
      act4 (S6Out.phiEquiv.symm (θ k)) (F₂ v) := by
    intro k v
    rw [hF₂, hF₂, hconj]
    have h1 := hFe ⟨t * k * t⁻¹, (mem_normalizer_iff.1 htK k).1 k.2⟩ (conjAct V ⟨t, htV⟩ v)
    rw [h1, hθt, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rw [hs]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  have hsy : s (F ⟨y, hy⟩) = F ⟨y, hy⟩ := by
    apply Subtype.ext
    show act4f (S6Out.phiEquiv.symm τ) (F ⟨y, hy⟩ : P6) = (F ⟨y, hy⟩ : P6)
    rw [hFy, S6Out.phi_inv_eq]
    exact (fix_dv45_iff _).2 (S6Out.phi_inv_D6 τ hτ)
  have hy₂ : F₂ ⟨y, hy⟩ = F ⟨y, hy⟩ := by
    have hty' : conjAct V ⟨t, htV⟩ ⟨y, hy⟩ = ⟨y, hy⟩ :=
      Subtype.ext (by rw [conjAct_val, hty, mul_inv_cancel_right])
    rw [hF₂, hty', MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact hsy.symm
  have hF₂F := eq_of_gen hKV hy hgen (fun k => act4 (S6Out.phiEquiv.symm (θ k))) h₂ hFe hy₂
  have h3 := DFunLike.congr_fun hF₂F v
  rw [hF₂, MulAut.inv_apply, MulEquiv.symm_apply_eq] at h3
  exact h3

end CFSG.Quasithin.H13.U3
