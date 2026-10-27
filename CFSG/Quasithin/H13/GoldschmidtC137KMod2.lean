module

public import CFSG.Quasithin.H13.GoldschmidtC137KMod1
public import CFSG.Quasithin.Background.SmithB42Alt6Norm
public import CFSG.Quasithin.Background.B3ThreeChief

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3 CFSG.Quasithin.S143 CFSG.Quasithin.B42Alt6

theorem fixG_ut0 : fixG (actL 6 Mod.ut0) = ⊥ := by
  rcases (B3_1_1 (n := 6) (by norm_num)).2 (fixG (actL 6 Mod.ut0))
      (fun g hg v hv => isInv_fixG (actL 6 Mod.ut0) ⟨g, hg⟩ v hv) with h | h
  · exact h
  · exfalso
    obtain ⟨g, w, hw⟩ := exists_nontrivial_action (n := 6) (by norm_num)
    apply hw
    have : w ∈ fixG (actL 6 Mod.ut0) := by
      rw [h]
      exact Subgroup.mem_top w
    exact this g

theorem commG_ut0 : commG (actL 6 Mod.ut0) = ⊤ := by
  rcases (B3_1_1 (n := 6) (by norm_num)).2 (commG (actL 6 Mod.ut0))
      (fun g hg v hv => isInv_commG (actL 6 Mod.ut0) ⟨g, hg⟩ v hv) with h | h
  · exfalso
    obtain ⟨g, w, hw⟩ := exists_nontrivial_action (n := 6) (by norm_num)
    apply hw
    have h1 : actL 6 Mod.ut0 g w * w⁻¹ ∈ commG (actL 6 Mod.ut0) := mul_inv_mem_commG g w
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
  · exact h

theorem commG_u0 : commG (actL 6 Mod.u0) = ⊤ := by
  have hc := c0_mem_commG (n := 6) (by norm_num) (by norm_num)
  have hinv : ∀ g ∈ alternatingGroup (Fin 6), ∀ v ∈ (commG (actL 6 Mod.u0)).map (projU0 6),
      Mod.act 6 Mod.ut0 g v ∈ (commG (actL 6 Mod.u0)).map (projU0 6) := by
    rintro g hg _ ⟨c, hc', rfl⟩
    refine ⟨actL 6 Mod.u0 ⟨g, hg⟩ c, isInv_commG (actL 6 Mod.u0) ⟨g, hg⟩ c hc', ?_⟩
    rw [actL_apply]
    exact projU0_act g c
  rcases (B3_1_1 (n := 6) (by norm_num)).2 _ hinv with h | h
  · exfalso
    obtain ⟨g, w, hw⟩ := exists_nontrivial_action (n := 6) (by norm_num)
    apply hw
    obtain ⟨w', rfl⟩ := projU0_surjective w
    have h1 : actL 6 Mod.u0 g w' * w'⁻¹ ∈ commG (actL 6 Mod.u0) := mul_inv_mem_commG g w'
    have h2 : projU0 6 (actL 6 Mod.u0 g w' * w'⁻¹) ∈ (⊥ : Subgroup (Mod.V 6 Mod.ut0)) := by
      rw [← h]
      exact ⟨_, h1, rfl⟩
    rw [Subgroup.mem_bot, map_mul, map_inv, mul_inv_eq_one] at h2
    exact (projU0_act g.1 w').symm.trans h2
  · rw [eq_top_iff]
    intro w _
    obtain ⟨c, hcC, hcw⟩ : projU0 6 w ∈ (commG (actL 6 Mod.u0)).map (projU0 6) := by
      rw [h]
      trivial
    have hk : w * c⁻¹ ∈ (projU0 6).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcw, mul_inv_cancel]
    rcases projU0_ker (hn := by norm_num) hk with h' | h'
    · rw [mul_inv_eq_one] at h'
      rw [h']
      exact hcC
    · have : w = c0 6 (by norm_num) * c := by
        rw [← h']
        group
      rw [this]
      exact (commG (actL 6 Mod.u0)).mul_mem hc hcC

theorem act_mem_normalizer (k : Mod) (σ : Equiv.Perm (Fin 6)) :
    Mod.act 6 k σ ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (Mod.act 6 k) : Subgroup (MulAut (Mod.V 6 k))) :
        Set (MulAut (Mod.V 6 k))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨σ * γ * σ⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (alternatingGroup.normal (α := Fin 6)).conj_mem γ hγ σ
  · rintro ⟨γ, hγ, hγl⟩
    refine ⟨σ⁻¹ * γ * σ, ?_, ?_⟩
    · have := (alternatingGroup.normal (α := Fin 6)).conj_mem γ hγ σ⁻¹
      simpa using this
    · have h1 : Mod.act 6 k σ * Mod.act 6 k (σ⁻¹ * γ * σ) * (Mod.act 6 k σ)⁻¹ =
          Mod.act 6 k γ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      have h2 : Mod.act 6 k (σ⁻¹ * γ * σ) =
          (Mod.act 6 k σ)⁻¹ * Mod.act 6 k γ * Mod.act 6 k σ := by
        rw [← h1]
        group
      rw [h2, hγl]
      group

theorem n6ModEquiv_symm_act (σ : Equiv.Perm (Fin 6)) (v : Mod.V 6 Mod.ut0) :
    n6ModEquiv.symm (Mod.act 6 Mod.ut0 σ v) = n6Act σ (n6ModEquiv.symm v) := by
  apply n6ModEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  show _ = n6ToV (n6Act σ (n6ModEquiv.symm v))
  rw [n6ToV_act_perm]
  show _ = Mod.act 6 Mod.ut0 σ (n6ModEquiv (n6ModEquiv.symm v))
  rw [MulEquiv.apply_symm_apply]

theorem normalizer_alt_act_ut0 :
    ∀ g ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0) :
        Subgroup (MulAut (Mod.V 6 Mod.ut0))) : Set (MulAut (Mod.V 6 Mod.ut0))),
      ∃ σ, Mod.act 6 Mod.ut0 σ = g := by
  intro g hg
  let N : N6Model ((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0)) :=
    ⟨n6ModEquiv.symm, Mod.act 6 Mod.ut0, act_injective (by norm_num) Mod.ut0,
      n6ModEquiv_symm_act, rfl⟩
  have hS : ∀ s : Mod.V 6 Mod.ut0, s * s = 1 := fun s => by
    rw [← pow_two]
    exact V_sq _ _
  have hbij : Function.Bijective N.ρL := ⟨fun a b hab =>
    Subtype.ext (N.ρ_inj (congrArg Subtype.val hab)), N.ρL_surjective⟩
  exact N.le_range hS (MulEquiv.ofBijective N.ρL hbij).symm hg

theorem act_fixed_of_mem_ker {ε : Mod.V 6 Mod.u0} (hε : ε ∈ (projU0 6).ker) (γ : Gp 6) :
    Mod.act 6 Mod.u0 γ ε = ε := by
  rcases projU0_ker (hn := by norm_num) hε with rfl | rfl
  · exact map_one _
  · exact act_c0 γ

theorem eq_one_of_trivial_proj (ψ : MulAut (Mod.V 6 Mod.u0))
    (hψn : ψ ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.u0) :
        Subgroup (MulAut (Mod.V 6 Mod.u0))) : Set (MulAut (Mod.V 6 Mod.u0))))
    (hψ : ∀ w, projU0 6 (ψ w) = projU0 6 w) : ψ = 1 := by
  rw [Subgroup.mem_normalizer_iff] at hψn
  have hPinv : ∀ x, projU0 6 (ψ⁻¹ x) = projU0 6 x := fun x => by
    have := hψ (ψ⁻¹ x)
    rw [MulAut.apply_inv_self] at this
    exact this.symm
  have hcomm : ∀ γ ∈ alternatingGroup (Fin 6), ∀ w, ψ (Mod.act 6 Mod.u0 γ w) =
      Mod.act 6 Mod.u0 γ (ψ w) := by
    intro γ hγ w
    obtain ⟨γ', hγ', hγ'e⟩ := (hψn (Mod.act 6 Mod.u0 γ)).1 ⟨γ, hγ, rfl⟩
    have hact : Mod.act 6 Mod.ut0 γ' = Mod.act 6 Mod.ut0 γ := by
      refine MulEquiv.ext fun v => ?_
      obtain ⟨w', rfl⟩ := projU0_surjective v
      calc Mod.act 6 Mod.ut0 γ' (projU0 6 w') = projU0 6 (Mod.act 6 Mod.u0 γ' w') :=
            (projU0_act γ' w').symm
        _ = projU0 6 (ψ (Mod.act 6 Mod.u0 γ (ψ⁻¹ w'))) := by rw [hγ'e]; rfl
        _ = projU0 6 (Mod.act 6 Mod.u0 γ (ψ⁻¹ w')) := hψ _
        _ = Mod.act 6 Mod.ut0 γ (projU0 6 (ψ⁻¹ w')) := projU0_act γ _
        _ = Mod.act 6 Mod.ut0 γ (projU0 6 w') := by rw [hPinv]
    have hγγ' : γ' = γ := act_injective (by norm_num) Mod.ut0 hact
    rw [hγγ'] at hγ'e
    have h2 : ψ * Mod.act 6 Mod.u0 γ = Mod.act 6 Mod.u0 γ * ψ := by
      calc ψ * Mod.act 6 Mod.u0 γ = (ψ * Mod.act 6 Mod.u0 γ * ψ⁻¹) * ψ := by group
        _ = Mod.act 6 Mod.u0 γ * ψ := by rw [← hγ'e]
    exact congrArg (fun f : MulAut (Mod.V 6 Mod.u0) => f w) h2
  have hker : ∀ w, ψ w * w⁻¹ ∈ (projU0 6).ker := fun w => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψ w, mul_inv_cancel]
  let S : Subgroup (Mod.V 6 Mod.u0) := MonoidHom.eqLocus ψ.toMonoidHom (MonoidHom.id _)
  have hS : commG (actL 6 Mod.u0) ≤ S := by
    refine commOn_le fun g m _ => ?_
    have hε := hker m
    have hψm : ψ m = (ψ m * m⁻¹) * m := (inv_mul_cancel_right _ _).symm
    have e1 : ψ (actL 6 Mod.u0 g m * m⁻¹) = Mod.act 6 Mod.u0 g.1 (ψ m) * (ψ m)⁻¹ := by
      rw [map_mul, map_inv, ← hcomm g.1 g.2 m]
      rfl
    have e2 : Mod.act 6 Mod.u0 g.1 (ψ m) = (ψ m * m⁻¹) * Mod.act 6 Mod.u0 g.1 m := by
      conv_lhs => rw [hψm]
      rw [map_mul, act_fixed_of_mem_ker hε]
    show ψ (actL 6 Mod.u0 g m * m⁻¹) = actL 6 Mod.u0 g m * m⁻¹
    rw [e1, e2]
    show ψ m * m⁻¹ * Mod.act 6 Mod.u0 g.1 m * (ψ m)⁻¹ = Mod.act 6 Mod.u0 g.1 m * m⁻¹
    rw [mul_right_comm, mul_inv_cancel_comm, mul_comm]
  refine MulEquiv.ext fun w => ?_
  have hw : w ∈ S := hS (by rw [commG_u0]; trivial)
  exact hw

theorem exists_induced_aut (g : MulAut (Mod.V 6 Mod.u0))
    (hg : ∀ x ∈ (projU0 6).ker, g x ∈ (projU0 6).ker)
    (hg' : ∀ x ∈ (projU0 6).ker, g⁻¹ x ∈ (projU0 6).ker) :
    ∃ g' : MulAut (Mod.V 6 Mod.ut0), ∀ w, g' (projU0 6 w) = projU0 6 (g w) := by
  let φ₀ : Mod.V 6 Mod.u0 →* Mod.V 6 Mod.ut0 := (projU0 6).comp g.toMonoidHom
  let φ₁ : Mod.V 6 Mod.u0 →* Mod.V 6 Mod.ut0 := (projU0 6).comp (g⁻¹ : MulAut _).toMonoidHom
  let φ : Mod.V 6 Mod.ut0 →* Mod.V 6 Mod.ut0 :=
    MonoidHom.liftOfSurjective (projU0 6) projU0_surjective ⟨φ₀, fun x hx => hg x hx⟩
  let φ' : Mod.V 6 Mod.ut0 →* Mod.V 6 Mod.ut0 :=
    MonoidHom.liftOfSurjective (projU0 6) projU0_surjective ⟨φ₁, fun x hx => hg' x hx⟩
  have hφ : ∀ w, φ (projU0 6 w) = projU0 6 (g w) := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ₀, fun x hx => hg x hx⟩ w
  have hφ' : ∀ w, φ' (projU0 6 w) = projU0 6 (g⁻¹ w) := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ₁, fun x hx => hg' x hx⟩ w
  refine ⟨MonoidHom.toMulEquiv φ φ' ?_ ?_, hφ⟩
  · refine MonoidHom.ext fun v => ?_
    obtain ⟨w, rfl⟩ := projU0_surjective v
    show φ' (φ (projU0 6 w)) = projU0 6 w
    rw [hφ, hφ', MulAut.inv_apply_self]
  · refine MonoidHom.ext fun v => ?_
    obtain ⟨w, rfl⟩ := projU0_surjective v
    show φ (φ' (projU0 6 w)) = projU0 6 w
    rw [hφ', hφ, MulAut.apply_inv_self]

theorem mem_normalizer_of_conj_gc {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S) (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

theorem normalizer_preserves_ker {g : MulAut (Mod.V 6 Mod.u0)}
    (hg : g ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.u0) :
        Subgroup (MulAut (Mod.V 6 Mod.u0))) : Set (MulAut (Mod.V 6 Mod.u0)))) :
    ∀ x ∈ (projU0 6).ker, g x ∈ (projU0 6).ker := by
  intro x hx
  have hfix : ∀ γ ∈ alternatingGroup (Fin 6), Mod.act 6 Mod.u0 γ (g x) = g x := by
    intro γ hγ
    have hginv := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) (Mod.act 6 Mod.u0 γ)).1
      ⟨γ, hγ, rfl⟩
    obtain ⟨γ', -, he⟩ := hginv
    have h1 : (g⁻¹ * Mod.act 6 Mod.u0 γ * g⁻¹⁻¹) x = x := by
      rw [← he]
      exact act_fixed_of_mem_ker hx γ'
    rw [inv_inv] at h1
    have h2 : g⁻¹ (Mod.act 6 Mod.u0 γ (g x)) = x := h1
    calc Mod.act 6 Mod.u0 γ (g x) = g (g⁻¹ (Mod.act 6 Mod.u0 γ (g x))) :=
          (g.apply_symm_apply _).symm
      _ = g x := by rw [h2]
  have hP : projU0 6 (g x) ∈ fixG (actL 6 Mod.ut0) := by
    intro γ
    show Mod.act 6 Mod.ut0 γ.1 (projU0 6 (g x)) = projU0 6 (g x)
    rw [← projU0_act, hfix γ.1 γ.2]
  rw [fixG_ut0] at hP
  exact hP

theorem induced_conj_mem {g : MulAut (Mod.V 6 Mod.u0)} {g' : MulAut (Mod.V 6 Mod.ut0)}
    (hrel : ∀ w, g' (projU0 6 w) = projU0 6 (g w))
    (hgn : ∀ l ∈ (alternatingGroup (Fin 6)).map (Mod.act 6 Mod.u0),
      g * l * g⁻¹ ∈ (alternatingGroup (Fin 6)).map (Mod.act 6 Mod.u0)) :
    ∀ l ∈ (alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0),
      g' * l * g'⁻¹ ∈ (alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0) := by
  have hrel' : ∀ w, g'⁻¹ (projU0 6 w) = projU0 6 (g⁻¹ w) := fun w => by
    show g'.symm (projU0 6 w) = projU0 6 (g⁻¹ w)
    rw [MulEquiv.symm_apply_eq, hrel, MulAut.apply_inv_self]
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨γ', hγ', he⟩ := hgn (Mod.act 6 Mod.u0 γ) ⟨γ, hγ, rfl⟩
  refine ⟨γ', hγ', ?_⟩
  refine MulEquiv.ext fun v => ?_
  obtain ⟨w, rfl⟩ := projU0_surjective v
  calc Mod.act 6 Mod.ut0 γ' (projU0 6 w) = projU0 6 (Mod.act 6 Mod.u0 γ' w) :=
        (projU0_act γ' w).symm
    _ = projU0 6 (g (Mod.act 6 Mod.u0 γ (g⁻¹ w))) := by rw [he]; rfl
    _ = g' (projU0 6 (Mod.act 6 Mod.u0 γ (g⁻¹ w))) := (hrel _).symm
    _ = g' (Mod.act 6 Mod.ut0 γ (projU0 6 (g⁻¹ w))) := by rw [projU0_act]
    _ = g' (Mod.act 6 Mod.ut0 γ (g'⁻¹ (projU0 6 w))) := by rw [hrel']
    _ = (g' * Mod.act 6 Mod.ut0 γ * g'⁻¹) (projU0 6 w) := rfl

theorem normalizer_alt_act_u0 :
    ∀ g ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.u0) :
        Subgroup (MulAut (Mod.V 6 Mod.u0))) : Set (MulAut (Mod.V 6 Mod.u0))),
      ∃ σ, Mod.act 6 Mod.u0 σ = g := by
  intro g hg
  have hg1 := (Subgroup.mem_normalizer_iff.1 hg)
  have hg2 := (Subgroup.mem_normalizer_iff.1 (inv_mem hg))
  obtain ⟨g', hrel⟩ := exists_induced_aut g (normalizer_preserves_ker hg)
    (normalizer_preserves_ker (inv_mem hg))
  have hrel' : ∀ w, g'⁻¹ (projU0 6 w) = projU0 6 (g⁻¹ w) := fun w => by
    show g'.symm (projU0 6 w) = projU0 6 (g⁻¹ w)
    rw [MulEquiv.symm_apply_eq, hrel, MulAut.apply_inv_self]
  have hg'n : g' ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (Mod.act 6 Mod.ut0) :
        Subgroup (MulAut (Mod.V 6 Mod.ut0))) : Set (MulAut (Mod.V 6 Mod.ut0))) := by
    refine mem_normalizer_of_conj_gc (induced_conj_mem hrel fun l hl => (hg1 l).1 hl) ?_
    intro l hl
    have := induced_conj_mem (g := g⁻¹) (g' := g'⁻¹) hrel' (fun l hl => (hg2 l).1 hl) l hl
    simpa using this
  obtain ⟨σ, hσ⟩ := normalizer_alt_act_ut0 g' hg'n
  refine ⟨σ, ?_⟩
  have hψ : ∀ w, projU0 6 ((g * (Mod.act 6 Mod.u0 σ)⁻¹) w) = projU0 6 w := fun w => by
    show projU0 6 (g ((Mod.act 6 Mod.u0 σ)⁻¹ w)) = projU0 6 w
    rw [← hrel, hσ.symm, ← map_inv, projU0_act, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel,
      map_one]
    rfl
  have hψn := (Subgroup.normalizer _).mul_mem hg (inv_mem (act_mem_normalizer Mod.u0 σ))
  have := eq_one_of_trivial_proj _ hψn hψ
  exact (mul_inv_eq_one.1 this).symm

theorem normalizer_alt_act {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) :
    ∀ g ∈ Subgroup.normalizer
      (((alternatingGroup (Fin 6)).map (Mod.act 6 k) :
        Subgroup (MulAut (Mod.V 6 k))) : Set (MulAut (Mod.V 6 k))),
      ∃ σ, Mod.act 6 k σ = g := by
  rcases hk with rfl | rfl
  · exact normalizer_alt_act_ut0
  · exact normalizer_alt_act_u0

end CFSG.Quasithin.H13.U3.GC137
