module

public import CFSG.Quasithin.Background.SmithC27RCaseIIMod8
public import CFSG.Quasithin.H13.VolIAltCoverEight
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Background.SmithC27RCaseIIStar
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

section Perfect

variable {W : Type*} [CommGroup W]

theorem mem_closure_comm_of_perfect {L : Subgroup (MulAut W)} (hperf : ⁅L, L⁆ = L) {v : W}
    (hv : v ∈ commV L) :
    v ∈ Subgroup.closure {x | ∃ l ∈ L, ∃ u ∈ commV L, x = l u * u⁻¹} := by
  set U₂ := Subgroup.closure {x | ∃ l ∈ L, ∃ u ∈ commV L, x = l u * u⁻¹} with hU₂
  have hgen : ∀ l ∈ L, ∀ u ∈ commV L, l u * u⁻¹ ∈ U₂ := fun l hl u hu =>
    Subgroup.subset_closure ⟨l, hl, u, hu, rfl⟩
  have hcV : ∀ l ∈ L, ∀ w : W, l w * w⁻¹ ∈ commV L := fun l hl w =>
    Subgroup.subset_closure ⟨l, hl, w, rfl⟩
  suffices key : ∀ l ∈ L, ∀ w : W, l w * w⁻¹ ∈ U₂ by
    unfold commV at hv
    refine (Subgroup.closure_le _).2 (fun x hx => ?_) hv
    obtain ⟨l, hl, w, rfl⟩ := hx
    exact key l hl w
  intro l hl w
  let f : ↥L →* W ⧸ U₂ :=
    { toFun := fun l => QuotientGroup.mk ((l : MulAut W) w * w⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hb : (b : MulAut W) w * w⁻¹ ∈ commV L := hcV b b.2 w
        have h1 := hgen a a.2 _ hb
        have h2 : (QuotientGroup.mk ((a : MulAut W) ((b : MulAut W) w * w⁻¹)) : W ⧸ U₂) =
            QuotientGroup.mk ((b : MulAut W) w * w⁻¹) := by
          rw [QuotientGroup.eq]
          have h3 := U₂.inv_mem h1
          rwa [mul_inv_rev, inv_inv, mul_comm] at h3
        show (QuotientGroup.mk ((a : MulAut W) ((b : MulAut W) w) * w⁻¹) : W ⧸ U₂) =
          QuotientGroup.mk ((a : MulAut W) w * w⁻¹) * QuotientGroup.mk ((b : MulAut W) w * w⁻¹)
        simp only [map_mul, map_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2 ⊢
        generalize (QuotientGroup.mk ((a : MulAut W) ((b : MulAut W) w)) : W ⧸ U₂) = x at h2 ⊢
        generalize (QuotientGroup.mk ((a : MulAut W) w) : W ⧸ U₂) = y at h2 ⊢
        generalize (QuotientGroup.mk ((b : MulAut W) w) : W ⧸ U₂) = z at h2 ⊢
        generalize (QuotientGroup.mk w : W ⧸ U₂) = t at h2 ⊢
        rw [mul_inv_eq_iff_eq_mul] at h2
        rw [h2]
        ac_rfl }
  have hker : ∀ g ∈ (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L), f g = 1 := by
    intro g hg
    have hle : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) ≤ f.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
        mul_comm]
    exact hle hg
  have hl' : (⟨l, hl⟩ : ↥L) ∈ (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) := by
    have h1 : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : l ∈ (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L).map L.subtype := by
      rw [h1, hperf]
      exact hl
    obtain ⟨g, hg, hgl⟩ := h2
    have : g = ⟨l, hl⟩ := Subtype.ext hgl
    rw [← this]
    exact hg
  have h3 := hker _ hl'
  exact (QuotientGroup.eq_one_iff _).1 h3

end Perfect

section SymCover

open H13.VolI

theorem symCover8_bound (W : Type) [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    (C' : ModelCover (FFModel.symDn 8) W) : Nat.card C'.β.ker ≤ 2 := by
  classical
  let ρ' : Perm (Fin 8) →* MulAut W := C'.ρ
  let ρA : ↥(alternatingGroup (Fin 8)) →* MulAut W := ρ'.comp (alternatingGroup (Fin 8)).subtype
  set W₁ : Subgroup W :=
    Subgroup.closure {x | ∃ (γ : ↥(alternatingGroup (Fin 8))) (w : W), x = ρA γ w * w⁻¹} with hW₁
  have hinv : ∀ σ : Perm (Fin 8), ∀ x ∈ W₁, ρ' σ x ∈ W₁ := by
    intro σ x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, w, rfl⟩ := hx
      have hγ : σ * (γ : Perm (Fin 8)) * σ⁻¹ ∈ alternatingGroup (Fin 8) :=
        Subgroup.Normal.conj_mem inferInstance _ γ.2 σ
      refine Subgroup.subset_closure ⟨⟨_, hγ⟩, ρ' σ w, ?_⟩
      show ρ' σ (ρ' (γ : Perm (Fin 8)) w * w⁻¹) =
        ρ' (σ * (γ : Perm (Fin 8)) * σ⁻¹) (ρ' σ w) * (ρ' σ w)⁻¹
      rw [map_mul, map_mul, map_inv, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
        MulAut.inv_apply_self]
    | one => rw [map_one]; exact W₁.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact W₁.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact W₁.inv_mem hx
  have hsurj : ∀ s : (FFModel.symDn 8).Sec, ∃ w₁ ∈ W₁, C'.β w₁ = s := by
    intro s
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective s
    let T : Subgroup ↥(G6.coreMod 8) :=
      { carrier := {m | ∃ w₁ ∈ W₁, C'.β w₁ = QuotientGroup.mk m}
        one_mem' := ⟨1, W₁.one_mem, by rw [map_one]; rfl⟩
        mul_mem' := fun ⟨a, ha, hae⟩ ⟨b, hb, hbe⟩ =>
          ⟨a * b, W₁.mul_mem ha hb, by rw [map_mul, hae, hbe]; rfl⟩
        inv_mem' := fun ⟨a, ha, hae⟩ =>
          ⟨a⁻¹, W₁.inv_mem ha, by rw [map_inv, hae]; rfl⟩ }
    have hgen : Subgroup.closure {x | ∃ σ y, x = act8 σ y * y⁻¹} ≤ T := by
      rw [Subgroup.closure_le]
      rintro _ ⟨σ, y, rfl⟩
      obtain ⟨u, hu⟩ := C'.surj (QuotientGroup.mk y)
      refine ⟨ρA σ u * u⁻¹, Subgroup.subset_closure ⟨σ, u, rfl⟩, ?_⟩
      have hact : (FFModel.symDn 8).act (σ : Perm (Fin 8)) (y : G6.PermMod 8) ∈
          (FFModel.symDn 8).sec := G6.permAct_mem_coreMod _ y.2
      have h1 := C'.equiv (σ : Perm (Fin 8)) u y hact hu
      rw [map_mul, map_inv, hu]
      show C'.β (C'.ρ (σ : Perm (Fin 8)) u) * _ = _
      rw [h1]
      rfl
    exact hgen (coreMod_eight_gen m)
  have hgenA : ∀ w : W, w ∈ Subgroup.closure {x | ∃ γ w, x = ρA γ w * w⁻¹} := by
    intro w
    refine (Subgroup.closure_le _).2 ?_ (C'.gen w)
    rintro _ ⟨σ, w', rfl⟩
    obtain ⟨w₁, hw₁, hβ⟩ := hsurj (C'.β w')
    have hk : C'.β (w' * w₁⁻¹) = 1 := by rw [map_mul, map_inv, hβ, mul_inv_cancel]
    have hfix := C'.fix σ _ hk
    have e : C'.ρ σ w' * w'⁻¹ = C'.ρ σ w₁ * w₁⁻¹ := by
      have h2 : C'.ρ σ w' = C'.ρ σ (w' * w₁⁻¹) * C'.ρ σ w₁ := by
        rw [← map_mul, inv_mul_cancel_right]
      have h3 : w' * w₁⁻¹ * w'⁻¹ = w₁⁻¹ := by
        rw [mul_comm w' w₁⁻¹, mul_assoc, mul_inv_cancel, mul_one]
      rw [h2, hfix, mul_comm (w' * w₁⁻¹), mul_assoc, h3]
    rw [e]
    exact W₁.mul_mem (hinv σ w₁ hw₁) (W₁.inv_mem hw₁)
  let CA : ModelCover (FFModel.altDn 8) W :=
    { ρ := ρA
      β := C'.β
      surj := C'.surj
      fix := fun γ v hv => C'.fix (Subtype.val γ) v hv
      equiv := fun γ v m hm hvm => C'.equiv (Subtype.val γ) v m hm hvm
      gen := hgenA }
  exact cover8_bound W hW2 CA

end SymCover

section Ctx

open H13.VolI

variable {G : Type} [Group G] [Finite G] {R K V : Subgroup G}

namespace CaseIICtx

variable (C : CaseIICtx R K V 8)

theorem le_stabSub (hs : StarHyp R K V) :
    autI C.hV (K ⊔ R) ≤ stabSub (commV (autI C.hV K)) := by
  intro g hg u
  have hN := C124.YZ.autI_normalizes C.hV hs.le_normalizer hg
  have hNi := C124.YZ.autI_normalizes C.hV hs.le_normalizer ((autI C.hV (K ⊔ R)).inv_mem hg)
  constructor
  · intro hu
    have h1 := C124.YZ.apply_mem_commV hNi hu
    rwa [MulAut.inv_apply_self] at h1
  · intro hu
    exact C124.YZ.apply_mem_commV hN hu

@[expose] noncomputable def ρU (hs : StarHyp R K V) :
    Perm (Fin 8) →* MulAut ↥(commV (autI C.hV K)) :=
  (resHomOn (commV (autI C.hV K)) (C.le_stabSub hs)).comp
    (C.ι.symm.toMonoidHom : Perm (Fin 8) →* ↥(autI C.hV (K ⊔ R)))

theorem ρU_apply (hs : StarHyp R K V) (σ : Perm (Fin 8)) (u : ↥(commV (autI C.hV K))) :
    ((C.ρU hs σ u : ↥(commV (autI C.hV K))) : IntMod V C.hV) =
      ((C.ι.symm σ : MulAut ↥V) : MulAut (IntMod V C.hV)) u.1 := rfl

theorem β_ρU (hs : StarHyp R K V) (σ : Perm (Fin 8)) (u : ↥(commV (autI C.hV K))) :
    C.β (C.ρU hs σ u) = C124.YZ.dAct 8 σ (C.β u) := by
  have hu : ((C.ι.symm σ : MulAut ↥V) : MulAut (IntMod V C.hV)) u.1 ∈
      commV (autI C.hV K) := (C.ρU hs σ u).2
  have h1 := C.β_equiv (C.ι.symm σ) u hu
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1

theorem commutator_K (hs : StarHyp R K V) : ⁅autI C.hV K, autI C.hV K⁆ = autI C.hV K := by
  have := hs.quasisimple.1
  have h1 : ⁅(⊤ : Subgroup ↥(autOn K V)), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  have h2 := congrArg (Subgroup.map (autOn K V).subtype) h1
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2

theorem gen_U (hs : StarHyp R K V) (v : ↥(commV (autI C.hV K))) :
    v ∈ Subgroup.closure {x | ∃ (γ : ↥(alternatingGroup (Fin 8))) (w : ↥(commV (autI C.hV K))),
      x = C.ρU hs γ w * w⁻¹} := by
  set S' := Subgroup.closure {x | ∃ (γ : ↥(alternatingGroup (Fin 8)))
    (w : ↥(commV (autI C.hV K))), x = C.ρU hs γ w * w⁻¹} with hS'
  have h1 := mem_closure_comm_of_perfect (C.commutator_K hs) v.2
  have hle : Subgroup.closure {x | ∃ l ∈ autI C.hV K, ∃ u ∈ commV (autI C.hV K),
      x = l u * u⁻¹} ≤ S'.map (commV (autI C.hV K)).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    have hlX : l ∈ autI C.hV (K ⊔ R) := autI_mono C.hV le_sup_left hl
    have hγ : C.ι ⟨l, hlX⟩ ∈ alternatingGroup (Fin 8) := (C.mem_K ⟨l, hlX⟩).1 hl
    let u' : ↥(commV (autI C.hV K)) := ⟨u, hu⟩
    refine ⟨C.ρU hs (C.ι ⟨l, hlX⟩) u' * u'⁻¹, Subgroup.subset_closure ⟨⟨_, hγ⟩, u', rfl⟩, ?_⟩
    have h2 : ((C.ρU hs (C.ι ⟨l, hlX⟩) u' : ↥(commV (autI C.hV K))) : IntMod V C.hV) = l u := by
      rw [ρU_apply, MulEquiv.symm_apply_apply]
      rfl
    show ((C.ρU hs (C.ι ⟨l, hlX⟩) u' : ↥(commV (autI C.hV K))) : IntMod V C.hV) * u⁻¹ =
      l u * u⁻¹
    rw [h2]
  obtain ⟨v', hv', hvv'⟩ := hle h1
  have : v' = v := Subtype.ext hvv'
  rw [← this]
  exact hv'

theorem card_ker_β_le_two (hs : StarHyp R K V) : Nat.card C.β.ker ≤ 2 := by
  have hU2 : ∀ w : ↥(commV (autI C.hV K)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact IntMod.sq_eq_one _)
  let CA : ModelCover (FFModel.altDn 8) ↥(commV (autI C.hV K)) :=
    { ρ := (C.ρU hs).comp (alternatingGroup (Fin 8)).subtype
      β := C.β
      surj := C.β_surj
      fix := fun γ v hv => by
        apply Subtype.ext
        show ((C.ι.symm (Subtype.val γ) : MulAut ↥V) : MulAut (IntMod V C.hV)) v.1 = v.1
        have hγK : ((C.ι.symm (Subtype.val γ) : MulAut ↥V)) ∈ autOn K V := by
          rw [C.mem_K, MulEquiv.apply_symm_apply]
          exact γ.2
        exact ((C.β_ker v).1 hv) _ hγK
      equiv := fun γ v m hm hvm => by
        show C.β (C.ρU hs (Subtype.val γ) v) = _
        rw [C.β_ρU hs]
        exact (congrArg (C124.YZ.dAct 8 (Subtype.val γ)) hvm).trans rfl
      gen := fun v => C.gen_U hs v }
  exact cover8_bound _ hU2 CA

theorem ρU_eq_of_β_eq_one (hs : StarHyp R K V) (σ : Perm (Fin 8))
    {v : ↥(commV (autI C.hV K))} (hv : C.β v = 1) : C.ρU hs σ v = v := by
  classical
  by_contra hne
  have hσv : C.β (C.ρU hs σ v) = 1 := by
    rw [C.β_ρU hs, hv, map_one]
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hne (map_one _)
  have hσv1 : C.ρU hs σ v ≠ 1 := fun h => hv1 ((C.ρU hs σ).injective (h.trans (map_one _).symm))
  have h3 : 3 ≤ Nat.card C.β.ker := by
    have : Fintype ↥C.β.ker := Fintype.ofFinite _
    let a : ↥C.β.ker := 1
    let b : ↥C.β.ker := ⟨v, hv⟩
    let c : ↥C.β.ker := ⟨C.ρU hs σ v, hσv⟩
    have hab : a ≠ b := fun h => hv1 (congrArg Subtype.val h).symm
    have hac : a ≠ c := fun h => hσv1 (congrArg Subtype.val h).symm
    have hbc : b ≠ c := fun h => hne (congrArg Subtype.val h).symm
    have : ({a, b, c} : Finset ↥C.β.ker).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_pair hbc]
    rw [← this, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  exact absurd (C.card_ker_β_le_two hs) (by omega)

@[expose] noncomputable def coverS (hs : StarHyp R K V) :
    ModelCover (FFModel.symDn 8) ↥(commV (autI C.hV K)) where
  ρ := C.ρU hs
  β := C.β
  surj := C.β_surj
  fix := fun γ v hv => C.ρU_eq_of_β_eq_one hs γ hv
  equiv := fun γ v m hm hvm =>
    (C.β_ρU hs γ v).trans ((congrArg (C124.YZ.dAct 8 γ) hvm).trans rfl)
  gen := fun v => (Subgroup.closure_le _).2 (fun x hx => by
    obtain ⟨γ, w, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨(γ : Perm (Fin 8)), w, rfl⟩) (C.gen_U hs v)

theorem exists_mulEquiv_coreMod (hs : StarHyp R K V) (h2 : Nat.card C.β.ker = 2) :
    ∃ Φ : ↥(commV (autI C.hV K)) ≃* ↥(G6.coreMod 8),
      ∀ σ v, Φ (C.ρU hs σ v) = G6.coreAct 8 σ (Φ v) := by
  have hU2 : ∀ w : ↥(commV (autI C.hV K)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact IntMod.sq_eq_one _)
  have : Finite ↥(FFModel.symDn 8).sec := (inferInstance : Finite ↥(G6.coreMod 8))
  exact ModelCover.exists_mulEquiv (D := FFModel.symDn 8) (G6.coreAct 8) (fun _ _ => rfl)
    (fun γ m hm => by
      have hm' : (Subtype.val m : G6.PermMod 8) ∈ Subgroup.zpowers (G6.allOnes 8) := hm.1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm'
      apply Subtype.ext
      show G6.permAct 8 γ (Subtype.val m) = Subtype.val m
      rw [← hk, map_zpow]
      exact congrArg (· ^ k) (permAct_allOnes 8 γ))
    card_ker_eight
    (fun m => (Subgroup.closure_le _).2 (fun x hx => by
      obtain ⟨σ, y, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨(σ : Perm (Fin 8)), y, rfl⟩) (coreMod_eight_gen m))
    (fun m => Subtype.ext (permMod_sq _)) symCover8_bound hU2 (C.coverS hs) h2

theorem apply_swap01_eq_of_fix_V8 (hs : StarHyp R K V) {u : IntMod V C.hV}
    (hu : u ∈ commV (autI C.hV K))
    (hfix : ∀ g ∈ Claim2526.V8, ((C.ι.symm g : MulAut ↥V) : MulAut (IntMod V C.hV)) u = u) :
    ((C.ι.symm (swap 0 1) : MulAut ↥V) : MulAut (IntMod V C.hV)) u = u := by
  set u' : ↥(commV (autI C.hV K)) := ⟨u, hu⟩ with hu'
  have hρ : ∀ g ∈ Claim2526.V8, C.ρU hs g u' = u' := fun g hg => Subtype.ext (hfix g hg)
  suffices h : C.ρU hs (swap 0 1) u' = u' from congrArg Subtype.val h
  by_cases hZ : C.β.ker = ⊥
  · have hinj : Function.Injective C.β := (MonoidHom.ker_eq_bot_iff _).1 hZ
    apply hinj
    rw [C.β_ρU hs]
    apply dAct_swap01_of_fix_V8
    intro g hg
    rw [← C.β_ρU hs, hρ g hg]
  · have h2 : Nat.card C.β.ker = 2 := by
      have hle := C.card_ker_β_le_two hs
      have hne : Nat.card C.β.ker ≠ 1 := fun h => hZ (Subgroup.eq_bot_of_card_eq _ h)
      have hpos : 0 < Nat.card C.β.ker := Nat.card_pos
      omega
    obtain ⟨Φ, hΦ⟩ := C.exists_mulEquiv_coreMod hs h2
    apply Φ.injective
    rw [hΦ]
    apply coreAct_swap01_of_fix_V8
    intro g hg
    rw [← hΦ, hρ g hg]

end CaseIICtx

end Ctx

end CFSG.Quasithin.SmithC27
