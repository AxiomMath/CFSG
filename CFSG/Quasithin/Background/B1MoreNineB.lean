module

public import CFSG.Quasithin.Background.B1MoreNineA
public import CFSG.Quasithin.Background.B1MoreSevenB

public section

namespace CFSG.Quasithin

open CFSG.Open B19Aux

variable {V : Type*} [CommGroup V]

structure B19Loc (G A : Subgroup (MulAut V)) : Prop where
  hO2 : pCoreOf 2 G = ⊥
  hA : IsFFStarMin G A
  hF : ⁅fittingOf G, A⁆ ≠ ⊥

noncomputable abbrev FAsub (G A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⁅fittingOf G, A⁆

namespace B19Loc

variable {G A : Subgroup (MulAut V)}

theorem A_le (P : B19Loc G A) : A ≤ G := P.hA.1.1

theorem A_abel (P : B19Loc G A) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := P.hA.1.2.2.1.1

theorem A_sq (P : B19Loc G A) : ∀ a ∈ A, a ^ 2 = 1 := P.hA.1.2.2.1.2

theorem conj_fitting (P : B19Loc G A) {a x : MulAut V} (ha : a ∈ A) (hx : x ∈ fittingOf G) :
    a * x * a⁻¹ ∈ fittingOf G :=
  conj_mem_fittingOf (P.A_le ha) hx

theorem FA_le (P : B19Loc G A) : ⁅fittingOf G, A⁆ ≤ fittingOf G := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
  show x * a * x⁻¹ * a⁻¹ ∈ fittingOf G
  rw [e]
  exact (fittingOf G).mul_mem hx (P.conj_fitting ha ((fittingOf G).inv_mem hx))

theorem FA_odd [Finite V] (P : B19Loc G A) : ∀ f ∈ ⁅fittingOf G, A⁆, Odd (orderOf f) :=
  fun f hf => odd_orderOf_of_mem_fittingOf P.hO2 f (P.FA_le hf)

theorem A_normalizes_FA (G A : Subgroup (MulAut V)) :
    A ≤ Subgroup.normalizer ((FAsub G A : Subgroup (MulAut V)) : Set (MulAut V)) :=
  le_normalizer_of_conj fun _ ha _ hf => conj_mem_commutator ha hf

theorem conj_FA {a f : MulAut V} (ha : a ∈ A) (hf : f ∈ FAsub G A) :
    a * f * a⁻¹ ∈ FAsub G A :=
  conj_mem_commutator ha hf

theorem FA_comm [Finite V] (P : B19Loc G A) : ⁅⁅fittingOf G, A⁆, A⁆ = ⁅fittingOf G, A⁆ := by
  refine le_antisymm (commutator_le_of_normalizes (A_normalizes_FA G A)) ?_
  exact commutator_le_commutator_commutator (fun x hx => odd_orderOf_of_mem_fittingOf P.hO2 x hx)
    P.A_sq (fun a ha x hx => P.conj_fitting ha hx)

theorem FA_comm_ne_bot [Finite V] (P : B19Loc G A) : ⁅⁅fittingOf G, A⁆, A⁆ ≠ ⊥ := by
  rw [P.FA_comm]
  exact P.hF

@[expose] noncomputable def Bsub (G A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A ⊓ Subgroup.centralizer ((FAsub G A : Subgroup (MulAut V)) : Set (MulAut V))

theorem B_le_A : Bsub G A ≤ A := inf_le_left

theorem B_comm {f b : MulAut V} (hf : f ∈ FAsub G A) (hb : b ∈ Bsub G A) :
    f * b = b * f :=
  Subgroup.mem_centralizer_iff.1 hb.2 f hf

theorem B_pgroup (P : B19Loc G A) : IsPGroup 2 ↥(Bsub G A) := by
  intro x
  refine ⟨1, ?_⟩
  have : (x : MulAut V) ^ 2 = 1 := P.A_sq x (B_le_A x.2)
  exact Subtype.ext (by simpa using this)

@[expose] noncomputable def Csub (G A : Subgroup (MulAut V)) : Subgroup V := fixV (Bsub G A)

theorem FA_inv_C {f : MulAut V} (hf : f ∈ FAsub G A) :
    ∀ c ∈ Csub G A, f c ∈ Csub G A := by
  intro c hc b hb
  have h : b (f c) = f (b c) := by
    have := congrArg (fun t : MulAut V => t c) (B_comm hf hb)
    simpa only [MulAut.mul_apply] using this.symm
  rw [h, hc b hb]

theorem A_inv_C (P : B19Loc G A) {a : MulAut V} (ha : a ∈ A) :
    ∀ c ∈ Csub G A, a c ∈ Csub G A := by
  intro c hc b hb
  have h : b (a c) = a (b c) := by
    have := congrArg (fun t : MulAut V => t c) (P.A_abel b (B_le_A hb) a ha)
    simpa only [MulAut.mul_apply] using this
  rw [h, hc b hb]

@[expose] noncomputable def Wsub (G A : Subgroup (MulAut V)) : Subgroup V :=
  commSub (Csub G A) (FAsub G A)

theorem W_le_C : Wsub G A ≤ Csub G A :=
  commSub_le_of_invariant fun _ hf _ hc => FA_inv_C hf _ hc

theorem odd_card_FA [Finite V] (P : B19Loc G A) : Odd (Nat.card (FAsub G A)) :=
  odd_card_of_forall_odd_orderOf P.FA_odd

theorem FA_faithful_C [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) {f : MulAut V}
    (hf : f ∈ FAsub G A) (hfix : ∀ c ∈ Csub G A, f c = c) : f = 1 := by
  have hodd : Odd (Nat.card (Subgroup.zpowers f)) := by
    rw [Nat.card_zpowers]
    exact P.FA_odd f hf
  have hcomm : ∀ y ∈ Subgroup.zpowers f, ∀ b ∈ Bsub G A, y * b = b * y := by
    intro y hy b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_left (B_comm hf hb : Commute f b) k
  have hfixY : ∀ y ∈ Subgroup.zpowers f, ∀ m ∈ (⊤ : Subgroup V) ⊓ fixV (Bsub G A), y m = m := by
    intro y hy m hm
    have hst : f ∈ MulAction.stabilizer (MulAut V) m := hfix m hm.2
    exact (Subgroup.zpowers_le.2 hst) hy
  have h := B1.axb hV hodd P.B_pgroup hcomm (M := ⊤) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial) hfixY
  ext v
  exact h (Subgroup.mem_top v) f (Subgroup.mem_zpowers f)

theorem W_ne_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) : Wsub G A ≠ ⊥ := by
  intro hW
  have hCf : Csub G A ≤ fixV (FAsub G A) := commSub_eq_bot_iff.1 hW
  obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 P.hF
  exact hf1 (Subtype.ext (P.FA_faithful_C hV f.2 fun c hc => hCf hc f f.2))

theorem W_inv_FA {f : MulAut V} (hf : f ∈ FAsub G A) :
    ∀ w ∈ Wsub G A, f w ∈ Wsub G A :=
  fun w hw => commSub_inv_H (FAsub G A) (Csub G A) f hf w hw

theorem W_inv_A (P : B19Loc G A) {a : MulAut V} (ha : a ∈ A) :
    ∀ w ∈ Wsub G A, a w ∈ Wsub G A := by
  intro w hw
  unfold Wsub commSub at hw ⊢
  refine Subgroup.closure_induction (p := fun w _ => a w ∈ Subgroup.closure
    {c | ∃ x ∈ FAsub G A, ∃ y ∈ Csub G A, x y * y⁻¹ = c}) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨f, hf, c, hc, rfl⟩
    have e : a (f c * c⁻¹) = (a * f * a⁻¹) (a c) * (a c)⁻¹ := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e]
    exact Subgroup.subset_closure ⟨a * f * a⁻¹, conj_FA ha hf, a c, P.A_inv_C ha c hc, rfl⟩
  · simp
  · intro x y _ _ hx hy
    simpa using Subgroup.mul_mem _ hx hy
  · intro x _ hx
    simpa using Subgroup.inv_mem _ hx

theorem W_inf_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    Wsub G A ⊓ fixV (FAsub G A) = ⊥ := by
  obtain ⟨-, hinf⟩ := B1.coprime_decomp hV P.odd_card_FA (M := Csub G A)
    (fun y hy m hm => FA_inv_C hy m hm)
  refine (Subgroup.eq_bot_iff_forall _).2 fun w hw => ?_
  have : w ∈ (Csub G A ⊓ fixV (FAsub G A)) ⊓ commSub (Csub G A) (FAsub G A) :=
    ⟨⟨W_le_C hw.1, hw.2⟩, hw.1⟩
  rw [hinf] at this
  exact this

theorem comm_W_FA [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    commSub (Wsub G A) (FAsub G A) = Wsub G A := by
  obtain ⟨hsup, -⟩ := B1.coprime_decomp hV P.odd_card_FA (M := Wsub G A)
    (fun y hy m hm => W_inv_FA hy m hm)
  rw [P.W_inf_fixV hV, bot_sup_eq] at hsup
  exact hsup

theorem FA_faithful_W [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) {f : MulAut V}
    (hf : f ∈ FAsub G A) (hfix : ∀ w ∈ Wsub G A, f w = w) : f = 1 := by
  refine P.FA_faithful_C hV hf fun c hc => ?_
  obtain ⟨hsup, -⟩ := B1.coprime_decomp hV P.odd_card_FA (M := Csub G A)
    (fun y hy m hm => FA_inv_C hy m hm)
  have hc' : c ∈ (Csub G A ⊓ fixV (FAsub G A)) ⊔ commSub (Csub G A) (FAsub G A) := by
    rw [hsup]; exact hc
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hc'
  rw [map_mul, hu.2 f hf, hfix w hw]

theorem commSub_W_A_ne_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    commSub (Wsub G A) A ≠ ⊥ := by
  intro h
  have hWA : Wsub G A ≤ fixV A := commSub_eq_bot_iff.1 h
  have hcent : ∀ f ∈ FAsub G A, ∀ a ∈ A, a * f * a⁻¹ = f := by
    intro f hf a ha
    have h1 : a * f * a⁻¹ * f⁻¹ ∈ FAsub G A :=
      (FAsub G A).mul_mem (conj_FA ha hf) ((FAsub G A).inv_mem hf)
    have h2 : ∀ w ∈ Wsub G A, (a * f * a⁻¹ * f⁻¹) w = w := by
      intro w hw
      have hfw : f⁻¹ w ∈ Wsub G A := W_inv_FA ((FAsub G A).inv_mem hf) w hw
      have e1 : a⁻¹ (f⁻¹ w) = f⁻¹ w := hWA hfw a⁻¹ (A.inv_mem ha)
      have e2 : a (f (f⁻¹ w)) = a w := by simp
      have e3 : a w = w := hWA hw a ha
      simp only [MulAut.mul_apply]
      rw [e1]
      simp [e3]
    exact mul_inv_eq_one.1 (P.FA_faithful_W hV h1 h2)
  apply P.FA_comm_ne_bot
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro f hf a ha
  show f * a * f⁻¹ * a⁻¹ ∈ (⊥ : Subgroup (MulAut V))
  rw [Subgroup.mem_bot]
  have h3 := hcent f⁻¹ ((FAsub G A).inv_mem hf) a ha
  calc f * a * f⁻¹ * a⁻¹ = f * (a * f⁻¹ * a⁻¹) := by group
    _ = 1 := by rw [h3]; group

theorem offender_autSub_W [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    IsFFStarOffender (autSub G (Wsub G A)) (autSub A (Wsub G A)) :=
  B1_5_1 P.hA.1 (fun _ ha w hw => P.W_inv_A ha w hw) (P.commSub_W_A_ne_bot hV)

end B19Loc

end CFSG.Quasithin
