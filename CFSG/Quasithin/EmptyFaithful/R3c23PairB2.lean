module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.EmptyFaithful.R3c23Def
import CFSG.Quasithin.EmptyFaithful.R3c23PairB

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Assembly.LowTwoRank

section Invariance

variable {V : Type} [CommGroup V]

private theorem pairB_apply_mem_commV_of_mem {A : Subgroup (MulAut V)} {a : MulAut V}
    (ha : a ∈ A) {u : V} (hu : u ∈ commV A) : a u ∈ commV A :=
  CFSG.Quasithin.commV_apply_mem_of_mem ha hu

private theorem pairB_apply_mem_commV_of_comm {A : Subgroup (MulAut V)} {b : MulAut V}
    (hbc : ∀ a ∈ A, a * b = b * a) {u : V} (hu : u ∈ commV A) : b u ∈ commV A := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    have h1 : x (b v) = b (x v) := by
      have := congrArg (fun f : MulAut V => f v) (hbc x hx)
      simpa using this
    rw [map_mul, map_inv, ← h1]
    exact Subgroup.subset_closure ⟨x, hx, b v, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact inv_mem hy

private theorem pairB_apply_mem_sup {A : Subgroup (MulAut V)} {C : Subgroup V} {a : MulAut V}
    (hinv : ∀ u ∈ commV A, a u ∈ commV A) (hfix : ∀ c ∈ C, a c = c) {w : V}
    (hw : w ∈ commV A ⊔ C) : a w ∈ commV A ⊔ C := by
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul, hfix c hc]
  exact Subgroup.mul_mem_sup (hinv u hu) hc

private theorem pairB_triv_of_gen {G H L : Subgroup (MulAut V)} {W₁ W₂ C : Subgroup V}
    (hcomm : ∀ a ∈ G, ∀ b ∈ H, a * b = b * a)
    (hfixG : ∀ a ∈ G, ∀ c ∈ C, a c = c) (hfixH : ∀ b ∈ H, ∀ c ∈ C, b c = c)
    (hW₁ : W₁ = commV G ⊔ C) (hW₂ : W₂ = commV H ⊔ C) (hinf : W₁ ⊓ W₂ = C)
    (hLG : L ≤ G) (hgen : W₁ ≤ commMod L W₁ ⊔ C) :
    ∀ b ∈ H, ∀ w ∈ W₁, b w = w := by
  intro b hb
  have hbc : ∀ a ∈ G, a * b = b * a := fun a ha => hcomm a ha b hb
  have hinv : ∀ y ∈ W₁, b y ∈ W₁ := by
    intro y hy
    rw [hW₁] at hy ⊢
    exact pairB_apply_mem_sup (fun u hu => pairB_apply_mem_commV_of_comm hbc hu) (hfixH b hb) hy
  have hcy : ∀ y ∈ W₁, b y * y⁻¹ ∈ C := by
    intro y hy
    rw [← hinf]
    refine Subgroup.mem_inf.2 ⟨mul_mem (hinv y hy) (inv_mem hy), ?_⟩
    rw [hW₂]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, hb, y, rfl⟩)
  have hgenfix : ∀ l ∈ L, ∀ y ∈ W₁, b (l y * y⁻¹) = l y * y⁻¹ := by
    intro l hl y hy
    have hlc : l (b y * y⁻¹) = b y * y⁻¹ := hfixG l (hLG hl) _ (hcy y hy)
    have h1 : b (l y) = l (b y) := by
      have := congrArg (fun f : MulAut V => f y) (hbc l (hLG hl))
      simpa using this.symm
    have h3 : l (b y) = b y * y⁻¹ * l y := by
      rw [map_mul, map_inv] at hlc
      exact mul_inv_eq_iff_eq_mul.1 hlc
    calc b (l y * y⁻¹) = b (l y) * (b y)⁻¹ := by rw [map_mul, map_inv]
      _ = l (b y) * (b y)⁻¹ := by rw [h1]
      _ = b y * y⁻¹ * l y * (b y)⁻¹ := by rw [h3]
      _ = (l y * y⁻¹) * (b y * (b y)⁻¹) := by ac_rfl
      _ = l y * y⁻¹ := by rw [mul_inv_cancel, mul_one]
  have hfixSub : commMod L W₁ ⊔ C ≤ (b.toMonoidHom).eqLocus (MonoidHom.id V) := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
    · rintro x ⟨l, hl, y, hy, rfl⟩
      exact hgenfix l hl y hy
    · intro c hc
      exact hfixH b hb c hc
  intro w hw
  exact hfixSub (hgen hw)

private theorem pairB_lin2Cover_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : Lin2Cover L) : Lin2Cover L' := by
  obtain ⟨F, hF, hFin, n, hn, hc, ⟨e'⟩⟩ := h
  exact ⟨F, hF, hFin, n, hn, hc, ⟨e.symm.trans e'⟩⟩

end Invariance

theorem pairOutput_of_twoB56Gen (h₁ : SL2PieceFacts) (h₂ : Sym5PieceFacts)
    {V : Type} [CommGroup V] [Finite V] {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hK : Lin2Cover ↥L₁)
    (h : TwoB56Gen X L₁ L₂) : PairOutput X L₁ L₂ := by
  obtain ⟨G₁, G₂, W₁, W₂, hJ, hinf, hcomm, hL₁, hL₂, hG₁, hG₂, -, -, hsup, hWinf, hp₁, hp₂⟩ := h
  let e : ↥L₁ ≃* ↥L₂ :=
    (Subgroup.equivMapOfInjective L₁ (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hτ.symm)
  have hK₂ : Lin2Cover ↥L₂ := pairB_lin2Cover_of_mulEquiv e hK
  have hperf₁ : Group.IsPerfect ↥L₁ := hq₁.1
  have hperf₂ : Group.IsPerfect ↥L₂ :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have f₁ := pairB_pieceFacts h₁ h₂ hperf₁ hK hL₁ hG₁ hp₁
  have f₂ := pairB_pieceFacts h₁ h₂ hperf₂ hK₂ hL₂ hG₂ hp₂
  have hfix₁ : ∀ a ∈ G₁, ∀ c ∈ fixV (G₁ ⊔ G₂), a c = c :=
    fun a ha c hc => hc a (Subgroup.mem_sup_left ha)
  have hfix₂ : ∀ b ∈ G₂, ∀ c ∈ fixV (G₁ ⊔ G₂), b c = c :=
    fun b hb c hc => hc b (Subgroup.mem_sup_right hb)
  unfold PairOutput
  refine ⟨G₁, G₂, W₁, W₂, fixV (G₁ ⊔ G₂),
    ⟨hcomm, hinf, hsup, hWinf, fun g hg c hc => hc g hg, ?_, ?_, ?_, ?_⟩,
    f₁.natCount, f₂.natCount, hJ.le, hL₁, hL₂, f₁.ne, f₁.free⟩
  · intro a ha w hw
    rw [f₁.eq_comm] at hw ⊢
    exact pairB_apply_mem_sup (fun u hu => pairB_apply_mem_commV_of_mem ha hu) (hfix₁ a ha) hw
  · intro b hb w hw
    rw [f₂.eq_comm] at hw ⊢
    exact pairB_apply_mem_sup (fun u hu => pairB_apply_mem_commV_of_mem hb hu) (hfix₂ b hb) hw
  · exact pairB_triv_of_gen hcomm hfix₁ hfix₂ f₁.eq_comm f₂.eq_comm hWinf hL₁ f₁.gen
  · exact pairB_triv_of_gen (fun a ha b hb => (hcomm b hb a ha).symm) hfix₂ hfix₁ f₂.eq_comm
      f₁.eq_comm (by rw [inf_comm]; exact hWinf) hL₂ f₂.gen

end R3c23

end CFSG.Quasithin
