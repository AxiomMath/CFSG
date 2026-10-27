module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepOdd
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nTR_refl_mul_comm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {rc ra : V ≃ₗ[ZMod p] V} {hc ha : V}
    {αc αa : Module.Dual (ZMod p) V} (hc' : ∀ v, rc v = v - αc v • hc)
    (ha' : ∀ v, ra v = v - αa v • ha) (h0c : αc ha = 0) (h0a : αa hc = 0) :
    rc * ra = ra * rc := by
  have h1 : rc ha = ha := by rw [hc' ha, h0c, zero_smul, sub_zero]
  have h2 : ra hc = hc := by rw [ha' hc, h0a, zero_smul, sub_zero]
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hl : rc (ra v) = v - αc v • hc - αa v • ha := by
    calc rc (ra v) = rc (v - αa v • ha) := by rw [ha' v]
      _ = rc v - rc (αa v • ha) := by rw [map_sub]
      _ = rc v - αa v • rc ha := by rw [map_smul]
      _ = rc v - αa v • ha := by rw [h1]
      _ = (v - αc v • hc) - αa v • ha := by rw [hc' v]
      _ = v - αc v • hc - αa v • ha := by abel
  have hr : ra (rc v) = v - αc v • hc - αa v • ha := by
    calc ra (rc v) = ra (v - αc v • hc) := by rw [hc' v]
      _ = ra v - ra (αc v • hc) := by rw [map_sub]
      _ = ra v - αc v • ra hc := by rw [map_smul]
      _ = ra v - αc v • hc := by rw [h2]
      _ = (v - αa v • ha) - αc v • hc := by rw [ha' v]
      _ = v - αc v • hc - αa v • ha := by abel
  rw [hl, hr]

private theorem l05nTT_root_form {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαaha : αa ha = 2) (hαax : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hno : ∀ c, αa (h c) = 0) :
    (∃ f : Module.Dual (ZMod p) V, f x = 2 ∧ ∀ w, ra w = w - f w • x) ∧
      ∀ c, r c * ra = ra * r c := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hαcc : ∀ c, α c (h c) = 2 := fun c => by simpa [CartanMatrix.A] using F.pair c c
  have h0c : ∀ c, α c ha = 0 := fun c =>
    ggDepA_pair_zero_symm (p := p) hp2 (Subgroup.closure (Set.range r ∪ {ra})) hnt
      (rc := ra) (ra := r c) (hc := ha) (ha := h c)
      (αc := αa) (αa := α c)
      (hrc := Subgroup.subset_closure (Or.inr rfl))
      (hra := Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
      (hc' := fun v => hra v) (ha' := fun v => hr c v)
      (hαc := hαaha) (hαa := hαcc c) (h0 := hno c)
  have hcomm : ∀ c, r c * ra = ra * r c := fun c =>
    l05nTR_refl_mul_comm (rc := r c) (ra := ra) (hc := h c) (ha := ha)
      (αc := α c) (αa := αa) (hc' := fun v => hr c v) (ha' := fun v => hra v)
      (h0c := h0c c) (h0a := hno c)
  have hx_fix : ∀ c, r c x = x := fun c => by rw [hr c, F.x_ker c, zero_smul, sub_zero]
  have hrax : ∀ c, α c (ra x) = 0 := fun c => by
    have hfixc : r c (ra x) = ra x := by
      have hh := congrArg (fun e : V ≃ₗ[ZMod p] V => e x) (hcomm c)
      simp only [LinearEquiv.mul_apply] at hh
      rw [hh, hx_fix c]
    have hsub : ra x - α c (ra x) • h c = ra x := by
      rw [← hr c (ra x)]
      exact hfixc
    have hsm : α c (ra x) • h c = 0 := sub_eq_self.mp hsub
    have hcne : h c ≠ 0 := by
      intro h0
      apply h2
      rw [← hαcc c, h0, map_zero]
    exact (smul_eq_zero.mp hsm).resolve_right hcne
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp (F.fix (ra x) hrax)
  have hha : αa x • ha = (1 - lam) • x := by
    have hh := hra x
    rw [← hlam] at hh
    have hsum : lam • x + αa x • ha = x := eq_sub_iff_add_eq.mp hh
    have h3 : αa x • ha = x - lam • x := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact hsum
    rw [h3, sub_smul, one_smul]
  let mu : ZMod p := (1 - lam) / αa x
  have hmu_eq : mu = (1 - lam) / αa x := rfl
  have hha_mu : ha = mu • x := by
    have key : (αa x)⁻¹ • (αa x • ha) = (αa x)⁻¹ • ((1 - lam) • x) := by rw [hha]
    rw [smul_smul, inv_mul_cancel₀ hαax, one_smul, smul_smul] at key
    rw [show (αa x)⁻¹ * (1 - lam) = mu by rw [hmu_eq, div_eq_mul_inv, mul_comm]] at key
    exact key
  have hmu : mu * αa x = 2 := by
    have hh := congrArg αa hha_mu
    rw [map_smul, smul_eq_mul, hαaha] at hh
    exact hh.symm
  refine ⟨⟨mu • αa, ?_, ?_⟩, hcomm⟩
  · show (mu • αa) x = 2
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact hmu
  · intro w
    rw [hra w, hha_mu, smul_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [mul_comm (αa w) mu]

private theorem l05nTT_root_prod {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {x : V} (hx : x ≠ 0)
    {f g : Module.Dual (ZMod p) V} (hf : f x = 2) (hg : g x = 2) (hfg : f ≠ g)
    (ra rb : V ≃ₗ[ZMod p] V) (hra : ∀ w, ra w = w - f w • x) (hrb : ∀ w, rb w = w - g w • x) :
    Module.finrank (ZMod p) (ggLinMove (ra * rb)) = 1 ∧
      ∀ w, (ra * rb) ((ra * rb) w - w) = (ra * rb) w - w := by
  have hsub_ne : f - g ≠ 0 := sub_ne_zero.mpr hfg
  obtain ⟨w0, hw0⟩ : ∃ w, (f - g) w ≠ 0 := by
    by_contra h
    exact hsub_ne (LinearMap.ext fun w => not_not.mp (not_exists.mp h w))
  have hform : ∀ w, (ra * rb) w = w - (f - g) w • x := by
    intro w
    rw [LinearEquiv.mul_apply, hrb w, hra]
    simp only [map_sub, map_smul, hf, LinearMap.sub_apply, smul_eq_mul]
    module
  have hker : (f - g) x = 0 := by rw [LinearMap.sub_apply, hf, hg, sub_self]
  have hmove : ∀ w, (ra * rb) w - w = -((f - g) w) • x := by
    intro w
    rw [hform w]
    module
  have hrange : ggLinMove (ra * rb) = Submodule.span (ZMod p) {x} := by
    apply le_antisymm
    · intro v hv
      rw [ggLinMove, LinearMap.mem_range] at hv
      obtain ⟨w, hw⟩ := hv
      rw [← hw]
      change (ra * rb) w - w ∈ Submodule.span (ZMod p) {x}
      rw [hmove w]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · intro v hv
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨c, rfl⟩ := hv
      have hmem : (ra * rb) w0 - w0 ∈ ggLinMove (ra * rb) := by
        rw [ggLinMove, LinearMap.mem_range]
        exact ⟨w0, rfl⟩
      have hxw : x = (-((f - g) w0))⁻¹ • ((ra * rb) w0 - w0) := by
        rw [hmove w0, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hw0), one_smul]
      rw [hxw, smul_smul]
      exact Submodule.smul_mem _ _ hmem
  refine ⟨?_, ?_⟩
  · rw [hrange]
    exact finrank_span_singleton hx
  · intro w
    rw [hmove w, hform]
    have hzero : (f - g) (-((f - g) w) • x) = 0 := by
      rw [map_smul, hker, smul_zero]
    rw [hzero, zero_smul, sub_zero]

theorem ggTK_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]

private theorem l05nTK1_finrank_U {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x) (t : V) :
    Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h) ⊔
      Submodule.span (ZMod p) ({t} : Set V)) ≤ N - 1 := by
  obtain ⟨-, -, hfin⟩ := ggDepA_relation F
  have hN2 : 2 ≤ N := by
    by_contra h
    have h0 : N - 1 = 0 := by omega
    apply F.dep
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hi : (i : ℕ) < 0 := by omega
    exact (Nat.not_lt_zero i.val hi).elim
  have hle := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span (ZMod p) (Set.range h)) (Submodule.span (ZMod p) ({t} : Set V))
  have hsingle : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) ≤ 1 :=
    finrank_le_one ⟨t, Submodule.mem_span_singleton_self t⟩ (fun w => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
      exact ⟨c, Subtype.ext hc⟩)
  calc Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h) ⊔
          Submodule.span (ZMod p) ({t} : Set V))
      ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) +
        Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) := hle
    _ = (N - 2) + Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({t} : Set V)) := by
        rw [hfin]
    _ ≤ (N - 2) + 1 := by omega
    _ = N - 1 := by omega

private theorem l05nTK1_moves {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {Λ : Type} {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
    {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (U : Submodule (ZMod p) V) (hU : ∀ o, h o ∈ U)
    (A' : Subgroup (MulAut ↥Bs)) (hA' : A' = Subgroup.closure (Set.range φ)) :
    ∀ a ∈ A'.map (ggLin (p := p) ι), ∀ w, a w - w ∈ U := by
  intro a ha
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
  rw [hA'] at hψ
  let Q : MulAut ↥Bs → Prop := fun ψ => ∀ w, ggLin (p := p) ι ψ w - w ∈ U
  have hgenQ : ∀ o : Option Λ, Q (φ o) := by
    intro o w
    have h1 := hφ o w
    rw [h1]
    have hsub : w - α o w • h o - w = -(α o w) • h o := by
      rw [sub_sub_cancel_left, ← neg_smul]
    rw [hsub]
    exact U.smul_mem _ (hU o)
  have honeQ : Q 1 := by
    intro w
    show ggLin (p := p) ι (1 : MulAut ↥Bs) w - w ∈ U
    rw [map_one]
    simpa using (Submodule.zero_mem U : (0 : V) ∈ U)
  have hmulQ : ∀ a b : MulAut ↥Bs, Q a → Q b → Q (a * b) := by
    intro a b ha hb w
    have h1 : ggLin (p := p) ι b w - w ∈ U := hb w
    have h2 : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) -
        (ggLin (p := p) ι b w - w) ∈ U := ha (ggLin (p := p) ι b w - w)
    have h3 : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) ∈ U := by
      have hsum : ggLin (p := p) ι a (ggLin (p := p) ι b w - w) =
          (ggLin (p := p) ι a (ggLin (p := p) ι b w - w) -
            (ggLin (p := p) ι b w - w)) + (ggLin (p := p) ι b w - w) := by abel_nf
      rw [hsum]
      exact Submodule.add_mem _ h2 h1
    have h4 : ggLin (p := p) ι a w - w ∈ U := ha w
    have hmul : ggLin (p := p) ι a (ggLin (p := p) ι b w) - w =
        ggLin (p := p) ι a (ggLin (p := p) ι b w - w) + (ggLin (p := p) ι a w - w) := by
      rw [map_sub]
      abel_nf
    rw [map_mul, LinearEquiv.mul_apply, hmul]
    exact Submodule.add_mem _ h3 h4
  have hinvQ : ∀ a : MulAut ↥Bs, Q a → Q a⁻¹ := by
    intro a ha w
    have h := ha ((ggLin (p := p) ι a)⁻¹ w)
    have hw : w - (ggLin (p := p) ι a)⁻¹ w ∈ U := by simpa using h
    have hneg : (ggLin (p := p) ι a)⁻¹ w - w =
        -(w - (ggLin (p := p) ι a)⁻¹ w) := by abel_nf
    rw [map_inv, hneg]
    exact Submodule.neg_mem _ hw
  refine Subgroup.closure_induction (k := Set.range φ) (p := fun a _ => Q a) ?_ ?_ ?_ ?_ hψ
  · rintro x ⟨o, rfl⟩
    exact hgenQ o
  · exact honeQ
  · intro x y _ _ hx hy
    exact hmulQ x y hx hy
  · intro x _ hx
    exact hinvQ x hx

private theorem l05nTK1_card_Al {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {x : G} (hx : x ∈ Bs) (ι : Additive ↥Bs ≃+ V)
    {Λ : Type} [Fintype Λ] {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    {L : Subgroup G}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (e : Fin (N - 1) ≃ Λ)
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨x, hx⟩))) :
    Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial N := by
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := by
    intro i v
    exact hφ (e i) v
  obtain ⟨ρ, hρswap, hρmem, -, -⟩ :=
    ggDepAOdd_perm_embed (p := p) (N := N) hp2 hN F r hr
  have hmap : (ggAutomizer L Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range r) := by
    rw [hAL, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨e.symm i, by simp [r]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φ (e i), ⟨e i, rfl⟩, rfl⟩
  have hcard_eq : Nat.card ↥(ggAutomizer L Bs) =
      Nat.card ↥((ggAutomizer L Bs).map (ggLin (p := p) ι)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer L Bs)
      (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv
  have hle1 : Subgroup.closure (Set.range r) ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    exact MonoidHom.mem_range.mpr
      ⟨Equiv.swap (ggDepALeft N i) (ggDepARight N i), hρswap i⟩
  have hle2 : ρ.range ≤ Subgroup.closure (Set.range r) := by
    intro y hy
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hy
    exact hρmem σ
  have hρrange : Subgroup.closure (Set.range r) = ρ.range := le_antisymm hle1 hle2
  calc Nat.card ↥(ggAutomizer L Bs)
      = Nat.card ↥((ggAutomizer L Bs).map (ggLin (p := p) ι)) := hcard_eq
    _ = Nat.card ↥(Subgroup.closure (Set.range r)) := by rw [hmap]
    _ = Nat.card ↥(ρ.range) := by rw [hρrange]
    _ ≤ Nat.card (Equiv.Perm (Fin N)) :=
        Nat.card_le_card_of_surjective
          (fun σ : Equiv.Perm (Fin N) => (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range))
          (fun y => by
            obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp y.2
            exact ⟨σ, Subtype.ext hσ⟩)
    _ = Nat.factorial N := by rw [Nat.card_perm, Nat.card_fin]

theorem ggTT_not_fixed (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    (hfix : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩) : False := by
  classical
  let bb : ↥Bs := ⟨x, hx⟩
  have hfixK' : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := hfix
  have hbb1 : (bb : G) = 1 :=
    hFixK.1 G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb (Subgroup.mem_zpowers x) hfixK'
  have hx1 : x = 1 := by simpa [bb] using hbb1
  exact ggTK_x_ne_one hH hx1

theorem ggTT_nt_sup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {ψ : MulAut ↥Bs}
    (hψ : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    ¬ (Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
      ∀ w, ggLin (p := p) ι ψ (ggLin (p := p) ι ψ w - w) = ggLin (p := p) ι ψ w - w) := by
  intro hcond
  have hψind : ψ ∈ ggInduced ⊤ Bs := by
    have hle_top : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs (le_top)) (ggAutomizer_mono Bs (le_top))
    have hmem := hle_top hψ
    rw [ggAutomizer_eq] at hmem
    exact hmem
  exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)

private theorem l05nTT_card (hOrb : GGResCentBoundInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 11 ≤ N)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    {t : MulAut ↥Bs} (htm : t ∈ ggAutomizer K Bs) {ha : V} {αa : Module.Dual (ZMod p) V}
    (hform : ∀ w, ggLin (p := p) ι t w = w - αa w • ha) :
    Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let h' : Fin (N - 1) → V := fun i => h (e i)
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  let R : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r ∪ {ra})
  let U : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h') ⊔
      Submodule.span (ZMod p) ({ha} : Set V)
  let x' : V := ι (Additive.ofMul ⟨x, hx⟩)
  let Φ : Option (Fin (N - 1)) → MulAut ↥Bs := fun o => match o with
    | none => t
    | some i => φ (e i)
  let Hf : Option (Fin (N - 1)) → V := fun o => match o with
    | none => ha
    | some i => h (e i)
  let Af : Option (Fin (N - 1)) → Module.Dual (ZMod p) V := fun o => match o with
    | none => αa
    | some i => α (e i)
  let A0 : Subgroup (MulAut ↥Bs) := Subgroup.closure (Set.range Φ)
  have hΦform : ∀ o w, ggLin (p := p) ι (Φ o) w = w - Af o w • Hf o := by
    intro o w
    cases o with
    | none => simpa [Φ, Af, Hf] using hform w
    | some i => simpa [Φ, Af, Hf] using hφ (e i) w
  have hUmem : ∀ o : Option (Fin (N - 1)), Hf o ∈ U := by
    intro o
    cases o with
    | none => exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton ha))
    | some i => exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, by simp [Hf, h']⟩)
  have hmoves := l05nTK1_moves (p := p) ι hΦform U hUmem A0 rfl
  have hR_eq : R = A0.map (ggLin (p := p) ι) := by
    show Subgroup.closure (Set.range r ∪ {ra}) = Subgroup.map (ggLin (p := p) ι) A0
    rw [show A0 = Subgroup.closure (Set.range Φ) from rfl, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨φ (e i), ⟨some i, by simp [Φ]⟩, rfl⟩
      · exact ⟨t, ⟨none, by simp [Φ]⟩, rfl⟩
    · rintro ⟨g, ⟨o, rfl⟩, rfl⟩
      cases o with
      | none => exact Or.inr rfl
      | some i => exact Or.inl ⟨i, rfl⟩
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hA0le : A0 ≤ A' := by
    rw [show A0 = Subgroup.closure (Set.range Φ) from rfl, Subgroup.closure_le]
    rintro g ⟨o, rfl⟩
    cases o with
    | none => exact Subgroup.mem_sup_right htm
    | some i => exact Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨e i, rfl⟩)
  have hRle : R ≤ A_V := by
    rw [hR_eq]
    exact Subgroup.map_mono hA0le
  have hmovesR : ∀ g ∈ R, g x' - x' ∈ U := by
    intro g hg
    rw [hR_eq] at hg
    exact hmoves g hg x'
  let orb := MulAction.orbit (↥R) x'
  have hOrbU : Nat.card orb ≤ Nat.card U := by
    refine Nat.card_le_card_of_injective
      (fun o : orb => (⟨(o : V) - x', ?_⟩ : U)) ?_
    · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp o.2
      rw [← hg]
      exact hmovesR g.1 g.2
    · intro o o' h
      apply Subtype.ext
      have hh := congrArg (fun z : U => (z : V)) h
      have h1 := congrArg (fun v : V => v + x') hh
      simpa using h1
  haveI : Finite U := Finite.of_injective (fun u : U => (u : V)) Subtype.val_injective
  have hUcard : Nat.card U = p ^ Module.finrank (ZMod p) ↥U :=
    (FiniteField.pow_finrank_eq_natCard p U).symm
  have hOrb_card : Nat.card orb ≤ p ^ (N - 1) := by
    calc Nat.card orb ≤ Nat.card U := hOrbU
      _ = p ^ Module.finrank (ZMod p) ↥U := hUcard
      _ ≤ p ^ (N - 1) :=
        Nat.pow_le_pow_right (by have h : 2 ≤ p := (Fact.out : p.Prime).two_le; omega)
          (l05nTK1_finrank_U F ha)
  have hstab : Nat.card ↥(MulAction.stabilizer (↥R) x') ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := by
    let E : ↥A' ≃* ↥A_V :=
      Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)
    let fA : ↥(MulAction.stabilizer (↥R) x') → ↥A' :=
      fun s => E.symm ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩
    have hfA : Function.Injective fA := by
      intro s s' h
      have hE1 : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by
        simp [fA]
      have hE2 : E (fA s') = ⟨(s'.1 : V ≃ₗ[ZMod p] V), hRle s'.1.2⟩ := by
        simp [fA]
      have hg : (s.1 : V ≃ₗ[ZMod p] V) = (s'.1 : V ≃ₗ[ZMod p] V) := by
        have hEE : E (fA s) = E (fA s') := by rw [h]
        have := congrArg (fun z : ↥A_V => (z : V ≃ₗ[ZMod p] V)) (hE1.symm.trans (hEE.trans hE2))
        simpa using this
      exact Subtype.ext (Subtype.ext hg)
    let f : ↥(MulAction.stabilizer (↥R) x') →
        ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
      fun s => ⟨(fA s : MulAut ↥Bs), ⟨(fA s).2, by
        change (fA s : MulAut ↥Bs) • (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩
        have hE : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by
          simp [fA]
        have hval : ggLin (p := p) ι (fA s : MulAut ↥Bs) = (s.1 : V ≃ₗ[ZMod p] V) := by
          have hE : E (fA s) = ⟨(s.1 : V ≃ₗ[ZMod p] V), hRle s.1.2⟩ := by simp [fA]
          have h2 := congrArg (fun z : ↥A_V => (z : V ≃ₗ[ZMod p] V)) hE
          change (E (fA s) : V ≃ₗ[ZMod p] V) = (s.1 : V ≃ₗ[ZMod p] V)
          exact h2
        have hgx : (s.1 : V ≃ₗ[ZMod p] V) x' = x' := by
          have hs := MulAction.mem_stabilizer_iff.mp s.2
          change (s.1 : V ≃ₗ[ZMod p] V) x' = x' at hs
          exact hs
        have hlin : ggLin (p := p) ι (fA s : MulAut ↥Bs) x' = x' := by
          rw [hval]; exact hgx
        have hpt : (fA s : MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs) = ⟨x, hx⟩ := by
          have h2 := hlin
          simp only [x', ggLin_apply_ofMul] at h2
          exact Additive.ofMul.injective (ι.injective h2)
        simpa using hpt⟩⟩
    have hf : Function.Injective f := by
      intro s s' h
      have h1 : ((f s).1 : MulAut ↥Bs) = ((f s').1 : MulAut ↥Bs) :=
        congrArg (fun z => (z.1 : MulAut ↥Bs)) h
      exact hfA (Subtype.ext h1)
    calc Nat.card ↥(MulAction.stabilizer (↥R) x')
        ≤ Nat.card ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) :=
          Nat.card_le_card_of_injective f hf
      _ ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := hOrb G p B Bs x L D J y K hH hx
  have hAl : Nat.card ↥(ggAutomizer L Bs) ≤ Nat.factorial N :=
    l05nTK1_card_Al hp2 (by omega : 5 ≤ N) hx ι hφ hAL e F
  have hRcard : Nat.card ↥R = Nat.card orb * Nat.card ↥(MulAction.stabilizer (↥R) x') := by
    haveI : Finite (V ≃ₗ[ZMod p] V) :=
      Finite.of_injective (fun g : V ≃ₗ[ZMod p] V => (g : V → V))
        (fun _ _ h => LinearEquiv.ext (congrFun h))
    haveI : Finite ↥R := Finite.of_injective (fun g : ↥R => (g : V ≃ₗ[ZMod p] V))
      Subtype.val_injective
    haveI : Fintype ↥R := Fintype.ofFinite ↥R
    haveI : Fintype orb := Fintype.ofFinite orb
    haveI : Fintype ↥(MulAction.stabilizer (↥R) x') := Fintype.ofFinite _
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥R) x'
    simp only [← Nat.card_eq_fintype_card] at hOS
    exact hOS.symm
  calc Nat.card ↥R = Nat.card orb * Nat.card ↥(MulAction.stabilizer (↥R) x') := hRcard
    _ ≤ p ^ (N - 1) * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
        Nat.mul_le_mul hOrb_card hstab
    _ ≤ p ^ (N - 1) * ((p - 1) * 6 * Nat.factorial N) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hAl)
    _ ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) := by
        have hpow : p ^ (N - 1) ≤ p ^ N :=
          Nat.pow_le_pow_right (by have h : 2 ≤ p := (Fact.out : p.Prime).two_le; omega)
            (by omega : N - 1 ≤ N)
        have heq : ((p - 1) * 6) * Nat.factorial N = (6 * (p - 1)) * Nat.factorial N := by
          rw [Nat.mul_comm (p - 1) 6]
        rw [heq]
        exact Nat.mul_le_mul_right _ hpow

private theorem l05nTK2_rtg_symm {α : Type*} {R : α → α → Prop}
    (hsymm : ∀ a c, R a c → R c a) {a b : α}
    (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.head (hsymm _ _ hbc)

private theorem l05nTK2_first_edge {α : Type*} {R : α → α → Prop}
    (hsymm : ∀ a c, R a c → R c a) {start b : α}
    (h : Relation.ReflTransGen R start b) (hb : b ≠ start) : ∃ c, R start c := by
  have h' : Relation.ReflTransGen R b start := l05nTK2_rtg_symm hsymm h
  have hgoal : b = start ∨ ∃ c, R start c :=
    Relation.ReflTransGen.head_induction_on (r := R) (b := start) h'
      (motive := fun x _ => x = start ∨ ∃ c, R start c)
      (Or.inl rfl)
      (by
        intro p q hpq _ ih
        rcases ih with hq | hex
        · rw [hq] at hpq
          exact Or.inr ⟨p, hsymm _ _ hpq⟩
        · exact Or.inr hex)
  rcases hgoal with hh | hex
  · exact absurd hh hb
  · exact hex

private theorem l05nTK2_nonempty_of_weyl {ι : Type} {M : CoxeterMatrix ι}
    (hW : GGIsWeylMatrix M) : Nonempty ι := by
  rcases hW with ⟨n, e, hn, -⟩ | hE6 | hE7 | hE8 | hF4 | hG2
  · exact ⟨e ⟨0, by omega⟩⟩
  · obtain ⟨e, -⟩ := hE6
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hE7
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hE8
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hF4
    exact ⟨e 0⟩
  · obtain ⟨e, -⟩ := hG2
    exact ⟨e 0⟩

private theorem l05nTK2_nt_closure
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    {t : MulAut ↥Bs} (htm : t ∈ ggAutomizer K Bs) :
    ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
  classical
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A_V : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  have hgenL : ∀ i : Fin (N - 1), ggLin (p := p) ι (φ (e i)) ∈ A_V := by
    intro i
    refine Subgroup.mem_map.mpr ⟨φ (e i), ?_, rfl⟩
    exact Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨e i, rfl⟩)
  have hgenN : ggLin (p := p) ι t ∈ A_V := by
    refine Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩
    exact Subgroup.mem_sup_right htm
  have hle : Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
        ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t}) ≤ A_V := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · obtain ⟨i, rfl⟩ := hy
      exact hgenL i
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hgenN
  intro g hg hcond
  have hgA : g ∈ A_V := hle hg
  obtain ⟨ψ, hψA, hψeq⟩ := Subgroup.mem_map.mp hgA
  have hψsup : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := hψA
  have hcond' : Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
      ∀ w, ggLin (p := p) ι ψ (ggLin (p := p) ι ψ w - w) = ggLin (p := p) ι ψ w - w := by
    rwa [hψeq]
  exact ggTT_nt_sup hH ι hψsup hcond'

private theorem l05nTK2_label_two {G : Type} [Group G] [Finite G]
    {Bs K : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    {φ : ι → MulAut ↥Bs} {f : M.Group ≃* ↥(ggAutomizer K Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    {i j : ι} (hij : i ≠ j) (hcomm : φ i * φ j = φ j * φ i) :
    M.M i j = 2 := by
  have hcomm_group : M.simple i * M.simple j = M.simple j * M.simple i := by
    apply f.injective
    apply Subtype.ext
    rw [map_mul, map_mul]
    show ((f (M.simple i) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) *
          ((f (M.simple j) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) =
        ((f (M.simple j) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) *
          ((f (M.simple i) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs)
    rw [hf i, hf j]
    exact hcomm
  have hi2 : M.simple i * M.simple i = 1 := by
    have := CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem i
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using this
  have hj2 : M.simple j * M.simple j = 1 := by
    have := CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem j
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using this
  have h2 : (M.simple i * M.simple j)^2 = 1 := by
    have key : (M.simple i * M.simple j) * (M.simple i * M.simple j) =
        M.simple i * M.simple i * (M.simple j * M.simple j) := by
      calc (M.simple i * M.simple j) * (M.simple i * M.simple j)
          = M.simple i * (M.simple j * M.simple i) * M.simple j := by group
        _ = M.simple i * (M.simple i * M.simple j) * M.simple j := by
              rw [← hcomm_group]
        _ = M.simple i * M.simple i * (M.simple j * M.simple j) := by group
    rw [pow_two, key, hi2, hj2, mul_one]
  have hord : orderOf (M.simple i * M.simple j) = M.M i j := by
    have := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem i j
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using this
  have hdvd : M.M i j ∣ 2 := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr h2
  have hM1 : M.M i j ≠ 1 := M.off_diagonal i j hij
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2'
  · exact absurd h1 hM1
  · exact h2'

private theorem l05nTKS_adj {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hWM : GGIsWeylMatrix M) (S : ι → Prop) (hj₀ : ∃ j : ι, ¬ S j) {b : ι}
    (hzero : ∀ j : ι, ¬ S j → M.M b j = 2) :
    ∃ b' : ι, S b' ∧ b' ≠ b ∧ M.M b b' ≠ 2 := by
  obtain ⟨j₀, hj₀⟩ := hj₀
  by_cases hb : j₀ = b
  · exfalso
    have h2 : M.M b b = 2 := hzero b (hb ▸ hj₀)
    rw [M.diagonal] at h2
    omega
  · have hpath := ggRC_weyl_connected hWM b j₀
    have hsymm : ∀ a c : ι, (a ≠ c ∧ M.M a c ≠ 2) → (c ≠ a ∧ M.M c a ≠ 2) := by
      rintro a c ⟨hne, h2⟩
      exact ⟨hne.symm, by rwa [M.symmetric c a]⟩
    obtain ⟨c, hc⟩ := l05nTK2_first_edge hsymm hpath hb
    refine ⟨c, ?_, hc.1.symm, hc.2⟩
    by_contra hSc
    exact hc.2 (hzero c hSc)

private theorem l05nTKS_core
    (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    {ΛK : Type} [Fintype ΛK] [DecidableEq ΛK] (S : ΛK → Prop) {MK : CoxeterMatrix ΛK}
    (hWMK : GGIsWeylMatrix MK) {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
    {ιK : Additive ↥Bs ≃+ VK} {φK : ΛK → MulAut ↥Bs} {hKc : ΛK → VK}
    {αK : ΛK → Module.Dual (ZMod p) VK}
    (hlinK : ∀ i w, ggLin (p := p) ιK (φK i) w = w - αK i w • hKc i)
    (hpairK : ∀ i, αK i (hKc i) = 2)
    (hfK : ∃ f : MK.Group ≃* ↥(ggAutomizer K Bs), ∀ i, (f (MK.simple i) : MulAut ↥Bs) = φK i)
    (hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φK))
    (hJne : ∃ j, ¬ S j) (hJφ : ∀ j, ¬ S j → φK j ∈ ggAutomizer J Bs) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V), t ∈ ggAutomizer K Bs ∧
      (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧ (∃ c : Fin (N - 1), αa (h (e c)) ≠ 0) := by
  classical
  have hJL : J ≤ L := (hH.1.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
  obtain ⟨fK, hfKp⟩ := hfK
  let eK : VK ≃ₗ[ZMod p] V := LinearEquiv.ofBijective
      ((ιK.symm.trans ι).toAddMonoidHom.toZModLinearMap p) (ιK.symm.trans ι).bijective
  have he : ∀ w : VK, eK w = ι (ιK.symm w) := by
    intro w
    change (ιK.symm.trans ι) w = ι (ιK.symm w)
    rfl
  have hes : ∀ w : V, eK.symm w = ιK (ι.symm w) := by
    intro w
    apply eK.injective
    rw [LinearEquiv.apply_symm_apply, he]
    simp
  let haF : ΛK → V := fun b => eK (hKc b)
  let αaF : ΛK → Module.Dual (ZMod p) V := fun b =>
    (αK b).comp (eK.symm : V ≃ₗ[ZMod p] VK).toLinearMap
  have hformF : ∀ b w, ggLin (p := p) ι (φK b) w = w - αaF b w • haF b := by
    intro b w
    have h1 : ggLin (p := p) ι (φK b) w = eK (ggLin (p := p) ιK (φK b) (eK.symm w)) := by
      rw [he, hes, ggLin_apply, ggLin_apply]
      congr 1
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rw [h1, hlinK b (eK.symm w), map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  have hhaF : ∀ b, αaF b (haF b) = 2 := by
    intro b
    show (αK b).comp (eK.symm : V ≃ₗ[ZMod p] VK).toLinearMap (eK (hKc b)) = 2
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
    exact hpairK b
  have htmF : ∀ b, φK b ∈ ggAutomizer K Bs := by
    intro b
    rw [hclosK]
    exact Subgroup.subset_closure ⟨b, rfl⟩
  have hval : ∀ b : ΛK, αaF b (ι (Additive.ofMul ⟨x, hx⟩)) =
      αK b (ιK (Additive.ofMul ⟨x, hx⟩)) := by
    intro b
    show (αK b).comp (eK.symm : V ≃ₗ[ZMod p] VK).toLinearMap
        (ι (Additive.ofMul ⟨x, hx⟩)) = _
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hes]
    congr 1
    rw [AddEquiv.symm_apply_apply]
  have hx0 : ∀ i : Λ, α i (ι (Additive.ofMul ⟨x, hx⟩)) = 0 := by
    intro i
    have := F.x_ker (e.symm i)
    simpa using this
  have hALfix : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [hAL]
    refine ggFixed_of_mem_closure φ ⟨x, hx⟩ ?_
    intro i
    refine (ggLin_fix_iff (p := p) ι (φ i) ⟨x, hx⟩).mpr ?_
    rw [hφ i, hx0 i, zero_smul, sub_zero]
  have hAJle : ggAutomizer J Bs ≤ ggAutomizer L Bs := ggAutomizer_mono Bs hJL
  have hfixJ : ∀ ψ ∈ ggAutomizer J Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    fun ψ hψ => hALfix ψ (hAJle hψ)
  have hJmove_zero : ∀ j : ΛK, ¬ S j → αaF j (ι (Additive.ofMul ⟨x, hx⟩)) = 0 := by
    intro j hj
    have hfixj : φK j ⟨x, hx⟩ = ⟨x, hx⟩ := hfixJ (φK j) (hJφ j hj)
    have hlin : ggLin (p := p) ιK (φK j) (ιK (Additive.ofMul ⟨x, hx⟩)) =
        ιK (Additive.ofMul ⟨x, hx⟩) :=
      (ggLin_fix_iff (p := p) ιK (φK j) ⟨x, hx⟩).mp hfixj
    rw [hlinK j] at hlin
    have hsm : αK j (ιK (Additive.ofMul ⟨x, hx⟩)) • hKc j = 0 := sub_eq_self.mp hlin
    have hKc_ne : hKc j ≠ 0 := by
      intro h0
      have h2 := hpairK j
      rw [h0, map_zero] at h2
      exact (zmod_two_ne_zero hp2) h2.symm
    have h0 : αK j (ιK (Additive.ofMul ⟨x, hx⟩)) = 0 :=
      (smul_eq_zero.mp hsm).resolve_right hKc_ne
    rw [hval j, h0]
  have hsome_move : ∃ b : ΛK, αaF b (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 := by
    by_contra h
    push Not at h
    have hχ : ∀ i : ΛK, φK i ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro i
      by_cases hi : S i
      · refine (ggLin_fix_iff (p := p) ιK (φK i) ⟨x, hx⟩).mpr ?_
        have h0 : αK i (ιK (Additive.ofMul ⟨x, hx⟩)) = 0 := by
          rw [← hval i]; exact h i
        rw [hlinK i, h0, zero_smul, sub_zero]
      · exact hfixJ (φK i) (hJφ i hi)
    have hfixK' : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hclosK]
      exact ggFixed_of_mem_closure φK ⟨x, hx⟩ hχ
    exact ggTT_not_fixed hFixK hH hx hfixK'
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have key : ∀ b : ΛK, S b → αaF b (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 →
      (∀ y : ΛK, S y → αaF y (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 →
        ∀ c, αaF y (h (e c)) = 0) →
      (∀ c, αaF b (h (e c)) = 0) → False := by
    intro b hSb hbmov hnone_b hbnj
    have hntA_b := l05nTK2_nt_closure hH hx e hφ hAL (htmF b)
    obtain ⟨⟨f, hfx, hra_form⟩, hcomm_c⟩ :=
      l05nTT_root_form (p := p) hp2 F r hr (ggLin (p := p) ι (φK b)) (haF b) (αaF b)
        (hformF b) (hhaF b) hbmov hntA_b hbnj
    have hM2 : ∀ j : ΛK, ¬ S j → MK.M b j = 2 := by
      intro j hj
      have hle_cz : Subgroup.closure (Set.range r) ≤
          Subgroup.centralizer ({ggLin (p := p) ι (φK b)} : Set (V ≃ₗ[ZMod p] V)) := by
        rw [Subgroup.closure_le]
        rintro g ⟨c, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm_c c)
      have hmapAL : (ggAutomizer L Bs).map (ggLin (p := p) ι) =
          Subgroup.closure (Set.range r) := by
        rw [hAL, MonoidHom.map_closure]
        congr 1
        ext y
        constructor
        · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
          exact ⟨e.symm i, by simp [r]⟩
        · rintro ⟨i, rfl⟩
          exact ⟨φ (e i), ⟨e i, rfl⟩, rfl⟩
      have hφjJ : φK j ∈ ggAutomizer J Bs := hJφ j hj
      have hφjL : φK j ∈ ggAutomizer L Bs := (ggAutomizer_mono Bs hJL) hφjJ
      have hlinj : ggLin (p := p) ι (φK j) ∈ Subgroup.closure (Set.range r) := by
        rw [← hmapAL]
        exact Subgroup.mem_map.mpr ⟨φK j, hφjL, rfl⟩
      have hcomm_j : ggLin (p := p) ι (φK j) * ggLin (p := p) ι (φK b) =
          ggLin (p := p) ι (φK b) * ggLin (p := p) ι (φK j) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hle_cz hlinj)
      have hcomm_tj : φK j * φK b = φK b * φK j := by
        have hcomm_j' : ggLin (p := p) ι (φK j * φK b) =
            ggLin (p := p) ι (φK b * φK j) := by
          rw [map_mul, map_mul]
          exact hcomm_j
        exact ggLin_injective (p := p) ι hcomm_j'
      have hjne_b : b ≠ j := fun hh => hj (hh ▸ hSb)
      exact l05nTK2_label_two hfKp hjne_b hcomm_tj.symm
    obtain ⟨b', hSb', hb'ne, hMbb'⟩ := l05nTKS_adj hWMK S hJne hM2
    have hnoncomm : φK b * φK b' ≠ φK b' * φK b := fun hcomm =>
      hMbb' (l05nTK2_label_two hfKp hb'ne.symm hcomm)
    by_cases hb'mov : αaF b' (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0
    · have hntA_b' := l05nTK2_nt_closure hH hx e hφ hAL (htmF b')
      obtain ⟨⟨g, hgx, hrb_form⟩, -⟩ :=
        l05nTT_root_form (p := p) hp2 F r hr (ggLin (p := p) ι (φK b')) (haF b') (αaF b')
          (hformF b') (hhaF b') hb'mov hntA_b' (hnone_b b' hSb' hb'mov)
      by_cases hfg : f = g
      · have hra_eq : ggLin (p := p) ι (φK b) = ggLin (p := p) ι (φK b') := by
          ext w
          rw [hra_form, hrb_form, hfg]
        have ht_eq : φK b = φK b' := ggLin_injective (p := p) ι hra_eq
        exact hnoncomm (by rw [ht_eq])
      · have htrans := l05nTT_root_prod (p := p) (x := ι (Additive.ofMul ⟨x, hx⟩)) F.x_ne
          hfx hgx hfg (ggLin (p := p) ι (φK b)) (ggLin (p := p) ι (φK b'))
          hra_form hrb_form
        have hmem : φK b * φK b' ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
          Subgroup.mem_sup_right (Subgroup.mul_mem _ (htmF b) (htmF b'))
        have htrans' : Module.finrank (ZMod p)
            (ggLinMove (ggLin (p := p) ι (φK b * φK b'))) = 1 ∧
            ∀ w, ggLin (p := p) ι (φK b * φK b')
              (ggLin (p := p) ι (φK b * φK b') w - w) =
              ggLin (p := p) ι (φK b * φK b') w - w := by
          rw [map_mul]
          exact htrans
        exact ggTT_nt_sup hH ι hmem htrans'
    · push Not at hb'mov
      have hu_x : ggLin (p := p) ι (φK b') (ι (Additive.ofMul ⟨x, hx⟩)) =
          ι (Additive.ofMul ⟨x, hx⟩) := by
        rw [hformF b' (ι (Additive.ofMul ⟨x, hx⟩)), hb'mov, zero_smul, sub_zero]
      let u : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φK b')
      have hu_x' : u (ι (Additive.ofMul ⟨x, hx⟩)) = ι (Additive.ofMul ⟨x, hx⟩) := hu_x
      let g : Module.Dual (ZMod p) V := f.comp (u.symm : V ≃ₗ[ZMod p] V).toLinearMap
      have hgx : g (ι (Additive.ofMul ⟨x, hx⟩)) = 2 := by
        have hus : u.symm (ι (Additive.ofMul ⟨x, hx⟩)) = ι (Additive.ofMul ⟨x, hx⟩) := by
          apply u.injective
          rw [LinearEquiv.apply_symm_apply, hu_x']
        show f (u.symm (ι (Additive.ofMul ⟨x, hx⟩))) = 2
        rw [hus, hfx]
      have hconj_form : ∀ w, (u * ggLin (p := p) ι (φK b) * u.symm) w =
          w - g w • ι (Additive.ofMul ⟨x, hx⟩) := by
        intro w
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hra_form (u.symm w), map_sub, map_smul,
          LinearEquiv.apply_symm_apply, hu_x']
        rfl
      by_cases hfg : f = g
      · have hconj_eq : u * ggLin (p := p) ι (φK b) * u.symm =
            ggLin (p := p) ι (φK b) := by
          ext w
          rw [hconj_form w, hra_form w, hfg]
        have hcomm' : u * ggLin (p := p) ι (φK b) =
            ggLin (p := p) ι (φK b) * u := by
          ext w
          have h := congrArg (fun z : V ≃ₗ[ZMod p] V => z (u w)) hconj_eq
          simp only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply] at h
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
          exact h
        apply hnoncomm
        have hlin : ggLin (p := p) ι (φK b' * φK b) =
            ggLin (p := p) ι (φK b * φK b') := by
          rw [map_mul, map_mul]
          exact hcomm'
        have ht : φK b' * φK b = φK b * φK b' := ggLin_injective (p := p) ι hlin
        exact ht.symm
      · have htrans := l05nTT_root_prod (p := p) (x := ι (Additive.ofMul ⟨x, hx⟩)) F.x_ne
          hfx hgx hfg (ggLin (p := p) ι (φK b))
          (u * ggLin (p := p) ι (φK b) * u.symm) hra_form hconj_form
        have hmem : φK b * (φK b' * φK b * (φK b')⁻¹) ∈
            ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
          refine Subgroup.mem_sup_right ?_
          exact Subgroup.mul_mem _ (htmF b)
            (Subgroup.mul_mem _ (Subgroup.mul_mem _ (htmF b') (htmF b))
              (Subgroup.inv_mem _ (htmF b')))
        have heq : ggLin (p := p) ι (φK b * (φK b' * φK b * (φK b')⁻¹)) =
            ggLin (p := p) ι (φK b) * (u * ggLin (p := p) ι (φK b) * u.symm) := by
          simp only [map_mul, map_inv]
          rfl
        have htrans' : Module.finrank (ZMod p)
            (ggLinMove (ggLin (p := p) ι (φK b * (φK b' * φK b * (φK b')⁻¹)))) = 1 ∧
            ∀ w, ggLin (p := p) ι (φK b * (φK b' * φK b * (φK b')⁻¹))
              (ggLin (p := p) ι (φK b * (φK b' * φK b * (φK b')⁻¹)) w - w) =
              ggLin (p := p) ι (φK b * (φK b' * φK b * (φK b')⁻¹)) w - w := by
          rw [heq]
          exact htrans
        exact ggTT_nt_sup hH ι hmem htrans'
  have hgood : ∃ b : ΛK, αaF b (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧
      (∃ c, αaF b (h (e c)) ≠ 0) := by
    obtain ⟨b, hbmov⟩ := hsome_move
    have hSb : S b := by
      by_contra hbS
      exact hbmov (hJmove_zero b hbS)
    by_contra hbad
    have hnone : ∀ y : ΛK, S y → αaF y (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 →
        ∀ c, αaF y (h (e c)) = 0 := by
      intro y hy hymov c
      by_contra hc
      exact hbad ⟨y, hymov, ⟨c, hc⟩⟩
    exact key b hSb hbmov hnone (hnone b hSb hbmov)
  obtain ⟨b, hbmov, hbjoin⟩ := hgood
  exact ⟨φK b, haF b, αaF b, htmF b, hformF b, hhaF b, hbmov, hbjoin⟩

private theorem l05nTK2_core
    (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    (hK : GGResTwoNodeSideDatum p Bs K J) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V), t ∈ ggAutomizer K Bs ∧
      (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧ (∃ c : Fin (N - 1), αa (h (e c)) ≠ 0) := by
  classical
  obtain ⟨ΛK, iKf, iKd, b₁, b₂, MK, CK, MJ, VK, iKac, iKm, ιK, φK, hKc, αK,
    hb, hWMK, hCK, hWMJ, hMJ, hlinK, hreflK, hpairK, hKf, hclosK, hKfJ, hclosJ, hconjK⟩ := hK
  exact l05nTKS_core hFixK hp2 hH hx e hφ hAL F (fun j => j = b₁ ∨ j = b₂) hWMK hlinK
    (fun i => by have h1 := hpairK i i; rw [hCK.1 i] at h1; simpa using h1) hKf hclosK
    (by
      obtain ⟨j₀⟩ := l05nTK2_nonempty_of_weyl hWMJ
      exact ⟨j₀.1, by push Not; exact j₀.2⟩)
    (fun j hj => by
      rw [hclosJ]
      refine Subgroup.subset_closure ⟨⟨j, ?_⟩, rfl⟩
      push Not at hj
      exact hj)

private theorem l05nTK3_core
    (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    (hK : GGResLeviSideDatumLE3 p Bs K J) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V), t ∈ ggAutomizer K Bs ∧
      (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧ (∃ c : Fin (N - 1), αa (h (e c)) ≠ 0) := by
  classical
  obtain ⟨ΛK, iKf, iKd, SK, MK, CK, MJ, VK, iKac, iKm, ιK, φK, hKc, αK,
    hS2, hS3, hWMK, hCK, hWMJ, hMJ, hlinK, hreflK, hpairK, hKf, hclosK, hKfJ, hclosJ,
    hconjK⟩ := hK
  exact l05nTKS_core hFixK hp2 hH hx e hφ hAL F (fun j => j ∈ SK) hWMK hlinK
    (fun i => by have h1 := hpairK i i; rw [hCK.1 i] at h1; simpa using h1) hKf hclosK
    (by
      obtain ⟨j₀⟩ := l05nTK2_nonempty_of_weyl hWMJ
      exact ⟨j₀.1, j₀.2⟩)
    (fun j hj => by
      rw [hclosJ]
      refine Subgroup.subset_closure ⟨⟨j, ?_⟩, rfl⟩
      simpa using hj)

theorem ggTwoNodeTwo_kside (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 11 ≤ N) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    (hK : GGResTwoNodeSideDatum p Bs K J) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V), t ∈ ggAutomizer K Bs ∧
      (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧ (∃ c : Fin (N - 1), αa (h (e c)) ≠ 0) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (e i))) ∪
          {ggLin (p := p) ι t}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t})) ≤
        p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  obtain ⟨t, ha, αa, htm, hform, hha, hxne, hjoin⟩ :=
    l05nTK2_core hFixK hp2 hH hx e hφ hAL F hK
  exact ⟨t, ha, αa, htm, hform, hha, hxne, hjoin,
    l05nTK2_nt_closure hH hx e hφ hAL htm,
    l05nTT_card hOrb hp2 hH hx hN e hφ hAL F htm hform⟩

theorem ggTwoNodeLE3_kside (hFixK : GGTBFixNbrInput) (hOrb : GGResCentBoundInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 11 ≤ N) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)))
    (hK : GGResLeviSideDatumLE3 p Bs K J) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V), t ∈ ggAutomizer K Bs ∧
      (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 ∧ (∃ c : Fin (N - 1), αa (h (e c)) ≠ 0) ∧
      (∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (e i))) ∪
          {ggLin (p := p) ι t}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      Nat.card ↥(Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          ggLin (p := p) ι (φ (e i))) ∪ {ggLin (p := p) ι t})) ≤
        p ^ N * (6 * (p - 1) * Nat.factorial N) := by
  obtain ⟨t, ha, αa, htm, hform, hha, hxne, hjoin⟩ :=
    l05nTK3_core hFixK hp2 hH hx e hφ hAL F hK
  exact ⟨t, ha, αa, htm, hform, hha, hxne, hjoin,
    l05nTK2_nt_closure hH hx e hφ hAL htm,
    l05nTT_card hOrb hp2 hH hx hN e hφ hAL F htm hform⟩

theorem ggTwoNodeAtL_false (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hxL : x ∉ L) {N : ℕ}
    (hN : 11 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hK : GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J ∨
      GGResLeviSideDatumLE3 p Bs K J) : False := by
  have hN5 : 5 ≤ N := by omega
  haveI : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hdep : ¬ LinearIndependent (ZMod p) h :=
    ggXDatumA_dep hFix hp2 hH hx hxL hN5 hpN e hML hCL hφ hpair hAL
  let F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨x, hx⟩)) :=
    ggXDatumA_frame hFix hp2 hH hx hN5 hpN e hML hCL hφ hpair hAL hdep
  obtain ⟨t, ha, αa, htK, htlin, hαaha, hαax, hjoin, hnt, hcard⟩ :=
    hK.elim
      (fun hK => ggTwoNodeOdd_kside hFixK hOrb hp2 hH hx hN e hφ hAL F hK)
      (fun hK => hK.elim
        (fun hK => ggTwoNodeTwo_kside hFixK hOrb hp2 hH hx hN e hφ hAL F hK)
        (fun hK => ggTwoNodeLE3_kside hFixK hOrb hp2 hH hx hN e hφ hAL F hK))
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  have hr : ∀ i v, r i v = v - α (e i) v • h (e i) := by
    intro i v
    exact hφ (e i) v
  have hra : ∀ v, ra v = v - αa v • ha := by
    intro v
    exact htlin v
  have hnt' : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    simpa only [r, ra] using hnt
  have hcard' : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N) := by
    simpa only [r, ra] using hcard
  by_cases hHa : ha ∈ Submodule.span (ZMod p) (Set.range (fun i : Fin (N - 1) => h (e i)))
  · exact ggDepAOdd_caseII_false hKG hp2 hN F r hr ra ha αa hra hαaha hαax hnt' hcard' hHa
  · refine ggDepAOdd_caseI_false hKG hp2 hN F r hr ra ha αa hra hαaha ?_ hαax hnt' hcard' hHa
    obtain ⟨c, hc⟩ := hjoin
    exact ⟨c, hc⟩

end CFSG.StandardType
