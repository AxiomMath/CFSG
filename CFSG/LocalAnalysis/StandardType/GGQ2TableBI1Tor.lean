module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Frame
public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGStdSubExist
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_shape_linear {p : ℕ} [Fact p.Prime] {N : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {C : Matrix (Fin N) (Fin N) ℤ}
    (hrank : N ≤ (C.map (Int.castRingHom (ZMod p))).rank + 1) (h : Fin N → V)
    (α : Fin N → Module.Dual (ZMod p) V) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {v : V} (hv0 : v ≠ 0) (hker : (LinearMap.pi α).ker = Submodule.span (ZMod p) {v}) :
    (LinearIndependent (ZMod p) h ∧ v ∉ Submodule.span (ZMod p) (Set.range h) ∧
        Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) {v} = ⊤) ∨
      (LinearIndependent (ZMod p) h ∧ v ∈ Submodule.span (ZMod p) (Set.range h) ∧
        Module.finrank (ZMod p) V = N + 1 ∧ Function.Surjective (LinearMap.pi α)) ∨
      (Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) + 1 = N ∧
        v ∉ Submodule.span (ZMod p) (Set.range h) ∧
        Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) {v} = ⊤) ∨
      (Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) + 1 = N ∧
        v ∉ Submodule.span (ZMod p) (Set.range h) ∧
        Module.finrank (ZMod p) V = N + 1 ∧ Function.Surjective (LinearMap.pi α)) ∨
      (LinearIndependent (ZMod p) h ∧ Submodule.span (ZMod p) (Set.range h) = ⊤) := by
  classical
  let D : Matrix (Fin N) (Fin N) (ZMod p) := C.map (Int.castRingHom (ZMod p))
  let ρ : V →ₗ[ZMod p] (Fin N → ZMod p) := LinearMap.pi α
  let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  have hrankD : N ≤ D.rank + 1 := hrank
  have hkerρ : ρ.ker = Submodule.span (ZMod p) {v} := by simpa [ρ] using hker
  have hρh : ρ ∘ h = D.col := by
    funext j i
    simpa [ρ, D, Matrix.col] using hpair i j
  have hHmap : H.map ρ = LinearMap.range D.mulVecLin := by
    simp only [H]
    rw [Submodule.map_span, ← Set.range_comp, hρh, ← Matrix.range_mulVecLin]
  have hHmap_fin : Module.finrank (ZMod p) (H.map ρ) = D.rank := by
    rw [hHmap]
    rfl
  have hDrank_le : D.rank ≤ N := Matrix.rank_le_width D
  have hDcases : D.rank = N ∨ D.rank + 1 = N := by omega
  have hVrank : Module.finrank (ZMod p) V =
      Module.finrank (ZMod p) (LinearMap.range ρ) + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ρ
    rw [hkerρ, finrank_span_singleton hv0] at h
    omega
  have hRange_le : Module.finrank (ZMod p) (LinearMap.range ρ) ≤ N := by
    simpa using Submodule.finrank_le (LinearMap.range ρ)
  have hRange_ge : D.rank ≤ Module.finrank (ZMod p) (LinearMap.range ρ) := by
    rw [← hHmap_fin]
    exact Submodule.finrank_mono (LinearMap.map_le_range (p := H) (f := ρ))
  have hVcases : Module.finrank (ZMod p) V = N ∨
      Module.finrank (ZMod p) V = N + 1 := by omega
  have hkerfin : Module.finrank (ZMod p) (LinearMap.ker (ρ.domRestrict H)) =
      Module.finrank (ZMod p) ↥(H ⊓ Submodule.span (ZMod p) {v}) := by
    rw [LinearMap.ker_domRestrict, hkerρ,
      ← Submodule.finrank_map_subtype_eq H, Submodule.map_comap_subtype]
  have hinf : Module.finrank (ZMod p) ↥(H ⊓ Submodule.span (ZMod p) {v}) =
      if v ∈ H then 1 else 0 := by
    by_cases hvH : v ∈ H
    · rw [if_pos hvH]
      have hle : Submodule.span (ZMod p) {v} ≤ H :=
        (Submodule.span_singleton_le_iff_mem v H).mpr hvH
      rw [inf_eq_right.mpr hle, finrank_span_singleton hv0]
    · rw [if_neg hvH]
      rw [disjoint_iff.mp ((Submodule.disjoint_span_singleton' hv0).mpr hvH), finrank_bot]
  have hHrank : Module.finrank (ZMod p) H =
      D.rank + (if v ∈ H then 1 else 0) := by
    have h := LinearMap.finrank_range_add_finrank_ker (ρ.domRestrict H)
    rw [LinearMap.range_domRestrict, hHmap_fin, hkerfin, hinf] at h
    exact h.symm
  have hHle : Module.finrank (ZMod p) H ≤ N := by
    have h := finrank_range_le_card (R := ZMod p) h
    simpa [H, Set.finrank, Fintype.card_fin] using h
  have hLI_of_finrank : Module.finrank (ZMod p) H = N → LinearIndependent (ZMod p) h := by
    intro hHr
    refine linearIndependent_iff_card_eq_finrank_span.mpr ?_
    simpa [Set.finrank, H, Fintype.card_fin] using hHr.symm
  have hsurj : Module.finrank (ZMod p) (LinearMap.range ρ) = N →
      Function.Surjective ρ := by
    intro hN
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [hN]
    exact (Module.finrank_fin_fun (R := ZMod p) (n := N)).symm
  rcases hDcases with hD | hD
  · have hvH : v ∉ H := by
      rintro hvH
      have hHr : Module.finrank (ZMod p) H = N + 1 := by
        rw [hHrank, if_pos hvH, hD]
      omega
    have hHr : Module.finrank (ZMod p) H = N := by
      rw [hHrank, if_neg hvH, add_zero, hD]
    have hLI : LinearIndependent (ZMod p) h := hLI_of_finrank hHr
    have hVN : Module.finrank (ZMod p) V = N + 1 := by
      rw [hVrank]
      omega
    have hsup : H ⊔ Submodule.span (ZMod p) {v} = ⊤ := by
      apply Submodule.eq_top_of_disjoint (s := H) (t := Submodule.span (ZMod p) {v})
      · rw [finrank_span_singleton hv0, hVN, hHr]
      · exact (Submodule.disjoint_span_singleton' hv0).mpr hvH
    exact Or.inl ⟨hLI, hvH, hsup⟩
  · by_cases hvH : v ∈ H
    · have hHr : Module.finrank (ZMod p) H = N := by
        rw [hHrank, if_pos hvH, hD]
      have hLI : LinearIndependent (ZMod p) h := hLI_of_finrank hHr
      rcases hVcases with hV | hV
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hLI, ?_⟩)))
        exact Submodule.eq_top_of_finrank_eq (S := H) (hHr.trans hV.symm)
      · refine Or.inr (Or.inl ⟨hLI, hvH, hV, ?_⟩)
        exact hsurj (by omega)
    · have hHr : Module.finrank (ZMod p) H + 1 = N := by
        rw [hHrank, if_neg hvH, add_zero, hD]
      rcases hVcases with hV | hV
      · refine Or.inr (Or.inr (Or.inl ⟨hHr, hvH, ?_⟩))
        apply Submodule.eq_top_of_disjoint (s := H) (t := Submodule.span (ZMod p) {v})
        · rw [finrank_span_singleton hv0, hV, ← hHr]
        · exact (Submodule.disjoint_span_singleton' hv0).mpr hvH
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hHr, hvH, hV, ?_⟩)))
        exact hsurj (by omega)

theorem ggTD_mem_iff_mem_closure_coroot {G : Type} [Group G] {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {Bs X : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs)
    (hXx : X ≤ Subgroup.centralizer ({x} : Set G)) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit p N ↥X (ggGamma X hN).range) (hw : w.Holds C M) :
    x ∈ X ↔ x ∈ Subgroup.closure (Set.range fun k => ((w.cor k (ggZetaP p p) : ↥X) : G)) := by
  have hp := Fact.out (p := p.Prime)
  constructor
  · intro hxX
    set z : ↥X := ⟨x, hxX⟩ with hz
    have hzcenter : z ∈ Subgroup.center ↥X := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hXx y.2))
    have hzpow : z ^ p = 1 := by
      apply Subtype.ext
      simpa [hz] using hBs.2 x hxBs
    have hdvd : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzpow
    have hodd : Odd (orderOf z) := by
      rcases hp.eq_one_or_self_of_dvd (orderOf z) hdvd with h1 | h1
      · rw [h1]; exact odd_one
      · rw [h1]; exact hp.odd_of_ne_two hp2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hoddZ, ⟨-, -, htor⟩, -, -⟩ := hw
    have hzTsc : z ∈ w.Tsc := hoddZ z hzcenter hodd
    have hziSup : z ∈ ⨆ k, (w.cor k).range := htor z hzTsc hzpow
    have hrange : ∀ k, (w.cor k).range =
        Subgroup.zpowers (w.cor k (ggZetaP p p)) := by
      intro k
      refine le_antisymm ?_ (Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
      rintro _ ⟨u, rfl⟩
      obtain ⟨j, rfl⟩ := ggZetaP_exists_pow hp hp.ne_zero (dvd_refl p) u (ggTor_pow_m u)
      rw [map_pow]
      exact Subgroup.npow_mem_zpowers _ j
    have hsup : (⨆ k, (w.cor k).range) =
        Subgroup.closure (Set.range fun k => w.cor k (ggZetaP p p)) := by
      refine le_antisymm (iSup_le fun k => ?_) ((Subgroup.closure_le _).2 ?_)
      · rw [hrange k]
        exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_range_self k))
      · rintro _ ⟨k, rfl⟩
        exact Subgroup.mem_iSup_of_mem k (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have hzcl : z ∈ Subgroup.closure (Set.range fun k => w.cor k (ggZetaP p p)) :=
      hsup ▸ hziSup
    have hmem := Subgroup.mem_map_of_mem (Subgroup.subtype X) hzcl
    rw [MonoidHom.map_closure] at hmem
    have hset : Set.range (fun k => ((w.cor k (ggZetaP p p) : ↥X) : G)) =
        Subgroup.subtype X '' Set.range (fun k => w.cor k (ggZetaP p p)) :=
      Set.range_comp (Subgroup.subtype X) (fun k => w.cor k (ggZetaP p p))
    rw [hset]
    simpa [hz] using hmem
  · intro hx
    refine (Subgroup.closure_le (K := X)).2 ?_ hx
    rintro _ ⟨k, rfl⟩
    exact (w.cor k (ggZetaP p p)).2

private theorem mem_closure_iff_mem_span {G : Type} [Group G] {p : ℕ} [NeZero p]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {ι₀ : Type} (g : ι₀ → G) (hg : ∀ k, g k ∈ Bs) :
    ∀ {b : G} (hb : b ∈ Bs), b ∈ Subgroup.closure (Set.range g) ↔
      ι (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈
        Submodule.span (ZMod p) (Set.range fun k => ι (Additive.ofMul (⟨g k, hg k⟩ : ↥Bs))) := by
  intro b hb
  constructor
  · intro hbcl
    have key : ∀ y ∈ Subgroup.closure (Set.range g), ∃ hy : y ∈ Bs,
        ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∈
          Submodule.span (ZMod p) (Set.range fun k =>
            ι (Additive.ofMul (⟨g k, hg k⟩ : ↥Bs))) := by
      intro y hy
      refine Subgroup.closure_induction (p := fun z _ => ∃ hz : z ∈ Bs,
        ι (Additive.ofMul (⟨z, hz⟩ : ↥Bs)) ∈
          Submodule.span (ZMod p) (Set.range fun k =>
            ι (Additive.ofMul (⟨g k, hg k⟩ : ↥Bs)))) ?_ ?_ ?_ ?_ hy
      · rintro z ⟨k, rfl⟩
        exact ⟨hg k, Submodule.subset_span (Set.mem_range_self k)⟩
      · refine ⟨Bs.one_mem, ?_⟩
        have h0 : ι (Additive.ofMul (⟨1, Bs.one_mem⟩ : ↥Bs)) = 0 := by
          rw [show Additive.ofMul (⟨1, Bs.one_mem⟩ : ↥Bs) = 0 from ofMul_one, map_zero]
        rw [h0]
        exact Submodule.zero_mem _
      · rintro a c _ _ ⟨ha, hpa⟩ ⟨hc, hpc⟩
        refine ⟨Bs.mul_mem ha hc, ?_⟩
        have h1 : ι (Additive.ofMul (⟨a * c, Bs.mul_mem ha hc⟩ : ↥Bs)) =
            ι (Additive.ofMul (⟨a, ha⟩ : ↥Bs)) +
              ι (Additive.ofMul (⟨c, hc⟩ : ↥Bs)) := by
          rw [← map_add, ← ofMul_mul]
          rfl
        rw [h1]
        exact Submodule.add_mem _ hpa hpc
      · rintro a _ ⟨ha, hpa⟩
        refine ⟨Bs.inv_mem ha, ?_⟩
        have h1 : ι (Additive.ofMul (⟨a⁻¹, Bs.inv_mem ha⟩ : ↥Bs)) =
            -ι (Additive.ofMul (⟨a, ha⟩ : ↥Bs)) := by
          rw [← map_neg, ← ofMul_inv]
          rfl
        rw [h1]
        exact Submodule.neg_mem _ hpa
    obtain ⟨hy, hq⟩ := key b hbcl
    simpa using hq
  · intro hspan
    have key : ((Additive.toMul (ι.symm (ι (Additive.ofMul (⟨b, hb⟩ : ↥Bs)))) : ↥Bs) : G) ∈
        Subgroup.closure (Set.range g) := by
      refine Submodule.span_induction (p := fun v _ =>
        ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ Subgroup.closure (Set.range g))
        ?_ ?_ ?_ ?_ hspan
      · rintro v ⟨k, rfl⟩
        simpa using Subgroup.subset_closure (Set.mem_range_self k)
      · simpa using Subgroup.one_mem (Subgroup.closure (Set.range g))
      · intro x y _ _ hx hy
        have h1 : ((Additive.toMul (ι.symm (x + y)) : ↥Bs) : G) =
            ((Additive.toMul (ι.symm x) : ↥Bs) : G) *
              ((Additive.toMul (ι.symm y) : ↥Bs) : G) := by
          rw [map_add, toMul_add, Subgroup.coe_mul]
        rw [h1]
        exact Subgroup.mul_mem _ hx hy
      · intro c x _ hx
        have h1 : c • x = c.val • x := by
          conv_lhs => rw [← ZMod.natCast_zmod_val c]
          exact Nat.cast_smul_eq_nsmul (ZMod p) c.val x
        rw [h1]
        have h2 : ((Additive.toMul (ι.symm (c.val • x)) : ↥Bs) : G) =
            ((Additive.toMul (ι.symm x) : ↥Bs) : G) ^ c.val := by
          rw [map_nsmul, toMul_nsmul, Subgroup.coe_pow]
        rw [h2]
        exact Subgroup.pow_mem _ hx c.val
    simpa using key

theorem exists_ggQ2LDatum_of_torData_of_closure {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m N : ℕ} (hm : Odd m) (hpm : p ∣ m)
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (hTor : GGTorusTorData m N C M ↥L (ggGamma L hN).range)
    (hcl : x ∈ L → ∀ w : GGTorusTorWit m N ↥L (ggGamma L hN).range, w.Holds C M →
      x ∈ Subgroup.closure (Set.range fun k => ((w.cor k (ggZetaP p m) : ↥L) : G)))
    {lab : LargeEvenLabel} (hlab : GGQ2LabelWeyl lab M) :
    ∃ D : GGQ2LDatum p Bs L x, GGQ2LabelWeyl lab D.coxeter ∧
      (∃ e : Fin N ≃ D.Λ, ∀ i j, D.cartan (e i) (e j) = C i j) ∧ D.Shape := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hxBL : x ∈ Bs ∧ x ∈ Subgroup.centralizer (L : Set G) := by
    rw [← Subgroup.mem_inf, hBL]
    exact Subgroup.mem_zpowers x
  have hxBs : x ∈ Bs := hxBL.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxBL.2 l hl)
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, iadd, imod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  letI : AddCommGroup V := iadd
  letI : Module (ZMod p) V := imod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hnk, hbk, α, hrefl, hpair, hγ, hsep⟩ :=
    ggTD_linearData hm hpm hBs hSC hN w hw V ιV
  have hAL : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun k => ggTDρB L Bs (ggTDnH w hnk k)) :=
    ggTD_closure hN hw hp2 hBs hnk
  let simple : Fin N → MulAut ↥Bs := fun k => ggTDρB L Bs (ggTDnH w hnk k)
  let coroot : Fin N → V := fun k => ιV (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))
  let xV : V := ιV (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  have hxV0 : xV ≠ 0 := by
    intro h
    apply hx1
    have h1 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
      apply ιV.injective
      simpa [xV] using h
    have h2 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      simpa using Additive.ofMul.injective h1
    exact congrArg (fun b : ↥Bs => (b : G)) h2
  have hxVfix : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := p) ιV φ xV = xV := by
    intro φ hφ
    obtain ⟨a, haL, -, ha⟩ := mem_ggAutomizer_iff.mp hφ
    have hax : a * x = x * a :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLx haL)
    have hφx : φ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      apply Subtype.ext
      rw [ha]
      change a * x * a⁻¹ = x
      calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [hax]
        _ = x := by group
    change ggLin (p := p) ιV φ (ιV (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) = xV
    rw [ggLin_apply_ofMul, hφx]
  have hci : ∀ i, coroot i ≠ 0 := by
    intro i h0
    have h2 : ((C i i : ℤ) : ZMod p) = 0 := by
      rw [← hpair i i]
      change α i (coroot i) = 0
      rw [h0, map_zero]
    rw [hC.1 i] at h2
    exact zmod_two_ne_zero hp2 (by simpa using h2)
  have hker : (LinearMap.pi α).ker = Submodule.span (ZMod p) {xV} := by
    apply le_antisymm
    · intro v hv
      have hv' : ∀ i, α i v = 0 := fun i => congrFun (LinearMap.mem_ker.mp hv) i
      have hb : ggGamma L hN (Additive.toMul (ιV.symm v)) = 1 := hsep v hv'
      have hbcent : ((Additive.toMul (ιV.symm v) : ↥Bs) : G) ∈
          Bs ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨(Additive.toMul (ιV.symm v)).2, (ggGamma_eq_one_iff L hN _).mp hb⟩
      rw [hBL] at hbcent
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hbcent
      have hb' : Additive.toMul (ιV.symm v) = (⟨x, hxBs⟩ : ↥Bs) ^ n := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        exact hn.symm
      have hv_eq : v = (n : ZMod p) • xV := by
        rw [Int.cast_smul_eq_zsmul]
        calc v = ιV (Additive.ofMul (Additive.toMul (ιV.symm v))) :=
              (ιV.apply_symm_apply v).symm
          _ = ιV (Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ n)) := by rw [hb']
          _ = ιV (n • Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by rw [ofMul_zpow]
          _ = n • xV := by rw [map_zsmul]
      rw [hv_eq]
      exact Submodule.smul_mem (Submodule.span (ZMod p) {xV}) (n : ZMod p)
        (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine LinearMap.mem_ker.mpr ?_
      funext i
      exact hγ i ⟨x, hxBs⟩ ((ggGamma_eq_one_iff L hN _).mpr
        (mem_centralizer_of_le_centralizer hLx))
  have hfixed_x : ggFixedSubmodule (p := p) ιV (ggAutomizer L Bs) =
      Submodule.span (ZMod p) {xV} := by
    apply le_antisymm
    · intro v hv
      have hroot_v : ∀ i, α i v = 0 := by
        intro i
        have hsi : simple i ∈ ggAutomizer L Bs := by
          rw [hAL]
          exact Subgroup.subset_closure ⟨i, rfl⟩
        have hfix := mem_ggFixedSubmodule_iff.mp hv (simple i) hsi
        have hfix' : ggLin (p := p) ιV (ggTDρB L Bs (ggTDnH w hnk i)) v = v := hfix
        have heq := hrefl i v
        rw [hfix'] at heq
        have hzero : α i v • coroot i = 0 := sub_eq_self.mp heq.symm
        exact (smul_eq_zero.mp hzero).resolve_right (hci i)
      have hvker : v ∈ (LinearMap.pi α).ker := by
        rw [LinearMap.mem_ker]
        funext i
        exact hroot_v i
      rw [hker] at hvker
      exact hvker
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_ggFixedSubmodule_iff.mpr hxVfix
  have hrank : N ≤ (C.map (Int.castRingHom (ZMod p))).rank + 1 := by
    simpa using ggIntCartan_card_le_rank_add_one hM hC p hp2
  have hshape := ggQ2_shape_linear (p := p) hrank coroot α hpair hxV0 hker
  have hspan := mem_closure_iff_mem_span (p := p) ιV (fun k => ((w.cor k (ggZetaP p m) : ↥L) : G))
    hbk hxBs
  have hmem : x ∈ L ↔ xV ∈ Submodule.span (ZMod p) (Set.range coroot) := by
    refine ⟨fun hxL => hspan.mp (hcl hxL w hw), fun hxV => ?_⟩
    refine (Subgroup.closure_le (K := L)).2 ?_ (hspan.mpr hxV)
    rintro _ ⟨k, rfl⟩
    exact (w.cor k (ggZetaP p m)).2
  let D : GGQ2LDatum p Bs L x :=
    { Λ := Fin N
      coxeter := M
      cartan := C
      V := V
      model := ιV
      hx := hxBs
      simple := simple
      coroot := coroot
      root := α
      isWeyl := hM
      isCartan := hC
      pairing := hpair
      simple_apply := hrefl
      automizer_L := hAL
      fixed_x := hfixed_x }
  refine ⟨D, ?_, ⟨Equiv.refl _, fun _ _ => rfl⟩, ?_⟩
  · change GGQ2LabelWeyl lab M
    exact hlab
  · change D.ShapeFull ∨ D.ShapeA ∨ D.ShapeB ∨ D.ShapeC ∨ D.ShapeD
    rcases hshape with ⟨hLI, hxVH, hsup⟩ | ⟨hLI, hxVH, hdim, hsurj⟩ |
      ⟨hfin, hxVH, hsup⟩ | ⟨hfin, hxVH, hdim, hsurj⟩ | ⟨hLI, htop⟩
    · refine Or.inl ⟨fun hxL => hxVH (hmem.mp hxL), hLI, ?_, ?_⟩
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hsup
    · refine Or.inr (Or.inl ⟨hmem.mpr hxVH, hLI, ?_, ?_, ?_⟩)
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · dsimp only [D]
        simpa using hdim
      · simpa [GGQ2LDatum.rootMap] using hsurj
    · refine Or.inr (Or.inr (Or.inl ⟨fun hxL => hxVH (hmem.mp hxL), ?_, ?_, ?_⟩))
      · exact hfin.trans (Fintype.card_fin N).symm
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hsup
    · refine Or.inr (Or.inr (Or.inr (Or.inl
        ⟨fun hxL => hxVH (hmem.mp hxL), ?_, ?_, ?_, ?_⟩)))
      · exact hfin.trans (Fintype.card_fin N).symm
      · simpa [GGQ2LDatum.coSpan, GGQ2LDatum.xV] using hxVH
      · dsimp only [D]
        simpa using hdim
      · simpa [GGQ2LDatum.rootMap] using hsurj
    · have hxVH : xV ∈ Submodule.span (ZMod p) (Set.range coroot) := by
        rw [htop]
        exact Submodule.mem_top
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hmem.mpr hxVH, hLI, ?_⟩)))
      simpa [GGQ2LDatum.coSpan] using htop

theorem exists_ggQ2LDatum_of_torData {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hTor : GGTorusTorData p N C M ↥L (ggGamma L hN).range) {lab : LargeEvenLabel}
    (hlab : GGQ2LabelWeyl lab M) :
    ∃ D : GGQ2LDatum p Bs L x, GGQ2LabelWeyl lab D.coxeter ∧
      (∃ e : Fin N ≃ D.Λ, ∀ i j, D.cartan (e i) (e j) = C i j) ∧ D.Shape := by
  have hxBL : x ∈ Bs ∧ x ∈ Subgroup.centralizer (L : Set G) := by
    rw [← Subgroup.mem_inf, hBL]
    exact Subgroup.mem_zpowers x
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxBL.2 l hl)
  exact exists_ggQ2LDatum_of_torData_of_closure hp2 hBs hSC hx1 hBL hN
    ((Fact.out : p.Prime).odd_of_ne_two hp2) dvd_rfl hM hC hTor
    (fun hxL w hw => (ggTD_mem_iff_mem_closure_coroot hp2 hBs hxBL.1 hLx hN w hw).mp hxL) hlab

theorem exists_ggQ2LDatum_of_torData_of_not_mem {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m N : ℕ} (hm : Odd m) (hpm : p ∣ m)
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} (hM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (hTor : GGTorusTorData m N C M ↥L (ggGamma L hN).range)
    (hxL : x ∉ L) {lab : LargeEvenLabel} (hlab : GGQ2LabelWeyl lab M) :
    ∃ D : GGQ2LDatum p Bs L x, GGQ2LabelWeyl lab D.coxeter ∧
      (∃ e : Fin N ≃ D.Λ, ∀ i j, D.cartan (e i) (e j) = C i j) ∧
      (D.ShapeFull ∨ D.ShapeB ∨ D.ShapeC) := by
  obtain ⟨D, hW, he, hS⟩ := exists_ggQ2LDatum_of_torData_of_closure hp2 hBs hSC hx1 hBL hN hm
    hpm hM hC hTor (fun h => absurd h hxL) hlab
  refine ⟨D, hW, he, ?_⟩
  rcases hS with hF | hA | hB | hC' | hD
  · exact Or.inl hF
  · exact absurd hA.1 hxL
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr hC')
  · exact absurd hD.1 hxL

theorem ggQ2TableBI1FailOn_of_tor {S : LargeEvenLabel → Prop}
    (hS : ∀ lab, S lab → GGQ2TBLabel lab ∧
      ((lab.tag = .twA ∧ 3 ∣ lab.rank + 1) ∨ lab.tag = .twE6))
    (h : ∀ lab, LargeEvenInLambda2 lab → GGLabQTwo 3 lab → S lab →
      ∃ (N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGQ2LabelWeyl lab M ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        LargeEvenLabelAll lab (fun R _ I _ => ∃ r s, s ≤ r + 1 ∧ GGTorusLift 3 r R ∧
          GGTorusTorW 3 s 3 N C M R I)) :
    GGQ2TableBI1FailOn S := by
  intro G _ _ p B Bs x L D J hset hp hI1 _ hM
  subst hp
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨⟨hq, hSl⟩, hBsN, h3I⟩ := hP
  obtain ⟨N, C, M, hlabW, hMw, hC, hall⟩ := h lab hlab hq hSl
  obtain ⟨R₂, _, I₂, F₂, hQ₂⟩ := largeEvenRawDatum_exists (hall _ hraw)
  obtain ⟨hQold, r, s, hsr, hlift, hTorW⟩ := hQ₂
  obtain ⟨-, -, θ₂, hP₂⟩ := hQold
  obtain ⟨-, hBsN₂, h3I₂⟩ := hP₂
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ₂ ⟨b, hBsN₂ hb⟩ ∈ I₂ :=
    fun b hb => ggLAut_mem_of_induces L θ₂ hBsN₂ h3I₂ hb
  have hsB : 3 ^ s ≤ Nat.card (ggGamma L hBsN₂).range :=
    (Nat.pow_le_pow_right (by norm_num) hsr).trans
      (pow_succ_le_card_range_ggGamma_of_not_i1 hset.1.1 hI1 hperf θ₂ hBsN₂ hlift)
  have hcfg : GGConfig 3 B Bs x L D J := hset.1.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hSstar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hSstar.2.2.2.2
  have hcardmul : Nat.card (ggGamma L hBsN₂).range * 3 = Nat.card Bs :=
    card_range_ggGamma_mul_of (p := 3) hp hBs hxBs hx1 hLx hcyc hBsN₂
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN₂).range := by
    have h4 := (pow_four_le_card_of_bmax hp hSstar.1 hcfg.1.2.2.2.2.2.1.2.2.2).trans
      (Subgroup.card_le_of_le hcfg.2.1.1)
    rw [← hcardmul, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 (by norm_num)
  have hTB : GGTorusTBGroup 3 s R₂ I₂ L (ggQuotHom θ₂) (ggGamma L hBsN₂).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hperf θ₂ hBsN₂ hBsI hsB h3
  have hTor : GGTorusTorData 3 N C M ↥L (ggGamma L hBsN₂).range :=
    hTorW ↥L (ggQuotHom θ₂) (ggGamma L hBsN₂).range hTB
  obtain ⟨D, hDW, -, hDshape⟩ :=
    exists_ggQ2LDatum_of_torData (p := 3) (by norm_num) hBs hSC hx1
      (inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxBs hx1 hLx hcyc) hBsN₂ hMw hC hTor hlabW
  exact ⟨lab, hq, (hS lab hSl).1, ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩,
    D, hDW, hDshape, fun _ => (hS lab hSl).2⟩

end CFSG.StandardType

end
