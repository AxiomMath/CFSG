module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddSemi
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailBstar
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open CFSG.Assembly CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL Matrix

section Transport

variable {R R' : Type} [Group R] [Group R']

theorem ggBstarBoundInnR_of_mulEquiv {p r : ℕ} (e : R ≃* R')
    (h : GGBstarBoundInnR p r R' (LargeEvenInnSet R')) :
    GGBstarBoundInnR p r R (LargeEvenInnSet R) := by
  intro Eb Eh hEbI hEb hr h3 ⟨V, hV1, hV2, hV⟩ hle hEh hcard
  set c := MulAut.congr e with hc
  have hcapp : ∀ (φ : MulAut R) (x : R), c φ (e x) = e (φ x) := fun φ x => by
    change e (φ (e.symm (e x))) = e (φ x)
    rw [MulEquiv.symm_apply_apply]
  have hcard' : ∀ H : Subgroup (MulAut R), Nat.card (H.map c.toMonoidHom) = Nat.card H :=
    fun H => Subgroup.card_map_of_injective c.injective
  obtain ⟨E'', hlt, hE''le, W, hW1, hW2, hW⟩ := h (Eb.map c.toMonoidHom) (Eh.map c.toMonoidHom)
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      obtain ⟨x, rfl⟩ := hEbI hφ
      exact ⟨e x, (OuterAutomorphisms.congr_conj e x).symm⟩)
    (TableB.isElemAbelian_map hEb _) (by rw [hcard']; exact hr) (by rw [hcard']; exact h3)
    ⟨V.map e.toMonoidHom,
      fun h0 => hV1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h0),
      hV2.map _, by
        rintro _ ⟨φ, hφ, rfl⟩ _ ⟨v, hv, rfl⟩
        exact ⟨φ v, hV φ hφ v hv, (hcapp φ v).symm⟩⟩
    (Subgroup.map_mono hle) (TableB.isElemAbelian_map hEh _)
    (by rw [hcard', hcard']; exact hcard)
  have hE''eq : (E''.comap c.toMonoidHom).map c.toMonoidHom = E'' :=
    Subgroup.map_comap_eq_self_of_surjective c.surjective _
  refine ⟨E''.comap c.toMonoidHom, lt_of_le_of_ne (fun φ hφ => hlt.le ⟨φ, hφ, rfl⟩) fun heq => ?_,
    fun φ hφ => ?_, W.comap e.toMonoidHom, fun h0 => hW1 ?_, ?_, fun φ hφ w hw => ?_⟩
  · apply hlt.ne
    rw [← hE''eq, ← heq]
  · obtain ⟨ψ, hψ, hψφ⟩ := hE''le hφ
    have : ψ = φ := c.injective hψφ
    exact this ▸ hψ
  · rw [eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := e.surjective w
    have hx : x ∈ W.comap e.toMonoidHom := hw
    rw [h0, Subgroup.mem_bot] at hx
    rw [hx, map_one]
    exact one_mem _
  · exact hW2.comap_of_injective e.toMonoidHom e.injective
  · change e (φ w) ∈ W
    rw [← hcapp]
    exact hW _ hφ _ hw

end Transport

section Stab

variable {G : Type*} [Group G]

@[expose] def stabSub (U : Subgroup G) : Subgroup (MulAut G) where
  carrier := {φ | U.map φ.toMonoidHom = U}
  mul_mem' := by
    intro φ ψ hφ hψ
    change U.map (φ * ψ).toMonoidHom = U
    have : (φ * ψ).toMonoidHom = φ.toMonoidHom.comp ψ.toMonoidHom := rfl
    rw [this, ← Subgroup.map_map]
    change (U.map ψ.toMonoidHom).map φ.toMonoidHom = U
    rw [hψ, hφ]
  one_mem' := by
    change U.map (MonoidHom.id G) = U
    exact Subgroup.map_id U
  inv_mem' := by
    intro φ hφ
    change U.map φ⁻¹.toMonoidHom = U
    conv_lhs => rw [← (show U.map φ.toMonoidHom = U from hφ)]
    rw [Subgroup.map_map]
    have : φ⁻¹.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext fun x => by simp
    rw [this, Subgroup.map_id]

theorem mem_stabSub {U : Subgroup G} [Finite U] {φ : MulAut G} (h : ∀ u ∈ U, φ u ∈ U) :
    φ ∈ stabSub U := by
  have hle : U.map φ.toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective φ.injective])

theorem apply_mem_of_mem_stabSub {U : Subgroup G} {φ : MulAut G} (hφ : φ ∈ stabSub U) {u : G}
    (hu : u ∈ U) : φ u ∈ U := by
  have : φ u ∈ U.map φ.toMonoidHom := ⟨u, hu, rfl⟩
  rwa [show U.map φ.toMonoidHom = U from hφ] at this

theorem isElemAbelian_comap {H : Type*} [Group H] {p : ℕ} {E : Subgroup H}
    (hE : IsElemAbelian p E) {f : G →* H} (hf : Function.Injective f) :
    IsElemAbelian p (E.comap f) := CFSG.Open.IsElemAbelian.comap hE hf

end Stab

section Gamma

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem polar_semi {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {G : V ≃+ V} {σ : K ≃+* K} {μ : K} (hGQ : ∀ v, Q (G v) = μ * σ (Q v)) (u w : V) :
    QuadraticMap.polar Q (G u) (G w) = μ * σ (QuadraticMap.polar Q u w) := by
  simp only [QuadraticMap.polar, ← map_add, hGQ, map_sub]
  ring

theorem exists_plane_of_torus {n p : ℕ} (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {Tt Ebt Ut : Subgroup (matrixDerived (Qm n hn4 b c))}
    (hET : Ebt ≤ Tt) (hT : IsElemAbelian p Tt) (hTc : p ^ n ≤ Nat.card Tt)
    (hEc : p ^ (n - 1) ≤ Nat.card Ebt) (hU1 : Ut ≠ ⊥) (hU2 : IsPGroup 2 Ut)
    (hnorm : ∀ e ∈ Ebt, ∀ u ∈ Ut, e * u * e⁻¹ ∈ Ut)
    {G : (Fin (2 * n) → K) ≃+ (Fin (2 * n) → K)} {σ : K ≃+* K} {μ a : K}
    (hGs : ∀ (x : K) v, G (x • v) = σ x • G v)
    (hGQ : ∀ v, Qm n hn4 b c (G v) = μ * σ (Qm n hn4 b c v)) (hGp : ∀ v, (⇑G)^[p] v = a • v)
    (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1)
    (hGT : ∀ t ∈ Tt, ∀ w, ((t : GL (Fin (2 * n)) K)).val *ᵥ G w =
      G (((t : GL (Fin (2 * n)) K)).val *ᵥ w)) :
    ∃ x y : Fin (2 * n) → K, (∀ α β : K, Qm n hn4 b c (α • x + β • y) = 0) ∧
      (∀ α β : K, α • x + β • y = 0 → α = 0 ∧ β = 0) ∧
      (∀ e ∈ Ebt, ∀ v ∈ Submodule.span K {x, y},
        ((e : GL (Fin (2 * n)) K)).val *ᵥ v ∈ Submodule.span K {x, y}) ∧
      ∀ v ∈ Submodule.span K {x, y}, G v ∈ Submodule.span K {x, y} := by
  classical
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  set ι : matrixDerived (Qm n hn4 b c) →* ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
    matrixLinearIso.toMonoidHom.comp (matrixDerived (Qm n hn4 b c)).subtype with hι
  have hιinj : Function.Injective ι := matrixLinearIso.injective.comp Subtype.val_injective
  have hιQ : ∀ x : matrixDerived (Qm n hn4 b c), ∀ v,
      (Qm n hn4 b c) (ι x v) = (Qm n hn4 b c) v := fun x v =>
    (mem_matrixIsometries_iff (Qm n hn4 b c) _).1
      (matrixDerived_le_isometries (Qm n hn4 b c) x.2) v
  set T' := Tt.map ι with hT'
  set E' := Ebt.map ι with hE'
  have hT'comm : ∀ g ∈ T', ∀ h ∈ T', g * h = h * g := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hT hx hy]
  have hT'pow : ∀ g ∈ T', g ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hT.2 x hx, map_one]
  have hT'Q : ∀ g ∈ T', ∀ v, (Qm n hn4 b c) (g v) = (Qm n hn4 b c) v := by
    rintro _ ⟨x, -, rfl⟩ v
    exact hιQ x v
  have hE'T' : E' ≤ T' := Subgroup.map_mono hET
  obtain ⟨Y, hY0, hYinv, hYsing⟩ := exists_singular_of_two hnd hK1 (S := Ut.map ι) (N := E')
    (hU2.map ι) (fun h0 => hU1 ((Subgroup.map_eq_bot_iff_of_injective _ hιinj).mp h0))
    (by rintro _ ⟨u, -, rfl⟩ v; exact hιQ u v)
    (by
      rintro _ ⟨u, -, rfl⟩
      exact (mem_matrixDerived_iff_even hnd hT3
        (matrixDerived_le_isometries (Qm n hn4 b c) u.2)).mp u.2)
    (by rintro _ ⟨e, -, rfl⟩ v; exact hιQ e v) (fun g hg => hT'pow g (hE'T' hg))
    (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨u, hu, rfl⟩
      exact ⟨e * u * e⁻¹, hnorm e he u hu, by rw [map_mul, map_mul, map_inv]⟩)
  have hfin : Module.finrank K (Fin (2 * n) → K) = 2 * n := by rw [Module.finrank_fin_fun]
  obtain ⟨t, htT, t', ht'T, s, hsE, τ, hFD⟩ := frame_of_singular hp hp2 hK1 n _ hfin
    (Qm n hn4 b c) hnd T' E'
    hE'T' hT'comm hT'pow hT'Q (by rw [Subgroup.card_map_of_injective hιinj]; exact hTc)
    (by rw [Subgroup.card_map_of_injective hιinj]; exact hEc) Y hY0 hYinv hYsing
  have hGcomm : ∀ g ∈ T', ∀ w, G (g w) = g (G w) := by
    rintro _ ⟨x, hx, rfl⟩ w
    exact (hGT x hx w).symm
  have hsT := hE'T' hsE
  have hGW : ∀ r ∈ T', ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace r,
      G v ∈ CFSG.RankThree.PartOne.LIT.commSpace r := by
    intro r hr v hv
    obtain ⟨z, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hv
    refine CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨G z, ?_⟩
    rw [map_sub, hGcomm r hr z]
  have hsW : ∀ r ∈ T', ∀ v ∈ CFSG.RankThree.PartOne.LIT.commSpace r,
      s v ∈ CFSG.RankThree.PartOne.LIT.commSpace r := fun r hr v hv =>
    CFSG.RankThree.PartOne.LIT.map_mem_commSpace (hT'comm s hsT r hr) hv
  obtain ⟨x, hxW, hsing, hind, α, β, hGx⟩ := exists_isotropic_line hp hK1 hFD (hT'Q s hsT)
    (hT'pow s hsT) (hsW t htT) (hsW t' ht'T) hGs hGQ (hGW t htT) (hGW t' ht'T)
    (fun v => hGcomm s hsT v) hGp hσp hσ1
  have hsx : s (s x) = τ • s x + x := hFD.sq x hxW
  have hsxW : s x ∈ CFSG.RankThree.PartOne.LIT.commSpace t ⊔
      CFSG.RankThree.PartOne.LIT.commSpace t' := by
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hxW
    rw [map_add]
    exact Submodule.add_mem_sup (hsW t htT w₁ hw₁) (hsW t' ht'T w₂ hw₂)
  have hspan : ∀ α' β' : K, α' • x + β' • s x ∈ Submodule.span K {x, s x} := fun α' β' =>
    Submodule.mem_span_pair.mpr ⟨α', β', rfl⟩
  refine ⟨x, s x, hsing, hind, fun e he v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨α', β', hαβ⟩ := hFD.act (ι e) ⟨e, he, rfl⟩
    obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hv
    change ι e (γ • x + δ • s x) ∈ _
    rw [map_add, map_smul, map_smul, hαβ x hxW, hαβ (s x) hsxW, hsx]
    convert hspan (γ * α' + δ * β') (γ * β' + δ * α' + δ * β' * τ) using 1
    module
  · obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [map_add, hGs, hGs, hGcomm s hsT, hGx, map_add, map_smul, map_smul, hsx]
    convert hspan (σ γ * α + σ δ * β) (σ γ * β + σ δ * α + σ δ * β * τ) using 1
    module

theorem ggBstarBoundInnR_gamma {f n p : ℕ} (hf : Nat.card K = 2 ^ f) (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) :
    GGBstarBoundInnR p (n - 1) (matrixDerived (Qm n hn4 b c)) (LargeEvenInnSet _) := by
  classical
  intro Eb Eh hEbI hEb hr _ ⟨U, hU1, hU2, hUinv⟩ hle hEh hcard
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hZ : Subgroup.center (matrixDerived (Qm n hn4 b c)) = ⊥ :=
    OrthRestOdd.center_matrixDerived_eq_bot hnd (by omega)
  have hinj := OrthRest.conj_injective hZ
  have : Finite (GL (Fin (2 * n)) K) := Finite.of_injective (fun g : GL (Fin (2 * n)) K =>
    (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) Units.val_injective
  have : Finite (MulAut (matrixDerived (Qm n hn4 b c))) :=
    Finite.of_injective (fun α : MulAut (matrixDerived (Qm n hn4 b c)) => (α : _ → _))
      fun a b h => MulEquiv.ext (congrFun h)
  have hIsoΓ : ∀ x : matrixDerived (Qm n hn4 b c), ∀ v,
      Qm n hn4 b c (((x : GL (Fin (2 * n)) K)).val *ᵥ v) = Qm n hn4 b c v := fun x v =>
    (mem_matrixIsometries_iff _ _).1 (matrixDerived_le_isometries _ x.2) v
  set T := Eh ⊓ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) with hT
  have hEhT : Nat.card Eh ≤ p * Nat.card T :=
    OrthRestTail.card_le_mul_inf_of_cyclic (AutOm.frobAut hn4 hirr)
      (fun α => AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf α) hp hEh
  have hTab : IsElemAbelian p T :=
    ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hEh a.2.1 b.2.1)⟩⟩,
      fun x hx => hEh.2 x hx.1⟩
  set Tt := T.comap (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _) with hTt
  have hcTt : Nat.card Tt = Nat.card T := by
    have hmc : Tt.map (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _) = T :=
      Subgroup.map_comap_eq_self inf_le_right
    rw [← hmc, Subgroup.card_map_of_injective hinj]
  have hTtab : IsElemAbelian p Tt := isElemAbelian_comap hTab hinj
  have hTtle : Nat.card Tt ≤ p ^ n := by
    have h := OrthRest.card_le_of_isometry (Qm n hn4 b c) hnd hp hp2
      (Tt.map (matrixDerived (Qm n hn4 b c)).subtype)
      (by rintro _ ⟨x, -, rfl⟩ v; exact hIsoΓ x v)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hTtab hx hy])
      (by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hTtab.2 x hx, map_one])
    rwa [Subgroup.card_map_of_injective Subtype.val_injective, Fintype.card_fin,
      Nat.mul_div_cancel_left _ two_pos] at h
  have hEh1 : p ^ (n + 1) ≤ Nat.card Eh :=
    calc p ^ (n + 1) = p ^ 2 * p ^ (n - 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
  have hTge : p ^ n ≤ Nat.card Tt := by
    rw [hcTt]
    refine Nat.le_of_mul_le_mul_left ?_ hp.pos
    calc p * p ^ n = p ^ (n + 1) := (pow_succ' p n).symm
      _ ≤ Nat.card Eh := hEh1
      _ ≤ p * Nat.card T := hEhT
  obtain ⟨φ, hφEh, hφI⟩ :
      ∃ φ ∈ Eh, φ ∉ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := by
    by_contra hcon
    push Not at hcon
    have hTeq : T = Eh := le_antisymm inf_le_left (le_inf le_rfl hcon)
    have h1 : Nat.card Eh ≤ p ^ n := by rw [← hTeq, ← hcTt]; exact hTtle
    have h2 : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  set Ab := Eb.comap (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _) with hAb
  have hEbInn : Eb ≤ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := fun ψ hψ =>
    hEbI hψ
  have hAbTt : Ab ≤ Tt := Subgroup.comap_mono (le_inf hle hEbInn)
  have hcAb : Nat.card Ab = Nat.card Eb := by
    have hmc : Ab.map (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _) = Eb :=
      Subgroup.map_comap_eq_self hEbInn
    rw [← hmc, Subgroup.card_map_of_injective hinj]
  obtain ⟨G, σ, μ, a, hGs, hμ, hGQ, hGp, hσp, hσ1, hGconj⟩ :=
    exists_semi_of_aut hn4 hirr hpo (hEh.2 φ hφEh) hφI
  have hφfix : ∀ t ∈ Tt, φ t = t := by
    intro t ht
    have hcomm := TableB.IsElemAbelian.comm hEh hφEh ht.1
    apply hinj
    rw [← OrthRestOdd.conj_map_mulAut, hcomm, mul_inv_cancel_right]
  have hGT : ∀ t ∈ Tt, ∀ w, ((t : GL (Fin (2 * n)) K)).val *ᵥ G w =
      G (((t : GL (Fin (2 * n)) K)).val *ᵥ w) := by
    intro t ht w
    have h := hGconj t w
    rwa [hφfix t ht] at h
  obtain ⟨x, y, hsing, hind, hEX, hGX⟩ := exists_plane_of_torus hn4 hirr hp hp2 hK1 hAbTt hTtab
    hTge (by rw [hcAb]; exact hr) hU1 hU2
    (fun e he u hu => by simpa [MulAut.conj_apply] using hUinv _ he u hu) hGs hGQ hGp hσp hσ1 hGT
  set X := Submodule.span K {x, y} with hX
  have hxX : x ∈ X := Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩
  have hyX : y ∈ X := Submodule.mem_span_pair.mpr ⟨0, 1, by simp⟩
  have hXiso : ∀ v ∈ X, ∀ v' ∈ X, QuadraticMap.polar (Qm n hn4 b c) v v' = 0 := by
    intro v hv v' hv'
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
    obtain ⟨α', β', rfl⟩ := Submodule.mem_span_pair.mp hv'
    exact polar_eq_zero_of_sing hsing α β α' β'
  set H := (matrixDerived (Qm n hn4 b c)).map
    (matrixLinearIso (d := 2 * n) (K := K)).toMonoidHom with hH
  set lin : matrixDerived (Qm n hn4 b c) →* ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
    (matrixLinearIso (d := 2 * n) (K := K)).toMonoidHom.comp (matrixDerived (Qm n hn4 b c)).subtype
    with hlin
  have hlinj : Function.Injective lin := matrixLinearIso.injective.comp Subtype.val_injective
  have hlinH : ∀ g, lin g ∈ H := fun g => ⟨g.val, g.2, rfl⟩
  have hsiegH : siegEquiv hsing ∈ H := by
    refine ⟨matrixLinearIso.symm (siegEquiv hsing), ?_, by simp⟩
    rw [SetLike.mem_coe, mem_matrixDerived_iff hnd hT3, MulEquiv.apply_symm_apply]
    exact siegEquiv_mem_omegaGroup hnd hsing
  set U₂ := (siegSub (Qm n hn4 b c) X H).comap lin with hU₂
  have hsieg := siegEquiv_mem_siegSub hsing hxX hyX hsiegH
  obtain ⟨h₀, hh₀Γ, hh₀⟩ := hsiegH
  have hU₂1 : U₂ ≠ ⊥ := by
    intro h0
    have hmem : (⟨h₀, hh₀Γ⟩ : matrixDerived (Qm n hn4 b c)) ∈ U₂ := by
      change lin ⟨h₀, hh₀Γ⟩ ∈ siegSub (Qm n hn4 b c) X H
      rw [show lin ⟨h₀, hh₀Γ⟩ = siegEquiv hsing from hh₀]
      exact hsieg
    rw [h0, Subgroup.mem_bot] at hmem
    apply siegEquiv_ne_one hnd hsing hind
    rw [← hh₀]
    change lin ⟨h₀, hh₀Γ⟩ = 1
    rw [hmem, map_one]
  have hU₂2 : IsPGroup 2 U₂ := fun u => ⟨1, Subtype.ext (hlinj (by
    rw [pow_one, Subgroup.coe_pow, map_pow, pow_two, OneMemClass.coe_one, map_one]
    exact siegSub_mul_self hXiso u.2))⟩
  have hEbU : ∀ ψ ∈ Eb, ∀ v ∈ U₂, ψ v ∈ U₂ := by
    intro ψ hψ v hv
    obtain ⟨e, rfl⟩ := hEbI hψ
    have he : e ∈ Ab := hψ
    change lin (MulAut.conj e v) ∈ siegSub (Qm n hn4 b c) X H
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    refine conj_mem_siegSub ?_ (fun x' hx' => hEX e he x' hx') (fun w hw => ?_) hv
    · rintro _ ⟨h', hh', rfl⟩
      refine ⟨(e : GL (Fin (2 * n)) K) * h' * (e : GL (Fin (2 * n)) K)⁻¹,
        mul_mem (mul_mem e.2 hh') (inv_mem e.2), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rfl
    · refine map_mem_perp (fun v' => ?_) (fun x' hx' => ?_) hw
      · rw [← map_inv]
        exact hIsoΓ e⁻¹ v'
      · rw [inv_inv]
        exact hEX e he x' hx'
  have hGP : ∀ w ∈ perp (Qm n hn4 b c) X, G.symm w ∈ perp (Qm n hn4 b c) X := by
    intro w hw
    rw [mem_perp] at hw ⊢
    intro x' hx'
    have h1 := hw (G x') (hGX x' hx')
    rw [← G.apply_symm_apply w, polar_semi hGQ] at h1
    exact (map_eq_zero_iff σ σ.injective).mp ((mul_eq_zero.mp h1).resolve_left hμ)
  have hlinφ : ∀ v w, lin (φ v) w = G (lin v (G.symm w)) := fun v w => by
    have h := hGconj v (G.symm w)
    rwa [AddEquiv.apply_symm_apply] at h
  have hφU : ∀ v ∈ U₂, φ v ∈ U₂ := by
    intro v hv
    obtain ⟨-, hvX, hvP⟩ := hv
    refine ⟨hlinH (φ v), fun w => ?_, fun w hw => ?_⟩
    · rw [hlinφ]
      have h1 := hGX _ (hvX (G.symm w))
      rwa [map_sub, AddEquiv.apply_symm_apply] at h1
    · rw [hlinφ, hvP _ (hGP w hw), AddEquiv.apply_symm_apply]
  have hstab : Eb ⊔ Subgroup.zpowers φ ≤ stabSub U₂ :=
    sup_le (fun ψ hψ => mem_stabSub (hEbU ψ hψ))
      (Subgroup.zpowers_le.mpr (mem_stabSub hφU))
  refine ⟨Eb ⊔ Subgroup.zpowers φ, lt_of_le_of_ne le_sup_left fun heq => hφI ?_,
    sup_le hle (Subgroup.zpowers_le.mpr hφEh), U₂, hU₂1, hU₂2,
    fun ψ hψ v hv => apply_mem_of_mem_stabSub (hstab hψ) hv⟩
  exact hEbInn (heq ▸ (le_sup_right : Subgroup.zpowers φ ≤ Eb ⊔ Subgroup.zpowers φ)
    (Subgroup.mem_zpowers φ))

end Gamma

end OrthBstarOdd

open OrthBstarOdd in
theorem ggOrthRestBstarOddInput_holds : GGOrthRestBstarOddInput := by
  intro K _ _ n m p b c hK hm _ hp hpn _ hbc
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at h1
      omega
    · exact h0
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_add_right (dvd_pow_self 2 (by omega))]
      norm_num
    exact hodd hpn
  have hn4 : 4 ≤ m + 1 := by omega
  exact ggBstarBoundInnR_of_mulEquiv (RecipeFieldOmega.minusEquiv hn4 b c)
    (ggBstarBoundInnR_gamma hK hn4 hbc hp hp2 (OrthRestOdd.eq_one_of_pow_eq_one_of_dvd hK hp hpn))

end CFSG.StandardType
