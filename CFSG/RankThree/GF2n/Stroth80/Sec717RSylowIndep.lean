module

public import CFSG.RankThree.GF2n.Stroth80.Sec717RSylowIndepSteps
public import CFSG.RankThree.GF2n.Stroth80.Sec717RSylowIndepMid
public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec717RSylow
import CFSG.RankThree.GF2n.Stroth80.Sec717RSylowIndepSchur
import CFSG.RankThree.GF2n.Stroth80.Sec717RSylowIndepAgree
import CFSG.RankThree.GF2n.Stroth80.Sec717TwistKlein

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem agree_of_wedge_of_isPGroup {X : Type*} {K : Type} {E : Type*} [Group X] [Field K]
    [Finite K] [CharP K 2]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E] (φ : X →* (E ≃ₗ[K] E))
    (T : Submodule K E) (hT0 : T ≠ ⊥) {Rb Lb Vb : Subgroup X}
    (hRL : ∀ r ∈ Rb, ∀ l ∈ Lb, r * l * r⁻¹ ∈ Lb)
    (η : ↥Rb →* Matrix.SpecialLinearGroup (Fin 4) K) (hηs : Function.Surjective η)
    (hη1 : ∀ r : ↥Rb, η r = 1 → ∀ w ∈ T, φ r w = w)
    (θ : ↥Lb →* Multiplicative (Fin 4 → K)) (hθs : Function.Surjective θ)
    (hθk : ∀ l : ↥Lb, θ l = 1 ↔ (l : X) ∈ Vb)
    (hθ : ∀ (r : ↥Rb) (l l' : ↥Lb), (l' : X) = (r : X) * l * (r : X)⁻¹ →
      Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l))
    (ψ : ↥T ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
    (hψ : ∀ (r : ↥Rb) (w w' : ↥T), (w' : E) = φ (r : X) w →
      ψ w' = PartOne.K159.Klein.rho (η r) (ψ w))
    (hRT : ∀ r ∈ Rb, ∀ w ∈ T, φ r w ∈ T)
    (hschur : ∀ x : X, (∀ w ∈ T, φ x w ∈ T) →
      (∀ r ∈ Rb, ∀ w ∈ T, φ x (φ r w) = φ r (φ x w)) → ∃ c : K, ∀ w ∈ T, φ x w = c • w)
    (hscal : ∀ r ∈ Rb, ∀ c : K, (∀ w ∈ T, φ r w = c • w) → c = 1)
    {s : X} (hsR : s ∈ Subgroup.normalizer (Rb : Set X))
    (hsL : s ∈ Subgroup.normalizer (Lb : Set X)) (hsV : s ∈ Subgroup.normalizer (Vb : Set X))
    (hsT : ∀ w ∈ T, φ s w ∈ T) (hs2 : IsPGroup 2 ↥(Subgroup.zpowers s)) :
    ∃ r ∈ Rb, ∀ w ∈ T, φ s w = φ r w := by
  classical
  have hsR' : ∀ r ∈ Rb, s * r * s⁻¹ ∈ Rb := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hsR r).mp hr
  have hsL' : ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hsL l).mp hl
  have hsV' : ∀ v ∈ Vb, s * v * s⁻¹ ∈ Vb := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hsV v).mp hv
  have hsVi : ∀ v ∈ Vb, s⁻¹ * v * s⁻¹⁻¹ ∈ Vb := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hsV) v).mp hv
  let cs : ↥Lb → ↥Lb := fun l => ⟨s * l * s⁻¹, hsL' l l.2⟩
  have hcs_mul : ∀ l l' : ↥Lb, cs (l * l') = cs l * cs l' := fun l l' => by
    apply Subtype.ext
    simp only [cs, Subgroup.coe_mul]
    group
  have hwd : ∀ l l' : ↥Lb, θ l = θ l' → θ (cs l) = θ (cs l') := by
    intro l l' h
    have h1 : θ (l⁻¹ * l') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hsV' _ ((hθk _).mp h1)
    have h3 : cs (l⁻¹ * l') = (cs l)⁻¹ * cs l' := by
      apply Subtype.ext
      simp only [cs, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h4 : θ (cs (l⁻¹ * l')) = 1 := (hθk _).mpr h2
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h4
    exact h4
  let sec := Function.surjInv hθs
  have hsec : ∀ x, θ (sec x) = x := Function.surjInv_eq hθs
  let Af : (Fin 4 → K) → (Fin 4 → K) :=
    fun v => Multiplicative.toAdd (θ (cs (sec (Multiplicative.ofAdd v))))
  have hAf : ∀ l : ↥Lb, Af (Multiplicative.toAdd (θ l)) = Multiplicative.toAdd (θ (cs l)) := by
    intro l
    show Multiplicative.toAdd (θ (cs (sec (Multiplicative.ofAdd (Multiplicative.toAdd (θ l)))))) =
      _
    rw [ofAdd_toAdd, hwd _ _ (hsec _)]
  have hpre : ∀ v : Fin 4 → K, ∃ l : ↥Lb, Multiplicative.toAdd (θ l) = v := fun v =>
    ⟨sec (Multiplicative.ofAdd v), by rw [hsec]; rfl⟩
  have hAadd : ∀ v v', Af (v + v') = Af v + Af v' := by
    intro v v'
    obtain ⟨l, rfl⟩ := hpre v
    obtain ⟨l', rfl⟩ := hpre v'
    have e3 : Multiplicative.toAdd (θ l) + Multiplicative.toAdd (θ l') =
        Multiplicative.toAdd (θ (l * l')) := by rw [map_mul]; rfl
    rw [e3, hAf, hAf, hAf, hcs_mul, map_mul]
    rfl
  have hAinj : Function.Injective Af := by
    intro v v' h
    obtain ⟨l, rfl⟩ := hpre v
    obtain ⟨l', rfl⟩ := hpre v'
    rw [hAf, hAf] at h
    have h1 : θ (cs l) = θ (cs l') := Multiplicative.toAdd.injective h
    have h2 : θ ((cs l)⁻¹ * cs l') = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := hsVi _ ((hθk _).mp h2)
    have h4 : s⁻¹ * (((cs l)⁻¹ * cs l' : ↥Lb) : X) * s⁻¹⁻¹ = ((l⁻¹ * l' : ↥Lb) : X) := by
      simp only [cs, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h4] at h3
    have h5 : θ (l⁻¹ * l') = 1 := (hθk _).mpr h3
    rw [map_mul, map_inv, inv_mul_eq_one] at h5
    rw [h5]
  let A : (Fin 4 → K) ≃+ (Fin 4 → K) :=
    AddEquiv.ofBijective (AddMonoidHom.mk' Af hAadd)
      ⟨hAinj, Finite.injective_iff_surjective.mp hAinj⟩
  have hAapp : ∀ v, A v = Af v := fun v => rfl
  have hAη : ∀ (r : ↥Rb) (v : Fin 4 → K), A (η r • v) = η ⟨s * r * s⁻¹, hsR' r r.2⟩ • A v := by
    intro r v
    obtain ⟨l, rfl⟩ := hpre v
    set l₁ : ↥Lb := ⟨(r : X) * l * (r : X)⁻¹, hRL r r.2 l l.2⟩ with hl₁
    have e1 : η r • Multiplicative.toAdd (θ l) = Multiplicative.toAdd (θ l₁) :=
      (hθ r l l₁ rfl).symm
    rw [hAapp, hAapp, e1, hAf, hAf]
    refine hθ ⟨s * r * s⁻¹, hsR' r r.2⟩ (cs l) (cs l₁) ?_
    show s * ((r : X) * l * (r : X)⁻¹) * s⁻¹ = s * r * s⁻¹ * (s * l * s⁻¹) * (s * r * s⁻¹)⁻¹
    group
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_of_scalar_commutant (K := K) (K' := K)
    (A := Fin 4 → K) rfl (addCommutantScalar_statedSL (K := K) (m := 4) (by norm_num)) A (by
      intro c Xg hXg v
      rw [statedSL_eq_range_toGL] at hXg
      obtain ⟨g, rfl⟩ := hXg
      obtain ⟨r', hr'⟩ := hηs g
      set r : ↥Rb := ⟨s⁻¹ * r' * s⁻¹⁻¹,
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hsR) r').mp r'.2⟩ with hr
      have hrr : (⟨s * r * s⁻¹, hsR' r r.2⟩ : ↥Rb) = r' := by
        apply Subtype.ext
        show s * (s⁻¹ * (r' : X) * s⁻¹⁻¹) * s⁻¹ = r'
        group
      have hA' : ∀ w, A (η r • w) = g • A w := fun w => by rw [hAη, hrr, hr']
      have hAs : ∀ u, A.symm (g • u) = η r • A.symm u := fun u => by
        apply A.injective
        rw [AddEquiv.apply_symm_apply, hA', AddEquiv.apply_symm_apply]
      have hmv : ∀ u, ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) *ᵥ u = g • u := fun u => rfl
      rw [hmv, hmv, hAs, ← smul_comm (η r) c, hA'])
  let φsT : ↥T →ₗ[K] ↥T := LinearMap.restrict (φ s : E →ₗ[K] E) hsT
  have hφsT_inj : Function.Injective φsT := by
    intro w w' h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact (φ s).injective this
  let Bt : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
    (ψ.symm.trans (LinearEquiv.ofInjectiveEndo φsT hφsT_inj)).trans ψ
  have hBt : ∀ (r : ↥Rb) (w : Fin 3 ⊕ Fin 3 → K),
      Bt (PartOne.K159.Klein.rho (η r) w) =
        PartOne.K159.Klein.rho (η ⟨s * r * s⁻¹, hsR' r r.2⟩) (Bt w) := by
    intro r w
    obtain ⟨x, rfl⟩ : ∃ x : ↥T, ψ x = w := ⟨ψ.symm w, ψ.apply_symm_apply w⟩
    have hrx : φ (r : X) x ∈ T := hRT r r.2 x x.2
    rw [← hψ r x ⟨_, hrx⟩ rfl]
    show ψ (φsT (ψ.symm (ψ ⟨_, hrx⟩))) = PartOne.K159.Klein.rho (η ⟨s * r * s⁻¹, hsR' r r.2⟩)
      (ψ (φsT (ψ.symm (ψ x))))
    rw [ψ.symm_apply_apply, ψ.symm_apply_apply]
    refine hψ ⟨s * r * s⁻¹, hsR' r r.2⟩ (φsT x) (φsT ⟨_, hrx⟩) ?_
    show φ s (φ (r : X) x) = φ (s * r * s⁻¹) (φ s x)
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, phi_inv_apply_phi]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  let ru : K → ↥Rb := fun t => Function.surjInv hηs (Matrix.SpecialLinearGroup.transvection h01 t)
  have hru : ∀ t, η (ru t) = Matrix.SpecialLinearGroup.transvection h01 t := fun t =>
    Function.surjInv_eq hηs _
  have hτ1 : τ = RingEquiv.refl K := by
    refine ringEquiv_eq_refl_of_kleinTwist τ A hτ
      (fun t => η ⟨s * ru t * s⁻¹, hsR' (ru t) (ru t).2⟩) (fun t v => ?_) Bt (fun t w => ?_)
    · rw [← hru t, hAη]
    · rw [← hru t, hBt]
  have hAlin : ∀ (c : K) (v : Fin 4 → K), A (c • v) = c • A v := fun c v => by
    rw [hτ, hτ1, RingEquiv.refl_apply]
  let Al : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := { A with map_smul' := hAlin }
  obtain ⟨r₀, hr₀, c, hc⟩ := exists_smul_agree_of_conj φ T η hηs hη1 hRT hschur hsR' hsT Al hAη
  exact ⟨r₀, hr₀, agree_of_smul_agree_of_isPGroup φ T hT0 hRT hscal hs2 hr₀ hc⟩

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.rSylow_of_layerWedge (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hCent : Sec715CentStatement) (hHard : Step713O2HardStatement)
    (hWedge : Sec717LayerWedgeStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZNc : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {L : Subgroup G} (hL : Sec717L hc t Z0 L) (hLn : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L)
    {m : ℕ} {γ : G → GaloisField 2 m} (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ)
    (hM : GlobalModelData M Q Z γ M₀)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[GaloisField 2 m] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule (GaloisField 2 m) M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∃ S : Sylow 2 ↥(bar M Q (H0 M Z)),
      (S : Subgroup ↥(bar M Q (H0 M Z))) ≤
        (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) := by
  classical
  have hn10 : n = 10 := by
    have hcN78 := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 3 (by norm_num) (Or.inl hp3)
    unfold Conc78 at hcN78
    rcases hcN78 with ⟨-, h10, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
    · exact h10
    all_goals omega
  subst hn10
  have LD := hc.sec717LayerData h34 h311a hZt hZcard hZc h78 hZV h52a hA hs hp3 hZ0 hZNc hTI hL
    hLn M₀ hM φ hφπ T hT
  have Bs := Ctx.yBase h34 h311a hZt hZcard hZc h78 hc hs hp3 hZ0 hZNc hTI hL hLn
  obtain ⟨η, hηs, hηk, ⟨θ, hθs, hθk, hθ⟩, ψ, hψ⟩ :=
    hWedge G M Q Z B hc 10 t hs hp3 Z0 hZ0 hZNc hTI L hL hLn m γ M₀ hM φ hφπ T hT
  have hKT : ∀ k ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      ∀ w ∈ T, φ k w ∈ T := by
    intro k hk w hw
    obtain ⟨a₀, ha₀V, ha₀1⟩ := LD.V_ne
    have hkN : k ∈ Subgroup.normalizer
        (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup ↥(bar M Q (H0 M Z))) :
          Set ↥(bar M Q (H0 M Z))) := by
      rw [← Bs.K_eq]; exact hk
    have hkV := (Subgroup.mem_normalizer_iff.mp hkN a₀).mp ha₀V
    have hka1 : k * a₀ * k⁻¹ ≠ 1 := fun h => ha₀1 (by
      have e : a₀ = k⁻¹ * (k * a₀ * k⁻¹) * k := by group
      rw [e, h]
      group)
    rw [← LD.range_V a₀ ha₀V ha₀1] at hw
    obtain ⟨e, rfl⟩ := hw
    rw [← LD.range_V _ hkV hka1]
    refine ⟨φ k e, ?_⟩
    rw [opm_conj, phi_inv_apply_phi]
  have hNfix : ∀ r ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ w ∈ T, φ r w = w :=
    fun r hr w hw => by
      have h := (LD.Nb_low r hr).bot w hw
      rw [opm_apply, sub_eq_zero] at h
      exact h
  have hT0 : T ≠ ⊥ := by
    intro h
    have h6 := LD.finrank_T
    rw [h, finrank_bot] at h6
    exact absurd h6 (by norm_num)
  have h2 : ∀ s ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      IsPGroup 2 ↥(Subgroup.zpowers s) →
        ∃ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
          ∀ w ∈ T, φ s w = φ r w := by
    intro s hsK hs2
    have hsV : s ∈ Subgroup.normalizer
        (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup ↥(bar M Q (H0 M Z))) :
          Set ↥(bar M Q (H0 M Z))) := by
      rw [← Bs.K_eq]; exact hsK
    exact agree_of_wedge_of_isPGroup φ T hT0
      (fun r hr l hl => (Subgroup.mem_normalizer_iff.mp (Bs.Ln r (Bs.RK hr)) l).mp hl)
      η hηs (fun r hr w hw => hNfix _ ((hηk r).mp hr) w hw) θ hθs hθk hθ ψ hψ LD.Rb_T
      (fun x hxT hxR => hc.smul_of_comm_layerT hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ T hT hxT hxR)
      (fun r hr c hrc => hc.eq_one_of_smul_layerT hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ T hT hr
        hrc)
      (Bs.Rn s hsK) (Bs.Ln s hsK) hsV (hKT s hsK) hs2
  have h4mid := hc.opm_mem_of_two_fix_T h34 hA hPts h52a h52b hZt hZcard hZc hZV hs hp3 hZ0 M₀ hM
    φ hφπ T hT LD.Rb_T LD.Rb_fix
  exact hc.rSylow_of_layerSteps h34 h311a hZt hZcard hZc h78 hZV h52a hA hCent hHard hs hp3 hZ0
    hZNc hTI hL hLn M₀ hM φ hφπ T hT h2 h4mid

theorem sec717RSylow_indep (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hCent : Sec715CentStatement) (hHard : Step713O2HardStatement)
    (hWedge : Sec717LayerWedgeStatement) : Sec717RSylowStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZNc hTI L hL hLn
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  obtain ⟨m, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ₀, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hM
  obtain ⟨φ, -, hφmk⟩ := exists_barAct hQH hHM φ₀ hφker
  have hφπ' : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z))
      (x : G), x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x) := by
    intro y hy x hx
    have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hy
    rw [hφmk y hy hyH]
    exact hφπ ⟨(y : G), hyH⟩ x hx
  obtain ⟨Tt, hTtR, -, -, -⟩ := Ctx.move_Tt_facts hZV hZc hZcard hc hs hp3 hZ0 M₀ hM.card φ hφπ'
  have hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = Tt 1 := fun a ha ha1 => by
    have h := hTtR 1 a ha ha1
    simpa using h
  exact hc.rSylow_of_layerWedge h34 h311a hZt hZcard hZc h78 hZV h52a h52b hA hPts hCent hHard
    hWedge hs hp3 hZ0 hZNc hTI hL hLn M₀ hM φ hφπ' (Tt 1) hT

end CFSG.RankThree.GF2n.Stroth80
