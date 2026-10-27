module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Two
public import CFSG.RankThree.GF2n.Stroth80.Sec57
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatField
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatPsi

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem addEquiv_imgSub_smul {ι G Kg K' : Type} [Group G] [Field Kg] [Field K']
    {Q Z V : Subgroup G} {γ : G → Kg} (M₀ : Tim79.QuadModel Q Z Kg γ) (hVQ : V ≤ Q)
    (hS : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V)
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K'))
    (θ : Kg ≃+* K')
    (hθ : ∀ (c : Kg) (v w : ↥V), M₀.π w = c • M₀.π v →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (Ψ : ↥(imgSub M₀ V hS) ≃+ (ι → K'))
    (hΨ : ∀ (v : ↥V) (h : M₀.π v ∈ imgSub M₀ V hS),
      Ψ ⟨M₀.π v, h⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∀ (c : Kg) (e : ↥(imgSub M₀ V hS)), Ψ (c • e) = θ c • Ψ e := by
  intro c e
  obtain ⟨v, hvV, hvQ, hv⟩ := M₀.mem_img.mp ((mem_imgSub (M₀ := M₀) (hS := hS)).mp e.2)
  obtain ⟨v', hv'V, hv'Q, hv'⟩ :=
    M₀.mem_img.mp (hS c _ ((mem_imgSub (M₀ := M₀) (hS := hS)).mpr (M₀.pi_mem_img hvV hvQ)))
  have hve : (e : M₀.E) = M₀.π v := hv.symm
  have hv'm : M₀.π v' = c • M₀.π v := by rw [hv']
  have hce : c • e = ⟨M₀.π v', (mem_imgSub (M₀ := M₀)).mpr
      (M₀.pi_mem_img hv'V hv'Q)⟩ := Subtype.ext (by
    show c • (e : M₀.E) = M₀.π v'
    rw [hve, ← hv'])
  have he : e = ⟨M₀.π v, (mem_imgSub (M₀ := M₀)).mpr
      (M₀.pi_mem_img hvV hvQ)⟩ := Subtype.ext hve
  calc
    Ψ (c • e) = Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v', hv'V⟩)) := by
      rw [hce]
      exact hΨ ⟨v', hv'V⟩ _
    _ = θ c • Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hvV⟩)) :=
      hθ c ⟨v, hvV⟩ ⟨v', hv'V⟩ hv'm
    _ = θ c • Ψ e := by
      rw [he]
      exact congrArg (θ c • ·) (hΨ ⟨v, hvV⟩ _).symm

private noncomputable def imgSubCoordsEquiv {ι G Kg K' : Type} [Group G] [Field Kg] [Field K']
    {Q Z V : Subgroup G} {γ : G → Kg} (M₀ : Tim79.QuadModel Q Z Kg γ)
    (hS : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V)
    (θ : Kg ≃+* K') (Ψ : ↥(imgSub M₀ V hS) ≃+ (ι → K'))
    (hΨsmul : ∀ (c : Kg) (e : ↥(imgSub M₀ V hS)), Ψ (c • e) = θ c • Ψ e) :
    ↥(imgSub M₀ V hS) ≃ₗ[Kg] (ι → Kg) :=
  AddEquiv.toLinearEquiv
    { toFun := fun e i => θ.symm (Ψ e i)
      invFun := fun v => Ψ.symm (fun i => θ (v i))
      left_inv := fun e => Ψ.injective (by
        rw [AddEquiv.apply_symm_apply]
        funext i
        exact RingEquiv.apply_symm_apply θ (Ψ e i))
      right_inv := fun v => by
        funext i
        change θ.symm (Ψ (Ψ.symm (fun i => θ (v i))) i) = v i
        rw [AddEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
      map_add' := fun e e' => by
        funext i
        change θ.symm (Ψ (e + e') i) = θ.symm (Ψ e i) + θ.symm (Ψ e' i)
        rw [map_add, Pi.add_apply, map_add] }
    fun c e => by
      funext i
      change θ.symm (Ψ (c • e) i) = c * θ.symm (Ψ e i)
      rw [hΨsmul, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]

private theorem exists_preimage_map_statedSL {G : Type} [Group G] {R : Subgroup G}
    {K K' : Type} [Field K] [Field K'] {m : ℕ} (θ : K ≃+* K')
    (φ' : ↥R →* GL (Fin m) K') (hφ' : φ'.range = StatedSL m K')
    (A : Matrix.SpecialLinearGroup (Fin m) K) :
    ∃ r₀ : ↥R, φ' r₀ = Matrix.SpecialLinearGroup.toGL (A.map θ) := by
  have hmem : Matrix.SpecialLinearGroup.toGL (A.map θ) ∈ φ'.range := by
    rw [hφ', CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
    exact MonoidHom.mem_range.mpr ⟨A.map θ, rfl⟩
  exact MonoidHom.mem_range.mp hmem

private theorem exists_mul_mem_inf_centralizer {G : Type} [Group G] {R Q : Subgroup G} {t : G}
    [(Q.subgroupOf R).Normal]
    (hR : R = Q ⊔ (R ⊓ Subgroup.centralizer ({t} : Set G))) {r₀ : G} (hr₀ : r₀ ∈ R) :
    ∃ q₀ ∈ Q, ∃ r ∈ R ⊓ Subgroup.centralizer ({t} : Set G), q₀ * r = r₀ := by
  have hQR : Q ≤ R := by rw [hR]; exact le_sup_left
  have hKR : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ R := inf_le_left
  have hmem : (⟨r₀, hr₀⟩ : ↥R) ∈ (Q.subgroupOf R) ⊔
      ((R ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf R) := by
    rw [← Subgroup.subgroupOf_sup hQR hKR]
    exact Subgroup.mem_subgroupOf.mpr (hR ▸ hr₀)
  obtain ⟨q, hq, k, hk, hqk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨(q : G), Subgroup.mem_subgroupOf.mp hq, (k : G), Subgroup.mem_subgroupOf.mp hk, ?_⟩
  simpa using congrArg Subtype.val hqk


private theorem exists_mem_centralizer_action
    {hc : Ctx M Q Z B} {m : ℕ} {t : G} (htLB : t ∈ LB M Q B)
    (h102 : Rt M (LB M Q B) t =
      Q ⊔ (Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G)))
    {K K' : Type} [Field K] [Field K']
    (φ' : ↥(Rt M (LB M Q B) t) →* GL (Fin m) K')
    (hφ'ker : φ'.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    (A : Matrix.SpecialLinearGroup (Fin m) K) (θ : K ≃+* K')
    (r₀ : ↥(Rt M (LB M Q B) t))
    (hr₀ : φ' r₀ = Matrix.SpecialLinearGroup.toGL (A.map θ)) :
    ∃ (r : G) (hr : r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G))
      (hrH0 : r ∈ H0 M Z), φ' ⟨r, hr.1⟩ = Matrix.SpecialLinearGroup.toGL (A.map θ) := by
  have hQR : Q ≤ Rt M (LB M Q B) t := by rw [h102]; exact le_sup_left
  have hQNR : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQR).mpr
      (fun x hx => hc.hyp.Q_normal.2 (hc.Rt_le_M t hx))
  haveI := hQNR
  obtain ⟨q₀, hq₀Q, rC, hrC, hq₀rC⟩ := exists_mul_mem_inf_centralizer h102 r₀.2
  have hrCH0 : rC ∈ H0 M Z := hc.Rt_le_H0 t hrC.1
  have hq₀R : q₀ ∈ Rt M (LB M Q B) t := hc.Q_le_Rt htLB hq₀Q
  have hq₀CN : q₀ ∈ hc.CN t :=
    Ctx.mem_CN.mpr ⟨hq₀R, fun v hv =>
      hc.hyp.toHyp79.comm_mem_V hq₀Q (hc.Vt_le_Q t hv)⟩
  have hφ'q₀ : φ' ⟨q₀, hq₀R⟩ = 1 :=
    MonoidHom.mem_ker.mp (by
      rw [hφ'ker]
      exact Subgroup.mem_subgroupOf.mpr hq₀CN)
  have hφ'rC : φ' ⟨rC, hrC.1⟩ = Matrix.SpecialLinearGroup.toGL (A.map θ) := by
    have hrCeq : (⟨rC, hrC.1⟩ : ↥(Rt M (LB M Q B) t)) = ⟨q₀, hq₀R⟩⁻¹ * r₀ :=
      Subtype.ext (by
        show rC = q₀⁻¹ * (r₀ : G)
        rw [← hq₀rC]
        group)
    rw [hrCeq, map_mul, map_inv, hφ'q₀, inv_one, one_mul, hr₀]
  exact ⟨rC, hrC, hrCH0, hφ'rC⟩

private theorem apply_basis_eq_sum
    (hc : Ctx M Q Z B) {m : ℕ} {t : G}
    {K K' : Type} [Field K] [Field K']
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (h : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((h : G) * x * (h : G)⁻¹) = φ h (M₀.π x))
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (hRV : Rt M (LB M Q B) t ≤
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (φ' : ↥(Rt M (LB M Q B) t) →* GL (Fin m) K')
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸
      Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃* Multiplicative (Fin m → K'))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t))
      (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ' s : Matrix (Fin m) (Fin m) K') *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (Ψ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) ≃+ (Fin m → K'))
    (hΨ : ∀ (v : ↥(Vt M (LB M Q B) B Z t))
      (h : M₀.π v ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS),
      Ψ ⟨M₀.π v, h⟩ = Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (b : Module.Basis (Fin m) K (imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    (θ : K ≃+* K')
    (hΨsmul : ∀ (c : K) (e : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)),
      Ψ (c • e) = θ c • Ψ e)
    (hΨbj : ∀ j, Ψ (b j) = Pi.single j 1)
    {A : Matrix.SpecialLinearGroup (Fin m) K} {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hrH0 : r ∈ H0 M Z)
    (hrφ' : φ' ⟨r, hr⟩ = Matrix.SpecialLinearGroup.toGL (A.map θ)) :
    ∀ j, φ ⟨r, hrH0⟩ (b j) =
      ∑ i, (A : Matrix (Fin m) (Fin m) K) i j • (b i : M₀.E) := by
  intro j
  obtain ⟨vj, hvjV, hvjQ, hvjπ⟩ :=
    M₀.mem_img.mp ((mem_imgSub (M₀ := M₀) (hS := hS)).mp (b j).2)
  have hwVQ : r * vj * r⁻¹ ∈ Vt M (LB M Q B) B Z t ⊓ Q :=
    ⟨(Subgroup.mem_normalizer_iff.mp (hRV hr) vj).mp hvjV,
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) vj).mp hvjQ⟩
  have hmemφ : φ ⟨r, hrH0⟩ (b j) ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS := by
    rw [mem_imgSub, ← hvjπ, ← hφπ ⟨r, hrH0⟩ vj hvjQ]
    exact M₀.pi_mem_img hwVQ.1 hwVQ.2
  let eφ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
    ⟨φ ⟨r, hrH0⟩ (b j), hmemφ⟩
  have hΨφ : Ψ eφ =
      ((Matrix.SpecialLinearGroup.toGL (A.map θ) : GL (Fin m) K') :
        Matrix (Fin m) (Fin m) K') *ᵥ Pi.single j 1 := by
    have heq : eφ = ⟨M₀.π (r * vj * r⁻¹), (mem_imgSub (hS := hS)).mpr
        (M₀.pi_mem_img hwVQ.1 hwVQ.2)⟩ := Subtype.ext (by
      show φ ⟨r, hrH0⟩ (b j) = M₀.π (r * vj * r⁻¹)
      rw [← hvjπ, ← hφπ ⟨r, hrH0⟩ vj hvjQ])
    rw [heq, hΨ ⟨r * vj * r⁻¹, hwVQ.1⟩]
    have hψ' := hψ ⟨r, hr⟩ ⟨vj, hvjV⟩ ⟨r * vj * r⁻¹, hwVQ.1⟩ rfl
    rw [hψ', hrφ',
      ← hΨ ⟨vj, hvjV⟩ ((mem_imgSub (hS := hS)).mpr (M₀.pi_mem_img hvjV hvjQ)),
      show (⟨M₀.π vj, _⟩ : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) = b j
        from Subtype.ext hvjπ,
      hΨbj j]
  have hsumΨ : Ψ (∑ i, A i j • b i) =
      ((Matrix.SpecialLinearGroup.toGL (A.map θ) : GL (Fin m) K') :
        Matrix (Fin m) (Fin m) K') *ᵥ Pi.single j 1 := by
    rw [map_sum]; simp only [hΨsmul, hΨbj]
    rw [Matrix.mulVec_single_one]
    funext k
    rw [Finset.sum_apply, Matrix.col_apply]
    calc
      ∑ i, (θ (A i j) • Pi.single i 1 : Fin m → K') k =
          ∑ i, Pi.single i (θ (A i j)) k := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      _ = θ (A k j) := by
        simpa using Finset.sum_pi_single k (fun i : Fin m => θ (A i j)) Finset.univ
      _ = ((Matrix.SpecialLinearGroup.toGL (A.map θ) : GL (Fin m) K') :
          Matrix (Fin m) (Fin m) K') k j := by
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have heq : eφ = ∑ i, A i j • b i := Ψ.injective (hΨφ.trans hsumΨ.symm)
  simpa [eφ, Submodule.coe_sum, Submodule.coe_smul] using congrArg Subtype.val heq

theorem SLMNat.exists_basis_statedSL (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n m : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) (hm : SLMNat hc t m) (hm2 : 2 ≤ m)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (h : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((h : G) * x * (h : G)⁻¹) = φ h (M₀.π x)) :
    ∃ b : Module.Basis (Fin m) K
        (imgSub M₀ (Vt M (LB M Q B) B Z t) fun c _ he => hc.smul_mem_img_Vt hM t c he),
      ∀ A : Matrix.SpecialLinearGroup (Fin m) K,
        ∃ r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G), ∃ hr : r ∈ H0 M Z,
          ∀ j, φ ⟨r, hr⟩ (b j) =
            ∑ i, (A : Matrix (Fin m) (Fin m) K) i j • (b i : M₀.E) := by
  classical
  let V := Vt M (LB M Q B) B Z t
  let R := Rt M (LB M Q B) t
  have hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V :=
    fun c e he => hc.smul_mem_img_Vt hM t c he
  obtain ⟨K', fK', finK', hK', hrep⟩ := hm
  letI := fK'
  letI := finK'
  obtain ⟨φ', hφ'range, hφ'ker, hRV, hZnorm, ψ, hψ⟩ := hrep
  haveI := hZnorm
  have hcard : Nat.card K = Nat.card K' := hM.card.trans hK'.symm
  have hX : AddCommutantScalar (StatedSL m K') := addCommutantScalar_statedSL hm2
  have hlin : ∀ r ∈ R, ∃ T : M₀.E →ₗ[K] M₀.E,
      ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x) := by
    intro r hr
    exact ⟨(φ ⟨r, hc.Rt_le_H0 t hr⟩ : M₀.E →ₗ[K] M₀.E),
      fun x hx => hφπ ⟨r, hc.Rt_le_H0 t hr⟩ x hx⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcard M₀ (hc.Vt_le_Q t) hX hS hlin φ' hφ'range hRV ψ hψ
  obtain ⟨Ψ, hΨ⟩ := exists_addEquiv_imgSub M₀ (hc.Vt_le_Q t) hS ψ
  have hΨsmul : ∀ (c : K) (e : ↥(imgSub M₀ V hS)), Ψ (c • e) = θ c • Ψ e :=
    addEquiv_imgSub_smul M₀ (hc.Vt_le_Q t) hS ψ θ hθ Ψ hΨ
  let L : ↥(imgSub M₀ V hS) ≃ₗ[K] (Fin m → K) :=
    imgSubCoordsEquiv M₀ hS θ Ψ hΨsmul
  let b : Module.Basis (Fin m) K (imgSub M₀ V hS) := Module.Basis.ofEquivFun L
  have hb : ∀ j, b j = L.symm (Pi.single j 1) := fun j =>
    congrFun (Module.Basis.coe_ofEquivFun L) j
  have hLb : ∀ j, L (b j) = Pi.single j 1 := fun j => by
    rw [hb j, LinearEquiv.apply_symm_apply]
  have hΨbj : ∀ j, Ψ (b j) = Pi.single j 1 := by
    intro j
    funext i
    have h := congrArg θ (congrFun (hLb j) i)
    simpa [L, imgSubCoordsEquiv, AddEquiv.toLinearEquiv, Pi.single_apply] using h
  have h102 : R = Q ⊔ (R ⊓ Subgroup.centralizer ({t} : Set G)) :=
    stroth_10_2 (stroth_5_7 h34 hspread) G M Q Z B hc n t H ht
  refine ⟨b, ?_⟩
  intro A
  obtain ⟨r₀, hr₀⟩ := exists_preimage_map_statedSL θ φ' hφ'range A
  obtain ⟨rC, hrC, hrCH0, hφ'rC⟩ :=
    exists_mem_centralizer_action ht.mem_LB h102 φ' hφ'ker A θ r₀ hr₀
  exact ⟨rC, hrC, hrCH0,
    apply_basis_eq_sum hc φ hφπ hS hRV φ' ψ hψ Ψ hΨ b θ hΨsmul hΨbj
      hrC.1 hrCH0 hφ'rC⟩

end CFSG.RankThree.GF2n.Stroth80
