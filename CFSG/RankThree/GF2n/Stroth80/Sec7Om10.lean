module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Steps
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Point
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10LinAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Symplectic
  CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace Om10

section Stab

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def stabVec (a : ι → K) : Subgroup (GL ι K) where
  carrier := {A | (A : Matrix ι ι K) *ᵥ a = a}
  mul_mem' := fun {A B} hA hB => by
    show ((A * B : GL ι K) : Matrix ι ι K) *ᵥ a = a
    rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    rw [show (B : Matrix ι ι K) *ᵥ a = a from hB]
    exact hA
  one_mem' := by
    show ((1 : GL ι K) : Matrix ι ι K) *ᵥ a = a
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  inv_mem' := fun {A} hA => by
    show ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ a = a
    have hA' : (A : Matrix ι ι K) *ᵥ a = a := hA
    conv_lhs => rw [← hA']
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

variable {G : Type} [Group G]

@[expose] def stabSub {R : Subgroup G} (φ : ↥R →* GL ι K) (a : ι → K) : Subgroup G :=
  ((stabVec a).comap φ).map R.subtype

theorem mem_stabSub {R : Subgroup G} {φ : ↥R →* GL ι K} {a : ι → K} {y : G} :
    y ∈ stabSub φ a ↔ ∃ hy : y ∈ R, (φ ⟨y, hy⟩ : Matrix ι ι K) *ᵥ a = a := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

theorem stabSub_le {R : Subgroup G} (φ : ↥R →* GL ι K) (a : ι → K) : stabSub φ a ≤ R :=
  Subgroup.map_subtype_le _

end Stab

theorem isOppDecomp_symm {G : Type} [Group G] {P I L₁ L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) : IsOppDecomp P I L₂ L₁ A₂ A₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hd
  exact ⟨h3, h4, h1, h2, by rw [sup_comm]; exact h5, by rw [inf_comm]; exact h6, h7, h8, h10, h9⟩

end Om10

open Om10 in
theorem step71VanishOmega10_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hPair : Step71VanishPairStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) :
    Step71VanishOmega10Statement := by
  intro G _ _ M Q Z B hc n t hs hno hom hn x hx hxt v hv
  by_contra hvZ
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hxH, hx2⟩ := conjMod_facts hc ht hx
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hxM : x ∈ M := hx.1
  have hom' := hom
  obtain ⟨K, fK, finK, hK, hnat⟩ := hom
  haveI : CharP K 2 := sec7ctr_charP hc hK
  have hnat' := hnat
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨-, hnrm, ψ, hψ⟩ := hact
  haveI := hnrm
  haveI : Nonempty (Fin 5 ⊕ Fin 5) := ⟨Sum.inl 0⟩
  have hm3 : 3 ≤ 5 := by norm_num
  have hX := addCommutantScalar_statedOmegaPlus (K := K) hm3
  have hQnd := nondegenerate_polarBilin_quadPlus 5 K
  have E := ElemMatrixIso.plus (K := K) hm3
  have h3 : 3 ≤ Module.finrank K (Fin 5 ⊕ Fin 5 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have h4 : 4 ≤ Fintype.card (Fin 5 ⊕ Fin 5) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  obtain ⟨Fx, hFx⟩ := exists_fx_of_natural h34 (stroth310Chi_of_34 h34) hZc hZV hZcard hc hs hZ0
    hK hX φ hφ ψ hψ hxM hxt hxH
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ w ∈ Vt M (LB M Q B) B Z t,
      y * w * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy w hw =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) w).mp hw
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)
  have hxV : ∀ w ∈ Vt M (LB M Q B) B Z t, x * w * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hxVn w).mp hw
  have hxR : ∀ y ∈ Rt M (LB M Q B) t, x * y * x⁻¹ ∈ Rt M (LB M Q B) t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc hxM hxt)) y).mp hy
  have hRM : ∀ y ∈ Rt M (LB M Q B) t, y ∈ M := fun y hy => hc.Rt_le_M t hy
  have hxQn : x ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hxM
  have hxWn : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), x * w * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun w hw => conj_mem_Wt hxQn hxVn hw
  have hRW : ∀ r ∈ Rt M (LB M Q B) t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      r * w * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun r hr w hw =>
    conj_mem_Wt (hc.hyp.Q_normal.2 (hRM r hr)) (hc.Rt_normalizes_Vt ht hr) hw
  have hFFx : ∀ w, Fx (Fx w) = w := by
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    set k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k * x⁻¹, hxV k k.2⟩ with hk₁
    set k₂ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k₁ * x⁻¹, hxV k₁ k₁.2⟩ with hk₂
    have e1 : Fx (secVec ψ k) = secVec ψ k₁ := hFx k k₁ rfl
    have e2 : Fx (secVec ψ k₁) = secVec ψ k₂ := hFx k₁ k₂ rfl
    rw [e1, e2, secVec_eq_iff]
    have e3 : (k₂ : G) * (k : G)⁻¹ = ⁅x ^ 2, (k : G)⁆ := by
      rw [hk₂, hk₁]
      simp only [commutatorElement_def, pow_two]
      group
    rw [e3]
    exact Smith81.comm_mem_Z hc.hyp hx2 (hVQ k.2)
  have hcompat : ∀ g ∈ StatedOmega (StatedQuadPlus 5 K), ∃ g' ∈ StatedOmega (StatedQuadPlus 5 K),
      ∀ w, Fx ((g : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ Fx w) =
        (g' : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w := by
    intro g hg
    have hgR : g ∈ φ.range := by rw [hφ]; exact hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hgR
    have ha' : x * (a : G) * x⁻¹ ∈ Rt M (LB M Q B) t := hxR a a.2
    have ha'M : x * (a : G) * x⁻¹ ∈ M := M.mul_mem (M.mul_mem hxM (hRM a a.2)) (M.inv_mem hxM)
    refine ⟨φ ⟨x * (a : G) * x⁻¹, ha'⟩, ?_, ?_⟩
    · rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    have eL : Fx ((φ a : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ Fx (secVec ψ k)) =
        secVec ψ ⟨x * ((a : G) * (x * k * x⁻¹) * (a : G)⁻¹) * x⁻¹,
          hxV _ (hVR a a.2 _ (hxV k k.2))⟩ := by
      have e1 : Fx (secVec ψ k) = secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ :=
        hFx k ⟨x * k * x⁻¹, hxV k k.2⟩ rfl
      rw [e1]
      have e2 : (φ a : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ
          secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ =
          secVec ψ ⟨(a : G) * (x * k * x⁻¹) * (a : G)⁻¹, hVR a a.2 _ (hxV k k.2)⟩ :=
        (hψ a ⟨x * k * x⁻¹, hxV k k.2⟩ _ rfl).symm
      rw [e2]
      exact hFx _ _ rfl
    have eR : (φ ⟨x * (a : G) * x⁻¹, ha'⟩ : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ
        secVec ψ k =
        secVec ψ ⟨x * (a : G) * x⁻¹ * k * (x * (a : G) * x⁻¹)⁻¹, hVR _ ha' k k.2⟩ :=
      (hψ ⟨x * (a : G) * x⁻¹, ha'⟩ k _ rfl).symm
    rw [eL, eR, secVec_eq_iff]
    have hz : x * (a : G) * x⁻¹ * ⁅x ^ 2, (k : G)⁆ * (x * (a : G) * x⁻¹)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha'M) _).mp
        (Smith81.comm_mem_Z hc.hyp hx2 (hVQ k.2))
    convert hz using 1
    simp only [commutatorElement_def, pow_two, Subgroup.coe_mk]
    group
  have hN : ∀ A : GL (Fin 5 ⊕ Fin 5) K,
      (∀ g ∈ StatedOmega (StatedQuadPlus 5 K), A * g * A⁻¹ ∈ StatedOmega (StatedQuadPlus 5 K)) →
      ∃ c : K, c ≠ 0 ∧ ∀ w, quadPlus 5 K
        (c • ((A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w)) = quadPlus 5 K w := by
    intro A hA
    obtain ⟨c, hc0, hcv⟩ := normalizerOmegaFor_plus K hK4 (by norm_num : 2 ≤ 5) A hA
    exact ⟨c, hc0, fun w => by rw [coe_quadPlus]; exact hcv w⟩
  have iso : ∀ w, quadPlus 5 K (Fx w) = quadPlus 5 K w :=
    vanishGeom_isometry_of_normalizer hQnd hN Fx hFFx hcompat
  have hnatO : SpNat hc t ∨ OmegaNat hc t := Or.inr ⟨K, fK, finK, hK, Or.inl ⟨5, hm3, hnat'⟩⟩
  have hW : ∀ c d : Fin 5 ⊕ Fin 5 → K, c ≠ 0 → d ≠ 0 → quadPlus 5 K c = quadPlus 5 K d →
      ∃ A ∈ StatedOmega (StatedQuadPlus 5 K),
        (A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ c = d :=
    fun c d hc0 hd0 hcd => statedOmegaPlus_exists_mulVec_eq hm3 hc0 hd0 hcd
  have hSC := (sec56SingularConj_of h34 hRoot).1 G M Q Z B hc n t hs.toSec5 K hK 5 hm3
  have hOrb := Ctx.conj_orbit_omegaPlus h34 hRoot hc hs.toSec5 hK hm3 hSC hnat'
  have hns := step71Vanish_defect_nonsingular h34 hRoot hZV hc hs hno hnatO hK E hQnd h3 hX φ hφ
    hker ψ hψ hW hOrb hx hxt Fx hFx
  have hne : ∃ w, Fx w ≠ w := by
    refine ⟨secVec ψ ⟨v, hv⟩, fun h => hvZ ?_⟩
    have hcV : ⁅x, v⁆ ∈ Vt M (LB M Q B) B Z t := by
      have e : ⁅x, v⁆ = (x * v * x⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact (Vt M (LB M Q B) B Z t).mul_mem (hxV v hv) ((Vt M (LB M Q B) B Z t).inv_mem hv)
    have e : (⟨⁅x, v⁆, hcV⟩ : ↥(Vt M (LB M Q B) B Z t)) = ⟨x * v * x⁻¹, hxV v hv⟩ * ⟨v, hv⟩⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    have h0 : secVec ψ ⟨⁅x, v⁆, hcV⟩ = 0 := by
      rw [e, secVec_mul, secVec_inv, ← hFx ⟨v, hv⟩ ⟨x * v * x⁻¹, hxV v hv⟩ rfl, h,
        add_neg_cancel]
    exact (secVec_eq_zero_iff ψ _).mp h0
  obtain ⟨a, haQ, hFa⟩ := exists_transvection_of_defect Fx hFFx iso hns hne
  obtain ⟨π, σ, hco⟩ := exists_isCoord haQ
  have hsingB := hc.omega_singular h34 hRoot hs.toSec5 hnatO hK E hQnd h3 hX φ hφ ψ hψ
  obtain ⟨uB, hQuB, huB0, hBiff, -, -, hpts⟩ :=
    hc.omega_points_core h34 hRoot hs.toSec5 hnatO hK E hQnd h3 hX φ hφ hker ψ hψ hsingB
  have hBu : ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B → ∃ c : K, secVec ψ b = c • uB :=
    fun b hb => (hBiff _).mp ⟨b, hb, rfl⟩
  have hmemX : ∀ r : ↥(Rt M (LB M Q B) t), φ r ∈ StatedOmega (StatedQuadPlus 5 K) := fun r => by
    rw [← hφ]
    exact MonoidHom.mem_range.mpr ⟨r, rfl⟩
  have hisoR : ∀ (r : ↥(Rt M (LB M Q B) t)) (w : Fin 5 ⊕ Fin 5 → K),
      quadPlus 5 K ((φ r : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w) = quadPlus 5 K w :=
    fun r w => vanishGeom_isometry_of_mem E (hmemX r) w
  have hpolR : ∀ (r : ↥(Rt M (LB M Q B) t)) (w w' : Fin 5 ⊕ Fin 5 → K),
      polar (quadPlus 5 K) ((φ r : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w)
        ((φ r : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w') =
        polar (quadPlus 5 K) w w' := by
    intro r w w'
    simp only [QuadraticMap.polar, ← Matrix.mulVec_add, hisoR]
  set e₁ : Fin 4 ⊕ Fin 4 → K := Pi.single (Sum.inl 0) 1 with he₁
  set f₁ : Fin 4 ⊕ Fin 4 → K := Pi.single (Sum.inr 0) 1 with hf₁
  have hspef : spForm 4 K e₁ f₁ = 1 := by
    rw [he₁, hf₁, spForm_single_inl_inr]
    simp
  have hQe₁ : quadPlus 4 K e₁ = 0 := by
    rw [quadPlus_apply, he₁]
    simp [Pi.single_apply]
  have hQf₁ : quadPlus 4 K f₁ = 0 := by
    rw [quadPlus_apply, hf₁]
    simp [Pi.single_apply]
  set b₁ := σ e₁ with hb₁
  set b₂ := σ f₁ with hb₂
  have hb₁Q : quadPlus 5 K b₁ = 0 := by rw [hb₁, hco.quad_sec, hQe₁]
  have hb₂Q : quadPlus 5 K b₂ = 0 := by rw [hb₂, hco.quad_sec, hQf₁]
  have hb₁a : polar (quadPlus 5 K) b₁ a = 0 := hco.perp_sec e₁
  have hb₂a : polar (quadPlus 5 K) b₂ a = 0 := hco.perp_sec f₁
  have hπb₁ : π b₁ = e₁ := hco.proj_sec e₁
  have hπb₂ : π b₂ = f₁ := hco.proj_sec f₁
  have hb₁b₂ : polar (quadPlus 5 K) b₁ b₂ = 1 := by
    rw [← hco.form b₁ b₂ hb₁a hb₂a, hπb₁, hπb₂, hspef]
  have hb₂b₁ : polar (quadPlus 5 K) b₂ b₁ = 1 := by rw [polar_comm]; exact hb₁b₂
  have hb₁0 : b₁ ≠ 0 := by
    intro h
    have := hb₁b₂
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  have hb₂0 : b₂ ≠ 0 := by
    intro h
    have := hb₁b₂
    rw [h, polar_zero_right] at this
    exact zero_ne_one this
  have haa : polar (quadPlus 5 K) a a = 0 := by
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  obtain ⟨A₁, hA₁X, hA₁u⟩ := hW uB b₁ huB0 hb₁0 (hQuB.trans hb₁Q.symm)
  obtain ⟨A₂, hA₂X, hA₂u⟩ := hW uB b₂ huB0 hb₂0 (hQuB.trans hb₂Q.symm)
  obtain ⟨h₁, hh₁⟩ := MonoidHom.mem_range.mp (show A₁ ∈ φ.range by rw [hφ]; exact hA₁X)
  obtain ⟨h₂, hh₂⟩ := MonoidHom.mem_range.mp (show A₂ ∈ φ.range by rw [hφ]; exact hA₂X)
  have hh₁u : (φ h₁ : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ uB = b₁ := by
    rw [hh₁]; exact hA₁u
  have hh₂u : (φ h₂ : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ uB = b₂ := by
    rw [hh₂]; exact hA₂u
  have hL₁img : ((conjSubgroup (h₁ : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      E.LomGL b₁ := by rw [(hpts h₁).2, hh₁u]
  have hL₂img : ((conjSubgroup (h₂ : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      E.LomGL b₂ := by rw [(hpts h₂).2, hh₂u]
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hconjR : ∀ h : ↥(Rt M (LB M Q B) t),
      conjSubgroup (h : G) (LB M Q B) ≤ Rt M (LB M Q B) t := by
    intro h y hy
    have hy' : (h : G)⁻¹ * y * h ∈ Rt M (LB M Q B) t := hLR (mem_conjSubgroup.mp hy)
    have e : y = (h : G) * ((h : G)⁻¹ * y * h) * (h : G)⁻¹ := by group
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem h.2 hy')
      ((Rt M (LB M Q B) t).inv_mem h.2)
  have hL₁R := hconjR h₁
  have hL₂R := hconjR h₂
  have hr₁₂ : (h₂ : G) * (h₁ : G)⁻¹ ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem h₂.2 ((Rt M (LB M Q B) t).inv_mem h₁.2)
  have hpol₁₂ : polar (quadPlus 5 K) uB
      ((φ (h₁⁻¹ * h₂) : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ uB) ≠ 0 := by
    have e : (φ (h₁⁻¹ * h₂) : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ uB =
        (φ h₁⁻¹ : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ b₂ := by
      rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh₂u]
    rw [e, ← hpolR h₁, hh₁u, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, ← map_mul,
      mul_inv_cancel, map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, hb₁b₂]
    exact one_ne_zero
  have hplaneB : HypPlane Q Z B
      (conjSubgroup ((h₁⁻¹ * h₂ : ↥(Rt M (LB M Q B) t)) : G) B) t :=
    ((hpts (h₁⁻¹ * h₂)).1).mpr hpol₁₂
  have hplane : HypPlane Q Z (conjSubgroup (h₁ : G) B)
      (conjSubgroup ((h₂ : G) * (h₁ : G)⁻¹) (conjSubgroup (h₁ : G) B)) t := by
    rw [← conjSubgroup_mul, hypPlane_conj_R hc ht h₁.2 hr₁₂]
    have e : (h₁ : G)⁻¹ * ((h₂ : G) * (h₁ : G)⁻¹) * (h₁ : G) =
        ((h₁⁻¹ * h₂ : ↥(Rt M (LB M Q B) t)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hplaneB
  have hNW : ∀ s ∈ hc.CN t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t :=
    (h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat _ (h₁⁻¹ * h₂).2 hplaneB _ (hc.CN t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl).2
  have hd₁₂ := opp_of_frame h52b hc hs h₁.2 hr₁₂ hplane
  have e₂₁ : (h₂ : G) * (h₁ : G)⁻¹ * (h₁ : G) = (h₂ : G) := by group
  rw [e₂₁] at hd₁₂
  set A₁s := (QB (conjSubgroup (h₁ : G) B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
    Vt M (LB M Q B) B Z t with hA₁s
  set A₂s := (QB (conjSubgroup ((h₂ : G) * (h₁ : G)⁻¹) (conjSubgroup (h₁ : G) B)) ⊓
    Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t with hA₂s
  have hxL : ∀ h : ↥(Rt M (LB M Q B) t),
      polar (quadPlus 5 K) ((φ h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ uB) a = 0 →
      conjSubgroup x (conjSubgroup (h : G) (LB M Q B)) = conjSubgroup (h : G) (LB M Q B) := by
    intro h hpol
    have hBZ := conj_BZ_eq hc ht hψ hxM hxt Fx hFx hFa hBu h.2 hpol
    rw [← conjSubgroup_mul]
    exact hc.conj_LB_eq_of_conj_BZ (M.mul_mem hxM (hRM _ h.2)) (hRM _ h.2) hBZ
  have hxL₁ := hxL h₁ (by rw [hh₁u]; exact hb₁a)
  have hxL₂ := hxL h₂ (by rw [hh₂u]; exact hb₂a)
  have hnormA : ∀ {L A : Subgroup G},
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), (w ∈ A ↔ ∀ l ∈ L, ⁅l, w⁆ ∈ Vt M (LB M Q B) B Z t)) →
      A ≤ Wt Q (Vt M (LB M Q B) B Z t) → conjSubgroup x L = L →
      ∀ c ∈ A, x * c * x⁻¹ ∈ A := by
    intro L A hfA hAW hxL' c hcA
    have hcW := hAW hcA
    refine (hfA _ (hxWn c hcW)).mpr fun l hl => ?_
    have hl' : x⁻¹ * l * x ∈ L := by
      rw [← hxL'] at hl
      exact mem_conjSubgroup.mp hl
    have h1 := (hfA c hcW).mp hcA _ hl'
    have e : ⁅l, x * c * x⁻¹⁆ = x * ⁅x⁻¹ * l * x, c⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hxV _ h1
  have hxA₁ : ∀ c ∈ A₁s, x * c * x⁻¹ ∈ A₁s := hnormA hd₁₂.2.2.2.2.2.2.2.2.1 hd₁₂.2.1 hxL₁
  have hxA₂ : ∀ c ∈ A₂s, x * c * x⁻¹ ∈ A₂s := hnormA hd₁₂.2.2.2.2.2.2.2.2.2 hd₁₂.2.2.2.1 hxL₂
  set R₀ := stabSub φ a with hR₀
  have hR₀R : R₀ ≤ Rt M (LB M Q B) t := stabSub_le φ a
  set f : ↥R₀ →* GL (Fin 5 ⊕ Fin 5) K := φ.comp (Subgroup.inclusion hR₀R) with hf
  have hfiso : ∀ (y : ↥R₀) (w : Fin 5 ⊕ Fin 5 → K),
      quadPlus 5 K ((f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w) = quadPlus 5 K w :=
    fun y w => hisoR _ w
  have hfa : ∀ y : ↥R₀, (f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a := by
    intro y
    obtain ⟨hyR, hya⟩ := mem_stabSub.mp y.2
    exact hya
  set φ' := rhoHom hco f hfiso hfa with hφ'
  have hcommFx : ∀ r : ↥(Rt M (LB M Q B) t),
      (φ r : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a → ∀ w,
      Fx ((φ r : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w) =
        (φ r : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ Fx w := by
    intro r hra w
    have hp := hpolR r w a
    rw [hra] at hp
    rw [hFa, hFa, Matrix.mulVec_add, Matrix.mulVec_smul, hra, hp]
  have hPR₀ : ∀ r ∈ R₀, ∀ p ∈ fixSec Q (Vt M (LB M Q B) B Z t) x,
      r * p * r⁻¹ ∈ fixSec Q (Vt M (LB M Q B) B Z t) x := by
    intro r hr p hp
    obtain ⟨hrR, hra⟩ := mem_stabSub.mp hr
    have hcN := comm_mem_CN hc ht hψ hxM hxt Fx hFx hFFx hrR (hcommFx ⟨r, hrR⟩ hra)
    have hcR : ⁅x, r⁆ ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hcN).1
    refine ⟨hRW r hrR p hp.1, ?_⟩
    have e : ⁅x, r * p * r⁻¹⁆ =
        (⁅x, r⁆ * (r * ⁅x, p⁆ * r⁻¹) * ⁅x, r⁆⁻¹) * ⁅⁅x, r⁆, r * p * r⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hVR _ hcR _ (hVR r hrR _ hp.2))
      (hNW _ hcN _ (hRW r hrR p hp.1))
  have hIR₀ : ∀ r ∈ R₀, ∀ y ∈ Vt M (LB M Q B) B Z t, r * y * r⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun r hr y hy => hVR r (hR₀R hr) y hy
  have hNP : ∀ s ∈ hc.CN t, ∀ y ∈ fixSec Q (Vt M (LB M Q B) B Z t) x,
      ⁅s, y⁆ ∈ Vt M (LB M Q B) B Z t := fun s hs' y hy => hNW s hs' y hy.1
  have hrho : ∀ (y : ↥R₀) (z : Fin 4 ⊕ Fin 4 → K),
      ((φ' y : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ z =
        π ((f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ σ z) :=
    fun y z => rhoHom_mulVec hco f hfiso hfa y z
  have hker' : φ'.ker = (hc.CN t).subgroupOf R₀ := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hy1
      have htriv : ∀ z, π ((f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ σ z) = z := by
        intro z
        rw [← hrho y z, hy1, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      rcases eq_or_transvection_of_trivial hco (hfiso y) (hfa y) htriv with hid | hrefl
      · have hfy : f y = 1 := Units.ext (vanishGeom_matrix_eq_of_mulVec fun w => by
          rw [hid w, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec])
        have hmem : Subgroup.inclusion hR₀R y ∈ φ.ker := hfy
        rw [hker, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      · exact absurd (hmemX (Subgroup.inclusion hR₀R y))
          (transvection_not_mem_statedOmega haQ hrefl)
    · intro hy
      have hmem : Subgroup.inclusion hR₀R y ∈ φ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        exact hy
      have hfy : f y = 1 := hmem
      refine Units.ext (vanishGeom_matrix_eq_of_mulVec fun z => ?_)
      rw [hrho y z, hfy, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, hco.proj_sec,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hLimg : ∀ (h : ↥(Rt M (LB M Q B) t)) (b : Fin 5 ⊕ Fin 5 → K),
      ((conjSubgroup (h : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL b →
      quadPlus 5 K b = 0 → polar (quadPlus 5 K) b a = 0 → b ≠ 0 →
      ((conjSubgroup (h : G) (LB M Q B) ⊓ R₀).subgroupOf R₀).map φ' = LspGL 4 K (π b) := by
    intro h b himg hbQ hba hb0
    ext A
    constructor
    · rintro ⟨y, hy, rfl⟩
      replace hy := Subgroup.mem_subgroupOf.mp hy
      have hyL : Subgroup.inclusion hR₀R y ∈
          (conjSubgroup (h : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t) :=
        Subgroup.mem_subgroupOf.mpr hy.1
      have hmem : f y ∈ E.LomGL b := by
        rw [← himg]
        exact ⟨_, hyL, rfl⟩
      obtain ⟨-, w, hbw, hfw⟩ := (mem_LomGL_iff_eichler E).mp hmem
      have hwa : polar (quadPlus 5 K) w a = 0 := by
        have h1 := hfa y
        rw [hfw, eichler_apply hbQ hbw, polar_comm (quadPlus 5 K) a b, hba, zero_smul, add_zero,
          mul_zero, add_zero, sub_eq_self, smul_eq_zero] at h1
        rw [polar_comm]
        exact h1.resolve_right hb0
      rw [mem_LspGL_iff_siegel]
      refine ⟨rhoHom_mem_statedSp hco f hfiso hfa y, π w, quadPlus 5 K w, ?_, fun z => ?_⟩
      · rw [hco.form b w hba hwa]
        exact hbw
      · rw [hrho, hfw, proj_eichler hco hbQ hbw hba hwa]
    · intro hA
      obtain ⟨hAsp, w', c, hw', hAz⟩ := mem_LspGL_iff_siegel.mp hA
      obtain ⟨w, hbw, hwa, hπw, hQw⟩ := exists_lift hco hba hw' c
      obtain ⟨A', hA'L, hA'app⟩ := exists_LomGL_eichler E hbw
      rw [← himg] at hA'L
      obtain ⟨y, hyL, hyA'⟩ := hA'L
      have hya : (φ y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a := by
        rw [hyA', hA'app, eichler_apply hbQ hbw, polar_comm (quadPlus 5 K) a b, hba, zero_smul,
          add_zero, mul_zero, add_zero, polar_comm (quadPlus 5 K) a w, hwa, zero_smul, sub_zero]
      have hyR₀ : (y : G) ∈ R₀ := mem_stabSub.mpr ⟨y.2, hya⟩
      refine ⟨⟨y, hyR₀⟩, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hyL, hyR₀⟩, ?_⟩
      have hfy : f ⟨y, hyR₀⟩ = A' := hyA'
      refine Units.ext (vanishGeom_matrix_eq_of_mulVec fun z => ?_)
      rw [hrho, hfy, hA'app, proj_eichler hco hbQ hbw hba hwa, hπw, hQw, hAz]
  have hL₁' := hLimg h₁ b₁ hL₁img hb₁Q hb₁a hb₁0
  have hL₂' := hLimg h₂ b₂ hL₂img hb₂Q hb₂a hb₂0
  rw [hπb₁] at hL₁'
  rw [hπb₂] at hL₂'
  have hrange : φ'.range = StatedSp 4 K := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact rhoHom_mem_statedSp hco f hfiso hfa y
    · rw [← LspGL_sup_eq (by rw [hspef]; exact one_ne_zero : spForm 4 K e₁ f₁ ≠ 0), ← hL₁', ← hL₂']
      exact sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  have hnonA2 : ∀ (h : ↥(Rt M (LB M Q B) t)) (b b' : Fin 5 ⊕ Fin 5 → K),
      ((conjSubgroup (h : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL b →
      quadPlus 5 K b = 0 → quadPlus 5 K b' = 0 → polar (quadPlus 5 K) b a = 0 →
      polar (quadPlus 5 K) b' b = 1 →
      ∃ y : ↥(Rt M (LB M Q B) t), (y : G) ∈ conjSubgroup (h : G) (LB M Q B) ⊓ R₀ ∧
        ∃ w : Fin 5 ⊕ Fin 5 → K,
          polar (quadPlus 5 K) w ((φ y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ w) ≠ 0 := by
    intro h b b' himg hbQ hb'Q hba hb'b
    obtain ⟨A', hA'L, hA'app⟩ := exists_LomGL_eichler E hba
    rw [← himg] at hA'L
    obtain ⟨y, hyL, hyA'⟩ := hA'L
    have hya : (φ y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a := by
      rw [hyA', hA'app, eichler_apply hbQ hba, polar_comm (quadPlus 5 K) a b, hba, zero_smul,
        add_zero, mul_zero, add_zero, haa, zero_smul, sub_zero]
    refine ⟨y, ⟨Subgroup.mem_subgroupOf.mp hyL, mem_stabSub.mpr ⟨y.2, hya⟩⟩, b', ?_⟩
    rw [hyA', hA'app, polar_apply_eichler_self hbQ hba, hb'Q, haQ, hb'b]
    norm_num
  obtain ⟨y₁, hy₁, w₁, hw₁⟩ := hnonA2 h₁ b₁ b₂ hL₁img hb₁Q hb₂Q hb₁a hb₂b₁
  obtain ⟨y₂, hy₂, w₂, hw₂⟩ := hnonA2 h₂ b₂ b₁ hL₂img hb₂Q hb₁Q hb₂a hb₁b₂
  have hfix₁ : ∀ y ∈ fixSec Q (Vt M (LB M Q B) B Z t) x,
      (∀ l ∈ conjSubgroup (h₁ : G) (LB M Q B) ⊓ R₀, ⁅l, y⁆ ∈ Vt M (LB M Q B) B Z t) →
      y ∈ A₁s := fun y hy hall =>
    mem_of_comm_nonA2 E hQnd h4 φ hφ hker hRW hVR hNW (isOppDecomp_symm hd₁₂) hL₂R hL₁R hb₂Q
      hb₁Q (by rw [hb₂b₁]; exact one_ne_zero) hL₂img hL₁img hy₁.1 ⟨w₁, hw₁⟩ hy.1 (hall _ hy₁)
  have hfix₂ : ∀ y ∈ fixSec Q (Vt M (LB M Q B) B Z t) x,
      (∀ l ∈ conjSubgroup (h₂ : G) (LB M Q B) ⊓ R₀, ⁅l, y⁆ ∈ Vt M (LB M Q B) B Z t) →
      y ∈ A₂s := fun y hy hall =>
    mem_of_comm_nonA2 E hQnd h4 φ hφ hker hRW hVR hNW hd₁₂ hL₁R hL₂R hb₁Q hb₂Q
      (by rw [hb₁b₂]; exact one_ne_zero) hL₁img hL₂img hy₂.1 ⟨w₂, hw₂⟩ hy.1 (hall _ hy₂)
  have hdP := isOppDecomp_fixSec hd₁₂ hxV hxA₁ hxA₂ inf_le_left inf_le_left hfix₁ hfix₂
  obtain ⟨k, hk⟩ := stroth_2_1_ii_secSp (m := 4) (by norm_num) φ' hrange hker' hPR₀ hIR₀ hNP hdP
    inf_le_right inf_le_right (by rw [hspef]; exact one_ne_zero) hL₁' hL₂'
  rw [hK] at hk
  have hcW := card_Wt h34 hc hs hom' hn
  obtain ⟨⟨a', ha'W, ha'P⟩, ⟨y', hy'P, hy'V⟩⟩ :=
    pair_facts hPair h52b h34 hc hs hno hom' hn hx hxt ⟨v, hv, hvZ⟩
  have hPW : fixSec Q (Vt M (LB M Q B) B Z t) x ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    fixSec_le_Wt _ _ _
  have hVP : Vt M (LB M Q B) B Z t ≤ fixSec Q (Vt M (LB M Q B) B Z t) x :=
    hdP.1.trans inf_le_right
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, mul_zero, pow_zero, mul_one] at hk
    have hPV : Vt M (LB M Q B) B Z t = fixSec Q (Vt M (LB M Q B) B Z t) x :=
      Subgroup.eq_of_le_of_card_ge hVP (le_of_eq hk)
    exact hy'V (hPV ▸ hy'P)
  · have hle : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) ≤
        Nat.card ↥(fixSec Q (Vt M (LB M Q B) B Z t) x) := by
      rw [hcW, hk]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Nat.card_pos (by omega))
    have hPW' := Subgroup.eq_of_le_of_card_ge hPW hle
    have ha'P' : a' ∈ fixSec Q (Vt M (LB M Q B) B Z t) x := hPW' ▸ ha'W
    exact ha'P ha'P'.2

end CFSG.RankThree.GF2n.Stroth80
