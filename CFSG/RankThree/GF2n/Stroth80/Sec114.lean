module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar
public import CFSG.RankThree.GF2n.Stroth80.Sec114Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec111Order
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.normal_inf_bar_H0 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    (Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z)).Normal := by
  have hH := hc.normal_bar_H0
  have hXn := hc.Xbar_normal
  refine ⟨fun n hn g => ⟨?_, hH.conj_mem n hn.2 g⟩⟩
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hx' : g⁻¹ * x * g ∈ Xbar M Q Z B := by
    have := hXn.conj_mem x hx g⁻¹
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hn.1 (g⁻¹ * x * g) hx'
  calc x * (g * n * g⁻¹) = g * ((g⁻¹ * x * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = g * n * g⁻¹ * x := by group

theorem liftF_one [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφ : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) : liftF φ (1 : Mbar M Q) = 1 := by
  have h1 := liftF_mkH hφ (1 : ↥(H0 M Z))
  rw [map_one, map_one] at h1
  exact h1

theorem liftF_mul_inv [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφ : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {c : Mbar M Q}
    (hc : c ∈ bar M Q (H0 M Z)) : liftF φ c * liftF φ c⁻¹ = 1 := by
  rw [← liftF_mul hφ (mem_bar_H0_iff.mp hc) (mem_bar_H0_iff.mp ((bar M Q (H0 M Z)).inv_mem hc)),
    mul_inv_cancel, liftF_one hφ]

theorem stroth_11_4_of_line [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a)
    (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
      ∃ f : ↥(Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z)) →*
        GL (Fin 2) K, Function.Injective f := by
  classical
  obtain ⟨q, γ, M₀, hZq, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hBline, hcent, -⟩ := hc.dictB h
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  refine ⟨GaloisField 2 q, inferInstance, inferInstance, h.card, ?_⟩
  set X₁ : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ⊓
    bar M Q (H0 M Z) with hX₁
  have haH : a ∈ H0 M Z := hc.LB_le_H0 ha
  have haM : a ∈ M := haH.1
  set tb : Mbar M Q := QuotientGroup.mk (⟨a, haM⟩ : ↥M) with htb
  have htbH : tb ∈ bar M Q (H0 M Z) := mem_bar_H0_iff.mpr ⟨⟨a, haH⟩, rfl⟩
  have htbX : tb ∈ Xbar M Q Z B := Subgroup.subset_closure (hc.mk_mem_Ebar ha hA)
  have htbL : tb ∈ bar M Q (LB M Q B) :=
    Subgroup.mem_map.mpr ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hQn : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haM) x).mp hx
  have hQn' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem haM)) x).mp hx
    simpa using this
  have hTπ : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = φ ⟨a, haH⟩ (M₀.π x) := fun x hx =>
    hφπ ⟨a, haH⟩ x hx
  have hKcard : 1 < Nat.card (GaloisField 2 q) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  obtain ⟨-, -, hW2, -⟩ :=
    (isA2_iff M₀ h.reg h.card hKcard (φ ⟨a, haH⟩) hQn hQn' hTπ).mp hA
  set Ta : M₀.E ≃ₗ[GaloisField 2 q] M₀.E := φ ⟨a, haH⟩ with hTa
  set W : Submodule (GaloisField 2 q) M₀.E :=
    LinearMap.range ((Ta : M₀.E →ₗ[GaloisField 2 q] M₀.E) - 1) with hWdef
  have hBW : ∀ u ∈ B, M₀.π u ∈ W := by
    intro u hu
    have hcomQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hyM : a ^ k ∈ M := M.zpow_mem haM k
      have e : ⁅x, a ^ k⁆ = x * ((a ^ k) * x⁻¹ * (a ^ k)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Q.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) x⁻¹).mp
        (Q.inv_mem hx))
    have h2 := stroth_sup_le_lift h hcomQ (hline hu)
    exact (Tim79.QuadModel.mem_img_commutator_zpowers Ta hQn hQn' hTπ).mp h2.2
  let ρ : ↥X₁ →* (M₀.E ≃ₗ[GaloisField 2 q] M₀.E) :=
    { toFun := fun y => liftF φ (y : Mbar M Q)
      map_one' := liftF_one hφker
      map_mul' := fun y y' => liftF_mul hφker (mem_bar_H0_iff.mp (Subgroup.mem_inf.mp y.2).2)
        (mem_bar_H0_iff.mp (Subgroup.mem_inf.mp y'.2).2) }
  have htbF : liftF φ tb = Ta := liftF_mkH hφker ⟨a, haH⟩
  have hstab : ∀ c : Mbar M Q, c ∈ bar M Q (H0 M Z) → c * tb = tb * c →
      ∀ w ∈ W, liftF φ c w ∈ W := by
    intro c hcH hct w hw
    obtain ⟨v, rfl⟩ := hw
    have e1 := liftF_mul hφker (mem_bar_H0_iff.mp hcH) (mem_bar_H0_iff.mp htbH)
    have e2 := liftF_mul hφker (mem_bar_H0_iff.mp htbH) (mem_bar_H0_iff.mp hcH)
    rw [hct, e2, htbF] at e1
    refine ⟨liftF φ c v, ?_⟩
    have e3 := congrArg (fun f : M₀.E ≃ₗ[GaloisField 2 q] M₀.E => f v) e1
    simp only [LinearEquiv.mul_apply] at e3
    simp [LinearMap.sub_apply, e3]
  have hstabX : ∀ y : ↥X₁, ∀ w ∈ W, ρ y w ∈ W := fun y w hw =>
    hstab (y : Mbar M Q) (Subgroup.mem_inf.mp y.2).2
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).1 tb htbX).symm w hw
  obtain ⟨f, hf⟩ := exists_hom_GL_two_of_stable ρ W hW2 hstabX
  refine ⟨f, (injective_iff_map_eq_one f).mpr fun y hy => ?_⟩
  set N : Subgroup ↥X₁ := f.ker with hN
  set Kb : Subgroup (Mbar M Q) := N.map X₁.subtype with hKb
  have hKbX : Kb ≤ X₁ := Subgroup.map_subtype_le N
  have hX₁N : X₁.Normal := hc.normal_inf_bar_H0
  have hXK : X₁ ≤ Subgroup.normalizer (Kb : Set (Mbar M Q)) := by
    have hsub : Kb.subgroupOf X₁ = N :=
      Subgroup.comap_map_eq_self_of_injective X₁.subtype_injective N
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKbX, hsub]
    exact f.normal_ker
  have hΓ : CFSG.pCore 2 (Mbar M Q) = ⊥ := hc.pCore_two_Mbar
  have hKb_mem : ∀ z ∈ Kb, z ∈ X₁ ∧ ∀ w ∈ W, liftF φ z w = w := by
    intro z hz
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨y'.2, (hf y').mp (MonoidHom.mem_ker.mp hy')⟩
  have hKb_of : ∀ z ∈ X₁, (∀ w ∈ W, liftF φ z w = w) → z ∈ Kb := by
    intro z hz hfix
    exact Subgroup.mem_map.mpr ⟨⟨z, hz⟩, MonoidHom.mem_ker.mpr ((hf ⟨z, hz⟩).mpr hfix), rfl⟩
  have hlift : ∀ z ∈ Kb, ∃ g : ↥(H0 M Z), mkH M Q Z g = z ∧ ∀ w ∈ W, φ g w = w := by
    intro z hz
    obtain ⟨hzX, hzfix⟩ := hKb_mem z hz
    obtain ⟨g, hg⟩ := mem_bar_H0_iff.mp (Subgroup.mem_inf.mp hzX).2
    refine ⟨g, hg, fun w hw => ?_⟩
    have := hzfix w hw
    rwa [← hg, liftF_mkH hφker] at this
  have hBcomm : ∀ g : ↥(H0 M Z), (∀ w ∈ W, φ g w = w) → ∀ u ∈ B, ⁅(g : G), u⁆ ∈ Z := by
    intro g hg u hu
    have huQ : u ∈ Q := hc.le hu
    have hgu : (g : G) * u * (g : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 g.2.1) u).mp huQ
    refine (M₀.comm_mem_iff huQ hgu).mpr ?_
    rw [hφπ g u huQ]
    exact hg _ (hBW u hu)
  have hnormLB : ∀ g : ↥(H0 M Z), (∀ w ∈ W, φ g w = w) →
      ∀ t ∈ LB M Q B, (g : G) * t * (g : G)⁻¹ ∈ LB M Q B := by
    intro g hg t ht
    have hB' := hBcomm g hg
    have hgBZ : (g : G) ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hle : (B ⊔ Z : Subgroup G) ≤
          (B ⊔ Z : Subgroup G).comap (MulAut.conj (g : G)).toMonoidHom := by
        refine sup_le (fun u hu => ?_) (fun z hz => ?_)
        · show (MulAut.conj (g : G)) u ∈ (B ⊔ Z : Subgroup G)
          rw [MulAut.conj_apply]
          have e : (g : G) * u * (g : G)⁻¹ = ⁅(g : G), u⁆ * u := by
            rw [commutatorElement_def]
            group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hB' u hu)) (Subgroup.mem_sup_left hu)
        · show (MulAut.conj (g : G)) z ∈ (B ⊔ Z : Subgroup G)
          rw [MulAut.conj_apply]
          have e : (g : G) * z * (g : G)⁻¹ = z := by
            have := Subgroup.mem_centralizer_iff.mp g.2.2 z hz
            rw [mul_inv_eq_iff_eq_mul]
            exact this.symm
          rw [e]
          exact Subgroup.mem_sup_right hz
      exact hle hx
    exact (Subgroup.mem_normalizer_iff.mp ((stroth_11_1a hc hw hn g.2.1).mp hgBZ) t).mp ht
  have hnormL : ∀ z ∈ Kb, ∀ l ∈ bar M Q (LB M Q B), z * l * z⁻¹ ∈ bar M Q (LB M Q B) := by
    intro z hz l hl
    obtain ⟨g, rfl, hgfix⟩ := hlift z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hl
    have hx' : (x : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨(g : G), g.2.1⟩ * x * ⟨(g : G), g.2.1⟩⁻¹,
      Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · simpa using hnormLB g hgfix _ hx'
    · rw [map_mul, map_mul, map_inv]
      rfl
  have hlH : ∀ l ∈ bar M Q (LB M Q B), l ∈ bar M Q (H0 M Z) := fun l hl => by
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hl
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr
      (hc.LB_le_H0 (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
  have hLcomm : ∀ l ∈ bar M Q (LB M Q B), l * tb = tb * l := fun l hl =>
    congrArg Subtype.val (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨l, hl⟩ ⟨tb, htbL⟩)
  have hnormK : ∀ l ∈ bar M Q (LB M Q B), ∀ z ∈ Kb, l * z * l⁻¹ ∈ Kb := by
    intro l hl z hz
    obtain ⟨hzX, hzfix⟩ := hKb_mem z hz
    refine hKb_of _ (hX₁N.conj_mem z hzX l) fun w hw => ?_
    have hl' : l⁻¹ ∈ bar M Q (LB M Q B) := (bar M Q (LB M Q B)).inv_mem hl
    have hlH1 : l ∈ bar M Q (H0 M Z) := hlH l hl
    have hlH2 : l⁻¹ ∈ bar M Q (H0 M Z) := hlH l⁻¹ hl'
    have hzH : z ∈ bar M Q (H0 M Z) := (Subgroup.mem_inf.mp hzX).2
    have e1 : liftF φ (l * z * l⁻¹) = liftF φ l * liftF φ z * liftF φ l⁻¹ := by
      rw [liftF_mul hφker (mem_bar_H0_iff.mp ((bar M Q (H0 M Z)).mul_mem hlH1 hzH))
          (mem_bar_H0_iff.mp hlH2),
        liftF_mul hφker (mem_bar_H0_iff.mp hlH1) (mem_bar_H0_iff.mp hzH)]
    have hw' : liftF φ l⁻¹ w ∈ W := hstab l⁻¹ hlH2 (hLcomm l⁻¹ hl') w hw
    have e2 := liftF_mul_inv hφker hlH1
    rw [e1]
    show liftF φ l (liftF φ z (liftF φ l⁻¹ w)) = w
    rw [hzfix _ hw']
    have e3 := congrArg (fun f : M₀.E ≃ₗ[GaloisField 2 q] M₀.E => f w) e2
    simpa using e3
  have hL2 : IsPGroup 2 ↥(bar M Q (LB M Q B)) := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hc.isElemAbelian_bar_LB.2 x x.2⟩
  haveI : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hLK : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Kb : Set (Mbar M Q)) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun z hz => hnormK l hl z hz
  have hKL : Kb ≤ Subgroup.normalizer
      ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) :=
    fun z hz => Subgroup.mem_normalizer_fintype fun l hl => hnormL z hz l hl
  have hcommKL := commute_of_pCore_trivial hKbX hXK hX₁N hΓ hL2 hLK hKL
  have hKb2 : IsPGroup 2 ↥Kb := by
    intro z
    obtain ⟨g, hgz, hgfix⟩ := hlift z.1 z.2
    have hL : ∀ t ∈ LB M Q B, ⁅(g : G), t⁆ ∈ Q := by
      intro t ht
      have htM : t ∈ M := hc.LB_le_M ht
      have hmem : (QuotientGroup.mk' (Q.subgroupOf M) (⟨t, htM⟩ : ↥M)) ∈ bar M Q (LB M Q B) :=
        Subgroup.mem_map.mpr ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      have h1 := hcommKL z.1 z.2 _ hmem
      rw [← hgz] at h1
      exact (mk_commute_iff ⟨(g : G), g.2.1⟩ ⟨t, htM⟩).mp h1
    obtain ⟨k, hk⟩ := stroth_11_1b_ii hc hw g.2 hL (hBcomm g hgfix)
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : mkH M Q Z (g ^ 2 ^ k) = 1 :=
      (mkH_eq_one_iff (g ^ 2 ^ k)).mpr (by simpa [Subgroup.coe_pow] using hk)
    rw [map_pow, hgz] at h1
    simpa using h1
  have hKbot : Kb = ⊥ := eq_bot_of_isPGroup_of_subnormal hKbX hXK hX₁N hΓ hKb2
  have hyKb : (y : Mbar M Q) ∈ Kb := Subgroup.mem_map.mpr ⟨y, MonoidHom.mem_ker.mpr hy, rfl⟩
  rw [hKbot, Subgroup.mem_bot] at hyKb
  exact Subtype.ext hyKb

theorem stroth114_of_line (hline : StrothA2LineStatement) : Stroth114Statement := by
  intro G _ _ M Q Z B _ hc n hw hn ⟨a, ha, hA⟩
  exact stroth_11_4_of_line hc hw hn ha hA (hline G M Q Z B hc n hw hn a ha hA)

end CFSG.RankThree.GF2n.Stroth80
