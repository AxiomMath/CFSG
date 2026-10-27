module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93Rt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93Fix
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93Loc
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Cent
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreL
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreW
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91QB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

section Vec

variable {V : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  [(Z.subgroupOf V).Normal]

@[expose] def vecPre91 (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    (S : Submodule K (ι → K)) : Subgroup G where
  carrier := {x | ∃ h : x ∈ V, secVec ψ ⟨x, h⟩ ∈ S}
  mul_mem' := by
    rintro a b ⟨ha, haS⟩ ⟨hb, hbS⟩
    refine ⟨V.mul_mem ha hb, ?_⟩
    have h := secVec_mul ψ ⟨a, ha⟩ ⟨b, hb⟩
    have h' : secVec ψ ⟨a * b, V.mul_mem ha hb⟩ = secVec ψ ⟨a, ha⟩ + secVec ψ ⟨b, hb⟩ := h
    rw [h']
    exact S.add_mem haS hbS
  one_mem' := by
    refine ⟨V.one_mem, ?_⟩
    have h : secVec ψ ⟨1, V.one_mem⟩ = 0 := (secVec_eq_zero_iff ψ ⟨1, V.one_mem⟩).mpr Z.one_mem
    rw [h]
    exact S.zero_mem
  inv_mem' := by
    rintro a ⟨ha, haS⟩
    refine ⟨V.inv_mem ha, ?_⟩
    have h := secVec_inv ψ ⟨a, ha⟩
    have h' : secVec ψ ⟨a⁻¹, V.inv_mem ha⟩ = -secVec ψ ⟨a, ha⟩ := h
    rw [h']
    exact S.neg_mem haS

end Vec

section Perp

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K]
  {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (Fin 2 ⊕ Fin 2 → K)}
  {u : Fin 2 ⊕ Fin 2 → K}

theorem perp_mem_QB91 (P : Pts91 hc t E φ ψ u) {y : ↥(Vt M (LB M Q B) B Z t)}
    (h : polar (quadPlus 2 K) u (secVec ψ y) = 0) : (y : G) ∈ QB B := by
  obtain ⟨w, hw, hwv⟩ := (P.perp (secVec ψ y)).mpr h
  exact mem_of_secVec_eq hc.Z_le_QB.1 ψ hw.2 hwv

theorem perp_mem_QB_conj91 (ht : t ∈ LB M Q B) (P : Pts91 hc t E φ ψ u)
    (r : ↥(Rt M (LB M Q B) t)) (hrX : (φ r : GL (Fin 2 ⊕ Fin 2) K) ∈
      StatedOmega (StatedQuadPlus 2 K)) {y : ↥(Vt M (LB M Q B) B Z t)}
    (h : polar (quadPlus 2 K) ((φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u)
      (secVec ψ y) = 0) : (y : G) ∈ QB (conjSubgroup (r : G) B) := by
  have hVn := hc.Rt_normalizes_Vt ht
  have hr1 : (r : G)⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem r.2
  have hy'V : (r : G)⁻¹ * (y : G) * (r : G) ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp (hVn hr1) (y : G)).mp y.2
    simpa using this
  let y' : ↥(Vt M (LB M Q B) B Z t) := ⟨(r : G)⁻¹ * (y : G) * (r : G), hy'V⟩
  have hyy : (y : G) = (r : G) * (y' : G) * (r : G)⁻¹ := by
    show (y : G) = (r : G) * ((r : G)⁻¹ * (y : G) * (r : G)) * (r : G)⁻¹
    group
  have hvec : secVec ψ y =
      (φ r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ y' := P.act r y' y hyy
  have hp : polar (quadPlus 2 K) u (secVec ψ y') = 0 := by
    have := E.polar_mulVec hrX u (secVec ψ y')
    rw [← hvec] at this
    rw [← this]
    exact h
  have hy'B : (y' : G) ∈ QB B := perp_mem_QB91 P hp
  have hrB : (r : G) * (y' : G) * (r : G)⁻¹ ∈ conjSubgroup (r : G) (QB B) :=
    mem_conjSubgroup.mpr (by
      have e : (r : G)⁻¹ * ((r : G) * (y' : G) * (r : G)⁻¹) * (r : G) = (y' : G) := by group
      rw [e]
      exact hy'B)
  rw [hyy, QB_conj]
  exact hrB

end Perp

theorem false_of_nonsingular91 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hsc : StronglyClosedMod M Z0 (LB M Q B))
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : ElemMatrixIso (quadPlus 2 K) (StatedOmega (StatedQuadPlus 2 K))}
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K} (P : Pts91 hc t E φ ψ u)
    {nn : ℕ} {γ : G → GaloisField 2 nn} {M₀ : Tim79.QuadModel Q Z (GaloisField 2 nn) γ}
    (hglob : GlobalModelData M Q Z γ M₀) (θ : GaloisField 2 nn ≃+* K)
    (hθ : ∀ (c : GaloisField 2 nn) (v w : ↥(Vt M (LB M Q B) B Z t)),
      M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v)
    {m : G} (hm : m ∈ M) (hDV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t)
    {d₀ : Fin 2 ⊕ Fin 2 → K}
    (hDiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ conjSubgroup m B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • d₀)
    (hperp₁ : polar (quadPlus 2 K) u d₀ = 0)
    (hperp₂ : polar (quadPlus 2 K)
      ((φ ⟨r, hr.mem⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) d₀ = 0)
    (hns : quadPlus 2 K d₀ ≠ 0) : False := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  let r' : ↥(Rt M (LB M Q B) t) := ⟨r, hrR⟩
  have hne := (hypPlane_iff_polar91 h34 hs P r').mp hr.plane
  set u' : Fin 2 ⊕ Fin 2 → K :=
    (φ r' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u with hu'def
  have hrX : (φ r' : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadPlus 2 K) :=
    P.range ▸ MonoidHom.mem_range.mpr ⟨r', rfl⟩
  have hu : quadPlus 2 K u = 0 := P.sing
  have hu' : quadPlus 2 K u' = 0 := by
    rw [hu'def, E.quad_mulVec hrX]
    exact hu
  have hD : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hcA : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVn := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hDB : conjSubgroup m B ≤ QB B := by
    intro y hy
    obtain ⟨c, hcc⟩ := (hDiff (secVec ψ ⟨y, hDV hy⟩)).mp ⟨⟨y, hDV hy⟩, hy, rfl⟩
    refine perp_mem_QB91 P (y := ⟨y, hDV hy⟩) ?_
    rw [hcc, polar_smul_right_eq, hperp₁, mul_zero]
  have hDA : conjSubgroup m B ≤ QB (conjSubgroup r B) := by
    intro y hy
    obtain ⟨c, hcc⟩ := (hDiff (secVec ψ ⟨y, hDV hy⟩)).mp ⟨⟨y, hDV hy⟩, hy, rfl⟩
    refine perp_mem_QB_conj91 ht P r' hrX (y := ⟨y, hDV hy⟩) ?_
    rw [hcc, polar_smul_right_eq, hperp₂, mul_zero]
  obtain ⟨b₀, hb₀B, hb₀⟩ := (P.point u).mpr ⟨1, (one_smul K u).symm⟩
  have ha₀V : r * (b₀ : G) * r⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hVn hrR) (b₀ : G)).mp b₀.2
  let a₀V : ↥(Vt M (LB M Q B) B Z t) := ⟨r * (b₀ : G) * r⁻¹, ha₀V⟩
  have ha₀vec : secVec ψ a₀V = u' := by
    have h1 : secVec ψ a₀V = (φ r' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ b₀ :=
      P.act r' b₀ a₀V rfl
    rw [h1, hb₀]
  have ha₀A : r * (b₀ : G) * r⁻¹ ∈ conjSubgroup r B :=
    mem_conjSubgroup.mpr (by
      have e : r⁻¹ * (r * (b₀ : G) * r⁻¹) * r = (b₀ : G) := by group
      rw [e]
      exact hb₀B)
  have hBD : B ≠ conjSubgroup m B := by
    intro hBD
    obtain ⟨c, hcc⟩ := (hDiff u).mp ⟨b₀, hBD ▸ hb₀B, hb₀⟩
    have h0 : quadPlus 2 K u = c ^ 2 * quadPlus 2 K d₀ := by rw [hcc, map_smul_eq_sq]
    rw [hu] at h0
    have hc0 : c = 0 := by
      by_contra hc0
      exact mul_ne_zero (pow_ne_zero 2 hc0) hns h0.symm
    exact P.ne_zero (by rw [hcc, hc0, zero_smul])
  have hAD : conjSubgroup r B ≠ conjSubgroup m B := by
    intro hAD
    obtain ⟨c, hcc⟩ := (hDiff u').mp ⟨a₀V, hAD ▸ ha₀A, ha₀vec⟩
    have h0 : quadPlus 2 K u' = c ^ 2 * quadPlus 2 K d₀ := by rw [hcc, map_smul_eq_sq]
    rw [hu'] at h0
    have hc0 : c = 0 := by
      by_contra hc0
      exact mul_ne_zero (pow_ne_zero 2 hc0) hns h0.symm
    apply hne
    rw [hcc, hc0, zero_smul, polar_zero_right]
  have hBDq : B ≤ QB (conjSubgroup m B) :=
    (hc.hyp.le_QB_iff_le_QB hc.conj hD.conj hBD).mpr hDB
  have hADq : conjSubgroup r B ≤ QB (conjSubgroup m B) :=
    (hc.hyp.le_QB_iff_le_QB hcA.conj hD.conj hAD).mpr hDA
  have hind : r * (b₀ : G) * r⁻¹ ∉ B ⊔ conjSubgroup m B ⊔ Z := by
    intro hmem
    have hle : B ⊔ conjSubgroup m B ⊔ Z ≤ vecPre91 ψ (Submodule.span K {u, d₀}) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        refine ⟨hBV hx, ?_⟩
        obtain ⟨c, hcc⟩ := (P.point _).mp ⟨⟨x, hBV hx⟩, hx, rfl⟩
        rw [hcc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · intro x hx
        refine ⟨hDV hx, ?_⟩
        obtain ⟨c, hcc⟩ := (hDiff _).mp ⟨⟨x, hDV hx⟩, hx, rfl⟩
        rw [hcc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · intro x hx
        refine ⟨hZV hx, ?_⟩
        rw [(secVec_eq_zero_iff ψ _).mpr hx]
        exact Submodule.zero_mem _
    obtain ⟨h1, hv⟩ := hle hmem
    have hv' : secVec ψ ⟨r * (b₀ : G) * r⁻¹, h1⟩ = u' := ha₀vec
    rw [hv'] at hv
    obtain ⟨α, κ, hακ⟩ := Submodule.mem_span_pair.mp hv
    apply hne
    rw [← hακ, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_eq_zero hu, hperp₁]
    ring
  obtain ⟨l, hl, hlB, c₁, hc₁D, hc₁Z, hc₁eq⟩ := exists_elation91 h34 hD hc hcA hs5.width hs5.n_gt
    (hc.noA2_conj hs5.noA2 hm) (hs5.gen.conj_of_mem hm) hBDq hADq ha₀A hind
  have hlM : l ∈ M := hD.LB_le_M hl
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z := fun y hy =>
    exists_mul_of_mem_sup (fun b hb z hz => by
      have := hc.conj_Z_of_mem_Q (hc.le hb) hz
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [this]) hy
  have hlN : l ∈ Subgroup.normalizer (LB M Q B : Set G) := by
    refine (hc.mem_normalizer_LB_iff h35 hlM).mpr ?_
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨b, hb, z, hz, rfl⟩ := hBZ x hx
    have e : l * (b * z) * l⁻¹ = (⁅l, b⁆ * b) * (l * z * l⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine (B ⊔ Z).mul_mem ((B ⊔ Z).mul_mem (Subgroup.mem_sup_right (hlB b hb))
      (Subgroup.mem_sup_left hb)) (Subgroup.mem_sup_right ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hlM) z).mp hz
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨hprod, hcomm, -⟩ := sec9_N51 h34 h311a hNC hs hr
  have heq := isCentrePre_eq_inf91 hs hr hprod hcomm hZ0
  have hZ0L : Z0 ≤ LB M Q B := by rw [heq]; exact inf_le_left
  have hZ0A : Z0 ≤ LB M Q (conjSubgroup r B) := by rw [heq]; exact inf_le_right
  have hlZ0 : l ∈ Subgroup.normalizer (Z0 : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 : l * x * l⁻¹ ∈ LB M Q B := (Subgroup.mem_normalizer_iff.mp hlN x).mp (hZ0L hx)
    exact hsc x hx l hlM h1
  obtain ⟨s₀, hs₀Z, hs₀Q⟩ : ∃ s ∈ Z0, s ∉ Q := by
    by_contra hcon
    push Not at hcon
    have hlow := centre95CardLower_holds91 h34 h311a h311bComm G M Q Z B hc n t hs Z0 hZ0
    have hle : Nat.card Z0 ≤ Nat.card Q := Subgroup.card_le_of_le (fun x hx => hcon x hx)
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    nlinarith
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  have hUs : Ut Q Z s₀ = Vt M (LB M Q B) B Z t := centre_clause91 h34 h91b hs hr hZ0 hs₀Z hs₀Q
  have hs₀'Z : l * s₀ * l⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hlZ0 s₀).mp hs₀Z
  have hs₀'Q : l * s₀ * l⁻¹ ∉ Q := by
    intro h
    apply hs₀Q
    have h2 := conj_mem_Q91 hc (M.inv_mem hlM) h
    have e : l⁻¹ * (l * s₀ * l⁻¹) * l⁻¹⁻¹ = s₀ := by group
    rwa [e] at h2
  have hUs' : Ut Q Z (l * s₀ * l⁻¹) = Vt M (LB M Q B) B Z t :=
    centre_clause91 h34 h91b hs hr hZ0 hs₀'Z hs₀'Q
  have hlV : conjSubgroup l (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
    calc conjSubgroup l (Vt M (LB M Q B) B Z t) = conjSubgroup l (Ut Q Z s₀) := by rw [hUs]
      _ = Ut Q Z (l * s₀ * l⁻¹) :=
          (Ut_conj_of_normalizes (hc.conj_Q_eq hlM) (hc.conj_Z_eq hlM) s₀).symm
      _ = Vt M (LB M Q B) B Z t := hUs'
  have hlVmem : ∀ x ∈ Vt M (LB M Q B) B Z t, l * x * l⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    intro x hx
    have h1 : l * x * l⁻¹ ∈ conjSubgroup l (Vt M (LB M Q B) B Z t) :=
      mem_conjSubgroup.mpr (by
        have e : l⁻¹ * (l * x * l⁻¹) * l = x := by group
        rw [e]
        exact hx)
    rwa [hlV] at h1
  have ha₁V : l * (r * (b₀ : G) * r⁻¹) * l⁻¹ ∈ Vt M (LB M Q B) B Z t := hlVmem _ ha₀V
  let a₁V : ↥(Vt M (LB M Q B) B Z t) := ⟨_, ha₁V⟩
  have hc₁V : c₁ ∈ Vt M (LB M Q B) B Z t := hDV hc₁D
  let c₁V : ↥(Vt M (LB M Q B) B Z t) := ⟨c₁, hc₁V⟩
  obtain ⟨κ, hκ⟩ := (hDiff (secVec ψ c₁V)).mp ⟨c₁V, hc₁D, rfl⟩
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hc₁Z
    exact (secVec_eq_zero_iff ψ c₁V).mp (by rw [hκ, h0, zero_smul])
  have hvec₁ : secVec ψ a₁V = u' + κ • d₀ := by
    have h1 : secVec ψ a₁V = secVec ψ (a₀V * c₁V) := by
      rw [secVec_eq_iff]
      have hQ1 : r * (b₀ : G) * r⁻¹ * c₁ ∈ Q :=
        Q.mul_mem (hVQ ha₀V) (hVQ hc₁V)
      have e : l * (r * (b₀ : G) * r⁻¹) * l⁻¹ * (r * (b₀ : G) * r⁻¹ * c₁)⁻¹ =
          (r * (b₀ : G) * r⁻¹ * c₁) * ((r * (b₀ : G) * r⁻¹ * c₁)⁻¹ *
            (l * (r * (b₀ : G) * r⁻¹) * l⁻¹)) * (r * (b₀ : G) * r⁻¹ * c₁)⁻¹ := by group
      show l * (r * (b₀ : G) * r⁻¹) * l⁻¹ * (r * (b₀ : G) * r⁻¹ * c₁)⁻¹ ∈ Z
      rw [e, hc.conj_Z_of_mem_Q hQ1 hc₁eq]
      exact hc₁eq
    rw [h1, secVec_mul, ha₀vec, hκ]
  have hQa₁ : quadPlus 2 K (u' + κ • d₀) = κ ^ 2 * quadPlus 2 K d₀ := by
    rw [QuadraticMap.map_add (quadPlus 2 K) u' (κ • d₀), map_smul_eq_sq, hu', polar_smul_right_eq,
      hperp₂]
    ring
  have hQa₁ne : quadPlus 2 K (u' + κ • d₀) ≠ 0 := by
    rw [hQa₁]
    exact mul_ne_zero (pow_ne_zero 2 hκ0) hns
  have hlrM : l * r ∈ M := M.mul_mem hlM hrM
  have hcA' : Ctx M Q Z (conjSubgroup (l * r) B) := hc.conj_of_mem hlrM
  have hnoA' := hc.noA2_conj hs5.noA2 hlrM
  have hgenA' := hs5.gen.conj_of_mem hlrM
  have hA'V : conjSubgroup (l * r) B ≤ Vt M (LB M Q B) B Z t := by
    intro x hx
    have hx' : (l * r)⁻¹ * x * (l * r) ∈ B := mem_conjSubgroup.mp hx
    have e : x = l * (r * ((l * r)⁻¹ * x * (l * r)) * r⁻¹) * l⁻¹ := by group
    rw [e]
    exact hlVmem _ ((Subgroup.mem_normalizer_iff.mp (hVn hrR) _).mp (hBV hx'))
  have ha₁A' : l * (r * (b₀ : G) * r⁻¹) * l⁻¹ ∈ conjSubgroup (l * r) B := by
    rw [mem_conjSubgroup]
    have e : (l * r)⁻¹ * (l * (r * (b₀ : G) * r⁻¹) * l⁻¹) * (l * r) = (b₀ : G) := by group
    rw [e]
    exact hb₀B
  have hs₀'A' : l * s₀ * l⁻¹ ∈ conjSubgroup (l * r) (LB M Q B) := by
    rw [mem_conjSubgroup]
    have h1 : s₀ ∈ conjSubgroup r (LB M Q B) := by
      rw [← hc.LB_conj hrM]
      exact hZ0A hs₀Z
    have h2 := mem_conjSubgroup.mp h1
    have e : (l * r)⁻¹ * (l * s₀ * l⁻¹) * (l * r) = r⁻¹ * s₀ * r := by group
    rw [e]
    exact h2
  have hLA'R : LB M Q (conjSubgroup (l * r) B) ≤ Rt M (LB M Q B) t := by
    rw [hc.LB_conj hlrM]
    have h1 := conjSubgroup_le_Rt (M := M) (L := LB M Q B) hlrM hs₀'A'
    rwa [Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 hs₀'Z hs₀'Q] at h1
  let U₀ : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
    ((LB M Q (conjSubgroup (l * r) B)).subgroupOf (Rt M (LB M Q B) t)).map φ
  have hU₀X : U₀ ≤ StatedOmega (StatedQuadPlus 2 K) := by
    rintro _ ⟨x, -, rfl⟩
    rw [← P.range]
    exact ⟨x, rfl⟩
  have hU₀p : IsPGroup 2 U₀ := by
    have hLp : IsPGroup 2 ↥(LB M Q (conjSubgroup (l * r) B)) :=
      hcA'.isPGroup_LB h34 hs5.width hs5.n_gt hnoA' hgenA'
    have h1 : IsPGroup 2
        ↥((LB M Q (conjSubgroup (l * r) B)).subgroupOf (Rt M (LB M Q B) t)) :=
      hLp.of_injective (Subgroup.subgroupOfEquivOfLe hLA'R).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hLA'R).injective
    exact h1.of_surjective (φ.subgroupMap _) (φ.subgroupMap_surjective _)
  have h4 : 4 ≤ Nat.card K := by
    rw [P.card]
    exact hc.hyp.q4
  obtain ⟨p, hp0, hpsing, hpfix⟩ := exists_singular_fixed91 h4 E hu P.ne_zero hU₀X hU₀p
  obtain ⟨w, hwp⟩ := exists_secVec_eq ψ p
  have hwC : (w : G) ∈ CQt Q Z (LB M Q (conjSubgroup (l * r) B)) := by
    refine ⟨hVQ w.2, fun x hx => ?_⟩
    have hxR : x ∈ Rt M (LB M Q B) t := hLA'R hx
    let x' : ↥(Rt M (LB M Q B) t) := ⟨x, hxR⟩
    have hxU : φ x' ∈ U₀ := ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hfix := hpfix _ hxU
    have hxw : x * (w : G) * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVn hxR) (w : G)).mp w.2
    let w' : ↥(Vt M (LB M Q B) B Z t) := ⟨x * (w : G) * x⁻¹, hxw⟩
    have hv : secVec ψ w' =
        (φ x' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ w := P.act x' w w' rfl
    have hv' : secVec ψ w' = secVec ψ w := by rw [hv, hwp, hfix]
    have hz := (secVec_eq_iff ψ w' w).mp hv'
    rw [commutatorElement_def]
    exact hz
  have h35' := (stroth_3_5 h34 hcA' hs5.width hs5.n_gt hnoA' hgenA').2.1
  have hwA : (w : G) ∈ conjSubgroup (l * r) B ⊔ Z := by
    have h := hwC
    rw [h35'] at h
    exact h
  obtain ⟨d'', hd''A, hd''ne, hA'iff⟩ := hcA'.exists_point_of_le hA'V ψ hglob θ hθ
  have hcommA : ∀ a ∈ conjSubgroup (l * r) B, ∀ z ∈ Z, a * z = z * a := fun a ha z hz => by
    have := hcA'.conj_Z_of_mem_Q (hcA'.le ha) hz
    calc a * z = (a * z * a⁻¹) * a := by group
      _ = z * a := by rw [this]
  obtain ⟨a, haA, z, hzZ, hwaz⟩ := exists_mul_of_mem_sup hcommA hwA
  have haV : a ∈ Vt M (LB M Q B) B Z t := hA'V haA
  have hwa : secVec ψ w = secVec ψ ⟨a, haV⟩ := by
    rw [secVec_eq_iff]
    show (w : G) * a⁻¹ ∈ Z
    rw [hwaz]
    have e : a * z * a⁻¹ = z := hcA'.conj_Z_of_mem_Q (hcA'.le haA) hzZ
    rw [e]
    exact hzZ
  obtain ⟨c', hc'⟩ := (hA'iff (secVec ψ ⟨a, haV⟩)).mp ⟨⟨a, haV⟩, haA, rfl⟩
  obtain ⟨c'', hc''⟩ := (hA'iff (secVec ψ a₁V)).mp ⟨a₁V, ha₁A', rfl⟩
  have hQd : quadPlus 2 K (secVec ψ d'') ≠ 0 := by
    intro h0
    apply hQa₁ne
    rw [← hvec₁, hc'', map_smul_eq_sq, h0, mul_zero]
  have hc'0 : c' = 0 := by
    by_contra hne'
    have h1 : quadPlus 2 K p = c' ^ 2 * quadPlus 2 K (secVec ψ d'') := by
      rw [← hwp, hwa, hc', map_smul_eq_sq]
    rw [hpsing] at h1
    exact mul_ne_zero (pow_ne_zero 2 hne') hQd h1.symm
  apply hp0
  rw [← hwp, hwa, hc', hc'0, zero_smul]

end HS9

theorem step93One_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement) :
    Step93OneStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 hsc m hm hmV
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have hq4 : 4 ≤ Nat.card K := by
    rw [P.card]
    exact hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
  have hX := addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv ht P.card hX φ P.range ψ P.act
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  have hD : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hDV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := le_trans le_sup_left hmV
  obtain ⟨d₀', hd₀'D, hd₀'ne, hDiff⟩ := hD.exists_point_of_le hDV ψ hglob θ hθ
  set d₀ : Fin 2 ⊕ Fin 2 → K := secVec ψ d₀' with hd₀def
  have hsing : quadPlus 2 K d₀ = 0 := by
    by_contra hns
    let r' : ↥(Rt M (LB M Q B) t) := ⟨r, hr.mem⟩
    have hne := (HS9.hypPlane_iff_polar91 h34 hs P r').mp hr.plane
    have hrX : (φ r' : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadPlus 2 K) :=
      P.range ▸ MonoidHom.mem_range.mpr ⟨r', rfl⟩
    have hu' : quadPlus 2 K ((φ r' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) = 0 := by
      rw [E.quad_mulVec hrX]
      exact P.sing
    obtain ⟨d', hd'u, hd'u', hd'Q⟩ :=
      HS9.exists_nonsingular_perp_value91 P.sing hu' hne hns
    have hd'0 : d' ≠ 0 := fun h0 => hns (by rw [← hd'Q, h0, QuadraticMap.map_zero])
    obtain ⟨A, hA, hAd⟩ := E.exists_mulVec_eq hQ (P := plusPair K 0) (P' := plusPair K 1)
      (plusPair_orth (by decide)) hd₀'ne hd'0 hd'Q.symm
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(Rt M (LB M Q B) t), φ ρ = A := by
      rw [← P.range] at hA
      exact MonoidHom.mem_range.mp hA
    have hρM : (ρ : G) ∈ M := hc.Rt_le_M t ρ.2
    have hρm : (ρ : G) * m ∈ M := M.mul_mem hρM hm
    have hVn := hc.Rt_normalizes_Vt ht
    have hVρ : ∀ y ∈ Vt M (LB M Q B) B Z t, (ρ : G) * y * (ρ : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp (hVn ρ.2) y).mp hy
    have hVρ' : ∀ y ∈ Vt M (LB M Q B) B Z t,
        (ρ : G)⁻¹ * y * (ρ : G) ∈ Vt M (LB M Q B) B Z t := fun y hy => by
      have := (Subgroup.mem_normalizer_iff.mp (hVn ((Rt M (LB M Q B) t).inv_mem ρ.2)) y).mp hy
      simpa using this
    have hDV' : conjSubgroup ((ρ : G) * m) B ≤ Vt M (LB M Q B) B Z t := by
      intro x hx
      have hx' : ((ρ : G) * m)⁻¹ * x * ((ρ : G) * m) ∈ B := mem_conjSubgroup.mp hx
      have e : x = (ρ : G) * (m * (((ρ : G) * m)⁻¹ * x * ((ρ : G) * m)) * m⁻¹) * (ρ : G)⁻¹ := by
        group
      rw [e]
      refine hVρ _ ?_
      have hmx : m * (((ρ : G) * m)⁻¹ * x * ((ρ : G) * m)) * m⁻¹ ∈ conjSubgroup m B :=
        mem_conjSubgroup.mpr (by
          have e2 : m⁻¹ * (m * (((ρ : G) * m)⁻¹ * x * ((ρ : G) * m)) * m⁻¹) * m =
              ((ρ : G) * m)⁻¹ * x * ((ρ : G) * m) := by group
          rw [e2]
          exact hx')
      exact hDV hmx
    have hDiff' : ∀ x : Fin 2 ⊕ Fin 2 → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ conjSubgroup ((ρ : G) * m) B ∧
          secVec ψ b = x) ↔ ∃ c : K, x = c • d' := by
      intro x
      constructor
      · rintro ⟨b, hb, rfl⟩
        have hb₀V : (ρ : G)⁻¹ * (b : G) * (ρ : G) ∈ Vt M (LB M Q B) B Z t := hVρ' _ b.2
        have hb₀D : (ρ : G)⁻¹ * (b : G) * (ρ : G) ∈ conjSubgroup m B := by
          rw [mem_conjSubgroup]
          have hb' : ((ρ : G) * m)⁻¹ * (b : G) * ((ρ : G) * m) ∈ B := mem_conjSubgroup.mp hb
          have e : m⁻¹ * ((ρ : G)⁻¹ * (b : G) * (ρ : G)) * m =
              ((ρ : G) * m)⁻¹ * (b : G) * ((ρ : G) * m) := by group
          rw [e]
          exact hb'
        obtain ⟨c, hc'⟩ := (hDiff (secVec ψ ⟨_, hb₀V⟩)).mp ⟨⟨_, hb₀V⟩, hb₀D, rfl⟩
        refine ⟨c, ?_⟩
        have hv : secVec ψ b = (φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            secVec ψ ⟨(ρ : G)⁻¹ * (b : G) * (ρ : G), hb₀V⟩ :=
          P.act ρ ⟨_, hb₀V⟩ b (by
            show (b : G) = (ρ : G) * ((ρ : G)⁻¹ * (b : G) * (ρ : G)) * (ρ : G)⁻¹
            group)
        rw [hv, hc', Matrix.mulVec_smul, hρ, hAd]
      · rintro ⟨c, rfl⟩
        obtain ⟨b₀, hb₀D, hb₀⟩ := (hDiff (c • d₀)).mpr ⟨c, rfl⟩
        have hbV : (ρ : G) * (b₀ : G) * (ρ : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := hVρ _ b₀.2
        refine ⟨⟨_, hbV⟩, ?_, ?_⟩
        · rw [mem_conjSubgroup]
          have hb₀D' := mem_conjSubgroup.mp hb₀D
          have e : ((ρ : G) * m)⁻¹ * ((ρ : G) * (b₀ : G) * (ρ : G)⁻¹) * ((ρ : G) * m) =
              m⁻¹ * (b₀ : G) * m := by group
          rw [e]
          exact hb₀D'
        · have hv : secVec ψ ⟨(ρ : G) * (b₀ : G) * (ρ : G)⁻¹, hbV⟩ =
              (φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec ψ b₀ :=
            P.act ρ b₀ ⟨_, hbV⟩ rfl
          rw [hv, hb₀, Matrix.mulVec_smul, hρ, hAd]
    exact HS9.false_of_nonsingular91 h34 h311a h311bComm h312b hs hr hZ0 hsc P hglob θ hθ hρm
      hDV' hDiff' hd'u hd'u' (by rw [hd'Q]; exact hns)
  obtain ⟨A, hA, hAu⟩ := E.exists_mulVec_eq hQ (P := plusPair K 0) (P' := plusPair K 1)
    (plusPair_orth (by decide)) P.ne_zero hd₀'ne (by rw [P.sing, hsing])
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(Rt M (LB M Q B) t), φ ρ = A := by
    rw [← P.range] at hA
    exact MonoidHom.mem_range.mp hA
  exact ⟨ρ, ρ.2, hc.conj_sup_eq_of_mulVec_eq hs5 φ ψ P.act hm hmV P.point hDiff ρ
    (by rw [hρ]; exact hAu)⟩

end CFSG.RankThree.GF2n.Stroth80
