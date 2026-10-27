module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec312bAux
public import CFSG.RankThree.GF2n.Stroth80.Sec312bOpp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Stroth80.Classify
open scoped commutatorElement Matrix Pointwise

namespace S94F

section Model

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem l56u_range_pairing {T : M₀.E ≃ₗ[K] M₀.E} (hTB : ∀ e f, M₀.B (T e) (T f) = M₀.B e f)
    {A : Type*} [AddCommGroup A] (ι : A →+ M₀.E)
    (hι : ∀ u, ι u ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)) :
    ∃ β : A →+ A →+ K,
      (∀ (g : A → A) (S : M₀.E ≃ₗ[K] M₀.E), (∀ e f, M₀.B (S e) (S f) = M₀.B e f) →
        (∀ e, S (T e) = T (S e)) → (∀ u, ι (g u) = S (ι u)) →
          ∀ u u', β (g u) (g u') = β u u') ∧
      ∀ u u' (z : M₀.E), ((T : M₀.E →ₗ[K] M₀.E) - 1) z = ι u' → β u u' = M₀.B (ι u) z := by
  set U := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)
  have hpre : ∀ y : M₀.E, ∃ z : M₀.E, y ∈ U → ((T : M₀.E →ₗ[K] M₀.E) - 1) z = y := by
    intro y
    by_cases hy : y ∈ U
    · obtain ⟨z, hz⟩ := hy
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose s hs using hpre
  have hperp : ∀ x ∈ U, ∀ z w : M₀.E,
      ((T : M₀.E →ₗ[K] M₀.E) - 1) z = ((T : M₀.E →ₗ[K] M₀.E) - 1) w → M₀.B x z = M₀.B x w := by
    intro x hx z w hzw
    have hfix : T (z - w) = z - w := by
      have h0 : ((T : M₀.E →ₗ[K] M₀.E) - 1) (z - w) = 0 := by rw [map_sub, hzw, sub_self]
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
      exact h0
    have h0 := (Tim79.QuadModel.mem_range_sub_one_iff' hTB x).mp hx _ hfix
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  let β : A →+ A →+ K := AddMonoidHom.mk'
    (fun u => AddMonoidHom.mk' (fun u' => M₀.B (ι u) (s (ι u'))) fun a b => by
      rw [← map_add (M₀.B (ι u))]
      refine hperp _ (hι u) _ _ ?_
      rw [hs _ (hι (a + b)), map_add ((T : M₀.E →ₗ[K] M₀.E) - 1), hs _ (hι a), hs _ (hι b),
        map_add ι])
    fun a b => by
      ext u'
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, LinearMap.add_apply]
  have hβ : ∀ u u', β u u' = M₀.B (ι u) (s (ι u')) := fun _ _ => rfl
  refine ⟨β, fun g S hSB hST hg u u' => ?_, fun u u' z hz => ?_⟩
  · rw [hβ, hβ, hg, hg]
    have hSU : S (ι u') ∈ U := by rw [← hg]; exact hι _
    rw [hperp _ (by rw [← hg]; exact hι _) (s (S (ι u'))) (S (s (ι u'))) ?_, hSB]
    rw [hs _ hSU]
    have h0 := hs _ (hι u')
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply] at h0 ⊢
    rw [← hST, ← map_sub, h0]
  · rw [hβ]
    exact hperp _ (hι u) _ _ (by rw [hs _ (hι u'), hz])

end Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem l56u_pi_comm {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {u a : G}
    (ha : a ∈ Q) (hua : u * a * u⁻¹ ∈ Q) (τ : M₀.E ≃ₗ[K] M₀.E)
    (hτ : M₀.π (u * a * u⁻¹) = τ (M₀.π a)) :
    M₀.π ⁅u, a⁆ = τ (M₀.π a) - M₀.π a := by
  rw [commutatorElement_def, M₀.π_mul _ hua _ (Q.inv_mem ha), M₀.pi_inv ha, hτ, sub_eq_add_neg]

theorem l56u_false_of_SLNat (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {u : G}
    (hs : Sec5Hyp hc n u) (hsl : SLNat hc u)
    (hcard : Nat.card Z ^ 3 < Nat.card ↥(Vt M (LB M Q B) B Z u))
    {b a : G} (hb : b ∈ Vt M (LB M Q B) B Z u) (ha : a ∈ Q)
    (hua : ⁅u, a⁆ ∈ Vt M (LB M Q B) B Z u) (hba : ⁅b, a⁆ ≠ 1) : False := by
  classical
  have ht := hs.mem
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hVT := hc.Vt_le_Tt_of_SLNat hs h35 hsl
  obtain ⟨K', _, _, hK', d, -, φ', hrange, -, hRN, hZn, ψ, hψ⟩ := hsl
  set V := Vt M (LB M Q B) B Z u with hVdef
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVQ : V ≤ Q := hc.Vt_le_Q u
  have hcardQ : Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card Z ^ d := by
    rw [Nat.card_congr ψ.toEquiv,
      show Nat.card (Multiplicative (Fin d → K')) = Nat.card (Fin d → K') from rfl,
      Nat.card_fun, Nat.card_fin, hK']
  have hcardZ : Nat.card (Z.subgroupOf V) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
  have hcardV : Nat.card V = Nat.card Z * Nat.card Z ^ d := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V), hcardQ, hcardZ,
      mul_comm]
  have hq1 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have hd3 : 3 ≤ d := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card Z * Nat.card Z ^ d ≤ Nat.card Z ^ 3 := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by omega) (by omega)
    rw [← hcardV] at h1
    exact absurd hcard (not_lt.mpr h1)
  have hVU : V ≤ Ut Q Z u :=
    hVT.trans (sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z)
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, -, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  have htM : u ∈ M := hc.LB_le_M ht
  have htH := hc.LB_le_H0 ht
  obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
  set τ := φ ⟨u, htH⟩
  have hτπ : ∀ x ∈ Q, M₀.π (u * x * u⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨u, htH⟩ x hx
  have hτB : ∀ e f, M₀.B (τ e) (τ f) = M₀.B e f := B_map_eq_of_Qf τ (hφiso _)
  have hU : ∀ x ∈ Q, x ∈ Ut Q Z u ↔
      M₀.π x ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n'] M₀.E) - 1) := fun x hx =>
    (M₀.mem_img_iff (le_sup_right : Z ≤ Ut Q Z u) hx).symm.trans
      (mem_img_comm_zpowers_sup_iff M₀ h.reg τ htQ1 htQ2 hτπ _)
  obtain ⟨ι, hιπ, -⟩ := exists_Vt_transport (M₀ := M₀) hVQ ψ
  have hψs : ∀ w, ∃ v : V, Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = w := fun w => by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd w))
    exact ⟨v, by rw [hv, ψ.apply_symm_apply, toAdd_ofAdd]⟩
  have hι : ∀ w, ι w ∈ LinearMap.range ((τ : M₀.E →ₗ[GaloisField 2 n'] M₀.E) - 1) := by
    intro w
    obtain ⟨v, rfl⟩ := hψs w
    rw [hιπ]
    exact (hU v (hVQ v.2)).mp (hVU v.2)
  obtain ⟨β, hβinv, hβval⟩ := l56u_range_pairing hτB ι hι
  have hinv : ∀ g : GL (Fin d) K', g ∈ StatedSL d K' → ∀ x y : Fin d → K',
      β ((g : Matrix (Fin d) (Fin d) K') *ᵥ x) ((g : Matrix (Fin d) (Fin d) K') *ᵥ y) =
        β x y := by
    intro g hg x y
    rw [← hrange] at hg
    obtain ⟨r, rfl⟩ := hg
    have hrM : (r : G) ∈ M := hc.Rt_le_M u r.2
    have hrH : (r : G) ∈ H0 M Z := hc.Rt_le_H0 u r.2
    refine hβinv (fun w => (φ' r : Matrix (Fin d) (Fin d) K') *ᵥ w) (φ ⟨r, hrH⟩)
      (B_map_eq_of_Qf _ (hφiso _)) (fun e => hc.hyp.comm_action hrM htM
        (hc.Rt_comm_mem_Q r.2) (hφπ ⟨r, hrH⟩) hτπ e) (fun w => ?_) x y
    obtain ⟨v, rfl⟩ := hψs w
    have hw : (r : G) * v * (r : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hRN r.2) v).mp v.2
    rw [← hψ r v ⟨_, hw⟩ rfl, hιπ, hιπ]
    exact hφπ ⟨r, hrH⟩ v (hVQ v.2)
  have h0 := biadd_eq_zero_of_SL hd3 β hinv
  have hval := hβval (Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨b, hb⟩)))
    (Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨⁅u, a⁆, hua⟩))) (M₀.π a) (by
      rw [hιπ]
      show (τ : M₀.E →ₗ[GaloisField 2 n'] M₀.E) (M₀.π a) - M₀.π a = M₀.π ⁅u, a⁆
      rw [l56u_pi_comm ha (htQ1 a ha) τ (hτπ a ha)]
      rfl)
  rw [hιπ, h0] at hval
  apply hba
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (M₀.comm_iff_B h.reg (hVQ hb) ha).mpr hval.symm

theorem l56u_gen_of_opp (h34 : Stroth34Statement) (hX : Classify.TheoremXStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {u : G} (hs : Sec5Hyp hc n u)
    (hR : Rt M (LB M Q B) u ≠ LB M Q B) (hnot : ¬ Vt M (LB M Q B) B Z u ≤ QB B)
    {c d : G} (hcM : c ∈ M) (hdM : d ∈ M) (huc : u ∈ conjSubgroup c (LB M Q B))
    (hud : u ∈ conjSubgroup d (LB M Q B)) {b a : G} (hb : b ∈ conjSubgroup c B) (ha : a ∈ Q)
    (hua : ⁅u, a⁆ ∈ conjSubgroup d B ⊔ Z) (hba : ⁅b, a⁆ ≠ 1) :
    ∀ r ∈ Rt M (LB M Q B) u, ∃ y ∈ conjSubgroup c (LB M Q B) ⊔ conjSubgroup d (LB M Q B),
      y⁻¹ * r ∈ hc.CN u := by
  classical
  have ht := hs.mem
  have hL₁R : conjSubgroup c (LB M Q B) ≤ Rt M (LB M Q B) u := conjSubgroup_le_Rt hcM huc
  have hL₂R : conjSubgroup d (LB M Q B) ≤ Rt M (LB M Q B) u := conjSubgroup_le_Rt hdM hud
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z u) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z u) :=
    fun c _ he => hc.smul_mem_img_Vt h u c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hs hnot h hS
  have hSymp := sympRep_two_of_not_le_QB h34 hc hs hnot
    (stroth310SympForm_of_34 h34 G M Q Z B hc n u hs hR hnot)
  have hKZ : Nat.card (GaloisField 2 n') = Nat.card Z := h.card
  have hq4 : 4 ≤ Nat.card (GaloisField 2 n') := by
    rw [hKZ]
    exact hc.hyp.q4
  have hdim : 4 ≤ Module.finrank (GaloisField 2 n')
      ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) := by
    obtain ⟨K₁, _, _, hK₁, m₁', hm₁', φ₁, -, -, hsec⟩ := hSymp
    have hcardV := card_eq_of_sectionAct
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := u)) hsec
    have hcardM := M₀.card_eq (hc.Vt_le_Q u)
      (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := u))
    have hfin : Nat.card (M₀.img (Vt M (LB M Q B) B Z u)) =
        Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_imgSub.symm)
    have hpow : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) =
        Nat.card (GaloisField 2 n') ^ Module.finrank (GaloisField 2 n')
          ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) :=
      Module.natCard_eq_pow_finrank (K := GaloisField 2 n')
        (V := ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS))
    rw [hcardV, hfin] at hcardM
    have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardM
    simp only [Fintype.card_sum, Fintype.card_fin] at h2
    rw [hK₁, hpow, hKZ] at h2
    have h3 : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    have h4 := Nat.pow_right_injective h3 h2
    omega
  obtain ⟨P, hP0, hPspan, hPful, hPgen⟩ := hc.theoremX_data h34 hs h D hdim
  have hH : D.ρ.range ≤ Classify.sympSubgroup D.F := by
    rintro _ ⟨r, rfl⟩
    exact D.isom r
  have hcases := hX (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) D.F hq4 D.nondeg
    D.alt hdim D.ρ.range hH P hP0 hPspan hPful hPgen
  obtain ⟨e₁, he₁0, heB₁, hepr₁, heful₁⟩ := D.elation_data h34 hs h hdim hcM huc
  obtain ⟨e₂, he₂0, heB₂, hepr₂, heful₂⟩ := D.elation_data h34 hs h hdim hdM hud
  have hVQ : Vt M (LB M Q B) B Z u ≤ Q := hc.Vt_le_Q u
  have hbV : b ∈ Vt M (LB M Q B) B Z u := sec39_conjB_le_Vt hcM huc hb
  have hBdV : conjSubgroup d B ⊔ Z ≤ Vt M (LB M Q B) B Z u :=
    sup_le (sec39_conjB_le_Vt hdM hud) sec39_Z_le_Vt
  have huaV : ⁅u, a⁆ ∈ Vt M (LB M Q B) B Z u := hBdV hua
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  have huM : u ∈ M := hc.LB_le_M ht
  have huH := hc.LB_le_H0 ht
  obtain ⟨huQ1, -⟩ := hc.conj_mem_Q_of_mem_M huM
  set τ := φ ⟨u, huH⟩
  have hτπ : ∀ x ∈ Q, M₀.π (u * x * u⁻¹) = τ (M₀.π x) := fun x hx => hφπ ⟨u, huH⟩ x hx
  let w : ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) :=
    ⟨M₀.π b, mem_imgSub.mpr (M₀.pi_mem_img hbV (hVQ hbV))⟩
  let w' : ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS) :=
    ⟨M₀.π ⁅u, a⁆, mem_imgSub.mpr (M₀.pi_mem_img huaV (hVQ huaV))⟩
  have hFww : D.F w w' = M₀.B (M₀.π b) (M₀.π a) :=
    D.form τ hτπ w w' (M₀.π a) (by
      show τ (M₀.π a) - M₀.π a = M₀.π ⁅u, a⁆
      rw [l56u_pi_comm ha (huQ1 a ha) τ (hτπ a ha)])
  have hBne : M₀.B (M₀.π b) (M₀.π a) ≠ 0 := by
    intro h0
    apply hba
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (M₀.comm_iff_B h.reg (hVQ hbV) ha).mpr h0
  obtain ⟨s₁, hs₁⟩ := (heB₁ (M₀.π b)).mp (M₀.pi_mem_img hb (hVQ hbV))
  have hua' : M₀.π ⁅u, a⁆ ∈ M₀.img (conjSubgroup d B) := by
    have hBdn : conjSubgroup d B ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ (sec39_conjB_le_Vt hdM hud hx)))
    have hmem : ⁅u, a⁆ ∈ ((conjSubgroup d B : Set G) * (Z : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup d B) Z hBdn]
      exact hua
    obtain ⟨b', hb', z, hz, hbz⟩ := hmem
    have hb'Q : b' ∈ Q := hVQ (sec39_conjB_le_Vt hdM hud hb')
    have hzQ : z ∈ Q := hc.Z_le_Q hz
    have e1 : M₀.π ⁅u, a⁆ = M₀.π b' := by
      rw [← hbz, M₀.π_mul _ hb'Q _ hzQ, (M₀.π_ker z hzQ).mpr hz, add_zero]
    rw [e1]
    exact M₀.pi_mem_img hb' hb'Q
  obtain ⟨s₂, hs₂⟩ := (heB₂ (M₀.π ⁅u, a⁆)).mp hua'
  have hF : D.F e₁ e₂ ≠ 0 := by
    intro h0
    apply hBne
    rw [← hFww]
    have hw : w = s₁ • e₁ := Subtype.ext hs₁
    have hw' : w' = s₂ • e₂ := Subtype.ext hs₂
    rw [hw, hw', LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, h0, mul_zero,
      mul_zero]
  have hSinv : D.ρ.range = Classify.sympSubgroup D.F →
      ∀ x : ↥(imgSub M₀ (Vt M (LB M Q B) B Z u) hS), D.F x e₁ = 0 →
      ∀ g ∈ ((conjSubgroup c (LB M Q B)).subgroupOf (Rt M (LB M Q B) u)).map D.ρ,
        Classify.symTransvection D.alt x 1 * g * (Classify.symTransvection D.alt x 1)⁻¹ ∈
          ((conjSubgroup c (LB M Q B)).subgroupOf (Rt M (LB M Q B) u)).map D.ρ := by
    intro hsp x hx g hg
    have htx : Classify.symTransvection D.alt x 1 ∈ D.ρ.range := by
      rw [hsp]
      exact Classify.symTransvection_mem D.alt x 1
    obtain ⟨r, hr⟩ := htx
    have hre : D.ρ r e₁ = (1 : GaloisField 2 n') • e₁ := by
      rw [hr, one_smul, Classify.symTransvection_apply, one_mul]
      have : D.F e₁ x = 0 := by rw [Classify.form_comm D.alt]; exact hx
      rw [this, zero_smul, add_zero]
    have hrn := hc.mem_normalizer_conj_LB_of_fix hs h D hcM huc e₁ heB₁ r 1 hre
    obtain ⟨y, hy, rfl⟩ := hg
    refine ⟨r * y * r⁻¹, ?_, ?_⟩
    · have hy' : y ∈ (conjSubgroup c (LB M Q B)).subgroupOf (Rt M (LB M Q B) u) := hy
      show r * y * r⁻¹ ∈ (conjSubgroup c (LB M Q B)).subgroupOf (Rt M (LB M Q B) u)
      rw [Subgroup.mem_subgroupOf] at hy' ⊢
      have := (Subgroup.mem_normalizer_iff.mp hrn (y : G)).mp hy'
      simpa using this
    · rw [map_mul, map_mul, map_inv, hr]
  exact opp_glue hX (Rt M (LB M Q B) u) (hc.CN u) (conjSubgroup c (LB M Q B))
    (conjSubgroup d (LB M Q B)) hL₁R hL₂R D.F D.nondeg D.alt hq4 hdim D.ρ D.ker hH e₁ e₂ hF
    hepr₁ hepr₂ heful₁ heful₂ hcases hSinv

end S94F

end CFSG.RankThree.GF2n.Stroth80
