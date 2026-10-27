module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S33XMain
public import CFSG.Quasithin.MS93.S510Tv
public import CFSG.Quasithin.MS93.S512FCoord
public import CFSG.Quasithin.MS93.S512HCoc
public import CFSG.Quasithin.MS93.S512TSp
public import CFSG.Quasithin.MS93.S5A56

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

namespace S512H

theorem commutator_sup_le_left {Γ : Type*} [Group Γ] {A B E : Subgroup Γ}
    (hAB : A ≤ Subgroup.normalizer (B : Set Γ))
    (hBE : B ≤ Subgroup.centralizer (E : Set Γ)) : ⁅A ⊔ B, E⁆ ≤ ⁅A, E⁆ := by
  rw [Subgroup.commutator_le]
  intro w hw e he
  have hw' : w ∈ ((A : Set Γ) * (B : Set Γ)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hAB]
    exact hw
  obtain ⟨x, hx, y, hy, rfl⟩ := hw'
  have hye : y * e = e * y := (Subgroup.mem_centralizer_iff.1 (hBE hy) e he).symm
  have e1 : ⁅x * y, e⁆ = ⁅x, e⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc x * y * e * (x * y)⁻¹ * e⁻¹ = x * (y * e) * y⁻¹ * x⁻¹ * e⁻¹ := by group
      _ = x * (e * y) * y⁻¹ * x⁻¹ * e⁻¹ := by rw [hye]
      _ = x * e * x⁻¹ * e⁻¹ := by group
  rw [e1]
  exact Subgroup.commutator_mem_commutator hx he

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem point_inf_fixSp_eq_bot (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {T₁ Z Q : Subgroup (puAmalgam h.le).Universal}
    (hT₁ : T₁ ≤ stab _ (baseA (puAmalgam h.le))) (hZ : Z ≤ stab _ (baseA (puAmalgam h.le)))
    (hgen : T₁ ⊔ Z = stab _ (baseA (puAmalgam h.le)))
    (hTQ : T₁ ≤ Subgroup.normalizer (Q : Set (puAmalgam h.le).Universal))
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p) (hZp : S5.vIm h.le a Z = MSP.xPoint p)
    (hQne : MSP.fixSp (S5.vIm h.le a Q) ≠ ⊤) :
    p ⊓ MSP.fixSp (S5.vIm h.le a Q) = ⊥ := by
  set W := MSP.fixSp (S5.vIm h.le a Q) with hW
  by_contra hne
  obtain ⟨v, ⟨hvp, hvW⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hpW : p ≤ W := by
    have hle : F ∙ v ≤ p := (Submodule.span_singleton_le_iff_mem v p).2 hvp
    have heq : F ∙ v = p := Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_singleton hv0]
      exact (show Module.finrank F p = 1 from hp).symm)
    rw [← heq]
    exact (Submodule.span_singleton_le_iff_mem v W).2 hvW
  have hst := S5.ofA_range_eq (hTM := h.le)
  have hT₁W : S5.vIm h.le a T₁ ≤ MSP.stab W := by
    rintro _ ⟨m, hm, rfl⟩
    refine MSP.mem_stab_of_le fun w hw => ?_
    rw [MSP.mem_fixSp] at hw ⊢
    intro e he
    have hn : (puAmalgam h.le).ofA m⁻¹ ∈ Subgroup.normalizer (Q : Set _) := by
      rw [map_inv]
      exact inv_mem (hTQ hm)
    have hconj := S5.vIm_map_conj (hTM := h.le) (a := a) m⁻¹ Q
    rw [map_conj_eq_of_mem_normalizer hn] at hconj
    have he' : (a m)⁻¹ * e * a m ∈ S5.vIm h.le a Q := by
      rw [hconj]
      refine ⟨e, he, ?_⟩
      simp
    calc MSP.mat e *ᵥ (MSP.mat (a m) *ᵥ w)
        = MSP.mat (a m) *ᵥ (MSP.mat ((a m)⁻¹ * e * a m) *ᵥ w) := by
          rw [← MSP.mat_mul_mulVec, ← MSP.mat_mul_mulVec]
          congr 1
          group
      _ = MSP.mat (a m) *ᵥ w := by rw [hw _ he']
  have hZW : S5.vIm h.le a Z ≤ MSP.stab W := by
    rw [hZp]
    intro g hg
    refine MSP.mem_stab_of_le fun w hw => ?_
    have h1 := MSP.sub_mem_of_mem_fixer_perp hg w
    have e : MSP.mat g *ᵥ w = w + (MSP.mat g *ᵥ w - w) := by abel
    rw [e]
    exact add_mem hw (hpW h1)
  have htop : S5.vIm h.le a T₁ ⊔ S5.vIm h.le a Z = ⊤ := by
    rw [← S5.vIm_sup h.le (hT₁.trans hst.ge) (hZ.trans hst.ge), hgen, puAmalgam.stab_baseA,
      S5B.vIm_imM h.le, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top]
    exact hd.surj
  have hall : ∀ g : MSP.Sp4 F, g ∈ MSP.stab W := fun g => by
    have : g ∈ S5.vIm h.le a T₁ ⊔ S5.vIm h.le a Z := by rw [htop]; exact Subgroup.mem_top g
    exact sup_le hT₁W hZW this
  have hWtop := S512T.eq_top_of_invariant (W := W.toAddSubgroup)
    (fun g w hw => MSP.mulVec_mem_of_mem_stab (hall g) hw) hvW hv0
  apply hQne
  rw [eq_top_iff]
  intro w _
  have : w ∈ W.toAddSubgroup := by rw [hWtop]; exact AddSubgroup.mem_top w
  exact this

theorem commutator_mem_zq_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G))
    {Z Q : Subgroup (puAmalgam h.le).Universal} (hZ : Z ≤ stab _ (baseA (puAmalgam h.le)))
    (hQ : Q ≤ stab _ (baseA (puAmalgam h.le))) {p : Submodule F (MSP.V4 F)}
    (hp : MSP.IsPoint p) (hZp : S5.vIm h.le a Z ≤ MSP.xPoint p)
    (hpQ : p ⊓ MSP.fixSp (S5.vIm h.le a Q) = ⊥) {x z : (puAmalgam h.le).Universal}
    (hx : x ∈ imM h.le (S5Q2.X52.xFix h)) (hz : z ∈ Z)
    (hzx : ⁅z, x⁆ ∈ Subgroup.centralizer (Q : Set (puAmalgam h.le).Universal)) :
    ⁅z, x⁆ ∈ imM h.le (Zq M L) := by
  have hst := S5.ofA_range_eq (hTM := h.le)
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨n, hn⟩ := (hst.ge (hZ hz) : z ∈ (puAmalgam h.le).ofA.range)
  subst hn
  rw [puAmalgam.stab_baseA] at hQ
  obtain ⟨Q₀, -, hQ₀M, rfl⟩ := S5B.exists_eq_imM h.le hQ
  rw [S5B.vIm_imM h.le] at hpQ
  have hna : a n ∈ MSP.xPoint p := hZp ⟨n, hz, rfl⟩
  have hc : ⁅(n : G), (m : G)⁆ ∈ Subgroup.centralizer (Q₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqM := hQ₀M hq
    have h1 := Subgroup.mem_centralizer_iff.1 hzx ((puAmalgam h.le).ofA ⟨q, hqM⟩)
      ⟨⟨q, hqM⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩
    rw [← map_commutatorElement, ← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
    simpa [commutatorElement_def] using h2
  have key := commutator_mem_zq_of_xPoint h hd hZc (Subgroup.mem_subgroupOf.1 hm) hp n.2 hna
    hQ₀M hpQ hc
  refine ⟨⁅n, m⁆, Subgroup.mem_subgroupOf.2 ?_, map_commutatorElement _ _ _⟩
  simpa [commutatorElement_def] using key

theorem mem_sup_pCoreOf_of_ker (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {m : ↥M}
    (hm : a m = 1) : (m : G) ∈ L ⊔ pCoreOf 2 M := by
  set N := L ⊔ pCoreOf 2 M with hN
  have hNM : N ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hNn : M ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_sup h.le_normalizer (le_normalizer_pCoreOf M)
  have hNs : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hNn
  set φ := QuotientGroup.mk' (N.subgroupOf M)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hsup : L.subgroupOf M ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
  have hmem : m ∈ L.subgroupOf M ⊔ T.subgroupOf M := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hφl : φ l = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hl))
  obtain ⟨e, he⟩ := h.isPGroup ⟨(t : G), Subgroup.mem_subgroupOf.1 ht⟩
  have he' : t ^ 2 ^ e = 1 := Subtype.ext (by
    have := congrArg Subtype.val he
    simpa using this)
  have hφm : φ m ^ 2 ^ e = 1 := by rw [← hlt, map_mul, hφl, one_mul, ← map_pow, he', map_one]
  obtain ⟨j, hj, f, hf⟩ := exists_pow_isTwoElt φ m hφm
  have hmj : ((m ^ j : ↥M) : G) ∈ pCoreOf 2 M := by
    refine S5B.mem_pCoreOf_of_ker h hd (by rw [map_pow, hm, one_pow]) ⟨f, ?_⟩
    have := congrArg Subtype.val hf
    simpa using this
  have hφ1 : φ (m ^ j) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right hmj)
  have hm1 : φ m = 1 := by rw [← hj, hφ1]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm1
  exact hm1

theorem le_normalizer_xFix (h : PUHyp M T L) :
    M ≤ Subgroup.normalizer ((S5Q2.X52.xFix h : Subgroup G) : Set G) := by
  have hNn := S5Q2.X52.le_normalizer_uq_sup_cXL h
  have key : ∀ m ∈ M, ∀ y ∈ S5Q2.X52.xFix h, m * y * m⁻¹ ∈ S5Q2.X52.xFix h := by
    intro m hm y hy
    refine ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_Xq M hm) y).1 hy.1, fun m' hm' => ?_⟩
    have e : ⁅m', m * y * m⁻¹⁆ = m * ⁅m⁻¹ * m' * m, y⁆ * m⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hNn hm) _).1
      (hy.2 _ (M.mul_mem (M.mul_mem (M.inv_mem hm) hm') hm))
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key m hm y, fun hy => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hy
  simpa [mul_assoc] using this

theorem mem_xFix_of_commute (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) {r : G} (hr : r ∈ Xq M) {z : G} (hzM : z ∈ M)
    (hz : k = 1 → a ⟨z, hzM⟩ ∉ commutator (StatedSp 2 F)) (hzr : z * r = r * z) :
    r ∈ S5Q2.X52.xFix h := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  swap
  · refine ⟨hr, fun m hm => Subgroup.mem_sup_left ?_⟩
    rw [commutatorElement_def]
    exact S33.commutator_mem_uq h hd hk hXL hr hm
  have hk1 : k = 1 := by have := hd.1; omega
  have hq : Nat.card F = 2 := by rw [hd.nat_card_eq, hk1]; rfl
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hq
  have hidx := MSP.index_commutator c
  have hNn := S5Q2.X52.le_normalizer_uq_sup_cXL h
  set N := Uq M T L ⊔ S5.cXL M L with hNdef
  let H : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ⁅m, r⁆ ∈ N}
      mul_mem' := fun {m₁ m₂} h₁ h₂ => ⟨M.mul_mem h₁.1 h₂.1, by
        rw [S5.commutatorElement_mul_left']
        exact N.mul_mem ((Subgroup.mem_normalizer_iff.1 (hNn h₁.1) _).1 h₂.2) h₁.2⟩
      one_mem' := ⟨M.one_mem, by
        rw [commutatorElement_one_left]
        exact N.one_mem⟩
      inv_mem' := fun {m} hm => ⟨M.inv_mem hm.1, by
        have e : ⁅m⁻¹, r⁆ = m⁻¹ * ⁅m, r⁆⁻¹ * m⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hNn (M.inv_mem hm.1)) _).1 (N.inv_mem hm.2)⟩ }
  have hLH : L ≤ H := fun l hl => by
    refine ⟨h.L_le hl, Subgroup.mem_sup_left ?_⟩
    have := hXL (Subgroup.commutator_mem_commutator hr hl)
    rw [← commutatorElement_inv]
    exact (Uq M T L).inv_mem this
  have hOH : pCoreOf 2 M ≤ H := fun o ho => by
    refine ⟨pCoreOf_le' M ho, ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.2 (S5.commute_of_mem_pCoreOf hr ho)]
    exact N.one_mem
  have hzH : z ∈ H := by
    refine ⟨hzM, ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.2 hzr]
    exact N.one_mem
  have hkerH : ∀ m : ↥M, a m = 1 → (m : G) ∈ H := fun m hm =>
    sup_le hLH hOH (mem_sup_pCoreOf_of_ker h hd hm)
  have hcomm : ∀ m : ↥M, a m ∈ commutator (StatedSp 2 F) → (m : G) ∈ H := by
    intro m hm
    obtain ⟨l, hl, hla⟩ := S5.commutator_le_imSp_L h hd hm
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have hker : a (l⁻¹ * m) = 1 := by rw [map_mul, map_inv, hla, inv_mul_cancel]
    have e : (m : G) = l * ((l⁻¹ * m : ↥M) : G) := by simp
    rw [e]
    exact H.mul_mem (hLH hlL) (hkerH _ hker)
  refine ⟨hr, fun m hm => ?_⟩
  by_cases hma : a ⟨m, hm⟩ ∈ commutator (StatedSp 2 F)
  · exact (hcomm ⟨m, hm⟩ hma).2
  · have hz' := hz hk1
    have hmz : a (⟨m, hm⟩ * ⟨z, hzM⟩⁻¹) ∈ commutator (StatedSp 2 F) := by
      rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false hma (fun hzi => hz' (by simpa using hzi))
    have h1 := hcomm _ hmz
    have e : m = ((⟨m, hm⟩ * ⟨z, hzM⟩⁻¹ : ↥M) : G) * z := by simp
    rw [e]
    exact (H.mul_mem h1 hzH).2

theorem commutator_uq_le_of_relIndex_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E E' : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) (hE'E : E' ≤ E)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hcard : 2 ^ k ≤ Nat.card (S5.imSp a E')) : ⁅Uq M T L, E⁆ ≤ ⁅Uq M T L, E'⁆ := by
  have := hd.charP
  obtain ⟨p, hp, -, -, hEp⟩ := S510.exists_point_of_relIndex h hd hEM hrel
  have hEq : S5.imSp a E' = S5.imSp a E := by
    refine Subgroup.eq_of_le_of_card_ge (S5.imSp_mono a hE'E) ?_
    calc Nat.card (S5.imSp a E) ≤ Nat.card (MSP.xPoint p) := Subgroup.card_le_of_le hEp
      _ = 2 ^ k := by rw [MSP.card_xPoint hp, hd.nat_card_eq]
      _ ≤ _ := hcard
  rw [Subgroup.commutator_le]
  intro u hu e he
  have heM := hEM he
  have hmem : a ⟨e, heM⟩ ∈ S5.imSp a E' := by
    rw [hEq]
    exact ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  obtain ⟨e', he', hae⟩ := hmem
  have he'E : (e' : G) ∈ E := hE'E (Subgroup.mem_subgroupOf.1 he')
  set κ : G := (e' : G)⁻¹ * e with hκ
  have hκM : κ ∈ M := M.mul_mem (M.inv_mem e'.2) heM
  have hκ1 : a ⟨κ, hκM⟩ = 1 := by
    have e0 : (⟨κ, hκM⟩ : ↥M) = e'⁻¹ * ⟨e, heM⟩ := rfl
    rw [e0, map_mul, map_inv, hae, inv_mul_cancel]
  have hκE : κ ∈ E := E.mul_mem (E.inv_mem he'E) he
  obtain ⟨f, hf⟩ := hE2 ⟨κ, hκE⟩
  have hκO : κ ∈ pCoreOf 2 M := by
    refine S5B.mem_pCoreOf_of_ker h hd hκ1 ⟨f, ?_⟩
    have := congrArg Subtype.val hf
    simpa using this
  have hκu : κ * u = u * κ := S5.commute_of_mem_pCoreOf (h.Uq_le_Xq hu) hκO
  have hκu' : κ * u⁻¹ = u⁻¹ * κ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hκu, ← mul_assoc, inv_mul_cancel, one_mul]
  have e1 : e = (e' : G) * κ := by rw [hκ, mul_inv_cancel_left]
  have e2 : ⁅u, e⁆ = ⁅u, (e' : G)⁆ := by
    rw [e1, commutatorElement_def, commutatorElement_def]
    calc u * ((e' : G) * κ) * u⁻¹ * ((e' : G) * κ)⁻¹ =
        u * (e' : G) * (κ * u⁻¹) * κ⁻¹ * (e' : G)⁻¹ := by group
      _ = u * (e' : G) * (u⁻¹ * κ) * κ⁻¹ * (e' : G)⁻¹ := by rw [hκu']
      _ = u * (e' : G) * u⁻¹ * (e' : G)⁻¹ := by group
  rw [e2]
  exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_subgroupOf.1 he')

theorem commutator_uSub_le_of_relIndex (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E E' : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) (hE2 : IsPGroup 2 E) (hE'E : E' ≤ E)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    (hq : 2 ^ k ≤ (Qv _ δ).relIndex E') :
    ⁅S5.uSub h.le L δ, E⁆ ≤ ⁅S5.uSub h.le L δ, E'⁆ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨E₁, hE₁M, rfl⟩ := S5B.exists_eq_map_imM h.le g (hE'E.trans hE)
  have hE₁E₀ : E₁ ≤ E₀ := (imM_le_imM_iff h.le hE₁M).1 ((map_conj_le_map_conj_iff g).1 hE'E)
  have hE₀2 := S512F.isPGroup_of_smul h g hE₀M hE2
  have hE₁2 : IsPGroup 2 (imM h.le E₁) :=
    (hE2.to_le hE'E).of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  have hE₁st : imM h.le E₁ ≤ stab _ (baseA (puAmalgam h.le)) := by
    rw [puAmalgam.stab_baseA]
    exact imM_mono h.le hE₁M
  rw [qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,
    S33.relIndex_qv_baseA_eq_card h hd hE₁st hE₁2, S5.vIm_imM h E₁] at hq
  have key := commutator_uq_le_of_relIndex_M h hd hE₀M hE₀2 hE₁E₀ hrel hq
  have hU : S5.uSub h.le L (g • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj g).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h]
  rw [hU, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
    ← S33.imM_commutator h.le hUM hE₀M, ← S33.imM_commutator h.le hUM hE₁M]
  exact Subgroup.map_mono (imM_mono h.le key)

end S512H

end CFSG.Quasithin.MS93
