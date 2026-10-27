module

public import CFSG.Timmesfeld.ARS.CaseEDist
public import CFSG.Timmesfeld.ARS.ExclNSStab
public import CFSG.Timmesfeld.ARS.ExclNSPolar

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity

section DoubleCoset

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)

include hct in
theorem nrep_mem_of_forall_mem_parabolic {P : Subgroup K} {J : Set (Fin D.rank)}
    (hn : ∀ k ∈ J, n k ∈ P) {u : (coxeterMatrix D.isFiniteType).Group}
    (hu : u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J) : nrep hct u ∈ P := by
  obtain ⟨ω, hred, hωJ, rfl⟩ :=
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced_wordProd_eq_of_mem_parabolic hu
  rw [nrep_wordProd hct hred]
  clear hred hu
  induction ω with
  | nil => exact one_mem _
  | cons k ω ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (hn k (hωJ k List.mem_cons_self))
      (ih fun i hi => hωJ i (List.mem_cons_of_mem k hi))

include hct in
theorem exists_eq_mul_mul_of_weylNHom_eq (hext : SteinbergExtras D n H) {P : Subgroup K}
    (hT : ⨆ i, H i ≤ P) {J : Set (Fin D.rank)} (hn : ∀ k ∈ J, n k ∈ P) (x y : weylN n H)
    {u v : (coxeterMatrix D.isFiniteType).Group}
    (hu : u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J)
    (hv : v ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J)
    (h : weylNHom hct hext y = u * weylNHom hct hext x * v) :
    ∃ p ∈ P, ∃ p' ∈ P, (y : K) = p * x * p' := by
  set z : weylN n H :=
    ⟨nrep hct u, nrep_mem_weylN hct u⟩ * x * ⟨nrep hct v, nrep_mem_weylN hct v⟩
  have hz : weylNHom hct hext z = weylNHom hct hext y := by
    rw [h, map_mul, map_mul, weylNHom_nrep, weylNHom_nrep]
  have ht : ((z⁻¹ * y : weylN n H) : K) ∈ ⨆ i, H i := by
    refine mem_iSup_of_actsAs_one hct hext (z⁻¹ * y).2 ?_
    have := actsAs_weylNHom hct hext (z⁻¹ * y)
    rwa [map_mul, map_inv, hz, inv_mul_cancel] at this
  refine ⟨nrep hct u, nrep_mem_of_forall_mem_parabolic hct hn hu,
    nrep hct v * ((z⁻¹ * y : weylN n H) : K),
    mul_mem (nrep_mem_of_forall_mem_parabolic hct hn hv) (hT ht), ?_⟩
  simp only [z, Subgroup.coe_mul, Subgroup.coe_inv]
  group

include hct in
theorem false_of_injective_doubleCoset (hext : SteinbergExtras D n H) {P : Subgroup K}
    (hB : (⨆ i, H i) ⊔ negUnipotent D ≤ P) {J : Set (Fin D.rank)} (hn : ∀ k ∈ J, n k ∈ P)
    {α : Type*} (ρ : K → α) (hρ : ∀ g, ∀ p ∈ P, ∀ p' ∈ P, ρ (p * g * p') = ρ g) {c : ℕ}
    (x : Fin c → (coxeterMatrix D.isFiniteType).Group)
    (hx : ∀ w, ∃ i, ∃ u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J,
      ∃ v ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J, w = u * x i * v)
    (g : Fin (c + 1) → K) (hg : Function.Injective (ρ ∘ g)) : False := by
  classical
  have hT : ⨆ i, H i ≤ P := le_sup_left.trans hB
  choose b hb y hy b' hb' hgy using fun k => exists_eq_mul_mul_negBorel hct hext (g k)
  have hρy : ∀ k, ρ (g k) = ρ (y k) := fun k => by rw [hgy k, hρ _ _ (hB (hb k)) _ (hB (hb' k))]
  choose i u hu v hv hw using fun k => hx (weylNHom hct hext ⟨y k, hy k⟩)
  obtain ⟨k, l, hkl, hi⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
  have hrel : weylNHom hct hext ⟨y l, hy l⟩ =
      (u l * (u k)⁻¹) * weylNHom hct hext ⟨y k, hy k⟩ * ((v k)⁻¹ * v l) := by
    rw [hw l, hw k, hi]
    group
  obtain ⟨p, hp, p', hp', he⟩ := exists_eq_mul_mul_of_weylNHom_eq hct hext hT hn ⟨y k, hy k⟩
    ⟨y l, hy l⟩ (mul_mem (hu l) (inv_mem (hu k))) (mul_mem (inv_mem (hv k)) (hv l)) hrel
  refine hkl (hg ?_)
  simp only [Function.comp_apply]
  rw [hρy k, hρy l]
  simp only at he
  rw [he, hρ _ _ hp _ hp']

end DoubleCoset

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

noncomputable def relType (R : Set (Subgroup G)) (X Y : Subgroup G) : Fin 4 := by
  classical
  exact if Y = X then 0 else if Y ∈ lambdaSet R X then 1 else if Commuting X Y then 2 else 3

theorem relType_conjSub (hR : IsRootClass R) (X Y : Subgroup G) (g : G) :
    relType R (conjSub X g) (conjSub Y g) = relType R X Y := by
  classical
  have hinj : conjSub Y g = conjSub X g ↔ Y = X := ⟨fun h => by
    have := congrArg (fun Z => conjSub Z g⁻¹) h
    simpa only [ExclNS.conjSub_conjSub_inv] using this, fun h => h ▸ rfl⟩
  have hl : conjSub Y g ∈ lambdaSet R (conjSub X g) ↔ Y ∈ lambdaSet R X := ⟨fun h => by
    have := conjSub_mem_lambdaSet hR h g⁻¹
    simpa only [ExclNS.conjSub_conjSub_inv] using this, fun h => conjSub_mem_lambdaSet hR h g⟩
  have hc := commuting_conjSub_iff' (X := X) (Y := Y) g
  unfold relType
  simp only [hinj, hl, hc]

section Lift

variable {A A₀ : Subgroup G}

noncomputable def liftBar (R : Set (Subgroup G)) (A A₀ : Subgroup G)
    (a : ↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀)) : ↥(levi R A A₀) :=
  Classical.choose (QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) a)

theorem mk_liftBar (a : ↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀)) :
    QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) (liftBar R A A₀ a) = a :=
  Classical.choose_spec (QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) a)

theorem conjSub_eq_of_mk_eq (hS : Sec13 R A A₀) {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    {v w : ↥(levi R A A₀)}
    (h : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) v =
      QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) w) :
    conjSub B (v : G) = conjSub B (w : G) := by
  have hz : v⁻¹ * w ∈ Subgroup.center ↥(levi R A A₀) := QuotientGroup.eq.1 h
  have e : (w : G) = (v : G) * ((v⁻¹ * w : ↥(levi R A A₀)) : G) := by simp
  rw [e, conjSub_mul, ExclNS.conjSub_eq_of_mem_center hS hB hz]

end Lift

section Count

variable {A A₀ : Subgroup G} {K : Type*} [Group K] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem false_of_doubleCoset_three (hS : Sec13 R A A₀)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H)
    (Ψ : K →* (↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀))) (hsurj : Function.Surjective Ψ)
    {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hBorel : ((⨆ i, H i) ⊔ negUnipotent D).map Ψ ≤ ExclNS.stabBar R A A₀ B)
    {J : Set (Fin D.rank)} (hn : ∀ k ∈ J, Ψ (n k) ∈ ExclNS.stabBar R A A₀ B)
    (x : Fin 3 → (coxeterMatrix D.isFiniteType).Group)
    (hx : ∀ w, ∃ i, ∃ u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J,
      ∃ v ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J, w = u * x i * v) :
    False := by
  classical
  have h := hS.hyp
  have := h.finite
  have hR := h.root
  set P := (ExclNS.stabBar R A A₀ B).comap Ψ with hP
  have hBP : (⨆ i, H i) ⊔ negUnipotent D ≤ P := Subgroup.map_le_iff_le_comap.1 hBorel
  set ρ : K → Fin 4 := fun k => relType R B (conjSub B (liftBar R A A₀ (Ψ k) : G)) with hρdef
  have hρ : ∀ g, ∀ p ∈ P, ∀ p' ∈ P, ρ (p * g * p') = ρ g := by
    intro g p hp p' hp'
    set lp := liftBar R A A₀ (Ψ p)
    set lg := liftBar R A A₀ (Ψ g)
    set lp' := liftBar R A A₀ (Ψ p')
    have hmk : QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) (liftBar R A A₀
        (Ψ (p * g * p'))) = QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) (lp * lg * lp') := by
      rw [mk_liftBar, map_mul, map_mul, map_mul, map_mul, mk_liftBar, mk_liftBar, mk_liftBar]
    have hp'B : conjSub B (lp' : G) = B := conjSub_eq_self_iff.2
      ((ExclNS.mk_mem_stabBar_iff hS hB lp').1 (by rw [mk_liftBar]; exact hp'))
    have hpB : conjSub B (lp : G) = B := conjSub_eq_self_iff.2
      ((ExclNS.mk_mem_stabBar_iff hS hB lp).1 (by rw [mk_liftBar]; exact hp))
    simp only [hρdef]
    rw [conjSub_eq_of_mk_eq hS hB hmk]
    simp only [Subgroup.coe_mul]
    rw [conjSub_mul, conjSub_mul, hp'B]
    have e := relType_conjSub hR B (conjSub B (lg : G)) (lp : G)
    rw [hpB] at e
    exact e
  have hval : ∀ C ∈ lambdaStar R A A₀, ∃ k, conjSub B (liftBar R A A₀ (Ψ k) : G) = C := by
    intro C hC
    obtain ⟨v, hv, hvC⟩ :=
      exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hS.mem hS.sec8.2 hS.max hS.opp hB hC
    obtain ⟨k, hk⟩ := hsurj (QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) ⟨v, hv⟩)
    refine ⟨k, ?_⟩
    rw [← hvC]
    exact conjSub_eq_of_mk_eq hS hB (v := liftBar R A A₀ (Ψ k)) (w := ⟨v, hv⟩)
      (by rw [mk_liftBar, hk])
  obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_special h hS.mem hS.sec8.2 hS.opp hB
  obtain ⟨hC₁, hC₁B, -⟩ := commutator_mem_lambdaStar h hS.mem hS.sec8.2 hS.opp hB hX hBX
  obtain ⟨C₂, hC₂, hC₂B, hC₂c, hC₂l⟩ := ExclNS.exists_mem_lambdaStar_polar hS hB
  obtain ⟨C₃, hC₃, hC₃c⟩ : ∃ C ∈ lambdaStar R A A₀, ¬ Commuting B C := by
    by_contra! hall
    obtain ⟨-, -, -, hcentA, -⟩ := Q_eq_M h hS.mem
    have hBM : Commuting B (M R A) := by
      rw [M_eq_gen_lambdaStar h hS.mem hS.opp, commuting_iff_le_centralizer]
      exact gen_le fun Y hY => commuting_iff_le_centralizer.1 (hall Y hY)
    have hmem : B ∈ {X | X ∈ R ∧ Commuting X (M R A)} := ⟨hB.1.1.1, hBM⟩
    rw [hcentA, Set.mem_singleton_iff] at hmem
    exact hB.1.1.2.1 hmem
  obtain ⟨k₁, hk₁⟩ := hval _ hC₁
  obtain ⟨k₂, hk₂⟩ := hval _ hC₂
  obtain ⟨k₃, hk₃⟩ := hval _ hC₃
  have h0 : ρ 1 = 0 := by
    have e : conjSub B (liftBar R A A₀ (Ψ 1) : G) = B := by
      have := conjSub_eq_of_mk_eq hS hB (v := liftBar R A A₀ (Ψ 1)) (w := 1)
        (by rw [mk_liftBar, map_one, map_one])
      rw [this, OneMemClass.coe_one, conjSub_one]
    simp only [hρdef]
    rw [e]
    simp [relType]
  have h1 : ρ k₁ = 1 := by
    simp [hρdef, hk₁, relType, hC₁B.1.2.1, hC₁B]
  have h2 : ρ k₂ = 2 := by
    simp [hρdef, hk₂, relType, hC₂B, hC₂l, hC₂c]
  have h3 : ρ k₃ = 3 := by
    have hne : C₃ ≠ B := fun e => hC₃c (by rw [e]; exact hR.commuting_self hB.1.1.1)
    have hnl : C₃ ∉ lambdaSet R B := fun hl => hC₃c hl.1.2.2
    simp [hρdef, hk₃, relType, hne, hnl, hC₃c]
  refine false_of_injective_doubleCoset hct hext hBP hn ρ hρ x hx ![1, k₁, k₂, k₃] ?_
  intro a b hab
  simp only [Function.comp_apply] at hab
  fin_cases a <;> fin_cases b <;> simp_all [Matrix.cons_val]

end Count

end CFSG.Timmesfeld.ARS
