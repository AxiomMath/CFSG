module

public import CFSG.Quasithin.MS93.S511SBase

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem relIndex_center_le_card (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {H E₁ E₂ : Subgroup G}
    (hH : H ≤ Uq M T L ⊔ M ⊓ Subgroup.centralizer (M : Set G)) (hE₁ : E₁ ≤ M) (hE₂ : E₂ ≤ M)
    (hHE : H ≤ Subgroup.centralizer (E₁ : Set G) ⊓ Subgroup.centralizer (E₂ : Set G)) :
    (M ⊓ Subgroup.centralizer (M : Set G)).relIndex H ≤
      Nat.card ↥(MSP.fixSp (S5.imSp a E₁) ⊓ MSP.fixSp (S5.imSp a E₂)) := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hlift2 := (sp4Lift_holds G M T L h k F _ _ a hd).2.1
  set Zc := M ⊓ Subgroup.centralizer (M : Set G) with hZc
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hZn : Zc ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    inf_le_left.trans (le_normalizer_Uq h.le_normalizer)
  have hcomm : ∀ z ∈ Zc, ∀ m ∈ M, z * m = m * z := fun z hz m hm =>
    (Subgroup.mem_centralizer_iff.1 hz.2 m hm).symm
  have hdec : ∀ x : ↥H, ∃ u : ↥(Uq M T L), ∃ z ∈ Zc, (u : G) * z = x := by
    intro x
    have hx' : (x : G) ∈ ((Uq M T L ⊔ Zc : Subgroup G) : Set G) := hH x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZn] at hx'
    obtain ⟨u, hu, z, hz, he⟩ := hx'
    exact ⟨⟨u, hu⟩, z, hz, he⟩
  have huniq : ∀ (u₁ u₂ : ↥(Uq M T L)) (z₁ z₂ : G), z₁ ∈ Zc → z₂ ∈ Zc →
      (u₁ : G) * z₁ = u₂ * z₂ → nv.toVec u₁ = nv.toVec u₂ := by
    intro u₁ u₂ z₁ z₂ hz₁ hz₂ he
    have e1 : ((u₂⁻¹ * u₁ : ↥(Uq M T L)) : G) = z₂ * z₁⁻¹ := by
      push_cast
      calc (u₂ : G)⁻¹ * u₁ = (u₂ : G)⁻¹ * (u₁ * z₁) * z₁⁻¹ := by group
        _ = (u₂ : G)⁻¹ * (u₂ * z₂) * z₁⁻¹ := by rw [he]
        _ = z₂ * z₁⁻¹ := by group
    have hmem : ((u₂⁻¹ * u₁ : ↥(Uq M T L)) : G) ∈
        Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hlift2]
      refine Subgroup.mem_inf.2 ⟨(u₂⁻¹ * u₁).2, ?_⟩
      rw [e1]
      exact mul_mem (Subgroup.mem_inf.1 hz₂).2 (inv_mem (Subgroup.mem_inf.1 hz₁).2)
    have h1 := (nv.ker_iff _).2 hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  choose uH zH hzH heH using hdec
  let ψ : ↥H →* Multiplicative (MSP.V4 F) :=
    { toFun := fun x => nv.toVec (uH x)
      map_one' := by
        rw [← map_one nv.toVec]
        refine huniq _ 1 (zH 1) 1 (hzH 1) (one_mem _) ?_
        rw [heH, OneMemClass.coe_one, OneMemClass.coe_one, one_mul]
      map_mul' := by
        intro x y
        rw [← map_mul]
        refine huniq _ (uH x * uH y) (zH (x * y)) (zH x * zH y) (hzH _)
          (mul_mem (hzH x) (hzH y)) ?_
        rw [heH, Subgroup.coe_mul, Subgroup.coe_mul, ← heH x, ← heH y]
        have := hcomm (zH x) (hzH x) (uH y) (hUM (uH y).2)
        calc (uH x : G) * zH x * (uH y * zH y) = uH x * (zH x * uH y) * zH y := by group
          _ = uH x * (uH y * zH x) * zH y := by rw [this]
          _ = uH x * uH y * (zH x * zH y) := by group }
  have hker : ψ.ker = Zc.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show nv.toVec (uH x) = 1 ↔ (x : G) ∈ Zc
    constructor
    · intro h1
      have h2 := (nv.ker_iff _).1 h1
      rw [hlift2] at h2
      rw [← heH x]
      exact mul_mem ⟨hUM (uH x).2, h2.2⟩ (hzH x)
    · intro hx
      rw [← map_one nv.toVec]
      refine huniq _ 1 (zH x) x (hzH x) hx ?_
      rw [heH x, OneMemClass.coe_one, one_mul]
  have hval : ∀ x : ↥H, Multiplicative.toAdd (ψ x) ∈
      MSP.fixSp (S5.imSp a E₁) ⊓ MSP.fixSp (S5.imSp a E₂) := by
    intro x
    have hux : ∀ {E : Subgroup G}, E ≤ M → (x : G) ∈ Subgroup.centralizer (E : Set G) →
        ((uH x : ↥(Uq M T L)) : G) ∈ Subgroup.centralizer (E : Set G) := by
      intro E hEM hxE
      have e : ((uH x : ↥(Uq M T L)) : G) = x * (zH x)⁻¹ := by
        rw [← heH x]
        group
      rw [e]
      refine mul_mem hxE (inv_mem ?_)
      exact Subgroup.mem_centralizer_iff.2 fun m hm =>
        (Subgroup.mem_centralizer_iff.1 (hzH x).2 m (hEM hm))
    exact ⟨nv.vec_mem_fixSp (uH x) (hux hE₁ (hHE x.2).1),
      nv.vec_mem_fixSp (uH x) (hux hE₂ (hHE x.2).2)⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  refine Nat.card_le_card_of_injective
    (fun y : ↥ψ.range => (⟨Multiplicative.toAdd (y : Multiplicative (MSP.V4 F)), ?_⟩ :
      ↥(MSP.fixSp (S5.imSp a E₁) ⊓ MSP.fixSp (S5.imSp a E₂)))) ?_
  · obtain ⟨x, hx⟩ := y.2
    rw [← hx]
    exact hval x
  · intro y₁ y₂ hy
    have h1 := congrArg (fun w : ↥(MSP.fixSp (S5.imSp a E₁) ⊓ MSP.fixSp (S5.imSp a E₂)) =>
      (w : MSP.V4 F)) hy
    exact Subtype.ext (Multiplicative.toAdd.injective h1)

omit [Fintype F] in
theorem vec_commutator (h : PUHyp M T L) (nv : S5.NatVec M T L a) (e : ↥M)
    (u : ↥(Uq M T L)) :
    ∃ hc : ⁅(e : G), (u : G)⁆ ∈ Uq M T L,
      nv.vec ⟨_, hc⟩ = MSP.mat (a e) *ᵥ nv.vec u - nv.vec u := by
  have hMU := le_normalizer_Uq (T := T) h.le_normalizer
  have heu : (e : G) * u * (e : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hMU e.2) u).1 u.2
  have hc : ⁅(e : G), (u : G)⁆ ∈ Uq M T L := by
    rw [commutatorElement_def]
    exact mul_mem heu (inv_mem u.2)
  refine ⟨hc, ?_⟩
  have e1 : (⟨_, hc⟩ : ↥(Uq M T L)) = ⟨_, heu⟩ * u⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  have h1 := nv.vec_conj e u heu
  simp only [S5.NatVec.vec] at h1 ⊢
  rw [e1, map_mul, map_inv, toAdd_mul, toAdd_inv, h1, sub_eq_add_neg]

omit [Fintype F] in
theorem commSp_le_iff_vec (h : PUHyp M T L) (nv : S5.NatVec M T L a) {E : Subgroup G}
    (hE : E ≤ M) {W : Submodule F (MSP.V4 F)} :
    MSP.commSp (S5.imSp a E) ≤ W ↔
      ∀ x : ↥(Uq M T L), (x : G) ∈ ⁅Uq M T L, E⁆ → nv.vec x ∈ W := by
  constructor
  · intro hW
    set H₃ : Subgroup G :=
      ((AddSubgroup.toSubgroup W.toAddSubgroup).comap nv.toVec).map (Uq M T L).subtype
      with hH₃
    have hmem : ∀ x : ↥(Uq M T L), (x : G) ∈ H₃ ↔ nv.vec x ∈ W := by
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
        have : y = x := Subtype.ext hyx
        subst this
        exact hy
      · intro hx
        exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    have hle : ⁅Uq M T L, E⁆ ≤ H₃ := by
      rw [Subgroup.commutator_le]
      intro u hu e he
      obtain ⟨hc, hv⟩ := vec_commutator h nv ⟨e, hE he⟩ ⟨u, hu⟩
      have hc' : ⁅u, e⁆ ∈ Uq M T L := by
        rw [← commutatorElement_inv]
        exact inv_mem hc
      have e1 : (⟨⁅u, e⁆, hc'⟩ : ↥(Uq M T L)) = (⟨_, hc⟩ : ↥(Uq M T L))⁻¹ := by
        apply Subtype.ext
        simp [commutatorElement_inv]
      refine (hmem ⟨_, hc'⟩).2 ?_
      have h2 : nv.vec (⟨_, hc⟩ : ↥(Uq M T L))⁻¹ = -nv.vec ⟨_, hc⟩ := by
        simp only [S5.NatVec.vec]
        rw [map_inv, toAdd_inv]
      rw [e1, h2, hv]
      have hmA : a ⟨e, hE he⟩ ∈ S5.imSp a E :=
        Subgroup.mem_map.2 ⟨⟨e, hE he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      exact W.neg_mem (hW (MSP.sub_mem_commSp hmA _))
    intro x hx
    exact (hmem x).1 (hle hx)
  · intro hW
    refine MSP.commSp_le_iff.2 ?_
    rintro _ ⟨e, he, rfl⟩ v
    obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd v)
    have hv : nv.vec u = v := by
      simp only [S5.NatVec.vec]
      rw [hu, toAdd_ofAdd]
    obtain ⟨hc, hcv⟩ := vec_commutator h nv e u
    rw [← hv, ← hcv]
    refine hW _ ?_
    show ⁅(e : G), (u : G)⁆ ∈ _
    rw [← commutatorElement_inv]
    exact inv_mem (Subgroup.commutator_mem_commutator u.2 (Subgroup.mem_subgroupOf.1 he))

theorem card_commSp_le_relIndex (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hE : E ≤ M) :
    Nat.card ↥(MSP.commSp (S5.imSp a E)) ≤
      (M ⊓ Subgroup.centralizer (M : Set G)).relIndex ⁅Uq M T L, E⁆ := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hlift2 := (sp4Lift_holds G M T L h k F _ _ a hd).2.1
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hKU : ⁅Uq M T L, E⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hE.trans (le_normalizer_Uq h.le_normalizer))
  let ψ : ↥⁅Uq M T L, E⁆ →* Multiplicative (MSP.V4 F) :=
    nv.toVec.comp (Subgroup.inclusion hKU)
  have hker : ψ.ker = (M ⊓ Subgroup.centralizer (M : Set G)).subgroupOf ⁅Uq M T L, E⁆ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show nv.toVec (Subgroup.inclusion hKU x) = 1 ↔ _
    rw [nv.ker_iff, hlift2]
    exact ⟨fun hx => ⟨hUM hx.1, hx.2⟩, fun hx => ⟨hKU x.2, hx.2⟩⟩
  have hsub : ∀ w ∈ MSP.commSp (S5.imSp a E), ∀ c : F,
      Multiplicative.ofAdd (c • w) ∈ ψ.range := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨_, ⟨e, he, rfl⟩, v, rfl⟩ := hw
      intro c
      obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd (c • v))
      have hv : nv.vec u = c • v := by
        simp only [S5.NatVec.vec]
        rw [hu, toAdd_ofAdd]
      obtain ⟨hc, hcv⟩ := vec_commutator h nv e u
      have hcK : ⁅(e : G), (u : G)⁆ ∈ ⁅Uq M T L, E⁆ := by
        rw [← commutatorElement_inv]
        exact inv_mem (Subgroup.commutator_mem_commutator u.2 (Subgroup.mem_subgroupOf.1 he))
      refine ⟨⟨_, hcK⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      show nv.vec ⟨_, hc⟩ = _
      rw [hcv, hv, toAdd_ofAdd, smul_sub, Matrix.mulVec_smul]
    | zero =>
      intro c
      rw [smul_zero, ofAdd_zero]
      exact one_mem _
    | add x y _ _ hx hy =>
      intro c
      rw [smul_add, ofAdd_add]
      exact mul_mem (hx c) (hy c)
    | smul d x _ hx =>
      intro c
      rw [smul_smul]
      exact hx (c * d)
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  refine Nat.card_le_card_of_injective
    (fun w : ↥(MSP.commSp (S5.imSp a E)) =>
      (⟨Multiplicative.ofAdd (w : MSP.V4 F), ?_⟩ : ↥ψ.range)) ?_
  · have := hsub w w.2 1
    rwa [one_smul] at this
  · intro w₁ w₂ hw
    have h1 := congrArg (fun y : ↥ψ.range => Multiplicative.toAdd (y : Multiplicative (MSP.V4 F)))
      hw
    exact Subtype.ext h1

theorem uq_inf_centralizer_eq_of_commutator_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E E' : Subgroup G} (hE : E ≤ M) (hE' : E' ≤ M) (heq : ⁅Uq M T L, E⁆ = ⁅Uq M T L, E'⁆) :
    Uq M T L ⊓ Subgroup.centralizer (E : Set G) =
      Uq M T L ⊓ Subgroup.centralizer (E' : Set G) := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hMU := le_normalizer_Uq (T := T) h.le_normalizer
  have hcomm : MSP.commSp (S5.imSp a E) = MSP.commSp (S5.imSp a E') := by
    refine le_antisymm ((commSp_le_iff_vec h nv hE).2 fun x hx => ?_)
      ((commSp_le_iff_vec h nv hE').2 fun x hx => ?_)
    · exact (commSp_le_iff_vec h nv hE').1 le_rfl x (heq ▸ hx)
    · exact (commSp_le_iff_vec h nv hE).1 le_rfl x (heq.symm ▸ hx)
  have hfix : MSP.fixSp (S5.imSp a E) = MSP.fixSp (S5.imSp a E') := by
    rw [S33.fixSp_eq_perp_commSp, S33.fixSp_eq_perp_commSp, hcomm]
  ext x
  constructor
  · rintro ⟨hxU, hxC⟩
    refine ⟨hxU, ?_⟩
    have := (nv.mem_centralizer_iff_vec_mem_fixSp hMU hlift hE ⟨x, hxU⟩).1 hxC
    rw [hfix] at this
    exact (nv.mem_centralizer_iff_vec_mem_fixSp hMU hlift hE' ⟨x, hxU⟩).2 this
  · rintro ⟨hxU, hxC⟩
    refine ⟨hxU, ?_⟩
    have := (nv.mem_centralizer_iff_vec_mem_fixSp hMU hlift hE' ⟨x, hxU⟩).1 hxC
    rw [← hfix] at this
    exact (nv.mem_centralizer_iff_vec_mem_fixSp hMU hlift hE ⟨x, hxU⟩).2 this

theorem z0q_le_sup (h32 : S32) (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) :
    Z0q M T ≤ Uq M T L ⊔ M ⊓ Subgroup.centralizer (M : Set G) := by
  have key := zm_le_sup' h32 h53 h hmin hb hd (isMVtx_baseA (puAmalgam h.le))
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hCM : Xq M ⊓ (M ⊓ Subgroup.centralizer (M : Set G)) ≤ M := inf_le_right.trans inf_le_left
  rw [puAmalgam.zm_baseA, S5B.uSub_baseA h, S5B.xm_baseA_eq h, S5B.stabCenter_baseA, ← imM_inf,
    ← S5B.imM_sup_of_le h.le hUM hCM, imM_le_imM_iff h.le (Z0q_le M T)] at key
  exact key.trans (sup_le_sup_left inf_le_right _)

theorem relIndex_stabCenter_le_card (h32 : S32) (h53 : S53) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {H E₁ E₂ : Subgroup (puAmalgam h.le).Universal} (hH : H ≤ ZM _ (baseA (puAmalgam h.le)))
    (hE₁ : E₁ ≤ stab _ (baseA (puAmalgam h.le))) (hE₂ : E₂ ≤ stab _ (baseA (puAmalgam h.le)))
    (hHE : H ≤ Subgroup.centralizer (E₁ : Set _) ⊓ Subgroup.centralizer (E₂ : Set _)) :
    (stabCenter _ (baseA (puAmalgam h.le))).relIndex H ≤
      Nat.card ↥(MSP.fixSp (S5.vIm h.le a E₁) ⊓ MSP.fixSp (S5.vIm h.le a E₂)) := by
  rw [puAmalgam.stab_baseA] at hE₁ hE₂
  obtain ⟨E₁₀, -, hE₁M, rfl⟩ := S5.exists_eq_imM h.le hE₁
  obtain ⟨E₂₀, -, hE₂M, rfl⟩ := S5.exists_eq_imM h.le hE₂
  rw [puAmalgam.zm_baseA] at hH
  obtain ⟨H₀, hH₀Z, hH₀M, rfl⟩ := S5.exists_eq_imM h.le hH
  have hHE₀ : H₀ ≤ Subgroup.centralizer (E₁₀ : Set G) ⊓ Subgroup.centralizer (E₂₀ : Set G) := by
    have h1 : imM h.le H₀ ≤ imM h.le (H₀ ⊓ (Subgroup.centralizer (E₁₀ : Set G) ⊓
        Subgroup.centralizer (E₂₀ : Set G))) := by
      rw [← inf_assoc, imM_inf_centralizer h.le _ hE₂M, imM_inf_centralizer h.le _ hE₁M]
      exact le_inf (le_inf le_rfl (hHE.trans inf_le_left)) (hHE.trans inf_le_right)
    exact ((imM_le_imM_iff h.le hH₀M).1 h1).trans inf_le_right
  rw [S5B.stabCenter_baseA, S5B.relIndex_imM h.le hH₀M, S5B.vIm_imM h.le, S5B.vIm_imM h.le]
  exact relIndex_center_le_card h hd (hH₀Z.trans (z0q_le_sup h32 h53 h hmin hb hd)) hE₁M hE₂M
    hHE₀

theorem le_stabCenter_of_fixSp (h32 : S32) (h53 : S53) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {E₁ E₂ : Subgroup (puAmalgam h.le).Universal}
    (hE₁ : E₁ ≤ stab _ (baseA (puAmalgam h.le))) (hE₂ : E₂ ≤ stab _ (baseA (puAmalgam h.le)))
    (hfix : MSP.fixSp (S5.vIm h.le a E₁) ⊓ MSP.fixSp (S5.vIm h.le a E₂) = ⊥) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E₁ : Set _) ⊓
        Subgroup.centralizer (E₂ : Set _) ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  have key := relIndex_stabCenter_le_card h32 h53 h hmin hb hd
    (H := ZM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E₁ : Set _) ⊓
        Subgroup.centralizer (E₂ : Set _)) (inf_le_left.trans inf_le_left) hE₁ hE₂
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  rw [hfix] at key
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hZβ : ZM _ (baseA (puAmalgam h.le)) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    (zm_le_qv_self _ hα hb0).trans (qv_le_qv _ hyp hα (adj_baseA_baseB _))
  have : Finite ↥(Qv (puAmalgam h.le) (baseB (puAmalgam h.le))) :=
    finite_qv _ hyp (not_isMVtx_baseB _)
  have : Finite ↥(ZM (puAmalgam h.le) (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E₁ : Set _) ⊓ Subgroup.centralizer (E₂ : Set _)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((inf_le_left.trans inf_le_left).trans hZβ))
  have h1 : (stabCenter _ (baseA (puAmalgam h.le))).relIndex
      (ZM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E₁ : Set _) ⊓
        Subgroup.centralizer (E₂ : Set _)) = 1 := by
    have h0 : 0 < (stabCenter _ (baseA (puAmalgam h.le))).relIndex
        (ZM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E₁ : Set _) ⊓
          Subgroup.centralizer (E₂ : Set _)) := Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
    have : Nat.card ↥(⊥ : Submodule F (MSP.V4 F)) = 1 := by simp
    omega
  exact Subgroup.relIndex_eq_one.1 h1

theorem card_commSp_le_relIndex_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ (baseA (puAmalgam h.le))) :
    Nat.card ↥(MSP.commSp (S5.vIm h.le a E)) ≤
      (stabCenter _ (baseA (puAmalgam h.le))).relIndex
        ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), E⁆ := by
  rw [puAmalgam.stab_baseA] at hE
  obtain ⟨E₀, -, hE₀M, rfl⟩ := S5.exists_eq_imM h.le hE
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hKU : ⁅Uq M T L, E₀⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hE₀M.trans (le_normalizer_Uq h.le_normalizer))
  rw [S5B.uSub_baseA h, ← imM_commutator h.le hUM hE₀M, S5B.stabCenter_baseA,
    S5B.relIndex_imM h.le (hKU.trans hUM), S5B.vIm_imM h.le]
  exact card_commSp_le_relIndex h hd hE₀M

theorem uSub_inf_centralizer_eq_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E E' : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hE' : E' ≤ stab _ (baseA (puAmalgam h.le)))
    (heq : ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), E⁆ =
      ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), E'⁆) :
    S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E : Set _) =
      S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E' : Set _) := by
  rw [puAmalgam.stab_baseA] at hE hE'
  obtain ⟨E₀, -, hE₀M, rfl⟩ := S5.exists_eq_imM h.le hE
  obtain ⟨E₀', -, hE₀M', rfl⟩ := S5.exists_eq_imM h.le hE'
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  rw [S5B.uSub_baseA h, ← imM_commutator h.le hUM hE₀M, ← imM_commutator h.le hUM hE₀M'] at heq
  have hKU : ⁅Uq M T L, E₀⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hE₀M.trans (le_normalizer_Uq h.le_normalizer))
  have hKU' : ⁅Uq M T L, E₀'⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hE₀M'.trans (le_normalizer_Uq h.le_normalizer))
  have heq₀ : ⁅Uq M T L, E₀⁆ = ⁅Uq M T L, E₀'⁆ :=
    le_antisymm ((imM_le_imM_iff h.le (hKU.trans hUM)).1 heq.le)
      ((imM_le_imM_iff h.le (hKU'.trans hUM)).1 heq.ge)
  rw [S5B.uSub_baseA h, ← imM_inf_centralizer h.le _ hE₀M, ← imM_inf_centralizer h.le _ hE₀M',
    uq_inf_centralizer_eq_of_commutator_eq h hd hE₀M hE₀M' heq₀]

end S511S

end CFSG.Quasithin.MS93
