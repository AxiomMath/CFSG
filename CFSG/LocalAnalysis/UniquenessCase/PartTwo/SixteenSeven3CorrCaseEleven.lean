module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private noncomputable def restrictAutAux {X : Type*} [Group X] (E : Subgroup X)
    (𝒜 : Subgroup (MulAut X)) (h𝒜 : ∀ β ∈ 𝒜, ∀ x ∈ E, β x ∈ E) : 𝒜 →* MulAut E where
  toFun β :=
    { toFun := fun x => ⟨(β : MulAut X) x, h𝒜 β β.2 x x.2⟩
      invFun := fun x => ⟨(β : MulAut X)⁻¹ x, h𝒜 _ (𝒜.inv_mem β.2) x x.2⟩
      left_inv := fun x => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun x => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul (β : MulAut X) (x : X) (y : X)) }
  map_one' := by ext x; rfl
  map_mul' β γ := by ext x; rfl

private theorem card_dvd_21_of_le_normalizer_order_seven {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 8) (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ e : E, e * e = 1)
    {A Z : Subgroup (MulAut E)} (hZ : Nat.card Z = 7)
    (hAZ : A ≤ normalizer (Z : Set (MulAut E))) : Nat.card A ∣ 21 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := CFSG.Sporadic.RuSchreier.ru_nonempty_mulEquiv_of_elementary (p := 2) hcomm
    (fun a => by rw [pow_two]; exact hsq a) (n := 3) (by rw [hE]; norm_num)
  let e : MulAut E ≃* GL (Fin 3) (ZMod 2) :=
    (MulAut.congr e₀).trans (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 2) 3)
  have hle : A.map e.toMonoidHom ≤ normalizer (Z.map e.toMonoidHom) :=
    (Subgroup.map_mono hAZ).trans (Subgroup.le_normalizer_map e.toMonoidHom)
  have hZc : Nat.card (Z.map e.toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective e.injective, hZ]
  have hN : Nat.card (normalizer (Z.map e.toMonoidHom : Set (GL (Fin 3) (ZMod 2)))) = 21 :=
    CFSG.ComponentClassification.GMS78.card_normalizer_eq_of_card_eq_seven_GL32 hZc
  have hdiv : Nat.card (A.map e.toMonoidHom) ∣ 21 := by
    have h2 := Subgroup.card_subgroup_dvd_card
      ((A.map e.toMonoidHom).subgroupOf (normalizer (Z.map e.toMonoidHom)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hN] at h2
    exact h2
  rw [Subgroup.card_map_of_injective e.injective] at hdiv
  exact hdiv

theorem s16c167_rk_le_one_of_case168_11 (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h : Case168_11 D ⊥ V hV L)
    {X : Subgroup (MulAut (Vtil ⊥ V hV))} (hXM : X ≤ Mbar D.M ⊥ V hV)
    (hX : IsElemAbelian2 X) : rk ↥X ≤ 1 := by
  classical
  have hsq : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  set Mb : Subgroup (MulAut (Vtil ⊥ V hV)) := Mbar D.M ⊥ V hV with hMb
  set Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L with hLb
  set Wt : Subgroup (Vtil ⊥ V hV) := wTil ⊥ V hV L with hWt
  have hLbcard : Nat.card Lb = 7 := by
    rw [hLb]; simpa only [lBar] using h.1.2
  have hWtrk : rk ↥Wt = 3 := by rw [hWt]; simpa only [wTil] using h.2.1
  have hWtcard : Nat.card ↥Wt = 8 := by
    have h1 := card_eq_two_pow hsq Wt
    rw [hWtrk] at h1
    simpa using h1
  have hs15 : s15 D.M ⊥ V hV L = 2 := h.2.2.1
  letI : MulAction Mb (Subgroup (MulAut (Vtil ⊥ V hV))) :=
    { smul := fun φ Y => Y.map (MulAut.conj (φ : MulAut (Vtil ⊥ V hV))).toMonoidHom
      one_smul := fun Y => by
        show Y.map (MulAut.conj (((1 : Mb) : MulAut (Vtil ⊥ V hV)))).toMonoidHom = Y
        have h1 : ((1 : Mb) : MulAut (Vtil ⊥ V hV)) = 1 := rfl
        rw [h1, map_one]
        change Y.map (MonoidHom.id (MulAut (Vtil ⊥ V hV))) = Y
        exact Subgroup.map_id Y
      mul_smul := fun φ ψ Y => by
        show Y.map (MulAut.conj (((φ * ψ : Mb) : MulAut (Vtil ⊥ V hV)))).toMonoidHom =
          (Y.map (MulAut.conj (ψ : MulAut (Vtil ⊥ V hV))).toMonoidHom).map
            (MulAut.conj (φ : MulAut (Vtil ⊥ V hV))).toMonoidHom
        have hfun : (MulAut.conj (((φ * ψ : Mb) : MulAut (Vtil ⊥ V hV)))).toMonoidHom =
            (MulAut.conj (φ : MulAut (Vtil ⊥ V hV))).toMonoidHom.comp
              (MulAut.conj (ψ : MulAut (Vtil ⊥ V hV))).toMonoidHom := by
          ext x
          simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply,
            MulAut.mul_apply, Subgroup.coe_mul]
          simp [MulAut.mul_apply]
        rw [Subgroup.map_map, hfun] }
  have hstab : MulAction.stabilizer Mb Lb = (Mb ⊓ normalizer (Lb : Set _)).subgroupOf Mb := by
    ext φ
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hφ
      exact ⟨φ.2, (Subgroup.mem_normalizer_iff_map_conj_eq).2 hφ⟩
    · rintro ⟨-, hφ⟩
      exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 hφ
  set M0 : Subgroup (MulAut (Vtil ⊥ V hV)) := Mb ⊓ normalizer (Lb : Set _) with hM0
  have hstabM0 : MulAction.stabilizer Mb Lb = M0.subgroupOf Mb := by rw [hstab, hM0]
  have hidx : (M0.subgroupOf Mb).index = 2 := by
    rw [← hstabM0, MulAction.index_stabilizer]
    have hset : MulAction.orbit Mb Lb =
        {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
          ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} := by
      ext Y
      constructor
      · rintro ⟨φ, rfl⟩
        exact ⟨(φ : MulAut (Vtil ⊥ V hV)), by rw [← hMb]; exact φ.2, rfl⟩
      · rintro ⟨φ, hφ, rfl⟩
        exact ⟨⟨φ, by rw [hMb]; exact hφ⟩, rfl⟩
    rw [hset]
    exact hs15
  have hM0normal : (M0.subgroupOf Mb).Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨a, ha_not, ha_swap⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.mp hidx
  set ψ : MulAut (Vtil ⊥ V hV) := (a : MulAut (Vtil ⊥ V hV))⁻¹ with hψ
  have hpsi_not : ψ ∉ M0 := by
    intro hmem
    apply ha_not
    rw [Subgroup.mem_subgroupOf]
    have : (a : MulAut (Vtil ⊥ V hV)) = ψ⁻¹ := by rw [hψ, inv_inv]
    rw [this]
    exact M0.inv_mem hmem
  set Lb' : Subgroup (MulAut (Vtil ⊥ V hV)) := Lb.map (MulAut.conj ψ).toMonoidHom with hLb'
  set Wt' : Subgroup (Vtil ⊥ V hV) := Wt.map ψ.toMonoidHom with hWt'
  have hLbM0 : Lb ≤ M0 := by
    intro l hl
    rw [hM0, Subgroup.mem_inf]
    refine ⟨?_, Subgroup.le_normalizer hl⟩
    rw [hMb]
    exact barSub_mono ⊥ V hV hc.setting.hyp151.le hl
  have hWtcomm : commSub Wt Lb = Wt := by
    have h1 := s15_Lin_commSub_commSub_eq_of_no_two_quotient hsq
      (s15_Kbar_no_two_quotient hc.setting.hyp151)
    rw [hWt, hLb]
    simpa only [wTil] using h1
  have hWt_ne : Wt ≠ ⊥ := by
    intro hbot
    have : rk ↥Wt = 0 := by rw [hbot, rk_bot]
    omega
  have hWt_map_of_normalizes : ∀ β ∈ M0, Wt.map β.toMonoidHom = Wt := by
    intro β hβ
    have hβN : β ∈ normalizer (Lb : Set (MulAut (Vtil ⊥ V hV))) := (Subgroup.mem_inf.1 hβ).2
    have hmap : Lb.map (MulAut.conj β).toMonoidHom = Lb :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).1 hβN
    have h := s15_Core_commSub_map_conj (⊤ : Subgroup (Vtil ⊥ V hV)) Lb β
    rw [Subgroup.map_top_of_surjective _ β.surjective, hmap] at h
    rw [hWt, wTil]
    exact h.symm
  have hinv : M0.map (MulAut.conj ψ).toMonoidHom = M0 := by
    have hle : M0.map (MulAut.conj ψ).toMonoidHom ≤ M0 := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨hmMb, -⟩ := Subgroup.mem_inf.1 hm
      have hmem : (⟨m, hmMb⟩ : Mb) ∈ M0.subgroupOf Mb := by
        rw [Subgroup.mem_subgroupOf]; exact hm
      have hconj := hM0normal.conj_mem (⟨m, hmMb⟩ : Mb) hmem (a⁻¹)
      rw [Subgroup.mem_subgroupOf] at hconj
      simpa [hψ, MulAut.conj_apply, mul_assoc] using hconj
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj ψ).injective]
  have hLb'M0 : Lb' ≤ M0 := by
    rw [hLb', ← hinv]
    exact Subgroup.map_mono hLbM0
  have hWt'eq : Wt' = commSub ⊤ Lb' := by
    have h := s15_Core_commSub_map_conj (⊤ : Subgroup (Vtil ⊥ V hV)) Lb ψ
    rw [Subgroup.map_top_of_surjective _ ψ.surjective] at h
    rw [hWt', hLb', hWt, wTil]
    exact h.symm
  have hM0N : M0 ≤ normalizer (Lb' : Set (MulAut (Vtil ⊥ V hV))) := by
    have h2 : (normalizer (Lb : Set (MulAut (Vtil ⊥ V hV)))).map (MulAut.conj ψ).toMonoidHom =
        normalizer (Lb' : Set (MulAut (Vtil ⊥ V hV))) := by
      rw [hLb']; exact Subgroup.map_equiv_normalizer_eq (H := Lb) (MulAut.conj ψ)
    intro m hm
    have hm' : m ∈ (normalizer (Lb : Set _)).map (MulAut.conj ψ).toMonoidHom := by
      have hle : M0.map (MulAut.conj ψ).toMonoidHom ≤
          (normalizer (Lb : Set _)).map (MulAut.conj ψ).toMonoidHom :=
        Subgroup.map_mono (inf_le_right : M0 ≤ normalizer (Lb : Set _))
      rw [hinv] at hle
      exact hle hm
    rwa [h2] at hm'
  have hWt'_map_of_normalizes : ∀ β ∈ M0, Wt'.map β.toMonoidHom = Wt' := by
    intro β hβ
    have hβN : Lb'.map (MulAut.conj β).toMonoidHom = Lb' :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hM0N hβ)
    have h := s15_Core_commSub_map_conj (⊤ : Subgroup (Vtil ⊥ V hV)) Lb' β
    rw [Subgroup.map_top_of_surjective _ β.surjective, hβN] at h
    rw [hWt'eq]
    exact h.symm
  have hpres₁ : ∀ β ∈ M0, ∀ x ∈ Wt, β x ∈ Wt := by
    intro β hβ x hx
    rw [← hWt_map_of_normalizes β hβ]
    exact Subgroup.mem_map_of_mem β.toMonoidHom hx
  have hpres₂ : ∀ β ∈ M0, ∀ x ∈ Wt', β x ∈ Wt' := by
    intro β hβ x hx
    rw [← hWt'_map_of_normalizes β hβ]
    exact Subgroup.mem_map_of_mem β.toMonoidHom hx
  let r₁ : M0 →* MulAut ↥Wt := restrictAutAux Wt M0 hpres₁
  let r₂ : M0 →* MulAut ↥Wt' := restrictAutAux Wt' M0 hpres₂
  obtain ⟨t, htM, -, -, -, hconcW⟩ := hc.conc
  have hsup : (⨆ Y ∈ conjSubs (Mbar D.M ⊥ V hV) Wt, Y) = ⊤ := by
    simpa only [hWt, wTil, lBar] using hconcW.1
  have hWt_top : Wt ⊔ Wt' = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hsup]
    refine iSup₂_le fun Y hY => ?_
    obtain ⟨g, hgM, rfl⟩ := hY
    by_cases hgM0 : g ∈ M0
    · rw [hWt_map_of_normalizes g hgM0]
      exact le_sup_left
    · have hswap := ha_swap (⟨g, hgM⟩ : Mb)
      have hmem : ((a : MulAut (Vtil ⊥ V hV)) * g) ∈ M0 := by
        rcases hswap with h | h
        · exact Subgroup.mem_subgroupOf.1 h
        · exact absurd (Subgroup.mem_subgroupOf.1 h) hgM0
      have h2 : (Wt.map g.toMonoidHom).map (a : MulAut (Vtil ⊥ V hV)).toMonoidHom = Wt := by
        have h1 := hWt_map_of_normalizes ((a : MulAut (Vtil ⊥ V hV)) * g) hmem
        have hcomp_eq : (((a : MulAut (Vtil ⊥ V hV)) * g)).toMonoidHom =
            (a : MulAut (Vtil ⊥ V hV)).toMonoidHom.comp g.toMonoidHom := rfl
        rw [hcomp_eq, ← Subgroup.map_map] at h1
        exact h1
      have h4 : Wt.map g.toMonoidHom =
          Wt.map ((a : MulAut (Vtil ⊥ V hV))⁻¹).toMonoidHom := by
        have h5 := congrArg
          (fun Z : Subgroup (Vtil ⊥ V hV) =>
            Z.map ((a : MulAut (Vtil ⊥ V hV))⁻¹).toMonoidHom) h2
        have hcomp : (((a : MulAut (Vtil ⊥ V hV))⁻¹).toMonoidHom).comp
            (a : MulAut (Vtil ⊥ V hV)).toMonoidHom = MonoidHom.id (Vtil ⊥ V hV) := by
          ext x; simp [MulAut.mul_apply]
        rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h5
        exact h5
      rw [h4, hWt', hψ]
      exact le_sup_right
  let r₁L : (Lb.subgroupOf M0) →* MulAut ↥Wt := r₁.comp (Lb.subgroupOf M0).subtype
  let r₂L : (Lb'.subgroupOf M0) →* MulAut ↥Wt' := r₂.comp (Lb'.subgroupOf M0).subtype
  have hker₁ : r₁L.ker = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    have hk' : r₁ ((k : Lb.subgroupOf M0) : M0) = 1 := hk
    have hz_mem : (((k : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) ∈ Lb :=
      Subgroup.mem_subgroupOf.1 k.2
    have htriv : ∀ v : Vtil ⊥ V hV, v ∈ Wt →
        (((k : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) v = v := by
      intro v hv
      have h1 := congrArg (fun f : MulAut ↥Wt => f ⟨v, hv⟩) hk'
      simp only [MulAut.one_apply] at h1
      exact congrArg Subtype.val h1
    by_cases hz1 : (((k : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) = 1
    · exact Subtype.ext (Subtype.ext hz1)
    · exfalso
      have hfix : Wt ≤ fixV (Subgroup.zpowers
          (((k : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV))) := by
        intro v hv
        rw [mem_fixV]
        intro y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have hzfix : v ∈ MulAction.fixedBy (Vtil ⊥ V hV)
            (((k : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) := by
          rw [MulAction.mem_fixedBy, MulAut.smul_def]
          exact htriv v hv
        have := MulAction.mem_fixedBy_zpow hzfix j
        rwa [MulAction.mem_fixedBy, MulAut.smul_def] at this
      have hbot := commSub_eq_bot_iff.mpr hfix
      have hzpow : Subgroup.zpowers
          (((k : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) = Lb := by
        apply Subgroup.eq_of_le_of_card_ge
        · intro y hy
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
          exact Lb.zpow_mem hz_mem j
        · rw [Nat.card_zpowers, hLbcard]
          have hdvd : orderOf
              (((k : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) ∣ 7 := by
            simpa [hLbcard] using Subgroup.orderOf_dvd_natCard Lb hz_mem
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h1 | h1
          · exact absurd (orderOf_eq_one_iff.1 h1) hz1
          · exact le_of_eq h1.symm
      rw [hzpow, hWtcomm] at hbot
      exact hWt_ne hbot
  set Z₁ : Subgroup (MulAut ↥Wt) := r₁L.range with hZ₁
  have hZ₁card : Nat.card Z₁ = 7 := by
    have h1 : Nat.card r₁L.ker * r₁L.ker.index = Nat.card (Lb.subgroupOf M0) :=
      Subgroup.card_mul_index r₁L.ker
    rw [Subgroup.index_ker, hker₁, Subgroup.card_bot, one_mul] at h1
    have h2 : Nat.card (Lb.subgroupOf M0) = Nat.card Lb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLbM0).toEquiv
    rw [hZ₁, h1, h2, hLbcard]
  have hA₁dvd : Nat.card r₁.range ∣ 21 := by
    have hle : r₁.range ≤ normalizer (Z₁ : Set (MulAut ↥Wt)) := by
      rw [Subgroup.le_normalizer_iff]
      intro φ hφ z hz
      obtain ⟨β, rfl⟩ := hφ
      rw [hZ₁] at hz
      obtain ⟨l, rfl⟩ := hz
      have hmem : β * ((l : Lb.subgroupOf M0) : M0) * β⁻¹ ∈ Lb.subgroupOf M0 := by
        rw [Subgroup.mem_subgroupOf]
        have hβN : (β : MulAut (Vtil ⊥ V hV)) ∈
            normalizer (Lb : Set (MulAut (Vtil ⊥ V hV))) := (Subgroup.mem_inf.1 β.2).2
        have hlLb : (((l : Lb.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) ∈ Lb :=
          Subgroup.mem_subgroupOf.1 l.2
        have hβNmap : Lb.map (MulAut.conj (β : MulAut (Vtil ⊥ V hV))).toMonoidHom = Lb :=
          (Subgroup.mem_normalizer_iff_map_conj_eq).1 hβN
        have hx := Subgroup.mem_map_of_mem
          (MulAut.conj (β : MulAut (Vtil ⊥ V hV))).toMonoidHom hlLb
        rw [hβNmap] at hx
        simpa [MulAut.conj_apply] using hx
      refine ⟨⟨β * ((l : Lb.subgroupOf M0) : M0) * β⁻¹, hmem⟩, ?_⟩
      change r₁ (β * ((l : Lb.subgroupOf M0) : M0) * β⁻¹) =
        r₁ β * r₁ ((l : Lb.subgroupOf M0) : M0) * (r₁ β)⁻¹
      rw [map_mul, map_mul, map_inv]
    exact card_dvd_21_of_le_normalizer_order_seven hWtcard (fun x y => mul_comm x y)
      (fun e => Subtype.ext (by simpa [pow_two] using hsq (e : Vtil ⊥ V hV))) hZ₁card hle
  have hker₂ : r₂L.ker = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    have hk' : r₂ ((k : Lb'.subgroupOf M0) : M0) = 1 := hk
    have hz_mem : (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) ∈ Lb' :=
      Subgroup.mem_subgroupOf.1 k.2
    have htriv : ∀ v : Vtil ⊥ V hV, v ∈ Wt' →
        (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) v = v := by
      intro v hv
      have h1 := congrArg (fun f : MulAut ↥Wt' => f ⟨v, hv⟩) hk'
      simp only [MulAut.one_apply] at h1
      exact congrArg Subtype.val h1
    by_cases hz1 : (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) = 1
    · exact Subtype.ext (Subtype.ext hz1)
    · exfalso
      have hfix : Wt' ≤ fixV (Subgroup.zpowers
          (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV))) := by
        intro v hv
        rw [mem_fixV]
        intro y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        have hzfix : v ∈ MulAction.fixedBy (Vtil ⊥ V hV)
            (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) := by
          rw [MulAction.mem_fixedBy, MulAut.smul_def]
          exact htriv v hv
        have := MulAction.mem_fixedBy_zpow hzfix j
        rwa [MulAction.mem_fixedBy, MulAut.smul_def] at this
      have hbot : commSub Wt' (Subgroup.zpowers
          (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV))) = ⊥ :=
        commSub_eq_bot_iff.mpr hfix
      have hcardLb' : Nat.card Lb' = 7 := by
        rw [hLb', Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hLbcard]
      have hzpow : Subgroup.zpowers
          (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) = Lb' := by
        apply Subgroup.eq_of_le_of_card_ge
        · intro y hy
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
          exact Lb'.zpow_mem hz_mem j
        · rw [Nat.card_zpowers, hcardLb']
          have hdvd : orderOf
              (((k : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) ∣ 7 := by
            simpa [hcardLb'] using Subgroup.orderOf_dvd_natCard Lb' hz_mem
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h1 | h1
          · exact absurd (orderOf_eq_one_iff.1 h1) hz1
          · exact le_of_eq h1.symm
      have hWt'comm : commSub Wt' Lb' = Wt' := by
        rw [hWt', hLb', s15_Core_commSub_map_conj, hWtcomm]
      rw [hzpow, hWt'comm] at hbot
      have hWt'_ne : Wt' ≠ ⊥ := by
        intro hbot'
        have hcard : Nat.card ↥Wt' = 8 := by
          rw [hWt', Subgroup.card_map_of_injective ψ.injective, hWtcard]
        have : Nat.card ↥Wt' = 1 := by rw [hbot', Subgroup.card_bot]
        omega
      exact hWt'_ne hbot
  set Z₂ : Subgroup (MulAut ↥Wt') := r₂L.range with hZ₂
  have hLb'card : Nat.card Lb' = 7 := by
    rw [hLb', Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hLbcard]
  have hWt'card : Nat.card ↥Wt' = 8 := by
    rw [hWt', Subgroup.card_map_of_injective ψ.injective, hWtcard]
  have hZ₂card : Nat.card Z₂ = 7 := by
    have h1 : Nat.card r₂L.ker * r₂L.ker.index = Nat.card (Lb'.subgroupOf M0) :=
      Subgroup.card_mul_index r₂L.ker
    rw [Subgroup.index_ker, hker₂, Subgroup.card_bot, one_mul] at h1
    have h2 : Nat.card (Lb'.subgroupOf M0) = Nat.card Lb' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLb'M0).toEquiv
    rw [hZ₂, h1, h2, hLb'card]
  have hA₂dvd : Nat.card r₂.range ∣ 21 := by
    have hle : r₂.range ≤ normalizer (Z₂ : Set (MulAut ↥Wt')) := by
      rw [Subgroup.le_normalizer_iff]
      intro φ hφ z hz
      obtain ⟨β, rfl⟩ := hφ
      rw [hZ₂] at hz
      obtain ⟨l, rfl⟩ := hz
      have hmem : β * ((l : Lb'.subgroupOf M0) : M0) * β⁻¹ ∈ Lb'.subgroupOf M0 := by
        rw [Subgroup.mem_subgroupOf]
        have hβN : (β : MulAut (Vtil ⊥ V hV)) ∈
            normalizer (Lb' : Set (MulAut (Vtil ⊥ V hV))) := hM0N β.2
        have hlLb : (((l : Lb'.subgroupOf M0) : M0) : MulAut (Vtil ⊥ V hV)) ∈ Lb' :=
          Subgroup.mem_subgroupOf.1 l.2
        have hβNmap : Lb'.map (MulAut.conj (β : MulAut (Vtil ⊥ V hV))).toMonoidHom = Lb' :=
          (Subgroup.mem_normalizer_iff_map_conj_eq).1 hβN
        have hx := Subgroup.mem_map_of_mem
          (MulAut.conj (β : MulAut (Vtil ⊥ V hV))).toMonoidHom hlLb
        rw [hβNmap] at hx
        simpa [MulAut.conj_apply] using hx
      refine ⟨⟨β * ((l : Lb'.subgroupOf M0) : M0) * β⁻¹, hmem⟩, ?_⟩
      change r₂ (β * ((l : Lb'.subgroupOf M0) : M0) * β⁻¹) =
        r₂ β * r₂ ((l : Lb'.subgroupOf M0) : M0) * (r₂ β)⁻¹
      rw [map_mul, map_mul, map_inv]
    exact card_dvd_21_of_le_normalizer_order_seven hWt'card (fun x y => mul_comm x y)
      (fun e => Subtype.ext (by simpa [pow_two] using hsq (e : Vtil ⊥ V hV))) hZ₂card hle
  let r : M0 →* MulAut ↥Wt × MulAut ↥Wt' := r₁.prod r₂
  have hker : r.ker = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at hm
    have h1 : r₁ m = 1 := by
      change (r m).1 = 1
      simpa using congrArg Prod.fst hm
    have h2 : r₂ m = 1 := by
      change (r m).2 = 1
      simpa using congrArg Prod.snd hm
    have htrivW : ∀ x ∈ Wt, (m : MulAut (Vtil ⊥ V hV)) x = x := by
      intro x hx
      have := congrArg (fun f : MulAut ↥Wt => f ⟨x, hx⟩) h1
      simp only [MulAut.one_apply] at this
      exact congrArg Subtype.val this
    have htrivW' : ∀ x ∈ Wt', (m : MulAut (Vtil ⊥ V hV)) x = x := by
      intro x hx
      have := congrArg (fun f : MulAut ↥Wt' => f ⟨x, hx⟩) h2
      simp only [MulAut.one_apply] at this
      exact congrArg Subtype.val this
    have htriv : ∀ v : Vtil ⊥ V hV, (m : MulAut (Vtil ⊥ V hV)) v = v := by
      intro v
      have hv : v ∈ Wt ⊔ Wt' := by rw [hWt_top]; exact Subgroup.mem_top v
      rw [Subgroup.mem_sup] at hv
      obtain ⟨x, hx, y, hy, rfl⟩ := hv
      rw [map_mul, htrivW x hx, htrivW' y hy]
    exact Subtype.ext (MulEquiv.ext htriv)
  have hcardM0 : Nat.card M0 ∣ 441 := by
    have h1 : Nat.card r.ker * r.ker.index = Nat.card M0 := Subgroup.card_mul_index r.ker
    rw [Subgroup.index_ker, hker, Subgroup.card_bot, one_mul] at h1
    have hle : r.range ≤ r₁.range.prod r₂.range := by
      rintro p ⟨m, hm⟩
      rw [← hm]
      change (r₁ m, r₂ m) ∈ r₁.range.prod r₂.range
      exact Subgroup.mem_prod.2 ⟨⟨m, rfl⟩, ⟨m, rfl⟩⟩
    have h3 : Nat.card r.range ∣ Nat.card (r₁.range.prod r₂.range) := by
      have := Subgroup.card_subgroup_dvd_card (r.range.subgroupOf (r₁.range.prod r₂.range))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
    have h4 : Nat.card (r₁.range.prod r₂.range) =
        Nat.card r₁.range * Nat.card r₂.range := by
      rw [Nat.card_congr (Subgroup.prodEquiv r₁.range r₂.range).toEquiv, Nat.card_prod]
    calc Nat.card M0 = Nat.card r.range := h1.symm
      _ ∣ Nat.card (r₁.range.prod r₂.range) := h3
      _ = Nat.card r₁.range * Nat.card r₂.range := h4
      _ ∣ 21 * 21 := Nat.mul_dvd_mul hA₁dvd hA₂dvd
      _ = 441 := by norm_num
  have hM0odd : Odd (Nat.card M0) := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact (by norm_num : ¬ (2 : ℕ) ∣ 441) (he.two_dvd.trans hcardM0)
  have hXb_disj : X.subgroupOf Mb ⊓ M0.subgroupOf Mb = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hzX, hzM0⟩ := Subgroup.mem_inf.1 hz
    have hzX' : (z : MulAut (Vtil ⊥ V hV)) ∈ X := Subgroup.mem_subgroupOf.1 hzX
    have hzM0' : (z : MulAut (Vtil ⊥ V hV)) ∈ M0 := Subgroup.mem_subgroupOf.1 hzM0
    have hz2 : (z : MulAut (Vtil ⊥ V hV)) ^ 2 = 1 := hX.2 _ hzX'
    have hdvd : orderOf (z : MulAut (Vtil ⊥ V hV)) ∣ Nat.card M0 :=
      Subgroup.orderOf_dvd_natCard M0 hzM0'
    have hodd : Odd (orderOf (z : MulAut (Vtil ⊥ V hV))) := hM0odd.of_dvd_nat hdvd
    have hdvd2 : orderOf (z : MulAut (Vtil ⊥ V hV)) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.2 hz2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h1
    · exact Subtype.ext (orderOf_eq_one_iff.1 h1)
    · exact absurd h1 (hodd.ne_two_of_dvd_nat dvd_rfl)
  have hcardX : Nat.card X ≤ 2 := by
    have hkerf : ((QuotientGroup.mk'
        (M0.subgroupOf Mb)).comp (X.subgroupOf Mb).subtype).ker = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      rw [MonoidHom.mem_ker] at hz
      have hzS : (z : Mb) ∈ M0.subgroupOf Mb := (QuotientGroup.eq_one_iff _).1 hz
      have hzX : (z : Mb) ∈ X.subgroupOf Mb := z.2
      have hmem : (z : Mb) ∈ X.subgroupOf Mb ⊓ M0.subgroupOf Mb :=
        Subgroup.mem_inf.2 ⟨hzX, hzS⟩
      rw [hXb_disj, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hle := Nat.card_le_card_of_injective
      ((QuotientGroup.mk' (M0.subgroupOf Mb)).comp (X.subgroupOf Mb).subtype)
      ((MonoidHom.ker_eq_bot_iff _).mp hkerf)
    rw [Subgroup.index_eq_card] at hidx
    have hXbcard : Nat.card (X.subgroupOf Mb) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
    rw [hXbcard, hidx] at hle
    exact hle
  rw [rk]
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hdvd : Nat.card X ∣ 2 := by
    have h1 : Nat.card X = 1 ∨ Nat.card X = 2 := by omega
    rcases h1 with h1 | h1 <;> simp [h1]
  calc padicValNat 2 (Nat.card X) ≤ padicValNat 2 2 :=
        CFSG.Quasithin.padicValNat_two_le_of_dvd (by norm_num) hdvd
    _ = 1 := by norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
