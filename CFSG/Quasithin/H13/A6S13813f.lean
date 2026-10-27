module

public import CFSG.Quasithin.H13.A6S13813d

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

theorem A6P.map_one_mulAut {M : Type*} [Group M] (Z : Subgroup M) :
    Z.map (1 : MulAut M).toMonoidHom = Z := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hu
    exact ⟨u, hu, rfl⟩

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem card_tilde_V3 (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) :
    Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) S.V3) = 4 := by
  have hF := (hS.hF H hH).toHypF91
  have hV1V3 : fsuV1 T V ≤ S.V3 := hF.V₁_le_Vp
  have hV3U : S.V3 ≤ conjClosure S.V3 H := le_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hF.H_normalizes_V₁
  have h1 : Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) S.V3) =
      Nat.card ↥(tildeOf (fsuV1 T V) S.V3) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (secImg_mono hV3U)).toEquiv
  have h2 := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G))
    (B := fsuV1 T V) (T := fsuV1 T V) (H := S.V3) le_rfl hV1V3 (hV3U.trans hIHN)
  rw [show secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ from
    tildeOf_eq_bot_of_le le_rfl, Subgroup.relIndex_bot_left] at h2
  have h3 := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := S.V3)
  rw [inf_of_le_left hV1V3, S.card_V3, hF.card_V₁] at h3
  rw [h1]
  change Nat.card ↥(secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) S.V3) = 4
  rw [h2]
  omega

theorem exists_c0 : ∃ c : ↥(Subgroup.normalizer (V : Set G)), (c : G) ∈ S.L1 ∧
    S.frame.ρ c = Equiv.swap 0 1 * Equiv.swap 1 2 ∧ ∃ e : ℕ, (c : G) ^ 3 ^ e = 1 := by
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_c012
  obtain ⟨e, m, hm3, hmo⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3
    (by norm_num)
  refine ⟨g ^ (m ^ 2), ?_, ?_, e, ?_⟩
  · rw [Subgroup.coe_pow]
    exact S.L1.pow_mem hgL1 _
  · have hm2 : m ^ 2 % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rw [Nat.pow_mod]
      rcases this with h | h <;> simp [h]
    rw [map_pow, hg, ← Nat.div_add_mod (m ^ 2) 3, hm2, pow_add, pow_mul, c012_facts.2.2,
      one_pow, one_mul, pow_one]
  · have : (g ^ (m ^ 2)) ^ 3 ^ e = 1 := by
      rw [← pow_mul, show m ^ 2 * 3 ^ e = 3 ^ e * m * m by ring, pow_mul, ← hmo,
        pow_orderOf_eq_one, one_pow]
    simpa using congrArg Subtype.val this

section Mod

variable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
  (hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G))
  (hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G))
include hS hH

theorem stab_tilde_V3 {x : ↥H} (hx : (x : G) ∈ S.L1 ⊔ T) :
    actH hV₁ hIH x ∈ stabSub (subM (fsuV1 T V) (conjClosure S.V3 H) S.V3) := by
  have hF := (hS.hF H hH).toHypF91
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  exact (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hF.V₁_le_Vp (le_conjClosure S.V3 H) x).2
    (hF.L₁T_normalizes_Vp hx)

theorem fix_tilde_V3_c012 {c : ↥(Subgroup.normalizer (V : Set G))}
    (hc : S.frame.ρ c = Equiv.swap 0 1 * Equiv.swap 1 2) (hcH : (c : G) ∈ H)
    {w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hw : w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3)
    (hcw : actH hV₁ hIH ⟨c, hcH⟩ w = w) : w = 1 := by
  have hF := (hS.hF H hH).toHypF91
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  obtain ⟨⟨a, haN⟩, haU, hau⟩ := exists_mk_of_mem_tilde w
  have haU' : a ∈ conjClosure S.V3 H := haU
  have hwa : w = modMk hIHN a haU' := Subtype.ext hau.symm
  have haV3 : a ∈ S.V3 := by
    rw [← modMk_mem_subM_iff hIHN hF.V₁_le_Vp haU', ← hwa]
    exact hw
  rw [hwa, actH_modMk hV₁ hIHN hIH ⟨_, hcH⟩ haU'] at hcw
  have hcomm := (A6Tv.modMk_conj_eq_iff' hIHN haU' _).1 hcw
  rw [hwa]
  exact (A6Tv.modMk_eq_one_iff' hIHN haU').2 (mem_V1_of_c012 hc haV3 hcomm)

theorem R1_fix_tilde_V3 {r : ↥H} (hr : (r : G) ∈ pCoreOf 2 (S.L1 ⊔ T))
    {w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hw : w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3) : actH hV₁ hIH r w = w := by
  have hF := (hS.hF H hH).toHypF91
  set φ := actH hV₁ hIH with hφ
  set W := subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 with hW
  have hVsq : ∀ v : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)), v ^ 2 = 1 :=
    fun v => Subtype.ext (hF.isElemAbelian_tilde.2 v v.2)
  have hstR : ∀ q : ↥H, (q : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → φ q ∈ stabSub W := fun q hq =>
    S.stab_tilde_V3 hS hH hV₁ hIH (pCoreOf_le 2 _ hq)
  let K0 : Subgroup ↥H := (pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H
  let ψ : ↥K0 →* MulAut ↥W := (resHom W).comp ((φ.comp K0.subtype).codRestrict (stabSub W)
    fun q => hstR q.1 (Subgroup.mem_subgroupOf.1 q.2))
  have hψ : ∀ q : ↥K0, ψ q = resHom W ⟨φ q.1, hstR q.1 (Subgroup.mem_subgroupOf.1 q.2)⟩ :=
    fun q => rfl
  have hK02 : IsPGroup 2 ↥K0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    intro q
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (S.L1 ⊔ T)) ⟨(q.1 : G), Subgroup.mem_subgroupOf.1 q.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hR2 : IsPGroup 2 ψ.range := hK02.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨c0, hc0L1, hc0ρ, -⟩ := S.exists_c0
  have hc0H : (c0 : G) ∈ H := hF.L₁T_le_H (Subgroup.mem_sup_left hc0L1)
  have hc0st : φ ⟨c0, hc0H⟩ ∈ stabSub W := S.stab_tilde_V3 hS hH hV₁ hIH
    (Subgroup.mem_sup_left hc0L1)
  have hcR : ∀ ψ' ∈ ψ.range, resHom W ⟨φ ⟨c0, hc0H⟩, hc0st⟩ * ψ' *
      (resHom W ⟨φ ⟨c0, hc0H⟩, hc0st⟩)⁻¹ ∈ ψ.range := by
    rintro _ ⟨q, rfl⟩
    have hq : ((⟨c0, hc0H⟩ * q.1 * (⟨c0, hc0H⟩ : ↥H)⁻¹ : ↥H) : G) ∈
        pCoreOf 2 (S.L1 ⊔ T) := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (S.L1 ⊔ T)
        (Subgroup.mem_sup_left hc0L1)) q.1).mp (Subgroup.mem_subgroupOf.1 q.2)
      simpa using this
    refine ⟨⟨_, Subgroup.mem_subgroupOf.2 hq⟩, ?_⟩
    rw [hψ, hψ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  have hfix : ∀ w : ↥W, resHom W ⟨φ ⟨c0, hc0H⟩, hc0st⟩ w = w → w = 1 := by
    intro w hcw
    have h1 : φ ⟨c0, hc0H⟩ (w : ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) = w := by
      have := congrArg Subtype.val hcw
      rwa [resHom_apply] at this
    exact Subtype.ext (S.fix_tilde_V3_c012 hS hH hV₁ hIH hc0ρ hc0H w.2 h1)
  have hbot := A6P.eq_bot_of_normal_two hVsq (S.card_tilde_V3 hS hH) hR2 hcR hfix
  have hmem : ψ ⟨r, Subgroup.mem_subgroupOf.2 hr⟩ ∈ ψ.range := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot, hψ] at hmem
  have := congrArg (fun ψ' : MulAut ↥W => ((ψ' ⟨w, hw⟩ : ↥W) :
    ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))) hmem
  simpa [resHom_apply] using this

end Mod

section PSec

variable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
  [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))]
  {hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G)}
  {hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G)} {p : ℕ}
  {P : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H)))}
  (hP : A6P.PData S.L1 T L H (actH hV₁ hIH)
    (((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) p P)
include hS hH hP

theorem iSup_P_tilde_V3 :
    (⨆ x ∈ P, (subM (fsuV1 T V) (conjClosure S.V3 H) S.V3).map
      (x : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))).toMonoidHom) = ⊤ := by
  have hF := (hS.hF H hH).toHypF91
  set φ := actH hV₁ hIH with hφ
  set W := subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 with hW
  set Z := ⨆ x ∈ P, W.map (x : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))).toMonoidHom
    with hZ
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hPZ : ∀ x ∈ P, Z.map (x : MulAut _).toMonoidHom ≤ Z := by
    intro x hx
    rw [hZ, Subgroup.map_iSup]
    refine iSup_le fun x' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hx' => ?_
    rw [Subgroup.map_map]
    exact le_iSup₂_of_le (f := fun (y : MulAut _) (_ : y ∈ P) => W.map y.toMonoidHom)
      (x * x') (P.mul_mem hx hx') le_rfl
  have hYZ : ∀ y : ↥H, (y : G) ∈ S.L1 ⊔ T → Z.map (φ y).toMonoidHom ≤ Z := by
    intro y hy
    have hyW : W.map (φ y).toMonoidHom = W := by
      have hst := S.stab_tilde_V3 hS hH hV₁ hIH hy
      ext w
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact (hst w').2 hw'
      · intro hw
        refine ⟨(φ y)⁻¹ w, (hst _).1 (by rw [MulAut.apply_inv_self]; exact hw), ?_⟩
        show (φ y) ((φ y)⁻¹ w) = w
        exact MulAut.apply_inv_self _ _ _
    rw [hZ, Subgroup.map_iSup]
    refine iSup_le fun x' => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hx' => ?_
    rw [Subgroup.map_map]
    have e : (φ y).toMonoidHom.comp (x' : MulAut _).toMonoidHom =
        (φ y * x' * (φ y)⁻¹).toMonoidHom.comp (φ y).toMonoidHom := by
      ext w
      simp
    rw [e, ← Subgroup.map_map, hyW]
    exact le_iSup₂_of_le (f := fun (z : MulAut _) (_ : z ∈ P) => W.map z.toMonoidHom)
      _ (hP.normal _ ⟨y, rfl⟩ _ hx') le_rfl
  let St : Subgroup (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    { carrier := {m | Z.map m.toMonoidHom ≤ Z ∧ Z.map m⁻¹.toMonoidHom ≤ Z}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · rw [show (a * b).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom from rfl,
            ← Subgroup.map_map]
          exact (Subgroup.map_mono hb1).trans ha1
        · rw [mul_inv_rev, show (b⁻¹ * a⁻¹).toMonoidHom = b⁻¹.toMonoidHom.comp a⁻¹.toMonoidHom
            from rfl, ← Subgroup.map_map]
          exact (Subgroup.map_mono ha2).trans hb2
      one_mem' := ⟨by rw [A6P.map_one_mulAut], by rw [inv_one, A6P.map_one_mulAut]⟩
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        exact ⟨ha2, by rwa [inv_inv]⟩ }
  set K : Subgroup G := (St.comap φ).map H.subtype with hK
  have hmemK : ∀ y : ↥H, Z.map (φ y).toMonoidHom ≤ Z → Z.map (φ y⁻¹).toMonoidHom ≤ Z →
      (y : G) ∈ K := fun y h1 h2 => ⟨y, ⟨h1, by rwa [← map_inv]⟩, rfl⟩
  have hle : (oTwoRes ((P.comap φ).map H.subtype) ⊔ S.L1) ⊔ T ≤ K := by
    have hPh : oTwoRes ((P.comap φ).map H.subtype) ≤ H :=
      (oTwoRes_le _).trans (Subgroup.map_subtype_le _)
    have hLT : S.L1 ⊔ T ≤ H := hF.L₁T_le_H
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      have hxP := hP.map_mem ⟨x, hPh hx⟩ hx
      exact hmemK ⟨x, hPh hx⟩ (hPZ _ hxP) (by rw [map_inv]; exact hPZ _ (P.inv_mem hxP))
    · intro x hx
      have hxL : x ∈ S.L1 ⊔ T := Subgroup.mem_sup_left hx
      exact hmemK ⟨x, hLT hxL⟩ (hYZ _ hxL) (hYZ _ ((S.L1 ⊔ T).inv_mem hxL))
    · intro x hx
      have hxL : x ∈ S.L1 ⊔ T := Subgroup.mem_sup_right hx
      exact hmemK ⟨x, hLT hxL⟩ (hYZ _ hxL) (hYZ _ ((S.L1 ⊔ T).inv_mem hxL))
  have hHK : ∀ h : ↥H, Z.map (φ h).toMonoidHom ≤ Z := by
    intro h
    obtain ⟨h', hh', hh'eq⟩ := Subgroup.mem_map.1 (hle (hP.eq.le h.2))
    have : h' = h := Subtype.ext hh'eq
    rw [← this]
    exact hh'.1
  have hgen := iSup_actH_subM_eq_top hV₁ hIHN hIH hF.V₁_le_Vp
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun m hm => ?_
  obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.1 hm
  have hWZ : W ≤ Z := by
    have := le_iSup₂_of_le (f := fun (z : MulAut _) (_ : z ∈ P) => W.map z.toMonoidHom)
      1 P.one_mem le_rfl
    rwa [A6P.map_one_mulAut] at this
  exact (Subgroup.map_mono hWZ).trans (hHK h)

theorem eq_one_of_cent_P {r : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hr : r ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (hrP : ∀ x ∈ P, r * x = x * r) : r = 1 := by
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hr
  have hfix : ∀ x ∈ P, (subM (fsuV1 T V) (conjClosure S.V3 H) S.V3).map
      (x : MulAut _).toMonoidHom ≤ fixV (Subgroup.zpowers (actH hV₁ hIH q)) := by
    rintro x hx _ ⟨w, hw, rfl⟩
    refine mem_fixV.2 fun z hz => B1.zpowers_fix ?_ z hz
    have h1 := congrArg (fun m : MulAut _ => m w) (hrP x hx)
    simp only [MulAut.mul_apply] at h1
    rw [MulEquiv.coe_toMonoidHom, h1,
      S.R1_fix_tilde_V3 hS hH hV₁ hIH (Subgroup.mem_subgroupOf.1 hq) hw]
  have htop := S.iSup_P_tilde_V3 hS hH hP
  have hle : (⊤ : Subgroup _) ≤ fixV (Subgroup.zpowers (actH hV₁ hIH q)) := by
    rw [← htop]
    exact iSup₂_le fun x hx => hfix x hx
  exact MulEquiv.ext fun u => hle (Subgroup.mem_top u) _ (Subgroup.mem_zpowers _)

omit hS hH [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H)))] hP in
theorem pow_two_pow_eq_one_of_mem_R1 {s : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hs : s ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) :
    ∃ k : ℕ, s ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hs
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (S.L1 ⊔ T)) ⟨q, Subgroup.mem_subgroupOf.1 hq⟩
  have hk' : q ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  exact ⟨k, by rw [← map_pow, hk', map_one]⟩

theorem P_le_closure {s : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (hs : s ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) (hs1 : s ≠ 1) :
    P ≤ Subgroup.closure {y | ∃ x ∈ (actH hV₁ hIH).range, y = x * s * x⁻¹} := by
  set φ := actH hV₁ hIH with hφ
  set C := Subgroup.closure {y | ∃ x ∈ φ.range, y = x * s * x⁻¹} with hC
  have hsX : s ∈ φ.range := Subgroup.map_le_range _ _ hs
  have hCn : ∀ x ∈ φ.range, ∀ z ∈ C, x * z * x⁻¹ ∈ C := by
    intro x hx z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x', hx', rfl⟩ := hz
      exact Subgroup.subset_closure ⟨x * x', φ.range.mul_mem hx hx', by group⟩
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact C.one_mem
    | mul a b _ _ ha hb =>
      have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [e]
      exact C.mul_mem ha hb
    | inv a _ ha =>
      have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [e]
      exact C.inv_mem ha
  have hsC : s ∈ C := Subgroup.subset_closure ⟨1, φ.range.one_mem, by group⟩
  have hYX : ∀ y ∈ ((S.L1 ⊔ T).subgroupOf H).map φ, y ∈ φ.range :=
    fun y hy => Subgroup.map_le_range _ _ hy
  have hR := hP.minimal (P ⊓ C) inf_le_left (fun y hy x hx =>
    ⟨hP.normal y (hYX y hy) x hx.1, hCn y (hYX y hy) x hx.2⟩) (fun hcent => hs1 ?_)
  · rw [← hR]
    exact inf_le_right
  refine S.eq_one_of_cent_P hS hH hP hs fun x hx => ?_
  have hxX : x ∈ φ.range := (hP.le_pCore.trans (pCoreOf_le p _)) hx
  set c := s * x * s⁻¹ * x⁻¹ with hc
  have hcP : c ∈ P := P.mul_mem (hP.normal s hsX x hx) (P.inv_mem hx)
  have hcC : c ∈ C := by
    have h1 : x * s * x⁻¹ ∈ C := Subgroup.subset_closure ⟨x, hxX, rfl⟩
    have e : c = s * (x * s * x⁻¹)⁻¹ := by rw [hc]; group
    rw [e]
    exact C.mul_mem hsC (C.inv_mem h1)
  have hsc : s * c = c * s := hcent c ⟨hcP, hcC⟩ s hs
  have hpow : ∀ n : ℕ, s ^ n * x * (s ^ n)⁻¹ = c ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hsc' : s * c ^ n * s⁻¹ = c ^ n := by
        rw [((Commute.pow_right hsc n) : s * c ^ n = c ^ n * s), mul_inv_cancel_right]
      have hsx : s * x * s⁻¹ = c * x := by rw [hc]; group
      calc s ^ (n + 1) * x * (s ^ (n + 1))⁻¹ = s * (s ^ n * x * (s ^ n)⁻¹) * s⁻¹ := by group
        _ = s * (c ^ n * x) * s⁻¹ := by rw [ih]
        _ = (s * c ^ n * s⁻¹) * (s * x * s⁻¹) := by group
        _ = c ^ n * (c * x) := by rw [hsc', hsx]
        _ = c ^ (n + 1) * x := by group
  obtain ⟨k, hk⟩ := S.pow_two_pow_eq_one_of_mem_R1 hs
  have hc2 : c ^ 2 ^ k = 1 := by
    have := hpow (2 ^ k)
    rw [hk, one_mul, inv_one, mul_one] at this
    exact mul_eq_right.1 this.symm
  have hc1 : c = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k
      ((Nat.coprime_primes Nat.prime_two hP.prime).2 (Ne.symm hP.ne_two)))
      (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one (hP.exp c hcP))
  have : s * x * s⁻¹ * x⁻¹ = 1 := hc1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
  exact this

theorem inv_of_card_eq (hcard : Nat.card P = p)
    {a : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (ha : a ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH)) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) : ∀ x ∈ P, a * x * a⁻¹ = x⁻¹ := by
  have : Fact p.Prime := ⟨hP.prime⟩
  have : IsCyclic ↥P := isCyclic_of_prime_card hcard
  have haX : a ∈ (actH hV₁ hIH).range := Subgroup.map_le_range _ _ ha
  set C := P ⊓ Subgroup.centralizer ({a} : Set (MulAut _)) with hCdef
  have hC : C = ⊥ := by
    have hdvd : Nat.card C ∣ p := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hP.prime).1 hdvd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      have hCP : C = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
      apply ha1
      refine S.eq_one_of_cent_P hS hH hP ha fun x hx => ?_
      have hxC : x ∈ C := hCP ▸ hx
      exact Subgroup.mem_centralizer_iff.1 hxC.2 a rfl
  intro x hx
  have hax : a * x * a⁻¹ ∈ P := hP.normal a haX x hx
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hy : x * (a * x * a⁻¹) ∈ C := by
    refine ⟨P.mul_mem hx hax, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hcomm : x * (z * x * z⁻¹) = (z * x * z⁻¹) * x :=
      congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥P) ⟨_, hax⟩)
    have e : z * (x * (z * x * z⁻¹)) * z⁻¹ = (z * x * z⁻¹) * ((z * z) * x * (z * z)⁻¹) := by
      group
    calc z * (x * (z * x * z⁻¹)) = z * (x * (z * x * z⁻¹)) * z⁻¹ * z := by group
      _ = (z * x * z⁻¹) * ((z * z) * x * (z * z)⁻¹) * z := by rw [e]
      _ = (z * x * z⁻¹) * x * z := by rw [ha2]; group
      _ = x * (z * x * z⁻¹) * z := by rw [hcomm]
  rw [hC, Subgroup.mem_bot] at hy
  exact eq_inv_of_mul_eq_one_right hy

theorem eq_of_card_eq (hcard : Nat.card P = p)
    {a b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))}
    (ha : a ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (hb : b ∈ ((pCoreOf 2 (S.L1 ⊔ T)).subgroupOf H).map (actH hV₁ hIH))
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have h1 := S.inv_of_card_eq hS hH hP hcard ha ha2 ha1
  have h2 := S.inv_of_card_eq hS hH hP hcard hb hb2 hb1
  have hab := S.eq_one_of_cent_P hS hH hP (Subgroup.mul_mem _ ha hb) fun x hx => by
    have hbx : b * x * b⁻¹ = x⁻¹ := h2 x hx
    have hax' : a * x⁻¹ * a⁻¹ = x := by
      calc a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
        _ = x := by rw [h1 x hx, inv_inv]
    calc a * b * x = a * (b * x * b⁻¹) * b := by group
      _ = a * x⁻¹ * b := by rw [hbx]
      _ = (a * x⁻¹ * a⁻¹) * (a * b) := by group
      _ = x * (a * b) := by rw [hax']
  calc a = a * b * b := by rw [mul_assoc, hb2, mul_one]
    _ = b := by rw [hab, one_mul]

end PSec

end Setting4

end CFSG.Quasithin.H13.A6

