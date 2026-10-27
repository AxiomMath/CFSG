module

public import CFSG.Quasithin.EmptyFaithful.T1531In46
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4
public import CFSG.Quasithin.Background.E3Nlow
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.E3OffenderB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Weak

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

open scoped commutatorElement

theorem isSolvable_of_card_six {L : Type*} [Group L] [Finite L] (h : Nat.card L = 6) :
    Group.IsSolvable L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 (by rw [h]; norm_num)
  have hP : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := (Subgroup.zpowers x).card_mul_index
    rw [hP, h] at this
    omega
  have : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hidx
  have : IsCyclic (L ⧸ Subgroup.zpowers x) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, hidx])
  exact Group.isSolvable_of_subgroup_quotient (Subgroup.zpowers x)

theorem isSolvable_sup_of_commute {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) [Group.IsSolvable A] [Group.IsSolvable B] :
    Group.IsSolvable ↥(A ⊔ B) := by
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    { toFun := fun p => ⟨p.1 * p.2,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by
        have h1 : (q.1 : Γ) * p.2 = p.2 * q.1 := hc q.1 q.1.2 p.2 p.2.2
        show ((p.1 : Γ) * q.1) * ((p.2 : Γ) * q.2) = ((p.1 : Γ) * p.2) * ((q.1 : Γ) * q.2)
        calc ((p.1 : Γ) * q.1) * ((p.2 : Γ) * q.2) = (p.1 : Γ) * ((q.1 : Γ) * p.2) * q.2 := by
              simp only [mul_assoc]
          _ = (p.1 : Γ) * (p.2 * q.1) * q.2 := by rw [h1]
          _ = ((p.1 : Γ) * p.2) * ((q.1 : Γ) * q.2) := by simp only [mul_assoc]) }
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, b, hb, e⟩ := S1417.exists_mul_of_mem_sup_of_commute hc hy
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext e⟩
  exact Group.isSolvable_of_surjective hsurj

theorem isSolvable_of_ofourStruct {W : Type*} [CommGroup W] [Finite W]
    {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W} (h : OfourStruct X L₁ L₂ t) :
    Group.IsSolvable ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Group.IsSolvable ↥L₁ := isSolvable_of_card_six h.card_L₁
  have h2 : Group.IsSolvable ↥L₂ := isSolvable_of_card_six h.card_L₂
  have h3 : Group.IsSolvable ↥(L₁ ⊔ L₂) := isSolvable_sup_of_commute h.comm
  have hN : ((L₁ ⊔ L₂).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.normalizer_sup
  have h4 : Group.IsSolvable ↥((L₁ ⊔ L₂).subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h.le_X_sup).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe h.le_X_sup).injective
  have h5 : IsCyclic (↥X ⧸ (L₁ ⊔ L₂).subgroupOf X) :=
    isCyclic_of_prime_card (p := 2) (by
      rw [← Subgroup.index_eq_card]
      exact h.relIndex_sup)
  exact Group.isSolvable_of_subgroup_quotient ((L₁ ⊔ L₂).subgroupOf X)

theorem isSolvable_autI_153 (h : Hyp153 G T Mc M) : Group.IsSolvable ↥(autI h.elemAbelian M) := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  exact isSolvable_of_ofourStruct hS

theorem pCore_autI_eq_bot_153 (h : Hyp153 G T Mc M) :
    CFSG.Open.pCore 2 ↥(autI h.elemAbelian M) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.elemAbelian
  have hred := h.twoReduced.1
  have hMN := h.le_normalizer
  have hPX : pCoreOf 2 (autI hV M) ≤ autI hV M := pCoreOf_le 2 _
  have hP2 : IsPGroup 2 (pCoreOf 2 (autI hV M)) := pCoreOf_isPGroup 2 _
  have hXn : autI hV M ≤ Subgroup.normalizer
      ((pCoreOf 2 (autI hV M) : Subgroup (MulAut (IntMod (VZ T M) hV))) :
        Set (MulAut (IntMod (VZ T M) hV))) := le_normalizer_pCoreOf 2 _
  have hDM : preI hV M hMN (pCoreOf 2 (autI hV M)) ≤ M := preI_le hV
  have key : ∀ m ∈ M, ∀ d ∈ preI hV M hMN (pCoreOf 2 (autI hV M)),
      m * d * m⁻¹ ∈ preI hV M hMN (pCoreOf 2 (autI hV M)) := by
    intro m hm d hd
    obtain ⟨hdM, hdP⟩ := (mem_preI hV).1 hd
    have hmem : m * d * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hdM) (M.inv_mem hm)
    refine (mem_preI hV).2 ⟨hmem, ?_⟩
    have e : (⟨m * d * m⁻¹, hmem⟩ : ↥M) = ⟨m, hm⟩ * ⟨d, hdM⟩ * ⟨m, hm⟩⁻¹ := rfl
    have hmX : convHom hV M hMN ⟨m, hm⟩ ∈ autI hV M := by
      rw [convHom_apply]
      exact convI_mem_autI hV hm (hMN hm)
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXn hmX) _).mp hdP
  have hDn : M ≤ Subgroup.normalizer
      ((preI hV M hMN (pCoreOf 2 (autI hV M)) : Subgroup G) : Set G) := fun m hm =>
    B6.mem_normalizer_of_forall_mem (key m hm)
      (fun x hx => by simpa using key m⁻¹ (M.inv_mem hm) x hx)
  have hD2 : ∀ d ∈ preI hV M hMN (pCoreOf 2 (autI hV M)),
      ∃ k : ℕ, d ^ (2 ^ k) ∈ Subgroup.centralizer (VZ T M : Set G) := by
    intro d hd
    obtain ⟨hdM, hdP⟩ := (mem_preI hV).1 hd
    obtain ⟨k, hk⟩ := hP2 ⟨convHom hV M hMN ⟨d, hdM⟩, hdP⟩
    refine ⟨k, ?_⟩
    have h2 : (⟨d, hdM⟩ : ↥M) ^ 2 ^ k ∈ (convHom hV M hMN).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hk
    rw [ker_convHom hV M hMN, Subgroup.mem_subgroupOf] at h2
    simpa using h2.2
  have hDC := hred.2.2.2 _ hDM hDn hD2
  have hPbot : pCoreOf 2 (autI hV M) = ⊥ := by
    refine eq_bot_iff.mpr fun φ hφ => ?_
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 (hPX hφ)
    have hgD : (g : G) ∈ preI hV M hMN (pCoreOf 2 (autI hV M)) :=
      (mem_preI hV).2 ⟨hgM, by rw [convHom_apply]; exact hφ⟩
    exact Subgroup.mem_bot.mpr ((convI_eq_one_iff hV g).2 (hDC hgD))
  exact (Subgroup.map_eq_bot_iff_of_injective _ (autI hV M).subtype_injective).mp hPbot

theorem aSet_two_autI_153 (h : Hyp153 G T Mc M) : E3.aSet 2 (autI h.elemAbelian M) = ∅ :=
  E3.aSet_two_eq_empty (fun w => IntMod.sq_eq_one w) (isSolvable_autI_153 h)
    (pCore_autI_eq_bot_153 h)

theorem w1_le_centralizer (h : Hyp153 G T Mc M) (r62 : Res15362 T Mc M)
    (hr : (3 : ℕ∞) ≤ E3.rParam (VZ T M)) :
    E3.wClos (VZ T M) 1 T ≤ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := h.elemAbelian
  refine E3.wClos_le_of_forall fun A hA => ?_
  obtain ⟨hAT, g, hAVg, hmA⟩ := hA
  by_contra hAC
  have hAM : A ≤ M := hAT.trans h.T_le
  have hAN : A ≤ Subgroup.normalizer (VZ T M : Set G) := hAM.trans h.le_normalizer
  have hAb : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAVg (E3.isElemAbelian_conjSubgroup hV g)
  have hbar1 : autI hV A ≠ ⊥ := fun hb => hAC ((autI_eq_bot_iff hV hAN).1 hb)
  have hnot : autI hV A ∉ E3.aSet 2 (autI hV M) := by
    rw [aSet_two_autI_153 h]
    exact Set.notMem_empty _
  obtain ⟨B', hB'A, hmB', hfix⟩ : ∃ B' ≤ autI hV A, E3.mQuot (autI hV A) B' < 2 ∧
      fixV B' ≠ fixV (autI hV A) := by
    by_contra hcon
    push Not at hcon
    exact hnot ⟨autI_mono hV hAM, hbar1, isElemAbelian2_autI hV hAb hAN, hcon⟩
  have hBA : preI hV A hAN B' ≤ A := preI_le hV
  have hmAB : E3.mQuot A (preI hV A hAN B') < 2 := by
    rw [← E3.mQuot_autI_preI hV hAN hB'A]
    exact hmB'
  have hmVB : E3.mQuot (conjSubgroup (VZ T M) g) (preI hV A hAN B') < 3 := by
    have := E3.mQuot_add hBA hAVg
    omega
  have hCB : Subgroup.centralizer ((preI hV A hAN B' : Subgroup G) : Set G) ≤
      Subgroup.normalizer (conjSubgroup (VZ T M) g : Set G) := by
    by_contra hC
    have h1 := E3.rParam_le_mQuot (hBA.trans hAVg) hC
    rw [E3.rParam_conj] at h1
    have h2 : (3 : ℕ∞) ≤ (E3.mQuot (conjSubgroup (VZ T M) g) (preI hV A hAN B') : ℕ∞) := hr.trans h1
    have h3 : 3 ≤ E3.mQuot (conjSubgroup (VZ T M) g) (preI hV A hAN B') := by exact_mod_cast h2
    omega
  obtain ⟨v, hvB', hvA⟩ : ∃ v : IntMod (VZ T M) hV, v ∈ fixV B' ∧ v ∉ fixV (autI hV A) := by
    by_contra hcon
    push Not at hcon
    refine hfix (le_antisymm (fun v hv => hcon v hv) fun v hv => ?_)
    rw [mem_fixV] at hv ⊢
    exact fun x hx => hv x (hB'A hx)
  have hvB : v.val ∈ Subgroup.centralizer ((preI hV A hAN B' : Subgroup G) : Set G) :=
    (E3.mem_fixV_iff_preI hV hAN hB'A v).1 hvB'
  have hvA' : v.val ∉ Subgroup.centralizer (A : Set G) := fun hh =>
    hvA ((mem_fixV_autI hV hAN v).2 hh)
  obtain ⟨a, haA, hav⟩ : ∃ a ∈ A, a * v.val ≠ v.val * a := by
    by_contra hcon
    push Not at hcon
    exact hvA' (Subgroup.mem_centralizer_iff.mpr hcon)
  have hvN : v.val ∈ Subgroup.normalizer (conjSubgroup (VZ T M) g : Set G) := hCB hvB
  have haN : a ∈ Subgroup.normalizer (VZ T M : Set G) := hAN haA
  have hcomm_ne : ⁅v.val, a⁆ ≠ 1 := fun e => hav (commutatorElement_eq_one_iff_mul_comm.mp e).symm
  have hcV : ⁅v.val, a⁆ ∈ VZ T M := by
    have h1 : a * v.val⁻¹ * a⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp haN v.val⁻¹).mp ((VZ T M).inv_mem v.val_mem)
    have e : ⁅v.val, a⁆ = v.val * (a * v.val⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (VZ T M).mul_mem v.val_mem h1
  have hcVg : ⁅v.val, a⁆ ∈ conjSubgroup (VZ T M) g := by
    have h1 : v.val * a * v.val⁻¹ ∈ conjSubgroup (VZ T M) g :=
      (Subgroup.mem_normalizer_iff.mp hvN a).mp (hAVg haA)
    rw [commutatorElement_def]
    exact (conjSubgroup (VZ T M) g).mul_mem h1 ((conjSubgroup (VZ T M) g).inv_mem (hAVg haA))
  have hne : VZ T M ⊓ conjSubgroup (VZ T M) g ≠ ⊥ := by
    intro hb
    have : ⁅v.val, a⁆ ∈ VZ T M ⊓ conjSubgroup (VZ T M) g := ⟨hcV, hcVg⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hcomm_ne this
  have hbot := r62.commutes g hne
  have hmem : ⁅v.val, a⁆ ∈ ⁅VZ T M, conjSubgroup (VZ T M) g⁆ :=
    Subgroup.commutator_mem_commutator v.val_mem (hAVg haA)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hcomm_ne hmem

end Weak

section Proofs

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem isSylowIn_top_T (h : Hyp153 G T Mc M) : IsSylowIn 2 T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.qtfe.exists_sylow
  have := isSylowIn_top S
  rwa [hS] at this

theorem VZ_ne_bot_153 (h : Hyp153 G T Mc M) : VZ T M ≠ ⊥ := by
  intro hb
  have := h.card_VZ
  rw [hb, Subgroup.card_bot] at this
  omega

theorem n_gt_one_of_w_gt_one (h : Hyp153 G T Mc M) (hr : (3 : ℕ∞) ≤ E3.rParam (VZ T M))
    (hw : 1 < E3.wParam T (VZ T M)) {H : Subgroup G} (hH : IsHTM153 T M H) :
    1 < E1.nParam H := by
  by_contra hn
  have hn' : E1.nParam H ≤ 1 := not_lt.mp hn
  apply hH.2
  have hV := h.elemAbelian
  have hVT : VZ T M ≤ T := h.VZ_le_T
  have hT : E3.HypE322 T (VZ T M) :=
    ⟨isSylowIn_top_T h, hVT, h.T_le.trans h.le_normalizer⟩
  have hVR : VZ T M ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf hVT fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
      B2F.isElemAbelian_comm hV hw hv
  have hR1 : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≠ ⊥ := fun e =>
    VZ_ne_bot_153 h (le_bot_iff.mp (e ▸ hVR))
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := h.isHv_of_inM' h.inM
  have hTH : IsSylowIn 2 T H := by
    refine ⟨hH.1.1, h.isSylowTwoOf.2.1, fun h2 => (isSylowIn_top_T h).not_dvd_relIndex (h2.trans ?_)⟩
    rw [← Subgroup.relIndex_mul_relIndex T H ⊤ hH.1.1 le_top]
    exact Dvd.intro _ rfl
  have hCH : H ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ M := fun x hx => by
    rw [hHv]
    exact Subgroup.centralizer_le_normalizer _ hx.2
  have hmin : E1.nParam H < min (E3.wParam T (VZ T M)) (E3.rParam (VZ T M)) :=
    lt_of_le_of_lt hn' (lt_min hw (lt_of_lt_of_le (by norm_num) hr))
  exact E3.e3_35_one hV (VZ_ne_bot_153 h) hT (isUniqueM_normalizer_R h hR1) hTH hCH inf_le_left hmin

omit [Finite G] in
theorem one_lt_wParam_of_w0_w1
    (hw0 : E3.wClos (VZ T M) 0 T ≤ Subgroup.centralizer (VZ T M : Set G))
    (hw1 : E3.wClos (VZ T M) 1 T ≤ Subgroup.centralizer (VZ T M : Set G)) :
    1 < E3.wParam T (VZ T M) := by
  have h2 : (2 : ℕ∞) ≤ E3.wParam T (VZ T M) := by
    refine le_iInf₂ fun j hj => ?_
    have hj2 : 2 ≤ j := by
      by_contra hlt
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · exact hj (le_inf (E3.wClos_le 0 T) hw0)
      · exact hj (le_inf (E3.wClos_le 1 T) hw1)
    exact_mod_cast hj2
  have h2' : (1 : ℕ∞) + 1 ≤ E3.wParam T (VZ T M) := by
    rw [one_add_one_eq_two]
    exact h2
  exact (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mp h2'

end Proofs

theorem stage15363 : Stage15363 := by
  intro G _ _ T Mc M V₁ V₂ t c _ r46 _ r62 hr
  have h1 := w1_le_centralizer c.hyp r62 hr
  have hw := one_lt_wParam_of_w0_w1 r46.w0_centralizes h1
  exact ⟨h1, hw, fun _ hH => n_gt_one_of_w_gt_one c.hyp hr hw hH⟩

end CFSG.Quasithin
